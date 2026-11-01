(* FS3 load3: the internal specification of ZSTD_DCtx_refDDict implies the API one (API v3.1: with the caller's
   DDicts, dict_res + set_res).  The API allows NULL and any stage and allocator: the internal call
   is made on the context with its allocator's bound raised (Load3Rdd.ref_mem; CMem.CM_mono) so that the set fits
   beside the largest stream buffers *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Split Zstd.proof.dec.v3.FS.load3.Load3Post Zstd.proof.dec.v3.FS.load3.Load3Rdd
  Zstd.proof.dec.v3.FS.load3.Load3Set.
Local Open Scope logic.

Section CM_Load3RefSub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma hset_rep_nodup am sp l hb : hset_rep am sp l hb |-- !! NoDup (map fst l).
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval).
  - Intros. subst. entailer!. constructor.
  - Intros tp tbl. entailer!. match goal with H: hs_inv _ _ |- _ => destruct H as [_ [_ [_ [Hnd _]]]] end. exact Hnd.
Qed.

Lemma veqb_ptr' q : isptr q -> veqb q nullval = false.
Proof. intros H. unfold veqb. destruct (Val.eq q nullval); [subst; contradiction | reflexivity]. Qed.

Lemma ctx_rep3_nodup DENT TABS gv p k : ctx_rep3 DENT TABS gv p k |-- !! NoDup (map fst (c3_set k)).
Proof.
  rewrite ctx_rep3_split. Intros.
  sep_apply (hset_rep_nodup (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k))).
  entailer!.
Qed.

(* the fields of a DDict other than dictBuffer and dictID, and the memory it owns besides its struct token *)
Definition dd_rest (DENT: dent_pred) (gv: globals) (x: ddx) (buf: val) : mpred :=
  field_at Ews t_ddict (DOT _dictContent) buf (dx_q x) *
  field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength (dx_bytes x)))) (dx_q x) *
  field_at Ews t_ddict (DOT _entropyPresent) (Vint (Int.repr match ddx_ent x with Some _ => 1 | None => 0 end)) (dx_q x) *
  field_at Ews t_ddict (DOT _cMem) (cmem_v (dx_mem x)) (dx_q x) * DENT gv (dx_q x) (ddx_ent x) *
  (if ddx_copied x
   then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf *
        data_at Ews (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf
   else emp) * ddict_pad (dx_q x).

(* the pure facts of DD3_of's struct *)
Definition dd_props (x: ddx) (buf: val) : Prop :=
  isptr (dx_q x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ bytes_ok (dx_bytes x) /\
  ld_rel (dx_bytes x) (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None) /\
  (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
  (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\
  (match dx_ref x with Some p => buf = p | None => True end) /\ cmem_ok (dx_mem x).

Lemma dd_rebuild DENT gv q dd :
  dd_props (dd_x q dd) (dd_buf dd) ->
  field_at Ews t_ddict (DOT _dictBuffer) (ddb dd) q *
  field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (dd_id dd))) q *
  malloc_token Ews t_ddict q * dd_rest DENT gv (dd_x q dd) (dd_buf dd) |-- DD3x DENT gv q dd && valid_pointer q.
Proof.
  intros HP. apply andp_right; [| eapply derives_trans; [| apply (l3s_dd_valid DENT gv q dd)]].
  all: unfold DD3x, DD3_of, ddict_rep_at, ddict_struct, ddict_mem, dd_rest; rewrite l3s_dd_x_buf;
       change (dx_q (dd_x q dd)) with q; change (dx_raw (dd_x q dd)) with false; cbv iota;
       change (dict_id_of (dx_bytes (dd_x q dd))) with (dd_id dd); change (Tstruct _ZSTD_DDict_s noattr) with t_ddict;
       unfold dd_props in HP; rewrite !prop_true_andp by tauto;
       repeat match goal with |- context [field_at ?sh ?t ?gfs ?v ?p] => generalize (field_at sh t gfs v p); intro end;
       cancel.
Qed.

Lemma pull_prop {A: Prop} (P Q: mpred) : (P |-- !! A) -> (A -> P |-- Q) -> P |-- Q.
Proof.
  intros H1 H2. apply derives_trans with (!! A && P); [apply andp_right; auto |].
  apply derives_extract_prop; auto.
Qed.

(* the context's representation holds with the allocator of the internal call (its bound raised) *)
Lemma ctx_rep3_ref_mem DENT TABS gv d st k q w :
  sf_mem (c3_s k) = dc_mem st ->
  ctx_rep3 DENT TABS gv d k |-- ctx_rep3 DENT TABS gv d (k_mem k (ref_mem st k q w)).
Proof.
  intros Hm. destruct (ref_mem_raise st k q w Hm) as [[w' E] | E]; rewrite E.
  - apply ctx_rep3_raise.
  - unfold k_mem. rewrite sf_with_mem_same, c3_with_s_same. apply derives_refl.
Qed.

(* the window limit the internal call's allocator covers: the context, the set and the largest stream buffers *)
Definition ref_w (k: cst3) : Z :=
  sf_given (c3_s k) + 3 * set_new_bytes + 3 * sf_held (c3_s k) + dstream_size (2 ^ 31) + 2 ^ 31.

Lemma ref_w_facts (st: dctx_st) (k: cst3) :
  base_rel3 st k -> 0 <= sf_held (c3_s k) -> 0 <= sf_inSize (c3_s k) -> 0 <= sf_outSize (c3_s k) -> par_ok (c3_par k) ->
  dp_wmax (dc_par st) <= ref_w k /\
  sf_given (c3_s k) + 3 * set_new_bytes + 3 * sf_held (c3_s k) + dstream_size (2 ^ 31) <= dstream_size (ref_w k).
Proof.
  intros (_ & Hp & _) H1 H2 H3 (_ & _ & _ & Hw & _). rewrite <- Hp.
  unfold ref_w, dstream_size, sf_given, set_new_bytes, ZSTD_BLOCKSIZE_MAX. rewrite dctx_size_eq. simpl sizeof. lia.
Qed.

(* the internal call's pure preconditions on the context's side *)
Lemma ref_mem_pre (st: dctx_st) (k: cst3) (q: val) :
  base_rel3 st k -> 0 <= sf_held (c3_s k) -> 0 <= sf_inSize (c3_s k) -> 0 <= sf_outSize (c3_s k) -> par_ok (c3_par k) ->
  local_mem (sf_mem (c3_s (k_mem k (ref_mem st k q (ref_w k))))) (c3_dict k) /\
  (sf_stage (c3_s k) = 0 -> q <> nullval ->
     cm_room (sf_mem (c3_s (k_mem k (ref_mem st k q (ref_w k))))) (sf_given (c3_s k))
             (3 * set_new_bytes + 2 * sf_held (c3_s k))).
Proof.
  intros Hb H1 H2 H3 Hpar.
  destruct (base_rel3_mem _ _ Hb) as (Hm1 & Hm2 & Hm3).
  destruct (ref_w_facts st k Hb H1 H2 H3 Hpar) as [_ Hw2].
  cbn [k_mem c3_s c3_with_s sf_mem sf_with_mem]. split.
  - destruct (ref_mem_raise st k q (ref_w k) Hm1) as [[w' E] | E]; rewrite E; [apply local_mem_raise |]; exact Hm3.
  - intros Hs Hq. unfold ref_mem. rewrite if_true by auto. rewrite if_false by auto. rewrite <- Hm1.
    destruct (sf_mem (c3_s k)) as [m|]; simpl; [| exact I].
    assert (0 <= sf_given (c3_s k)) by (unfold sf_given; rewrite dctx_size_eq; lia).
    assert (0 <= set_new_bytes) by (unfold set_new_bytes; simpl; lia).
    assert (0 <= dstream_size (2 ^ 31)) by (unfold dstream_size, ZSTD_BLOCKSIZE_MAX; rewrite dctx_size_eq; lia).
    unfold set_new_bytes in *; simpl sizeof in *. lia.
Qed.

Lemma refDDict_rsub DENT TABS SR BR : DENT_OK DENT -> TABS_OK TABS ->
  funspec_sub (snd (ZSTD_DCtx_refDDict_int_spec3 DENT TABS))
              (snd (ZSTD_DCtx_refDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT))).
Proof.
  intros HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[gv d] st] q] dd] sh] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold LOCALx at 1, argsassert2assert at 1; simpl.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  match goal with Hx: is_pointer_or_null q |- _ => rename Hx into Hpq end.
  destruct (eq_dec q nullval) as [Hq0 | Hq0].
  - (* NULL: no dictionary *)
    subst q.
    unfold DC3x at 1, DC3_of. Intros k.
    match goal with Hx: base_rel3 st k |- _ => rename Hx into Hb end.
    match goal with Hx: dc_ss st <> ss_init -> _ |- _ => rename Hx into Hsr end.
    match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
    match goal with Hx: ex_on3 SR st k |- _ => rename Hx into Hex end.
    apply (pull_prop (A := 0 <= sf_held (c3_s k) /\ 0 <= sf_inSize (c3_s k) /\ 0 <= sf_outSize (c3_s k) /\
                           par_ok (c3_par k))).
    { apply andp_left2. rewrite ctx_rep3_split. Intros. sep_apply (ctx_rest3k_props TABS gv d k). entailer!. }
    intros (Hk1 & Hk2 & Hk3 & Hpar).
    destruct (ref_mem_pre st k nullval Hb Hk1 Hk2 Hk3 Hpar) as [Hlm Hroom].
    destruct (ref_w_facts st k Hb Hk1 Hk2 Hk3 Hpar) as [Hw1 Hw2].
    assert (Hw3: 3 * set_new_bytes + 3 * sf_held (c3_s k) + dstream_size (2 ^ 31) <= dstream_size (ref_w k))
      by (assert (0 <= sf_given (c3_s k)) by (unfold sf_given; rewrite dctx_size_eq; lia); lia).
    Exists (@nil ptr_witness, gv, d, k_mem k (ref_mem st k nullval (ref_w k)), nullval, dd)
      (dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st)).
    simpl. apply andp_right.
    + unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
      rewrite prop_true_andp.
      2: { split; [left; reflexivity |].
           split; [split; [intros Hc; contradiction | split; [exact Hlm | split; [exact Hroom | exact I]]] |].
           split; [reflexivity | assumption]. }
      replace (veqb nullval nullval) with true by (unfold veqb; destruct (Val.eq nullval nullval); congruence).
      simpl andb. cbv iota. unfold pws_pred; simpl.
      sep_apply (ctx_rep3_ref_mem DENT TABS gv d st k nullval (ref_w k) (proj1 (base_rel3_mem _ _ Hb))).
      cancel.
    + apply prop_right. intros rho'. normalize.
      rename x into r. rename x0 into k'.
      match goal with Hx: refddict_int_res _ _ _ _ _ |- _ => rename Hx into Hres end.
      destruct (ref_api_post SR gv BR st k nullval dd (ref_w k) r k' Hb Hbl Hsr Hbr Hex
                  ltac:(intros Hc; contradiction) Hw1 Hw3 Hres) as (st' & Hst' & Hb' & Hsr' & Hbr' & Hex').
      replace (veqb nullval nullval) with true by (unfold veqb; destruct (Val.eq nullval nullval); congruence).
      simpl andb. cbv iota.
      Exists r st'.
      unfold DC3x, DC3_of. Exists k'.
      unfold local, lift1; simpl. normalize.
      unfold ref_api_res in Hst'. simpl in Hst'. apply andp_right; [apply prop_right; tauto |].
      unfold pws_pred; simpl. cancel.
  - (* a DDict *)
    assert (Pq: isptr q) by (destruct q; simpl in *; try contradiction; auto; subst; contradiction).
    rewrite if_false by auto.
    apply (pull_prop (A := ~ In q (map fst (dc_set st)))).
    { apply andp_left2.
      apply derives_trans with ((DD3x DENT gv q dd * dict_res (DD3x DENT) gv sh (dc_dict st) *
                                 set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st)) * TT); [cancel |].
      eapply derives_trans; [apply sepcon_derives; [apply (proj2 load3_set_ok DENT gv sh st q dd) | apply derives_refl] |].
      apply derives_trans with (!! (~ In q (map fst (dc_set st))) && TT * TT);
        [apply sepcon_derives; [apply andp_right; auto | auto] |].
      rewrite sepcon_andp_prop'. apply andp_left1; auto. }
    intros Hnin.
    unfold DC3x at 1, DC3_of. Intros k.
    match goal with Hx: base_rel3 st k |- _ => rename Hx into Hb end.
    match goal with Hx: dc_ss st <> ss_init -> _ |- _ => rename Hx into Hsr end.
    match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr end.
    match goal with Hx: ex_on3 SR st k |- _ => rename Hx into Hex end.
    apply (pull_prop (A := NoDup (map fst (c3_set k)))).
    { apply andp_left2. sep_apply (ctx_rep3_nodup DENT TABS gv d k). entailer!. }
    intros Hnd.
    apply (pull_prop (A := 0 <= sf_held (c3_s k) /\ 0 <= sf_inSize (c3_s k) /\ 0 <= sf_outSize (c3_s k) /\
                           par_ok (c3_par k))).
    { apply andp_left2. rewrite ctx_rep3_split. Intros. sep_apply (ctx_rest3k_props TABS gv d k). entailer!. }
    intros (Hk1 & Hk2 & Hk3 & Hpar).
    assert (Hset: c3_set k = dc_set st) by (destruct Hb as [_ [_ [E _]]]; exact E).
    assert (Hpar': c3_par k = dc_par st) by (destruct Hb as [_ [E _]]; exact E).
    assert (Hcur: set_cur_ok st) by (destruct Hb as [_ [_ [_ [_ [E _]]]]]; exact E).
    destruct (ref_mem_pre st k q Hb Hk1 Hk2 Hk3 Hpar) as [Hlm Hroom].
    destruct (ref_w_facts st k Hb Hk1 Hk2 Hk3 Hpar) as [Hw1 Hw2].
    assert (Hw3: 3 * set_new_bytes + 3 * sf_held (c3_s k) + dstream_size (2 ^ 31) <= dstream_size (ref_w k))
      by (assert (0 <= sf_given (c3_s k)) by (unfold sf_given; rewrite dctx_size_eq; lia); lia).
    unfold DD3x at 1, DD3_of, ddict_rep_at, ddict_struct, ddict_mem. Intros.
    rewrite l3s_dd_x_buf.
    change (dx_q (dd_x q dd)) with q. change (dx_raw (dd_x q dd)) with false. cbv iota.
    change (dict_id_of (dx_bytes (dd_x q dd))) with (dd_id dd).
    change (Tstruct _ZSTD_DDict_s noattr) with t_ddict.
    assert (HP: dd_props (dd_x q dd) (dd_buf dd)) by (unfold dd_props; repeat split; auto).
    assert (Hvb: is_pointer_or_null (ddb dd)).
    { unfold ddb. destruct (dd_xref dd); [reflexivity |]. destruct HP as [_ [_ [_ [_ [_ [Hb' _]]]]]].
      destruct Hb' as [Hb' | (-> & _)]; [destruct (dd_buf dd); try contradiction; exact I | simpl; auto]. }
    assert (Hrange: 0 <= dd_id dd <= Int.max_unsigned)
      by (apply l3s_dict_id_of_range; destruct HP as [_ [_ [Hok _]]]; exact Hok).
    destruct (Z.eq_dec (dp_multi (c3_par k)) 1) as [Hm | Hm].
    + rewrite Hset in Hnd.
      Exists (@nil ptr_witness, gv, d, k_mem k (ref_mem st k q (ref_w k)), q, dd)
        (dd_rest DENT gv (dd_x q dd) (dd_buf dd) * malloc_token Ews t_ddict q *
         (set_ids (dc_set st) -* (dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st)))).
      simpl. apply andp_right.
      * unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
        rewrite prop_true_andp.
        2: { split; [right; split; [auto | left; exact Hm] |].
             split; [split; [intros _ _; rewrite Hset; split; auto | split; [exact Hlm | split; [exact Hroom | exact I]]] |].
             split; [reflexivity | assumption]. }
        rewrite (veqb_ptr' _ Pq), Hm. simpl andb. cbv iota. rewrite Hset.
        sep_apply (ctx_rep3_ref_mem DENT TABS gv d st k q (ref_w k) (proj1 (base_rel3_mem _ _ Hb))).
        sep_apply (proj1 load3_set_ok DENT gv sh st Hcur Hnd).
        unfold ddid, dd_rest, pws_pred. change (dx_q (dd_x q dd)) with q. simpl. rewrite prop_true_andp by auto. cancel.
      * apply prop_right. intros rho'. normalize.
        rename x into r. rename x0 into k'.
        match goal with Hx: refddict_int_res _ _ _ _ _ |- _ => rename Hx into Hres end.
        destruct (ref_api_post SR gv BR st k q dd (ref_w k) r k' Hb Hbl Hsr Hbr Hex
                    ltac:(intros _; split; auto) Hw1 Hw3 Hres) as (st' & Hst' & Hb' & Hsr' & Hbr' & Hex').
        rewrite if_false by auto.
        rewrite (veqb_ptr' _ Pq), Hm. simpl andb. cbv iota. rewrite Hset.
        Exists r st'.
        unfold DC3x, DC3_of. Exists k'.
        unfold local, lift1; simpl. normalize.
        unfold ddid. Intros. sep_apply (dd_rebuild DENT gv q dd HP).
        sep_apply (modus_ponens_wand (set_ids (dc_set st))
                     (dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st))).
        unfold pws_pred; simpl.
        unfold ref_api_res in Hst'. simpl in Hst'. apply andp_right; [apply prop_right; tauto |].
        cancel.
    + assert (Hm': (dp_multi (c3_par k) =? 1) = false) by (apply Z.eqb_neq; exact Hm).
      Exists ([rdd_w q], gv, d, k_mem k (ref_mem st k q (ref_w k)), q, dd)
        (field_at Share.Rsh t_ddict (DOT _dictBuffer) (ddb dd) q * dd_rest DENT gv (dd_x q dd) (dd_buf dd) *
         field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (dd_id dd))) q * malloc_token Ews t_ddict q *
         (dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st))).
      simpl. apply andp_right.
      * unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
        rewrite prop_true_andp.
        2: { split; [right; split; [auto | right; apply rdd_wvp] |].
             split; [split; [intros _ Hc; contradiction | split; [exact Hlm | split; [exact Hroom | exact I]]] |].
             split; [reflexivity | assumption]. }
        rewrite (veqb_ptr' _ Pq), Hm'. simpl andb. cbv iota.
        sep_apply (ctx_rep3_ref_mem DENT TABS gv d st k q (ref_w k) (proj1 (base_rel3_mem _ _ Hb))).
        sep_apply (rdd_lend _ q Hvb).
        unfold dd_rest. change (dx_q (dd_x q dd)) with q. cancel.
      * apply prop_right. intros rho'. normalize.
        rename x into r. rename x0 into k'.
        match goal with Hx: refddict_int_res _ _ _ _ _ |- _ => rename Hx into Hres end.
        destruct (ref_api_post SR gv BR st k q dd (ref_w k) r k' Hb Hbl Hsr Hbr Hex
                    ltac:(intros _; split; auto) Hw1 Hw3 Hres) as (st' & Hst' & Hb' & Hsr' & Hbr' & Hex').
        rewrite if_false by auto.
        rewrite (veqb_ptr' _ Pq), Hm'. simpl andb. cbv iota.
        Exists r st'.
        unfold DC3x, DC3_of. Exists k'.
        unfold local, lift1; simpl. normalize.
        sep_apply (rdd_back _ q Hvb).
        sep_apply (dd_rebuild DENT gv q dd HP).
        unfold ref_api_res in Hst'. simpl in Hst'. apply andp_right; [apply prop_right; tauto |].
        cancel.
Qed.

End CM_Load3RefSub_1.
