(* FS3 one-shot: ZSTD_decompressDCtx = ZSTD_decompress_usingDDict(dctx, ..., ZSTD_getDDict(dctx)).
   Between the two calls the context's dictionary resources are lent to ZSTD_decompress_usingDDict: dctx_lend
   states what the body needs (the dictionary argument, the selection's resources, and how they come back);
   the cases are proved in O3DCtxCases*.v.  The context's allocator am lends its state (cm_have, out of the streaming
   fields) to ZSTD_getDDict and the selection, which may free the local DDict through it; the set (hs bytes of am)
   is lent to the selection.  After a stream (any dc_ss), ZSTD_decompressMultiFrame leaves streamStage at zdss_init
   (code fix F10): a new stream (Spec_api6.ss_next).
   From the configuration of a new context (Spec_api6.fresh_cfg: no dictionary, default parameters) ZSTD_getDDict
   returns NULL, so ZSTD_decompress_usingDDict runs without a dictionary argument and with the default parameters,
   where its exact result (FSSpecs3.os_match) is Spec_api6.oneshot_exact's. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base.
Local Open Scope logic.

Section CM_O3DCtxDef_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* what the representation of the DDict set gives *)
Definition hset_props (sp: val) (l: list (val * ddict_st)) : Prop :=
  (sp = nullval <-> l = nil) /\ Forall (fun e => isptr (fst e)) l /\ NoDup (map fst l).

Lemma set_bytes_nonneg (am: option cmem) (n: Z) : 0 <= n -> 0 <= set_bytes am n.
Proof. intros H. destruct am; simpl; [unfold sizeof; simpl; lia | lia]. Qed.

Lemma hset_rep_props (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  hset_rep am sp l hb |-- !! (hset_props sp l /\ 0 <= hb).
Proof.
  unfold hset_rep, hset_props. destruct (eq_dec sp nullval) as [E | E].
  - Intros. subst. apply prop_right. split; [tauto | split; [split; constructor | lia]].
  - Intros tp tbl. apply prop_right.
    match goal with H: hs_inv _ _ |- _ => destruct H as [_ [_ [_ [Hnd [_ [Hp _]]]]]] end.
    split; [split; intros; contradiction | split; [split; auto |]].
    match goal with H: hb = set_bytes _ _ |- _ => rewrite H end. apply set_bytes_nonneg, Zlength_nonneg.
Qed.

(* ---------- the streaming fields around a one-shot decoding ---------- *)

(* the streaming group without streamStage and the allocator's state (whose count of bytes depends on sf_held) *)
Definition sgroup_rest (p: val) (s: sfields) : mpred :=
  !! (0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
      Int.min_signed <= sf_nfp s <= Int.max_signed /\
      0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
      (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\
      (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s) /\ cmem_ok (sf_mem s)) &&
  (field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
   field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
   field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
   field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
   field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
   field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
   field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
   field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
   field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
   field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
   field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
   field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
   field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
   ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
   field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem s)) p *
   blk_tok (sf_mem s) (tarray tuchar (sizeof t_dctx)) p).

Lemma sgroup_take (p: val) (s: sfields) :
  sgroup p s |--
  !! (cmem_ok (sf_mem s) /\ 0 <= sf_held s /\ 0 <= sf_inSize s /\ 0 <= sf_outSize s) &&
  (field_at_ Ews t_dctx (DOT _streamStage) p * cm_have (sf_mem s) (sf_given s) * sgroup_rest p s).
Proof.
  unfold sgroup, mgroup, sgroup_rest. Intros. entailer!.
Qed.

(* the streaming group given back with streamStage = zdss_init and the other blocks' bytes h *)
Lemma sgroup_give (p: val) (s: sfields) (h: Z) : 0 <= h ->
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p *
  cm_have (sf_mem s) (sf_given s - sf_held s + h) * sgroup_rest p s |--
  sgroup p (sf_end_stage (sf_with_held s h)).
Proof.
  intros Hh. unfold sgroup, mgroup, sgroup_rest, sf_end_stage, sf_with_held, sf_given; simpl. Intros.
  replace (dctx_size + h + sf_inSize s + sf_outSize s)
    with (dctx_size + sf_held s + sf_inSize s + sf_outSize s - sf_held s + h) by lia.
  entailer!.
Qed.

Lemma cm_have_eq (am: option cmem) (h h': Z) : h = h' -> cm_have am h = cm_have am h'.
Proof. intros ->. reflexivity. Qed.

(* ---------- the allocator's bytes of the local DDict ---------- *)

Lemma ddx_held_nonneg (x: ddx) : 0 <= ddx_held x.
Proof.
  unfold ddx_held. destruct (dx_mem x); [| lia].
  pose proof (Zlength_nonneg (dx_bytes x)). destruct (ddx_copied x); unfold sizeof; simpl; lia.
Qed.

Lemma local_held_nonneg (d: dfields) : 0 <= local_held d.
Proof.
  unfold local_held. destruct (eq_dec (df_local d) nullval); [lia |].
  destruct (df_lx d) as [[x ?] |]; [apply ddx_held_nonneg | lia].
Qed.

(* the default allocator's local DDicts hold none of its bytes *)
Lemma local_held_none (d: dfields) : local_mem None d -> local_held d = 0.
Proof.
  unfold local_mem, local_held. intros H. destruct (eq_dec (df_local d) nullval) as [E | E]; [reflexivity |].
  destruct (df_lx d) as [[x b] |] eqn:Ex; [| reflexivity].
  destruct (H E) as [_ H2]. specialize (H2 x b eq_refl).
  unfold ddx_held. destruct (dx_mem x); [contradiction | reflexivity].
Qed.

Lemma getddict_local (d: dfields) :
  (local_held (snd (getddict_res d)) = local_held d \/ local_held (snd (getddict_res d)) = 0) /\
  (forall am, local_mem am d -> local_mem am (snd (getddict_res d))).
Proof.
  unfold getddict_res. destruct (df_uses d =? 0); [| destruct (df_uses d =? 1)]; simpl.
  - split; [right; reflexivity |]. intros am _ E. contradiction.
  - split; [left; reflexivity |]. intros am H. exact H.
  - split; [left; reflexivity |]. intros am H. exact H.
Qed.

(* the bytes of the dictionary fields after the lending (ZSTD_getDDict's, or a DDict of the set) *)
Lemma lend_local_held (k: cst3) (d': dfields) :
  (d' = snd (getddict_res (c3_dict k)) \/
   (sel_on (c3_par k) (c3_sp k) = true /\ exists q, In q (map fst (c3_set k)) /\ d' = switch_fields q)) ->
  0 <= local_held d' <= local_held (c3_dict k) /\
  (forall am, local_mem am (c3_dict k) -> local_mem am d').
Proof.
  pose proof (local_held_nonneg (c3_dict k)) as H0.
  intros [-> | [_ [q [_ ->]]]].
  - destruct (getddict_local (c3_dict k)) as [[E | E] H]; rewrite E; split; auto; lia.
  - assert (E: local_held (switch_fields q) = 0).
    { unfold local_held, switch_fields; simpl. destruct (eq_dec nullval nullval); [reflexivity | contradiction]. }
    rewrite E. split; [lia | intros am _ E'; contradiction].
Qed.

(* room for a stream once the dictionaries hold fewer bytes *)
Lemma mem_room_less (s: sfields) (h: Z) :
  mem_room s -> 0 <= h <= sf_held s -> mem_room (sf_end_stage (sf_with_held s h)).
Proof.
  unfold mem_room, sf_end_stage, sf_with_held; simpl. intros Hm Hh.
  destruct (sf_mem s); [destruct Hm; [left | right]; lia | lia].
Qed.

(* the facts about the context ZSTD_decompressDCtx starts from *)
Definition dctx_pre (W: list ptr_witness) (shk shd: share) (cap: Z) (dst: val) (st: dctx_st) (k: cst3) : Prop :=
  base_rel3 st k /\ hset_props (c3_sp k) (c3_set k) /\ dict_buf_ok W shk (dc_dict st) shd cap dst /\
  Forall (fun e => ddict_buf_ok W shk (snd e) shd cap dst) (dc_set st) /\
  readable_share shk /\ writable_share shd /\ dc_bl st = None /\ 0 <= cap.

(* the lending: the dictionary argument a of ZSTD_decompress_usingDDict (the DDict ZSTD_getDDict returned) and
   the set's table tbl (w = (a, tbl), chosen from the resources), and the rest Rf w *)
Definition lend_ok (W: list ptr_witness) (shk shd: share) (cap: Z) (dst: val) (s: list Z) (st: dctx_st) (k: cst3)
    (w: darg * list val) : Prop :=
  let '(a, tbl) := w in
  let d1 := snd (getddict_res (c3_dict k)) in
  let pr := c3_par k in let sp := c3_sp k in let l := c3_set k in
  darg_is_ddict a /\ darg_ddict a = fst (getddict_res (c3_dict k)) /\ darg_ok3 W a shd cap dst /\
  (sel_on pr sp = true -> msel_ok W d1 l a shk shd cap dst) /\
  (forall r out, bytes_ok s -> (is_error_code r = false -> r <= cap) ->
     (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out) ->
     (sel_on pr sp = true -> darg_ddict a <> nullval ->
        oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out) ->
     oneshot_dctx st s cap r out) /\
  (* the error codes, for a context without a DDict set (Spec_codes.oneshot_codes) *)
  (dc_set st = nil -> forall r,
     (sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r) ->
     oneshot_codes (dmode_of (dc_par st)) sel_none (dictref_model (dc_dict st)) s cap r) /\
  (* a NULL DDict is passed as no dictionary argument at all (the exact result needs DA_none) *)
  (darg_ddict a = nullval -> a = DA_none).

(* am: the context's allocator, hb the bytes it has given out besides the local DDict, hs the set's *)
Definition lend_pre (DENT: dent_pred) (gv: globals) (p: val) (shk: share) (st: dctx_st) (k: cst3)
    (am: option cmem) (hb hs: Z) : mpred :=
  mem_mgr gv * dgroup DENT gv p (snd (getddict_res (c3_dict k))) *
  cm_have am (hb + local_held (snd (getddict_res (c3_dict k)))) * hset_rep am (c3_sp k) (c3_set k) hs *
  dict_res (DD3x DENT) gv shk (dc_dict st) * set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st).

Definition lend_post (DENT: dent_pred) (gv: globals) (p: val) (shk: share) (st: dctx_st) (k: cst3)
    (am: option cmem) (hb hs: Z) (d': dfields) : mpred :=
  mem_mgr gv * dgroup DENT gv p d' * cm_have am (hb + local_held d') * hset_rep am (c3_sp k) (c3_set k) hs *
  dict_res (DD3x DENT) gv shk (dc_dict st) * set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st).

(* what ZSTD_decompress_usingDDict holds: the selection's resources with the dictionary fields d', the argument's
   (relative to the fields d it was called with) *)
Definition lend_mid (DENT: dent_pred) (gv: globals) (p: val) (shk: share) (k: cst3) (am: option cmem) (hb: Z)
    (d d': dfields) (w: darg * list val) : mpred :=
  let '(a, tbl) := w in
  msel_res DENT gv p (c3_par k) (c3_sp k) d' (c3_set k) tbl shk a am hb * darg_res3 DENT gv (c3_par k) (c3_sp k) d a.

Definition dctx_lend (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (shk shd: share) (cap: Z)
    (dst: val) (s: list Z) (st: dctx_st) (k: cst3) (am: option cmem) (hb hs: Z) : Prop :=
  let d1 := snd (getddict_res (c3_dict k)) in
  exists Rf: darg * list val -> mpred,
    (lend_pre DENT gv p shk st k am hb hs |--
       EX w: darg * list val, !! lend_ok W shk shd cap dst s st k w && (lend_mid DENT gv p shk k am hb d1 d1 w * Rf w)) /\
    (forall w d', lend_ok W shk shd cap dst s st k w ->
       (d' = d1 \/ (sel_on (c3_par k) (c3_sp k) = true /\ exists q, In q (map fst (c3_set k)) /\ d' = switch_fields q)) ->
       dict_rel3 (after_use st) d' /\
       (lend_mid DENT gv p shk k am hb d1 d' w * Rf w |-- lend_post DENT gv p shk st k am hb hs d')).

(* ZSTD_getDDict's precondition *)
Definition getddict_pre (d: dfields) : Prop :=
  (df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1) /\ (df_uses d <> 0 -> is_pointer_or_null (df_ddict d)).

(* ---------- the abstract state afterwards ---------- *)

Lemma after_use_parts st :
  dc_stable (after_use st) = dc_stable st /\ dc_par (after_use st) = dc_par st /\
  dc_set (after_use st) = dc_set st /\ dc_ss (after_use st) = dc_ss st /\ dc_bl (after_use st) = dc_bl st /\
  (dc_dict (after_use st) = None \/ dc_dict (after_use st) = dc_dict st).
Proof.
  unfold after_use. destruct (dc_dict st) as [[? ? o ?] | ] eqn:E; simpl; [destruct o | ]; simpl; rewrite ?E;
    repeat split; auto.
Qed.

(* the context after the one-shot decoding: its frame state, dictionary fields d', streamStage zdss_init (F10),
   the other blocks' bytes h and uninitialised tables with litExtraBuffer holding lxb *)
Definition k_after (k: cst3) (fs: fstate) (d': dfields) (h: Z) (lxb: list Z) : cst3 :=
  c3_with_dict (c3_with_fs (c3_with_s k (sf_end_stage (sf_with_held (c3_s k) h))) fs (TUninit lxb)) d'.

Lemma base_rel3_after_use (st: dctx_st) (k: cst3) (fs: fstate) (d': dfields) (h: Z) (lxb: list Z) :
  base_rel3 st k -> dc_bl st = None -> dict_rel3 (after_use st) d' -> fp_ok (fs_fParams fs) ->
  local_mem (sf_mem (c3_s k)) d' -> 0 <= h <= sf_held (c3_s k) ->
  base_rel3 (after_use st) (k_after k fs d' h lxb).
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [Hf [H6 [H7 Hm]]]]]]]] Hb Hd Hfp Hl Hh.
  destruct (after_use_parts st) as [E1 [E2 [E3 [E4 [E5 E6]]]]].
  unfold base_rel3, k_after; simpl. rewrite E1, E2, E3, E4, E5.
  split3; auto. split; auto. split; [exact Hd | ]. split.
  - unfold set_cur_ok. rewrite E3. destruct E6 as [E6 | E6]; rewrite E6; [intros; discriminate | exact H5].
  - split; [exact Hfp | ]. split.
    { unfold stage_rel3 in *; simpl. destruct H6 as [H6a H6b]. split; [exact H6a |].
      intros E. split; [reflexivity | apply (H6b E)]. }
    split; [intros E; contradiction | ].
    assert (Em: dc_mem (after_use st) = dc_mem st)
      by (unfold after_use; destruct (dc_dict st) as [[? ? o ?] | ]; [destruct o | ]; reflexivity).
    destruct Hm as [Hm1 [Hm2 Hm3]]. unfold mem_rel3; simpl. rewrite Em.
    split; [exact Hm1 | split; [apply mem_room_less; auto | exact Hl]].
Qed.

Lemma after_use_set_ss (st: dctx_st) (ss: sstate) : after_use (set_ss st ss) = set_ss (after_use st) ss.
Proof.
  destruct st as [dd ? ? ? ? ? ? ?]. unfold after_use, set_ss, set_dict; simpl.
  destruct dd as [[? ? o ?] | ]; [destruct o | ]; reflexivity.
Qed.

Lemma ss_restart_not_init : ss_restart <> ss_init.
Proof. unfold ss_restart, ss_init. intros E. inversion E. Qed.

(* after a stream, the new one (ss_next) on the context with streamStage zdss_init and the bound raised as set_ss
   raises the abstract one *)
Lemma base_rel3_restart (st: dctx_st) (k: cst3) :
  base_rel3 st k -> dc_ss st <> ss_init -> dc_bl st = None ->
  base_rel3 (set_ss st (ss_next (dc_ss st))) (c3_raise k (dp_wmax (dc_par st))).
Proof.
  intros [H1 [H2 [H3 [H4 [H5 [Hf [H6 [H7 Hm]]]]]]]] Hi Hb.
  unfold base_rel3, c3_raise; simpl.
  split3; auto. split; auto. split; [exact H4 |]. split; [exact H5 |]. split; [exact Hf |]. split.
  - unfold stage_rel3 in *; simpl. destruct H6 as [H6a H6b].
    unfold ss_next. destruct (ss_err (dc_ss st)) eqn:Ee.
    + split; [intros E; rewrite Ee in E; discriminate | intros E; contradiction].
    + split; [intros _; exact (H6a eq_refl) | intros E; exfalso; exact (ss_restart_not_init E)].
  - split; [intros E; contradiction |]. exact (mem_rel3_raise st k _ Hm).
Qed.

(* ---------- the body, given the lending ---------- *)

(* hides an equation of a variable from VST's subst *)
Definition o3_hide (P: Prop) : Prop := P.

Section Body.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.

Definition dctx_cases_ok : Prop :=
  forall gv p W shk shd cap dst s st k am hb hs,
    dctx_pre W shk shd cap dst st k ->
    getddict_pre (c3_dict k) /\ dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.

Lemma body_decompressDCtx3_of :
  dctx_cases_ok ->
  body_ok (FS3_G DENT TABS SR BR) (ZSTD_decompressDCtx_spec (DC3x DENT TABS SR BR) (DD3x DENT)).
Proof.
  intros Hcases.
  exists f_ZSTD_decompressDCtx; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  unfold DC3x, DC3_of, ctx_rep3, ctx_body3. Intros k.
  match goal with H: base_rel3 st k |- _ => rename H into Hbr end.
  assert_PROP (hset_props (c3_sp k) (c3_set k) /\
               0 <= sf_held (c3_s k) - local_held (c3_dict k)) as Hhs.
  { sep_apply (hset_rep_props (sf_mem (c3_s k)) (c3_sp k) (c3_set k)
                 (sf_held (c3_s k) - local_held (c3_dict k))). entailer!. }
  destruct Hhs as [Hhs Hhs0].
  sep_apply (sgroup_take d (c3_s k)). Intros.
  assert (Hcm: cmem_ok (sf_mem (c3_s k)) /\ 0 <= sf_held (c3_s k) /\ 0 <= sf_inSize (c3_s k) /\
               0 <= sf_outSize (c3_s k)) by tauto.
  assert (Hpre: dctx_pre W shk shd cap dst st k) by (unfold dctx_pre; tauto).
  pose proof (base_rel3_mem _ _ Hbr) as [Hm1 [Hm2 Hm3]].
  remember (sf_given (c3_s k) - local_held (c3_dict k)) as hb eqn:Ehb.
  assert (Hhb: 0 <= hb).
  { subst hb. unfold sf_given. destruct Hcm as (_ & _ & Hi & Ho). rewrite dctx_size_eq. lia. }
  rewrite (cm_have_eq (sf_mem (c3_s k)) (sf_given (c3_s k)) (hb + local_held (c3_dict k))) by lia.
  assert (Hhide: o3_hide (hb = sf_given (c3_s k) - local_held (c3_dict k))) by exact Ehb. clear Ehb.
  destruct (Hcases gv d W shk shd cap dst s st k (sf_mem (c3_s k)) hb
              (sf_held (c3_s k) - local_held (c3_dict k)) Hpre) as [[Hu Hpn] Hl].
  forward_call (gv, d, c3_dict k, sf_mem (c3_s k), hb).
  destruct Hl as [Rf [Hlend Hback]].
  unfold lend_pre in Hlend. sep_apply Hlend.
  Intros w. destruct w as [a tbl].
  match goal with H: lend_ok _ _ _ _ _ _ _ _ _ |- _ => pose proof H as Hok; destruct H as [Ha1 [Ha2 [Ha3 [Ha4 [Ha5 [Ha6 Ha7]]]]]] end.
  unfold lend_mid.
  rewrite <- Ha2.
  assert (Hsm: sel_mem (c3_par k) (c3_sp k) (snd (getddict_res (c3_dict k))) (sf_mem (c3_s k)) hb).
  { intros _. split; [apply (proj2 (getddict_local (c3_dict k))); exact Hm3 | split; [tauto | exact Hhb]]. }
  forward_call (W, gv, d, c3_fs k, c3_tabs k, c3_par k, c3_sp k, snd (getddict_res (c3_dict k)), c3_set k, tbl,
                shk, shd, dst, cap, shs, src, s, a, sf_mem (c3_s k), hb).
  { cancel. }
  Intros vret. destruct vret as [[[[r out] fs'] d'] lxb']. simpl fst in *; simpl snd in *.
  match goal with H: d' = _ \/ _ |- _ => pose proof H as Hd'; destruct (Hback (a, tbl) d' Hok H) as [Hrel Hent] end.
  unfold lend_mid, lend_post in Hent.
  sep_apply Hent.
  forward.
  unfold o3_hide in Hhide. subst hb.
  destruct (lend_local_held k d' Hd') as [Hld' Hlm'].
  remember (sf_held (c3_s k) - local_held (c3_dict k) + local_held d') as h' eqn:Eh'.
  assert (Hh': 0 <= h' <= sf_held (c3_s k)) by (subst h'; lia).
  rewrite (cm_have_eq (sf_mem (c3_s k)) (sf_given (c3_s k) - local_held (c3_dict k) + local_held d')
             (sf_given (c3_s k) - sf_held (c3_s k) + h'))
    by (subst h'; lia).
  sep_apply (sgroup_give d (c3_s k) h' ltac:(lia)).
  assert (Hfp: fp_ok (fs_fParams fs')) by (destruct Hbr as [_ [_ [_ [_ [_ [Hf _]]]]]]; match goal with H: fp_ok _ -> fp_ok (fs_fParams fs') |- _ => exact (H Hf) end).
  assert (Hb': base_rel3 (after_use st) (k_after k fs' d' h' lxb'))
    by (apply base_rel3_after_use; auto; apply Hlm'; exact Hm3).
  assert (Ho: oneshot_dctx st s (Zlength out) r out) by (apply Ha5; auto).
  assert (Hco: dc_set st = nil ->
            oneshot_codes (dmode_of (dc_par st)) sel_none (dictref_model (dc_dict st)) s (Zlength out) r)
    by (intros E; apply Ha6; auto).
  (* the exact result: a new context's configuration has no dictionary (ZSTD_getDDict returns NULL, the argument is
     DA_none) and the default parameters *)
  assert (Hex: oneshot_exact st s (Zlength out) r out).
  { intros (Hdn & Hpd & Hsn & _). right.
    assert (Ea: a = DA_none).
    { apply Ha7. rewrite Ha2.
      destruct Hbr as (_ & _ & _ & Hd & _). destruct Hd as [Hd | [Hd _]]; [ | contradiction].
      rewrite Hdn in Hd. destruct Hd as [Hu0 _]. unfold getddict_res. rewrite Hu0. reflexivity. }
    assert (Ep: c3_par k = dparams_dflt) by (destruct Hbr as (_ & Hp & _); rewrite Hp; exact Hpd).
    match goal with H: a = DA_none -> c3_par k = dparams_dflt -> os_match _ _ _ _ |- _ =>
      exact (H Ea Ep) end. }
  assert (Ehs: sf_held (c3_s k) - local_held (c3_dict k) = h' - local_held d') by lia.
  rewrite Ehs.
  destruct (after_use_parts st) as [_ [E2 [_ [E4 [E5 _]]]]].
  destruct (Classical_Prop.classic (dc_ss st = ss_init)) as [Ei | Ei].
  - (* before any stream: the one-shot's state *)
    assert (Hsr: dc_ss (set_ex (after_use st) false) <> ss_init -> ss_err (dc_ss (set_ex (after_use st) false)) = false ->
                 SR gv (set_ex (after_use st) false) (k_after k fs' d' h' lxb') \/
                 (dc_ss (set_ex (after_use st) false) = ss_restart /\ sf_stage (c3_s (k_after k fs' d' h' lxb')) = 0))
      by (cbn [set_ex dc_ss]; rewrite E4; intros E; contradiction).
    assert (Hbl: forall ba, dc_bl (set_ex (after_use st) false) = Some ba ->
              BR (c3_par (k_after k fs' d' h' lxb')) ba (c3_fs (k_after k fs' d' h' lxb')) (c3_tabs (k_after k fs' d' h' lxb'))
                 (sf_hbuf (c3_s (k_after k fs' d' h' lxb'))))
      by (cbn [set_ex dc_bl]; rewrite E5; intros ba E; congruence).
    assert (Had: oneshot_after st (set_ex (after_use st) false)) by (left; split; [exact Ei | left; reflexivity]).
    assert (Hex3: ex_on3 SR (set_ex (after_use st) false) (k_after k fs' d' h' lxb')) by (apply ex_on3_noex; reflexivity).
    Exists r out (set_ex (after_use st) false). unfold DC3x, DC3_of, ctx_rep3, ctx_body3.
    Exists (k_after k fs' d' h' lxb'). unfold k_after. simpl.
    entailer!.
  - (* after a stream: a new one (or the failed one kept), the bound raised *)
    set (ss' := ss_next (dc_ss st)).
    set (w := dp_wmax (dc_par st)).
    assert (Hb2: base_rel3 (set_ex (after_use (set_ss st ss')) false) (c3_raise (k_after k fs' d' h' lxb') w)).
    { change (base_rel3 (after_use (set_ss st ss')) (c3_raise (k_after k fs' d' h' lxb') w)). rewrite after_use_set_ss. subst ss' w. rewrite <- E4, <- E2.
      apply base_rel3_restart; auto; rewrite ?E4, ?E5; auto. }
    assert (Hsr: dc_ss (set_ex (after_use (set_ss st ss')) false) <> ss_init ->
                 ss_err (dc_ss (set_ex (after_use (set_ss st ss')) false)) = false ->
                 SR gv (set_ex (after_use (set_ss st ss')) false) (c3_raise (k_after k fs' d' h' lxb') w) \/
                 (dc_ss (set_ex (after_use (set_ss st ss')) false) = ss_restart /\
                  sf_stage (c3_s (c3_raise (k_after k fs' d' h' lxb') w)) = 0)).
    { cbn [set_ex dc_ss]. rewrite after_use_set_ss. destruct (after_use_parts (set_ss st ss')) as [_ [_ [_ [E4' _]]]].
      rewrite <- after_use_set_ss, E4'. simpl. subst ss'. unfold ss_next.
      destruct (ss_err (dc_ss st)) eqn:Ee; intros _ E; [rewrite Ee in E; discriminate | right; split; reflexivity]. }
    assert (Hbl: forall ba, dc_bl (set_ex (after_use (set_ss st ss')) false) = Some ba ->
              BR (c3_par (c3_raise (k_after k fs' d' h' lxb') w)) ba (c3_fs (c3_raise (k_after k fs' d' h' lxb') w))
                 (c3_tabs (c3_raise (k_after k fs' d' h' lxb') w)) (sf_hbuf (c3_s (c3_raise (k_after k fs' d' h' lxb') w)))).
    { cbn [set_ex dc_bl]. rewrite after_use_set_ss. destruct (after_use_parts (set_ss st ss')) as [_ [_ [_ [_ [E5' _]]]]].
      rewrite <- after_use_set_ss, E5'. simpl. intros ba E; congruence. }
    assert (Had: oneshot_after st (set_ex (after_use (set_ss st ss')) false)) by (right; split; [exact Ei | left; reflexivity]).
    sep_apply (sgroup_raise d (sf_end_stage (sf_with_held (c3_s k) h')) w).
    rewrite <- (hset_rep_raise (sf_mem (c3_s k)) w (c3_sp k) (c3_set k) (h' - local_held d')).
    assert (Hex3: ex_on3 SR (set_ex (after_use (set_ss st ss')) false) (c3_raise (k_after k fs' d' h' lxb') w))
      by (apply ex_on3_noex; reflexivity).
    Exists r out (set_ex (after_use (set_ss st ss')) false). unfold DC3x, DC3_of, ctx_rep3, ctx_body3.
    Exists (c3_raise (k_after k fs' d' h' lxb') w). unfold k_after, c3_raise. simpl.
    entailer!.
Qed.

End Body.

End CM_O3DCtxDef_1.
