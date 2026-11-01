(* FS3 one-shot frames: the end of the frame (statements 11..17: content size, checksum, results) (port of v2 body_frame.v's fr_end_ok). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Require Import Zstd.proof.dec.v3.FS.frames.Frame3_codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame Zstd.proof.model.ExFrameFacts.
Local Open Scope logic.

(* helpers of fr_end_ok *)
Ltac fe_ff :=
  unfold frame_fields, fr_fs, fh_val;
  cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
       fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize
       fs_isFrameDecompression fs_dictID fs_ddictIsCold]; cancel.

Section CM_Frame3_end_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma fe_sub_pp: forall q a c, isptr q ->
  force_val (sem_sub_pp tuchar (offset_val a q) (offset_val c q)) = Vlong (Int64.repr (a - c)).
Proof.
  intros q a c Hq. destruct q; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma fe_sameblock: forall q a c, isptr q -> is_true (sameblock (offset_val a q) (offset_val c q)).
Proof.
  intros q a c Hq. destruct q; try contradiction. unfold sameblock; simpl.
  destruct (peq b b); [reflexivity | contradiction].
Qed.

Lemma fe_le4_range: forall s i, bytes_ok s -> 0 <= i -> i + 4 <= Zlength s -> 0 <= le_field s i 4 < 2 ^ 32.
Proof.
  intros s0 i Hs Hi Hl. unfold le_field.
  assert (E: slice s0 i 4 = sublist i (i + 4) s0).
  { unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia. }
  rewrite E. pose proof (le_value_range (sublist i (i + 4) s0)) as R.
  rewrite Zlength_sublist in R by lia. replace (8 * (i + 4 - i))%Z with 32 in R by lia.
  apply R. eapply Forall_impl; [ | apply Forall_sublist; exact Hs]. intros a Ha. unfold is_byte in Ha. rep_lia.
Qed.

Lemma fe_win_split: forall sh N c off s0 b,
  field_compatible (tarray tuchar N) [] b -> 0 <= off -> off + Zlength s0 <= N -> Zlength c = N ->
  sublist off (off + Zlength s0) c = zbytes s0 ->
  data_at sh (tarray tuchar N) c b =
  (data_at sh (tarray tuchar off) (sublist 0 off c) b *
   data_at sh (tarray tuchar (Zlength s0)) (zbytes s0) (offset_val off b) *
   data_at sh (tarray tuchar (N - (off + Zlength s0))) (sublist (off + Zlength s0) N c)
     (offset_val (off + Zlength s0) b))%logic.
Proof.
  intros sh N c off s0 b Hfc Hoff Hn Hc Hw. pose proof (Zlength_nonneg s0).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s0) c b) by lia.
  rewrite !field_address0_offset.
  - simpl. rewrite Hw. replace (off + Zlength s0 - off) with (Zlength s0) by lia.
    rewrite !Z.mul_1_l. reflexivity.
  - apply (field_compatible0_cons_Tarray _ _ N noattr [] b tuchar); [reflexivity | exact Hfc | lia].
  - apply (field_compatible0_cons_Tarray _ _ N noattr [] b tuchar); [reflexivity | exact Hfc | lia].
Qed.

Lemma fe_win_merge: forall sh N c off s0 b,
  field_compatible (tarray tuchar N) [] b -> 0 <= off -> off + Zlength s0 <= N -> Zlength c = N ->
  sublist off (off + Zlength s0) c = zbytes s0 ->
  (data_at sh (tarray tuchar off) (sublist 0 off c) b *
   data_at sh (tarray tuchar (Zlength s0)) (zbytes s0) (offset_val off b) *
   data_at sh (tarray tuchar (N - (off + Zlength s0))) (sublist (off + Zlength s0) N c)
     (offset_val (off + Zlength s0) b))%logic |--
  data_at sh (tarray tuchar N) c b.
Proof. intros. rewrite (fe_win_split sh N c off s0 b) by auto. apply derives_refl. Qed.

Lemma fe_ck_iff: forall a m, 0 <= a < 2 ^ 32 ->
  (Int.repr a = Int.repr (Int64.unsigned (Int64.repr m)) <-> a = m mod 2 ^ 32).
Proof.
  intros a m Ha.
  assert (E: Int.unsigned (Int.repr (Int64.unsigned (Int64.repr m))) = m mod 2 ^ 32).
  { rewrite Int.unsigned_repr_eq, Int64.unsigned_repr_eq.
    change Int.modulus with (2 ^ 32). change Int64.modulus with (2 ^ 64).
    symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]. }
  split; intro H.
  - apply (f_equal Int.unsigned) in H. rewrite Int.unsigned_repr in H by rep_lia. congruence.
  - rewrite <- (Int.repr_unsigned (Int.repr (Int64.unsigned (Int64.repr m)))). rewrite E, H. reflexivity.
Qed.


Lemma fe_frame_res3: forall md sel dm0 s0 hs0 h0 j0 out0 cap oc0 d k4,
  fr_hdr3 md sel dm0 s0 hs0 h0 ->
  (forall o k, fr_DB dm0 h0 s0 hs0 = Some (o, k) -> o = out0 /\ k = j0) ->
  fr_RE dm0 h0 s0 hs0 j0 out0 -> 0 <= hs0 + j0 <= Zlength s0 ->
  (fh_contentSize h0 = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out0 = fh_contentSize h0) ->
  k4 = (if fh_checksumFlag h0 =? 1 then 4 else 0) ->
  (fh_checksumFlag h0 = 1 ->
     hs0 + j0 + 4 <= Zlength s0 /\ (md_ignore md = false -> le_field s0 (hs0 + j0) 4 = xxh64 out0 0 mod 2 ^ 32)) ->
  sublist d (d + Zlength out0) oc0 = zbytes out0 ->
  is_error_code (Zlength out0) = false ->
  frame_res3 md dm0 s0 cap (Zlength out0) oc0 d (hs0 + j0 + k4).
Proof.
  intros md sel dm0 s0 hs0 h0 j0 out0 cap oc0 d k4 Hh Hdb Hre Hj Hcsz Hk4 Hck Hsub Herr.
  unfold frame_res3. destruct (decode_frame_m md dm0 no_wlim s0) eqn:Hd.
  - destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh Hd) as (k & Hk & _ & Hc).
    apply Hdb in Hk as [-> ->].
    split; [ | intro; congruence].
    intros _. split; [reflexivity | split; [exact Hsub | ]].
    subst k4. destruct (fh_checksumFlag h0 =? 1); [destruct Hc as (_ & _ & ->) | subst]; lia.
  - exfalso. exact (fr_frame_hdr3_any _ _ _ _ _ _ Hh Hd).
  - exfalso. destruct (fr_frame_ck3_any _ _ _ _ _ _ Hh Hd) as (c & k & Hk & Hc1 & Hig & _ & _ & Hne).
    apply Hdb in Hk as [-> ->]. destruct (Hck Hc1) as (_ & Heq). apply Hne, Heq, Hig.
  - (* a refused frame: the C checked the content size and that the checksum is there *)
    intros Hr. exfalso. destruct (fr_refused_blocks3 _ _ _ _ _ _ Hh Hr) as [f0 Hf0].
    destruct (Hre f0 Hf0) as [[Hu Hm] | [Hc1 Hlt]].
    + destruct Hcsz as [E | E]; [contradiction | ]. apply Hm. rewrite Z.mod_small; [exact E | ].
      unfold is_error_code in Herr. apply Z.ltb_ge in Herr. pose proof (Zlength_nonneg out0). lia.
    + destruct (Hck Hc1) as (Hl4 & _). unfold fr_t in Hlt. rewrite Zlength_sublist in Hlt by lia. lia.
Qed.

(* frame_codes3 at the end of the frame (the blocks decoded to out0, ending at j0):
   - the success: no error, and a checksum-refused frame cannot reach it (the checksum matched or is ignored); *)
Lemma fe_codes_ok: forall md sel dm0 s0 hs0 h0 j0 out0 cap r,
  fr_hdr3 md sel dm0 s0 hs0 h0 ->
  (forall o k, fr_DB dm0 h0 s0 hs0 = Some (o, k) -> o = out0 /\ k = j0) ->
  (fh_checksumFlag h0 = 1 ->
     hs0 + j0 + 4 <= Zlength s0 /\ (md_ignore md = false -> le_field s0 (hs0 + j0) 4 = xxh64 out0 0 mod 2 ^ 32)) ->
  is_error_code r = false ->
  frame_codes3 md dm0 s0 cap r.
Proof.
  intros md sel dm0 s0 hs0 h0 j0 out0 cap r Hh Hdb Hck Hr. split.
  - intros c sz _ _ Hx. congruence.
  - intros Hd. exfalso. destruct (fr_frame_ck3_any _ _ _ _ _ _ Hh Hd) as (c & k & Hk & Hc1 & Hig & _ & _ & Hne).
    apply Hdb in Hk as [-> ->]. destruct (Hck Hc1) as (_ & Heq). apply Hne, Heq, Hig.
Qed.

(* - the content size check fails: the model decodes nothing (its frames have the declared size); *)
Lemma fe_codes_cs: forall md sel dm0 s0 hs0 h0 j0 out0 cap r,
  fr_hdr3 md sel dm0 s0 hs0 h0 ->
  (forall o k, fr_DB dm0 h0 s0 hs0 = Some (o, k) -> o = out0 /\ k = j0) ->
  ~ (fh_contentSize h0 = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out0 = fh_contentSize h0) ->
  frame_codes3 md dm0 s0 cap r.
Proof.
  intros md sel dm0 s0 hs0 h0 j0 out0 cap r Hh Hdb Hcs. apply fr_codes_none.
  - intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh Hd) as (k & Hk & Hc & _).
    apply Hdb in Hk as [-> _]. exact (Hcs Hc).
  - intros Hd. destruct (fr_frame_ck3_any _ _ _ _ _ _ Hh Hd) as (c & k & Hk & _ & _ & Hc & _).
    apply Hdb in Hk as [-> _]. exact (Hcs Hc).
Qed.

(* - the checksum exits return checksum_wrong; the model does not decode the frame there *)
Lemma fe_codes_ck: forall md dm0 s0 cap,
  (forall c sz, decode_frame_m md dm0 no_wlim s0 = FOk c sz -> False) ->
  frame_codes3 md dm0 s0 cap (Int64.unsigned (Int64.repr (-22))).
Proof.
  intros md dm0 s0 cap Hok. split.
  - intros c sz Hd. exfalso. exact (Hok c sz Hd).
  - intros _ c _ _. exact err_code_ck.
Qed.

(* ---------- the exact model at the end of the frame (ExFrameFacts.x_fend) ---------- *)

(* frame_exact of an error return, when the model refuses the frame *)
Lemma fe_exact_none: forall ts s0 cap r oc' d k lxb',
  is_error_code r = true -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s0 cap = None ->
  frame_exact ts s0 cap r oc' d k lxb'.
Proof. intros ts s0 cap r oc' d k lxb' Hr Hx. unfold frame_exact. rewrite Hx. exact Hr. Qed.

(* frame_exact of the success return: the model's content c written at d, the bytes k, its final state's
   litExtraBuffer *)
Lemma fe_exact_some: forall ts s0 cap c k ex oc' d,
  x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s0 cap = Some (c, k, ex) ->
  sublist d (d + Zlength c) oc' = zbytes c ->
  frame_exact ts s0 cap (Zlength c) oc' d k (x_lxb xhuf ex).
Proof. intros ts s0 cap c k ex oc' d Hx Hs. unfold frame_exact. rewrite Hx. auto. Qed.

(* the C's content size check fails: so does the model's *)
Lemma fe_fend_cs: forall (h0: frame_header) s0 hs0 out k (st': xstate),
  ~ (fh_contentSize h0 = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h0) ->
  x_fend xstate h0 s0 hs0 out k st' = None.
Proof.
  intros h0 s0 hs0 out k st' H. unfold x_fend.
  destruct (Z.eqb_spec (fh_contentSize h0) ZSTD_CONTENTSIZE_UNKNOWN); [tauto | ].
  destruct (Z.eqb_spec (Zlength out) (fh_contentSize h0)); [tauto | ]. reflexivity.
Qed.

(* the checksum is missing (fewer than 4 bytes after the last block) *)
Lemma fe_fend_short: forall (h0: frame_header) s0 hs0 out k (st': xstate),
  fh_checksumFlag h0 = 1 -> Zlength s0 - hs0 - k < 4 -> x_fend xstate h0 s0 hs0 out k st' = None.
Proof.
  intros h0 s0 hs0 out k st' Hc Hl. unfold x_fend.
  destruct (_ && _)%bool; [reflexivity | ]. rewrite Hc, Z.eqb_refl.
  destruct (Z.ltb_spec (Zlength s0 - hs0 - k) 4); [reflexivity | lia].
Qed.

(* the checksum does not match *)
Lemma fe_fend_ck: forall (h0: frame_header) s0 hs0 out k (st': xstate),
  fh_checksumFlag h0 = 1 -> le_field s0 (hs0 + k) 4 <> xxh64 out 0 mod 2 ^ 32 ->
  x_fend xstate h0 s0 hs0 out k st' = None.
Proof.
  intros h0 s0 hs0 out k st' Hc Hn. unfold x_fend.
  destruct (_ && _)%bool; [reflexivity | ]. rewrite Hc, Z.eqb_refl.
  destruct (_ <? 4); [reflexivity | ].
  destruct (Z.eqb_spec (le_field s0 (hs0 + k) 4) (xxh64 out 0 mod 2 ^ 32)); [contradiction | reflexivity].
Qed.

(* both checks pass: the frame ends after the checksum, if any *)
Lemma fe_fend_ok: forall (h0: frame_header) s0 hs0 out k (st': xstate),
  (fh_contentSize h0 = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h0) ->
  (fh_checksumFlag h0 = 0 \/ fh_checksumFlag h0 = 1) ->
  (fh_checksumFlag h0 = 1 -> hs0 + k + 4 <= Zlength s0 /\ le_field s0 (hs0 + k) 4 = xxh64 out 0 mod 2 ^ 32) ->
  x_fend xstate h0 s0 hs0 out k st' = Some (out, hs0 + k + (if fh_checksumFlag h0 =? 1 then 4 else 0), st').
Proof.
  intros h0 s0 hs0 out k st' Hcs Hf Hck. unfold x_fend.
  replace (negb (fh_contentSize h0 =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h0))%bool
    with false by (destruct Hcs as [E | E]; rewrite E, Z.eqb_refl; [reflexivity | symmetry; apply andb_false_r]).
  destruct Hf as [E | E]; rewrite E; cbn [Z.eqb Pos.eqb].
  - rewrite Z.add_0_r. reflexivity.
  - destruct (Hck E) as [Hl Hx]. destruct (Z.ltb_spec (Zlength s0 - hs0 - k) 4); [lia | ].
    rewrite Hx, Z.eqb_refl. reflexivity.
Qed.

(* an error return of the end (v2 errret0, with the dictionary fields d1 and the selection's resources) *)
Ltac errret3 rr oc' fs' ts :=
  match goal with
  | HT: TABS_OK ?T, HC: fr_ctx ?W ?fs ?ox ?dm ?e ?osh ?obase ?oN ?oc ?od ?ocap ?ish ?ibase ?iN ?ic ?ioff ?s ?pr ?dsp ?d ?l ?tbl ?lent ?h ?hs ?d1
    |- context [?T ?gv ?p ?ox _] =>
  match goal with |- context [fr_selR ?DENT _ _ _ _ _ _ ?xq _ ?am ?hb _] =>
  Exists rr oc' fs' 0 d1 (ts_lxb ts);
  rewrite Z.add_0_r, Z.sub_0_r; try rewrite Int64.repr_unsigned;
  sep_apply (HT gv p ox ts);
  sep_apply (fr_selR_post DENT W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s pr dsp d l tbl xq lent am hb h hs d1 HC);
  try sep_apply (zg_fold gv); unfold fcore3, cfg_fmt, cfg_lit; entailer!;
  repeat match goal with
  | |- _ /\ _ => split
  | |- is_error_code _ = false -> _ =>
      let Hx := fresh "Hx" in intro Hx; first [vm_compute in Hx; discriminate Hx | congruence]
  | |- frame_res3 _ _ _ _ _ _ _ _ => apply fr_err3; [first [reflexivity | assumption] | ]
  | |- dict_after _ _ _ _ _ => assumption
  | |- dict_sel _ _ _ _ _ _ _ => assumption
  | |- frame_codes3 _ _ _ _ _ => assumption
  | |- fp_ok _ -> fp_ok _ => intros _; eapply fr_fp; exact HC
  | |- ?lt = true -> ?a = ?b => let Hx := fresh "Hx" in intro Hx;
      match goal with Hl: lt = true -> _ /\ _ |- _ => exact (proj1 (Hl Hx)) end
  | |- _ |-- frame_fields _ _ => fe_ff
  | |- fs_dictEnd _ = fs_dictEnd _ => reflexivity
  | |- _ = Vint (Int.repr 0) \/ _ = Vint (Int.repr 1) => solve_cold
  | |- is_error_code _ = true -> _ /\ dec_err _ =>
      let Hx := fresh "Hx" in intro Hx; split; [reflexivity | solve_dec_err]
  | |- is_error_code _ = true -> dec_err _ => let Hx := fresh "Hx" in intro Hx; solve_dec_err
  | |- dec_err _ => solve_dec_err
  | Hxn: fx_on _ _ _ _ -> x_frame _ _ _ _ _ _ = None |- _ -> _ -> _ -> _ -> frame_exact _ _ _ _ _ _ _ _ =>
      let a := fresh "Ha" in let b := fresh "Hb" in let c := fresh "Hc" in let f := fresh "Hf" in
      intros a b c f; apply fe_exact_none; [reflexivity | exact (Hxn (conj a (conj b (conj c f))))]
  end end end.

Section Seg.
Context (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel)
  (W: list ptr_witness) (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (dm: dict_model) (e: ext_seg)
  (osh: share) (obase: val) (oN: Z) (oc: list val) (od ocap: Z)
  (ish: share) (ibase: val) (iN: Z) (ic: list val) (ioff: Z) (s: list Z) (sp ssp: val) (v_bp: val)
  (pr: dparams) (dsp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool)
  (am: option cmem) (hb: Z) (h: frame_header) (hs: Z) (fdid: Z) (d1: dfields) (ts0: tstate).

Lemma fr_end_ok3: DENT_OK DENT -> TABS_OK TABS ->
  fr_end_stmt DENT TABS SR BR W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb h hs fdid d1 ts0.
Proof.
  intros HD HT Espec j out oc1 st cold Hctx.
  pose proof Hctx as Hctx'. destruct Hctx'.
  unfold S_aft, fr_SEP, fr_LOC, fr_outP. cbn [app]. Intros.
  match goal with Hx: fr_RE _ _ _ _ _ _ |- _ => rename Hx into Hre end.
  match goal with Hx: exists f nb, blocks_size f (fr_rest s hs) = Some (j, nb) |- _ =>
    destruct Hx as (fbs & nbs & Hbsz) end.
  (* the exact model: the frame is the end x_fend after the blocks the loop decoded *)
  match goal with Hx: fr_xaft _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hx into Hxaft end.
  assert (HX: fx_on ox dm e pr ->
              x_frame xstate (xst_begin xhuf) xblock (ts_x ts0) s ocap = x_fend xstate h s hs out j (ts_x st)).
  { intros Hon. unfold fr_xaft in Hxaft. pose proof (Hxaft Hon) as E.
    etransitivity; [eapply fr_x_frame; eassumption | ]. rewrite E. reflexivity. }
  clear Hxaft.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv [seq_drop fr_body f_ZSTD_decompressFrame fn_body] in c in change c with c' end.
  unfold fr_R, fr_Delta. simplify_func_tycontext. abbreviate_semax.
  pose proof fc_hdr as (Hbs & Hlen9 & Hhs & Hlenh & h0 & Hgfh & Hcap & Hdid).
  pose proof (hs3_range (md_magicless (dmode_of pr)) s Hbs
    ltac:(unfold starting_len, mg_sh, ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *;
          destruct (md_magicless _); lia)) as Hhs6.
  rewrite <- Hhs in Hhs6.
  assert (Hhs0: 2 <= hs <= 18) by (unfold mg_sh in Hhs6; destruct (md_magicless _); lia).
  clear Hhs6.
  assert (Hslen: ioff + Zlength s <= 2 ^ 63 - 1) by (destruct fc_win as (_ & _ & ? & ? & _); lia).
  assert (Hioff: 0 <= ioff) by (destruct fc_win as (_ & ? & _); lia).
  pose proof (gfh3_range _ (sublist 0 hs s) h0 ltac:(apply Forall_sublist; auto) Hgfh)
    as (Hbsm & Hck & Hcs & Hws & Hdi).
  unfold frame_fields, fr_fs.
  cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
       fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize
       fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  assert (Hcs': 0 <= fh_contentSize h < 2 ^ 64) by (rewrite Hcap; exact Hcs).
  assert (Hck': fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) by (rewrite Hcap; exact Hck).
  clear Hcs Hck Hws Hdi Hbsm Hcap Hgfh Hhs Hdid.
  unfold fh_val. Intros.
  forward.
  assert (Hh3: fr_hdr3 (dmode_of pr) (sel_on pr dsp) dm s hs h) by exact fc_hdr.
  forward_if (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h).
  { lazymatch goal with |- semax _ (PROPx ?Ps ?L) _ _ =>
      forward_loop (PROPx Ps L)
        break: (PROPx ((fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h) :: Ps) L) end.
    { apply andp_left2, derives_refl. }
    { forward.
      forward_if.
      { apply prop_right, fe_sameblock; auto. }
      { rewrite fe_sub_pp in H9 by auto.
        assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap (Int64.unsigned (Int64.repr (-20)))).
        { apply (fe_codes_cs _ _ _ _ _ _ _ _ _ _ Hh3 H). intros [Hu | He].
          - apply H8. rewrite Hu. apply Int64.eqm_samerepr. exists 1. reflexivity.
          - replace (od + Zlength out - od) with (Zlength out) in H9 by lia.
            rewrite He in H9. unfold typed_true in H9. simpl in H9. rewrite Int64.eq_true in H9. discriminate H9. }
        assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts0) s ocap = None).
        { intros Hon. rewrite (HX Hon). apply fe_fend_cs. intros [Hu | He].
          - apply H8. rewrite Hu. apply Int64.eqm_samerepr. exists 1. reflexivity.
          - replace (od + Zlength out - od) with (Zlength out) in H9 by lia.
            rewrite He in H9. unfold typed_true in H9. simpl in H9. rewrite Int64.eq_true in H9. discriminate H9. }
        errblk. forward.
        errret3 (Int64.unsigned (Int64.repr (-20))) oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) st.
        { intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh3 Hd) as (k & Hdb & Hcs2 & _).
          apply H in Hdb as [-> _]. exfalso.
          replace (od + Zlength out - od) with (Zlength out) in H9 by lia.
          destruct Hcs2 as [Hu | He].
          - apply H8. rewrite Hu. apply Int64.eqm_samerepr. exists 1. reflexivity.
          - rewrite He, Int64.eq_true in H9. discriminate. } }
      { rewrite fe_sub_pp in H9 by auto. forward. entailer!.
        right. replace (od + Zlength out - od) with (Zlength out) in H9 by lia.
        destruct (Int64.eq (Int64.repr (Zlength out)) (Int64.repr (fh_contentSize h))) eqn:Eq; [ | inv H9].
        apply Int64.same_if_eq in Eq. apply repr_inj_unsigned64 in Eq; rep_lia. } }
    all: idtac. }
  { assert (Em: Int64.sub (Int64.repr 0) (Int64.repr 1) = Int64.repr ZSTD_CONTENTSIZE_UNKNOWN)
      by (unfold Int64.sub; apply Int64.eqm_samerepr; exists (-1); reflexivity).
    rewrite Em in H8. apply Int64.same_if_eq in H8.
    apply repr_inj_unsigned64 in H8; [ | unfold ZSTD_CONTENTSIZE_UNKNOWN in *; rep_lia..].
    forward. entailer!. }
  Intros. match goal with Hx: fh_contentSize h = _ \/ _ |- _ => rename Hx into Hcsz end.
  forward.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?Rs))) _ _ =>
  forward_if (EX k4: Z,
    PROPx [k4 = (if fh_checksumFlag h =? 1 then 4 else 0);
           fh_checksumFlag h = 1 -> hs + j + 4 <= Zlength s /\
             (md_ignore (dmode_of pr) = false -> le_field s (hs + j) 4 = xxh64 out 0 mod 2 ^ 32)]
    (LOCALx [temp _ip (offset_val (ioff + hs + j + k4) ibase);
             temp _op (offset_val (od + Zlength out) obase);
             temp _remainingSrcSize (Vlong (Int64.repr (Zlength s - hs - j - k4)));
             temp _ostart (offset_val od obase); temp _istart (offset_val ioff ibase);
             lvar _blockProperties (Tstruct ___gp_blockProperties_t noattr) v_bp;
             gvars gv; temp _dctx p; temp _srcPtr sp; temp _srcSizePtr ssp]
    (SEPx Rs)))
  end.
  { assert (Hc1: fh_checksumFlag h = 1)
      by (destruct Hck' as [Hc | Hc]; auto; rewrite Hc in H8; exfalso; apply H8; reflexivity).
    dw0p (4 <= Zlength s - hs - j).
    { forward_if.
      { assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap (Int64.unsigned (Int64.repr (-22)))).
        { apply fe_codes_ck. intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh3 Hd) as (k & Hdb & _ & Hck2).
          apply H in Hdb as [-> ->]. rewrite Hc1 in Hck2. simpl in Hck2. urepr. lia. }
        assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts0) s ocap = None)
          by (intros Hon; rewrite (HX Hon); apply fe_fend_short; [exact Hc1 | urepr; lia]).
        errblk. forward.
        errret3 (Int64.unsigned (Int64.repr (-22))) oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) st.
        { intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh3 Hd) as (k & Hdb & _ & Hck2).
          apply H in Hdb as [-> ->]. rewrite Hc1 in Hck2. simpl in Hck2. urepr. lia. } }
      { forward. entailer!. urepr. lia. } }
    Intros. match goal with Hx: 4 <= Zlength s - hs - j |- _ => rename Hx into Hrem4 end.
    forward.
    forward_if (hs + j + 4 <= Zlength s /\
                (md_ignore (dmode_of pr) = false -> le_field s (hs + j) 4 = xxh64 out 0 mod 2 ^ 32)).
    { assert (Hig0: dp_ignore pr = 0).
      { destruct fc_par as (_ & [Hi | Hi] & _); auto.
        rewrite Hi in H9. exfalso. apply Int.one_not_zero. exact H9. }
      assert (Ex: fr_xx fs pr h out = Some out)
        by (unfold fr_xx, fr_vck, vck; rewrite Hc1; cbn; rewrite Hig0; reflexivity).
      rewrite Ex.
      change (xxh_field p (Some out)) with (xxh64_state Ews 0 out (field_address t_dctx (DOT _xxhState) p)).
      assert_PROP (field_compatible t_dctx (DOT _xxhState) p).
      { entailer!. match goal with Hf: field_compatible t_dctx (DOT _format) p |- _ => destruct Hf as (? & ? & ? & ? & ?) end.
        repeat split; auto. simpl; unfold in_members; simpl; repeat (first [left; reflexivity | right]). }
      apply -> seq_assoc. eapply semax_seq'.
      forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, out).
      apply ENTAIL_refl.
      forward.
      change (xxh64_state Ews 0 out (field_address t_dctx (DOT _xxhState) p)) with (xxh_field p (Some out)).
      rewrite <- Ex.
      assert_PROP (field_compatible (tarray tuchar iN) [] ibase) as Hfci by entailer!.
      pose proof fc_win as (Hish & _ & HiN & _ & HicN & _ & _ & Hics).
      rewrite (fe_win_split ish iN ic ioff s ibase) by (auto; lia).
      Intros.
      apply -> seq_assoc. eapply semax_seq'.
      forward_call (ish, offset_val ioff ibase, s, hs + j).
      { entailer!. simpl. try rewrite offset_offset_val. f_equal. f_equal. lia. }
      { split; [auto | split; [lia | split; [lia | apply Forall_sublist; auto]]]. }
      apply ENTAIL_refl.
      forward.
      sep_apply (fe_win_merge ish iN ic ioff s ibase); [auto; lia .. | ].
      pose proof (fe_le4_range s (hs + j) Hbs ltac:(lia) ltac:(lia)) as Hle.
      assert (Hxx: xxh64_digest_model 0 out = xxh64 out 0)
        by (apply xxh64_digest_model_eq; rep_lia).
      rewrite Hxx.
      lazymatch goal with |- semax _ (PROPx ?Ps ?L) _ _ =>
        forward_loop (PROPx Ps L)
          break: (PROPx ((hs + j + 4 <= Zlength s /\ le_field s (hs + j) 4 = xxh64 out 0 mod 2 ^ 32) :: Ps) L) end.
      { apply andp_left2, derives_refl. }
      { forward_if.
        { assert (Hcodes: frame_codes3 (dmode_of pr) dm s ocap (Int64.unsigned (Int64.repr (-22)))).
          { apply fe_codes_ck. intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh3 Hd) as (k & Hdb & _ & Hck2).
            apply H in Hdb as [-> ->]. rewrite Hc1 in Hck2. simpl in Hck2. destruct Hck2 as (_ & Hck2 & _).
            match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end.
            apply fe_ck_iff; auto. apply Hck2. cbn. rewrite Hig0. reflexivity. }
          assert (Hxn: fx_on ox dm e pr -> x_frame xstate (xst_begin xhuf) xblock (ts_x ts0) s ocap = None).
          { intros Hon. rewrite (HX Hon). apply fe_fend_ck; [exact Hc1 | intro Heq].
            match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end.
            apply fe_ck_iff; auto. }
          errblk. forward.
          errret3 (Int64.unsigned (Int64.repr (-22))) oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) st.
          { intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh3 Hd) as (k & Hdb & _ & Hck2).
            apply H in Hdb as [-> ->]. rewrite Hc1 in Hck2. simpl in Hck2. destruct Hck2 as (_ & Hck2 & _).
            exfalso. match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end.
            apply fe_ck_iff; auto. apply Hck2. cbn. rewrite Hig0. reflexivity. } }
        { forward. entailer!. pose proof (proj1 (fe_ck_iff _ (xxh64 out 0) Hle) H11). first [assumption | split; [lia | assumption]]. } }
      { entailer!. } }
    { forward. entailer!. repeat split; try lia. intros. exfalso.
      destruct fc_par as (_ & [Hi | Hi] & _).
      - rewrite Hi in *. apply H9. reflexivity.
      - match goal with Hx: md_ignore _ = false |- _ => cbn in Hx; rewrite Hi in Hx; discriminate Hx end. }
    Intros. forward. forward.
    Exists 4. rewrite Hc1. simpl Z.eqb. cbv iota. entailer!. }
  { assert (Hc0: fh_checksumFlag h = 0)
      by (destruct Hck' as [Hc | Hc]; auto; rewrite Hc in H8; discriminate H8).
    forward. Exists 0. rewrite Hc0. simpl Z.eqb. cbv iota. entailer!. }
  Intros k4. match goal with Hx: k4 = _ |- _ => rename Hx into Hk4 end.
  match goal with Hx: fh_checksumFlag h = 1 -> _ |- _ => rename Hx into Hchk end.
  assert (Hk4r: 0 <= k4 /\ hs + j + k4 <= Zlength s).
  { subst k4. destruct Hck' as [Hc | Hc]; rewrite Hc; simpl; [lia | ]. destruct (Hchk Hc); lia. }
  assert (Hk4d: (fh_checksumFlag h = 1 /\ k4 = 4) \/ (fh_checksumFlag h = 0 /\ k4 = 0))
    by (subst k4; destruct Hck' as [Hc | Hc]; rewrite Hc; simpl; auto).
  clear Hk4.
  forward_call (p, Zlength out, hs + j + k4, 0).
  { entailer!. split; apply fe_sameblock; auto. }
  { apply prop_right. simpl. rewrite !fe_sub_pp by auto. simpl.
    replace (od + Zlength out - od) with (Zlength out) by lia.
    replace (ioff + hs + j + k4 - ioff) with (hs + j + k4) by lia. reflexivity. }
  dw0. { forward. entailer!. }
  forward. forward. forward.
  { apply prop_right, fe_sameblock; auto. }
  assert (Herr: is_error_code (Zlength out) = false) by (unfold is_error_code; apply Z.ltb_ge; rep_lia).
  assert (Hcok: frame_codes3 (dmode_of pr) dm s ocap (Zlength out))
    by exact (fe_codes_ok _ _ _ _ _ _ _ _ _ _ Hh3 H Hchk Herr).
  Exists (Zlength out) oc1 (fr_fs fs pr h hs fdid cold (fr_xx fs pr h out)) (hs + j + k4) d1 (ts_lxb st).
  rewrite fe_sub_pp by auto. replace (od + Zlength out - od) with (Zlength out) by lia.
  replace (ioff + (hs + j + k4)) with (ioff + hs + j + k4) by lia.
  replace (Zlength s - (hs + j + k4)) with (Zlength s - hs - j - k4) by lia.
  sep_apply (HT gv p ox st).
  sep_apply (fr_selR_post DENT W gv p fs ox dm e osh obase _ oc od ocap ish ibase iN ic ioff s pr dsp d l tbl xq lent am hb h hs d1 Hctx).
  sep_apply (zg_fold gv). unfold fcore3, cfg_fmt, cfg_lit.
  entailer!.
  - split; [intros _; exists out; auto | ].
    split; [apply (fe_frame_res3 (dmode_of pr) (sel_on pr dsp) dm s hs h j out); auto; try lia; destruct Hk4d as [[Hc ->] | [Hc ->]]; rewrite Hc; reflexivity | ].
    split; [solve_cold | split; [intro Hx; exact (proj1 (fc_lent Hx)) | ]].
    split; [intros _ Hsel Hdd; destruct (fc_ds2 Hsel Hdd) as [Hr Hp]; exists (fh_dictID h); split; [reflexivity | auto] | ].
    split; [intros _; eapply fr_fp; exact Hctx | ].
    split; cycle 1. split.
    { (* the end check: a frame that declares its content size decoded exactly that many bytes *)
      intros _ h' Hh' Ht' Hu'.
      pose proof fc_hdr as (_ & Hl9 & Ehs & _ & hq & Hg0 & Eh & _).
      assert (Hns: md_magicless (dmode_of pr) = true \/ is_skippable_magic (le_field s 0 4) = false).
      { destruct (md_magicless (dmode_of pr)) eqn:Em; [left; reflexivity | right].
        destruct (is_skippable_magic (le_field s 0 4)) eqn:Es; [| reflexivity].
        exfalso. apply (gfh_skip_type s h' Es); [| exact Ht'].
        change (md_magicless (dmode_of pr)) with (dp_fmt pr =? 1) in Em. rewrite Em in Hh'. exact Hh'. }
      destruct (gfh3_prefix (md_magicless (dmode_of pr)) s Hbs
                  ltac:(unfold starting_len, ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_FRAMEHEADERSIZE_PREFIX, mg_sh,
                          ZSTD_blockHeaderSize in *; destruct (md_magicless (dmode_of pr)); lia) Hns)
        as [E | (N1 & _)]; [| exfalso; rewrite <- Ehs in N1; exact (N1 hq Hg0)].
      rewrite <- Ehs, Hg0 in E. change (md_magicless (dmode_of pr)) with (dp_fmt pr =? 1) in E.
      rewrite Hh' in E. injection E as E'.
      assert (Ec: fh_contentSize h = fh_contentSize hq) by (rewrite Eh; reflexivity).
      rewrite <- E', <- Ec in Hu' |- *.
      destruct Hcsz as [Hx | Hx]; [exfalso; exact (Hu' Hx) | exact Hx]. }
    { (* the exact result: the model's end of the frame passes the same checks (the checksum is validated with
         the default parameters) *)
      intros Hox Hdm Hpr He.
      assert (Ek4: k4 = (if fh_checksumFlag h =? 1 then 4 else 0))
        by (destruct Hk4d as [[Hc ->] | [Hc ->]]; rewrite Hc; reflexivity).
      rewrite Ek4. apply (fe_exact_some ts0 s ocap out _ (ts_x st) oc1 od); [ | exact H6].
      rewrite (HX (conj Hox (conj Hdm (conj Hpr He)))). apply fe_fend_ok; auto.
      intros Hc. destruct (Hchk Hc) as [Hl Hx]. split; [lia | apply Hx]. rewrite Hpr. reflexivity. }
    intros _ Hns.
    assert (Ek4: k4 = (if fh_checksumFlag h =? 1 then 4 else 0))
      by (destruct Hk4d as [[Hc ->] | [Hc ->]]; rewrite Hc; reflexivity).
    rewrite Ek4. change (dp_fmt pr =? 1) with (md_magicless (dmode_of pr)).
    apply (fr_fcs3 (dmode_of pr) (sel_on pr dsp) dm s hs h j nbs fbs Hh3 Hbsz).
    + destruct Hns as [E | E]; [left; cbn [dmode_of md_magicless]; rewrite E; reflexivity | right; exact E].
    + intros Hc. destruct (Hchk Hc); lia.
  - fe_ff.
Qed.

End Seg.

End CM_Frame3_end_1.
