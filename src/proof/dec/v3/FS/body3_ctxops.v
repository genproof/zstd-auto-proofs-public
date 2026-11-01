(* FS3 bodies, ctxops3: parameters and resets (port of v2 body_FS_ctxops.v; every parameter).
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_body3_ctxops_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Ctx.
Variables (DENT : dent_pred) (TABS : tabs_pred) (SR : srel3) (BR : blrel).
Context (HDENT : DENT_OK DENT).
Context (HTABS : TABS_OK TABS).

Lemma body_getBoundsP3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_dParam_getBoundsP ZSTD_dParam_getBoundsP_spec3.
Proof.
  start_function.
  forward. forward. forward.
  assert (Hk: 0 <= k <= 2000) by
    (unfold dparam_known in H; simpl in H; unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H; lia).
  forward_if (PROP (False) LOCAL () SEP ()).
  - forward.
    forward_if (temp _t'1 (Vint (Int.repr 31))).
    { exfalso. discriminate. }
    { forward. entailer!. }
    forward. forward.
  - forward. forward. forward.
  - forward. forward. forward.
  - forward. forward. forward.
  - forward. forward. forward.
  - exfalso. unfold dparam_known in H; simpl in H.
    unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H; lia.
  - forward. forward. forward.
  - exfalso. unfold dparam_known in H; simpl in H.
    unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H.
    rewrite !Int.unsigned_repr in * by rep_lia. lia.
Qed.

Lemma body_withinBounds3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_dParam_withinBounds ZSTD_dParam_withinBounds_spec3.
Proof.
  start_function.
  assert (Hb: 0 <= fst (dparam_bounds k) <= 131072 /\ 0 <= snd (dparam_bounds k) <= 131072).
  { unfold dparam_bounds, ZSTD_BLOCKSIZE_MAX.
    destruct (k =? ZSTD_d_windowLogMax); [simpl; lia | ].
    destruct (k =? ZSTD_d_maxBlockSize); simpl; lia. }
  forward_call (Tsh, v_bounds, k).
  forward.
  forward_call 0.
  replace (is_error_code 0) with false by reflexivity.
  forward_if. { exfalso; auto. }
  forward.
  forward_if.
  { forward. entailer!. try rewrite Int.signed_repr in * by rep_lia. destruct (Z.leb_spec (fst (dparam_bounds k)) v); [lia | reflexivity]. }
  forward.
  forward_if.
  { forward. entailer!. try rewrite !Int.signed_repr in * by rep_lia.
    destruct (Z.leb_spec (fst (dparam_bounds k)) v); destruct (Z.leb_spec v (snd (dparam_bounds k)));
      try lia; reflexivity. }
  forward. entailer!. try rewrite !Int.signed_repr in * by rep_lia.
  destruct (Z.leb_spec (fst (dparam_bounds k)) v); destruct (Z.leb_spec v (snd (dparam_bounds k)));
    try lia; reflexivity.
Qed.

(* the state after ZSTD_DCtx_reset(ZSTD_reset_session_only) *)
Definition s_reset3 (s: sfields) : sfields :=
  {| sf_stage := 0; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := 0;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* ... with the bound of a context's own allocator raised to the window limit's stream (a session reset is a
   set_ss: Spec_api6.cm_raise) *)
Definition k_reset3 (k: cst3) : cst3 :=
  c3_with_s (c3_with_fs k (fsu_isFrameDecompression (c3_fs k) (Vint (Int.repr 1))) (c3_tabs k))
    (s_reset3 (c3_s (c3_raise k (dp_wmax (c3_par k))))).

Lemma fsu_isFD_same fs v : fs_isFrameDecompression fs = v -> fsu_isFrameDecompression fs v = fs.
Proof. intros <-. destruct fs; reflexivity. Qed.

Lemma reset_rel3 (gv: globals) st k :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  base_rel3 (set_ss st ss_init) (k_reset3 k) /\
  (dc_ss (set_ss st ss_init) <> ss_init -> ss_err (dc_ss (set_ss st ss_init)) = false ->
     SR gv (set_ss st ss_init) (k_reset3 k) \/
     (dc_ss (set_ss st ss_init) = ss_restart /\ sf_stage (c3_s (k_reset3 k)) = 0)) /\
  (forall ba, dc_bl (set_ss st ss_init) = Some ba ->
     BR (c3_par (k_reset3 k)) ba (c3_fs (k_reset3 k)) (c3_tabs (k_reset3 k)) (sf_hbuf (c3_s (k_reset3 k)))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HB.
  pose proof (mem_rel3_raise st k ss_init H9) as H9'.
  split; [ | split].
  - destruct H9' as (M1 & M2 & M3).
    unfold base_rel3, dict_rel3, set_cur_ok, mem_rel3, c3_raise in *; simpl in *. rewrite H2.
    repeat split; auto; try (apply M3; auto); unfold ZSTD_NO_FORWARD_PROGRESS_MAX; simpl; lia.
  - simpl. intros Hc; exfalso; apply Hc; reflexivity.
  - simpl. intros ba Hba.
    destruct H8 as [_ Hfd]; [rewrite Hba; discriminate | ].
    rewrite (fsu_isFD_same _ _ Hfd). apply HB; auto.
Qed.

(* the same for the state the session reset leaves: the stream's buffers and literal slack are no longer a clean
   context's (Spec_api6.dc_ex cleared); the concrete state is the same *)
Lemma reset_ex_rel3 (gv: globals) st k :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  base_rel3 (set_ex (set_ss st ss_init) false) (k_reset3 k) /\
  (dc_ss (set_ex (set_ss st ss_init) false) <> ss_init -> ss_err (dc_ss (set_ex (set_ss st ss_init) false)) = false ->
     SR gv (set_ex (set_ss st ss_init) false) (k_reset3 k) \/
     (dc_ss (set_ex (set_ss st ss_init) false) = ss_restart /\ sf_stage (c3_s (k_reset3 k)) = 0)) /\
  (forall ba, dc_bl (set_ex (set_ss st ss_init) false) = Some ba ->
     BR (c3_par (k_reset3 k)) ba (c3_fs (k_reset3 k)) (c3_tabs (k_reset3 k)) (sf_hbuf (c3_s (k_reset3 k)))).
Proof.
  intros Hb HB. destruct (reset_rel3 gv st k Hb HB) as (R1 & _ & R3).
  split; [ | split].
  - exact R1.
  - simpl. intros Hc; exfalso; apply Hc; reflexivity.
  - exact R3.
Qed.

Ltac skip_loop :=
  match goal with |- semax _ ?P _ _ => forward_loop P break: P; [apply ENTAIL_refl | forward | ]; [apply ENTAIL_refl | ] end.
(* do { if (0) debug(...); } while (0) *)
Ltac dbg_loop :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [apply ENTAIL_refl
    | forward_if P; [exfalso; match goal with H: 0 <> 0 |- _ => apply H; reflexivity end | forward | forward]
    | ]; try apply ENTAIL_refl end.
Ltac dloop := first [skip_loop | dbg_loop].

(* the concrete state after the parameter half of ZSTD_DCtx_reset (ZSTD_clearDict, ZSTD_DCtx_resetParameters, F8: the
   stream buffer freed, litExtraBuffer cleared): no dictionary, the default parameters, the tables forgotten (B's
   TABS gives the uninitialised tables) with litExtraBuffer zeroed *)
Definition s_par3 (s: sfields) (lh: Z) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := nullval; sf_inSize := 0; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := 0; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := 0; sf_ring := sf_ring s; sf_mem := sf_mem s;
     sf_held := sf_held s - lh |}.

(* ... the local DDict freed: its bytes (local_held) given back to the context's allocator *)
Definition k_par3 (k: cst3) : cst3 :=
  {| c3_fs := c3_fs k; c3_tabs := TUninit lxb_zero; c3_stable := false; c3_dict := df_none;
     c3_s := s_par3 (c3_s k) (local_held (c3_dict k));
     c3_par := dparams_dflt; c3_sp := c3_sp k; c3_set := c3_set k |}.

(* a context that has no running stream to relate (DC3_of's streaming clause holds without SR): before any stream,
   a failed stream, or a new one at zdss_init *)
Definition ss_quiet (st: dctx_st) (k: cst3) : Prop :=
  dc_ss st = ss_init \/ ss_err (dc_ss st) = true \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0).

Lemma ss_quiet_sr (gv: globals) st k : ss_quiet st k ->
  dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0).
Proof.
  intros [E | [E | E]] Hn He; [contradiction | rewrite E in He; discriminate | right; exact E].
Qed.

Lemma ss_restart_not_init : ss_restart <> ss_init.
Proof. unfold ss_restart, ss_init. intros E. inversion E. Qed.

(* the state a setter leaves: before any stream its result (b = false), between two frames its result with dc_ex
   cleared (b = true: Spec_api6.after_stage's restart) *)
Definition fin3 (b: bool) (st: dctx_st) : dctx_st := if b then set_ex st false else st.

(* DC3_of's clauses for a quiet context, kept by fin3 (dc_ex cleared: the exact relation is vacuous) *)
Lemma fin3_rel (gv: globals) (b: bool) st k :
  base_rel3 st k -> ss_quiet st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  (b = false -> ex_on3 SR st k) ->
  base_rel3 (fin3 b st) k /\
  (dc_ss (fin3 b st) <> ss_init -> ss_err (dc_ss (fin3 b st)) = false ->
     SR gv (fin3 b st) k \/ (dc_ss (fin3 b st) = ss_restart /\ sf_stage (c3_s k) = 0)) /\
  (forall ba, dc_bl (fin3 b st) = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) /\
  ex_on3 SR (fin3 b st) k.
Proof.
  intros Hb Hq HB Hx. destruct b; simpl.
  - split; [exact Hb | split; [exact (ss_quiet_sr gv (set_ex st false) k Hq) | split; [exact HB | apply ex_on3_noex; reflexivity]]].
  - split; [exact Hb | split; [apply (ss_quiet_sr gv); exact Hq | split; [exact HB | apply Hx; reflexivity]]].
Qed.

(* a setter before any stream keeps the exact relation (the configuration may change at dc_ss = ss_init) *)
Lemma ex3_par st k p' : ex_on3 SR st k -> dc_ss st = ss_init -> ex_on3 SR (set_par st p') (c3_with_par k p').
Proof.
  intros H E. exact (ex_on3_keep SR st (set_par st p') k (c3_with_par k p') H eq_refl (fun e => e) eq_refl eq_refl
                       eq_refl (or_introl E)).
Qed.

Lemma ex3_stable st k b : ex_on3 SR st k -> dc_ss st = ss_init ->
  ex_on3 SR (set_stable st b) (c3_with_stable k b).
Proof.
  intros H E. exact (ex_on3_keep SR st (set_stable st b) k (c3_with_stable k b) H eq_refl (fun e => e) eq_refl
                       eq_refl eq_refl (or_introl E)).
Qed.

(* a setter between two frames (zstd's streamStage at zdss_init) gives a new stream (or keeps a failed one): the base
   relation holds with the bound of a context's own allocator raised (ss_next is a set_ss), and no stream to relate *)
Lemma next_rel3 st k :
  base_rel3 st k -> dc_ss st <> ss_init -> sf_stage (c3_s k) = 0 ->
  base_rel3 (set_ss st (ss_next (dc_ss st))) (c3_raise k (dp_wmax (dc_par st))) /\
  ss_quiet (set_ss st (ss_next (dc_ss st))) (c3_raise k (dp_wmax (dc_par st))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & (H7a & H7b) & H8 & H9) Hss Hs0.
  pose proof (mem_rel3_raise st k (ss_next (dc_ss st)) H9) as (M1 & M2 & M3).
  unfold ss_quiet, ss_next. destruct (ss_err (dc_ss st)) eqn:Ee.
  - unfold base_rel3, dict_rel3, set_cur_ok, mem_rel3, stage_rel3, c3_raise in *; simpl in *.
    split; [| right; left; exact Ee].
    repeat split; auto; try (apply M3; auto); try (intros E; rewrite Ee in E; discriminate); try congruence.
    all: try (exfalso; destruct (H8 ltac:(assumption)) as [E' _]; contradiction).
  - specialize (H7a eq_refl).
    unfold base_rel3, dict_rel3, set_cur_ok, mem_rel3, stage_rel3, c3_raise in *; simpl in *.
    split; [| right; right; split; [reflexivity | exact Hs0]].
    repeat split; auto; try (apply M3; auto); try lia.
    all: try (intros E; exfalso; apply ss_restart_not_init, E).
    all: try (exfalso; apply ss_restart_not_init; assumption).
    all: try (exfalso; destruct (H8 ltac:(assumption)) as [E' _]; contradiction).
Qed.

Lemma local_held_nonneg (d: dfields) : 0 <= local_held d.
Proof.
  unfold local_held, ddx_held. destruct (eq_dec (df_local d) nullval); [lia |].
  destruct (df_lx d) as [[x buf]|]; [| lia]. destruct (dx_mem x); [| lia].
  destruct (ddx_copied x); simpl; pose proof (Zlength_nonneg (dx_bytes x)); lia.
Qed.

(* the context's allocator holds the local DDict's bytes and the set's (not negative) *)
Lemma ctx_rep3_held (gv: globals) (p: val) (k: cst3) :
  ctx_rep3 DENT TABS gv p k |-- !! (0 <= local_held (c3_dict k) <= sf_held (c3_s k)).
Proof.
  pose proof (local_held_nonneg (c3_dict k)).
  unfold ctx_rep3, ctx_body3, hset_rep.
  destruct (eq_dec (c3_sp k) nullval).
  - Intros. entailer!.
  - Intros tp tbl. entailer!. unfold set_bytes in *.
    destruct (sf_mem (c3_s k)); pose proof (Zlength_nonneg tbl); simpl in *; lia.
Qed.

(* room for a stream stays when the context's own allocator gets bytes back *)
Lemma mem_room_less (s s': sfields) : mem_room s -> sf_mem s' = sf_mem s -> 0 <= sf_held s' <= sf_held s ->
  mem_room s'.
Proof.
  unfold mem_room. intros Hr Em Hh. rewrite Em. destruct (sf_mem s); [| lia].
  destruct Hr as [Hr | Hr]; [left; lia | ].
  destruct (Z.eq_dec (sf_held s') 0); [left; auto | right; lia].
Qed.

Lemma reset_par_rel3 (gv: globals) st k :
  base_rel3 st k -> ss_quiet st k -> 0 <= local_held (c3_dict k) <= sf_held (c3_s k) ->
  base_rel3 (reset_par st) (k_par3 k) /\
  (dc_ss (reset_par st) <> ss_init -> ss_err (dc_ss (reset_par st)) = false ->
     SR gv (reset_par st) (k_par3 k) \/ (dc_ss (reset_par st) = ss_restart /\ sf_stage (c3_s (k_par3 k)) = 0)) /\
  (forall ba, dc_bl (reset_par st) = Some ba ->
     BR (c3_par (k_par3 k)) ba (c3_fs (k_par3 k)) (c3_tabs (k_par3 k)) (sf_hbuf (c3_s (k_par3 k)))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hss Hlh.
  split; [ | split].
  - unfold base_rel3, dict_rel3, dict_rel3_of, set_cur_ok; simpl.
    split; [reflexivity | split; [reflexivity | split; [exact H3 | split; [left; split; [reflexivity | left; reflexivity] | ]]]].
    split; [intros dr q dd dd' Hd; discriminate | split; [exact H6 | split; [exact H7 | ]]].
    split; [intros Hc; exfalso; apply Hc; reflexivity | ].
    destruct H9 as (Hm & Hh & Hn). split; [exact Hm | split].
    + apply (mem_room_less (c3_s k)); auto. simpl. lia.
    + intros E. exfalso. apply E. reflexivity.
  - apply (ss_quiet_sr gv). exact Hss.
  - simpl. intros ba Hba; discriminate.
Qed.

Lemma byte_cells_zeros n : byte_cells (Zrepeat (Vint (Int.repr 0)) n).
Proof.
  unfold byte_cells, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x.
  exists 0. split; [lia | reflexivity].
Qed.

Lemma ring_free3 (am: option cmem) (b: val) (n: Z) (c: list val) :
  ring_rep am b n c |--
  if eq_dec b nullval then emp else blk_tok am (tarray tuchar n) b * data_at_ Ews (tarray tuchar n) b.
Proof. unfold ring_rep. destruct (eq_dec b nullval); entailer!. Qed.

(* the bytes the allocator holds once clearDict freed the local DDict (lh bytes) and F8 the stream buffer *)
Lemma given_par3 (s: sfields) (lh: Z) : 0 <= sf_inSize s -> 0 <= sf_outSize s ->
  (sf_inBuff s = nullval -> sf_inSize s + sf_outSize s = 0) ->
  (if eq_dec (sf_inBuff s) nullval then sf_given s - lh
   else sf_given s - lh - sizeof (tarray tuchar (sf_inSize s + sf_outSize s))) = sf_given (s_par3 s lh).
Proof.
  intros Hi Ho Hn. unfold sf_given, s_par3; cbn [sf_held sf_inSize sf_outSize].
  destruct (eq_dec (sf_inBuff s) nullval) as [E|E].
  - specialize (Hn E). lia.
  - simpl sizeof. rewrite Z.max_r by lia. lia.
Qed.

(* the allocator's group of a context, folded; and with its bound raised (CM_mono) *)
Lemma mgroup_fold3 (am: option cmem) (q: val) (h: Z) : cmem_ok am ->
  field_at Ews t_dctx (DOT _customMem) (cmem_v am) q * blk_tok am (tarray tuchar (sizeof t_dctx)) q * cm_have am h
  |-- mgroup am q h.
Proof. intros Hok. unfold mgroup. apply andp_right; [apply prop_right; exact Hok | apply derives_refl]. Qed.

Lemma mgroup_raise3 (am: option cmem) (q: val) (h w: Z) : mgroup am q h |-- mgroup (cm_raise am w) q h.
Proof.
  unfold mgroup. rewrite blk_tok_raise, cmem_v_raise. Intros.
  apply andp_right; [apply prop_right; apply cmem_ok_raise; auto |]. cancel. apply cm_have_raise.
Qed.

(* the frame fields after the session half (isFrameDecompression = 1) *)
Lemma frame_fields_isFD (p: val) (fs: fstate) :
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (Vint (Int.repr 1)) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p |--
  frame_fields p (fsu_isFrameDecompression fs (Vint (Int.repr 1))).
Proof. unfold frame_fields, fsu_isFrameDecompression; simpl. cancel. Qed.

Lemma cm_fold3 (q: val) (v: reptype t_cmem) :
  data_at Ews t_cmem v (field_address t_dctx (DOT _customMem) q) |-- field_at Ews t_dctx (DOT _customMem) v q.
Proof. rewrite field_at_data_at. apply derives_refl. Qed.

Lemma tabs_rep_uninit gv p t : tabs_rep TABS gv p t |-- EX lxb: list Z, tables_uninit p lxb.
Proof. destruct t as [lxb | ox ts]; simpl; [Exists lxb; apply derives_refl | Exists (ts_lxb ts); apply HTABS]. Qed.

(* litExtraBuffer as the bytes memset writes, and back *)
Lemma lit_extra_mb (p: val) (l: list val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) l p |--
  memory_block Ews 65568 (field_address t_dctx (DOT _litExtraBuffer) p).
Proof.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litExtraBuffer) l p).
  rewrite field_at__memory_block. apply derives_refl.
Qed.

Lemma lit_extra_zero (p: val) :
  data_at Ews (tarray tuchar 65568) (Zrepeat (Vint (Int.repr 0)) 65568) (field_address t_dctx (DOT _litExtraBuffer) p) |--
  lit_extra_at p lxb_zero.
Proof.
  unfold lit_extra_at. apply andp_right.
  - apply prop_right. split.
    { unfold lxb_zero. apply Zlength_repeat. unfold LITEXTRA_N, WILDCOPY_OVERLENGTH. lia. }
    unfold lxb_zero, bytes_ok. apply Forall_forall; intros x Hx.
    apply repeat_spec in Hx. subst x. unfold is_byte. lia.
  - replace (zbytes lxb_zero) with (Zrepeat (Vint (Int.repr 0)) 65568)
      by (unfold lxb_zero, Zrepeat; rewrite map_repeat; change LITEXTRA_N with 65568; reflexivity).
    rewrite (field_at_data_at Ews t_dctx (DOT _litExtraBuffer)). apply derives_refl.
Qed.

(* the parameter fields, before ZSTD_DCtx_resetParameters and after it (the defaults: dparams_dflt, buffered output) *)
Lemma params_take (p: val) (pr: dparams) (stable: bool) (wmax: Z) :
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p * cgroup3 p stable wmax |--
  params_ p * field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p.
Proof.
  unfold params_, cfg_fmt, cfg_lit, cgroup3.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _format)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _disableHufAsm)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _forceIgnoreChecksum)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _maxBlockSizeParam)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _refMultipleDDicts)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _maxWindowSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _outBufferMode)).
  cancel.
Qed.

Lemma params_give (p: val) :
  params0 p * field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p |--
  cfg_fmt p (dp_fmt dparams_dflt) * cfg_lit p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore dparams_dflt))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax dparams_dflt))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi dparams_dflt))) p *
  cgroup3 p false (dp_wmax dparams_dflt).
Proof. unfold params0, cfg_fmt, cfg_lit, cgroup3; simpl. cancel. Qed.

(* ZSTD_DCtx_reset, one lemma per directive (one proof of the whole body exceeds the time budget of a Qed) *)
Definition reset_Delta : tycontext := func_tycontext f_ZSTD_DCtx_reset Vprog (FS3_G DENT TABS SR BR) nil.

Definition reset_P (gv: globals) (d: val) (k: cst3) (dir: Z) : environ -> mpred :=
  PROP () LOCAL (gvars gv; temp _dctx d; temp _reset (Vint (Int.repr dir)))
  SEP (mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv d k).

Definition reset_R (gv: globals) (d: val) (st: dctx_st) (dir: Z) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong
       (EX (r: Z) (st': dctx_st),
        PROP (0 <= r <= Int64.max_unsigned; reset_post dir st r st')
        RETURN (Vlong (Int64.repr r)) SEP (mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d st'))%argsassert)
    (stackframe_of f_ZSTD_DCtx_reset).

Ltac reset_start :=
  intros H0 H1 H2 H3; unfold reset_P, reset_R, reset_Delta; simplify_func_tycontext;
  match goal with |- semax _ _ ?c _ => let c' := eval cbv [fn_body f_ZSTD_DCtx_reset] in c in change c with c' end;
  abbreviate_semax.

Lemma reset3_session {Espec: OracleKind} (gv: globals) (d: val) (st: dctx_st) (k: cst3) :
  base_rel3 st k ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ex_on3 SR st k ->
  semax reset_Delta (reset_P gv d k ZSTD_reset_session_only) (fn_body f_ZSTD_DCtx_reset) (reset_R gv d st ZSTD_reset_session_only).
Proof.
  reset_start.
  (* ZSTD_reset_session_only: a set_ss, the bound of a context's own allocator raised *)
  sep_apply (ctx_rep3_raise DENT TABS gv d k (dp_wmax (c3_par k))).
  unfold ctx_rep3, ctx_body3, fgroup3, frame_fields, sgroup. Intros.
  unfold ZSTD_reset_session_only.
  forward_if (temp _t'1 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. auto. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
  forward. forward. forward.
  forward_if (temp _t'2 (Vint (Int.repr 0))).
  { exfalso. discriminate. }
  { forward. entailer!. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ exfalso; auto | ].
  forward.
  destruct (reset_ex_rel3 gv st k H0 H2) as (R1 & R2 & R3).
  assert (R4: ex_on3 SR (set_ex (set_ss st ss_init) false) (k_reset3 k)) by (apply ex_on3_noex; reflexivity).
  Exists 0 (set_ex (set_ss st ss_init) false).
  unfold DC3x, DC3_of. Exists (k_reset3 k).
  unfold ctx_rep3, ctx_body3, fgroup3, frame_fields, sgroup, k_reset3, s_reset3, c3_raise, c3_with_s, sf_with_mem;
    simpl.
  entailer!. split; reflexivity.
  unfold sf_given; simpl; apply derives_refl.
Qed.

Lemma reset3_params {Espec: OracleKind} (gv: globals) (d: val) (st: dctx_st) (k: cst3) :
  base_rel3 st k ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ex_on3 SR st k ->
  semax reset_Delta (reset_P gv d k ZSTD_reset_parameters) (fn_body f_ZSTD_DCtx_reset) (reset_R gv d st ZSTD_reset_parameters).
Proof.
  reset_start.
  (* ZSTD_reset_parameters *)
  assert_PROP (0 <= local_held (c3_dict k) <= sf_held (c3_s k)) as Hlh
    by (sep_apply (ctx_rep3_held gv d k); entailer!).
  unfold ctx_rep3, ctx_body3, fgroup3, sgroup. Intros.
  unfold ZSTD_reset_parameters.
  forward_if (temp _t'1 (Vint (Int.repr 0))).
  { exfalso. discriminate. }
  { forward. entailer!. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ exfalso; auto | ].
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { forward. entailer!. }
  { exfalso. auto. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
  match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx A (LOCALx Q (SEPx R))) break: (PROPx ((sf_stage (c3_s k) = 0) :: A) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_if.
    - (* a frame is being streamed: stage_wrong, nothing changed *)
      dloop. dloop. dloop. dloop. forward.
      Exists (Int64.unsigned (Int64.repr (-60))) st.
      unfold DC3x, DC3_of. Exists k.
      unfold ctx_rep3, ctx_body3, fgroup3, frame_fields, sgroup.
      entailer!.
      try (split; [ | exact H3]; []).
      split; [ | rewrite Int64.repr_unsigned; reflexivity].
      unfold reset_post, ZSTD_reset_session_only, ZSTD_reset_parameters; simpl. right. split.
      { intros Hi. pose proof H0 as (_ & _ & _ & _ & _ & _ & (_ & Hst) & _). destruct (Hst Hi) as [Hs _]. contradiction. }
      left. split; reflexivity.
    - forward. entailer!. }
  Intros. match goal with H: sf_stage (c3_s k) = 0 |- _ => rename H into Hs0 end.
  freeze FR1 := (dctx_token _) (dctx_pad _) (frame_fields _ _) (field_at _ _ (DOT _ddictSet) _ _) (hset_rep _ _ _ _)
    (field_at _ _ (DOT _streamStage) _ _) (field_at _ _ (DOT _inPos) _ _) (field_at _ _ (DOT _outBuff) _ _)
    (field_at _ _ (DOT _outStart) _ _) (field_at _ _ (DOT _outEnd) _ _).
  freeze FR2 := (field_at _ _ (DOT _lhSize) _ _) (field_at _ _ (DOT _hostageByte) _ _)
    (field_at _ _ (DOT _noForwardProgress) _ _) (field_at _ _ (DOT _expectedOutBuffer) _ _)
    (field_at _ _ (DOT _headerBuffer) _ _).
  (* clearDict frees the local DDict through the context's allocator *)
  unfold mgroup. Intros.
  replace (sf_given (c3_s k)) with ((sf_given (c3_s k) - local_held (c3_dict k)) + local_held (c3_dict k)) by lia.
  forward_call (gv, d, c3_dict k, sf_mem (c3_s k), sf_given (c3_s k) - local_held (c3_dict k)).
  { destruct (base_rel3_mem _ _ H0) as (_ & _ & Hl).
    split; [exact Hl | unfold sf_given; rewrite dctx_size_eq; lia]. }
  sep_apply (params_take d (c3_par k) (c3_stable k) (dp_wmax (c3_par k))).
  forward_call d. { cancel. }
  forward.
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if.
  2: { exfalso. match goal with H: Int64.repr 0 <> Int64.zero |- _ => apply H; reflexivity end. }
  assert_PROP (is_pointer_or_null (sf_inBuff (c3_s k)) /\
               (sf_inBuff (c3_s k) = nullval -> sf_inSize (c3_s k) + sf_outSize (c3_s k) = 0)) as Hib.
  { unfold ring_rep. destruct (eq_dec (sf_inBuff (c3_s k)) nullval) as [E|E]; [rewrite E; entailer! | ].
    Intros. entailer!. }
  destruct Hib as [Hib Hib0].
  forward.
  sep_apply (ring_free3 (sf_mem (c3_s k)) (sf_inBuff (c3_s k)) (sf_inSize (c3_s k) + sf_outSize (c3_s k))
               (sf_ring (c3_s k))).
  assert_PROP (field_compatible t_dctx (DOT _customMem) d) as Hfcm by entailer!.
  rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
  (* F8: the stream buffer freed through the context's allocator *)
  forward_call (gv, tarray tuchar (sf_inSize (c3_s k) + sf_outSize (c3_s k)), sf_inBuff (c3_s k), Ews,
                field_address t_dctx (DOT _customMem) d, sf_mem (c3_s k), sf_given (c3_s k) - local_held (c3_dict k)).
  { split.
    - intros _. unfold cm_held. destruct (sf_mem (c3_s k)); auto. simpl sizeof.
      rewrite Z.max_r by lia. unfold sf_given. rewrite dctx_size_eq. lia.
    - intros Nb _. match goal with Hx: sf_inBuff _ <> nullval -> 0 < _ |- _ => specialize (Hx Nb) end.
      simpl sizeof. rewrite Z.max_r by lia. lia. }
  rewrite given_par3 by auto.
  forward. forward. forward.
  forward.
  sep_apply (tabs_rep_uninit gv d (c3_tabs k)). Intros lxb. unfold tables_uninit, lit_extra_at. Intros.
  assert (Hfcl: field_compatible t_dctx (DOT _litExtraBuffer) d).
  { destruct Hfcm as (? & ? & ? & ? & ?). repeat split; auto. apply compute_in_members_true_iff. reflexivity. }
  sep_apply (lit_extra_mb d (zbytes lxb)).
  forward_call (Ews, field_address t_dctx (DOT _litExtraBuffer) d, 0, 65568).
  sep_apply (lit_extra_zero d).
  sep_apply (cm_fold3 d (cmem_v (sf_mem (c3_s k)))).
  sep_apply (params_give d).
  sep_apply (mgroup_fold3 (sf_mem (c3_s k)) d (sf_given (s_par3 (c3_s k) (local_held (c3_dict k)))) ltac:(assumption)).
  forward.
  thaw FR2. thaw FR1.
  destruct (Classical_Prop.classic (dc_ss st = ss_init)) as [Hi | Hn].
  + (* no stream begun: the parameters reset *)
    destruct (reset_par_rel3 gv st k H0 (or_introl Hi) Hlh) as (R1 & R2 & R3).
    (* the tables zeroed, the stream at zdss_init with no call without progress: a clean context *)
    assert (R4: ex_on3 SR (reset_par st) (k_par3 k)).
    { pose proof H0 as (_ & _ & _ & _ & _ & _ & (_ & Hst) & _). destruct (Hst Hi) as [_ Hnfp].
      unfold ex_on3. intros _ _ _. cbn [dc_ss reset_par]. rewrite Hi.
      exact (sr_ex_clean SR (c3_s (k_par3 k)) (c3_fs (k_par3 k)) Hs0 eq_refl eq_refl eq_refl Hnfp). }
    Exists 0 (reset_par st). unfold DC3x, DC3_of. Exists (k_par3 k).
    unfold ctx_rep3, ctx_body3, fgroup3, sgroup, k_par3, s_par3, tabs_rep, tables_uninit, ring_rep; simpl.
    unfold k_par3, s_par3 in R1, R2, R3, R4; simpl in R1, R2, R3, R4.
    entailer!.
    split; [ | apply par_ok_dflt].
    unfold reset_post, ZSTD_reset_session_only, ZSTD_reset_parameters; simpl. left. auto.
    apply derives_refl.
  + (* between two frames: the parameters reset on a new stream (or the failed one kept; a set_ss: the
       allocator's bound raised) *)
    destruct (next_rel3 st k H0 Hn Hs0) as (H0' & Hq').
    destruct (reset_par_rel3 gv _ _ H0' Hq' Hlh) as (R1 & _ & R3).
    destruct (fin3_rel gv true _ _ R1 Hq' R3 ltac:(discriminate)) as (R1' & R2 & R3' & R4).
    clear R1 R3. rename R1' into R1. rename R3' into R3. cbv [fin3] in R1, R2, R3, R4.
    sep_apply (mgroup_raise3 (sf_mem (c3_s k)) d (sf_given (s_par3 (c3_s k) (local_held (c3_dict k))))
                 (dp_wmax (dc_par st))).
    Exists 0 (set_ex (reset_par (set_ss st (ss_next (dc_ss st)))) false). unfold DC3x, DC3_of.
    Exists (k_par3 (c3_raise k (dp_wmax (dc_par st)))).
    unfold ctx_rep3, ctx_body3, fgroup3, sgroup, k_par3, s_par3, c3_raise, c3_with_s, sf_with_mem, tabs_rep,
      tables_uninit, ring_rep; simpl.
    unfold k_par3, s_par3, c3_raise, c3_with_s, sf_with_mem in R1, R2, R3, R4; simpl in R1, R2, R3, R4.
    rewrite hset_rep_raise.
    entailer!.
    split; [ | apply par_ok_dflt].
    unfold reset_post, ZSTD_reset_session_only, ZSTD_reset_parameters; simpl. right. split; [exact Hn | right; eexists; split; [split; reflexivity | reflexivity]].
    unfold sf_given; simpl; apply derives_refl.
Qed.

Lemma reset3_both {Espec: OracleKind} (gv: globals) (d: val) (st: dctx_st) (k: cst3) :
  base_rel3 st k ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ex_on3 SR st k ->
  semax reset_Delta (reset_P gv d k ZSTD_reset_session_and_parameters) (fn_body f_ZSTD_DCtx_reset) (reset_R gv d st ZSTD_reset_session_and_parameters).
Proof.
  reset_start.
  (* ZSTD_reset_session_and_parameters: a set_ss, the bound of a context's own allocator raised *)
  assert_PROP (0 <= local_held (c3_dict k) <= sf_held (c3_s k)) as Hlh
    by (sep_apply (ctx_rep3_held gv d k); entailer!).
  destruct (reset_rel3 gv st k H0 H2) as (R1 & R2 & R3).
  destruct (base_rel3_mem _ _ R1) as (_ & _ & Hl1).
  sep_apply (ctx_rep3_raise DENT TABS gv d k (dp_wmax (c3_par k))).
  remember (c3_raise k (dp_wmax (c3_par k))) as k1 eqn:Ek1.
  unfold ctx_rep3, ctx_body3, fgroup3, frame_fields, sgroup. Intros.
  unfold ZSTD_reset_session_and_parameters.
  forward_if (temp _t'1 (Vint (Int.repr 1))).
  { exfalso. discriminate. }
  { forward. entailer!. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
  forward. forward. forward.
  forward_if (temp _t'2 (Vint (Int.repr 1))).
  { exfalso. discriminate. }
  { forward. entailer!. }
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. forward_if.
    - exfalso. discriminate.
    - forward. entailer!. }
  Intros.
  sep_apply (frame_fields_isFD d (c3_fs k1)).
  freeze FR1 := (dctx_token _) (dctx_pad _) (frame_fields _ _) (field_at _ _ (DOT _ddictSet) _ _) (hset_rep _ _ _ _)
    (field_at _ _ (DOT _streamStage) _ _) (field_at _ _ (DOT _inPos) _ _) (field_at _ _ (DOT _outBuff) _ _)
    (field_at _ _ (DOT _outStart) _ _) (field_at _ _ (DOT _outEnd) _ _).
  freeze FR2 := (field_at _ _ (DOT _lhSize) _ _) (field_at _ _ (DOT _hostageByte) _ _)
    (field_at _ _ (DOT _noForwardProgress) _ _) (field_at _ _ (DOT _expectedOutBuffer) _ _)
    (field_at _ _ (DOT _headerBuffer) _ _).
  (* clearDict frees the local DDict through the context's allocator *)
  unfold mgroup. Intros.
  replace (sf_given (c3_s k1)) with ((sf_given (c3_s k1) - local_held (c3_dict k1)) + local_held (c3_dict k1)) by lia.
  forward_call (gv, d, c3_dict k1, sf_mem (c3_s k1), sf_given (c3_s k1) - local_held (c3_dict k1)).
  { subst k1. split; [exact Hl1 | unfold sf_given; rewrite dctx_size_eq; simpl in *; lia]. }
  sep_apply (params_take d (c3_par k1) (c3_stable k1) (dp_wmax (c3_par k1))).
  forward_call d. { cancel. }
  forward.
  try (unfold MORE_COMMANDS, abbreviate); apply semax_if_seq.
  forward_if.
  2: { exfalso. match goal with H: Int64.repr 0 <> Int64.zero |- _ => apply H; reflexivity end. }
  assert_PROP (is_pointer_or_null (sf_inBuff (c3_s k1)) /\
               (sf_inBuff (c3_s k1) = nullval -> sf_inSize (c3_s k1) + sf_outSize (c3_s k1) = 0)) as Hib.
  { unfold ring_rep. destruct (eq_dec (sf_inBuff (c3_s k1)) nullval) as [E|E]; [rewrite E; entailer! | ].
    Intros. entailer!. }
  destruct Hib as [Hib Hib0].
  forward.
  sep_apply (ring_free3 (sf_mem (c3_s k1)) (sf_inBuff (c3_s k1)) (sf_inSize (c3_s k1) + sf_outSize (c3_s k1))
               (sf_ring (c3_s k1))).
  assert_PROP (field_compatible t_dctx (DOT _customMem) d) as Hfcm by entailer!.
  rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
  (* F8: the stream buffer freed through the context's allocator *)
  forward_call (gv, tarray tuchar (sf_inSize (c3_s k1) + sf_outSize (c3_s k1)), sf_inBuff (c3_s k1), Ews,
                field_address t_dctx (DOT _customMem) d, sf_mem (c3_s k1), sf_given (c3_s k1) - local_held (c3_dict k1)).
  { split.
    - intros _. unfold cm_held. destruct (sf_mem (c3_s k1)); auto. simpl sizeof.
      rewrite Z.max_r by lia. subst k1. unfold sf_given. rewrite dctx_size_eq. simpl in *. lia.
    - intros Nb _. match goal with Hx: sf_inBuff _ <> nullval -> 0 < _ |- _ => specialize (Hx Nb) end.
      simpl sizeof. rewrite Z.max_r by lia. lia. }
  rewrite given_par3 by auto.
  forward. forward. forward.
  forward.
  sep_apply (tabs_rep_uninit gv d (c3_tabs k1)). Intros lxb. unfold tables_uninit, lit_extra_at. Intros.
  assert (Hfcl: field_compatible t_dctx (DOT _litExtraBuffer) d).
  { destruct Hfcm as (? & ? & ? & ? & ?). repeat split; auto. apply compute_in_members_true_iff. reflexivity. }
  sep_apply (lit_extra_mb d (zbytes lxb)).
  forward_call (Ews, field_address t_dctx (DOT _litExtraBuffer) d, 0, 65568).
  sep_apply (lit_extra_zero d).
  sep_apply (cm_fold3 d (cmem_v (sf_mem (c3_s k1)))).
  sep_apply (params_give d).
  sep_apply (mgroup_fold3 (sf_mem (c3_s k1)) d (sf_given (s_par3 (c3_s k1) (local_held (c3_dict k1))))
               ltac:(assumption)).
  forward.
  thaw FR2. thaw FR1.
  try subst k1.
  destruct (reset_par_rel3 gv _ _ R1 (or_introl eq_refl) Hlh) as (R1' & R2' & R3').
  (* the tables zeroed, the stream at zdss_init with no call without progress: a clean context *)
  assert (R4': ex_on3 SR (reset_par (set_ss st ss_init)) (k_par3 (k_reset3 k))).
  { unfold ex_on3. intros _ _ _.
    exact (sr_ex_clean SR (c3_s (k_par3 (k_reset3 k))) (c3_fs (k_par3 (k_reset3 k))) eq_refl eq_refl eq_refl
             eq_refl eq_refl). }
  Exists 0 (reset_par (set_ss st ss_init)). unfold DC3x, DC3_of. Exists (k_par3 (k_reset3 k)).
  unfold ctx_rep3, ctx_body3, fgroup3, sgroup, k_par3, s_par3, k_reset3, s_reset3, c3_raise, c3_with_s, c3_with_fs,
    sf_with_mem, tabs_rep, tables_uninit, ring_rep; simpl.
  unfold k_par3, s_par3, k_reset3, s_reset3, c3_raise, c3_with_s, c3_with_fs, sf_with_mem in R1', R2', R3', R4';
    simpl in R1', R2', R3', R4'.
  entailer!.
  split; [ | apply par_ok_dflt].
  unfold reset_post, ZSTD_reset_session_only, ZSTD_reset_parameters; simpl. split; reflexivity.
  all: unfold sf_given; simpl; apply derives_refl.
Qed.

Lemma body_reset3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_DCtx_reset (ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  unfold DC3x, DC3_of. Intros k.
  destruct H as [Hd | [Hd | Hd]]; subst dir.
  - apply (reset3_session gv d st k); assumption.
  - apply (reset3_params gv d st k); assumption.
  - apply (reset3_both gv d st k); assumption.
Qed.

Lemma par_rel3 (gv: globals) st k p' :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ss_quiet st k -> dc_bl st = None ->
  base_rel3 (set_par st p') (c3_with_par k p') /\
  (dc_ss (set_par st p') <> ss_init -> ss_err (dc_ss (set_par st p')) = false ->
     SR gv (set_par st p') (c3_with_par k p') \/
     (dc_ss (set_par st p') = ss_restart /\ sf_stage (c3_s (c3_with_par k p')) = 0)) /\
  (forall ba, dc_bl (set_par st p') = Some ba ->
     BR (c3_par (c3_with_par k p')) ba (c3_fs (c3_with_par k p')) (c3_tabs (c3_with_par k p')) (sf_hbuf (c3_s (c3_with_par k p')))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HB Hss Hbl.
  split; [ | split].
  - split; [exact H1 | split; [reflexivity | exact (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9))))))]].
  - apply (ss_quiet_sr gv). exact Hss.
  - simpl. intros ba Hba. rewrite Hbl in Hba. discriminate.
Qed.

Lemma stable_rel3 (gv: globals) st k b :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ss_quiet st k ->
  base_rel3 (set_stable st b) (c3_with_stable k b) /\
  (dc_ss (set_stable st b) <> ss_init -> ss_err (dc_ss (set_stable st b)) = false ->
     SR gv (set_stable st b) (c3_with_stable k b) \/
     (dc_ss (set_stable st b) = ss_restart /\ sf_stage (c3_s (c3_with_stable k b)) = 0)) /\
  (forall ba, dc_bl (set_stable st b) = Some ba ->
     BR (c3_par (c3_with_stable k b)) ba (c3_fs (c3_with_stable k b)) (c3_tabs (c3_with_stable k b)) (sf_hbuf (c3_s (c3_with_stable k b)))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HB Hss.
  split; [ | split].
  - split; [reflexivity | exact (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 H9)))))))].
  - apply (ss_quiet_sr gv). exact Hss.
  - simpl. exact HB.
Qed.

(* a setter's parameters or output mode on a quiet context, before any stream or between two frames (fin3) *)
Lemma par_fin3 (gv: globals) (b: bool) st k p' :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ss_quiet st k -> dc_bl st = None -> (b = false -> ex_on3 SR st k /\ dc_ss st = ss_init) ->
  let st' := fin3 b (set_par st p') in let k' := c3_with_par k p' in
  base_rel3 st' k' /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false -> SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
  (forall ba, dc_bl st' = Some ba -> BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))) /\
  ex_on3 SR st' k'.
Proof.
  intros Hb HB Hq Hbl Hx. destruct (par_rel3 gv st k p' Hb HB Hq Hbl) as (R1 & _ & R3).
  apply (fin3_rel gv b _ _ R1 Hq R3). intros E. destruct (Hx E). apply ex3_par; auto.
Qed.

Lemma stable_fin3 (gv: globals) (b: bool) st k v :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ss_quiet st k -> (b = false -> ex_on3 SR st k /\ dc_ss st = ss_init) ->
  let st' := fin3 b (set_stable st v) in let k' := c3_with_stable k v in
  base_rel3 st' k' /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false -> SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
  (forall ba, dc_bl st' = Some ba -> BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))) /\
  ex_on3 SR st' k'.
Proof.
  intros Hb HB Hq Hx. destruct (stable_rel3 gv st k v Hb HB Hq) as (R1 & _ & R3).
  apply (fin3_rel gv b _ _ R1 Hq R3). intros E. destruct (Hx E). apply ex3_stable; auto.
Qed.

Lemma shl1_pow n : 0 <= n < 64 -> Int64.shl (Int64.repr 1) (Int64.repr n) = Int64.repr (2 ^ n).
Proof.
  intros Hn. rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia.
  rewrite two_p_correct, Int64.mul_commut, Int64.mul_one. reflexivity.
Qed.

Lemma ps_wlog p v : param_set p ZSTD_d_windowLogMax v =
  if ((10 <=? (if v =? 0 then 27 else v)) && ((if v =? 0 then 27 else v) <=? 31))%bool
  then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p;
               dp_wmax := 2 ^ (if v =? 0 then 27 else v); dp_multi := dp_multi p |}
  else None.
Proof. reflexivity. Qed.

Lemma par_ok_wmax p n : par_ok p -> 10 <= n <= 31 ->
  par_ok {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := 2 ^ n;
            dp_multi := dp_multi p |}.
Proof.
  unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hn.
  split; [auto | split; [auto | split; [auto | split; [ | auto]]]].
  split; apply Z.pow_le_mono_r; lia.
Qed.

Lemma ps_fmt p v : param_set p ZSTD_d_format v =
  if ((0 <=? v) && (v <=? 1))%bool
  then Some {| dp_fmt := v; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
               dp_multi := dp_multi p |}
  else None.
Proof. reflexivity. Qed.

Lemma ps_ign p v : param_set p ZSTD_d_forceIgnoreChecksum v =
  if ((0 <=? v) && (v <=? 1))%bool
  then Some {| dp_fmt := dp_fmt p; dp_ignore := v; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
               dp_multi := dp_multi p |}
  else None.
Proof. reflexivity. Qed.

Lemma ps_multi p v : param_set p ZSTD_d_refMultipleDDicts v =
  if ((0 <=? v) && (v <=? 1))%bool
  then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
               dp_multi := v |}
  else None.
Proof. reflexivity. Qed.

Lemma ps_bmax p v : param_set p ZSTD_d_maxBlockSize v =
  if ((v =? 0) || ((1024 <=? v) && (v <=? ZSTD_BLOCKSIZE_MAX)))%bool
  then Some {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := v; dp_wmax := dp_wmax p;
               dp_multi := dp_multi p |}
  else None.
Proof. reflexivity. Qed.

Lemma par_ok_fmt p v : par_ok p -> 0 <= v <= 1 ->
  par_ok {| dp_fmt := v; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
            dp_multi := dp_multi p |}.
Proof. unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hv. repeat split; auto; lia. Qed.

Lemma par_ok_ign p v : par_ok p -> 0 <= v <= 1 ->
  par_ok {| dp_fmt := dp_fmt p; dp_ignore := v; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
            dp_multi := dp_multi p |}.
Proof. unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hv. repeat split; auto; lia. Qed.

Lemma par_ok_multi p v : par_ok p -> 0 <= v <= 1 ->
  par_ok {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := dp_wmax p;
            dp_multi := v |}.
Proof. unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hv. repeat split; auto; lia. Qed.

Lemma par_ok_bmax p v : par_ok p -> v = 0 \/ 1024 <= v <= ZSTD_BLOCKSIZE_MAX ->
  par_ok {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := v; dp_wmax := dp_wmax p;
            dp_multi := dp_multi p |}.
Proof. unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hv. repeat split; auto; lia. Qed.

Lemma par_ok_wm p m : par_ok p -> 1024 <= m <= 2147483648 ->
  par_ok {| dp_fmt := dp_fmt p; dp_ignore := dp_ignore p; dp_bmax := dp_bmax p; dp_wmax := m;
            dp_multi := dp_multi p |}.
Proof.
  unfold par_ok; cbn [dp_fmt dp_ignore dp_bmax dp_wmax dp_multi]; intros (? & ? & ? & ? & ?) Hm.
  repeat split; auto; change (2 ^ 10) with 1024; change (2 ^ 31) with 2147483648; lia.
Qed.

Lemma bool_repr_zero (b: bool) : Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. destruct b; intros Hc; auto; exfalso; apply Int.one_not_zero; exact Hc. Qed.

Lemma bool_repr_nz (b: bool) : Int.repr (if b then 1 else 0) <> Int.zero -> b = true.
Proof. destruct b; intros Hc; auto; exfalso; apply Hc; reflexivity. Qed.


Lemma ctx_stage_split gv p c :
  ctx_rep3 DENT TABS gv p c |--
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s c)))) p *
  (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s c)))) p -* ctx_rep3 DENT TABS gv p c).
Proof.
  unfold ctx_rep3, ctx_body3, sgroup. Intros.
  cancel. rewrite <- wand_sepcon_adjoint.
  unfold ctx_rep3, ctx_body3, sgroup. entailer!.
Qed.

Ltac err_post c st :=
  Exists (Int64.unsigned (Int64.repr (-42))) st;
  unfold DC3x, DC3_of; Exists c;
  entailer!;
  try (match goal with |- _ /\ (dc_ss _ <> ss_init -> _) =>
         split; [ | apply ss_quiet_sr; assumption] end);
  split; [ | rewrite Int64.repr_unsigned; reflexivity].
Ltac bnd_false_rw :=
  match goal with Hx: Int.repr (if ?b then 1 else 0) = Int.zero |- _ =>
    apply bool_repr_zero in Hx; rewrite Hx end.
Ltac bnd_true :=
  match goal with Hx: Int.repr (if ?b then 1 else 0) <> Int.zero |- _ =>
    apply bool_repr_nz in Hx; apply andb_prop in Hx;
    let Ha := fresh "Ha" in let Hb := fresh "Hb" in
    destruct Hx as [Ha Hb]; apply Z.leb_le in Ha; apply Z.leb_le in Hb end.

(* a setter's result on the context st0 (st itself, or st with ss_next's stream) is its result on st *)
Ltac lift_res st0 Hres :=
  match goal with |- after_stage (setpar_res ?K ?V) _ ?r (fin3 _ ?s) /\ ?Q =>
    cut (setpar_res K V st0 r s /\ Q);
    [intros [HA HB]; split; [apply Hres; exact HA | exact HB] | unfold setpar_res]
  end.

Lemma body_setParameter3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_DCtx_setParameter
    (ZSTD_DCtx_setParameter_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  unfold DC3x, DC3_of. Intros c.
  assert (Hk: 0 <= k <= 2000) by
    (simpl in H; unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H; lia).
  Intros.
  match goal with Hb: base_rel3 st c |- _ => rename Hb into Hb0 end.
  match goal with Hx: dc_ss st <> ss_init -> _ |- _ => rename Hx into Hsr0 end.
  match goal with Hx: forall ba, dc_bl st = Some ba -> _ |- _ => rename Hx into Hbr0 end.
  match goal with Hx: dc_bl st = None |- _ => rename Hx into Hbl end.
  assert_PROP (Int.min_signed <= sf_stage (c3_s c) <= Int.max_signed) as Hsrange
    by (unfold ctx_rep3, ctx_body3, sgroup; entailer!).
  sep_apply (ctx_stage_split gv d c). Intros.
  match goal with |- semax _ (PROPx ?A (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx A (LOCALx Q (SEPx R))) break: (PROPx ((sf_stage (c3_s c) = 0) :: A) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_if.
    - (* a frame is being streamed: stage_wrong, nothing changed *)
      dloop. dloop. dloop. dloop. forward.
      sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s c)))) d)
                                   (ctx_rep3 DENT TABS gv d c)).
      Exists (Int64.unsigned (Int64.repr (-60))) st.
      unfold DC3x, DC3_of. Exists c.
      entailer!.
      split; [ | rewrite Int64.repr_unsigned; reflexivity].
      right. split; [ | left; split; reflexivity].
      intros Hi. pose proof Hb0 as (_ & _ & _ & _ & _ & _ & (_ & Hst) & _). destruct (Hst Hi) as [Hs _]. rewrite Hs in *. contradiction.
    - forward. entailer!. }
  Intros. match goal with H: sf_stage (c3_s c) = 0 |- _ => rename H into Hs0 end.
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s c)))) d)
                               (ctx_rep3 DENT TABS gv d c)).
  (* between two frames the setter applies to the context with a new stream, or the failed one kept (ss_next, a
     set_ss: the concrete state with the bound of a context's own allocator raised) *)
  match goal with Hx: ex_on3 SR st c |- _ => rename Hx into Hex end.
  assert (Hst0: exists st0 c0 b, base_rel3 st0 c0 /\
    (forall ba, dc_bl st0 = Some ba -> BR (c3_par c0) ba (c3_fs c0) (c3_tabs c0) (sf_hbuf (c3_s c0))) /\
    ss_quiet st0 c0 /\ dc_bl st0 = None /\ (b = false -> ex_on3 SR st0 c0 /\ dc_ss st0 = ss_init) /\
    (forall r st', setpar_res k v st0 r st' -> after_stage (setpar_res k v) st r (fin3 b st')) /\
    (ctx_rep3 DENT TABS gv d c |-- ctx_rep3 DENT TABS gv d c0)).
  { destruct (Classical_Prop.classic (dc_ss st = ss_init)) as [Hi | Hn].
    - exists st, c, false. split; [exact Hb0 | split; [exact Hbr0 | split; [left; exact Hi | split; [exact Hbl | ]]]].
      split; [intros _; split; assumption | ].
      split; [| apply derives_refl].
      intros r st' Hr. left. split; assumption.
    - destruct (next_rel3 st c Hb0 Hn Hs0) as (Hb' & Hq').
      exists (set_ss st (ss_next (dc_ss st))), (c3_raise c (dp_wmax (dc_par st))), true.
      split; [exact Hb' | ].
      split; [intros ba Hba; simpl in Hba; rewrite Hbl in Hba; discriminate | ].
      split; [exact Hq' | split; [exact Hbl | ]].
      split; [discriminate | ].
      split; [| apply ctx_rep3_raise].
      intros r st' Hr. right. split; [exact Hn | right; exists st'; split; [exact Hr | reflexivity]]. }
  destruct Hst0 as (st0 & c0 & b & H3 & H5 & H1 & Hbl0 & Hex0 & Hres & Hc0).
  sep_apply Hc0. clear Hc0 Hb0 Hsr0 Hbr0 Hex.
  rename c into c_old. rename c0 into c.
  (* the clauses of the error results (nothing changed but, between two frames, dc_ex) *)
  destruct (fin3_rel gv b st0 c H3 H1 H5 (fun E => proj1 (Hex0 E))) as (E1 & E2 & E3 & E4).
  pose proof H3 as (_ & Hpar & _ & _ & _ & _ & _ & _).
  forward_if (PROP (False) LOCAL () SEP ()).
  - forward_if (temp _value (Vint (Int.repr (if v =? 0 then 27 else v)))).
    { forward. entailer!. }
    { forward. entailer!. destruct (Z.eqb_spec v 0); [subst; contradiction | reflexivity]. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((10 <= (if v =? 0 then 27 else v) <= 31) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { forward_call (ZSTD_d_windowLogMax, if v =? 0 then 27 else v).
      { destruct (v =? 0); rep_lia. }
      forward_if.
      - dloop. dloop. dloop. dloop. forward.
        err_post c (fin3 b st0). apply Hres. unfold setpar_res. rewrite ps_wlog. bnd_false_rw. split; reflexivity.
      - forward. entailer!. bnd_true. lia. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    set (v' := if v =? 0 then 27 else v) in *.
    rewrite Int.signed_repr, Int.unsigned_repr, shl1_pow by (unfold v' in *; rep_lia).
    forward.
    set (p' := {| dp_fmt := dp_fmt (dc_par st0); dp_ignore := dp_ignore (dc_par st0); dp_bmax := dp_bmax (dc_par st0);
                  dp_wmax := 2 ^ v'; dp_multi := dp_multi (dc_par st0) |}).
    destruct (par_fin3 gv b st0 c p' H3 H5 H1 Hbl0 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_par st0 p')).
    unfold DC3x, DC3_of. Exists (c3_with_par c p').
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    rewrite <- Hpar.
    entailer!.
    lift_res st0 Hres.
    rewrite ps_wlog. fold v'.
    replace ((10 <=? v') && (v' <=? 31))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    split; [split; [reflexivity | first [reflexivity | unfold p'; rewrite Hpar; reflexivity]] | ].
    unfold p'; rewrite <- Hpar. apply par_ok_wmax; auto.
  - (* format *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((0 <= v <= 1) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { forward_call (ZSTD_d_format, v).
      forward_if.
      - dloop. dloop. dloop. dloop. forward.
        err_post c (fin3 b st0). apply Hres. unfold setpar_res. rewrite ps_fmt. bnd_false_rw. split; reflexivity.
      - forward. entailer!. bnd_true. lia. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward. forward.
    set (p' := {| dp_fmt := v; dp_ignore := dp_ignore (dc_par st0); dp_bmax := dp_bmax (dc_par st0);
                  dp_wmax := dp_wmax (dc_par st0); dp_multi := dp_multi (dc_par st0) |}).
    destruct (par_fin3 gv b st0 c p' H3 H5 H1 Hbl0 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_par st0 p')).
    unfold DC3x, DC3_of. Exists (c3_with_par c p').
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    rewrite <- Hpar.
    entailer!.
    lift_res st0 Hres.
    rewrite ps_fmt.
    replace ((0 <=? v) && (v <=? 1))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    split; [split; [reflexivity | first [reflexivity | unfold p'; rewrite Hpar; reflexivity]] | ].
    unfold p'; rewrite <- Hpar. apply par_ok_fmt; auto; lia.
  - (* stableOutBuffer *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((0 <= v <= 1) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { forward_call (ZSTD_d_stableOutBuffer, v).
      forward_if.
      - dloop. dloop. dloop. dloop. forward.
        err_post c (fin3 b st0). apply Hres. unfold setpar_res. bnd_false_rw. split; reflexivity.
      - forward. entailer!. bnd_true. lia. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward. forward.
    destruct (stable_fin3 gv b st0 c (v =? 1) H3 H5 H1 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_stable st0 (v =? 1))).
    unfold DC3x, DC3_of. Exists (c3_with_stable c (v =? 1)).
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    assert (Hv: v = 0 \/ v = 1) by lia.
    destruct Hv; subst v; simpl; entailer!; apply Hres; unfold setpar_res; simpl; split; reflexivity.
  - (* forceIgnoreChecksum *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((0 <= v <= 1) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { forward_call (ZSTD_d_forceIgnoreChecksum, v).
      forward_if.
      - dloop. dloop. dloop. dloop. forward.
        err_post c (fin3 b st0). apply Hres. unfold setpar_res. rewrite ps_ign. bnd_false_rw. split; reflexivity.
      - forward. entailer!. bnd_true. lia. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward. forward.
    set (p' := {| dp_fmt := dp_fmt (dc_par st0); dp_ignore := v; dp_bmax := dp_bmax (dc_par st0);
                  dp_wmax := dp_wmax (dc_par st0); dp_multi := dp_multi (dc_par st0) |}).
    destruct (par_fin3 gv b st0 c p' H3 H5 H1 Hbl0 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_par st0 p')).
    unfold DC3x, DC3_of. Exists (c3_with_par c p').
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    rewrite <- Hpar.
    entailer!.
    lift_res st0 Hres.
    rewrite ps_ign.
    replace ((0 <=? v) && (v <=? 1))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    split; [split; [reflexivity | first [reflexivity | unfold p'; rewrite Hpar; reflexivity]] | ].
    unfold p'; rewrite <- Hpar. apply par_ok_ign; auto; lia.
  - (* refMultipleDDicts *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((0 <= v <= 1) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { forward_call (ZSTD_d_refMultipleDDicts, v).
      forward_if.
      - dloop. dloop. dloop. dloop. forward.
        err_post c (fin3 b st0). apply Hres. unfold setpar_res. rewrite ps_multi. bnd_false_rw. split; reflexivity.
      - forward. entailer!. bnd_true. lia. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ => forward_if (PROPx P (LOCALx Q (SEPx R))) end.
    { exfalso. discriminate. }
    { forward. entailer!. }
    forward. forward.
    set (p' := {| dp_fmt := dp_fmt (dc_par st0); dp_ignore := dp_ignore (dc_par st0); dp_bmax := dp_bmax (dc_par st0);
                  dp_wmax := dp_wmax (dc_par st0); dp_multi := v |}).
    destruct (par_fin3 gv b st0 c p' H3 H5 H1 Hbl0 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_par st0 p')).
    unfold DC3x, DC3_of. Exists (c3_with_par c p').
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    rewrite <- Hpar.
    entailer!.
    lift_res st0 Hres.
    rewrite ps_multi.
    replace ((0 <=? v) && (v <=? 1))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    split; [split; [reflexivity | first [reflexivity | unfold p'; rewrite Hpar; reflexivity]] | ].
    unfold p'; rewrite <- Hpar. apply par_ok_multi; auto; lia.
  - (* disableHuffmanAssembly: not a law's parameter *)
    exfalso. simpl in H. unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H; lia.
  - (* maxBlockSize *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx ((v = 0 \/ 1024 <= v <= 131072) :: P) (LOCALx Q (SEPx R))) end.
    { match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_loop (PROPx P (LOCALx Q (SEPx R)))
          break: (PROPx ((v = 0 \/ 1024 <= v <= 131072) :: P) (LOCALx Q (SEPx R))) end.
      { entailer!. }
      { forward_call (ZSTD_d_maxBlockSize, v).
        forward_if.
        - dloop. dloop. dloop. dloop. forward.
          err_post c (fin3 b st0). apply Hres. unfold setpar_res. rewrite ps_bmax.
          replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; auto).
          simpl orb. bnd_false_rw. split; reflexivity.
        - forward. entailer!. bnd_true. right. unfold ZSTD_BLOCKSIZE_MAX in *. lia. }
      }
    { forward. entailer!. }
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
    forward. forward.
    set (p' := {| dp_fmt := dp_fmt (dc_par st0); dp_ignore := dp_ignore (dc_par st0); dp_bmax := v;
                  dp_wmax := dp_wmax (dc_par st0); dp_multi := dp_multi (dc_par st0) |}).
    destruct (par_fin3 gv b st0 c p' H3 H5 H1 Hbl0 Hex0) as (R1 & R2 & R3 & R4).
    Exists 0 (fin3 b (set_par st0 p')).
    unfold DC3x, DC3_of. Exists (c3_with_par c p').
    unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
    rewrite <- Hpar.
    entailer!.
    lift_res st0 Hres.
    rewrite ps_bmax.
    replace ((v =? 0) || ((1024 <=? v) && (v <=? ZSTD_BLOCKSIZE_MAX)))%bool with true
      by (symmetry; unfold ZSTD_BLOCKSIZE_MAX in *;
          destruct (Z.eqb_spec v 0); [reflexivity | simpl; apply andb_true_intro; split; apply Z.leb_le; lia]).
    split; [split; [reflexivity | first [reflexivity | unfold p'; rewrite Hpar; reflexivity]] | ].
    unfold p'; rewrite <- Hpar. apply par_ok_bmax; auto; unfold ZSTD_BLOCKSIZE_MAX; lia.
  - (* default *)
    exfalso. simpl in H. unfold ZSTD_d_windowLogMax, ZSTD_d_format, ZSTD_d_stableOutBuffer,
       ZSTD_d_forceIgnoreChecksum, ZSTD_d_refMultipleDDicts, ZSTD_d_maxBlockSize in H.
    rewrite !Int.unsigned_repr in * by rep_lia. lia.
Qed.

(* the context after ZSTD_DCtx_refDDict(d, NULL): no dictionary, the local DDict's bytes given back *)
Definition k_nodict3 (k: cst3) : cst3 :=
  c3_with_dict (c3_with_s k (sf_with_held (c3_s k) (sf_held (c3_s k) - local_held (c3_dict k)))) df_none.

Lemma c3_with_set_same (k: cst3) : c3_with_set k (c3_sp k) (c3_set k) = k.
Proof. destruct k; reflexivity. Qed.

Lemma nodict_rel3 (gv: globals) st k :
  base_rel3 st k ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  dc_ss st = ss_init -> 0 <= local_held (c3_dict k) <= sf_held (c3_s k) ->
  base_rel3 (set_dict st None) (k_nodict3 k) /\
  (dc_ss (set_dict st None) <> ss_init -> ss_err (dc_ss (set_dict st None)) = false ->
     SR gv (set_dict st None) (k_nodict3 k) \/
     (dc_ss (set_dict st None) = ss_restart /\ sf_stage (c3_s (k_nodict3 k)) = 0)) /\
  (forall ba, dc_bl (set_dict st None) = Some ba ->
     BR (c3_par (k_nodict3 k)) ba (c3_fs (k_nodict3 k)) (c3_tabs (k_nodict3 k)) (sf_hbuf (c3_s (k_nodict3 k)))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HB Hss Hlh.
  split; [ | split].
  - split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [left; split; [reflexivity | left; reflexivity] | split]]]].
    + intros dr q dd dd' Hd; discriminate.
    + split; [exact H6 | split; [exact H7 | split; [exact H8 | ]]].
      destruct H9 as (Hm & Hh & Hn). split; [exact Hm | split].
      * apply (mem_room_less (c3_s k)); auto. simpl. lia.
      * intros E. exfalso. apply E. reflexivity.
  - simpl. intros Hc; exfalso; apply Hc; exact Hss.
  - simpl. exact HB.
Qed.

Lemma body_initDStream3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_initDStream (ZSTD_initDStream_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  dloop.
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (PROP () LOCAL (gvars gv; temp _zds d)
                           SEP (mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d (set_ex (set_ss st ss_init) false))) end.
  { entailer!. }
  { forward_call (gv, d, st, ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with Hx: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ Hx) as [-> ->] end.
    forward_call 0.
    replace (is_error_code 0) with false by reflexivity.
    forward_if. { exfalso; auto. }
    forward. entailer!. }
  unfold DC3x, DC3_of. Intros k.
  match goal with Hb: base_rel3 _ k |- _ => rename Hb into Hrel end.
  match goal with Hb: forall ba, dc_bl _ = Some ba -> BR _ _ _ _ _ |- _ => rename Hb into HBR end.
  pose proof Hrel as (_ & Hpar & _ & _ & _ & _ & (_ & Hst) & _ & Hmr). destruct (Hst eq_refl) as [Hs _]. clear Hst.
  assert_PROP (0 <= local_held (c3_dict k) <= sf_held (c3_s k)) as Hlh
    by (sep_apply (ctx_rep3_held gv d k); entailer!).
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (PROP () LOCAL (gvars gv; temp _zds d)
       SEP (mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv d (k_nodict3 k))) end.
  { entailer!. }
  { forward_call (@nil ptr_witness, gv, d, k, nullval, {| dd_bytes := nil; dd_ref := None; dd_buf := nullval; dd_ld := None |}).
    { simpl. unfold pws_pred; simpl. cancel. }
    { destruct Hmr as (_ & _ & Hl); exact Hl. }
    Intros vret. destruct vret as [r k']. cbn [fst snd] in *.
    assert (Hv: veqb nullval nullval = true)
      by (unfold veqb; destruct (Val.eq nullval nullval); [reflexivity | congruence]).
    match goal with Hx: refddict_int_res _ _ _ _ _ |- _ =>
      destruct Hx as [(Hc & _ & _) | (_ & sp' & l' & h' & Hr3 & _ & _ & Hh & ->)]; [contradiction | ] end.
    unfold refddict_res3 in Hr3; rewrite Hv in Hr3; destruct Hr3 as (-> & -> & ->).
    rewrite (Hh eq_refl). rewrite if_true by auto.
    rewrite Hv. cbn [negb andb].
    forward_call 0.
    replace (is_error_code 0) with false by reflexivity.
    forward_if. { exfalso; auto. }
    forward. entailer!. unfold k_nodict3, c3_with_dict, c3_with_s, c3_with_set; simpl. apply derives_refl. }
  unfold ctx_rep3, ctx_body3, fgroup3, cfg_fmt. Intros.
  simpl c3_par. simpl c3_fs. simpl c3_tabs. simpl c3_sp.
  forward.
  forward_call (dp_fmt (c3_par k)).
  { match goal with Hp: par_ok _ |- _ => destruct Hp as [Hf _]; exact Hf end. }
  forward.
  destruct (nodict_rel3 gv (set_ex (set_ss st ss_init) false) k Hrel HBR eq_refl Hlh) as (R1 & R2 & R3).
  assert (R4: ex_on3 SR (set_dict (set_ex (set_ss st ss_init) false) None) (k_nodict3 k))
    by (apply ex_on3_noex; reflexivity).
  unfold DC3x, DC3_of. Exists (k_nodict3 k).
  unfold ctx_rep3, ctx_body3, fgroup3, cfg_fmt; simpl.
  entailer!.
  - unfold fmt_mg; rewrite Hpar; reflexivity.
  - apply derives_refl.
Qed.

Lemma body_resetDStream3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_resetDStream (ZSTD_resetDStream_aspec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  dloop.
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (PROP () LOCAL (gvars gv; temp _dctx d)
                           SEP (mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d (set_ex (set_ss st ss_init) false))) end.
  { entailer!. }
  { forward_call (gv, d, st, ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with Hx: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ Hx) as [-> ->] end.
    forward_call 0.
    replace (is_error_code 0) with false by reflexivity.
    forward_if. { exfalso; auto. }
    forward. entailer!. }
  unfold DC3x, DC3_of. Intros k.
  match goal with Hb: base_rel3 _ k |- _ => rename Hb into Hrel end.
  pose proof Hrel as (_ & Hpar & _ & _ & _ & _ & _ & _).
  match goal with Hb: forall ba, dc_bl _ = Some ba -> BR _ _ _ _ _ |- _ => rename Hb into HBR end.
  unfold ctx_rep3, ctx_body3, fgroup3, cfg_fmt. Intros.
  forward.
  forward_call (dp_fmt (c3_par k)).
  { match goal with Hp: par_ok _ |- _ => destruct Hp as [Hf _]; exact Hf end. }
  forward.
  unfold DC3x, DC3_of. Exists k.
  unfold ctx_rep3, ctx_body3, fgroup3, cfg_fmt.
  entailer!.
  unfold fmt_mg; rewrite Hpar; reflexivity.
Qed.

Lemma body_setFormat3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_DCtx_setFormat
    (ZSTD_DCtx_setFormat_aspec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  forward_call (gv, d, st, ZSTD_d_format, v).
  { simpl; auto. }
  Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
  match goal with Hx: after_stage _ _ _ _ |- _ =>
    apply after_stage_init in Hx; [unfold setpar_res in Hx | assumption] end.
  forward.
  Exists r st'. entailer!.
Qed.

Lemma body_setMaxWindowSize3 :
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_DCtx_setMaxWindowSize
    (ZSTD_DCtx_setMaxWindowSize_aspec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  forward_call (Tsh, v_bounds, ZSTD_d_windowLogMax).
  { unfold dparam_known; simpl; auto. }
  change (dparam_bounds ZSTD_d_windowLogMax) with (10, 31). cbn [fst snd].
  forward. forward. forward. forward.
  replace (Int64.shl (Int64.repr (Int.signed (Int.repr 1))) (Int64.repr (Int.unsigned (Int.repr 10))))
    with (Int64.repr 1024) by reflexivity.
  replace (Int64.shl (Int64.repr (Int.signed (Int.repr 1))) (Int64.repr (Int.unsigned (Int.repr 31))))
    with (Int64.repr 2147483648) by reflexivity.
  unfold DC3x, DC3_of. Intros c. Intros.
  match goal with Hb: base_rel3 st c |- _ => rename Hb into Hrel end.
  match goal with Hb: forall ba, dc_bl _ = Some ba -> BR _ _ _ _ _ |- _ => rename Hb into HBR end.
  pose proof Hrel as (_ & Hpar & _ & _ & _ & _ & (_ & Hst) & _). destruct (Hst H0) as [Hs _]. clear Hst.
  sep_apply (ctx_stage_split gv d c). Intros.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. }
  { forward. forward_if. { exfalso. rewrite Hs in *. contradiction. }
    forward. entailer!. }
  sep_apply (modus_ponens_wand (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s c)))) d)
                               (ctx_rep3 DENT TABS gv d c)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((1024 <= m) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_if.
    - dloop. dloop. dloop. dloop. forward.
      err_post c st. change (2 ^ 10) with 1024. change (2 ^ 31) with 2147483648.
      replace ((1024 <=? m) && (m <=? 2147483648))%bool with false
        by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
      split; reflexivity.
    - forward. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx ((m <= 2147483648) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_if.
    - dloop. dloop. dloop. dloop. forward.
      err_post c st. change (2 ^ 10) with 1024. change (2 ^ 31) with 2147483648.
      replace ((1024 <=? m) && (m <=? 2147483648))%bool with false
        by (symmetry; apply andb_false_intro2; apply Z.leb_gt; lia).
      split; reflexivity.
    - forward. entailer!. }
  unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt. Intros.
  forward. forward.
  set (p' := {| dp_fmt := dp_fmt (dc_par st); dp_ignore := dp_ignore (dc_par st); dp_bmax := dp_bmax (dc_par st);
                dp_wmax := m; dp_multi := dp_multi (dc_par st) |}).
  destruct (par_rel3 gv st c p' Hrel HBR (or_introl H0) ltac:(assumption)) as (R1 & R2 & R3).
  assert (R4: ex_on3 SR (set_par st p') (c3_with_par c p')) by (apply ex3_par; assumption).
  Exists 0 (set_par st p').
  unfold DC3x, DC3_of. Exists (c3_with_par c p').
  unfold ctx_rep3, ctx_body3, cgroup3, fgroup3, cfg_fmt; simpl.
  rewrite <- Hpar.
  entailer!.
  change (Z.pow_pos 2 10) with 1024. change (Z.pow_pos 2 31) with 2147483648.
  replace ((1024 <=? m) && (m <=? 2147483648))%bool with true
    by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  split; [split; reflexivity | ].
  unfold p'; rewrite <- Hpar. apply par_ok_wm; auto.
Qed.

End Ctx.

Lemma bodies_ctxops3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_dParam_getBoundsP_spec3) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_dParam_withinBounds_spec3) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_setParameter_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_initDStream_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_resetDStream_aspec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_setMaxWindowSize_aspec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_setFormat_aspec (DC3x DENT TABS SR BR)).
Proof.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]];
    intros DENT TABS SR BR HD HT.
  - exists f_ZSTD_dParam_getBoundsP; split; [reflexivity | split; [reflexivity | ]].
    apply body_getBoundsP3; auto.
  - exists f_ZSTD_dParam_withinBounds; split; [reflexivity | split; [reflexivity | ]].
    apply body_withinBounds3; auto.
  - exists f_ZSTD_DCtx_setParameter; split; [reflexivity | split; [reflexivity | ]].
    apply body_setParameter3; auto.
  - exists f_ZSTD_DCtx_reset; split; [reflexivity | split; [reflexivity | ]].
    apply body_reset3; auto.
  - exists f_ZSTD_initDStream; split; [reflexivity | split; [reflexivity | ]].
    apply body_initDStream3; auto.
  - exists f_ZSTD_resetDStream; split; [reflexivity | split; [reflexivity | ]].
    apply body_resetDStream3; auto.
  - exists f_ZSTD_DCtx_setMaxWindowSize; split; [reflexivity | split; [reflexivity | ]].
    apply body_setMaxWindowSize3; auto.
  - exists f_ZSTD_DCtx_setFormat; split; [reflexivity | split; [reflexivity | ]].
    apply body_setFormat3; auto.
Qed.

End CM_body3_ctxops_1.
