(* FS3 streaming, case zdss_loadHeader, piece C, segment s13 (LH3C_lib.v):
   RETURN_ERROR_IF(zds->fParams.windowSize > zds->maxWindowSize, frameParameter_windowTooLarge). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_util.
Local Open Scope logic.

Section CM_LH3C_s13_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC_win_ltu : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr y) (Int64.repr x) = (y <? x).
Proof.
intros x y Hx Hy. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
destruct (zlt y x); destruct (Z.ltb_spec y x); try lia; reflexivity.
Qed.

Lemma lhC_facts_of : forall a w k1 h c, par_ok (c3_par k1) -> 0 <= fh_windowSize h <= Int64.max_unsigned ->
  lhC_cfacts a w k1 h c ->
  Int64.ltu (Int64.repr (dp_wmax (c3_par k1))) (Int64.repr (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN)) = false ->
  lhC_facts a w k1 h c.
Proof.
intros a w k1 h c Hp Hws (Hsm & Hdd & Hc & Hd & Hdf & Hdn & _) Hlt.
unfold par_ok in Hp. unfold ZSTD_WINDOWSIZE_ABSMIN in *.
rewrite lhC_win_ltu in Hlt by rep_lia. apply Z.ltb_ge in Hlt.
unfold lhC_facts. repeat split; auto.
all: try (intros Hs Hf Hcs; unfold lhC_small in Hsm; exact (small_false _ _ _ _ Hsm Hs Hf Hcs)).
all: try lia.
Qed.

Lemma lhC_seg13_ok : lhC_seg13_stmt.
Proof.
unfold lhC_seg13_stmt. intros Espec DENT TABS BR a w hb h tbl d1 did1 HP.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hs & Hg & Hf & HA).
pose proof Hf as (Hhb5 & Hfcs & Hws & Hbsm & Hbsm' & Hck & Hft & Hft1 & Hft2 & Hdid & Hhs).
remember (k_A (w_k w) (fh_val h) d1 did1) as k1 eqn:Hk1.
assert (Hpar: c3_par k1 = c3_par (w_k w)) by (rewrite Hk1; reflexivity).
change (lhC_eqk k1 (k_A (w_k w) (fh_val h) d1 did1)) in Hk1.
unfold lhC_S4, lhC_post_l, ds_Delta. simplify_func_tycontext. unfold lhC_s13. abbreviate_semax.
Intros c.
apply semax_dowhile0_gen.
match goal with |- semax _ _ _ ?Q =>
  let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
abbreviate_semax.
unfold ds_LI_St, ds_LI_L, ctx_rep3t, fgroup3, cgroup3, frame_fields.
rewrite lhC_k_kx, lhC_fs_eq.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
cbn [fsu_fParams fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart
  fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
  fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
Intros.
match goal with Hx: par_ok _ |- _ => pose proof Hx as (Hpf & Hpi & Hpb & Hpw & Hpm) end.
forward.
match goal with |- context [temp _t'124 ?v] =>
  change v with (Vlong (Int64.repr (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN))) end.
forward.
forward_if.
- (* RC_window *)
  match goal with Hx: Int64.ltu _ _ = true |- _ => rename Hx into Hlt end.
  match goal with Hx: par_ok _ |- _ => pose proof Hx as Hpo; unfold par_ok in Hpo end.
  unfold ZSTD_WINDOWSIZE_ABSMIN in Hlt.
  rewrite lhC_win_ltu in Hlt by rep_lia. apply Z.ltb_lt in Hlt.
  abbreviate_semax. unfold MORE_COMMANDS, abbreviate.
  apply semax_dowhile0.
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
  { apply semax_dowhile0_gen.
    match goal with |- semax _ _ _ ?Q =>
      let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
    abbreviate_semax.
    forward_if.
    all: try (match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end).
    forward. entailer!. }
  abbreviate_semax. unfold MORE_COMMANDS, abbreviate.
  apply semax_dowhile0. apply semax_dowhile0.
  apply semax_return_v with (v := Vlong (Int64.repr (err_code ZSTD_error_frameParameter_windowTooLarge))).
  { entailer!. }
  { ret_err_val. }
  unfold POSTCONDITION, abbreviate. cbn [RA_return loop1_ret_assert].
  clear POSTCONDITION. try clear MORE_COMMANDS.
  unfold lh_ret. Exists (err_code ZSTD_error_frameParameter_windowTooLarge) (a_ipos a) (lw_k w (lhC_k k1 hb h c)).
  unfold ds_S_ip, ds_LI_L. rewrite ctx_rep3_t. Exists tbl.
  unfold ctx_rep3t, fgroup3, cgroup3, frame_fields.
  rewrite lhC_k_kx, lhC_fs_eq.
  cbn [lw_k w_k w_smw w_ipc w_opc w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
  cbn [fsu_fParams fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart
    fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
    fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  match goal with Hc: lhC_cfacts _ _ _ _ _ |- _ => pose proof Hc as (Hsm & Hdd & Hcold & Hdid' & Hdfh & Hdn & _) end.
  go_lower.
  apply andp_right.
  { apply prop_right. repeat split; auto; try (rewrite eqb_type_refl; reflexivity);
      try (unfold err_code, ZSTD_error_frameParameter_windowTooLarge; rep_lia).
    unfold lhC_eqk in Hk1. subst k1.
    rewrite <- lhC_fs_eq, <- lhC_k_kx.
    apply (RC_window a w hb h tbl d1 did1 c); auto.
    unfold ZSTD_WINDOWSIZE_ABSMIN. rewrite <- Hpar. lia. }
  entailer!.
- forward. Exists c.
  unfold ds_LI_S, ds_LI_L. rewrite ctx_rep3_t. Exists tbl.
  unfold ctx_rep3t, fgroup3, cgroup3, frame_fields.
  rewrite lhC_k_kx, lhC_fs_eq.
  cbn [lw_k w_k w_smw w_ipc w_opc w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
  cbn [fsu_fParams fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart
    fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
    fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  entailer!.
  match goal with Hc: lhC_cfacts _ _ _ _ _ |- _ => pose proof Hc as (_ & _ & _ & _ & _ & _ & Hlx) end.
  split; [apply lhC_facts_of; auto | exact Hlx].
Qed.

End CM_LH3C_s13_1.
