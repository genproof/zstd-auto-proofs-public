(* FS3 streaming, case zdss_loadHeader, piece C, segment s12 (LH3C_lib.v):
   zds->fParams.windowSize = MAX(zds->fParams.windowSize, 1 KiB). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_util.
Local Open Scope logic.

Section CM_LH3C_s12_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhC_fs0_fParams (k1: cst3) (hb: list Z) (h: frame_header) (c: lhc) :
  fs_fParams (lhC_fs0 k1 hb h c) = fh_val h.
Proof. unfold lhC_fs0. destruct (fh_frameType h =? 1); reflexivity. Qed.

Lemma lhC_seg12_ok : lhC_seg12_stmt.
Proof.
unfold lhC_seg12_stmt. intros Espec DENT TABS BR a w hb h tbl d1 did1 HP.
generalize (k_A (w_k w) (fh_val h) d1 did1). intros k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hs & Hg & Hf & HA).
destruct Hf as (Hhb5 & Hfcs & Hws & Hbsm & Hbsm' & Hck & Hft & Hft1 & Hft2 & Hdid & Hhs).
unfold lhC_S3, lhC_post, ds_Delta. simplify_func_tycontext. unfold lhC_s12. abbreviate_semax.
Intros c.
unfold ds_LI_St, ds_LI_L, ctx_rep3t, fgroup3, frame_fields.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
rewrite lhC_fs0_fParams.
Intros.
forward.
forward_if (temp _t'42 (Vlong (Int64.repr (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN)))).
{ forward. forward. entailer!.
  match goal with H: Int.unsigned (Int.shl _ _) < _ |- _ =>
    change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 10))) with 1024 in H end.
  rewrite Z.max_l by (unfold ZSTD_WINDOWSIZE_ABSMIN; lia). reflexivity. }
{ forward. entailer!.
  match goal with H: Int.unsigned (Int.shl _ _) >= _ |- _ =>
    change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 10))) with 1024 in H end.
  change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 10))) with 1024.
  rewrite Z.max_r by (unfold ZSTD_WINDOWSIZE_ABSMIN; lia). reflexivity. }
forward.
match goal with |- context [field_at _ _ (DOT _fParams) ?v _] =>
  change v with (fh_val (fh_adj h (fh_blockSizeMax h))) end.
unfold lhC_S4. Exists c.
unfold ds_LI_St, ds_LI_L, ctx_rep3t, fgroup3, frame_fields.
rewrite lhC_k_kx, lhC_fs_eq.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc lhC_kx c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
cbn [fsu_fParams fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart
  fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
  fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
entailer!.
Qed.

End CM_LH3C_s12_1.
