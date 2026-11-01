(* FS3: the buffer-less API: BR, ZSTD_decompressContinue, nextSrcSizeToDecompress, nextInputType,
   ZSTD_decompressBegin*. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.BL.BLDefs Zstd.proof.dec.v3.FS.BL.BLBody Zstd.proof.dec.v3.FS.BL.BLSub Zstd.proof.dec.v3.FS.BL.BLSmall Zstd.proof.dec.v3.FS.BL.BLBegin.
Local Open Scope logic.

Section CM_FS3_bl_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma BL3_ok : BL3_obligation.
Proof.
  intros DENT TABS HD HT. exists BR. intros SR.
  split; [| split; [| split]].
  - exists f_ZSTD_decompressContinue. split; [reflexivity | split; [reflexivity |]].
    eapply semax_body_funspec_sub; [exact (BL_body_ok DENT TABS SR BR HD HT) | apply BL_cont_sub; auto |].
    apply compute_list_norepet_e; reflexivity.
  - apply (BL_next_subs DENT TABS SR HD HT).
  - apply (BL_next_subs DENT TABS SR HD HT).
  - apply (BL_begin_sub DENT TABS SR HD HT).
Qed.

End CM_FS3_bl_1.
