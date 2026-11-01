(* FS3-bl: the API specifications of ZSTD_decompressBegin, _usingDict, _usingDDict from B's exports (DecIface3),
   with BR = BLDefs.BR: the new frame satisfies BR (bl_begin ..). *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Require Import Zstd.proof.dec.v3.FS.BL.begin.BeginSub0 Zstd.proof.dec.v3.FS.BL.begin.BeginSub1 Zstd.proof.dec.v3.FS.BL.begin.BeginSub2.
Local Open Scope logic.

Section CM_BLBegin_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma BL_begin_sub : forall (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3),
  DENT_OK DENT -> TABS_OK TABS ->
  api_sub (B_api3 (DC3x DENT TABS SR BR) (DD3x DENT)) (B_exports3 DENT TABS).
Proof.
  intros DENT TABS SR HD HT.
  unfold api_sub, B_api3.
  repeat constructor.
  - eexists; split; [reflexivity | apply begin_sub0; exact HT].
  - eexists; split; [reflexivity | apply begin_sub1; exact HT].
  - eexists; split; [reflexivity | apply begin_sub2; exact HT].
Qed.

End CM_BLBegin_1.
