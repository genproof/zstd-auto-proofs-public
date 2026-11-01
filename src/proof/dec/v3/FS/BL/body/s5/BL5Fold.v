(* FS3-bl BODY, stage 5: folding the six fields of BL5Sep back into fcore3 (split from BL5Sep for check time). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Sep.
Local Open Scope logic.

Section CM_BL5Fold_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl5_fold_new p fs pr vc vd vq e s :
  par_ok pr -> vc = fs_validateChecksum fs -> vd = fs_decodedSize fs -> vq = fs_processedCSize fs ->
  field_at Ews t_dctx (DOT _validateChecksum) vc p * xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _decodedSize) vd p * field_at Ews t_dctx (DOT _processedCSize) vq p *
  field_at Ews t_dctx (DOT _expected) e p * field_at Ews t_dctx (DOT _stage) s p *
  bl5_rest p fs pr |-- fcore3 p (fsu_stage (fsu_expected fs e) s) pr nullval.
Proof. intros Hp -> -> ->. unfold fcore3, frame_fields, bl5_rest. cbn. apply andp_right; [apply prop_right; auto | cancel]. Qed.

Lemma bl5_fold_same p fs pr vc vd vq :
  par_ok pr -> vc = fs_validateChecksum fs -> vd = fs_decodedSize fs -> vq = fs_processedCSize fs ->
  field_at Ews t_dctx (DOT _validateChecksum) vc p * xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _decodedSize) vd p * field_at Ews t_dctx (DOT _processedCSize) vq p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  bl5_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros Hp -> -> ->. unfold fcore3, frame_fields, bl5_rest. apply andp_right; [apply prop_right; auto | cancel]. Qed.

End CM_BL5Fold_1.
