(* FS3-bl BODY stage 6: the frame group's join after stage 6 (split from S6Help for its check time). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s6.S6Help.
Local Open Scope logic.

Section CM_S6Join_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s6_fcore3_join7 p fs pr e :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 7)) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p * s6_fc_rest p fs pr |--
  fcore3 p (fsu_stage (fsu_expected fs (vlong e)) (Vint (Int.repr 7))) pr nullval.
Proof. intros. unfold fcore3, s6_fc_rest, frame_fields, fsu_stage, fsu_expected, vlong. simpl. entailer!. Qed.

End CM_S6Join_1.
