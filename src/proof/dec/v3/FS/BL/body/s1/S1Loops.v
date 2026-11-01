(* FS3-bl BODY stage 1: the DEBUGLOG loops (do {} while (0)) of FORWARD_IF_ERROR, without symbolic
   execution. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s1.S1Vst.
Local Open Scope logic.

Section CM_S1Loops_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s1_skiploop {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H. eapply semax_seq; [| exact H].
  apply semax_loop_nocontinue.
  apply -> semax_skip_seq.
  eapply semax_pre; [| apply semax_break]. destruct R. cbn. intros x. apply andp_left2. apply derives_refl.
Qed.

Lemma s1_ifloop {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) X c R :
  semax Delta P c R ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) X Sskip) Sbreak) c) R.
Proof.
  intros H. eapply semax_seq; [| exact H].
  apply semax_loop_nocontinue.
  apply semax_seq with P.
  - eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
    + eapply derives_trans; [| apply now_later]. apply andp_right; [| apply andp_left2, derives_refl].
      intro rho. unfold tc_expr. simpl. apply TT_right.
    + eapply semax_pre; [| apply semax_ff]. intro rho. unfold local, lift1, liftx; simpl.
      apply andp_left2. apply andp_left2. unfold typed_true; simpl. normalize. compute in H0. discriminate H0.
    + eapply semax_post; [| | | | apply semax_skip].
      all: destruct R; cbn; intros; apply andp_left2; try apply andp_left1; try apply derives_refl; try apply FF_left.
  - eapply semax_pre; [| apply semax_break]. destruct R. cbn. intros x. apply andp_left2. apply derives_refl.
Qed.

End CM_S1Loops_1.
