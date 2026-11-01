(* FS3-bl BODY, stages 3/4, raw block: the DEBUGLOG loops `for (;;break) {}` and
   `for (;;break) { if (0) ... }` as cheap lemmas. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.raw.RawFacts.
Local Open Scope logic.

Section CM_RawDbg_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma dbg_loop {Espec: OracleKind} Delta (P: environ -> mpred) body c R :
  semax Delta P body (loop1_ret_assert P (overridePost P R)) ->
  semax Delta P c R -> semax Delta P (Ssequence (Sloop body Sbreak) c) R.
Proof.
  intros Hb H. apply semax_seq with P; [| exact H].
  apply semax_loop with P; [exact Hb |].
  eapply semax_pre; [| apply semax_break]. destruct R. change (ENTAIL Delta, P |-- P). apply andp_left2, derives_refl.
Qed.

Lemma dbg_skip_post {Espec: OracleKind} Delta (P: environ -> mpred) R :
  semax Delta P Sskip (loop1_ret_assert P (overridePost P R)).
Proof.
  eapply semax_post; [| | | | apply semax_skip]; destruct R.
  - change (ENTAIL Delta, P |-- P). apply andp_left2, derives_refl.
  - change (ENTAIL Delta, FF |-- P). apply andp_left2, FF_left.
  - change (ENTAIL Delta, FF |-- P). apply andp_left2, FF_left.
  - intros vl. change (ENTAIL Delta, FF |-- RA_return vl). apply andp_left2, FF_left.
Qed.

Lemma dbg_skip {Espec: OracleKind} Delta (P: environ -> mpred) c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof. intros H. apply dbg_loop; [apply dbg_skip_post | exact H]. Qed.

Lemma dbg_if0 {Espec: OracleKind} Delta (P: environ -> mpred) s c R :
  semax Delta P c R ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) R.
Proof.
  intros H. apply dbg_loop; [| exact H].
  eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
  - apply andp_left2. eapply derives_trans; [| apply now_later]. apply andp_right; [| apply derives_refl].
    intro rho. unfold tc_expr. simpl. apply TT_right.
  - eapply semax_pre; [| apply semax_ff]. intro rho. unfold local, lift1, liftx; simpl.
    apply andp_left2. apply andp_left2. apply prop_left. intros Ht. inv Ht.
  - eapply semax_pre; [| apply dbg_skip_post].
    apply andp_left2. apply andp_left1, derives_refl.
Qed.

(* the same loops at the head of a nested sequence *)
Lemma dbg_skip_seq {Espec: OracleKind} Delta (P: environ -> mpred) c d R :
  semax Delta P (Ssequence c d) R -> semax Delta P (Ssequence (Ssequence (Sloop Sskip Sbreak) c) d) R.
Proof. intros H. apply seq_assoc. apply dbg_skip. exact H. Qed.

Lemma dbg_if0_seq {Espec: OracleKind} Delta (P: environ -> mpred) s c d R :
  semax Delta P (Ssequence c d) R ->
  semax Delta P (Ssequence (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) d) R.
Proof. intros H. apply seq_assoc. apply dbg_if0. exact H. Qed.

End CM_RawDbg_1.
