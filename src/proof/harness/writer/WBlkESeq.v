(* `Ssequence s K` from the right-nested form `sq_with n s K`: an if branch
   followed by the rest of the body is proved in the segments' continuation style. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.WBlkSeg.

Lemma unfold_sq_with : forall s K,
  unfold_Ssequence (sq_with (sq_len s) s K) = unfold_Ssequence (Ssequence s K).
Proof.
  induction s; intros K; try reflexivity.
  cbn [sq_len sq_with unfold_Ssequence]. rewrite IHs2. cbn [unfold_Ssequence].
  rewrite app_assoc. reflexivity.
Qed.

Lemma sq_with_seq : forall {CS: compspecs} {Espec: OracleKind} Delta s K P R,
  semax Delta P (sq_with (sq_len s) s K) R -> semax Delta P (Ssequence s K) R.
Proof.
  intros. eapply semax_unfold_Ssequence; [| exact H]. apply unfold_sq_with.
Qed.

(* re-packing the PROP facts moved into the context by Intros *)
Lemma ent_props : forall {CS: compspecs} Delta (Ps: list Prop) L S,
  fold_right and True Ps ->
  ENTAIL Delta, PROPx [] (LOCALx L (SEPx S)) |-- PROPx Ps (LOCALx L (SEPx S)).
Proof.
  intros. apply andp_left2. unfold PROPx. apply andp_right.
  - apply prop_right. exact H.
  - apply andp_left2. apply derives_refl.
Qed.
