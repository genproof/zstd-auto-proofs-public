(* Three facts for the counting allocators of the res_ harnesses (count_alloc, count_free of harness/res_free.c,
   res_memory_oneshot.c, res_memory_stream.c), whose specifications (CMem.cm_alloc_spec, cm_free_spec) name no
   global environment, while malloc and free (malloc_spec', free_spec') do. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Local Open Scope logic.

(* the global environment of a function's body, for calls whose specifications name it (GLOBALS) *)
Lemma semax_gvars_intro : forall {cs: compspecs} {Espec: OracleKind} Delta P Q R c Post,
  (forall gv, semax Delta (PROPx P (LOCALx (gvars gv :: Q) (SEPx R))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros. eapply semax_pre; [| apply extract_exists_pre; exact H].
  intro rho. unfold PROPx, LOCALx, SEPx, local, lift1. simpl. apply (exp_right (globals_of_env rho)). simpl.
  normalize. apply andp_right; auto. apply prop_right. unfold liftx, lift; simpl. split; auto. reflexivity.
Qed.

(* comparing a pointer one past the end of an object with NULL is defined *)
Lemma test_eq_null_weak : forall P p, isptr p -> P |-- weak_valid_pointer p ->
  P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros P p Hp H. destruct p; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. Opaque denote_tc_test_eq. simpl.
  apply andp_right; auto. apply prop_right. reflexivity.
Qed.

(* a block of 8 + n bytes: the size_t header and the n bytes given out *)
Lemma memory_block_split8 : forall sh b ofs n, 0 <= n -> Ptrofs.unsigned ofs + (8 + n) < Ptrofs.modulus ->
  memory_block sh (8 + n) (Vptr b ofs) = memory_block sh 8 (Vptr b ofs) * memory_block sh n (offset_val 8 (Vptr b ofs)).
Proof.
  intros. rewrite <- (Ptrofs.repr_unsigned ofs).
  rewrite (memory_block_split sh b (Ptrofs.unsigned ofs) 8 n) by rep_lia.
  rewrite Ptrofs.repr_unsigned. simpl. unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 8) by rep_lia.
  rewrite Z.add_comm. reflexivity.
Qed.
