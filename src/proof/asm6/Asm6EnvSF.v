(* The VST-externals of the units (QuickProof.Env's functions; memcpy and memmove are the libc unit's) as Component entries: SF_ok of each
   environment specification AT the whole program's compspecs CSW, in the world HonestEspec CSW
   (the body of the external is QuickProof.EnvBodies' semax_ext proof; any unit compspecs cs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import Zstd.proof.asm6.Asm6Lib QuickProof.EnvBodies.
Import compcert.lib.Maps.

Lemma SF_ok_external {Espec cs V} (p: QP.program function) (OK: QPprogram_OK p) G0 ix
  ef argsig retsig cc A P Q NEP NEQ:
  snd ix = mk_funspec (argsig, retsig) cc A P Q NEP NEQ ->
  (QP.prog_defs p) ! (fst ix) = Some (Gfun (External ef argsig retsig cc)) ->
  ef_sig ef = mksignature (map argtype_of_type argsig) (rettype_of_type retsig) cc ->
  ef_inline ef = false ->
  (forall gx ts x ret, Q ts x (make_ext_rval gx (rettype_of_type retsig) ret) &&
     !! Builtins0.val_opt_has_rettype ret (rettype_of_type retsig) |-- !! tc_option_val retsig ret) ->
  @body_lemma_of_funspec Espec ef (snd ix) ->
  @SF_ok Espec cs V p G0 ix.
Proof.
  destruct ix as [i phi]; simpl. intros EQ GET SIG INL TC BODY _ fd GET'. simpl in GET'. rewrite GET in GET'. inv GET'.
  subst; simpl. split3; [auto | auto | ]. split3; [auto | auto | ]. split3; [auto | auto | ]. split.
  - apply BODY.
  - apply (QPprogdefs_GFF OK GET).
Qed.

Ltac tc_post :=
  intros; simpl;
  repeat match goal with x: _ * _ |- _ => destruct x end;
  match goal with ret: option val |- _ => destruct ret as [v|] end;
  unfold make_ext_rval; simpl; unfold PROPx, LOCALx, SEPx, local, lift1; simpl;
  unfold_lift; simpl; normalize; unfold eval_id in *; simpl in *; subst; entailer!.

Section Env.
Context {cs: compspecs} (CSW: compspecs) {V: varspecs}.
Context (p: QP.program function) (OK: QPprogram_OK p) (G0: funspecs).

Lemma SF_ok_nondet_bytes:
  (QP.prog_defs p) ! _nondet_bytes = Some (Gfun (External
     (EF_external "nondet_bytes" (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default))
     ((tptr tuchar) :: tulong :: nil) tvoid cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 (@nondet_bytes_spec CSW).
Proof.
  intros GET.
  pose proof (@env_body_bytes CSW) as B.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact B].
  tc_post.
Qed.

Lemma SF_ok_nondet_u8:
  (QP.prog_defs p) ! _nondet_u8 = Some (Gfun (External
     (EF_external "nondet_u8" (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 nondet_u8_spec.
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_u8 CSW)].
  tc_post. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma SF_ok_nondet_u32:
  (QP.prog_defs p) ! _nondet_u32 = Some (Gfun (External
     (EF_external "nondet_u32" (mksignature nil AST.Xint cc_default)) nil tuint cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 nondet_u32_spec.
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_u32 CSW)].
  tc_post.
Qed.

Lemma SF_ok_nondet_size:
  (QP.prog_defs p) ! _nondet_size = Some (Gfun (External
     (EF_external "nondet_size" (mksignature nil AST.Xlong cc_default)) nil tulong cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 nondet_size_spec.
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_size CSW)].
  tc_post.
Qed.

Lemma SF_ok_gp_assert:
  (QP.prog_defs p) ! _gp_assert = Some (Gfun (External
     (EF_external "gp_assert" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default)) (tint :: nil) tvoid cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 gp_assert_spec.
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_assert CSW)].
  intros; simpl; auto.
Qed.

Lemma SF_ok_gp_assume:
  (QP.prog_defs p) ! _gp_assume = Some (Gfun (External
     (EF_external "gp_assume" (mksignature (AST.Xint :: nil) AST.Xvoid cc_default)) (tint :: nil) tvoid cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 gp_assume_spec.
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_assume CSW)].
  intros; simpl; auto.
Qed.

(* malloc/free: at the whole program's compspecs CSW (the malloc unit's externals). *)
Lemma SF_ok_malloc:
  (QP.prog_defs p) ! _quickproof_malloc = Some (Gfun (External
     (EF_external "quickproof_malloc" (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 (_quickproof_malloc, @malloc_spec' CSW).
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_malloc CSW)].
  intros; simpl. destruct x as [t gv].
  destruct ret as [v|]; unfold make_ext_rval; simpl; unfold PROPx, LOCALx, SEPx, local, lift1; simpl;
    unfold_lift; simpl; normalize.
  unfold eval_id in *; simpl in *. destruct (EqDec_val v nullval).
  - subst; apply prop_right; simpl; auto.
  - entailer!.
Qed.

Lemma SF_ok_free:
  (QP.prog_defs p) ! _quickproof_free = Some (Gfun (External
     (EF_external "quickproof_free" (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ->
  @SF_ok (@HonestEspec CSW) cs V p G0 (_quickproof_free, @free_spec' CSW).
Proof.
  intros GET.
  eapply (SF_ok_external p OK G0); [reflexivity | exact GET | reflexivity | reflexivity | | exact (@env_body_free CSW)].
  intros; simpl; auto.
Qed.
End Env.
