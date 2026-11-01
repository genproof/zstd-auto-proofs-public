(* Subtree H, API v3: the API specification of ZSTD_getFrameHeader_advanced (Spec_api6: a plain src pointer, the
   whole buffer) from the window export DecIface3.ZSTD_getFrameHeader_advanced_spec3 (off = 0, N = |s|). *)
Require Import Zstd.proof.dec.H.HLemmas.
Require Import Zstd.proof.dec.v3.H.HLift34.
Local Open Scope logic.

Lemma getFrameHeader_advanced_api_sub :
  funspec_sub (snd ZSTD_getFrameHeader_advanced_spec3) (snd ZSTD_getFrameHeader_advanced_aspec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[gv shz] pz] v0] sh] src] s] fmt] [g args]. simpl.
  Exists (gv, shz, pz, v0, sh, src, Zlength s, zbytes s, 0, s, fmt) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  2: { apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2. apply derives_refl. }
  apply andp_left2.
  unfold PROPx, PARAMSx, GLOBALSx, SEPx, LOCALx; simpl.
  apply derives_extract_prop; intros Hp.
  apply derives_extract_prop; intros Ha. subst args.
  match goal with |- ?L |-- _ => assert (HL: L |-- !! isptr src) end.
  { apply andp_left2. unfold argsassert2assert. simpl. rewrite sepcon_emp. entailer!. }
  eapply derives_trans; [apply andp_right; [exact HL | apply derives_refl] |].
  apply derives_extract_prop; intros Hs.
  rewrite isptr_offset_val_zero by auto.
  destruct Hp as [A [B [C _]]].
  apply andp_right; [apply prop_right; split; [exact A | split; [apply win_ok_full; exact B | split; [exact C | exact I]]] |].
  apply andp_right; [apply prop_right; reflexivity | auto].
Qed.

Lemma H3_api_sub : api_sub [ ZSTD_getFrameHeader_advanced_aspec ] H3_specs.
Proof.
  apply Forall_cons; [| apply Forall_nil].
  exists (snd ZSTD_getFrameHeader_advanced_spec3). split; [reflexivity | apply getFrameHeader_advanced_api_sub].
Qed.
