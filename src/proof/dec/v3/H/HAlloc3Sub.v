(* The allocation helpers' specifications for any allocator (HAlloc3) against the older ones:
   - for any class CMI they imply DecIface's default-allocator specifications (take am = None, h = 0), which the
     v2 bodies and B's proofs were written against;
   - for any class CMI they imply the same specifications at the class cmem_none, whose own-allocator cases are
     vacuous (cm_have (Some m) h is FF there): B's bodies, proved with H_exports3 at cmem_none, stay proved in a
     program whose helpers have the specifications of any class. *)
Require Export Zstd.proof.dec.DecIface.
Require Export Zstd.proof.dec.v3.H.HAlloc3.
Local Open Scope logic.

Section Sub.
Context {CMI: cmem_preds}.

Lemma customMallocP_cm_sub_dflt :
  funspec_sub (snd ZSTD_customMallocP_cm_spec) (snd ZSTD_customMallocP_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[gv t] shm] pm] [g args]. simpl.
  Exists (gv, t, shm, pm, @None cmem, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; repeat split; auto; congruence |].
    apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl.
    Intros q. Exists q. unfold cm_have, blk_tok. rewrite emp_sepcon.
    apply andp_right; [apply prop_right; auto |]. apply derives_refl.
Qed.

Lemma customCallocP_cm_sub_dflt :
  funspec_sub (snd ZSTD_customCallocP_cm_spec) (snd ZSTD_customCallocP_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[gv n] shm] pm] [g args]. simpl.
  Exists (gv, n, shm, pm, @None cmem, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; repeat split; auto; congruence |].
    apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl.
    Intros q. Exists q. unfold cm_have, blk_tok. rewrite emp_sepcon.
    apply andp_right; [apply prop_right; auto |]. apply derives_refl.
Qed.

Lemma customFreeP_cm_sub_dflt :
  funspec_sub (snd ZSTD_customFreeP_cm_spec) (snd ZSTD_customFreeP_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[gv t] q] shm] pm] [g args]. simpl.
  Exists (gv, t, q, shm, pm, @None cmem, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; repeat split; auto; congruence |].
    apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl.
    unfold cm_have. rewrite !sepcon_emp. apply derives_refl.
Qed.

Lemma customMem_copy_cm_sub_dflt :
  funspec_sub (snd ZSTD_customMem_copy_cm_spec) (snd ZSTD_customMem_copy_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[shd pd] shs] ps] [g args]. simpl.
  Exists (shd, pd, shs, ps, @None cmem) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; repeat split; auto |]. apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

(* own-allocator cases are vacuous at cmem_none *)
Lemma cm_have_none_some (m: cmem) (h: Z) : @cm_have cmem_none (Some m) h |-- FF.
Proof. unfold cm_have. simpl. rewrite sepcon_FF. apply derives_refl. Qed.

Lemma customMallocP_cm_sub_none :
  funspec_sub (snd (@ZSTD_customMallocP_cm_spec CMI)) (snd (@ZSTD_customMallocP_cm_spec cmem_none)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[gv t] shm] pm] am] h] [g args]. simpl.
  destruct am as [m|].
  - apply andp_left2. eapply derives_trans; [| apply FF_left].
    unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. unfold local, lift1, liftx, argsassert2assert; simpl.
    rewrite ?sepcon_emp, ?sepcon_FF, ?FF_sepcon. normalize. unfold LOCALx; simpl. normalize.
  - Exists (gv, t, shm, pm, @None cmem, h) (@emp mpred _ _). rewrite emp_sepcon. simpl.
    apply andp_right; [apply andp_left2; apply derives_refl |].
    apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma customCallocP_cm_sub_none :
  funspec_sub (snd (@ZSTD_customCallocP_cm_spec CMI)) (snd (@ZSTD_customCallocP_cm_spec cmem_none)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[gv n] shm] pm] am] h] [g args]. simpl.
  destruct am as [m|].
  - apply andp_left2. eapply derives_trans; [| apply FF_left].
    unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. unfold local, lift1, liftx, argsassert2assert; simpl.
    rewrite ?sepcon_emp, ?sepcon_FF, ?FF_sepcon. normalize. unfold LOCALx; simpl. normalize.
  - Exists (gv, n, shm, pm, @None cmem, h) (@emp mpred _ _). rewrite emp_sepcon. simpl.
    apply andp_right; [apply andp_left2; apply derives_refl |].
    apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

Lemma customFreeP_cm_sub_none :
  funspec_sub (snd (@ZSTD_customFreeP_cm_spec CMI)) (snd (@ZSTD_customFreeP_cm_spec cmem_none)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[gv t] q] shm] pm] am] h] [g args]. simpl.
  destruct am as [m|].
  - apply andp_left2. eapply derives_trans; [| apply FF_left].
    unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. unfold local, lift1, liftx, argsassert2assert; simpl.
    rewrite ?sepcon_emp, ?sepcon_FF, ?FF_sepcon. normalize. unfold LOCALx; simpl. normalize.
  - Exists (gv, t, q, shm, pm, @None cmem, h) (@emp mpred _ _). rewrite emp_sepcon. simpl.
    apply andp_right; [apply andp_left2; apply derives_refl |].
    apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
Qed.

End Sub.
