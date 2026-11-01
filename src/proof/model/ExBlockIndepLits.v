(* The literals' stores of a block (ExBlock.x_lits_store) on two related memories (ExBlockIndepMem.rel) whose
   destination is all clean: they read only the block's input and the (clean) destination, so both runs fail
   or both succeed with the same placement, the destination stays all clean, and the cells of litExtraBuffer
   that will be read as literals are clean: [0, litSize) when all the literals go there, [0, XLITEXTRA) when
   they are split.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeBlkDefs Zstd.proof.model.ExBlockIndepMem Zstd.proof.model.ExBlockIndepCopy.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* related, nothing clean became dirty, and the K cells of region r from d clean *)
Definition CW (c: creg) (r: xreg) (d K: Z) (m1 m2: xmem) : Prop :=
  exists c', rel c' m1 m2 /\ cle c c' /\ forall j, d <= j < d + K -> c' r j.

Lemma wrn_C : forall vs c m1 m2 r d, rel c m1 m2 ->
  orel (CW c r d (Zlength vs)) (xm_wrn vs m1 r d) (xm_wrn vs m2 r d).
Proof.
  intros vs c m1 m2 r d HR.
  pose proof (wrn_rel vs vs c m1 m2 r d (fun _ => True) HR eq_refl (fun _ _ _ => eq_refl)) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. split.
  - intros r' x Hx. apply cwr_true_sup. exact Hx.
  - intros j Hj. apply cwr_in; auto.
Qed.

Lemma fwd_C : forall src k c m1 m2 rd d rs s, rs <> rd -> (forall j, cl_of c rs j) -> rel c m1 m2 ->
  orel (CW c rd d (Z.of_nat k)) (xm_fwd src k m1 rd d rs s) (xm_fwd src k m2 rd d rs s).
Proof.
  intros src k c m1 m2 rd d rs s Hne Hcl HR.
  pose proof (fwd_x src k c m1 m2 rd d rs s Hne HR) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. split.
  - apply cwr_cle. intros; right; apply Hcl.
  - intros j Hj. apply cwr_in; [reflexivity|lia|right; apply Hcl].
Qed.

(* the placement and the memory after the literals' stores *)
Definition LS (a b: xmem * xreg * Z * Z * bool) : Prop :=
  let '(m1, lr1, li1, lim1, sp1) := a in let '(m2, lr2, li2, lim2, sp2) := b in
  lr1 = lr2 /\ li1 = li2 /\ lim1 = lim2 /\ sp1 = sp2 /\
  exists c', rel c' m1 m2 /\ Aall c' /\
    (if sp1 then forall j, 0 <= j < XLITEXTRA -> c' R_lxb j
     else lr1 = R_lxb -> forall j, 0 <= j < lim1 -> c' R_lxb j).

Lemma cl_src : forall c j, cl_of c R_src j.
Proof. intros; exact I. Qed.

Lemma cl_dst : forall c j, Aall c -> cl_of c R_dst j.
Proof. intros c j HA; apply HA. Qed.

Lemma lits_store_inv : forall body lits lused m1 m2 op0 ews bsm cap str c, rel c m1 m2 -> Aall c ->
  orel LS (x_lits_store body lits lused m1 op0 ews bsm cap str) (x_lits_store body lits lused m2 op0 ews bsm cap str).
Proof.
  intros body lits lused m1 m2 op0 ews bsm cap str c HR HA.
  pose proof (Zlength_nonneg lits) as Hn.
  unfold x_lits_store. cbv zeta.
  destruct (x_alloc_loc cap (Zlength lits) bsm str); cbn [xl_is_split].
  - (* in dst after the block's room *)
    pose proof (wrn_C (repeat 0 32) c m1 m2 R_dst (op0 + bsm + XWILDCOPY + Zlength lits) HR) as K0.
    odest K0. destruct K0 as (c0 & K0 & Hc0 & _). assert (HA0: Aall c0) by (eapply RC_A; eauto).
    destruct (Z.land (byte_at body 0) 3 =? 0).
    + destruct (lused + XWILDCOPY <=? Zlength body).
      * cbn. repeat (split; [reflexivity|]). exists c0. split; auto. split; auto. discriminate.
      * pose proof (fwd_C body (Z.to_nat (Zlength lits)) c0 ma mb R_dst (op0 + bsm + XWILDCOPY) R_src
                      (lused - Zlength lits) ltac:(discriminate) (cl_src c0) K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|discriminate].
    + destruct (Z.land (byte_at body 0) 3 =? 1).
      * pose proof (wrn_C (repeat (byte_at body (lused - 1)) (Z.to_nat (Zlength lits))) c0 ma mb R_dst
                      (op0 + bsm + XWILDCOPY) K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|discriminate].
      * pose proof (wrn_C lits c0 ma mb R_dst (op0 + bsm + XWILDCOPY) K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|discriminate].
  - (* litExtraBuffer *)
    destruct (Z.land (byte_at body 0) 3 =? 0).
    + destruct (lused + XWILDCOPY <=? Zlength body).
      * cbn. repeat (split; [reflexivity|]). exists c. split; auto. split; auto. discriminate.
      * pose proof (fwd_C body (Z.to_nat (Zlength lits)) c m1 m2 R_lxb 0 R_src
                      (lused - Zlength lits) ltac:(discriminate) (cl_src c) HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. lia.
    + destruct (Z.land (byte_at body 0) 3 =? 1).
      * pose proof (wrn_C (repeat (byte_at body (lused - 1)) (Z.to_nat (Zlength lits))) c m1 m2 R_lxb 0 HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. rewrite Zlength_correct, repeat_length. lia.
      * pose proof (wrn_C lits c m1 m2 R_lxb 0 HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. lia.
  - (* split *)
    destruct (if Z.land (byte_at body 0) 3 <=? 1 then _ else _) as [[lr lb] lbe].
    assert (Hmz: orel (RC c) (if Z.land (byte_at body 0) 3 <=? 1 then xm_wrn (repeat 0 32) m1 R_dst lbe else Some m1)
                         (if Z.land (byte_at body 0) 3 <=? 1 then xm_wrn (repeat 0 32) m2 R_dst lbe else Some m2)).
    { destruct (Z.land (byte_at body 0) 3 <=? 1).
      - pose proof (wrn_C (repeat 0 32) c m1 m2 R_dst lbe HR) as K0. eapply orel_mono; [|exact K0].
        intros a b (c' & ? & ? & _). exists c'; auto.
      - exists c. split; auto. apply cle_refl. }
    odest Hmz. destruct Hmz as (c0 & K0 & Hc0). assert (HA0: Aall c0) by (eapply RC_A; eauto).
    destruct (Z.land (byte_at body 0) 3 =? 0).
    + destruct (lused + XWILDCOPY <=? Zlength body).
      * cbn. repeat (split; [reflexivity|]). exists c0. split; auto. split; auto. discriminate.
      * pose proof (fwd_C body (Z.to_nat (Zlength lits - XLITEXTRA)) c0 ma mb R_dst lb R_src
                      (lused - Zlength lits) ltac:(discriminate) (cl_src c0) K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _).
        pose proof (fwd_C body (Z.to_nat XLITEXTRA) c1 ma0 mb0 R_lxb 0 R_src
                      (lused - Zlength lits + (Zlength lits - XLITEXTRA)) ltac:(discriminate) (cl_src c1) K1) as K2.
        odest K2. destruct K2 as (c2 & K2 & Hc2 & Hr2).
        cbn. repeat (split; [reflexivity|]). exists c2. split; auto.
        split; [eapply RC_A; [eapply RC_A; eauto|eauto]|].
        intros j Hj. apply Hr2. unfold XLITEXTRA in *; lia.
    + destruct (Z.land (byte_at body 0) 3 =? 1).
      * pose proof (wrn_C (repeat (byte_at body (lused - 1)) (Z.to_nat (Zlength lits - XLITEXTRA))) c0 ma mb
                      R_dst lb K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _).
        pose proof (wrn_C (repeat (byte_at body (lused - 1)) (Z.to_nat XLITEXTRA)) c1 ma0 mb0 R_lxb 0 K1) as K2.
        odest K2. destruct K2 as (c2 & K2 & Hc2 & Hr2).
        cbn. repeat (split; [reflexivity|]). exists c2. split; auto.
        split; [eapply RC_A; [eapply RC_A; eauto|eauto]|].
        intros j Hj. apply Hr2. rewrite Zlength_correct, repeat_length. unfold XLITEXTRA in *; lia.
      * pose proof (wrn_C lits c0 ma mb lr lb K0) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & _). assert (HA1: Aall c1) by (eapply RC_A; eauto).
        pose proof (fwd_C body (Z.to_nat XLITEXTRA) c1 ma0 mb0 R_lxb 0 R_dst (lbe - XLITEXTRA)
                      ltac:(discriminate) (fun j => cl_dst c1 j HA1) K1) as K2.
        odest K2. destruct K2 as (c2 & K2 & Hc2 & Hr2). assert (HA2: Aall c2) by (eapply RC_A; eauto).
        pose proof (move_A body (Z.to_nat (Zlength lits - XLITEXTRA)) c2 ma1 mb1 (lb + XLITEXTRA - XWILDCOPY) R_dst lb
                      K2 (or_intror (conj eq_refl HA2))) as K3.
        odest K3. destruct K3 as (c3 & K3 & Hc3).
        cbn. repeat (split; [reflexivity|]). exists c3. split; auto.
        split; [eapply RC_A; eauto|].
        intros j Hj. apply Hc3, Hr2. unfold XLITEXTRA in *; lia.
  - (* the input (not chosen by x_alloc_loc): as litExtraBuffer *)
    destruct (Z.land (byte_at body 0) 3 =? 0).
    + destruct (lused + XWILDCOPY <=? Zlength body).
      * cbn. repeat (split; [reflexivity|]). exists c. split; auto. split; auto. discriminate.
      * pose proof (fwd_C body (Z.to_nat (Zlength lits)) c m1 m2 R_lxb 0 R_src
                      (lused - Zlength lits) ltac:(discriminate) (cl_src c) HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. lia.
    + destruct (Z.land (byte_at body 0) 3 =? 1).
      * pose proof (wrn_C (repeat (byte_at body (lused - 1)) (Z.to_nat (Zlength lits))) c m1 m2 R_lxb 0 HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. rewrite Zlength_correct, repeat_length. lia.
      * pose proof (wrn_C lits c m1 m2 R_lxb 0 HR) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1 & Hr1).
        cbn. repeat (split; [reflexivity|]). exists c1. split; auto. split; [eapply RC_A; eauto|].
        intros _ j Hj. apply Hr1. lia.
Qed.
