(* Generic facts for linking the units of one harness program (Harness + (Malloc + (Libc + Zstd)),
   src/contracts/<h>.v): the whole program is QPprogram_OK, every unit's compspecs is included in the
   whole program's, every unit's internal function is one of the whole program's.  And list facts
   used to place the decoder's abstract specification list Int in the whole context. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.Clight_initial_world.
Require Import QuickProof.Env.
Require Import Zstd.proof.libc.LibcSpec.
Require Import Zstd.proof.asm6.Asm6Transfer.
Import compcert.lib.Maps.

Lemma PTree_sub_trans {A} (m1 m2 m3: PTree.t A): PTree_sub m1 m2 -> PTree_sub m2 m3 -> PTree_sub m1 m3.
Proof. intros H1 H2 i. eapply sub_option_trans; [apply H1 | apply H2]. Qed.

Lemma PTree_sub_refl {A} (m: PTree.t A): PTree_sub m m.
Proof. intros i. destruct (m ! i); simpl; auto. Qed.

Section Chain.
Context (pZ pL pM pH l1 l2 w: QP.program function)
  (L1: QPlink_progs pL pZ = Errors.OK l1) (L2: QPlink_progs pM l1 = Errors.OK l2)
  (L3: QPlink_progs pH l2 = Errors.OK w)
  (OKZ: QPprogram_OK pZ) (OKL: QPprogram_OK pL) (OKM: QPprogram_OK pM) (OKH: QPprogram_OK pH).

Definition OK1 : QPprogram_OK l1 := QPlink_progs_OK _ _ _ L1 OKL OKZ.
Definition OK2 : QPprogram_OK l2 := QPlink_progs_OK _ _ _ L2 OKM OK1.
Definition OKw : QPprogram_OK w := QPlink_progs_OK _ _ _ L3 OKH OK2.

Lemma chain_ce:
  PTree_sub (QP.prog_comp_env pZ) (QP.prog_comp_env w) /\
  PTree_sub (QP.prog_comp_env pL) (QP.prog_comp_env w) /\
  PTree_sub (QP.prog_comp_env pM) (QP.prog_comp_env w) /\
  PTree_sub (QP.prog_comp_env pH) (QP.prog_comp_env w).
Proof.
  destruct (linked_compspecs' _ _ _ (proj2 OKL) (proj2 OKZ) L1) as [C1 [SL SZ]].
  destruct (linked_compspecs' _ _ _ (proj2 OKM) C1 L2) as [C2 [SM S1]].
  destruct (linked_compspecs' _ _ _ (proj2 OKH) C2 L3) as [_ [SH S2]].
  split; [|split; [|split]]; auto; eapply PTree_sub_trans; eauto; eapply PTree_sub_trans; eauto.
Qed.

Lemma chain_cs (q: QP.program function) (OKq: QPprogram_OK q) (OKw': QPprogram_OK w) (cs: compspecs):
  cs = compspecs_of_QPcomposite_env _ (proj2 OKq) ->
  PTree_sub (QP.prog_comp_env q) (QP.prog_comp_env w) ->
  cspecs_sub cs (compspecs_of_QPcomposite_env _ (proj2 OKw')).
Proof. intros -> S. apply cspecs_sub_of_QPsub; auto. Qed.

Lemma chain_link:
  (forall i f, (QP.prog_defs pZ) ! i = Some (Gfun (Internal f)) -> (QP.prog_defs w) ! i = Some (Gfun (Internal f))) /\
  (forall i f, (QP.prog_defs pL) ! i = Some (Gfun (Internal f)) -> (QP.prog_defs w) ! i = Some (Gfun (Internal f))) /\
  (forall i f, (QP.prog_defs pM) ! i = Some (Gfun (Internal f)) -> (QP.prog_defs w) ! i = Some (Gfun (Internal f))) /\
  (forall i f, (QP.prog_defs pH) ! i = Some (Gfun (Internal f)) -> (QP.prog_defs w) ! i = Some (Gfun (Internal f))).
Proof.
  split; [|split; [|split]]; intros i f H.
  - apply (link_internal _ _ _ i f L3); right. apply (link_internal _ _ _ i f L2); right.
    apply (link_internal _ _ _ i f L1); right; auto.
  - apply (link_internal _ _ _ i f L3); right. apply (link_internal _ _ _ i f L2); right.
    apply (link_internal _ _ _ i f L1); left; auto.
  - apply (link_internal _ _ _ i f L3); right. apply (link_internal _ _ _ i f L2); left; auto.
  - apply (link_internal _ _ _ i f L3); left; auto.
Qed.
End Chain.

(* The decoder's specifications without its memcpy entry (memcpy is the libc unit's). *)
Definition Zrest (Int: funspecs) : funspecs := filter (fun ix => negb (Pos.eqb (fst ix) _memcpy)) Int.

Lemma Zrest_In Int j psi: In (j, psi) (Zrest Int) <-> In (j, psi) Int /\ j <> _memcpy.
Proof.
  unfold Zrest. rewrite filter_In. cbn [fst]. split; intros [H1 H2]; split; auto.
  - intros ->. rewrite Pos.eqb_refl in H2. discriminate.
  - destruct (Pos.eqb j _memcpy) eqn:E; auto. apply Pos.eqb_eq in E. contradiction.
Qed.

Lemma Zrest_ids Int (ids: list ident):
  (forall i, In i (map fst Int) <-> In i (_memcpy :: ids)) -> ~ In _memcpy ids ->
  forall i, In i (map fst (Zrest Int)) <-> In i ids.
Proof.
  intros H N i. split.
  - intros Hi. apply list_in_map_inv in Hi as [[j psi] [-> Hj]]. apply Zrest_In in Hj as [Hj Hm].
    simpl. assert (In j (map fst Int)) by (change j with (fst (j, psi)); apply in_map; auto).
    apply H in H0. destruct H0; [congruence | auto].
  - intros Hi. assert (In i (map fst Int)) by (apply H; right; auto).
    apply list_in_map_inv in H0 as [[j psi] [E Hj]]. simpl in E; subst j.
    change i with (fst (i, psi)). apply in_map. apply Zrest_In. split; auto. intros ->; contradiction.
Qed.

Lemma Zrest_NoDup Int: NoDup (map fst Int) -> NoDup (map fst (Zrest Int)).
Proof.
  unfold Zrest. induction Int as [|[j psi] Int IH]; intros H; [constructor|].
  cbn [filter map fst] in *. inv H. destruct (negb (Pos.eqb j _memcpy)); cbn [map fst]; auto.
  constructor; auto. intros Hin. apply H2.
  apply list_in_map_inv in Hin as [[k phi] [E Hk]]. simpl in E; subst k.
  apply filter_In in Hk as [Hk _]. change j with (fst (j, phi)). apply in_map; auto.
Qed.

(* Membership in a context without repeated names determines find_id. *)
Lemma find_id_of_In (G: funspecs) j psi: list_norepet (map fst G) -> In (j, psi) G -> find_id j G = Some psi.
Proof. intros. apply find_id_i; auto. Qed.

(* Two concrete identifier lists with the same elements, by computation. *)
Lemma same_ids (A B: list ident):
  forallb (fun i => id_in_list i B) A = true -> forallb (fun i => id_in_list i A) B = true ->
  forall i, In i A <-> In i B.
Proof.
  intros HA HB i. rewrite forallb_forall in HA, HB. split; intros H.
  - apply id_in_list_true. apply HA; auto.
  - apply id_in_list_true. apply HB; auto.
Qed.

Lemma NoDup_norepet {A} (l: list A): NoDup l <-> list_norepet l.
Proof. split; induction 1; constructor; auto. Qed.

Lemma perm_ids (l1 l2: list ident): NoDup l1 -> NoDup l2 -> (forall i, In i l1 <-> In i l2) -> Permutation l1 l2.
Proof. intros. apply NoDup_Permutation; auto. Qed.

(* A unit's varspecs are among the whole program's, by computation. *)
Definition vars_in (Vu V: varspecs) : bool :=
  forallb (fun jt => match find_id (fst jt) V with Some t => eqb_type (snd jt) t | None => false end) Vu.

Lemma vars_in_e Vu V j t: vars_in Vu V = true -> find_id j Vu = Some t -> find_id j V = Some t.
Proof.
  intros H F. apply find_id_e in F. unfold vars_in in H. rewrite forallb_forall in H.
  specialize (H _ F). simpl in H. destruct (find_id j V) as [t'|]; [|discriminate].
  apply eqb_type_true in H. subst; auto.
Qed.

Lemma find_id_app_in {A} (E R: list (ident * A)) i: In i (map fst E) -> find_id i (E ++ R) = find_id i E.
Proof.
  intros H. rewrite assoclists.find_id_app_char. destruct (find_id i E) eqn:F; auto.
  apply assoclists.find_id_None_iff in F. contradiction.
Qed.
