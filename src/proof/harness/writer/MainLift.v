(* main proved in G0 is proved in Gprog, for the 7 writer units. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WriterOK_detect.
Require Zstd.proof.harness.stable_out.WriterOK_stable_out.
Require Zstd.proof.harness.valid_dict.WriterOK_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WriterOK_valid_info.
Require Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WriterOK_valid_stream.

Section Generic.
Context {cs: compspecs}.

Lemma ml_find_id_app {A} i (l1 l2: list (ident * A)) :
  initial_world.find_id i (l1 ++ l2) =
  match initial_world.find_id i l1 with Some x => Some x | None => initial_world.find_id i l2 end.
Proof.
  induction l1 as [|[j x] l1 IH]; simpl; auto.
  destruct (Memory.EqDec_ident i j); auto.
Qed.

Lemma ml_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma ml_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma ml_make_tycontext_g_nil_none (Vs: varspecs) i :
  ~ In i (map fst Vs) -> Maps.PTree.get i (make_tycontext_g Vs nil) = None.
Proof.
  unfold make_tycontext_g; simpl.
  induction Vs as [|[j t] Vs IH]; simpl; intros H.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gso by (intro; subst; tauto). apply IH; tauto.
Qed.

(* entries of the small context are found unchanged in the big one *)
Lemma ml_G0_in (A E W H M: funspecs) :
  Forall (fun ix => initial_world.find_id (fst ix) H = Some (snd ix)) W ->
  forall i fs, initial_world.find_id i (A ++ E ++ W) = Some fs ->
               initial_world.find_id i (A ++ E ++ H ++ M) = Some fs.
Proof.
  intros HW i fs Hi.
  rewrite !ml_find_id_app in Hi |- *.
  destruct (initial_world.find_id i A); auto.
  destruct (initial_world.find_id i E); auto.
  apply initial_world.find_id_e in Hi.
  rewrite Forall_forall in HW. apply HW in Hi. change (initial_world.find_id i H = Some fs) in Hi.
  rewrite ml_find_id_app, Hi. reflexivity.
Qed.

Lemma ml_lift (V: varspecs) (A E W H M: funspecs) f spec :
  Forall (fun ix => initial_world.find_id (fst ix) H = Some (snd ix)) W ->
  list_disjoint (map fst V) (map fst (H ++ M)) ->
  semax_body V (A ++ E ++ W) f spec -> semax_body V (A ++ E ++ H ++ M) f spec.
Proof.
  intros HW HD Hb.
  eapply semax_body_subsumption; [apply Hb |].
  apply tycontext_sub_i99. split; intro i.
  - rewrite (ml_make_tycontext_g_find V (A ++ E ++ W) i).
    rewrite (ml_make_tycontext_g_find V (A ++ E ++ H ++ M) i).
    destruct (initial_world.find_id i (A ++ E ++ W)) as [fs|] eqn:E1.
    + rewrite (ml_G0_in A E W H M HW i fs E1). apply sub_option_refl.
    + destruct (in_dec Memory.EqDec_ident i (map fst V)) as [Hv|Hv].
      * destruct (initial_world.find_id i (A ++ E ++ H ++ M)) as [fs|] eqn:E2; [|apply sub_option_refl].
        exfalso.
        rewrite !ml_find_id_app in E1, E2.
        destruct (initial_world.find_id i A); [discriminate|].
        destruct (initial_world.find_id i E); [discriminate|].
        apply initial_world.find_id_e in E2. apply (in_map fst) in E2. simpl in E2.
        exact (HD i i Hv E2 eq_refl).
      * rewrite (ml_make_tycontext_g_nil_none V i Hv). exact Logic.I.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (A ++ E ++ W)) as [fs|] eqn:E1; [|exact Logic.I].
    rewrite (ml_G0_in A E W H M HW i fs E1). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

End Generic.

Lemma ml_disj (l1 l2: list ident) :
  forallb (fun i => negb (id_in_list i l1)) l2 = true -> list_disjoint l1 l2.
Proof.
  intros H x y Hx Hy ->.
  rewrite forallb_forall in H. apply H in Hy.
  destruct (id_in_list y l1) eqn:E; [discriminate|].
  exact (id_in_list_false _ _ E Hx).
Qed.

Ltac lift_unit :=
  intros DC DD WG WDS Hs Hmap HW Hb;
  eapply ml_lift; [exact HW | | exact Hb];
  rewrite map_app, Hmap; apply ml_disj; vm_compute; reflexivity.

Theorem main_lift_ok :
  Zstd.proof.harness.detect.WriterOK_detect.LiftOK /\
  Zstd.proof.harness.stable_out.WriterOK_stable_out.LiftOK /\
  Zstd.proof.harness.valid_dict.WriterOK_valid_dict.LiftOK /\
  Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.LiftOK /\
  Zstd.proof.harness.valid_info.WriterOK_valid_info.LiftOK /\
  Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.LiftOK /\
  Zstd.proof.harness.valid_stream.WriterOK_valid_stream.LiftOK.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    unfold Zstd.proof.harness.detect.WriterOK_detect.LiftOK, Zstd.proof.harness.stable_out.WriterOK_stable_out.LiftOK,
      Zstd.proof.harness.valid_dict.WriterOK_valid_dict.LiftOK, Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.LiftOK,
      Zstd.proof.harness.valid_info.WriterOK_valid_info.LiftOK, Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.LiftOK,
      Zstd.proof.harness.valid_stream.WriterOK_valid_stream.LiftOK;
    lift_unit.
Qed.
