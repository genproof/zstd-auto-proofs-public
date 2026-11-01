(* Changing compspecs along cspecs_sub, generically (no computation on concrete environments).
   The assembly needs, for a unit's compspecs cs1 included in the whole program's cs2:
   the environment's specifications at cs2 are funspec_subs of the same specifications at cs1
   (nondet_bytes in the shape the harness proofs use, HarnessDefs.nondet_bytes_nn_spec). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zstd.proof.top.HarnessDefs.

(* The change_composite_env instance of any two compspecs, without computing it. *)
Definition cce_of (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Section CS.
Context (cs1 cs2: compspecs) (Hsub: cspecs_sub cs1 cs2).

(* Every type complete in cs1 means the same in cs2. *)
Lemma cs_preserve_of_sub: forall t,
  @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  cs_preserve_type cs1 cs2 (@coeq _ _ (cce_of cs1 cs2)) t = true.
Proof.
  destruct Hsub as [Hcenv _].
  assert (Hco: forall id co, (Maps.PTree.get id (@cenv_cs cs1)) = Some co ->
            (forall m, In m (co_members co) ->
               cs_preserve_type cs1 cs2 (@coeq _ _ (cce_of cs1 cs2)) (type_member m) = true) ->
            match Maps.PTree.get id (@coeq _ _ (cce_of cs1 cs2)) with
            | Some b => test_aux cs1 cs2 b id | None => false end = true).
  { intros id co H1 IHm.
    assert (H2: (Maps.PTree.get id (@cenv_cs cs2)) = Some co).
    { specialize (Hcenv id). rewrite H1 in Hcenv. exact Hcenv. }
    destruct (proj1 (@coeq_complete _ _ (cce_of cs1 cs2) id) (ex_intro _ co H2)) as [b Hb].
    rewrite Hb.
    pose proof (@coeq_consistent _ _ (cce_of cs1 cs2) id co b H2 Hb) as Hbe.
    unfold test_aux. rewrite H1, H2.
    assert (Hm: cs_preserve_members cs1 cs2 (@coeq _ _ (cce_of cs1 cs2)) (co_members co) = true).
    { clear - IHm. induction (co_members co) as [|m ms IH]; simpl; auto.
      rewrite IHm by (left; reflexivity). simpl. apply IH. intros; apply IHm; right; auto. }
    rewrite Hbe, Hm. simpl.
    rewrite (proj2 (eqb_list_spec _ eqb_member_spec _ _) eq_refl).
    rewrite (proj2 (eqb_su_spec _ _) eq_refl).
    rewrite (proj2 (eqb_attr_spec _ _) eq_refl). reflexivity. }
  intros t.
  pattern t; apply (@VST.veric.type_induction.type_ind (@cenv_cs cs1) (@cenv_consistent cs1)); clear t.
  intros t IH Ht.
  destruct t; simpl in Ht |- *; auto.
  - destruct ((Maps.PTree.get i (@cenv_cs cs1))) as [co|] eqn:E; [|discriminate].
    apply (Hco i co E). intros m Hm.
    rewrite Forall_forall in IH. apply (IH m Hm).
    pose proof (@cenv_legal_su cs1 i co E) as L.
    clear - L Hm. induction (co_members co) as [|m' ms IHms]; simpl in *; [contradiction|].
    apply andb_prop in L as [L1 L2]. destruct Hm; [subst; auto | auto].
  - destruct ((Maps.PTree.get i (@cenv_cs cs1))) as [co|] eqn:E; [|discriminate].
    apply (Hco i co E). intros m Hm.
    rewrite Forall_forall in IH. apply (IH m Hm).
    pose proof (@cenv_legal_su cs1 i co E) as L.
    clear - L Hm. induction (co_members co) as [|m' ms IHms]; simpl in *; [contradiction|].
    apply andb_prop in L as [L1 L2]. destruct Hm; [subst; auto | auto].
Qed.

(* The environment's specifications, given that preservation (cs_preserve_of_sub) as a hypothesis. *)
Section Specs.
Context (PRES: forall t, @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
                 cs_preserve_type cs1 cs2 (@coeq _ _ (cce_of cs1 cs2)) t = true).

Lemma ha_sub_eq: forall t, @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  hardware_alignof (@ha_env_cs cs1) t = hardware_alignof (@ha_env_cs cs2) t.
Proof.
  destruct Hsub as [Hc [Hh Hl]].
  induction t; simpl; intros; auto.
  - destruct (Maps.PTree.get i (@cenv_cs cs1)) eqn:E; try discriminate.
    destruct (proj1 (@ha_env_cs_complete cs1 i) (ex_intro _ c E)) as [z Hz].
    specialize (Hh i). rewrite Hz in *. simpl in Hh. rewrite Hh. auto.
  - destruct (Maps.PTree.get i (@cenv_cs cs1)) eqn:E; try discriminate.
    destruct (proj1 (@ha_env_cs_complete cs1 i) (ex_intro _ c E)) as [z Hz].
    specialize (Hh i). rewrite Hz in *. simpl in Hh. rewrite Hh. auto.
Qed.

Lemma la_sub_eq: forall t, @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  legal_alignas_type (@cenv_cs cs1) (@ha_env_cs cs1) (@la_env_cs cs1) t =
  legal_alignas_type (@cenv_cs cs2) (@ha_env_cs cs2) (@la_env_cs cs2) t.
Proof.
  pose proof Hsub as [Hc [Hh Hl]].
  induction t; intros H; try (simpl in H; discriminate);
    pose proof (complete_legal_cosu_type_complete_type _ _ H) as HC;
    simpl legal_alignas_type; try rewrite (ha_sub_eq _ H);
    try rewrite (expr_lemmas4.cenv_sub_alignof Hc _ HC); auto.
  - simpl in H, HC. rewrite IHt by auto.
    rewrite (expr_lemmas4.cenv_sub_sizeof Hc _ HC), (ha_sub_eq _ H). auto.
  - simpl in H. destruct (Maps.PTree.get i (@cenv_cs cs1)) eqn:E; try discriminate.
    destruct (proj1 (@la_env_cs_complete cs1 i) (ex_intro _ c E)) as [z Hz].
    specialize (Hl i). rewrite Hz in Hl. simpl in Hl. unfold legal_alignas_obs in *. rewrite Hz, Hl. auto.
  - simpl in H. destruct (Maps.PTree.get i (@cenv_cs cs1)) eqn:E; try discriminate.
    destruct (proj1 (@la_env_cs_complete cs1 i) (ex_intro _ c E)) as [z Hz].
    specialize (Hl i). rewrite Hz in Hl. simpl in Hl. unfold legal_alignas_obs in *. rewrite Hz, Hl. auto.
Qed.

Lemma natural_aligned_sub: forall na t, @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  @natural_aligned cs1 na t = @natural_aligned cs2 na t.
Proof.
  intros. unfold natural_aligned, is_aligned.
  rewrite (ha_sub_eq _ H), (la_sub_eq _ H). auto.
Qed.

Lemma malloc_sub: funspec_sub (@malloc_spec' cs2) (@malloc_spec' cs1).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [t gv] [g args]. simpl.
  unfold PROPx; simpl. normalize.
  assert (HP := PRES t H2).
  pose proof (@sizeof_change_composite _ _ (cce_of cs1 cs2) t HP) as E1.
  pose proof (@complete_legal_cosu_type_change_composite _ _ (cce_of cs1 cs2) t HP) as E2.
  pose proof (@malloc_token_change_composite _ _ (cce_of cs1 cs2) Ews t HP) as E3.
  pose proof (@data_at__change_composite _ _ (cce_of cs1 cs2) Ews t HP) as E4.
  pose proof (natural_aligned_sub natural_alignment t H2) as E5.
  Exists (t, gv) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  rewrite <- E1, <- E2, <- E3, <- E4, <- E5.
  apply andp_right; [apply andp_right; [apply prop_right; auto | ] |
    apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto].
  rewrite ptrofs_to_int64_repr by reflexivity. auto.
Qed.

Lemma free_sub: funspec_sub (@free_spec' cs2) (@free_spec' cs1).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[t p] gv] [g args]. simpl.
  Exists (t, p, gv) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [|
    apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto].
  unfold PROPx; simpl. unfold_for_go_lower; simpl. normalize.
  apply andp_right; [apply prop_right; auto|].
  apply sepcon_derives; auto.
  destruct (EqDec_val p nullval); auto.
  assert_PROP (@field_compatible cs1 t nil p).
  { rewrite sepcon_comm. apply sepcon_derives_prop. apply (@data_at__local_facts cs1). }
  destruct H1 as [_ [Hcl _]].
  assert (HP := PRES t Hcl).
  rewrite (@malloc_token_change_composite _ _ (cce_of cs1 cs2) Ews t HP).
  rewrite (@data_at__change_composite _ _ (cce_of cs1 cs2) Ews t HP). auto.
Qed.

Lemma nondet_bytes_sub: funspec_sub (snd (@nondet_bytes_nn_spec cs2)) (snd (@nondet_bytes_nn_spec cs1)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[buf n] sh] [g args]. simpl.
  Exists (buf, n, sh) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  assert (HP: cs_preserve_type cs1 cs2 (@coeq _ _ (cce_of cs1 cs2)) (tarray tuchar n) = true)
    by reflexivity.
  rewrite (@data_at__change_composite _ _ (cce_of cs1 cs2) sh _ HP).
  assert (E: forall v, @data_at cs1 sh (tarray tuchar n) v = @data_at cs2 sh (tarray tuchar n) v)
    by (intros; apply (@data_at_change_composite _ _ (cce_of cs1 cs2)); auto).
  apply andp_right; [apply andp_left2; auto|].
  apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2.
  apply exp_derives; intros bs. rewrite E. auto.
Qed.

Lemma JMeq_eq_rect_T: forall (A B: Type) (E: A = B) (v: A), JMeq v (eq_rect A (fun T => T) v B E).
Proof. intros. destruct E. apply JMeq_refl. Qed.

Lemma env_specs_sub: Logic.and
  (funspec_sub (@malloc_spec' cs2) (@malloc_spec' cs1)) (Logic.and
  (funspec_sub (@free_spec' cs2) (@free_spec' cs1))
  (funspec_sub (snd (@nondet_bytes_nn_spec cs2)) (snd (@nondet_bytes_nn_spec cs1)))).
Proof.
  split; [exact malloc_sub|]. split; [exact free_sub | exact nondet_bytes_sub].
Qed.

End Specs.
End CS.
