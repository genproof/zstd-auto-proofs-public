(* VST's WholeComponent_semax_prog (floyd/VSU.v), with the compspecs of the conclusion named: it is
   the Component's own Comp_cs (VSU's version hides it under an existential, which loses the link
   with the compspecs of the external world HonestEspec cs required by QuickProof.Contract).
   The proof is VSU's, unchanged after the first lines. *)
Require Import VST.floyd.proofauto.
Require Import VST.veric.Clight_initial_world.
Require Import VST.floyd.assoclists.
Require Import VST.floyd.VSU.
Import compcert.lib.Maps.

Lemma WholeComponent_semax_prog_cs:
 forall {Espec Externs p Exports GP mainspec} (G: funspecs)
  (NO_MAIN: find_id (QP.prog_main p) G = None)
  (c: @Component Espec (QPvarspecs p) Externs nil p Exports GP (G_merge
                 [(QP.prog_main p, mainspec)] G))
  (z: OK_ty)
  (MAIN: exists post, mainspec = QPmain_spec_ext' p z post)
  (MAIN': isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)))
  (EXT_OK: all_unspecified_OK p)
  (ALIGNED: QPall_initializers_aligned p = true)
  (DEFS_NOT_BUILTIN: forallb not_builtin (PTree.elements (QP.prog_defs p)) = true)
  (CBC: forall H,
    cenv_built_correctly
        (map compdef_of_compenv_element
           (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H)
           = Errors.OK tt),
 @semax_prog Espec (Comp_cs c)
   (wholeprog_of_QPprog p (Comp_prog_OK c)
    (cenv_built_correctly_e
         (map compdef_of_compenv_element
            (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
         (composite_env_of_QPcomposite_env (QP.prog_comp_env p) (projT1 (proj2 (Comp_prog_OK c))))
         (CBC _)))
    z (QPvarspecs p)
      (G_merge [(QP.prog_main p, mainspec)] G).
Proof.
 intros ? ? ? ? ? mainspec; intros.
 pose (prog := prog_of_component c (CBC _)).
 split3; [ | | split3; [ | | split]].
 4: change SeparationLogicAsLogicSoundness.MainTheorem.CSHL_MinimumLogic.CSHL_Def.semax_func
  with semax_func.
-
 subst prog; simpl.
 unfold prog_defs_names. simpl.
 apply compute_list_norepet_i.
 clear - c.
 rewrite map_app.
 destruct (Comp_prog_OK c).
 rewrite map_map. 
 replace (fun x : ident * QP.builtin => fst (of_builtin x)) with (@fst ident QP.builtin); auto.
 extensionality x. destruct x,b; simpl; auto.
-
 red. unfold SeparationLogic.prog_vars;
 subst prog; simpl.
 clear - ALIGNED.
 unfold QPall_initializers_aligned in *.
 unfold QPprog_vars in ALIGNED.
  replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
 induction (PTree.elements (QP.prog_defs p)) as [|[i?]]; auto.
 destruct g; auto.
 simpl in ALIGNED|-*.
 rewrite andb_true_iff in ALIGNED|-*; destruct ALIGNED; auto.
-
  f_equal.
  apply (proj1 (QPcompspecs_OK_e _ (proj2 (Comp_prog_OK c)))).
-
 apply (@WholeComponent_semax_func _ _ _ _ _ _ c EXT_OK DEFS_NOT_BUILTIN).
-
  subst prog; simpl.
  unfold QPvarspecs, QPprog_vars, SeparationLogic.prog_vars. simpl.
  clear.
  replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
  induction (PTree.elements (QP.prog_defs p)) as [|[i?]].
  simpl. auto.
  simpl. destruct g; auto.
  simpl.
  rewrite eqb_ident_true by auto.
  rewrite eqb_type_refl by auto.
  simpl; auto.
- simpl find_id.
   unfold augment_funspecs.
   change SeparationLogic.prog_funct with prog_funct.
   erewrite prog_funct_QP_prog_funct; [ | reflexivity].
  set (G1 := G_merge [(QP.prog_main p, mainspec)] G).
   destruct (augment_funspecs'_exists G1 (QP.prog_builtins p) (QPprog_funct p)) 
     as [G' ?]; auto.
   * 
   apply (list_norepet_append_left _ _ (proj1 (Comp_prog_OK c))).
   *
   pose proof (list_norepet_append_right _ _ (proj1 (Comp_prog_OK c))).
   unfold QPprog_funct.
   clear - H. forget (PTree.elements (QP.prog_defs p)) as al.
   induction al as [|[i[|]]]; simpl in *; auto. inv H; constructor; auto.
   contradict H2. clear - H2; induction al as [|[j[|]]]; simpl in *; auto. destruct H2; auto.
   inv H; auto.
   *
   assert (H1 := proj1 (Comp_prog_OK c)).
   rewrite list_norepet_app in H1; destruct H1 as [_ [_ H1]].
   eapply assoclists.list_disjoint_mono; try apply H1; auto.
   clear; intros. unfold QPprog_funct in H.
   induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto. destruct H; auto.
   *
   clear - DEFS_NOT_BUILTIN.
   unfold QPprog_funct. induction (PTree.elements (QP.prog_defs p)) as [|[i[|]]]; simpl in *; auto.
   rewrite andb_true_iff in *|-*. tauto.
   *
     apply (Comp_G_LNR c).
   *
   intros.
   fold G1 in c.
   rewrite <- (Comp_G_dom c) in H.
   rewrite in_app in H; destruct H.
   apply IntIDs_elim in H; destruct H.
   unfold QPprog_funct.
   clear - H. induction (PTree.elements (QP.prog_defs p)) as [|[j[|]]]; simpl in *; auto.
   destruct H; auto. inv H; auto.   destruct H; auto. inv H; auto.
   apply (Comp_Externs c i) in H.
   destruct H as [? [? [? [? ?]]]].
   apply PTree.elements_correct in H.
   unfold QPprog_funct.
   clear - H. induction (PTree.elements (QP.prog_defs p)) as [|[j[|]]]; simpl in *; auto.
   destruct H; auto. inv H; auto.   destruct H; auto. inv H; auto.
   *
   change (G_merge _ _) with G1.
   rewrite H.
   apply augment_funspecs'_e in H.
   destruct MAIN as [post MAIN].
   change (prog_main prog) with (QP.prog_main p).
   assert   (MAINx: find_id (QP.prog_main p) G1 = Some (QPmain_spec_ext' p z post)). {
     apply G_merge_find_id_SomeNone.
     simpl. rewrite if_true by auto. f_equal; auto. auto.
   }
   rewrite (augment_funspecs_find_id_Some _ _ _ H (Comp_G_LNR c) _ _ MAINx).
   exists post.
   unfold QPmain_spec_ext', main_spec_ext'.
   f_equal.
   subst prog. unfold main_pre, SeparationLogic.main_pre.
   unfold SeparationLogic.prog_vars. simpl.
   unfold QPprog_vars.
   replace  (SeparationLogic.prog_vars'
     (map of_builtin (QP.prog_builtins p) ++ PTree.elements (QP.prog_defs p)))
    with  (SeparationLogic.prog_vars'(PTree.elements (QP.prog_defs p)))
       by (clear; induction (QP.prog_builtins p) as [|[i ?]]; try destruct b; simpl; auto).
   extensionality gv rho.
   normalize. f_equal. f_equal. f_equal. f_equal.
  clear.
  induction (PTree.elements (QP.prog_defs p)) as [|[i?]]; auto.
  simpl.
  destruct g; auto.
  f_equal; auto.
Qed.

Require Import QuickProof.Contract.

Lemma G_merge_single (i: ident) (m: funspec) (G: funspecs):
  find_id i G = None -> G_merge [(i, m)] G = (i, m) :: G.
Proof.
  intros H. unfold G_merge, G_merge_aux. simpl. rewrite H. simpl. f_equal.
  induction G as [|[j phi] G IH]; simpl in *; auto.
  destruct (Memory.EqDec_ident i j) as [E|E]; [discriminate|].
  destruct (Memory.EqDec_ident j i) as [E'|E']; [congruence|]. f_equal; auto.
Qed.

(* harness_safe of a whole program from the conditions of one Component over the whole program,
   at the program's own compspecs in the world HonestEspec of those compspecs. *)
Lemma harness_safe_of_parts (p: QP.program function) (OK: QPprogram_OK p)
  (E G: funspecs) (post: (ident -> val) -> environ -> mpred) :
  let CSW := compspecs_of_QPcomposite_env _ (proj2 OK) in
  let GG := (QP.prog_main p, QPmain_spec_ext' p tt post) :: G in
  find_id (QP.prog_main p) G = None ->
  isSome (PTree.get (QP.prog_main p) (QP.prog_defs p)) ->
  all_unspecified_OK p ->
  QPall_initializers_aligned p = true ->
  forallb not_builtin (PTree.elements (QP.prog_defs p)) = true ->
  (forall H, cenv_built_correctly
        (map compdef_of_compenv_element (sort_rank (PTree.elements (QP.prog_comp_env p)) []))
        (composite_env_of_QPcomposite_env (QP.prog_comp_env p) H) = Errors.OK tt) ->
  list_norepet (map fst (QPvarspecs p) ++ map fst GG) ->
  list_norepet (map fst E) ->
  (forall i, In i (map fst E) ->
     exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))) ->
  (forall i, In i (IntIDs p ++ map fst E) <-> In i (map fst GG)) ->
  (forall i, In i (map fst E) -> find_id i E = find_id i GG) ->
  (forall i phi fd, PTree.get i (QP.prog_defs p) = Some (Gfun fd) -> find_id i GG = Some phi ->
     @SF (@HonestEspec CSW) CSW (QPvarspecs p) (QPglobalenv p) GG i fd phi) ->
  harness_safe p.
Proof.
  intros CSW GG NO_MAIN MAIN' EXT_OK ALIGNED DNB CBC LNR ELNR EXT DOM GE JUST.
  assert (EQ: G_merge [(QP.prog_main p, QPmain_spec_ext' p tt post)] G = GG)
    by (apply G_merge_single; auto).
  clearbody GG. subst GG.
  set (GM := G_merge [(QP.prog_main p, QPmain_spec_ext' p tt post)] G) in *.
  assert (F1: forall i, In i (map fst (@nil (ident * funspec))) ->
     exists f ts t cc, PTree.get i (QP.prog_defs p) = Some (Gfun (External f ts t cc))) by (intros i []).
  assert (F2: list_norepet (map fst (QPvarspecs p) ++ map fst (GM ++ nil))) by (rewrite app_nil_r; exact LNR).
  assert (F3: list_norepet (map fst GM)) by (apply list_norepet_append_right in LNR; exact LNR).
  assert (F4: forall i phi (E: find_id i GM = Some phi), exists phi', find_id i GM = Some phi' /\ funspec_sub phi' phi)
    by (intros i phi H; exists phi; split; auto; apply funspec_sub_refl).
  assert (F5: forall gv, globals_ok gv -> InitGPred (Vardefs p) gv |-- (fun _ => TT) gv) by (intros; apply TT_right).
  pose (c := Build_Component (@HonestEspec CSW) (QPvarspecs p) E nil p GM (fun _ => TT) GM
               OK F1 F2 ELNR F3 EXT DOM GE (fun i phi fd H1 H2 => JUST i phi fd H1 H2) F4 F5).
  pose proof (@WholeComponent_semax_prog_cs (@HonestEspec CSW) E p GM (fun _ => TT)
     (QPmain_spec_ext' p tt post) G NO_MAIN c tt (ex_intro _ post eq_refl) MAIN' EXT_OK ALIGNED DNB CBC) as SP.
  exists CSW, OK, (cenv_built_correctly_e _ _ (CBC _)), GM. exact SP.
Qed.
