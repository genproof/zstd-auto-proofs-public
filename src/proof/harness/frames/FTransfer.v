(* Moving a body of the frames kit into a law's context.  The kit proves each body at any compspecs in the
   context of exactly the functions it calls (FSpecs.G_<fn>, no global variables); a law's harness proof
   needs it in its own context (its compspecs, the whole program's varspecs, its Gprog).  fk_transfer: any
   context that has the same specifications for those functions will do. *)
Require Import VST.floyd.proofauto.

Lemma fk_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with
  | Some fs => Some (type_of_funspec fs)
  | None => Maps.PTree.get i (make_tycontext_g Vs nil)
  end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma fk_transfer {cs: compspecs} (V: varspecs) (G Gk: funspecs) (f: function) (spec: ident * funspec) :
  semax_body [] Gk f spec ->
  (forall i fs, initial_world.find_id i Gk = Some fs -> initial_world.find_id i G = Some fs) ->
  semax_body V G f spec.
Proof.
  intros B HG.
  eapply semax_body_subsumption; [exact B |].
  apply tycontext_sub_i99. split; intro i.
  - rewrite (fk_make_tycontext_g_find [] Gk i).
    destruct (initial_world.find_id i Gk) as [fs|] eqn:E.
    + rewrite (fk_make_tycontext_g_find V G i), (HG i fs E). apply sub_option_refl.
    + assert (Hn: Maps.PTree.get i (make_tycontext_g [] []) = None)
        by (unfold make_tycontext_g; simpl; apply Maps.PTree.gempty).
      rewrite Hn. exact Logic.I.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i Gk) as [fs|] eqn:E; [| exact Logic.I].
    rewrite (HG i fs E). exists fs. split; [reflexivity |]. apply funspec_sub_si_refl.
Qed.

(* The side condition for a concrete list Gk: every entry of Gk is found in G. *)
Lemma fk_find_all (G Gk: funspecs) :
  Forall (fun ix => initial_world.find_id (fst ix) G = Some (snd ix)) Gk ->
  forall i fs, initial_world.find_id i Gk = Some fs -> initial_world.find_id i G = Some fs.
Proof.
  intros F i fs E.
  apply initial_world.find_id_e in E.
  rewrite Forall_forall in F. exact (F (i, fs) E).
Qed.
