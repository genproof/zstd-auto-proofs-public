(* Generic lemmas of the assembly: building a VSU Component from per-function obligations without
   unfolding any specification beyond its identifier and calling convention. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Import compcert.lib.Maps.

(* The per-function side conditions of semaxfunc_InternalInfo that depend only on the code,
   checked for every internal function of a program at once. *)
Definition fun_ok (cs: compspecs) (f: function) : bool :=
  semax_body_params_ok f &&
  forallb (fun it => Ctypes.complete_type (@cenv_cs cs) (snd it)) (fn_vars f) &&
  forallb (fun it => Z.leb (@sizeof cs (snd it)) Ptrofs.max_unsigned) (fn_vars f).

Definition prog_funs_ok (ce: compspecs) (p: QP.program function) : bool :=
  forallb (fun ig => match snd ig with Gfun (Internal f) => fun_ok ce f | _ => true end)
    (PTree.elements (QP.prog_defs p)).

Lemma prog_funs_ok_e: forall ce p i f,
  prog_funs_ok ce p = true ->
  (QP.prog_defs p) ! i = Some (Gfun (Internal f)) ->
  fun_ok ce f = true.
Proof.
  intros. apply PTree.elements_correct in H0.
  unfold prog_funs_ok in H. rewrite forallb_forall in H.
  apply H in H0. exact H0.
Qed.

(* The obligation of one entry of G. *)
Definition SF_ok {Espec cs V} (p: QP.program function) (G0: funspecs) (ix: ident * funspec) : Prop :=
  id_in_list (fst ix) (map fst G0) = true ->
  forall fd, (QP.prog_defs p) ! (fst ix) = Some (Gfun fd) ->
  @SF Espec cs V (QPglobalenv p) G0 (fst ix) fd (snd ix).

Lemma G_justified_of_Forall {Espec cs V} (p: QP.program function) Imports G:
  Forall (@SF_ok Espec cs V p (Imports ++ G)) G ->
  forall i phi fd, (QP.prog_defs p) ! i = Some (Gfun fd) -> initial_world.find_id i G = Some phi ->
  @SF Espec cs V (QPglobalenv p) (Imports ++ G) i fd phi.
Proof.
  intros. apply initial_world.find_id_e in H1.
  rewrite Forall_forall in H. specialize (H _ H1). apply (H); auto.
  apply assoclists.id_in_list_true_i. rewrite map_app. apply in_or_app. right.
  change i with (fst (i, phi)). apply in_map. auto.
Qed.

Lemma SF_ok_internal {Espec cs V} (p: QP.program function) (OK: QPprogram_OK p)
  (FOK: prog_funs_ok cs p = true) G0 ix f:
  semax_body V G0 f ix ->
  (QP.prog_defs p) ! (fst ix) = Some (Gfun (Internal f)) ->
  fn_callconv f = callingconvention_of_funspec (snd ix) ->
  @SF_ok Espec cs V p G0 ix.
Proof.
  intros SB GET CC IN fd GET'. rewrite GET in GET'. inv GET'.
  pose proof (prog_funs_ok_e _ _ _ _ FOK GET) as F.
  unfold fun_ok in F. rewrite !andb_true_iff in F. destruct F as [[F1 F2] F3].
  destruct ix as [i phi]. simpl in *.
  split; [| split; [| split; [| split; [| split]]]].
  - rewrite IN, F1. reflexivity.
  - rewrite forallb_forall in F2. apply Forall_forall. intros; apply F2; auto.
  - rewrite forallb_forall in F3. apply Forall_forall. intros x H.
    apply F3 in H. apply Z.leb_le in H. exact H.
  - exact CC.
  - exact SB.
  - apply (QPprogdefs_GFF OK GET).
Qed.
