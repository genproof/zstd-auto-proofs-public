(* FS3: lifting a body to a context with stronger specifications (as DecLift) and the intersection of two
   specifications of one body. *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_FSLift3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- lifting bodies to a context with stronger specifications (as DecLift) ---------- *)

Definition fs3_refines (G' G: funspecs) : Prop :=
  forall i phi, initial_world.find_id i G = Some phi ->
    exists phi', initial_world.find_id i G' = Some phi' /\ funspec_sub phi' phi.

Lemma fs3_make_tycontext_g_find_id (V: varspecs) (G: funspecs) (i: ident) :
  Maps.PTree.get i (make_tycontext_g V G) =
  match initial_world.find_id i G with
  | Some phi => Some (type_of_funspec phi)
  | None => initial_world.find_id i V
  end.
Proof.
  induction G as [|[j phi] G IH]; simpl.
  - apply semax_prog.make_tycontext_g_nilG_find_id.
  - rewrite Maps.PTree.gsspec. destruct (Coqlib.peq i j) as [E|E]; subst.
    + destruct (Memory.EqDec_ident j j); [reflexivity | congruence].
    + destruct (Memory.EqDec_ident i j); [congruence | exact IH].
Qed.

Lemma fs3_find_id_in_fst {A} (i: ident) (l: list (ident * A)) (x: A) :
  initial_world.find_id i l = Some x -> In i (map fst l).
Proof.
  induction l as [|[j y] l IH]; simpl; [discriminate |].
  destruct (Memory.EqDec_ident i j); [left; congruence | intros H; right; exact (IH H)].
Qed.

Lemma fs3_find_id_none {A} (i: ident) (l: list (ident * A)) :
  ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j y] l IH]; simpl; [reflexivity |].
  destruct (Memory.EqDec_ident i j); [intros H; exfalso; apply H; left; congruence |].
  intros H; apply IH; tauto.
Qed.

Lemma fs3_NoDup_app_disj {A} (l1 l2: list A) (x: A) :
  NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; simpl; [tauto |].
  intros Hn Hin. inversion Hn as [|y' l' Hy Hl]; subst. destruct Hin as [<-|Hin].
  - intros Hx. apply Hy. apply in_or_app; right; exact Hx.
  - exact (IH Hl Hin).
Qed.

Lemma fs3_refines_tycontext_sub (f: function) (G G': funspecs) :
  fs3_refines G' G -> NoDup (map fst Vprog ++ map fst G') ->
  tycontext_sub (func_tycontext f Vprog G nil) (func_tycontext f Vprog G' nil).
Proof.
  intros Hr Hnd.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  split; [intro id; destruct (Maps.PTree.get _ _); auto |].
  split; [auto |]. split; [auto |].
  split; [| split; [| intro id; first [exact I | apply Annotation_sub_refl]]].
  - intro id. hnf. rewrite !fs3_make_tycontext_g_find_id.
    destruct (initial_world.find_id id G) as [phi|] eqn:E.
    + destruct (Hr id phi E) as [phi' [E' Hs]]. rewrite E'.
      f_equal. apply type_of_funspec_sub; exact Hs.
    + destruct (initial_world.find_id id Vprog) as [t|] eqn:EV; [| exact I].
      assert (N: initial_world.find_id id G' = None).
      { apply fs3_find_id_none.
        exact (fs3_NoDup_app_disj _ _ _ Hnd (fs3_find_id_in_fst _ _ _ EV)). }
      rewrite N. reflexivity.
  - intro id. rewrite !initial_world.make_tycontext_s_find_id.
    destruct (initial_world.find_id id G) as [phi|] eqn:E; [| exact I].
    destruct (Hr id phi E) as [phi' [E' Hs]]. exists phi'. split; [exact E' |].
    apply funspec_sub_sub_si; exact Hs.
Qed.

Lemma fs3_body_ok_sub (G G': funspecs) (ix: ident * funspec) :
  body_ok G ix -> fs3_refines G' G -> NoDup (map fst Vprog ++ map fst G') -> body_ok G' ix.
Proof.
  intros [f [Hf [Hcc Hb]]] Hr Hnd'. exists f; split; [exact Hf | split; [exact Hcc |]].
  eapply semax_body_subsumption; [exact Hb |].
  apply fs3_refines_tycontext_sub; assumption.
Qed.

(* every specification of G is in G', except some of the identifier c, for which G' has a stronger one chi *)
Lemma fs3_refines_but (G' G: funspecs) (c: ident) (chi: funspec) :
  NoDup (map fst G') -> In (c, chi) G' ->
  (forall i phi, In (i, phi) G -> In (i, phi) G' \/ (i = c /\ funspec_sub chi phi)) ->
  fs3_refines G' G.
Proof.
  intros Hnd Hc H i phi Hf. apply initial_world.find_id_e in Hf.
  destruct (H i phi Hf) as [Hin | [-> Hs]].
  - exists phi. split; [| apply funspec_sub_refl].
    apply initial_world.find_id_i; [exact Hin | apply list_norepet_NoDup; exact Hnd].
  - exists chi. split; [| exact Hs].
    apply initial_world.find_id_i; [exact Hc | apply list_norepet_NoDup; exact Hnd].
Qed.

(* ---------- the intersection of two specifications of one body ---------- *)

Definition inter_of (phi psi: funspec) : funspec :=
  match binary_intersection phi psi with Some x => x | None => phi end.

Lemma inter_some (G1 G2: funspecs) (i: ident) (phi psi: funspec) :
  body_ok G1 (i, phi) -> body_ok G2 (i, psi) -> binary_intersection phi psi = Some (inter_of phi psi).
Proof.
  intros [f1 [H1 [Hc1 Hb1]]] [f2 [H2 [Hc2 Hb2]]]. simpl in *.
  unfold zstd_fun in H1, H2. rewrite H1 in H2. inversion H2; subst f2; clear H2.
  unfold inter_of. destruct phi as [[t1 r1] c1 A1 P1 Q1 P1n Q1n], psi as [[t2 r2] c2 A2 P2 Q2 P2n Q2n].
  simpl in Hb1, Hb2, Hc1, Hc2. destruct Hb1 as [Et1 [Er1 _]], Hb2 as [Et2 [Er2 _]].
  destruct (binary_intersection _ _) eqn:E; [reflexivity | exfalso].
  revert E. unfold binary_intersection.
  destruct (eq_dec (t1, r1) (t2, r2)) as [e|n]; [| intros _; apply n; congruence].
  destruct e. rewrite eq_dec_refl. assert (c1 = c2) by congruence. subst c2.
  match goal with |- context [if ?x then _ else _] => destruct x end; [intros Hd; inversion Hd | congruence].
Qed.

Lemma body_ok_inter (G: funspecs) (i: ident) (phi psi: funspec) :
  body_ok G (i, phi) -> body_ok G (i, psi) -> body_ok G (i, inter_of phi psi).
Proof.
  intros B1 B2. pose proof (inter_some _ _ _ _ _ B1 B2) as E.
  destruct B1 as [f1 [H1 [Hc1 Hb1]]], B2 as [f2 [H2 [Hc2 Hb2]]]. simpl in *.
  unfold zstd_fun in H1, H2. rewrite H1 in H2. inversion H2; subst f2; clear H2.
  exists f1. split; [exact H1 | split].
  - simpl. destruct (callconv_of_binary_intersection E) as [-> _]. exact Hc1.
  - exact (semax_body_binaryintersection f1 (i, phi) (i, psi) _ Hb1 Hb2 E).
Qed.

End CM_FSLift3_1.
