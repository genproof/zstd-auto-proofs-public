(* Assembling a subtree from groups: if every group proves its functions against the context and the
   exports of the groups (subtree_ok ids_g E_g (G ++ I_g), I_g among the exports), the union proves
   subtree_ok for any order of the same functions.  Generic; used for subtree B (DecB.v). *)
Require Export Zstd.proof.dec.DecSubtrees.
Require Import Coq.Sorting.Permutation.

(* a group: its functions, its exports, its imports *)
Definition group : Type := (list ident * funspecs * funspecs)%type.
Definition g_ids (g: group) : list ident := fst (fst g).
Definition g_exp (g: group) : funspecs := snd (fst g).
Definition g_imp (g: group) : funspecs := snd g.

Section Compose.
Variable G : funspecs.

Lemma groups_union (gs: list group) (EXP: funspecs) :
  Forall (fun g => subtree_ok (g_ids g) (g_exp g) (G ++ g_imp g)) gs ->
  Forall (fun g => incl (g_imp g) EXP) gs ->
  exists Sall: funspecs,
    map fst Sall = concat (map g_ids gs) /\
    incl (concat (map g_exp gs)) Sall /\
    Forall (fun x => exists I S', incl I EXP /\ incl S' Sall /\ body_ok (G ++ I ++ S') x) Sall.
Proof.
  induction gs as [|g gs IH]; intros Hok Himp.
  - exists nil; simpl; split; [reflexivity | split; [intros x Hx; inversion Hx | constructor]].
  - inversion Hok as [|? ? Hg Hgs]; subst. inversion Himp as [|? ? Hig Higs]; subst.
    destruct (IH Hgs Higs) as [S2 [H1 [H2 H3]]].
    destruct Hg as [S1 [K1 [K2 K3]]].
    exists (S1 ++ S2). split; [|split].
    + rewrite map_app, K1, H1. reflexivity.
    + simpl. apply incl_app; [apply incl_appl, K2 | apply incl_appr, H2].
    + apply Forall_app; split.
      * eapply Forall_impl; [|exact K3]. intros x Hx.
        exists (g_imp g), S1. split; [exact Hig | split; [apply incl_appl, incl_refl | rewrite <- app_assoc in Hx; exact Hx]].
      * eapply Forall_impl; [|exact H3]. intros x [I [S' [Ha [Hb Hc]]]].
        exists I, S'. split; [exact Ha | split; [apply incl_appr, Hb | exact Hc]].
Qed.

Fixpoint pick (Sall: funspecs) (ids: list ident) : funspecs :=
  match ids with
  | nil => nil
  | i :: r =>
      match find (fun x => Pos.eqb (fst x) i) Sall with
      | Some x => x :: pick Sall r
      | None => pick Sall r
      end
  end.

Lemma find_fst (Sall: funspecs) (i: ident) :
  In i (map fst Sall) ->
  exists x, find (fun x => Pos.eqb (fst x) i) Sall = Some x /\ fst x = i /\ In x Sall.
Proof.
  intros Hin.
  destruct (find (fun x => Pos.eqb (fst x) i) Sall) as [x|] eqn:E.
  - apply find_some in E as [Hx Heq]. apply Pos.eqb_eq in Heq. eauto.
  - exfalso. apply in_map_iff in Hin as [y [Hy Hiny]].
    pose proof (find_none _ _ E y Hiny) as Hf. simpl in Hf. subst i. rewrite Pos.eqb_refl in Hf. discriminate.
Qed.

Lemma pick_fst (Sall: funspecs) (ids: list ident) :
  incl ids (map fst Sall) -> map fst (pick Sall ids) = ids.
Proof.
  induction ids as [|i r IH]; intros Hinc; simpl; [reflexivity|].
  destruct (find_fst Sall i (Hinc i (or_introl eq_refl))) as [x [E [Hx _]]].
  rewrite E. simpl. f_equal; [exact Hx|]. apply IH. intros y Hy; apply Hinc; right; exact Hy.
Qed.

Lemma pick_incl (Sall: funspecs) (ids: list ident) : incl (pick Sall ids) Sall.
Proof.
  induction ids as [|i r IH]; simpl; [intros x Hx; inversion Hx|].
  destruct (find (fun x => Pos.eqb (fst x) i) Sall) eqn:E.
  - apply find_some in E as [Hx _]. intros y [<-|Hy]; [exact Hx | apply IH, Hy].
  - exact IH.
Qed.

Lemma nodup_fst_eq (S: funspecs) (x y: ident * funspec) :
  NoDup (map fst S) -> In x S -> In y S -> fst x = fst y -> x = y.
Proof.
  induction S as [|z S IH]; intros Hnd Hx Hy Hf; [inversion Hx|].
  simpl in Hnd. inversion Hnd as [|? ? Hz Hnd']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; auto.
  - exfalso; apply Hz. rewrite Hf. apply in_map, Hy.
  - exfalso; apply Hz. rewrite <- Hf. apply in_map, Hx.
Qed.

Lemma incl_pick (Sall: funspecs) (ids: list ident) :
  NoDup (map fst Sall) -> incl (map fst Sall) ids -> incl Sall (pick Sall ids).
Proof.
  intros Hnd Hinc x Hx.
  assert (Hi: In (fst x) ids) by (apply Hinc, in_map, Hx).
  clear Hinc. induction ids as [|i r IH]; [inversion Hi|]. simpl.
  destruct (find (fun x => Pos.eqb (fst x) i) Sall) as [y|] eqn:E.
  - destruct (Pos.eq_dec (fst x) i) as [Heq|Hne].
    + left. apply find_some in E as [Hy Hf]. apply Pos.eqb_eq in Hf.
      apply nodup_fst_eq with Sall; auto. change (@fst ident funspec y = @fst ident funspec x). rewrite Heq. exact Hf.
    + right. apply IH. destruct Hi as [Hi|Hi]; [exfalso; apply Hne; symmetry; exact Hi | exact Hi].
  - destruct Hi as [Hi|Hi].
    + exfalso. pose proof (find_none _ _ E x Hx) as Hf. simpl in Hf. rewrite Hi, Pos.eqb_refl in Hf. discriminate.
    + apply IH, Hi.
Qed.

Lemma subtree_compose (gs: list group) (ids: list ident) (X: funspecs) :
  Forall (fun g => subtree_ok (g_ids g) (g_exp g) (G ++ g_imp g)) gs ->
  Forall (fun g => incl (g_imp g) (concat (map g_exp gs))) gs ->
  incl ids (concat (map g_ids gs)) ->
  incl (concat (map g_ids gs)) ids ->
  NoDup (concat (map g_ids gs)) ->
  NoDup (map fst Vprog ++ map fst G ++ ids) ->
  incl X (concat (map g_exp gs)) ->
  subtree_ok ids X G.
Proof.
  intros Hok Himp Hi1 Hi2 Hnd Hnd2 HX.
  destruct (groups_union gs _ Hok Himp) as [Sall [H1 [H2 H3]]].
  assert (Hids: incl ids (map fst Sall)).
  { rewrite H1. exact Hi1. }
  assert (Hback: incl (map fst Sall) ids).
  { rewrite H1. exact Hi2. }
  assert (HndS: NoDup (map fst Sall)) by (rewrite H1; exact Hnd).
  set (S := pick Sall ids).
  assert (HS1: map fst S = ids) by (apply pick_fst, Hids).
  assert (HS2: incl Sall S) by (apply incl_pick; auto).
  assert (HS3: incl S Sall) by apply pick_incl.
  exists S. split; [exact HS1 | split].
  - intros x Hx. apply HS2, H2, HX, Hx.
  - rewrite Forall_forall. intros x Hx.
    rewrite Forall_forall in H3. destruct (H3 x (HS3 x Hx)) as [I [S' [Ha [Hb Hc]]]].
    eapply body_ok_mono; [exact Hc | |].
    + apply incl_app; [apply incl_appl, incl_refl|]. apply incl_app; apply incl_appr.
      * intros y Hy. apply HS2, H2, Ha, Hy.
      * intros y Hy. apply HS2, Hb, Hy.
    + rewrite map_app, HS1. exact Hnd2.
Qed.
End Compose.

(* deciding the conditions on ident lists *)
Definition memb (i: ident) (l: list ident) : bool := existsb (Pos.eqb i) l.
Definition inclb (a b: list ident) : bool := forallb (fun i => memb i b) a.
Fixpoint nodupb (l: list ident) : bool :=
  match l with nil => true | i :: r => negb (memb i r) && nodupb r end.

Lemma memb_ok (i: ident) (l: list ident) : memb i l = true -> In i l.
Proof.
  unfold memb. intros H. apply existsb_exists in H as [x [Hx Heq]]. apply Pos.eqb_eq in Heq. subst; exact Hx.
Qed.

Lemma inclb_ok (a b: list ident) : inclb a b = true -> incl a b.
Proof.
  unfold inclb. intros H i Hi. rewrite forallb_forall in H. apply memb_ok, H, Hi.
Qed.

Lemma nodupb_ok (l: list ident) : nodupb l = true -> NoDup l.
Proof.
  induction l as [|i r IH]; simpl; intros H; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|apply IH, H2].
  intros Hin. unfold memb in H1. destruct (existsb (Pos.eqb i) r) eqn:E; [discriminate|].
  assert (existsb (Pos.eqb i) r = true) by (apply existsb_exists; exists i; split; [exact Hin | apply Pos.eqb_refl]).
  congruence.
Qed.
