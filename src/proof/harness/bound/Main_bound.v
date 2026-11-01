(* The harness obligation of bound (harness/bound.c): main only, no helper, no decoder call. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.bound.HOK_bound.

Local Ltac expand_main_pre ::= idtac.

(* main calls only nondet_size and gp_assert *)
Definition G0 : funspecs := [nondet_size_spec; gp_assert_spec].

Lemma Externals_eq : Externals = G0.
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

(* any precondition implies the empty one with TT (the postcondition is TT) *)
Lemma pre_to_TT : forall (P: environ -> mpred), P |-- PROP () LOCAL () SEP (TT).
Proof. intros P rho. unfold PROPx, LOCALx, SEPx; simpl. normalize. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* ZSTD_MAX_INPUT_SIZE on 64 bits *)
Definition MAXIN : Z := 18374966859414961920.

Lemma MAXIN_repr : Int64.repr (-71777214294589696) = Int64.repr MAXIN.
Proof. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

(* the law: bound(a) + bound(b) <= bound(a+b), as main computes it in unsigned 64-bit arithmetic *)
Lemma bound_law a b : 131072 <= a -> 131072 <= b -> a + b < MAXIN ->
  Int64.ltu
    (Int64.add (Int64.add (Int64.repr (a + b)) (Int64.shru (Int64.repr (a + b)) (Int64.repr 8))) (Int64.repr 0))
    (Int64.add (Int64.add (Int64.add (Int64.repr a) (Int64.shru (Int64.repr a) (Int64.repr 8))) (Int64.repr 0))
               (Int64.add (Int64.add (Int64.repr b) (Int64.shru (Int64.repr b) (Int64.repr 8))) (Int64.repr 0)))
  = false.
Proof.
  intros Ha Hb Hab. unfold MAXIN in Hab.
  pose proof (Z.div_mod a 256 ltac:(lia)). pose proof (Z.mod_pos_bound a 256 ltac:(lia)).
  pose proof (Z.div_mod b 256 ltac:(lia)). pose proof (Z.mod_pos_bound b 256 ltac:(lia)).
  pose proof (Z.div_mod (a + b) 256 ltac:(lia)). pose proof (Z.mod_pos_bound (a + b) 256 ltac:(lia)).
  rewrite !Int64.shru_div_two_p.
  change (two_p (Int64.unsigned (Int64.repr 8))) with 256.
  rewrite !Int64.unsigned_repr by rep_lia.
  rewrite !add64_repr.
  rewrite ltu_Z by rep_lia.
  apply Z.ltb_ge. lia.
Qed.

Ltac norm :=
  try match goal with H: ?x <> ?x |- _ => exfalso; exact (H eq_refl) end;
  try rewrite sub64_repr in *;
  try rewrite add64_repr in *;
  try change (Int.signed (Int.shl (Int.repr 128) (Int.repr 10))) with 131072 in *;
  try rewrite MAXIN_repr in *;
  repeat match goal with
  | H: Int64.ltu (Int64.repr ?x) (Int64.repr ?y) = _ |- _ =>
      rewrite ltu_Z in H by (unfold MAXIN in *; rep_lia);
      first [apply Z.ltb_lt in H | apply Z.ltb_ge in H]
  end;
  try (exfalso; unfold MAXIN in *; lia).

Ltac step :=
  first
  [ match goal with |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
      apply semax_if_seq; forward_if; norm end
  | match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end
  | match goal with |- semax _ _ (Sifthenelse _ _ _) _ => forward_if; norm end
  | forward; norm ].

Lemma body_main_G0 : semax_body [] G0 f_main main_spec.
Proof.
  change (semax_body [] G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_bound.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply semax_pre with (P' := PROP () LOCAL () SEP (TT)); [apply andp_left2; apply pre_to_TT |].
  abbreviate_semax.
  forward_call tt.
  Intros a.
  forward_call tt.
  Intros b.
  do 60 (try step).
  forward_call Int.one.
  { entailer!. simpl. change (Int.unsigned (Int.repr 8)) with 8. change (Int.signed (Int.repr 0)) with 0.
    rewrite bound_law by lia. reflexivity. }
  forward.
Qed.

(* From G0 to Gprog API []: G0's entries are found there unchanged when API does not shadow them *)
Lemma find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma find_id_skip {A} i (l1 l2: list (ident * A)) : ~ In i (map fst l1) -> initial_world.find_id i (l1 ++ l2) = initial_world.find_id i l2.
Proof.
  induction l1 as [|[j x] l1 IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma G0_in_Gprog API : list_disjoint (map fst API) (map fst Externals) ->
  forall i fs, initial_world.find_id i G0 = Some fs -> initial_world.find_id i (Gprog API []) = Some fs.
Proof.
  intros HD i fs Hi.
  assert (Hin: In i (map fst Externals)).
  { rewrite Externals_eq. apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  assert (Hn: i = _nondet_size \/ i = _gp_assert).
  { rewrite Externals_eq in Hin. destruct Hin as [<-|[<-|[]]]; auto. }
  unfold Gprog.
  rewrite find_id_skip.
  - rewrite Externals_eq. apply initial_world.find_id_app1. exact Hi.
  - unfold Imports. simpl. intros [E|[E|E]].
    + destruct Hn; subst; discriminate.
    + destruct Hn; subst; discriminate.
    + exact (HD i i E Hin eq_refl).
Qed.

Lemma bound_ok : forall API, list_disjoint (map fst API) (map fst Externals) -> HarnessOK API [].
Proof.
  intros API HD. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply body_main_G0 |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (make_tycontext_g_find [] G0 i).
      destruct (initial_world.find_id i G0) as [fs|] eqn:E.
      * rewrite (make_tycontext_g_find Vprog (Gprog API []) i).
        rewrite (G0_in_Gprog API HD i fs E). apply sub_option_refl.
      * assert (Hn: Maps.PTree.get i (make_tycontext_g [] []) = None)
          by (unfold make_tycontext_g; simpl; apply Maps.PTree.gempty).
        rewrite Hn. exact Logic.I.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog API HD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
