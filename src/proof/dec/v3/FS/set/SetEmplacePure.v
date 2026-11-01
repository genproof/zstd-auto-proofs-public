(* FS3 set part: ZSTD_DDictHashSet_emplaceDDict keeps the weak invariant (plain Coq). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetEmplacePure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section EmplacePure.
Local Open Scope Z_scope.

Lemma ep_ids_distinct_NoDup : forall xs, ids_distinct xs = true <-> NoDup xs.
Proof.
  induction xs as [|x r IH]; simpl.
  - split; auto using NoDup_nil.
  - rewrite andb_true_iff, negb_true_iff, IH. split.
    + intros [H1 H2]. constructor; auto. intro Hin.
      assert (existsb (Z.eqb x) r = true) by (apply existsb_exists; exists x; split; auto; apply Z.eqb_refl).
      congruence.
    + intros H. inversion H; subst. split; auto.
      destruct (existsb (Z.eqb x) r) eqn:E; auto. apply existsb_exists in E.
      destruct E as [y [Hy Heq]]. apply Z.eqb_eq in Heq; subst. contradiction.
Qed.

Lemma ep_ptr_nonnull : forall q, isptr q -> q <> nullval.
Proof. intros q H; destruct q; simpl in H; try contradiction; discriminate. Qed.

Lemma ep_slot_range : forall h t n, 0 < n -> 0 <= hs_slot h t n < n.
Proof. intros; unfold hs_slot; apply Z.mod_pos_bound; lia. Qed.

Lemma ep_slot_dist : forall h t n, 0 < n -> 0 <= t < n -> (hs_slot h t n - h) mod n = t.
Proof.
  intros; unfold hs_slot. rewrite Zminus_mod_idemp_l. replace (h + t - h) with t by lia.
  apply Z.mod_small; lia.
Qed.

Lemma ep_slot_of : forall h j n, 0 < n -> 0 <= j < n -> hs_slot h ((j - h) mod n) n = j.
Proof.
  intros; unfold hs_slot. rewrite Zplus_mod_idemp_r. replace (h + (j - h)) with j by lia.
  apply Z.mod_small; lia.
Qed.

Lemma ep_nonnull_in : forall l tbl j, hs_inv0 l tbl -> 0 <= j < Zlength tbl -> Znth j tbl <> nullval ->
  In (Znth j tbl) (map fst l).
Proof.
  intros l tbl j H Hj Hn. destruct H as (_ & _ & _ & _ & _ & Hp & _).
  eapply Permutation_in; [exact Hp|]. unfold hs_nonnull. apply filter_In. split.
  - apply Znth_In; auto.
  - unfold veqb. destruct (Val.eq (Znth j tbl) nullval); auto; contradiction.
Qed.

Lemma ep_set_id : forall (l: list (val * ddict_st)) e, NoDup (map fst l) -> In e l ->
  set_id_of l (fst e) = dd_id (snd e).
Proof.
  induction l as [|x r IH]; intros e Hnd Hin; [contradiction|].
  simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hn1 Hn2]. unfold set_id_of; simpl.
  destruct Hin as [-> | Hin].
  - unfold veqb. destruct (Val.eq (fst e) (fst e)); [reflexivity | congruence].
  - unfold veqb at 1. destruct (Val.eq (fst x) (fst e)) as [E|E].
    + exfalso. apply Hn1. rewrite E. apply in_map; auto.
    + apply IH; auto.
Qed.

Lemma ep_nonnull_upd : forall tbl s (x: val), 0 <= s < Zlength tbl ->
  hs_nonnull tbl = hs_nonnull (sublist 0 s tbl) ++ hs_nonnull [Znth s tbl] ++
                   hs_nonnull (sublist (s+1) (Zlength tbl) tbl) /\
  hs_nonnull (upd_Znth s tbl x) = hs_nonnull (sublist 0 s tbl) ++ hs_nonnull [x] ++
                   hs_nonnull (sublist (s+1) (Zlength tbl) tbl).
Proof.
  intros. unfold hs_nonnull. rewrite upd_Znth_unfold by auto. rewrite !filter_app. split; auto.
  rewrite <- !filter_app. f_equal. cbn [app].
  rewrite <- sublist_next by lia. rewrite <- sublist_split by lia. rewrite sublist_same; auto.
Qed.

Lemma ep_nonnull_one : forall x, x <> nullval -> hs_nonnull [x] = [x].
Proof. intros. unfold hs_nonnull, veqb; simpl. destruct (Val.eq x nullval); [contradiction | reflexivity]. Qed.

Lemma ep_null_one : hs_nonnull [nullval] = [].
Proof. unfold hs_nonnull, veqb; simpl. destruct (Val.eq nullval nullval); [reflexivity | congruence]. Qed.

Lemma ep_upd_nonnull : forall (tbl: list val) s q k, isptr q -> Znth k tbl <> nullval ->
  0 <= s < Zlength tbl -> Znth k (upd_Znth s tbl q) <> nullval.
Proof.
  intros. destruct (Z.eq_dec k s) as [->|].
  - rewrite upd_Znth_same by auto. apply ep_ptr_nonnull; auto.
  - rewrite Znth_upd_Znth_diff; auto.
Qed.

Lemma ep_q_at : forall l tbl s q j, hs_inv0 l tbl -> ~ In q (map fst l) -> isptr q ->
  0 <= j < Zlength tbl -> Znth j (upd_Znth s tbl q) = q -> j = s.
Proof.
  intros l tbl s q j H Hq Hp Hj E. destruct (Z.eq_dec j s); auto.
  rewrite Znth_upd_Znth_diff in E by auto. exfalso. apply Hq. rewrite <- E.
  apply ep_nonnull_in; auto. rewrite E. apply ep_ptr_nonnull; auto.
Qed.

Lemma ep_npos : forall l (tbl: list val), hs_inv0 l tbl -> 0 < Zlength tbl.
Proof.
  intros l tbl ((k & Hk & Hnk) & _). rewrite Hnk. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma ep_insert : PF_insert.
Proof.
  unfold PF_insert. intros l tbl q dd t; cbv zeta.
  intros Hinv Hlen Hq Hqn Ht Hnull Hprobe.
  pose proof (ep_npos _ _ Hinv) as Hn.
  pose proof Hinv as Hinv'. unfold hs_inv0 in Hinv'; cbv zeta in Hinv'.
  destruct Hinv' as (Hpow & Hl & Hnd & Hids & Hptr & Hperm & Hnp & Hpr).
  set (n := Zlength tbl) in *. set (h := hs_home (dd_id dd) n) in *.
  set (s := hs_slot h t n) in *.
  assert (Hs: 0 <= s < n) by (apply ep_slot_range; auto).
  assert (Hnone: forall e, In e l -> dd_id (snd e) <> dd_id dd).
  { intros e He Heq.
    assert (Hin: In (fst e) (hs_nonnull tbl))
      by (eapply Permutation_in; [symmetry; exact Hperm | apply in_map; auto]).
    unfold hs_nonnull in Hin. apply filter_In in Hin as [Hin _].
    apply In_Znth in Hin as (j & Hj & Hje).
    assert (Hd: 0 <= (j - h) mod n < n) by (apply Z.mod_pos_bound; lia).
    assert (Hjd: hs_slot h ((j - h) mod n) n = j) by (apply ep_slot_of; auto).
    assert (Hfe: fst e <> nullval)
      by (apply ep_ptr_nonnull; rewrite Forall_forall in Hptr; apply Hptr; auto).
    destruct (Z.lt_total ((j - h) mod n) t) as [Hlt | [Heqt | Hgt]].
    - destruct (Hprobe ((j - h) mod n) ltac:(lia)) as [_ Hid]. apply Hid.
      rewrite Hjd, Hje. rewrite ep_set_id; auto.
    - subst s. rewrite <- Heqt, Hjd, Hje in Hnull. contradiction.
    - apply (Hpr j e Hj He Hje t). fold n. rewrite Heq. fold h. lia.
      rewrite Heq. fold h. exact Hnull. }
  assert (Hadd: set_add l q dd = l ++ [(q, dd)]).
  { unfold set_add. destruct (existsb _ l) eqn:E; auto.
    apply existsb_exists in E as (e & He & Heq). apply Z.eqb_eq in Heq. exfalso; apply (Hnone e); auto. }
  split; auto.
  unfold hs_inv0; cbv zeta. rewrite Zlength_upd_Znth. fold n.
  assert (Hqnn: q <> nullval) by (apply ep_ptr_nonnull; auto).
  split; [auto|]. split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [|split; [|split; [|split; [|split]]]].
  - apply Permutation_NoDup with (q :: map fst l); [rewrite map_app; cbn [map fst]; apply Permutation_cons_append|].
    constructor; auto.
  - rewrite ep_ids_distinct_NoDup in Hids |- *. rewrite map_app; cbn [map fst snd].
    apply Permutation_NoDup with (dd_id dd :: map (fun e => dd_id (snd e)) l); [apply Permutation_cons_append|].
    constructor; auto. intros Hin. apply in_map_iff in Hin as (e & He1 & He2). apply (Hnone e); auto.
  - apply Forall_app; split; auto.
  - destruct (ep_nonnull_upd tbl s q Hs) as [E1 E2]. rewrite E2. rewrite E1 in Hperm.
    rewrite Hnull, ep_null_one, app_nil_l in Hperm. rewrite ep_nonnull_one by auto. cbn [app] in Hperm |- *.
    rewrite map_app. cbn [map fst]. apply Permutation_elt. rewrite app_nil_r. exact Hperm.
  - apply Forall_upd_Znth; auto.
  - intros j e Hj Hin Hje t0 Ht0. apply in_app_or in Hin as [Hin | [<- | []]].
    + assert (Hjs: j <> s).
      { intros ->. rewrite upd_Znth_same in Hje by auto. apply Hqn. rewrite Hje. apply in_map; auto. }
      rewrite Znth_upd_Znth_diff in Hje by auto.
      apply ep_upd_nonnull; auto. apply (Hpr j e); auto.
    + cbn [fst snd] in Hje, Ht0 |- *. assert (j = s) by (eapply ep_q_at; eauto). subst j.
      fold h in Ht0. unfold s in Ht0. rewrite ep_slot_dist in Ht0 by auto.
      apply ep_upd_nonnull; auto. apply (Hprobe t0); lia.
Qed.

Lemma ep_replace : PF_replace.
Proof.
  unfold PF_replace. intros l tbl q dd t; cbv zeta.
  intros Hinv Hq Hqn Ht Hnn Hid.
  pose proof (ep_npos _ _ Hinv) as Hn.
  pose proof Hinv as Hinv'. unfold hs_inv0 in Hinv'; cbv zeta in Hinv'.
  destruct Hinv' as (Hpow & Hl & Hnd & Hids & Hptr & Hperm & Hnp & Hpr).
  set (n := Zlength tbl) in *. set (h := hs_home (dd_id dd) n) in *.
  set (s := hs_slot h t n) in *.
  assert (Hs: 0 <= s < n) by (apply ep_slot_range; auto).
  assert (Hqnn: q <> nullval) by (apply ep_ptr_nonnull; auto).
  pose proof (ep_nonnull_in l tbl s Hinv Hs Hnn) as Hin.
  apply in_map_iff in Hin as (e & Hes & He).
  rewrite <- Hes, ep_set_id in Hid by auto.
  destruct (in_split e l He) as (l1 & l2 & El).
  pose proof Hids as Hids'. rewrite ep_ids_distinct_NoDup in Hids'.
  rewrite El, map_app in Hids'. simpl in Hids'. apply NoDup_remove_2 in Hids'.
  assert (Hother: forall x, In x (l1 ++ l2) -> dd_id (snd x) <> dd_id dd).
  { intros x Hx Heq. apply Hids'. rewrite <- map_app. apply in_map_iff. exists x; split; auto. congruence. }
  assert (Hadd: set_add l q dd = l1 ++ (q, dd) :: l2).
  { unfold set_add. replace (existsb _ l) with true.
    2:{ symmetry. apply existsb_exists. exists e; split; auto. apply Z.eqb_eq; auto. }
    rewrite El, map_app. cbn [map fst snd]. rewrite Hid, Z.eqb_refl. f_equal; [|f_equal].
    - rewrite <- (map_id l1) at 2. apply map_ext_in. intros x Hx.
      destruct (dd_id (snd x) =? dd_id dd) eqn:E; auto. apply Z.eqb_eq in E.
      exfalso; apply (Hother x); auto. apply in_or_app; auto.
    - rewrite <- (map_id l2) at 2. apply map_ext_in. intros x Hx.
      destruct (dd_id (snd x) =? dd_id dd) eqn:E; auto. apply Z.eqb_eq in E.
      exfalso; apply (Hother x); auto. apply in_or_app; auto. }
  rewrite Hadd. subst l.
  split; [rewrite !Zlength_app, !Zlength_cons; lia|].
  unfold hs_inv0; cbv zeta. rewrite Zlength_upd_Znth. fold n.
  assert (Hqo: ~ In q (map fst l1 ++ map fst l2)).
  { intros Hx. apply Hqn. rewrite map_app. apply in_app_or in Hx as [Hx|Hx]; apply in_or_app; simpl; auto. }
  split; [auto|]. split; [rewrite !Zlength_app, !Zlength_cons in Hl |- *; lia|].
  split; [|split; [|split; [|split; [|split]]]].
  - rewrite map_app in Hnd |- *. cbn [map fst] in Hnd |- *. apply Permutation_NoDup with (q :: map fst l1 ++ map fst l2);
      [apply Permutation_middle|]. constructor; auto. eapply NoDup_remove_1; eauto.
  - replace (map (fun e0 => dd_id (snd e0)) (l1 ++ (q, dd) :: l2))
      with (map (fun e0 => dd_id (snd e0)) (l1 ++ e :: l2)); auto.
    rewrite !map_app; cbn [map fst snd]; rewrite Hid; reflexivity.
  - apply Forall_app in Hptr as [H1 H2]. inversion H2; subst. apply Forall_app; split; auto.
  - destruct (ep_nonnull_upd tbl s q Hs) as [E1 E2]. rewrite E2. rewrite E1 in Hperm.
    rewrite <- Hes in Hperm. rewrite ep_nonnull_one in Hperm by (rewrite Hes; auto).
    rewrite ep_nonnull_one by auto. rewrite map_app in Hperm |- *. cbn [app map fst] in Hperm |- *.
    apply Permutation_elt. eapply Permutation_app_inv; eauto.
  - apply Forall_upd_Znth; auto.
  - intros j e' Hj Hin Hje t0 Ht0.
    assert (Hold: forall x, In x l1 \/ In x l2 -> In x (l1 ++ e :: l2))
      by (intros x [Hx|Hx]; apply in_or_app; simpl; auto).
    apply in_app_or in Hin as [Hin | [<- | Hin]].
    3, 1: assert (Hin': In e' (l1 ++ e :: l2)) by (apply Hold; auto);
      assert (Hjs: j <> s)
        by (intros ->; rewrite upd_Znth_same in Hje by auto; apply Hqn; rewrite Hje; apply in_map; auto);
      rewrite Znth_upd_Znth_diff in Hje by auto;
      apply ep_upd_nonnull; auto; apply (Hpr j e'); auto.
    cbn [fst snd] in Hje, Ht0 |- *. assert (j = s) by (eapply ep_q_at; eauto). subst j.
    apply ep_upd_nonnull; auto. rewrite <- Hid. apply (Hpr s e); auto. rewrite Hid. exact Ht0.
Qed.

End EmplacePure.

Lemma set_emplace_pure : PF_insert /\ PF_replace.
Proof.
  split; [apply ep_insert | apply ep_replace].
Qed.

End CM_SetEmplacePure_1.
