(* FS3 set part: what the probe means, and the table facts the probing loops use (plain Coq). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetProbe_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section SetProbeHelpers.
Local Open Scope Z_scope.

Lemma sp_veqb_true : forall a b, veqb a b = true -> a = b.
Proof. intros a b H. unfold veqb in H. destruct (Val.eq a b); congruence. Qed.

Lemma sp_veqb_refl : forall a, veqb a a = true.
Proof. intros a. unfold veqb. destruct (Val.eq a a); congruence. Qed.

Lemma sp_inv0 : forall l tbl, hs_inv l tbl -> hs_inv0 l tbl.
Proof.
  intros l tbl H. unfold hs_inv in H; unfold hs_inv0, hs_nonnull.
  destruct H as (? & _ & ?). auto.
Qed.

Lemma sp_member : forall l tbl j,
  hs_inv0 l tbl -> 0 <= j < Zlength tbl -> Znth j tbl <> nullval -> exists e, In e l /\ fst e = Znth j tbl.
Proof.
  intros l tbl j H Hj Hn. destruct H as (_ & _ & _ & _ & _ & Hp & _ & _).
  assert (In (Znth j tbl) (hs_nonnull tbl)).
  { unfold hs_nonnull. apply filter_In. split. apply Znth_In; auto.
    unfold veqb. destruct (Val.eq (Znth j tbl) nullval); [contradiction | reflexivity]. }
  eapply Permutation_in in H; [| exact Hp].
  apply in_map_iff in H. destruct H as (e & ? & ?). eauto.
Qed.

Lemma sp_set_id : forall (l: list (val * ddict_st)) e,
  NoDup (map fst l) -> In e l -> set_id_of l (fst e) = dd_id (snd e).
Proof.
  intros l e. unfold set_id_of. induction l as [| x r IH]; intros Hnd Hin; simpl in *. contradiction.
  inversion Hnd; subst.
  destruct (veqb (fst x) (fst e)) eqn:E.
  - apply sp_veqb_true in E. destruct Hin as [-> | Hin]; auto.
    exfalso. apply H1. rewrite E. apply in_map; auto.
  - destruct Hin as [-> | Hin]. rewrite sp_veqb_refl in E; discriminate. auto.
Qed.

Lemma sp_ids_uniq : forall (l: list (val * ddict_st)) a b,
  ids_distinct (map (fun e => dd_id (snd e)) l) = true -> In a l -> In b l -> dd_id (snd a) = dd_id (snd b) -> a = b.
Proof.
  induction l as [| x r IH]; intros a b Hd Ha Hb Hab; simpl in *. contradiction.
  apply andb_prop in Hd. destruct Hd as [Hx Hd]. apply negb_true_iff in Hx.
  assert (Hc: forall c, In c r -> dd_id (snd x) <> dd_id (snd c)).
  { intros c Hc Heq. assert (existsb (Z.eqb (dd_id (snd x))) (map (fun e => dd_id (snd e)) r) = true).
    { apply existsb_exists. exists (dd_id (snd c)). split. apply in_map with (f := fun e => dd_id (snd e)); auto.
      apply Z.eqb_eq; auto. }
    congruence. }
  destruct Ha as [<- | Ha], Hb as [<- | Hb]; auto.
  - exfalso. eapply Hc; eauto.
  - exfalso. eapply Hc; eauto.
Qed.

Lemma sp_find_member : forall l e id,
  ids_distinct (map (fun e => dd_id (snd e)) l) = true -> In e l -> dd_id (snd e) = id -> set_find l id = fst e.
Proof.
  intros l e id Hd He Hid. unfold set_find.
  destruct (find (fun e => dd_id (snd e) =? id) l) eqn:F.
  - apply find_some in F. destruct F as [Hp Hq]. apply Z.eqb_eq in Hq.
    f_equal. eapply sp_ids_uniq; eauto. congruence.
  - exfalso. eapply find_none in F; eauto. apply Z.eqb_neq in F. auto.
Qed.

Lemma sp_home_range : forall id k, 0 <= k -> 0 <= hs_home id (2 ^ k) < 2 ^ k.
Proof.
  intros id k Hk. unfold hs_home.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by auto. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma sp_slot_range : forall h t n, 0 < n -> 0 <= hs_slot h t n < n.
Proof. intros. unfold hs_slot. apply Z.mod_pos_bound; auto. Qed.

Lemma sp_slot_succ : forall h t n, 0 < n -> (hs_slot h t n + 1) mod n = hs_slot h (t + 1) n.
Proof.
  intros. unfold hs_slot. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma sp_slot_back : forall h j n, 0 < n -> 0 <= j < n -> hs_slot h ((j - h) mod n) n = j.
Proof.
  intros. unfold hs_slot. rewrite Zplus_mod_idemp_r. replace (h + (j - h)) with j by lia.
  apply Z.mod_small; auto.
Qed.

Definition sp_stop (l: list (val * ddict_st)) (id: Z) (v: val) : Prop :=
  v = nullval \/ set_id_of l v = id \/ set_id_of l v = 0.

Lemma sp_stop_dec : forall l id v, {sp_stop l id v} + {~ sp_stop l id v}.
Proof.
  intros. unfold sp_stop.
  destruct (Val.eq v nullval); [left; auto |].
  destruct (Z.eq_dec (set_id_of l v) id); [left; auto |].
  destruct (Z.eq_dec (set_id_of l v) 0); [left; auto |].
  right. intros [? | [? | ?]]; contradiction.
Qed.

Lemma sp_probe_at : forall l tbl n id h fuel t T,
  0 < n -> t <= T < t + Z.of_nat fuel ->
  (forall t', t <= t' < T -> ~ sp_stop l id (Znth (hs_slot h t' n) tbl)) ->
  sp_stop l id (Znth (hs_slot h T n) tbl) ->
  hs_probe_f fuel l tbl (hs_slot h t n) n id = Znth (hs_slot h T n) tbl.
Proof.
  intros l tbl n id h fuel. induction fuel as [| f IH]; intros t T Hn HT Hpass Hstop.
  - simpl in HT. lia.
  - simpl hs_probe_f.
    destruct (zeq t T) as [-> | Hne].
    + unfold sp_stop in Hstop.
      destruct (EqDec_val (Znth (hs_slot h T n) tbl) nullval) as [E | E]; [rewrite E; auto |].
      destruct Hstop as [? | [Hs | Hs]]; [contradiction | |]; rewrite Hs, ?Z.eqb_refl; simpl;
        [reflexivity | rewrite orb_true_r; reflexivity].
    + assert (Hp := Hpass t ltac:(lia)). unfold sp_stop in Hp.
      destruct (EqDec_val (Znth (hs_slot h t n) tbl) nullval) as [E | E]; [exfalso; apply Hp; auto |].
      replace (orb _ _) with false.
      2: { symmetry. apply orb_false_intro; apply Z.eqb_neq; intro; apply Hp; auto. }
      rewrite sp_slot_succ by auto. apply IH; auto; [lia |].
      intros t' Ht'. apply Hpass. lia.
Qed.

Lemma sp_first : forall (P: Z -> Prop), (forall t, {P t} + {~ P t}) -> forall m: nat,
  (forall t, 0 <= t < Z.of_nat m -> ~ P t) \/
  (exists T, 0 <= T < Z.of_nat m /\ P T /\ forall t, 0 <= t < T -> ~ P t).
Proof.
  intros P Pd m. induction m as [| m IH].
  - left. intros. simpl in H. lia.
  - destruct IH as [IH | IH].
    + destruct (Pd (Z.of_nat m)) as [Hy | Hn].
      * right. exists (Z.of_nat m). split; [lia |]. split; auto.
      * left. intros t Ht. destruct (zeq t (Z.of_nat m)) as [-> | ?]; auto. apply IH. lia.
    + right. destruct IH as (T & ? & ? & ?). exists T. split; [lia | auto].
Qed.

Lemma sp_filter_all : forall (A: Type) (p: A -> bool) (l: list A),
  (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  intros A p l. induction l as [| x r IH]; intros H; simpl; auto.
  rewrite H by (left; auto). f_equal. apply IH. intros; apply H; right; auto.
Qed.

Lemma sp_notfull : forall l tbl h,
  hs_inv0 l tbl -> 0 <= h < Zlength tbl ->
  exists t, 0 <= t < Zlength tbl /\ Znth (hs_slot h t (Zlength tbl)) tbl = nullval.
Proof.
  intros l tbl h H Hh.
  destruct (sp_first (fun t => Znth (hs_slot h t (Zlength tbl)) tbl = nullval)
              (fun t => Val.eq _ _) (Z.to_nat (Zlength tbl))) as [Hall | (T & ? & ? & _)].
  - exfalso. destruct H as (_ & Hlt & _ & _ & _ & Hp & _ & _).
    assert (Hf: hs_nonnull tbl = tbl).
    { unfold hs_nonnull. apply sp_filter_all. intros x Hx.
      apply In_Znth in Hx. destruct Hx as (j & Hj & <-).
      rewrite <- (sp_slot_back h j (Zlength tbl)) by lia.
      unfold veqb. destruct (Val.eq _ _) as [E | E]; auto.
      exfalso. eapply Hall; [| exact E].
      assert (0 <= (j - h) mod Zlength tbl < Zlength tbl) by (apply Z.mod_pos_bound; lia). lia. }
    rewrite Hf in Hp. apply Permutation_length in Hp. rewrite length_map in Hp.
    rewrite !Zlength_correct in Hlt. lia.
  - exists T. split; auto. lia.
Qed.

Lemma sp_probe_ok : hs_probe_ok.
Proof.
  intros l tbl id Hinv Hid.
  pose proof (sp_inv0 _ _ Hinv) as H0.
  remember (Zlength tbl) as n eqn:En.
  pose proof H0 as H0'.
  destruct H0' as (Hk & Hlt & Hnd & Hdist & Hptr & Hperm & Hnn & Hreach).
  rewrite <- En in *.
  destruct Hk as (k & Hk6 & Hn).
  assert (Hnpos: 0 < n) by (rewrite Hn; apply Z.pow_pos_nonneg; lia).
  remember (hs_home id n) as h eqn:Eh.
  assert (Hh: 0 <= h < n) by (subst h; rewrite Hn; apply sp_home_range; lia).
  destruct (sp_notfull l tbl h H0 ltac:(lia)) as (t0 & Ht0 & Hnull0).
  rewrite <- En in *.
  destruct (sp_first (fun t => sp_stop l id (Znth (hs_slot h t n) tbl)) (fun t => sp_stop_dec _ _ _)
              (Z.to_nat n)) as [Hall | (T & HT & Hstop & Hmin)].
  { exfalso. apply (Hall t0); [lia | left; auto]. }
  assert (Hr: hs_probe l tbl id = Znth (hs_slot h T n) tbl).
  { unfold hs_probe. rewrite <- En, <- Eh.
    replace h with (hs_slot h 0 n) at 1 by (unfold hs_slot; rewrite Z.add_0_r; apply Z.mod_small; auto).
    apply sp_probe_at; auto; lia. }
  rewrite Hr. clear Hr.
  assert (HsT := sp_slot_range h T n Hnpos).
  split.
  - destruct (eq_dec (Znth (hs_slot h T n) tbl) nullval) as [E | E]; [left; auto | right].
    destruct (sp_member l tbl (hs_slot h T n) H0 ltac:(lia) E) as (e & He & <-). apply in_map; auto.
  - intros Hnz.
    destruct (eq_dec (Znth (hs_slot h T n) tbl) nullval) as [E | E].
    + rewrite E. unfold set_find.
      destruct (find (fun e => dd_id (snd e) =? id) l) as [e |] eqn:F; auto.
      exfalso. apply find_some in F. destruct F as [He Hq]. apply Z.eqb_eq in Hq.
      assert (Hin: In (fst e) (hs_nonnull tbl)).
      { apply Permutation_in with (map fst l); [apply Permutation_sym; auto | apply in_map; auto]. }
      unfold hs_nonnull in Hin. apply filter_In in Hin. destruct Hin as [Hin _].
      apply In_Znth in Hin. destruct Hin as (j & Hj & Hje).
      set (Te := (j - hs_home (dd_id (snd e)) n) mod n).
      assert (HTe: 0 <= Te < n) by (apply Z.mod_pos_bound; auto).
      assert (Hsl: hs_slot h Te n = j) by (unfold Te; rewrite Hq, <- Eh; apply sp_slot_back; lia).
      destruct (Z_lt_le_dec Te T) as [Hlt' | Hge].
      * apply (Hmin Te); [lia |]. unfold sp_stop. rewrite Hsl, Hje. right; left.
        rewrite sp_set_id by auto. auto.
      * destruct (zeq Te T) as [<- | Hne].
        -- rewrite Hsl, Hje in E. rewrite Forall_forall in Hptr. specialize (Hptr e He).
           destruct (fst e); simpl in Hptr; try contradiction; discriminate.
        -- apply (Hreach j e ltac:(lia) He Hje T); [| rewrite Hq, <- Eh; auto].
           fold Te. lia.
    + destruct (sp_member l tbl (hs_slot h T n) H0 ltac:(lia) E) as (e & He & Hfe).
      unfold sp_stop in Hstop. rewrite <- Hfe in Hstop. rewrite sp_set_id in Hstop by auto.
      rewrite Forall_forall in Hnz. specialize (Hnz e He).
      destruct Hstop as [Hs | [Hs | Hs]]; [rewrite Hfe in Hs; contradiction | | contradiction].
      rewrite <- Hfe. symmetry. apply sp_find_member; auto.
Qed.

End SetProbeHelpers.

Lemma set_probe_ok : hs_probe_ok /\ PF_member /\ PF_set_id /\ PF_notfull /\ PF_inv0.
Proof.
  split; [exact sp_probe_ok |]. split; [exact sp_member |]. split; [exact sp_set_id |].
  split; [exact sp_notfull | exact sp_inv0].
Qed.

End CM_SetProbe_1.
