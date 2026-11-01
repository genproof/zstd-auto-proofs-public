(* FS3 set part: creation, ZSTD_DDictHashSet_expand's refill, ZSTD_DDictHashSet_addDDict's invariant (plain Coq). *)
Require Import Zstd.proof.dec.v3.FS.set.SetDefs.
Local Open Scope logic.

Section CM_SetExpandPure_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section ExpPure.
Local Open Scope Z_scope.

Lemma sep_veqb_true (a b: val) : veqb a b = true <-> a = b.
Proof. unfold veqb; destruct (Val.eq a b); split; congruence. Qed.

Lemma sep_nn_true (v: val) : v <> nullval -> negb (veqb v nullval) = true.
Proof. intro H; apply Bool.negb_true_iff, Bool.not_true_iff_false; rewrite sep_veqb_true; auto. Qed.

Lemma sep_hs_nonnull_app (a b: list val) : hs_nonnull (a ++ b) = hs_nonnull a ++ hs_nonnull b.
Proof. unfold hs_nonnull; apply filter_app. Qed.

Lemma sep_hs_nonnull_In (v: val) (tbl: list val) : In v (hs_nonnull tbl) <-> In v tbl /\ v <> nullval.
Proof.
  unfold hs_nonnull; rewrite filter_In, Bool.negb_true_iff.
  split; intros [H1 H2]; split; auto.
  - intro E; subst; unfold veqb in H2; destruct (Val.eq nullval nullval); congruence.
  - unfold veqb; destruct (Val.eq v nullval); congruence.
Qed.

Lemma sep_hs_nonnull_repeat (m: Z) : hs_nonnull (Zrepeat nullval m) = nil.
Proof.
  unfold Zrepeat, hs_nonnull; induction (Z.to_nat m) as [|k IH]; [reflexivity|].
  cbn [repeat filter]; rewrite IH.
  unfold veqb; destruct (Val.eq nullval nullval); simpl; congruence.
Qed.

Lemma sep_set_entry_fst (l: list (val * ddict_st)) (v: val) : fst (set_entry l v) = v.
Proof.
  unfold set_entry; destruct (find (fun e => veqb (fst e) v) l) eqn:E; auto.
  apply find_some in E; destruct E as [_ E]; apply sep_veqb_true in E; auto.
Qed.

Lemma sep_map_fst_l_upto l tbl i : map fst (l_upto l tbl i) = hs_nonnull (sublist 0 i tbl).
Proof.
  unfold l_upto; rewrite map_map.
  erewrite map_ext by (intro; apply sep_set_entry_fst); apply map_id.
Qed.

Lemma sep_set_entry_in (l: list (val * ddict_st)) (v: val) : In v (map fst l) -> In (set_entry l v) l.
Proof.
  intro H; unfold set_entry; destruct (find (fun e => veqb (fst e) v) l) eqn:E.
  - apply find_some in E; tauto.
  - exfalso; apply in_map_iff in H; destruct H as [e [He Hin]].
    pose proof (find_none _ _ E e Hin) as F; simpl in F.
    subst; unfold veqb in F; destruct (Val.eq (fst e) (fst e)); congruence.
Qed.

Lemma sep_nodup_map_inj {A B} (f: A -> B) (l: list A) x y :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a r IH]; simpl; [tauto|].
  intros ND Hx Hy Hf; inversion ND as [|? ? Hn ND']; subst.
  destruct Hx as [Hx|Hx], Hy as [Hy|Hy]; subst; auto.
  - exfalso; apply Hn; rewrite Hf; apply in_map; auto.
  - exfalso; apply Hn; rewrite <- Hf; apply in_map; auto.
Qed.

Lemma sep_set_entry_mem (l: list (val * ddict_st)) e : NoDup (map fst l) -> In e l -> set_entry l (fst e) = e.
Proof.
  intros ND H; unfold set_entry; destruct (find (fun e' => veqb (fst e') (fst e)) l) eqn:E.
  - apply find_some in E; destruct E as [Hin E]; apply sep_veqb_true in E.
    eapply sep_nodup_map_inj; eauto.
  - exfalso; pose proof (find_none _ _ E e H) as F; simpl in F.
    unfold veqb in F; destruct (Val.eq (fst e) (fst e)); congruence.
Qed.

Lemma sep_ids_distinct_NoDup (l: list Z) : ids_distinct l = true <-> NoDup l.
Proof.
  induction l as [|x r IH]; simpl.
  - split; auto; constructor.
  - rewrite Bool.andb_true_iff, Bool.negb_true_iff, IH; split.
    + intros [H1 H2]; constructor; auto; intro Hin.
      assert (existsb (Z.eqb x) r = true) by (apply existsb_exists; exists x; split; auto; apply Z.eqb_refl).
      congruence.
    + intro ND; inversion ND as [|? ? Hn ND']; subst; split; auto.
      destruct (existsb (Z.eqb x) r) eqn:E; auto.
      apply existsb_exists in E; destruct E as [y [Hy E]]; apply Z.eqb_eq in E; subst; contradiction.
Qed.

Lemma sep_hs_inv0_perm (L l: list (val * ddict_st)) tbl :
  Permutation L l -> hs_inv0 L tbl -> hs_inv0 l tbl.
Proof.
  intros P H; unfold hs_inv0 in *.
  destruct H as [Hk [Hlt [ND [ID [Fp [Pm [Ft Hpr]]]]]]].
  assert (Zlength L = Zlength l) by (rewrite !Zlength_correct, (Permutation_length P); auto).
  split; [auto|]. split; [lia|].
  split; [eapply Permutation_NoDup; [apply Permutation_map; exact P|exact ND]|].
  split.
  { apply sep_ids_distinct_NoDup; apply sep_ids_distinct_NoDup in ID.
    eapply Permutation_NoDup; [apply Permutation_map; exact P|exact ID]. }
  split.
  { rewrite Forall_forall in *; intros x Hx; apply Fp; eapply Permutation_in; [symmetry; exact P|exact Hx]. }
  split; [eapply perm_trans; [exact Pm|apply Permutation_map; exact P]|].
  split; [auto|].
  intros j e Hj He; apply Hpr; auto; eapply Permutation_in; [symmetry; exact P|exact He].
Qed.

Lemma sep_set_add_len (l: list (val * ddict_st)) q dd : Zlength l <= Zlength (set_add l q dd).
Proof.
  unfold set_add; destruct (existsb _ l).
  - rewrite Zlength_map; lia.
  - rewrite Zlength_app; pose proof (Zlength_nonneg ((q, dd) :: nil)); lia.
Qed.

Lemma sep_inv_empty k : 6 <= k -> hs_inv0 nil (Zrepeat nullval (2 ^ k)).
Proof.
  intro Hk; unfold hs_inv0.
  assert (Hp: 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zlength_Zrepeat by lia.
  split; [exists k; auto|].
  split; [rewrite Zlength_nil; lia|].
  split; [constructor|]. split; [reflexivity|]. split; [constructor|].
  split; [rewrite sep_hs_nonnull_repeat; constructor|].
  split.
  { apply Forall_forall; intros x Hx; left; unfold Zrepeat in Hx; apply repeat_spec in Hx; auto. }
  intros j e _ He; destruct He.
Qed.

Lemma sep_init_gen (m: Z) : (exists k, 6 <= k /\ m = 2 ^ k) -> m <= 64 -> hs_inv nil (Zrepeat nullval m).
Proof.
  intros [k [Hk Hm]] H64.
  assert (Hp: 0 < m) by (subst m; apply Z.pow_pos_nonneg; lia).
  pose proof (sep_inv_empty k Hk) as H0; rewrite <- Hm in H0.
  unfold hs_inv0, hs_inv in *.
  destruct H0 as [Hk' Hr]; split; [exact Hk'|]; split; [|exact Hr].
  rewrite Zlength_Zrepeat, Zlength_nil by lia; lia.
Qed.

Lemma sep_init : hs_inv nil (Zrepeat nullval 64).
Proof. apply sep_init_gen; [exists 6; split; [lia|reflexivity]|lia]. Qed.

End ExpPure.

Lemma set_expand_pure : PF_init /\ PF_exp_init /\ PF_exp_step /\ PF_exp_skip /\ PF_exp_end /\ PF_add_noexp /\ PF_add_exp.
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* PF_init *)
    exact sep_init.
  - exact sep_inv_empty.
  - (* PF_exp_step *)
    intros l tbl i H Hi Hv.
    destruct H as [_ [_ [_ [ND [ID [_ [Pm _]]]]]]].
    set (v := Znth i tbl) in *.
    set (A := hs_nonnull (sublist 0 i tbl)).
    set (B := hs_nonnull (sublist (i + 1) (Zlength tbl) tbl)).
    assert (Esp: tbl = sublist 0 i tbl ++ v :: sublist (i + 1) (Zlength tbl) tbl).
    { rewrite <- (sublist_same 0 (Zlength tbl) tbl) at 1 by auto.
      rewrite (sublist_split 0 i (Zlength tbl)) by lia.
      rewrite (sublist_split i (i + 1) (Zlength tbl)) by lia.
      rewrite sublist_len_1 by lia; reflexivity. }
    assert (Enn: hs_nonnull tbl = A ++ v :: B).
    { rewrite Esp at 1; rewrite sep_hs_nonnull_app; f_equal.
      unfold hs_nonnull at 1; simpl.
      rewrite (sep_nn_true v Hv); reflexivity. }
    change (filter (fun v0 => negb (veqb v0 nullval)) tbl) with (hs_nonnull tbl) in Pm.
    rewrite Enn in Pm.
    assert (NDA: NoDup (A ++ v :: B)) by (eapply Permutation_NoDup; [symmetry; exact Pm|exact ND]).
    assert (HvA: ~ In v A) by (intro; eapply (NoDup_remove_2 A B v NDA); apply in_or_app; auto).
    assert (Hvl: In v (map fst l)) by (eapply Permutation_in; [exact Pm|apply in_or_app; right; left; auto]).
    assert (Hent: set_entry l v = (v, snd (set_entry l v))).
    { pose proof (sep_set_entry_fst l v) as F; destruct (set_entry l v); simpl in *; subst; auto. }
    assert (Hin: In (set_entry l v) l) by (apply sep_set_entry_in; auto).
    assert (Hincl: incl (l_upto l tbl i) l).
    { intros e He; unfold l_upto in He; fold A in He.
      apply in_map_iff in He; destruct He as [x [Ex Hx]]; subst e.
      apply sep_set_entry_in; eapply Permutation_in; [exact Pm|apply in_or_app; auto]. }
    split; [exact Hent|]. split; [exact Hin|]. split; [exact Hincl|].
    split; [rewrite sep_map_fst_l_upto; exact HvA|].
    split.
    { unfold l_upto; fold A; rewrite Zlength_map.
      apply Permutation_length in Pm; rewrite length_map, length_app in Pm; simpl in Pm.
      rewrite !Zlength_correct; lia. }
    unfold l_upto at 2; rewrite sublist_last_1 by lia; rewrite sep_hs_nonnull_app.
    fold A; fold v.
    assert (Ev: hs_nonnull [v] = [v]).
    { unfold hs_nonnull; simpl; rewrite (sep_nn_true v Hv); reflexivity. }
    rewrite Ev, map_app; cbn [map].
    unfold set_add; unfold l_upto; fold A.
    replace (existsb _ (map (set_entry l) A)) with false; [rewrite <- Hent; reflexivity|].
    symmetry; apply Bool.not_true_iff_false; intro E.
    apply existsb_exists in E; destruct E as [e [He E]]; apply Z.eqb_eq in E.
    apply in_map_iff in He; destruct He as [x [Ex Hx]].
    assert (Hxl: In e l) by (subst e; apply sep_set_entry_in; eapply Permutation_in; [exact Pm|apply in_or_app; auto]).
    apply sep_ids_distinct_NoDup in ID.
    assert (e = set_entry l v).
    { eapply (sep_nodup_map_inj (fun e => dd_id (snd e))); eauto. }
    apply HvA; rewrite <- (sep_set_entry_fst l v), <- H, <- Ex, sep_set_entry_fst; exact Hx.
  - (* PF_exp_skip *)
    intros l tbl i Hi Hv; unfold l_upto.
    rewrite sublist_last_1 by lia; rewrite sep_hs_nonnull_app, Hv.
    unfold hs_nonnull at 2; simpl.
    unfold veqb; destruct (Val.eq nullval nullval); [|congruence]; simpl.
    rewrite app_nil_r; reflexivity.
  - (* PF_exp_end *)
    intros l tbl tbl' H H0.
    destruct H as [_ [_ [_ [ND [_ [_ [Pm _]]]]]]].
    change (filter (fun v0 => negb (veqb v0 nullval)) tbl) with (hs_nonnull tbl) in Pm.
    assert (P: Permutation (l_upto l tbl (Zlength tbl)) l).
    { unfold l_upto; rewrite sublist_same by auto.
      eapply perm_trans; [apply Permutation_map; exact Pm|].
      rewrite map_map; erewrite map_ext_in; [rewrite map_id; apply Permutation_refl|].
      intros e He; apply sep_set_entry_mem; auto. }
    split; [eapply sep_hs_inv0_perm; eauto|].
    pose proof (Permutation_length P) as LP.
    rewrite (Zlength_correct (l_upto _ _ _)), (Zlength_correct l), LP; reflexivity.
  - (* PF_add_noexp *)
    intros l tbl tbl' q dd H Hlt Hn H0.
    pose proof (sep_set_add_len l q dd).
    destruct H as [_ [Hb _]].
    unfold hs_inv0 in H0; unfold hs_inv.
    destruct H0 as [Hk Hr]; split; [exact Hk|]; split; [|exact Hr].
    rewrite Hn; lia.
  - (* PF_add_exp *)
    intros l tbl tbl' q dd H Hlt Hn H0.
    pose proof (sep_set_add_len l q dd).
    destruct H as [_ [Hb _]].
    unfold hs_inv0 in H0; unfold hs_inv.
    destruct H0 as [Hk Hr]; split; [exact Hk|]; split; [|exact Hr].
    rewrite Hn; lia.
Qed.

End CM_SetExpandPure_1.
