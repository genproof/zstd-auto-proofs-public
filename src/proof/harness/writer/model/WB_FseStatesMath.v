(* Facts for the body of fse_states (harness/writer.h; template WB_fse_states): the cells of a
   writer table, counting the states of a symbol, and building fse_chain from its last state backwards. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Local Open Scope Z_scope.

(* the cells of the table of a writer fse_t *)
Lemma wfs_tab : forall F, wf_ok F ->
  ft_log (wf_table F) = wf_log F /\ 0 <= wf_log F <= 9 /\
  forall i, 0 <= i < 2 ^ wf_log F ->
    0 <= fe_sym (fse_cell (wf_table F) i) < 256 /\
    0 <= fe_nb (fse_cell (wf_table F) i) <= wf_log F /\ 0 <= fe_base (fse_cell (wf_table F) i) /\
    fe_base (fse_cell (wf_table F) i) + 2 ^ fe_nb (fse_cell (wf_table F) i) <= 2 ^ wf_log F.
Proof.
  intros F Hok. unfold wf_ok, wf_table in *. destruct (wf_log F =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. split; [reflexivity|]. split; [lia|].
    intros i Hi. simpl in Hi. assert (i = 0) by lia. subst i. unfold fse_cell, fse_rle; simpl. lia.
  - destruct Hok as [Hnd Hn]. destruct (fse_build_cells _ _ Hnd) as [H1 [_ H3]].
    pose proof Hnd as [Hl [Hlen _]]. split; [auto|]. split; [lia|].
    intros i Hi. specialize (H3 i Hi). cbv zeta in H3. lia.
Qed.

(* the number of j < n with f j *)
Fixpoint zcount (f: Z -> bool) (n: nat) : Z :=
  match n with O => 0 | S m => zcount f m + (if f (Z.of_nat m) then 1 else 0) end.

Lemma zcount_step : forall f s, 0 <= s ->
  zcount f (Z.to_nat (s + 1)) = zcount f (Z.to_nat s) + (if f s then 1 else 0).
Proof.
  intros. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma zcount_bounds : forall f n, 0 <= zcount f n <= Z.of_nat n.
Proof. induction n; [simpl; lia|]. rewrite Nat2Z.inj_succ. simpl. destruct (f _); lia. Qed.

Lemma zcount_pos : forall f n j, 0 <= j < Z.of_nat n -> f j = true -> 0 < zcount f n.
Proof.
  induction n; intros j Hj Hf; [simpl in Hj; lia|]. rewrite Nat2Z.inj_succ in Hj. simpl.
  destruct (Z.eq_dec j (Z.of_nat n)) as [->|Hne].
  - rewrite Hf. pose proof (zcount_bounds f n). lia.
  - pose proof (IHn j ltac:(lia) Hf). destruct (f (Z.of_nat n)); lia.
Qed.

Lemma zcount_0 : forall f, zcount f (Z.to_nat 0) = 0.
Proof. reflexivity. Qed.

(* zn and Znth *)
Lemma wfs_zn_Znth : forall l i, 0 <= i -> zn l i = Znth i l.
Proof. intros. unfold zn, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity]. Qed.

Lemma wfs_zn_cons : forall x l i, 0 < i -> zn (x :: l) i = zn l (i - 1).
Proof. intros. unfold zn. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity. Qed.

Lemma wfs_zn_0 : forall x l, zn (x :: l) 0 = x.
Proof. reflexivity. Qed.

(* fse_chain from the last state backwards *)
Lemma wfs_chain_one : forall tab c s,
  0 <= s < 2 ^ ft_log tab -> fe_sym (fse_cell tab s) = c -> fse_chain tab [c] [s].
Proof.
  intros. unfold fse_chain. split; [reflexivity|]. split.
  - intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. assert (i = 0) by lia. subst. auto.
  - intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia.
Qed.

Lemma wfs_chain_cons : forall tab c cs s sts, fse_chain tab cs sts ->
  0 <= s < 2 ^ ft_log tab -> fe_sym (fse_cell tab s) = c ->
  fe_base (fse_cell tab s) <= zn sts 0 < fe_base (fse_cell tab s) + 2 ^ fe_nb (fse_cell tab s) ->
  fse_chain tab (c :: cs) (s :: sts).
Proof.
  intros tab c cs s sts [HL [H1 H2]] Hs Hc Hb. split; [rewrite !Zlength_cons; lia|]. split.
  - intros i Hi. rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0) as [->|Hne]; [auto|].
    rewrite !wfs_zn_cons by lia. apply H1. lia.
  - intros i Hi. rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0) as [->|Hne].
    + rewrite wfs_zn_0, wfs_zn_cons by lia. exact Hb.
    + rewrite !wfs_zn_cons by lia. replace (i + 1 - 1) with (i - 1 + 1) by lia. apply H2. lia.
Qed.

(* the chain on the suffix from i, extended by the state of position i - 1 *)
Lemma wfs_chain_step : forall tab cs i sts s, 0 < i <= Zlength cs ->
  fse_chain tab (sublist i (Zlength cs) cs) sts ->
  0 <= s < 2 ^ ft_log tab -> fe_sym (fse_cell tab s) = Znth (i - 1) cs ->
  fe_base (fse_cell tab s) <= zn sts 0 < fe_base (fse_cell tab s) + 2 ^ fe_nb (fse_cell tab s) ->
  fse_chain tab (sublist (i - 1) (Zlength cs) cs) (s :: sts).
Proof.
  intros. rewrite (sublist_split (i - 1) i) by lia.
  replace (sublist (i - 1) i cs) with [Znth (i - 1) cs] by (rewrite <- sublist_len_1 by lia; f_equal; lia).
  simpl app. apply wfs_chain_cons; auto.
Qed.

Lemma wfs_byte_at : forall cs i, bytes_ok cs -> 0 <= i < Zlength cs -> 0 <= Znth i cs < 256.
Proof. intros cs i H Hi. unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply Znth_In; auto. Qed.

Lemma wfs_has_at : forall F cs i, Forall (fun x => fse_has_b F x = true) cs -> 0 <= i < Zlength cs ->
  fse_has_b F (Znth i cs) = true.
Proof. intros F cs i H Hi. rewrite Forall_forall in H. apply H. apply Znth_In; auto. Qed.

(* two small unsigned values compared as ints *)
Lemma wfs_repr_eq : forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Int.repr a = Int.repr b -> a = b.
Proof. intros. apply repr_inj_unsigned; auto. Qed.

(* loads produce Znth with their own Inhabitant instance *)
Lemma wfs_Znth_d : forall (d1 d2: Inhabitant val) (l: list val) i, 0 <= i < Zlength l ->
  @Znth val d1 i l = @Znth val d2 i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [lia|]. apply nth_indep. rewrite Zlength_correct in H. lia.
Qed.

(* the second loop of fse_states: after m states of the symbol (f), pick = r - m; st[k-1] is still
   unwritten while m <= r, and holds the r-th state (sx) afterwards *)
Definition wfs_pick_inv (f: Z -> bool) (L k r m: Z) (stv: list val) : Prop :=
  (m <= r -> stv = Zrepeat Vundef k) /\
  (r < m -> exists sx, 0 <= sx < 2 ^ L /\ f sx = true /\ stv = upd_Znth (k - 1) (Zrepeat Vundef k) (Vint (Int.repr sx))).

Lemma wfs_pick_inv_0 : forall f L k r, 0 <= r -> wfs_pick_inv f L k r 0 (Zrepeat Vundef k).
Proof. intros. split; intros; [reflexivity | lia]. Qed.

Lemma wfs_pick_inv_hit : forall f L k r m stv i, wfs_pick_inv f L k r m stv -> m = r ->
  0 <= i < 2 ^ L -> f i = true ->
  stv = Zrepeat Vundef k /\
  wfs_pick_inv f L k r (m + 1) (upd_Znth (k - 1) (Zrepeat Vundef k) (Vint (Int.repr i))).
Proof.
  intros f L k r m stv i [H1 H2] Hm Hi Hf. split; [apply H1; lia|]. split; intros; [lia|]. exists i. auto.
Qed.

Lemma wfs_pick_inv_miss : forall f L k r m stv, wfs_pick_inv f L k r m stv -> m <> r ->
  wfs_pick_inv f L k r (m + 1) stv.
Proof.
  intros f L k r m stv [H1 H2] Hm. split; intros.
  - apply H1. lia.
  - apply H2. lia.
Qed.

(* the main loop: the states from position i on *)
Definition wfs_chain_at (tab: fse_table) (cs: list Z) (i: Z) (suf: list Z) : Prop :=
  0 <= i <= Zlength cs - 1 /\ fse_chain tab (sublist i (Zlength cs) cs) suf.

(* a state for position i - 1 that leads to x, the state of position i *)
Definition wfs_pred_ok (tab: fse_table) (L: Z) (c x s: Z) : Prop :=
  0 <= s < 2 ^ L /\ fe_sym (fse_cell tab s) = c /\
  fe_base (fse_cell tab s) <= x < fe_base (fse_cell tab s) + 2 ^ fe_nb (fse_cell tab s).

Lemma wfs_chain_at_start : forall tab cs sx, 1 <= Zlength cs ->
  0 <= sx < 2 ^ ft_log tab -> fe_sym (fse_cell tab sx) = Znth (Zlength cs - 1) cs ->
  wfs_chain_at tab cs (Zlength cs - 1) [sx].
Proof.
  intros. split; [lia|]. replace (sublist (Zlength cs - 1) (Zlength cs) cs) with [Znth (Zlength cs - 1) cs].
  - apply wfs_chain_one; auto.
  - rewrite <- sublist_len_1 by lia. f_equal. lia.
Qed.

Lemma wfs_chain_at_len : forall tab cs i suf, wfs_chain_at tab cs i suf -> Zlength suf = Zlength cs - i.
Proof. intros tab cs i suf [Hi [HL _]]. rewrite HL, Zlength_sublist by lia. lia. Qed.

Lemma wfs_chain_at_step : forall tab cs i suf s, wfs_chain_at tab cs i suf -> 0 < i ->
  wfs_pred_ok tab (ft_log tab) (Znth (i - 1) cs) (Znth 0 suf) s ->
  wfs_chain_at tab cs (i - 1) (s :: suf).
Proof.
  intros tab cs i suf s [Hi Hc] Hpos [Hs [Hsym Hb]]. split; [lia|].
  apply wfs_chain_step; [lia | auto | auto | auto | rewrite wfs_zn_Znth by lia; auto].
Qed.

Lemma wfs_chain_at_end : forall tab cs suf, wfs_chain_at tab cs 0 suf -> fse_chain tab cs suf.
Proof. intros tab cs suf [_ Hc]. rewrite sublist_same in Hc by lia. auto. Qed.

Lemma wfs_ushort : forall s, 0 <= s < 65536 -> Int.zero_ext 16 (Int.repr s) = Int.repr s.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma wfs_chain_at_hd : forall tab cs i suf, wfs_chain_at tab cs i suf ->
  0 <= Znth 0 suf < 2 ^ ft_log tab.
Proof.
  intros tab cs i suf [Hi [HL [H1 _]]]. rewrite Zlength_sublist in H1 by lia.
  rewrite <- wfs_zn_Znth by lia. apply (H1 0). lia.
Qed.

Lemma wfs_zrepeat_last : forall {A} (x: A) i, 0 < i -> Zrepeat x i = Zrepeat x (i - 1) ++ [x].
Proof.
  intros. unfold Zrepeat. replace (Z.to_nat i) with (Z.to_nat (i - 1) + 1)%nat by lia.
  rewrite repeat_app. reflexivity.
Qed.

Lemma wfs_shl1 : forall n, 0 <= n <= 30 -> Int.shl (Int.repr 1) (Int.repr n) = Int.repr (2 ^ n).
Proof.
  intros. rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv, Int.mul_commut, Int.mul_one. reflexivity.
Qed.

Lemma wfs_upd_rep : forall n (v w: val) (l: list val), 0 <= n ->
  upd_Znth n (Zrepeat Vundef n ++ v :: l) w = Zrepeat Vundef n ++ w :: l.
Proof.
  intros. rewrite upd_Znth_app2 by (rewrite Zlength_Zrepeat by lia; rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia).
  rewrite Zlength_Zrepeat by lia. replace (n - n) with 0 by lia. rewrite upd_Znth0. reflexivity.
Qed.
