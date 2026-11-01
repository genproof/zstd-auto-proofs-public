(* Unit-independent lemmas for the body proofs of fse_build (WB_fse_build_<u>.v): the C's three loops
   against Fse.fse_build (place_low, spread, states), stated over the arrays of the fse_t. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* a write list applied to an array of values (the stores into t->sym) *)
Definition fbv (b: list val) (ws: list (Z * Z)) : list val :=
  fold_left (fun t pv => upd_Znth (fst pv) t (Vint (Int.repr (snd pv)))) ws b.

Lemma fbv_app : forall a c b, fbv b (a ++ c) = fbv (fbv b a) c.
Proof. intros. unfold fbv. apply fold_left_app. Qed.

Lemma fbv_snoc : forall b ws p v, fbv b (ws ++ [(p, v)]) = upd_Znth p (fbv b ws) (Vint (Int.repr v)).
Proof. intros. rewrite fbv_app. reflexivity. Qed.

Lemma fbv_Zlength : forall ws b, Zlength (fbv b ws) = Zlength b.
Proof.
  induction ws; intros; simpl; auto. unfold fbv in *. simpl. rewrite IHws. apply Zlength_upd_Znth.
Qed.

Lemma fbv_def : forall ws b, Forall (fun v => exists i, v = Vint i) b ->
  Forall (fun v => exists i, v = Vint i) (fbv b ws).
Proof.
  induction ws; intros b Hb; simpl; auto. unfold fbv in *. simpl. apply IHws.
  destruct (Sumbool.sumbool_and _ _ _ _ (Z_le_gt_dec 0 (fst a)) (Z_lt_dec (fst a) (Zlength b))) as [[H1 H2]|Hn].
  - apply Forall_upd_Znth; auto. eauto.
  - unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _); [lia|auto].
Qed.

Lemma fbv_nth : forall ws b (t: list Z) i,
  (forall p v, In (p, v) ws -> 0 <= p < Z.of_nat (length t)) ->
  Z.of_nat (length t) <= Zlength b -> 0 <= i < Zlength b ->
  Znth i (fbv b ws) =
    if in_dec Nat.eq_dec (Z.to_nat i) (map wft_pn ws) then Vint (Int.repr (nth (Z.to_nat i) (apw t ws) 0))
    else Znth i b.
Proof.
  induction ws as [|[p v] ws IH]; intros b t i Hw Hl Hi; [reflexivity|].
  assert (Hp : 0 <= p < Z.of_nat (length t)) by (eapply Hw; left; reflexivity).
  unfold fbv. simpl fold_left. fold (fbv (upd_Znth p b (Vint (Int.repr v))) ws).
  rewrite apw_cons. change (wft_pn (p, v)) with (Z.to_nat p). change (snd (p, v)) with v.
  rewrite (IH _ (upd (A:=Z) t (Z.to_nat p) v)).
  2: { intros. rewrite wft_upd_length. eapply Hw. right. eauto. }
  2: { rewrite wft_upd_length, Zlength_upd_Znth. auto. }
  2: { rewrite Zlength_upd_Znth. auto. }
  change (map wft_pn ((p, v) :: ws)) with (Z.to_nat p :: map wft_pn ws). destruct (in_dec Nat.eq_dec (Z.to_nat i) (map wft_pn ws)) as [Hin|Hin].
  - destruct (in_dec Nat.eq_dec (Z.to_nat i) (Z.to_nat p :: map wft_pn ws)) as [_|Hn]; [auto|].
    exfalso. apply Hn. right. auto.
  - destruct (Z.eq_dec i p) as [E|E].
    + subst i. rewrite upd_Znth_same by lia.
      destruct (in_dec Nat.eq_dec (Z.to_nat p) (Z.to_nat p :: map wft_pn ws)) as [_|Hn]; [|exfalso; apply Hn; left; auto].
      rewrite apw_notin by auto. rewrite wft_nth_upd_same by lia. reflexivity.
    + rewrite upd_Znth_diff by lia.
      destruct (in_dec Nat.eq_dec (Z.to_nat i) (Z.to_nat p :: map wft_pn ws)) as [Hn|_]; [|auto].
      exfalso. destruct Hn as [Hn|Hn]; [lia|auto].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the loops of place_low and spread, one symbol at a time *)
Lemma wft_lw_snoc : forall norm n s h,
  wft_lw norm s (S n) h = wft_lw norm s n h ++
    (if nth (s + n) norm 0 =? -1 then [(h - Z.of_nat (length (wft_lw norm s n h)), Z.of_nat (s + n))] else nil).
Proof.
  induction n; intros.
  - simpl. rewrite Nat.add_0_r. destruct (nth s norm 0 =? -1); simpl; auto. repeat f_equal; lia.
  - change (wft_lw norm s (S (S n)) h) with
      (if nth s norm 0 =? -1 then (h, Z.of_nat s) :: wft_lw norm (S s) (S n) (h - 1)
       else wft_lw norm (S s) (S n) h).
    change (wft_lw norm s (S n) h) with
      (if nth s norm 0 =? -1 then (h, Z.of_nat s) :: wft_lw norm (S s) n (h - 1)
       else wft_lw norm (S s) n h).
    replace (s + S n)%nat with (S s + n)%nat by lia.
    destruct (nth s norm 0 =? -1).
    + rewrite IHn. simpl length. simpl app. f_equal. f_equal. destruct (nth _ norm 0 =? -1); auto.
      do 2 f_equal. rewrite ?Zpos_P_of_succ_nat. lia.
    + apply IHn.
Qed.

Lemma wft_syms_snoc : forall norm n s,
  wft_syms norm s (S n) = wft_syms norm s n ++
    (let c := nth (s + n) norm 0 in if c >? 0 then repeat (Z.of_nat (s + n)) (Z.to_nat c) else nil).
Proof.
  induction n; intros.
  - simpl. rewrite Nat.add_0_r, !app_nil_r. auto.
  - change (wft_syms norm s (S (S n))) with
      ((let c := nth s norm 0 in if c >? 0 then repeat (Z.of_nat s) (Z.to_nat c) else nil)
        ++ wft_syms norm (S s) (S n)).
    change (wft_syms norm s (S n)) with
      ((let c := nth s norm 0 in if c >? 0 then repeat (Z.of_nat s) (Z.to_nat c) else nil)
        ++ wft_syms norm (S s) n).
    rewrite IHn, app_assoc. replace (S s + n)%nat with (s + S n)%nat by lia. auto.
Qed.

Lemma wft_lw_mono : forall norm m n h, (n <= m)%nat ->
  (length (wft_lw norm 0 n h) <= length (wft_lw norm 0 m h))%nat.
Proof.
  induction m; intros.
  - assert (n = O) by lia. subst. auto.
  - destruct (Nat.eq_dec n (S m)); [subst; auto|].
    rewrite wft_lw_snoc, app_length. specialize (IHm n h ltac:(lia)). lia.
Qed.

Lemma wft_syms_mono : forall norm m n, (n <= m)%nat ->
  (length (wft_syms norm 0 n) <= length (wft_syms norm 0 m))%nat.
Proof.
  induction m; intros.
  - assert (n = O) by lia. subst. auto.
  - destruct (Nat.eq_dec n (S m)); [subst; auto|].
    rewrite wft_syms_snoc, app_length. specialize (IHm n ltac:(lia)). lia.
Qed.

Lemma wft_combine_snoc : forall (L Sd: list Z) x, (length Sd < length L)%nat ->
  combine L (Sd ++ [x]) = combine L Sd ++ [(nth (length Sd) L 0, x)].
Proof.
  intros L Sd. revert L. induction Sd; intros L x H; destruct L; simpl in *; try lia.
  - destruct L; reflexivity.
  - f_equal. apply IHSd. lia.
Qed.

Lemma wft_skipn_cons : forall (L: list Z) k a r, skipn k L = a :: r -> nth k L 0 = a /\ skipn (S k) L = r.
Proof.
  induction L; destruct k; simpl; intros; try discriminate.
  - inversion H; auto.
  - apply IHL; auto.
Qed.

Lemma wft_gp_size : forall log, 0 <= log -> wft_gp log (Z.to_nat (2 ^ log)) = 0.
Proof.
  intros. unfold wft_gp. rewrite Z2Nat.id by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* fse_build as the states of the write list of the C's first two loops *)
Definition fb_LW (norm: list Z) (log: Z) : list (Z * Z) := wft_lw norm 0 (length norm) (2 ^ log - 1).
Definition fb_H (norm: list Z) (log: Z) : Z := 2 ^ log - 1 - Z.of_nat (length (fb_LW norm log)).
Definition fb_L0 (norm: list Z) (log: Z) : list Z := wft_LL log (fb_H norm log) 0.
Definition fb_W (norm: list Z) (log: Z) : list (Z * Z) :=
  fb_LW norm log ++ combine (fb_L0 norm log) (wft_syms norm 0 (length norm)).
Definition fb_T (norm: list Z) (log: Z) : list Z := apw (repeat 0 (Z.to_nat (2 ^ log))) (fb_W norm log).

Lemma fb_count : forall norm log, ndist_base log norm ->
  Z.of_nat (length (fb_LW norm log)) + Z.of_nat (length (wft_syms norm 0 (length norm))) = 2 ^ log.
Proof.
  intros norm log [Hlog [Hlen [Hf Hsum]]].
  assert (Hf1 : Forall (fun p => -1 <= p) norm) by (eapply Forall_impl; [|exact Hf]; simpl; intros; lia).
  pose proof (wft_count norm (length norm) 0 (2 ^ log - 1) eq_refl Hf1) as HC.
  simpl skipn in HC. rewrite Hsum in HC. exact HC.
Qed.

Lemma fb_L0_length : forall norm log, ndist_base log norm ->
  length (fb_L0 norm log) = length (wft_syms norm 0 (length norm)).
Proof.
  intros norm log Hnd. pose proof (fb_count norm log Hnd) as HC. pose proof Hnd as [Hlog _].
  destruct (wft_orbit log Hlog) as [_ [_ O3]]. unfold fb_L0. rewrite O3; unfold fb_H; lia.
Qed.

Lemma fb_build_eq : forall norm log, ndist_base log norm ->
  ft_cells (fse_build norm log) = states log (fb_T norm log) (wft_next0 norm) /\
  (forall p v, In (p, v) (fb_W norm log) -> 0 <= p < 2 ^ log /\
     exists i, (i < length norm)%nat /\ v = Z.of_nat i /\ nth i norm 0 <> 0) /\
  (forall q, (q < Z.to_nat (2 ^ log))%nat -> In q (map wft_pn (fb_W norm log))).
Proof.
  intros norm log Hnd. pose proof Hnd as [Hlog [Hlen [Hf Hsum]]].
  pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) ltac:(lia)) as Hpos.
  destruct (wft_orbit log Hlog) as [O1 [O2 O3]].
  pose proof (fb_count norm log Hnd) as HC. pose proof (fb_L0_length norm log Hnd) as HL0.
  assert (HLWin : forall p v, In (p, v) (fb_LW norm log) -> fb_H norm log < p <= 2 ^ log - 1 /\
            exists i, (0 <= i < 0 + length norm)%nat /\ v = Z.of_nat i /\ nth i norm 0 = -1).
  { intros p v Hp. pose proof (wft_lw_in _ _ _ _ _ _ Hp) as [H1 H2]. unfold fb_H. split; [|exact H2].
    unfold fb_LW in *. lia. }
  assert (HLWcov : forall q, fb_H norm log < q <= 2 ^ log - 1 -> In q (map fst (fb_LW norm log))).
  { intros q Hq. apply wft_lw_cover. unfold fb_H, fb_LW in *. lia. }
  assert (Hh : -1 <= fb_H norm log <= 2 ^ log - 1) by (unfold fb_H in *; lia).
  assert (HL0r : forall p, In p (fb_L0 norm log) -> 0 <= p <= fb_H norm log /\ 0 <= p < 2 ^ log).
  { intros p Hp. unfold fb_L0, wft_LL in Hp. apply filter_In in Hp. destruct Hp as [Hp Hle].
    apply in_map_iff in Hp. destruct Hp as [j [<- _]]. pose proof (wft_gp_range log j). lia. }
  assert (HI : wft_inv log (fb_H norm log) (fb_L0 norm log) 0).
  { exists O%nat. split; [lia|]. split; [reflexivity|]. intros Hn.
    assert (wft_gp log 0 = 0) as G by (unfold wft_gp; simpl; apply Z.mod_0_l; lia).
    rewrite G. split; auto. destruct (fb_L0 norm log) as [|z l] eqn:EL; [congruence|].
    destruct (HL0r z) as [? _]; [left; auto|]. lia. }
  split.
  { unfold fse_build. rewrite wft_place_low_ok. cbv beta iota zeta. fold (fb_LW norm log).
    change (2 ^ log - 1 - Z.of_nat (length (fb_LW norm log))) with (fb_H norm log).
    rewrite (wft_spread_ok norm log (fb_H norm log) (length norm) 0 _ 0 (fb_L0 norm log)) by (auto; lia).
    rewrite <- apw_app. reflexivity. }
  assert (HpnC : map wft_pn (combine (fb_L0 norm log) (wft_syms norm 0 (length norm))) = map Z.to_nat (fb_L0 norm log)).
  { unfold wft_pn. rewrite <- (map_map fst Z.to_nat). rewrite wft_map_fst_combine; auto. }
  unfold fb_W. split.
  - intros p v Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp].
    + apply HLWin in Hp. destruct Hp as [H1 [i [Hi [Hv Hn]]]]. split; [lia|]. exists i. split; [lia|]. split; auto. lia.
    + pose proof (in_combine_l _ _ _ _ Hp) as H1. pose proof (in_combine_r _ _ _ _ Hp) as H2.
      apply HL0r in H1. apply wft_syms_in in H2. destruct H2 as [i [Hi [Hv Hn]]].
      split; [lia|]. exists i. split; [lia|]. split; auto. lia.
  - intros q Hq. rewrite map_app, HpnC. apply in_or_app.
    destruct (Z_le_gt_dec (Z.of_nat q) (fb_H norm log)).
    + right. apply in_map_iff. exists (Z.of_nat q). split; [lia|].
      unfold fb_L0, wft_LL. apply filter_In. split; [|lia]. rewrite Nat.sub_0_r. apply O2. lia.
    + left. assert (In (Z.of_nat q) (map fst (fb_LW norm log))) as Hc' by (apply HLWcov; lia).
      apply in_map_iff in Hc'. destruct Hc' as [[p v] [Hp Hin]]. simpl in Hp.
      apply in_map_iff. exists (p, v). split; auto. unfold wft_pn. simpl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the third loop: the states, one cell at a time *)
Fixpoint fb_nexts (tab: list Z) (next: list Z) : list Z :=
  match tab with
  | nil => next
  | s :: tab' => fb_nexts tab' (upd next (Z.to_nat s) (nth (Z.to_nat s) next 0 + 1))
  end.

Lemma fb_nexts_app : forall a b n, fb_nexts (a ++ b) n = fb_nexts b (fb_nexts a n).
Proof. induction a; simpl; auto. Qed.

Lemma fb_nexts_length : forall l n, length (fb_nexts l n) = length n.
Proof. induction l; simpl; intros; auto. rewrite IHl, wft_upd_length. auto. Qed.

Lemma fb_nexts_bounds : forall l n j,
  nth j n 0 <= nth j (fb_nexts l n) 0 <= nth j n 0 + Z.of_nat (length l).
Proof.
  induction l; simpl; intros; [lia|].
  specialize (IHl (upd n (Z.to_nat a) (nth (Z.to_nat a) n 0 + 1)) j).
  destruct (wft_nth_upd_cases n (Z.to_nat a) j (nth (Z.to_nat a) n 0 + 1)) as [E|[E1 E2]].
  - rewrite E in IHl. lia.
  - rewrite E2 in IHl. subst. lia.
Qed.

Lemma fb_firstn_snoc : forall (l: list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof. induction l; destruct k; simpl; intros; try lia; auto. f_equal. apply IHl. lia. Qed.

Lemma fb_nexts_snoc : forall tab n k, (k < length tab)%nat ->
  fb_nexts (firstn (S k) tab) n =
    let s := nth k tab 0 in
    upd (fb_nexts (firstn k tab) n) (Z.to_nat s) (nth (Z.to_nat s) (fb_nexts (firstn k tab) n) 0 + 1).
Proof. intros. rewrite fb_firstn_snoc, fb_nexts_app by auto. reflexivity. Qed.

Lemma fb_states_nth : forall log tab n k d, (k < length tab)%nat ->
  nth k (states log tab n) d =
    let s := nth k tab 0 in let x := nth (Z.to_nat s) (fb_nexts (firstn k tab) n) 0 in
    {| fe_sym := s; fe_nb := log - highbit x; fe_base := Z.shiftl x (log - highbit x) - 2 ^ log |}.
Proof.
  induction tab; simpl; intros; [lia|]. destruct k; simpl; auto. apply IHtab. lia.
Qed.

(* list updates as upd_Znth *)
Lemma fb_upd_eq : forall (l: list Z) i x, (i < length l)%nat -> upd l i x = upd_Znth (Z.of_nat i) l x.
Proof.
  intros. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_correct, wft_upd_length. auto.
  - intros j Hj. rewrite Zlength_correct, wft_upd_length in Hj.
    destruct (Z.eq_dec j (Z.of_nat i)).
    + subst. rewrite upd_Znth_same by (rewrite Zlength_correct; lia).
      rewrite <- nth_Znth' by (rewrite Zlength_correct, wft_upd_length; lia).
      rewrite ?Nat2Z.id. apply wft_nth_upd_same. auto.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_correct; lia).
      rewrite <- (Z2Nat.id j) by lia.
      rewrite <- !nth_Znth' by (rewrite ?Zlength_correct, ?wft_upd_length; lia).
      apply wft_nth_upd_other. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* machine arithmetic *)
Lemma fb_and_mask : forall a log, 0 <= a <= Int.max_unsigned -> 0 <= log < 32 ->
  Int.and (Int.repr a) (Int.repr (2 ^ log - 1)) = Int.repr (Z.land a (2 ^ log - 1)).
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr; auto.
  split; [lia|]. assert (2 ^ log <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  assert (2 ^ 32 = Int.max_unsigned + 1) by reflexivity. lia.
Qed.

Lemma fb_land_range : forall a log, 0 <= log -> 0 <= Z.land a (2 ^ log - 1) < 2 ^ log.
Proof.
  intros. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by auto. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma fb_shl1 : forall log, 0 <= log < 31 -> Int.shl (Int.repr 1) (Int.repr log) = Int.repr (2 ^ log).
Proof.
  intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. auto.
Qed.

Lemma fb_shru : forall a k, 0 <= a <= Int.max_unsigned -> 0 <= k < 32 ->
  Int.shru (Int.repr a) (Int.repr k) = Int.repr (Z.shiftr a k).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. auto. Qed.

Lemma fb_stp_range : forall log, 5 <= log <= 9 -> 0 <= wft_stp log <= 2 ^ log.
Proof.
  intros. unfold wft_stp. rewrite !Z.shiftr_div_pow2 by lia.
  assert (32 <= 2 ^ log) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
  change (2 ^ 1) with 2. change (2 ^ 3) with 8.
  pose proof (Z.div_le_upper_bound (2 ^ log) 2 (2 ^ log / 2)). split.
  - pose proof (Z.div_pos (2 ^ log) 2). pose proof (Z.div_pos (2 ^ log) 8). lia.
  - pose proof (Z.mul_div_le (2 ^ log) 2). pose proof (Z.mul_div_le (2 ^ log) 8). lia.
Qed.

(* Z-indexed forms for the loop invariants *)
Lemma fb_Znth_nth : forall (l: list Z) s, 0 <= s -> Znth s l = nth (Z.to_nat s) l 0.
Proof. intros. unfold Znth. destruct (Z_lt_dec s 0); [lia|auto]. Qed.

Lemma fb_lw_stepZ : forall norm s h, 0 <= s ->
  wft_lw norm 0 (Z.to_nat (s + 1)) h = wft_lw norm 0 (Z.to_nat s) h ++
    (if Znth s norm =? -1 then [(h - Z.of_nat (length (wft_lw norm 0 (Z.to_nat s) h)), s)] else nil).
Proof.
  intros. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite wft_lw_snoc. simpl (0 + _)%nat.
  rewrite Z2Nat.id by lia. rewrite fb_Znth_nth by lia. auto.
Qed.

Lemma fb_syms_stepZ : forall norm s, 0 <= s ->
  wft_syms norm 0 (Z.to_nat (s + 1)) = wft_syms norm 0 (Z.to_nat s) ++
    (if Znth s norm >? 0 then repeat s (Z.to_nat (Znth s norm)) else nil).
Proof.
  intros. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite wft_syms_snoc. simpl (0 + _)%nat.
  rewrite Z2Nat.id by lia. rewrite fb_Znth_nth by lia. auto.
Qed.

Lemma fb_next0_Znth : forall norm s, 0 <= s < Zlength norm ->
  Znth s (wft_next0 norm) = if Znth s norm =? -1 then 1 else Znth s norm.
Proof. intros. unfold wft_next0. rewrite Znth_map by auto. auto. Qed.

Lemma fb_next0_Zlength : forall norm, Zlength (wft_next0 norm) = Zlength norm.
Proof. intros. unfold wft_next0. apply Zlength_map. Qed.

Lemma fb_Znth_indep : forall {A} (d1 d2: Inhabitant A) (l: list A) i, 0 <= i < Zlength l ->
  @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros. unfold Znth. destruct (Z_lt_dec i 0); [lia|]. apply nth_indep. rewrite Zlength_correct in H. lia.
Qed.

Lemma fb_zext : forall n z, 0 <= n < 32 -> 0 <= z < 2 ^ n -> Int.zero_ext n (Int.repr z) = Int.repr z.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr; [rewrite two_p_equiv; lia|].
  assert (2 ^ n <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). rep_lia.
Qed.

Lemma fb_next_step : forall (f: Z -> val) (l: list Z) s x, 0 <= s < Zlength l -> Zlength l <= 53 -> Znth s l = x ->
  upd_Znth s (map f (sublist 0 s l) ++ Zrepeat Vundef (53 - s)) (f x) =
  map f (sublist 0 (s + 1) l) ++ Zrepeat Vundef (53 - (s + 1)).
Proof. intros. subst x. list_solve. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the second loop (spread), step by step *)
Lemma fb_inv0 : forall norm log, ndist_base log norm -> wft_inv log (fb_H norm log) (fb_L0 norm log) 0.
Proof.
  intros norm log Hnd. pose proof Hnd as [Hlog _].
  pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) ltac:(lia)) as Hpos.
  exists O%nat. split; [lia|]. split; [reflexivity|]. intros Hn.
  assert (wft_gp log 0 = 0) as G by (unfold wft_gp; simpl; apply Z.mod_0_l; lia).
  rewrite G. split; auto. destruct (fb_L0 norm log) as [|z l] eqn:EL; [congruence|].
  assert (In z (fb_L0 norm log)) as Hz by (rewrite EL; left; auto).
  unfold fb_L0, wft_LL in Hz. apply filter_In in Hz. destruct Hz as [Hp Hle].
  apply in_map_iff in Hp. destruct Hp as [j [<- _]]. pose proof (wft_gp_range log j). lia.
Qed.

Lemma fb_spread_step : forall norm log symv Sd s pos, ndist_base log norm ->
  (length Sd < length (fb_L0 norm log))%nat ->
  wft_inv log (fb_H norm log) (skipn (length Sd) (fb_L0 norm log)) pos ->
  exists j, (j < Z.to_nat (2 ^ log))%nat /\ pos = wft_gp log j /\ 0 <= wft_gp log j <= fb_H norm log /\
    skipn (S (length Sd)) (fb_L0 norm log) = wft_LL log (fb_H norm log) (S j) /\
    fbv symv (fb_LW norm log ++ combine (fb_L0 norm log) (Sd ++ [s])) =
      upd_Znth pos (fbv symv (fb_LW norm log ++ combine (fb_L0 norm log) Sd)) (Vint (Int.repr s)).
Proof.
  intros norm log symv Sd s pos Hnd Hl [j [Hj [HR HP]]]. pose proof Hnd as [Hlog _].
  set (L0 := fb_L0 norm log) in *. set (H := fb_H norm log) in *.
  assert (Hn : skipn (length Sd) L0 <> nil).
  { intro E. assert (length (skipn (length Sd) L0) = O) by (rewrite E; auto). rewrite skipn_length in H0. lia. }
  destruct (HP Hn) as [Hpos Hle].
  assert (Hj' : (j < Z.to_nat (2 ^ log))%nat).
  { destruct (Nat.eq_dec j (Z.to_nat (2 ^ log))); [|lia]. subst. rewrite wft_LL_N in HR. congruence. }
  rewrite wft_LL_cons in HR by auto. assert (wft_gp log j <=? H = true) as E by lia. rewrite E in HR.
  destruct (wft_skipn_cons L0 (length Sd) _ _ HR) as [Hnth Hsk].
  pose proof (wft_gp_range log j ltac:(lia)).
  exists j. split; auto. split; auto. split; [lia|]. split; auto.
  rewrite wft_combine_snoc by auto. rewrite app_assoc, fbv_snoc, Hnth, Hpos. reflexivity.
Qed.

Lemma fb_while_step : forall log high j, 0 <= log -> 0 <= high -> (j <= Z.to_nat (2 ^ log))%nat ->
  wft_gp log j > high -> (j < Z.to_nat (2 ^ log))%nat /\ wft_LL log high (S j) = wft_LL log high j.
Proof.
  intros. destruct (Nat.eq_dec j (Z.to_nat (2 ^ log))).
  - subst. rewrite wft_gp_size in H2 by auto. lia.
  - split; [lia|]. rewrite (wft_LL_cons log high j) by lia.
    assert (wft_gp log j <=? high = false) as E by lia. rewrite E. auto.
Qed.

Lemma fb_repeat_snoc : forall {A} (x: A) n, repeat x n ++ [x] = repeat x (S n).
Proof. induction n; simpl; auto. rewrite IHn. auto. Qed.

Lemma fb_syms_len : forall norm log s, ndist_base log norm -> 0 <= s <= Zlength norm ->
  (length (wft_syms norm 0 (Z.to_nat s)) <= length (fb_L0 norm log))%nat.
Proof.
  intros. rewrite fb_L0_length by auto. apply wft_syms_mono. rewrite Zlength_correct in H0. lia.
Qed.

Lemma fb_W_eq : forall norm log, fb_LW norm log ++ combine (fb_L0 norm log) (wft_syms norm 0 (Z.to_nat (Zlength norm))) = fb_W norm log.
Proof. intros. unfold fb_W. rewrite Zlength_correct, Nat2Z.id. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the third loop (states), step by step *)
Definition fb_C (norm: list Z) (log: Z) : list fse_entry := states log (fb_T norm log) (wft_next0 norm).

Lemma fb_T_Zlength : forall norm log, 0 <= log -> Zlength (fb_T norm log) = 2 ^ log.
Proof.
  intros. unfold fb_T. rewrite Zlength_correct, apw_length, repeat_length.
  rewrite Z2Nat.id; auto. pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) H). lia.
Qed.

Lemma fb_C_Zlength : forall norm log, 0 <= log -> Zlength (fb_C norm log) = 2 ^ log.
Proof.
  intros. unfold fb_C. rewrite Zlength_correct, wft_states_length, <- Zlength_correct. apply fb_T_Zlength; auto.
Qed.

Lemma fb_sym_final : forall norm log symv i, ndist_base log norm -> 2 ^ log <= Zlength symv ->
  0 <= i < 2 ^ log -> Znth i (fbv symv (fb_W norm log)) = Vint (Int.repr (Znth i (fb_T norm log))).
Proof.
  intros norm log symv i Hnd Hl Hi. pose proof Hnd as [Hlog _].
  destruct (fb_build_eq norm log Hnd) as [_ [HW HC]].
  rewrite (fbv_nth (fb_W norm log) symv (repeat 0 (Z.to_nat (2 ^ log))) i).
  - destruct (in_dec _ _ _) as [_|Hn]; [|exfalso; apply Hn, HC; lia].
    rewrite fb_Znth_nth by lia. reflexivity.
  - intros p v Hp. rewrite repeat_length. destruct (HW p v Hp). lia.
  - rewrite repeat_length. lia.
  - lia.
Qed.

Lemma fb_T_range : forall norm log i, ndist_base log norm -> 0 <= i < 2 ^ log ->
  0 <= Znth i (fb_T norm log) < Zlength norm /\
  1 <= Znth (Znth i (fb_T norm log)) (wft_next0 norm) <= 2 ^ log.
Proof.
  intros norm log i Hnd Hi. pose proof Hnd as [Hlog [Hlen [Hf Hsum]]].
  destruct (fb_build_eq norm log Hnd) as [_ [HW HC]].
  assert (Hs : In (nth (Z.to_nat i) (fb_T norm log) 0) (map snd (fb_W norm log))).
  { unfold fb_T. apply apw_some; [apply HC; lia | rewrite repeat_length; lia]. }
  rewrite fb_Znth_nth by lia.
  apply in_map_iff in Hs. destruct Hs as [[p v] [Hv Hin]]. simpl in Hv. rewrite <- Hv.
  destruct (HW p v Hin) as [_ [i0 [Hi0 [Hv0 Hn0]]]]. subst v.
  assert (Hb : -1 <= nth i0 norm 0 <= 2 ^ log).
  { rewrite Forall_forall in Hf. apply Hf. apply nth_In. auto. }
  split; [rewrite Zlength_correct; lia|].
  rewrite fb_next0_Znth by (rewrite Zlength_correct; lia). rewrite Hv0, fb_Znth_nth, Nat2Z.id by lia.
  destruct (nth i0 norm 0 =? -1) eqn:E; lia.
Qed.

#[local] Instance fb_inh_entry : Inhabitant fse_entry := {| fe_sym := 0; fe_nb := 0; fe_base := 0 |}.

Lemma fb_state_step : forall norm log k, ndist_base log norm -> 0 <= k < 2 ^ log ->
  let T := fb_T norm log in
  let sk := Znth k T in
  let nx := fb_nexts (firstn (Z.to_nat k) T) (wft_next0 norm) in
  let x := Znth sk nx in
  Zlength nx = Zlength norm /\ 0 <= sk < Zlength norm /\
  1 <= x < 2 ^ (log + 1) /\
  nth (Z.to_nat k) (fb_C norm log) fb_inh_entry =
    {| fe_sym := sk; fe_nb := log - Z.log2 x; fe_base := Z.shiftl x (log - Z.log2 x) - 2 ^ log |} /\
  fb_nexts (firstn (Z.to_nat (k + 1)) T) (wft_next0 norm) = upd_Znth sk nx (x + 1).
Proof.
  intros norm log k Hnd Hk T sk nx x. pose proof Hnd as [Hlog _].
  pose proof (fb_T_Zlength norm log ltac:(lia)) as HT. fold T in HT.
  destruct (fb_T_range norm log k Hnd Hk) as [Hs Hn]. fold T sk in Hs, Hn.
  assert (Hnx : Zlength nx = Zlength norm).
  { unfold nx. rewrite !Zlength_correct, fb_nexts_length. unfold wft_next0. rewrite map_length. auto. }
  assert (Hx : nth (Z.to_nat sk) (wft_next0 norm) 0 <= x <= nth (Z.to_nat sk) (wft_next0 norm) 0 + k).
  { unfold x. rewrite fb_Znth_nth by lia. pose proof (fb_nexts_bounds (firstn (Z.to_nat k) T) (wft_next0 norm) (Z.to_nat sk)).
    rewrite firstn_length in H. rewrite Zlength_correct in HT. fold nx in H. lia. }
  rewrite <- fb_Znth_nth in Hx by lia.
  assert (H2 : 2 ^ (log + 1) = 2 * 2 ^ log) by (rewrite Z.pow_add_r by lia; lia).
  split; auto. split; auto. split; [lia|]. split.
  - unfold fb_C. fold T. rewrite fb_states_nth by (rewrite Zlength_correct in HT; lia).
    rewrite <- fb_Znth_nth by lia. fold sk. unfold highbit. fold nx.
    replace (nth (Z.to_nat sk) nx 0) with x by (unfold x; rewrite fb_Znth_nth by lia; auto). reflexivity.
  - rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite fb_nexts_snoc by (rewrite Zlength_correct in HT; lia).
    cbv zeta. rewrite <- fb_Znth_nth by lia. fold sk. fold nx.
    replace (nth (Z.to_nat sk) nx 0) with x by (unfold x; rewrite fb_Znth_nth by lia; auto).
    rewrite fb_upd_eq by (rewrite Zlength_correct in Hnx; lia). rewrite Z2Nat.id by lia. auto.
Qed.

Lemma fb_cell_Znth : forall norm log i, 0 <= i ->
  fse_cell (fse_build norm log) i = nth (Z.to_nat i) (ft_cells (fse_build norm log)) fb_inh_entry.
Proof. reflexivity. Qed.

Lemma fb_shl : forall x n, 0 <= x -> 0 <= n < 32 -> Z.shiftl x n <= Int.max_unsigned ->
  Int.shl (Int.repr x) (Int.repr n) = Int.repr (Z.shiftl x n).
Proof.
  intros. unfold Int.shl. rewrite (Int.unsigned_repr n) by rep_lia.
  rewrite Int.unsigned_repr; auto. split; auto.
  rewrite Z.shiftl_mul_pow2 in H1 by lia. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma fb_map_Znth : forall (f: fse_entry -> Z) (l: list fse_entry) i, 0 <= i < Zlength l ->
  Znth i (map f l) = f (nth (Z.to_nat i) l fb_inh_entry).
Proof.
  intros. rewrite fb_Znth_nth by lia. rewrite Zlength_correct in H.
  rewrite nth_indep with (d' := f fb_inh_entry) by (rewrite map_length; lia). apply map_nth.
Qed.

Lemma fb_arr_step : forall (f: Z -> val) (l: list Z) (b: list val) i v,
  0 <= i < Zlength l -> Zlength l <= Zlength b -> Znth i l = v ->
  upd_Znth i (map f (sublist 0 i l) ++ sublist i (Zlength b) b) (f v) =
  map f (sublist 0 (i + 1) l) ++ sublist (i + 1) (Zlength b) b.
Proof. intros. subst v. list_solve. Qed.

Lemma fb_upd_app_map : forall (f: Z -> val) (l: list Z) (r: list val) i v, 0 <= i < Zlength l ->
  upd_Znth i (map f l ++ r) (f v) = map f (upd_Znth i l v) ++ r.
Proof. intros. rewrite upd_Znth_app1 by (rewrite Zlength_map; lia). rewrite upd_Znth_map. auto. Qed.

Lemma fb_C_sym : forall norm log i, 0 <= log -> 0 <= i < 2 ^ log ->
  fe_sym (nth (Z.to_nat i) (fb_C norm log) fb_inh_entry) = Znth i (fb_T norm log).
Proof.
  intros. pose proof (fb_T_Zlength norm log H). unfold fb_C.
  rewrite fb_states_nth by (rewrite Zlength_correct in H1; lia). simpl. rewrite fb_Znth_nth by lia. auto.
Qed.

Lemma fb_cell : forall norm log i, ndist_base log norm -> 0 <= i ->
  fse_cell (fse_build norm log) i = nth (Z.to_nat i) (fb_C norm log) fb_inh_entry.
Proof.
  intros. destruct (fb_build_eq norm log H) as [E _]. unfold fse_cell. rewrite E. reflexivity.
Qed.

Lemma fb_vals_def : forall (f: Z -> val) (l: list Z) (b: list val) lo hi,
  (forall z, exists i, f z = Vint i) -> Forall (fun v => exists i, v = Vint i) b ->
  Forall (fun v => exists i, v = Vint i) (map f l ++ sublist lo hi b).
Proof.
  intros. apply Forall_app. split.
  - apply Forall_map. apply Forall_forall. intros z _. destruct (H z) as [i Hi]. exists i. auto.
  - apply Forall_sublist. auto.
Qed.
