(* X2T model: counting and the C's counting sort (HufX2M.x2_count). *)
Require Import Zstd.proof.dec.B.huf.HufX2M.
Local Open Scope Z_scope.

(* ---------- generic list facts ---------- *)

Ltac zb := repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b)
  | H: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b)
  | H: context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b)
  end; simpl in *; try discriminate; try lia; auto.

Lemma x2c_fmax_ge : forall l x, In x l -> x <= fold_right Z.max 0 l.
Proof.
  induction l; simpl; intros x H; [contradiction|].
  destruct H as [<-|H]; [lia|]. specialize (IHl _ H); lia.
Qed.

Lemma x2c_fmax_in : forall l, fold_right Z.max 0 l = 0 \/ In (fold_right Z.max 0 l) l.
Proof.
  induction l; simpl; [auto|].
  destruct (Z.max_spec a (fold_right Z.max 0 l)) as [[_ E]|[_ E]]; rewrite E; [|auto].
  destruct IHl; auto.
Qed.

Lemma x2c_fmax_le : forall l b, 0 <= b -> Forall (fun x => x <= b) l -> fold_right Z.max 0 l <= b.
Proof.
  induction l; simpl; intros b Hb H; [lia|]. apply Forall_cons_iff in H as [H1 H2]. specialize (IHl b Hb H2); lia.
Qed.

Lemma x2c_sum_app1 : forall l x, fold_right Z.add 0 (l ++ [x]) = fold_right Z.add 0 l + x.
Proof. intros l x; induction l; simpl; [lia|]. rewrite IHl; lia. Qed.

Lemma x2c_cnt_or : forall (p q: Z -> bool) l, (forall x, In x l -> p x = true -> q x = false) ->
  Zlength (filter (fun x => orb (p x) (q x)) l) = Zlength (filter p l) + Zlength (filter q l).
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  assert (IH' := IH (fun x Hx => H x (or_intror Hx))).
  specialize (H a (or_introl eq_refl)). simpl.
  destruct (p a), (q a); simpl; rewrite ?Zlength_cons, IH'; try lia; discriminate H; auto.
Qed.

Lemma x2c_filter_all : forall (p: Z -> bool) l, (forall x, In x l -> p x = true) -> filter p l = l.
Proof.
  induction l; simpl; intros H; [reflexivity|]. rewrite H by auto. rewrite IHl by auto. reflexivity.
Qed.

Lemma x2c_filter_none : forall (p: Z -> bool) l, (forall x, In x l -> p x = false) -> filter p l = [].
Proof.
  induction l; simpl; intros H; [reflexivity|]. rewrite H by auto. apply IHl; auto.
Qed.

Lemma x2c_map_nth_seq : forall (l: list Z), map (fun k => nth k l 0) (seq 0 (length l)) = l.
Proof.
  induction l; simpl; [reflexivity|]. f_equal. rewrite <- seq_shift, map_map. simpl. exact IHl.
Qed.

(* ---------- counting ---------- *)

Definition cntup (ht: huf_table) (k: nat) (w: Z) : Z :=
  Zlength (filter (fun s' => hw ht s' =? w) (map Z.of_nat (seq 0 k))).

Lemma cntup_S : forall ht k w,
  cntup ht (S k) w = cntup ht k w + (if hw ht (Z.of_nat k) =? w then 1 else 0).
Proof.
  intros. unfold cntup. rewrite seq_S, map_app, filter_app, Zlength_app. simpl.
  destruct (hw ht (Z.of_nat k) =? w); reflexivity.
Qed.

Lemma cntup_mono : forall ht j d w, cntup ht j w <= cntup ht (j + d) w.
Proof.
  induction d; intros; [rewrite Nat.add_0_r; lia|].
  rewrite Nat.add_succ_r, cntup_S. specialize (IHd w). destruct (_ =? _); lia.
Qed.

Lemma x2c_cnt_map : forall ht w (l: list nat),
  Zlength (filter (fun s => hw ht s =? w) (map Z.of_nat l)) =
  Zlength (filter (fun x => x =? w) (map (fun k => nth k (ht_weights ht) 0) l)).
Proof.
  induction l; simpl; [reflexivity|].
  unfold hw at 1. rewrite Nat2Z.id.
  destruct (nth a (ht_weights ht) 0 =? w); rewrite ?Zlength_cons; lia.
Qed.

Lemma cntup_full : forall ht w, cntup ht (length (ht_weights ht)) w = cntw ht w.
Proof.
  intros. unfold cntup, cntw. rewrite x2c_cnt_map, x2c_map_nth_seq. reflexivity.
Qed.

Lemma Zlength_symsw : forall ht w, Zlength (symsw ht w) = cntw ht w.
Proof. intros. apply cntup_full. Qed.

Lemma cntw_nonneg : forall ht w, 0 <= cntw ht w.
Proof. intros. apply Zlength_nonneg. Qed.

(* ---------- rstart ---------- *)

Lemma wbelow_S : forall w, 1 <= w -> wbelow (w + 1) = wbelow w ++ [w].
Proof.
  intros. unfold wbelow.
  replace (Z.to_nat (w + 1 - 1)) with (S (Z.to_nat (w - 1))) by lia.
  rewrite seq_S, map_app. simpl. f_equal. f_equal. f_equal. lia.
Qed.

Lemma rstart_1 : forall ht, rstart ht 1 = 0.
Proof. reflexivity. Qed.

Lemma rstart_S : forall ht w, 1 <= w -> rstart ht (w + 1) = rstart ht w + cntw ht w.
Proof.
  intros. unfold rstart. rewrite wbelow_S, map_app by lia. simpl map. apply x2c_sum_app1.
Qed.

Lemma rstart_formula : forall ht w, 1 <= w ->
  rstart ht w = Zlength (filter (fun x => andb (1 <=? x) (x <? w)) (ht_weights ht)).
Proof.
  intros ht w Hw.
  replace w with (1 + Z.of_nat (Z.to_nat (w - 1))) by lia.
  induction (Z.to_nat (w - 1)) as [|k IH].
  - change (1 + Z.of_nat 0) with 1. rewrite rstart_1, x2c_filter_none; [reflexivity|]. intros. zb.
  - replace (1 + Z.of_nat (S k)) with ((1 + Z.of_nat k) + 1) by lia.
    rewrite rstart_S, IH by lia. unfold cntw.
    rewrite <- x2c_cnt_or.
    + f_equal. apply filter_ext_in. intros. zb.
    + intros. zb.
Qed.

Lemma rstart_nonneg : forall ht w, 1 <= w -> 0 <= rstart ht w.
Proof. intros. rewrite rstart_formula by auto. apply Zlength_nonneg. Qed.

Lemma rstart_mono : forall ht a b, 1 <= a <= b -> rstart ht a <= rstart ht b.
Proof.
  intros ht a b H.
  replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  induction (Z.to_nat (b - a)) as [|k IH]; [rewrite Nat2Z.inj_0, Z.add_0_r; lia|].
  replace (a + Z.of_nat (S k)) with ((a + Z.of_nat k) + 1) by lia.
  rewrite rstart_S by lia. pose proof (cntw_nonneg ht (a + Z.of_nat k)). lia.
Qed.

Lemma Zlength_flat_symsw : forall ht l,
  Zlength (flat_map (symsw ht) l) = fold_right Z.add 0 (map (cntw ht) l).
Proof.
  induction l; simpl; [reflexivity|]. rewrite Zlength_app, Zlength_symsw, IHl. reflexivity.
Qed.

Lemma Zlength_sorted_syms : forall ht, Zlength (sorted_syms ht) = rstart ht (maxw ht + 1).
Proof. intros. apply Zlength_flat_symsw. Qed.

(* ---------- the facts on weights ---------- *)

Lemma x2c_weights_le : forall ht, x2_ht_ok ht -> Forall (fun x => 0 <= x <= maxw ht) (ht_weights ht).
Proof.
  intros ht (_ & _ & HF). rewrite Forall_forall in HF. apply Forall_forall. intros x Hx.
  specialize (HF x Hx). split; [lia|apply x2c_fmax_ge; auto].
Qed.

Lemma x2c_hw_in : forall ht s, 0 <= s < Zlength (ht_weights ht) -> In (hw ht s) (ht_weights ht).
Proof.
  intros. unfold hw. apply nth_In. rewrite Zlength_correct in H. lia.
Qed.

Lemma x2c_maxw_pos : forall ht, x2_ht_ok ht -> 1 <= maxw ht.
Proof.
  intros ht ((HT & HL & _) & _ & _).
  assert (0 < 2 ^ ht_log ht) by (apply Z.pow_pos_nonneg; lia).
  assert (Hne: exists c, In c (huf_cells ht)).
  { destruct (huf_cells ht) as [|c l]; [rewrite Zlength_nil in HL; lia | exists c; left; auto]. }
  destruct Hne as [c Hc]. unfold huf_cells in Hc.
  apply in_flat_map in Hc as [w [Hw Hc]]. apply in_flat_map in Hc as [s [Hs Hc]].
  destruct (nth s (ht_weights ht) 0 =? w) eqn:E; [|contradiction]. apply Z.eqb_eq in E.
  apply in_map_iff in Hw as [k [<- Hk]]. apply in_seq in Hk. apply in_seq in Hs.
  assert (In (nth s (ht_weights ht) 0) (ht_weights ht)) by (apply nth_In; lia).
  pose proof (x2c_fmax_ge _ _ H0). unfold maxw. lia.
Qed.

Lemma x2c_maxw_le : forall ht, x2_ht_ok ht -> maxw ht <= ht_log ht.
Proof.
  intros ht ((HT & _) & _ & HF). apply x2c_fmax_le; [lia|].
  eapply Forall_impl; [|exact HF]. simpl. intros; lia.
Qed.

Lemma x2c_cntw_maxw : forall ht, x2_ht_ok ht -> 0 < cntw ht (maxw ht).
Proof.
  intros ht H. pose proof (x2c_maxw_pos ht H).
  destruct (x2c_fmax_in (ht_weights ht)) as [E|Hin]; [unfold maxw in *; lia|].
  assert (Hf: In (maxw ht) (filter (fun x => x =? maxw ht) (ht_weights ht)))
    by (apply filter_In; split; [exact Hin|apply Z.eqb_refl]).
  unfold cntw. destruct (filter _ _) as [|a l]; [contradiction|].
  rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma x2c_cntw_above : forall ht w, x2_ht_ok ht -> maxw ht < w -> cntw ht w = 0.
Proof.
  intros ht w H Hw. pose proof (x2c_weights_le ht H) as HF. rewrite Forall_forall in HF.
  unfold cntw. rewrite x2c_filter_none; [reflexivity|]. intros x Hx. specialize (HF x Hx). zb.
Qed.

Lemma x2c_total : forall ht, x2_ht_ok ht -> rstart ht (maxw ht + 1) + cntw ht 0 = Zlength (ht_weights ht).
Proof.
  intros ht H. pose proof (x2c_maxw_pos ht H). pose proof (x2c_weights_le ht H) as HF.
  rewrite Forall_forall in HF.
  rewrite rstart_formula by lia. unfold cntw. rewrite <- x2c_cnt_or by (intros; zb).
  rewrite x2c_filter_all; [reflexivity|]. intros x Hx. specialize (HF x Hx). zb.
Qed.

Lemma x2c_len : forall ht, x2_ht_ok ht -> Zlength (ht_weights ht) = Z.of_nat (length (ht_weights ht)).
Proof. intros. apply Zlength_correct. Qed.

(* the start of the C's block of weight w (weight 0 last) *)
Definition x2c_base (ht: huf_table) (w: Z) : Z :=
  if w =? 0 then rstart ht (maxw ht + 1) else rstart ht w.

Lemma sort_pos_eq : forall ht s, sort_pos ht s = x2c_base ht (hw ht s) + cntup ht (Z.to_nat s) (hw ht s).
Proof. reflexivity. Qed.

Lemma x2c_hw_range : forall ht s, x2_ht_ok ht -> 0 <= s < Zlength (ht_weights ht) -> 0 <= hw ht s <= maxw ht.
Proof.
  intros. pose proof (x2c_weights_le ht H) as HF. rewrite Forall_forall in HF.
  apply HF, x2c_hw_in; auto.
Qed.

Lemma x2c_cntup_lt : forall ht s, 0 <= s < Zlength (ht_weights ht) ->
  cntup ht (Z.to_nat s) (hw ht s) + 1 <= cntw ht (hw ht s).
Proof.
  intros ht s Hs. rewrite Zlength_correct in Hs.
  rewrite <- cntup_full.
  replace (length (ht_weights ht)) with (S (Z.to_nat s) + (length (ht_weights ht) - S (Z.to_nat s)))%nat by lia.
  eapply Z.le_trans; [|apply cntup_mono].
  rewrite cntup_S, Z2Nat.id, Z.eqb_refl by lia. lia.
Qed.

Lemma x2c_block : forall ht w, x2_ht_ok ht -> 0 <= w <= maxw ht ->
  0 <= x2c_base ht w /\ x2c_base ht w + cntw ht w <= Zlength (ht_weights ht).
Proof.
  intros ht w H Hw. pose proof (x2c_maxw_pos ht H). pose proof (x2c_total ht H).
  pose proof (cntw_nonneg ht 0).
  unfold x2c_base. destruct (Z.eqb_spec w 0).
  - subst. pose proof (rstart_nonneg ht (maxw ht + 1)). lia.
  - pose proof (rstart_nonneg ht w). rewrite <- rstart_S by lia.
    pose proof (rstart_mono ht (w + 1) (maxw ht + 1)). lia.
Qed.

Lemma x2c_blocks_disj : forall ht a b, x2_ht_ok ht -> 0 <= a <= maxw ht -> 0 <= b <= maxw ht -> a <> b ->
  x2c_base ht a + cntw ht a <= x2c_base ht b \/ x2c_base ht b + cntw ht b <= x2c_base ht a.
Proof.
  intros ht a b H Ha Hb Hab. pose proof (x2c_maxw_pos ht H).
  unfold x2c_base. destruct (Z.eqb_spec a 0), (Z.eqb_spec b 0); [lia| | |].
  - right. rewrite <- rstart_S by lia. apply rstart_mono; lia.
  - left. rewrite <- rstart_S by lia. apply rstart_mono; lia.
  - destruct (Z.lt_ge_cases a b); [left|right]; rewrite <- rstart_S by lia; apply rstart_mono; lia.
Qed.

Lemma x2c_sort_pos_range : forall ht s, x2_ht_ok ht -> 0 <= s < Zlength (ht_weights ht) ->
  x2c_base ht (hw ht s) <= sort_pos ht s < x2c_base ht (hw ht s) + cntw ht (hw ht s) /\
  0 <= sort_pos ht s < Zlength (ht_weights ht).
Proof.
  intros ht s H Hs. rewrite sort_pos_eq.
  pose proof (x2c_cntup_lt ht s Hs). pose proof (x2c_block ht (hw ht s) H (x2c_hw_range ht s H Hs)).
  assert (0 <= cntup ht (Z.to_nat s) (hw ht s)) by apply Zlength_nonneg. lia.
Qed.

Lemma x2c_sort_pos_inj : forall ht s t, x2_ht_ok ht -> 0 <= s < Zlength (ht_weights ht) ->
  0 <= t < Zlength (ht_weights ht) -> s <> t -> sort_pos ht s <> sort_pos ht t.
Proof.
  intros ht s t H Hs Ht Hst.
  destruct (Z.eq_dec (hw ht s) (hw ht t)) as [E|E].
  - rewrite !sort_pos_eq, <- E.
    assert (forall a b, 0 <= a < b -> cntup ht (Z.to_nat a) (hw ht a) < cntup ht (Z.to_nat b) (hw ht a)).
    { intros a b Hab.
      replace (Z.to_nat b) with (S (Z.to_nat a) + (Z.to_nat b - S (Z.to_nat a)))%nat by lia.
      eapply Z.lt_le_trans; [|apply cntup_mono]. rewrite cntup_S, Z2Nat.id, Z.eqb_refl by lia. lia. }
    destruct (Z.lt_ge_cases s t).
    + specialize (H0 s t ltac:(lia)). lia.
    + specialize (H0 t s ltac:(lia)). rewrite <- E in H0. lia.
  - pose proof (x2c_sort_pos_range ht s H Hs). pose proof (x2c_sort_pos_range ht t H Ht).
    pose proof (x2c_blocks_disj ht _ _ H (x2c_hw_range ht s H Hs) (x2c_hw_range ht t H Ht) E). lia.
Qed.

Lemma sort_arr_S : forall ht k a0, sort_arr ht (S k) a0 =
  upd_Znth (sort_pos ht (Z.of_nat k)) (sort_arr ht k a0) (Vint (Int.repr (Z.of_nat k))).
Proof. intros. unfold sort_arr. rewrite seq_S, fold_left_app. reflexivity. Qed.

Lemma sort_arr_len : forall ht k a0, Zlength (sort_arr ht k a0) = Zlength a0.
Proof.
  induction k; intros; [reflexivity|]. rewrite sort_arr_S, Zlength_upd_Znth. apply IHk.
Qed.

Lemma sort_arr_inv : forall ht a0, x2_ht_ok ht -> Zlength a0 = 256 -> forall k,
  (k <= length (ht_weights ht))%nat -> forall s, 0 <= s < Z.of_nat k ->
  Znth (sort_pos ht s) (sort_arr ht k a0) = Vint (Int.repr s).
Proof.
  intros ht a0 H Ha k. pose proof H as (_ & HL & _). rewrite Zlength_correct in HL.
  induction k as [|k IH]; intros Hk s Hs; [lia|].
  rewrite sort_arr_S.
  assert (Hr: forall t, 0 <= t < Z.of_nat (length (ht_weights ht)) ->
    0 <= sort_pos ht t < Zlength (sort_arr ht k a0)).
  { intros t Ht. rewrite sort_arr_len. pose proof (x2c_sort_pos_range ht t H).
    rewrite Zlength_correct in H0. specialize (H0 Ht). lia. }
  destruct (Z.eq_dec s (Z.of_nat k)) as [->|E].
  - apply upd_Znth_same. apply Hr. lia.
  - rewrite upd_Znth_diff by (try apply Hr; try lia;
      apply x2c_sort_pos_inj; rewrite ?Zlength_correct; auto; lia).
    apply IH; lia.
Qed.

Lemma x2c_filter_idx : forall (p: Z -> bool) n k, 0 <= k < Zlength (filter p (map Z.of_nat (seq 0 n))) ->
  0 <= Znth k (filter p (map Z.of_nat (seq 0 n))) < Z.of_nat n /\
  p (Znth k (filter p (map Z.of_nat (seq 0 n)))) = true /\
  Zlength (filter p (map Z.of_nat (seq 0 (Z.to_nat (Znth k (filter p (map Z.of_nat (seq 0 n)))))))) = k.
Proof.
  intros p n k Hk.
  set (f := filter p (map Z.of_nat (seq 0 n))) in *.
  assert (Hin: In (Znth k f) f) by (apply Znth_In; auto).
  set (s := Znth k f) in *.
  pose proof Hin as Hin'. apply filter_In in Hin' as [Hm Hp].
  apply in_map_iff in Hm as [j [Hj Hj']]. apply in_seq in Hj'.
  assert (Hsplit: f = filter p (map Z.of_nat (seq 0 j)) ++ s :: filter p (map Z.of_nat (seq (S j) (n - S j)))).
  { unfold f. replace n with (j + S (n - S j))%nat at 1 by lia.
    rewrite seq_app. simpl. rewrite map_app, filter_app. simpl. rewrite Hj, Hp. reflexivity. }
  assert (Hnd: NoDup f).
  { apply NoDup_filter, FinFun.Injective_map_NoDup; [intros ? ? ?; lia|apply seq_NoDup]. }
  set (A := filter p (map Z.of_nat (seq 0 j))) in *.
  assert (Znth (Zlength A) f = s).
  { rewrite Hsplit, Znth_app2 by lia. rewrite Z.sub_diag. reflexivity. }
  assert (Zlength A = k).
  { apply (NoDup_Znth_inj f); auto.
    rewrite Hsplit, Zlength_app, Zlength_cons. pose proof (Zlength_nonneg A).
    pose proof (Zlength_nonneg (filter p (map Z.of_nat (seq (S j) (n - S j))))). lia. }
  subst s. rewrite <- Hj, Nat2Z.id. split; [lia|]. split; [congruence|auto].
Qed.

Lemma x2c_symsw_slice : forall ht w, x2_ht_ok ht -> 1 <= w <= maxw ht ->
  sublist (rstart ht w) (rstart ht (w + 1)) (sorted_syms ht) = symsw ht w.
Proof.
  intros ht w H Hw.
  assert (E: wbelow (maxw ht + 1) = wbelow w ++ [w] ++ map Z.of_nat (seq (1 + Z.to_nat w) (Z.to_nat (maxw ht - w)))).
  { rewrite app_assoc, <- wbelow_S by lia. unfold wbelow. rewrite <- map_app.
    replace (Z.to_nat (w + 1 - 1)) with (Z.to_nat w) by lia. rewrite <- seq_app.
    f_equal. f_equal. lia. }
  unfold sorted_syms. rewrite E, !flat_map_app. simpl flat_map at 2. rewrite app_nil_r.
  rewrite rstart_S by lia.
  assert (Zlength (flat_map (symsw ht) (wbelow w)) = rstart ht w) by apply Zlength_flat_symsw.
  rewrite sublist_app2 by (pose proof (Zlength_nonneg (flat_map (symsw ht) (wbelow w))); lia).
  rewrite sublist_app1 by (rewrite ?Zlength_symsw; pose proof (cntw_nonneg ht w); lia).
  apply sublist_same; rewrite ?Zlength_symsw; lia.
Qed.

Lemma x2_count_ok : x2_count.
Proof.
  constructor.
  - intros ht H. split; [split; [apply x2c_maxw_pos|apply x2c_maxw_le]; auto|].
    split; [apply x2c_cntw_maxw; auto|]. split; [intros; apply x2c_cntw_above; auto|].
    intros w Hw.
    assert (w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/
            w = 10 \/ w = 11 \/ w = 12) by lia.
    repeat destruct H0 as [->|H0]; try (subst; reflexivity).
  - intros ht w H Hw. split; [apply Zlength_symsw|]. split.
    + apply Forall_forall. intros s Hs. unfold symsw in Hs. apply filter_In in Hs as [Hs _].
      unfold hsyms in Hs. apply in_map_iff in Hs as [k [<- Hk]]. apply in_seq in Hk.
      pose proof H as (_ & HL & _). rewrite Zlength_correct in HL. lia.
    + apply x2c_symsw_slice; auto.
  - intros ht w H Hw. split; [apply rstart_1|]. split; [apply rstart_S; auto|].
    split; [apply Zlength_sorted_syms|apply x2c_total; auto].
  - intros ht s H Hs. apply x2c_sort_pos_range; auto.
  - intros ht a0 i H Ha Hi.
    pose proof (x2c_maxw_pos ht H).
    (* the weight w of index i *)
    assert (Hw: exists w, 1 <= w <= maxw ht /\ rstart ht w <= i < rstart ht (w + 1)).
    { assert (Hk: forall k, i < rstart ht (1 + Z.of_nat k) ->
                exists w, 1 <= w <= Z.of_nat k /\ rstart ht w <= i < rstart ht (w + 1)).
      { induction k as [|k IH]; intros Hik.
        - rewrite Nat2Z.inj_0, Z.add_0_r, rstart_1 in Hik. lia.
        - destruct (Z_lt_le_dec i (rstart ht (1 + Z.of_nat k))) as [Hl|Hl].
          + destruct (IH Hl) as [w Hw]. exists w. lia.
          + exists (1 + Z.of_nat k). replace (1 + Z.of_nat (S k)) with (1 + Z.of_nat k + 1) in Hik by lia.
            lia. }
      destruct (Hk (Z.to_nat (maxw ht))) as [w Hw]; [rewrite Z2Nat.id, Z.add_comm by lia; lia|].
      exists w. rewrite Z2Nat.id in Hw by lia. exact Hw. }
    destruct Hw as [w [Hw Hiw]].
    pose proof (rstart_nonneg ht w ltac:(lia)).
    rewrite rstart_S in Hiw by lia.
    assert (Hsi: Znth i (sorted_syms ht) = Znth (i - rstart ht w) (symsw ht w)).
    { rewrite <- (x2c_symsw_slice ht w H Hw), Znth_sublist by (rewrite ?rstart_S; lia).
      f_equal; lia. }
    destruct (x2c_filter_idx (fun s => hw ht s =? w) (length (ht_weights ht)) (i - rstart ht w))
      as (Hs & Hp & Hc).
    { change (filter _ _) with (symsw ht w). rewrite Zlength_symsw. lia. }
    change (filter (fun s => hw ht s =? w) (map Z.of_nat (seq 0 (length (ht_weights ht)))))
      with (symsw ht w) in *.
    set (s := Znth (i - rstart ht w) (symsw ht w)) in *.
    apply Z.eqb_eq in Hp.
    assert (Hpos: sort_pos ht s = i).
    { rewrite sort_pos_eq, Hp. unfold cntup. rewrite Hc. unfold x2c_base.
      destruct (Z.eqb_spec w 0); lia. }
    rewrite Hsi, <- Hpos. apply sort_arr_inv; auto; lia.
Qed.
