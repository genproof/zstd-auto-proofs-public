(* X2T model: the canonical layout in an L-table (HufX2M.x2_layout). *)
Require Import Zstd.proof.dec.B.huf.HufX2M.
Local Open Scope Z_scope.

(* ---------- helpers ---------- *)

(* the cells of the symbols of weight w *)
Definition xl_blk (ht: huf_table) (w: Z) : list (Z * Z) :=
  flat_map (fun s => repeat (s, ht_log ht + 1 - w) (Z.to_nat (2 ^ (w - 1)))) (symsw ht w).

(* the number of cells of the weights below w *)
Definition xl_pre (ht: huf_table) (w: Z) : Z :=
  fold_right Z.add 0 (map (fun w' => cntw ht w' * 2 ^ (w' - 1)) (wbelow w)).

Lemma xl_fold_add_app (l1 l2: list Z) :
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1; simpl; lia. Qed.

Lemma xl_wbelow_S (w: Z) : 1 <= w -> wbelow (w + 1) = wbelow w ++ [w].
Proof.
  intros Hw. unfold wbelow.
  replace (Z.to_nat (w + 1 - 1)) with (S (Z.to_nat (w - 1))) by lia.
  rewrite seq_S, map_app. simpl. f_equal. f_equal. lia.
Qed.

Lemma xl_wbelow_split (w T: Z) : 1 <= w <= T + 1 ->
  wbelow (T + 1) = wbelow w ++ map Z.of_nat (seq (Z.to_nat w) (Z.to_nat (T + 1 - w))).
Proof.
  intros Hw. unfold wbelow.
  replace (Z.to_nat (T + 1 - 1)) with (Z.to_nat (w - 1) + Z.to_nat (T + 1 - w))%nat by lia.
  rewrite seq_app, map_app. f_equal. f_equal. f_equal. lia.
Qed.

Lemma xl_rv0_S (ht: huf_table) (L w: Z) : 1 <= w ->
  rv0 ht L (w + 1) = rv0 ht L w + cntw ht w * 2 ^ (L - nbw ht w).
Proof.
  intros Hw. unfold rv0 at 1. rewrite xl_wbelow_S by lia. rewrite map_app, xl_fold_add_app. simpl.
  unfold rv0. lia.
Qed.

Lemma xl_pre_S (ht: huf_table) (w: Z) : 1 <= w ->
  xl_pre ht (w + 1) = xl_pre ht w + cntw ht w * 2 ^ (w - 1).
Proof.
  intros Hw. unfold xl_pre at 1. rewrite xl_wbelow_S by lia. rewrite map_app, xl_fold_add_app. simpl.
  unfold xl_pre. lia.
Qed.

Lemma xl_rv0_pre (ht: huf_table) (L w: Z) : ht_log ht <= L -> 1 <= w ->
  rv0 ht L w = 2 ^ (L - ht_log ht) * xl_pre ht w.
Proof.
  intros HL Hw. replace w with (1 + Z.of_nat (Z.to_nat (w - 1))) by lia.
  induction (Z.to_nat (w - 1)) as [|n IH].
  - unfold rv0, xl_pre, wbelow. simpl. lia.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc.
    rewrite xl_rv0_S, xl_pre_S, IH by lia. unfold nbw.
    replace (L - (ht_log ht + 1 - (1 + Z.of_nat n))) with ((L - ht_log ht) + (1 + Z.of_nat n - 1)) by lia.
    rewrite Z.pow_add_r by lia. ring.
Qed.

Lemma xl_filter_if {A B: Type} (f: A -> bool) (g: A -> list B) (l: list A) :
  flat_map (fun x => if f x then g x else nil) l = flat_map g (filter f l).
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. destruct (f a); simpl; rewrite IH; reflexivity. Qed.

Lemma xl_flat_map_map {A B C: Type} (f: B -> list C) (g: A -> B) (l: list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH; reflexivity. Qed.

Lemma xl_cells (ht: huf_table) : huf_cells ht = flat_map (xl_blk ht) (wbelow (ht_log ht + 1)).
Proof.
  unfold huf_cells, wbelow. rewrite Z.add_simpl_r. apply flat_map_ext. intros w.
  unfold xl_blk, symsw, hsyms. rewrite <- xl_filter_if, xl_flat_map_map. apply flat_map_ext. intros s.
  unfold hw. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma xl_filter_map {A B: Type} (f: B -> bool) (g: A -> B) (l: list A) :
  length (filter (fun x => f (g x)) l) = length (filter f (map g l)).
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. destruct (f (g a)); simpl; rewrite IH; reflexivity. Qed.

Lemma xl_map_nth_seq (l: list Z) : map (fun i => nth i l 0) (seq 0 (length l)) = l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. simpl. f_equal. rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma xl_symsw_len (ht: huf_table) (w: Z) : Zlength (symsw ht w) = cntw ht w.
Proof.
  unfold symsw, cntw, hsyms. rewrite !Zlength_correct. f_equal.
  rewrite <- (xl_filter_map (fun s => hw ht s =? w) Z.of_nat).
  rewrite <- (xl_map_nth_seq (ht_weights ht)) at 2.
  rewrite <- (xl_filter_map (fun x => x =? w) (fun i => nth i (ht_weights ht) 0)).
  f_equal. apply filter_ext. intros x. unfold hw. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma xl_len_fm_rep {A: Type} (l: list A) (c: Z) (m: nat) :
  length (flat_map (fun s => repeat (s, c) m) l) = (length l * m)%nat.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite app_length, repeat_length, IH. lia. Qed.

Lemma xl_nth_fm_rep {A: Type} (l: list A) (c: Z) (m kn i: nat) (a0: A) (d: A * Z) :
  (kn < length l)%nat -> (i < m)%nat ->
  nth (kn * m + i) (flat_map (fun s => repeat (s, c) m) l) d = (nth kn l a0, c).
Proof.
  revert kn. induction l as [|a l IH]; intros kn Hk Hi; simpl in *; [lia|].
  destruct kn as [|kn].
  - simpl. rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_lt. exact Hi.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
    replace (S kn * m + i - m)%nat with (kn * m + i)%nat by lia. apply IH; lia.
Qed.

Lemma xl_blk_len (ht: huf_table) (w: Z) : Zlength (xl_blk ht w) = cntw ht w * 2 ^ (w - 1).
Proof.
  unfold xl_blk. rewrite Zlength_correct, xl_len_fm_rep, Nat2Z.inj_mul, <- Zlength_correct, xl_symsw_len.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.pow_nonneg. lia.
Qed.

Lemma xl_len_fm (ht: huf_table) (l: list Z) :
  Zlength (flat_map (xl_blk ht) l) = fold_right Z.add 0 (map (fun w' => cntw ht w' * 2 ^ (w' - 1)) l).
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|]. rewrite Zlength_app, IH, xl_blk_len. reflexivity.
Qed.

Lemma xl_maxw_ge (l: list Z) (x: Z) : In x l -> x <= fold_right Z.max 0 l.
Proof. induction l as [|a l IH]; simpl; [tauto|]. intros [<-|H]; [lia|]. specialize (IH H). lia. Qed.

Lemma xl_maxw_le (l: list Z) (T: Z) : 0 <= T -> Forall (fun w => 0 <= w <= T) l -> 0 <= fold_right Z.max 0 l <= T.
Proof. intros HT H. induction H; simpl; lia. Qed.

Lemma xl_filter_none (l: list Z) (w: Z) : (forall x, In x l -> x < w) -> filter (fun x => x =? w) l = nil.
Proof.
  induction l as [|a l IH]; intros H; simpl; [reflexivity|].
  assert (a < w) by (apply H; left; reflexivity).
  destruct (Z.eqb_spec a w); [lia|]. apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma xl_cntw_0 (ht: huf_table) (w: Z) : maxw ht < w -> cntw ht w = 0.
Proof.
  intros Hw. unfold cntw. rewrite xl_filter_none; [reflexivity|].
  intros x Hx. apply xl_maxw_ge in Hx. unfold maxw in Hw. lia.
Qed.

Lemma xl_pre_flat (ht: huf_table) (n: nat) (w: Z) : 1 <= w -> maxw ht < w -> xl_pre ht (w + Z.of_nat n) = xl_pre ht w.
Proof.
  intros H1 Hw. induction n as [|n IH].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc, xl_pre_S by lia.
    rewrite IH, xl_cntw_0 by lia. lia.
Qed.

Lemma xl_pre_div (ht: huf_table) (n: nat) (w: Z) : 1 <= w -> (2 ^ (w - 1) | xl_pre ht (w + Z.of_nat n) - xl_pre ht w).
Proof.
  intros Hw. induction n as [|n IH].
  - rewrite Z.add_0_r, Z.sub_diag. apply Z.divide_0_r.
  - rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.add_assoc, xl_pre_S by lia.
    replace (xl_pre ht (w + Z.of_nat n) + cntw ht (w + Z.of_nat n) * 2 ^ (w + Z.of_nat n - 1) - xl_pre ht w)
      with ((xl_pre ht (w + Z.of_nat n) - xl_pre ht w) + cntw ht (w + Z.of_nat n) * 2 ^ (w + Z.of_nat n - 1)) by ring.
    apply Z.divide_add_r; [exact IH|]. apply Z.divide_mul_r.
    replace (w + Z.of_nat n - 1) with ((w - 1) + Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. apply Z.divide_factor_l.
Qed.

Lemma xl_T (ht: huf_table) (Hht: x2_ht_ok ht) : 1 <= ht_log ht <= HUF_TABLELOG_MAX.
Proof. destruct Hht as [[H _] _]. exact H. Qed.

Lemma xl_maxw_T (ht: huf_table) (Hht: x2_ht_ok ht) : 0 <= maxw ht <= ht_log ht.
Proof. pose proof (xl_T ht Hht). destruct Hht as [_ [_ Hf]]. apply xl_maxw_le; [lia | exact Hf]. Qed.

Lemma xl_pre_T (ht: huf_table) (Hht: x2_ht_ok ht) : xl_pre ht (ht_log ht + 1) = 2 ^ ht_log ht.
Proof.
  destruct Hht as [[_ [H _]] _]. rewrite <- H, xl_cells, xl_len_fm. reflexivity.
Qed.

Lemma xl_pre_max (ht: huf_table) (Hht: x2_ht_ok ht) : xl_pre ht (maxw ht + 1) = 2 ^ ht_log ht.
Proof.
  rewrite <- (xl_pre_T ht Hht). pose proof (xl_maxw_T ht Hht).
  replace (ht_log ht + 1) with (maxw ht + 1 + Z.of_nat (Z.to_nat (ht_log ht - maxw ht))) by lia.
  rewrite xl_pre_flat by lia. reflexivity.
Qed.

Lemma xl_pre_aligned (ht: huf_table) (Hht: x2_ht_ok ht) (w: Z) : 1 <= w <= maxw ht -> (2 ^ (w - 1) | xl_pre ht w).
Proof.
  intros Hw. pose proof (xl_maxw_T ht Hht).
  pose proof (xl_pre_div ht (Z.to_nat (ht_log ht + 1 - w)) w ltac:(lia)) as Hd.
  replace (w + Z.of_nat (Z.to_nat (ht_log ht + 1 - w))) with (ht_log ht + 1) in Hd by lia.
  rewrite (xl_pre_T ht Hht) in Hd.
  replace (xl_pre ht w) with (2 ^ ht_log ht - (2 ^ ht_log ht - xl_pre ht w)) by ring.
  apply Z.divide_sub_r; [|exact Hd].
  replace (ht_log ht) with ((w - 1) + (ht_log ht - (w - 1))) at 1 by ring.
  rewrite Z.pow_add_r by lia. apply Z.divide_factor_l.
Qed.

Lemma xl_pre_nonneg (ht: huf_table) (w: Z) : 0 <= xl_pre ht w.
Proof. unfold xl_pre. rewrite <- xl_len_fm. apply Zlength_nonneg. Qed.

Lemma xl_pow_split (ht: huf_table) (L w: Z) : ht_log ht <= L -> 1 <= w ->
  2 ^ (L - nbw ht w) = 2 ^ (L - ht_log ht) * 2 ^ (w - 1).
Proof. intros. unfold nbw. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma xl_hsym (ht: huf_table) (L w k i: Z) : x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= maxw ht ->
  0 <= k < cntw ht w -> 0 <= i < 2 ^ (L - nbw ht w) ->
  hsym ht L (rv0 ht L w + k * 2 ^ (L - nbw ht w) + i) = (Znth k (symsw ht w), nbw ht w).
Proof.
  intros Hht HL Hw Hk Hi. pose proof (xl_maxw_T ht Hht) as HmT.
  rewrite xl_rv0_pre by lia. rewrite xl_pow_split in * by lia.
  pose proof (xl_pre_nonneg ht w) as HP0.
  assert (HQ: 0 < 2 ^ (L - ht_log ht)) by (apply Z.pow_pos_nonneg; lia).
  assert (HM: 0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  unfold hsym.
  set (Q := 2 ^ (L - ht_log ht)) in *. set (M := 2 ^ (w - 1)) in *. set (P := xl_pre ht w) in *.
  replace (Q * P + k * (Q * M) + i) with (i + (P + k * M) * Q) by ring.
  rewrite Z.div_add by lia.
  assert (Hi': 0 <= i / Q < M) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  set (i' := i / Q) in *.
  rewrite xl_cells, (xl_wbelow_split w) by lia. rewrite flat_map_app.
  replace (Z.to_nat (ht_log ht + 1 - w)) with (S (Z.to_nat (ht_log ht - w))) by lia.
  cbn [seq map flat_map]. rewrite Z2Nat.id by lia.
  assert (HPl: length (flat_map (xl_blk ht) (wbelow w)) = Z.to_nat P).
  { rewrite <- (Nat2Z.id (length _)), <- Zlength_correct, xl_len_fm. reflexivity. }
  rewrite app_nth2 by (rewrite HPl; lia). rewrite HPl.
  assert (Hidx: (Z.to_nat (i' + (P + k * M)) - Z.to_nat P)%nat = (Z.to_nat k * Z.to_nat M + Z.to_nat i')%nat).
  { rewrite <- Z2Nat.inj_sub by lia. rewrite <- Z2Nat.inj_mul by lia. rewrite <- Z2Nat.inj_add by nia.
    f_equal. ring. }
  rewrite Hidx.
  pose proof (xl_blk_len ht w) as HB. fold M in HB.
  rewrite app_nth1.
  2:{ rewrite <- (Nat2Z.id (length (xl_blk ht w))), <- Zlength_correct, HB.
      rewrite <- Z2Nat.inj_mul by lia. rewrite <- Z2Nat.inj_add by nia. apply Z2Nat.inj_lt; nia. }
  unfold xl_blk. fold M. rewrite (xl_nth_fm_rep _ _ _ _ _ 0).
  - unfold Znth, nbw. destruct (Z_lt_dec k 0); [lia|reflexivity].
  - pose proof (xl_symsw_len ht w) as HS. rewrite Zlength_correct in HS. lia.
  - lia.
Qed.

Lemma x2_layout_ok : x2_layout.
Proof.
  constructor.
  - intros ht L w Hht HL Hw. pose proof (xl_maxw_T ht Hht) as HmT. split; [|split].
    + reflexivity.
    + apply xl_rv0_S. lia.
    + rewrite xl_rv0_pre by lia. rewrite (xl_pre_max ht Hht).
      rewrite <- Z.pow_add_r by (pose proof (xl_T ht Hht); lia). f_equal. lia.
  - intros ht L w Hht HL Hw. pose proof (xl_maxw_T ht Hht) as HmT.
    rewrite xl_rv0_pre, xl_pow_split by lia.
    apply Z.mod_divide.
    + assert (0 < 2 ^ (L - ht_log ht)) by (apply Z.pow_pos_nonneg; lia).
      assert (0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia). nia.
    + apply Z.mul_divide_mono_l. apply (xl_pre_aligned ht Hht); assumption.
  - intros ht L w k i Hht HL Hw Hk Hi. apply xl_hsym; assumption.
Qed.
