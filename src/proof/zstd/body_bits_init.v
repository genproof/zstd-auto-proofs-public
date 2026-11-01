(* Body of BIT_initDStream.
   Removed: the unproved body_BIT_initDStream; this file keeps its helper lemmas (proof: AllBodies_util_bits.v). *)
Require Import Zstd.proof.zstd.Gprog.

Lemma bi_src_split3: forall sh bp buf off n,
  0 <= off -> 0 <= n -> off + n <= Zlength buf ->
  field_compatible (tarray tuchar (Zlength buf)) [] bp ->
  data_at sh (tarray tuchar (Zlength buf)) (zbytes buf) bp =
  (data_at sh (tarray tuchar off) (zbytes (sublist 0 off buf)) bp *
   data_at sh (tarray tuchar n) (zbytes (sublist off (off + n) buf)) (offset_val off bp) *
   data_at sh (tarray tuchar (Zlength buf - (off + n)))
     (zbytes (sublist (off + n) (Zlength buf) buf)) (offset_val (off + n) bp))%logic.
Proof.
  intros sh bp buf off n H0 H1 H2 FC.
  unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength buf) off (off + n)) by (try lia; list_solve).
  rewrite !field_address0_offset.
  2,3: apply arr_field_compatible0; auto; lia.
  simpl. rewrite !sublist_map. replace (off + n - off) with n by lia.
  rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
Qed.

Lemma bi_ptr_eq: forall b i off n,
  0 <= n <= Int64.max_unsigned ->
  Vptr b (Ptrofs.sub (Ptrofs.add (Ptrofs.add i (Ptrofs.repr off))
                        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr n))))
            (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 8))))) =
  offset_val (off + (n - 8)) (Vptr b i).
Proof.
  intros. simpl. f_equal. rewrite Ptrofs.sub_add_opp, !Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_int64, Ptrofs.to_int64.
  rewrite (Ptrofs.unsigned_repr 8) by rep_lia.
  rewrite !Int64.unsigned_repr by rep_lia.
  rewrite !ptrofs_mul_repr, Ptrofs.neg_repr, !ptrofs_add_repr. f_equal. lia.
Qed.

Lemma bi_byte: forall s i, bytes_ok s -> 0 <= i < Zlength s -> 0 <= Znth i s <= Byte.max_unsigned.
Proof.
  intros s i Hs Hi. unfold bytes_ok in Hs. rewrite Forall_forall in Hs.
  specialize (Hs (Znth i s) (Znth_In i s Hi)). unfold is_byte in Hs. rep_lia.
Qed.

Lemma bi_highbit: forall b, 1 <= b <= Byte.max_unsigned -> 0 <= highbit b <= 7.
Proof.
  intros b Hb. unfold highbit. split. apply Z.log2_nonneg.
  assert (Z.log2 b < 8). { apply Z.log2_lt_pow2. lia. change (2^8) with 256. rep_lia. } lia.
Qed.

Lemma bi_last: forall s, 1 <= Zlength s -> last s 0 = Znth (Zlength s - 1) s.
Proof.
  intros s Hs. destruct s as [|x l] using rev_ind.
  - rewrite Zlength_nil in Hs. lia.
  - rewrite last_last. rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Znth_app2 by lia. replace (Zlength l + Z.succ 0 - 1 - Zlength l) with 0 by lia.
    reflexivity.
Qed.

Lemma bi_bs_total: forall s, 1 <= Zlength s ->
  bs_total s = 8 * (Zlength s - 1) + highbit (Znth (Zlength s - 1) s).
Proof.
  intros s Hs. unfold bs_total. rewrite bi_last by auto. rewrite Zlength_correct. reflexivity.
Qed.

Lemma bi_bs_wf: forall s, 1 <= Zlength s ->
  bs_wf s = negb (Znth (Zlength s - 1) s =? 0).
Proof.
  intros s Hs. unfold bs_wf. rewrite bi_last by auto.
  replace (Zlength s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma bi_le_value_app: forall l1 l2,
  le_value (l1 ++ l2) = le_value l1 + 2 ^ (8 * Zlength l1) * le_value l2.
Proof.
  induction l1 as [|b l1 IH]; intros l2.
  - simpl. rewrite ?Zlength_nil. simpl. lia.
  - simpl. rewrite IH, Zlength_cons.
    replace (8 * Z.succ (Zlength l1)) with (8 + 8 * Zlength l1) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l1); lia). change (2^8) with 256. ring.
Qed.

Lemma bi_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  induction l as [|b l IH]; intros Hl.
  - simpl. rewrite ?Zlength_nil. simpl. lia.
  - inversion Hl as [|? ? Hb Hl']; subst. specialize (IH Hl'). unfold is_byte in Hb.
    simpl le_value. rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2^8) with 256. nia.
Qed.

Lemma bi_bitC_big: forall s, bytes_ok s -> 8 <= Zlength s ->
  bit_C s (8 * (Zlength s - 8)) = le_field s (Zlength s - 8) 8.
Proof.
  intros s Hok Hn. unfold bit_C, bs_value, le_field, slice.
  set (n := Zlength s) in *.
  assert (Hsl: firstn (Z.to_nat 8) (skipn (Z.to_nat (n - 8)) s) = sublist (n - 8) n s).
  { unfold sublist. unfold n in *. rewrite Zlength_correct in *. rewrite Nat2Z.id, firstn_all.
    apply firstn_all2. rewrite skipn_length. lia. }
  rewrite Hsl.
  replace (le_value s) with (le_value (sublist 0 (n - 8) s ++ sublist (n - 8) n s))
    by (rewrite sublist_rejoin, sublist_same by lia; reflexivity).
  rewrite bi_le_value_app.
  assert (Hok1: bytes_ok (sublist 0 (n - 8) s)) by (apply Forall_sublist; auto).
  assert (Hok2: bytes_ok (sublist (n - 8) n s)) by (apply Forall_sublist; auto).
  pose proof (bi_le_value_range _ Hok1) as R1. pose proof (bi_le_value_range _ Hok2) as R2.
  rewrite Zlength_sublist in R1, R2 by lia. rewrite Zlength_sublist by lia.
  replace (n - 8 - 0) with (n - 8) in * by lia. replace (n - (n - 8)) with 8 in R2 by lia.
  rewrite Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; lia).
  rewrite Z.div_small by lia. rewrite Z.add_0_l.
  apply Z.mod_small. change (2^64) with (2^(8*8)). lia.
Qed.

Lemma bi_bitC_small: forall s, bytes_ok s -> Zlength s <= 8 ->
  bit_C s 0 = le_value s.
Proof.
  intros s Hok Hn. unfold bit_C, bs_value. rewrite Z.pow_0_r, Z.div_1_r.
  pose proof (bi_le_value_range _ Hok).
  apply Z.mod_small. split; [lia|].
  eapply Z.lt_le_trans; [apply H|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma bi_zext: forall b, 0 <= b <= Byte.max_unsigned -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof.
  intros b Hb. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia.
Qed.

Lemma bi_true: forall b, 0 <= b <= Byte.max_unsigned ->
  typed_true tuchar (Vint (Int.repr b)) -> b <> 0.
Proof.
  intros b Hb Ht ->. inversion Ht.
Qed.

Lemma bi_false: forall b, 0 <= b <= Byte.max_unsigned ->
  typed_false tuchar (Vint (Int.repr b)) -> b = 0.
Proof.
  intros b Hb Ht. unfold typed_false in Ht. simpl in Ht.
  destruct (Int.eq (Int.repr b) Int.zero) eqn:E; inversion Ht.
  apply int_eq_e in E. apply repr_inj_unsigned in E; rep_lia.
Qed.

Lemma bi_split_first: forall sh n (l: list val) q, 1 <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] q ->
  data_at sh (tarray tuchar n) l q =
  (data_at sh tuchar (Znth 0 l) q * data_at sh (tarray tuchar (n - 1)) (sublist 1 n l) (offset_val 1 q))%logic.
Proof.
  intros sh n l q Hn Hl FC. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh n 1) by lia.
  rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia).
  change (Tarray tuchar 1 noattr) with (tarray tuchar 1).
  rewrite (data_at_singleton_array_eq sh tuchar (Znth 0 l)) by (rewrite sublist_one by lia; reflexivity).
  reflexivity.
Qed.

Lemma bi_acc: forall x a K k, 0 <= a <= Byte.max_unsigned -> 0 <= k < 64 -> K = Int64.repr k ->
  Int64.add (Int64.repr x) (Int64.shl (Int64.repr (Int.unsigned (Int.repr a))) K) =
  Int64.repr (x + a * 2 ^ k).
Proof.
  intros x a K k Ha Hk ->. rewrite Int.unsigned_repr by rep_lia.
  unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. apply add64_repr.
Qed.

Fixpoint le_sum (s: list Z) (k: nat) : Z :=
  match k with O => 0 | S k' => le_sum s k' + Znth (Z.of_nat k') s * 2 ^ (8 * Z.of_nat k') end.

Lemma bi_le_last: forall s k, 1 <= k <= Zlength s ->
  le_value (sublist 0 k s) = le_value (sublist 0 (k - 1) s) + Znth (k - 1) s * 2 ^ (8 * (k - 1)).
Proof.
  intros s k Hk. rewrite (sublist_split 0 (k - 1) k s) by lia.
  replace (sublist (k - 1) k s) with [Znth (k - 1) s]
    by (rewrite <- sublist_len_1 by lia; f_equal; lia).
  rewrite bi_le_value_app. rewrite Zlength_sublist by lia.
  simpl le_value. replace (k - 1 - 0) with (k - 1) by lia. ring.
Qed.

Lemma bi_le_sum_ok: forall s k, (Z.of_nat k <= Zlength s) ->
  le_value (sublist 0 (Z.of_nat k) s) = le_sum s k.
Proof.
  intros s k. induction k as [|k IH]; intros Hk.
  - change (Z.of_nat 0) with 0. rewrite sublist_nil. reflexivity.
  - rewrite bi_le_last by lia. replace (Z.of_nat (S k) - 1) with (Z.of_nat k) by lia.
    rewrite IH by lia. reflexivity.
Qed.

Lemma bi_le_sum: forall s, le_value s = le_sum s (Z.to_nat (Zlength s)).
Proof.
  intros s. rewrite <- bi_le_sum_ok by (rewrite Z2Nat.id; pose proof (Zlength_nonneg s); lia).
  rewrite Z2Nat.id by (apply Zlength_nonneg). rewrite sublist_same by lia. reflexivity.
Qed.

Ltac bi_tc :=
  entailer!;
  match goal with
  | H: forall i, 0 <= i < _ -> 0 <= Znth i ?l <= _ |- context [Znth ?i ?l] =>
      pose proof (H i ltac:(lia))
  end;
  rewrite Int.unsigned_repr by rep_lia; rep_lia.

(* one case of the switch: bitContainer += src[i] << k *)
Ltac bi_byte k :=
  forward; forward; [bi_tc | ]; forward;
  rewrite (bi_acc _ _ _ k)
    by first [ reflexivity | lia
             | match goal with
               | H: forall i, 0 <= i < _ -> 0 <= Znth i ?l <= _ |- 0 <= Znth ?i ?l <= _ =>
                   apply H; lia
               end ].

(* the break at the end of a case: bitContainer = le_value s *)
Ltac bi_fin Hs E :=
  forward; entailer!;
  match goal with
  | |- data_at _ _ (Vlong (Int64.repr ?X), _) _ |-- data_at _ _ (Vlong (Int64.repr (le_value ?l)), _) _ =>
      replace (le_value l) with X; [apply derives_refl | rewrite bi_le_sum, Hs, E; simpl; ring]
  end.
