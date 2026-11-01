(* Arithmetic of the bit writer's bodies (plain Coq): little-endian
   bytes of W across the bytes bits_put / bits_end_mark / bits_pad put. *)
Require Import Zstd.proof.harness.writer.model.WModel.

Lemma wbm_pow_pos : forall a, 0 <= a -> 0 < 2 ^ a.
Proof. intros; apply Z.pow_pos_nonneg; lia. Qed.

Lemma wbm_le_bytes_snoc : forall k v,
  le_bytes (S k) v = le_bytes k v ++ [(v / 2 ^ (8 * Z.of_nat k)) mod 256].
Proof.
  induction k; intros v.
  - simpl. rewrite Z.div_1_r. reflexivity.
  - change (le_bytes (S (S k)) v) with ((v mod 256) :: le_bytes (S k) (v / 256)).
    change (le_bytes (S k) v) with ((v mod 256) :: le_bytes k (v / 256)).
    rewrite (IHk (v / 256)). cbn [app]. f_equal. f_equal. f_equal.
    rewrite Z.div_div by (first [lia | apply wbm_pow_pos; lia]).
    f_equal. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma wbm_le_bytes_add : forall k a b,
  le_bytes k (a + 2 ^ (8 * Z.of_nat k) * b) = le_bytes k a.
Proof.
  induction k; intros a b.
  - reflexivity.
  - assert (E: 2 ^ (8 * Z.of_nat (S k)) = 256 * 2 ^ (8 * Z.of_nat k)).
    { rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
      rewrite Z.pow_add_r by lia. reflexivity. }
    rewrite E. cbn [le_bytes]. replace (a + 256 * 2 ^ (8 * Z.of_nat k) * b) with (a + (2 ^ (8 * Z.of_nat k) * b) * 256) by ring.
    rewrite Z.mod_add by lia. rewrite Z.div_add by lia. rewrite IHk. reflexivity.
Qed.

Lemma wbm_pow_split : forall L, 0 <= L -> 2 ^ L = 2 ^ (8 * (L / 8)) * 2 ^ (L mod 8).
Proof.
  intros L HL. rewrite <- Z.pow_add_r by (Z.div_mod_to_equations; lia). f_equal. Z.div_mod_to_equations; lia.
Qed.

Lemma wbm_acc_bound : forall W L, 0 <= L -> 0 <= W < 2 ^ L ->
  0 <= W / 2 ^ (8 * (L / 8)) < 2 ^ (L mod 8).
Proof.
  intros W L HL HW. assert (0 <= L / 8) by (apply Z.div_pos; lia).
  pose proof (wbm_pow_pos (8 * (L / 8)) ltac:(lia)).
  split. apply Z.div_pos; lia.
  apply Z.div_lt_upper_bound; [lia |]. rewrite <- wbm_pow_split; lia.
Qed.

Lemma wbm_mod8_lt : forall L, 0 <= L -> 2 ^ (L mod 8) <= 128.
Proof.
  intros L HL. pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
Qed.

(* the full bytes do not change when v * 2^L is added *)
Lemma wbm_full_add : forall W L v, 0 <= L ->
  le_bytes (Z.to_nat (L / 8)) (W + v * 2 ^ L) = le_bytes (Z.to_nat (L / 8)) W.
Proof.
  intros W L v HL. assert (0 <= L / 8) by (apply Z.div_pos; lia).
  rewrite wbm_pow_split by lia.
  replace (W + v * (2 ^ (8 * (L / 8)) * 2 ^ (L mod 8)))
    with (W + 2 ^ (8 * Z.of_nat (Z.to_nat (L / 8))) * (v * 2 ^ (L mod 8))).
  apply wbm_le_bytes_add. rewrite Z2Nat.id by lia. ring.
Qed.

(* one more byte of a little-endian encoding (in Z) *)
Lemma wbm_le_bytes_succ : forall m W, 0 <= m ->
  le_bytes (Z.to_nat (m + 1)) W = le_bytes (Z.to_nat m) W ++ [(W / 2 ^ (8 * m)) mod 256].
Proof.
  intros m W Hm. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite wbm_le_bytes_snoc. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* the accumulator after "acc |= v << bits" *)
Lemma wbm_acc_put : forall W L v, 0 <= L -> 0 <= W < 2 ^ L -> 0 <= v ->
  W / 2 ^ (8 * (L / 8)) + v * 2 ^ (L mod 8) = (W + v * 2 ^ L) / 2 ^ (8 * (L / 8)).
Proof.
  intros W L v HL HW Hv. assert (0 <= L / 8) by (apply Z.div_pos; lia).
  rewrite (wbm_pow_split L) by lia.
  replace (W + v * (2 ^ (8 * (L / 8)) * 2 ^ (L mod 8)))
    with (W + (v * 2 ^ (L mod 8)) * 2 ^ (8 * (L / 8))) by ring.
  rewrite Z.div_add by (pose proof (wbm_pow_pos (8 * (L / 8))); lia). reflexivity.
Qed.

Lemma wbm_lor_add : forall a b r, 0 <= a < 2 ^ r -> 0 <= b -> 0 <= r ->
  Z.lor a (b * 2 ^ r) = a + b * 2 ^ r.
Proof.
  intros a b r Ha Hb Hr.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (D: Z.land a (Z.shiftl b r) = 0).
  { destruct (Z.eq_dec a 0) as [-> | Ha0]; [apply Z.land_0_l |].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n r).
    - rewrite Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
    - assert (Z.log2 a < r) by (apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 a n) by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D.
  rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

(* the end mark: one byte, acc + 2^bits *)
Lemma wbm_mark : forall W L, 0 <= L -> 0 <= W < 2 ^ L ->
  bw_mark W L = bw_full W L ++ [W / 2 ^ (8 * (L / 8)) + 2 ^ (L mod 8)] /\
  0 <= W / 2 ^ (8 * (L / 8)) + 2 ^ (L mod 8) < 256.
Proof.
  intros W L HL HW. assert (0 <= L / 8) by (apply Z.div_pos; lia).
  pose proof (wbm_acc_bound W L HL HW). pose proof (wbm_mod8_lt L HL).
  assert (E: W / 2 ^ (8 * (L / 8)) + 2 ^ (L mod 8) = (W + 1 * 2 ^ L) / 2 ^ (8 * (L / 8))).
  { rewrite <- wbm_acc_put by lia. ring. }
  split; [| lia].
  unfold bw_mark, bw_full. rewrite wbm_le_bytes_succ by lia.
  replace (W + 2 ^ L) with (W + 1 * 2 ^ L) by ring.
  rewrite wbm_full_add by lia. f_equal. f_equal. rewrite <- E. apply Z.mod_small. lia.
Qed.

(* the padding: one byte acc when bits > 0, nothing when bits = 0 *)
Lemma wbm_pad_pos : forall W L, 0 <= L -> 0 <= W < 2 ^ L -> 0 < L mod 8 ->
  bw_pad W L = bw_full W L ++ [W / 2 ^ (8 * (L / 8))].
Proof.
  intros W L HL HW Hr. assert (0 <= L / 8) by (apply Z.div_pos; lia).
  pose proof (wbm_acc_bound W L HL HW). pose proof (wbm_mod8_lt L HL).
  unfold bw_pad, bw_full.
  replace ((L + 7) / 8) with (L / 8 + 1).
  - rewrite wbm_le_bytes_succ by lia. f_equal. f_equal. apply Z.mod_small. lia.
  - Z.div_mod_to_equations; lia.
Qed.

Lemma wbm_pad_zero : forall W L, 0 <= L -> L mod 8 = 0 -> bw_pad W L = bw_full W L.
Proof.
  intros W L HL Hr. unfold bw_pad, bw_full. f_equal. f_equal.
  Z.div_mod_to_equations; lia.
Qed.

(* the loop of bits_put: after j bytes, with m = L/8 + j full bytes of W' = W + v 2^L *)
Lemma wbm_loop_exit : forall L' m b, 0 <= b < 8 -> L' = 8 * m + b -> L' / 8 = m /\ L' mod 8 = b.
Proof.
  intros. subst. split; Z.div_mod_to_equations; lia.
Qed.

Lemma wbm_acc_lt : forall W L m, 0 <= W < 2 ^ L -> 0 <= m -> 8 * m <= L ->
  0 <= W / 2 ^ (8 * m) < 2 ^ (L - 8 * m).
Proof.
  intros W L m HW Hm HmL. pose proof (wbm_pow_pos (8 * m) ltac:(lia)). split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia |]. rewrite <- Z.pow_add_r by lia.
    replace (8 * m + (L - 8 * m)) with L by ring. lia.
Qed.

Lemma wbm_div_succ : forall W m, 0 <= m -> W / 2 ^ (8 * m) / 256 = W / 2 ^ (8 * (m + 1)).
Proof.
  intros W m Hm. rewrite Z.div_div by (try lia; apply wbm_pow_pos; lia).
  f_equal. replace (8 * (m + 1)) with (8 * m + 8) by ring. rewrite Z.pow_add_r by lia. reflexivity.
Qed.

(* bits_put: the accumulator after "acc |= v << bits", the full bytes of W + v 2^L, its range *)
Lemma wbm_put_setup : forall W L v nb, 0 <= L -> 0 <= W < 2 ^ L -> 0 <= nb -> 0 <= v < 2 ^ nb ->
  bw_acc W L + v * 2 ^ (L mod 8) = (W + v * 2 ^ L) / 2 ^ (8 * (L / 8)) /\
  bw_full W L = le_bytes (Z.to_nat (L / 8)) (W + v * 2 ^ L) /\
  0 <= W + v * 2 ^ L < 2 ^ (L + nb).
Proof.
  intros W L v nb HL HW Hnb Hv. split; [| split].
  - unfold bw_acc. apply wbm_acc_put; lia.
  - unfold bw_full. rewrite wbm_full_add by lia. reflexivity.
  - pose proof (wbm_pow_pos L HL). rewrite Z.pow_add_r by lia. nia.
Qed.

(* bits_put's exit: L' = 8 (q + j) + bits, bits < 8 *)
Lemma wbm_put_final : forall Wn Ln m, 0 <= m -> 0 <= Ln - 8 * m < 8 ->
  bw_full Wn Ln = le_bytes (Z.to_nat m) Wn /\ bw_acc Wn Ln = Wn / 2 ^ (8 * m) /\ bw_bits Ln = Ln - 8 * m.
Proof.
  intros Wn Ln m Hm HL. assert (E: Ln / 8 = m) by (Z.div_mod_to_equations; lia).
  unfold bw_full, bw_acc, bw_bits. rewrite E. split; [reflexivity | split; [reflexivity |]].
  Z.div_mod_to_equations; lia.
Qed.
