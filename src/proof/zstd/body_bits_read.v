(* Bodies of BIT_getMiddleBits, BIT_lookBits(Fast), BIT_skipBits, BIT_readBits(Fast).
   Removed: the unproved body_BIT_{skipBits,lookBitsFast,readBits,readBitsFast}, bodies_bits_read (proofs: AllBodies_util_bits.v). *)
Require Import Zstd.proof.zstd.Gprog.

Lemma br_land63: forall st, 0 <= st -> Z.land st 63 = st mod 64.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma br_ones_range: forall nb, 0 <= nb < 64 -> 0 <= Z.ones nb <= Int64.max_unsigned.
Proof.
  intros. rewrite Z.ones_equiv. assert (2 ^ nb <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia). change (2^64) with (Int64.max_unsigned + 1) in H0. lia.
Qed.

Lemma br_mask: forall nb, 0 <= nb < 64 ->
  Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr nb)) (Int64.repr 1) = Int64.repr (Z.ones nb).
Proof.
  intros. unfold Int64.shl. rewrite (Int64.unsigned_repr nb) by rep_lia.
  rewrite (Int64.unsigned_repr 1) by rep_lia. rewrite Z.shiftl_1_l.
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ nb <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). change (2^63) with 9223372036854775808 in H1.
  unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.ones_equiv. try (f_equal; lia).
Qed.

Lemma br_middle: forall c k nb, 0 <= c <= Int64.max_unsigned -> 0 <= k < 64 -> 0 <= nb < 64 ->
  Int64.and (Int64.shru (Int64.repr c) (Int64.repr k))
    (Int64.sub (Int64.shl (Int64.repr 1) (Int64.repr nb)) (Int64.repr 1)) =
  Int64.repr (Z.land (Z.shiftr c k) (Z.ones nb)).
Proof.
  intros. rewrite br_mask by lia. unfold Int64.and, Int64.shru.
  rewrite (Int64.unsigned_repr c), (Int64.unsigned_repr k) by rep_lia.
  assert (0 <= Z.shiftr c k <= c). { rewrite Z.shiftr_div_pow2 by lia. split.
    apply Z.div_pos; [lia|]. apply Z.pow_pos_nonneg; lia.
    apply Z.div_le_upper_bound. apply Z.pow_pos_nonneg; lia.
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
  rewrite Int64.unsigned_repr by rep_lia. pose proof (br_ones_range nb H1).
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma br_repr_mod: forall a k, 32 <= k -> Int.repr (a mod 2 ^ k) = Int.repr a.
Proof.
  intros. apply Int.eqm_samerepr. unfold Int.eqm. apply Zbits.eqmod_sym.
  apply Zbits.eqmod_divides with (2 ^ k).
  - apply Zbits.eqmod_mod. assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). lia.
  - exists (2 ^ (k - 32)). change Int.modulus with (2 ^ 32). rewrite <- Z.pow_add_r by lia. f_equal; lia.
Qed.

Lemma br_tb_mod: forall a n m, 0 <= n -> Z.testbit (a mod 2 ^ n) m = andb (m <? n) (Z.testbit a m).
Proof.
  intros. destruct (Z.ltb_spec m n).
  - destruct (Z.leb_spec 0 m).
    + rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    + rewrite !Z.testbit_neg_r by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma br_tb_shiftr: forall a n m, Z.testbit (Z.shiftr a n) m = andb (0 <=? m) (Z.testbit a (m + n)).
Proof.
  intros. destruct (Z.leb_spec 0 m).
  - apply Z.shiftr_spec; auto.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma br_tb_shiftl: forall a n m, Z.testbit (Z.shiftl a n) m = andb (0 <=? m) (Z.testbit a (m - n)).
Proof.
  intros. destruct (Z.leb_spec 0 m).
  - apply Z.shiftl_spec; auto.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma br_tb_ones: forall n m, 0 <= n -> Z.testbit (Z.ones n) m = andb (0 <=? m) (m <? n).
Proof.
  intros. destruct (Z.leb_spec 0 m).
  - apply Z.testbit_ones_nonneg; auto.
  - rewrite Z.testbit_neg_r by lia. reflexivity.
Qed.

Lemma br_tb_V: forall a m, m < 0 -> Z.testbit a m = false.
Proof. intros. apply Z.testbit_neg_r; auto. Qed.

Lemma br_peek_eq: forall V pos nb, 0 <= nb -> 0 <= pos ->
  bs_peek V pos nb = Z.shiftr (V mod 2 ^ pos) (pos - nb).
Proof.
  intros. unfold bs_peek. remember (V mod 2 ^ pos) as x.
  destruct (Z_le_gt_dec nb pos).
  - rewrite Z.shiftr_div_pow2 by lia.
    replace (2 ^ pos) with (2 ^ (pos - nb) * 2 ^ nb) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    apply Z.div_mul_cancel_r; apply Z.pow_nonzero; lia.
  - replace (pos - nb) with (- (nb - pos)) by lia. rewrite Z.shiftr_opp_r, Z.shiftl_mul_pow2 by lia.
    replace (2 ^ nb) with (2 ^ (nb - pos) * 2 ^ pos) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite Z.mul_assoc. apply Z.div_mul. apply Z.pow_nonzero; lia.
Qed.

Lemma br_look: forall V lo pos nb, 0 <= lo -> 0 <= nb -> lo <= pos - nb -> pos <= lo + 64 ->
  Z.land (Z.shiftr ((V / 2 ^ lo) mod 2 ^ 64) ((pos - lo - nb) mod 64)) (Z.ones nb) = bs_peek V pos nb.
Proof.
  intros. rewrite br_peek_eq by lia.
  destruct (Z.eq_dec (pos - lo - nb) 64).
  - assert (nb = 0) by lia. subst nb. rewrite Z.land_0_r.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.sub_0_r, Z.div_small; auto.
    apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - rewrite (Z.mod_small (pos - lo - nb)) by lia. rewrite <- Z.shiftr_div_pow2 by lia.
    apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, !br_tb_shiftr, !br_tb_mod, br_tb_shiftr, br_tb_ones by lia.
    replace (i + (pos - lo - nb) + lo) with (i + (pos - nb)) by lia.
    destruct (Z.leb_spec 0 i); [|lia].
    destruct (Z.leb_spec 0 (i + (pos - lo - nb))); [|lia].
    destruct (Z.ltb_spec i nb); destruct (Z.ltb_spec (i + (pos - lo - nb)) 64);
    destruct (Z.ltb_spec (i + (pos - nb)) pos); simpl;
    rewrite ?andb_true_r, ?andb_false_r; try reflexivity; lia.
Qed.

Lemma br_fast: forall V lo pos nb, 0 <= lo -> 1 <= nb < 64 -> pos <= lo + 64 ->
  (lo <= pos - nb \/ (lo = 0 /\ 0 < pos)) ->
  Z.shiftr ((Z.shiftl ((V / 2 ^ lo) mod 2 ^ 64) ((lo + 64 - pos) mod 64)) mod 2 ^ 64) (64 - nb) =
  bs_peek V pos nb.
Proof.
  intros. assert (0 <= pos) by lia. rewrite br_peek_eq by lia.
  rewrite (Z.mod_small (lo + 64 - pos)) by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite !br_tb_shiftr, !br_tb_mod, br_tb_shiftl, br_tb_mod, br_tb_shiftr by lia.
  replace (i + (64 - nb) - (lo + 64 - pos) + lo) with (i + (pos - nb)) by lia.
  destruct (Z.leb_spec 0 i); [|lia].
  destruct (Z.leb_spec 0 (i + (64 - nb))); [|lia].
  destruct (Z.ltb_spec (i + (64 - nb)) 64); destruct (Z.leb_spec 0 (i + (64 - nb) - (lo + 64 - pos)));
  destruct (Z.ltb_spec (i + (64 - nb) - (lo + 64 - pos)) 64);
  destruct (Z.leb_spec 0 (i + (pos - nb))); destruct (Z.ltb_spec (i + (pos - nb)) pos); simpl;
  rewrite ?andb_true_r, ?andb_false_r; try reflexivity; try lia.
  all: rewrite br_tb_V by lia; reflexivity.
Qed.

Lemma body_BIT_getMiddleBits: semax_body Vprog Gprog f_BIT_getMiddleBits BIT_getMiddleBits_spec.
Proof.
  start_function.
  forward.
  assert (0 <= st mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  forward.
  - entailer!. rewrite br_land63 by lia. rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int64.iwordsize') with 64. lia.
  - entailer!. simpl. rewrite br_land63 by lia. rewrite Int.unsigned_repr by rep_lia.
    rewrite br_middle by lia. reflexivity.
Qed.

Lemma br_C_range: forall s lo, 0 <= bit_C s lo <= Int64.max_unsigned.
Proof.
  intros. unfold bit_C. pose proof (Z.mod_pos_bound (bs_value s / 2 ^ lo) (2 ^ 64) ltac:(lia)). rep_lia.
Qed.

Lemma body_BIT_lookBits: semax_body Vprog Gprog f_BIT_lookBits BIT_lookBits_spec.
Proof.
  start_function. unfold BIT_DStream_rep. Intros ptr lim.
  forward. forward.
  pose proof (br_C_range s lo) as HC.
  assert (0 <= (pos - lo - nb) mod 2 ^ 32 <= Int.max_unsigned)
    by (pose proof (Z.mod_pos_bound (pos - lo - nb) (2 ^ 32) ltac:(lia)); rep_lia).
  assert (Hinv := H0). destruct Hinv as (? & ? & ? & ? & ? & ? & ?).
  forward_call (bit_C s lo, (pos - lo - nb) mod 2 ^ 32, nb).
  { entailer!. simpl. rewrite Int64.Z_mod_modulus_eq. rewrite ?Int.unsigned_repr by rep_lia.
    change Int64.modulus with (2 ^ 64). change (Z.pow_pos 2 32) with (2 ^ 32).
    rewrite !br_repr_mod by lia. do 3 f_equal. f_equal. lia. }
  forward.
  rewrite <- (Zmod_div_mod 64 (2 ^ 32)) by (try lia; exists (2 ^ 26); reflexivity).
  Exists (Z.land (Z.shiftr (bit_C s lo) ((pos - lo - nb) mod 64)) (Z.ones nb)).
  unfold BIT_DStream_rep. Exists ptr lim. entailer!.
  split.
  - rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - intros. unfold bit_C. apply br_look; lia.
Qed.
