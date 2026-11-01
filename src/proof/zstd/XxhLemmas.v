(* Lemmas of group xxh: 64-bit arithmetic of the model (m64, rotl64) against Int64, and the facts
   about xxh64_state that clients use. *)
Require Import Zstd.proof.zstd.Gprog.
Require Export Zstd.proof.zstd.PickLemmas.

(* ---------- m64 and Int64 ---------- *)

Lemma m64_range: forall x, 0 <= m64 x <= Int64.max_unsigned.
Proof. intros. unfold m64. pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). rep_lia. Qed.

Lemma repr_m64: forall x, Int64.repr (m64 x) = Int64.repr x.
Proof.
  intros. unfold m64. change (2^64) with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq. apply Int64.repr_unsigned.
Qed.

Lemma m64_small: forall x, 0 <= x <= Int64.max_unsigned -> m64 x = x.
Proof. intros. unfold m64. apply Z.mod_small. rep_lia. Qed.

Lemma unsigned_repr_m64: forall x, Int64.unsigned (Int64.repr x) = m64 x.
Proof. intros. rewrite Int64.unsigned_repr_eq. reflexivity. Qed.

(* two in-range values with the same repr are equal *)
Lemma repr_inj_range: forall x y,
  0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.repr x = Int64.repr y -> x = y.
Proof.
  intros. rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by auto. congruence.
Qed.

Lemma rotl64_range: forall x r, 0 <= rotl64 x r <= Int64.max_unsigned.
Proof. intros. apply m64_range. Qed.

(* rotation: (x << r) | (x >> (64 - r)) *)
Lemma rotl64_repr: forall x r, 0 < r < 64 ->
  Int64.or (Int64.shl (Int64.repr x) (Int64.repr r)) (Int64.shru (Int64.repr x) (Int64.repr (64 - r))) =
  Int64.repr (rotl64 x r).
Proof.
  intros x r Hr.
  apply Int64.same_bits_eq. intros i Hi.
  change Int64.zwordsize with 64 in Hi.
  rewrite Int64.bits_or by auto.
  rewrite Int64.bits_shl by auto. rewrite Int64.bits_shru by auto.
  rewrite !Int64.unsigned_repr by rep_lia.
  change Int64.zwordsize with 64.
  unfold rotl64, m64. rewrite (Int64.testbit_repr _ i) by (change Int64.zwordsize with 64; lia).
  change (2^64) with (2^(Z.of_nat 64)).
  rewrite <- !Z.land_ones by lia.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec, Z.shiftr_spec by lia.
  rewrite (Z.ones_spec_low (Z.of_nat 64) i) by lia.
  rewrite Bool.andb_true_r.
  rewrite Z.land_spec.
  destruct (zlt i r).
  - rewrite (Z.testbit_neg_r x (i - r)) by lia.
    rewrite (Z.ones_spec_low (Z.of_nat 64) (i + (64 - r))) by lia.
    rewrite Bool.andb_true_r. simpl.
    destruct (zlt (i + (64 - r)) 64); [|lia].
    rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; lia). reflexivity.
  - destruct (zlt (i + (64 - r)) 64); [lia|].
    rewrite (Z.ones_spec_high (Z.of_nat 64) (i + (64 - r))) by lia.
    rewrite Bool.andb_false_r, !Bool.orb_false_r.
    rewrite Int64.testbit_repr by (change Int64.zwordsize with 64; lia). reflexivity.
Qed.

Lemma rotl64_m64: forall x r, 0 < r < 64 -> rotl64 (m64 x) r = rotl64 x r.
Proof.
  intros. apply repr_inj_range; try apply rotl64_range.
  rewrite <- !rotl64_repr by auto. rewrite repr_m64. reflexivity.
Qed.

(* Int64.repr equality from congruence mod 2^64 *)
Lemma repr_eqm: forall x y, x mod 2^64 = y mod 2^64 -> Int64.repr x = Int64.repr y.
Proof.
  intros. rewrite <- (repr_m64 x), <- (repr_m64 y). unfold m64. congruence.
Qed.

(* the primes as Clight writes them (signed literals) *)
Lemma P1_neg: Int64.repr (-7046029288634856825) = Int64.repr XXH_P1.
Proof. apply repr_eqm. reflexivity. Qed.
Lemma P2_neg: Int64.repr (-4417276706812531889) = Int64.repr XXH_P2.
Proof. apply repr_eqm. reflexivity. Qed.
Lemma P4_neg: Int64.repr (-8796714831421723037) = Int64.repr XXH_P4.
Proof. apply repr_eqm. reflexivity. Qed.

Lemma mod64_neg_P1: forall a, (a * -7046029288634856825) mod 2^64 = (a * XXH_P1) mod 2^64.
Proof.
  intros. rewrite (Z.mul_mod a), (Z.mul_mod a XXH_P1) by lia. f_equal.
Qed.
Lemma mod64_neg_P2: forall a, (a * -4417276706812531889) mod 2^64 = (a * XXH_P2) mod 2^64.
Proof.
  intros. rewrite (Z.mul_mod a), (Z.mul_mod a XXH_P2) by lia. f_equal.
Qed.

Lemma xxh_round_range: forall a i, 0 <= xxh_round a i <= Int64.max_unsigned.
Proof. intros. apply m64_range. Qed.
Lemma xxh_merge_range: forall a v, 0 <= xxh_merge a v <= Int64.max_unsigned.
Proof. intros. apply m64_range. Qed.

(* XXH64_round as VST's forward computes it *)
Lemma xxh_round_repr: forall acc input,
  Int64.mul
    (Int64.or (Int64.shl (Int64.repr (acc + input * -4417276706812531889)) (Int64.repr 31))
              (Int64.shru (Int64.repr (acc + input * -4417276706812531889)) (Int64.repr (64 - 31))))
    (Int64.repr (-7046029288634856825)) =
  Int64.repr (xxh_round acc input).
Proof.
  intros. rewrite rotl64_repr by lia. rewrite P1_neg, mul64_repr.
  unfold xxh_round. rewrite repr_m64. f_equal. f_equal.
  rewrite <- (rotl64_m64 (acc + input * _)) by lia. rewrite rotl64_m64 by lia.
  apply repr_inj_range; try apply rotl64_range.
  rewrite <- !rotl64_repr by lia. rewrite ?repr_m64.
  replace (Int64.repr (acc + m64 (input * XXH_P2))) with (Int64.repr (acc + input * -4417276706812531889));
    [reflexivity|].
  apply repr_eqm. unfold m64. rewrite Z.add_mod_idemp_r by lia.
  rewrite Z.add_mod, (Z.add_mod acc (input * XXH_P2)) by lia. rewrite mod64_neg_P2. reflexivity.
Qed.

(* ---------- the state predicate ---------- *)

Lemma xxh64_state_local_facts: forall sh seed l p,
  xxh64_state sh seed l p |-- !! (field_compatible t_xxh64_state [] p /\ bytes_ok l).
Proof.
  intros. unfold xxh64_state. Intros junk.
  rewrite field_at_compatible'. Intros. apply prop_right. split; auto.
  destruct H1 as [? [? [? [? [? ?]]]]]. repeat split; auto.
Qed.

Lemma xxh64_state_data_at_: forall sh seed l p,
  xxh64_state sh seed l p |-- data_at_ sh t_xxh64_state p.
Proof.
  intros. sep_apply (xxh64_state_local_facts sh seed l p). Intros. unfold xxh64_state. Intros junk.
  assert (data_at sh (tarray tuchar 32) (xxh_bytes (xxh_rest seed l) ++ junk)
            (field_address t_xxh64_state (DOT _mem64) p) |-- field_at_ sh t_xxh64_state (DOT _mem64) p).
  { rewrite field_at__memory_block. sep_apply (data_at_data_at_ sh (tarray tuchar 32)).
    rewrite data_at__memory_block. Intros. simpl sizeof. cancel. }
  sep_apply H2. clear H2.
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _total_len)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _v)).
  sep_apply (field_at_field_at_ sh t_xxh64_state (DOT _memsize)).
  unfold_data_at (data_at_ sh t_xxh64_state p). unfold field_at_. cancel.
Qed.

(* the streaming digest is the model's XXH64 for every length (lengths mod 2^64, as XXH64_digest) *)
Lemma xxh64_digest_model_eq_all: forall seed l, xxh64_digest_model seed l = xxh64 l seed.
Proof.
  intros seed l.
  unfold xxh64_digest_model, xxh64, xxh_lanes, xxh_rest. fold (xxh_init seed). rewrite Zlength_correct.
  destruct (xxh_stripes (length l) (xxh_init seed) l) as [[[[v1 v2] v3] v4] r]. cbv zeta.
  unfold xxh_lane1, xxh_lane2, xxh_lane3, xxh_lane4; simpl fst; simpl snd. cbv beta iota.
  assert (Hm: forall x y, m64 (x + m64 y) = m64 (x + y)) by (intros; unfold m64; apply Zplus_mod_idemp_r).
  rewrite Hm. reflexivity.
Qed.

Lemma xxh64_digest_model_eq: forall seed l,
  Zlength l <= Int64.max_unsigned -> xxh64_digest_model seed l = xxh64 l seed.
Proof. intros. apply xxh64_digest_model_eq_all. Qed.
