(* Lemmas for the writer's XXH64 bodies (WB_xxh): the C's 64-bit arithmetic against the model
   src/proof/model/Xxh64.v, and the model's stripe/tail functions one step at a time. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.model.Bytes.
Require Import Zstd.proof.model.Xxh64.

(* ---------- 64-bit words ---------- *)

Lemma repr64_mod (z: Z) : Int64.repr (z mod 2 ^ 64) = Int64.repr z.
Proof.
  rewrite <- (Int64.repr_unsigned (Int64.repr z)), Int64.unsigned_repr_eq. reflexivity.
Qed.

Lemma repr64_eq_mod (a b: Z) : a mod 2 ^ 64 = b mod 2 ^ 64 -> Int64.repr a = Int64.repr b.
Proof. intros H. rewrite <- (repr64_mod a), <- (repr64_mod b), H. reflexivity. Qed.

Lemma repr64_lor (a b: Z) : Int64.repr (Z.lor a b) = Int64.or (Int64.repr a) (Int64.repr b).
Proof.
  apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_or by auto. rewrite !Int64.testbit_repr by auto. apply Z.lor_spec.
Qed.

Lemma repr64_lxor (a b: Z) : Int64.repr (Z.lxor a b) = Int64.xor (Int64.repr a) (Int64.repr b).
Proof.
  apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_xor by auto. rewrite !Int64.testbit_repr by auto. apply Z.lxor_spec.
Qed.

Lemma m64_range (z: Z) : 0 <= m64 z <= Int64.max_unsigned.
Proof.
  unfold m64. pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)).
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. lia.
Qed.

Lemma m64_small (z: Z) : 0 <= z <= Int64.max_unsigned -> m64 z = z.
Proof.
  intros H. unfold m64. apply Z.mod_small.
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in H. simpl in H. lia.
Qed.

Lemma repr64_m64 (z: Z) : Int64.repr (m64 z) = Int64.repr z.
Proof. apply repr64_mod. Qed.

Lemma lxor_range (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> 0 <= Z.lxor a b <= Int64.max_unsigned.
Proof.
  intros Ha Hb.
  assert (E: forall x, 0 <= x <= Int64.max_unsigned -> 0 <= x < 2 ^ 64).
  { intros x Hx. unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize in Hx.
    simpl in Hx. simpl. lia. }
  apply E in Ha; apply E in Hb.
  assert (0 <= Z.lxor a b < 2 ^ 64).
  { split. apply Z.lxor_nonneg; lia.
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hn]; [lia|].
    apply Z.log2_lt_pow2. pose proof (Z.lxor_nonneg a b). lia.
    eapply Z.le_lt_trans. apply Z.log2_lxor; lia.
    apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]. simpl. lia. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]. simpl. lia. apply Z.log2_lt_pow2; lia. }
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl in *. lia.
Qed.

(* the C's rotation *)
Lemma rotl64_ok (x r: Z) :
  0 <= x <= Int64.max_unsigned -> 1 <= r <= 63 ->
  Int64.or (Int64.shl (Int64.repr x) (Int64.repr r)) (Int64.shru (Int64.repr x) (Int64.repr (64 - r))) =
  Int64.repr (rotl64 x r).
Proof.
  intros Hx Hr. unfold rotl64. rewrite repr64_m64, (m64_small x Hx), repr64_lor.
  unfold Int64.shl, Int64.shru. rewrite !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma rotl64_range (x r: Z) : 0 <= rotl64 x r <= Int64.max_unsigned.
Proof. apply m64_range. Qed.

(* the constants as the C writes them *)
Lemma XP1_c : Int64.repr (-7046029288634856825) = Int64.repr XXH_P1.
Proof. apply repr64_eq_mod. reflexivity. Qed.
Lemma XP2_c : Int64.repr (-4417276706812531889) = Int64.repr XXH_P2.
Proof. apply repr64_eq_mod. reflexivity. Qed.
Lemma XP4_c : Int64.repr (-8796714831421723037) = Int64.repr XXH_P4.
Proof. apply repr64_eq_mod. reflexivity. Qed.

Lemma xxh_round_range (a i: Z) : 0 <= xxh_round a i <= Int64.max_unsigned.
Proof. apply m64_range. Qed.

Lemma xxh_merge_range (a i: Z) : 0 <= xxh_merge a i <= Int64.max_unsigned.
Proof. apply m64_range. Qed.

(* ---------- little-endian reads ---------- *)

Lemma le_value_app (a b: list Z) : le_value (a ++ b) = le_value a + 256 ^ Zlength a * le_value b.
Proof.
  induction a as [|x a IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite IH, Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg a); lia). lia.
Qed.

Lemma le_value_bound (a: list Z) : bytes_ok a -> 0 <= le_value a < 256 ^ Zlength a.
Proof.
  induction a as [|x a IH]; intros H; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - inversion H as [|? ? Hx Ha]; subst. specialize (IH Ha). unfold is_byte in Hx.
    rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg a); lia). nia.
Qed.

Lemma lor_shiftl_disjoint (a b n: Z) :
  0 <= n -> 0 <= a < 2 ^ n -> 0 <= b -> Z.lor a (Z.shiftl b n) = a + b * 2 ^ n.
Proof.
  intros Hn Ha Hb. rewrite Z.shiftl_mul_pow2 by auto.
  assert (L: Z.land a (b * 2 ^ n) = 0).
  { apply Z.bits_inj'; intros k Hk. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec k n).
    - rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - destruct (Z.eq_dec a 0) as [->|Hz]. rewrite Z.testbit_0_l. reflexivity.
      rewrite Z.bits_above_log2. reflexivity. lia.
      pose proof (proj1 (Z.log2_lt_pow2 a n ltac:(lia)) (proj2 Ha)). lia. }
  rewrite <- Z.lxor_lor by auto. rewrite <- Z.add_nocarry_lxor by auto. reflexivity.
Qed.

(* one more byte of xread *)
Lemma le_value_snoc (l: list Z) (i j: Z) :
  bytes_ok l -> 0 <= i -> 0 <= j -> i + j < Zlength l ->
  le_value (sublist i (i + (j + 1)) l) =
  Z.lor (le_value (sublist i (i + j) l)) (Z.shiftl (Znth (i + j) l) (8 * j)).
Proof.
  intros Hb Hi Hj Hl.
  rewrite (sublist_split i (i + j) (i + (j + 1))) by lia.
  rewrite le_value_app, Zlength_sublist by lia.
  replace (i + (j + 1)) with (i + j + 1) by lia.
  rewrite sublist_len_1 by lia. simpl.
  assert (Hs: bytes_ok (sublist i (i + j) l)) by (apply Forall_sublist; auto).
  pose proof (le_value_bound _ Hs) as Hv. rewrite Zlength_sublist in Hv by lia.
  assert (Hy: is_byte (Znth (i + j) l)) by (apply Forall_Znth; auto; lia).
  unfold is_byte in Hy.
  replace (256 ^ (i + j - i)) with (2 ^ (8 * j)) in *
    by (replace (i + j - i) with j by lia; rewrite Z.pow_mul_r by lia; reflexivity).
  rewrite lor_shiftl_disjoint by lia. lia.
Qed.

Lemma le_field_sublist (l: list Z) (i k: Z) :
  0 <= i -> 0 <= k -> le_field l i k = le_value (sublist i (i + k) l).
Proof.
  intros. unfold le_field, slice, sublist. rewrite skipn_firstn_comm. f_equal. f_equal. lia.
Qed.

Lemma le_value_sublist_range (l: list Z) (i k: Z) :
  bytes_ok l -> 0 <= i -> 0 <= k <= 8 -> i + k <= Zlength l ->
  0 <= le_value (sublist i (i + k) l) <= Int64.max_unsigned.
Proof.
  intros Hb Hi Hk Hl.
  assert (Hs: bytes_ok (sublist i (i + k) l)) by (apply Forall_sublist; auto).
  pose proof (le_value_bound _ Hs) as Hv. rewrite Zlength_sublist in Hv by lia.
  replace (i + k - i) with k in Hv by lia.
  assert (256 ^ k <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
  unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl in *. lia.
Qed.

Lemma le_field_range (l: list Z) (i k: Z) :
  bytes_ok l -> 0 <= i -> 0 <= k <= 8 -> i + k <= Zlength l ->
  0 <= le_field l i k <= Int64.max_unsigned.
Proof. intros. rewrite le_field_sublist by lia. apply le_value_sublist_range; auto. Qed.

Lemma mod64_shift (a b k: Z) : b = a + k * 2 ^ 64 -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof. intros ->. rewrite Z_mod_plus_full. reflexivity. Qed.

(* the C's operators on unsigned long, without unfolding the constants *)
Lemma sem_mul_ll (cs: compspecs) (a b: int64) : force_val (sem_mul tulong tulong (Vlong a) (Vlong b)) = Vlong (Int64.mul a b).
Proof. reflexivity. Qed.
Lemma sem_add_ll (cs: compspecs) (a b: int64) : force_val (sem_add tulong tulong (Vlong a) (Vlong b)) = Vlong (Int64.add a b).
Proof. reflexivity. Qed.

Lemma byte_Znth (l: list Z) (j: Z) : bytes_ok l -> 0 <= j < Zlength l -> 0 <= Znth j l < 256.
Proof. intros Hb Hj. assert (is_byte (Znth j l)) by (apply Forall_Znth; auto). auto. Qed.

Lemma or_shl_repr (V b s: Z) :
  0 <= b <= Int64.max_unsigned -> 0 <= s <= Int64.max_unsigned ->
  Int64.or (Int64.repr V) (Int64.shl (Int64.repr b) (Int64.repr s)) = Int64.repr (Z.lor V (Z.shiftl b s)).
Proof.
  intros. rewrite repr64_lor. unfold Int64.shl. rewrite !Int64.unsigned_repr by lia. reflexivity.
Qed.

(* ---------- the model one step at a time ---------- *)

Lemma length_skipn_Z (l: list Z) (i: Z) :
  0 <= i <= Zlength l -> Z.of_nat (length (skipn (Z.to_nat i) l)) = Zlength l - i.
Proof.
  intros H. rewrite skipn_length, Nat2Z.inj_sub, <- Zlength_correct by (rewrite Zlength_correct in H; lia).
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma skipn_skipn_Z (l: list Z) (i o: Z) :
  0 <= i -> 0 <= o -> skipn (Z.to_nat o) (skipn (Z.to_nat i) l) = skipn (Z.to_nat (i + o)) l.
Proof. intros. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma le_field_skipn (l: list Z) (i o k: Z) :
  0 <= i -> 0 <= o -> le_field (skipn (Z.to_nat i) l) o k = le_field l (i + o) k.
Proof. intros. unfold le_field, slice. rewrite skipn_skipn_Z by auto. reflexivity. Qed.

Lemma skipn_Znth_cons (l: list Z) (i: Z) :
  0 <= i < Zlength l -> skipn (Z.to_nat i) l = Znth i l :: skipn (Z.to_nat (i + 1)) l.
Proof.
  intros H. rewrite Zlength_correct in H.
  assert (G: forall n (l: list Z), (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l).
  { induction n as [|n IH]; intros [|x l'] Hn; simpl in *; try lia; auto. apply IH; lia. }
  rewrite G by lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. f_equal.
  unfold Znth. destruct (Z_lt_dec i 0); [lia|]. reflexivity.
Qed.

Lemma skipn_all_Z (l: list Z) : skipn (Z.to_nat (Zlength l)) l = [].
Proof. rewrite Zlength_correct, Nat2Z.id. apply skipn_all. Qed.

Lemma xxh_stripes_step (n: nat) (v1 v2 v3 v4: Z) (l: list Z) :
  32 <= Z.of_nat (length l) ->
  xxh_stripes (S n) (v1, v2, v3, v4) l =
  xxh_stripes n (xxh_round v1 (le_field l 0 8), xxh_round v2 (le_field l 8 8),
                 xxh_round v3 (le_field l 16 8), xxh_round v4 (le_field l 24 8)) (skipn 32 l).
Proof.
  intros H. cbn [xxh_stripes]. destruct (Z.of_nat (length l) <? 32) eqn:E; [lia|]. reflexivity.
Qed.

Lemma xxh_stripes_done (n: nat) (v: Z * Z * Z * Z) (l: list Z) :
  Z.of_nat (length l) < 32 -> xxh_stripes n v l = (v, l).
Proof.
  intros H. destruct n; [reflexivity|]. destruct v as [[[v1 v2] v3] v4]. cbn [xxh_stripes].
  destruct (Z.of_nat (length l) <? 32) eqn:E; [reflexivity|lia].
Qed.

Definition xxh_fin4 (h: Z) (l: list Z) : Z :=
  let (h, r) := xxh_tail4 h l in xxh_avalanche (xxh_tail1 h r).

Definition xxh_fin8 (n: nat) (h: Z) (l: list Z) : Z :=
  let (h, r) := xxh_tail8 n h l in xxh_fin4 h r.

Lemma xxh_finalize_fin8 (h: Z) (l: list Z) : xxh_finalize h l = xxh_fin8 4 h l.
Proof. reflexivity. Qed.

Lemma xxh_fin8_step (n: nat) (h: Z) (l: list Z) :
  8 <= Z.of_nat (length l) ->
  xxh_fin8 (S n) h l =
  xxh_fin8 n (m64 (rotl64 (Z.lxor h (xxh_round 0 (le_field l 0 8))) 27 * XXH_P1 + XXH_P4)) (skipn 8 l).
Proof.
  intros H. unfold xxh_fin8. cbn [xxh_tail8]. destruct (Z.of_nat (length l) <? 8) eqn:E; [lia|]. reflexivity.
Qed.

Lemma xxh_fin8_done (n: nat) (h: Z) (l: list Z) :
  Z.of_nat (length l) < 8 -> xxh_fin8 n h l = xxh_fin4 h l.
Proof.
  intros H. unfold xxh_fin8. destruct n; [reflexivity|]. cbn [xxh_tail8].
  destruct (Z.of_nat (length l) <? 8) eqn:E; [reflexivity|lia].
Qed.

Lemma xxh_fin4_yes (h: Z) (l: list Z) :
  4 <= Z.of_nat (length l) ->
  xxh_fin4 h l =
  xxh_avalanche (xxh_tail1 (m64 (rotl64 (Z.lxor h (m64 (le_field l 0 4 * XXH_P1))) 23 * XXH_P2 + XXH_P3))
                           (skipn 4 l)).
Proof.
  intros H. unfold xxh_fin4, xxh_tail4. destruct (Z.of_nat (length l) <? 4) eqn:E; [lia|]. reflexivity.
Qed.

Lemma xxh_fin4_no (h: Z) (l: list Z) :
  Z.of_nat (length l) < 4 -> xxh_fin4 h l = xxh_avalanche (xxh_tail1 h l).
Proof.
  intros H. unfold xxh_fin4, xxh_tail4. destruct (Z.of_nat (length l) <? 4) eqn:E; [reflexivity|lia].
Qed.

Lemma xxh_tail1_cons (h b: Z) (l: list Z) :
  xxh_tail1 h (b :: l) = xxh_tail1 (m64 (rotl64 (Z.lxor h (m64 (b * XXH_P5))) 11 * XXH_P1)) l.
Proof. reflexivity. Qed.

Definition xxh_init : Z * Z * Z * Z := (m64 (0 + XXH_P1 + XXH_P2), m64 (0 + XXH_P2), m64 0, m64 (0 - XXH_P1)).

Definition xxh_mergeall (v1 v2 v3 v4: Z) : Z :=
  xxh_merge (xxh_merge (xxh_merge (xxh_merge
    (m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18)) v1) v2) v3) v4.

Lemma xxh64_long (bs: list Z) (v1 v2 v3 v4: Z) (rest: list Z) :
  32 <= Zlength bs -> Zlength bs <= Int64.max_unsigned ->
  xxh_stripes (length bs) xxh_init bs = ((v1, v2, v3, v4), rest) ->
  xxh64 bs 0 = xxh_fin8 4 (m64 (xxh_mergeall v1 v2 v3 v4 + Zlength bs)) rest.
Proof.
  intros H Hb E. rewrite xxh64_br_eq by (rewrite <- Zlength_correct; rep_lia). unfold xxh64_br. rewrite <- Zlength_correct.
  replace (m64 (Zlength bs)) with (Zlength bs)
    by (unfold m64; rewrite Z.mod_small; [reflexivity | rep_lia]).
  destruct (Zlength bs >=? 32) eqn:E2; [|lia].
  unfold xxh_init in E. rewrite E, xxh_finalize_fin8. unfold xxh_mergeall. reflexivity.
Qed.

Lemma xxh64_short (bs: list Z) :
  Zlength bs < 32 -> 0 <= Zlength bs -> xxh64 bs 0 = xxh_fin8 4 (m64 (m64 (0 + XXH_P5) + Zlength bs)) bs.
Proof.
  intros H Hb. rewrite xxh64_br_eq by (rewrite <- Zlength_correct; lia). unfold xxh64_br. rewrite <- Zlength_correct.
  replace (m64 (Zlength bs)) with (Zlength bs)
    by (unfold m64; rewrite Z.mod_small; [reflexivity | lia]).
  destruct (Zlength bs >=? 32) eqn:E2; [lia|]. rewrite xxh_finalize_fin8. reflexivity.
Qed.

Lemma shiftr_range (x k: Z) : 0 <= x <= Int64.max_unsigned -> 0 <= k -> 0 <= Z.shiftr x k <= Int64.max_unsigned.
Proof.
  intros Hx Hk. rewrite Z.shiftr_div_pow2 by auto.
  split. apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
  apply Z.div_le_upper_bound. apply Z.pow_pos_nonneg; lia.
  assert (1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). nia.
Qed.

Lemma shru_repr (x k: Z) :
  0 <= x <= Int64.max_unsigned -> 0 <= k <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr k) = Int64.repr (Z.shiftr x k).
Proof. intros. unfold Int64.shru. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma XP2_mul (a: Z) : Int64.mul (Int64.repr a) (Int64.repr (-4417276706812531889)) = Int64.repr (m64 (a * XXH_P2)).
Proof. rewrite XP2_c, mul64_repr, repr64_m64. reflexivity. Qed.
Lemma XP1_mul (a: Z) : Int64.mul (Int64.repr a) (Int64.repr (-7046029288634856825)) = Int64.repr (m64 (a * XXH_P1)).
Proof. rewrite XP1_c, mul64_repr, repr64_m64. reflexivity. Qed.
