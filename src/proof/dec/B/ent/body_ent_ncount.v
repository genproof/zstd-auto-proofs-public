(* Group ENT: body of FSE_readNCount_body. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope Z_scope.

(* ---------- arithmetic: ctz (copied from zstd/body_util_count.v, not imported here) ---------- *)

Lemma nc_odd_factor v : 0 < v -> exists k j, 0 <= k /\ 0 <= j /\ v = 2 ^ k * (2 * j + 1).
Proof.
  intros Hv. assert (H0: 0 <= v) by lia. revert Hv. pattern v. apply Z_lt_induction; [|exact H0].
  clear. intros v IH Hv.
  destruct (Z.even v) eqn:E.
  - apply Z.even_spec in E. destruct E as [m Em].
    destruct (IH m) as (k & j & Hk & Hj & Ev); [lia|lia|].
    exists (k + 1), j. split; [lia|split; [lia|]].
    rewrite Z.pow_add_r by lia. rewrite Em, Ev. ring.
  - assert (O: Z.odd v = true) by (rewrite <- Z.negb_even, E; reflexivity).
    apply Z.odd_spec in O. destruct O as [m Em].
    exists 0, m. split; [lia|split; [lia|]]. rewrite Em. simpl. ring.
Qed.

Lemma nc_land_odd_neg j : Z.land (2 * j + 1) (- (2 * j + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (- (2 * j + 1)) with (2 * (- j - 1) + 1) by ring.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    replace (- j - 1) with (Z.lnot j) by (unfold Z.lnot; lia).
    rewrite Z.lnot_spec by lia.
    rewrite (Z.bits_above_log2 1) by (simpl; lia).
    destruct (Z.testbit j (n - 1)); reflexivity.
Qed.

Lemma nc_land_neg_factor k j : 0 <= k ->
  Z.land (2 ^ k * (2 * j + 1)) (- (2 ^ k * (2 * j + 1))) = 2 ^ k.
Proof.
  intros Hk.
  replace (- (2 ^ k * (2 * j + 1))) with (- (2 * j + 1) * 2 ^ k) by ring.
  rewrite (Z.mul_comm (2 ^ k)).
  rewrite <- !Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.shiftl_land, nc_land_odd_neg.
  rewrite Z.shiftl_mul_pow2 by lia. ring.
Qed.

Lemma nc_ctz_factor k j : 0 <= k -> ctz (2 ^ k * (2 * j + 1)) = k.
Proof.
  intros Hk. unfold ctz. rewrite nc_land_neg_factor by lia. apply Z.log2_pow2; lia.
Qed.

Lemma nc_ctz_bits x : 0 < x ->
  Z.testbit x (ctz x) = true /\ (forall i, 0 <= i < ctz x -> Z.testbit x i = false) /\ 0 <= ctz x.
Proof.
  intros Hx. destruct (nc_odd_factor x Hx) as (k & j & Hk & Hj & ->). rewrite nc_ctz_factor by lia.
  rewrite (Z.mul_comm (2 ^ k)), <- Z.shiftl_mul_pow2 by lia.
  split; [|split; [|lia]].
  - rewrite Z.shiftl_spec by lia. replace (k - k) with 0 by lia. apply Z.testbit_odd_0.
  - intros i Hi. rewrite Z.shiftl_spec by lia. apply Z.testbit_neg_r; lia.
Qed.

Lemma nc_ctz_char x k : 0 < x -> 0 <= k -> Z.testbit x k = true ->
  (forall i, 0 <= i < k -> Z.testbit x i = false) -> ctz x = k.
Proof.
  intros Hx Hk Hb Hl. destruct (nc_ctz_bits x Hx) as (B & L & N).
  destruct (Z.lt_total (ctz x) k) as [C|[C|C]]; auto.
  - rewrite Hl in B by lia. discriminate.
  - rewrite L in Hb by lia. discriminate.
Qed.

(* ---------- the forward bitstream as one number ---------- *)

Lemma nc_le_value_bound (b: list Z) : bytes_ok b -> 0 <= le_value b < 2 ^ (8 * Zlength b).
Proof.
  induction b as [|x l IH]; intros Hb.
  - simpl. lia.
  - inversion Hb as [|? ? Hx Hl]; subst. unfold is_byte in Hx. specialize (IH Hl).
    rewrite Zlength_cons. simpl le_value.
    replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia). change (2 ^ 8) with 256. nia.
Qed.

Lemma nc_le_value_firstn (b: list Z) (m: nat) : bytes_ok b ->
  le_value (firstn m b) = le_value b mod 2 ^ (8 * Z.of_nat m).
Proof.
  revert m. induction b as [|x l IH]; intros m Hb.
  - destruct m; reflexivity.
  - inversion Hb as [|? ? Hx Hl]; subst. unfold is_byte in Hx.
    destruct m as [|m].
    + simpl. symmetry. apply Z.mod_1_r.
    + simpl firstn. simpl le_value. rewrite (IH m Hl).
      replace (8 * Z.of_nat (S m)) with (8 + 8 * Z.of_nat m) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia).
      replace ((x + 256 * le_value l) mod 256) with x
        by (rewrite Z.mul_comm, Z.mod_add by lia; rewrite Z.mod_small; lia).
      replace ((x + 256 * le_value l) / 256) with (le_value l)
        by (rewrite Z.mul_comm, Z.div_add by lia; rewrite Z.div_small; lia).
      reflexivity.
Qed.

Lemma nc_le_value_skipn (b: list Z) (a: nat) : bytes_ok b ->
  le_value (skipn a b) = le_value b / 2 ^ (8 * Z.of_nat a).
Proof.
  revert a. induction b as [|x l IH]; intros a Hb.
  - destruct a; simpl; reflexivity.
  - inversion Hb as [|? ? Hx Hl]; subst. unfold is_byte in Hx.
    destruct a as [|a].
    + simpl skipn. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
    + simpl skipn. rewrite (IH a Hl). simpl le_value.
      replace (8 * Z.of_nat (S a)) with (8 + 8 * Z.of_nat a) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
      f_equal. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small; lia.
Qed.

Lemma nc_le_value_slice (b: list Z) (a m: Z) : bytes_ok b -> 0 <= a -> 0 <= m ->
  le_value (slice b a m) = (le_value b / 2 ^ (8 * a)) mod 2 ^ (8 * m).
Proof.
  intros Hb Ha Hm. unfold slice.
  rewrite nc_le_value_firstn.
  - rewrite nc_le_value_skipn by auto. rewrite !Z2Nat.id by lia. reflexivity.
  - unfold bytes_ok in *. rewrite <- (firstn_skipn (Z.to_nat a) b) in Hb.
    apply Forall_app in Hb. tauto.
Qed.

(* the bits of the stream: fbits reads bits p .. p+k-1 of le_value b *)
Lemma nc_fbits_eq (b: list Z) (p k: Z) : bytes_ok b -> 0 <= p -> 0 <= k <= 32 ->
  fbits b p k = (le_value b / 2 ^ p) mod 2 ^ k.
Proof.
  intros Hb Hp Hk. unfold fbits. rewrite nc_le_value_slice by (auto; try lia; apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound p 8 ltac:(lia)).
  apply Z.bits_inj'. intros j Hj.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (j <? k) eqn:E; cbn [andb]; [|reflexivity]. apply Z.ltb_lt in E.
  assert (0 <= p / 8) by (apply Z.div_pos; lia).
  rewrite !Z.div_pow2_bits by lia.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.div_pow2_bits by lia.
  f_equal. pose proof (Z.div_mod p 8 ltac:(lia)). lia.
Qed.

(* C's 32-bit window at byte i, shifted by bc: its low k bits are the stream's bits at 8i + bc, as long as they
   come from the window, or the window is the last 4 bytes (the stream is 0 past the end) *)
Lemma nc_window (b: list Z) (i bc k: Z) : bytes_ok b -> 0 <= i <= Zlength b - 4 -> 0 <= bc <= 31 ->
  0 <= k <= 32 -> (k + bc <= 32 \/ i = Zlength b - 4) ->
  (le_field b i 4 / 2 ^ bc) mod 2 ^ k = fbits b (8 * i + bc) k.
Proof.
  intros Hb Hi Hbc Hk Hw. rewrite nc_fbits_eq by (auto; lia). unfold le_field.
  rewrite nc_le_value_slice by (auto; lia).
  pose proof (nc_le_value_bound b Hb) as HV.
  apply Z.bits_inj'. intros j Hj.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (j <? k) eqn:E; cbn [andb]; [|reflexivity]. apply Z.ltb_lt in E.
  rewrite !Z.div_pow2_bits by lia.
  destruct (j + bc <? 8 * 4) eqn:E2.
  - apply Z.ltb_lt in E2. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
    f_equal. lia.
  - apply Z.ltb_ge in E2. rewrite Z.mod_pow2_bits_high by lia.
    destruct Hw as [Hw|Hw]; [lia|].
    symmetry. rewrite <- (Z.mod_small (le_value b) (2 ^ (8 * Zlength b))) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma nc_stream_high (b: list Z) (q: Z) : bytes_ok b -> 8 * Zlength b <= q -> Z.testbit (le_value b) q = false.
Proof.
  intros Hb Hq. pose proof (nc_le_value_bound b Hb).
  rewrite <- (Z.mod_small (le_value b) (2 ^ (8 * Zlength b))) by lia.
  apply Z.mod_pow2_bits_high. pose proof (Zlength_nonneg b). lia.
Qed.

(* ---------- the zero-repeat flags: C's ctz(~bitStream | 0x80000000) >> 1 is reps 12 ---------- *)

Lemma nc_mod4_3 (x: Z) : 0 <= x -> (x mod 4 =? 3) = (Z.testbit x 0 && Z.testbit x 1)%bool.
Proof.
  intros Hx. change 4 with (2 ^ 2).
  rewrite <- (Z.mod_pow2_bits_low x 2 0) by lia. rewrite <- (Z.mod_pow2_bits_low x 2 1) by lia.
  change (2 ^ 2) with 4.
  assert (Hy: 0 <= x mod 4 < 4) by (apply Z.mod_pos_bound; lia).
  destruct (x mod 4) as [|y|y] eqn:E; [reflexivity| |lia].
  assert (y = 1 \/ y = 2 \/ y = 3)%positive as [-> | [-> | ->]] by lia; reflexivity.
Qed.

(* t = the number of trailing ones of W, capped at 31; the 2-bit flags of the stream from q are W's *)
Lemma nc_reps_gen (b: list Z) (q W t: Z) : 0 <= W -> 0 <= t <= 31 ->
  (forall j, 0 <= j < t -> Z.testbit W j = true) -> (t < 31 -> Z.testbit W t = false) ->
  (forall j, 0 <= j <= 11 -> fbits b (q + 2 * j) 2 = (W / 2 ^ (2 * j)) mod 4) ->
  forall (k: nat) (j: Z), 0 <= j <= t / 2 -> j + Z.of_nat k <= 12 ->
  reps k b (q + 2 * j) = Z.min (Z.of_nat k) (t / 2 - j).
Proof.
  intros HW Ht Hones Hzero Hf k. induction k as [|k IH]; intros j Hj Hk.
  - simpl reps. change (Z.of_nat 0) with 0. lia.
  - simpl reps. rewrite Hf by lia.
    assert (Hd: 0 <= W / 2 ^ (2 * j)) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
    rewrite nc_mod4_3 by exact Hd. rewrite !Z.div_pow2_bits by lia.
    pose proof (Z.div_mod t 2 ltac:(lia)). pose proof (Z.mod_pos_bound t 2 ltac:(lia)).
    destruct (Z.eq_dec j (t / 2)) as [E|E].
    + (* the pair holding bit t: not 0b11 *)
      assert (Ht31: t < 31) by lia.
      assert (Z.testbit W (0 + 2 * j) = false \/ Z.testbit W (1 + 2 * j) = false) as [Z0|Z0].
      { destruct (Z.eq_dec (t mod 2) 0); [left | right]; rewrite <- Hzero by lia; f_equal; lia. }
      * rewrite Z0. cbn [andb Z.eqb]. lia.
      * rewrite Z0, Bool.andb_false_r. cbn [Z.eqb]. lia.
    + rewrite !Hones by lia. cbn [andb].
      replace (q + 2 * j + 2) with (q + 2 * (j + 1)) by lia.
      rewrite IH by lia. lia.
Qed.

Lemma nc_not_or_bits (W j: Z) : 0 <= W <= Int.max_unsigned -> 0 <= j ->
  Z.testbit (Int.unsigned (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648)))) j =
  if j <? 31 then negb (Z.testbit W j) else j =? 31.
Proof.
  intros HW Hj.
  destruct (Z_lt_le_dec j 32) as [Hj32|Hj32].
  - change (Z.testbit (Int.unsigned (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648)))) j) with
      (Int.testbit (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648))) j).
    rewrite Int.bits_or, Int.bits_not by (unfold Int.zwordsize; simpl; lia).
    unfold Int.testbit. rewrite !Int.unsigned_repr by (try rep_lia; cbv; discriminate).
    destruct (j <? 31) eqn:E.
    + apply Z.ltb_lt in E. replace (Z.testbit (Int.unsigned (Int.repr (-2147483648))) j) with false.
      * rewrite Bool.orb_false_r. reflexivity.
      * change (Int.unsigned (Int.repr (-2147483648))) with (2 ^ 31). rewrite Z.pow2_bits_false; auto; lia.
    + apply Z.ltb_ge in E. assert (j = 31) as -> by lia.
      change (Int.unsigned (Int.repr (-2147483648))) with (2 ^ 31). rewrite Z.pow2_bits_true by lia.
      rewrite Bool.orb_true_r. reflexivity.
  - rewrite (proj2 (Z.ltb_ge j 31)) by lia. rewrite (proj2 (Z.eqb_neq j 31)) by lia.
    pose proof (Int.unsigned_range (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648)))).
    rewrite <- (Z.mod_small (Int.unsigned _) (2 ^ 32)) by (change (2 ^ 32) with Int.modulus; lia).
    apply Z.mod_pow2_bits_high. lia.
Qed.

(* the repeats C computes from a window W whose low 24 bits are the stream's from q *)
Lemma nc_repeats (b: list Z) (q W: Z) : 0 <= W <= Int.max_unsigned ->
  (forall j, 0 <= j <= 11 -> fbits b (q + 2 * j) 2 = (W / 2 ^ (2 * j)) mod 4) ->
  let x := Int.unsigned (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648))) in
  0 <= ctz x <= 31 /\ (forall j, 0 <= j < ctz x -> Z.testbit W j = true) /\
  (ctz x / 2 >= 12 <-> reps 12 b q = 12) /\ (ctz x / 2 < 12 -> reps 12 b q = ctz x / 2).
Proof.
  intros HW Hf x.
  assert (Hb: forall j, 0 <= j -> Z.testbit x j = if j <? 31 then negb (Z.testbit W j) else j =? 31)
    by (intros; unfold x; apply nc_not_or_bits; lia).
  assert (Hx: 0 < x).
  { assert (H31: Z.testbit x 31 = true) by (rewrite Hb by lia; reflexivity).
    assert (0 <= x) by (unfold x; apply Int.unsigned_range).
    destruct (Z.eq_dec x 0) as [E|]; [rewrite E in H31; discriminate | lia]. }
  destruct (nc_ctz_bits x Hx) as (B & L & N).
  assert (Ht: ctz x <= 31).
  { destruct (Z_le_gt_dec (ctz x) 31) as [|C]; auto.
    specialize (L 31 ltac:(lia)). rewrite Hb in L by lia. discriminate. }
  assert (Hones: forall j, 0 <= j < ctz x -> Z.testbit W j = true).
  { intros j Hj. specialize (L j Hj). rewrite Hb in L by lia.
    rewrite (proj2 (Z.ltb_lt j 31)) in L by lia. destruct (Z.testbit W j); auto. }
  assert (Hzero: ctz x < 31 -> Z.testbit W (ctz x) = false).
  { intros C. rewrite Hb in B by lia.
    rewrite (proj2 (Z.ltb_lt _ 31)) in B by lia. destruct (Z.testbit W (ctz x)); auto. }
  pose proof (nc_reps_gen b q W (ctz x) ltac:(lia) ltac:(lia) Hones Hzero Hf 12 0) as R.
  rewrite Z.mul_0_r, Z.add_0_r in R. change (Z.of_nat 12) with 12 in R.
  assert (0 <= ctz x / 2) by (apply Z.div_pos; lia).
  rewrite R by lia. split; [lia|]. split; [exact Hones|]. split; lia.
Qed.
(* ---------- C's re-reads are wrapP ---------- *)

Lemma nc_wrapP_range (n p: Z) : 8 <= n -> 0 <= p -> 0 <= wrapP n p < 8 * n.
Proof.
  intros Hn Hp. unfold wrapP. destruct (p <? 8 * n) eqn:E; [apply Z.ltb_lt in E; lia|].
  apply Z.ltb_ge in E. pose proof (Z.mod_pos_bound (p - 8 * (n - 4)) 32 ltac:(lia)). lia.
Qed.

Lemma nc_wrapP_small (n p: Z) : p < 8 * n -> wrapP n p = p.
Proof. intros. unfold wrapP. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.

Lemma nc_wrapP_idem (n p: Z) : 8 <= n -> 0 <= p -> wrapP n (wrapP n p) = wrapP n p.
Proof. intros. apply nc_wrapP_small. pose proof (nc_wrapP_range n p). lia. Qed.

(* the C state (ip offset i, bitCount bc) of a re-read position: 8 i + bc, inside the last 4 bytes or bc <= 7 *)
Definition nc_rd (n i bc: Z) : Prop := 0 <= i <= n - 4 /\ 0 <= bc <= 31 /\ (bc <= 7 \/ i = n - 4).

(* the re-read after a count or after the zero repeats:
   if (ip <= iend-7 || (bitCount>>3) <= (iend-4) - ip) { ip += bitCount>>3; bitCount &= 7; }
   else { bitCount -= 8*(iend-4-ip); bitCount &= 31; ip = iend-4; } *)
Definition nc_reread (n i bc: Z) : Z * Z :=
  if orb (i <=? n - 7) (bc / 8 <=? n - 4 - i) then (i + bc / 8, bc mod 8)
  else (n - 4, (bc - 8 * (n - 4 - i)) mod 32).

Lemma nc_reread_ok (n i bc: Z) : 8 <= n -> 0 <= i <= n - 4 -> 0 <= bc <= 47 -> (i < n - 4 -> bc <= 31) ->
  nc_rd n (fst (nc_reread n i bc)) (snd (nc_reread n i bc)) /\
  8 * fst (nc_reread n i bc) + snd (nc_reread n i bc) = wrapP n (8 * i + bc).
Proof.
  intros Hn Hi Hbc Hlt. unfold nc_reread, nc_rd.
  pose proof (Z.div_mod bc 8 ltac:(lia)). pose proof (Z.mod_pos_bound bc 8 ltac:(lia)).
  destruct (orb (i <=? n - 7) (bc / 8 <=? n - 4 - i)) eqn:E; cbn [fst snd].
  - apply Bool.orb_true_iff in E. rewrite !Z.leb_le in E.
    assert (i + bc / 8 <= n - 4) by (destruct E; [assert (bc <= 31) by (apply Hlt; lia) |]; lia).
    rewrite nc_wrapP_small by lia. lia.
  - apply Bool.orb_false_iff in E. rewrite !Z.leb_gt in E. destruct E as [E1 E2].
    pose proof (Z.mod_pos_bound (bc - 8 * (n - 4 - i)) 32 ltac:(lia)).
    unfold wrapP. destruct (8 * i + bc <? 8 * n) eqn:F.
    + apply Z.ltb_lt in F. rewrite Z.mod_small by lia. lia.
    + replace (8 * i + bc - 8 * (n - 4)) with (bc - 8 * (n - 4 - i)) by lia. lia.
Qed.

(* the shift after 12 repeats: if (ip <= iend-7) ip += 3; else { bitCount -= 8*(iend-7-ip); bitCount &= 31;
   ip = iend-4; } *)
Definition nc_shift (n i bc: Z) : Z * Z :=
  if i <=? n - 7 then (i + 3, bc) else (n - 4, (bc - 8 * (n - 7 - i)) mod 32).

Lemma nc_shift_ok (n i bc: Z) : 8 <= n -> nc_rd n i bc ->
  nc_rd n (fst (nc_shift n i bc)) (snd (nc_shift n i bc)) /\
  8 * fst (nc_shift n i bc) + snd (nc_shift n i bc) = wrapP n (8 * i + bc + 24).
Proof.
  intros Hn (Hi & Hbc & Hw). unfold nc_shift, nc_rd.
  destruct (i <=? n - 7) eqn:E; cbn [fst snd].
  - apply Z.leb_le in E. rewrite nc_wrapP_small by lia. lia.
  - apply Z.leb_gt in E.
    pose proof (Z.mod_pos_bound (bc - 8 * (n - 7 - i)) 32 ltac:(lia)).
    unfold wrapP. destruct (8 * i + bc + 24 <? 8 * n) eqn:F.
    + apply Z.ltb_lt in F. rewrite Z.mod_small by lia. lia.
    + replace (8 * i + bc + 24 - 8 * (n - 4)) with (bc - 8 * (n - 7 - i)) by lia. lia.
Qed.

(* ---------- the zero-repeat scan terminates within its fuel ---------- *)

Lemma nc_reps_all (k: nat) (b: list Z) (p: Z) : reps k b p = Z.of_nat k ->
  forall j, 0 <= j < Z.of_nat k -> fbits b (p + 2 * j) 2 = 3.
Proof.
  revert p. induction k as [|k IH]; intros p Hr j Hj.
  - simpl in Hj. lia.
  - simpl reps in Hr. destruct (fbits b p 2 =? 3) eqn:E.
    + apply Z.eqb_eq in E. destruct (Z.eq_dec j 0) as [->|Hj0]; [rewrite Z.add_0_r; exact E|].
      replace (p + 2 * j) with ((p + 2) + 2 * (j - 1)) by lia. apply IH; lia.
    + lia.
Qed.

Lemma nc_reps12_end (b: list Z) (q: Z) : bytes_ok b -> 0 <= q -> reps 12 b q = 12 -> q + 24 <= 8 * Zlength b.
Proof.
  intros Hb Hq Hr. pose proof (nc_reps_all 12 b q Hr 11 ltac:(simpl; lia)) as H.
  rewrite nc_fbits_eq in H by (auto; lia).
  destruct (Z_lt_le_dec (q + 23) (8 * Zlength b)) as [|C]; [lia|].
  assert (Z.testbit ((le_value b / 2 ^ (q + 2 * 11)) mod 2 ^ 2) 1 = false).
  { rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia. apply nc_stream_high; auto; lia. }
  rewrite H in H0. discriminate.
Qed.

Definition nc_mu (d: Z) : Z := d / 24 + (if d mod 24 =? 0 then 1 else 0).

Lemma nc_mu_bound (d: Z) : 0 <= d -> 0 <= nc_mu d <= d / 24 + 1.
Proof. intros. unfold nc_mu. pose proof (Z.div_pos d 24). destruct (d mod 24 =? 0); lia. Qed.

Lemma nc_mu_step (n q: Z) : 8 <= n -> 0 <= q -> q + 24 <= 8 * n ->
  nc_mu (8 * n - wrapP n (q + 24)) < nc_mu (8 * n - q).
Proof.
  intros Hn Hq Hl. destruct (Z.eq_dec (q + 24) (8 * n)) as [E|E].
  - unfold wrapP. rewrite E, Z.ltb_irrefl. replace (8 * n - 8 * (n - 4)) with 32 by lia.
    replace (8 * n - q) with 24 by lia. change (32 mod 32) with 0. replace (8 * n - (8 * (n - 4) + 0)) with 32 by lia.
    reflexivity.
  - rewrite nc_wrapP_small by lia. unfold nc_mu.
    replace (8 * n - (q + 24)) with ((8 * n - q) + (-1) * 24) by lia.
    rewrite Z.div_add, Z.mod_add by lia. lia.
Qed.

(* ---------- the main loop of FSE_readNCount_body (hbSize >= 8) ---------- *)

(* the part of one iteration of ncount_loop_c after the zero repeats: the re-read, one count, the checks *)
Definition nc_count (f: nat) (b: list Z) (n maxsv1 p remaining threshold nbBits: Z) (acc: list Z)
    : option (list Z * Z * Z) :=
  let p := wrapP n p in
  let max := (2 * threshold - 1) - remaining in
  let low := fbits b p (nbBits - 1) in
  let '(count, p) :=
    if low <? max then (low, p + nbBits - 1)
    else let c := fbits b p nbBits in
         ((if c >=? threshold then c - max else c), p + nbBits) in
  let count := count - 1 in
  let remaining := if count >=? 0 then remaining - count else remaining + count in
  let acc := acc ++ [count] in
  let prev0 := count =? 0 in
  if andb (remaining <? threshold) (remaining <=? 1) then Some (acc, remaining, p) else
  let '(nbBits, threshold) :=
    if remaining <? threshold then (highbit remaining + 1, 2 ^ highbit remaining)
    else (nbBits, threshold) in
  if Zlength acc >=? maxsv1 then Some (acc, remaining, p) else
  ncount_loop_c f b n maxsv1 p remaining threshold nbBits prev0 acc.

Lemma nc_loop_unfold (f: nat) (b: list Z) (n maxsv1 p remaining threshold nbBits: Z) (prev0: bool)
    (acc: list Z) :
  ncount_loop_c (S f) b n maxsv1 p remaining threshold nbBits prev0 acc =
  if prev0 then
    let '(z, p') := zeros_c (Z.to_nat (8 * n + 8)) b n p 0 in
    let acc := acc ++ repeat 0 (Z.to_nat z) in
    if Zlength acc >=? maxsv1 then Some (acc, remaining, p')
    else nc_count f b n maxsv1 p' remaining threshold nbBits acc
  else nc_count f b n maxsv1 p remaining threshold nbBits acc.
Proof. destruct prev0; [|reflexivity]. simpl. destruct (zeros_c _ _ _ _ _). reflexivity. Qed.

(* the counting state: nbBits, threshold = 2^(nbBits-1), threshold <= remaining < 2 threshold *)
Definition nc_cnt_ok (rem thr nb: Z) : Prop :=
  2 <= nb <= 16 /\ thr = 2 ^ (nb - 1) /\ thr <= rem <= 2 * thr - 1.

Section NC.
Context (gv: globals) (shn shm sht sh: share) (pn pm pt base v_buffer: val) (nn maxsv N off: Z)
  (c: list val) (s: list Z).

Definition nc_log : Z := fbits s 0 4 + FSE_MIN_TABLELOG.

Definition nc_RES : option (list Z * Z * Z) :=
  ncount_loop_c (Z.to_nat (maxsv + 2)) s (Zlength s) (maxsv + 1) 4 (2 ^ nc_log + 1) (2 ^ nc_log)
    (nc_log + 1) false nil.

(* the 32-bit window MEM_readLE32(ip) >> bitCount *)
Definition nc_win (i bc: Z) : Z := le_field s i 4 / 2 ^ bc.

(* the counter array's first maxSV1 cells: the counts read so far, then the memset zeros *)
Definition nc_arr (acc: list Z) : list val :=
  map short_val acc ++ Zrepeat (Vint (Int.repr 0)) (maxsv + 1 - Zlength acc).

Definition nc_locals : list localdef :=
  [temp _maxSV1 (Vint (Int.repr (maxsv + 1))); temp _iend (offset_val (off + Zlength s) base);
   temp _istart (offset_val off base); lvar _buffer (tarray tschar 8) v_buffer; gvars gv;
   temp _normalizedCounter pn; temp _maxSVPtr pm; temp _tableLogPtr pt;
   temp _headerBuffer (offset_val off base); temp _hbSize (Vlong (Int64.repr (Zlength s)))].

Definition nc_seps (A: list val) : list mpred :=
  [data_at_ Tsh (tarray tschar 8) v_buffer; zstd_globals gv;
   data_at shn (tarray tshort (maxsv + 1)) A pn;
   data_at_ shn (tarray tshort (nn - (maxsv + 1))) (offset_val (2 * (maxsv + 1)) pn);
   data_at shm tuint (Vint (Int.repr maxsv)) pm; data_at sht tuint (Vint (Int.repr nc_log)) pt;
   data_at sh (tarray tuchar off) (sublist 0 off c) base;
   data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
   data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
     (offset_val (off + Zlength s) base)].

(* the C state of a re-read position i, bc and the model position: 8 i + bc = wrapP n P *)
Definition nc_pos (P i bc: Z) : Prop := 8 * i + bc = wrapP (Zlength s) P /\ nc_rd (Zlength s) i bc.

(* at the head of the for loop *)
Definition nc_inv : environ -> mpred :=
  EX F: nat, EX P: Z, EX rem: Z, EX thr: Z, EX nb: Z, EX prev0: bool, EX acc: list Z, EX i: Z, EX bc: Z,
  PROPx [ncount_loop_c F s (Zlength s) (maxsv + 1) P rem thr nb prev0 acc = nc_RES; nc_pos P i bc;
         maxsv + 2 - Zlength acc <= Z.of_nat F; Zlength acc < maxsv + 1; nc_cnt_ok rem thr nb]
  (LOCALx (temp _ip (offset_val (off + i) base) :: temp _bitCount (Vint (Int.repr bc)) ::
           temp _bitStream (Vint (Int.repr (nc_win i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
           temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
           temp _nbBits (Vint (Int.repr nb)) :: temp _previous0 (Vint (Int.repr (if prev0 then 1 else 0))) ::
           nc_locals)
  (SEPx (nc_seps (nc_arr acc)))).

(* before the count of an iteration (after the zero repeats, if any, and their re-read) *)
Definition nc_ready : environ -> mpred :=
  EX F: nat, EX P: Z, EX rem: Z, EX thr: Z, EX nb: Z, EX acc: list Z, EX i: Z, EX bc: Z,
  PROPx [nc_count F s (Zlength s) (maxsv + 1) P rem thr nb acc = nc_RES; nc_pos P i bc;
         maxsv + 1 - Zlength acc <= Z.of_nat F; Zlength acc < maxsv + 1; nc_cnt_ok rem thr nb]
  (LOCALx (temp _ip (offset_val (off + i) base) :: temp _bitCount (Vint (Int.repr bc)) ::
           temp _bitStream (Vint (Int.repr (nc_win i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
           temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
           temp _nbBits (Vint (Int.repr nb)) :: nc_locals)
  (SEPx (nc_seps (nc_arr acc)))).

(* at a break: the model's loop result; either C's state is the model's (charnum = |acc|, C's last position
   8 i + bc = P, not re-read), or the remaining count is not 1 (the zero-repeat scan stopped early at
   charnum >= maxSV1, code fix F11: C's charnum and position are then not the model's, but C rejects the
   description at its first check after the loop, as the model does) *)
Definition nc_brk : environ -> mpred :=
  EX acc: list Z, EX P: Z, EX rem: Z, EX i: Z, EX bc: Z, EX ch: Z, EX A: list val,
  PROPx [nc_RES = Some (acc, rem, P); 0 <= rem <= 2 ^ 16; Zlength A = maxsv + 1;
         (8 * i + bc = P /\ 0 <= i <= Zlength s - 4 /\ 0 <= bc <= 47 /\ (i < Zlength s - 4 -> bc <= 31) /\
          ch = Zlength acc /\ 0 <= Zlength acc <= Int.max_unsigned /\ (Zlength acc <= maxsv + 1 -> A = nc_arr acc))
         \/ rem <> 1]
  (LOCALx (temp _ip (offset_val (off + i) base) :: temp _bitCount (Vint (Int.repr bc)) ::
           temp _charnum (Vint (Int.repr ch)) :: temp _remaining (Vint (Int.repr rem)) ::
           nc_locals)
  (SEPx (nc_seps A))).

End NC.

Local Open Scope logic.

(* ---------- the window (copied from dec/H/HLemmas.v) ---------- *)

Lemma nc_arr_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p)).
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma nc_win_split: forall sh N c off s base,
  win_ok sh N c off (Zlength s) s -> field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  (data_at sh (tarray tuchar off) (sublist 0 off c) base *
   data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
   data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
     (offset_val (off + Zlength s) base)).
Proof.
  intros sh N c off s base [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]] Hfc. pose proof (Zlength_nonneg s).
  rewrite (nc_arr_split3 sh N off (Zlength s) c base) by (auto; lia). rewrite H8. reflexivity.
Qed.

Lemma nc_arr_split2: forall sh n k (l: list val) p,
  0 <= k <= n -> Zlength l = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar k) (sublist 0 k l) p *
   data_at sh (tarray tuchar (n - k)) (sublist k n l) (offset_val k p)).
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar sh n k) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma nc_win_join: forall sh N c off s base,
  win_ok sh N c off (Zlength s) s -> field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
  data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
    (offset_val (off + Zlength s) base) |-- data_at sh (tarray tuchar N) c base.
Proof. intros. rewrite (nc_win_split sh N c off s base) by auto. apply derives_refl. Qed.

Lemma nc_read_ncount_size (b: list Z) (maxsv: Z) norm log size :
  read_ncount b maxsv = Some (norm, log, size) -> size <= Zlength b.
Proof.
  unfold read_ncount. destruct (Zlength b =? 0); [discriminate|].
  destruct (fbits b 0 4 + FSE_MIN_TABLELOG >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
  destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[nm rm] p]|]; [|discriminate].
  destruct (negb (rm =? 1)); [discriminate|]. destruct (Zlength nm >? maxsv + 1); [discriminate|].
  destruct ((p + 7) / 8 >? Zlength b) eqn:E; [discriminate|].
  intros Hs. injection Hs as <- <- <-. rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. exact E.
Qed.

Lemma nc_short_vals (nc: list val) (norm: list Z) :
  Forall (value_fits tshort) nc -> sublist 0 (Zlength norm) nc = zbytes norm ->
  sublist 0 (Zlength norm) nc = map short_val norm.
Proof.
  intros Hf Hs. rewrite Hs.
  assert (Hf2: Forall (value_fits tshort) (zbytes norm)) by (rewrite <- Hs; apply Forall_sublist; auto).
  clear Hs Hf. induction norm as [|x l IH]; [reflexivity|].
  simpl in Hf2 |- *. inversion Hf2 as [|? ? Hx Hl]; subst.
  rewrite (IH Hl). f_equal. unfold short_val. f_equal. symmetry. apply sign_ext_inrange.
  rewrite value_fits_eq in Hx. simpl in Hx. specialize (Hx ltac:(discriminate)).
  unfold tc_val' in Hx. simpl in Hx. unfold two_p; simpl. lia.
Qed.

Lemma nc_short_split_: forall sh n k p,
  0 <= k <= n -> field_compatible (tarray tshort n) [] p ->
  data_at_ sh (tarray tshort n) p =
  (data_at_ sh (tarray tshort k) p * data_at_ sh (tarray tshort (n - k)) (offset_val (2 * k) p)).
Proof.
  intros. rewrite (split2_data_at__Tarray_app k n) by lia.
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_comm. reflexivity.
Qed.

Lemma nc_memset_short: forall sh k p, readable_share sh -> 0 <= k -> field_compatible (tarray tshort k) [] p ->
  data_at sh (tarray tuchar (2 * k)) (Zrepeat (Vint (Int.repr 0)) (2 * k)) p |--
  data_at sh (tarray tshort k) (Zrepeat (Vint (Int.repr 0)) k) p.
Proof.
  intros sh k p Hr Hk Hf.
  replace (2 * k)%Z with (sizeof (tarray tshort k)) by (simpl; rewrite Z.max_r by lia; lia).
  eapply derives_trans; [apply memset_zero_data_at; auto|].
  rewrite zero_val_tarray. unfold tshort. rewrite zero_val_Tint. apply derives_refl.
Qed.

Lemma nc_and_mask (w k: Z) : 0 <= k < 32 ->
  Int.and (Int.repr w) (Int.repr (2 ^ k - 1)) = Int.repr (w mod 2 ^ k).
Proof.
  intros Hk. apply Int.same_bits_eq. intros j Hj.
  rewrite Int.bits_and by auto. rewrite !Int.testbit_repr by auto.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). rewrite Z.testbit_ones_nonneg by lia.
  rewrite Z.testbit_mod_pow2 by lia.
  destruct (j <? k) eqn:E; [apply Bool.andb_true_r | apply Bool.andb_false_r].
Qed.

Lemma nc_short_join: forall sh n k (A: list val) p,
  0 <= k <= n -> Zlength A = k -> field_compatible (tarray tshort n) [] p ->
  data_at sh (tarray tshort k) A p * data_at_ sh (tarray tshort (n - k)) (offset_val (2 * k) p) |--
  data_at sh (tarray tshort n) (A ++ Zrepeat Vundef (n - k)) p.
Proof.
  intros. rewrite (split2_data_at_Tarray_app k n) by list_solve.
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite (Z.mul_comm 2 k).
  apply sepcon_derives; [apply derives_refl|]. unfold data_at_, field_at_. apply derives_refl.
Qed.

Lemma nc_neg_repr (e: Z) : Int64.repr (- e) = Int64.repr (2 ^ 64 - e).
Proof. apply Int64.eqm_samerepr. exists (-1). change Int64.modulus with (2 ^ 64). lia. Qed.

Lemma nc_shl1 (k: Z) : 0 <= k < 31 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
  intros Hk. rewrite Int.shl_mul_two_p. rewrite Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. rewrite Int.mul_commut, Int.mul_one. reflexivity.
Qed.

Lemma nc_pow_bound (k: Z) : 0 <= k <= 15 -> 1 <= 2 ^ k <= 2 ^ 15.
Proof. intros. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]. Qed.

Lemma nc_le_field_range (b: list Z) (i: Z) : bytes_ok b -> 0 <= i -> 0 <= le_field b i 4 <= Int.max_unsigned.
Proof.
  intros Hb Hi. unfold le_field. rewrite nc_le_value_slice by (auto; lia).
  pose proof (Z.mod_pos_bound (le_value b / 2 ^ (8 * i)) (2 ^ (8 * 4)) ltac:(reflexivity)).
  change (2 ^ (8 * 4)) with (Int.max_unsigned + 1) in *. lia.
Qed.

Lemma nc_win_range (b: list Z) (i bc: Z) : bytes_ok b -> 0 <= i -> 0 <= bc ->
  0 <= le_field b i 4 / 2 ^ bc <= Int.max_unsigned.
Proof.
  intros Hb Hi Hbc. pose proof (nc_le_field_range b i Hb Hi).
  assert (0 < 2 ^ bc) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply Z.le_trans with (le_field b i 4); [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma nc_shru (w k: Z) : 0 <= w <= Int.max_unsigned -> 0 <= k < 32 ->
  Int.shru (Int.repr w) (Int.repr k) = Int.repr (w / 2 ^ k).
Proof.
  intros Hw Hk. rewrite Int.shru_div_two_p. rewrite !Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. reflexivity.
Qed.

Lemma nc_size_check (n i bc: Z) : 8 <= n -> 0 <= i <= n - 4 -> 0 <= bc <= 47 -> (i < n - 4 -> bc <= 31) ->
  ((8 * i + bc + 7) / 8 >? n) = (bc >? 32) /\ (bc <= 32 -> (8 * i + bc + 7) / 8 = i + (bc + 7) / 8).
Proof.
  intros Hn Hi Hbc Hlt.
  replace (8 * i + bc + 7) with ((bc + 7) + i * 8) by lia. rewrite Z.div_add by lia.
  split; [|lia].
  pose proof (Z.div_mod (bc + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (bc + 7) 8 ltac:(lia)).
  destruct (bc >? 32) eqn:E.
  - apply Z.gtb_lt in E. assert (i = n - 4) by (destruct (Z_lt_le_dec i (n - 4)); [specialize (Hlt l)|]; lia).
    apply Z.gtb_lt. lia.
  - rewrite Z.gtb_ltb in E |- *. apply Z.ltb_ge in E. apply Z.ltb_ge. lia.
Qed.

Ltac nc_err_post HR e A nn maxsv shn pn sh c off s base :=
  Exists (2 ^ 64 - e) (A ++ Zrepeat Vundef (nn - (maxsv + 1))) (@None (list Z * Z * Z));
  unfold nc_rel; match goal with h: (?x <? 8) = false |- _ => change (Zlength s) with x; rewrite h end;
  match goal with h: x_ncount s maxsv = _ |- _ => rewrite h end;
  rewrite HR;
  entailer!;
  [ try (split; [list_solve|]); rewrite nc_neg_repr; reflexivity
  | sep_apply (nc_short_join shn nn (maxsv + 1) A pn); auto; try lia; try list_solve;
    sep_apply (nc_win_join sh (Zlength c) c off s base); auto; cancel ].

Lemma nc_sub_pp (base: val) (off d: Z) : isptr base -> 0 <= d <= Ptrofs.max_signed ->
  force_val (sem_sub_pp tuchar (offset_val (off + d) base) (offset_val off base)) = Vlong (Int64.repr d).
Proof.
  intros Hp Hd. destruct base; try contradiction. unfold sem_sub_pp. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr (off + d))) (Ptrofs.add i (Ptrofs.repr off)) = Ptrofs.repr d).
  { rewrite <- ptrofs_add_repr. rewrite <- Ptrofs.add_assoc. rewrite Ptrofs.sub_add_l.
    rewrite Ptrofs.sub_idem. rewrite Ptrofs.add_zero_l. reflexivity. }
  rewrite E. rewrite if_true by auto. simpl. unfold Vptrofs. simpl. unfold Ptrofs.divs.
  rewrite Ptrofs.signed_repr by (pose proof Ptrofs.min_signed_neg; lia).
  change (Ptrofs.signed (Ptrofs.repr 1)) with 1. rewrite Z.quot_1_r.
  unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by (pose proof Ptrofs.max_signed_unsigned; lia).
  reflexivity.
Qed.

(* ---------- the two segments of one iteration of the main loop ---------- *)

Definition nc_Delta : tycontext :=
  func_tycontext f_FSE_readNCount_body Vprog (G_B0 ++ [FSE_readNCount_spec]) nil.

(* if (previous0) { <nc_zeros_stmt> } <nc_count_stmt> : the body of the for loop *)
Definition nc_zeros_stmt : statement :=
  ltac:(let b := eval cbv delta [f_FSE_readNCount_body] in (fn_body f_FSE_readNCount_body) in
        match b with context [Sifthenelse (Etempvar _previous0 tint) ?T Sskip] => exact T end).
Definition nc_count_stmt : statement :=
  ltac:(let b := eval cbv delta [f_FSE_readNCount_body] in (fn_body f_FSE_readNCount_body) in
        match b with context [Ssequence (Sifthenelse (Etempvar _previous0 tint) _ Sskip) ?C] => exact C end).

(* normal exit Q, break exit B, no continue, no return *)
Definition nc_ret (Q B: environ -> mpred) : ret_assert :=
  overridePost Q (loop1_ret_assert FF (normal_ret_assert B)).

Lemma nc_arr_upd (maxsv: Z) (acc: list Z) (x: Z) : Zlength acc < maxsv + 1 ->
  upd_Znth (Zlength acc) (nc_arr maxsv acc) (Vint (Int.sign_ext 16 (Int.repr x))) = nc_arr maxsv (acc ++ [x]).
Proof.
  intros H. unfold nc_arr. rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil. simpl map.
  pose proof (Zlength_nonneg acc).
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia). rewrite Zlength_map, Z.sub_diag.
  replace (maxsv + 1 - Zlength acc) with (1 + (maxsv + 1 - (Zlength acc + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. f_equal; try reflexivity.
Qed.

Lemma nc_eq_zero (x: Z) : -1 <= x <= Int.max_signed -> Int.eq (Int.repr x) Int.zero = (x =? 0).
Proof.
  intros Hx. destruct (Z.eqb_spec x 0) as [->|E]; [reflexivity|].
  apply Int.eq_false. intro R. apply E. apply repr_inj_signed; [rep_lia | rep_lia | exact R].
Qed.

Lemma nc_count_eq (F: nat) (b: list Z) (n maxsv1 P rem thr nb: Z) (acc: list Z)
    (q mx low cf cnt0 badd cnt rem1: Z) :
  q = wrapP n P -> mx = 2 * thr - 1 - rem -> low = fbits b q (nb - 1) -> cf = fbits b q nb ->
  cnt0 = (if low <? mx then low else if cf >=? thr then cf - mx else cf) ->
  badd = (if low <? mx then nb - 1 else nb) -> cnt = cnt0 - 1 ->
  rem1 = (if cnt >=? 0 then rem - cnt else rem + cnt) ->
  nc_count F b n maxsv1 P rem thr nb acc =
  if andb (rem1 <? thr) (rem1 <=? 1) then Some (acc ++ [cnt], rem1, q + badd) else
  if Zlength (acc ++ [cnt]) >=? maxsv1 then Some (acc ++ [cnt], rem1, q + badd) else
  ncount_loop_c F b n maxsv1 (q + badd) rem1 (if rem1 <? thr then 2 ^ highbit rem1 else thr)
    (if rem1 <? thr then highbit rem1 + 1 else nb) (cnt =? 0) (acc ++ [cnt]).
Proof.
  intros Hq Hmx Hlow Hcf Hc0 Hb Hc Hr. unfold nc_count. rewrite <- Hq, <- Hmx, <- Hlow.
  destruct (low <? mx) eqn:E.
  - rewrite <- Hc0 in *. replace (q + nb - 1) with (q + badd) by lia. rewrite <- Hc, <- Hr.
    destruct (rem1 <? thr); reflexivity.
  - rewrite <- Hcf, <- Hc0. replace (q + nb) with (q + badd) by lia. rewrite <- Hc, <- Hr.
    destruct (rem1 <? thr); reflexivity.
Qed.

(* ---------- pointer tests in one byte array (copied from zstd/body6_xxh_update.v) ---------- *)

Lemma ncx_wvp_off: forall sh n c p i, readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite data_at__memory_block. Intros. simpl sizeof.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.



Lemma ncx_test_order': forall R a b p, isptr p ->
  (R |-- weak_valid_pointer (offset_val a p)) -> (R |-- weak_valid_pointer (offset_val b p)) ->
  R |-- denote_tc_test_order (offset_val a p) (offset_val b p).
Proof.
  intros. destruct p; try contradiction.
  apply derives_trans with (weak_valid_pointer (offset_val a (Vptr b0 i)) && weak_valid_pointer (offset_val b (Vptr b0 i))).
  { apply andp_right; auto. }
  Transparent denote_tc_test_order. unfold denote_tc_test_order. Opaque denote_tc_test_order.
  simpl. unfold test_order_ptrs. simpl. destruct (peq b0 b0); [|contradiction]. simpl. apply derives_refl.
Qed.

Lemma ncx_ofs: forall b i n a, field_compatible (tarray tuchar n) [] (Vptr b i) -> 0 <= a <= n ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr a)) = Ptrofs.unsigned i + a.
Proof.
  intros. destruct H as [_ [_ [Hs _]]]. simpl in Hs. rewrite Z.max_r in Hs by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr a) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma ncx_cmp: forall p n a c, field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= c <= n ->
  sem_cmp_pp Cle (offset_val a p) (offset_val c p) = Some (bool2val (a <=? c)) /\
  sem_cmp_pp Clt (offset_val a p) (offset_val c p) = Some (bool2val (a <? c)).
Proof.
  intros. destruct p; try (destruct H; contradiction).
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !(ncx_ofs b i n) by auto.
  split; f_equal; f_equal.
  - destruct (zlt _ _), (a <=? c) eqn:E; simpl; auto; try (apply Z.leb_le in E; lia); try (apply Z.leb_gt in E; lia).
  - destruct (zlt _ _), (a <? c) eqn:E; simpl; auto; try (apply Z.ltb_lt in E; lia); try (apply Z.ltb_ge in E; lia).
Qed.

Lemma nc_sub_pi: forall p a k, isptr p -> 0 <= k <= Int.max_signed ->
  force_val (sem_sub_pi tuchar Signed (offset_val a p) (Vint (Int.repr k))) = offset_val (a - k) p.
Proof.
  intros p a k Hp Hk. destruct p; try contradiction. unfold sem_sub_pi. simpl. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr, Z.mul_1_l.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite <- Ptrofs.sub_add_opp, ptrofs_sub_repr. reflexivity.
Qed.

Lemma nc_cmp_le: forall n off base a c, field_compatible (tarray tuchar n) [] (offset_val off base) ->
  0 <= a <= n -> 0 <= c <= n ->
  sem_cmp_pp Cle (offset_val (off + a) base) (offset_val (off + c) base) = Some (bool2val (a <=? c)).
Proof.
  intros. rewrite <- !(offset_offset_val base off). apply (ncx_cmp (offset_val off base) n); auto.
Qed.

Lemma nc_typed_true_b (b: bool) : typed_true tint (bool2val b) -> b = true.
Proof. destruct b; auto. intros H. unfold typed_true in H. simpl in H. discriminate. Qed.

Lemma nc_typed_false_b (b: bool) : typed_false tint (bool2val b) -> b = false.
Proof. destruct b; auto. intros H. unfold typed_false in H. simpl in H. discriminate. Qed.

Lemma nc_reread_cond (base: val) (off n i bc1: Z) : isptr base -> 0 <= i <= n - 4 -> 0 <= bc1 <= 47 ->
  n <= 2 ^ 63 - 1 ->
  force_val (sem_cast tint tbool (eval_binop Ole tint tlong
     (eval_binop Oshr tint tint (Vint (Int.repr bc1)) (Vint (Int.repr 3)))
     (eval_binop Osub (tptr tuchar) (tptr tuchar)
        (eval_binop Osub (tptr tuchar) tint (offset_val (off + n) base) (Vint (Int.repr 4)))
        (offset_val (off + i) base)))) = Vint (Int.repr (if bc1 / 8 <=? n - 4 - i then 1 else 0)).
Proof.
  intros Hp Hi Hb Hn.
  assert (E1: eval_binop Osub (tptr tuchar) tint (offset_val (off + n) base) (Vint (Int.repr 4)) =
              offset_val (off + i + (n - 4 - i)) base).
  { unfold eval_binop. simpl. replace (off + i + (n - 4 - i)) with (off + n - 4) by lia.
    apply nc_sub_pi; auto; rep_lia. }
  rewrite E1.
  assert (E2: eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val (off + i + (n - 4 - i)) base)
                (offset_val (off + i) base) = Vlong (Int64.repr (n - 4 - i))).
  { unfold eval_binop. simpl. apply nc_sub_pp; auto. rep_lia. }
  rewrite E2.
  assert (E3: eval_binop Oshr tint tint (Vint (Int.repr bc1)) (Vint (Int.repr 3)) = Vint (Int.repr (bc1 / 8))).
  { unfold eval_binop. simpl. unfold Int.shr. rewrite Int.signed_repr by rep_lia.
    rewrite Int.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  rewrite E3.
  assert (Hb8: 0 <= bc1 / 8 <= 5) by (split; [apply Z.div_pos; lia | change 5 with (47 / 8); apply Z.div_le_mono; lia]).
  remember (bc1 / 8) as k eqn:Hk. remember (n - 4 - i) as d eqn:Hd.
  unfold eval_binop. simpl. unfold Int64.lt. rewrite !Int64.signed_repr by rep_lia.
  rewrite Int.signed_repr by rep_lia.
  destruct (zlt d k) as [L|L]; simpl.
  - rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  - rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma nc_add_shr (p: val) (a x: Z) : isptr p -> 0 <= x <= 47 ->
  force_val (sem_add_ptr_int tuchar Signed (offset_val a p) (Vint (Int.shr (Int.repr x) (Int.repr 3)))) =
  offset_val (a + x / 8) p.
Proof.
  intros Hp Hx. assert (Hx8: 0 <= x / 8 <= 5) by (split; [apply Z.div_pos; lia | change 5 with (47 / 8); apply Z.div_le_mono; lia]).
  unfold Int.shr. rewrite Int.signed_repr by rep_lia. rewrite Int.unsigned_repr by rep_lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. remember (x / 8) as k.
  destruct p; try contradiction. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr, Z.mul_1_l.
  rewrite ptrofs_add_repr. reflexivity.
Qed.

Lemma nc_land_mod (x k: Z) : 0 <= k -> Z.land x (2 ^ k - 1) = x mod 2 ^ k.
Proof. intros. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia). apply Z.land_ones; lia. Qed.

Lemma nc_sub_pp2 (p: val) (off a b: Z) : isptr p -> 0 <= b - a <= Ptrofs.max_signed ->
  force_val (sem_sub_pp tuchar (offset_val (off + b) p) (offset_val (off + a) p)) = Vlong (Int64.repr (b - a)).
Proof. intros. replace (off + b) with ((off + a) + (b - a)) by lia. apply nc_sub_pp; auto. Qed.

Lemma nc_mul8_cast (d: Z) : 0 <= d <= 2 ^ 20 ->
  force_val (sem_cast_l2i I32 Signed (force_val (sem_mul tint tlong (Vint (Int.repr 8)) (Vlong (Int64.repr d))))) =
  Vint (Int.repr (8 * d)).
Proof.
  intros Hd. unfold sem_mul, sem_binarith. simpl.
  rewrite !Int64.Z_mod_modulus_eq. change Int64.modulus with (2 ^ 64).
  rewrite (Z.mod_small d) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma nc_highbit_facts (r: Z) : 2 <= r < 2 ^ 15 ->
  1 <= highbit r <= 14 /\ 2 ^ highbit r <= r < 2 * 2 ^ highbit r.
Proof.
  intros Hr. unfold highbit. pose proof (Z.log2_spec r ltac:(lia)) as [L1 L2].
  rewrite Z.pow_succ_r in L2 by (apply Z.log2_nonneg).
  assert (1 <= Z.log2 r) by (change 1 with (Z.log2 2); apply Z.log2_le_mono; lia).
  assert (Z.log2 r < 15) by (apply Z.log2_lt_pow2; lia).
  lia.
Qed.

Ltac ncx_wvp_find := first [ apply derives_refl
  | apply sepcon_weak_valid_pointer1; ncx_wvp_find | apply sepcon_weak_valid_pointer2; ncx_wvp_find ].


(* ---------- the zero-repeat scan ---------- *)

Lemma nc_wrapP_idem2 (n p: Z) : 8 <= n -> wrapP n (wrapP n p) = wrapP n p.
Proof.
  intros Hn. destruct (Z_lt_le_dec p (8 * n)) as [L|L].
  - rewrite (nc_wrapP_small n p L). apply nc_wrapP_small. exact L.
  - apply nc_wrapP_small. pose proof (nc_wrapP_range n p ltac:(lia) ltac:(lia)). lia.
Qed.

(* the scan only adds zeros *)
Lemma nc_zeros_ge (f: nat) (b: list Z) (n p z: Z) : z <= fst (zeros_c f b n p z).
Proof.
  revert p z; induction f as [|f IH]; intros p z; cbn [zeros_c]; [simpl; lia|].
  destruct (reps 12 b (wrapP n p) =? 12); [specialize (IH (wrapP n p + 24) (z + 36)); lia|].
  cbn [fst]. pose proof (reps_nonneg 12 b (wrapP n p)).
  pose proof (ncmc_fbits_nonneg b (wrapP n p + 2 * reps 12 b (wrapP n p)) 2 ltac:(lia)). lia.
Qed.

Lemma nc_zeros_wrap (f: nat) (b: list Z) (n p z: Z) : 8 <= n ->
  zeros_c (S f) b n p z = zeros_c (S f) b n (wrapP n p) z.
Proof. intros Hn. cbn [zeros_c]. rewrite nc_wrapP_idem2 by lia. reflexivity. Qed.

Lemma nc_zeros_group (f: nat) (b: list Z) (n q z: Z) : wrapP n q = q -> reps 12 b q = 12 ->
  zeros_c (S f) b n q z = zeros_c f b n (q + 24) (z + 36).
Proof. intros Hw Hr. cbn [zeros_c]. rewrite Hw, Hr. reflexivity. Qed.

Lemma nc_zeros_last (f: nat) (b: list Z) (n q z r: Z) : wrapP n q = q -> reps 12 b q = r -> r < 12 ->
  zeros_c (S f) b n q z = (z + 3 * r + fbits b (q + 2 * r) 2, q + 2 * r + 2).
Proof. intros Hw Hr Hlt. cbn [zeros_c]. rewrite Hw, Hr. rewrite (proj2 (Z.eqb_neq r 12)) by lia. reflexivity. Qed.

(* the window shifted by a further a bits *)
Lemma nc_window2 (b: list Z) (i bc a k: Z) : bytes_ok b -> 0 <= i <= Zlength b - 4 -> 0 <= bc <= 31 ->
  0 <= a -> 0 <= k <= 32 -> (a + k + bc <= 32 \/ i = Zlength b - 4) ->
  (le_field b i 4 / 2 ^ bc / 2 ^ a) mod 2 ^ k = fbits b (8 * i + bc + a) k.
Proof.
  intros Hb Hi Hbc Ha Hk Hw. rewrite nc_fbits_eq by (auto; lia). unfold le_field.
  rewrite nc_le_value_slice by (auto; lia).
  apply Z.bits_inj'. intros j Hj.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (j <? k) eqn:E; cbn [andb]; [|reflexivity]. apply Z.ltb_lt in E.
  rewrite !Z.div_pow2_bits by lia.
  destruct (j + a + bc <? 8 * 4) eqn:E2.
  - apply Z.ltb_lt in E2. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.div_pow2_bits by lia.
    f_equal. lia.
  - apply Z.ltb_ge in E2. rewrite Z.mod_pow2_bits_high by lia.
    destruct Hw as [Hw|Hw]; [lia|].
    symmetry. apply nc_stream_high; auto. lia.
Qed.

Lemma nc_sub_pp_z (base: val) (off d: Z) : isptr base -> - 2 ^ 31 <= d <= 2 ^ 31 ->
  force_val (sem_sub_pp tuchar (offset_val (off + d) base) (offset_val off base)) = Vlong (Int64.repr d).
Proof.
  intros Hp Hd. destruct base; try contradiction. unfold sem_sub_pp. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr (off + d))) (Ptrofs.add i (Ptrofs.repr off)) = Ptrofs.repr d).
  { rewrite <- ptrofs_add_repr. rewrite <- Ptrofs.add_assoc. rewrite Ptrofs.sub_add_l.
    rewrite Ptrofs.sub_idem. rewrite Ptrofs.add_zero_l. reflexivity. }
  rewrite E. rewrite if_true by auto. simpl. unfold Vptrofs. simpl. unfold Ptrofs.divs.
  rewrite Ptrofs.signed_repr by (unfold Ptrofs.min_signed, Ptrofs.max_signed; simpl; lia).
  change (Ptrofs.signed (Ptrofs.repr 1)) with 1. rewrite Z.quot_1_r.
  unfold Ptrofs.to_int64. f_equal. apply Int64.eqm_samerepr. apply Int64.eqm_sym.
  change Int64.eqm with Ptrofs.eqm. apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma nc_mul8_cast_z (d: Z) : - 2 ^ 20 <= d <= 2 ^ 20 ->
  force_val (sem_cast_l2i I32 Signed (force_val (sem_mul tint tlong (Vint (Int.repr 8)) (Vlong (Int64.repr d))))) =
  Vint (Int.repr (8 * d)).
Proof.
  intros Hd. unfold sem_mul, sem_binarith. simpl. f_equal.
  apply Int.eqm_samerepr. rewrite !Int64.Z_mod_modulus_eq. change Int64.modulus with (2 ^ 64).
  unfold Int.eqm. change Int.modulus with (2 ^ 32).
  apply Zbits.eqmod_trans with (8 * (d mod 2 ^ 64))%Z.
  - apply Zbits.eqmod_divides with (2 ^ 64). apply Zbits.eqmod_sym, Zbits.eqmod_mod. lia.
    exists (2 ^ 32). reflexivity.
  - apply Zbits.eqmod_mult; [apply Zbits.eqmod_refl|].
    apply Zbits.eqmod_divides with (2 ^ 64). apply Zbits.eqmod_sym, Zbits.eqmod_mod. lia.
    exists (2 ^ 32). reflexivity.
Qed.

Lemma nc_arr_zeros (maxsv: Z) (acc: list Z) (z: Z) : 0 <= z -> Zlength acc + z <= maxsv + 1 ->
  nc_arr maxsv (acc ++ repeat 0 (Z.to_nat z)) = nc_arr maxsv acc.
Proof.
  intros Hz Hl. unfold nc_arr. rewrite map_app, Zlength_app, Zlength_repeat by lia. rewrite ?Z2Nat.id by lia.
  rewrite map_repeat. rewrite <- app_assoc. f_equal.
  change (short_val 0) with (Vint (Int.repr 0)).
  replace (maxsv + 1 - Zlength acc) with (z + (maxsv + 1 - (Zlength acc + z))) by lia.
  rewrite <- Zrepeat_app by lia. reflexivity.
Qed.

Definition nc_x (W: Z) : Z := Int.unsigned (Int.or (Int.not (Int.repr W)) (Int.repr (-2147483648))).

Lemma nc_x_range (W: Z) : 0 <= nc_x W <= Int.max_unsigned.
Proof. unfold nc_x. apply Int.unsigned_range_2. Qed.



Lemma nc_rd_window (b: list Z) (i bc: Z) : bytes_ok b -> nc_rd (Zlength b) i bc ->
  forall j, 0 <= j <= 11 -> fbits b (8 * i + bc + 2 * j) 2 = (nc_win b i bc / 2 ^ (2 * j)) mod 4.
Proof.
  intros Hb (Hi & Hbc & Hcl) j Hj. unfold nc_win. change 4 with (2 ^ 2).
  rewrite nc_window2; auto; try lia.
Qed.

Lemma nc_repeats' (b: list Z) (i bc: Z) : bytes_ok b -> nc_rd (Zlength b) i bc ->
  0 <= ctz (nc_x (nc_win b i bc)) <= 31 /\
  (forall j, 0 <= j < ctz (nc_x (nc_win b i bc)) -> Z.testbit (nc_win b i bc) j = true) /\
  (ctz (nc_x (nc_win b i bc)) / 2 >= 12 <-> reps 12 b (8 * i + bc) = 12) /\
  (ctz (nc_x (nc_win b i bc)) / 2 < 12 -> reps 12 b (8 * i + bc) = ctz (nc_x (nc_win b i bc)) / 2).
Proof.
  intros Hb Hrd. destruct Hrd as (Hi & Hbc & Hcl) eqn:Hrd'.
  apply (nc_repeats b (8 * i + bc) (nc_win b i bc)).
  - apply nc_win_range; auto; lia.
  - apply nc_rd_window; auto.
Qed.

Lemma nc_ctz_le (b: list Z) (i bc t: Z) : bytes_ok b -> 0 <= i -> 0 <= bc <= 31 -> 0 <= t ->
  (forall j, 0 <= j < t -> Z.testbit (nc_win b i bc) j = true) -> t <= 32 - bc.
Proof.
  intros Hb Hi Hbc Ht Hones. destruct (Z_le_gt_dec t (32 - bc)) as [|C]; auto.
  specialize (Hones (32 - bc) ltac:(lia)).
  assert (HW: nc_win b i bc < 2 ^ (32 - bc)).
  { unfold nc_win. pose proof (nc_le_field_range b i Hb Hi). apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; lia. rewrite <- Z.pow_add_r by lia. replace (bc + (32 - bc)) with 32 by lia.
    change (2 ^ 32) with (Int.max_unsigned + 1). lia. }
  assert (0 <= nc_win b i bc) by (unfold nc_win; apply Z.div_pos; [apply nc_le_field_range; auto | apply Z.pow_pos_nonneg; lia]).
  rewrite <- (Z.mod_small (nc_win b i bc) (2 ^ (32 - bc))) in Hones by lia.
  rewrite Z.mod_pow2_bits_high in Hones by lia. discriminate.
Qed.

Section NCSEG.
Context (gv: globals) (shn shm sht sh: share) (pn pm pt base v_buffer: val) (nn maxsv N off: Z)
  (c: list val) (s: list Z).

(* the facts of the context that both segments may use *)
Definition nc_ctx : Prop :=
  writable_share shn /\ writable_share shm /\ writable_share sht /\ readable_share sh /\
  0 <= maxsv <= 255 /\ maxsv + 1 <= nn <= 256 /\ 8 <= Zlength s /\ bytes_ok s /\
  0 <= off /\ off + Zlength s <= N /\ N <= 2 ^ 63 - 1 /\ Zlength c = N /\
  5 <= nc_log s <= 15.

(* the head of the loop when previous0 holds (the zero-repeat scan comes first) *)
Definition nc_zpre : environ -> mpred :=
  EX f: nat, EX P: Z, EX rem: Z, EX thr: Z, EX nb: Z, EX acc: list Z, EX i: Z, EX bc: Z,
  PROPx [ncount_loop_c (S f) s (Zlength s) (maxsv + 1) P rem thr nb true acc = nc_RES maxsv s; nc_pos s P i bc;
         maxsv + 1 - Zlength acc <= Z.of_nat f; Zlength acc < maxsv + 1; nc_cnt_ok rem thr nb]
  (LOCALx (temp _ip (offset_val (off + i) base) :: temp _bitCount (Vint (Int.repr bc)) ::
           temp _bitStream (Vint (Int.repr (nc_win s i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
           temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
           temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
  (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc)))).

End NCSEG.

(* the zero-repeat scan (repeats of 12, the last repeat, the re-read), for a window of any length: inside the
   repeat loop charnum < maxSV1 (code fix F11), so C's unsigned charnum stays below maxSV1 + 36 + 48 *)
Opaque zeros_c.

Lemma nc_zeros_ok {Espec: OracleKind} gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s :
  nc_ctx shn shm sht sh nn maxsv N off c s ->
  semax nc_Delta (nc_zpre gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s) nc_zeros_stmt
    (nc_ret (nc_ready gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s)
            (nc_brk gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s)).
Proof.
  intros Hctx. destruct Hctx as (SHn & SHm & SHt & Hrd & Hmsv & Hnn & Hn8 & Hbytes & Hoff & Hend & HN & Hlc & Hlog).
  unfold nc_ret, nc_zpre. Intros f P rem thr nb acc i bc.
  rename H into HM. rename H0 into Hpos. rename H1 into HF. rename H2 into Hacc. rename H3 into Hcnt.
  destruct Hpos as [Hq (Hi & Hbc & Hcl)].
  rewrite nc_loop_unfold in HM. cbv beta iota in HM.
  destruct (zeros_c (Z.to_nat (8 * Zlength s + 8)) s (Zlength s) P 0) as [zf pf] eqn:EZ.
  assert (EZ0: zeros_c (Z.to_nat (8 * Zlength s + 8)) s (Zlength s) (8 * i + bc) 0 = (zf, pf)).
  { rewrite <- EZ. replace (Z.to_nat (8 * Zlength s + 8)) with (S (Z.to_nat (8 * Zlength s + 7))) by lia.
    rewrite Hq. symmetry. apply nc_zeros_wrap. lia. }
  unfold nc_zeros_stmt. unfold nc_locals, nc_seps.
  assert_PROP (field_compatible (tarray tuchar (Zlength s)) [] (offset_val off base)) as Hfw.
  { entailer!. match goal with H: Zlength (sublist 0 off c) = off,
      H': field_compatible _ _ (offset_val (Zlength (sublist 0 off c)) base) |- _ => rewrite H in H'; exact H' end. }
  assert (Hbp: isptr base) by (destruct Hfw as [Hp _]; destruct base; try contradiction; auto).
  assert (Hwv: forall k, 0 <= k <= Zlength s ->
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) |--
     weak_valid_pointer (offset_val (off + k) base)).
  { intros k Hk. rewrite <- offset_offset_val. apply ncx_wvp_off; auto; lia. }
  assert (HWr: 0 <= nc_win s i bc <= Int.max_unsigned) by (apply nc_win_range; auto; lia).
  forward_call (nc_x (nc_win s i bc), gv).
  { entailer!. unfold nc_x. rewrite Int.repr_unsigned. reflexivity. }
  { apply nc_x_range. }
  forward.
  set (n := Zlength s) in *.
  forward_loop ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in
    (EX F': nat, EX i': Z, EX bc': Z, EX z: Z,
     PROPx [zeros_c F' s n (8 * i' + bc') z = (zf, pf); nc_rd n i' bc';
            nc_mu (8 * n - (8 * i' + bc')) < Z.of_nat F'; 0 <= z; Zlength acc + z <= maxsv + 36]
     (LOCALx (temp _repeats (Vint (Int.repr (ctz (nc_x (nc_win s i' bc')) / 2))) ::
              temp _ip (offset_val (off + i') base) :: temp _bitCount (Vint (Int.repr bc')) ::
              temp _bitStream (Vint (Int.repr (nc_win s i' bc'))) ::
              temp _charnum (Vint (Int.repr (Zlength acc + z))) ::
              temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
              temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x)
  break: ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in
    (EX F': nat, EX i': Z, EX bc': Z, EX z: Z, EX early: bool,
     PROPx [zeros_c F' s n (8 * i' + bc') z = (zf, pf); nc_rd n i' bc';
            nc_mu (8 * n - (8 * i' + bc')) < Z.of_nat F'; 0 <= z; Zlength acc + z <= maxsv + 36;
            if early then 12 <= ctz (nc_x (nc_win s i' bc')) / 2 /\ maxsv + 1 <= Zlength acc + z
            else ctz (nc_x (nc_win s i' bc')) / 2 < 12]
     (LOCALx (temp _repeats (Vint (Int.repr (ctz (nc_x (nc_win s i' bc')) / 2))) ::
              temp _ip (offset_val (off + i') base) :: temp _bitCount (Vint (Int.repr bc')) ::
              temp _bitStream (Vint (Int.repr (nc_win s i' bc'))) ::
              temp _charnum (Vint (Int.repr (Zlength acc + z))) ::
              temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
              temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
  { (* entry *)
    Exists (Z.to_nat (8 * n + 8)) i bc 0.
    destruct (nc_repeats' s i bc Hbytes ltac:(unfold nc_rd; auto)) as (Hct & _).
    rewrite nc_shru by (unfold Int.max_unsigned, Int.modulus; simpl; lia).
    entailer!.
    pose proof (nc_mu_bound (8 * Zlength s - (8 * i + bc)) ltac:(lia)).
    assert ((8 * Zlength s - (8 * i + bc)) / 24 <= 8 * Zlength s) by (apply Z.div_le_upper_bound; lia).
    rewrite Z2Nat.id by lia. split; [unfold nc_rd; lia | lia]. }
  { (* one pass: the test (repeats >= 12 && charnum < maxSV1), then a group of 12 repeats *)
    Intros F' i' bc' z.
    rename H into HZ. rename H0 into Hrd2. rename H1 into Hmu. rename H2 into Hz0. rename H3 into Hzb.
    destruct (nc_repeats' s i' bc' Hbytes Hrd2) as (Hct & Hones & Hge & Hlt).
    set (r := ctz (nc_x (nc_win s i' bc')) / 2) in *.
    assert (Hr0: 0 <= r <= 15) by (unfold r; split; [apply Z.div_pos; lia | change 15 with (31 / 2); apply Z.div_le_mono; lia]).
    set (b5 := andb (12 <=? r) (Zlength acc + z <? maxsv + 1)).
    forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in
     (PROPx [] (LOCALx (temp _t'5 (Vint (Int.repr (if b5 then 1 else 0))) ::
              temp _repeats (Vint (Int.repr r)) ::
              temp _ip (offset_val (off + i') base) :: temp _bitCount (Vint (Int.repr bc')) ::
              temp _bitStream (Vint (Int.repr (nc_win s i' bc'))) ::
              temp _charnum (Vint (Int.repr (Zlength acc + z))) ::
              temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
              temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
    { try (rewrite Int.signed_repr in H by rep_lia).
      forward. unfold nc_locals, nc_seps. entailer!.
      unfold b5. rewrite (proj2 (Z.leb_le 12 r)) by lia. simpl andb.
      try (unfold Int.ltu; rewrite !Int.unsigned_repr by rep_lia).
      destruct (zlt _ _), (Z.ltb_spec (Zlength acc + z) (maxsv + 1)); try lia; reflexivity. }
    { try (rewrite Int.signed_repr in H by rep_lia).
      forward. unfold nc_locals, nc_seps. entailer!.
      unfold b5. rewrite (proj2 (Z.leb_gt 12 r)) by lia. reflexivity. }
    apply semax_if_seq. forward_if.
    2: { (* the loop ends *)
      destruct b5 eqn:Eb5; [simpl in *; exfalso; apply Int.one_not_zero; auto|].
      forward.
      Exists F' i' bc' z (12 <=? r). unfold nc_locals, nc_seps. entailer!.
      destruct (Z.leb_spec 12 r); [|unfold r in *; lia].
      simpl in Eb5. apply Z.ltb_ge in Eb5. unfold r in *; lia. }
    destruct b5 eqn:Eb5; [|simpl in *; contradiction].
    repeat match goal with h: Int.repr 1 <> Int.zero |- _ => clear h | h: 1 <> 0 |- _ => clear h end.
    apply andb_prop in Eb5. destruct Eb5 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    assert (H12: r >= 12) by lia.
    apply Hge in H12. clear Hge Hlt.
    destruct Hrd2 as (Hi2 & Hbc2 & Hcl2).
    set (q := 8 * i' + bc') in *.
    assert (Hq8: q < 8 * n) by lia.
    assert (Hend24: q + 24 <= 8 * n) by (apply nc_reps12_end; auto; lia).
    pose proof (nc_mu_step n q ltac:(lia) ltac:(lia) Hend24) as Hmu2.
    pose proof (nc_mu_bound (8 * n - wrapP n (q + 24))) as Hmu3.
    pose proof (nc_wrapP_range n (q + 24) ltac:(lia) ltac:(lia)) as Hwr.
    destruct F' as [|F1]; [lia|].
    rewrite (nc_zeros_group F1 s n q z (nc_wrapP_small n q Hq8) H12) in HZ.
    destruct F1 as [|F2]; [rewrite Nat2Z.inj_succ in Hmu; lia|].
    rewrite nc_zeros_wrap in HZ by lia.
    destruct (nc_shift_ok n i' bc' ltac:(lia) ltac:(unfold nc_rd; auto)) as [Hrd3 Hsh].
    set (i2 := fst (nc_shift n i' bc')) in *. set (bc2 := snd (nc_shift n i' bc')) in *.
    assert (Hnsh: nc_shift n i' bc' = if i' <=? n - 7 then (i' + 3, bc') else (n - 4, (bc' - 8 * (n - 7 - i')) mod 32))
      by reflexivity.
    forward.
    rewrite mul_repr, add_repr.
    forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in
      (PROPx [] (LOCALx (temp _ip (offset_val (off + i2) base) :: temp _bitCount (Vint (Int.repr bc2)) ::
           temp _charnum (Vint (Int.repr (Zlength acc + z + 3 * 12))) ::
           temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
           temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
        (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
    { rewrite nc_sub_pi by (auto; rep_lia). replace (off + Zlength s - 7) with (off + (Zlength s - 7)) by lia.
      apply ncx_test_order'; auto.
      - sep_apply (Hwv i' ltac:(lia)). ncx_wvp_find.
      - sep_apply (Hwv (n - 7) ltac:(lia)). ncx_wvp_find. }
    { rewrite nc_sub_pi in H by (auto; rep_lia).
      replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in H by lia.
      rewrite (nc_cmp_le (Zlength s)) in H by (auto; lia). simpl in H.
      apply nc_typed_true_b in H. fold n in H.
      assert (Hi3: i2 = i' + 3) by (unfold i2; rewrite Hnsh, H; reflexivity).
      assert (Hb3: bc2 = bc') by (unfold bc2; rewrite Hnsh, H; reflexivity).
      forward. unfold nc_locals, nc_seps. entailer!.
      rewrite Hi3. f_equal. lia. }
    { rewrite nc_sub_pi in H by (auto; rep_lia).
      replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in H by lia.
      rewrite (nc_cmp_le (Zlength s)) in H by (auto; lia). simpl in H.
      apply nc_typed_false_b in H. fold n in H.
      assert (Hi3: i2 = n - 4) by (unfold i2; rewrite Hnsh, H; reflexivity).
      assert (Hb3: bc2 = (bc' - 8 * (n - 7 - i')) mod 32) by (unfold bc2; rewrite Hnsh, H; reflexivity).
      assert (Hd7: n - 7 < i') by (apply Z.leb_gt in H; lia).
      forward.
      { entailer!.
        - destruct base; try contradiction; simpl; auto.
        - rewrite nc_sub_pi by (auto; rep_lia).
          replace (off + Zlength s - 7) with (off + i' + (Zlength s - 7 - i')) by lia.
          rewrite nc_sub_pp_z by (auto; lia). rewrite nc_mul8_cast_z by lia. simpl.
          rewrite Int.signed_repr by rep_lia. rewrite Int64.signed_repr by rep_lia.
          repeat apply andp_right; apply prop_right; try rep_lia.
          destruct base; try contradiction; simpl. destruct (peq b b); [reflexivity | contradiction]. }
      forward. forward.
      unfold nc_locals, nc_seps. entailer!.
      rewrite !nc_sub_pi by (auto; rep_lia).
      replace (off + Zlength s - 7) with (off + i' + (Zlength s - 7 - i')) by lia.
      rewrite nc_sub_pp_z by (auto; lia). rewrite nc_mul8_cast_z by lia.
      split.
      - rewrite Hi3. f_equal. lia.
      - rewrite Hb3. simpl. rewrite sub_repr. change (Int.repr 31) with (Int.repr (2 ^ 5 - 1)).
        rewrite nc_and_mask by lia. reflexivity. }
    destruct Hrd3 as (Hi4 & Hb4 & Hc4).
    forward_call (sh, offset_val off base, s, i2).
    { unfold mem_read_pre. split; [auto|split; [lia|split; [lia|]]].
      unfold bytes_ok in *. apply Forall_sublist. auto. }
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite nc_shru by (try apply nc_le_field_range; auto; lia).
    fold (nc_win s i2 bc2).
    forward_call (nc_x (nc_win s i2 bc2), gv).
    { entailer!. unfold nc_x. rewrite Int.repr_unsigned. reflexivity. }
    { apply nc_x_range. }
    destruct (nc_repeats' s i2 bc2 Hbytes ltac:(unfold nc_rd; auto)) as (Hct2 & _).
    forward.
    Exists (S F2) i2 bc2 (z + 36).
    rewrite nc_shru by (unfold Int.max_unsigned, Int.modulus; simpl; lia).
    assert (HZ2: zeros_c (S F2) s n (8 * i2 + bc2) (z + 36) = (zf, pf)).
    { rewrite Hsh. exact HZ. }
    clear HM EZ EZ0 HZ H12 Hones.
    unfold nc_locals, nc_seps. entailer!.
    rewrite Hsh. change (8 * i' + bc' + 24) with (q + 24). rewrite !Nat2Z.inj_succ in *.
    repeat split; try (unfold nc_rd; tauto); try lia.
    f_equal. f_equal. lia. }
  (* after the repeat loop: the last group, the final 2-bit count *)
  Intros F' i' bc' z early.
  rename H into HZ. rename H0 into Hrd2. rename H1 into Hmu. rename H2 into Hz0. rename H3 into Hzb.
  rename H4 into HRE.
  destruct (nc_repeats' s i' bc' Hbytes Hrd2) as (Hct & Hones & Hge & Hlt).
  set (r := ctz (nc_x (nc_win s i' bc')) / 2) in *.
  assert (Hr0: 0 <= r <= 15) by (unfold r; split; [apply Z.div_pos; lia | change 15 with (31 / 2); apply Z.div_le_mono; lia]).
  destruct Hrd2 as (Hi2 & Hbc2 & Hcl2).
  set (q := 8 * i' + bc') in *.
  assert (Hq8: q < 8 * n) by lia.
  assert (Hctb: ctz (nc_x (nc_win s i' bc')) <= 32 - bc') by (apply (nc_ctz_le s i'); auto; lia).
  assert (H2r: 2 * r <= ctz (nc_x (nc_win s i' bc'))) by (unfold r; pose proof (Z.mul_div_le (ctz (nc_x (nc_win s i' bc'))) 2); lia).
  pose proof (nc_zeros_ge F' s n q z) as Hzge. rewrite HZ in Hzge. simpl fst in Hzge.
  set (accz := acc ++ repeat 0 (Z.to_nat zf)).
  assert (Hlz: Zlength accz = Zlength acc + zf) by (unfold accz; rewrite Zlength_app, Zlength_repeat by lia; reflexivity).
  cbv zeta in HM. fold accz in HM.
  destruct Hcnt as (Hnb & Hthr & Hrem).
  assert (Hpw: 2 ^ (nb - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (Hp0: 2 <= 2 ^ (nb - 1)) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  destruct early.
  { (* the loop stopped at charnum >= maxSV1 (F11): C breaks, remaining <> 1 *)
    destruct HRE as [Hr12 Hmx].
    set (x3 := (nc_win s i' bc' / 2 ^ (2 * r)) mod 2 ^ 2).
    assert (Hx3: 0 <= x3 < 4) by (apply Z.mod_pos_bound; reflexivity).
    forward. rewrite mul_repr, add_repr.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite mul_repr, nc_shru by (try apply nc_win_range; auto; lia).
    forward. rewrite mul_repr, add_repr.
    forward. change (Int.repr 3) with (Int.repr (2 ^ 2 - 1)). rewrite nc_and_mask by lia. fold x3. rewrite add_repr.
    forward. rewrite add_repr.
    apply semax_if_seq. forward_if.
    { forward. unfold nc_brk. Exists accz pf rem i' (bc' + 2 * r + 2) (Zlength acc + z + 3 * r + x3) (nc_arr maxsv acc).
      assert (HR: nc_RES maxsv s = Some (accz, rem, pf))
        by (rewrite <- HM; rewrite Hlz, (proj2 (Z.geb_le _ _)) by lia; reflexivity).
      assert (Hr1: rem <> 1) by lia.
      unfold nc_locals, nc_seps. entailer!. }
    exfalso. lia. }
  (* the scan ended normally *)
  specialize (Hlt HRE). clear Hge.
  pose proof (nc_mu_bound (8 * n - q) ltac:(lia)) as Hmub.
  destruct F' as [|F1]; [simpl in Hmu; lia|].
  rewrite (nc_zeros_last F1 s n q z r (nc_wrapP_small n q Hq8) Hlt HRE) in HZ.
  injection HZ as Hzf Hpf.
  assert (Hfb: (nc_win s i' bc' / 2 ^ (2 * r)) mod 2 ^ 2 = fbits s (q + 2 * r) 2).
  { unfold nc_win, q. apply nc_window2; auto; try lia. }
  assert (Hfb4: 0 <= fbits s (q + 2 * r) 2 < 4) by (rewrite <- Hfb; apply Z.mod_pos_bound; reflexivity).
  assert (Hzf2: 0 <= zf <= maxsv + 36 + 3 * 12 + 3) by (pose proof (Zlength_nonneg acc); lia).
  forward. rewrite mul_repr, add_repr.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite mul_repr, nc_shru by (try apply nc_win_range; auto; lia).
  forward. rewrite mul_repr, add_repr.
  forward. change (Int.repr 3) with (Int.repr (2 ^ 2 - 1)). rewrite nc_and_mask by lia. rewrite Hfb, add_repr.
  forward. rewrite add_repr.
  replace (Zlength acc + z + 3 * r + fbits s (q + 2 * r) 2) with (Zlength acc + zf) by lia.
  apply semax_if_seq. forward_if.
  { (* charnum >= maxSV1: break *)
    forward. unfold nc_brk. Exists accz pf rem i' (bc' + 2 * r + 2) (Zlength acc + zf) (nc_arr maxsv acc).
    assert (HR: nc_RES maxsv s = Some (accz, rem, pf))
      by (rewrite <- HM; rewrite Hlz, (proj2 (Z.geb_le _ _)) by lia; reflexivity).
    assert (HL: 8 * i' + (bc' + 2 * r + 2) = pf /\ 0 <= i' <= Zlength s - 4 /\ 0 <= bc' + 2 * r + 2 <= 47 /\
                (i' < Zlength s - 4 -> bc' + 2 * r + 2 <= 31) /\ Zlength acc + zf = Zlength accz /\
                0 <= Zlength accz <= Int.max_unsigned /\
                (Zlength accz <= maxsv + 1 -> nc_arr maxsv acc = nc_arr maxsv accz)).
    { rewrite Hlz. unfold q in *. pose proof (Zlength_nonneg acc). repeat split; try rep_lia.
      intros Hle. unfold accz. rewrite nc_arr_zeros by lia. reflexivity. }
    clear HM.
    unfold nc_locals, nc_seps. entailer!. }
  match goal with Hx: Zlength acc + zf < maxsv + 1 |- _ => rename Hx into Hlt1 end.
  set (bcA := bc' + 2 * r + 2) in *.
  assert (HbA: 0 <= bcA <= 34) by (unfold bcA; lia).
  assert (HbA2: i' < n - 4 -> bcA <= 31) by (intros; unfold bcA; destruct Hcl2; lia).
  pose proof (nc_reread_ok n i' bcA ltac:(lia) ltac:(lia) ltac:(lia) HbA2) as [Hrd1 Hrr].
  set (ri := fst (nc_reread n i' bcA)) in *. set (rb := snd (nc_reread n i' bcA)) in *.
  set (cnd := orb (i' <=? n - 7) (bcA / 8 <=? n - 4 - i')).
  forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _t'8 (Vint (Int.repr (if cnd then 1 else 0))) ::
     temp _charnum (Vint (Int.repr (Zlength acc + zf))) ::
     temp _bitCount (Vint (Int.repr bcA)) :: temp _ip (offset_val (off + i') base) ::
     temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
     temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
   (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
  { rewrite nc_sub_pi by (auto; rep_lia). replace (off + Zlength s - 7) with (off + (Zlength s - 7)) by lia.
    apply ncx_test_order'; auto.
    - sep_apply (Hwv i' ltac:(lia)). ncx_wvp_find.
    - sep_apply (Hwv (n - 7) ltac:(lia)). ncx_wvp_find. }
  { match goal with Hx: typed_true _ _ |- _ => rename Hx into Hc1 end.
    rewrite nc_sub_pi in Hc1 by (auto; rep_lia).
    replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in Hc1 by lia.
    rewrite (nc_cmp_le (Zlength s)) in Hc1 by (auto; lia). simpl in Hc1.
    apply nc_typed_true_b in Hc1. fold n in Hc1.
    forward. unfold nc_locals, nc_seps. entailer!.
    unfold cnd. rewrite Hc1. reflexivity. }
  { match goal with Hx: typed_false _ _ |- _ => rename Hx into Hc1 end.
    rewrite nc_sub_pi in Hc1 by (auto; rep_lia).
    replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in Hc1 by lia.
    rewrite (nc_cmp_le (Zlength s)) in Hc1 by (auto; lia). simpl in Hc1.
    apply nc_typed_false_b in Hc1. fold n in Hc1.
    forward.
    { entailer!. all: try apply prop_right; try rewrite nc_sub_pi by (auto; rep_lia);
        destruct base; try contradiction; simpl; auto;
        try (destruct (peq b b); [reflexivity | contradiction]). }
    rewrite nc_reread_cond by (auto; lia).
    unfold nc_locals, nc_seps. entailer!.
    unfold cnd. rewrite Hc1. reflexivity. }
  assert (Hnc: nc_reread n i' bcA = if cnd then (i' + bcA / 8, bcA mod 8)
               else (n - 4, (bcA - 8 * (n - 4 - i')) mod 32)) by reflexivity.
  forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _ip (offset_val (off + ri) base) :: temp _bitCount (Vint (Int.repr rb)) ::
     temp _charnum (Vint (Int.repr (Zlength acc + zf))) ::
     temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
     temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
   (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
  { destruct cnd eqn:Ec; [|simpl in *; contradiction].
    assert (Hri: ri = i' + bcA / 8) by (unfold ri; rewrite Hnc; reflexivity).
    assert (Hrb: rb = bcA mod 8) by (unfold rb; rewrite Hnc; reflexivity).
    forward. forward.
    unfold nc_locals, nc_seps. entailer!. split.
    - rewrite nc_add_shr by (auto; lia). rewrite Hri. f_equal. lia.
    - rewrite Hrb. change 7 with (2 ^ 3 - 1). rewrite nc_land_mod by lia. reflexivity. }
  { destruct cnd eqn:Ec; [simpl in *; try lia; exfalso; apply Int.one_not_zero; auto|].
    assert (Hri: ri = n - 4) by (unfold ri; rewrite Hnc; reflexivity).
    assert (Hrb: rb = (bcA - 8 * (n - 4 - i')) mod 32) by (unfold rb; rewrite Hnc; reflexivity).
    assert (Hd7: n - 7 < i') by (unfold cnd in Ec; apply Bool.orb_false_iff in Ec;
      destruct Ec as [E1 _]; apply Z.leb_gt in E1; lia).
    forward.
    { entailer!.
      - destruct base; try contradiction; simpl; auto.
      - rewrite nc_sub_pi by (auto; rep_lia).
        replace (off + Zlength s - 4) with (off + (Zlength s - 4)) by lia.
        rewrite nc_sub_pp2 by (auto; rep_lia). rewrite nc_mul8_cast by lia. simpl.
        rewrite Int.signed_repr by rep_lia. rewrite Int64.signed_repr by rep_lia.
        repeat apply andp_right; apply prop_right; try rep_lia.
        destruct base; try contradiction; simpl. destruct (peq b b); [reflexivity | contradiction]. }
    forward. forward.
    unfold nc_locals, nc_seps. entailer!.
    rewrite !nc_sub_pi by (auto; rep_lia).
    replace (off + Zlength s - 4) with (off + (Zlength s - 4)) by lia.
    rewrite nc_sub_pp2 by (auto; rep_lia). rewrite nc_mul8_cast by lia.
    split.
    - rewrite Hri. reflexivity.
    - rewrite Hrb. simpl. rewrite sub_repr. change (Int.repr 31) with (Int.repr (2 ^ 5 - 1)).
      rewrite nc_and_mask by lia. reflexivity. }
  destruct Hrd1 as (Hri1 & Hrb1 & Hrc1).
  forward_call (sh, offset_val off base, s, ri).
  { unfold mem_read_pre. split; [auto|split; [lia|split; [lia|]]].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite nc_shru by (try apply nc_le_field_range; auto; lia).
  clear EZ EZ0 Hones Hlt.
  unfold nc_ready. Exists f pf rem thr nb accz ri rb.
  unfold nc_locals, nc_seps. rewrite Hlz. entailer!.
  - split; [|split].
    + rewrite <- HM. rewrite Hlz, Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
    + unfold nc_pos, nc_rd. split; [rewrite Hrr; f_equal; unfold bcA, q; lia | lia].
    + unfold nc_cnt_ok. lia.
  - unfold accz. rewrite nc_arr_zeros by lia. apply derives_refl.
Qed.

Transparent zeros_c.

(* one count, the threshold update, the checks and the re-read *)
Lemma nc_count_ok {Espec: OracleKind} gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s :
  nc_ctx shn shm sht sh nn maxsv N off c s ->
  semax nc_Delta (nc_ready gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s) nc_count_stmt
    (nc_ret (nc_inv gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s)
            (nc_brk gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s)).
Proof.
  intros Hctx. destruct Hctx as (SHn & SHm & SHt & Hrd & Hmsv & Hnn & Hn8 & Hbytes & Hoff & Hend & HN & Hlc & Hlog).
  unfold nc_ret, nc_ready. Intros F P rem thr nb acc i bc.
  rename H into HM. rename H0 into Hpos. rename H1 into HF. rename H2 into Hacc. rename H3 into Hcnt.
  destruct Hpos as [Hq (Hi & Hbc & Hcl)]. destruct Hcnt as (Hnb & Hthr & Hrem).
  assert (HW: forall k, 0 <= k <= 16 -> nc_win s i bc mod 2 ^ k = fbits s (8 * i + bc) k).
  { intros k Hk. unfold nc_win. apply nc_window; auto; try lia. }
  assert (HWr: 0 <= nc_win s i bc <= Int.max_unsigned) by (apply nc_win_range; auto; lia).
  assert (Hp1: 2 ^ (nb - 1) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (Hp0: 2 <= 2 ^ (nb - 1)) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  assert (Hpn: (2 ^ nb = 2 * 2 ^ (nb - 1))%Z).
  { replace nb with ((nb - 1) + 1)%Z at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1)%Z with 2%Z. lia. }
  set (q := 8 * i + bc) in *.
  set (mx := 2 * thr - 1 - rem).
  set (low := fbits s q (nb - 1)).
  set (cf := fbits s q nb).
  set (cnt0 := if low <? mx then low else (if cf >=? thr then cf - mx else cf)).
  set (bc1 := if low <? mx then bc + (nb - 1) else bc + nb).
  assert (Hlo: Int.and (Int.repr (nc_win s i bc)) (Int.repr (thr - 1)) = Int.repr low).
  { rewrite Hthr, nc_and_mask by lia. unfold low. rewrite HW by lia. reflexivity. }
  assert (Hhi: Int.and (Int.repr (nc_win s i bc)) (Int.repr (2 * thr - 1)) = Int.repr cf).
  { rewrite Hthr. rewrite <- Hpn, nc_and_mask by lia. unfold cf. rewrite HW by lia. reflexivity. }
  assert (HloZ: Z.land (nc_win s i bc) (2 ^ (nb - 1) - 1) = low).
  { replace (2 ^ (nb - 1) - 1) with (Z.ones (nb - 1)) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. apply HW; lia. }
  assert (HhiZ: Z.land (nc_win s i bc) (2 * 2 ^ (nb - 1) - 1) = cf).
  { replace (2 * 2 ^ (nb - 1) - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. apply HW; lia. }
  assert (Hlow: 0 <= low < 2 ^ (nb - 1)) by (unfold low; rewrite <- HW by lia; apply Z.mod_pos_bound; lia).
  assert (Hcf: 0 <= cf < 2 ^ nb) by (unfold cf; rewrite <- HW by lia; apply Z.mod_pos_bound; lia).
  unfold nc_count_stmt. unfold nc_locals, nc_seps.
  assert_PROP (field_compatible (tarray tuchar (Zlength s)) [] (offset_val off base)) as Hfw.
  { entailer!. match goal with H: Zlength (sublist 0 off c) = off,
      H': field_compatible _ _ (offset_val (Zlength (sublist 0 off c)) base) |- _ => rewrite H in H'; exact H' end. }
  assert (Hbp: isptr base) by (destruct Hfw as [Hp _]; destruct base; try contradiction; auto).
  assert (Hwv: forall k, 0 <= k <= Zlength s ->
     data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) |--
     weak_valid_pointer (offset_val (off + k) base)).
  { intros k Hk. rewrite <- offset_offset_val. apply ncx_wvp_off; auto; lia. }
  forward.
  replace (Int.sub (Int.sub (Int.mul (Int.repr 2) (Int.repr thr)) (Int.repr 1)) (Int.repr rem))
    with (Int.repr mx) by (rewrite mul_repr, !sub_repr; reflexivity).
  forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _count (Vint (Int.repr cnt0)) :: temp _bitCount (Vint (Int.repr bc1)) ::
       temp _max (Vint (Int.repr mx)) :: temp _ip (offset_val (off + i) base) ::
       temp _bitStream (Vint (Int.repr (nc_win s i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
       temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
       temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
  - (* low < max *)
    rewrite Hlo, Int.unsigned_repr in H by rep_lia.
    forward. forward.
    unfold nc_locals, nc_seps. entailer!.
    unfold cnt0, bc1. rewrite (proj2 (Z.ltb_lt _ _) H). rewrite HloZ. split; reflexivity.
  - (* low >= max *)
    rewrite Hlo, Int.unsigned_repr in H by rep_lia.
    forward. rewrite mul_repr, sub_repr, Hhi.
    forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _count (Vint (Int.repr cnt0)) ::
       temp _max (Vint (Int.repr mx)) :: temp _ip (offset_val (off + i) base) :: temp _bitCount (Vint (Int.repr bc)) ::
       temp _bitStream (Vint (Int.repr (nc_win s i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
       temp _remaining (Vint (Int.repr rem)) :: temp _threshold (Vint (Int.repr thr)) ::
       temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
    + forward. unfold nc_locals, nc_seps. entailer!.
      unfold cnt0. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.geb_le _ _)) by lia.
      reflexivity.
    + forward. unfold nc_locals, nc_seps. entailer!.
      unfold cnt0. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia.
      reflexivity.
    + forward. unfold nc_locals, nc_seps. entailer!.
      unfold bc1. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
  - (* the count, the remaining, the store *)
    assert (Hmx: 0 <= mx <= thr - 1) by lia.
    assert (Hc0: 0 <= cnt0 <= rem).
    { unfold cnt0. destruct (Z.ltb_spec low mx); [lia|].
      assert (low <= cf).
      { unfold low, cf. rewrite <- !HW by lia. rewrite Hpn, (Z.mul_comm 2 (2 ^ (nb - 1))).
        rewrite Z.rem_mul_r by lia.
        pose proof (Z.mod_pos_bound (nc_win s i bc / 2 ^ (nb - 1)) 2 ltac:(lia)). nia. }
      destruct (Z.geb_spec cf thr); lia. }
    set (cnt := cnt0 - 1).
    set (rem1 := if cnt >=? 0 then rem - cnt else rem + cnt).
    assert (Hrem1: 1 <= rem1 <= rem) by (unfold rem1; destruct (Z.geb_spec cnt 0); lia).
    unfold nc_locals, nc_seps.
    forward.
    forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _remaining (Vint (Int.repr rem1)) :: temp _count (Vint (Int.repr cnt)) ::
       temp _bitCount (Vint (Int.repr bc1)) ::
       temp _max (Vint (Int.repr mx)) :: temp _ip (offset_val (off + i) base) ::
       temp _bitStream (Vint (Int.repr (nc_win s i bc))) :: temp _charnum (Vint (Int.repr (Zlength acc))) ::
       temp _threshold (Vint (Int.repr thr)) ::
       temp _nbBits (Vint (Int.repr nb)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
     (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv acc))))) in exact x).
    + forward. unfold nc_locals, nc_seps. entailer!. unfold rem1. rewrite (proj2 (Z.geb_le _ _)) by lia.
      try rewrite sub_repr; reflexivity.
    + forward. unfold nc_locals, nc_seps. entailer!. unfold rem1. rewrite Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia.
      try rewrite add_repr; reflexivity.
    + unfold nc_locals, nc_seps. Intros.
      forward. forward. forward.
      { entailer!. }
      rewrite Int.sign_ext_idem by lia. rewrite nc_arr_upd by lia. rewrite add_repr.
      forward.
      rewrite nc_eq_zero by rep_lia.
      set (badd := if low <? mx then nb - 1 else nb).
      assert (Hbc1: bc1 = bc + badd) by (unfold bc1, badd; destruct (low <? mx); lia).
      rewrite (nc_count_eq F s (Zlength s) (maxsv + 1) P rem thr nb acc q mx low cf cnt0 badd cnt rem1)
        in HM by first [exact Hq | reflexivity].
      set (nb2 := if rem1 <? thr then highbit rem1 + 1 else nb).
      set (thr2 := if rem1 <? thr then 2 ^ highbit rem1 else thr).
      assert (Hacc1: Zlength (acc ++ [cnt]) = Zlength acc + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [2 <= rem1] (LOCALx (temp _previous0 (Vint (Int.repr (if cnt =? 0 then 1 else 0))) ::
         temp _charnum (Vint (Int.repr (Zlength acc + 1))) ::
         temp _remaining (Vint (Int.repr rem1)) :: temp _bitCount (Vint (Int.repr bc1)) ::
         temp _ip (offset_val (off + i) base) ::
         temp _threshold (Vint (Int.repr thr2)) ::
         temp _nbBits (Vint (Int.repr nb2)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
       (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv (acc ++ [cnt])))))) in exact x).
      * (* remaining < threshold *)
        apply semax_if_seq. forward_if.
        { (* remaining <= 1: break *)
          forward. unfold nc_brk.
          Exists (acc ++ [cnt]) (q + badd) rem1 i bc1 (Zlength (acc ++ [cnt])) (nc_arr maxsv (acc ++ [cnt])).
          assert (Hbadd: nb - 1 <= badd <= nb) by (unfold badd; destruct (low <? mx); lia).
          assert (HR: nc_RES maxsv s = Some (acc ++ [cnt], rem1, q + badd)).
          { rewrite <- HM. rewrite (proj2 (Z.ltb_lt _ _) H), (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
          assert (HL: 8 * i + bc1 = q + badd /\ 0 <= i <= Zlength s - 4 /\ 0 <= bc1 <= 47 /\
                      (i < Zlength s - 4 -> bc1 <= 31) /\ Zlength (acc ++ [cnt]) = Zlength (acc ++ [cnt]) /\
                      0 <= Zlength (acc ++ [cnt]) <= Int.max_unsigned /\
                      (Zlength (acc ++ [cnt]) <= maxsv + 1 -> nc_arr maxsv (acc ++ [cnt]) = nc_arr maxsv (acc ++ [cnt]))).
          { rewrite Hacc1. pose proof (Zlength_nonneg acc). repeat split; auto; try rep_lia. }
          clear HM.
          unfold nc_locals, nc_seps. rewrite Hacc1 in *. entailer!. }
        assert (Hhb: 1 <= highbit rem1 <= 14 /\ 2 ^ highbit rem1 <= rem1 < 2 * 2 ^ highbit rem1).
        { unfold highbit. pose proof (Z.log2_spec rem1 ltac:(lia)) as [L1 L2].
          rewrite Z.pow_succ_r in L2 by (apply Z.log2_nonneg).
          assert (1 <= Z.log2 rem1) by (change 1 with (Z.log2 2); apply Z.log2_le_mono; lia).
          assert (Z.log2 rem1 <= 14).
          { assert (Z.log2 rem1 < nb - 1); [|lia]. apply Z.log2_lt_pow2; lia. }
          lia. }
        forward_call (rem1, gv).
        forward.
        forward.
        { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
        unfold nc_locals, nc_seps. entailer!.
        unfold thr2, nb2. rewrite (proj2 (Z.ltb_lt _ _) H).
        replace (highbit rem1 + 1 - 1) with (highbit rem1) by lia. rewrite nc_shl1 by lia.
        destruct (cnt =? 0); simpl; auto.
      * (* remaining >= threshold *)
        forward. unfold nc_locals, nc_seps. entailer!.
        unfold thr2, nb2. rewrite (proj2 (Z.ltb_ge _ _)) by lia. destruct (cnt =? 0); simpl; auto.
      * Intros.
        forward_if.
        { (* charnum >= maxSV1: break *)
          forward. unfold nc_brk.
          Exists (acc ++ [cnt]) (q + badd) rem1 i bc1 (Zlength (acc ++ [cnt])) (nc_arr maxsv (acc ++ [cnt])).
          assert (Hbadd: nb - 1 <= badd <= nb) by (unfold badd; destruct (low <? mx); lia).
          assert (HR: nc_RES maxsv s = Some (acc ++ [cnt], rem1, q + badd)).
          { rewrite <- HM. rewrite (proj2 (Z.leb_gt rem1 1)) by lia. rewrite Bool.andb_false_r.
            rewrite Hacc1, (proj2 (Z.geb_le _ _)) by lia. reflexivity. }
          assert (HL: 8 * i + bc1 = q + badd /\ 0 <= i <= Zlength s - 4 /\ 0 <= bc1 <= 47 /\
                      (i < Zlength s - 4 -> bc1 <= 31) /\ Zlength (acc ++ [cnt]) = Zlength (acc ++ [cnt]) /\
                      0 <= Zlength (acc ++ [cnt]) <= Int.max_unsigned /\
                      (Zlength (acc ++ [cnt]) <= maxsv + 1 -> nc_arr maxsv (acc ++ [cnt]) = nc_arr maxsv (acc ++ [cnt]))).
          { rewrite Hacc1. pose proof (Zlength_nonneg acc). repeat split; auto; try rep_lia. }
          clear HM.
          unfold nc_locals, nc_seps. rewrite Hacc1 in *. entailer!. }
        (* the re-read *)
        assert (Hbadd: nb - 1 <= badd <= nb) by (unfold badd; destruct (low <? mx); lia).
        pose proof (nc_reread_ok (Zlength s) i bc1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; destruct Hcl; lia))
          as [Hrd1 Hrr].
        set (ri := fst (nc_reread (Zlength s) i bc1)) in *. set (rb := snd (nc_reread (Zlength s) i bc1)) in *.
        set (cnd := orb (i <=? Zlength s - 7) (bc1 / 8 <=? Zlength s - 4 - i)).
        forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _t'12 (Vint (Int.repr (if cnd then 1 else 0))) ::
           temp _previous0 (Vint (Int.repr (if cnt =? 0 then 1 else 0))) ::
           temp _charnum (Vint (Int.repr (Zlength acc + 1))) ::
           temp _remaining (Vint (Int.repr rem1)) :: temp _bitCount (Vint (Int.repr bc1)) ::
           temp _ip (offset_val (off + i) base) ::
           temp _threshold (Vint (Int.repr thr2)) ::
           temp _nbBits (Vint (Int.repr nb2)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
         (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv (acc ++ [cnt])))))) in exact x).
        { rewrite nc_sub_pi by (auto; rep_lia). replace (off + Zlength s - 7) with (off + (Zlength s - 7)) by lia.
          apply ncx_test_order'; auto.
          - sep_apply (Hwv i ltac:(lia)). ncx_wvp_find.
          - sep_apply (Hwv (Zlength s - 7) ltac:(lia)). ncx_wvp_find. }
        { rewrite nc_sub_pi in H1 by (auto; rep_lia).
          replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in H1 by lia.
          rewrite (nc_cmp_le (Zlength s)) in H1 by (auto; lia). simpl in H1.
          apply nc_typed_true_b in H1.
          forward. unfold nc_locals, nc_seps. entailer!.
          unfold cnd. rewrite H1. reflexivity. }
        { rewrite nc_sub_pi in H1 by (auto; rep_lia).
          replace (off + Zlength s - 7) with (off + (Zlength s - 7)) in H1 by lia.
          rewrite (nc_cmp_le (Zlength s)) in H1 by (auto; lia). simpl in H1.
          apply nc_typed_false_b in H1.
          forward.
          { entailer!. all: try apply prop_right; try rewrite nc_sub_pi by (auto; rep_lia);
              destruct base; try contradiction; simpl; auto;
              try (destruct (peq b b); [reflexivity | contradiction]). }
          rewrite nc_reread_cond by (auto; lia).
          unfold nc_locals, nc_seps. entailer!.
          unfold cnd. rewrite H1. reflexivity. }
        assert (Hnc: nc_reread (Zlength s) i bc1 = if cnd then (i + bc1 / 8, bc1 mod 8)
                     else (Zlength s - 4, (bc1 - 8 * (Zlength s - 4 - i)) mod 32)) by reflexivity.
        forward_if ltac:(let x := eval cbv delta [nc_locals nc_seps] beta in (PROPx [] (LOCALx (temp _ip (offset_val (off + ri) base) :: temp _bitCount (Vint (Int.repr rb)) ::
           temp _previous0 (Vint (Int.repr (if cnt =? 0 then 1 else 0))) ::
           temp _charnum (Vint (Int.repr (Zlength acc + 1))) ::
           temp _remaining (Vint (Int.repr rem1)) ::
           temp _threshold (Vint (Int.repr thr2)) ::
           temp _nbBits (Vint (Int.repr nb2)) :: nc_locals gv pn pm pt base v_buffer maxsv off s)
         (SEPx (nc_seps gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s (nc_arr maxsv (acc ++ [cnt])))))) in exact x).
        { destruct cnd eqn:Ec; [|simpl in *; contradiction].
          assert (Hri: ri = i + bc1 / 8) by (unfold ri; rewrite Hnc; reflexivity).
          assert (Hrb: rb = bc1 mod 8) by (unfold rb; rewrite Hnc; reflexivity).
          forward. forward.
          unfold nc_locals, nc_seps. entailer!. split.
          - rewrite nc_add_shr by (auto; lia). rewrite Hri. f_equal. lia.
          - rewrite Hrb. change 7 with (2 ^ 3 - 1). rewrite nc_land_mod by lia. reflexivity. }
        { destruct cnd eqn:Ec; [simpl in *; try lia; exfalso; apply Int.one_not_zero; auto|].
          assert (Hri: ri = Zlength s - 4) by (unfold ri; rewrite Hnc; reflexivity).
          assert (Hrb: rb = (bc1 - 8 * (Zlength s - 4 - i)) mod 32) by (unfold rb; rewrite Hnc; reflexivity).
          assert (Hd7: Zlength s - 7 < i) by (unfold cnd in Ec; apply Bool.orb_false_iff in Ec;
            destruct Ec as [E1 _]; apply Z.leb_gt in E1; lia).
          forward.
          { entailer!.
            - destruct base; try contradiction; simpl; auto.
            - rewrite nc_sub_pi by (auto; rep_lia).
              replace (off + Zlength s - 4) with (off + (Zlength s - 4)) by lia.
              rewrite nc_sub_pp2 by (auto; rep_lia). rewrite nc_mul8_cast by lia. simpl.
              rewrite Int.signed_repr by rep_lia. rewrite Int64.signed_repr by rep_lia.
              repeat apply andp_right; apply prop_right; try rep_lia.
              destruct base; try contradiction; simpl. destruct (peq b b); [reflexivity | contradiction]. }
          forward. forward.
          unfold nc_locals, nc_seps. entailer!.
          rewrite !nc_sub_pi by (auto; rep_lia).
          replace (off + Zlength s - 4) with (off + (Zlength s - 4)) by lia.
          rewrite nc_sub_pp2 by (auto; rep_lia). rewrite nc_mul8_cast by lia.
          split.
          - rewrite Hri. reflexivity.
          - rewrite Hrb. simpl. rewrite sub_repr. change (Int.repr 31) with (Int.repr (2 ^ 5 - 1)).
            rewrite nc_and_mask by lia. reflexivity. }
        destruct Hrd1 as (Hri1 & Hrb1 & Hrc1).
        forward_call (sh, offset_val off base, s, ri).
        { unfold mem_read_pre. split; [auto|split; [lia|split; [lia|]]].
          unfold bytes_ok in *. apply Forall_sublist. auto. }
        forward.
        { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
        rewrite nc_shru by (try apply nc_le_field_range; auto; lia).
        unfold nc_inv. Exists F (q + badd) rem1 thr2 nb2 (cnt =? 0) (acc ++ [cnt]) ri rb.
        unfold nc_locals, nc_seps. rewrite Hacc1. entailer!.
        split; [|split].
        { rewrite <- HM. rewrite (proj2 (Z.leb_gt rem1 1)) by lia. rewrite Bool.andb_false_r.
          rewrite Hacc1, Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
        { unfold nc_pos, nc_rd. split; [rewrite Hrr; f_equal; lia | lia]. }
        { unfold nc_cnt_ok, thr2, nb2. destruct (Z.ltb_spec rem1 (2 ^ (nb - 1))).
          { destruct (nc_highbit_facts rem1 ltac:(lia)) as [Hh1 Hh2].
            replace (highbit rem1 + 1 - 1) with (highbit rem1) by lia. lia. }
          { lia. } }
Qed.

(* below 8 bytes the body's result is FSE_readNCount's on the zero-padded copy, rejected when longer than s *)
Lemma nc_short_x (s: list Z) (maxsv: Z) : Zlength s < 8 ->
  x_ncount s maxsv =
  match x_ncount (s ++ repeat 0 (Z.to_nat (8 - Zlength s))) maxsv with
  | Some (norm, log, size) => if size >? Zlength s then None else Some (norm, log, size)
  | None => None
  end.
Proof.
  intros H. unfold x_ncount at 1. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite x_ncount_ge8 by (rewrite Zlength_app, Zlength_repeat; lia). reflexivity.
Qed.

Lemma body_ent_ncount :
  semax_body Vprog (G_B0 ++ [FSE_readNCount_spec]) f_FSE_readNCount_body FSE_readNCount_body_spec.
Proof.
  start_function.
  match goal with h: Zlength s <= 2 ^ 63 - 1 |- _ => rename h into Hslen end.
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
  pose proof H1 as Hw. destruct Hw as (Hrd & Hoff & Hend & HN & Hlc & _ & Hbytes & Hsub).
  rewrite (nc_win_split sh N c off s base H1 Hfc).
  set (n := Zlength s) in *.
  Intros.
  forward. forward. forward. forward. forward. forward.
  assert (Hiend: force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val off base)
    (Vlong (Int64.repr n))) = offset_val (off + n) base).
  { destruct base; try (destruct Hfc; contradiction). simpl. unfold sem_add_ptr_long. simpl. f_equal.
    rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_int64. rewrite ptrofs_mul_repr.
    rewrite Int64.unsigned_repr by rep_lia. rewrite ptrofs_add_repr. f_equal. lia. }
  rewrite Hiend. rewrite add_repr.
  assert (Hn0: 0 <= n) by apply Zlength_nonneg.
  forward. apply semax_if_seq. forward_if.
  { (* hbSize < 8: FSE_readNCount on a zero-padded copy *)
    forward. forward. forward. forward. forward. forward. forward. forward.
    rewrite !Int64.unsigned_repr in H2 by rep_lia.
    set (s8 := s ++ repeat 0 (Z.to_nat (8 - n))).
    assert (Hs8: Zlength s8 = 8) by (unfold s8; rewrite Zlength_app, Zlength_repeat; lia).
    assert (Hb8: bytes_ok s8).
    { unfold s8, bytes_ok. apply Forall_app. split; auto. apply Forall_forall. intros x Hx.
      apply repeat_spec in Hx. subst. unfold is_byte. lia. }
    change (upd_Znth 7 _ _) with (map Vbyte (repeat Byte.zero 8)).
    rewrite data_at_tarray_tschar_tuchar.
    assert_PROP (field_compatible (tarray tuchar 8) [] v_buffer) as Hfb by entailer!.
    rewrite (nc_arr_split2 Tsh 8 n) by (auto; rewrite ?Zlength_map; simpl; lia).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar n) (sublist 0 n (map Vubyte (repeat Byte.zero 8))) v_buffer).
    forward_call (sh, Tsh, offset_val off base, v_buffer, existT (fun t => reptype t) (tarray tuchar n) (zbytes s)).
    { cbn [projT1 projT2]. split; [simpl sizeof; rewrite Z.max_r by lia; rep_lia |].
      apply memcpy_ok_zbytes; [reflexivity | assumption]. }
    simpl projT1; simpl projT2.
    gather_SEP (data_at Tsh (tarray tuchar n) _ v_buffer) (data_at Tsh (tarray tuchar (8 - n)) _ _).
    replace (data_at Tsh (tarray tuchar n) (zbytes s) v_buffer *
             data_at Tsh (tarray tuchar (8 - n)) (sublist n 8 (map Vubyte (repeat Byte.zero 8))) (offset_val n v_buffer))
      with (data_at Tsh (tarray tuchar 8) (zbytes s8) v_buffer).
    2: { rewrite (nc_arr_split2 Tsh 8 n) by (auto; try rewrite Zlength_map; lia).
         unfold s8. rewrite map_app, sublist_app1, sublist_app2 by (rewrite ?Zlength_map; lia).
         rewrite !Zlength_map. fold n. rewrite sublist_same by (rewrite ?Zlength_map; lia).
         rewrite Z.sub_diag, sublist_same by (rewrite ?Zlength_map, ?Zlength_repeat; lia).
         f_equal. f_equal. change (map Vubyte (repeat Byte.zero 8)) with (zbytes (repeat 0 8)).
         rewrite sublist_map. f_equal. change (repeat 0 8) with (repeat 0 (Z.to_nat 8)).
         rewrite sublist_repeat by lia. reflexivity. }
    forward_call (gv, shn, pn, nn, shm, pm, sht, pt, maxsv, Tsh, v_buffer, 8, zbytes s8, 0, s8).
    { entailer!. simpl. rewrite Hs8. reflexivity. }
    { unfold win_ok. rewrite Hs8, Zlength_map, Hs8. rewrite sublist_same by (rewrite ?Zlength_map; lia).
      repeat split; auto; try lia. }
    Intros vret. destruct vret as [[r nc] res]. simpl fst in *; simpl snd in *.
    sep_apply (nc_win_join sh N c off s base H1 Hfc).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 8) (zbytes s8) v_buffer).
    rewrite <- (memory_block_data_at__tarray_tuchar_eq Tsh v_buffer 8) by rep_lia.
    rewrite (memory_block_data_at__tarray_tschar_eq Tsh v_buffer 8) by rep_lia.
    assert (Hres: forall x, ncount_res s maxsv = Some x -> read_ncount s8 maxsv = Some x /\ snd x <= n).
    { intros [[norm log] size] Ex. unfold ncount_res in Ex. rewrite (proj2 (Z.ltb_lt _ _)) in Ex by lia.
      fold n s8 in Ex. destruct (read_ncount s8 maxsv) as [[[norm' log'] size']|]; [|discriminate].
      destruct (size' >? n) eqn:Eg; [discriminate|]. injection Ex as <- <- <-.
      split; [reflexivity|]. simpl. rewrite Z.gtb_ltb, Z.ltb_ge in Eg. lia. }
    assert (Hn8: (n <? 8) = true) by (apply Z.ltb_lt; lia).
    forward_call r.
    assert (HxS: x_ncount s maxsv =
      match x_ncount s8 maxsv with
      | Some (norm, log, size) => if size >? n then None else Some (norm, log, size)
      | None => None
      end) by (apply nc_short_x; lia).
    match goal with h: res = x_ncount s8 maxsv |- _ => rewrite <- h in HxS end.
    destruct res as [[[norm log] size]|].
    - destruct H6 as (-> & Hsz & Hok & Hnc). rewrite Hs8 in Hsz.
      assert (He: is_error_code size = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
      rewrite He. forward_if. { exfalso. auto. }
      forward_if.
      + forward. Exists (2 ^ 64 - 20) nc (@None (list Z * Z * Z)). unfold nc_rel; try fold n; rewrite Hn8.
        rewrite (proj2 (Z.gtb_lt _ _)) in HxS by lia. rewrite HxS.
        entailer!. split.
        { intros x Ex. destruct (Hres x Ex) as [Er Hx]. specialize (H5 x Er). inversion H5; subst x.
          simpl in Hx. lia. }
        f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
      + forward. Exists size nc (Some (norm, log, size)). unfold nc_rel; try fold n; rewrite Hn8.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) in HxS by lia. rewrite HxS.
        entailer!. split.
        * intros x Ex. destruct (Hres x Ex) as [Er _]. auto.
        * intros [Hc|Hc]; [lia|]. apply nc_short_vals; auto.
    - forward_if; [|rewrite H6 in H8; discriminate].
      forward. Exists r nc (@None (list Z * Z * Z)). unfold nc_rel; try fold n; rewrite Hn8. rewrite HxS. entailer!.
      intros x Ex. destruct (Hres x Ex) as [Er _]. specialize (H5 x Er). discriminate. }
  (* hbSize >= 8 *)
  rewrite !Int64.unsigned_repr in H2 by rep_lia.
  assert (Hres: ncount_res s maxsv = ncount_c s maxsv)
    by (unfold ncount_res; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
  assert (Hn8: (n <? 8) = false) by (apply Z.ltb_ge; lia).
  assert (Hxr: x_ncount s maxsv = ncount_res s maxsv) by (symmetry; apply ncount_res_x; lia).
  assert_PROP (field_compatible (tarray tshort nn) [] pn) as Hfn by entailer!.
  rewrite (nc_short_split_ shn nn (maxsv + 1) pn) by (auto; lia). Intros.
  forward.
  rewrite (data_at__memory_block shn (tarray tshort (maxsv + 1)) pn). Intros.
  change (sizeof (tarray tshort (maxsv + 1))) with (2 * Z.max 0 (maxsv + 1))%Z. rewrite Z.max_r by lia.
  forward_call (shn, pn, 0, (2 * (maxsv + 1))%Z).
  { entailer!. simpl. rewrite (Z.mul_comm (maxsv + 1) 2). reflexivity. }
  sep_apply (nc_memset_short shn (maxsv + 1) pn); auto; try lia.
  forward_call (sh, offset_val off base, s, 0).
  { unfold mem_read_pre. split; [auto|split; [lia|split; [fold n; lia|]]].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  forward.
  assert (Hw0: forall k, 0 <= k <= 32 -> (le_field s 0 4 / 2 ^ 0) mod 2 ^ k = fbits s 0 k).
  { intros k Hk. apply (nc_window s 0 0 k); auto; lia. }
  assert (Hlog: Int.add (Int.and (Int.repr (le_field s 0 4)) (Int.repr 15)) (Int.repr 5) =
                Int.repr (nc_log s)).
  { change 15 with (2 ^ 4 - 1). rewrite nc_and_mask by lia. rewrite add_repr. f_equal.
    unfold nc_log, FSE_MIN_TABLELOG. rewrite <- Hw0 by lia. rewrite Z.pow_0_r, Z.div_1_r. reflexivity. }
  assert (Hlog0: 0 <= fbits s 0 4 < 16).
  { rewrite <- Hw0 by lia. apply Z.mod_pos_bound. reflexivity. }
  rewrite Hlog.
  forward_if.
  { (* tableLog > 15 *)
    forward.
    assert (Hlg: nc_log s > 15).
    { rewrite Int.signed_repr in H4 by (unfold nc_log, FSE_MIN_TABLELOG; rep_lia). lia. }
    assert (HNone: ncount_res s maxsv = None).
    { rewrite Hres. unfold ncount_c. fold (nc_log s). rewrite (proj2 (Z.gtb_lt _ _)) by (unfold FSE_TABLELOG_ABSOLUTE_MAX; lia).
      reflexivity. }
    Exists (2 ^ 64 - 44) (Zrepeat (Vint (Int.repr 0)) (maxsv + 1) ++ Zrepeat Vundef (nn - (maxsv + 1)))
      (@None (list Z * Z * Z)). unfold nc_rel; try fold n; rewrite Hn8, Hxr, HNone.
    entailer!.
    - split; [list_solve|]. rewrite nc_neg_repr. reflexivity.
    - sep_apply (nc_short_join shn nn (maxsv + 1) (Zrepeat (Vint (Int.repr 0)) (maxsv + 1)) pn);
        auto; try lia; try list_solve.
      sep_apply (nc_win_join sh (Zlength c) c off s base); auto.
      cancel. }
  assert (Hlg: nc_log s <= 15).
  { rewrite Int.signed_repr in H4 by (unfold nc_log, FSE_MIN_TABLELOG; rep_lia). lia. }
  assert (Hlg5: 5 <= nc_log s) by (unfold nc_log, FSE_MIN_TABLELOG; lia).
  assert (Hp2: 32 <= 2 ^ nc_log s <= 2 ^ 15).
  { split; [change 32 with (2 ^ 5) |]; apply Z.pow_le_mono_r; lia. }
  forward. forward. forward.
  forward. { entailer!. rewrite nc_shl1 by lia. rewrite Int.signed_repr by rep_lia. split; [rep_lia | change (Int.unsigned Int.iwordsize) with 32; lia]. }
  forward. { entailer!. change (Int.unsigned Int.iwordsize) with 32; lia. }
  forward.
  forward_loop (nc_inv gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s)
    break: (nc_brk gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s).
  { (* the invariant holds at entry *)
    unfold nc_inv. Exists (Z.to_nat (maxsv + 2)) 4 (2 ^ nc_log s + 1) (2 ^ nc_log s) (nc_log s + 1) false
      (@nil Z) 0 4.
    rewrite nc_shl1 by lia. rewrite add_repr.
    rewrite nc_shru by (try apply nc_le_field_range; auto; lia).
    unfold nc_locals, nc_seps, nc_arr. simpl Zlength. rewrite Z.sub_0_r, Z.add_0_r.
    entailer!.
    - unfold nc_pos, nc_rd, nc_cnt_ok. rewrite nc_wrapP_small by lia. rewrite Zlength_nil.
      replace (nc_log s + 1 - 1) with (nc_log s) by lia. lia.
    - apply derives_refl. }
  { (* one iteration *)
    assert (Hctx: nc_ctx shn shm sht sh nn maxsv N off c s).
    { unfold nc_ctx. refine (conj SH (conj SH0 (conj SH1 (conj Hrd _)))).
      repeat split; auto; try lia. }
    unfold nc_inv. Intros F P rem thr nb prev0 acc i bc.
    destruct F as [|f]; [lia|].
    forward_if (nc_ready gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s).
    - (* previous0: the zero-repeat scan *)
      destruct prev0; [|simpl in *; lia].
      eapply semax_pre; [|eapply semax_post; [| | | | apply (nc_zeros_ok gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s Hctx)]].
      + unfold nc_zpre. Exists f P rem thr nb acc i bc. unfold nc_locals, nc_seps. entailer!.
      + simpl RA_normal. apply ENTAIL_refl.
      + simpl RA_break. apply ENTAIL_refl.
      + simpl RA_continue. apply andp_left2. intro rho. apply FF_left.
      + intros vl. simpl RA_return. apply andp_left2. intro rho. apply FF_left.
    - (* no zero repeats *)
      forward. destruct prev0; [simpl in *; discriminate|].
      unfold nc_ready. Exists f P rem thr nb acc i bc. rewrite nc_loop_unfold in H5.
      unfold nc_locals, nc_seps. entailer!.
    - unfold MORE_COMMANDS, abbreviate.
      apply semax_seq with (Q := nc_inv gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s).
      + eapply semax_post; [| | | | apply (nc_count_ok gv shn shm sht sh pn pm pt base v_buffer nn maxsv N off c s Hctx)].
        * simpl RA_normal. apply ENTAIL_refl.
        * simpl RA_break. apply ENTAIL_refl.
        * simpl RA_continue. apply andp_left2. intro rho. apply FF_left.
        * intros vl. simpl RA_return. apply andp_left2. intro rho. apply FF_left.
      + forward. apply ENTAIL_refl. }
  (* after the loop *)
  unfold nc_brk. Intros acc P rem i bc ch A. unfold nc_locals, nc_seps.
  rename H5 into HR. rename H6 into Hrem. rename H7 into HAl. rename H8 into Hdisj.
  assert (Hc: ncount_c s maxsv = if negb (rem =? 1) then None else if Zlength acc >? maxsv + 1 then None else
     if (P + 7) / 8 >? n then None else Some (acc, nc_log s, (P + 7) / 8)).
  { unfold ncount_c. fold (nc_log s). rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by (unfold FSE_TABLELOG_ABSOLUTE_MAX; lia).
    unfold nc_RES in HR. rewrite HR. reflexivity. }
  rewrite Hc in Hres.
  destruct Hdisj as [(HP & Hi & Hbc & Hlt & Hch & Hacc & HA) | Hr1].
  2: { (* the zero-repeat scan stopped early: remaining != 1 *)
    forward_if.
    { forward. rewrite (proj2 (Z.eqb_neq rem 1)) in Hres by exact Hr1. simpl in Hres.
      nc_err_post Hres 20 A nn maxsv shn pn sh c off s base. }
    match goal with Hx: rem = 1 |- _ => exfalso; exact (Hr1 Hx) end. }
  subst P ch.
  forward_if.
  { (* remaining != 1 *)
    forward. rewrite (proj2 (Z.eqb_neq rem 1)) in Hres by (intro E; subst; contradiction). simpl in Hres.
    nc_err_post Hres 20 A nn maxsv shn pn sh c off s base. }
  match goal with Hx: rem = 1 |- _ => subst rem end. rewrite Z.eqb_refl in Hres. cbn [negb] in Hres.
  forward_if.
  { (* charnum > maxSV1 *)
    forward.
    rewrite (proj2 (Z.gtb_lt _ _)) in Hres by lia.
    nc_err_post Hres 48 A nn maxsv shn pn sh c off s base. }
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) in Hres by lia.
  rewrite HA in * by lia.
  destruct (nc_size_check n i bc) as [Hsz Hsz2]; try lia.
  forward_if.
  { (* bitCount > 32 *)
    forward.
    rewrite Hsz, (proj2 (Z.gtb_lt _ _)) in Hres by lia.
    nc_err_post Hres 20 (nc_arr maxsv acc) nn maxsv shn pn sh c off s base. }
  rewrite Hsz, Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) in Hres by lia.
  rewrite Hsz2 in Hres by lia.
  forward. forward.
  assert (Hb7: 0 <= (bc + 7) / 8 <= 4).
  { split; [apply Z.div_pos; lia|]. change 4 with (39 / 8). apply Z.div_le_mono; lia. }
  assert (Hip: force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val (off + i) base)
     (eval_binop Oshr tint tint (eval_binop Oadd tint tint (Vint (Int.repr bc)) (Vint (Int.repr 7)))
        (Vint (Int.repr 3)))) = offset_val (off + i + (bc + 7) / 8) base).
  { assert (Hsh: Int.shr (Int.add (Int.repr bc) (Int.repr 7)) (Int.repr 3) = Int.repr ((bc + 7) / 8)).
    { rewrite add_repr. unfold Int.shr. rewrite Int.signed_repr by rep_lia.
      rewrite Int.unsigned_repr by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    change (eval_binop Oshr tint tint (eval_binop Oadd tint tint (Vint (Int.repr bc)) (Vint (Int.repr 7)))
        (Vint (Int.repr 3))) with (Vint (Int.shr (Int.add (Int.repr bc) (Int.repr 7)) (Int.repr 3))).
    rewrite Hsh. remember ((bc + 7) / 8) as k.
    destruct base; try (destruct Hfc; contradiction). simpl. f_equal.
    rewrite Ptrofs.add_assoc. f_equal.
    unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr, Z.mul_1_l.
    rewrite ptrofs_add_repr. f_equal; lia. }
  rewrite Hip. rewrite sub_repr.
  forward.
  { entailer!. destruct base; try contradiction. simpl. destruct (peq b b); [reflexivity | contradiction]. }
  Exists (i + (bc + 7) / 8) (nc_arr maxsv acc ++ Zrepeat Vundef (nn - (maxsv + 1))) (ncount_res s maxsv).
  unfold nc_rel; try fold n; rewrite Hn8, Hxr, Hres.
  entailer!.
  - split; [list_solve|]. split.
    + unfold nc_arr. rewrite <- app_assoc. rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
      rewrite sublist_same by (rewrite ?Zlength_map; lia). reflexivity.
    + replace (off + i + (bc + 7) / 8) with (off + (i + (bc + 7) / 8)) by lia.
      apply nc_sub_pp; auto. rep_lia.
  - sep_apply (nc_short_join shn nn (maxsv + 1) (nc_arr maxsv acc) pn); auto; try lia.
    sep_apply (nc_win_join sh (Zlength c) c off s base); auto. cancel.
Qed.
