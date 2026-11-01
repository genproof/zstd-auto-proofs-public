(* Model lemma for group HUF: the C peeks L >= tableLog bits (BIT_lookBitsFast,
   exact: bs_peek, zeros below the end) and indexes a table rescaled to L bits (BRep.hsym); the model
   (Huffman.huf_decode_syms) peeks tableLog bits with BitsFast.bs_peek_s.  They pick the same cell. *)
Require Export Zstd.proof.dec.B.BRep.

Lemma hmp_le_value_range (s: list Z) : bytes_ok s -> 0 <= le_value s.
Proof.
  induction s as [|b s IH]; intros H; cbn [le_value]; [lia|].
  inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb. specialize (IH Hs). lia.
Qed.

Lemma hmp_le_value_skipn (k: nat) (s: list Z) :
  bytes_ok s -> le_value s / 2 ^ (8 * Z.of_nat k) = le_value (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H.
  - replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.div_1_r. reflexivity.
  - destruct s as [|b s]; cbn [le_value skipn].
    + rewrite Zdiv_0_l. reflexivity.
    + inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb.
      rewrite <- (IH s Hs).
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
      assert (0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by lia.
      f_equal. change (2 ^ 8) with 256.
      rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma hmp_le_value_firstn (k: nat) (s: list Z) :
  bytes_ok s -> le_value (firstn k s) = le_value s mod 2 ^ (8 * Z.of_nat k).
Proof.
  revert s; induction k as [|k IH]; intros s H.
  - replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.mod_1_r. reflexivity.
  - destruct s as [|b s]; cbn [le_value firstn].
    + rewrite Zmod_0_l. reflexivity.
    + inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb.
      rewrite (IH s Hs).
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
      assert (0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite Z.rem_mul_r by lia.
      rewrite (Z.add_comm b), (Z.mul_comm 256 (le_value s)), Z_mod_plus_full.
      rewrite (Z.mod_small b 256) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. lia.
Qed.

Lemma hmp_bytes_ok_skipn (k: nat) (s: list Z) : bytes_ok s -> bytes_ok (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H; [exact H|].
  destruct s as [|b s]; [exact H|]. cbn [skipn]. inversion H; subst. auto.
Qed.

(* (a mod (b c)) / b = (a / b) mod c *)
Lemma hmp_mod_div (a b c: Z) : 0 < b -> 0 < c -> (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros Hb Hc. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm b ((a / b) mod c)), Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma hmp_mod_mod_pow (a k n: Z) : 0 <= k <= n -> (a mod 2 ^ n) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros H. replace n with (k + (n - k)) by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (n - k)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma hmp_peek_scale (V pos nb L: Z) :
  0 <= pos -> 0 <= nb <= L -> bs_peek V pos L / 2 ^ (L - nb) = bs_peek V pos nb.
Proof.
  intros Hp Hn. unfold bs_peek.
  assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (L - nb)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_div by lia.
  replace L with (nb + (L - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z.div_mul_cancel_r; lia.
Qed.

Lemma hmp_le_value_window (s: list Z) (q: Z) :
  bytes_ok s -> 0 <= q -> le_value (slice s q 5) = (le_value s / 2 ^ (8 * q)) mod 2 ^ 40.
Proof.
  intros H Hq. unfold slice.
  rewrite hmp_le_value_firstn by (apply hmp_bytes_ok_skipn; exact H).
  rewrite <- hmp_le_value_skipn by exact H.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma hmp_peek_eq (s: list Z) (pos nb: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= 32 -> bs_peek (bs_value s) pos nb = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn. unfold bs_peek_s, bs_peek, bs_value.
  destruct (pos <? 0) eqn:E; [lia|].
  set (V := le_value s).
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  destruct (pos - nb >=? 0) eqn:E2.
  - set (lo := pos - nb).
    assert (Hlo: 0 <= lo) by lia.
    assert (0 < 2 ^ lo) by (apply Z.pow_pos_nonneg; lia).
    replace pos with (lo + nb) by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.div_mul_cancel_r by lia. rewrite hmp_mod_div by lia.
    rewrite hmp_le_value_window by (auto; apply Z.div_pos; lia).
    fold V.
    assert (Hr: 0 <= lo mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (0 < 2 ^ (lo mod 8)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq: 0 <= lo / 8) by (apply Z.div_pos; lia).
    assert (0 < 2 ^ (8 * (lo / 8))) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ 40) with (2 ^ (lo mod 8) * 2 ^ (40 - lo mod 8))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite hmp_mod_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite hmp_mod_mod_pow by lia.
    rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia.
    rewrite <- (Z_div_mod_eq_full lo 8). reflexivity.
  - assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 2 ^ (- (pos - nb))) by (apply Z.pow_pos_nonneg; lia).
    replace nb with (pos + - (pos - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.mul_assoc, (Z.mul_comm _ (2 ^ pos)), <- Z.mul_assoc, (Z.mul_comm (2 ^ pos)), Z.div_mul by lia.
    f_equal. unfold slice. replace (Z.to_nat 0) with O by reflexivity. cbn [skipn].
    rewrite hmp_le_value_firstn by exact Hs.
    replace (8 * Z.of_nat (Z.to_nat 5)) with 40 by reflexivity.
    rewrite hmp_mod_mod_pow by lia. reflexivity.
Qed.

Lemma bs_peek_div (s: list Z) (pos nb L: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= L -> L <= 32 ->
  bs_peek (bs_value s) pos L / 2 ^ (L - nb) = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn HL. rewrite hmp_peek_scale by lia. apply hmp_peek_eq; auto; lia.
Qed.

Lemma hsym_peek (ht: huf_table) (s: list Z) (L pos: Z) :
  0 <= ht_log ht <= L -> L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  hsym ht L (bs_peek (bs_value s) pos L) = nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0).
Proof.
  intros Hl HL Hs Hp. unfold hsym. unfold HUF_TABLELOG_MAX in HL.
  rewrite bs_peek_div by (auto; lia). reflexivity.
Qed.
