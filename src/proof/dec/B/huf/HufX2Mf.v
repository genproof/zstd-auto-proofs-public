(* X2T model: the fill region by region, and the cells
   (HufX2M.x2_fill), from x2_count and x2_layout. *)
Require Import Zstd.proof.dec.B.huf.HufX2M.
Local Open Scope Z_scope.

(* ---------- lists ---------- *)

Lemma x2f_Znth_map_seq0 {A} {d: Inhabitant A} (f: nat -> A) (n: nat) (j: Z) :
  0 <= j < Z.of_nat n -> Znth j (map f (seq 0 n)) = f (Z.to_nat j).
Proof.
  intros Hj. unfold Znth. destruct (Z_lt_dec j 0); [lia|].
  rewrite nth_indep with (d' := f 0%nat) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma x2f_Zlength_map_seq0 {A} (f: nat -> A) (n: nat) : Zlength (map f (seq 0 n)) = Z.of_nat n.
Proof. rewrite Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma x2f_Zlength_flat_rep {A} (g: Z -> A) (syms: list Z) (len: Z) : 0 <= len ->
  Zlength (flat_map (fun s => repeat (g s) (Z.to_nat len)) syms) = Zlength syms * len.
Proof.
  intros Hl. induction syms as [|a t IH]; simpl flat_map.
  - rewrite !Zlength_nil; lia.
  - rewrite Zlength_app, Zlength_repeat, IH, Zlength_cons by lia. lia.
Qed.

Lemma x2f_Znth_flat_rep {A} {d: Inhabitant A} (g: Z -> A) (syms: list Z) (len j: Z) : 0 < len ->
  0 <= j < Zlength syms * len ->
  Znth j (flat_map (fun s => repeat (g s) (Z.to_nat len)) syms) = g (Znth (j / len) syms).
Proof.
  intros Hl. revert j. induction syms as [|a t IH]; intros j Hj; simpl flat_map.
  - rewrite Zlength_nil in Hj; lia.
  - rewrite Zlength_cons in Hj.
    destruct (zlt j len).
    + rewrite Znth_app1 by (rewrite Zlength_repeat; lia).
      rewrite Znth_repeat' by (rewrite Z2Nat.id; lia).
      rewrite Z.div_small by lia. rewrite Znth_0_cons. reflexivity.
    + rewrite Znth_app2 by (rewrite Zlength_repeat; lia).
      rewrite Zlength_repeat by lia. rewrite IH by nia.
      assert (Hq: 1 <= j / len) by (apply Z.div_le_lower_bound; lia).
      rewrite Znth_pos_cons by lia. f_equal. f_equal.
      replace j with ((j - len) + 1 * len) at 2 by ring. rewrite Z.div_add by lia. lia.
Qed.

Lemma x2f_divmod (j len cnt: Z) : 0 < len -> 0 <= j < cnt * len ->
  0 <= j / len < cnt /\ 0 <= j mod len < len /\ j = j / len * len + j mod len.
Proof.
  intros Hl Hj. split; [split|split].
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
  - apply Z.mod_pos_bound; lia.
  - pose proof (Z_div_mod_eq_full j len). lia.
Qed.

Lemma x2f_deltu1 s nb bs : deltu s nb bs 1 = s + 65536 * nb + 16777216.
Proof. unfold deltu. rewrite Z.eqb_refl. ring. Qed.

Lemma x2f_deltu2 s nb bs : deltu s nb bs 2 = bs + 256 * s + 65536 * nb + 33554432.
Proof. unfold deltu. replace (2 =? 1) with false by reflexivity. ring. Qed.

(* ---------- the table ---------- *)

Section Fill.
Context (HC : x2_count) (HL : x2_layout) (ht: huf_table) (L: Z)
  (Hht : x2_ht_ok ht) (HLr : ht_log ht <= L <= HUF_TABLELOG_MAX).

Lemma x2f_T : 1 <= ht_log ht <= 12.
Proof. destruct Hht as [[H _] _]. unfold HUF_TABLELOG_MAX in H. lia. Qed.

Lemma x2f_mw : 1 <= maxw ht <= ht_log ht /\ 0 < cntw ht (maxw ht).
Proof. destruct (xc_maxw HC ht Hht) as (? & ? & _). auto. Qed.

Lemma x2f_cnt w : 0 <= cntw ht w.
Proof. unfold cntw. apply Zlength_nonneg. Qed.

Lemma x2f_rv0_1 : rv0 ht L 1 = 0.
Proof. apply (xl_rv0 HL ht L 1 Hht); lia. Qed.

Lemma x2f_step w : 1 <= w -> rv0 ht L (w + 1) = rv0 ht L w + cntw ht w * 2 ^ (L - nbw ht w).
Proof. intros. apply (xl_rv0 HL ht L w Hht); lia. Qed.

Lemma x2f_top : rv0 ht L (maxw ht + 1) = 2 ^ L.
Proof. apply (xl_rv0 HL ht L 1 Hht); lia. Qed.

Lemma x2f_lenw w : 1 <= w -> 0 < 2 ^ (L - nbw ht w).
Proof. intros. pose proof x2f_T. unfold nbw. apply Z.pow_pos_nonneg; lia. Qed.

Lemma x2f_mono w1 w2 : 1 <= w1 <= w2 -> rv0 ht L w1 <= rv0 ht L w2.
Proof.
  intros H. replace w2 with (w1 + Z.of_nat (Z.to_nat (w2 - w1))) by lia.
  induction (Z.to_nat (w2 - w1)) as [|n IH].
  - rewrite Z.add_0_r. lia.
  - replace (w1 + Z.of_nat (S n)) with (w1 + Z.of_nat n + 1) by lia.
    rewrite x2f_step by lia.
    pose proof (x2f_cnt (w1 + Z.of_nat n)). pose proof (Z.pow_nonneg 2 (L - nbw ht (w1 + Z.of_nat n))).
    nia.
Qed.

Lemma x2f_nonneg w : 1 <= w -> 0 <= rv0 ht L w.
Proof. intros. rewrite <- x2f_rv0_1. apply x2f_mono. lia. Qed.

Lemma x2f_le_top w : 1 <= w <= maxw ht + 1 -> rv0 ht L w <= 2 ^ L.
Proof. intros. rewrite <- x2f_top. apply x2f_mono. lia. Qed.

Lemma x2f_lt_top w : 1 <= w <= maxw ht -> rv0 ht L w < 2 ^ L.
Proof.
  intros. destruct x2f_mw as [? ?].
  pose proof (x2f_mono w (maxw ht) ltac:(lia)).
  pose proof (x2f_step (maxw ht) ltac:(lia)). rewrite x2f_top in *.
  pose proof (x2f_lenw (maxw ht) ltac:(lia)). nia.
Qed.

Lemma x2f_cover_aux (n: nat) : forall x, 0 <= x < rv0 ht L (Z.of_nat n + 1) ->
  exists w, 1 <= w <= Z.of_nat n /\ rv0 ht L w <= x < rv0 ht L (w + 1).
Proof.
  induction n as [|n IH]; intros x Hx.
  - change (Z.of_nat 0 + 1) with 1 in Hx. rewrite x2f_rv0_1 in Hx. lia.
  - destruct (zlt x (rv0 ht L (Z.of_nat n + 1))).
    + destruct (IH x) as (w & ? & ?); [lia|]. exists w; lia.
    + exists (Z.of_nat n + 1).
      replace (Z.of_nat (S n) + 1) with (Z.of_nat n + 1 + 1) in Hx by lia. lia.
Qed.

Lemma x2f_cover x : 0 <= x < 2 ^ L ->
  exists w k i, 1 <= w <= maxw ht /\ 0 <= k < cntw ht w /\ 0 <= i < 2 ^ (L - nbw ht w) /\
    x = rv0 ht L w + k * 2 ^ (L - nbw ht w) + i.
Proof.
  intros Hx. destruct x2f_mw as [? ?].
  rewrite <- x2f_top in Hx.
  replace (maxw ht + 1) with (Z.of_nat (Z.to_nat (maxw ht)) + 1) in Hx by lia.
  destruct (x2f_cover_aux _ x Hx) as (w & Hw & Hr).
  rewrite Z2Nat.id in Hw by lia.
  rewrite x2f_step in Hr by lia.
  pose proof (x2f_lenw w ltac:(lia)).
  destruct (x2f_divmod (x - rv0 ht L w) (2 ^ (L - nbw ht w)) (cntw ht w)) as (? & ? & ?); [lia|lia|].
  exists w, ((x - rv0 ht L w) / 2 ^ (L - nbw ht w)), ((x - rv0 ht L w) mod 2 ^ (L - nbw ht w)).
  split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma x2f_sym w k : 1 <= w <= maxw ht -> 0 <= k < cntw ht w -> 0 <= Znth k (symsw ht w) < 256.
Proof.
  intros Hw Hk. destruct (xc_symsw HC ht w Hht Hw) as (Hz & Hf & _).
  apply (proj1 (Forall_Znth _ _) Hf k). lia.
Qed.

Lemma x2f_hsym x : 0 <= x < 2 ^ L ->
  exists w s, 1 <= w <= maxw ht /\ rv0 ht L w <= x < rv0 ht L (w + 1) /\ 0 <= s < 256 /\
    hsym ht L x = (s, nbw ht w).
Proof.
  intros Hx. destruct (x2f_cover x Hx) as (w & k & i & Hw & Hk & Hi & ->).
  exists w, (Znth k (symsw ht w)). split; [lia|]. split; [|split].
  - rewrite x2f_step by lia. pose proof (x2f_lenw w ltac:(lia)). nia.
  - apply x2f_sym; lia.
  - apply (xl_layout HL); auto; lia.
Qed.

Lemma x2f_below x w' : 0 <= x < rv0 ht L w' -> 1 <= w' <= maxw ht + 1 ->
  exists w s, 1 <= w < w' /\ hsym ht L x = (s, nbw ht w).
Proof.
  intros Hx Hw'. pose proof (x2f_le_top w' Hw').
  destruct (x2f_hsym x ltac:(lia)) as (w & s & Hw & Hr & _ & Hs).
  exists w, s. split; [|auto]. split; [lia|].
  destruct (zlt w w'); auto. pose proof (x2f_mono w' w ltac:(lia)). lia.
Qed.

Lemma x2f_Zlength_x2 : Zlength (x2_u32s ht L) = 2 ^ L.
Proof. unfold x2_u32s. rewrite x2f_Zlength_map_seq0, Z2Nat.id; [lia|]. apply Z.pow_nonneg; lia. Qed.

Lemma x2f_Znth_x2 v : 0 <= v < 2 ^ L -> Znth v (x2_u32s ht L) = Vint (Int.repr (x2_elt ht L v)).
Proof.
  intros. unfold x2_u32s. rewrite x2f_Znth_map_seq0 by (rewrite Z2Nat.id; lia).
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma x2f_Zlength_lvl2 s1 n1 : Zlength (lvl2_u32s ht L s1 n1) = 2 ^ (L - n1).
Proof. unfold lvl2_u32s. rewrite x2f_Zlength_map_seq0, Z2Nat.id; [lia|]. apply Z.pow_nonneg; lia. Qed.

Lemma x2f_Znth_lvl2 s1 n1 j : 0 <= j < 2 ^ (L - n1) ->
  Znth j (lvl2_u32s ht L s1 n1) = Vint (Int.repr (x2_cellu ht L s1 n1 (j * 2 ^ n1))).
Proof.
  intros. unfold lvl2_u32s. rewrite x2f_Znth_map_seq0 by (rewrite Z2Nat.id; lia).
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma x2f_elt v s1 n1 : hsym ht L v = (s1, n1) -> x2_elt ht L v = x2_cellu ht L s1 n1 ((v * 2 ^ n1) mod 2 ^ L).
Proof. intros H. unfold x2_elt. rewrite H. reflexivity. Qed.

Lemma x2f_cellu_double s1 n1 x s2 n2 : hsym ht L x = (s2, n2) -> n1 + n2 <= L ->
  x2_cellu ht L s1 n1 x = deltu s2 (n1 + n2) s1 2.
Proof.
  intros H Hn. unfold x2_cellu. rewrite H. cbv beta iota.
  destruct (Z.leb_spec (n1 + n2) L); [reflexivity|lia].
Qed.

Lemma x2f_cellu_single s1 n1 x s2 n2 : hsym ht L x = (s2, n2) -> L < n1 + n2 ->
  x2_cellu ht L s1 n1 x = deltu s1 n1 0 1.
Proof.
  intros H Hn. unfold x2_cellu. rewrite H. cbv beta iota.
  destruct (Z.leb_spec (n1 + n2) L); [lia|reflexivity].
Qed.

(* every code is at least minbits long *)
Lemma x2f_cellu_short s1 n1 x : 0 <= x < 2 ^ L -> L < n1 + minbits ht ->
  x2_cellu ht L s1 n1 x = deltu s1 n1 0 1.
Proof.
  intros Hx Hn. destruct (x2f_hsym x Hx) as (w & s & Hw & _ & _ & Hs).
  apply (x2f_cellu_single _ _ _ _ _ Hs). unfold minbits, nbw in *. lia.
Qed.

Lemma x2f_single w : 1 <= w <= maxw ht -> L - nbw ht w < minbits ht ->
  sublist (rv0 ht L w) (rv0 ht L (w + 1)) (x2_u32s ht L) = fw_u32s (symsw ht w) (nbw ht w) 0 1 (2 ^ (L - nbw ht w)).
Proof.
  intros Hw Hm. pose proof x2f_T. destruct x2f_mw as [? ?].
  pose proof (x2f_lenw w ltac:(lia)) as Hlen.
  pose proof (x2f_step w ltac:(lia)) as Hst.
  pose proof (x2f_nonneg w ltac:(lia)). pose proof (x2f_le_top (w + 1) ltac:(lia)).
  pose proof (x2f_cnt w).
  destruct (xc_symsw HC ht w Hht Hw) as (Hz & _ & _).
  assert (Hsl: Zlength (sublist (rv0 ht L w) (rv0 ht L (w + 1)) (x2_u32s ht L)) = cntw ht w * 2 ^ (L - nbw ht w))
    by (rewrite Zlength_sublist by (rewrite ?x2f_Zlength_x2; nia); lia).
  apply Znth_eq_ext.
  - rewrite Hsl. unfold fw_u32s. rewrite x2f_Zlength_flat_rep by lia. rewrite Hz. lia.
  - intros j Hj. rewrite Hsl in Hj.
    rewrite Znth_sublist by nia. rewrite x2f_Znth_x2 by nia.
    unfold fw_u32s. rewrite x2f_Znth_flat_rep by (rewrite ?Hz; lia).
    destruct (x2f_divmod j _ _ Hlen Hj) as (Hk & Hi & Hji).
    assert (Hs: hsym ht L (j + rv0 ht L w) = (Znth (j / 2 ^ (L - nbw ht w)) (symsw ht w), nbw ht w)).
    { rewrite Hji at 1.
      replace (j / 2 ^ (L - nbw ht w) * 2 ^ (L - nbw ht w) + j mod 2 ^ (L - nbw ht w) + rv0 ht L w)
        with (rv0 ht L w + j / 2 ^ (L - nbw ht w) * 2 ^ (L - nbw ht w) + j mod 2 ^ (L - nbw ht w)) by ring.
      apply (xl_layout HL); auto; lia. }
    rewrite (x2f_elt _ _ _ Hs). f_equal. f_equal.
    apply x2f_cellu_short; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | lia].
Qed.

Lemma x2f_double w k : 1 <= w <= maxw ht -> minbits ht <= L - nbw ht w -> 0 <= k < cntw ht w ->
  sublist (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) (x2_u32s ht L) =
  lvl2_u32s ht L (Znth k (symsw ht w)) (nbw ht w).
Proof.
  intros Hw Hm Hk. pose proof x2f_T. destruct x2f_mw as [? ?].
  pose proof (x2f_lenw w ltac:(lia)) as Hlen.
  pose proof (x2f_step w ltac:(lia)) as Hst.
  pose proof (x2f_nonneg w ltac:(lia)). pose proof (x2f_le_top (w + 1) ltac:(lia)).
  assert (Hsl: Zlength (sublist (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w))
                 (x2_u32s ht L)) = 2 ^ (L - nbw ht w))
    by (rewrite Zlength_sublist by (rewrite ?x2f_Zlength_x2; nia); lia).
  assert (H2L: 2 ^ L = 2 ^ (L - nbw ht w) * 2 ^ nbw ht w).
  { rewrite <- Z.pow_add_r by (unfold nbw; lia). f_equal. lia. }
  pose proof (xl_aligned HL ht L w Hht ltac:(lia) Hw) as Hal.
  apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq].
  apply Znth_eq_ext.
  - rewrite Hsl, x2f_Zlength_lvl2. reflexivity.
  - intros j Hj. rewrite Hsl in Hj.
    rewrite Znth_sublist by nia. rewrite x2f_Znth_x2 by nia.
    rewrite x2f_Znth_lvl2 by lia.
    assert (Hs: hsym ht L (j + (rv0 ht L w + k * 2 ^ (L - nbw ht w))) = (Znth k (symsw ht w), nbw ht w)).
    { replace (j + (rv0 ht L w + k * 2 ^ (L - nbw ht w))) with (rv0 ht L w + k * 2 ^ (L - nbw ht w) + j) by ring.
      apply (xl_layout HL); auto; lia. }
    rewrite (x2f_elt _ _ _ Hs). f_equal. f_equal. f_equal.
    rewrite Hq, H2L.
    replace ((j + (q * 2 ^ (L - nbw ht w) + k * 2 ^ (L - nbw ht w))) * 2 ^ nbw ht w)
      with (j * 2 ^ nbw ht w + (q + k) * (2 ^ (L - nbw ht w) * 2 ^ nbw ht w)) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small.
    assert (0 < 2 ^ nbw ht w) by (apply Z.pow_pos_nonneg; unfold nbw; lia). nia.
Qed.

Lemma x2f_skip s1 n1 : minbits ht <= n1 <= L - minbits ht -> 1 < Z.max 1 (n1 + ht_log ht + 1 - L) ->
    0 <= rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1 < 2 ^ (L - n1) /\
    sublist 0 (rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1) (lvl2_u32s ht L s1 n1) =
    repeat (Vint (Int.repr (deltu s1 n1 0 1))) (Z.to_nat (rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1)).
Proof.
  intros Hn Hmw. pose proof x2f_T. destruct x2f_mw as [? ?].
  assert (Emw: Z.max 1 (n1 + ht_log ht + 1 - L) = n1 + ht_log ht + 1 - L) by lia.
  rewrite Emw in *. unfold minbits in Hn.
  set (mw := n1 + ht_log ht + 1 - L) in *.
  assert (H2L: 2 ^ L = 2 ^ (L - n1) * 2 ^ n1).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (HP: 0 < 2 ^ n1) by (apply Z.pow_pos_nonneg; lia).
  pose proof (x2f_lt_top mw ltac:(lia)). pose proof (x2f_nonneg mw ltac:(lia)).
  assert (HB: 0 <= rv0 ht L mw / 2 ^ n1 < 2 ^ (L - n1)).
  { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  split; [exact HB|].
  apply Znth_eq_ext.
  - rewrite Zlength_sublist by (rewrite ?x2f_Zlength_lvl2; lia). rewrite Zlength_repeat; lia.
  - intros j Hj. rewrite Zlength_sublist in Hj by (rewrite ?x2f_Zlength_lvl2; lia).
    rewrite Znth_sublist by lia. rewrite x2f_Znth_lvl2 by lia.
    rewrite Znth_repeat' by (rewrite Z2Nat.id; lia).
    assert (Hx: (j + 0) * 2 ^ n1 < rv0 ht L mw).
    { pose proof (Z.mul_div_le (rv0 ht L mw) (2 ^ n1) HP). nia. }
    destruct (x2f_below ((j + 0) * 2 ^ n1) mw ltac:(nia) ltac:(lia)) as (w2 & s2 & Hw2 & Hs2).
    f_equal. f_equal. apply (x2f_cellu_single _ _ _ _ _ Hs2). unfold nbw. lia.
Qed.

Lemma x2f_weight s1 n1 w : minbits ht <= n1 <= L - minbits ht -> Z.max 1 (n1 + ht_log ht + 1 - L) <= w <= maxw ht ->
    0 <= L - n1 - nbw ht w /\
    rv0 ht L (w + 1) / 2 ^ n1 = rv0 ht L w / 2 ^ n1 + cntw ht w * 2 ^ (L - n1 - nbw ht w) /\
    sublist (rv0 ht L w / 2 ^ n1) (rv0 ht L (w + 1) / 2 ^ n1) (lvl2_u32s ht L s1 n1) =
    fw_u32s (symsw ht w) (n1 + nbw ht w) s1 2 (2 ^ (L - n1 - nbw ht w)).
Proof.
  intros Hn Hw. pose proof x2f_T. destruct x2f_mw as [? ?].
  assert (Hw1: 1 <= w /\ n1 + ht_log ht + 1 - L <= w <= maxw ht) by lia.
  unfold minbits in Hn.
  assert (Hd: 0 <= L - n1 - nbw ht w) by (unfold nbw; lia).
  split; [exact Hd|].
  assert (HP: 0 < 2 ^ n1) by (apply Z.pow_pos_nonneg; lia).
  assert (Hl2: 0 < 2 ^ (L - n1 - nbw ht w)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hlw: 2 ^ (L - nbw ht w) = 2 ^ (L - n1 - nbw ht w) * 2 ^ n1).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (H2L: 2 ^ L = 2 ^ (L - n1) * 2 ^ n1).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  pose proof (x2f_step w ltac:(lia)) as Hst. rewrite Hlw in Hst.
  pose proof (xl_aligned HL ht L w Hht ltac:(lia) ltac:(lia)) as Hal.
  apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. rewrite Hlw in Hq.
  assert (HA: rv0 ht L w / 2 ^ n1 = q * 2 ^ (L - n1 - nbw ht w)).
  { rewrite Hq. rewrite Z.mul_assoc. apply Z.div_mul. lia. }
  assert (HA1: rv0 ht L (w + 1) / 2 ^ n1 = q * 2 ^ (L - n1 - nbw ht w) + cntw ht w * 2 ^ (L - n1 - nbw ht w)).
  { rewrite Hst, Hq.
    replace (q * (2 ^ (L - n1 - nbw ht w) * 2 ^ n1) + cntw ht w * (2 ^ (L - n1 - nbw ht w) * 2 ^ n1))
      with ((q * 2 ^ (L - n1 - nbw ht w) + cntw ht w * 2 ^ (L - n1 - nbw ht w)) * 2 ^ n1) by ring.
    apply Z.div_mul. lia. }
  split; [rewrite HA, HA1; reflexivity|].
  pose proof (x2f_le_top (w + 1) ltac:(lia)) as Htop.
  assert (HB: q * 2 ^ (L - n1 - nbw ht w) + cntw ht w * 2 ^ (L - n1 - nbw ht w) <= 2 ^ (L - n1)).
  { rewrite <- HA1. apply Z.div_le_upper_bound; lia. }
  pose proof (x2f_nonneg w ltac:(lia)). pose proof (x2f_cnt w).
  assert (Hq0: 0 <= q * 2 ^ (L - n1 - nbw ht w)) by (rewrite <- HA; apply Z.div_pos; lia).
  destruct (xc_symsw HC ht w Hht ltac:(lia)) as (Hz & _ & _).
  rewrite HA, HA1.
  apply Znth_eq_ext.
  - rewrite Zlength_sublist by (rewrite ?x2f_Zlength_lvl2; lia).
    unfold fw_u32s. rewrite x2f_Zlength_flat_rep by lia. rewrite Hz. lia.
  - intros j Hj. rewrite Zlength_sublist in Hj by (rewrite ?x2f_Zlength_lvl2; lia).
    replace (q * 2 ^ (L - n1 - nbw ht w) + cntw ht w * 2 ^ (L - n1 - nbw ht w) - q * 2 ^ (L - n1 - nbw ht w))
      with (cntw ht w * 2 ^ (L - n1 - nbw ht w)) in Hj by ring.
    rewrite Znth_sublist by lia. rewrite x2f_Znth_lvl2 by lia.
    unfold fw_u32s. rewrite x2f_Znth_flat_rep by (rewrite ?Hz; lia).
    destruct (x2f_divmod j _ _ Hl2 Hj) as (Hk & Hi & Hji).
    assert (Hs: hsym ht L ((j + q * 2 ^ (L - n1 - nbw ht w)) * 2 ^ n1) =
                (Znth (j / 2 ^ (L - n1 - nbw ht w)) (symsw ht w), nbw ht w)).
    { replace ((j + q * 2 ^ (L - n1 - nbw ht w)) * 2 ^ n1) with
        (rv0 ht L w + j / 2 ^ (L - n1 - nbw ht w) * 2 ^ (L - nbw ht w) + j mod 2 ^ (L - n1 - nbw ht w) * 2 ^ n1)
        by (rewrite Hq, Hlw; set (a := j / 2 ^ (L - n1 - nbw ht w)) in *;
            set (b := j mod 2 ^ (L - n1 - nbw ht w)) in *; rewrite Hji; ring).
      apply (xl_layout HL); auto; try lia. rewrite Hlw. nia. }
    f_equal. f_equal. apply (x2f_cellu_double _ _ _ _ _ Hs). unfold nbw in *. lia.
Qed.

Lemma x2f_cell v : 0 <= v < 2 ^ L ->
  0 <= x2_elt ht L v < 16777216 * 3 /\ x2_cell_ok ht L v (x2_cell ht L v).
Proof.
  intros Hv. pose proof x2f_T. destruct x2f_mw as [? ?].
  destruct (x2f_hsym v Hv) as (w1 & s1 & Hw1 & _ & Hs1r & Hs1).
  assert (Hx: 0 <= (v * 2 ^ nbw ht w1) mod 2 ^ L < 2 ^ L)
    by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (x2f_hsym _ Hx) as (w2 & s2 & Hw2 & _ & Hs2r & Hs2).
  pose proof (x2f_elt _ _ _ Hs1) as He.
  unfold x2_cell_ok, x2_cell. rewrite Hs1. cbv beta iota. rewrite Hs2. cbv beta iota.
  unfold HUF_TABLELOG_MAX in HLr.
  destruct (Z.le_gt_cases (nbw ht w1 + nbw ht w2) L) as [Hle|Hgt].
  - rewrite (x2f_cellu_double _ _ _ _ _ Hs2 Hle) in He. rewrite x2f_deltu2 in He.
    unfold nbw in *. rewrite He. split; [lia|]. right. split; [lia|].
    set (n := ht_log ht + 1 - w1 + (ht_log ht + 1 - w2)) in *.
    assert (E1: (s1 + 256 * s2 + 65536 * n + 33554432) mod 65536 = s1 + 256 * s2)
      by (symmetry; apply Z.mod_unique with (q := n + 512); lia).
    assert (E2: (s1 + 256 * s2 + 65536 * n + 33554432) / 65536 = n + 512)
      by (symmetry; apply Z.div_unique with (r := s1 + 256 * s2); lia).
    assert (E3: (n + 512) mod 256 = n) by (symmetry; apply Z.mod_unique with (q := 2); lia).
    assert (E4: (s1 + 256 * s2 + 65536 * n + 33554432) / 16777216 = 2)
      by (symmetry; apply Z.div_unique with (r := s1 + 256 * s2 + 65536 * n); lia).
    rewrite E1, E2, E3, E4. reflexivity.
  - rewrite (x2f_cellu_single _ _ _ _ _ Hs2 Hgt) in He. rewrite x2f_deltu1 in He.
    unfold nbw in *. rewrite He. split; [lia|]. left. exists 0. split; [lia|].
    set (n := ht_log ht + 1 - w1) in *.
    assert (E1: (s1 + 65536 * n + 16777216) mod 65536 = s1)
      by (symmetry; apply Z.mod_unique with (q := n + 256); lia).
    assert (E2: (s1 + 65536 * n + 16777216) / 65536 = n + 256)
      by (symmetry; apply Z.div_unique with (r := s1); lia).
    assert (E3: (n + 256) mod 256 = n) by (symmetry; apply Z.mod_unique with (q := 1); lia).
    assert (E4: (s1 + 65536 * n + 16777216) / 16777216 = 1)
      by (symmetry; apply Z.div_unique with (r := s1 + 65536 * n); lia).
    rewrite E1, E2, E3, E4. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.

End Fill.

Lemma x2_fill_ok : x2_count -> x2_layout -> x2_fill.
Proof.
  intros HC HL. constructor.
  - intros. apply x2f_single; auto.
  - intros. apply x2f_double; auto.
  - intros. apply x2f_skip; auto.
  - intros. apply x2f_weight; auto.
  - intros. apply x2f_cell; auto.
  - intros. apply x2f_cell; auto.
Qed.
