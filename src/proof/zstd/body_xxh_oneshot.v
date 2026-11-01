(* Bodies of XXH64_endian_align and ZSTD_XXH64 (group xxh).
   Removed: the unproved body_XXH64_endian_align and bodies_xxh_oneshot (proof: AllBodies_xxh.v, body_XXH64_endian_align_v2). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.

(* ---------- the stripes of the model, one at a time ---------- *)

Definition xo_step (v: Z * Z * Z * Z) (l: list Z) : Z * Z * Z * Z :=
  match v with (v1, v2, v3, v4) =>
    (xxh_round v1 (le_field l 0 8), xxh_round v2 (le_field l 8 8),
     xxh_round v3 (le_field l 16 8), xxh_round v4 (le_field l 24 8))
  end.

Lemma xo_stripes_unfold: forall n v l, xxh_stripes (S n) v l =
  if Z.of_nat (length l) <? 32 then (v, l) else xxh_stripes n (xo_step v l) (skipn 32 l).
Proof. intros. destruct v as [[[v1 v2] v3] v4]. reflexivity. Qed.

Lemma xo_stripes_add: forall k n v l, (32 * Z.of_nat k <= Z.of_nat (length l))%Z ->
  xxh_stripes (k + n) v l = xxh_stripes n (fst (xxh_stripes k v l)) (snd (xxh_stripes k v l)).
Proof.
  induction k; intros n v l Hk. reflexivity.
  rewrite Nat.add_succ_l, !xo_stripes_unfold.
  destruct (Z.of_nat (length l) <? 32) eqn:E. { apply Z.ltb_lt in E. lia. }
  apply IHk. rewrite length_skipn. lia.
Qed.

Lemma xo_stripes_snd: forall k v l, (32 * Z.of_nat k <= Z.of_nat (length l))%Z ->
  snd (xxh_stripes k v l) = skipn (32 * k) l.
Proof.
  induction k; intros v l Hk. reflexivity.
  rewrite xo_stripes_unfold.
  destruct (Z.of_nat (length l) <? 32) eqn:E. { apply Z.ltb_lt in E. lia. }
  rewrite IHk by (rewrite length_skipn; lia). rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma xo_stripes_S: forall k v l, (32 * Z.of_nat (S k) <= Z.of_nat (length l))%Z ->
  fst (xxh_stripes (S k) v l) = xo_step (fst (xxh_stripes k v l)) (skipn (32 * k) l).
Proof.
  intros. replace (S k) with (k + 1)%nat by lia. rewrite xo_stripes_add by lia.
  rewrite xo_stripes_snd by lia.
  rewrite xo_stripes_unfold, length_skipn.
  destruct (Z.of_nat (length l - 32 * k) <? 32) eqn:E.
  { apply Z.ltb_lt in E. lia. }
  reflexivity.
Qed.

Lemma xo_stripes_short: forall n v l, (Z.of_nat (length l) < 32)%Z -> xxh_stripes n v l = (v, l).
Proof.
  destruct n; intros v l H. reflexivity. rewrite xo_stripes_unfold.
  replace (Z.of_nat (length l) <? 32) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma xo_stripes_all: forall k v l, (32 * Z.of_nat k <= Z.of_nat (length l) < 32 * Z.of_nat k + 32)%Z ->
  xxh_stripes (length l) v l = (fst (xxh_stripes k v l), skipn (32 * k) l).
Proof.
  intros. replace (length l) with (k + (length l - k))%nat by lia.
  rewrite xo_stripes_add by lia. rewrite xo_stripes_snd by lia.
  rewrite xo_stripes_short. reflexivity. rewrite length_skipn. lia.
Qed.

Definition xo_in_range (v: Z * Z * Z * Z) : Prop :=
  match v with (v1, v2, v3, v4) =>
    0 <= v1 <= Int64.max_unsigned /\ 0 <= v2 <= Int64.max_unsigned /\
    0 <= v3 <= Int64.max_unsigned /\ 0 <= v4 <= Int64.max_unsigned
  end.

Lemma xo_stripes_range: forall k v l, xo_in_range v -> xo_in_range (fst (xxh_stripes k v l)).
Proof.
  induction k; intros v l H. exact H.
  rewrite xo_stripes_unfold.
  destruct (Z.of_nat (length l) <? 32). exact H.
  apply IHk. destruct v as [[[v1 v2] v3] v4]. simpl. auto using xxh_round_range.
Qed.

Lemma xo_le_field: forall l i j, 0 <= i -> 0 <= j ->
  le_field (skipn (Z.to_nat i) l) j 8 = le_value (sublist (i + j) (i + j + 8) l).
Proof.
  intros. unfold le_field, slice, sublist. rewrite skipn_skipn.
  rewrite skipn_firstn_comm. f_equal. f_equal. f_equal. lia. f_equal. lia.
Qed.

(* ---------- an 8-byte window of a byte array ---------- *)

Definition xo_frame (sh: share) (bs: list Z) (i: Z) (p: val) : mpred :=
  sepcon (data_at sh (tarray tuchar i) (xxh_bytes (sublist 0 i bs)) p)
    (data_at sh (tarray tuchar (Zlength bs - (i + 8))) (xxh_bytes (sublist (i + 8) (Zlength bs) bs))
       (offset_val (i + 8) p)).

Lemma xo_window: forall sh bs i p, field_compatible (tarray tuchar (Zlength bs)) [] p ->
  0 <= i -> i + 8 <= Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p =
  sepcon (data_at sh (tarray tuchar 8) (xxh_bytes (sublist i (i + 8) bs)) (offset_val i p)) (xo_frame sh bs i p).
Proof.
  intros. unfold xo_frame, xxh_bytes.
  assert (Zlength (map (fun b => Vint (Int.repr b)) bs) = Zlength bs) by apply Zlength_map.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength bs) i (i + 8)) by lia.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  rewrite !sublist_map. replace (i + 8 - i) with 8 by lia.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  apply pred_ext; cancel.
Qed.

Lemma xo_split: forall sh bs i p, field_compatible (tarray tuchar (Zlength bs)) [] p ->
  0 <= i <= Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p =
  sepcon (data_at sh (tarray tuchar i) (xxh_bytes (sublist 0 i bs)) p)
    (data_at sh (tarray tuchar (Zlength (sublist i (Zlength bs) bs))) (xxh_bytes (sublist i (Zlength bs) bs)) (offset_val i p)).
Proof.
  intros. unfold xxh_bytes.
  assert (Zlength (map (fun b => Vint (Int.repr b)) bs) = Zlength bs) by apply Zlength_map.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) i) by lia.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  rewrite !sublist_map, Zlength_sublist by lia.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
Qed.

Lemma body_ZSTD_XXH64: semax_body Vprog Gprog f_ZSTD_XXH64 ZSTD_XXH64_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _input p; temp _len (Vlong (Int64.repr (Zlength bs)));
                 temp _seed (Vlong (Int64.repr seed)))
              SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { contradiction. }
  { forward. entailer!. }
  forward_call (sh, p, bs, seed, w).
  forward.
Qed.
