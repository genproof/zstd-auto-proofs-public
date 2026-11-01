(* Body of XXH64_finalize (group xxh).
   Removed: the unproved xf_tail8_snd, xf_tail8_S, body_XXH64_finalize (proof: body6_xxh_finalize.v, body6_XXH64_finalize). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.

(* ---------- the model of the tail loops ---------- *)

Definition xf_step8 (h: Z) (r: list Z) : Z :=
  m64 (rotl64 (Z.lxor h (xxh_round 0 (le_field r 0 8))) 27 * XXH_P1 + XXH_P4).

Lemma xf_tail8_snoc: forall n h l,
  xxh_tail8 (S n) h l =
  let (h', r) := xxh_tail8 n h l in
  if Z.of_nat (length r) <? 8 then (h', r) else (xf_step8 h' r, skipn 8 r).
Proof.
  induction n; intros h l.
  - cbn [xxh_tail8]. destruct (Z.of_nat (length l) <? 8); reflexivity.
  - change (xxh_tail8 (S (S n)) h l) with
      (if Z.of_nat (length l) <? 8 then (h, l) else
       xxh_tail8 (S n) (m64 (rotl64 (Z.lxor h (xxh_round 0 (le_field l 0 8))) 27 * XXH_P1 + XXH_P4)) (skipn 8 l)).
    change (xxh_tail8 (S n) h l) with
      (if Z.of_nat (length l) <? 8 then (h, l) else
       xxh_tail8 n (m64 (rotl64 (Z.lxor h (xxh_round 0 (le_field l 0 8))) 27 * XXH_P1 + XXH_P4)) (skipn 8 l)).
    destruct (Z.of_nat (length l) <? 8) eqn:E.
    + rewrite E. reflexivity.
    + apply IHn.
Qed.

Lemma xf_tail8_stop: forall m n h l, Z.of_nat (length (snd (xxh_tail8 n h l))) < 8 ->
  xxh_tail8 (m + n) h l = xxh_tail8 n h l.
Proof.
  induction m; intros n h l H; [reflexivity|].
  change (S m + n)%nat with (S (m + n)). rewrite xf_tail8_snoc. rewrite IHm by auto.
  destruct (xxh_tail8 n h l) as [h' r]. cbn [snd] in H.
  replace (Z.of_nat (length r) <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma xf_tail8_range: forall n h l, 0 <= h <= Int64.max_unsigned ->
  0 <= fst (xxh_tail8 n h l) <= Int64.max_unsigned.
Proof.
  induction n; intros h l H; cbn [xxh_tail8 fst]; auto.
  destruct (Z.of_nat (length l) <? 8); cbn [fst]; auto. apply IHn, m64_range.
Qed.

Lemma xf_tail1_snoc: forall l h b,
  xxh_tail1 h (l ++ [b]) = m64 (rotl64 (Z.lxor (xxh_tail1 h l) (m64 (b * XXH_P5))) 11 * XXH_P1).
Proof. induction l; intros; cbn [xxh_tail1 app]; auto. Qed.

Lemma xf_tail1_range: forall l h, 0 <= h <= Int64.max_unsigned ->
  0 <= xxh_tail1 h l <= Int64.max_unsigned.
Proof. induction l; intros; cbn [xxh_tail1]; auto. apply IHl, m64_range. Qed.

Lemma xf_le_field_sublist: forall bs i k, 0 <= i -> 0 <= k ->
  le_field bs i k = le_value (sublist i (i + k) bs).
Proof.
  intros. unfold le_field, slice, sublist. f_equal.
  rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma xf_bytes_ok_range: forall l, bytes_ok l -> Forall (fun b => 0 <= b <= Byte.max_unsigned) l.
Proof.
  intros l H. eapply Forall_impl; [|exact H]. intros a Ha. unfold is_byte in Ha. rep_lia.
Qed.

Lemma xf_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.
