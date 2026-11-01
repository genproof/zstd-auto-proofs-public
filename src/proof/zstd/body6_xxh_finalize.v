(* Body of XXH64_finalize (group xxh).  Run 6: the proof of this body (body_xxh_finalize.v holds the group's other lemmas). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.zstd.body_xxh_finalize.

(* ---------- the 8-byte loop of the model, one step at a time ---------- *)

Lemma x6_tail8_snd: forall n h l, 8 * Z.of_nat n <= Zlength l ->
  snd (xxh_tail8 n h l) = skipn (8 * n) l.
Proof.
  induction n; intros h l H. reflexivity.
  cbn [xxh_tail8]. rewrite Zlength_correct in H.
  destruct (Z.of_nat (length l) <? 8) eqn:E. { apply Z.ltb_lt in E. lia. }
  rewrite IHn by (rewrite Zlength_correct, length_skipn; lia).
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma x6_skipn_sublist: forall (l: list Z) i, 0 <= i <= Zlength l ->
  skipn (Z.to_nat i) l = sublist i (Zlength l) l.
Proof.
  intros. unfold sublist. rewrite firstn_same; auto.
  rewrite Zlength_correct; lia.
Qed.

Lemma x6_tail8_S: forall n h l, 8 * Z.of_nat n + 8 <= Zlength l ->
  xxh_tail8 (S n) h l =
  (xf_step8 (fst (xxh_tail8 n h l)) (sublist (8 * Z.of_nat n) (Zlength l) l),
   sublist (8 * Z.of_nat n + 8) (Zlength l) l).
Proof.
  intros. rewrite xf_tail8_snoc.
  pose proof (x6_tail8_snd n h l ltac:(lia)) as Hs.
  destruct (xxh_tail8 n h l) as [h' r]. cbn [fst snd] in *. subst r.
  rewrite length_skipn. rewrite Zlength_correct in H.
  destruct (Z.of_nat (length l - 8 * n) <? 8) eqn:E. { apply Z.ltb_lt in E. lia. }
  rewrite skipn_skipn.
  rewrite <- !x6_skipn_sublist by (rewrite Zlength_correct; lia).
  f_equal; [f_equal|]; f_equal; lia.
Qed.

(* ---------- 64-bit arithmetic ---------- *)

Lemma x6_lxor_range: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  0 <= Z.lxor a b <= Int64.max_unsigned.
Proof.
  intros a b Ha Hb.
  assert (N: 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros; lia).
  split; [exact N|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [rewrite E; rep_lia|].
  assert (0 < Z.lxor a b) by lia.
  pose proof (Z.log2_lxor a b (proj1 Ha) (proj1 Hb)).
  assert (Z.log2 a < 64).
  { destruct (Z.eq_dec a 0); [subst; simpl; lia|]. apply Z.log2_lt_pow2; rep_lia. }
  assert (Z.log2 b < 64).
  { destruct (Z.eq_dec b 0); [subst; simpl; lia|]. apply Z.log2_lt_pow2; rep_lia. }
  assert (Z.lxor a b < 2^64) by (apply Z.log2_lt_pow2; lia).
  rep_lia.
Qed.

Lemma x6_xor64_repr: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.xor (Int64.repr a) (Int64.repr b) = Int64.repr (Z.lxor a b).
Proof. intros. unfold Int64.xor. rewrite !Int64.unsigned_repr by auto. reflexivity. Qed.

Lemma x6_and31: forall len, 0 <= len <= Int64.max_unsigned ->
  Int64.and (Int64.repr len) (Int64.repr 31) = Int64.repr (len mod 32).
Proof.
  intros. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* ---------- the aligned reads ---------- *)

Lemma x6_fc_offset: forall t n i b o,
  field_compatible (tarray tuchar n) [] (Vptr b o) ->
  0 <= i -> i + sizeof t <= n -> complete_legal_cosu_type t = true -> legal_nested_field t [] ->
  align_compatible t (Vptr b (Ptrofs.repr (Ptrofs.unsigned o + i))) ->
  field_compatible t [] (offset_val i (Vptr b o)).
Proof.
  intros t n i b o FC Hi Hn H1 H2 H3.
  destruct FC as [_ [_ [Hs _]]]. simpl in Hs. pose proof (Ptrofs.unsigned_range o).
  pose proof (sizeof_pos t).
  rewrite Z.max_r in Hs by lia.
  simpl offset_val. rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr i) by rep_lia.
  repeat split; auto.
  simpl. rewrite Ptrofs.unsigned_repr by rep_lia. lia.
Qed.

Lemma x6_fc_tulong: forall n i b o,
  field_compatible (tarray tuchar n) [] (Vptr b o) -> (8 | Ptrofs.unsigned o) -> (8 | i) ->
  0 <= i -> i + 8 <= n -> field_compatible tulong [] (offset_val i (Vptr b o)).
Proof.
  intros n i b o FC Ho Hi H0 Hn.
  pose proof FC as FC'. destruct FC' as [_ [_ [Hs _]]]. simpl in Hs. pose proof (Ptrofs.unsigned_range o).
  rewrite Z.max_r in Hs by lia.
  apply (x6_fc_offset tulong n); auto.
  { simpl; auto. }
  simpl. apply align_compatible_rec_by_value with Mint64; [reflexivity|].
  rewrite Ptrofs.unsigned_repr by rep_lia. simpl. apply Z.divide_add_r; auto.
Qed.

Lemma x6_fc_tuint: forall n i b o,
  field_compatible (tarray tuchar n) [] (Vptr b o) -> (8 | Ptrofs.unsigned o) -> (8 | i) ->
  0 <= i -> i + 4 <= n -> field_compatible tuint [] (offset_val i (Vptr b o)).
Proof.
  intros n i b o FC Ho Hi H0 Hn.
  pose proof FC as FC'. destruct FC' as [_ [_ [Hs _]]]. simpl in Hs. pose proof (Ptrofs.unsigned_range o).
  rewrite Z.max_r in Hs by lia.
  apply (x6_fc_offset tuint n); auto.
  { simpl; auto. }
  simpl. apply align_compatible_rec_by_value with Mint32; [reflexivity|].
  rewrite Ptrofs.unsigned_repr by rep_lia. simpl.
  apply Z.divide_add_r; eapply Z.divide_trans; eauto; exists 2; lia.
Qed.

Lemma x6_window: forall sh bs i k p,
  0 <= i -> 0 <= k -> i + k <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] p ->
  data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p =
  (data_at sh (tarray tuchar i) (xxh_bytes (sublist 0 i bs)) p *
   data_at sh (tarray tuchar k) (xxh_bytes (sublist i (i + k) bs)) (offset_val i p) *
   data_at sh (tarray tuchar (Zlength bs - (i + k))) (xxh_bytes (sublist (i + k) (Zlength bs) bs))
     (offset_val (i + k) p))%logic.
Proof.
  intros. rewrite (xf_split3 sh (Zlength bs) i k (xxh_bytes bs) p) by (unfold xxh_bytes; rewrite ?Zlength_map; auto).
  unfold xxh_bytes. rewrite !sublist_map. reflexivity.
Qed.

Lemma x6_step8_repr: forall hk v, 0 <= hk <= Int64.max_unsigned ->
  Int64.add
    (Int64.mul
       (Int64.or
          (Int64.shl (Int64.xor (Int64.repr hk) (Int64.repr (xxh_round 0 v))) (Int64.repr 27))
          (Int64.shru (Int64.xor (Int64.repr hk) (Int64.repr (xxh_round 0 v))) (Int64.repr (64 - 27))))
       (Int64.repr (-7046029288634856825)))
    (Int64.repr (-8796714831421723037)) =
  Int64.repr (m64 (rotl64 (Z.lxor hk (xxh_round 0 v)) 27 * XXH_P1 + XXH_P4)).
Proof.
  intros. rewrite x6_xor64_repr by (auto; apply xxh_round_range).
  rewrite rotl64_repr by lia. rewrite P1_neg, P4_neg, mul64_repr, add64_repr, repr_m64. reflexivity.
Qed.

Lemma x6_tail8_next: forall k h bs, 0 <= k -> 8 * k + 8 <= Zlength bs ->
  fst (xxh_tail8 (Z.to_nat (k + 1)) h bs) =
  m64 (rotl64 (Z.lxor (fst (xxh_tail8 (Z.to_nat k) h bs))
                      (xxh_round 0 (le_value (sublist (8 * k) (8 * k + 8) bs)))) 27 * XXH_P1 + XXH_P4).
Proof.
  intros. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
  rewrite x6_tail8_S by (rewrite Z2Nat.id; lia). cbn [fst]. unfold xf_step8.
  rewrite Z2Nat.id by lia. rewrite xf_le_field_sublist by lia.
  rewrite sublist_sublist; try lia. replace (0 + 8 * k) with (8 * k) by lia. replace (0 + 8 + 8 * k) with (8 * k + 8) by lia. reflexivity.
Qed.

Lemma x6_step4_repr: forall h v, 0 <= h <= Int64.max_unsigned ->
  Int64.add
    (Int64.mul
       (Int64.or
          (Int64.shl (Int64.xor (Int64.repr h) (Int64.repr (v * -7046029288634856825))) (Int64.repr 23))
          (Int64.shru (Int64.xor (Int64.repr h) (Int64.repr (v * -7046029288634856825))) (Int64.repr (64 - 23))))
       (Int64.repr (-4417276706812531889)))
    (Int64.repr 1609587929392839161) =
  Int64.repr (m64 (rotl64 (Z.lxor h (m64 (v * XXH_P1))) 23 * XXH_P2 + XXH_P3)).
Proof.
  intros.
  replace (Int64.repr (v * -7046029288634856825)) with (Int64.repr (m64 (v * XXH_P1)))
    by (apply repr_eqm; unfold m64; rewrite Z.mod_mod by lia; symmetry; apply mod64_neg_P1).
  rewrite x6_xor64_repr by (auto; apply m64_range).
  rewrite rotl64_repr by lia. rewrite P2_neg, mul64_repr, add64_repr, repr_m64. reflexivity.
Qed.

Lemma x6_tail4_short: forall h l, Zlength l < 4 -> xxh_tail4 h l = (h, l).
Proof.
  intros. unfold xxh_tail4. rewrite Zlength_correct in H.
  destruct (Z.of_nat (length l) <? 4) eqn:E; auto. apply Z.ltb_ge in E. lia.
Qed.

Lemma x6_tail4_long: forall h bs i, 0 <= i -> i + 4 <= Zlength bs ->
  xxh_tail4 h (sublist i (Zlength bs) bs) =
  (m64 (rotl64 (Z.lxor h (m64 (le_value (sublist i (i + 4) bs) * XXH_P1))) 23 * XXH_P2 + XXH_P3),
   sublist (i + 4) (Zlength bs) bs).
Proof.
  intros. unfold xxh_tail4.
  pose proof (Zlength_sublist i (Zlength bs) bs ltac:(lia) ltac:(lia)) as L. rewrite Zlength_correct in L.
  destruct (Z.of_nat (length (sublist i (Zlength bs) bs)) <? 4) eqn:E. { apply Z.ltb_lt in E. lia. }
  rewrite xf_le_field_sublist by lia. rewrite sublist_sublist by lia.
  change (skipn 4 ?l) with (skipn (Z.to_nat 4) l).
  rewrite x6_skipn_sublist by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia.
  replace (0 + i) with i by lia. replace (0 + 4 + i) with (i + 4) by lia.
  replace (4 + i) with (i + 4) by lia. replace (Zlength bs - i + i) with (Zlength bs) by lia. reflexivity.
Qed.

Lemma x6_tail8_all: forall k h bs, 0 <= k -> 8 * k <= Zlength bs < 8 * k + 8 -> k <= 4 ->
  xxh_tail8 4 h bs = (fst (xxh_tail8 (Z.to_nat k) h bs), sublist (8 * k) (Zlength bs) bs).
Proof.
  intros.
  pose proof (x6_tail8_snd (Z.to_nat k) h bs ltac:(rewrite Z2Nat.id; lia)) as Hs.
  replace 4%nat with ((4 - Z.to_nat k) + Z.to_nat k)%nat by lia.
  rewrite xf_tail8_stop.
  - rewrite (surjective_pairing (xxh_tail8 _ h bs)). f_equal. rewrite Hs.
    replace (8 * Z.to_nat k)%nat with (Z.to_nat (8 * k)) by lia.
    apply x6_skipn_sublist; lia.
  - rewrite Hs, length_skipn. rewrite Zlength_correct in H0. lia.
Qed.

Lemma x6_sublist_snoc: forall (l: list Z) i j, 0 <= i <= j -> j < Zlength l ->
  sublist i (j + 1) l = sublist i j l ++ [Znth j l].
Proof.
  intros. rewrite (sublist_split i j (j + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma x6_step1_repr: forall h b, 0 <= h <= Int64.max_unsigned ->
  Int64.mul
    (Int64.or
       (Int64.shl (Int64.xor (Int64.repr h) (Int64.repr (b * 2870177450012600261))) (Int64.repr 11))
       (Int64.shru (Int64.xor (Int64.repr h) (Int64.repr (b * 2870177450012600261))) (Int64.repr (64 - 11))))
    (Int64.repr (-7046029288634856825)) =
  Int64.repr (m64 (rotl64 (Z.lxor h (m64 (b * XXH_P5))) 11 * XXH_P1)).
Proof.
  intros. change 2870177450012600261 with XXH_P5. rewrite <- (repr_m64 (b * XXH_P5)).
  rewrite x6_xor64_repr by (auto; apply m64_range).
  rewrite rotl64_repr by lia. rewrite P1_neg, mul64_repr, repr_m64. reflexivity.
Qed.

Lemma body6_XXH64_finalize: semax_body Vprog Gprog f_XXH64_finalize XXH64_finalize_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  forward_if (PROP () LOCAL (temp _hash (Vlong (Int64.repr h)); temp _ptr p; temp _len (Vlong (Int64.repr len)); temp _align (Vint (Int.repr align)))
                SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { pose proof FC as [Pp _]. destruct p; try contradiction.
    change (denote_tc_test_eq (Vptr b i) (Vlong (Int64.repr 0)))
      with (!! (Int64.repr 0 = Int64.zero) && weak_valid_pointer (Vptr b i)).
    apply andp_right. apply prop_right; auto.
    destruct (zeq (Zlength bs) 0).
    - apply sepcon_weak_valid_pointer2. apply H4; auto.
    - apply sepcon_weak_valid_pointer1. eapply derives_trans; [|apply valid_pointer_weak].
      apply data_at_valid_ptr. auto. simpl. rep_lia. }
  { pose proof FC as [Pp _]. destruct p; try contradiction. discriminate. }
  { forward. entailer!. }
  assert (Hn: 0 <= Zlength bs < 32) by (rewrite H1; apply Z.mod_pos_bound; lia).
  forward.
  rewrite x6_and31 by auto. rewrite <- H1.
  forward_while (EX k: Z,
    PROP (0 <= k; 8 * k <= Zlength bs)
    LOCAL (temp _len (Vlong (Int64.repr (Zlength bs - 8 * k)));
           temp _hash (Vlong (Int64.repr (fst (xxh_tail8 (Z.to_nat k) h bs))));
           temp _ptr (offset_val (8 * k) p); temp _align (Vint (Int.repr align)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { Exists 0. entailer!. }
  { entailer!. }
  { set (hk := fst (xxh_tail8 (Z.to_nat k) h bs)).
    assert (Hhk: 0 <= hk <= Int64.max_unsigned) by (apply xf_tail8_range; auto).
    set (r := sublist (8 * k) (8 * k + 8) bs).
    assert (Hr: Zlength r = 8) by (unfold r; rewrite Zlength_sublist; lia).
    assert (Hrok: bytes_ok r) by (unfold r; apply Forall_sublist; auto).
    pose proof (le_value_range r (xf_bytes_ok_range r Hrok)) as Hrv. rewrite Hr in Hrv.
    rewrite (x6_window sh bs (8 * k) 8 p) by (auto; lia). Intros.
    forward_call (sh, offset_val (8 * k) p, r, align).
    { destruct H3 as [?|[? [b [o [? ?]]]]]; [left; auto|right; split; auto].
      subst p. apply (x6_fc_tulong (Zlength bs)); auto; try lia. exists k; lia. }
    forward_call (0, le_value r).
    forward. forward. forward. forward. forward.
    Exists (k + 1). entailer!.
    { split; [f_equal; f_equal; lia|]. split; [|f_equal; lia].
      f_equal. rewrite x6_step8_repr by auto. rewrite x6_tail8_next by lia. reflexivity. }
    rewrite (x6_window sh bs (8 * k) 8 p) by (auto; lia). cancel. }
  set (h8 := fst (xxh_tail8 (Z.to_nat k) h bs)).
  assert (Hh8: 0 <= h8 <= Int64.max_unsigned) by (apply xf_tail8_range; auto).
  forward_if (EX q: Z, EX h4: Z,
    PROP (8 * k <= q <= Zlength bs; 0 <= h4 <= Int64.max_unsigned;
          xxh_tail4 h8 (sublist (8 * k) (Zlength bs) bs) = (h4, sublist q (Zlength bs) bs))
    LOCAL (temp _len (Vlong (Int64.repr (Zlength bs - q)));
           temp _hash (Vlong (Int64.repr h4));
           temp _ptr (offset_val q p); temp _align (Vint (Int.repr align)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { rewrite !Int64.unsigned_repr in H7 by rep_lia.
    set (r := sublist (8 * k) (8 * k + 4) bs).
    assert (Hr: Zlength r = 4) by (unfold r; rewrite Zlength_sublist; lia).
    assert (Hrok: bytes_ok r) by (unfold r; apply Forall_sublist; auto).
    pose proof (le_value_range r (xf_bytes_ok_range r Hrok)) as Hrv. rewrite Hr in Hrv.
    rewrite (x6_window sh bs (8 * k) 4 p) by (auto; lia). Intros.
    forward_call (sh, offset_val (8 * k) p, r, align).
    { destruct H3 as [?|[? [b [o [? ?]]]]]; [left; auto|right; split; auto].
      subst p. apply (x6_fc_tuint (Zlength bs)); auto; try lia. exists k; lia. }
    forward. forward. forward. forward.
    Exists (8 * k + 4) (m64 (rotl64 (Z.lxor h8 (m64 (le_value r * XXH_P1))) 23 * XXH_P2 + XXH_P3)).
    entailer!.
    { split; [apply m64_range|]. split; [apply x6_tail4_long; lia|].
      split; [f_equal; f_equal; lia|]. f_equal. symmetry. apply x6_step4_repr; auto. }
    rewrite (x6_window sh bs (8 * k) 4 p) by (auto; lia). cancel. }
  { rewrite !Int64.unsigned_repr in H7 by rep_lia.
    forward. Exists (8 * k) h8. entailer!. apply x6_tail4_short. rewrite Zlength_sublist; lia. }
  Intros q h4.
  forward_while (EX j: Z,
    PROP (q <= j <= Zlength bs)
    LOCAL (temp _len (Vlong (Int64.repr (Zlength bs - j)));
           temp _hash (Vlong (Int64.repr (xxh_tail1 h4 (sublist q j bs))));
           temp _ptr (offset_val j p); temp _align (Vint (Int.repr align)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { Exists q. entailer!. rewrite sublist_nil. reflexivity. }
  { entailer!. }
  { set (h1 := xxh_tail1 h4 (sublist q j bs)).
    assert (Hh1: 0 <= h1 <= Int64.max_unsigned) by (apply xf_tail1_range; auto).
    assert (Hb: 0 <= Znth j bs <= Byte.max_unsigned).
    { pose proof (xf_bytes_ok_range bs H2) as Hf. rewrite Forall_Znth in Hf. apply Hf. lia. }
    rewrite (x6_window sh bs j 1 p) by (auto; lia). Intros.
    rewrite sublist_len_1 by lia. unfold xxh_bytes at 2. cbn [map].
    rewrite (data_at_singleton_array_eq sh tuchar (Vint (Int.repr (Znth j bs)))) by reflexivity.
    forward. forward. forward.
    { entailer!; lia. }
    forward. forward. forward.
    Exists (j + 1). entailer!.
    { split; [f_equal; f_equal; lia|]. f_equal. rewrite x6_step1_repr by auto.
      rewrite x6_sublist_snoc by lia. rewrite xf_tail1_snoc. reflexivity. }
    rewrite (x6_window sh bs j 1 p) by (auto; lia). rewrite sublist_len_1 by lia.
    unfold xxh_bytes at 2. cbn [map].
    rewrite (data_at_singleton_array_eq sh tuchar (Vint (Int.repr (Znth j bs)))) by reflexivity.
    cancel. }
  assert (j = Zlength bs) by lia. subst j.
  assert (Hfin: xxh_finalize h bs = xxh_avalanche (xxh_tail1 h4 (sublist q (Zlength bs) bs))).
  { unfold xxh_finalize. rewrite (x6_tail8_all k) by lia. fold h8. rewrite H9. reflexivity. }
  forward_call (xxh_tail1 h4 (sublist q (Zlength bs) bs)).
  { apply xf_tail1_range; auto. }
  forward.
Qed.
