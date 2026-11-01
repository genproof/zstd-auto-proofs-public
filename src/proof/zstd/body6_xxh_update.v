(* Body of ZSTD_XXH64_update (group xxh).  Run 6: the proof of this body (body_xxh_update.v holds the group's other lemmas).
   Removed: the unproved body6_ZSTD_XXH64_update; this file keeps its helper lemmas (proof: AllBodies_xxh.v, body_ZSTD_XXH64_update_v2). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.zstd.body_xxh_update.

Lemma xu_test_eq_ptr: forall b i,
  weak_valid_pointer (Vptr b i) |-- denote_tc_test_eq (Vptr b i) (Vlong (Int64.repr 0)).
Proof. intros. Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq. Qed.

Lemma xu_bytes_wvp: forall sh n c b i, readable_share sh -> 0 < n ->
  data_at sh (tarray tuchar n) c (Vptr b i) |-- weak_valid_pointer (Vptr b i).
Proof.
  intros. eapply derives_trans; [|apply valid_pointer_weak]. apply data_at_valid_ptr.
  apply readable_nonidentity; auto. simpl. lia.
Qed.

(* ---------- model facts ---------- *)

Lemma xu_le_field: forall l i, 0 <= i -> le_field l i 8 = le_value (sublist i (i + 8) l).
Proof.
  intros. unfold le_field, slice, sublist. rewrite skipn_firstn_comm. f_equal. f_equal. lia.
Qed.

Lemma xu_le8_range: forall c, bytes_ok c -> Zlength c = 8 -> 0 <= le_value c <= Int64.max_unsigned.
Proof.
  intros. assert (Forall (fun b => 0 <= b <= Byte.max_unsigned) c).
  { eapply Forall_impl; [|apply H]. intros a Ha. unfold is_byte in Ha. rep_lia. }
  apply le_value_range in H1. rewrite H0 in H1. rep_lia.
Qed.

Definition xu_rng (V: Z * Z * Z * Z) : Prop :=
  0 <= xxh_lane1 V <= Int64.max_unsigned /\ 0 <= xxh_lane2 V <= Int64.max_unsigned /\
  0 <= xxh_lane3 V <= Int64.max_unsigned /\ 0 <= xxh_lane4 V <= Int64.max_unsigned.

Lemma xu_stripes_rng: forall n V l, xu_rng V -> xu_rng (fst (xxh_stripes n V l)).
Proof.
  induction n; intros V l H. exact H.
  rewrite xxh_stripes_S. destruct V as [[[v1 v2] v3] v4].
  destruct (Z.of_nat (length l) <? 32). exact H.
  apply IHn. unfold xu_rng; simpl. repeat split; apply xxh_round_range.
Qed.

Lemma xu_lanes_rng: forall seed l, xu_rng (xxh_lanes seed l).
Proof.
  intros. apply xu_stripes_rng. unfold xu_rng, xxh_init; simpl. repeat split; apply m64_range.
Qed.

Lemma xu_round4_eq: forall V c,
  xxh_round4 V c = (xxh_round (xxh_lane1 V) (le_field c 0 8), xxh_round (xxh_lane2 V) (le_field c 8 8),
                    xxh_round (xxh_lane3 V) (le_field c 16 8), xxh_round (xxh_lane4 V) (le_field c 24 8)).
Proof. intros. destruct V as [[[v1 v2] v3] v4]. reflexivity. Qed.

Lemma xu_bytes_ok_sublist: forall bs i j, bytes_ok bs -> bytes_ok (sublist i j bs).
Proof. intros. unfold bytes_ok in *. apply Forall_sublist. auto. Qed.

Lemma xu_Zlength_bytes: forall l, Zlength (xxh_bytes l) = Zlength l.
Proof. intros. unfold xxh_bytes. apply Zlength_map. Qed.

Lemma xu_bytes_app: forall a b, xxh_bytes (a ++ b) = xxh_bytes a ++ xxh_bytes b.
Proof. intros. unfold xxh_bytes. apply map_app. Qed.

Lemma xu_bytes_sublist: forall l i j, xxh_bytes (sublist i j l) = sublist i j (xxh_bytes l).
Proof. intros. unfold xxh_bytes. rewrite sublist_map. reflexivity. Qed.

(* ---------- byte arrays ---------- *)

Lemma xu_split2: forall sh bs k p, field_compatible (tarray tuchar (Zlength bs)) [] p ->
  0 <= k <= Zlength bs ->
  data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p =
  (data_at sh (tarray tuchar k) (xxh_bytes (sublist 0 k bs)) p *
   data_at sh (tarray tuchar (Zlength bs - k)) (xxh_bytes (sublist k (Zlength bs) bs)) (offset_val k p))%logic.
Proof.
  intros. unfold xxh_bytes.
  assert (Zlength (map (fun b => Vint (Int.repr b)) bs) = Zlength bs) by apply Zlength_map.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength bs) k) by lia.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  rewrite !sublist_map.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
Qed.

(* an 8-byte window at i of the n bytes bs *)
Definition xu_frame (sh: share) (n: Z) (bs: list Z) (i: Z) (p: val) : mpred :=
  sepcon (data_at sh (tarray tuchar i) (xxh_bytes (sublist 0 i bs)) p)
    (data_at sh (tarray tuchar (n - (i + 8))) (xxh_bytes (sublist (i + 8) n bs))
       (offset_val (i + 8) p)).

Lemma xu_window: forall sh n bs i p, Zlength bs = n -> field_compatible (tarray tuchar n) [] p ->
  0 <= i -> i + 8 <= n ->
  data_at sh (tarray tuchar n) (xxh_bytes bs) p =
  sepcon (data_at sh (tarray tuchar 8) (xxh_bytes (sublist i (i + 8) bs)) (offset_val i p)) (xu_frame sh n bs i p).
Proof.
  intros. subst n. unfold xu_frame, xxh_bytes.
  assert (Zlength (map (fun b => Vint (Int.repr b)) bs) = Zlength bs) by apply Zlength_map.
  rewrite (split3_data_at_Tarray_tuchar sh (Zlength bs) i (i + 8)) by lia.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  rewrite !sublist_map. replace (i + 8 - i) with 8 by lia.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  apply pred_ext; cancel.
Qed.

(* mem64: the 32 bytes a ++ junk, opened at Zlength a for k bytes *)
Lemma xu_mem_split: forall sh (a: list Z) (junk: list val) k q,
  Zlength a + Zlength junk = 32 -> 0 <= k <= Zlength junk ->
  field_compatible (tarray tuchar 32) [] q ->
  data_at sh (tarray tuchar 32) (xxh_bytes a ++ junk) q |--
  (data_at sh (tarray tuchar (Zlength a)) (xxh_bytes a) q *
   data_at_ sh (tarray tuchar k) (offset_val (Zlength a) q) *
   data_at sh (tarray tuchar (32 - (Zlength a + k))) (sublist k (Zlength junk) junk) (offset_val (Zlength a + k) q))%logic.
Proof.
  intros. pose proof (Zlength_nonneg a). pose proof (Zlength_nonneg junk).
  rewrite (xu_arr_split3 sh 32 (Zlength a) k) by (auto; try lia; rewrite Zlength_app, xu_Zlength_bytes; lia).
  rewrite sublist_app1 by (rewrite ?xu_Zlength_bytes; lia).
  rewrite sublist_same by (rewrite ?xu_Zlength_bytes; lia).
  rewrite sublist_app2 by (rewrite ?xu_Zlength_bytes; lia).
  rewrite sublist_app2 by (rewrite ?xu_Zlength_bytes; lia).
  rewrite !xu_Zlength_bytes. replace (Zlength a - Zlength a) with 0 by lia.
  replace (Zlength a + k - Zlength a) with k by lia. replace (32 - Zlength a) with (Zlength junk) by lia.
  cancel.
Qed.

Lemma xu_mem_join: forall sh (a c: list Z) (junk: list val) k q,
  Zlength c = k -> Zlength a + k + Zlength junk = 32 ->
  field_compatible (tarray tuchar 32) [] q ->
  (data_at sh (tarray tuchar (Zlength a)) (xxh_bytes a) q *
   data_at sh (tarray tuchar k) (xxh_bytes c) (offset_val (Zlength a) q) *
   data_at sh (tarray tuchar (32 - (Zlength a + k))) junk (offset_val (Zlength a + k) q))%logic
  |-- data_at sh (tarray tuchar 32) (xxh_bytes (a ++ c) ++ junk) q.
Proof.
  intros. subst k. pose proof (Zlength_nonneg a). pose proof (Zlength_nonneg c). pose proof (Zlength_nonneg junk).
  rewrite xu_bytes_app, <- app_assoc.
  rewrite (xu_arr_split3 sh 32 (Zlength a) (Zlength c)) by (first [assumption | lia | rewrite !Zlength_app, !xu_Zlength_bytes; lia]).
  pose proof (xu_Zlength_bytes a). pose proof (xu_Zlength_bytes c). autorewrite with sublist. cancel.
Qed.

Lemma xu_window_fold: forall sh n bs i p, Zlength bs = n -> field_compatible (tarray tuchar n) [] p ->
  0 <= i -> i + 8 <= n ->
  (data_at sh (tarray tuchar 8) (xxh_bytes (sublist i (i + 8) bs)) (offset_val i p) * xu_frame sh n bs i p)%logic
  |-- data_at sh (tarray tuchar n) (xxh_bytes bs) p.
Proof. intros. rewrite (xu_window sh n bs i p) by auto. apply derives_refl. Qed.

Lemma xu_wvp_off: forall sh n c p i, readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite data_at__memory_block. Intros. simpl sizeof.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma xu_split2_fold: forall sh bs k p, field_compatible (tarray tuchar (Zlength bs)) [] p ->
  0 <= k <= Zlength bs ->
  (data_at sh (tarray tuchar k) (xxh_bytes (sublist 0 k bs)) p *
   data_at sh (tarray tuchar (Zlength bs - k)) (xxh_bytes (sublist k (Zlength bs) bs)) (offset_val k p))%logic
  |-- data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p.
Proof. intros. rewrite (xu_split2 sh bs k p) by auto. apply derives_refl. Qed.

Lemma xu_stripes_suffix: forall n V l, exists pre, l = pre ++ snd (xxh_stripes n V l).
Proof.
  induction n; intros V l. exists []. reflexivity.
  rewrite xxh_stripes_S. destruct V as [[[v1 v2] v3] v4].
  destruct (Z.of_nat (length l) <? 32). exists []. reflexivity.
  destruct (IHn (xxh_round v1 (le_field l 0 8), xxh_round v2 (le_field l 8 8),
                 xxh_round v3 (le_field l 16 8), xxh_round v4 (le_field l 24 8)) (skipn 32 l)) as [pre E].
  exists (firstn 32 l ++ pre). rewrite <- app_assoc, <- E. symmetry. apply firstn_skipn.
Qed.

Lemma xu_rest_bytes: forall seed l, bytes_ok l -> bytes_ok (xxh_rest seed l).
Proof.
  intros. unfold xxh_rest. destruct (xu_stripes_suffix (length l) (xxh_init seed) l) as [pre E].
  unfold bytes_ok in *. rewrite E in H. apply Forall_app in H. tauto.
Qed.

Lemma xu_sub_pp: forall p a c, isptr p ->
  force_val (sem_sub_pp tuchar (offset_val a p) (offset_val c p)) = Vlong (Int64.repr (a - c)).
Proof.
  intros. destruct p; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr a)), (Ptrofs.add_commut i (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma xu_sub_pi: forall p a, isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val a p) (Vint (Int.repr 32))) =
  offset_val (a - 32) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  change (Ptrofs.of_ints (Int.repr 32)) with (Ptrofs.repr 32).
  rewrite ptrofs_sub_repr. f_equal. lia.
Qed.

Lemma xu_add_pi: forall p a, isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val a p) (Vint (Int.repr 8))) =
  offset_val (a + 8) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  change (Ptrofs.of_ints (Int.repr 8)) with (Ptrofs.repr 8).
  rewrite ptrofs_add_repr. f_equal. lia.
Qed.

Lemma xu_chunk_lanes: forall seed l bs j,
  xxh_rest seed (l ++ sublist 0 j bs) = [] -> 0 <= j -> j + 32 <= Zlength bs ->
  xxh_lanes seed (l ++ sublist 0 (j + 32) bs) =
    (xxh_round (xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs))) (le_value (sublist j (j + 8) bs)),
     xxh_round (xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs))) (le_value (sublist (j + 8) (j + 8 + 8) bs)),
     xxh_round (xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs))) (le_value (sublist (j + 16) (j + 16 + 8) bs)),
     xxh_round (xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs))) (le_value (sublist (j + 24) (j + 24 + 8) bs))) /\
  xxh_rest seed (l ++ sublist 0 (j + 32) bs) = [].
Proof.
  intros.
  assert (E: l ++ sublist 0 (j + 32) bs = (l ++ sublist 0 j bs) ++ sublist j (j + 32) bs)
    by (rewrite <- app_assoc, sublist_rejoin by lia; reflexivity).
  rewrite E. destruct (xxh_app_chunk seed (l ++ sublist 0 j bs) (sublist j (j + 32) bs)) as [F1 F2]; auto.
  { rewrite Zlength_sublist by lia. lia. }
  split; auto. rewrite F1, xu_round4_eq, !xu_le_field by lia.
  rewrite !sublist_sublist; try lia.
  replace (0 + j) with j by lia. replace (0 + 8 + j) with (j + 8) by lia. replace (8 + j) with (j + 8) by lia.
  replace (8 + 8 + j) with (j + 8 + 8) by lia. replace (16 + j) with (j + 16) by lia.
  replace (16 + 8 + j) with (j + 16 + 8) by lia. replace (24 + j) with (j + 24) by lia.
  replace (24 + 8 + j) with (j + 24 + 8) by lia. reflexivity.
Qed.

Lemma xu_test_order: forall sh n c p a b, readable_share sh -> 0 <= a <= n -> 0 <= b <= n -> 0 < n -> isptr p ->
  data_at sh (tarray tuchar n) c p |-- denote_tc_test_order (offset_val a p) (offset_val b p).
Proof.
  intros. destruct p; try contradiction.
  apply derives_trans with (weak_valid_pointer (offset_val a (Vptr b0 i)) && weak_valid_pointer (offset_val b (Vptr b0 i))).
  { apply andp_right; eapply xu_wvp_off; eauto. }
  Transparent denote_tc_test_order. unfold denote_tc_test_order. Opaque denote_tc_test_order.
  simpl. unfold test_order_ptrs. simpl. destruct (peq b0 b0); [|contradiction]. simpl. apply derives_refl.
Qed.

Lemma xu_ofs: forall b i n a, field_compatible (tarray tuchar n) [] (Vptr b i) -> 0 <= a <= n ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr a)) = Ptrofs.unsigned i + a.
Proof.
  intros. destruct H as [_ [_ [Hs _]]]. simpl in Hs. rewrite Z.max_r in Hs by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr a) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma xu_cmp: forall p n a c, field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= c <= n ->
  sem_cmp_pp Cle (offset_val a p) (offset_val c p) = Some (bool2val (a <=? c)) /\
  sem_cmp_pp Clt (offset_val a p) (offset_val c p) = Some (bool2val (a <? c)).
Proof.
  intros. destruct p; try (destruct H; contradiction).
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !(xu_ofs b i n) by auto.
  split; f_equal; f_equal.
  - destruct (zlt _ _), (a <=? c) eqn:E; simpl; auto; try (apply Z.leb_le in E; lia); try (apply Z.leb_gt in E; lia).
  - destruct (zlt _ _), (a <? c) eqn:E; simpl; auto; try (apply Z.ltb_lt in E; lia); try (apply Z.ltb_ge in E; lia).
Qed.

Lemma xu_test_order': forall R a b p, isptr p ->
  (R |-- weak_valid_pointer (offset_val a p)) -> (R |-- weak_valid_pointer (offset_val b p)) ->
  R |-- denote_tc_test_order (offset_val a p) (offset_val b p).
Proof.
  intros. destruct p; try contradiction.
  apply derives_trans with (weak_valid_pointer (offset_val a (Vptr b0 i)) && weak_valid_pointer (offset_val b (Vptr b0 i))).
  { apply andp_right; auto. }
  Transparent denote_tc_test_order. unfold denote_tc_test_order. Opaque denote_tc_test_order.
  simpl. unfold test_order_ptrs. simpl. destruct (peq b0 b0); [|contradiction]. simpl. apply derives_refl.
Qed.

Ltac xu_wvp_find := first [ apply derives_refl
  | apply sepcon_weak_valid_pointer1; xu_wvp_find | apply sepcon_weak_valid_pointer2; xu_wvp_find ].

Lemma xu_mem_split0: forall sh (m: list val) K q, Zlength m = 32 -> 0 <= K <= 32 ->
  field_compatible (tarray tuchar 32) [] q ->
  data_at sh (tarray tuchar 32) m q |--
  (data_at_ sh (tarray tuchar K) q * data_at sh (tarray tuchar (32 - K)) (sublist K 32 m) (offset_val K q))%logic.
Proof.
  intros. rewrite (split2_data_at_Tarray_tuchar sh 32 K) by lia.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. cancel.
Qed.

Lemma xu_mem_join0: forall sh (c: list Z) (junk: list val) K q, Zlength c = K -> K + Zlength junk = 32 ->
  field_compatible (tarray tuchar 32) [] q ->
  (data_at sh (tarray tuchar K) (xxh_bytes c) q * data_at sh (tarray tuchar (32 - K)) junk (offset_val K q))%logic
  |-- data_at sh (tarray tuchar 32) (xxh_bytes c ++ junk) q.
Proof.
  intros. pose proof (xu_Zlength_bytes c). pose proof (Zlength_nonneg junk). pose proof (Zlength_nonneg c).
  rewrite (split2_data_at_Tarray_tuchar sh 32 K) by (rewrite ?Zlength_app, ?xu_Zlength_bytes; lia).
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  autorewrite with sublist. cancel.
Qed.
