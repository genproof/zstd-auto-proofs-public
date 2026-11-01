(* Body of XXH64_endian_align (group xxh).  Run 6: the proof of this body (body_xxh_oneshot.v holds the group's other lemmas).
   Removed: the unproved eo_result, eo_result_short and body6_XXH64_endian_align, which used them; this file keeps its helper lemmas (proof: AllBodies_xxh.v, body_XXH64_endian_align_v2 with eo_result_v2, eo_result_short_v2). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.zstd.body_xxh_oneshot.

(* ---------- the model of the stripe loop ---------- *)

Lemma eo_le8_range: forall l, bytes_ok l -> Zlength l = 8 -> 0 <= le_value l <= Int64.max_unsigned.
Proof.
  intros l Hok Hl.
  assert (F: Forall (fun b => 0 <= b <= Byte.max_unsigned) l).
  { eapply Forall_impl; [|exact Hok]. intros a Ha. unfold is_byte in Ha. rep_lia. }
  pose proof (le_value_range l F) as R. rewrite Hl in R.
  change (2 ^ (8 * 8)) with (Int64.max_unsigned + 1) in R. lia.
Qed.

(* the lanes after k stripes *)
Definition eo_v (seed: Z) (bs: list Z) (k: Z) : Z * Z * Z * Z :=
  fst (xxh_stripes (Z.to_nat k) (xxh_init seed) bs).

Lemma eo_v_range: forall seed bs k,
  0 <= xxh_lane1 (eo_v seed bs k) <= Int64.max_unsigned /\
  0 <= xxh_lane2 (eo_v seed bs k) <= Int64.max_unsigned /\
  0 <= xxh_lane3 (eo_v seed bs k) <= Int64.max_unsigned /\
  0 <= xxh_lane4 (eo_v seed bs k) <= Int64.max_unsigned.
Proof.
  intros. unfold eo_v.
  assert (H: xo_in_range (fst (xxh_stripes (Z.to_nat k) (xxh_init seed) bs))).
  { apply xo_stripes_range. unfold xxh_init, xo_in_range. auto using m64_range. }
  destruct (fst _) as [[[a b] c] d]. exact H.
Qed.

Lemma eo_field: forall bs k j, 0 <= k -> 0 <= j ->
  le_field (skipn (32 * Z.to_nat k) bs) (8 * j) 8 = le_value (sublist (32 * k + 8 * j) (32 * k + 8 * j + 8) bs).
Proof.
  intros. replace (32 * Z.to_nat k)%nat with (Z.to_nat (32 * k)) by lia.
  apply xo_le_field; lia.
Qed.

Lemma eo_step: forall seed bs k, 0 <= k -> 32 * k + 32 <= Zlength bs ->
  eo_v seed bs (k + 1) =
  (xxh_round (xxh_lane1 (eo_v seed bs k)) (le_value (sublist (32 * k) (32 * k + 8) bs)),
   xxh_round (xxh_lane2 (eo_v seed bs k)) (le_value (sublist (32 * k + 8) (32 * k + 8 + 8) bs)),
   xxh_round (xxh_lane3 (eo_v seed bs k)) (le_value (sublist (32 * k + 16) (32 * k + 16 + 8) bs)),
   xxh_round (xxh_lane4 (eo_v seed bs k)) (le_value (sublist (32 * k + 24) (32 * k + 24 + 8) bs))).
Proof.
  intros seed bs k Hk Hn. unfold eo_v.
  rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r.
  rewrite xo_stripes_S by (rewrite Zlength_correct in Hn; lia).
  pose proof (eo_field bs k 0 Hk ltac:(lia)) as F0.
  pose proof (eo_field bs k 1 Hk ltac:(lia)) as F1.
  pose proof (eo_field bs k 2 Hk ltac:(lia)) as F2.
  pose proof (eo_field bs k 3 Hk ltac:(lia)) as F3.
  rewrite Z.add_0_r in F0. simpl (8 * _) in F0, F1, F2, F3.
  destruct (fst (xxh_stripes (Z.to_nat k) (xxh_init seed) bs)) as [[[a b] c] d].
  unfold xo_step. rewrite F0, F1, F2, F3. reflexivity.
Qed.

Lemma eo_add8: forall q, isptr q ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint q (Vint (Int.repr 8))) = offset_val 8 q.
Proof. intros. destruct q; try contradiction. reflexivity. Qed.

Lemma eo_cmp: forall n p i j, field_compatible (tarray tuchar n) [] p -> 0 <= i <= n -> 0 <= j <= n ->
  sem_cmp_pp Clt (offset_val i p) (offset_val j p) = Some (Vint (if zlt i j then Int.one else Int.zero)).
Proof.
  intros n p i j FC Hi Hj. destruct FC as [Pp [_ [Hs _]]]. destruct p; try contradiction.
  simpl in Hs. rewrite Z.max_r in Hs by lia. pose proof (Ptrofs.unsigned_range i0).
  unfold sem_cmp_pp. simpl.
  rewrite if_true by auto. simpl. f_equal. unfold Ptrofs.ltu, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr i), (Ptrofs.unsigned_repr j) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt (Ptrofs.unsigned i0 + i) (Ptrofs.unsigned i0 + j)), (zlt i j); try reflexivity; lia.
Qed.

Lemma eo_test_order: forall sh n c p i j R, readable_share sh -> field_compatible (tarray tuchar n) [] p ->
  0 <= i <= n -> 0 <= j <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p * R |-- denote_tc_test_order (offset_val i p) (offset_val j p).
Proof.
  intros sh n c p i j R SH FC Hi Hj Hn.
  assert (Wi: data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val i p)).
  { apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply data_at_memory_block|].
    apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia. }
  assert (Wj: data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val j p)).
  { apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply data_at_memory_block|].
    apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia. }
  destruct FC as [Pp _]. destruct p; try contradiction.
  unfold denote_tc_test_order. simpl offset_val in *. unfold test_order_ptrs.
  simpl sameblock. destruct (peq b b); [|congruence]. simpl. apply andp_right; auto.
Qed.

Lemma eo_limit: forall p n, isptr p -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint
    (force_val (sem_binary_operation' Oadd (tptr tuchar) tulong p (Vlong (Int64.repr n)))) (Vint (Int.repr 31)))
  = offset_val (n - 31) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 31))) with (Ptrofs.repr 31).
  replace (Ptrofs.of_int64 (Int64.repr n)) with (Ptrofs.repr n).
  2: { unfold Ptrofs.of_int64; rewrite Int64.unsigned_repr by rep_lia; reflexivity. }
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_l, Ptrofs.sub_add_opp, Ptrofs.add_assoc.
  f_equal. rewrite Ptrofs.neg_repr, ptrofs_add_repr. f_equal. lia.
Qed.
