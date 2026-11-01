(* Bodies of group xxh: XXH_memcpy and the byte reads XXH_read32/64, XXH_readLE32/64(_align). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.

Lemma bytes_ok_range: forall bs, bytes_ok bs -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs.
Proof. intros. eapply Forall_impl; [|exact H]. unfold is_byte. simpl. intros; rep_lia. Qed.

Lemma body_XXH_memcpy: semax_body Vprog Gprog f_XXH_memcpy XXH_memcpy_spec.
Proof.
  start_function.
  forward_call (shs, shd, src, dst, tv).
  forward.
Qed.

Lemma body_XXH_read32: semax_body Vprog Gprog f_XXH_read32 XXH_read32_spec.
Proof.
  start_function.
  assert_PROP (field_compatible tuint [] v_val) by entailer!.
  rewrite data_at__tuint_bytes by auto.
  forward_call (sh, Tsh, p, v_val, existT (fun t => reptype t) (tarray tuchar 4) (xxh_bytes bs)).
  { unfold xxh_bytes; memcpy_side. }
  simpl projT1; simpl projT2.
  unfold xxh_bytes at 2. rewrite (bytes4_tuint Tsh bs v_val) by (auto using bytes_ok_range).
  forward.
  forward.
  { entailer!. }
Qed.

Lemma body_XXH64_round: semax_body Vprog Gprog f_XXH64_round XXH64_round_spec.
Proof.
  start_function.
  forward. forward. forward.
  forward.
  entailer!. f_equal. apply xxh_round_repr.
Qed.

Lemma body_XXH_readLE32: semax_body Vprog Gprog f_XXH_readLE32 XXH_readLE32_spec.
Proof.
  start_function.
  forward_call (sh, p, bs).
  forward.
Qed.

Lemma body_XXH_readLE32_align: semax_body Vprog Gprog f_XXH_readLE32_align XXH_readLE32_align_spec.
Proof.
  start_function.
  forward_if.
  { forward_call (sh, p, bs). forward. }
  destruct H1 as [?|[? FC]]; [contradiction|subst align].
  (* the aligned load: the bytes stay, the load sees the scalar *)
  eapply semax_seq'. eapply semax_seq'.
  hoist_later_in_pre.
  eapply (semax_load_nth_ram O _ sh _ _ _ _ _ _ _ _ (Vint (Int.repr (le_value bs))) p);
    [reflexivity|reflexivity|reflexivity| |reflexivity|auto| |].
  - entailer!.
  - unfold xxh_bytes. apply bytes4_tuint_TT; auto using bytes_ok_range.
  - entailer!.
  - simpl remove_localdef_temp. forward. apply ENTAIL_refl.
  - abbreviate_semax. forward.
Qed.

Lemma body_XXH_read64: semax_body Vprog Gprog f_XXH_read64 XXH_read64_spec.
Proof.
  start_function.
  assert_PROP (field_compatible tulong [] v_val) by entailer!.
  rewrite data_at__tulong_bytes by auto.
  forward_call (sh, Tsh, p, v_val, existT (fun t => reptype t) (tarray tuchar 8) (xxh_bytes bs)).
  { unfold xxh_bytes; memcpy_side. }
  simpl projT1; simpl projT2.
  unfold xxh_bytes at 2. sep_apply (bytes8_tulong Tsh bs v_val); auto using bytes_ok_range.
  forward.
  forward.
  { entailer!. }
Qed.

Lemma body_XXH_readLE64: semax_body Vprog Gprog f_XXH_readLE64 XXH_readLE64_spec.
Proof.
  start_function.
  forward_call (sh, p, bs).
  forward.
Qed.

Lemma body_XXH_readLE64_align: semax_body Vprog Gprog f_XXH_readLE64_align XXH_readLE64_align_spec.
Proof.
  start_function.
  forward_if.
  { forward_call (sh, p, bs). forward. }
  destruct H1 as [?|[? FC]]; [contradiction|subst align].
  (* the aligned load: the bytes stay, the load sees the scalar *)
  eapply semax_seq'. eapply semax_seq'.
  hoist_later_in_pre.
  eapply (semax_load_nth_ram O _ sh _ _ _ _ _ _ _ _ (Vlong (Int64.repr (le_value bs))) p);
    [reflexivity|reflexivity|reflexivity| |reflexivity|auto| |].
  - entailer!.
  - unfold xxh_bytes. apply bytes8_tulong_TT; auto using bytes_ok_range.
  - entailer!.
  - simpl remove_localdef_temp. forward. apply ENTAIL_refl.
  - abbreviate_semax. forward.
Qed.

(* ---------- 64-bit arithmetic of mergeRound and avalanche ---------- *)

Lemma lxor_range64: forall a b,
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

Lemma shiftr_range64: forall a k,
  0 <= a <= Int64.max_unsigned -> 0 <= k -> 0 <= Z.shiftr a k <= Int64.max_unsigned.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. split.
  - apply Z.div_pos; [lia|]. apply Z.pow_pos_nonneg; lia.
  - apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    assert (1 <= 2^k) by (apply (Z.pow_le_mono_r 2 0 k); lia). nia.
Qed.

Lemma xor64_repr: forall a b,
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.xor (Int64.repr a) (Int64.repr b) = Int64.repr (Z.lxor a b).
Proof. intros. unfold Int64.xor. rewrite !Int64.unsigned_repr by auto. reflexivity. Qed.

Lemma shru64_repr: forall a k,
  0 <= a <= Int64.max_unsigned -> 0 <= k <= Int64.max_unsigned ->
  Int64.shru (Int64.repr a) (Int64.repr k) = Int64.repr (Z.shiftr a k).
Proof. intros. unfold Int64.shru. rewrite !Int64.unsigned_repr by auto. reflexivity. Qed.

Lemma mul64_m64: forall a c, Int64.mul (Int64.repr a) (Int64.repr c) = Int64.repr (m64 (a * c)).
Proof. intros. rewrite mul64_repr, repr_m64. reflexivity. Qed.

Lemma xxh_merge_repr: forall acc v,
  0 <= acc <= Int64.max_unsigned ->
  Int64.add (Int64.mul (Int64.xor (Int64.repr acc) (Int64.repr (xxh_round 0 v)))
                       (Int64.repr (-7046029288634856825)))
            (Int64.repr (-8796714831421723037)) =
  Int64.repr (xxh_merge acc v).
Proof.
  intros. rewrite xor64_repr by (auto; apply xxh_round_range).
  rewrite P1_neg, P4_neg, mul64_repr, add64_repr.
  unfold xxh_merge. rewrite repr_m64. reflexivity.
Qed.

(* one avalanche step: h ^ (h >> k) *)
Lemma xorshift64_repr: forall h k,
  0 <= h <= Int64.max_unsigned -> 0 <= k <= Int64.max_unsigned ->
  Int64.xor (Int64.repr h) (Int64.shru (Int64.repr h) (Int64.repr k)) = Int64.repr (Z.lxor h (Z.shiftr h k)).
Proof.
  intros. rewrite shru64_repr by auto. apply xor64_repr; auto. apply shiftr_range64; lia.
Qed.

Lemma xxh_avalanche_repr: forall h,
  0 <= h <= Int64.max_unsigned ->
  Int64.xor
    (Int64.mul
       (Int64.xor
          (Int64.mul (Int64.xor (Int64.repr h) (Int64.shru (Int64.repr h) (Int64.repr 33)))
             (Int64.repr (-4417276706812531889)))
          (Int64.shru
             (Int64.mul (Int64.xor (Int64.repr h) (Int64.shru (Int64.repr h) (Int64.repr 33)))
                (Int64.repr (-4417276706812531889)))
             (Int64.repr 29))) (Int64.repr 1609587929392839161))
    (Int64.shru
       (Int64.mul
          (Int64.xor
             (Int64.mul (Int64.xor (Int64.repr h) (Int64.shru (Int64.repr h) (Int64.repr 33)))
                (Int64.repr (-4417276706812531889)))
             (Int64.shru
                (Int64.mul (Int64.xor (Int64.repr h) (Int64.shru (Int64.repr h) (Int64.repr 33)))
                   (Int64.repr (-4417276706812531889)))
                (Int64.repr 29))) (Int64.repr 1609587929392839161))
       (Int64.repr 32)) =
  Int64.repr (xxh_avalanche h).
Proof.
  intros h Hh.
  rewrite xorshift64_repr by (auto; rep_lia).
  rewrite P2_neg, mul64_m64.
  rewrite xorshift64_repr by (try apply m64_range; rep_lia).
  rewrite mul64_m64.
  rewrite xorshift64_repr by (try apply m64_range; rep_lia).
  unfold xxh_avalanche. change XXH_P3 with 1609587929392839161. reflexivity.
Qed.

Lemma body_XXH64_mergeRound: semax_body Vprog Gprog f_XXH64_mergeRound XXH64_mergeRound_spec.
Proof.
  start_function.
  forward_call (0, v).
  forward. forward. forward.
  entailer!. f_equal. apply xxh_merge_repr; auto.
Qed.

Lemma body_XXH64_avalanche: semax_body Vprog Gprog f_XXH64_avalanche XXH64_avalanche_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward. forward.
  entailer!. f_equal. apply xxh_avalanche_repr; auto.
Qed.

(* All the body lemmas of this file. *)
Lemma bodies_xxh_read :
  semax_body Vprog Gprog f_XXH_memcpy XXH_memcpy_spec /\
  semax_body Vprog Gprog f_XXH_read32 XXH_read32_spec /\
  semax_body Vprog Gprog f_XXH64_round XXH64_round_spec /\
  semax_body Vprog Gprog f_XXH_readLE32 XXH_readLE32_spec /\
  semax_body Vprog Gprog f_XXH_readLE32_align XXH_readLE32_align_spec /\
  semax_body Vprog Gprog f_XXH_read64 XXH_read64_spec /\
  semax_body Vprog Gprog f_XXH_readLE64 XXH_readLE64_spec /\
  semax_body Vprog Gprog f_XXH_readLE64_align XXH_readLE64_align_spec /\
  semax_body Vprog Gprog f_XXH64_mergeRound XXH64_mergeRound_spec /\
  semax_body Vprog Gprog f_XXH64_avalanche XXH64_avalanche_spec.
Proof.
  split; [exact body_XXH_memcpy|]. split; [exact body_XXH_read32|].
  split; [exact body_XXH64_round|]. split; [exact body_XXH_readLE32|].
  split; [exact body_XXH_readLE32_align|]. split; [exact body_XXH_read64|].
  split; [exact body_XXH_readLE64|]. split; [exact body_XXH_readLE64_align|].
  split; [exact body_XXH64_mergeRound|]. exact body_XXH64_avalanche.
Qed.
