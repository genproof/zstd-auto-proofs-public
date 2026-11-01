(* Reinterpretation of bytes as integer scalars, with the exact value (little-endian, model/Bytes.v).
   Adapted from QuickProof.Pick (whose .vo is not built), for the reads XXH_read32/64 (memcpy into a
   local scalar) and the aligned reads of XXH64_finalize.  cs-generic.
   - bytes4_tuint (=), bytes2_tushort (=): VST's data_at_int_bytes / data_at_short_bytes;
   - bytes8_tulong (|-- only: VST has no converse for 8 bytes);
   - data_at__tuchar_scalar: data_at_ of a scalar = data_at_ of its bytes. *)
From Coq Require Import List.
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.model.Bytes.
Import ListNotations.

Section PickLemmas.
Context {cs: compspecs}.

Lemma pk_fa0_offset1: forall n p,
  0 < n ->
  field_compatible (tarray tuchar n) [] p ->
  field_address0 (tarray tuchar n) [ArraySubsc 1] p = offset_val 1 p.
Proof.
  intros n p Hn FC.
  rewrite field_address0_offset.
  - unfold nested_field_offset, nested_field_rec, gfield_offset. simpl. reflexivity.
  - apply arr_field_compatible0; auto; lia.
Qed.

Lemma pk_tail_fc: forall n p,
  0 <= n ->
  field_compatible (tarray tuchar (n+1)) [] p ->
  field_compatible (tarray tuchar n) [] (offset_val 1 p).
Proof.
  intros n p Hn FC.
  destruct (field_compatible_Tarray_split tuchar 1 (n+1) p) as [FWD _]. lia.
  specialize (FWD FC). destruct FWD as [_ FC2].
  rewrite pk_fa0_offset1 in FC2 by (auto; lia).
  replace (n+1-1) with n in FC2 by lia. auto.
Qed.

Lemma pk_peel1: forall sh n m (w: val) (ws: list val) p,
  n = m + 1 -> 0 <= m -> Zlength ws = m ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (w::ws) p =
  (data_at sh tuchar w p *
   data_at sh (tarray tuchar m) ws (offset_val 1 p))%logic.
Proof.
  intros sh n m w ws p Hn Hm Hlen FC. subst n.
  rewrite (split2_data_at_Tarray_tuchar sh (m+1) 1 (w::ws) p) by (try lia; list_solve).
  pose proof (pk_fa0_offset1 (m+1) p ltac:(lia) FC) as HH. unfold tarray in HH. rewrite HH.
  rewrite sublist_0_cons by lia. rewrite sublist_nil.
  rewrite (data_at_tuchar_singleton_array_eq sh w).
  rewrite sublist_1_cons.
  replace (m+1-1) with (Zlength ws) by (rewrite Hlen; lia).
  rewrite sublist_same by lia.
  replace (Zlength ws) with m by lia.
  reflexivity.
Qed.

Lemma pk_Vint_repr_Vubyte: forall (z: Z),
  0 <= z <= Byte.max_unsigned ->
  Vint (Int.repr z) = Vubyte (Byte.repr z).
Proof.
  intros z Hz. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* the little-endian value of bytes is CompCert's decode_int *)
Lemma decode_int_le_value: forall bs,
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  decode_int (map Byte.repr bs) = le_value bs.
Proof.
  intros bs H. unfold decode_int, rev_if_be.
  replace Archi.big_endian with false by reflexivity.
  induction H; simpl; auto.
  rewrite IHForall. rewrite Byte.unsigned_repr by rep_lia. lia.
Qed.

Lemma le_value_range: forall bs,
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  0 <= le_value bs < 2 ^ (8 * Zlength bs).
Proof.
  intros bs H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. replace (8 * Z.succ (Zlength l)) with (8 + 8 * Zlength l) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    change (2^8) with 256. rep_lia.
Qed.

Lemma fc_scalar_bytes: forall t n p,
  sizeof t = n -> (alignof (tarray tuchar n) | alignof t) ->
  field_compatible t [] p -> field_compatible (tarray tuchar n) [] p.
Proof.
  intros t n p Hs Ha FC. destruct FC as [A [B [C [D E]]]].
  repeat split; auto.
  - red. destruct p; auto. simpl in C |- *. rewrite Z.max_r; [lia|].
    pose proof (sizeof_pos t). lia.
  - destruct p; simpl in D |- *; auto.
    apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
Qed.

Lemma bytes4_tuint: forall sh (bs: list Z) p,
  field_compatible tuint [] p ->
  Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 4) (map (fun b => Vint (Int.repr b)) bs) p =
  data_at sh tuint (Vint (Int.repr (le_value bs))) p.
Proof.
  intros sh bs p FCu Hlen Hr.
  assert (FC4: field_compatible (tarray tuchar 4) [] p)
    by (apply (fc_scalar_bytes tuint); auto; simpl; apply Z.divide_1_l).
  assert (FC3: field_compatible (tarray tuchar 3) [] (offset_val 1 p))
    by (apply (pk_tail_fc 3 p); [lia | auto]).
  assert (FC2: field_compatible (tarray tuchar 2) [] (offset_val 1 (offset_val 1 p)))
    by (apply (pk_tail_fc 2 (offset_val 1 p)); [lia | auto]).
  assert (FC1: field_compatible (tarray tuchar 1) [] (offset_val 1 (offset_val 1 (offset_val 1 p))))
    by (apply (pk_tail_fc 1 (offset_val 1 (offset_val 1 p))); [lia | auto]).
  rewrite <- (decode_int_le_value bs Hr).
  destruct bs as [|z0 [|z1 [|z2 [|z3 [|z4 bs]]]]]; try (exfalso; revert Hlen; list_solve).
  simpl map.
  pose proof (Forall_inv Hr) as R0. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R1. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R2. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R3.
  rewrite (pk_Vint_repr_Vubyte z0 R0), (pk_Vint_repr_Vubyte z1 R1),
          (pk_Vint_repr_Vubyte z2 R2), (pk_Vint_repr_Vubyte z3 R3).
  rewrite (pk_peel1 sh 4 3 _ _ p) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 3 2 _ _ (offset_val 1 p)) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 2 1 _ _ (offset_val 1 (offset_val 1 p))) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 1 0 _ _ (offset_val 1 (offset_val 1 (offset_val 1 p)))) by (try lia; try list_solve; auto).
  rewrite !offset_offset_val. simpl Z.add.
  rewrite (data_at_zero_array_eq sh tuchar (@nil val) (offset_val 4 p))
    by (auto; destruct FCu as [? _]; destruct p; try contradiction; exact I).
  rewrite <- (data_at_int_bytes eq_refl sh _ _ _ _ p FCu).
  rewrite sepcon_emp. rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma bytes8_tulong: forall sh (bs: list Z) p,
  field_compatible tulong [] p ->
  Zlength bs = 8 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) bs) p
  |-- data_at sh tulong (Vlong (Int64.repr (le_value bs))) p.
Proof.
  intros sh bs p FCl Hlen Hr.
  assert (FC8: field_compatible (tarray tuchar 8) [] p)
    by (apply (fc_scalar_bytes tulong); auto; simpl; apply Z.divide_1_l).
  assert (FC7: field_compatible (tarray tuchar 7) [] (offset_val 1 p))
    by (apply (pk_tail_fc 7 p); [lia|auto]).
  assert (FC6: field_compatible (tarray tuchar 6) [] (offset_val 1 (offset_val 1 p)))
    by (apply (pk_tail_fc 6 (offset_val 1 p)); [lia|auto]).
  assert (FC5: field_compatible (tarray tuchar 5) [] (offset_val 1 (offset_val 1 (offset_val 1 p))))
    by (apply (pk_tail_fc 5 (offset_val 1 (offset_val 1 p))); [lia|auto]).
  assert (FC4: field_compatible (tarray tuchar 4) []
                 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p)))))
    by (apply (pk_tail_fc 4 (offset_val 1 (offset_val 1 (offset_val 1 p)))); [lia|auto]).
  assert (FC3: field_compatible (tarray tuchar 3) []
                 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p))))))
    by (apply (pk_tail_fc 3 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p))))); [lia|auto]).
  assert (FC2: field_compatible (tarray tuchar 2) []
                 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p)))))))
    by (apply (pk_tail_fc 2 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p)))))); [lia|auto]).
  assert (FC1: field_compatible (tarray tuchar 1) []
                 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p))))))))
    by (apply (pk_tail_fc 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 (offset_val 1 p))))))); [lia|auto]).
  rewrite <- (decode_int_le_value bs Hr).
  destruct bs as [|z0 [|z1 [|z2 [|z3 [|z4 [|z5 [|z6 [|z7 [|z8 bs]]]]]]]]];
    try (exfalso; revert Hlen; list_solve).
  simpl map.
  pose proof (Forall_inv Hr) as R0. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R1. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R2. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R3. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R4. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R5. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R6. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R7.
  rewrite (pk_Vint_repr_Vubyte z0 R0), (pk_Vint_repr_Vubyte z1 R1),
          (pk_Vint_repr_Vubyte z2 R2), (pk_Vint_repr_Vubyte z3 R3),
          (pk_Vint_repr_Vubyte z4 R4), (pk_Vint_repr_Vubyte z5 R5),
          (pk_Vint_repr_Vubyte z6 R6), (pk_Vint_repr_Vubyte z7 R7).
  rewrite (pk_peel1 sh 8 7 _ _ p) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 7 6 _ _ (offset_val 1 p)) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 6 5 _ _ _) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 5 4 _ _ _) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 4 3 _ _ _) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 3 2 _ _ _) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 2 1 _ _ _) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 1 0 _ _ _) by (try lia; try list_solve; auto).
  rewrite !offset_offset_val. simpl Z.add.
  sep_apply (data_at_zero_array_inv sh tuchar (@nil val) (offset_val 8 p) eq_refl eq_refl).
  sep_apply (data_at_long_bytes_forward eq_refl sh
               (Byte.repr z0) (Byte.repr z1) (Byte.repr z2) (Byte.repr z3)
               (Byte.repr z4) (Byte.repr z5) (Byte.repr z6) (Byte.repr z7) p FCl).
  cancel.
Qed.

(* the aligned reads: the bytes stay, the load sees the scalar *)
Lemma bytes8_tulong_TT: forall sh (bs: list Z) p,
  field_compatible tulong [] p ->
  Zlength bs = 8 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) bs) p
  |-- mapsto sh tulong p (Vlong (Int64.repr (le_value bs))) * TT.
Proof.
  intros. sep_apply bytes8_tulong.
  erewrite <- (mapsto_data_at' sh tulong) by (auto; reflexivity). cancel.
Qed.

Lemma bytes4_tuint_TT: forall sh (bs: list Z) p,
  field_compatible tuint [] p ->
  Zlength bs = 4 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 4) (map (fun b => Vint (Int.repr b)) bs) p
  |-- mapsto sh tuint p (Vint (Int.repr (le_value bs))) * TT.
Proof.
  intros. rewrite bytes4_tuint by auto.
  erewrite <- (mapsto_data_at' sh tuint) by (auto; reflexivity). cancel.
Qed.

(* a scalar's data_at_ is the data_at_ of its bytes *)
Lemma data_at__scalar_bytes: forall sh t n p,
  sizeof t = n -> field_compatible t [] p ->
  data_at_ sh t p = data_at_ sh (tarray tuchar n) p.
Proof.
  intros. rewrite !data_at__memory_block.
  rewrite !prop_true_andp; auto.
  - simpl. rewrite Z.max_r by (subst; pose proof (sizeof_pos t); lia). rewrite Z.mul_1_l. subst; auto.
  - apply (fc_scalar_bytes t); auto; simpl; apply Z.divide_1_l.
Qed.

Lemma data_at__tushort_bytes: forall sh p,
  field_compatible tushort [] p -> data_at_ sh tushort p = data_at_ sh (tarray tuchar 2) p.
Proof. intros. apply data_at__scalar_bytes; auto. Qed.
Lemma data_at__tuint_bytes: forall sh p,
  field_compatible tuint [] p -> data_at_ sh tuint p = data_at_ sh (tarray tuchar 4) p.
Proof. intros. apply data_at__scalar_bytes; auto. Qed.
Lemma data_at__tulong_bytes: forall sh p,
  field_compatible tulong [] p -> data_at_ sh tulong p = data_at_ sh (tarray tuchar 8) p.
Proof. intros. apply data_at__scalar_bytes; auto. Qed.

Lemma bytes2_tushort: forall sh (bs: list Z) p,
  field_compatible tushort [] p ->
  Zlength bs = 2 ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 2) (map (fun b => Vint (Int.repr b)) bs) p =
  data_at sh tushort (Vint (Int.repr (le_value bs))) p.
Proof.
  intros sh bs p FCu Hlen Hr.
  assert (FC2: field_compatible (tarray tuchar 2) [] p)
    by (apply (fc_scalar_bytes tushort); auto; simpl; apply Z.divide_1_l).
  assert (FC1: field_compatible (tarray tuchar 1) [] (offset_val 1 p))
    by (apply (pk_tail_fc 1 p); [lia | auto]).
  rewrite <- (decode_int_le_value bs Hr).
  destruct bs as [|z0 [|z1 [|z2 bs]]]; try (exfalso; revert Hlen; list_solve).
  simpl map.
  pose proof (Forall_inv Hr) as R0. apply Forall_inv_tail in Hr.
  pose proof (Forall_inv Hr) as R1.
  rewrite (pk_Vint_repr_Vubyte z0 R0), (pk_Vint_repr_Vubyte z1 R1).
  rewrite (pk_peel1 sh 2 1 _ _ p) by (try lia; try list_solve; auto).
  rewrite (pk_peel1 sh 1 0 _ _ (offset_val 1 p)) by (try lia; try list_solve; auto).
  rewrite !offset_offset_val. simpl Z.add.
  rewrite (data_at_zero_array_eq sh tuchar (@nil val) (offset_val 2 p))
    by (auto; destruct FCu as [? _]; destruct p; try contradiction; exact I).
  rewrite <- (data_at_short_bytes sh _ _ p FCu).
  rewrite sepcon_emp. reflexivity.
Qed.

Lemma le_value_le_bytes: forall k v,
  le_value (le_bytes k v) = v mod 2 ^ (8 * Z.of_nat k).
Proof.
  induction k; intros v.
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - cbn [le_bytes le_value]. rewrite IHk.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256.
    rewrite Z.mul_comm with (n := 256).
    rewrite Z.rem_mul_r with (b := 256) by (try lia; apply Z.pow_pos_nonneg; lia).
    lia.
Qed.

Lemma le_bytes_bytes: forall k v,
  Forall (fun b => 0 <= b <= Byte.max_unsigned) (le_bytes k v).
Proof.
  induction k; intros v; simpl; constructor; auto.
  pose proof (Z.mod_pos_bound v 256 ltac:(lia)). rep_lia.
Qed.

Lemma Zlength_le_bytes: forall k v, Zlength (le_bytes k v) = Z.of_nat k.
Proof.
  induction k; intros v; simpl; auto. rewrite Zlength_cons, IHk. lia.
Qed.

Lemma tuint_bytes4: forall sh v p,
  field_compatible tuint [] p ->
  data_at sh tuint (Vint (Int.repr v)) p =
  data_at sh (tarray tuchar 4) (map (fun b => Vint (Int.repr b)) (le_bytes 4 v)) p.
Proof.
  intros. rewrite bytes4_tuint; auto using le_bytes_bytes, Zlength_le_bytes.
  rewrite le_value_le_bytes. change (2 ^ (8 * Z.of_nat 4)) with Int.modulus.
  rewrite <- Int.unsigned_repr_eq, Int.repr_unsigned. reflexivity.
Qed.

Lemma tushort_bytes2: forall sh v p,
  field_compatible tushort [] p ->
  0 <= v < 2 ^ 16 ->
  data_at sh tushort (Vint (Int.repr v)) p =
  data_at sh (tarray tuchar 2) (map (fun b => Vint (Int.repr b)) (le_bytes 2 v)) p.
Proof.
  intros. rewrite bytes2_tushort; auto using le_bytes_bytes, Zlength_le_bytes.
  rewrite le_value_le_bytes. rewrite Z.mod_small; auto.
Qed.

End PickLemmas.
