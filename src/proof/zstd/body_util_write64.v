(* Body of MEM_write64: memcpy from a local U64 into a byte array (needs a store rule that yields the 8 bytes). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.PickLemmas.

Lemma w64_arr_split3: forall sh n i k (l: list val) p,
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

Lemma w64_mem_written_split: forall sh c i k v p,
  0 <= i -> 0 <= k -> i + k <= Zlength c ->
  field_compatible (tarray tuchar (Zlength c)) [] p ->
  data_at sh (tarray tuchar (Zlength c)) (mem_written c i k v) p =
  (data_at sh (tarray tuchar i) (sublist 0 i c) p *
   data_at sh (tarray tuchar k) (zbytes (le_bytes (Z.to_nat k) v)) (offset_val i p) *
   data_at sh (tarray tuchar (Zlength c - (i + k))) (sublist (i + k) (Zlength c) c)
     (offset_val (i + k) p))%logic.
Proof.
  intros.
  assert (Zlength (zbytes (le_bytes (Z.to_nat k) v)) = k)
    by (rewrite Zlength_map, Zlength_le_bytes; lia).
  assert (Zlength (mem_written c i k v) = Zlength c)
    by (unfold mem_written; list_solve).
  rewrite (w64_arr_split3 sh (Zlength c) i k (mem_written c i k v) p) by (auto; lia).
  unfold mem_written.
  f_equal; [f_equal|]; f_equal; list_solve.
Qed.

Lemma w64_zext8: forall z, Int.zero_ext 8 (Int.zero_ext 8 (Int.repr z)) = Int.repr (z mod 256).
Proof.
  intros. rewrite Int.zero_ext_idem by (cbn; lia).
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr z))).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 8) with 256.
  symmetry; apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 16777216; reflexivity].
Qed.

Lemma w64_byte: forall v n, 0 <= v < 2 ^ 64 -> 0 <= n ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8
    (Int.repr (Int64.Z_mod_modulus (Z.shiftr (Int64.unsigned (Int64.repr v)) n))))) =
  Vint (Int.repr (v / 2 ^ n mod 256)).
Proof.
  intros. rewrite w64_zext8. rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small (v / 2 ^ n) Int64.modulus); auto.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with v; [apply Z.div_le_upper_bound; nia|].
  change Int64.modulus with (2 ^ 64). lia.
Qed.

Lemma w64_byte0: forall v, 0 <= v < 2 ^ 64 ->
  Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.unsigned (Int64.repr v))))) =
  Vint (Int.repr (v mod 256)).
Proof.
  intros. rewrite w64_zext8. rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  reflexivity.
Qed.

Lemma w64_le_bytes: forall v,
  zbytes (le_bytes (Z.to_nat 8) v) =
  [Vint (Int.repr (v mod 256)); Vint (Int.repr (v / 2 ^ 8 mod 256));
   Vint (Int.repr (v / 2 ^ 16 mod 256)); Vint (Int.repr (v / 2 ^ 24 mod 256));
   Vint (Int.repr (v / 2 ^ 32 mod 256)); Vint (Int.repr (v / 2 ^ 40 mod 256));
   Vint (Int.repr (v / 2 ^ 48 mod 256)); Vint (Int.repr (v / 2 ^ 56 mod 256))].
Proof.
  intros. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add le_bytes map].
  rewrite !Z.div_div by lia. reflexivity.
Qed.

Local Arguments Z.shiftr : simpl never.
Local Opaque Z.shiftr.

(* Name the stored byte and compute the updated 8-byte list, so the terms stay small. *)
Ltac w64_flat :=
  match goal with |- context [upd_Znth ?n ?l ?x] =>
    let x' := fresh "b" in remember x as x';
    let l' := eval compute in (upd_Znth n l x') in change (upd_Znth n l x') with l'
  end.

Lemma body_MEM_write64 :
  semax_body Vprog Gprog f_MEM_write64 MEM_write64_spec.
Proof.
  start_function. destruct H as (Hsh & Hi & Hik).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] p) as FC by entailer!.
  rewrite (w64_arr_split3 sh (Zlength c) i 8 c p) by (auto; list_solve). Intros.
  sep_apply (data_at_data_at_ sh (tarray tuchar 8) (sublist i (i + 8) c) (offset_val i p)).
  unfold data_at_, field_at_; simpl default_val.
  change (field_at sh (tarray tuchar 8) [] _ (offset_val i p))
    with (data_at sh (tarray tuchar 8) (Zrepeat Vundef 8) (offset_val i p)).
  remember (Int64.repr v) as w eqn:Hw.
  forward.
  do 8 (forward; w64_flat).
  rewrite (w64_mem_written_split sh c i 8 v p) by (auto; lia).
  rewrite w64_le_bytes. subst.
  rewrite w64_byte0 by auto. rewrite !w64_byte by (auto; lia).
  entailer!.
Qed.
