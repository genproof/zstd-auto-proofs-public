(* Small facts the bodies of the frames kit share (FBodies*.v): little-endian bytes written one at a time,
   the byte casts of CompCert. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.zstd.PickLemmas.
Require Import Zstd.proof.harness.frames.FSpecs.

Lemma fk_le_bytes_snoc : forall k v,
  le_bytes (S k) v = le_bytes k v ++ [(v / 2 ^ (8 * Z.of_nat k)) mod 256].
Proof.
  induction k; intros v.
  - cbn [le_bytes app]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - change (le_bytes (S (S k)) v) with ((v mod 256) :: le_bytes (S k) (v / 256)).
    change (le_bytes (S k) v) with ((v mod 256) :: le_bytes k (v / 256)).
    rewrite (IHk (v / 256)). cbn [app]. f_equal. f_equal. f_equal.
    rewrite Z.div_div by (first [lia | apply Z.pow_pos_nonneg; lia]).
    f_equal. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
Qed.

(* writing byte j of v after bytes 0..j-1 *)
Lemma fk_mem_written_step : forall (c: list val) i j v,
  0 <= i -> 0 <= j -> i + j < Zlength c ->
  upd_Znth (i + j) (Zstd.proof.zstd.Spec_util.mem_written c i j v)
    (Vint (Int.repr ((v / 2 ^ (8 * j)) mod 256))) =
  Zstd.proof.zstd.Spec_util.mem_written c i (j + 1) v.
Proof.
  intros c i j v Hi Hj Hc. unfold Zstd.proof.zstd.Spec_util.mem_written.
  rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r, fk_le_bytes_snoc.
  rewrite Z2Nat.id by lia.
  pose proof (Zlength_le_bytes (Z.to_nat j) v) as L. rewrite Z2Nat.id in L by lia.
  rewrite map_app. list_solve.
Qed.

(* the byte (unsigned char) (v >> 8 j) of a 64-bit v *)
Lemma fk_byte_of_shift : forall v j, 0 <= v <= Int64.max_unsigned -> 0 <= j < 8 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus
    (Z.shiftr (Int64.Z_mod_modulus v) (Int64.Z_mod_modulus (8 * Int64.Z_mod_modulus j)))))) =
  Int.repr ((v / 2 ^ (8 * j)) mod 256).
Proof.
  intros v j Hv Hj.
  rewrite !Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small v) by (unfold Int64.max_unsigned in Hv; lia).
  rewrite (Z.mod_small j) by (change Int64.modulus with (2^64); lia).
  rewrite (Z.mod_small (8 * j)) by (change Int64.modulus with (2^64); lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= v / 2 ^ (8 * j) < Int64.modulus).
  { split. apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
    apply Z.le_lt_trans with v; [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|] |].
    - assert (1 <= 2 ^ (8 * j)) by (apply Z.pow_le_mono_r with (a := 2) (b := 0); lia || (simpl; lia)).
      nia.
    - unfold Int64.max_unsigned in Hv; lia. }
  rewrite (Z.mod_small (v / 2 ^ (8 * j))) by lia.
  rewrite Int.zero_ext_idem by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 8) with 256.
  symmetry; apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 16777216; reflexivity].
Qed.
