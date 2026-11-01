(* The format model (plain Coq, no VST): bytes and little-endian fields.
   A byte string is a `list Z` whose elements are in [0, 256). *)
From Coq Require Export ZArith List Lia.
Export ListNotations.
Open Scope Z_scope.

Definition is_byte (b: Z) : Prop := 0 <= b < 256.
Definition bytes_ok (l: list Z) : Prop := Forall is_byte l.

(* the byte at position i (0 if out of range) *)
Definition byte_at (l: list Z) (i: Z) : Z := nth (Z.to_nat i) l 0.

(* little-endian value of a list of bytes *)
Fixpoint le_value (l: list Z) : Z :=
  match l with nil => 0 | b :: l' => b + 256 * le_value l' end.

(* bytes [i, i+k) of l *)
Definition slice (l: list Z) (i k: Z) : list Z := firstn (Z.to_nat k) (skipn (Z.to_nat i) l).

(* the little-endian field of k bytes at position i *)
Definition le_field (l: list Z) (i k: Z) : Z := le_value (slice l i k).

(* the k-byte little-endian encoding of v (mod 256^k) *)
Fixpoint le_bytes (k: nat) (v: Z) : list Z :=
  match k with O => nil | S k' => (v mod 256) :: le_bytes k' (v / 256) end.

(* floor(log2 x) for x >= 1; 0 for x <= 0 *)
Definition highbit (x: Z) : Z := Z.log2 x.


(* ZSTD_isError / ERR_isError: a size_t result c is an error code iff c > (size_t)-ZSTD_error_maxCode,
   ZSTD_error_maxCode = 120. *)
Definition is_error_code (c: Z) : bool := 2 ^ 64 - 120 <? c.
