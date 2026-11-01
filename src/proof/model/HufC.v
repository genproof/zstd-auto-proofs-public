(* The cells of zstd's two Huffman decoding table types (lib/decompress/huf_decompress.c) as the C writes
   them, as functions of the parsed description (Huffman.huf_table).  Plain Coq over the format model.  The
   decoder's table representations (dec/B/BRep.v, which exports this file; dec/B/huf/HufX2M.v) and the exact
   model (ExHuf.v) state the tables with these functions. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Huffman.
Local Open Scope Z_scope.

(* X1 (HUF_readDTableX1_wksp): the symbol and code length of the L-bit value x (L >= ht_log): the cell of its
   top ht_log bits *)
Definition hsym (ht: huf_table) (L x: Z) : Z * Z :=
  nth (Z.to_nat (x / 2 ^ (L - ht_log ht))) (huf_cells ht) (0, 0).

(* X2 (HUF_fillDTableX2): HUF_buildDEltX2U32(symbol, nbBits, baseSeq, level) on a little-endian machine *)
Definition deltu (sym nb bs lv: Z) : Z :=
  (if lv =? 1 then sym else bs + 256 * sym) + 65536 * nb + 16777216 * lv.

(* the cell of first symbol s1 (code length n1), x = the L bits after the first code (zeros below) *)
Definition x2_cellu (ht: huf_table) (L s1 n1 x: Z) : Z :=
  let '(s2, n2) := hsym ht L x in
  if n1 + n2 <=? L then deltu s2 (n1 + n2) s1 2 else deltu s1 n1 0 1.

(* the U32 of the X2 cell of the L-bit value v: its first symbol, and the second one when both codes fit in
   the L bits *)
Definition x2_elt (ht: huf_table) (L v: Z) : Z :=
  let '(s1, n1) := hsym ht L v in x2_cellu ht L s1 n1 ((v * 2 ^ n1) mod 2 ^ L).
