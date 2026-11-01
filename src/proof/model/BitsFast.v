(* The format model: reading a backward bitstream from its bytes (a window of at most 5 bytes), which
   computes fast; equal to Bitstream.bs_peek on the stream's value for reads of at most 32 bits
   (bs_peek_s_eq).  The model's decoders (Huffman.v, Block.v) read with bs_peek_s. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream.

(* the nb bits below position pos of the stream s (zeros below 0) *)
Definition bs_peek_s (s: list Z) (pos nb: Z) : Z :=
  if pos <? 0 then 0 else
  let lo := pos - nb in
  if lo >=? 0 then (le_value (slice s (lo / 8) 5) / 2 ^ (lo mod 8)) mod 2 ^ nb
  else (le_value (slice s 0 5) mod 2 ^ pos) * 2 ^ (- lo).
