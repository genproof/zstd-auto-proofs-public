(* The format model: the backward bitstream (RFC 8878, 4.1).

   A bitstream is a byte string s = s[0..n), n >= 1, whose last byte is not 0.  Read as the
   little-endian number V = le_value s, its highest set bit is the end mark; the payload is the
   bs_total s = 8 (n-1) + highbit (last byte) bits below it.  A decoder reads from the top: its
   state is `pos`, the number of payload bits not yet read (initially bs_total s).  Reading nb bits
   gives the next nb bits as a number (the first bit read is the most significant); bits below
   position 0 read as zeros (zstd's decoders peek past the end this way, e.g. Huffman's table
   lookups at the end of a stream).  A stream is fully consumed when pos = 0. *)
Require Import Zstd.proof.model.Bytes.

Definition bs_ok (s: list Z) : Prop :=
  bytes_ok s /\ s <> nil /\ last s 0 <> 0.

Definition bs_okb (s: list Z) : bool :=
  andb (andb (forallb (fun b => andb (0 <=? b) (b <? 256)) s) (negb (Nat.eqb (length s) 0)))
       (negb (last s 0 =? 0)).

Definition bs_value (s: list Z) : Z := le_value s.

Definition bs_total (s: list Z) : Z :=
  8 * (Z.of_nat (length s) - 1) + highbit (last s 0).

(* the nb bits below position pos (zeros below 0), as a number *)
Definition bs_peek (V pos nb: Z) : Z :=
  (V mod 2 ^ pos) * 2 ^ nb / 2 ^ pos.

(* read nb bits at pos: the value and the new position *)
Definition bs_read (V pos nb: Z) : Z * Z := (bs_peek V pos nb, pos - nb).

(* Sanity: the stream [0x05] (bits 101, end mark 1 at bit 2): 2 payload bits, 01. *)
Example bs_example1 : bs_total [5] = 2 /\ bs_read 5 2 2 = (1, 0).
Proof. vm_compute. auto. Qed.
(* peeking 4 bits of a 2-bit remainder pads with zeros: 01 -> 0100 *)
Example bs_example2 : bs_peek 5 2 4 = 4.
Proof. vm_compute. auto. Qed.
