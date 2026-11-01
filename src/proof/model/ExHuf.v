(* The exact model of zstd's Huffman literals decoding (lib/decompress/huf_decompress.c,
   lib/common/bitstream.h, lib/common/entropy_common.c), in the build configuration of quickproof.conf:
   64-bit, HUF_DISABLE_FAST_DECODE (no fast 4-stream loops), DYNAMIC_BMI2 = 0, neither
   HUF_FORCE_DECOMPRESS_X1 nor _X2.

   Unlike the format model (Huffman.v), which only says what a valid input decodes to, every function
   here returns exactly what the C code computes on every input, and None exactly when the C function
   returns an error code.  Where the C code reads bits that are not in the stream (past its end, or past
   the bit container's window), the result here is what the C computes from its 64-bit container, so
   that "None" is decided exactly as the C decides it.

   - x_huf_read: HUF_readDTableX1_wksp / HUF_readDTableX2_wksp (the table and the description's size);
   - x_huf_select: HUF_selectDecoder;
   - x_huf_decode: HUF_decompress{1X1,1X2,4X1,4X2}_usingDTable_internal (by the table's type);
   - x_lits_huf: the Huffman part of ZSTD_decodeLiteralsBlock (literals block types 2 and 3).

   The C-exact pieces the decoder's proofs already established are reused, from the plain-Coq files they
   share with those proofs: EntC.ncount_c (FSE_readNCount_body on >= 8 bytes), EntC.weights_of /
   huf_parse_res (FSE_decompress_wksp and HUF_readStats_body given readNCount's result), HufC.hsym (the X1
   cells HUF_readDTableX1_wksp writes, dec/B/huf/HufMRescale.v), HufC.x2_elt (the X2 cells
   HUF_fillDTableX2 writes, dec/B/huf/HufX2Mf.v x2_fill_ok).  This file stays plain Coq over the format
   model (src/proof/model).

   One assumption on the table's state: the descriptor's maxTableLog is 12, as ZSTD_decompressBegin and
   ZSTD_initDDict_internal set it (hufTable[0] = 12 * 0x1000001), and as both readers keep it. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast.
Require Import Zstd.proof.model.Fse Zstd.proof.model.NCount Zstd.proof.model.Huffman.
Require Export Zstd.proof.model.EntC Zstd.proof.model.HufC.
Local Open Scope Z_scope.

(* ===================== The tree description: HUF_readStats_wksp ===================== *)

(* FSE_readNCount_body (entropy_common.c, lines 43-188) on any window s, exactly.  On >= 8 bytes it is
   EntC.ncount_c.  On fewer bytes (lines 58-67) the C copies s into a zero-filled 8-byte buffer,
   runs the same function on those 8 bytes (hence ncount_c again) and rejects a description longer
   than s.  (EntModel.ncount_res, the specifications' result, takes the format model's read_ncount
   there, which is C's result only where it succeeds: EntModel.nc_rel.) *)
Definition x_ncount (s: list Z) (maxsv: Z) : option (list Z * Z * Z) :=
  if Zlength s <? 8 then
    match ncount_c (s ++ repeat 0 (Z.to_nat (8 - Zlength s))) maxsv with
    | Some (norm, log, size) => if size >? Zlength s then None else Some (norm, log, size)
    | None => None
    end
  else ncount_c s maxsv.

(* On >= 8 bytes this is ncount_c, the result EntModel's specifications give there (nc_rel). *)
Lemma x_ncount_ge8 (s: list Z) (maxsv: Z) : 8 <= Zlength s -> x_ncount s maxsv = ncount_c s maxsv.
Proof.
  intros H. unfold x_ncount.
  destruct (Zlength s <? 8) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

(* HUF_readStats_wksp(huffWeight, 256, rankStats, .., b, |b|, wksp, 4 * 219, flags) (entropy_common.c,
   lines 243-307): the weights (the implied last one included) and the description's size iSize + 1.
   Both table readers pass a statsWksp of HUF_READ_STATS_WORKSPACE_SIZE_U32 = 219 words; the FSE-coded
   weights read their FSE description with x_ncount on the window rs_window b. *)
Definition x_readstats (b: list Z) : option (huf_table * Z) :=
  huf_parse_res (match rs_window b with Some w => x_ncount w 255 | None => None end) 219 b.

(* ===================== The decoding table: HUF_DTable ===================== *)

(* A HUF_DTable as zstd keeps it between blocks (dctx->entropy.hufTable): the descriptor's tableType
   (xh_x2: false = 0, X1 cells; true = 1, X2 cells), its tableLog (xh_log, the dtLog the decoders peek),
   and the 2^xh_log cells, each read as (sequence, nbBits, length):
   - X1 (HUF_DEltX1 {nbBits; byte}): (byte, nbBits, 1);
   - X2 (HUF_DEltX2 {sequence; nbBits; length}): sequence is the U16 of the first symbol (low byte) and
     the second one (high byte; 0 for a one-symbol cell), length 1 or 2. *)
Record xhuf := { xh_x2 : bool; xh_log : Z; xh_cells : list (Z * Z * Z) }.

(* HUF_readDTableX1_wksp (lines 412-419): targetTableLog = MIN(maxTableLog + 1, 11) = 11 and
   HUF_rescaleStats raises the tableLog to it (lines 361-383); the check "tableLog > maxTableLog + 1"
   (line 416) never fails, since HUF_readStats bounds tableLog by 12. *)
Definition xh_x1_log (ht: huf_table) : Z := Z.max (ht_log ht) 11.

(* HUF_readDTableX2_wksp (lines 1213-1215): maxTableLog = 12 (the check "maxTableLog > 12", line 1206,
   and "tableLog > maxTableLog", line 1213, never fail), lowered to 11 when tableLog <= 11. *)
Definition xh_x2_log (ht: huf_table) : Z := if ht_log ht <=? 11 then 11 else 12.

(* the fields of an X2 cell written as one little-endian U32 (HUF_buildDEltX2U32, lines 970-985) *)
Definition xh_x2_fields (e: Z) : Z * Z * Z := (e mod 65536, (e / 65536) mod 256, e / 16777216).

(* The X1 cells (lines 456-527): cell v holds the symbol of the code whose top bits are v and its code
   length; after the rescale they are the cells of the parsed table, each repeated 2^(L - tableLog)
   times, which is HufC.hsym ht L v (HufMRescale; BRep.x1_cells). *)
Definition xh_cells_x1 (ht: huf_table) (L: Z) : list (Z * Z * Z) :=
  map (fun n => let '(s, nb) := hsym ht L (Z.of_nat n) in (s, nb, 1)) (seq 0 (Z.to_nat (2 ^ L))).

(* The X2 cells (HUF_fillDTableX2, lines 1131-1184, with the level-2 fill HUF_fillDTableX2Level2 and its
   minWeight rule): HufC.x2_elt, the cell of the L-bit value v with its second symbol when the two
   codes fit in L bits (HufX2Mf.x2_fill_ok, HufX2Sc.x2_u32s_cells). *)
Definition xh_cells_x2 (ht: huf_table) (L: Z) : list (Z * Z * Z) :=
  map (fun n => xh_x2_fields (x2_elt ht L (Z.of_nat n))) (seq 0 (Z.to_nat (2 ^ L))).

(* the table the reader of type x2 builds from the parsed description ht *)
Definition xhuf_of (x2: bool) (ht: huf_table) : xhuf :=
  if x2 then
    let L := xh_x2_log ht in {| xh_x2 := true; xh_log := L; xh_cells := xh_cells_x2 ht L |}
  else
    let L := xh_x1_log ht in {| xh_x2 := false; xh_log := L; xh_cells := xh_cells_x1 ht L |}.

(* HUF_readDTableX1_wksp (x2 = false, lines 394-529) / HUF_readDTableX2_wksp (x2 = true, lines
   1186-1270) on the description bytes b: the table and the size of the description (the return value
   iSize).  Both fail only where HUF_readStats_wksp fails (the workspace checks pass: zstd's
   dctx->workspace has 2560 bytes).  On failure the C leaves the table unchanged; the callers then fail
   the whole block. *)
Definition x_huf_read (x2: bool) (b: list Z) : option (xhuf * Z) :=
  match x_readstats b with
  | Some (ht, size) => Some (xhuf_of x2 ht, size)
  | None => None
  end.

(* the cell of the peeked value v (v < 2^xh_log for the decoders' peeks) *)
Definition xh_cell (t: xhuf) (v: Z) : Z * Z * Z := nth (Z.to_nat v) (xh_cells t) (0, 0, 0).

(* ===================== The bit container: BIT_DStream_t (bitstream.h) ===================== *)

(* The state of a BIT_DStream_t reading the stream bytes s: bitContainer (a U64), bitsConsumed (a U32)
   and ptr, as an offset from start (Some k) or &zeroFilled (None, the overflow state of
   BIT_reloadDStream).  In terms of zstd/Spec_bits.v: ptr = start + lo / 8, bitContainer = bit_C s lo,
   bitsConsumed = lo + 64 - pos; here the container is kept itself, so that a peek outside the window
   (unspecified in Spec_bits) has the value the C computes. *)
Record xbit := { xb_c : Z; xb_bc : Z; xb_ptr : option Z }.

(* BIT_DStream_status *)
Definition XB_unfinished : Z := 0.
Definition XB_endOfBuffer : Z := 1.
Definition XB_completed : Z := 2.
Definition XB_overflow : Z := 3.

(* MEM_readLEST at start + k *)
Definition xb_rd64 (s: list Z) (k: Z) : Z := le_value (slice s k 8).

(* BIT_initDStream (lines 254-300).  srcSize = 0 and a last byte 0 are errors.  srcSize >= 8: the
   container is the last 8 bytes, bitsConsumed = 8 - highbit(last byte).  Shorter: the container is the
   whole stream (zero-extended), and bitsConsumed counts the missing bytes too. *)
Definition xb_init (s: list Z) : option xbit :=
  let n := Zlength s in
  if n <? 1 then None else
  let last := byte_at s (n - 1) in
  if last =? 0 then None else
  if 8 <=? n then Some {| xb_c := xb_rd64 s (n - 8); xb_bc := 8 - highbit last; xb_ptr := Some (n - 8) |}
  else Some {| xb_c := le_value s; xb_bc := 8 - highbit last + (8 - n) * 8; xb_ptr := Some 0 |}.

(* BIT_lookBitsFast(nb), 1 <= nb (lines 346-351): (container << (bitsConsumed & 63)) >> ((64 - nb) & 63).
   The shift by bitsConsumed & 63 wraps when bitsConsumed >= 64: the value the C computes past the
   stream's end. *)
Definition xb_look_fast (d: xbit) (nb: Z) : Z :=
  Z.shiftr ((Z.shiftl (xb_c d) (xb_bc d mod 64)) mod 2 ^ 64) ((64 - nb) mod 64).

(* BIT_skipBits (lines 353-356), in U32 arithmetic *)
Definition xb_skip (d: xbit) (nb: Z) : xbit :=
  {| xb_c := xb_c d; xb_bc := (xb_bc d + nb) mod 2 ^ 32; xb_ptr := xb_ptr d |}.

(* BIT_reloadDStream_internal at ptr = start + k (lines 384-392) *)
Definition xb_reload_internal (s: list Z) (d: xbit) (k: Z) : Z * xbit :=
  let k' := k - Z.shiftr (xb_bc d) 3 in
  (XB_unfinished, {| xb_c := xb_rd64 s k'; xb_bc := Z.land (xb_bc d) 7; xb_ptr := Some k' |}).

(* BIT_reloadDStream (lines 414-445, with patch item 12's comparisons inside the stream): overflow when
   bitsConsumed > 64 (ptr := &zeroFilled, the state is kept forever since bitsConsumed only grows);
   a full reload when 8 bytes remain below ptr; at start, endOfBuffer or completed; otherwise the cautious
   reload, endOfBuffer when it reaches start.  The case ptr = &zeroFilled with bitsConsumed <= 64 cannot
   arise (bitsConsumed only grows after an overflow); it returns overflow. *)
Definition xb_reload (s: list Z) (d: xbit) : Z * xbit :=
  if 64 <? xb_bc d then (XB_overflow, {| xb_c := xb_c d; xb_bc := xb_bc d; xb_ptr := None |}) else
  match xb_ptr d with
  | None => (XB_overflow, d)
  | Some k =>
      if 8 <=? k then xb_reload_internal s d k
      else if k =? 0 then ((if xb_bc d <? 64 then XB_endOfBuffer else XB_completed), d)
      else
        let nbB := Z.shiftr (xb_bc d) 3 in
        let '(nbB, r) := if k <? nbB then (k, XB_endOfBuffer) else (nbB, XB_unfinished) in
        let k' := k - nbB in
        (r, {| xb_c := xb_rd64 s k'; xb_bc := xb_bc d - nbB * 8; xb_ptr := Some k' |})
  end.

(* BIT_reloadDStreamFast (lines 400-405): overflow (no change) when fewer than 8 bytes are below ptr.
   The 4-stream loops, its only callers, never see ptr = &zeroFilled. *)
Definition xb_reload_fast (s: list Z) (d: xbit) : Z * xbit :=
  match xb_ptr d with
  | Some k => if k <? 8 then (XB_overflow, d) else xb_reload_internal s d k
  | None => (XB_overflow, d)
  end.

(* BIT_endOfDStream (lines 450-453): ptr == start and bitsConsumed == 64 *)
Definition xb_end (d: xbit) : bool :=
  match xb_ptr d with
  | Some k => andb (k =? 0) (xb_bc d =? 64)
  | None => false
  end.

(* ===================== X1 decoding ===================== *)

(* HUF_decodeSymbolX1 (lines 530-536): peek dtLog bits, emit the cell's byte, skip its nbBits *)
Definition xh_x1_sym (t: xhuf) (d: xbit) : Z * xbit :=
  let '(sq, nb, _) := xh_cell t (xb_look_fast d (xh_log t)) in (sq, xb_skip d nb).

(* k symbols without reload *)
Fixpoint xh_x1_n (t: xhuf) (d: xbit) (k: nat) : list Z * xbit :=
  match k with
  | O => (nil, d)
  | S k' => let '(c, d) := xh_x1_sym t d in let '(l, d) := xh_x1_n t d k' in (c :: l, d)
  end.

(* The 4-symbol loop of HUF_decodeStreamX1 (lines 559-566): while (reload == unfinished) & (p < pEnd - 3)
   (both operands are evaluated: the reload happens at every test), 4 symbols.  rem = pEnd - p.  Fuel:
   each body takes 4 of rem > 3, so there are at most rem / 4 bodies and rem / 4 + 1 tests; fuel rem + 1
   is never exhausted. *)
Fixpoint xh_x1_loop4 (fuel: nat) (s: list Z) (t: xhuf) (d: xbit) (rem: Z) (acc: list Z)
    : list Z * xbit * Z :=
  match fuel with
  | O => (acc, d, rem)
  | S f =>
      let '(st, d) := xb_reload s d in
      if andb (st =? XB_unfinished) (3 <? rem) then
        let '(l, d) := xh_x1_n t d 4 in xh_x1_loop4 f s t d (rem - 4) (acc ++ l)
      else (acc, d, rem)
  end.

(* HUF_decodeStreamX1 (lines 555-581) on rem = pEnd - p symbols: the 4-symbol loop (or one reload when
   rem <= 3), then the remaining symbols without reload (the MEM_32bits loop is not compiled in).  It
   always emits exactly rem symbols. *)
Definition xh_x1_stream (t: xhuf) (s: list Z) (d: xbit) (rem: Z) : list Z * xbit :=
  let '(a, d, rem) :=
    if 3 <? rem then xh_x1_loop4 (Z.to_nat rem + 1) s t d rem nil
    else let '(_, d) := xb_reload s d in (nil, d, rem) in
  let '(b, d) := xh_x1_n t d (Z.to_nat rem) in (a ++ b, d).

(* ===================== X2 decoding ===================== *)

(* HUF_decodeSymbolX2 (lines 1273-1279): peek dtLog bits, write the cell's 2-byte sequence, skip its
   nbBits, advance by its length.  Only the `length` bytes the pointer advances over are emitted: when
   length = 1 the second byte written lands on the next symbol's position and is overwritten by it
   (every write of HUF_decodeStreamX2 is inside [p, pEnd), and its last symbol ends exactly at pEnd). *)
Definition xh_x2_sym (t: xhuf) (d: xbit) : list Z * xbit :=
  let '(sq, nb, len) := xh_cell t (xb_look_fast d (xh_log t)) in
  (firstn (Z.to_nat len) [sq mod 256; sq / 256], xb_skip d nb).

(* k decodes without reload *)
Fixpoint xh_x2_n (t: xhuf) (d: xbit) (k: nat) : list Z * xbit :=
  match k with
  | O => (nil, d)
  | S k' => let '(c, d) := xh_x2_sym t d in let '(l, d) := xh_x2_n t d k' in (c ++ l, d)
  end.

(* HUF_decodeLastSymbolX2 (lines 1282-1297): one byte (the sequence's first symbol); a one-symbol cell
   skips its nbBits; a two-symbol cell skips them only while bitsConsumed < 64, then caps bitsConsumed
   at 64. *)
Definition xh_x2_last (t: xhuf) (d: xbit) : list Z * xbit :=
  let '(sq, nb, len) := xh_cell t (xb_look_fast d (xh_log t)) in
  let d :=
    if len =? 1 then xb_skip d nb
    else if xb_bc d <? 64 then
      let d' := xb_skip d nb in
      if 64 <? xb_bc d' then {| xb_c := xb_c d'; xb_bc := 64; xb_ptr := xb_ptr d' |} else d'
    else d in
  ([sq mod 256], d).

(* A loop of HUF_decodeStreamX2 with reloads: while (reload == unfinished) & cond(rem), k decodes
   (lines 1323-1327 with k = 5, cond rem > 9; lines 1330-1335 with k = 4, cond rem > 7; line 1342 with
   k = 1, cond rem >= 2).  Fuel: each body emits at least one byte (cells have length 1 or 2) of
   rem >= 1, so at most rem bodies and rem + 1 tests; fuel rem + 1 is never exhausted. *)
Fixpoint xh_x2_loopr (fuel: nat) (s: list Z) (t: xhuf) (k: nat) (cond: Z -> bool) (d: xbit) (rem: Z)
    (acc: list Z) : list Z * xbit * Z :=
  match fuel with
  | O => (acc, d, rem)
  | S f =>
      let '(st, d) := xb_reload s d in
      if andb (st =? XB_unfinished) (cond rem) then
        let '(l, d) := xh_x2_n t d k in xh_x2_loopr f s t k cond d (rem - Zlength l) (acc ++ l)
      else (acc, d, rem)
  end.

(* the loop without reload (lines 1344-1345): while rem >= 2, one decode; same fuel argument *)
Fixpoint xh_x2_loop1 (fuel: nat) (t: xhuf) (d: xbit) (rem: Z) (acc: list Z) : list Z * xbit * Z :=
  match fuel with
  | O => (acc, d, rem)
  | S f =>
      if 2 <=? rem then
        let '(l, d) := xh_x2_sym t d in xh_x2_loop1 f t d (rem - Zlength l) (acc ++ l)
      else (acc, d, rem)
  end.

(* HUF_decodeStreamX2 (lines 1315-1356) on rem = pEnd - p bytes: the 5-decode loop (dtLog <= 11) or the
   4-decode loop when rem >= 8 (else one reload), then while rem >= 2 one decode with reloads, then
   without, then the last symbol when one byte is left.  It always emits exactly rem bytes. *)
Definition xh_x2_stream (t: xhuf) (s: list Z) (d: xbit) (rem: Z) : list Z * xbit :=
  let fuel := (Z.to_nat rem + 1)%nat in
  let '(a, d, rem) :=
    if 8 <=? rem then
      if xh_log t <=? 11 then xh_x2_loopr fuel s t 5 (fun r => 9 <? r) d rem nil
      else xh_x2_loopr fuel s t 4 (fun r => 7 <? r) d rem nil
    else let '(_, d) := xb_reload s d in (nil, d, rem) in
  let '(b, d, rem) :=
    if 2 <=? rem then
      let '(b1, d, rem) := xh_x2_loopr fuel s t 1 (fun r => 2 <=? r) d rem nil in
      let '(b2, d, rem) := xh_x2_loop1 fuel t d rem nil in (b1 ++ b2, d, rem)
    else (nil, d, rem) in
  let '(c, d) := if 0 <? rem then xh_x2_last t d else (nil, d) in
  (a ++ b ++ c, d).

(* ===================== One stream and four streams ===================== *)

(* HUF_decompress1X1_usingDTable_internal_body (lines 584-605) / 1X2 (lines 1360-1385): initialize on
   the whole input, decode n symbols, require the exact end. *)
Definition xh_1stream (fin: list Z -> xbit -> Z -> list Z * xbit) (src: list Z) (n: Z) : option (list Z) :=
  match xb_init src with
  | None => None
  | Some d => let '(l, d) := fin src d n in if xb_end d then Some l else None
  end.

(* The jump table (lines 627-634 / 1408-1415): three LE16 sizes, the fourth stream the rest; the check
   "length4 > cSrcSize" (size_t arithmetic) fails exactly when the three sizes and the table exceed the
   input. *)
Definition xh_split4 (src: list Z) : option (list Z * list Z * list Z * list Z) :=
  let n := Zlength src in
  let l1 := le_field src 0 2 in
  let l2 := le_field src 2 2 in
  let l3 := le_field src 4 2 in
  if n <? l1 + l2 + l3 + 6 then None else
  Some (slice src 6 l1, slice src (6 + l1) l2, slice src (6 + l1 + l2) l3,
        slice src (6 + l1 + l2 + l3) (n - 6 - l1 - l2 - l3)).

(* The main loop of the 4-stream decoders (X1: lines 654-676, olimit = oend - 3; X2: lines 1469-1489,
   olimit = oend - 7): while endSignal & (op4 < olimit), 4 decodes per stream, then endSignal = all four
   BIT_reloadDStreamFast are unfinished (all four are called).  lim4 = olimit - opStart4; the outputs o_i
   are what each stream emitted since its segment start (the streams are independent; a stream that runs
   into its neighbour's segment is rejected right after the loop, and one that reaches it exactly still
   has bits left, so it fails its end check).  Fuel: each body emits at least 4 bytes into o4 while
   |o4| < lim4 <= n, so fuel n + 1 is never exhausted. *)
Fixpoint xh_loop4s (fuel: nat) (dec4: xbit -> list Z * xbit) (lim4: Z) (s1 s2 s3 s4: list Z)
    (d1 d2 d3 d4: xbit) (o1 o2 o3 o4: list Z)
    : (xbit * xbit * xbit * xbit) * (list Z * list Z * list Z * list Z) :=
  match fuel with
  | O => ((d1, d2, d3, d4), (o1, o2, o3, o4))
  | S f =>
      if negb (Zlength o4 <? lim4) then ((d1, d2, d3, d4), (o1, o2, o3, o4)) else
      let '(a1, d1) := dec4 d1 in
      let '(a2, d2) := dec4 d2 in
      let '(a3, d3) := dec4 d3 in
      let '(a4, d4) := dec4 d4 in
      let '(r1, d1) := xb_reload_fast s1 d1 in
      let '(r2, d2) := xb_reload_fast s2 d2 in
      let '(r3, d3) := xb_reload_fast s3 d3 in
      let '(r4, d4) := xb_reload_fast s4 d4 in
      let o1 := o1 ++ a1 in let o2 := o2 ++ a2 in let o3 := o3 ++ a3 in let o4 := o4 ++ a4 in
      if andb (andb (r1 =? XB_unfinished) (r2 =? XB_unfinished)) (andb (r3 =? XB_unfinished) (r4 =? XB_unfinished))
      then xh_loop4s f dec4 lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4
      else ((d1, d2, d3, d4), (o1, o2, o3, o4))
  end.

(* HUF_decompress4X1_usingDTable_internal_body (lines 611-707) / 4X2 (lines 1391-1508) on src with
   dstSize n: the size checks, the jump table, the four BIT_initDStream, the main loop when
   oend - op4 >= 8, the checks op_i <= opStart_{i+1}, each stream finished on its segment (segments of
   (n + 3) / 4, the fourth the rest), and all four end checks.  slack = sizeof(size_t) - 1 for X2, 3 for
   X1. *)
Definition xh_4streams (dec4: xbit -> list Z * xbit) (slack: Z) (fin: list Z -> xbit -> Z -> list Z * xbit)
    (src: list Z) (n: Z) : option (list Z) :=
  if Zlength src <? 10 then None else
  if n <? 6 then None else
  match xh_split4 src with
  | None => None
  | Some (s1, s2, s3, s4) =>
      let seg := (n + 3) / 4 in
      if n <? 3 * seg then None else
      match xb_init s1, xb_init s2, xb_init s3, xb_init s4 with
      | Some d1, Some d2, Some d3, Some d4 =>
          let '((d1, d2, d3, d4), (o1, o2, o3, o4)) :=
            if 8 <=? n - 3 * seg
            then xh_loop4s (Z.to_nat n + 1) dec4 (n - slack - 3 * seg) s1 s2 s3 s4 d1 d2 d3 d4 nil nil nil nil
            else ((d1, d2, d3, d4), (nil, nil, nil, nil)) in
          if seg <? Zlength o1 then None else
          if seg <? Zlength o2 then None else
          if seg <? Zlength o3 then None else
          let '(t1, d1) := fin s1 d1 (seg - Zlength o1) in
          let '(t2, d2) := fin s2 d2 (seg - Zlength o2) in
          let '(t3, d3) := fin s3 d3 (seg - Zlength o3) in
          let '(t4, d4) := fin s4 d4 (n - 3 * seg - Zlength o4) in
          if andb (andb (xb_end d1) (xb_end d2)) (andb (xb_end d3) (xb_end d4))
          then Some (o1 ++ t1 ++ o2 ++ t2 ++ o3 ++ t3 ++ o4 ++ t4)
          else None
      | _, _, _, _ => None
      end
  end.

(* The decoding of litSize symbols from the stream bytes with table t, by its type (HUF_decompress1X_ /
   HUF_decompress4X_usingDTable, lines 1891-1937; with fast decoding disabled each _internal function is
   its _body): single = one stream, else four streams with the jump table. *)
Definition x_huf_decode (t: xhuf) (single: bool) (streams: list Z) (litSize: Z) : option (list Z) :=
  if xh_x2 t then
    if single then xh_1stream (xh_x2_stream t) streams litSize
    else xh_4streams (fun d => xh_x2_n t d 4) 7 (xh_x2_stream t) streams litSize
  else
    if single then xh_1stream (xh_x1_stream t) streams litSize
    else xh_4streams (fun d => xh_x1_n t d 4) 3 (xh_x1_stream t) streams litSize.

(* ===================== HUF_selectDecoder ===================== *)

(* algoTime[16][2] (lines 1808-1828): ((tableTime, decode256Time) of X1, (tableTime, decode256Time) of X2) *)
Definition xh_algo_time : list ((Z * Z) * (Z * Z)) :=
  [ ((0, 0), (1, 1)); ((0, 0), (1, 1));
    ((150, 216), (381, 119)); ((170, 205), (514, 112)); ((177, 199), (539, 110));
    ((197, 194), (644, 107)); ((221, 192), (735, 107)); ((256, 189), (881, 106));
    ((359, 188), (1167, 109)); ((582, 187), (1570, 114)); ((688, 187), (1712, 122));
    ((825, 186), (1965, 136)); ((976, 185), (2131, 150)); ((1180, 186), (2070, 175));
    ((1377, 185), (1731, 202)); ((1412, 185), (1695, 202)) ].

(* HUF_selectDecoder (lines 1836-1858), true = X2: Q = cSrcSize * 16 / dstSize (15 when cSrcSize >=
   dstSize), D256 = (U32)(dstSize >> 8), the two times in U32 arithmetic, X2's raised by 1/32. *)
Definition x_huf_select (litSize litCSize: Z) : bool :=
  let Q := if litSize <=? litCSize then 15 else litCSize * 16 / litSize in
  let D256 := Z.shiftr litSize 8 mod 2 ^ 32 in
  let '((t0, d0), (t1, d1)) := nth (Z.to_nat Q) xh_algo_time ((0, 0), (0, 0)) in
  let DTime0 := (t0 + d0 * D256) mod 2 ^ 32 in
  let DTime1 := (t1 + d1 * D256) mod 2 ^ 32 in
  let DTime1 := (DTime1 + Z.shiftr DTime1 5) mod 2 ^ 32 in
  DTime1 <? DTime0.

(* ===================== ZSTD_decodeLiteralsBlock's Huffman part ===================== *)

(* HUF_decompress1X1_DCtx_wksp (lines 1909-1919) / HUF_decompress4X{1,2}_DCtx_wksp (lines 939-951,
   1784-1797): read the table of type x2 from cb, require hSize < cSrcSize, decode the rest. *)
Definition xh_dctx (x2 single: bool) (cb: list Z) (litSize: Z) : option (list Z * xhuf) :=
  match x_huf_read x2 cb with
  | None => None
  | Some (t, h) =>
      if Zlength cb <=? h then None else
      match x_huf_decode t single (skipn (Z.to_nat h) cb) litSize with
      | Some l => Some (l, t)
      | None => None
      end
  end.

(* The Huffman part of ZSTD_decodeLiteralsBlock (zstd_decompress_block.c, lines 150-251) for a literals
   block of type ty with litSize literals and litCSize = |cb| compressed bytes cb (the size checks against
   the block maximum and the capacity are outside):
   - ty = 2 (set_compressed): single stream: HUF_decompress1X1_DCtx_wksp (always X1); four streams:
     HUF_decompress4X_hufOnly_wksp (lines 1939-1958: litSize = 0 and litCSize = 0 are errors, then X1 or
     X2 by HUF_selectDecoder);
   - ty = 3 (set_repeat): the previous table (None: dctx->litEntropy = 0, an error), with
     HUF_decompress1X_usingDTable / HUF_decompress4X_usingDTable.
   The result: the literals and the table zstd keeps for later blocks (dctx->HUFptr). *)
Definition x_lits_huf (hprev: option xhuf) (ty: Z) (single: bool) (cb: list Z) (litSize: Z)
    : option (list Z * xhuf) :=
  if ty =? 2 then
    if single then xh_dctx false true cb litSize
    else if litSize =? 0 then None
    else if Zlength cb =? 0 then None
    else xh_dctx (x_huf_select litSize (Zlength cb)) false cb litSize
  else if ty =? 3 then
    match hprev with
    | None => None
    | Some t =>
        match x_huf_decode t single cb litSize with
        | Some l => Some (l, t)
        | None => None
        end
    end
  else None.

(* ===================== Examples, computed by hand from the C code ===================== *)

(* A direct description of two symbols of weight 1 (header 128: one weight, 0x10: weight 1 for symbol
   0; the implied last weight is 1): tableLog 1, 2 bytes.  The X1 table is rescaled to 11: cells
   0..1023 give symbol 0, 1024..2047 symbol 1, each code 1 bit. *)
Definition xh_ex_desc : list Z := [128; 16].

Example x_huf_read_ex1 :
  option_map (fun '(t, h) => (xh_x2 t, xh_log t, h, length (xh_cells t),
                              xh_cell t 0, xh_cell t 1023, xh_cell t 1024, xh_cell t 2047))
             (x_huf_read false xh_ex_desc)
  = Some (false, 11, 2, 2048%nat, (0, 1, 1), (0, 1, 1), (1, 1, 1), (1, 1, 1)).
Proof. vm_compute. reflexivity. Qed.

(* The X2 table of the same description (log 11): every cell holds two symbols (bit 10, then bit 9 of v),
   2 bits, length 2; e.g. v = 512 = 0b01000000000: symbols 0 then 1, sequence 0 + 256 * 1. *)
Example x_huf_read_ex2 :
  option_map (fun '(t, h) => (xh_x2 t, xh_log t, h, length (xh_cells t), xh_cell t 512, xh_cell t 1024))
             (x_huf_read true xh_ex_desc)
  = Some (true, 11, 2, 2048%nat, (256, 2, 2), (1, 2, 2)).
Proof. vm_compute. reflexivity. Qed.

(* An invalid description: a single weight-2 symbol gives total 2, tableLog 2, rest 2, last weight 2:
   no weight 1 (rankStats[1] < 2), rejected *)
Example x_huf_read_ex3 : option_map snd (x_huf_read false [128; 32]) = None.
Proof. vm_compute. reflexivity. Qed.

Definition xh_ex_t1 : xhuf := match x_huf_read false xh_ex_desc with Some (t, _) => t | None => {| xh_x2 := false; xh_log := 0; xh_cells := nil |} end.
Definition xh_ex_t2 : xhuf := match x_huf_read true xh_ex_desc with Some (t, _) => t | None => {| xh_x2 := false; xh_log := 0; xh_cells := nil |} end.

(* BIT_initDStream on [0x05]: container 5, bitsConsumed 8 - 2 + 7 * 8 = 62, ptr = start. *)
Example xb_init_ex : xb_init [5] = Some {| xb_c := 5; xb_bc := 62; xb_ptr := Some 0 |}.
Proof. vm_compute. reflexivity. Qed.

(* One X1 stream [0x05] (payload bits 0, 1 below the end mark): symbols 0, 1, then bitsConsumed = 64 at
   start: the end.  A third symbol overreads (the peek wraps to bitsConsumed & 63 = 0) and fails the end
   check. *)
Example x_huf_decode_ex1 : x_huf_decode xh_ex_t1 true [5] 2 = Some [0; 1].
Proof. vm_compute. reflexivity. Qed.
Example x_huf_decode_ex2 : x_huf_decode xh_ex_t1 true [5] 3 = None.
Proof. vm_compute. reflexivity. Qed.
(* no end mark *)
Example x_huf_decode_ex3 : x_huf_decode xh_ex_t1 true [0] 0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A 9-byte X1 stream: 8 bytes 0xAA and the end mark 0x01: the cautious reload (ptr = start + 1,
   bitsConsumed 8: one byte down, unfinished), one 4-symbol round, then endOfBuffer and 60 symbols
   without reload: 64 symbols 1, 0, 1, 0, ... *)
Example x_huf_decode_ex4 :
  x_huf_decode xh_ex_t1 true (repeat 170 8 ++ [1]) 64 = Some (concat (repeat [1; 0] 32)).
Proof. vm_compute. reflexivity. Qed.

(* X2, one stream: [0x05] decodes as one two-symbol cell; [0x03] (one payload bit 1) with one literal
   goes through HUF_decodeLastSymbolX2: a two-symbol cell, 1 byte, bitsConsumed 63 + 2 capped at 64. *)
Example x_huf_decode_ex5 : x_huf_decode xh_ex_t2 true [5] 2 = Some [0; 1].
Proof. vm_compute. reflexivity. Qed.
Example x_huf_decode_ex6 : x_huf_decode xh_ex_t2 true [3] 1 = Some [1].
Proof. vm_compute. reflexivity. Qed.

(* Four streams, 6 literals: segments 2, 2, 2, 0; streams [5], [5], [5] and [1] (only the end mark). *)
Definition xh_ex_4s : list Z := [1; 0; 1; 0; 1; 0; 5; 5; 5; 1].
Example x_huf_decode_ex7 : x_huf_decode xh_ex_t1 false xh_ex_4s 6 = Some [0; 1; 0; 1; 0; 1].
Proof. vm_compute. reflexivity. Qed.
Example x_huf_decode_ex8 : x_huf_decode xh_ex_t2 false xh_ex_4s 6 = Some [0; 1; 0; 1; 0; 1].
Proof. vm_compute. reflexivity. Qed.
(* a jump table larger than the input *)
Example x_huf_decode_ex9 : x_huf_decode xh_ex_t1 false [9; 0; 1; 0; 1; 0; 5; 5; 5; 1] 6 = None.
Proof. vm_compute. reflexivity. Qed.

(* Four streams, 32 literals (segments of 8): the main loop runs once (oend - op4 = 8); streams
   [0xAA; 0x01]: X1 decodes 4 symbols per stream there, then the fast reload overflows (ptr = start) and
   each stream finishes its last 4 symbols; X2 decodes all 8 bytes per stream in the main loop. *)
Definition xh_ex_4l : list Z := [2; 0; 2; 0; 2; 0; 170; 1; 170; 1; 170; 1; 170; 1].
Example x_huf_decode_ex10 : x_huf_decode xh_ex_t1 false xh_ex_4l 32 = Some (concat (repeat [1; 0] 16)).
Proof. vm_compute. reflexivity. Qed.
Example x_huf_decode_ex11 : x_huf_decode xh_ex_t2 false xh_ex_4l 32 = Some (concat (repeat [1; 0] 16)).
Proof. vm_compute. reflexivity. Qed.

(* HUF_selectDecoder: (1000, 300): Q = 4, D256 = 3, X1 774 vs X2 869 + 27: X1.  (65536, 20000): Q = 4,
   D256 = 256, X1 51121 vs X2 28699 + 896: X2.  (32, 16): Q = 8, D256 = 0: 359 vs 1167 + 36: X1. *)
Example x_huf_select_ex : (x_huf_select 1000 300, x_huf_select 65536 20000, x_huf_select 32 16) = (false, true, false).
Proof. vm_compute. reflexivity. Qed.

(* The literals section: compressed, one stream (X1); compressed, four streams (X1 chosen); treeless with
   the previous X2 table; treeless without a previous table. *)
Example x_lits_huf_ex1 : option_map fst (x_lits_huf None 2 true (xh_ex_desc ++ [5]) 2) = Some [0; 1].
Proof. vm_compute. reflexivity. Qed.
Example x_lits_huf_ex2 :
  option_map (fun '(l, t) => (l, xh_x2 t)) (x_lits_huf None 2 false (xh_ex_desc ++ xh_ex_4l) 32)
  = Some (concat (repeat [1; 0] 16), false).
Proof. vm_compute. reflexivity. Qed.
Example x_lits_huf_ex3 :
  option_map (fun '(l, t) => (l, xh_x2 t)) (x_lits_huf (Some xh_ex_t2) 3 false xh_ex_4s 6)
  = Some ([0; 1; 0; 1; 0; 1], true).
Proof. vm_compute. reflexivity. Qed.
Example x_lits_huf_ex4 : x_lits_huf None 3 true [5] 2 = None.
Proof. vm_compute. reflexivity. Qed.
(* a description that takes the whole section (hSize >= cSrcSize) *)
Example x_lits_huf_ex5 : x_lits_huf None 2 true xh_ex_desc 2 = None.
Proof. vm_compute. reflexivity. Qed.
