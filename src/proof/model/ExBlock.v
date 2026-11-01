(* The exact model of a compressed block: what ZSTD_decompressBlock_internal
   (lib/decompress/zstd_decompress_block.c 2194-2303) computes on EVERY input, in the verified build
   (64-bit, neither ZSTD_FORCE_DECOMPRESS_SEQUENCES_SHORT nor _LONG, DYNAMIC_BMI2 = 0, no asserts,
   GP_INPLACE = 0: src and dst are separate objects).  Plain Coq over the format model.

   Unlike Block.decode_block (exact where it returns Some, no claim where it returns None), the functions
   here return None exactly when the C returns an error code, and otherwise the C's result: the entropy
   state the block leaves, the destination memory after it and the block's size.  x_block runs zstd's
   own copies (ZSTD_copy16, ZSTD_wildcopy, ZSTD_overlapCopy8, ZSTD_safecopy*, memcpy, memmove) store by
   store on the destination memory as zstd addresses it (prefix [prefixStart, op), extDict
   [dictStart, dictEnd)), so it is exact also where the output overwrites history or literals it later
   reads.  In particular:
   - no window check: a match may reach back to virtualStart, the only check zstd makes;
   - no Block_Maximum_Size check on the content: the content is bounded by the output end zstd uses
     (`oend`, which depends on where the literals are placed, x_alloc_loc), not by bsm;
   - zstd's offset resolution on size_t values (an invalid repeat offset becomes (size_t)-1), its U32
     repeat offsets between blocks, its FSE_readNCount on a short header (zero-padded 8-byte copy).

   The Huffman decoding of compressed / treeless literals is a parameter of the section (x_lits_huf,
   with the table type xhuf); it is instantiated with the exact Huffman model.  Its contract: on
   (hprev, ty, single, cb, n), with ty = 2 (compressed: a tree description, then the streams) or ty = 3
   (treeless: hprev = Some t), it returns Some (l, t') exactly when HUF_decompress1X1_DCtx_wksp /
   HUF_decompress4X_hufOnly_wksp (ty = 2) or HUF_decompress1X/4X_usingDTable (ty = 3) succeed, with
   l their n decoded bytes and t' the table dctx->HUFptr designates afterwards (for ty = 3, t).

   The C-exact pieces of the proof layer this model needs (FSE_readNCount_body, ZSTD_decodeSequence, its
   offset resolution) are section parameters too, named at their declaration.

   Every function is total and structural; the copies run on nat fuel equal to the number of bytes or
   16-byte chunks the C copies, the sequence loop on fuel nbSeq (one sequence per iteration, as the C's
   loops). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast.
Require Import Zstd.proof.model.Fse Zstd.proof.model.Block.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* WILDCOPY_OVERLENGTH (lib/common/zstd_internal.h) *)
Definition XWILDCOPY : Z := 32.
(* ZSTD_LITBUFFEREXTRASIZE = BOUNDED(64, ZSTD_DECODER_INTERNAL_BUFFER = 1 << 16, 128 << 10)
   (lib/decompress/zstd_decompress_internal.h) *)
Definition XLITEXTRA : Z := 65536.

(* the three sequence tables LL, OF, ML *)
Definition seq_tabs : Type := (fse_table * fse_table * fse_table)%type.

(* the repeat offsets as the context stores them between blocks: dctx->entropy.rep[i] =
   (U32)seqState.prevOffset[i] (end of each ZSTD_decompressSequences* body) *)
Definition x_rep32 (rep: Z * Z * Z) : Z * Z * Z :=
  let '(r1, r2, r3) := rep in (r1 mod 2 ^ 32, r2 mod 2 ^ 32, r3 mod 2 ^ 32).

(* ---------- literals placement (ZSTD_allocateLiteralsBuffer, 83-129) ---------- *)

(* where the literals of a block are read from:
   - XL_in_dst: in dst after the block's room (litBuffer = dst + blockSizeMax + WILDCOPY_OVERLENGTH);
     the sequences' output end is then litBuffer (oend = bsm + 32 bytes from dst);
   - XL_extra: in dctx->litExtraBuffer (ZSTD_not_in_dst);
   - XL_split: the first litSize - XLITEXTRA literals in dst, ending WILDCOPY_OVERLENGTH bytes before
     dst + expectedWriteSize, the last XLITEXTRA ones in dctx->litExtraBuffer (ZSTD_split);
   - XL_src: raw literals read in place from the block (ZSTD_not_in_dst, litPtr into src). *)
Inductive xlitloc : Type := XL_in_dst | XL_extra | XL_split | XL_src.

Definition xl_is_split (l: xlitloc) : bool := match l with XL_split => true | _ => false end.

(* ZSTD_allocateLiteralsBuffer(dctx, dst, cap, litSize, streaming, expectedWriteSize, _): its choice
   (the two split variants, splitImmediately or not, end with the same layout: see x_split_L0) *)
Definition x_alloc_loc (cap litSize bsm: Z) (streaming: bool) : xlitloc :=
  if negb streaming && (cap >? bsm + XWILDCOPY + litSize + XWILDCOPY) then XL_in_dst
  else if litSize <=? XLITEXTRA then XL_extra
  else XL_split.

(* The placement ZSTD_decodeLiteralsBlock leaves for the literals section at the start of b, which took
   lused bytes and gave litSize literals: raw literals followed by at least WILDCOPY_OVERLENGTH more bytes
   of the block are referenced in place (set_basic, 297-302); every other section goes where
   ZSTD_allocateLiteralsBuffer puts it. *)
Definition x_litloc (b: list Z) (lused litSize bsm cap: Z) (streaming: bool) : xlitloc :=
  if (Z.land (byte_at b 0) 3 =? 0) && (lused + XWILDCOPY <=? Zlength b) then XL_src
  else x_alloc_loc cap litSize bsm streaming.

(* The split layout, positions from dst, ews = expectedWriteSize = MIN(blockSizeMax, dstCapacity):
   the dst part (D = litSize - XLITEXTRA literals) starts at L0 = ews - litSize + XLITEXTRA - 32 and
   ends at ews - 32.  splitImmediately (raw / RLE, 116-120): placed there at once; Huffman (121-124,
   then 236-246): decoded at dst + ews - litSize, the last XLITEXTRA bytes copied to litExtraBuffer, the
   rest moved up by XLITEXTRA - 32. *)
Definition x_split_L0 (ews litSize: Z) : Z := ews - litSize + XLITEXTRA - XWILDCOPY.

Section ExBlock.
Variable xhuf : Type.
Variable x_lits_huf : option xhuf -> Z -> bool -> list Z -> Z -> option (list Z * xhuf).

(* Three C-exact functions, parameters here and instantiated with them (model/Exact.v, dec/B/blk/BlkIface.v):
   - x_ncount_body := EntC.ncount_c (src/proof/model/EntC.v): FSE_readNCount_body on a header
     of at least 8 bytes, (normalized counts, accuracy log, bytes used);
   - x_dseq_one := ExCSeq.dseq_one (src/proof/model/ExCSeq.v): one ZSTD_decodeSequence
     on the bitstream V (isLastSeq = last) from states (LL, OF, ML) at bit position pos: the sequence (with
     its offset VALUE ov), the next states, the new position; None when a read goes below bit 0;
   - x_c_offset := ExCSeq.c_offset: ZSTD_decodeSequence's offset resolution on size_t repeat
     offsets ((size_t)-1 for an invalid repeat), the offset and the new repeat offsets.
   (The decoder's proofs use the same functions: dec/B/ent/EntModel.v and dec/B/blk/BlkSeqDecModel.v export
   those files.) *)
Variable x_ncount_body : list Z -> Z -> option (list Z * Z * Z).
Variable x_dseq_one : fse_table -> fse_table -> fse_table -> list Z -> bool -> Z -> Z -> Z -> Z ->
  option (sequence * (Z * Z * Z) * Z).
Variable x_c_offset : Z * Z * Z -> Z -> Z -> Z * (Z * Z * Z).

(* ---------- the entropy state between the blocks of a frame ---------- *)

(* x_huf: the Huffman table of the last compressed literals (dctx->HUFptr; None while
   dctx->litEntropy = 0); x_seq: the tables LL, OF, ML of the last block with sequences (dctx->LLTptr,
   OFTptr, MLTptr; None while dctx->fseEntropy = 0); x_rep: dctx->entropy.rep; x_lxb: the
   XLITEXTRA + 32 bytes of dctx->litExtraBuffer.  zstd's copies read up to 32 bytes past the literals
   they copy and store them past the output (wild-copy overshoot); from litExtraBuffer those are bytes
   of earlier blocks, and an extDict match after a ring wrap can read them back, so the buffer is part
   of the state.  ZSTD_decompressBegin does not touch it. *)
Record xst := { x_huf : option xhuf; x_seq : option seq_tabs; x_rep : Z * Z * Z; x_lxb : list Z }.

(* ZSTD_decompressBegin without a dictionary (litEntropy = fseEntropy = 0, rep = 1, 4, 8), keeping
   litExtraBuffer *)
Definition xst_begin (st: xst) : xst := {| x_huf := None; x_seq := None; x_rep := (1, 4, 8); x_lxb := x_lxb st |}.

(* ... on a new context (calloc'd, patch item 17), or after ZSTD_DCtx_reset with the parameters (F8 clears
   the literal buffer): litExtraBuffer all zeros *)
Definition xst_init : xst :=
  {| x_huf := None; x_seq := None; x_rep := (1, 4, 8); x_lxb := repeat 0 (Z.to_nat (XLITEXTRA + XWILDCOPY)) |}.

(* ---------- the literals section (ZSTD_decodeLiteralsBlock, 139-347) ---------- *)

(* ZSTD_decodeLiteralsBlock(dctx, b, |b|, dst, cap, streaming) with blockSizeMax = bsm and
   wmax = expectedWriteSize = MIN(bsm, cap): the literals, the bytes the section takes, the Huffman table
   kept.  dst is not NULL (one-shot and streaming decoding always pass a non-NULL block start), so the
   `litSize > 0 && dst == NULL` checks never fire.  `streaming` plays no role in the result (only in the
   placement, x_litloc). *)
Definition x_lits (hprev: option xhuf) (b: list Z) (bsm wmax: Z) (streaming: bool)
    : option (list Z * Z * option xhuf) :=
  let n := Zlength b in
  if n <? 2 then None else                                    (* MIN_CBLOCK_SIZE, 144 *)
  let b0 := byte_at b 0 in
  let ty := Z.land b0 3 in
  let lhl := Z.land (Z.shiftr b0 2) 3 in
  if ty =? 0 then
    (* set_basic, 273-303 *)
    if (lhl =? 3) && (n <? 3) then None else
    let '(lh, litSize) :=
      if lhl =? 1 then (2, Z.shiftr (le_field b 0 2) 4)
      else if lhl =? 3 then (3, Z.shiftr (le_field b 0 3) 4)
      else (1, Z.shiftr b0 3) in
    if litSize >? bsm then None else
    if wmax <? litSize then None else
    if lh + litSize >? n then None else
    Some (slice b lh litSize, lh + litSize, hprev)
  else if ty =? 1 then
    (* set_rle, 305-340 *)
    if (lhl =? 1) && (n <? 3) then None else
    if (lhl =? 3) && (n <? 4) then None else
    let '(lh, litSize) :=
      if lhl =? 1 then (2, Z.shiftr (le_field b 0 2) 4)
      else if lhl =? 3 then (3, Z.shiftr (le_field b 0 3) 4)
      else (1, Z.shiftr b0 3) in
    if litSize >? bsm then None else
    if wmax <? litSize then None else
    Some (repeat (byte_at b lh) (Z.to_nat litSize), lh + 1, hprev)
  else
    (* set_repeat (3, needs litEntropy) and set_compressed (2), 152-271 *)
    if (ty =? 3) && (match hprev with None => true | Some _ => false end) then None else
    if n <? 5 then None else
    let lhc := le_field b 0 4 in
    let '(lh, litSize, litCSize, single) :=
      if lhl =? 2 then (4, Z.land (Z.shiftr lhc 4) 16383, Z.shiftr lhc 18, false)
      else if lhl =? 3 then (5, Z.land (Z.shiftr lhc 4) 262143, Z.shiftr lhc 22 + byte_at b 4 * 1024, false)
      else (3, Z.land (Z.shiftr lhc 4) 1023, Z.land (Z.shiftr lhc 14) 1023, lhl =? 0) in
    if litSize >? bsm then None else
    if negb single && (litSize <? MIN_LITERALS_FOR_4_STREAMS) then None else
    if litCSize + lh >? n then None else
    if wmax <? litSize then None else
    match x_lits_huf hprev ty single (slice b lh litCSize) litSize with
    | Some (l, t) => Some (l, lh + litCSize, Some t)
    | None => None
    end.

(* ---------- the sequences section header (ZSTD_decodeSeqHeaders 702-785, ZSTD_buildSeqTable 654-700) ---------- *)

(* FSE_readNCount on the window s (lib/common/entropy_common.c FSE_readNCount_body): at least 8 bytes,
   the body itself (x_ncount_body); fewer, the body on a zero-padded 8-byte copy, then an error when
   it used more than |s| bytes.  Result: (normalized counts, accuracy log, bytes used). *)
Definition x_ncount (s: list Z) (maxsv: Z) : option (list Z * Z * Z) :=
  if Zlength s <? 8 then
    match x_ncount_body (s ++ repeat 0 (Z.to_nat (8 - Zlength s))) maxsv with
    | Some (norm, log, size) => if size >? Zlength s then None else Some (norm, log, size)
    | None => None
    end
  else x_ncount_body s maxsv.

(* ZSTD_buildSeqTable for one code type: mode 0 predefined, 1 RLE, 2 FSE-compressed, 3 repeat (prev =
   the table of the previous block, None while fseEntropy = 0); the table and the bytes it takes.
   The C tables built by ZSTD_buildSeqTable_rle / ZSTD_buildFSETable are fse_rle / fse_build (with the
   code tables of Block.v); the predefined ones are LL/OF/ML_predef. *)
Definition x_seq_table (mode: Z) (predef: fse_table) (prev: option fse_table) (max maxLog: Z) (b: list Z)
    : option (fse_table * Z) :=
  if mode =? 0 then Some (predef, 0)
  else if mode =? 1 then
    (if Zlength b <? 1 then None
     else if byte_at b 0 >? max then None
     else Some (fse_rle (byte_at b 0), 1))
  else if mode =? 3 then
    match prev with Some t => Some (t, 0) | None => None end
  else
    match x_ncount b max with
    | None => None
    | Some (norm, log, size) =>
        if log >? maxLog then None else Some (fse_build norm log, size)
    end.

(* ZSTD_decodeSeqHeaders on the rest b of the block: nbSeq, the tables (unchanged when nbSeq = 0), the
   bytes the header takes. *)
Definition x_seq_header (prev: option seq_tabs) (b: list Z) : option (Z * option seq_tabs * Z) :=
  let n := Zlength b in
  if n <? 1 then None else                                    (* MIN_SEQUENCES_SIZE *)
  let b0 := byte_at b 0 in
  let '(nbSeq, pos, ok) :=
    if b0 <=? 127 then (b0, 1, true)
    else if b0 =? 255 then (le_field b 1 2 + LONGNBSEQ, 3, 3 <=? n)
    else ((b0 - 128) * 256 + byte_at b 1, 2, 2 <=? n) in
  if negb ok then None else
  if nbSeq =? 0 then (if pos =? n then Some (0, prev, pos) else None) else
  if pos + 1 >? n then None else
  let modes := byte_at b pos in
  if negb (Z.land modes 3 =? 0) then None else
  let pos := pos + 1 in
  let pLL := option_map (fun '(l, _, _) => l) prev in
  let pOF := option_map (fun '(_, o, _) => o) prev in
  let pML := option_map (fun '(_, _, m) => m) prev in
  match x_seq_table (Z.shiftr modes 6) LL_predef pLL MaxLL LLFSELog (skipn (Z.to_nat pos) b) with
  | None => None
  | Some (tLL, k1) =>
    let pos := pos + k1 in
    match x_seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef pOF MaxOff OffFSELog (skipn (Z.to_nat pos) b) with
    | None => None
    | Some (tOF, k2) =>
      let pos := pos + k2 in
      match x_seq_table (Z.land (Z.shiftr modes 2) 3) ML_predef pML MaxML MLFSELog (skipn (Z.to_nat pos) b) with
      | None => None
      | Some (tML, k3) => Some (nbSeq, Some (tLL, tOF, tML), pos + k3)
      end
    end
  end.

(* ---------- the memory zstd reads and writes ---------- *)

(* The three objects a block's decoding reads: the destination region (R_dst: cells addressed from its
   base, None = never written), dctx->litExtraBuffer (R_lxb, XLITEXTRA + 32 cells, all defined: the
   context is calloc'd, patch item 17) and the block's input (R_src, read only).  Every read of a cell
   that is not defined (a never-written destination cell, a cell outside litExtraBuffer or the block)
   makes the model return None; the existing safety proof of the decoder shows that zstd never makes
   such a read (its copies read only defined bytes, docs/port-beta), so this None never contradicts the
   C. *)
Inductive xreg : Type := R_dst | R_lxb | R_src.

Record xmem := { xm_dst : list (option Z); xm_lxb : list Z }.

Section Mem.
Variable src : list Z.   (* the block's input *)

Definition xm_rd (m: xmem) (r: xreg) (i: Z) : option Z :=
  if i <? 0 then None else
  match r with
  | R_dst => nth (Z.to_nat i) (xm_dst m) None
  | R_lxb => if i <? Zlength (xm_lxb m) then Some (byte_at (xm_lxb m) i) else None
  | R_src => if i <? Zlength src then Some (byte_at src i) else None
  end.

(* a store of one byte; a destination cell past the written ones extends the region (cells skipped stay
   never written) *)
Definition xm_wr (m: xmem) (r: xreg) (i v: Z) : option xmem :=
  if i <? 0 then None else
  match r with
  | R_dst =>
      let d := xm_dst m in
      Some {| xm_dst := if i <? Zlength d then upd d (Z.to_nat i) (Some v)
                        else d ++ repeat None (Z.to_nat (i - Zlength d)) ++ [Some v];
              xm_lxb := xm_lxb m |}
  | R_lxb =>
      if i <? Zlength (xm_lxb m) then Some {| xm_dst := xm_dst m; xm_lxb := upd (xm_lxb m) (Z.to_nat i) v |}
      else None
  | R_src => None
  end.

(* k bytes copied forwards one at a time, each read after the previous one is written: the C library's
   memcpy (a byte loop), ZSTD_copy8 / ZSTD_copy4 (memcpy), the one-byte ZSTD_memmove loops of
   ZSTD_safecopy*, ZSTD_overlapCopy8 *)
Fixpoint xm_fwd (k: nat) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z) : option xmem :=
  match k with
  | O => Some m
  | S k' =>
      match xm_rd m rs s with
      | None => None
      | Some v => match xm_wr m rd d v with
                  | None => None
                  | Some m => xm_fwd k' m rd (d + 1) rs (s + 1)
                  end
      end
  end.

Fixpoint xm_rdn (k: nat) (m: xmem) (r: xreg) (i: Z) : option (list Z) :=
  match k with
  | O => Some nil
  | S k' => match xm_rd m r i, xm_rdn k' m r (i + 1) with
            | Some v, Some vs => Some (v :: vs)
            | _, _ => None
            end
  end.

Fixpoint xm_wrn (vs: list Z) (m: xmem) (r: xreg) (i: Z) : option xmem :=
  match vs with
  | nil => Some m
  | v :: vs' => match xm_wr m r i v with Some m => xm_wrn vs' m r (i + 1) | None => None end
  end.

(* k bytes moved: all read, then all written: the C library's memmove (a true move), ZSTD_copy16 (16 bytes
   through a local buffer, zstd_internal.h: neither SSE2 nor NEON in this build) *)
Definition xm_move (k: nat) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z) : option xmem :=
  match xm_rdn k m rs s with Some vs => xm_wrn vs m rd d | None => None end.

(* k ZSTD_copy16 at stride 16 *)
Fixpoint xm_chunks16 (k: nat) (m: xmem) (d: Z) (rs: xreg) (s: Z) : option xmem :=
  match k with
  | O => Some m
  | S k' => match xm_move 16 m R_dst d rs s with
            | Some m => xm_chunks16 k' m (d + 16) rs (s + 16)
            | None => None
            end
  end.

(* ZSTD_wildcopy(d, s, len, ovtype) (zstd_internal.h 218-247); srcb4 = ZSTD_overlap_src_before_dst (then s
   is in dst too).  Short-offset case: COPY8 until len is covered (at least once); otherwise one
   ZSTD_copy16, and when len > 16 pairs of ZSTD_copy16 until len is covered. *)
Definition xm_wild (m: xmem) (d: Z) (rs: xreg) (s len: Z) (srcb4: bool) : option xmem :=
  if srcb4 && (d - s <? 16) then
    xm_fwd (Z.to_nat (8 * Z.max 1 ((len + 7) / 8))) m R_dst d rs s
  else
    let nch := if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32) in
    xm_chunks16 (Z.to_nat nch) m d rs s.

Definition xdec32 (o: Z) : Z := nth (Z.to_nat o) [0; 1; 2; 1; 4; 4; 4; 4] 0.
Definition xdec64 (o: Z) : Z := nth (Z.to_nat o) [8; 8; 8; 7; 8; 9; 10; 11] 0.

(* ZSTD_overlapCopy8(&op, &ip, off) (822-843), ip in dst: the new memory, op and ip *)
Definition xm_ov8 (m: xmem) (op ip off: Z) : option (xmem * Z * Z) :=
  if off <? 8 then
    match xm_fwd 4 m R_dst op R_dst ip with
    | None => None
    | Some m =>
        let ip1 := ip + xdec32 off in
        match xm_fwd 4 m R_dst (op + 4) R_dst ip1 with
        | Some m => Some (m, op + 8, ip1 - xdec64 off + 8)
        | None => None
        end
    end
  else match xm_fwd 8 m R_dst op R_dst ip with Some m => Some (m, op + 8, ip + 8) | None => None end.

(* ZSTD_safecopy(op, oend_w, ip, len, ovtype) (857-891) *)
Definition xm_safecopy (m: xmem) (op oend_w: Z) (rs: xreg) (ip len: Z) (srcb4: bool) : option xmem :=
  let oend := op + len in
  if len <? 8 then xm_fwd (Z.to_nat len) m R_dst op rs ip else
  match (if srcb4 then xm_ov8 m op ip (op - ip) else Some (m, op, ip)) with
  | None => None
  | Some (m, op1, ip1) =>
      let len1 := if srcb4 then len - 8 else len in
      if oend_w - oend >=? 0 then xm_wild m op1 rs ip1 len1 srcb4 else
      let '(mo, op2, ip2) :=
        if oend_w - op1 >=? 0 then (xm_wild m op1 rs ip1 (oend_w - op1) srcb4, oend_w, ip1 + (oend_w - op1))
        else (Some m, op1, ip1) in
      match mo with
      | None => None
      | Some m => xm_fwd (Z.to_nat (oend - op2)) m R_dst op2 rs ip2
      end
  end.

(* ZSTD_safecopyDstBeforeSrc(op, ip, len) (896-915), ip in dst *)
Definition xm_sdbs (m: xmem) (op ip len: Z) : option xmem :=
  let diff := op - ip in
  if (len <? 8) || (diff >? -8) then xm_fwd (Z.to_nat len) m R_dst op R_dst ip else
  let '(mo, op1, ip1) :=
    if (len >=? 32) && (diff <? -16) then (xm_wild m op R_dst ip (len - 32) false, op + len - 32, ip + len - 32)
    else (Some m, op, ip) in
  match mo with
  | None => None
  | Some m => xm_fwd (Z.to_nat (op + len - op1)) m R_dst op1 R_dst ip1
  end.
End Mem.

(* ---------- executing the sequences ---------- *)

(* What the execution of one block's sequences depends on, fixed for the block (addresses in the
   destination region): its input; prefixStart, virtualStart (= prefixStart - (dictEnd - dictStart)),
   dictEnd; the output end oend (litBuffer when the literals lie in dst after the block's room, else
   dst + dstCapacity). *)
Record xenv := { xe_src : list Z; xe_ps : Z; xe_vs : Z; xe_de : Z; xe_oend : Z }.

(* The match of a sequence, written at oLitEnd (after its literals): from the extDict when the offset
   exceeds oLitEnd - prefixStart (an error beyond oLitEnd - virtualStart; ZSTD_memmove from
   dictEnd + (match - prefixStart), then the rest from prefixStart), then within the prefix: in the fast
   path (wo = None) ZSTD_wildcopy, or ZSTD_overlapCopy8 and ZSTD_wildcopy (src before dst) for offsets
   below 16 (1076-1121, 1171-1212); in the slow paths (wo = Some oend_w) ZSTD_safecopy (src before dst)
   (950-969, 1001-1020). *)
Definition xm_prefix (e: xenv) (m: xmem) (op mt ml off: Z) (wo: option Z) : option xmem :=
  let src := xe_src e in
  match wo with
  | Some w => xm_safecopy src m op w R_dst mt ml true
  | None =>
      if off >=? 16 then xm_wild src m op R_dst mt ml false else
      match xm_ov8 src m op mt off with
      | None => None
      | Some (m, op1, mt1) => if ml >? 8 then xm_wild src m op1 R_dst mt1 (ml - 8) true else Some m
      end
  end.

Definition xm_match (e: xenv) (m: xmem) (oLitEnd ml off: Z) (wo: option Z) : option xmem :=
  if off >? oLitEnd - xe_ps e then
    if off >? oLitEnd - xe_vs e then None else
    let mt := xe_de e + (oLitEnd - off - xe_ps e) in
    if xe_de e - mt >=? ml then xm_move (xe_src e) (Z.to_nat ml) m R_dst oLitEnd R_dst mt else
    let l1 := xe_de e - mt in
    match xm_move (xe_src e) (Z.to_nat l1) m R_dst oLitEnd R_dst mt with
    | None => None
    | Some m => xm_prefix e m (oLitEnd + l1) (xe_ps e) (ml - l1) off wo
    end
  else xm_prefix e m oLitEnd (oLitEnd - off) ml off wo.

(* ZSTD_execSequence (1025-1122) / ZSTD_execSequenceEnd (927-970): sequence (ll, ml, off) at op, literals at
   index li of region lr, ending at llim.  The new memory, op and literal index.  Slow path when the
   literals end before ll or the sequence does not end 32 bytes before oend: errors when it does not
   fit before oend or the literals are missing; ZSTD_safecopy of the literals.  Fast path: ZSTD_copy16,
   ZSTD_wildcopy beyond 16 literals.  Then the match (its offset error). *)
Definition x_exec (e: xenv) (m: xmem) (op: Z) (lr: xreg) (li llim ll ml off: Z) : option (xmem * Z * Z) :=
  let src := xe_src e in
  let oLitEnd := op + ll in
  let oend_w := xe_oend e - XWILDCOPY in
  if (llim - li <? ll) || (oend_w - op <? ll + ml) then
    if ll + ml >? xe_oend e - op then None else
    if ll >? llim - li then None else
    match xm_safecopy src m op oend_w lr li ll false with
    | None => None
    | Some m => match xm_match e m oLitEnd ml off (Some oend_w) with
                | Some m => Some (m, op + ll + ml, li + ll)
                | None => None
                end
    end
  else
    match xm_move src 16 m R_dst op lr li with
    | None => None
    | Some m =>
        match (if ll >? 16 then xm_wild src m (op + 16) lr (li + 16) (ll - 16) false else Some m) with
        | None => None
        | Some m => match xm_match e m oLitEnd ml off None with
                    | Some m => Some (m, op + ll + ml, li + ll)
                    | None => None
                    end
        end
    end.

(* ZSTD_execSequenceSplitLitBuffer (1126-1213) / ZSTD_execSequenceEndSplitLitBuffer (977-1021): the
   literals in dst at li (their part in dst ends at llim), oend_w = iLitEnd - 32 (1620).  The slow path
   also refuses an output starting strictly inside the literals it copies (997) and copies them with
   ZSTD_safecopyDstBeforeSrc. *)
Definition x_exec_split (e: xenv) (m: xmem) (op li llim ll ml off: Z) : option (xmem * Z * Z) :=
  let src := xe_src e in
  let oLitEnd := op + ll in
  let oend_w := li + ll - XWILDCOPY in
  if (llim - li <? ll) || (oend_w - op <? ll + ml) then
    if ll + ml >? xe_oend e - op then None else
    if ll >? llim - li then None else
    if (op >? li) && (op <? li + ll) then None else
    match xm_sdbs src m op li ll with
    | None => None
    | Some m => match xm_match e m oLitEnd ml off (Some oend_w) with
                | Some m => Some (m, op + ll + ml, li + ll)
                | None => None
                end
    end
  else
    match xm_move src 16 m R_dst op R_dst li with
    | None => None
    | Some m =>
        match (if ll >? 16 then xm_wild src m (op + 16) R_dst (li + 16) (ll - 16) false else Some m) with
        | None => None
        | Some m => match xm_match e m oLitEnd ml off None with
                    | Some m => Some (m, op + ll + ml, li + ll)
                    | None => None
                    end
        end
    end.

(* the execution state: memory, op, the literal pointer (region, index) and its limit (litBufferEnd), and
   whether the literals are still split with the cursor in their dst part (litBufferLocation ==
   ZSTD_split) *)
Record xex := { xmm : xmem; xop : Z; xlr : xreg; xli : Z; xlim : Z; xsp : bool }.

(* One sequence as ZSTD_decompressSequences_bodySplitLitBuffer (1521-1728) / ZSTD_decompressSequences_body
   (1732-1807) execute it.  Split, dst part: when the sequence needs more literals than the dst part has
   left (1619), the leftover is copied with ZSTD_safecopyDstBeforeSrc (checked against oend, 1638), the
   literals continue in litExtraBuffer and the rest of the sequence runs as ZSTD_execSequence; otherwise
   ZSTD_execSequenceSplitLitBuffer.  Elsewhere ZSTD_execSequence. *)
Definition x_step (e: xenv) (s: xex) (ll ml off: Z) : option xex :=
  let m := xmm s in let op := xop s in
  if xsp s then
    let left := xlim s - xli s in
    if left <? ll then
      let mo :=
        if left =? 0 then Some (m, op) else
        if left >? xe_oend e - op then None else
        match xm_sdbs (xe_src e) m op (xli s) left with Some m => Some (m, op + left) | None => None end in
      match mo with
      | None => None
      | Some (m, op) =>
          match x_exec e m op R_lxb 0 XLITEXTRA (ll - left) ml off with
          | Some (m, op, li) => Some {| xmm := m; xop := op; xlr := R_lxb; xli := li; xlim := XLITEXTRA; xsp := false |}
          | None => None
          end
      end
    else
      match x_exec_split e m op (xli s) (xlim s) ll ml off with
      | Some (m, op, li) => Some {| xmm := m; xop := op; xlr := R_dst; xli := li; xlim := xlim s; xsp := true |}
      | None => None
      end
  else
    match x_exec e m op (xlr s) (xli s) (xlim s) ll ml off with
    | Some (m, op, li) => Some {| xmm := m; xop := op; xlr := xlr s; xli := li; xlim := xlim s; xsp := false |}
    | None => None
    end.

(* The sequence loop: k sequences left, FSE states st = (LL, OF, ML), bit position pos, repeat offsets
   rep (size_t values).  Each iteration decodes one sequence (ZSTD_decodeSequence, isLastSeq when it is
   the last: x_dseq_one, its offset resolved by x_c_offset) and executes it.
   x_dseq_one fails exactly when a read goes below the start of the bitstream; zstd then keeps decoding
   values from an overflowed container (bitsConsumed > 64, which only grows), and its final
   BIT_endOfDStream check fails: an error either way (the sequences it still executes write only the
   destination, whose contents do not matter after an error).  Fuel = nbSeq, one per iteration. *)
Fixpoint x_seq_loop (e: xenv) (tLL tOF tML: fse_table) (V: list Z) (k: nat) (st: Z * Z * Z) (pos: Z)
    (rep: Z * Z * Z) (s: xex) : option (xex * Z * (Z * Z * Z)) :=
  match k with
  | O => Some (s, pos, rep)
  | S k' =>
      let '(sLL, sOF, sML) := st in
      match x_dseq_one tLL tOF tML V (Nat.eqb k' 0) sLL sOF sML pos with
      | None => None
      | Some (sq, st', pos') =>
          let '(off, rep') := x_c_offset rep (sq_ll sq) (sq_ov sq) in
          match x_step e s (sq_ll sq) (sq_ml sq) off with
          | None => None
          | Some s' => x_seq_loop e tLL tOF tML V k' st' pos' rep' s'
          end
      end
  end.

(* The last literals (after the loops): split with the cursor in dst, first the dst part (ZSTD_memmove,
   checked against oend), then litExtraBuffer from its start; then the literals left (checked against
   oend, memcpy).  The memory and the final op. *)
Definition x_last (e: xenv) (s: xex) : option (xmem * Z) :=
  let src := xe_src e in
  let st :=
    if xsp s then
      let n1 := xlim s - xli s in
      if n1 >? xe_oend e - xop s then None else
      match xm_move src (Z.to_nat n1) (xmm s) R_dst (xop s) R_dst (xli s) with
      | Some m => Some (m, xop s + n1, R_lxb, 0, XLITEXTRA)
      | None => None
      end
    else Some (xmm s, xop s, xlr s, xli s, xlim s) in
  match st with
  | None => None
  | Some (m, op, lr, li, lim) =>
      let n := lim - li in
      if n >? xe_oend e - op then None else
      match xm_fwd src (Z.to_nat n) m R_dst op lr li with
      | Some m => Some (m, op + n)
      | None => None
      end
  end.

(* The sequences of a block with nbSeq > 0 sequences, tables tabs, repeat offsets rep, bitstream bits,
   from the state s0 after the literals section: BIT_initDStream (an error on an empty stream or a last
   byte 0: Bitstream.bs_okb), the three ZSTD_initFseState (LL, OF, ML), the loop, BIT_endOfDStream (all
   bits read: position 0), the U32 repeat offsets, the last literals.  The memory, the final op, the
   new repeat offsets.

   The decoder zstd picks: ZSTD_decompressBlock_internal calls ZSTD_decompressSequencesLong when
   usePrefetchDecoder (dctx->ddictIsCold, or a share of long offsets in the OF table when the history
   exceeds 16 MiB and nbSeq > 8), otherwise ZSTD_decompressSequencesSplitLitBuffer (split layout) or
   ZSTD_decompressSequences.  On 64-bit isLongOffset is 0 and the three give the same outcome on every
   input, so this one function models all of them:
   - decoding never reads or writes memory (the bit reads, FSE states and repeat offsets live in
     seqState), so the long decoder (1854-2011), which decodes up to 8 sequences ahead, executes the
     same sequences in the same order;
   - its per-sequence execution is the short decoders' (the same split transition test, leftover copy
     and check, ZSTD_execSequenceSplitLitBuffer / ZSTD_execSequence with the same oend: litBuffer for
     literals in dst after the block's room, dst + dstCapacity otherwise), and so are its last literals
     (memmove where the short bodies use memcpy, on ranges that do not overlap);
   - it checks BIT_endOfDStream before executing the last (up to 8) sequences, the short decoders after:
     every check is an error and nothing else differs, so both fail or both succeed, with the same
     memory; ZSTD_prefetchMatch has no effect. *)
Definition x_seqs (e: xenv) (tabs: seq_tabs) (rep: Z * Z * Z) (bits: list Z) (nbSeq: Z) (s0: xex)
    : option (xmem * Z * (Z * Z * Z)) :=
  let '(tLL, tOF, tML) := tabs in
  if negb (bs_okb bits) then None else
  match rd bits (bs_total bits) (ft_log tLL) with None => None | Some (sLL, pos) =>
  match rd bits pos (ft_log tOF) with None => None | Some (sOF, pos) =>
  match rd bits pos (ft_log tML) with None => None | Some (sML, pos) =>
  match x_seq_loop e tLL tOF tML bits (Z.to_nat nbSeq) (sLL, sOF, sML) pos rep s0 with
  | None => None
  | Some (s, pos, rep') =>
      if negb (pos =? 0) then None else
      match x_last e s with
      | Some (m, op) => Some (m, op, x_rep32 rep')
      | None => None
      end
  end end end end.

(* ---------- the literals' stores (ZSTD_allocateLiteralsBuffer, ZSTD_decodeLiteralsBlock) ---------- *)

(* The stores of ZSTD_decodeLiteralsBlock for the section at the start of body (lused bytes, literals lits,
   from x_lits), the block written at op0 with capacity cap, ews = MIN(bsm, cap), in C's order:
   ZSTD_allocateLiteralsBuffer's zeroed slack (patch item 19: after literals in dst after the block's room;
   after the dst part of literals split at once, raw / RLE), then the literals: raw copied (or read in
   place: no store), RLE set, Huffman decoded (its decoder stores exactly the n decoded bytes at
   litBuffer) and, split, its last XLITEXTRA bytes copied to litExtraBuffer and its dst part moved up by
   XLITEXTRA - 32 (236-246).  Returns the memory, the literal pointer (region, index), its limit
   (litBufferEnd), and whether the literals are split. *)
Definition x_lits_store (body lits: list Z) (lused: Z) (m: xmem) (op0 ews bsm cap: Z) (streaming: bool)
    : option (xmem * xreg * Z * Z * bool) :=
  let litSize := Zlength lits in
  let ty := Z.land (byte_at body 0) 3 in
  let loc := x_alloc_loc cap litSize bsm streaming in
  let D := litSize - XLITEXTRA in
  let sImm := ty <=? 1 in
  let '(lr, lb, lbe) :=
    match loc with
    | XL_in_dst => (R_dst, op0 + bsm + XWILDCOPY, op0 + bsm + XWILDCOPY + litSize)
    | XL_split => if sImm then (R_dst, op0 + x_split_L0 ews litSize, op0 + ews - XWILDCOPY)
                  else (R_dst, op0 + ews - litSize, op0 + ews)
    | _ => (R_lxb, 0, litSize)
    end in
  let split := xl_is_split loc in
  let mz :=
    match loc with
    | XL_in_dst => xm_wrn (repeat 0 32) m R_dst lbe
    | XL_split => if sImm then xm_wrn (repeat 0 32) m R_dst lbe else Some m
    | _ => Some m
    end in
  match mz with
  | None => None
  | Some m =>
    if ty =? 0 then
      let lh := lused - litSize in
      if lused + XWILDCOPY <=? Zlength body then Some (m, R_src, lh, lh + litSize, false) else
      if split then
        match xm_fwd body (Z.to_nat D) m R_dst lb R_src lh with
        | None => None
        | Some m => match xm_fwd body (Z.to_nat XLITEXTRA) m R_lxb 0 R_src (lh + D) with
                    | Some m => Some (m, R_dst, lb, lbe, true)
                    | None => None
                    end
        end
      else
        match xm_fwd body (Z.to_nat litSize) m lr lb R_src lh with
        | Some m => Some (m, lr, lb, lbe, false)
        | None => None
        end
    else if ty =? 1 then
      let v := byte_at body (lused - 1) in
      if split then
        match xm_wrn (repeat v (Z.to_nat D)) m R_dst lb with
        | None => None
        | Some m => match xm_wrn (repeat v (Z.to_nat XLITEXTRA)) m R_lxb 0 with
                    | Some m => Some (m, R_dst, lb, lbe, true)
                    | None => None
                    end
        end
      else
        match xm_wrn (repeat v (Z.to_nat litSize)) m lr lb with
        | Some m => Some (m, lr, lb, lbe, false)
        | None => None
        end
    else
      match xm_wrn lits m lr lb with
      | None => None
      | Some m =>
          if split then
            match xm_fwd body (Z.to_nat XLITEXTRA) m R_lxb 0 R_dst (lbe - XLITEXTRA) with
            | None => None
            | Some m =>
                match xm_move body (Z.to_nat D) m R_dst (lb + XLITEXTRA - XWILDCOPY) R_dst lb with
                | Some m => Some (m, R_dst, lb + XLITEXTRA - XWILDCOPY, lbe - XWILDCOPY, true)
                | None => None
                end
            end
          else Some (m, lr, lb, lbe, false)
      end
  end.

(* the written cells of a destination region, up to the first never-written one *)
Fixpoint x_written (d: list (option Z)) : list Z :=
  match d with
  | Some v :: d' => v :: x_written d'
  | _ => nil
  end.

(* ---------- a compressed block (ZSTD_decompressBlock_internal, 2194-2303) ---------- *)

(* ZSTD_decompressBlock_internal(dctx, dst, cap, body, |body|, streaming) for a compressed block, in the
   destination region mem (its written cells, addressed from its base; cells at index >= |mem| were never
   written), dst at address op, from the entropy state st, with blockSizeMax = bsm, prefixStart = ps,
   dictStart = ds and dictEnd = de (no extDict when ds = de; virtualStart = ps - (de - ds)).
   None iff the C returns an error (or would read a never-written cell, which the safety proof excludes);
   else the new state, the destination's written cells after the block and the block's size (its return
   value: op advances by it).  dst is not NULL and GP_DST_NEAR_TOP is 0 (quickproof.conf).

   Every read and store is the C's, in its order, on the memory as it is at that moment: a match may read
   cells the block has just written, cells of the extDict the block has overwritten (after a ring wrap),
   the literals in dst may be overwritten by the output before they are read (split layout), and the
   cells written past the block's content (wild-copy overshoot, the literal buffer, its zeroed slack) are
   in the result.  The returned cells stop at the first never-written one: the literal buffer placed
   after the block's room (one-shot only) may leave a gap after the content, and no later read reaches
   the cells beyond such a gap before the output overwrites them (a later block writes its literals
   before reading them, and reads the history only below its op or within an extDict, which the output
   of an earlier segment covered).

   One-shot decoding without a dictionary calls it with mem = the frame's output so far, ps = 0,
   op = |mem|, ds = de = 0, cap = the capacity left, streaming = false. *)
Definition x_block (st: xst) (mem: list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (streaming: bool)
    : option (xst * list Z * Z) :=
  if Zlength body >? bsm then None else                       (* srcSize_wrong, 2209 *)
  let ews := Z.min bsm cap in
  match x_lits (x_huf st) body bsm ews streaming with
  | None => None
  | Some (lits, lused, huf) =>
    let litSize := Zlength lits in
    let rest := skipn (Z.to_nat lused) body in
    match x_seq_header (x_seq st) rest with
    | None => None
    | Some (nbSeq, tabs, hused) =>
      if (nbSeq >? 0) && (cap =? 0) then None else            (* dstSize_tooSmall, 2258 *)
      let m0 := {| xm_dst := map Some mem; xm_lxb := x_lxb st |} in
      match x_lits_store body lits lused m0 op ews bsm cap streaming with
      | None => None
      | Some (m, lr, li, lim, sp) =>
        let loc := x_litloc body lused litSize bsm cap streaming in
        let e := {| xe_src := body; xe_ps := ps; xe_vs := ps - (de - ds); xe_de := de;
                    xe_oend := match loc with XL_in_dst => op + bsm + XWILDCOPY | _ => op + cap end |} in
        let s0 := {| xmm := m; xop := op; xlr := lr; xli := li; xlim := lim; xsp := sp |} in
        let bits := skipn (Z.to_nat hused) rest in
        let res :=
          if nbSeq =? 0 then
            match x_last e s0 with Some (m, op') => Some (m, op', x_rep st) | None => None end
          else
            match tabs with
            | Some t => x_seqs e t (x_rep st) bits nbSeq s0
            | None => None
            end in
        match res with
        | None => None
        | Some (m, op', rep) =>
            Some ({| x_huf := huf; x_seq := tabs; x_rep := rep; x_lxb := xm_lxb m |},
                  x_written (xm_dst m), op' - op)
        end
      end
    end
  end.

End ExBlock.

(* ---------- small cases, computed ---------- *)

Section Examples.
(* Test instances of the parameters, for these examples only: no Huffman decoding (raw and RLE literals
   only), no FSE header (predefined tables only), the last-sequence decoding step taken from
   Block.decode_seqs and the offset resolution from Block.resolve_offset (both agree with the C-exact
   functions on these inputs; the real instances are named at the section's parameters). *)
Let nohuf : option unit -> Z -> bool -> list Z -> Z -> option (list Z * unit) := fun _ _ _ _ _ => None.
Let t_ncount (s: list Z) (m: Z) : option (list Z * Z * Z) := None.
Let t_dseq (tLL tOF tML: fse_table) (V: list Z) (last: bool) (sLL sOF sML pos: Z)
    : option (sequence * (Z * Z * Z) * Z) :=
  if last then
    match decode_seqs tLL tOF tML V 1 sLL sOF sML pos with
    | Some ([sq], p) => Some (sq, (sLL, sOF, sML), p)
    | _ => None
    end
  else None.
Let t_off (rep: Z * Z * Z) (ll ov: Z) : Z * (Z * Z * Z) :=
  match resolve_offset rep ll ov with Some r => r | None => (2 ^ 64 - 1, rep) end.
Let xb := x_block unit nohuf t_ncount t_dseq t_off.
Let st0 := xst_init unit.
(* one-shot: the frame's output so far is the whole history, no extDict *)
Let os (out body: list Z) (cap: Z) := xb st0 out 0 (Zlength out) 0 0 body 131072 cap false.
(* the written cells and the size only *)
Let ms (r: option (xst unit * list Z * Z)) : option (list Z * Z) :=
  match r with Some (_, m, n) => Some (m, n) | None => None end.

(* raw literals "abc" (header 0x18: raw, 1-byte header, 3 literals), no sequences (nbSeq byte 0): the
   literals go to litExtraBuffer, the last-literals memcpy writes exactly them *)
Example x_block_raw : ms (os nil [24; 97; 98; 99; 0] 100) = Some ([97; 98; 99], 3).
Proof. vm_compute. reflexivity. Qed.

(* the same with a 2-byte output: expectedWriteSize = 2 < 3 literals *)
Example x_block_raw_small : os nil [24; 97; 98; 99; 0] 2 = None.
Proof. vm_compute. reflexivity. Qed.

(* RLE literals: header 0x29 (RLE, 1-byte header, 5 literals), byte 120, no sequences, after 2 bytes of
   earlier output *)
Example x_block_rle : ms (os [1; 2] [41; 120; 0] 10) = Some ([1; 2; 120; 120; 120; 120; 120], 5).
Proof. vm_compute. reflexivity. Qed.

(* a body larger than Block_Maximum_Size *)
Example x_block_big : xb st0 nil 0 0 0 0 [24; 97; 98; 99; 0] 4 100 false = None.
Proof. vm_compute. reflexivity. Qed.

(* the literals placed in dst after the block's room (capacity > bsm + 64 + litSize, one-shot): oend is
   litBuffer; the literal buffer lies past a gap, so only the content is returned *)
Example x_block_raw_in_dst :
  ms (xb st0 nil 0 0 0 0 [24; 97; 98; 99; 0] 10 200 false) = Some ([97; 98; 99], 3).
Proof. vm_compute. reflexivity. Qed.

(* One sequence with the predefined tables: literals "abc", then (ll 3, match 4, offset 3).
   Codes: LL 3 (base 3, no extra bit), ML 1 (base 4), OF 2 (offset value 4 + 2 extra bits = 6, a new
   offset 6 - 3 = 3).  States: the first LL state of symbol 3, OF state of symbol 2, ML state of symbol 1.
   Bitstream value (read from the top): marker bit 19, LL state (6 bits), OF state (5), ML state (6),
   the 2 offset bits (value 2). *)
Let first_state (t: fse_table) (sym: Z) : Z :=
  let l := filter (fun s => fe_sym (fse_cell t s) =? sym) (map Z.of_nat (seq 0 (length (ft_cells t)))) in
  hd 0 l.
Let seq_bits : list Z :=
  le_bytes 3 (2 ^ 19 + first_state LL_predef 3 * 2 ^ 13 + first_state OF_predef 2 * 2 ^ 8
              + first_state ML_predef 1 * 2 ^ 2 + 2).
Let one_seq_block : list Z := [24; 97; 98; 99] ++ [1; 0] ++ seq_bits.

(* The content "abcabca" (7 bytes); the fast path's ZSTD_copy16 also wrote 16 cells, the literals and
   litExtraBuffer's zeros after them, and ZSTD_overlapCopy8 rewrote cells 3-10: the 16 written cells are
   the result. *)
Example x_block_one_seq :
  ms (os nil one_seq_block 100) = Some ([97; 98; 99; 97; 98; 99; 97; 98; 99; 97; 98; 0; 0; 0; 0; 0], 7).
Proof. vm_compute. reflexivity. Qed.

(* the state after it: the predefined tables, the repeat offsets (3, 1, 4), the literals in
   litExtraBuffer *)
Let sst (r: option (xst unit * list Z * Z)) :=
  match r with
  | Some (st, _, _) => Some (x_huf _ st, x_seq _ st, x_rep _ st, firstn 4 (x_lxb _ st), Zlength (x_lxb _ st))
  | None => None
  end.
Example x_block_one_seq_state :
  sst (os nil one_seq_block 100) =
  Some (None, Some (LL_predef, OF_predef, ML_predef), (3, 1, 4), [97; 98; 99; 0], XLITEXTRA + XWILDCOPY).
Proof. vm_compute. reflexivity. Qed.

(* the 7 bytes of content do not fit in 6 *)
Example x_block_one_seq_small : os nil one_seq_block 6 = None.
Proof. vm_compute. reflexivity. Qed.

(* capacity 0 with a sequence: dstSize_tooSmall (literals checked first: expectedWriteSize 0 < 3) *)
Example x_block_one_seq_cap0 : os nil one_seq_block 0 = None.
Proof. vm_compute. reflexivity. Qed.

(* capacity 40: the sequence does not end 32 bytes before oend, so the slow path ZSTD_execSequenceEnd runs,
   whose copies write exactly the content *)
Example x_block_one_seq_slow :
  ms (os nil one_seq_block 38) = Some ([97; 98; 99; 97; 98; 99; 97], 7).
Proof. vm_compute. reflexivity. Qed.

(* offset 4 (offset bits 3): beyond the 3 bytes reachable without history (corruption_detected) ... *)
Let seq_bits4 : list Z :=
  le_bytes 3 (2 ^ 19 + first_state LL_predef 3 * 2 ^ 13 + first_state OF_predef 2 * 2 ^ 8
              + first_state ML_predef 1 * 2 ^ 2 + 3).
Let far_block : list Z := [24; 97; 98; 99] ++ [1; 0] ++ seq_bits4.
Example x_block_far : os nil far_block 100 = None.
Proof. vm_compute. reflexivity. Qed.

(* ... and into the frame's earlier output "x" when it is there (slow path, exact content) *)
Example x_block_far_hist :
  ms (os [120] far_block 38) = Some ([120; 97; 98; 99; 120; 97; 98; 99], 7).
Proof. vm_compute. reflexivity. Qed.

(* After a ring wrap: the region holds the old segment "PQRSTU" (cells 0-5) as the extDict
   (ds = 0, de = 6), the new segment starts at op = ps = 0.  Offset 4 at oLitEnd = 3 exceeds the prefix
   (3 bytes): the match starts in the extDict at dictEnd - 1 (cell 5, "U"), then continues from
   prefixStart, which the literals "abc" have just overwritten. *)
Example x_block_ext :
  ms (xb st0 [80; 81; 82; 83; 84; 85] 0 0 0 6 far_block 131072 38 true)
  = Some ([97; 98; 99; 85; 97; 98; 99], 7).
Proof. vm_compute. reflexivity. Qed.

(* Offset 8 (OF code 3, offset value 11 = 8 + 3 extra bits 3): the match starts in the extDict at cell 1,
   which the literals already overwrote ("b"), and reads on through cells 2-4 ("c", then the old "S", "T") *)
Let seq_bits8 : list Z :=
  le_bytes 3 (2 ^ 20 + first_state LL_predef 3 * 2 ^ 14 + first_state OF_predef 3 * 2 ^ 9
              + first_state ML_predef 1 * 2 ^ 3 + 3).
Let ext8_block : list Z := [24; 97; 98; 99] ++ [1; 0] ++ seq_bits8.
Example x_block_ext8 :
  ms (xb st0 [80; 81; 82; 83; 84; 85] 0 0 0 6 ext8_block 131072 38 true)
  = Some ([97; 98; 99; 98; 99; 83; 84], 7).
Proof. vm_compute. reflexivity. Qed.

(* the same offset without an extDict reaches before virtualStart *)
Example x_block_ext8_none :
  xb st0 [80; 81; 82; 83; 84; 85] 0 0 0 0 ext8_block 131072 38 true = None.
Proof. vm_compute. reflexivity. Qed.

(* the placement *)
Example x_alloc_loc_in_dst : x_alloc_loc 300000 1000 131072 false = XL_in_dst.
Proof. reflexivity. Qed.
Example x_alloc_loc_stream : x_alloc_loc 300000 1000 131072 true = XL_extra.
Proof. reflexivity. Qed.
Example x_alloc_loc_split : x_alloc_loc 200000 70000 131072 false = XL_split.
Proof. reflexivity. Qed.
End Examples.
