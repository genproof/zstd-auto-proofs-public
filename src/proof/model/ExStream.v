(* The exact outcome of streaming decompression (ZSTD_decompressStream) from a context in the configuration
   of a new one: no dictionary, default parameters (format zstd1, maxWindowSize = 2^27 + 1, checksums
   checked, no maximal block size), buffered output (ZSTD_bm_buffered), every allocation succeeding (the
   specification allows a memory error at any call separately).  Plain Coq.

   zstd's stream state is abstracted by the record `zstate`: the stream stage, the header buffer, the frame
   parameters, the input buffer, the buffer sizes and oversizedDuration, the output ring (its cells,
   outStart, outEnd), noForwardProgress, the hostage byte, and the state of ZSTD_decompressContinue
   (`dstate`: its stage, `expected`, the block type, the frame's content so far, previousDstEnd /
   prefixStart / the extDict's bounds as ring offsets, the entropy state).  `zstep` is one call of
   ZSTD_decompressStream on that image: the error, or the return value, how far in.pos moves, the bytes
   written to the caller's output, noForwardProgress after the call and the hostage byte.  All line
   numbers refer to lib/decompress/zstd_decompress.c unless stated otherwise.

   The output ring (outBuff = zds->inBuff + inBuffSize, outBuffSize bytes) is carried cell by cell
   (zs_mem, index = offset in outBuff, Zlength zs_mem = outBuffSize):
   - a context without buffers (new, or after ZSTD_DCtx_reset with the parameters, F8) has none;
   - when a frame's header asks for new buffers (zdss_loadHeader, 2292-2325) the ring is replaced by a
     fresh one, ZSTD_customCallocP (genproof item 17): outBuffSize zero bytes, all of them defined;
   - otherwise the ring keeps its cells from the earlier frames;
   - Raw and RLE blocks and ZSTD_decompressBlock_internal write into it at outStart (x_block returns
     the ring after the block, the wildcopy over-writes and the literals it placed there included);
   - zdss_flush copies from it (ZSTD_limitCopy from outBuff + outStart); the single-pass shortcut writes
     straight into the caller's buffer and leaves the ring alone.

   Compressed blocks and the one-shot decoding of the single-pass shortcut are parameters of the section:
   x_block is ZSTD_decompressBlock_internal (model/ExBlock.v), x_frame1 is ZSTD_decompressFrame from the
   configuration of a new context (model/ExFrame.v's x_frame). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Xxh64.
Require Import Zstd.proof.model.ExCall.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- constants ---------- *)

(* ZSTD_MAXWINDOWSIZE_DEFAULT (line 40): (1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT) + 1, the default maxWindowSize *)
Definition ZS_MAXWINDOWSIZE_DEFAULT : Z := 2 ^ 27 + 1.
(* WILDCOPY_OVERLENGTH (lib/common/zstd_internal.h 201) *)
Definition ZS_WILDCOPY_OVERLENGTH : Z := 32.
(* ZSTD_WORKSPACETOOLARGE_FACTOR and _MAXDURATION (lib/common/zstd_internal.h 263-266) *)
Definition ZS_WORKSPACETOOLARGE_FACTOR : Z := 3.
Definition ZS_WORKSPACETOOLARGE_MAXDURATION : Z := 128.
(* ZSTD_NO_FORWARD_PROGRESS_MAX (line 51) *)
Definition ZS_NO_FORWARD_PROGRESS_MAX : Z := 16.
(* ZSTD_FRAMEIDSIZE (lib/common/zstd_internal.h 82) *)
Definition ZS_FRAMEIDSIZE : Z := 4.

(* ZSTD_dStreamStage (zstd_decompress_internal.h 94) *)
Definition ZDSS_init : Z := 0.
Definition ZDSS_loadHeader : Z := 1.
Definition ZDSS_read : Z := 2.
Definition ZDSS_load : Z := 3.
Definition ZDSS_flush : Z := 4.

(* ZSTD_dStage (zstd_decompress_internal.h 89-92) *)
Definition DS_getFrameHeaderSize : Z := 0.
Definition DS_decodeFrameHeader : Z := 1.
Definition DS_decodeBlockHeader : Z := 2.
Definition DS_decompressBlock : Z := 3.
Definition DS_decompressLastBlock : Z := 4.
Definition DS_checkChecksum : Z := 5.
Definition DS_decodeSkippableHeader : Z := 6.
Definition DS_skipFrame : Z := 7.

(* blockType_e (lib/common/zstd_internal.h 86): bt_raw 0, bt_rle 1, bt_compressed 2, bt_reserved 3 *)
Definition BT_reserved : Z := 3.

(* the ring's cells after writing b at offset pos (ZSTD_memmove / ZSTD_memset into outBuff).  Every write
   of the decoder lies inside the ring, pos + Zlength b <= outBuffSize = Zlength mem, so this is the plain
   replacement of those cells. *)
Definition mem_write (mem: list Z) (pos: Z) (b: list Z) : list Z :=
  firstn (Z.to_nat pos) mem ++ b ++ skipn (Z.to_nat (pos + Zlength b)) mem.

(* a ring just allocated by ZSTD_customCallocP (lib/common/allocations.h 69-83; quickproof's calloc
   stores 0 in every byte): n defined zero bytes *)
Definition ring_fresh (n: Z) : list Z := repeat 0 (Z.to_nat n).

Section ExStream.

(* the block decoder's part of the context: entropy tables, repeat offsets, litEntropy / fseEntropy,
   litExtraBuffer (whose bytes survive ZSTD_decompressBegin and are read as slack) *)
Variable xst : Type.
(* that state in a new context, or after ZSTD_DCtx_reset with the parameters (litExtraBuffer zeroed:
   ZSTD_customCallocP of the context, item 17; the memset of F8) *)
Variable xst_init : xst.
(* ZSTD_decompressBegin without a dictionary (1584-1609): tables dropped, repeat offsets 1 4 8,
   litExtraBuffer kept *)
Variable xst_begin : xst -> xst.
(* ZSTD_decompressBlock_internal on a compressed block: x_block st mem ps op ds de body bsm cap streaming,
   with the entropy state, the written cells of the destination region (here the output ring, index =
   offset in outBuff), the prefix [ps, op), the extDict [ds, de) (empty if ds = de), the block body,
   Block_Maximum_Size, the capacity from op and the streaming flag; the new entropy state, the region's
   cells after the block and the decoded size (the block's content is the new mem's [op, op + size)),
   None = an error *)
Variable x_block : xst -> list Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Z -> bool -> option (xst * list Z * Z).
(* one-shot decoding of the frame at the start of the bytes with a capacity, on the same context
   (ZSTD_decompressBegin then ZSTD_decompressFrame, as ZSTD_decompressMultiFrame does; it applies xst_begin
   itself): from the block decoder's state, the content, the bytes the frame takes and the state after,
   None = an error (model/ExFrame.v's x_frame) *)
Variable x_frame1 : xst -> list Z -> Z -> option (list Z * Z * xst).

(* ---------- ZSTD_decompressContinue's state ---------- *)

(* The fields of the context that ZSTD_decompressContinue reads and writes.  The four pointers are offsets
   in outBuff, None = NULL.  zstd stores virtualStart, not the extDict's start; with
   virtualStart = dst - (previousDstEnd - prefixStart) as ZSTD_checkContinuity sets it, the extDict
   [dictEnd - (prefixStart - virtualStart), dictEnd) is [the old prefixStart, the old previousDstEnd),
   which d_ds, d_de record. *)
Record dstate := mkD {
  d_stage : Z;           (* dctx->stage (ZSTD_dStage) *)
  d_expected : Z;        (* dctx->expected *)
  d_btype : Z;           (* dctx->bType *)
  d_rle : Z;             (* dctx->rleSize *)
  d_out : list Z;        (* the frame's content so far: decodedSize = Zlength, xxhState = XXH64 of it *)
  d_check : bool;        (* dctx->validateChecksum *)
  d_ent : xst;           (* the block decoder's state (entropy, repeat offsets, litExtraBuffer) *)
  d_prev : option Z;     (* previousDstEnd *)
  d_pfx : option Z;      (* prefixStart *)
  d_ds : option Z;       (* the extDict's start (dictEnd - (prefixStart - virtualStart)) *)
  d_de : option Z        (* dictEnd *)
}.

Definition d_goto (d: dstate) (stage expected: Z) : dstate :=
  mkD stage expected (d_btype d) (d_rle d) (d_out d) (d_check d) (d_ent d)
      (d_prev d) (d_pfx d) (d_ds d) (d_de d).

Definition d_set_check (d: dstate) (b: bool) : dstate :=
  mkD (d_stage d) (d_expected d) (d_btype d) (d_rle d) (d_out d) b (d_ent d)
      (d_prev d) (d_pfx d) (d_ds d) (d_de d).

(* ZSTD_decompressBegin (1584-1609), without a dictionary: expected = ZSTD_startingInputLength = 5, stage
   getFrameHeaderSize, decodedSize 0, previousDstEnd = prefixStart = virtualStart = dictEnd = NULL, the
   block decoder's state through xst_begin (litExtraBuffer kept), bType = bt_reserved.  validateChecksum
   and rleSize are kept (and set again before they are read). *)
Definition d_begin (d: dstate) : dstate :=
  mkD DS_getFrameHeaderSize ZSTD_FRAMEHEADERSIZE_PREFIX BT_reserved (d_rle d) nil (d_check d)
      (xst_begin (d_ent d)) None None None None.

(* the state the single-pass shortcut leaves: the block decoder's state after the frame, expected 0.  The
   other fields (previousDstEnd then points into the caller's buffer) are not read again before
   ZSTD_decompressBegin sets them. *)
Definition d_after_shortcut (d: dstate) (e: xst) : dstate :=
  mkD (d_stage d) 0 (d_btype d) (d_rle d) (d_out d) (d_check d) e (d_prev d) (d_pfx d) (d_ds d) (d_de d).

(* ZSTD_checkContinuity (zstd_decompress_block.c 2307-2316): writing at dst with dstSize > 0 bytes of room
   when dst is not previousDstEnd starts a new segment: dictEnd := previousDstEnd, virtualStart :=
   dst - (previousDstEnd - prefixStart) (dst when previousDstEnd is NULL: no extDict), prefixStart :=
   previousDstEnd := dst.  gpDictCopy is 0 without a dictionary. *)
Definition d_continuity (d: dstate) (dst dstSize: Z) : dstate :=
  let contiguous := match d_prev d with Some p => p =? dst | None => false end in
  if (dstSize >? 0) && negb contiguous then
    mkD (d_stage d) (d_expected d) (d_btype d) (d_rle d) (d_out d) (d_check d) (d_ent d)
        (Some dst) (Some dst)
        (match d_prev d with Some _ => d_pfx d | None => None end) (d_prev d)
  else d.

(* the history ZSTD_decompressBlock_internal sees when writing at op: the prefix [prefixStart, op) and the
   extDict.  prefixStart is NULL only while the capacity at op is 0 (ZSTD_checkContinuity was skipped),
   where no history is used (zstd_decompress_block.c 2224-2226, 2253); it is then given as op. *)
Definition d_hist (d: dstate) (op: Z) : Z * Z * Z :=
  let ps := match d_pfx d with Some p => p | None => op end in
  match d_ds d, d_de d with
  | Some a, Some b => (ps, a, b)
  | _, _ => (ps, op, op)
  end.

(* ZSTD_nextSrcSizeToDecompressWithInputSize (1254-1260): a raw block may be taken in pieces,
   BOUNDED(1, inputSize, expected); otherwise exactly `expected` *)
Definition d_next_in (d: dstate) (avail: Z) : Z :=
  if ((d_stage d =? DS_decompressBlock) || (d_stage d =? DS_decompressLastBlock)) && (d_btype d =? 0)
  then Z.max 1 (Z.min avail (d_expected d)) else d_expected d.

(* The end of a frame's last block (1343-1355 for an empty block, F6; 1398-1412 otherwise): the declared
   content size is compared with dctx->decodedSize, a U64 (the frame's content length modulo 2^64: a streamed
   frame's content is not bounded by any buffer), then the checksum is expected or the frame ends (expected 0). *)
Definition d_end_frame (fp: frame_header) (d: dstate) : option dstate :=
  if negb (fh_contentSize fp =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength (d_out d) mod 2 ^ 64 =? fh_contentSize fp)
  then None
  else if fh_checksumFlag fp =? 1 then Some (d_goto d DS_checkChecksum 4)
  else Some (d_goto d DS_getFrameHeaderSize 0).

(* ZSTD_decompressContinue (1293-1454) on the n bytes src (for a skippable frame's content, which it does
   not read, src is nil and only n matters), writing into the ring mem at offset dst with dstCapacity cap:
   the new state, the ring's cells after the call, and the return value (the number of bytes written at
   dst).  fp = dctx->fParams.  The stages getFrameHeaderSize, decodeFrameHeader and decodeSkippableHeader
   are never reached from ZSTD_decompressStream (zdss_loadHeader consumes the frame header itself and sets
   the stage to decodeBlockHeader or skipFrame; a finished frame has expected = 0, which zdss_read never
   decodes): they are given as errors. *)
Definition d_continue (fp: frame_header) (d0: dstate) (mem: list Z) (dst cap: Z) (src: list Z) (n: Z)
    : option (dstate * list Z * Z) :=
  (* the sanity check (1297) *)
  if negb (n =? d_next_in d0 n) then None else
  let d := d_continuity d0 dst cap in
  let bsm := fh_blockSizeMax fp in
  if d_stage d =? DS_decodeBlockHeader then
    (* 1329-1359: ZSTD_getcBlockSize, the block size against Block_Maximum_Size, empty blocks *)
    match cblock_size src with
    | None => None
    | Some c =>
        if c >? bsm then None else
        let bp := block_props_of src in
        let d1 := mkD (d_stage d) c (bp_type bp) (bp_origSize bp) (d_out d) (d_check d) (d_ent d)
                      (d_prev d) (d_pfx d) (d_ds d) (d_de d) in
        if c >? 0 then
          Some (d_goto d1 (if bp_last bp =? 1 then DS_decompressLastBlock else DS_decompressBlock) c, mem, 0)
        else if bp_last bp =? 1 then
          match d_end_frame fp d1 with Some d2 => Some (d2, mem, 0) | None => None end
        else Some (d_goto d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem, 0)
    end
  else if (d_stage d =? DS_decompressBlock) || (d_stage d =? DS_decompressLastBlock) then
    (* 1361-1420: the block (or a piece of a raw block); ZSTD_copyRawBlock (902-913) and ZSTD_setRleBlock
       (915-925) check only the capacity, then every block's size is checked against Block_Maximum_Size
       (1389) *)
    let res :=
      if d_btype d =? 2 then
        let '(ps, ds, de) := d_hist d dst in
        match x_block (d_ent d) mem ps dst ds de src bsm cap true with
        | Some (e, mem', sz) => Some (e, mem', sz, 0)
        | None => None
        end
      else if d_btype d =? 0 then
        (if n >? cap then None else Some (d_ent d, mem_write mem dst src, n, d_expected d - n))
      else if d_btype d =? 1 then
        (if d_rle d >? cap then None
         else Some (d_ent d, mem_write mem dst (repeat (byte_at src 0) (Z.to_nat (d_rle d))), d_rle d, 0))
      else None in
    match res with
    | None => None
    | Some (e, mem', sz, ex) =>
        if sz >? bsm then None else
        let d1 := mkD (d_stage d) ex (d_btype d) (d_rle d) (d_out d ++ slice mem' dst sz) (d_check d) e
                      (Some (dst + sz)) (d_pfx d) (d_ds d) (d_de d) in
        if ex >? 0 then Some (d1, mem', sz)
        else if d_stage d =? DS_decompressLastBlock then
          match d_end_frame fp d1 with Some d2 => Some (d2, mem', sz) | None => None end
        else Some (d_goto d1 DS_decodeBlockHeader ZSTD_blockHeaderSize, mem', sz)
    end
  else if d_stage d =? DS_checkChecksum then
    (* 1422-1435: the low 32 bits of XXH64 of the content, seed 0 *)
    if d_check d && negb (le_field src 0 4 =? xxh64 (d_out d) 0 mod 2 ^ 32) then None
    else Some (d_goto d DS_getFrameHeaderSize 0, mem, 0)
  else if d_stage d =? DS_skipFrame then
    (* 1446-1449 *)
    Some (d_goto d DS_getFrameHeaderSize 0, mem, 0)
  else None.

(* ---------- the stream state ---------- *)

Record zstate := mkZ {
  zs_stage : Z;          (* zds->streamStage (ZSTD_dStreamStage) *)
  zs_hbuf : list Z;      (* headerBuffer[0 .. lhSize) *)
  zs_fp : frame_header;  (* zds->fParams (windowSize raised to 1 KiB once the header is consumed) *)
  zs_ibuf : list Z;      (* inBuff[0 .. inPos) (not filled for a skippable frame, which is not copied) *)
  zs_inpos : Z;          (* inPos *)
  zs_inbs : Z;           (* inBuffSize *)
  zs_outbs : Z;          (* outBuffSize *)
  zs_over : Z;           (* oversizedDuration *)
  zs_mem : list Z;       (* the cells of outBuff[0 .. outBuffSize) *)
  zs_ostart : Z;         (* outStart *)
  zs_oend : Z;           (* outEnd *)
  zs_nfp : Z;            (* noForwardProgress *)
  zs_host : Z;           (* hostageByte *)
  zs_dc : dstate         (* ZSTD_decompressContinue's state *)
}.

Definition z_stage (z: zstate) (s: Z) : zstate :=
  mkZ s (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_hbuf (z: zstate) (hb: list Z) : zstate :=
  mkZ (zs_stage z) hb (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_fp (z: zstate) (fp: frame_header) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) fp (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_in (z: zstate) (ib: list Z) (ipos: Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) ib ipos (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_bufs (z: zstate) (inbs outbs over: Z) (mem: list Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) inbs outbs over
      mem (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_mem (z: zstate) (mem: list Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      mem (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_ring (z: zstate) (ostart oend: Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) ostart oend (zs_nfp z) (zs_host z) (zs_dc z).
Definition z_nfp (z: zstate) (n: Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) n (zs_host z) (zs_dc z).
Definition z_host (z: zstate) (h: Z) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) h (zs_dc z).
Definition z_dc (z: zstate) (d: dstate) : zstate :=
  mkZ (zs_stage z) (zs_hbuf z) (zs_fp z) (zs_ibuf z) (zs_inpos z) (zs_inbs z) (zs_outbs z) (zs_over z)
      (zs_mem z) (zs_ostart z) (zs_oend z) (zs_nfp z) (zs_host z) d.

(* the zeroed ZSTD_FrameHeader of a new (calloc'd) context *)
Definition fh_zero : frame_header :=
  {| fh_contentSize := 0; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 0;
     fh_headerSize := 0; fh_dictID := 0; fh_checksumFlag := 0 |}.

(* The state after ZSTD_createDCtx (ZSTD_initDCtx_internal) or ZSTD_DCtx_reset(session_and_parameters)
   (1985-2007, F8): stage zdss_init, no buffers (inBuffSize = outBuffSize = 0, no ring cells),
   oversizedDuration 0, noForwardProgress 0, the block decoder's state xst_init (litExtraBuffer zeroed).  The other fields are never read before zdss_init /
   ZSTD_decompressBegin set them (a used context after the reset has other values there, with the same
   results). *)
Definition zstate_init : zstate :=
  mkZ ZDSS_init nil fh_zero nil 0 0 0 0 nil 0 0 0 0
      (mkD DS_getFrameHeaderSize 0 0 0 nil false xst_init None None None None).

(* ---------- one iteration of ZSTD_decompressStream's loop ---------- *)

(* The outcome of one iteration of the `while (someMoreWork)` loop (2153-2402), for the call's input inp
   (input->src + [input->pos, input->size)) and room (output->size - output->pos); ip = ip - istart, dl = the
   bytes written at ostart .. op so far.  LNext: the loop goes on; LStop: someMoreWork = 0; LEarly: the
   early return of a partial frame header (2229-2234) with its hint. *)
Inductive lstep :=
  | LErr
  | LNext (z: zstate) (ip: Z) (dl: list Z)
  | LStop (z: zstate) (ip: Z) (dl: list Z)
  | LEarly (z: zstate) (r: Z).

(* ZSTD_decompressContinueStream (2110-2137), buffered output: decode into the ring at outStart with the
   room left in the ring (none for a skippable frame); a frame part producing no bytes goes back to
   zdss_read, otherwise the bytes [outStart, outStart + r) are to be flushed. *)
Definition z_dcs (z: zstate) (src: list Z) (n: Z) : option zstate :=
  let skip := d_stage (zs_dc z) =? DS_skipFrame in
  let cap := if skip then 0 else zs_outbs z - zs_ostart z in
  match d_continue (zs_fp z) (zs_dc z) (zs_mem z) (zs_ostart z) cap src n with
  | None => None
  | Some (d', mem', r) =>
      let z1 := z_mem (z_dc z d') mem' in
      if (r =? 0) && negb skip then Some (z_stage z1 ZDSS_read)
      else Some (z_stage (z_ring z1 (zs_ostart z) (zs_ostart z + r)) ZDSS_flush)
  end.

(* zdss_load (2349-2376): copy what is missing of the next part into inBuff (a skippable frame's content
   is only counted), decode it once complete *)
Definition st_load (inp: list Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  let avail := Zlength inp - ip in
  let needed := d_expected (zs_dc z) in
  let toLoad := needed - zs_inpos z in
  let skip := d_stage (zs_dc z) =? DS_skipFrame in
  if negb skip && (toLoad >? zs_inbs z - zs_inpos z) then LErr else
  let loaded := Z.min toLoad avail in
  let ib := if skip then zs_ibuf z else zs_ibuf z ++ slice inp ip loaded in
  let z1 := z_in z ib (zs_inpos z + loaded) in
  let ip1 := ip + loaded in
  if loaded <? toLoad then LStop z1 ip1 dl else
  match z_dcs (z_in z1 nil 0) (if skip then nil else ib) needed with
  | None => LErr
  | Some z2 => LNext z2 ip1 dl
  end.

(* zdss_read (2329-2347): the end of the frame (expected 0) ends the call in zdss_init; with enough input
   the part is decoded from the caller's input directly; otherwise zdss_load, unless no input is left *)
Definition st_read (inp: list Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  let avail := Zlength inp - ip in
  let needed := d_next_in (zs_dc z) avail in
  if needed =? 0 then LStop (z_stage z ZDSS_init) ip dl
  else if avail >=? needed then
    match z_dcs z (slice inp ip needed) needed with
    | None => LErr
    | Some z1 => LNext z1 (ip + needed) dl
    end
  else if avail =? 0 then LStop z ip dl
  else st_load inp (z_stage z ZDSS_load) ip dl.

(* zdss_flush (2377-2397): ZSTD_limitCopy of the ring's cells [outStart, outEnd) to the caller's output;
   once all are out, zdss_read, and the ring restarts at 0 when the frame is larger than the ring and a
   block of Block_Maximum_Size would not fit after outStart *)
Definition st_flush (room: Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  let toFlush := zs_oend z - zs_ostart z in
  let fl := Z.min (room - Zlength dl) toFlush in
  let dl1 := dl ++ slice (zs_mem z) (zs_ostart z) fl in
  let z1 := z_ring z (zs_ostart z + fl) (zs_oend z) in
  if fl =? toFlush then
    let z2 := z_stage z1 ZDSS_read in
    if (zs_outbs z2 <? fh_contentSize (zs_fp z2))
       && (zs_ostart z2 + fh_blockSizeMax (zs_fp z2) >? zs_outbs z2)
    then LNext (z_ring z2 0 0) ip dl1
    else LNext z2 ip dl1
  else LStop z1 ip dl1.

(* zdss_loadHeader once the header is complete (fParams = h), 2240-2327, then zdss_read (fall-through):
   - the single-pass shortcut (2240-2258, fixes F3 and F7): a frame of declared size that fits the room, whose
     whole header came in this call and whose bytes are all in this call's input, is decoded by
     ZSTD_decompress_usingDDict on the same context straight into the caller's output with capacity the
     declared size (the ring is not touched); the call then ends in zdss_init with expected = 0 and the
     block decoder's state the frame left (d_after_shortcut);
   - otherwise ZSTD_decompressBegin, the skippable frame or ZSTD_decodeFrameHeader (dictID must be 0
     without a dictionary; validateChecksum := checksumFlag), the window against maxWindowSize, then
     the buffer sizes: ZSTD_decodingBufferSize_internal (2015-2032; its size_t check never fails with a
     64-bit size_t), ZSTD_DCtx_updateOversizedDuration (2061-2072), new buffers (a fresh zeroed ring)
     when one is too small or the buffers were oversized for ZSTD_WORKSPACETOOLARGE_MAXDURATION frames
     (allocation succeeds). *)
Definition st_header_done (inp: list Z) (room: Z) (z: zstate) (h: frame_header) (ip: Z) (dl: list Z)
    : lstep :=
  let fcs := fh_contentSize h in
  let shortcut :=
    if negb (fcs =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (fh_frameType h =? 1)
       && (room - Zlength dl >=? fcs) && (Zlength (zs_hbuf z) =? ip)
    then match frame_compressed_size inp with
         | Some cs => if cs <=? Zlength inp then Some cs else None
         | None => None
         end
    else None in
  match shortcut with
  | Some cs =>
      (* ZSTD_decompressMultiFrame on exactly the frame's bytes: one frame, then nothing may be left *)
      match x_frame1 (d_ent (zs_dc z)) (firstn (Z.to_nat cs) inp) fcs with
      | Some (c, k, e) =>
          if k =? cs
          then LStop (z_stage (z_dc z (d_after_shortcut (zs_dc z) e)) ZDSS_init) cs (dl ++ c)
          else LErr
      | None => LErr
      end
  | None =>
      let hb := zs_hbuf z in
      let d0 := d_begin (zs_dc z) in
      let dres :=
        if is_skippable_magic (le_field hb 0 4) then Some (d_goto d0 DS_skipFrame (le_field hb 4 4))
        else if negb (fh_dictID h =? 0) then None
        else Some (d_goto (d_set_check d0 (fh_checksumFlag h =? 1)) DS_decodeBlockHeader ZSTD_blockHeaderSize) in
      match dres with
      | None => LErr
      | Some d1 =>
          let ws := Z.max (fh_windowSize h) (2 ^ ZSTD_WINDOWLOG_ABSOLUTEMIN) in
          if ws >? ZS_MAXWINDOWSIZE_DEFAULT then LErr else
          let fp := {| fh_contentSize := fcs; fh_windowSize := ws; fh_blockSizeMax := fh_blockSizeMax h;
                       fh_frameType := fh_frameType h; fh_headerSize := fh_headerSize h;
                       fh_dictID := fh_dictID h; fh_checksumFlag := fh_checksumFlag h |} in
          let bsm := fh_blockSizeMax h in
          let needIn := Z.max bsm 4 in
          let needOut := Z.min fcs (ws + 2 * Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm + 2 * ZS_WILDCOPY_OVERLENGTH) in
          let over := if zs_inbs z + zs_outbs z >=? (needIn + needOut) * ZS_WORKSPACETOOLARGE_FACTOR
                      then zs_over z + 1 else 0 in
          let realloc := (zs_inbs z <? needIn) || (zs_outbs z <? needOut)
                         || (over >=? ZS_WORKSPACETOOLARGE_MAXDURATION) in
          let z1 := z_dc (z_fp z fp) d1 in
          let z2 := if realloc then z_bufs z1 needIn needOut over (ring_fresh needOut)
                    else z_bufs z1 (zs_inbs z) (zs_outbs z) over (zs_mem z) in
          st_read inp (z_stage z2 ZDSS_read) ip dl
      end
  end.

(* zdss_loadHeader (2180-2238): ZSTD_getFrameHeader_advanced on the bytes of the header so far; when more
   are needed, load them if the input has them all (and go round again), else take all of the input and
   return the hint (2219-2234, fix F2): with hSize the size asked before the load and lhSize after it,
   ZSTD_SKIPPABLEHEADERSIZE - lhSize while the frame type is unknown, hSize - lhSize for a skippable frame,
   else max(ZSTD_FRAMEHEADERSIZE_MIN, hSize) - lhSize + ZSTD_blockHeaderSize. *)
Definition st_load_header (inp: list Z) (room: Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  let hb := zs_hbuf z in
  match get_frame_header hb with
  | FH_err => LErr
  | FH_ok h => st_header_done inp room (z_fp z h) h ip dl
  | FH_more hSize =>
      let toLoad := hSize - Zlength hb in
      let avail := Zlength inp - ip in
      if toLoad >? avail then
        let hb1 := hb ++ slice inp ip avail in
        let lh := Zlength hb1 in
        match get_frame_header hb1 with
        | FH_err => LErr
        | _ =>
            LEarly (z_hbuf z hb1)
              (if (lh <? ZS_FRAMEIDSIZE) || is_skippable_magic (le_field hb1 0 4)
               then (if lh <? ZS_FRAMEIDSIZE then ZSTD_SKIPPABLEHEADERSIZE else hSize) - lh
               else Z.max ZSTD_FRAMEHEADERSIZE_MIN hSize - lh + ZSTD_blockHeaderSize)
        end
      else LNext (z_hbuf z (hb ++ slice inp ip toLoad)) (ip + toLoad) dl
  end.

(* zdss_init (2169-2178): the transparent reset of a new frame, then zdss_loadHeader *)
Definition z_new_frame (z: zstate) : zstate :=
  z_host (z_ring (z_in (z_hbuf (z_stage z ZDSS_loadHeader) nil) nil 0) 0 0) 0.

Definition one_iter (inp: list Z) (room: Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  let s := zs_stage z in
  if s =? ZDSS_init then st_load_header inp room (z_new_frame z) ip dl
  else if s =? ZDSS_loadHeader then st_load_header inp room z ip dl
  else if s =? ZDSS_read then st_read inp z ip dl
  else if s =? ZDSS_load then st_load inp z ip dl
  else if s =? ZDSS_flush then st_flush room z ip dl
  else LErr.

(* The loop.  Every iteration that goes on either takes at least one input byte (a header load, a part
   decoded from the input, a load that completes: their sizes are at least 1 because hSize > lhSize and
   inPos < expected, expected >= 1, outside zdss_init) or is a completed flush, after which zdss_read
   takes a byte or stops; so a call of n input bytes has at most 2 n + 2 iterations, and the fuel
   2 n + 4 of zstep is never exhausted from a state reached from zstate_init. *)
Fixpoint z_loop (fuel: nat) (inp: list Z) (room: Z) (z: zstate) (ip: Z) (dl: list Z) : lstep :=
  match fuel with
  | O => LErr
  | S f =>
      match one_iter inp room z ip dl with
      | LNext z1 ip1 dl1 => z_loop f inp room z1 ip1 dl1
      | r => r
      end
  end.

(* ---------- one call ---------- *)

(* ZSTD_decompressStream (2139-2450) in buffered mode, call c = (the input bytes from input->pos, the room
   output->size - output->pos): None = an error; Some (z', (r, k, dl, stall, a)) = the new state, the return
   value, in.pos moves by k, dl is written at output->pos (out.pos moves by Zlength dl), noForwardProgress
   after the call, a = 1 iff a hostage byte is held after the call.
   - output->pos > output->size is an error (2152); input->pos > input->size cannot be expressed by c;
   - the partial-header early return takes all of the input, writes nothing and leaves noForwardProgress;
   - otherwise (2405-2448) noForwardProgress counts the calls in a row that neither read nor wrote; on
     the 16th such call the error is destFull with no room, inputEmpty with no input, and otherwise (only
     possible on a call that releases a hostage byte) the assert(0) is void (NDEBUG) and the call goes on;
   - the hint: at the end of a frame (expected 0), 0 if the output is flushed, the hostage byte (kept
     back at in.pos - 1) released if the input has it, else 1 with the stage set to zdss_read; when the
     output is not flushed the last byte read becomes the hostage (in.pos - 1) and the return is 1;
     inside a frame expected + ZSTD_blockHeaderSize (in a non-last block) - inPos. *)
Definition zstep (z: zstate) (c: zcall) : option (zstate * (Z * Z * list Z * Z * Z)) :=
  let (inp, room) := c in
  if room <? 0 then None else
  match z_loop (2 * length inp + 4) inp room z 0 nil with
  | LErr => None
  | LNext _ _ _ => None
  | LEarly z1 r => Some (z1, (r, Zlength inp, nil, zs_nfp z1, 0))
  | LStop z1 ip dl =>
      let noprog := (ip =? 0) && (Zlength dl =? 0) in
      let nfp := if noprog then zs_nfp z1 + 1 else 0 in
      if noprog && (nfp >=? ZS_NO_FORWARD_PROGRESS_MAX) && ((room =? 0) || (Zlength inp =? 0)) then None else
      let z2 := z_nfp z1 nfp in
      if d_expected (zs_dc z2) =? 0 then
        if zs_oend z2 =? zs_ostart z2 then
          if zs_host z2 =? 1 then
            if ip >=? Zlength inp then Some (z_stage z2 ZDSS_read, (1, ip, dl, nfp, 1))
            else Some (z2, (0, ip + 1, dl, nfp, 0))
          else Some (z2, (0, ip, dl, nfp, 0))
        else if zs_host z2 =? 0 then Some (z_host z2 1, (1, ip - 1, dl, nfp, 1))
        else Some (z2, (1, ip, dl, nfp, 1))
      else
        let d := zs_dc z2 in
        Some (z2, (d_expected d + (if d_stage d =? DS_decompressBlock then ZSTD_blockHeaderSize else 0)
                     - zs_inpos z2, ip, dl, nfp, zs_host z2))
  end.

(* the calls h since the last session reset, from zstate_init; None if one of them fails *)
Fixpoint zs_run_from (z: zstate) (h: list zcall) : option zstate :=
  match h with
  | nil => Some z
  | c :: h' =>
      match zstep z c with
      | Some (z', _) => zs_run_from z' h'
      | None => None
      end
  end.

Definition zs_run (h: list zcall) : option zstate := zs_run_from zstate_init h.

(* the outcome of the call c after the calls h *)
Definition zs_call (h: list zcall) (c: zcall) : option (Z * Z * list Z * Z * Z) :=
  match zs_run h with
  | Some z => option_map snd (zstep z c)
  | None => None
  end.

End ExStream.

(* ---------- sanity checks ---------- *)

Require Zstd.proof.model.ExFrame.

(* a block decoder that refuses every compressed block, for the one-shot and the streaming side *)
Local Definition no_cblock (_: unit) (_: list Z) (_ _ _ _: Z) (_: list Z) (_ _: Z) (_: bool)
  : option (unit * list Z * Z) := None.
Local Definition xf1 := ExFrame.x_frame unit (fun u => u) no_cblock.
Local Definition zsc := zs_call unit tt (fun u => u) no_cblock xf1.

(* raw block "abc" in a single-segment frame of declared size 3 (12 bytes) *)
Local Definition abc_frame : list Z := [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99].

(* one call with room 3: the header comes in two loads (5 bytes, then the 6th), then the single-pass
   shortcut decodes the whole frame; return 0 *)
Example zs_abc_shortcut : zsc nil (abc_frame, 3) = Some (0, 12, [97; 98; 99], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* one call with room 2: no shortcut; buffers of 4 + 3 bytes; the block header and the raw block are
   decoded from the input into the ring, 2 bytes flushed; the last byte is held as hostage (in.pos 11)
   and 1 returned *)
Example zs_abc_hostage : zsc nil (abc_frame, 2) = Some (1, 11, [97; 98], 0, 1).
Proof. vm_compute. reflexivity. Qed.

(* the next call, given the hostage byte again and room 1: the last byte flushed from the ring, the
   hostage released (in.pos moves by 1 without reading it); return 0 *)
Example zs_abc_release : zsc [(abc_frame, 2)] ([99], 1) = Some (0, 1, [99], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* the frame cut after 7 bytes: the header, then 1 byte of the block header loaded into inBuff; the hint
   is the rest of the block header, 2 *)
Example zs_abc_cut1 : zsc nil (firstn 7 abc_frame, 10) = Some (2, 7, [], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* the rest: the block header completed from inBuff, the raw block decoded from the input and flushed *)
Example zs_abc_cut2 : zsc [(firstn 7 abc_frame, 10)] (skipn 7 abc_frame, 10) = Some (0, 5, [97; 98; 99], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* an empty first call: nothing read, the hint ZSTD_SKIPPABLEHEADERSIZE (the frame type is unknown) *)
Example zs_empty : zsc nil (nil, 10) = Some (8, 0, [], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* a skippable frame of 1 byte with no output room: buffers of 4 + 1 bytes are allocated (the frame's
   size counts as its content size), the content is skipped; return 0 *)
Example zs_skippable : zsc nil ([80; 42; 77; 24; 1; 0; 0; 0; 7], 0) = Some (0, 9, [], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* the no-progress guard: with the hostage byte held and the output flushed, empty calls return 1 and
   count; the 16th such call in a row is an error (inputEmpty) *)
Example zs_stall15 : zsc ((abc_frame, 2) :: (nil, 1) :: repeat (nil, 1) 14) (nil, 1) = Some (1, 0, [], 15, 1).
Proof. vm_compute. reflexivity. Qed.
Example zs_stall16 : zsc ((abc_frame, 2) :: (nil, 1) :: repeat (nil, 1) 15) (nil, 1) = None.
Proof. vm_compute. reflexivity. Qed.
(* a 16th call that releases the hostage byte reads and writes nothing either, but has input and room:
   the guard's assert(0) is void and the call returns 0 *)
Example zs_stall16_release : zsc ((abc_frame, 2) :: (nil, 1) :: repeat (nil, 1) 15) ([5], 1) = Some (0, 1, [], 16, 0).
Proof. vm_compute. reflexivity. Qed.

(* The ring's layout as a compressed block sees it.  A test block decoder that writes its arguments
   (ps, op, ds, de) as 4 cells at op.  Frame: window 1 KiB (Block_Maximum_Size 1024), no declared size,
   so the ring has 1024 + 2 * 1024 + 64 = 3136 cells; three raw blocks of 1024 bytes, then a compressed
   last block of 1 byte. *)
Local Definition probe_block (_: unit) (mem: list Z) (ps op ds de: Z) (_: list Z) (_ _: Z) (_: bool)
  : option (unit * list Z * Z) := Some (tt, mem_write mem op [ps; op; ds; de], 4).
Local Definition zsp := zs_call unit tt (fun u => u) probe_block xf1.
Local Definition raw1k : list Z := [0; 32; 0] ++ repeat 7 1024.
Local Definition probe_hdr : list Z := [40; 181; 47; 253; 0; 0].

(* a compressed block in the first segment: prefix [0, 0), no extDict *)
Example zs_probe_first :
  zsp nil (probe_hdr ++ [13; 0; 0; 0], 100) = Some (0, 10, [0; 0; 0; 0], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* after the third raw block outStart = 3072 and 3072 + 1024 > 3136: the ring restarts at 0, and the
   compressed block sees the prefix [0, 0) and the extDict [0, 3072), the whole earlier segment *)
Example zs_probe_wrap :
  option_map (fun '(r, k, dl, s, a) => (r, k, skipn 3072 dl, s, a))
    (zsp nil (probe_hdr ++ raw1k ++ raw1k ++ raw1k ++ [13; 0; 0; 0], 5000))
  = Some (0, 3091, [0; 0; 0; 3072], 0, 0).
Proof. vm_compute. reflexivity. Qed.

(* The block decoder's state is threaded through frames and through the shortcut: a test decoder whose
   state counts the compressed blocks decoded so far and writes the count.  Frame 1 (declared size 4, one
   compressed block) takes the shortcut; frame 2 (the same) is streamed with room 2, so its block is
   decoded into the ring with the count the shortcut left. *)
Local Definition count_block (st: Z) (mem: list Z) (_ op _ _: Z) (_: list Z) (_ _: Z) (_: bool)
  : option (Z * list Z * Z) := Some (st + 1, mem_write mem op [st; st; st; st], 4).
Local Definition zsn := zs_call Z 0 (fun n => n) count_block (ExFrame.x_frame Z (fun n => n) count_block).
Local Definition cframe : list Z := [40; 181; 47; 253; 32; 4; 13; 0; 0; 0].
Example zs_count_shortcut : zsn nil (cframe, 4) = Some (0, 10, [0; 0; 0; 0], 0, 0).
Proof. vm_compute. reflexivity. Qed.
Example zs_count_next : zsn [(cframe, 4)] (cframe, 2) = Some (1, 9, [1; 1], 0, 1).
Proof. vm_compute. reflexivity. Qed.
