(* The exact outcome of one-shot decoding (ZSTD_decompressDCtx) from a context in the configuration of a new
   one: no dictionary, default parameters (format zstd1, checksums checked, no maximal block size).  Plain Coq.

   Unlike model/Series.v, which claims nothing on some inputs, these functions return exactly what the C code
   does on every input: None exactly when it returns an error.  They follow lib/decompress/zstd_decompress.c:
   ZSTD_decompressMultiFrame (the series), ZSTD_decompressFrame (one frame), ZSTD_copyRawBlock and
   ZSTD_setRleBlock (Raw and RLE blocks: only the capacity is checked, not Block_Maximum_Size).  Compressed
   blocks are a parameter of the section: ZSTD_decompressBlock_internal (model/ExBlock.v) on the destination
   memory as zstd addresses it: the written cells, the prefix [ps, op) and the extDict [ds, de) it may read as
   history, the block's body, Block_Maximum_Size, the capacity from op and the streaming flag; it returns the
   new entropy state, the new cells and the decoded size.  In one-shot decoding without a dictionary the
   destination is the frame's output so far, all of it prefix (zstd's prefixStart is the frame's start). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Xxh64.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section ExFrame.

Variable xst : Type.
(* the context's decoding state on a new context (no tables, the literal buffer zeroed), and what
   ZSTD_decompressBegin without a dictionary makes of a state (tables dropped, litExtraBuffer kept) *)
Variable xst_init : xst.
Variable xst_begin : xst -> xst.
(* ZSTD_decompressBlock_internal on a compressed block: st mem ps op ds de body bsm cap streaming *)
Variable x_block : xst -> list Z -> Z -> Z -> Z -> Z -> list Z -> Z -> Z -> bool -> option (xst * list Z * Z).

(* The blocks of a frame from s (at a block header): ZSTD_decompressFrame's loop (zstd_decompress.c 994-1048).
   out = the frame's output so far, cap = the frame's capacity (dstCapacity), bsm = its Block_Maximum_Size.
   The output, the bytes taken from s and the state after the last block.  Each block takes at least its 3
   header bytes, so length s steps suffice. *)
Fixpoint x_blocks (fuel: nat) (st: xst) (s out: list Z) (cap bsm: Z) : option (list Z * Z * xst) :=
  match fuel with
  | O => None
  | S f =>
      match cblock_size s with
      | None => None
      | Some c =>
          if c >? Zlength s - ZSTD_blockHeaderSize then None else
          let bp := block_props_of s in
          let body := slice s ZSTD_blockHeaderSize c in
          let room := cap - Zlength out in
          let res :=
            if bp_type bp =? 2 then
              match x_block st out 0 (Zlength out) 0 0 body bsm room false with
              | Some (st', mem, d) => Some (st', slice mem (Zlength out) d)
              | None => None
              end
            else if bp_type bp =? 0 then (if c >? room then None else Some (st, body))
            else (if bp_origSize bp >? room then None
                  else Some (st, repeat (byte_at body 0) (Z.to_nat (bp_origSize bp)))) in
          match res with
          | None => None
          | Some (st', content) =>
              let out' := out ++ content in
              if bp_last bp =? 1 then Some (out', ZSTD_blockHeaderSize + c, st')
              else match x_blocks f st' (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' cap bsm with
                   | Some (o, k, st'') => Some (o, ZSTD_blockHeaderSize + c + k, st'')
                   | None => None
                   end
          end
      end
  end.

(* One Zstandard frame at the start of s with capacity cap (ZSTD_decompressFrame, 959-1074, with
   ZSTD_frameHeaderSize_internal and ZSTD_decodeFrameHeader), from the context's state st (ZSTD_decompressBegin
   first): the content, the bytes the frame takes and the state after it. *)
Definition x_frame (st: xst) (s: list Z) (cap: Z) : option (list Z * Z * xst) :=
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize then None else
  let hs := fhd_header_size (byte_at s 4) in
  if Zlength s <? hs + ZSTD_blockHeaderSize then None else
  match get_frame_header (slice s 0 hs) with
  | FH_ok h =>
      (* without a dictionary dctx->dictID is 0: any other frame dictionary ID is dictionary_wrong *)
      if negb (fh_dictID h =? 0) then None else
      let rest := skipn (Z.to_nat hs) s in
      match x_blocks (length rest) (xst_begin st) rest nil cap (fh_blockSizeMax h) with
      | None => None
      | Some (out, k, st') =>
          if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
          then None else
          if fh_checksumFlag h =? 1 then
            (if Zlength s - hs - k <? 4 then None
             else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then None
             else Some (out, hs + k + 4, st'))
          else Some (out, hs + k, st')
      end
  | _ => None
  end.

(* The series from s (ZSTD_decompressMultiFrame, 1076-1205): frames and skippable frames while at least
   ZSTD_startingInputLength = 5 bytes are left, then nothing may be left.  out = the output so far, cap = the
   whole capacity.  Every iteration takes at least 8 bytes, so length s + 1 steps suffice. *)
Fixpoint x_series_loop (fuel: nat) (st: xst) (s: list Z) (cap: Z) (out: list Z) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (if Zlength s =? 0 then Some out else None) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => None
        | Some k => x_series_loop f st (skipn (Z.to_nat k) s) cap out
        end
      else
        match x_frame st s (cap - Zlength out) with
        | None => None
        | Some (c, k, st') => x_series_loop f st' (skipn (Z.to_nat k) s) cap (out ++ c)
        end
  end.

(* ZSTD_decompressDCtx(dctx, dst, cap, s, |s|) on a new context (or one reset with the parameters) *)
Definition x_series (s: list Z) (cap: Z) : option (list Z) := x_series_loop (S (length s)) xst_init s cap nil.

End ExFrame.

(* sanity checks on frames without compressed blocks (model/Series.v's examples) *)
Local Definition no_cblock (_: unit) (_: list Z) (_ _ _ _: Z) (_: list Z) (_ _: Z) (_: bool) : option (unit * list Z * Z) :=
  None.

(* raw block "abc" in a single-segment frame of declared size 3 *)
Example x_raw_abc : x_series unit tt (fun u => u) no_cblock [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 3 = Some [97; 98; 99].
Proof. vm_compute. reflexivity. Qed.
(* the same with a capacity of 2: dstSize_tooSmall *)
Example x_raw_abc_small : x_series unit tt (fun u => u) no_cblock [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 2 = None.
Proof. vm_compute. reflexivity. Qed.
(* RLE block of 5 x 'z' *)
Example x_rle : x_series unit tt (fun u => u) no_cblock [40; 181; 47; 253; 32; 5; 43; 0; 0; 122] 5 = Some [122; 122; 122; 122; 122].
Proof. vm_compute. reflexivity. Qed.
(* the Reserved_bit set: refused *)
Example x_reserved : x_series unit tt (fun u => u) no_cblock [40; 181; 47; 253; 40; 5; 43; 0; 0; 122] 5 = None.
Proof. vm_compute. reflexivity. Qed.
(* a skippable frame of 1 byte, then the raw frame *)
Example x_skip_raw : x_series unit tt (fun u => u) no_cblock
  [80; 42; 77; 24; 1; 0; 0; 0; 7; 40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] 10 = Some [97; 98; 99].
Proof. vm_compute. reflexivity. Qed.
(* trailing garbage of 3 bytes after the frame: srcSize_wrong *)
Example x_trailing : x_series unit tt (fun u => u) no_cblock [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99; 1; 2; 3] 3 = None.
Proof. vm_compute. reflexivity. Qed.
