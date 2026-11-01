(* The format model: frames (RFC 8878, 3.1), as zstd's decoder reads them (lib/decompress/zstd_decompress.c).

   Plain Coq, no VST.  Byte strings are `list Z` (Bytes.v).  The functions here mirror the C functions
   that only read the input (ZSTD_getFrameHeader_advanced, ZSTD_frameHeaderSize_internal,
   readSkippableFrameSize, ZSTD_getcBlockSize, ZSTD_findFrameSizeInfo, ZSTD_findDecompressedSize):
   their specifications say "returns exactly this".  Only the format ZSTD_f_zstd1 (with magic number)
   is modelled: no harness sets another format.

   Sizes are mathematical integers; the C results are size_t / unsigned long long: an error is an
   error code (Bytes.is_error_code), modelled by `err` below (which error code is not specified). *)
Require Import Zstd.proof.model.Bytes.
Local Open Scope bool_scope.

Definition ZSTD_MAGICNUMBER : Z := 4247762216.            (* 0xFD2FB528 *)
Definition ZSTD_MAGIC_SKIPPABLE_START : Z := 407710288.    (* 0x184D2A50 *)
Definition ZSTD_MAGIC_SKIPPABLE_MASK : Z := 4294967280.    (* 0xFFFFFFF0 *)
Definition ZSTD_CONTENTSIZE_UNKNOWN : Z := 2 ^ 64 - 1.
Definition ZSTD_CONTENTSIZE_ERROR : Z := 2 ^ 64 - 2.
Definition ZSTD_BLOCKSIZE_MAX : Z := 131072.               (* 128 KiB *)
Definition ZSTD_WINDOWLOG_MAX : Z := 31.                   (* 64-bit *)
Definition ZSTD_WINDOWLOG_ABSOLUTEMIN : Z := 10.
Definition ZSTD_FRAMEHEADERSIZE_PREFIX : Z := 5.           (* = ZSTD_startingInputLength(ZSTD_f_zstd1) *)
Definition ZSTD_FRAMEHEADERSIZE_MIN : Z := 6.
Definition ZSTD_SKIPPABLEHEADERSIZE : Z := 8.
Definition ZSTD_blockHeaderSize : Z := 3.

Definition is_skippable_magic (m: Z) : bool :=
  Z.land m ZSTD_MAGIC_SKIPPABLE_MASK =? ZSTD_MAGIC_SKIPPABLE_START.

(* ---------- frame header ---------- *)

(* ZSTD_FrameHeader (the struct the decoder fills), with frameType 0 = ZSTD_frame, 1 = skippable. *)
Record frame_header := {
  fh_contentSize : Z;      (* ZSTD_CONTENTSIZE_UNKNOWN if absent *)
  fh_windowSize : Z;
  fh_blockSizeMax : Z;
  fh_frameType : Z;
  fh_headerSize : Z;
  fh_dictID : Z;
  fh_checksumFlag : Z
}.

(* ZSTD_frameHeaderSize_internal, for srcSize >= 5: the header size given by the descriptor byte s[4] *)
Definition fhd_header_size (fhd: Z) : Z :=
  let dictID := Z.land fhd 3 in
  let singleSegment := Z.land (Z.shiftr fhd 5) 1 in
  let fcsId := Z.shiftr fhd 6 in
  5 + (1 - singleSegment)
    + nth (Z.to_nat dictID) [0; 1; 2; 4] 0
    + nth (Z.to_nat fcsId) [0; 2; 4; 8] 0
    + (if (singleSegment =? 1) && (fcsId =? 0) then 1 else 0).

(* The outcome of ZSTD_getFrameHeader_advanced(zfh, src, srcSize, ZSTD_f_zstd1):
   FH_err = an error code; FH_more k = returns k > 0 (needs k bytes); FH_ok h = returns 0, zfh := h. *)
Inductive fh_result := FH_err | FH_more (k: Z) | FH_ok (h: frame_header).

(* The 4 bytes of hbuf after copying min(4, n) bytes of s over `fill` (little-endian) *)
Definition magic_prefix (s: list Z) (fill: Z) : Z :=
  le_value (firstn (Z.to_nat (Z.min 4 (Zlength s))) s ++ skipn (Z.to_nat (Z.min 4 (Zlength s))) (le_bytes 4 fill)).

Definition get_frame_header (s: list Z) : fh_result :=
  let n := Zlength s in
  if n <? 5 then
    (if n >? 0 then
       (if negb (magic_prefix s ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER)
           && negb (is_skippable_magic (magic_prefix s ZSTD_MAGIC_SKIPPABLE_START))
        then FH_err else FH_more 5)
     else FH_more 5)
  else
  let magic := le_field s 0 4 in
  if negb (magic =? ZSTD_MAGICNUMBER) then
    (if is_skippable_magic magic then
       (if n <? ZSTD_SKIPPABLEHEADERSIZE then FH_more ZSTD_SKIPPABLEHEADERSIZE
        else FH_ok {| fh_contentSize := le_field s 4 4; fh_windowSize := 0; fh_blockSizeMax := 0;
                      fh_frameType := 1; fh_headerSize := ZSTD_SKIPPABLEHEADERSIZE;
                      fh_dictID := magic - ZSTD_MAGIC_SKIPPABLE_START; fh_checksumFlag := 0 |})
     else FH_err)
  else
  let fhd := byte_at s 4 in
  let fhsize := fhd_header_size fhd in
  if n <? fhsize then FH_more fhsize else
  let dictIDSizeCode := Z.land fhd 3 in
  let checksumFlag := Z.land (Z.shiftr fhd 2) 1 in
  let singleSegment := Z.land (Z.shiftr fhd 5) 1 in
  let fcsID := Z.shiftr fhd 6 in
  if negb (Z.land fhd 8 =? 0) then FH_err else
  let wlByte := byte_at s 5 in
  let windowLog := Z.shiftr wlByte 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN in
  if (singleSegment =? 0) && (windowLog >? ZSTD_WINDOWLOG_MAX) then FH_err else
  let pos := 5 + (1 - singleSegment) in
  let dsz := nth (Z.to_nat dictIDSizeCode) [0; 1; 2; 4] 0 in
  let dictID := le_field s pos dsz in
  let pos := pos + dsz in
  let fcs :=
    if fcsID =? 0 then (if singleSegment =? 1 then byte_at s pos else ZSTD_CONTENTSIZE_UNKNOWN)
    else if fcsID =? 1 then le_field s pos 2 + 256
    else if fcsID =? 2 then le_field s pos 4
    else le_field s pos 8 in
  let windowSize :=
    if singleSegment =? 1 then fcs
    else 2 ^ windowLog + Z.shiftr (2 ^ windowLog) 3 * Z.land wlByte 7 in
  FH_ok {| fh_contentSize := fcs; fh_windowSize := windowSize;
           fh_blockSizeMax := Z.min windowSize ZSTD_BLOCKSIZE_MAX;
           fh_frameType := 0; fh_headerSize := fhsize; fh_dictID := dictID;
           fh_checksumFlag := checksumFlag |}.

(* ZSTD_getFrameContentSize *)
Definition frame_content_size (s: list Z) : Z :=
  match get_frame_header s with
  | FH_ok h => if fh_frameType h =? 1 then 0 else fh_contentSize h
  | _ => ZSTD_CONTENTSIZE_ERROR
  end.

(* readSkippableFrameSize: Some size, or None (an error code) *)
Definition skippable_frame_size (s: list Z) : option Z :=
  if Zlength s <? ZSTD_SKIPPABLEHEADERSIZE then None else
  let sz := le_field s 4 4 in
  if sz + ZSTD_SKIPPABLEHEADERSIZE >? Zlength s then None else
  Some (sz + ZSTD_SKIPPABLEHEADERSIZE).

(* ---------- blocks ---------- *)

(* blockProperties_t: lastBlock, blockType (0 raw, 1 RLE, 2 compressed, 3 reserved), origSize *)
Record block_props := { bp_last : Z; bp_type : Z; bp_origSize : Z }.

Definition block_props_of (s: list Z) : block_props :=
  let h := le_field s 0 3 in
  {| bp_last := Z.land h 1; bp_type := Z.land (Z.shiftr h 1) 3; bp_origSize := Z.shiftr h 3 |}.

(* ZSTD_getcBlockSize: the bytes the block body takes after its header (RLE: 1), or None *)
Definition cblock_size (s: list Z) : option Z :=
  if Zlength s <? ZSTD_blockHeaderSize then None else
  let bp := block_props_of s in
  if bp_type bp =? 1 then Some 1 else
  if bp_type bp =? 3 then None else
  Some (bp_origSize bp).

(* ZSTD_findFrameSizeInfo's block walk: from the first block header, the bytes up to the end of the
   last block (headers included) and the number of blocks; None on an error. *)
Fixpoint blocks_size (fuel: nat) (s: list Z) : option (Z * Z) :=
  match fuel with
  | O => None
  | S f =>
      match cblock_size s with
      | None => None
      | Some c =>
          if ZSTD_blockHeaderSize + c >? Zlength s then None else
          if bp_last (block_props_of s) =? 1 then Some (ZSTD_blockHeaderSize + c, 1)
          else match blocks_size f (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) with
               | Some (k, nb) => Some (ZSTD_blockHeaderSize + c + k, nb + 1)
               | None => None
               end
      end
  end.

(* ZSTD_findFrameCompressedSize (format zstd1): Some size (the frame's bytes), or None (error) *)
Definition frame_compressed_size (s: list Z) : option Z :=
  if (Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field s 0 4) then
    skippable_frame_size s
  else
  match get_frame_header s with
  | FH_ok h =>
      let rest := skipn (Z.to_nat (fh_headerSize h)) s in
      match blocks_size (length rest) rest with
      | None => None
      | Some (k, _) =>
          let sz := fh_headerSize h + k in
          if fh_checksumFlag h =? 1 then
            (if Zlength s - sz <? 4 then None else Some (sz + 4))
          else Some sz
      end
  | _ => None
  end.

(* ZSTD_findDecompressedSize *)
Fixpoint fds_loop (fuel: nat) (s: list Z) (acc: Z) : Z :=
  match fuel with
  | O => ZSTD_CONTENTSIZE_ERROR
  | S f =>
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then
        (if Zlength s =? 0 then acc else ZSTD_CONTENTSIZE_ERROR)
      else if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => ZSTD_CONTENTSIZE_ERROR
        | Some k => fds_loop f (skipn (Z.to_nat k) s) acc
        end
      else
        let fcs := frame_content_size s in
        if fcs >=? ZSTD_CONTENTSIZE_ERROR then fcs else
        if acc + fcs >=? 2 ^ 64 then ZSTD_CONTENTSIZE_ERROR else
        match frame_compressed_size s with
        | None => ZSTD_CONTENTSIZE_ERROR
        | Some k => fds_loop f (skipn (Z.to_nat k) s) (acc + fcs)
        end
  end.

Definition find_decompressed_size (s: list Z) : Z := fds_loop (S (length s)) s 0.

(* A sanity check: an empty frame (magic, FHD 0x20 = single segment, fcs 0 in one byte, one empty raw
   last block 0x01 0x00 0x00): 0 bytes, frame size 9. *)
Example fds_empty_frame :
  find_decompressed_size [40; 181; 47; 253; 32; 0; 1; 0; 0] = 0 /\
  frame_compressed_size [40; 181; 47; 253; 32; 0; 1; 0; 0] = Some 9.
Proof. vm_compute. auto. Qed.
