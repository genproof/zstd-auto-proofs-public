(* The format model under zstd's decoding parameters (API v3).  Plain Coq.

   Series.v / StreamModel.v model zstd with its default parameters.  This file generalises them, without
   changing them:
   - dmode: ZSTD_d_format (magicless frames: no magic number, no skippable frames), ZSTD_d_forceIgnoreChecksum
     (a Content_Checksum is read but not compared), ZSTD_d_maxBlockSize (Block_Maximum_Size capped);
   - sel: the per-frame dictionary of ZSTD_d_refMultipleDDicts (streaming: at each Zstandard frame header,
     zstd looks the frame's Dictionary_ID up in its DDict set and, when found, decodes with that DDict from
     then on); sel_none = no selection; the dictionary before the first frame is an option (None: not known,
     e.g. which DDict an earlier selection left current; frames it would decode give no claim);
   - the buffer-less API (ZSTD_decompressBegin / ZSTD_nextSrcSizeToDecompress / ZSTD_decompressContinue), as
     a step function over its stages.
   With md_dflt and sel_none every function here is the one of Series.v / StreamModel.v (lemmas *_dflt). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Xxh64.
Local Open Scope bool_scope.

(* ---------- decoding parameters ---------- *)

(* md_bmax: the cap ZSTD_d_maxBlockSize puts on Block_Maximum_Size (ZSTD_BLOCKSIZE_MAX when not set);
   md_dwin (v3.1): the dictionary is referenced only while the frame's output stays within its window
   (RFC 8878 5: "the dictionary can be referenced as long as Window_Size is not exceeded"): what zstd's
   buffered streaming keeps (its ring buffer drops the dictionary at the first wrap); one-shot decoding keeps
   the whole dictionary (md_dwin = false, the model of Block.v) *)
Record dmode := { md_magicless : bool; md_ignore : bool; md_bmax : Z; md_dwin : bool }.
Definition md_dflt : dmode :=
  {| md_magicless := false; md_ignore := false; md_bmax := ZSTD_BLOCKSIZE_MAX; md_dwin := false |}.

(* the same, with the dictionary window rule *)
Definition dmode_w (md: dmode) : dmode :=
  {| md_magicless := md_magicless md; md_ignore := md_ignore md; md_bmax := md_bmax md; md_dwin := true |}.

(* ZSTD_startingInputLength(format) *)
Definition starting_len (mg: bool) : Z := if mg then 1 else ZSTD_FRAMEHEADERSIZE_PREFIX.

Definition magic_bytes : list Z := le_bytes 4 ZSTD_MAGICNUMBER.

Definition fh_unshift (h: frame_header) : frame_header :=
  {| fh_contentSize := fh_contentSize h; fh_windowSize := fh_windowSize h; fh_blockSizeMax := fh_blockSizeMax h;
     fh_frameType := fh_frameType h; fh_headerSize := fh_headerSize h - 4; fh_dictID := fh_dictID h;
     fh_checksumFlag := fh_checksumFlag h |}.

(* ZSTD_getFrameHeader_advanced(zfh, src, srcSize, format): a magicless header reads as the zstd1 header of
   the same bytes behind a magic number, 4 bytes shorter *)
Definition get_frame_header_m (mg: bool) (s: list Z) : fh_result :=
  if negb mg then get_frame_header s else
  if Zlength s <? 1 then FH_more 1 else
  match get_frame_header (magic_bytes ++ s) with
  | FH_ok h => FH_ok (fh_unshift h)
  | FH_more k => FH_more (k - 4)
  | FH_err => FH_err
  end.

(* v3.1: the error code ZSTD_getFrameHeader_advanced returns where get_frame_header_m gives FH_err:
   prefix_unknown (10) for bytes that are not a frame's start, frameParameter_unsupported (14) for the
   Reserved_bit, frameParameter_windowTooLarge (16) for a window beyond ZSTD_WINDOWLOG_MAX (as 2^64 - code).
   Magicless: the zstd1 code of the same bytes behind a magic number (never prefix_unknown). *)
Definition ZSTD_error_prefix_unknown : Z := 10.
Definition ZSTD_error_frameParameter_unsupported : Z := 14.
Definition ZSTD_error_frameParameter_windowTooLarge : Z := 16.

Definition fh_err_code (s: list Z) : Z :=
  let n := Zlength s in
  if n <? 5 then 2 ^ 64 - ZSTD_error_prefix_unknown else
  if negb (le_field s 0 4 =? ZSTD_MAGICNUMBER) then 2 ^ 64 - ZSTD_error_prefix_unknown else
  let fhd := byte_at s 4 in
  if negb (Z.land fhd 8 =? 0) then 2 ^ 64 - ZSTD_error_frameParameter_unsupported
  else 2 ^ 64 - ZSTD_error_frameParameter_windowTooLarge.

Definition fh_err_code_m (mg: bool) (s: list Z) : Z :=
  if mg then fh_err_code (magic_bytes ++ s) else fh_err_code s.

(* ZSTD_frameHeaderSize_internal(src, n >= starting_len, format) *)
Definition header_size_m (mg: bool) (s: list Z) : Z :=
  if mg then fhd_header_size (byte_at s 0) - 4 else fhd_header_size (byte_at s 4).

(* ---------- blocks with the dictionary window rule (md_dwin) ----------
   Block.v's exec_seqs / decode_block / Series.decode_blocks, except that a match beyond the window
   (offset > wsize) is allowed only into the dictionary (offset > the frame's output so far) while the output
   stays within the window (|out| + ml <= wsize).  Without a dictionary (hist = []) they are Block.v's. *)
Fixpoint exec_seqs_w (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    : option (list Z * list Z * (Z * Z * Z)) :=
  match seqs with
  | nil => Some (out, lits, rep)
  | sq :: rest =>
      if sq_ll sq >? Zlength lits then None else
      let out := out ++ firstn (Z.to_nat (sq_ll sq)) lits in
      let lits := skipn (Z.to_nat (sq_ll sq)) lits in
      match resolve_offset rep (sq_ll sq) (sq_ov sq) with
      | None => None
      | Some (offset, rep) =>
          if offset >? Zlength hist + Zlength out then None else
          if (offset >? wsize) && negb ((offset >? Zlength out) && (Zlength out + sq_ml sq <=? wsize)) then None else
          exec_seqs_w wsize rep hist lits (lz_copy hist out offset (Z.to_nat (sq_ml sq))) rest
      end
  end.

Definition decode_block_w (st: dstate) (hist out: list Z) (b: list Z) (bsm wsize: Z)
    : option (dstate * list Z) :=
  if Zlength b >? bsm then None else
  match decode_literals (st_huf st) b bsm with
  | None => None
  | Some (lits, lused, huf) =>
    let rest := skipn (Z.to_nat lused) b in
    match decode_seq_header (st_seq st) rest with
    | None => None
    | Some (nbSeq, tabs, hused) =>
      let bits := skipn (Z.to_nat hused) rest in
      let seqs :=
        if nbSeq =? 0 then Some nil else
        match tabs with
        | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML bits nbSeq
        | None => None
        end in
      match seqs with
      | None => None
      | Some seqs =>
        match exec_seqs_w wsize (st_rep st) hist lits out seqs with
        | None => None
        | Some (out', lits', rep') =>
            let content := skipn (length out) (out' ++ lits') in
            if Zlength content >? bsm then None else
            Some ({| st_huf := huf; st_seq := tabs; st_rep := rep' |}, content)
        end
      end
    end
  end.

Fixpoint decode_blocks_w (fuel: nat) (st: dstate) (hist: list Z) (s out: list Z) (bsm wsize: Z)
    : option (list Z * Z) :=
  match fuel with
  | O => None
  | S f =>
      match cblock_size s with
      | None => None
      | Some c =>
          if c >? Zlength s - ZSTD_blockHeaderSize then None else
          let bp := block_props_of s in
          let body := slice s ZSTD_blockHeaderSize c in
          let res :=
            if bp_type bp =? 0 then
              (if c >? bsm then None else Some (st, out ++ body))
            else if bp_type bp =? 1 then
              (if (bp_origSize bp >? bsm) || (c >? bsm) then None
               else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
            else
              match decode_block_w st hist out body bsm wsize with
              | Some (st', content) => Some (st', out ++ content)
              | None => None
              end in
          match res with
          | None => None
          | Some (st', out') =>
              if bp_last bp =? 1 then Some (out', ZSTD_blockHeaderSize + c)
              else match decode_blocks_w f st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' bsm wsize with
                   | Some (o, k) => Some (o, ZSTD_blockHeaderSize + c + k)
                   | None => None
                   end
          end
      end
  end.

(* ---------- one Zstandard frame (ZSTD_decompressFrame) ---------- *)

Definition decode_frame_m (md: dmode) (dm: dict_model) (wlim: Z) (s: list Z) : fres :=
  let mg := md_magicless md in
  let sh := if mg then 4 else 0 in
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN - sh + ZSTD_blockHeaderSize then FUnk else
  if negb mg && negb (le_field s 0 4 =? ZSTD_MAGICNUMBER) then FUnk else
  let fhd := byte_at s (4 - sh) in
  if Zlength s <? fhd_header_size fhd - sh + ZSTD_blockHeaderSize then FUnk else
  if negb (Z.land fhd 8 =? 0) then FDetHdr else
  let single := Z.land (Z.shiftr fhd 5) 1 =? 1 in
  if negb single && (Z.shiftr (byte_at s (5 - sh)) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)
  then FDetHdr else
  match get_frame_header_m mg s with
  | FH_ok h =>
      if fh_windowSize h >? wlim then FDetHdr else
      if negb (fh_frameType h =? 0) then FUnk else
      if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
      let hs := fh_headerSize h in
      let rest := skipn (Z.to_nat hs) s in
      let bsm := Z.min (fh_blockSizeMax h) (md_bmax md) in
      match (if md_dwin md then decode_blocks_w else decode_blocks)
              (length rest) (dm_state dm) (dm_content dm) rest nil bsm (fh_windowSize h) with
      | None => FUnk
      | Some (out, k) =>
          if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
          then FUnk else
          if fh_checksumFlag h =? 1 then
            (if Zlength s - hs - k <? 4 then FUnk
             else if negb (md_ignore md) && negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
             else FOk out (hs + k + 4))
          else FOk out (hs + k)
      end
  | _ => FUnk
  end.

(* ---------- series, with the per-frame dictionary selection ---------- *)

Definition sel_none : Z -> option dict_model := fun _ => None.

(* the dictionary a Zstandard frame at the start of s is decoded with: the one sel gives for its
   Dictionary_ID, else the current one cur (None: not known, no claim) *)
Definition frame_dict (mg: bool) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z)
    : option dict_model :=
  match get_frame_header_m mg s with
  | FH_ok h => match sel (fh_dictID h) with Some d => Some d | None => cur end
  | _ => match cur with Some d => Some d | None => Some no_dict end
     (* v3.3: a header zstd cannot parse decides the frame (FDetHdr / FUnk) with any dictionary *)
  end.

Fixpoint walk_m (fuel: nat) (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wlim: Z)
    (s: list Z) (off: Z) : list frec * tail :=
  match fuel with
  | O => (nil, TUnk)
  | S f =>
      let mg := md_magicless md in
      if Zlength s <? starting_len mg then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if negb mg && is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            (* v3.4: buffered streaming (md_dwin) also selects a DDict by a skippable frame's magic variant *)
            let cur' := if md_dwin md
                        then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end
                        else cur in
            let '(l, t) := walk_m f md sel cur' wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match frame_dict mg sel cur s with
        | None => (nil, TUnk)
        | Some d =>
            match decode_frame_m md d wlim s with
            | FOk c k =>
                let '(l, t) := walk_m f md sel (Some d) wlim (skipn (Z.to_nat k) s) (off + k) in
                ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
            | FDetHdr => (nil, TDetHdr)
            | FDetCk => (nil, TDetCk)
            | FUnk => (nil, TUnk)
            end
        end
  end.

Definition series_frames_m (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (wlim: Z) (s: list Z)
    : list frec * tail :=
  walk_m (S (length s)) md sel dm wlim s 0.

Definition decode_series_m (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (wlim: Z) (s: list Z)
    : sres :=
  match series_frames_m md sel dm wlim s with
  | (l, TEnd) => SOk (flat_map fr_content l)
  | (_, TDetHdr) => SDet
  | (_, TDetCk) => SDet
  | (_, TUnk) => SUnk
  end.

(* ---------- streaming (StreamModel.v with parameters, a dictionary and a window limit wl) ---------- *)

Definition stream_alive_m (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (sin: list Z) : Prop :=
  exists s, bytes_ok s /\ is_prefix sin s /\
    (snd (series_frames_m md sel dm no_wlim s) = TEnd \/ snd (series_frames_m md sel dm no_wlim s) = TDetHdr).

Definition stream_claims_m (md: dmode) (sel: Z -> option dict_model) (dm: option dict_model) (wl: Z)
    (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) : Prop :=
  forall s, bytes_ok s -> is_prefix sin s ->
  let fl0 := fst (series_frames_m md sel dm no_wlim s) in
  let t0 := snd (series_frames_m md sel dm no_wlim s) in
  let fl := fst (series_frames_m md sel dm wl s) in
  let t := snd (series_frames_m md sel dm wl s) in
  (t0 = TEnd \/ t0 = TDetHdr -> is_prefix sout (flat_map fr_content fl0)) /\
  (r = 0 -> t0 <> TUnk ->
     exists n, (1 <= n <= length fl0)%nat /\
       Zlength sin = fr_end (nth (n - 1) fl0 fr_dflt) /\
       sout = flat_map fr_content (firstn n fl0)) /\
  (t0 = TEnd \/ t0 = TDetHdr -> is_error_code r = false -> 0 < r ->
     (Zlength sin0 < Zlength s \/ Zlength sout0 < Zlength (flat_map fr_content fl0)) ->
     r <= Z.max (if (Zlength sin <? Zlength s) || (Zlength sout <? Zlength (flat_map fr_content fl0)) then 1 else a1)
                (cur_end fl0 (Zlength sin) (Zlength sout) (Zlength s) - Zlength sin)) /\
  (is_prefix sall s -> t = TEnd -> is_error_code r = true -> forall e, r = 2 ^ 64 - e ->
     e = ZSTD_error_memory_allocation \/ e = ZSTD_error_noForwardProgress_destFull \/
     e = ZSTD_error_noForwardProgress_inputEmpty \/
     (exists osz, ocap = Some osz /\ osz < Zlength (flat_map fr_content fl))).

(* ---------- the buffer-less API (ZSTD_decompressContinue's stages) ---------- *)

(* ZSTDds_getFrameHeaderSize, decodeFrameHeader, decodeBlockHeader, decompressBlock, decompressLastBlock,
   checkChecksum, decodeSkippableHeader, skipFrame *)
Inductive blstage := BHdrPrefix | BHdrRest | BBlkHdr | BBlk | BLastBlk | BCk | BSkipHdr | BSkip.

(* the stage, dctx->expected, the header bytes read so far, the frame header (v3.1: blockSizeMax NOT capped by
   md_bmax: ZSTD_decompressContinue ignores ZSTD_d_maxBlockSize), the entropy state, the frame's content so far, the current block's type and RLE size.
   A frame is fully decoded in stage BHdrPrefix with bs_expect = 0. *)
Record blst := {
  bs_stage : blstage; bs_expect : Z; bs_hbuf : list Z; bs_hdr : frame_header; bs_ds : dstate;
  bs_out : list Z; bs_btype : Z; bs_rle : Z }.

Definition fh_none : frame_header :=
  {| fh_contentSize := 0; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 0; fh_headerSize := 0;
     fh_dictID := 0; fh_checksumFlag := 0 |}.

(* after ZSTD_decompressBegin* with the dictionary dm *)
Definition bl_init (md: dmode) (dm: dict_model) : blst :=
  {| bs_stage := BHdrPrefix; bs_expect := starting_len (md_magicless md); bs_hbuf := nil; bs_hdr := fh_none;
     bs_ds := dm_state dm; bs_out := nil; bs_btype := 0; bs_rle := 0 |}.

Definition bl_set (b: blst) (stg: blstage) (e: Z) : blst :=
  {| bs_stage := stg; bs_expect := e; bs_hbuf := bs_hbuf b; bs_hdr := bs_hdr b; bs_ds := bs_ds b;
     bs_out := bs_out b; bs_btype := bs_btype b; bs_rle := bs_rle b |}.

(* BLOk b' out: the call succeeds, delivers out (when the capacity holds it) and leaves b';
   BLErr: zstd returns an error; BLUnk: no claim (the block model rejects what zstd may accept) *)
Inductive blres := BLOk (b: blst) (out: list Z) | BLErr | BLUnk.

Definition bl_frame_end (b: blst) : blstage * Z :=
  if fh_checksumFlag (bs_hdr b) =? 1 then (BCk, 4) else (BHdrPrefix, 0).

(* a block's content decoded: the content size check at the last block, then the next stage *)
Definition bl_block_done (b: blst) (ds: dstate) (content: list Z) : blres :=
  let out' := bs_out b ++ content in
  let b1 := {| bs_stage := bs_stage b; bs_expect := 0; bs_hbuf := bs_hbuf b; bs_hdr := bs_hdr b; bs_ds := ds;
               bs_out := out'; bs_btype := bs_btype b; bs_rle := bs_rle b |} in
  if Zlength content >? fh_blockSizeMax (bs_hdr b) then BLErr else
  match bs_stage b with
  | BLastBlk =>
      if negb (fh_contentSize (bs_hdr b) =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out' =? fh_contentSize (bs_hdr b))
      then BLErr
      else let '(stg, e) := bl_frame_end b in BLOk (bl_set b1 stg e) content
  | _ => BLOk (bl_set b1 BBlkHdr ZSTD_blockHeaderSize) content
  end.

(* One call ZSTD_decompressContinue(dctx, dst, cap, c, Zlength c) with Zlength c = bs_expect b > 0, in a
   frame begun with the dictionary dm.  The block's history is the dictionary content and the frame's
   content so far (the output written contiguously). *)
Definition bl_step (md: dmode) (dm: dict_model) (b: blst) (c: list Z) : blres :=
  let mg := md_magicless md in
  match bs_stage b with
  | BHdrPrefix =>
      if negb mg && is_skippable_magic (le_field c 0 4) then
        BLOk {| bs_stage := BSkipHdr; bs_expect := ZSTD_SKIPPABLEHEADERSIZE - Zlength c; bs_hbuf := c;
                bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |} nil
      else
        BLOk {| bs_stage := BHdrRest; bs_expect := header_size_m mg c - Zlength c; bs_hbuf := c;
                bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |} nil
  | BHdrRest =>
      match get_frame_header_m mg (bs_hbuf b ++ c) with
      | FH_ok h =>
          if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then BLErr else
          let h' := {| fh_contentSize := fh_contentSize h; fh_windowSize := fh_windowSize h;
                       fh_blockSizeMax := fh_blockSizeMax h; fh_frameType := fh_frameType h;
                       fh_headerSize := fh_headerSize h; fh_dictID := fh_dictID h;
                       fh_checksumFlag := fh_checksumFlag h |} in
          BLOk {| bs_stage := BBlkHdr; bs_expect := ZSTD_blockHeaderSize; bs_hbuf := bs_hbuf b ++ c; bs_hdr := h';
                  bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |} nil
      | _ => BLErr
      end
  | BBlkHdr =>
      match cblock_size c with
      | None => BLErr
      | Some cs =>
          let bp := block_props_of c in
          if cs >? fh_blockSizeMax (bs_hdr b) then BLErr else
          let b1 := {| bs_stage := bs_stage b; bs_expect := cs; bs_hbuf := bs_hbuf b; bs_hdr := bs_hdr b;
                       bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := bp_type bp; bs_rle := bp_origSize bp |} in
          if cs =? 0 then
            (if bp_last bp =? 1 then
               (* F6: an empty last block ends the frame, with the content size check of bl_block_done *)
               if negb (fh_contentSize (bs_hdr b) =? ZSTD_CONTENTSIZE_UNKNOWN) &&
                  negb (Zlength (bs_out b) =? fh_contentSize (bs_hdr b))
               then BLErr
               else let '(stg, e) := bl_frame_end b in BLOk (bl_set b1 stg e) nil
             else BLOk (bl_set b1 BBlkHdr ZSTD_blockHeaderSize) nil)
          else BLOk (bl_set b1 (if bp_last bp =? 1 then BLastBlk else BBlk) cs) nil
      end
  | BBlk | BLastBlk =>
      if bs_btype b =? 0 then bl_block_done b (bs_ds b) c
      else if bs_btype b =? 1 then bl_block_done b (bs_ds b) (repeat (byte_at c 0) (Z.to_nat (bs_rle b)))
      else if bs_btype b =? 2 then
        match decode_block (bs_ds b) (dm_content dm) (bs_out b) c (fh_blockSizeMax (bs_hdr b))
                (fh_windowSize (bs_hdr b)) with
        | Some (ds', content) => bl_block_done b ds' content
        | None => BLUnk
        end
      else BLErr
  | BCk =>
      if (fh_checksumFlag (bs_hdr b) =? 1) && negb (md_ignore md) &&
         negb (le_field c 0 4 =? xxh64 (bs_out b) 0 mod 2 ^ 32)
      then BLErr
      else BLOk (bl_set b BHdrPrefix 0) nil
  | BSkipHdr =>
      BLOk {| bs_stage := BSkip; bs_expect := le_field (bs_hbuf b ++ c) 4 4; bs_hbuf := bs_hbuf b ++ c;
              bs_hdr := bs_hdr b; bs_ds := bs_ds b; bs_out := bs_out b; bs_btype := 0; bs_rle := 0 |} nil
  | BSkip => BLOk (bl_set b BHdrPrefix 0) nil
  end.

(* ZSTD_nextInputType: ZSTDnit_frameHeader 0, blockHeader 1, block 2, lastBlock 3, checksum 4, skippableFrame 5 *)
Definition bl_input_type (b: blst) : Z :=
  match bs_stage b with
  | BHdrPrefix | BHdrRest => 0 | BBlkHdr => 1 | BBlk => 2 | BLastBlk => 3 | BCk => 4 | BSkipHdr | BSkip => 5
  end.

(* exact feeding: the bytes fed so far, in the pieces zstd asked for; None when a call fails or is unknown *)
Fixpoint bl_run (md: dmode) (dm: dict_model) (b: blst) (pieces: list (list Z)) : option blst :=
  match pieces with
  | nil => Some b
  | c :: cs =>
      if negb (Zlength c =? bs_expect b) then None else
      match bl_step md dm b c with
      | BLOk b' _ => bl_run md dm b' cs
      | _ => None
      end
  end.

(* ---------- small checks ---------- *)

Example get_frame_header_m_magicless :
  get_frame_header_m true [32; 3; 25; 0; 0; 97; 98; 99] =
  match get_frame_header [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] with
  | FH_ok h => FH_ok (fh_unshift h) | r => r end.
Proof. vm_compute. reflexivity. Qed.

Example decode_series_m_raw_abc :
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] = SOk [97; 98; 99] /\
  decode_series_m {| md_magicless := true; md_ignore := false; md_bmax := ZSTD_BLOCKSIZE_MAX; md_dwin := false |} sel_none (Some no_dict) no_wlim
    [32; 3; 25; 0; 0; 97; 98; 99] = SOk [97; 98; 99] /\
  decode_series_m {| md_magicless := false; md_ignore := false; md_bmax := 2; md_dwin := false |} sel_none (Some no_dict) no_wlim
    [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] = SUnk.
Proof. vm_compute. auto. Qed.

(* the buffer-less steps on the frame "abc": 5 header bytes, 2 more, a block header, the block *)
Example bl_run_abc :
  match bl_run md_dflt no_dict (bl_init md_dflt no_dict) [[40; 181; 47; 253; 32]; [3]; [25; 0; 0]; [97; 98; 99]] with
  | Some b => (bs_stage b, bs_expect b, bs_out b)
  | None => (BSkip, -1, nil)
  end = (BHdrPrefix, 0, [97; 98; 99]).
Proof. vm_compute. reflexivity. Qed.
