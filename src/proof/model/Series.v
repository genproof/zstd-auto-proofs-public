(* The format model: dictionaries (RFC 8878, 5), frames (3.1.1) and series of frames, as zstd's
   decoder reads them (lib/decompress/zstd_decompress.c, zstd_ddict.c).  Plain Coq, no VST.

   The outcome of decoding a series s with a dictionary dm (`decode_series dm wlim s`):
   - SOk c: zstd's decoder returns exactly c (the specifications allow the errors that do not depend
     on the data: memory allocation, a capacity smaller than c);
   - SDet: zstd's decoder certainly returns an error: the first frame that is not Ok has its
     Reserved_bit set, or a window beyond zstd's range (windowLog > ZSTD_WINDOWLOG_MAX; Window_Size >
     wlim, the streaming limit), or a wrong Content_Checksum on content the model decodes;
   - SUnk: nothing is claimed.
   Frames are decoded in order; skippable frames are skipped.  wlim = the largest window accepted
   (one-shot decoding: no limit, `no_wlim`; streaming: ZSTD_WINDOWLOG_LIMIT_DEFAULT, `stream_wlim`). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Fse Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Frame Zstd.proof.model.Xxh64 Zstd.proof.model.Block.
Local Open Scope bool_scope.

Definition ZSTD_MAGIC_DICTIONARY : Z := 3962610743.   (* 0xEC30A437 *)
Definition no_wlim : Z := 2 ^ 64.
Definition stream_wlim : Z := 2 ^ 27 + 1.             (* (1 << ZSTD_WINDOWLOG_LIMIT_DEFAULT) + 1 *)

(* ---------- dictionaries ---------- *)

(* A dictionary as the decoder uses it: its content (the history in front of every frame), its ID
   (0 for raw content), and the entropy state frames start from. *)
Record dict_model := { dm_content : list Z; dm_id : Z; dm_state : dstate }.

(* no dictionary, or raw content (ZSTD_dct_rawContent; a dictionary without the magic number) *)
Definition dict_raw (b: list Z) : dict_model :=
  {| dm_content := b; dm_id := 0; dm_state := dstate_init |}.
Definition no_dict : dict_model := dict_raw nil.

(* ZSTD_loadDEntropy on a dictionary b with the magic number: the entropy state and the bytes of
   the header (magic, ID, tables, repeat offsets) *)
Definition load_dentropy (b: list Z) : option (dstate * Z) :=
  if Zlength b <=? 8 then None else
  match huf_parse_desc (skipn 8 b) with
  | None => None
  | Some (ht, hs) =>
  let p := 8 + hs in
  match read_ncount (skipn (Z.to_nat p) b) MaxOff with
  | None => None
  | Some (nOF, lOF, sOF) =>
  if lOF >? OffFSELog then None else
  let p := p + sOF in
  match read_ncount (skipn (Z.to_nat p) b) MaxML with
  | None => None
  | Some (nML, lML, sML) =>
  if lML >? MLFSELog then None else
  let p := p + sML in
  match read_ncount (skipn (Z.to_nat p) b) MaxLL with
  | None => None
  | Some (nLL, lLL, sLL) =>
  if lLL >? LLFSELog then None else
  let p := p + sLL in
  if p + 12 >? Zlength b then None else
  let csize := Zlength b - (p + 12) in
  let r1 := le_field b p 4 in
  let r2 := le_field b (p + 4) 4 in
  let r3 := le_field b (p + 8) 4 in
  if existsb (fun r => (r =? 0) || (r >? csize)) [r1; r2; r3] then None else
  Some ({| st_huf := Some ht;
           st_seq := Some (fse_build nLL lLL, fse_build nOF lOF, fse_build nML lML);
           st_rep := (r1, r2, r3) |}, p + 12)
  end end end end.

(* A dictionary in ZSTD_dct_auto mode (ZSTD_decompress_usingDict, ZSTD_createDDict(_byReference),
   ZSTD_DCtx_loadDictionary(_byReference)): raw content unless it starts with the magic number; None = a
   corrupted formatted dictionary (zstd: dictionary_corrupted). *)
Definition dict_auto (b: list Z) : option dict_model :=
  if Zlength b <? 8 then Some (dict_raw b) else
  if negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY) then Some (dict_raw b) else
  match load_dentropy b with
  | None => None
  | Some (st, esize) =>
      Some {| dm_content := skipn (Z.to_nat esize) b; dm_id := le_field b 4 4; dm_state := st |}
  end.

(* ZSTD_getDictID_fromDict *)
Definition dict_id_of (b: list Z) : Z :=
  if Zlength b <? 8 then 0 else
  if negb (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY) then 0 else le_field b 4 4.

(* ---------- frames ---------- *)

(* The blocks of a frame from s (at a block header), after the frame's output out: the output and the
   bytes taken.  Every block's content and size fit in Block_Maximum_Size bsm. *)
Fixpoint decode_blocks (fuel: nat) (st: dstate) (hist: list Z) (s out: list Z) (bsm wsize: Z)
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
              match decode_block st hist out body bsm wsize with
              | Some (st', content) => Some (st', out ++ content)
              | None => None
              end in
          match res with
          | None => None
          | Some (st', out') =>
              if bp_last bp =? 1 then Some (out', ZSTD_blockHeaderSize + c)
              else match decode_blocks f st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' bsm wsize with
                   | Some (o, k) => Some (o, ZSTD_blockHeaderSize + c + k)
                   | None => None
                   end
          end
      end
  end.

(* FDetHdr: rejected at the frame header (Reserved_bit, window), nothing of the frame is delivered;
   FDetCk: a wrong Content_Checksum, detected after the frame's content is decoded *)
Inductive fres := FOk (c: list Z) (size: Z) | FDetHdr | FDetCk | FUnk.

(* One Zstandard frame at the start of s (ZSTD_decompressFrame): its content and the bytes it takes. *)
Definition decode_frame (dm: dict_model) (wlim: Z) (s: list Z) : fres :=
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize then FUnk else
  if negb (le_field s 0 4 =? ZSTD_MAGICNUMBER) then FUnk else
  let fhd := byte_at s 4 in
  if Zlength s <? fhd_header_size fhd + ZSTD_blockHeaderSize then FUnk else
  if negb (Z.land fhd 8 =? 0) then FDetHdr else
  let single := Z.land (Z.shiftr fhd 5) 1 =? 1 in
  if negb single && (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)
  then FDetHdr else
  match get_frame_header s with
  | FH_ok h =>
      if fh_windowSize h >? wlim then FDetHdr else
      if negb (fh_frameType h =? 0) then FUnk else
      if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
      let hs := fh_headerSize h in
      let rest := skipn (Z.to_nat hs) s in
      match decode_blocks (length rest) (dm_state dm) (dm_content dm) rest nil (fh_blockSizeMax h) (fh_windowSize h) with
      | None => FUnk
      | Some (out, k) =>
          if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
          then FUnk else
          if fh_checksumFlag h =? 1 then
            (if Zlength s - hs - k <? 4 then FUnk
             else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
             else FOk out (hs + k + 4))
          else FOk out (hs + k)
      end
  | _ => FUnk
  end.

(* ---------- series ---------- *)

(* A frame of a series: where it is in the series' bytes, and its content (none for a skippable
   frame). *)
Record frec := { fr_start : Z; fr_size : Z; fr_content : list Z; fr_skippable : bool }.

(* How the walk over a series ends: all bytes consumed (TEnd), a frame that zstd certainly rejects at its
   header (TDetHdr) or by its checksum (TDetCk), or anything else (TUnk). *)
Inductive tail := TEnd | TDetHdr | TDetCk | TUnk.

(* The frames of s from offset off (ZSTD_decompressMultiFrame), in order, up to the first frame that
   is not Ok. *)
Fixpoint walk (fuel: nat) (dm: dict_model) (wlim: Z) (s: list Z) (off: Z) : list frec * tail :=
  match fuel with
  | O => (nil, TUnk)
  | S f =>
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match decode_frame dm wlim s with
        | FOk c k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
        | FDetHdr => (nil, TDetHdr)
        | FDetCk => (nil, TDetCk)
        | FUnk => (nil, TUnk)
        end
  end.

Definition series_frames (dm: dict_model) (wlim: Z) (s: list Z) : list frec * tail :=
  walk (S (length s)) dm wlim s 0.

Inductive sres := SOk (c: list Z) | SDet | SUnk.

Definition decode_series (dm: dict_model) (wlim: Z) (s: list Z) : sres :=
  match series_frames dm wlim s with
  | (l, TEnd) => SOk (flat_map fr_content l)
  | (_, TDetHdr) => SDet
  | (_, TDetCk) => SDet
  | (_, TUnk) => SUnk
  end.

(* ---------- sanity checks ---------- *)

(* raw block "abc" in a single-segment frame of declared size 3 (FHD 0x20, fcs byte 3) *)
Example decode_raw_abc :
  decode_series no_dict no_wlim [40; 181; 47; 253; 32; 3; 25; 0; 0; 97; 98; 99] = SOk [97; 98; 99].
Proof. vm_compute. reflexivity. Qed.

(* RLE block of 5 x 'z' (header: last=1, type=1, size=5: 5<<3 | 1<<1 | 1 = 43) *)
Example decode_rle :
  decode_series no_dict no_wlim [40; 181; 47; 253; 32; 5; 43; 0; 0; 122] = SOk [122; 122; 122; 122; 122].
Proof. vm_compute. reflexivity. Qed.

(* the same with the Reserved_bit set (FHD 0x28): certainly rejected *)
Example decode_reserved :
  decode_series no_dict no_wlim [40; 181; 47; 253; 40; 5; 43; 0; 0; 122] = SDet.
Proof. vm_compute. reflexivity. Qed.
