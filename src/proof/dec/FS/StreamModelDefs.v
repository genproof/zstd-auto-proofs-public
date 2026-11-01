(* FS streaming: the model side of ZSTD_decompressStream's invariant.
   Plain Coq over the format model (model/Series.v, model/StreamModel.v); fixed for the streaming proof.

   The bytes a stream has read (sin) split into the frames it has finished (dsin: the model decodes them,
   no window limit, and they end exactly there) and the bytes fb of the frame it is in; the frame's
   progress fp (fprog) is what zstd knows of it: a header being loaded, a skippable frame being skipped,
   or a Zstandard frame with its header, its complete blocks, the content decoded so far, the entropy
   state and the position inside the current unit (block header, block body, checksum).
   - m_rel sin sout fp pend: the model agrees with zstd: the delivered bytes sout followed by the pending
     ones (decoded, not yet flushed) are the content of the finished frames and of the current one;
   - dead sin: the model makes no claim on any series that starts with sin (its first frame that is not
     Ok is FUnk, already decided by sin). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64
  Zstd.proof.model.Series Zstd.proof.model.StreamModel.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- one block of a frame (the body of Series.decode_blocks, no dictionary) ---------- *)

(* the block at the start of s after the frame's output out: the new entropy state, the output, the bytes
   the block takes (header included), whether it is the last one *)
Definition block_res (st: dstate) (s out: list Z) (bsm wsize: Z) : option (dstate * list Z * Z * bool) :=
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
          match decode_block st nil out body bsm wsize with
          | Some (st', content) => Some (st', out ++ content)
          | None => None
          end in
      match res with
      | None => None
      | Some (st', out') => Some (st', out', ZSTD_blockHeaderSize + c, bp_last bp =? 1)
      end
  end.

(* the complete blocks bl of a frame (bsm = Block_Maximum_Size, wsize = Window_Size): the state and the
   output after them, and whether the last one ends the frame *)
Inductive blocks_pre (bsm wsize: Z) : list Z -> dstate -> list Z -> bool -> Prop :=
| BPre_nil : blocks_pre bsm wsize nil dstate_init nil false
| BPre_snoc : forall bl ts out b ts' out' last,
    blocks_pre bsm wsize bl ts out false ->
    block_res ts b out bsm wsize = Some (ts', out', Zlength b, last) ->
    blocks_pre bsm wsize (bl ++ b) ts' out' last.

(* ---------- the progress of the current frame ---------- *)

(* where zstd is in a Zstandard frame after its header *)
Inductive zphase :=
| ZP_bhdr              (* at (or inside) a block header *)
| ZP_body (bh: list Z) (* inside the body of the block whose header is bh (3 bytes, body size > 0) *)
| ZP_ck                (* at (or inside) the Content_Checksum *)
| ZP_end.              (* the frame is complete *)

(* zstd's knowledge of a Zstandard frame: the header h, the bytes of the complete blocks, the entropy
   state after them, the content decoded so far (complete blocks, then the part of a raw block read so
   far), the phase, and the bytes of the current unit read so far (block header / body / checksum) *)
Record zprog := {
  zp_h : frame_header; zp_bl : list Z; zp_ts : dstate; zp_out : list Z; zp_ph : zphase; zp_got : list Z }.

Inductive fprog :=
| FP_none                              (* nothing of a frame (a stream's start) *)
| FP_hdr (hb: list Z)                  (* a frame header being loaded: its first bytes hb *)
| FP_skip (hdr: list Z) (got: Z)       (* a skippable frame: its 8 header bytes, got content bytes skipped *)
| FP_zstd (hdr: list Z) (z: zprog).    (* a Zstandard frame: its header bytes, the progress *)

(* the content zstd decoded of the current frame *)
Definition fp_content (fp: fprog) : list Z :=
  match fp with FP_zstd _ z => zp_out z | _ => nil end.

(* the frame is complete *)
Definition fp_complete (fp: fprog) : bool :=
  match fp with
  | FP_skip hdr got => got =? le_field hdr 4 4
  | FP_zstd _ z => match zp_ph z with ZP_end => true | _ => false end
  | _ => false
  end.

Definition fcs_ok (h: frame_header) (out: list Z) : Prop :=
  fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h.

(* the bytes fb of the current frame read so far, and what zstd knows of them, as the model reads them *)
Definition cur_rel (fb: list Z) (fp: fprog) : Prop :=
  match fp with
  | FP_none => fb = nil
  | FP_hdr hb =>
      fb = hb /\
      match get_frame_header hb with
      | FH_more k => Zlength hb < k
      | FH_ok h => fh_headerSize h = Zlength hb
      | FH_err => hb <> nil
      end
  | FP_skip hdr got =>
      Zlength hdr = ZSTD_SKIPPABLEHEADERSIZE /\ is_skippable_magic (le_field hdr 0 4) = true /\
      le_field hdr 4 4 + ZSTD_SKIPPABLEHEADERSIZE < 2 ^ 32 /\ 0 <= got <= le_field hdr 4 4 /\
      exists sk, fb = hdr ++ sk /\ Zlength sk = got
  | FP_zstd hdr z =>
      let h := zp_h z in
      let bsm := fh_blockSizeMax h in
      let ws := fh_windowSize h in
      get_frame_header hdr = FH_ok h /\ Zlength hdr = fh_headerSize h /\ fh_frameType h = 0 /\
      fh_dictID h = 0 /\
      exists outc last,
        blocks_pre bsm ws (zp_bl z) (zp_ts z) outc last /\
        fb = hdr ++ zp_bl z ++
             match zp_ph z with ZP_body bh => bh ++ zp_got z | _ => zp_got z end /\
        match zp_ph z with
        | ZP_bhdr =>
            last = false /\ zp_out z = outc /\ Zlength (zp_got z) < ZSTD_blockHeaderSize
        | ZP_body bh =>
            last = false /\ Zlength bh = ZSTD_blockHeaderSize /\
            exists c, cblock_size bh = Some c /\ 0 < c <= bsm /\ Zlength (zp_got z) < c /\
              zp_out z = (if bp_type (block_props_of bh) =? 0 then outc ++ zp_got z else outc)
        | ZP_ck =>
            last = true /\ zp_out z = outc /\ fcs_ok h outc /\ fh_checksumFlag h = 1 /\
            Zlength (zp_got z) < 4
        | ZP_end =>
            last = true /\ zp_out z = outc /\ fcs_ok h outc /\
            ((fh_checksumFlag h = 0 /\ zp_got z = nil) \/
             (fh_checksumFlag h = 1 /\ Zlength (zp_got z) = 4 /\
              le_field (zp_got z) 0 4 = xxh64 outc 0 mod 2 ^ 32))
        end
  end.

(* the stream agrees with the model: sin = the finished frames, then the current one; sout and the pending
   output pend are their content *)
Definition m_rel (sin sout: list Z) (fp: fprog) (pend: list Z) : Prop :=
  exists dsin fb recs,
    sin = dsin ++ fb /\ series_frames no_dict no_wlim dsin = (recs, TEnd) /\ cur_rel fb fp /\
    sout ++ pend = flat_map fr_content recs ++ fp_content fp.

(* no claim: every series that starts with sin stops at a frame the model does not decode *)
Definition dead (sin: list Z) : Prop :=
  forall s, is_prefix sin s -> snd (series_frames no_dict no_wlim s) = TUnk.

(* ---------- one unit of a Zstandard frame (ZSTD_decompressContinue, as the stream uses it) ---------- *)

(* the phase after a complete block *)
Definition next_phase (h: frame_header) (bh: list Z) : zphase :=
  if bp_last (block_props_of bh) =? 1 then (if fh_checksumFlag h =? 1 then ZP_ck else ZP_end) else ZP_bhdr.

Definition zp_with (z: zprog) (bl: list Z) (ts: dstate) (out: list Z) (ph: zphase) (got: list Z) : zprog :=
  {| zp_h := zp_h z; zp_bl := bl; zp_ts := ts; zp_out := out; zp_ph := ph; zp_got := got |}.

(* the progress after the unit u (cnt: the content zstd wrote, ts': the tables after it) *)
Definition zstep (z: zprog) (u cnt: list Z) (ts': dstate) : zprog :=
  match zp_ph z with
  | ZP_bhdr =>
      match cblock_size u with
      | Some c =>
          if c =? 0 then zp_with z (zp_bl z ++ u) (zp_ts z) (zp_out z) (next_phase (zp_h z) u) nil
          else zp_with z (zp_bl z) (zp_ts z) (zp_out z) (ZP_body u) nil
      | None => z
      end
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then
        let got' := zp_got z ++ u in
        if match cblock_size bh with Some c => Zlength got' =? c | None => false end
        then zp_with z (zp_bl z ++ bh ++ got') (zp_ts z) (zp_out z ++ u) (next_phase (zp_h z) bh) nil
        else zp_with z (zp_bl z) (zp_ts z) (zp_out z ++ u) (ZP_body bh) got'
      else zp_with z (zp_bl z ++ bh ++ u) ts' (zp_out z ++ cnt) (next_phase (zp_h z) bh) nil
  | ZP_ck => zp_with z (zp_bl z) (zp_ts z) (zp_out z) ZP_end u
  | ZP_end => z
  end.

(* the content zstd writes for the unit u, and the tables after it, on a success *)
Definition cnt_ok (z: zprog) (u cnt: list Z) (ts': dstate) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then cnt = u /\ ts' = zp_ts z
      else if bp_type bp =? 1 then cnt = repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)) /\ ts' = zp_ts z
      else bytes_ok cnt /\ Zlength cnt <= fh_blockSizeMax h /\
           match decode_block (zp_ts z) nil (zp_out z) u (fh_blockSizeMax h) (fh_windowSize h) with
           | Some (ts2, c2) => map (fun b => b mod 2 ^ 32) cnt = map (fun b => b mod 2 ^ 32) c2 /\ ts' = ts2
           | None => True
           end
  | _ => cnt = nil /\ ts' = zp_ts z
  end.

(* what zstd's content for the unit u is in any case (without the model) *)
Definition cnt_safe (z: zprog) (u cnt: list Z) (ts': dstate) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then cnt = u /\ ts' = zp_ts z
      else if bp_type bp =? 1 then
        cnt = repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)) /\ ts' = zp_ts z /\
        bp_origSize bp <= fh_blockSizeMax h
      else bytes_ok cnt /\ Zlength cnt <= fh_blockSizeMax h
  | _ => cnt = nil /\ ts' = zp_ts z
  end.

(* the model decodes the unit u (a compressed block), or u is not a compressed block *)
Definition cnt_model_some (z: zprog) (u: list Z) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      bp_type (block_props_of bh) = 2 ->
      decode_block (zp_ts z) nil (zp_out z) u (fh_blockSizeMax h) (fh_windowSize h) <> None
  | _ => True
  end.

(* why zstd may fail on the unit u at capacity cap (stated against the model) *)
Definition fcs_bad (h: frame_header) (out: list Z) : Prop :=
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ Zlength out <> fh_contentSize h.

Definition cont_err (fp: fprog) (u: list Z) (cap: Z) : Prop :=
  match fp with
  | FP_zstd _ z =>
      let h := zp_h z in
      let bsm := fh_blockSizeMax h in
      let out := zp_out z in
      match zp_ph z with
      | ZP_bhdr => match cblock_size u with None => True | Some c => c > bsm end
      | ZP_body bh =>
          let bp := block_props_of bh in
          let lastc o := bp_last bp = 1 /\ fcs_bad h o in
          if bp_type bp =? 0 then
            Zlength u > cap \/ (Some (Zlength (zp_got z ++ u)) = cblock_size bh /\ lastc (out ++ u))
          else if bp_type bp =? 1 then
            bp_origSize bp > cap \/ bp_origSize bp > bsm \/
            lastc (out ++ repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)))
          else
            match decode_block (zp_ts z) nil out u bsm (fh_windowSize h) with
            | None => True
            | Some (_, c2) => cap < Zlength c2 \/ lastc (out ++ c2)
            end
      | ZP_ck => le_field u 0 4 <> xxh64 out 0 mod 2 ^ 32
      | ZP_end => False
      end
  | _ => False
  end.

(* the unit zstd passes for the progress fp (srcSize, and whether src is read) *)
Definition unit_ok (fp: fprog) (n: Z) : Prop :=
  match fp with
  | FP_skip hdr got => got = 0 /\ n = le_field hdr 4 4
  | FP_zstd _ z =>
      match zp_ph z with
      | ZP_bhdr => zp_got z = nil /\ n = ZSTD_blockHeaderSize
      | ZP_body bh =>
          exists c, cblock_size bh = Some c /\
          if bp_type (block_props_of bh) =? 0 then 1 <= n <= c - Zlength (zp_got z)
          else zp_got z = nil /\ n = c
      | ZP_ck => zp_got z = nil /\ n = 4
      | ZP_end => False
      end
  | _ => False
  end.

Definition is_skip (fp: fprog) : bool := match fp with FP_skip _ _ => true | _ => false end.

(* the checks a success passed: the frame content size at the end of the last block, the checksum *)
Definition cont_checks (z: zprog) (u cnt: list Z) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      zp_ph (zstep z u cnt (zp_ts z)) <> ZP_body bh -> bp_last (block_props_of bh) = 1 ->
      (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/
       Zlength (zp_out z ++ cnt) mod 2 ^ 64 = fh_contentSize h)
  | ZP_ck => le_field u 0 4 = xxh64 (zp_out z) 0 mod 2 ^ 32
  | _ => True
  end.


(* ---------- shared by the model facts (StreamModelFacts) and their statements (StreamModelStmts) ---------- *)

Definition fdead (x: list Z) : Prop :=
  forall s, is_prefix x s -> snd (series_frames no_dict no_wlim s) = TUnk.

Definition fbad (x: list Z) : Prop :=
  forall s, is_prefix x s -> snd (series_frames no_dict stream_wlim s) <> TEnd.

Definition zp_set_got (z: zprog) (g: list Z) : zprog :=
  {| zp_h := zp_h z; zp_bl := zp_bl z; zp_ts := zp_ts z; zp_out := zp_out z; zp_ph := zp_ph z; zp_got := g |}.

Definition z_start (h: frame_header) : zprog :=
  {| zp_h := h; zp_bl := nil; zp_ts := dstate_init; zp_out := nil; zp_ph := ZP_bhdr; zp_got := nil |}.

Definition cap_room (z: zprog) (cap: Z) : Prop :=
  fh_blockSizeMax (zp_h z) <= cap \/
  (fh_contentSize (zp_h z) <> ZSTD_CONTENTSIZE_UNKNOWN /\ fh_contentSize (zp_h z) - Zlength (zp_out z) <= cap).

(* the content claim of a stream (stream_claims' first clause): what was delivered is a prefix of the
   content of every series that extends what was read *)
Definition content_ok (sin sout: list Z) : Prop :=
  forall s, is_prefix sin s ->
    (snd (series_frames no_dict no_wlim s) = TEnd \/ snd (series_frames no_dict no_wlim s) = TDetHdr) ->
    is_prefix sout (flat_map fr_content (fst (series_frames no_dict no_wlim s))).
