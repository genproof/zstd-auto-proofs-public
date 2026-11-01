(* FS3 streaming: the model side of ZSTD_decompressStream's invariant, API v3.  Plain Coq over the format model
   (model/Series.v, model/Params.v); the
   definitions the streaming proofs share.  v2's StreamModelDefs (src/proof/dec/FS/) generalised to

   - a streaming mode sm (smode): the parameters' model md (magicless format, ignored checksums, the
     Block_Maximum_Size cap), the dictionary selection sel and the dictionary before the first frame cur
     (Params.frame_dict / walk_m: each Zstandard frame uses sel of its Dictionary_ID, else the current one,
     and its dictionary becomes the current one), and the window limit wl (ZSTD_d_windowLogMax);
   - a Zstandard frame in progress (zprog) carries its dictionary (zp_dm: content = the history in front
     of the frame, entropy state = the tables before its first block), its effective Block_Maximum_Size
     (zp_bsm = min(header's, md_bmax)) and whether checksums are ignored (zp_ign);
   - the content zstd writes for a compressed block is stated with an explicit history H (cnt_ok, cont_err):
     the dictionary content, or nil once zstd's ring has wrapped (the dictionary is then out of zstd's
     reach; with the dictionary window rule (R1: dec_block true) the two agree once the output exceeds the window).

   The bytes a stream has read split into the finished frames dsin (the model decodes them, no window
   limit) and the bytes fb of the current frame; walk_cur gives the dictionary current after dsin. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.Huffman.
Require Import Zstd.proof.model.Refuse.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- the streaming mode ---------- *)

Definition ZSTD_WINDOWSIZE_ABSMIN : Z := 1024.   (* 1 << ZSTD_WINDOWLOG_ABSOLUTEMIN *)


Record smode := { sm_md : dmode; sm_sel : Z -> option dict_model; sm_cur : option dict_model; sm_wl : Z }.

Definition sm_mg (sm: smode) : bool := md_magicless (sm_md sm).

(* R2 (API v3.4, G-skip): with the dictionary window rule (buffered streaming) a skippable frame's header selects
   the DDict of its magic variant (zstd's ZSTD_DCtx_selectFrameDDict on fParams.dictID = the variant), else the
   current one stays (Params.walk_m); s: the frame's bytes (only its magic number is read) *)
Definition skip_cd (md: dmode) (sel: Z -> option dict_model) (s: list Z) (cur: option dict_model)
    : option dict_model :=
  if md_dwin md then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end else cur.

(* the dictionary current after the frames of s (walk_m's threading); meaningful when the walk ends at TEnd *)
Fixpoint walk_cur (fuel: nat) (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wlim: Z)
    (s: list Z) : option dict_model :=
  match fuel with
  | O => cur
  | S f =>
      let mg := md_magicless md in
      if Zlength s <? starting_len mg then cur else
      if negb mg && is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => cur
        | Some k => walk_cur f md sel (skip_cd md sel s cur) wlim (skipn (Z.to_nat k) s)
        end
      else
        match frame_dict mg sel cur s with
        | None => cur
        | Some d =>
            match decode_frame_m md d wlim s with
            | FOk _ k => walk_cur f md sel (Some d) wlim (skipn (Z.to_nat k) s)
            | _ => cur
            end
        end
  end.

Definition series_cur (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wlim: Z) (s: list Z)
    : option dict_model :=
  walk_cur (S (length s)) md sel cur wlim s.

(* a dictionary the model handles like zstd's bytes: byte content, Huffman tables of at most 256
   symbols *)
Definition dm_ok (dm: dict_model) : Prop :=
  bytes_ok (dm_content dm) /\ forall t, st_huf (dm_state dm) = Some t -> (length (Huffman.ht_weights t) <= 256)%nat.

(* ---------- one block of a frame (the body of Series.decode_blocks) ---------- *)

(* the block decoder of the model: with the dictionary window rule (R1, API v3.1 md_dwin: streaming) or Block.v's
   (one-shot) *)
Definition dec_block (dw: bool) : dstate -> list Z -> list Z -> list Z -> Z -> Z -> option (dstate * list Z) :=
  if dw then decode_block_w else decode_block.

(* the block at the start of s after the frame's output out (history hist in front of the frame): the new
   entropy state, the output, the bytes the block takes (header included), whether it is the last one *)
Definition block_res (dw: bool) (st: dstate) (hist: list Z) (s out: list Z) (bsm wsize: Z)
    : option (dstate * list Z * Z * bool) :=
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
          match dec_block dw st hist out body bsm wsize with
          | Some (st', content) => Some (st', out ++ content)
          | None => None
          end in
      match res with
      | None => None
      | Some (st', out') => Some (st', out', ZSTD_blockHeaderSize + c, bp_last bp =? 1)
      end
  end.

(* the complete blocks bl of a frame (history hist, effective Block_Maximum_Size bsm, Window_Size wsize,
   tables ts0 before the first block): the state and the output after them, and whether the last one ends
   the frame *)
Inductive blocks_pre (dw: bool) (hist: list Z) (bsm wsize: Z) (ts0: dstate) : list Z -> dstate -> list Z -> bool -> Prop :=
| BPre_nil : blocks_pre dw hist bsm wsize ts0 nil ts0 nil false
| BPre_snoc : forall bl ts out b ts' out' last,
    blocks_pre dw hist bsm wsize ts0 bl ts out false ->
    block_res dw ts hist b out bsm wsize = Some (ts', out', Zlength b, last) ->
    blocks_pre dw hist bsm wsize ts0 (bl ++ b) ts' out' last.

(* ---------- the progress of the current frame ---------- *)

Inductive zphase :=
| ZP_bhdr              (* at (or inside) a block header *)
| ZP_body (bh: list Z) (* inside the body of the block whose header is bh (3 bytes, body size > 0) *)
| ZP_ck                (* at (or inside) the Content_Checksum *)
| ZP_end.              (* the frame is complete *)

(* zstd's knowledge of a Zstandard frame: the header h, the frame's dictionary, the effective
   Block_Maximum_Size, whether checksums are ignored, the bytes of the complete blocks, the entropy state
   after them, the content decoded so far, the phase, and the bytes of the current unit read so far *)
Record zprog := {
  zp_h : frame_header; zp_dm : dict_model; zp_bsm : Z; zp_ign : bool;
  zp_bl : list Z; zp_ts : dstate; zp_out : list Z; zp_ph : zphase; zp_got : list Z }.

Definition zp_hist (z: zprog) : list Z := dm_content (zp_dm z).

Inductive fprog :=
| FP_none                              (* nothing of a frame (a stream's start) *)
| FP_hdr (hb: list Z)                  (* a frame header being loaded: its first bytes hb *)
| FP_skip (hdr: list Z) (got: Z)       (* a skippable frame: its 8 header bytes, got content bytes skipped *)
| FP_zstd (hdr: list Z) (z: zprog).    (* a Zstandard frame: its header bytes, the progress *)

Definition fp_content (fp: fprog) : list Z :=
  match fp with FP_zstd _ z => zp_out z | _ => nil end.

Definition fp_complete (fp: fprog) : bool :=
  match fp with
  | FP_skip hdr got => got =? le_field hdr 4 4
  | FP_zstd _ z => match zp_ph z with ZP_end => true | _ => false end
  | _ => false
  end.

Definition fcs_ok (h: frame_header) (out: list Z) : Prop :=
  fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out = fh_contentSize h.

(* zstd's own check of the content size (decodedSize, a U64, against Frame_Content_Size): modulo 2^64.  It differs
   from fcs_ok only for a frame of at least 2^64 bytes of content, which the model does not decode (FUnk) and does
   not refuse when complete either; such a frame stays alive until its checksum is read *)
Definition fcs_okm (h: frame_header) (out: list Z) : Prop :=
  fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength out mod 2 ^ 64 = fh_contentSize h.

(* a header loaded by zdss_loadHeader (format mg): incomplete, exactly complete, or rejected *)
Definition hdr_lenok (mg: bool) (hb: list Z) : Prop :=
  match get_frame_header_m mg hb with
  | FH_more k => Zlength hb < k
  | FH_ok h => fh_headerSize h = Zlength hb
  | FH_err => hb <> nil
  end.

(* the bytes fb of the current frame read so far, and what zstd knows of them, as the model reads them
   (md, sel; cd: the dictionary current before the frame) *)
Definition cur_rel (md: dmode) (sel: Z -> option dict_model) (cd: option dict_model) (fb: list Z) (fp: fprog)
    : Prop :=
  let mg := md_magicless md in
  match fp with
  | FP_none => fb = nil
  | FP_hdr hb => fb = hb /\ hdr_lenok mg hb
  | FP_skip hdr got =>
      mg = false /\
      Zlength hdr = ZSTD_SKIPPABLEHEADERSIZE /\ is_skippable_magic (le_field hdr 0 4) = true /\
      0 <= got <= le_field hdr 4 4 /\
      exists sk, fb = hdr ++ sk /\ Zlength sk = got
  | FP_zstd hdr z =>
      let h := zp_h z in
      let bsm := zp_bsm z in
      let ws := fh_windowSize h in
      get_frame_header_m mg hdr = FH_ok h /\ Zlength hdr = fh_headerSize h /\ fh_frameType h = 0 /\
      frame_dict mg sel cd hdr = Some (zp_dm z) /\
      (fh_dictID h = 0 \/ fh_dictID h = dm_id (zp_dm z)) /\
      bsm = Z.min (fh_blockSizeMax h) (md_bmax md) /\ zp_ign z = md_ignore md /\
      exists outc last,
        blocks_pre (md_dwin md) (zp_hist z) bsm ws (dm_state (zp_dm z)) (zp_bl z) (zp_ts z) outc last /\
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
            last = true /\ zp_out z = outc /\ fcs_okm h outc /\ fh_checksumFlag h = 1 /\
            Zlength (zp_got z) < 4
        | ZP_end =>
            last = true /\ zp_out z = outc /\ fcs_ok h outc /\
            ((fh_checksumFlag h = 0 /\ zp_got z = nil) \/
             (fh_checksumFlag h = 1 /\ Zlength (zp_got z) = 4 /\
              (zp_ign z = true \/ le_field (zp_got z) 0 4 = xxh64 outc 0 mod 2 ^ 32)))
        end
  end.

(* the stream agrees with the model: sin = the finished frames dsin, then the current one fb; cd the
   dictionary current after dsin; sout and the pending output pend are their content *)
Definition m_rel_cd (sm: smode) (sin sout: list Z) (fp: fprog) (pend: list Z) (cd: option dict_model) : Prop :=
  exists dsin fb recs,
    sin = dsin ++ fb /\ series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim dsin = (recs, TEnd) /\
    series_cur (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim dsin = cd /\
    cur_rel (sm_md sm) (sm_sel sm) cd fb fp /\
    sout ++ pend = flat_map fr_content recs ++ fp_content fp.

(* no byte series that starts with x ends refused (Refuse.series_refused_m, from the dictionary cd): x already
   contains a point where the model gives up without a refusal (a frame without its dictionary or with another
   Dictionary_ID, a compressed block zstd decodes and the model does not) *)
Definition nref (md: dmode) (sel: Z -> option dict_model) (cd: option dict_model) (x: list Z) : Prop :=
  forall s, bytes_ok s -> is_prefix x s -> ~ series_refused_m md sel cd no_wlim s.

(* no claim: every series that starts with sin stops at a frame the model does not decode, and none ends refused
   (a return of 0 then needs no claim: Refuse.stream_zero_ref) *)
Definition dead (sm: smode) (sin: list Z) : Prop :=
  ((forall s, is_prefix sin s -> snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s) = TUnk) /\
   nref (sm_md sm) (sm_sel sm) (sm_cur sm) sin)%type.

(* the dictionary current after the finished frames (cd) and the current one fp: the one of a Zstandard frame in
   progress, the one a skippable frame's header selected (R2, skip_cd) *)
Definition next_cd (sm: smode) (fp: fprog) (cd: option dict_model) : option dict_model :=
  match fp with
  | FP_zstd _ z => Some (zp_dm z)
  | FP_skip hdr _ => skip_cd (sm_md sm) (sm_sel sm) hdr cd
  | _ => cd
  end.

(* ---------- one unit of a Zstandard frame (ZSTD_decompressContinue, as the stream uses it) ---------- *)

Definition next_phase (h: frame_header) (bh: list Z) : zphase :=
  if bp_last (block_props_of bh) =? 1 then (if fh_checksumFlag h =? 1 then ZP_ck else ZP_end) else ZP_bhdr.

Definition zp_with (z: zprog) (bl: list Z) (ts: dstate) (out: list Z) (ph: zphase) (got: list Z) : zprog :=
  {| zp_h := zp_h z; zp_dm := zp_dm z; zp_bsm := zp_bsm z; zp_ign := zp_ign z;
     zp_bl := bl; zp_ts := ts; zp_out := out; zp_ph := ph; zp_got := got |}.

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

(* the content zstd writes for the unit u, and the tables after it, on a success; a compressed block is
   decoded behind the history H (what zstd still reaches of the dictionary: its content, or nil after a
   ring wrap) *)
Definition cnt_ok (z: zprog) (H: list Z) (u cnt: list Z) (ts': dstate) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then cnt = u /\ ts' = zp_ts z
      else if bp_type bp =? 1 then cnt = repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)) /\ ts' = zp_ts z
      else bytes_ok cnt /\ Zlength cnt <= zp_bsm z /\
           match decode_block (zp_ts z) H (zp_out z) u (zp_bsm z) (fh_windowSize h) with
           | Some (ts2, c2) => map (fun b => b mod 2 ^ 32) cnt = map (fun b => b mod 2 ^ 32) c2 /\ ts' = ts2
           | None => True
           end
  | _ => cnt = nil /\ ts' = zp_ts z
  end.

(* what zstd's content for the unit u is in any case (without the model) *)
Definition cnt_safe (z: zprog) (u cnt: list Z) (ts': dstate) : Prop :=
  match zp_ph z with
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then cnt = u /\ ts' = zp_ts z
      else if bp_type bp =? 1 then
        cnt = repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)) /\ ts' = zp_ts z /\
        bp_origSize bp <= zp_bsm z
      else bytes_ok cnt /\ Zlength cnt <= zp_bsm z
  | _ => cnt = nil /\ ts' = zp_ts z
  end.

(* the model (dw: with the dictionary window rule) decodes the unit u (a compressed block, behind the frame's
   dictionary), or u is not one *)
Definition cnt_model_some (dw: bool) (z: zprog) (u: list Z) : Prop :=
  match zp_ph z with
  | ZP_body bh =>
      bp_type (block_props_of bh) = 2 ->
      dec_block dw (zp_ts z) (zp_hist z) (zp_out z) u (zp_bsm z) (fh_windowSize (zp_h z)) <> None
  | _ => True
  end.

Definition fcs_bad (h: frame_header) (out: list Z) : Prop :=
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN /\ Zlength out <> fh_contentSize h.

(* why zstd may fail on the unit u at capacity cap (stated against the model, history H) *)
Definition cont_err (fp: fprog) (H: list Z) (u: list Z) (cap: Z) : Prop :=
  match fp with
  | FP_zstd _ z =>
      let h := zp_h z in
      let bsm := zp_bsm z in
      let out := zp_out z in
      match zp_ph z with
      | ZP_bhdr =>
          (* F6: an empty last block ends the frame, with the content size check of a non-empty one *)
          match cblock_size u with
          | None => True
          | Some c => c > bsm \/ (c = 0 /\ bp_last (block_props_of u) = 1 /\ fcs_bad h out)
          end
      | ZP_body bh =>
          let bp := block_props_of bh in
          let lastc o := bp_last bp = 1 /\ fcs_bad h o in
          if bp_type bp =? 0 then
            Zlength u > cap \/ (Some (Zlength (zp_got z ++ u)) = cblock_size bh /\ lastc (out ++ u))
          else if bp_type bp =? 1 then
            bp_origSize bp > cap \/ bp_origSize bp > bsm \/
            lastc (out ++ repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)))
          else
            match decode_block (zp_ts z) H out u bsm (fh_windowSize h) with
            | None => True
            | Some (_, c2) => cap < Zlength c2 \/ lastc (out ++ c2)
            end
      | ZP_ck => zp_ign z = false /\ le_field u 0 4 <> xxh64 out 0 mod 2 ^ 32
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

(* the checks a success passed: at a block header, a block type other than Reserved, a size within the effective
   Block_Maximum_Size, and for an empty last block the frame content size (F6); the frame content size at the end
   of the last block; the checksum (unless ignored) *)
Definition cont_checks (z: zprog) (u cnt: list Z) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_bhdr =>
      exists c, cblock_size u = Some c /\ c <= zp_bsm z /\
        (c = 0 -> bp_last (block_props_of u) = 1 -> fcs_okm h (zp_out z))
  | ZP_body bh =>
      zp_ph (zstep z u cnt (zp_ts z)) <> ZP_body bh -> bp_last (block_props_of bh) = 1 ->
      (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/
       Zlength (zp_out z ++ cnt) mod 2 ^ 64 = fh_contentSize h)
  | ZP_ck => zp_ign z = true \/ le_field u 0 4 = xxh64 (zp_out z) 0 mod 2 ^ 32
  | _ => True
  end.

(* ---------- shared by the model facts and their statements ---------- *)

(* the frame-local forms (x: bytes of the current frame, cd: the dictionary current before it) *)
Definition fdead (sm: smode) (cd: option dict_model) (x: list Z) : Prop :=
  ((forall s, is_prefix x s -> snd (series_frames_m (sm_md sm) (sm_sel sm) cd no_wlim s) = TUnk) /\
   nref (sm_md sm) (sm_sel sm) cd x)%type.

Definition fbad (sm: smode) (cd: option dict_model) (x: list Z) : Prop :=
  forall s, is_prefix x s -> snd (series_frames_m (sm_md sm) (sm_sel sm) cd (sm_wl sm) s) <> TEnd.

Definition zp_set_got (z: zprog) (g: list Z) : zprog := zp_with z (zp_bl z) (zp_ts z) (zp_out z) (zp_ph z) g.

(* a Zstandard frame after its header h, decoded with the dictionary dm, effective bsm, checksum policy ign *)
Definition z_start (h: frame_header) (dm: dict_model) (bsm: Z) (ign: bool) : zprog :=
  {| zp_h := h; zp_dm := dm; zp_bsm := bsm; zp_ign := ign;
     zp_bl := nil; zp_ts := dm_state dm; zp_out := nil; zp_ph := ZP_bhdr; zp_got := nil |}.

Definition cap_room (z: zprog) (cap: Z) : Prop :=
  zp_bsm z <= cap \/
  (fh_contentSize (zp_h z) <> ZSTD_CONTENTSIZE_UNKNOWN /\ fh_contentSize (zp_h z) - Zlength (zp_out z) <= cap).

(* the parameters' model without the dictionary window rule (one-shot decoding: ZSTD_decompress_usingDDict's
   claims, the streaming shortcut) *)
Definition md_len (md: dmode) : dmode :=
  {| md_magicless := md_magicless md; md_ignore := md_ignore md; md_bmax := md_bmax md; md_dwin := false |}.

(* the content claim of a stream (stream_claims_m's first clause) *)
Definition content_ok (sm: smode) (sin sout: list Z) : Prop :=
  forall s, is_prefix sin s ->
    let t0 := snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s) in
    (t0 = TEnd \/ t0 = TDetHdr) ->
    is_prefix sout (flat_map fr_content (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s))).
