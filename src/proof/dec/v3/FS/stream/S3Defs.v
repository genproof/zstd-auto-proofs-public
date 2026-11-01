(* FS3 streaming: the stream relation SR3 (FSRep3.srel3) of ZSTD_decompressStream, API v3.  The
   definitions every streaming proof shares.  v2's StreamDefs generalised to the parameters, a dictionary per frame and
   the DDict set:

   SR3 gv st k = exists sv, c_rel gv st k sv /\ bytes_ok ss_in /\ hostage accounting /\
              (dead sm ss_in \/ exists cd, m_rel_cd sm ss_in ss_out fp pend cd /\ cur_dict_ok st k (next_cd sm fp cd)
                                           /\ hist_ok k sv)
   with sm = sm_of st (dmode_w (dmode_of dc_par): the dictionary window rule; st_sel; dp_wmax).
   - sview: + sv_dd, the DDict the current frame began with (ZSTD_decompressBegin_usingDDict) and its content
     buffer; the tables are TABS gv p (option_map fst sv_dd) ts;
   - hlay: + HL_dict (the DDict content referenced as the prefix, before the first write of the frame);
     HL_stuck remembers it; the first segment's extDict is the DDict content (ExtSep), until a ring wrap;
   - cur_dict_ok: the DDict zstd will begin the next frame with (getDDict after the selection) is the one the
     model's current dictionary cd describes. *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Require Export Zstd.proof.dec.v3.FS.stream.S3XRel.
Require Export Zstd.proof.dec.v3.FS.stream.S3ModelDefs.
Require Export Zstd.proof.zstd.NullBuf.
Local Open Scope logic.

Section CM_S3Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the streaming mode of a context *)
Definition sm_of (st: dctx_st) : smode :=
  {| sm_md := dmode_w (dmode_of (dc_par st)); sm_sel := fst (st_sel st); sm_cur := snd (st_sel st);
     sm_wl := dp_wmax (dc_par st) |}.

(* the header zstd keeps in fParams once a frame starts: windowSize raised to 1 KiB, blockSizeMax capped
   (bsm: min(header's, maxBlockSizeParam)) *)
Definition fh_adj (h: frame_header) (bsm: Z) : frame_header :=
  {| fh_contentSize := fh_contentSize h; fh_windowSize := Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN;
     fh_blockSizeMax := bsm; fh_frameType := fh_frameType h; fh_headerSize := fh_headerSize h;
     fh_dictID := fh_dictID h; fh_checksumFlag := fh_checksumFlag h |}.

(* the output ring's size for a frame (ZSTD_decodingBufferSize_internal with zstd's fParams) *)
Definition ring_needed (h: frame_header) (bsm: Z) : Z :=
  let ws := Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN in
  let bs := Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm in
  Z.min (fh_contentSize h) (ws + bs * 2 + WILDCOPY_OVERLENGTH * 2).

(* ---------- the history layout (the frame fields previousDstEnd .. dictEnd, gpDictCopy) ---------- *)

(* the DDict content as a prefix: its buffer eb, its cells ec, gpDictCopy gp (1: zstd's own copy) *)
Definition dpre : Type := (val * list val * Z)%type.

(* HL_none: no dictionary, no segment (fs_begin3: all NULL);
   HL_dict eb ec gp: the DDict content [eb, eb + |ec|) is the prefix (ZSTD_decompressBegin_usingDDict), no
   segment yet;
   HL_stuck base pe od: no segment, but a block of 0 bytes written at capacity 0 set previousDstEnd = base + pe
   (the capacity stays 0 for the frame); od the dictionary prefix still referenced;
   HL_seg base ps pe e: the current segment [base + ps, base + pe) and the extDict e (ExtNone; ExtIn in the
   same array, after a ring wrap; ExtSep, the DDict content, before it) *)
Inductive hlay :=
| HL_none
| HL_dict (eb: val) (ec: list val) (gp: Z)
| HL_stuck (base: val) (pe: Z) (od: option dpre)
| HL_seg (base: val) (ps pe: Z) (e: ext_seg).

(* the arithmetic of DecIface.layout_ok for a segment starting at ps in an array of N cells *)
Definition layout_ok_seg (ps: Z) (e: ext_seg) (N: Z) : Prop :=
  0 <= ps /\ 0 <= ext_len e <= 2 ^ 63 - 1 /\
  match e with
  | ExtNone => True
  | ExtIn e1 elen => 0 <= e1 - elen /\ e1 <= N
  | ExtSep sh eb en ec e1 elen =>
      readable_share sh /\ Zlength ec = en /\ 0 <= e1 - elen /\ e1 <= en /\ en <= 2 ^ 63 - 1
  end.

Definition pre_fields (fs: fstate) (od: option dpre) : Prop :=
  match od with
  | None =>
      fs_gpDictCopy fs = Vint (Int.repr 0) /\
      fs_prefixStart fs = nullval /\ fs_virtualStart fs = nullval /\ fs_dictEnd fs = nullval
  | Some (eb, ec, gp) =>
      isptr eb /\ fs_gpDictCopy fs = Vint (Int.repr gp) /\
      fs_prefixStart fs = eb /\ fs_virtualStart fs = eb /\ fs_dictEnd fs = offset_val (Zlength ec) eb
  end.

Definition lay_fields (fs: fstate) (l: hlay) : Prop :=
  match l with
  | HL_none => pre_fields fs None /\ fs_previousDstEnd fs = nullval
  | HL_dict eb ec gp =>
      pre_fields fs (Some (eb, ec, gp)) /\ fs_previousDstEnd fs = offset_val (Zlength ec) eb
  | HL_stuck base pe od =>
      (* the block that left previousDstEnd at dst + 0 also cleared gpDictCopy *)
      isptr base /\ 0 <= pe /\ fs_previousDstEnd fs = offset_val pe base /\
      pre_fields fs (match od with Some (eb, ec, _) => Some (eb, ec, 0) | None => None end)
  | HL_seg base ps pe e =>
      fs_gpDictCopy fs = Vint (Int.repr 0) /\
      isptr base /\ 0 <= ps <= pe /\
      fs_previousDstEnd fs = offset_val pe base /\ fs_prefixStart fs = offset_val ps base /\
      fs_virtualStart fs = offset_val (ps - ext_len e) base /\
      match e with
      | ExtNone => fs_dictEnd fs = nullval
      | ExtIn e1 elen => fs_dictEnd fs = offset_val e1 base /\ 0 <= e1 - elen
      | ExtSep _ eb _ _ e1 elen => fs_dictEnd fs = offset_val e1 eb /\ 0 <= e1 - elen
      end
  end.

(* the extDict of the DDict content (cells ec at eb) *)
Definition ext_of_dict (eb: val) (ec: list val) : ext_seg :=
  ExtSep Ews eb (Zlength ec) ec (Zlength ec) (Zlength ec).

(* the room of the extDict in buffered mode (after a wrap: the whole old segment [0, e1), far enough from the
   writes of a block at the segment's end, and frame output); no content without a segment *)
Definition lay_room (l: hlay) (N: Z) (out: list Z) (wsize bsm: Z) : Prop :=
  match l with
  | HL_seg _ ps pe e =>
      match e with
      | ExtNone => True
      | ExtIn e1 elen => elen = e1 /\ ps = 0 /\ wsize + bsm + WILDCOPY_OVERLENGTH <= e1 <= N /\
                         e1 <= Zlength out
      | ExtSep _ _ _ _ _ _ => ps = 0
      end
  | _ => out = nil
  end.

(* the layout's dictionary is the frame's DDict dd (x, its content buffer) *)
Definition dd_pre (dd: option (ddx * val)) (p: dpre) : Prop :=
  let '(eb, ec, gp) := p in
  exists x, dd = Some (x, eb) /\ ec = zbytes (dx_bytes x) /\ gp = (if ddx_copied x then 1 else 0) /\
    (* ddict_struct's facts; the content is at a pointer (not the DDict without content) *)
    bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\ isptr eb.

(* the frame's DDict brings no dictionary content: none, or the DDict without content (ZSTD_createDDict(NULL, 0):
   content NULL, no bytes), with which zstd begins a frame as with no dictionary (only its tables are the DDict's) *)
Definition dd_nodict (dd: option (ddx * val)) : Prop :=
  match dd with
  | None => True
  | Some (x, buf) => buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil
  end.

Definition lay_dd (l: hlay) (dd: option (ddx * val)) : Prop :=
  match l with
  | HL_none => dd_nodict dd
  | HL_dict eb ec gp => dd_pre dd (eb, ec, gp)
  | HL_stuck _ _ od => match od with None => dd_nodict dd | Some p => dd_pre dd p end
  | HL_seg _ _ _ e =>
      match e with
      | ExtNone => dd_nodict dd
      | ExtIn _ _ => True
      | ExtSep sh eb en ec e1 elen =>
          sh = Ews /\ en = Zlength ec /\ e1 = en /\ elen = en /\ exists gp, dd_pre dd (eb, ec, gp)
      end
  end.

(* ---------- the frame fields of a frame in progress ---------- *)

Definition phase_fields (fs: fstate) (z: zprog) : Prop :=
  match zp_ph z with
  | ZP_bhdr =>
      fs_stage fs = Vint (Int.repr ds_decodeBlockHeader) /\
      fs_expected fs = Vlong (Int64.repr ZSTD_blockHeaderSize)
  | ZP_body bh =>
      let bp := block_props_of bh in
      exists c, cblock_size bh = Some c /\
      fs_stage fs = Vint (Int.repr (if bp_last bp =? 1 then ds_decompressLastBlock else ds_decompressBlock)) /\
      fs_bType fs = Vint (Int.repr (bp_type bp)) /\ fs_rleSize fs = Vlong (Int64.repr (bp_origSize bp)) /\
      fs_expected fs = Vlong (Int64.repr (if bp_type bp =? 0 then c - Zlength (zp_got z) else c))
  | ZP_ck =>
      fs_stage fs = Vint (Int.repr ds_checkChecksum) /\ fs_expected fs = Vlong (Int64.repr 4)
  | ZP_end =>
      fs_stage fs = Vint (Int.repr ds_getFrameHeaderSize) /\ fs_expected fs = Vlong (Int64.repr 0)
  end.

(* the dictionary model of the frame's DDict (none: no dictionary) *)
Definition dd_model (dd: option (ddx * val)) (dm: dict_model) : Prop :=
  match dd with None => dm = no_dict | Some (x, _) => ddx_model x = Some dm end.

Definition dd_ox (dd: option (ddx * val)) : option ddx := option_map fst dd.

(* a DDict without content has the model of no dictionary *)
Lemma dd_nodict_model : forall dd dm, dd_nodict dd -> dd_model dd dm -> dm = no_dict.
Proof.
intros [[x buf]|] dm Hn Hm; cbn in *; [|exact Hm].
destruct Hn as (_ & _ & Hb). unfold ddx_model in Hm. rewrite Hb in Hm.
destruct (dx_raw x); inversion Hm; reflexivity.
Qed.

Lemma dd_nodict_model_ok : forall dd, dd_nodict dd -> dd_model dd no_dict.
Proof.
intros [[x buf]|] Hn; cbn in *; [|reflexivity].
destruct Hn as (_ & _ & Hb). unfold ddx_model. rewrite Hb. destruct (dx_raw x); reflexivity.
Qed.

(* zstd's frame fields and tables for the progress fp (after ZSTD_decompressBegin_usingDDict with dd and the
   header), the layout l.  The tables' entropy state is the model's (zp_ts); the type of the Huffman table and
   litExtraBuffer's bytes (DecRep.tstate) are not tracked here. *)
Definition c_frame (fs: fstate) (tabs: tabs3) (fp: fprog) (l: hlay) (dd: option (ddx * val)) : Prop :=
  fs_isFrameDecompression fs = Vint (Int.repr 1) /\
  (fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1)) /\
  (exists pcs, fs_processedCSize fs = Vlong (Int64.repr pcs)) /\
  lay_fields fs l /\ lay_dd l dd /\
  match fp with
  | FP_skip hdr got =>
      (l = HL_none \/ exists eb ec gp, l = HL_dict eb ec gp) /\ (exists ts, tabs = TInit (dd_ox dd) ts) /\
      (exists h, get_frame_header hdr = FH_ok h /\ fh_frameType h = 1 /\
                 fs_fParams fs = fh_val (fh_adj h (fh_blockSizeMax h))) /\
      0 <= got <= le_field hdr 4 4 /\ le_field hdr 4 4 < 2 ^ 32 /\
      (if got =? le_field hdr 4 4
       then (fs_stage fs = Vint (Int.repr ds_getFrameHeaderSize) \/ fs_stage fs = Vint (Int.repr ds_skipFrame)) /\
            fs_expected fs = Vlong (Int64.repr 0)
       else fs_stage fs = Vint (Int.repr ds_skipFrame) /\
            fs_expected fs = Vlong (Int64.repr (le_field hdr 4 4)))
  | FP_zstd hdr z =>
      let h := zp_h z in
      let v := andb (fh_checksumFlag h =? 1) (negb (zp_ign z)) in
      fh_frameType h = 0 /\ fs_fParams fs = fh_val (fh_adj h (zp_bsm z)) /\
      0 <= zp_bsm z <= fh_blockSizeMax h /\ fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX /\
      0 <= fh_windowSize h /\ Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN <= 2 ^ 31 /\
      0 <= fh_contentSize h < 2 ^ 64 /\
      (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
      dd_model dd (zp_dm z) /\
      (exists ts, tabs = TInit (dd_ox dd) ts /\ ts_d ts = zp_ts z) /\
      phase_fields fs z /\
      fs_decodedSize fs = Vlong (Int64.repr (Zlength (zp_out z))) /\
      fs_validateChecksum fs = Vint (Int.repr (if v then 1 else 0)) /\
      (v = true -> fs_xxh fs = Some (zp_out z)) /\
      bytes_ok (zp_out z) /\
      match zp_ph z with
      | ZP_bhdr => Zlength (zp_got z) < ZSTD_blockHeaderSize
      | ZP_body bh =>
          Zlength bh = ZSTD_blockHeaderSize /\ bytes_ok bh /\
          exists c, cblock_size bh = Some c /\ 0 < c <= zp_bsm z /\ Zlength (zp_got z) < c /\
                    bp_type (block_props_of bh) <> 3
      | ZP_ck => Zlength (zp_got z) < 4 /\ fh_checksumFlag h = 1
      | ZP_end => True
      end /\ bytes_ok (zp_got z)
  | _ => False
  end.

(* the tables of a Zstandard frame in progress: in the frame's DDict, with the model's entropy state *)
Lemma c_frame_ts (fs: fstate) (ox: option ddx) (ts: tstate) (hdr: list Z) (z: zprog) (l: hlay)
    (dd: option (ddx * val)) :
  c_frame fs (TInit ox ts) (FP_zstd hdr z) l dd -> ox = dd_ox dd /\ ts_d ts = zp_ts z.
Proof.
  intros H. destruct H as (_ & _ & _ & _ & _ & H). destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (ts0 & E & Et) & _).
  injection E as -> ->. split; [reflexivity | exact Et].
Qed.

(* ---------- the abstract view of a stream and the concrete relation ---------- *)

Record sview := {
  sv_fp : fprog;                 (* the progress of the current frame *)
  sv_pend : list Z;              (* buffered mode: the output decoded, not yet flushed ([outStart, outEnd)) *)
  sv_ahead : list Z;             (* the hostage byte zstd read but does not report yet ([] or [b]) *)
  sv_lay : hlay;                 (* the history layout of the current frame *)
  sv_dd : option (ddx * val)     (* the DDict the current frame began with, and its content buffer *)
}.

Definition fp_bsm (fp: fprog) : Z := match fp with FP_zstd _ z => zp_bsm z | _ => 0 end.
Definition fp_ws (fp: fprog) : Z := match fp with FP_zstd _ z => fh_windowSize (zp_h z) | _ => 0 end.
Definition fp_fcs (fp: fprog) : Z :=
  match fp with
  | FP_zstd _ z => fh_contentSize (zp_h z)
  | FP_skip hdr _ => le_field hdr 4 4
  | _ => 0
  end.

Definition fp_loaded (fp: fprog) : list Z :=
  match fp with FP_zstd _ z => zp_got z | _ => nil end.
Definition fp_inpos (fp: fprog) : Z :=
  match fp with FP_zstd _ z => Zlength (zp_got z) | FP_skip _ got => got | _ => 0 end.

Definition fp_rawbody (fp: fprog) : bool :=
  match fp with
  | FP_zstd _ z => match zp_ph z with ZP_body bh => bp_type (block_props_of bh) =? 0 | _ => false end
  | _ => false
  end.

(* the history zstd still reaches for a compressed block of the frame z with the extDict e: the dictionary
   content, except after a ring wrap (ExtIn) *)
Definition hist_for (e: ext_seg) (z: zprog) : list Z :=
  match e with ExtIn _ _ => nil | _ => zp_hist z end.

Definition fp_hist (fp: fprog) (l: hlay) : list Z :=
  match fp, l with
  | FP_zstd _ z, HL_seg _ _ _ e => hist_for e z
  | FP_zstd _ z, _ => zp_hist z
  | _, _ => nil
  end.

(* the stream buffer of a frame in progress: [inBuff | outBuff], the history layout, the pending output
   and the next write position outStart *)
Definition c_ring (stable: bool) (obuf: option (val * Z)) (sout: list Z) (s: sfields) (fp: fprog) (pend: list Z)
    (l: hlay) : Prop :=
  let bsm := fp_bsm fp in
  sf_inBuff s <> nullval /\ isptr (sf_inBuff s) /\ Z.max bsm 4 <= sf_inSize s /\
  exists ostart oend,
    sf_outStart s = vlong ostart /\ sf_outEnd s = vlong oend /\ 0 <= ostart <= oend /\
    if stable then
      ostart = 0 /\ oend = 0 /\ pend = nil /\
      exists ob osz, obuf = Some (ob, osz) /\
      match l with
      | HL_none => fp_content fp = nil
      | HL_dict _ _ _ => fp_content fp = nil
      | HL_stuck base pe _ => base = ob /\ fp_content fp = nil /\ pe = Zlength sout /\ pe = osz
      | HL_seg base ps pe e =>
          base = ob /\ (match e with ExtIn _ _ => False | _ => True end) /\
          pe = Zlength sout /\ ps = pe - Zlength (fp_content fp) /\
          sublist ps pe sout = fp_content fp
      end
    else
      let ocells := sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s) in
      oend <= sf_outSize s /\
      sublist ostart oend ocells = zbytes pend /\ Zlength pend <= bsm /\
      (match fp with FP_zstd _ z => sf_outSize s >= ring_needed (zp_h z) (zp_bsm z) | _ => True end) /\
      match l with
      | HL_none => fp_content fp = nil /\ ostart = 0 /\ oend = 0
      | HL_dict _ _ _ => fp_content fp = nil /\ ostart = 0 /\ oend = 0
      | HL_stuck base pe _ => base = sf_outBuff s /\ fp_content fp = nil /\ pe = 0 /\ ostart = 0 /\ oend = 0 /\
                              sf_outSize s = 0
      | HL_seg base ps pe e =>
          base = sf_outBuff s /\ ps = 0 /\ pe <= sf_outSize s /\
          (* the segment holds frame output only *)
          pe <= Zlength (fp_content fp) /\
          lay_room l (sf_outSize s) (fp_content fp) (fp_ws fp) bsm /\
          (* the history cells (segment and extDict) are bytes, on any input *)
          hist_def ocells pe ps e /\
          (* pend is the end of the frame's content *)
          (exists pre, fp_content fp = pre ++ pend) /\
          (* the pending output ends at the segment's end, or the ring restarts at 0 (nothing pending) *)
          (oend = pe \/
           (ostart = 0 /\ oend = 0 /\ pend = nil /\ sf_outSize s < fp_fcs fp /\ sf_outSize s < pe + bsm)) /\
          (* no wrap when the ring holds the whole frame *)
          (fp_fcs fp <= sf_outSize s -> (match e with ExtIn _ _ => False | _ => True end) /\
                                        pe = Zlength (fp_content fp)) /\
          (* room for the next block at outStart (once flushed) *)
          (ostart = oend -> ostart + bsm <= sf_outSize s \/ fp_fcs fp <= sf_outSize s)
      end.

(* the C state of a stream (stable mode: its output buffer obuf and the delivered bytes sout), as the view sv
   says; also within a call (sout: delivered so far) *)
Definition c_core (stable: bool) (obuf: option (val * Z)) (sout: list Z) (k: cst3) (sv: sview) : Prop :=
  let s := c3_s k in
  let mg := dp_fmt (c3_par k) =? 1 in
  (sf_stage s = zdss_init /\ sv_ahead sv = nil \/
   sf_hostage s = Vint (Int.repr 0) /\ sv_ahead sv = nil \/
   sf_hostage s = Vint (Int.repr 1) /\ stable = false /\ fp_complete (sv_fp sv) = true /\
     Zlength (sv_ahead sv) = 1 /\ bytes_ok (sv_ahead sv) /\
     (sf_stage s = zdss_init \/ sf_stage s = zdss_read \/ sf_stage s = zdss_flush)) /\
  (fs_ddictIsCold (c3_fs k) = Vint (Int.repr 0) \/ fs_ddictIsCold (c3_fs k) = Vint (Int.repr 1)) /\
  sf_inSize s + sf_outSize s <= 2 ^ 32 /\
  if sf_stage s =? zdss_init then
    (sv_fp sv = FP_none \/ fp_complete (sv_fp sv) = true) /\ sv_pend sv = nil
  else if sf_stage s =? zdss_loadHeader then
    sv_pend sv = nil /\ sf_hostage s = Vint (Int.repr 0) /\
    sf_inPos s = vlong 0 /\ sf_outStart s = vlong 0 /\ sf_outEnd s = vlong 0 /\
    exists hb, sv_fp sv = FP_hdr hb /\ Zlength hb <= 18 /\ bytes_ok hb /\
      sf_lhSize s = vlong (Zlength hb) /\ sublist 0 (Zlength hb) (sf_hbuf s) = zbytes hb /\
      hdr_lenok mg hb
  else
    (sf_stage s = zdss_read \/ sf_stage s = zdss_load \/ sf_stage s = zdss_flush) /\
    c_frame (c3_fs k) (c3_tabs k) (sv_fp sv) (sv_lay sv) (sv_dd sv) /\
    c_ring stable obuf sout s (sv_fp sv) (sv_pend sv) (sv_lay sv) /\
    (stable = true -> sf_stage s <> zdss_flush) /\
    (sf_stage s = zdss_load ->
       sv_pend sv = nil /\ fp_complete (sv_fp sv) = false /\ fp_rawbody (sv_fp sv) = false /\
       sf_outStart s = sf_outEnd s /\
       sf_inPos s = vlong (fp_inpos (sv_fp sv)) /\
       sublist 0 (Zlength (fp_loaded (sv_fp sv))) (sf_ring s) = zbytes (fp_loaded (sv_fp sv))) /\
    (sf_stage s <> zdss_load ->
       sf_inPos s = vlong 0 /\
       (fp_rawbody (sv_fp sv) = true \/ fp_loaded (sv_fp sv) = nil \/ fp_complete (sv_fp sv) = true) /\
       match sv_fp sv with FP_skip _ got => got = 0 \/ fp_complete (sv_fp sv) = true | _ => True end) /\
    (sf_stage s = zdss_read -> sv_pend sv = nil /\ sf_outStart s = sf_outEnd s).

(* the caller's DDicts a stream may use (Spec_api6 dict_res / set_res): a member of the set, or the context's
   dictionary when it is a DDict *)
Definition dd_caller (st: dctx_st) (q: val) (dd: ddict_st) : Prop :=
  In (q, dd) (dc_set st) \/
  (exists dr, dc_dict st = Some dr /\ dr_src dr = DSDDict q dd).

(* the DDict a frame began with: the context's local DDict, or a caller's one, as its DD3_of pins it (API v3.1
   dd_buf / dd_ld, FSRep3.dd_x) *)
Definition dd_src (st: dctx_st) (k: cst3) (x: ddx) (buf: val) : Prop :=
  (df_local (c3_dict k) = dx_q x /\ dx_q x <> nullval /\ ddx_copied x = true /\
   df_lx (c3_dict k) = Some (x, buf)) \/
  (exists dd, dd_caller st (dx_q x) dd /\ x = dd_x (dx_q x) dd /\ buf = dd_buf dd).

(* in the frame stages, the frame's DDict is one of those *)
Definition sv_dd_ok (st: dctx_st) (k: cst3) (sv: sview) : Prop :=
  zdss_read <= sf_stage (c3_s k) -> forall x buf, sv_dd sv = Some (x, buf) -> dd_src st k x buf.

(* the base zstd computes with for a recorded output buffer (F9: ZSTD_emptyBuffer for NULL) *)
Definition obuf_base (gv: globals) (o: option (val * Z)) : option (val * Z) :=
  match o with Some (ob, osz) => Some (nbase gv ob, osz) | None => None end.

(* SR's concrete part: the no-progress count (at most the abstract one), the recorded stable buffer (the history of
   the frame lies at its base) *)
Definition c_rel (gv: globals) (st: dctx_st) (k: cst3) (sv: sview) : Prop :=
  let ss := dc_ss st in
  let s := c3_s k in
  0 <= ss_stall ss /\ 0 <= sf_nfp s <= ZSTD_NO_FORWARD_PROGRESS_MAX /\
  ((sf_nfp s <= ss_stall ss /\ sf_nfp s < ZSTD_NO_FORWARD_PROGRESS_MAX) \/
   sf_stage s = zdss_init \/
   (sf_stage s = zdss_loadHeader /\ exists hb k0, sv_fp sv = FP_hdr hb /\
      get_frame_header_m (dp_fmt (c3_par k) =? 1) hb = FH_more k0)) /\
  (sf_stage s = zdss_flush -> fp_complete (sv_fp sv) = true -> sv_pend sv <> nil ->
     sf_hostage s = Vint (Int.repr 1)) /\
  (dc_stable st = true -> sf_stage s <> zdss_init ->
     exists ob osz, ss_obuf ss = Some (ob, osz) /\
       sf_expOut s = (ob, (vlong osz, vlong (Zlength (ss_out ss))))) /\
  (sf_stage s <= zdss_loadHeader -> sv_ahead sv = nil) /\
  sv_dd_ok st k sv /\
  c_core (dc_stable st) (obuf_base gv (ss_obuf ss)) (ss_out ss) k sv.

(* the history zstd keeps in its ring (buffered mode) is the model's (the dictionary content until a wrap,
   then the frame output only), as far as the window reaches (needed only while the model agrees) *)
Definition hist_ok (stable: bool) (k: cst3) (sv: sview) : Prop :=
  let s := c3_s k in
  stable = false -> sf_stage s <> zdss_init -> sf_stage s <> zdss_loadHeader ->
  match sv_lay sv with
  | HL_seg _ ps pe e =>
      hist_view (sublist (sf_inSize s) (sf_inSize s + sf_outSize s) (sf_ring s)) pe ps e
        (fp_hist (sv_fp sv) (sv_lay sv)) (fp_content (sv_fp sv)) (fp_ws (sv_fp sv))
  | _ => True
  end.

(* the DDict zstd begins the next frame with, when the selection does not pick another (no set: the context's
   dictionary; a set: its current DDict, a member) is the model's current dictionary cd; with a set, the
   dictID left in fParams (which loadHeader probes again before the next header is complete) selects nothing
   else *)
Definition cur_dict_ok (st: dctx_st) (k: cst3) (cd: option dict_model) : Prop :=
  forall dm, cd = Some dm ->
    (dc_set st = nil /\ dictref_model (dc_dict st) = Some dm) \/
    (dc_set st <> nil /\ df_uses (c3_dict k) = -1 /\
     (exists dd, In (df_ddict (c3_dict k), dd) (dc_set st) /\ dict_auto (dd_bytes dd) = Some dm) /\
     (exists id, fp_dictID (fs_fParams (c3_fs k)) = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
        (set_find (dc_set st) id = nullval \/ set_find (dc_set st) id = df_ddict (c3_dict k)))).

(* the model side of a live stream: dead, or the model agrees (with the dictionary and the ring history) *)
Definition alive_ok (st: dctx_st) (k: cst3) (sv: sview) (sin sout: list Z) : Prop :=
  dead (sm_of st) sin \/
  (exists cd, m_rel_cd (sm_of st) sin sout (sv_fp sv) (sv_pend sv) cd /\
     cur_dict_ok st k (next_cd (sm_of st) (sv_fp sv) cd) /\ hist_ok (dc_stable st) k sv).

(* the stream relation: a running stream (SR3_run), and the exact relation (S3XRel.xrel3) *)
Definition SR3_run (gv: globals) (st: dctx_st) (k: cst3) : Prop :=
    exists sv: sview, c_rel gv st k sv /\ bytes_ok (ss_in (dc_ss st)) /\
      ss_ahead (dc_ss st) = Zlength (sv_ahead sv) /\
      (exists sin0, ss_in (dc_ss st) = sin0 ++ sv_ahead sv) /\
      alive_ok st k sv (ss_in (dc_ss st)) (ss_out (dc_ss st)).

Definition SR3 : srel3 := {| sr_run := SR3_run; sr_ex := xrel3; sr_ex_clean := xrel3_clean |}.

(* the same running-stream relation with no exact claim: the post of the relational pieces of the stream proof
   (S3Main.ds_post, S3Ret.RET3, the VST cases of zdss_loadHeader), which the exact pieces (S3Ret.RET3x,
   lh/LH3*X.v) reuse and strengthen *)
Definition SR3r : srel3 :=
  {| sr_run := SR3_run; sr_ex := fun _ _ _ _ => True; sr_ex_clean := fun _ _ _ _ _ _ _ => I |}.

End CM_S3Defs_1.
