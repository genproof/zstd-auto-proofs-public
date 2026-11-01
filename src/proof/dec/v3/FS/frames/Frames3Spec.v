(* FS3 one-shot frames: the specification of ZSTD_decompressFrame chosen by the FRAMES3 part, the port of v2's
   FramesSpec.v (spec-dec-FS-frames) to API v3: the frame group
   with the parameters (fcore3: format, forceIgnoreChecksum, maxBlockSizeParam, refMultipleDDicts, ddictSet)
   and the dictionary selection of ZSTD_decodeFrameHeader (sel_res, FSSpecs3). *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame.
Local Open Scope logic.

Section CM_Frames3Spec_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- v2 FramesSpec's history predicates (unchanged) ---------- *)

(* the byte at distance k >= 1 before the end of the extDict *)
Definition ext_byte (e: ext_seg) (k: Z) : val :=
  match e with
  | ExtSep _ _ _ ec e1 _ => Znth (e1 - k) ec
  | _ => Vundef
  end.

(* the extDict ends with the dictionary content hist (the frame's history before its first byte) *)
Definition ext_view (e: ext_seg) (hist: list Z) : Prop :=
  forall k, 1 <= k <= Zlength hist ->
    k <= ext_len e /\ ext_byte e k = Vint (Int.repr (byte_at hist (Zlength hist - k))).

(* the history pointers the block decoder loads, for any output array: prefixStart and virtualStart NULL
   or pointers, dictEnd NULL or the end of the extDict *)
Definition hist_ptrs_e (fs: fstate) (e: ext_seg) : Prop :=
  is_pointer_or_null (fs_prefixStart fs) /\ is_pointer_or_null (fs_virtualStart fs) /\
  (fs_dictEnd fs = nullval \/
   match e with ExtSep _ eb en _ e1 _ => fs_dictEnd fs = offset_val e1 eb /\ 0 <= e1 <= en | _ => False end).

(* every byte of the extDict is defined *)
Definition ext_def (e: ext_seg) : Prop :=
  forall k, 1 <= k <= ext_len e -> is_byte_val (ext_byte e k).

(* where the frame's history before its first byte (the dictionary content hist) lies, for a frame written at
   base + d of an output array of N cells c: in the extDict, the current segment starting at dst (prefixStart =
   dst); or in the output array itself just before dst, with no extDict (ZSTD_decompress_usingDict with the
   dictionary right before dst in one object, [dict | dst]: ZSTD_checkContinuity then keeps the dictionary content
   as the prefix of dst's output, prefixStart = virtualStart = the content's start, dictEnd = NULL) *)
Definition frame_hist (fs: fstate) (base: val) (N: Z) (c: list val) (d: Z) (e: ext_seg) (hist: list Z) : Prop :=
  (layout_ok fs base N d d e /\ ext_view e hist) \/
  (e = ExtNone /\ Zlength hist <= d /\ layout_ok fs base N d (d - Zlength hist) ExtNone /\
   sublist (d - Zlength hist) d c = zbytes hist).

(* ---------- v3 ---------- *)

(* what ZSTD_decompressFrame returns on the bytes s under the decoding mode md (Params.decode_frame_m), written
   at d with capacity cap: r, the new output oc', the bytes k taken; an error on a frame zstd certainly refuses
   (Refuse.frame_refused_m) *)
Definition frame_res3 (md: dmode) (dm: dict_model) (s: list Z) (cap r: Z) (oc': list val) (d k: Z) : Prop :=
  match decode_frame_m md dm no_wlim s with
  | FOk c sz =>
      (is_error_code r = false -> r = Zlength c /\ sublist d (d + r) oc' = zbytes c /\ k = sz) /\
      (is_error_code r = true -> cap < Zlength c)
  | FDetHdr | FDetCk => is_error_code r = true
  | FUnk => frame_refused_m md dm no_wlim s -> is_error_code r = true
  end.

(* the exact result (model/ExFrame.v's x_frame over model/Exact.v's block decoder) of ZSTD_decompressFrame on the
   bytes s with capacity cap, from the tables' state ts (without a dictionary: x_frame's ZSTD_decompressBegin keeps
   only litExtraBuffer's bytes): an error iff x_frame fails; else exactly its content c written at d, the bytes k it
   takes, and the litExtraBuffer lxb' it leaves in the tables (the model's final state's) *)
Definition frame_exact (ts: tstate) (s: list Z) (cap r: Z) (oc': list val) (d k: Z) (lxb': list Z) : Prop :=
  match x_frame xstate (xst_begin xhuf) xblock (ts_x ts) s cap with
  | None => is_error_code r = true
  | Some (c, k', e) =>
      r = Zlength c /\ sublist d (d + r) oc' = zbytes c /\ k = k' /\ lxb' = x_lxb xhuf e
  end.

(* the error codes of ZSTD_decompressFrame: a frame the model decodes, with only Raw and
   RLE blocks, refused (only for a too small capacity: frame_res3) with ZSTD_error_dstSize_tooSmall; a frame refused
   by its checksum, with room for its content, refused with ZSTD_error_checksum_wrong *)
Definition frame_codes3 (md: dmode) (dm: dict_model) (s: list Z) (cap r: Z) : Prop :=
  (forall c sz, decode_frame_m md dm no_wlim s = FOk c sz -> frame_rr_m md s -> is_error_code r = true ->
     r = err_code ZSTD_error_dstSize_tooSmall) /\
  (decode_frame_m md dm no_wlim s = FDetCk -> forall c, frame_out_m md dm s = Some c -> Zlength c <= cap ->
     r = err_code ZSTD_error_checksum_wrong).

(* the tables hold the context's LOCAL DDict x (ZSTD_decompressDCtx after ZSTD_DCtx_loadDictionary, with the
   selection on): its entropy stays in dgroup (sel_res) while ZSTD_decodeFrameHeader runs, which is safe because
   the selection finds no DDict for this frame (the header bytes ZSTD_decodeFrameHeader reads) (with one, zstd would free the local DDict: ZSTD_decompressMultiFrame
   then begins with the set's DDict instead, fix F4) *)
Definition lent_ok (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val)
    (ox: option ddx) (s: list Z) : Prop :=
  sel_on pr sp = true /\
  (exists x buf, ox = Some x /\ df_lx d = Some (x, buf) /\ df_local d <> nullval) /\
  (forall h, get_frame_header_m (dp_fmt pr =? 1) (sublist 0 (header_size_m (dp_fmt pr =? 1) s) s) = FH_ok h ->
     sel_r d l tbl (fh_dictID h) = nullval).

(* the dictionary fields after the frame: unchanged, or (selection) a DDict of the set *)
Definition dict_after (pr: dparams) (sp: val) (l: list (val * ddict_st)) (d d': dfields) : Prop :=
  d' = d \/ (sel_on pr sp = true /\ exists q, In q (map fst l) /\ d' = switch_fields q).


(* ---------- `lent`: the selection's resources without the local DDict's entropy and copied bytes ---------- *)

(* dgroup without the local DDict's entropy (DENT) and, for a copied local DDict, without its bytes (both are the
   frame's: dent_of ox and ext_res e) *)
Definition dgroup_hole (gv: globals) (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p *
  match df_lx d with
  | Some (x, buf) => !! (dx_q x = df_local d) &&
      (ddict_struct x buf * blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
       (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp) *
       ddict_pad (dx_q x))
  | None => emp
  end.

Definition sel_hole (gv: globals) (p: val) (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st))
    (tbl: list val) (xq: option (val * val)) (am: option cmem) (hb: Z) : mpred :=
  if sel_on pr sp
  then mem_mgr gv * dgroup_hole gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl * set_ids l *
       opt_token xq
  else emp.

(* the selection's resources ZSTD_decompressFrame gets: whole, or (lent) with the hole *)
Definition sel_any (DENT: dent_pred) (gv: globals) (p: val) (pr: dparams) (sp: val) (d: dfields)
    (l: list (val * ddict_st)) (tbl: list val) (xq: option (val * val)) (lent: bool) (am: option cmem) (hb: Z)
    : mpred :=
  if lent then sel_hole gv p pr sp d l tbl xq am hb else sel_res DENT gv p pr sp d l tbl xq am hb.

(* with `lent`, the extDict of a copied local DDict is that copy *)
Definition lent_ext (d: dfields) (e: ext_seg) : Prop :=
  match df_lx d with
  | Some (x, buf) => ddx_copied x = true ->
      exists e1 elen, e = ExtSep Ews buf (Zlength (dx_bytes x)) (zbytes (dx_bytes x)) e1 elen
  | None => True
  end.

(* with the selection, which DDict the frame's header bytes x selected: none, or the one the
   probe finds for its Dictionary_ID *)
Definition dict_sel (pr: dparams) (sp: val) (l: list (val * ddict_st)) (tbl: list val) (x: list Z)
    (d d': dfields) : Prop :=
  sel_on pr sp = true -> forall h, get_frame_header_m (dp_fmt pr =? 1) x = FH_ok h ->
    d' = d \/ (hs_probe l tbl (fh_dictID h) <> nullval /\ d' = switch_fields (hs_probe l tbl (fh_dictID h))).

Section S.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* ZSTD_decompressFrame(dctx, dst, cap, srcPtr, srcSizePtr), after ZSTD_decompressBegin_usingDict /
   usingDDict and ZSTD_checkContinuity: one frame of ANY bytes s = iw_s i at *srcPtr, with *srcSizePtr = |s|,
   written at dst = base + d of the output array o (capacity cap = oa_cap o), with the parameters pr and the set
   pointer sp (the selection's resources sel_res, with the context's allocator am, which has given out hb bytes
   besides the local DDict; lent: the tables' DDict is the local one, its entropy in dgroup).
   As v2 (FramesSpec), with frame_res3 under dmode_of pr (also with the selection: the C's dictID check against
   the context's dictID after the selection and the model's against dm_id dm agree up to FUnk).  Afterwards the
   dictionary fields are d' (dict_after); after a success with the selection and a current DDict, fParams' dictID
   is one for which the probe finds nothing or the new current DDict.  The tables hold ts (DecRep.tstate), whose
   entropy state is the dictionary's; afterwards they are uninitialised, litExtraBuffer holding lxb' (the exact model's, frame_exact). *)
Definition ZSTD_decompressFrame_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressFrame
  WITH W: list ptr_witness, gv: globals, p: val, fs: fstate, ox: option ddx, dm: dict_model, e: ext_seg,
       o: outarr, i: inwin, sp: val, ssp: val,
       pr: dparams, dsp: val, d: dfields, l: list (val * ddict_st), tbl: list val, xq: option (val * val), lent: bool,
       am: option cmem, hb: Z, ts: tstate
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr (tptr tvoid), tptr tulong ]
    PROP (outarr_ok o; inwin_ok i;
          match e with ExtIn _ _ => False | _ => True end;
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          fs_dictID fs = Vint (Int.repr (dm_id dm)); 0 <= dm_id dm <= Int.max_unsigned;
          fs_processedCSize fs = Vlong (Int64.repr 0);
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          hist_ptrs_e fs e; bytes_ok (dm_content dm); ext_def e; ext0_ok W fs e;
          0 < oa_cap o -> frame_hist fs (oa_base o) (oa_N o) (oa_c o) (oa_d o) e (dm_content dm);
          sel_on pr dsp = true -> cur_ok d l xq; sel_mem pr dsp d am hb;
          lent = true -> lent_ok pr dsp d l tbl ox (iw_s i) /\ lent_ext d e;
          ts_d ts = dm_state dm)
    PARAMS (p; offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o)); sp; ssp)
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; fcore3 p fs pr dsp; sel_any DENT gv p pr dsp d l tbl xq lent am hb;
         TABS gv p ox ts; dent_of DENT gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res e;
         data_at Tsh (tptr tvoid) (offset_val (iw_off i) (iw_base i)) sp;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength (iw_s i)))) ssp)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX fs': fstate, EX k: Z, EX d': dfields, EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          is_error_code r = false -> r <= oa_cap o /\ 0 <= k <= Zlength (iw_s i);
          is_error_code r = false ->
            exists c, bytes_ok c /\ Zlength c = r /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes c;
          is_error_code r = true -> k = 0 /\ dec_err r;
          frame_res3 (dmode_of pr) dm (iw_s i) (oa_cap o) r oc' (oa_d o) k;
          fs_dictEnd fs' = fs_dictEnd fs;
          fs_ddictIsCold fs' = Vint (Int.repr 0) \/ fs_ddictIsCold fs' = Vint (Int.repr 1);
          dict_after pr dsp l d d'; lent = true -> d' = d;
          is_error_code r = false -> sel_on pr dsp = true -> df_ddict d <> nullval ->
            exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
              (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d');
          fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs');
          dict_sel pr dsp l tbl (sublist 0 (header_size_m (dp_fmt pr =? 1) (iw_s i)) (iw_s i)) d d';
          is_error_code r = false -> (dp_fmt pr = 1 \/ is_skippable_magic (le_field (iw_s i) 0 4) = false) ->
            frame_compressed_size_m (dp_fmt pr =? 1) (iw_s i) = Some k;
          frame_codes3 (dmode_of pr) dm (iw_s i) (oa_cap o) r;
          (* the end-of-frame check: a success on a Zstandard frame that declares its content size decodes
             exactly that many bytes *)
          is_error_code r = false -> forall h, get_frame_header_m (dp_fmt pr =? 1) (iw_s i) = FH_ok h ->
            fh_frameType h = 0 -> fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h;
          (* the exact result, from the context's own tables without a dictionary, with the default parameters *)
          ox = None -> dm = no_dict -> pr = dparams_dflt -> e = ExtNone ->
            frame_exact ts (iw_s i) (oa_cap o) r oc' (oa_d o) k lxb')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; fcore3 p fs' pr dsp; sel_any DENT gv p pr dsp d' l tbl xq lent am hb;
         tables_uninit p lxb'; dent_of DENT gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res e;
         data_at Tsh (tptr tvoid) (offset_val (iw_off i + k) (iw_base i)) sp;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength (iw_s i) - k))) ssp).

End S.

(* the context of both bodies *)
Definition FR3_G (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel) : funspecs :=
  FS3_G DENT TABS SR BR ++ [ZSTD_decompressFrame_spec3 DENT TABS].

End CM_Frames3Spec_1.
