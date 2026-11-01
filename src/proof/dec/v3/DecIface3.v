(* API v3: the interfaces between the decoder's subtrees, fixed: each subtree is proved against them.
   Only what changes from v2 (DecIface.v, still in force otherwise):

   - the configuration fields: v2's cfg_b (format = 0, disableHufAsm = 0) is split into cfg_fmt p f (the
     context's format, ZSTD_d_format: 0 zstd1, 1 magicless) and cfg_lit p (disableHufAsm = 0, which no law
     changes); cfg_b p = cfg_fmt p 0 * cfg_lit p (cfg_b_split);
   - H exports with the format: startingInputLength, frameHeaderSize_internal, getFrameHeader_advanced,
     findFrameCompressedSize_advanced (models: model/Params.v, model/ParamsH.v);
   - B exports: ZSTD_decompressBegin (now exported: an API function), Begin_usingDict and Begin_usingDDict
     with any format (dctx->expected = ZSTD_startingInputLength(format)); Begin_usingDDict after the contract's
     VST-layer fix (ddictIsCold is set without comparing dictEnd,
     so no precondition on the context's dictEnd); the block decoder without the format field (cfg_lit only:
     it never reads the format, and the frame decoders call it with any); initDDict_internal with the
     content type ZSTD_dct_fullDict (2).
   Every v3 spec is a funspec_sub of its v2 spec (DecLift.v), so v2 bodies that call these stay valid. *)
Require Export Zstd.proof.dec.DecIface.
Require Export Zstd.proof.model.ParamsH.
Require Export Zstd.proof.dec.v3.H.HAlloc3.
Local Open Scope logic.

(* ---------- configuration fields ---------- *)

Definition cfg_fmt (p: val) (f: Z) : mpred := field_at Ews t_dctx (DOT _format) (Vint (Int.repr f)) p.
Definition cfg_lit (p: val) : mpred := field_at Ews t_dctx (DOT _disableHufAsm) (Vint (Int.repr 0)) p.

Lemma cfg_b_split (p: val) : cfg_b p = cfg_fmt p 0 * cfg_lit p.
Proof. reflexivity. Qed.

(* the format as the model reads it *)
Definition fmt_mg (f: Z) : bool := f =? 1.

(* =====================================================================================
   H
   ===================================================================================== *)

Definition ZSTD_startingInputLength_spec3 : ident * funspec :=
  DECLARE _ZSTD_startingInputLength
  WITH f: Z
  PRE [ tint ] PROP (f = 0 \/ f = 1) PARAMS (Vint (Int.repr f)) SEP ()
  POST [ tulong ] PROP () RETURN (Vlong (Int64.repr (starting_len (fmt_mg f)))) SEP ().

Definition ZSTD_frameHeaderSize_internal_spec3 : ident * funspec :=
  DECLARE _ZSTD_frameHeaderSize_internal
  WITH gv: globals, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, f: Z
  PRE [ tptr tvoid, tulong, tint ]
    PROP (win_ok sh N c off (Zlength s) s; f = 0 \/ f = 1)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr f)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_header_size_m (fmt_mg f) s with Some k => r = k | None => dec_err r end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base).

(* Spec_api6.fh_post_m: the outcome of model/Params.get_frame_header_m (the struct untouched below
   ZSTD_startingInputLength bytes, zeroes when more input is asked for) *)
Definition ZSTD_getFrameHeader_advanced_spec3 : ident * funspec :=
  DECLARE _ZSTD_getFrameHeader_advanced
  WITH gv: globals, shz: share, zfh: val, v0: reptype t_fh,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, f: Z
  PRE [ tptr t_fh, tptr tvoid, tulong, tint ]
    PROP (writable_share shz; win_ok sh N c off (Zlength s) s; f = 0 \/ f = 1)
    PARAMS (zfh; offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr f)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX v: reptype t_fh,
    PROP (0 <= r <= Int64.max_unsigned; fh_post_m (fmt_mg f) s r v0 v)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shz t_fh v zfh; data_at sh (tarray tuchar N) c base).

Definition ZSTD_findFrameCompressedSize_advanced_spec3 : ident * funspec :=
  DECLARE _ZSTD_findFrameCompressedSize_advanced
  WITH gv: globals, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, f: Z
  PRE [ tptr tvoid, tulong, tint ]
    PROP (win_ok sh N c off (Zlength s) s; f = 0 \/ f = 1)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr f)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_compressed_size_m (fmt_mg f) s with Some k => r = k | None => is_error_code r = true end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base).

(* the allocation helpers for any allocator (H/HAlloc3.v): malloc, calloc and free through a context's own allocator
   or the default one *)
Section HEx.
Context {CMI: cmem_preds}.

Definition H_exports3 : funspecs :=
  [ ZSTD_startingInputLength_spec3; ZSTD_frameHeaderSize_internal_spec3; ZSTD_getFrameHeader_advanced_spec3;
    readSkippableFrameSize_spec; ZSTD_getcBlockSize_spec; ZSTD_findFrameCompressedSize_advanced_spec3;
    ZSTD_customMallocP_cm_spec; ZSTD_customCallocP_cm_spec; ZSTD_customFreeP_cm_spec; ZSTD_customMem_copy_cm_spec ].

End HEx.

(* =====================================================================================
   B
   ===================================================================================== *)

(* ZSTD_decompressBegin in a context of format f: v2's fs_begin with dctx->expected =
   ZSTD_startingInputLength(f) *)
Definition fs_begin3 (fs: fstate) (f: Z) : fstate :=
  {| fs_previousDstEnd := nullval;
     fs_gpDictCopy := Vint (Int.repr 0);
     fs_prefixStart := nullval;
     fs_virtualStart := nullval;
     fs_dictEnd := nullval;
     fs_expected := Vlong (Int64.repr (starting_len (fmt_mg f)));
     fs_fParams := fs_fParams fs;
     fs_processedCSize := Vlong (Int64.repr 0);
     fs_decodedSize := Vlong (Int64.repr 0);
     fs_bType := Vint (Int.repr 3);
     fs_stage := Vint (Int.repr 0);
     fs_xxh := fs_xxh fs;
     fs_headerSize := fs_headerSize fs;
     fs_validateChecksum := fs_validateChecksum fs;
     fs_rleSize := fs_rleSize fs;
     fs_isFrameDecompression := Vint (Int.repr 1);
     fs_dictID := Vint (Int.repr 0);
     fs_ddictIsCold := fs_ddictIsCold fs |}.

Lemma fs_begin3_zstd1 (fs: fstate) : fs_begin3 fs 0 = fs_begin fs.
Proof. reflexivity. Qed.

(* ---------- a DDict made through the allocator am (ZSTD_createDDict_advancedP stores it in cMem) ---------- *)

(* the DDict struct after ZSTD_customMallocP: cMem set by the caller to am, the rest uninitialised *)
Definition ddict_fresh3 (am: option cmem) (q: val) : mpred :=
  let t := Tstruct _ZSTD_DDict_s noattr in
  field_at_ Ews t (DOT _dictBuffer) q * field_at_ Ews t (DOT _dictContent) q *
  field_at_ Ews t (DOT _dictSize) q * field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q * field_at_ Ews t (DOT _entropyPresent) q *
  field_at Ews t (DOT _cMem) (cmem_v am) q.

(* ZSTD_initDDict_internal's DDict description (DecIface.ddx_of) with its allocator *)
Definition ddx_of3 (am: option cmem) (q p: val) (b: list Z) (method ctype: Z) (ores: option (dstate * Z)) : ddx :=
  {| dx_q := q; dx_bytes := b;
     dx_ref := if orb (method =? 1) (Zlength b =? 0) then Some p else None;
     dx_raw := ctype =? 1; dx_ld := ores; dx_mem := am |}.

Lemma ddx_of3_none (q p: val) (b: list Z) (method ctype: Z) (ores: option (dstate * Z)) :
  ddx_of3 None q p b method ctype ores = ddx_of q p b method ctype ores.
Proof. reflexivity. Qed.

Section B.
Context {CMI: cmem_preds}.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* what ZSTD_freeDDict needs of a DDict of the allocator am whose initialisation failed: dictBuffer NULL or a block
   of n bytes (nb: the bytes of that block, 0 without one; not empty for an own allocator, whose free compares it
   with NULL), the other fields anything *)
Definition ddict_failed3 (am: option cmem) (q: val) (n nb: Z) : mpred :=
  let t := Tstruct _ZSTD_DDict_s noattr in
  EX db: val,
  !! (nb = (if eq_dec db nullval then 0 else n) /\ (db <> nullval -> am <> None -> 0 < n)) &&
  (field_at Ews t (DOT _dictBuffer) db q *
   (if eq_dec db nullval then emp else blk_tok am (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db) *
   field_at_ Ews t (DOT _dictContent) q * field_at_ Ews t (DOT _dictSize) q * field_at_ Ews t (DOT _entropy) q *
   field_at_ Ews t (DOT _dictID) q * field_at_ Ews t (DOT _entropyPresent) q *
   field_at Ews t (DOT _cMem) (cmem_v am) q).

(* ZSTD_decompressBegin(dctx): a new frame, no dictionary, the initial entropy state, litExtraBuffer kept;
   never fails *)
Definition ZSTD_decompressBegin_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressBegin
  WITH gv: globals, p: val, fs: fstate, f: Z, lxb: list Z
  PRE [ tptr t_dctx ]
    PROP (f = 0 \/ f = 1)
    PARAMS (p) GLOBALS (gv)
    SEP (zstd_globals gv; cfg_fmt p f; frame_fields p fs; tables_uninit p lxb)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; cfg_fmt p f; frame_fields p (fs_begin3 fs f); TABS gv p None (tstate_begin lxb)).

(* v2's ZSTD_decompressBegin_usingDict_spec in a context of format f *)
Definition ZSTD_decompressBegin_usingDict_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDict
  WITH gv: globals, p: val, fs: fstate, W: list ptr_witness, shk: share, dk: val, b: list Z, f: Z,
       lxb: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (readable_share shk; Zlength b <= 2 ^ 63 - 1; bytes_ok b; f = 0 \/ f = 1;
          dk = nullval /\ b = [] \/ buf_ok W shk (Zlength b) dk)
    PARAMS (p; dk; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs; tables_uninit p lxb;
         if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
         match usingdict_model dk b ores with
         | None => !! (dec_err r) &&
             EX fs': fstate, !! (fs_dictEnd fs' = nullval /\ fs_ddictIsCold fs' = fs_ddictIsCold fs /\ fs_fParams fs' = fs_fParams fs) &&
               frame_fields p fs' * tables_uninit p lxb
         | Some dm =>
             !! (r = 0) &&
             frame_fields p
               (if eq_dec dk nullval then fs_begin3 fs f
                else if Zlength b =? 0 then fs_begin3 fs f
                else fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                       (offset_val (Zlength b) dk) 0 (dm_id dm)) *
             EX x2: bool, TABS gv p None (mk_tstate (dm_state dm) x2 lxb)
         end;
         if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk).

(* ZSTD_decompressBegin_usingDDict(dctx, ddict) in a context of format f: ddict = NULL (no dictionary) or the
   DDict x.  With the VST-layer fix, ddictIsCold is set (0 or 1) without comparing dictEnd: no condition
   on the context's previous dictionary.  Never fails.  The DDict's memory (ddict_mem, of its allocator) is passed:
   zstd compares its copy's pointer with NULL (gpDictCopy), which needs the copy's validity. *)
Definition ZSTD_decompressBegin_usingDDict_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDDict
  WITH gv: globals, p: val, fs: fstate, W: list ptr_witness, ox: option ddx, buf: val, f: Z, lxb: list Z
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (f = 0 \/ f = 1)
    PARAMS (p; match ox with None => nullval | Some x => dx_q x end) GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p fs; tables_uninit p lxb;
         match ox with
         | None => emp
         | Some x => ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf
         end)
  POST [ tulong ]
    EX cold: val,
    PROP (match ox with
          | None => cold = fs_ddictIsCold fs
          | Some _ => cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)
          end)
    RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
         match ox with
         | None => frame_fields p (fs_begin3 fs f) * TABS gv p None (tstate_begin lxb)
         | Some x =>
             frame_fields p
               (fs_set_dictEnd
                  (fs_with_dict (fs_set_cold (fs_begin3 fs f) cold) buf (ddx_end x buf)
                     (if ddx_copied x then 1 else 0) (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
                  (ddx_end x buf)) *
             TABS gv p ox (mk_tstate (ddx_state x) false lxb) *
             ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf
         end).

(* v2's ZSTD_decompressBlock_internal_spec with cfg_lit instead of cfg_b (the format field is the caller's) *)
Definition ZSTD_decompressBlock_internal_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressBlock_internal
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, ts: tstate, bsm: Z, streaming: Z,
       W: list ptr_witness, o: outarr, i: inwin, h: hctx
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (outarr_ok o; inwin_ok i;
          streaming = 0 \/ streaming = 1;
          0 <= bsm <= ZSTD_BLOCKSIZE_MAX;
          fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          0 < oa_cap o -> layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h);
          (match hc_ext h with ExtIn _ _ => streaming = 1 | _ => True end);
          hist_ptrs_ok fs o (hc_ext h); ext0_ok W fs (hc_ext h);
          (* the history the matches copy holds defined bytes (memcpy and memmove are libc.c's byte loops) *)
          hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h))
    PARAMS (p; offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o));
            offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i))); Vint (Int.repr streaming))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p fs; TABS gv p ox ts; dent_of DENT gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h))
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX cold: val, EX ts': option tstate,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          (byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc');
          is_error_code r = false ->
            r <= oa_cap o /\ cold = Vint (Int.repr 0) /\ ts' <> None /\
            (streaming = 1 -> r <= bsm ->
             unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))) /\
            (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
             (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
             exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
          is_error_code r = true -> ts' = None /\ dec_err r;
          cold = fs_ddictIsCold fs \/ cold = Vint (Int.repr 0);
          oa_cap o = 0 \/
          (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
           ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
          bytes_ok (hc_hist h) -> bytes_ok (hc_out h) ->
            block_ok ts (hc_hist h) (hc_out h) (iw_s i) bsm (hc_wsize h) streaming (oa_c o) oc'
              (oa_d o) (oa_cap o) r (option_map ts_d ts');
          ox = None -> block_exact ts o i h bsm streaming r oc' ts')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p (fs_set_cold fs cold);
         match ts' with Some ts2 => TABS gv p ox ts2 | None => EX lxb: list Z, tables_uninit p lxb end;
         dent_of DENT gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)).

(* v2's ZSTD_initDDict_internal_spec, content type ctype 0 auto, 1 raw content, 2 fullDict (refuses bytes
   without the dictionary magic number: then dictionary_corrupted; a success has them); the copy goes through the
   DDict's allocator am (its cMem), which has given out h bytes.  The bytes may be NULL for none (pk = NULL,
   b = nil: ZSTD_createDDict(NULL, 0)); the DDict then has no content (dx_ref = Some nullval, buf = NULL) *)
Definition ZSTD_initDDict_internal_spec3 : ident * funspec :=
  DECLARE _ZSTD_initDDict_internal
  WITH gv: globals, q: val, W: list ptr_witness, sh: share, pk: val, b: list Z, method: Z, ctype: Z,
       am: option cmem, h: Z
  PRE [ tptr t_ddict, tptr tvoid, tulong, tint, tint ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          is_pointer_or_null pk; pk = nullval -> b = nil; pk <> nullval -> buf_ok W sh (Zlength b) pk;
          method = 0 \/ method = 1; ctype = 0 \/ ctype = 1 \/ ctype = 2; isptr q;
          cm_room am h (Zlength b); cmem_ok am)
    PARAMS (q; pk; Vlong (Int64.repr (Zlength b)); Vint (Int.repr method); Vint (Int.repr ctype))
    GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; pws_pred W; ddict_fresh3 am q; cm_have am h; bytes_at sh b pk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores;
          (r = 0 /\ (ctype = 2 -> dict_formatted b = true)) \/
          (is_error_code r = true /\
           ((ctype <> 1 /\ dict_auto b = None) \/ (ctype = 2 /\ dict_formatted b = false) \/
            r = err_code ZSTD_error_memory_allocation)))
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; pws_pred W; bytes_at sh b pk;
         if Z.eq_dec r 0
         then let x := ddx_of3 am q pk b method ctype ores in
              EX buf: val, ddict_struct x buf * DENT gv q (ddx_ent x) *
                (if ddx_copied x
                 then blk_tok am (tarray tuchar (Zlength b)) buf *
                      data_at Ews (tarray tuchar (Zlength b)) (zbytes b) buf
                 else emp) *
                cm_have am (h + (if ddx_copied x then Zlength b else 0))
         else EX nb: Z, ddict_failed3 am q (Zlength b) nb * cm_have am (h + nb)).

Definition B_exports3 : funspecs :=
  [ ZSTD_decompressBegin_spec3; ZSTD_decompressBegin_usingDict_spec3; ZSTD_decompressBegin_usingDDict_spec3;
    ZSTD_decompressBlock_internal_spec3; ZSTD_initDDict_internal_spec3;
    ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec ].

End B.
