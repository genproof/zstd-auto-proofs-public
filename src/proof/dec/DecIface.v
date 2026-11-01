(* The interfaces between the decoder's subtrees.  Fixed: the three subtrees are proved against these
   specifications.

   The decoder unit's functions are split into L0 (Specs_L0, proved), DEAD (no law reaches them: vacuous
   specifications, proved in the decoder's assembly), and three subtrees:
   - H  (headers, frame inspection, allocation helpers): pure readers of the input, exact against
        model/Frame.v and model/Info.v; exports H_exports below and its API specifications;
   - B  (blocks: FSE / Huffman tables and decoders, literals, sequences, ZSTD_decompressBlock_internal;
        ZSTD_decompressBegin*, the dictionary's entropy, DDict initialisation); chooses the predicates
        DENT and TABS (DecRep.v) and exports B_exports;
   - FS (frames, streaming, contexts, dictionary API): chooses DC and DD of Spec_api6 and proves all the
        other API specifications.
   Each subtree proves its bodies against L0, the exports of the subtrees it calls, and its own internal
   specifications (DecSubtrees.v). *)
Require Export Zstd.proof.dec.DecRep.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Local Open Scope logic.

(* ---------- input windows ----------
   n bytes s at offset off of a byte array (N cells c, any contents outside the window) at base *)
Definition win_ok (sh: share) (N: Z) (c: list val) (off n: Z) (s: list Z) : Prop :=
  readable_share sh /\ 0 <= off /\ off + n <= N /\ N <= 2 ^ 63 - 1 /\ Zlength c = N /\
  Zlength s = n /\ bytes_ok s /\ sublist off (off + n) c = zbytes s.

(* =====================================================================================
   H: headers (exact on any bytes) and the allocation helpers
   ===================================================================================== *)

Definition ZSTD_startingInputLength_spec : ident * funspec :=
  DECLARE _ZSTD_startingInputLength
  WITH u: unit
  PRE [ tint ] PROP () PARAMS (Vint (Int.repr 0)) SEP ()
  POST [ tulong ] PROP () RETURN (Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX)) SEP ().

Definition ZSTD_frameHeaderSize_internal_spec : ident * funspec :=
  DECLARE _ZSTD_frameHeaderSize_internal
  WITH gv: globals, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tint ]
    PROP (win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_header_size s with Some k => r = k | None => dec_err r end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base).

(* ZSTD_getFrameHeader_advanced also says what it leaves in *zfh when it asks for more input: nothing
   written for fewer than 5 bytes, zeroes otherwise (memset before the size checks) *)
(* the same outcome as the API's ZSTD_getFrameHeader (Spec_api6.fh_post: v0 = the struct before the call,
   left untouched for fewer than 5 bytes; dec_err on an error) *)
Definition fh_post_adv (s: list Z) (r: Z) (v0 v: reptype t_fh) : Prop := fh_post s r v0 v.

Definition ZSTD_getFrameHeader_advanced_spec : ident * funspec :=
  DECLARE _ZSTD_getFrameHeader_advanced
  WITH gv: globals, shz: share, zfh: val, v0: reptype t_fh,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr t_fh, tptr tvoid, tulong, tint ]
    PROP (writable_share shz; win_ok sh N c off (Zlength s) s)
    PARAMS (zfh; offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shz t_fh v0 zfh; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX v: reptype t_fh,
    PROP (0 <= r <= Int64.max_unsigned; fh_post_adv s r v0 v)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shz t_fh v zfh; data_at sh (tarray tuchar N) c base).

(* exact on any input: the model's skippable_frame_size is fix F5's single test in size_t *)
Definition readSkippableFrameSize_spec : ident * funspec :=
  DECLARE _readSkippableFrameSize
  WITH sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong ]
    PROP (win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)))
    SEP (data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match skippable_frame_size s with Some k => r = k | None => dec_err r end)
    RETURN (Vlong (Int64.repr r))
    SEP (data_at sh (tarray tuchar N) c base).

(* blockProperties_t: blockType, lastBlock, origSize *)
Definition bp_val (bp: block_props) : reptype t_bp :=
  (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)), Vint (Int.repr (bp_origSize bp)))).

Definition ZSTD_getcBlockSize_spec : ident * funspec :=
  DECLARE _ZSTD_getcBlockSize
  WITH gv: globals, shb: share, bpp: val, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr t_bp ]
    PROP (writable_share shb; win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)); bpp) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shb t_bp bpp; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX v: reptype t_bp,
    PROP (0 <= r <= Int64.max_unsigned;
          match cblock_size s with
          | None => dec_err r
          | Some k => r = k /\ v = bp_val (block_props_of s)
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shb t_bp v bpp; data_at sh (tarray tuchar N) c base).

Definition ZSTD_findFrameCompressedSize_advanced_spec : ident * funspec :=
  DECLARE _ZSTD_findFrameCompressedSize_advanced
  WITH gv: globals, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tint ]
    PROP (win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          match frame_compressed_size s with Some k => r = k | None => is_error_code r = true end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar N) c base).

(* The allocation helpers with the allocator { NULL, NULL, NULL } at pm: malloc / calloc / free of an
   object of type t (the caller chooses t, as with malloc_spec'). *)
Definition ZSTD_customMallocP_spec : ident * funspec :=
  DECLARE _ZSTD_customMallocP
  WITH gv: globals, t: type, shm: share, pm: val
  PRE [ tulong, tptr t_cmem ]
    PROP (readable_share shm; 0 <= sizeof t <= Ptrofs.max_unsigned;
          complete_legal_cosu_type t = true; natural_aligned natural_alignment t = true)
    PARAMS (Vlong (Int64.repr (sizeof t)); pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm)
  POST [ tptr tvoid ]
    EX q: val,
    PROP (is_pointer_or_null q)
    RETURN (q)
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm;
         if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q).

(* calloc of n bytes (zstd: the DDict hash set only) *)
Definition ZSTD_customCallocP_spec : ident * funspec :=
  DECLARE _ZSTD_customCallocP
  WITH gv: globals, n: Z, shm: share, pm: val
  PRE [ tulong, tptr t_cmem ]
    PROP (readable_share shm; 0 <= n <= Ptrofs.max_unsigned)
    PARAMS (Vlong (Int64.repr n); pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm)
  POST [ tptr tvoid ]
    EX q: val,
    PROP (is_pointer_or_null q)
    RETURN (q)
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm;
         if eq_dec q nullval then emp
         else malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (Zrepeat (Vint Int.zero) n) q).

Definition ZSTD_customFreeP_spec : ident * funspec :=
  DECLARE _ZSTD_customFreeP
  WITH gv: globals, t: type, q: val, shm: share, pm: val
  PRE [ tptr tvoid, tptr t_cmem ]
    PROP (readable_share shm)
    PARAMS (q; pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm;
         if eq_dec q nullval then emp else malloc_token Ews t q * data_at_ Ews t q)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; data_at shm t_cmem cmem_null pm).

Definition ZSTD_customMem_copy_spec : ident * funspec :=
  DECLARE _ZSTD_customMem_copy
  WITH shd: share, pd: val, shs: share, ps: val
  PRE [ tptr t_cmem, tptr t_cmem ]
    PROP (writable_share shd; readable_share shs)
    PARAMS (pd; ps)
    SEP (data_at_ shd t_cmem pd; data_at shs t_cmem cmem_null ps)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd t_cmem cmem_null pd; data_at shs t_cmem cmem_null ps).

Definition H_exports : funspecs :=
  [ ZSTD_startingInputLength_spec; ZSTD_frameHeaderSize_internal_spec; ZSTD_getFrameHeader_advanced_spec;
    readSkippableFrameSize_spec; ZSTD_getcBlockSize_spec; ZSTD_findFrameCompressedSize_advanced_spec;
    ZSTD_customMallocP_spec; ZSTD_customCallocP_spec; ZSTD_customFreeP_spec; ZSTD_customMem_copy_spec ].

(* =====================================================================================
   B: beginning a frame, the blocks, the DDict's entropy
   ===================================================================================== *)

(* ZSTD_decompressBegin: the frame fields of a new frame (no dictionary) *)
Definition fs_begin (fs: fstate) : fstate :=
  {| fs_previousDstEnd := nullval;
     fs_gpDictCopy := Vint (Int.repr 0);
     fs_prefixStart := nullval;
     fs_virtualStart := nullval;
     fs_dictEnd := nullval;
     fs_expected := Vlong (Int64.repr ZSTD_FRAMEHEADERSIZE_PREFIX);
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

(* ... then the dictionary content [start, end) referenced as the prefix (ZSTD_refDictContent, after
   ZSTD_decompressBegin): previousDstEnd = end, prefixStart = virtualStart = start, dictEnd = NULL *)
Definition fs_with_dict (fs: fstate) (start fin: val) (gpcopy: Z) (dictID: Z) : fstate :=
  {| fs_previousDstEnd := fin;
     fs_gpDictCopy := Vint (Int.repr gpcopy);
     fs_prefixStart := start;
     fs_virtualStart := start;
     fs_dictEnd := fs_dictEnd fs;
     fs_expected := fs_expected fs;
     fs_fParams := fs_fParams fs;
     fs_processedCSize := fs_processedCSize fs;
     fs_decodedSize := fs_decodedSize fs;
     fs_bType := fs_bType fs;
     fs_stage := fs_stage fs;
     fs_xxh := fs_xxh fs;
     fs_headerSize := fs_headerSize fs;
     fs_validateChecksum := fs_validateChecksum fs;
     fs_rleSize := fs_rleSize fs;
     fs_isFrameDecompression := fs_isFrameDecompression fs;
     fs_dictID := Vint (Int.repr dictID);
     fs_ddictIsCold := fs_ddictIsCold fs |}.

Definition fs_set_dictEnd (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs;
     fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := v;
     fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs;
     fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs;
     fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs;
     fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs;
     fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.

Definition fs_set_cold (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs;
     fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs;
     fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs;
     fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs;
     fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs;
     fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs;
     fs_dictID := fs_dictID fs; fs_ddictIsCold := v |}.

(* the dictionary model of the bytes b given to ZSTD_decompressBegin_usingDict (none: NULL or 0 bytes), as
   zstd loads it (ores: ZSTD_loadDEntropy's result, ld_rel) *)
Definition usingdict_model (dk: val) (b: list Z) (ores: option (dstate * Z)) : option dict_model :=
  if eq_dec dk nullval then Some no_dict
  else if Zlength b =? 0 then Some no_dict else dict_auto_c b ores.

(* ZSTD_decompressBegin_usingDict(dctx, dict, dictSize): dict = dk, NULL (then b = []) or the caller's
   b (by reference, ZSTD_dct_auto).  Fails only on a formatted dictionary zstd cannot load (then the
   model cannot either: ld_rel_auto_none).  On success the
   tables hold the dictionary's entropy state (or the initial one) and the dictionary's content
   [dk + |b| - |content|, dk + |b|) is the prefix.  litExtraBuffer keeps its bytes lxb; the type of the
   Huffman table (x2) is left open (a dictionary's table is X2; no table without entropy). *)
Section B.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition ZSTD_decompressBegin_usingDict_spec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDict
  WITH gv: globals, p: val, fs: fstate, W: list ptr_witness, shk: share, dk: val, b: list Z, lxb: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (readable_share shk; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          dk = nullval /\ b = [] \/ buf_ok W shk (Zlength b) dk)
    PARAMS (p; dk; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p fs; tables_uninit p lxb;
         if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_b p;
         match usingdict_model dk b ores with
         | None => !! (dec_err r) &&
             EX fs': fstate, !! (fs_dictEnd fs' = nullval /\ fs_ddictIsCold fs' = fs_ddictIsCold fs) &&
               frame_fields p fs' * tables_uninit p lxb
         | Some dm =>
             !! (r = 0) &&
             frame_fields p
               (if eq_dec dk nullval then fs_begin fs
                else if Zlength b =? 0 then fs_begin fs
                else fs_with_dict (fs_begin fs) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                       (offset_val (Zlength b) dk) 0 (dm_id dm)) *
             EX x2: bool, TABS gv p None (mk_tstate (dm_state dm) x2 lxb)
         end;
         if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk).

(* the end of a DDict's content (dictContent + dictSize; F12: dictContent itself for 0 bytes, so that the DDict
   without content, buf = NULL, ends at NULL) *)
Definition ddx_end (x: ddx) (buf: val) : val :=
  match buf with Vptr _ _ => offset_val (Zlength (dx_bytes x)) buf | _ => buf end.

Lemma ddx_end_ptr (x: ddx) (buf: val) : isptr buf -> ddx_end x buf = offset_val (Zlength (dx_bytes x)) buf.
Proof. intros Hp. destruct buf; try contradiction. reflexivity. Qed.

Lemma ddx_end_null (x: ddx) : ddx_end x nullval = nullval.
Proof. reflexivity. Qed.

(* the entropy state a context starts a frame with when it uses the DDict x *)
Definition ddx_state (x: ddx) : dstate :=
  match ddx_ent x with Some st => st | None => dstate_init end.

(* ZSTD_decompressBegin_usingDDict(dctx, ddict): ddict = NULL (no dictionary) or the DDict x, whose fields,
   entropy and memory the caller holds.  zstd first compares the context's dictEnd (of its previous
   decoding) with the DDict's end: the laws use one dictionary per context (Spec_api6.dc_last), so dictEnd
   is NULL or that end.  Never fails.  litExtraBuffer keeps its bytes lxb. *)
Definition ZSTD_decompressBegin_usingDDict_spec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin_usingDDict
  WITH gv: globals, p: val, fs: fstate, W: list ptr_witness, ox: option ddx, buf: val, lxb: list Z
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (match ox with
          | None => True
          | Some x =>
              (fs_dictEnd fs = nullval \/ fs_dictEnd fs = ddx_end x buf) /\
              (pws_pred W * ddict_mem x buf |-- weak_valid_pointer (ddx_end x buf))
          end)
    PARAMS (p; match ox with None => nullval | Some x => dx_q x end) GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p fs; tables_uninit p lxb;
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
    SEP (zstd_globals gv; pws_pred W; cfg_b p;
         match ox with
         | None => frame_fields p (fs_begin fs) * TABS gv p None (tstate_begin lxb)
         | Some x =>
             frame_fields p
               (fs_set_dictEnd
                  (fs_with_dict (fs_set_cold (fs_begin fs) cold) buf (ddx_end x buf)
                     (if ddx_copied x then 1 else 0) (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
                  (ddx_end x buf)) *
             TABS gv p ox (mk_tstate (ddx_state x) false lxb) *
             ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf
         end).

(* ---------- the block decoder ---------- *)

(* The previous segment (extDict) of the history, in front of the current one (prefixStart .. dst):
   none; elen bytes ending at e1 in the output array itself (streaming: the ring buffer); or elen bytes
   ending at e1 of a separate array (a dictionary) *)
Inductive ext_seg :=
| ExtNone
| ExtIn (e1 elen: Z)
| ExtSep (sh: share) (eb: val) (en: Z) (ec: list val) (e1 elen: Z).

Definition ext_len (e: ext_seg) : Z :=
  match e with ExtNone => 0 | ExtIn _ l => l | ExtSep _ _ _ _ _ l => l end.

Definition ext_res (e: ext_seg) : mpred :=
  match e with ExtSep sh eb en ec _ _ => data_at sh (tarray tuchar en) ec eb | _ => emp end.

(* The history pointers of the frame fields for a block written at dst = base + d: prefixStart =
   base + ps (ps <= d), virtualStart = prefixStart - elen, dictEnd = the end of the extDict. *)
Definition layout_ok (fs: fstate) (base: val) (N d ps: Z) (e: ext_seg) : Prop :=
  0 <= ps <= d /\ fs_prefixStart fs = offset_val ps base /\
  fs_virtualStart fs = offset_val (ps - ext_len e) base /\ 0 <= ext_len e <= 2 ^ 63 - 1 /\
  match e with
  | ExtNone => True
  | ExtIn e1 elen => fs_dictEnd fs = offset_val e1 base /\ 0 <= e1 - elen /\ e1 <= N
  | ExtSep sh eb en ec e1 elen =>
      fs_dictEnd fs = offset_val e1 eb /\ readable_share sh /\ Zlength ec = en /\
      0 <= e1 - elen /\ e1 <= en /\ en <= 2 ^ 63 - 1
  end.

(* the byte at distance k >= 1 before dst in the history zstd sees: the current segment, then the
   extDict *)
Definition chist (oc: list val) (d ps: Z) (e: ext_seg) (k: Z) : val :=
  if k <=? d - ps then Znth (d - k) oc
  else match e with
       | ExtNone => Vundef
       | ExtIn e1 _ => Znth (e1 - (k - (d - ps))) oc
       | ExtSep _ _ _ ec e1 _ => Znth (e1 - (k - (d - ps))) ec
       end.

(* The model's history hist ++ out (dictionary content, frame output so far) as far as a block may
   reach back (Block.exec_seqs: offset <= wsize + |hist| and <= |hist| + |out|) is what zstd sees. *)
Definition hist_view (oc: list val) (d ps: Z) (e: ext_seg) (hist out: list Z) (wsize: Z) : Prop :=
  let ho := hist ++ out in
  forall k, 1 <= k <= Z.min (Zlength ho) (wsize + Zlength hist) ->
    k <= d - ps + ext_len e /\ chist oc d ps e k = Vint (Int.repr (byte_at ho (Zlength ho - k))).

(* an extDict in the output array (streaming) lies, as far as the window reaches, beyond what a block
   writes: [d, d + min(cap, bsm + WILDCOPY_OVERLENGTH)) *)
Definition ext_clear (d ps cap bsm: Z) (e: ext_seg) (hist out: list Z) (wsize: Z) : Prop :=
  match e with
  | ExtIn e1 _ =>
      forall k, d - ps < k <= Z.min (Zlength (hist ++ out)) (wsize + Zlength hist) ->
        e1 - (k - (d - ps)) >= d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)
  | _ => True
  end.

(* the history zstd may copy from holds defined bytes *)
Definition is_byte_val (v: val) : Prop := exists z, 0 <= z < 256 /\ v = Vint (Int.repr z).
Definition hist_def (oc: list val) (d ps: Z) (e: ext_seg) : Prop :=
  forall k, 1 <= k <= d - ps + ext_len e -> is_byte_val (chist oc d ps e k).

(* an extDict in the output array lies outside what a block may write, overshoot included *)
Definition ext_clean (d cap: Z) (e: ext_seg) : Prop :=
  match e with ExtIn e1 elen => e1 <= d \/ d + cap + WILDCOPY_OVERLENGTH <= e1 - elen | _ => True end.

(* an extDict in the output array beyond what a block of at most bsm bytes writes (zstd's op only grows, so a
   block that returns r <= bsm wrote only [d, d + min(cap, bsm + WILDCOPY_OVERLENGTH)): buffered streaming
   after a ring wrap, where cap is the whole ring) *)
Definition ext_far (d cap bsm: Z) (e: ext_seg) : Prop :=
  match e with ExtIn e1 elen => d + Z.min cap (bsm + WILDCOPY_OVERLENGTH) <= e1 - elen | _ => True end.

(* a separate extDict (a dictionary) holds bytes *)
Definition ext_bytes (e: ext_seg) : Prop :=
  match e with ExtSep _ _ _ ec _ _ => byte_cells ec | _ => True end.

Definition unchanged_outside (oc oc': list val) (lo hi: Z) : Prop :=
  forall i, 0 <= i < Zlength oc -> ~ (lo <= i < hi) -> Znth i oc' = Znth i oc.

(* What a block returns on a block the model decodes: exactly its content and the model's new state, or
   (only) a capacity error. *)
Definition block_ok (ts: dstate) (hist out b: list Z) (bsm wsize: Z) (streaming: Z) (oc oc': list val)
    (d cap r: Z) (ts': option dstate) : Prop :=
  match decode_block ts hist out b bsm wsize with
  | None => True
  | Some (ts2, cnt) =>
      (is_error_code r = false /\ r = Zlength cnt /\ sublist d (d + r) oc' = zbytes cnt /\ bytes_ok cnt /\ ts' = Some ts2 /\
       (streaming = 1 -> unchanged_outside oc oc' d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)))) \/
      (dec_err r /\ cap < Zlength cnt)
  end.

(* the arguments of ZSTD_decompressBlock_internal, grouped: the output array (N cells oc at base, the
   block written at base + d with capacity cap), the input window (the body b at offset off of an array
   of N cells c at base), the history (extDict, prefix start, the model's dictionary content and frame
   output so far, the window size) *)
Record outarr := { oa_sh : share; oa_base : val; oa_N : Z; oa_c : list val; oa_d : Z; oa_cap : Z }.
Record inwin := { iw_sh : share; iw_base : val; iw_N : Z; iw_c : list val; iw_off : Z; iw_s : list Z }.
Record hctx := { hc_ext : ext_seg; hc_ps : Z; hc_hist : list Z; hc_out : list Z; hc_wsize : Z }.

(* the history of h in region coordinates (rb: the region's base in the output array): prefixStart, dictStart,
   dictEnd (no extDict: dictStart = dictEnd); None for an extDict in a separate array (a dictionary) *)
Definition hc_region (h: hctx) (rb: Z) : option (Z * Z * Z) :=
  match hc_ext h with
  | ExtNone => Some (hc_ps h - rb, hc_ps h - rb, hc_ps h - rb)
  | ExtIn e1 elen => Some (hc_ps h - rb, e1 - elen - rb, e1 - rb)
  | ExtSep _ _ _ _ _ _ => None
  end.

Definition outarr_ok (o: outarr) : Prop :=
  writable_share (oa_sh o) /\ Zlength (oa_c o) = oa_N o /\ oa_N o <= 2 ^ 63 - 1 /\
  0 <= oa_d o /\ 0 <= oa_cap o /\ oa_d o + oa_cap o <= oa_N o.

Definition inwin_ok (i: inwin) : Prop :=
  win_ok (iw_sh i) (iw_N i) (iw_c i) (iw_off i) (Zlength (iw_s i)) (iw_s i).

(* the history pointers the sequence decoders load (always, even with cap = 0): prefixStart and
   virtualStart NULL or pointers; dictEnd NULL or weakly valid (into the output array, or the end of a
   separate extDict): ZSTD_prefetchMatch tests `matchBase != NULL` *)
Definition dictend_ok (fs: fstate) (o: outarr) (e: ext_seg) : Prop :=
  fs_dictEnd fs = nullval \/
  (exists k, 0 <= k <= oa_N o /\ fs_dictEnd fs = offset_val k (oa_base o)) \/
  (match e with ExtSep _ eb en _ e1 _ => fs_dictEnd fs = offset_val e1 eb /\ 0 <= e1 <= en | _ => False end).
Definition hist_ptrs_ok (fs: fstate) (o: outarr) (e: ext_seg) : Prop :=
  is_pointer_or_null (fs_prefixStart fs) /\ is_pointer_or_null (fs_virtualStart fs) /\ dictend_ok fs o e.
(* an extDict in a separate array of 0 bytes (a DDict of 0 bytes keeps the caller's pointer, which becomes
   dictEnd after checkContinuity): its end is weakly valid through the caller's witnesses (the Long
   decoder compares dictEnd with NULL); with en > 0, ext_res shows it *)
Definition ext0_ok (W: list ptr_witness) (fs: fstate) (e: ext_seg) : Prop :=
  match e with
  | ExtSep _ _ en _ _ _ => en = 0 -> (pws_pred W |-- weak_valid_pointer (fs_dictEnd fs))
  | _ => True
  end.

(* ZSTD_decompressBlock_internal exactly: model/ExBlock.v's x_block (model/Exact.v's xblock) on the state ts_x ts.
   For any region mem of the output array at offset rb (its cells [rb, rb + |mem|) hold mem; the block is written
   at op = d - rb), starting at or before prefixStart and dictStart, that holds the history zstd's matches may
   read ([prefixStart, op) and an extDict in the output array, hc_region): an error iff the model fails, else the block's size, the region's written cells after the
   block, and the tables' new state. *)
Definition block_exact (ts: tstate) (o: outarr) (i: inwin) (h: hctx) (bsm streaming r: Z) (oc': list val)
    (ts': option tstate) : Prop :=
  forall rb mem ps ds de,
    0 <= rb <= oa_d o -> rb + Zlength mem <= oa_N o -> sublist rb (rb + Zlength mem) (oa_c o) = zbytes mem ->
    hc_region h rb = Some (ps, ds, de) -> 0 <= ps -> 0 <= ds ->
    (forall j, ps <= j < oa_d o - rb \/ ds <= j < de -> 0 <= j < Zlength mem) ->
    match x_block xhuf x_lits_huf ncount_c dseq_one c_offset (ts_x ts) mem ps (oa_d o - rb) ds de
            (iw_s i) bsm (oa_cap o) (streaming =? 1) with
    | None => is_error_code r = true
    | Some (st2, mem2, n) =>
        r = n /\ sublist rb (rb + Zlength mem2) oc' = zbytes mem2 /\ exists ts2, ts' = Some ts2 /\ ts_x ts2 = st2
    end.

(* ZSTD_decompressBlock_internal(dctx, dst, cap, src, n, streaming): the compressed block whose body b
   is the input window i, written at dst = base + d of the output array o with capacity cap.  For ANY b:
   no undefined behaviour, the output array changes only in [d, d + cap), a success is <= cap defined
   bytes.  The correctness clause (block_ok) holds whenever the history zstd sees is the model's
   (hist_view) and, for an extDict in the output array, out of the block's way (ext_clear); with cap = 0
   always (no history is read then).  ts is the tables' state (TABS); after a success the tables hold
   some state (the model's when it decodes b), after an error they are to be reinitialised
   (tables_uninit, litExtraBuffer some bytes).  With the context's own tables (no DDict) the outcome is exact
   (block_exact).  Bytes in, bytes out: when the output and input arrays hold only bytes (FS's calloc'd
   ring and input buffer, contract patch item 17), so does the output array afterwards, success or error
   (zstd copies only bytes; litExtraBuffer holds bytes by tables_uninit/TABS).  Streaming, a success r <= bsm wrote only [d, d + min(cap, bsm + WILDCOPY_OVERLENGTH)) (op only
   grows; the split literal buffer lies below d + min(cap, bsm); not streaming, ZSTD_in_dst puts literals beyond). *)
Definition ZSTD_decompressBlock_internal_spec : ident * funspec :=
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
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p fs; TABS gv p ox ts; dent_of DENT gv ox;
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
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p (fs_set_cold fs cold);
         match ts' with Some ts2 => TABS gv p ox ts2 | None => EX lxb: list Z, tables_uninit p lxb end;
         dent_of DENT gv ox;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)).

(* ---------- DDicts ---------- *)

(* the DDict struct after ZSTD_customMallocP: cMem set by the caller, the rest uninitialised *)
Definition ddict_fresh (q: val) : mpred :=
  let t := Tstruct _ZSTD_DDict_s noattr in
  field_at_ Ews t (DOT _dictBuffer) q * field_at_ Ews t (DOT _dictContent) q *
  field_at_ Ews t (DOT _dictSize) q * field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q * field_at_ Ews t (DOT _entropyPresent) q *
  field_at Ews t (DOT _cMem) cmem_null q.

(* what ZSTD_freeDDict needs of a DDict whose initialisation failed: dictBuffer NULL or a block of
   |b| bytes, the other fields anything *)
Definition ddict_failed (q: val) (n: Z) : mpred :=
  let t := Tstruct _ZSTD_DDict_s noattr in
  EX db: val,
  field_at Ews t (DOT _dictBuffer) db q *
  (if eq_dec db nullval then emp else malloc_token Ews (tarray tuchar n) db * data_at_ Ews (tarray tuchar n) db) *
  field_at_ Ews t (DOT _dictContent) q * field_at_ Ews t (DOT _dictSize) q * field_at_ Ews t (DOT _entropy) q *
  field_at_ Ews t (DOT _dictID) q * field_at_ Ews t (DOT _entropyPresent) q *
  field_at Ews t (DOT _cMem) cmem_null q.

(* ZSTD_initDDict_internal(ddict, dict, dictSize, dictLoadMethod, dictContentType): method 0 = by copy,
   1 = by reference; contentType 0 = auto, 1 = raw content (refPrefix).  A copy of 0 bytes keeps the
   caller's pointer (x has dx_ref = Some p then).  On success the DDict x (ddict_rep without the
   struct's malloc token, which the caller holds); on an error (a corrupted formatted dictionary, or no
   memory for the copy) a DDict the caller frees.  ores: ZSTD_loadDEntropy's result on b (ld_rel). *)
Definition ddx_of (q p: val) (b: list Z) (method ctype: Z) (ores: option (dstate * Z)) : ddx :=
  {| dx_q := q; dx_bytes := b;
     dx_ref := if orb (method =? 1) (Zlength b =? 0) then Some p else None;
     dx_raw := ctype =? 1; dx_ld := ores; dx_mem := None |}.

Definition ZSTD_initDDict_internal_spec : ident * funspec :=
  DECLARE _ZSTD_initDDict_internal
  WITH gv: globals, q: val, W: list ptr_witness, sh: share, pk: val, b: list Z, method: Z, ctype: Z
  PRE [ tptr t_ddict, tptr tvoid, tulong, tint, tint ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b; buf_ok W sh (Zlength b) pk;
          method = 0 \/ method = 1; ctype = 0 \/ ctype = 1; isptr q)
    PARAMS (q; pk; Vlong (Int64.repr (Zlength b)); Vint (Int.repr method); Vint (Int.repr ctype))
    GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; pws_pred W; ddict_fresh q;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores;
          r = 0 \/
          (is_error_code r = true /\
           ((ctype = 0 /\ dict_auto b = None) \/ r = err_code ZSTD_error_memory_allocation)))
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; zstd_globals gv; pws_pred W; data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk;
         if Z.eq_dec r 0
         then let x := ddx_of q pk b method ctype ores in
              EX buf: val, ddict_struct x buf * DENT gv q (ddx_ent x) *
                (if ddx_copied x
                 then malloc_token Ews (tarray tuchar (Zlength b)) buf *
                      data_at Ews (tarray tuchar (Zlength b)) (zbytes b) buf
                 else emp)
         else ddict_failed q (Zlength b)).

(* ZSTD_DDict_dictContent / ZSTD_DDict_dictSize *)
Definition ZSTD_DDict_dictContent_spec : ident * funspec :=
  DECLARE _ZSTD_DDict_dictContent
  WITH x: ddx, buf: val
  PRE [ tptr t_ddict ]
    PROP () PARAMS (dx_q x) SEP (ddict_struct x buf)
  POST [ tptr tvoid ]
    PROP () RETURN (buf) SEP (ddict_struct x buf).

Definition ZSTD_DDict_dictSize_spec : ident * funspec :=
  DECLARE _ZSTD_DDict_dictSize
  WITH x: ddx, buf: val
  PRE [ tptr t_ddict ]
    PROP () PARAMS (dx_q x) SEP (ddict_struct x buf)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Zlength (dx_bytes x)))) SEP (ddict_struct x buf).

Definition B_exports : funspecs :=
  [ ZSTD_decompressBegin_usingDict_spec; ZSTD_decompressBegin_usingDDict_spec;
    ZSTD_decompressBlock_internal_spec; ZSTD_initDDict_internal_spec;
    ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec ].

End B.
