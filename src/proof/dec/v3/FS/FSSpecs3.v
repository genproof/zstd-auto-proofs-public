(* Subtree FS of the decoder, API v3: the shared internal specifications, fixed for every
   FS3 part.

   The first part is v2's FSSpecs (definitions and the specifications that did not change, same names; v2's
   FSSpecs.v no longer compiles against Spec_api6 v3).  The second part states the specifications v3 changes
   or adds, suffixed 3: the parameters (fgroup3/fcore3/ctx_rep3), the DDict set (hset_rep, set_ids) and the
   frame's dictionary selection (ZSTD_DCtx_selectFrameDDict, inside ZSTD_decodeFrameHeader).
   Specifications chosen by parts (FSOblig3): ZSTD_decompressFrame (frames part), the 13 streaming helpers
   (streaming part), the hash set's getIndex/emplaceDDict/expand (set part); the buffer-less part proves
   ZSTD_decompressContinue / nextSrcSizeToDecompress / nextInputType against their API specifications. *)
Require Export Zstd.proof.dec.v3.FS.FSRep3.
Require Export Zstd.proof.zstd.Spec_codes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame.
Local Open Scope logic.

(* ---------- the initial context (ZSTD_createDCtx) ---------- *)

Definition fs0 : fstate :=
  {| fs_previousDstEnd := Vundef; fs_gpDictCopy := Vundef; fs_prefixStart := Vundef;
     fs_virtualStart := Vundef; fs_dictEnd := nullval; fs_expected := Vundef;
     fs_fParams := fh_val fh_zero; fs_processedCSize := Vundef; fs_decodedSize := Vundef;
     fs_bType := Vundef; fs_stage := Vundef; fs_xxh := None; fs_headerSize := Vundef;
     fs_validateChecksum := Vundef; fs_rleSize := Vundef; fs_isFrameDecompression := Vint (Int.repr 1);
     fs_dictID := Vundef; fs_ddictIsCold := Vint (Int.repr 0) |}.

Definition s0 : sfields :=
  {| sf_stage := 0; sf_inBuff := nullval; sf_inSize := 0; sf_inPos := Vundef; sf_outBuff := Vundef;
     sf_outSize := 0; sf_outStart := Vundef; sf_outEnd := Vundef; sf_lhSize := Vundef;
     sf_hostage := Vundef; sf_nfp := 0; sf_expOut := default_val t_outBuffer;
     sf_hbuf := default_val (tarray tuchar 18); sf_over := 0; sf_ring := nil; sf_mem := None; sf_held := 0 |}.

Definition k0 : cst :=
  {| c_fs := fs0; c_tabs := None; c_stable := false; c_dict := df_none; c_s := s0 |}.

(* the seven parameters ZSTD_DCtx_resetParameters sets *)
Definition params_ (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _format) p * field_at_ Ews t_dctx (DOT _maxWindowSize) p *
  field_at_ Ews t_dctx (DOT _outBufferMode) p * field_at_ Ews t_dctx (DOT _forceIgnoreChecksum) p *
  field_at_ Ews t_dctx (DOT _refMultipleDDicts) p * field_at_ Ews t_dctx (DOT _disableHufAsm) p *
  field_at_ Ews t_dctx (DOT _maxBlockSizeParam) p.

Definition params0 (p: val) : mpred :=
  field_at Ews t_dctx (DOT _format) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr ZSTD_MAXWINDOWSIZE_DEFAULT)) p *
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _disableHufAsm) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr 0)) p.

(* ---------- frame-level helpers ---------- *)

(* ZSTD_checkContinuity: does the output start a new segment? *)
Definition cont_moves (fs: fstate) (dst: val) (n: Z) : bool :=
  andb (0 <? n) (orb (negb (veqb (fs_gpDictCopy fs) (Vint (Int.repr 0)))) (negb (veqb dst (fs_previousDstEnd fs)))).

Definition continuity (fs: fstate) (dst: val) (n: Z) : fstate :=
  if cont_moves fs dst n then
    let pde := fs_previousDstEnd fs in
    fsu_gpDictCopy
      (fsu_previousDstEnd
         (fsu_prefixStart
            (fsu_virtualStart (fsu_dictEnd fs pde)
               (offset_val (- (if veqb pde nullval then 0 else vptr_diff pde (fs_prefixStart fs))) dst))
            dst)
         dst)
      (Vint (Int.repr 0))
  else fs.

(* ZSTD_decodeFrameHeader on the header bytes s, with the context's dictID did and processedCSize pcs *)
Definition dfh_post (fs: fstate) (did pcs: Z) (s: list Z) (r: Z) (fs': fstate) : Prop :=
  match get_frame_header s with
  | FH_ok h =>
      if orb (fh_dictID h =? 0) (fh_dictID h =? did) then
        r = 0 /\
        fs' = fsu_processedCSize
                (fsu_xxh
                   (fsu_validateChecksum (fsu_fParams fs (fh_val h)) (Vint (Int.repr (fh_checksumFlag h))))
                   (if fh_checksumFlag h =? 1 then Some nil else fs_xxh fs))
                (Vlong (Int64.repr (pcs + Zlength s)))
      else dec_err r /\ fs' = fsu_fParams fs (fh_val h)
  | _ => dec_err r /\ exists v, fs' = fsu_fParams fs v
  end.

(* the frame group without the tables (what ZSTD_decodeFrameHeader touches) *)
Definition fcore (p: val) (fs: fstate) : mpred :=
  cfg_b p * frame_fields p fs *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

(* ZSTD_getDDict: the DDict returned and the new dictionary fields *)
Definition df_set_uses (d: dfields) (u: Z) : dfields :=
  {| df_local := df_local d; df_ddict := df_ddict d; df_uses := u; df_lx := df_lx d |}.

Definition getddict_res (d: dfields) : val * dfields :=
  if df_uses d =? 0 then (nullval, df_none)
  else if df_uses d =? 1 then (df_ddict d, df_set_uses d 0)
  else (df_ddict d, d).

(* ZSTD_DCtx_loadDictionary_advanced(dctx, pk, |b|, method, ctype): the new dictionary fields *)
Definition load_res (pk: val) (b: list Z) (method ctype r: Z) (d': dfields) : Prop :=
  if Zlength b =? 0 then r = 0 /\ d' = df_none
  else (r = 0 /\ exists q buf ores, isptr q /\ (method = 1 -> buf = pk) /\
          d' = {| df_local := q; df_ddict := q; df_uses := -1;
                  df_lx := Some (ddx_of q pk b method ctype ores, buf) |}) \/
       (r = err_code ZSTD_error_memory_allocation /\ d' = df_none).

Definition ddict_ref_fields (q: val) : dfields :=
  {| df_local := nullval; df_ddict := q; df_uses := -1; df_lx := None |}.

(* ---------- the dictionary argument of ZSTD_decompressMultiFrame ---------- *)

(* none (dict NULL, ddict NULL), the caller's bytes b at pk (ZSTD_decompress_usingDict), or the DDict x
   whose content is at buf (sh: the share of the caller's bytes when x refers to them) *)
Inductive darg :=
| DA_none
| DA_dict (sh: share) (pk: val) (b: list Z)
| DA_ddict (x: ddx) (buf: val) (sh: share).

Definition darg_dict (a: darg) : val := match a with DA_dict _ pk _ => pk | _ => nullval end.
Definition darg_size (a: darg) : Z := match a with DA_dict _ _ b => Zlength b | _ => 0 end.
Definition darg_ddict (a: darg) : val := match a with DA_ddict x _ _ => dx_q x | _ => nullval end.

Definition darg_model (a: darg) : option dict_model :=
  match a with
  | DA_none => Some no_dict
  | DA_dict _ _ b => dict_auto b
  | DA_ddict x _ _ => ddx_model x
  end.

(* the end of the dictionary content (what dictEnd may become; none for 0 bytes given to usingDict) *)
Definition darg_end (a: darg) : val :=
  match a with
  | DA_none => nullval
  | DA_dict _ pk b => if Zlength b =? 0 then nullval else offset_val (Zlength b) pk
  | DA_ddict x buf _ => ddx_end x buf
  end.

(* the conditions on the dictionary: as for the API (Spec_api6.dict_ptr_ok for the caller's bytes),
   and for a DDict the context's dictEnd is NULL or this DDict's end *)
Definition darg_ok (W: list ptr_witness) (fs: fstate) (a: darg) (shd: share) (cap: Z) (dst: val) : Prop :=
  match a with
  | DA_none => True
  | DA_dict sh pk b =>
      readable_share sh /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\ dict_ptr_ok W sh (Zlength b) pk shd cap dst
  | DA_ddict x buf sh =>
      (fs_dictEnd fs = nullval \/ fs_dictEnd fs = ddx_end x buf) /\
      (ddx_copied x = false -> readable_share sh /\ dict_ptr_ok W sh (Zlength (dx_bytes x)) buf shd cap dst)
  end.

Definition darg_is_ddict (a: darg) : Prop := match a with DA_dict _ _ _ => False | _ => True end.

(* At cap = 0 ZSTD_checkContinuity (patched: dstSize first) compares nothing, so a
   by-reference 0-byte dictionary at a valid pointer is enough (the stream's shortcut with dst one past the end) *)
Definition dict_ptr_ok0 (W: list ptr_witness) (sh: share) (n: Z) (p: val) (shd: share) (cap: Z) (dst: val) : Prop :=
  dict_ptr_ok W sh n p shd cap dst \/ (cap = 0 /\ n = 0 /\ (pws_pred W |-- valid_pointer p)).

Definition ddict_buf_ok0 (W: list ptr_witness) (sh: share) (dd: ddict_st) (shd: share) (cap: Z) (dst: val) : Prop :=
  match dd_ref dd with Some p => dict_ptr_ok0 W sh (Zlength (dd_bytes dd)) p shd cap dst | None => True end.

(* v3: no condition on the context's dictEnd (ZSTD_decompressBegin_usingDDict no longer compares it); the caller's
   bytes as for ZSTD_decompress_usingDict (Spec_api6.dict_ptr_ok_any: also before dst, possibly as its prefix); none
   for the DDict without content (buf = NULL) *)
Definition darg_ok3 (W: list ptr_witness) (a: darg) (shd: share) (cap: Z) (dst: val) : Prop :=
  match a with
  | DA_none => True
  | DA_dict sh pk b =>
      readable_share sh /\ Zlength b <= 2 ^ 63 - 1 /\ bytes_ok b /\ dict_ptr_ok_any W sh (Zlength b) pk shd cap dst
  | DA_ddict x buf sh =>
      ddx_copied x = false -> buf <> nullval ->
      readable_share sh /\ dict_ptr_ok0 W sh (Zlength (dx_bytes x)) buf shd cap dst
  end.

(* ---------- v3: the DDict set and the dictionary selection ---------- *)

(* what zstd's hash set reads of a DDict q: its dictID field (a 32-bit value id), and, since zstd tests the pointer
   against NULL, its first field dictBuffer (offset 0: weak validity of q) with its exact value db *)
Definition ddid (q: val) (id: Z) (db: val) : mpred :=
  !! (0 <= id <= Int.max_unsigned) &&
  (field_at Ews t_ddict (DOT _dictBuffer) db q * field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr id)) q).

(* the dictBuffer field of a DDict described by dd (DD3_of): zstd's copy, or NULL by reference or without content *)
Definition ddb (dd: ddict_st) : val := match dd_xref dd with None => dd_buf dd | Some _ => nullval end.

Definition set_ids (l: list (val * ddict_st)) : mpred :=
  fold_right sepcon emp (map (fun e => ddid (fst e) (dd_id (snd e)) (ddb (snd e))) l).

(* ZSTD_getDictID_fromDDict on NULL or what the hash set holds of a DDict (internal; the API spec follows) *)
Definition ZSTD_getDictID_fromDDict_int_spec : ident * funspec :=
  DECLARE _ZSTD_getDictID_fromDDict
  WITH q: val, id: Z, db: val
  PRE [ tptr t_ddict ]
    PROP () PARAMS (q)
    SEP (if eq_dec q nullval then emp else ddid q id db)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if eq_dec q nullval then 0 else id)))
    SEP (if eq_dec q nullval then emp else ddid q id db).

Section HSetViews.
Context {CMI: cmem_preds}.

(* the set struct at sp (non-NULL) with the table tbl, any number of DDicts (a fresh set holds none), allocated
   through the context's allocator am *)
Definition hset_tbl (am: option cmem) (sp: val) (l: list (val * ddict_st)) (tbl: list val) : mpred :=
  EX tp: val,
  !! (hs_inv l tbl) &&
  (blk_tok am t_hset sp *
   data_at Ews t_hset (tp, (Vlong (Int64.repr (Zlength tbl)), Vlong (Int64.repr (Zlength l)))) sp *
   hs_table am tp tbl).

(* ... holding hb bytes of am (FSRep3.set_bytes) *)
Definition hset_at (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) : mpred :=
  EX tbl: list val, !! (hb = set_bytes am (Zlength tbl)) && hset_tbl am sp l tbl.

Lemma hset_rep_at (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hb: Z) :
  sp <> nullval -> hset_rep am sp l hb = !! (l <> nil) && hset_at am sp l hb.
Proof.
  intros H. unfold hset_rep, hset_at, hset_tbl. destruct (eq_dec sp nullval); [contradiction |].
  apply pred_ext.
  - Intros tp tbl. Exists tbl tp. entailer!.
  - Intros tbl tp. Exists tp tbl. entailer!.
Qed.

End HSetViews.

(* the bytes a set's expansion may allocate next to the set of hb bytes of an own allocator: the doubled table *)
Definition set_grow (hb: Z) : Z := Z.max 0 (2 * (hb - sizeof t_hset)).

(* the bytes of a new set (ZSTD_createDDictHashSet: the struct and a table of DDICT_HASHSET_TABLE_BASE_SIZE = 64) *)
Definition set_new_bytes : Z := sizeof t_hset + 8 * 64.

(* ZSTD_DDictHashSet_getDDict's probe: from the home slot of id, the first slot that is NULL or holds a DDict of
   ID id or of ID 0 (getDictID_fromDDict(NULL) = 0); the table always has a NULL slot (hs_inv), so n steps end it *)
Definition set_id_of (l: list (val * ddict_st)) (v: val) : Z :=
  match find (fun e => veqb (fst e) v) l with Some e => dd_id (snd e) | None => 0 end.

Fixpoint hs_probe_f (fuel: nat) (l: list (val * ddict_st)) (tbl: list val) (j n id: Z) : val :=
  match fuel with
  | O => nullval
  | S f =>
      let v := Znth j tbl in
      if eq_dec v nullval then nullval
      else if orb (set_id_of l v =? id) (set_id_of l v =? 0) then v
      else hs_probe_f f l tbl ((j + 1) mod n) n id
  end.

Definition hs_probe (l: list (val * ddict_st)) (tbl: list val) (id: Z) : val :=
  hs_probe_f (Z.to_nat (Zlength tbl)) l tbl (hs_home id (Zlength tbl)) (Zlength tbl) id.

(* what the probe means (to be proved by the set part): NULL or a DDict of the set; with non-zero IDs, the DDict
   of the ID (set_find) *)
Definition set_lookup (l: list (val * ddict_st)) (id: Z) (r: val) : Prop :=
  (r = nullval \/ In r (map fst l)) /\
  (Forall (fun e => dd_id (snd e) <> 0) l -> r = set_find l id).

Definition hs_probe_ok : Prop :=
  forall l tbl id, hs_inv l tbl -> 0 <= id <= Int.max_unsigned -> set_lookup l id (hs_probe l tbl id).


(* ZSTD_DCtx_selectFrameDDict: no DDict (dctx->ddict NULL) means no lookup *)
Definition sel_r (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (id: Z) : val :=
  if eq_dec (df_ddict d) nullval then nullval else hs_probe l tbl id.

(* the dictionary fields after selecting the DDict r (NULL: none found, unchanged) *)
Definition switch_fields (r: val) : dfields := {| df_local := nullval; df_ddict := r; df_uses := -1; df_lx := None |}.

Definition sel_dict (d: dfields) (r: val) : dfields := if eq_dec r nullval then d else switch_fields r.

(* whether ZSTD_decodeFrameHeader selects (refMultipleDDicts and a set) *)
Definition sel_on (pr: dparams) (sp: val) : bool := andb (dp_multi pr =? 1) (negb (veqb sp nullval)).

(* the current DDict, tested against NULL: none, the local one (in dgroup), one of the set, or a caller's DDict q
   whose first field (dictBuffer, value v) the caller lends (xq = Some (q, v)) *)
Definition opt_token (xq: option (val * val)) : mpred :=
  match xq with Some (q, v) => field_at Ews t_ddict (DOT _dictBuffer) v q | None => emp end.

Definition cur_ok (d: dfields) (l: list (val * ddict_st)) (xq: option (val * val)) : Prop :=
  (df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1) /\
  (df_ddict d = nullval \/ df_ddict d = df_local d \/ In (df_ddict d) (map fst l) \/
   exists v, xq = Some (df_ddict d, v)).

(* the frame header ZSTD_decodeFrameHeader decodes: the header bytes s, the context's dictID did and processedCSize
   pcs, the format and checksum policy of md; with the selection (sel), the DDict rq found for the frame's
   Dictionary_ID (NULL: none) becomes the context's, and its ID the context's dictID *)
Definition dfh_post3 (md: dmode) (sel: bool) (d: dfields) (l: list (val * ddict_st)) (tbl: list val)
    (fs: fstate) (did pcs: Z) (s: list Z) (r: Z) (fs': fstate) (d': dfields) : Prop :=
  match get_frame_header_m (md_magicless md) s with
  | FH_ok h =>
      let rq := if sel then sel_r d l tbl (fh_dictID h) else nullval in
      let did' := if eq_dec rq nullval then did else fh_dictID h in
      let fs1 := fsu_dictID (fsu_fParams fs (fh_val h)) (Vint (Int.repr did')) in
      let v := andb (fh_checksumFlag h =? 1) (negb (md_ignore md)) in
      d' = sel_dict d rq /\
      if orb (fh_dictID h =? 0) (fh_dictID h =? did') then
        r = 0 /\
        fs' = fsu_processedCSize
                (fsu_xxh (fsu_validateChecksum fs1 (Vint (Int.repr (if v then 1 else 0))))
                   (if v then Some nil else fs_xxh fs))
                (Vlong (Int64.repr (pcs + Zlength s)))
      else dec_err r /\ fs' = fs1
  | _ => dec_err r /\ d' = d /\
         exists v, fs' = fsu_fParams fs v /\ (v = fs_fParams fs \/ fp_dictID v = Vint (Int.repr 0))
  end.

(* the parameters ZSTD_DCtx_setParameter / ZSTD_dParam_getBounds know, and their bounds *)
Definition dparam_known (k: Z) : Prop :=
  In k [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_stableOutBuffer; ZSTD_d_forceIgnoreChecksum;
        ZSTD_d_refMultipleDDicts; ZSTD_d_maxBlockSize].

Definition dparam_bounds (k: Z) : Z * Z :=
  if k =? ZSTD_d_windowLogMax then (10, 31)
  else if k =? ZSTD_d_maxBlockSize then (1024, ZSTD_BLOCKSIZE_MAX)
  else (0, 1).

(* ZSTD_DCtx_loadDictionary_advanced(dctx, pk, |b|, method, ctype): the new dictionary fields (ctype 2 =
   fullDict: a success has the magic number) *)
Definition load_res3 (am: option cmem) (pk: val) (b: list Z) (method ctype r: Z) (d': dfields) : Prop :=
  if Zlength b =? 0 then r = 0 /\ d' = df_none
  else (r = 0 /\ (ctype = 2 -> dict_formatted b = true) /\
        exists q buf ores, isptr q /\ (method = 1 -> buf = pk) /\
          d' = {| df_local := q; df_ddict := q; df_uses := -1;
                  df_lx := Some (ddx_of3 am q pk b method ctype ores, buf) |}) \/
       (r = err_code ZSTD_error_memory_allocation /\ d' = df_none).

(* ZSTD_DCtx_refDDict(dctx, q) with refMultipleDDicts = multi: the set pointer and set after it *)
Definition refddict_res3 (multi: Z) (sp: val) (l: list (val * ddict_st)) (q: val) (dd: ddict_st)
    (r: Z) (sp': val) (l': list (val * ddict_st)) : Prop :=
  if orb (veqb q nullval) (negb (multi =? 1)) then r = 0 /\ sp' = sp /\ l' = l
  else (r = 0 /\ l' = set_add l q dd /\ (sp <> nullval -> sp' = sp)) \/
       (is_error_code r = true /\ sp' = sp /\ l' = l).

(* the fields of a calloc'd context but customMem and fParams (fParams: the calloc's zero header) *)
Definition dctx_fields_nofp (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _LLTptr) p *
  field_at_ Ews t_dctx (DOT _MLTptr) p *
  field_at_ Ews t_dctx (DOT _OFTptr) p *
  field_at_ Ews t_dctx (DOT _HUFptr) p *
  field_at_ Ews t_dctx (DOT _entropy) p *
  field_at_ Ews t_dctx (DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _previousDstEnd) p *
  field_at_ Ews t_dctx (DOT _gpDictCopy) p *
  field_at_ Ews t_dctx (DOT _prefixStart) p *
  field_at_ Ews t_dctx (DOT _virtualStart) p *
  field_at_ Ews t_dctx (DOT _dictEnd) p *
  field_at_ Ews t_dctx (DOT _expected) p *
  field_at_ Ews t_dctx (DOT _processedCSize) p *
  field_at_ Ews t_dctx (DOT _decodedSize) p *
  field_at_ Ews t_dctx (DOT _bType) p *
  field_at_ Ews t_dctx (DOT _stage) p *
  field_at_ Ews t_dctx (DOT _litEntropy) p *
  field_at_ Ews t_dctx (DOT _fseEntropy) p *
  field_at_ Ews t_dctx (DOT _xxhState) p *
  field_at_ Ews t_dctx (DOT _headerSize) p *
  field_at_ Ews t_dctx (DOT _format) p *
  field_at_ Ews t_dctx (DOT _forceIgnoreChecksum) p *
  field_at_ Ews t_dctx (DOT _validateChecksum) p *
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _rleSize) p *
  field_at_ Ews t_dctx (DOT _staticSize) p *
  field_at_ Ews t_dctx (DOT _isFrameDecompression) p *
  field_at_ Ews t_dctx (DOT _ddictLocal) p *
  field_at_ Ews t_dctx (DOT _ddict) p *
  field_at_ Ews t_dctx (DOT _dictID) p *
  field_at_ Ews t_dctx (DOT _ddictIsCold) p *
  field_at_ Ews t_dctx (DOT _dictUses) p *
  field_at_ Ews t_dctx (DOT _ddictSet) p *
  field_at_ Ews t_dctx (DOT _refMultipleDDicts) p *
  field_at_ Ews t_dctx (DOT _disableHufAsm) p *
  field_at_ Ews t_dctx (DOT _maxBlockSizeParam) p *
  field_at_ Ews t_dctx (DOT _streamStage) p *
  field_at_ Ews t_dctx (DOT _inBuff) p *
  field_at_ Ews t_dctx (DOT _inBuffSize) p *
  field_at_ Ews t_dctx (DOT _inPos) p *
  field_at_ Ews t_dctx (DOT _maxWindowSize) p *
  field_at_ Ews t_dctx (DOT _outBuff) p *
  field_at_ Ews t_dctx (DOT _outBuffSize) p *
  field_at_ Ews t_dctx (DOT _outStart) p *
  field_at_ Ews t_dctx (DOT _outEnd) p *
  field_at_ Ews t_dctx (DOT _lhSize) p *
  field_at_ Ews t_dctx (DOT _hostageByte) p *
  field_at_ Ews t_dctx (DOT _noForwardProgress) p *
  field_at_ Ews t_dctx (DOT _outBufferMode) p *
  field_at_ Ews t_dctx (DOT _expectedOutBuffer) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_at p lxb_zero *
  field_at_ Ews t_dctx (DOT _headerBuffer) p *
  field_at_ Ews t_dctx (DOT _oversizedDuration) p.

(* the initial concrete state (ZSTD_createDCtx): v2's k0 with the default parameters, no set *)
Definition k03 : cst3 :=
  {| c3_fs := fs0; c3_tabs := TUninit lxb_zero; c3_stable := false; c3_dict := df_none; c3_s := s0;
     c3_par := dparams_dflt; c3_sp := nullval; c3_set := nil |}.

(* ... allocated by am (k03m None = k03) *)
Definition k03m (am: option cmem) : cst3 := c3_with_s k03 (sf_with_mem s0 am).

Lemma k03m_none : k03m None = k03.
Proof. reflexivity. Qed.

Section Specs.
Context {CMI: cmem_preds}.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition darg_res (gv: globals) (a: darg) : mpred :=
  match a with
  | DA_none => emp
  | DA_dict sh pk b => data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk
  | DA_ddict x buf sh =>
      ddict_rep_at DENT gv x buf * (if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf)
  end.

(* ===================== DDicts ===================== *)

(* any DDict of the allocator am that ZSTD_freeDDict can free (a live one, or one whose initialisation failed),
   holding a copy of nb bytes (0: none) besides its struct *)
Definition ddict_any3 (am: option cmem) (q: val) (nb: Z) : mpred :=
  EX n: Z, ddict_failed3 am q n nb * ddict_pad q * blk_tok am t_ddict q.

(* ZSTD_freeDDict on NULL or any DDict of the allocator am (it frees through the DDict's cMem), which has given out
   h bytes (internal; implies the API specification, am = None) *)
Definition ZSTD_freeDDict_int_spec : ident * funspec :=
  DECLARE _ZSTD_freeDDict
  WITH gv: globals, q: val, am: option cmem, h: Z, nb: Z
  PRE [ tptr t_ddict ]
    PROP (cmem_ok am; q <> nullval -> am <> None -> 0 <= nb /\ sizeof t_ddict + nb <= h)
    PARAMS (q) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; cm_have am h; if eq_dec q nullval then emp else ddict_any3 am q nb)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (mem_mgr gv; zstd_globals gv; cm_have am (if eq_dec q nullval then h else h - (sizeof t_ddict + nb))).

(* ===================== contexts ===================== *)

Definition ZSTD_DCtx_resetParameters_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_resetParameters
  WITH p: val
  PRE [ tptr t_dctx ]
    PROP () PARAMS (p) SEP (params_ p)
  POST [ tvoid ]
    PROP () RETURN () SEP (params0 p).

(* frees the local DDict, which the context's allocator am gave out (its bytes: FSRepC.local_held), if own *)
Definition ZSTD_clearDict_spec : ident * funspec :=
  DECLARE _ZSTD_clearDict
  WITH gv: globals, p: val, d: dfields, am: option cmem, hb: Z
  PRE [ tptr t_dctx ]
    PROP (local_mem am d; cmem_ok am; 0 <= hb) PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; dgroup DENT gv p d; cm_have am (hb + local_held d))
  POST [ tvoid ]
    PROP () RETURN () SEP (mem_mgr gv; zstd_globals gv; dgroup DENT gv p df_none; cm_have am hb).

(* with no use left, zstd clears the dictionary (ZSTD_clearDict: the local DDict freed through the context's
   allocator am, which has given out hb bytes besides it) *)
Definition ZSTD_getDDict_spec : ident * funspec :=
  DECLARE _ZSTD_getDDict
  WITH gv: globals, p: val, d: dfields, am: option cmem, hb: Z
  PRE [ tptr t_dctx ]
    PROP (df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1; df_uses d <> 0 -> is_pointer_or_null (df_ddict d);
          local_mem am d; cmem_ok am; 0 <= hb)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; dgroup DENT gv p d; cm_have am (hb + local_held d))
  POST [ tptr t_ddict ]
    PROP () RETURN (fst (getddict_res d))
    SEP (mem_mgr gv; zstd_globals gv; dgroup DENT gv p (snd (getddict_res d));
         cm_have am (hb + local_held (snd (getddict_res d)))).

(* ===================== dictionary loading ===================== *)

(* ===================== frames: shared by one-shot and streaming decoding ===================== *)

Definition ZSTD_DCtx_trace_end_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_trace_end
  WITH p: val, a: Z, b: Z, s: Z
  PRE [ tptr t_dctx, tulong, tulong, tint ]
    PROP () PARAMS (p; Vlong (Int64.repr a); Vlong (Int64.repr b); Vint (Int.repr s)) SEP ()
  POST [ tvoid ]
    PROP () RETURN () SEP ().

(* ZSTD_checkContinuity(dctx, dst, n) (the contract's code tests n > 0 first): the comparison
   dst != previousDstEnd (made when n > 0 and gpDictCopy = 0) needs W; the new segment computes
   previousDstEnd - prefixStart and dst - that *)
Definition ZSTD_checkContinuity_spec : ident * funspec :=
  DECLARE _ZSTD_checkContinuity
  WITH p: val, fs: fstate, W: list ptr_witness, dst: val, n: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (0 <= n <= Int64.max_unsigned;
          fs_gpDictCopy fs = Vint (Int.repr 0) \/ fs_gpDictCopy fs = Vint (Int.repr 1);
          0 < n -> fs_gpDictCopy fs = Vint (Int.repr 0) ->
            (pws_pred W |-- denote_tc_test_eq dst (fs_previousDstEnd fs));
          cont_moves fs dst n = true ->
            isptr dst /\ (pws_pred W |-- denote_tc_test_eq (fs_previousDstEnd fs) nullval) /\
            (fs_previousDstEnd fs <> nullval -> sameblock (fs_previousDstEnd fs) (fs_prefixStart fs) = true))
    PARAMS (p; dst; Vlong (Int64.repr n))
    SEP (pws_pred W; frame_fields p fs)
  POST [ tvoid ]
    PROP () RETURN () SEP (pws_pred W; frame_fields p (continuity fs dst n)).

(* a raw block: the window i copied at the output o (separate arrays) *)
Definition ZSTD_copyRawBlock_spec : ident * funspec :=
  DECLARE _ZSTD_copyRawBlock
  WITH W: list ptr_witness, o: outarr, i: inwin
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (outarr_ok o; inwin_ok i;
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o))))
    PARAMS (offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o));
            offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i))))
    SEP (pws_pred W; data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i))
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned;
          if Zlength (iw_s i) >? oa_cap o then r = err_code ZSTD_error_dstSize_tooSmall /\ oc' = oa_c o
          else r = Zlength (iw_s i) /\ oc' = put_bytes (oa_c o) (oa_d o) (iw_s i))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)).

(* an RLE block: n copies of the byte b *)
Definition ZSTD_setRleBlock_spec : ident * funspec :=
  DECLARE _ZSTD_setRleBlock
  WITH W: list ptr_witness, o: outarr, b: Z, n: Z
  PRE [ tptr tvoid, tulong, tuchar, tulong ]
    PROP (outarr_ok o; 0 <= b <= Byte.max_unsigned; 0 <= n <= Int64.max_unsigned;
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o))))
    PARAMS (offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o)); Vint (Int.repr b);
            Vlong (Int64.repr n))
    SEP (pws_pred W; data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o))
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned;
          if n >? oa_cap o then r = err_code ZSTD_error_dstSize_tooSmall /\ oc' = oa_c o
          else r = n /\ oc' = put_bytes (oa_c o) (oa_d o) (Zrepeat b n))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o)).

(* ===================== one-shot decoding ===================== *)


(* ===================================================================================
   v3 specifications
   =================================================================================== *)

(* the selection's resources: with refMultipleDDicts and a set (sel_on), ZSTD_decodeFrameHeader may free the
   local DDict (mem_mgr, and the context's allocator am with hb bytes given out besides the local DDict), reads and
   changes the dictionary fields (dgroup), the set (hset_tbl), the IDs of the set's DDicts (set_ids) and tests the
   current DDict (opt_token) *)
Definition sel_res (gv: globals) (p: val) (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st))
    (tbl: list val) (xq: option (val * val)) (am: option cmem) (hb: Z) : mpred :=
  if sel_on pr sp
  then mem_mgr gv * dgroup DENT gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl * set_ids l *
       opt_token xq
  else emp.

(* what the selection's free needs of the allocator *)
Definition sel_mem (pr: dparams) (sp: val) (d: dfields) (am: option cmem) (hb: Z) : Prop :=
  sel_on pr sp = true -> local_mem am d /\ cmem_ok am /\ 0 <= hb.

(* ZSTD_createDDict_advancedP with a content type 0 auto, 1 raw content, 2 fullDict (a DDict of type 2 has the
   magic number) *)
(* ... through the allocator am at pm (the default one, or a context's own: ZSTD_DCtx_loadDictionary_advanced passes
   &dctx->customMem), which has given out h bytes: the DDict remembers it (dx_mem) and holds ddx_held of it; the
   bytes may be NULL for none (ZSTD_createDDict(NULL, 0): a DDict without content, ZSTD_initDDict_internal_spec3) *)
Definition ZSTD_createDDict_advancedP_spec3 : ident * funspec :=
  DECLARE _ZSTD_createDDict_advancedP
  WITH W: list ptr_witness, gv: globals, sh: share, pk: val, b: list Z, method: Z, ctype: Z,
       shm: share, pm: val, am: option cmem, h: Z
  PRE [ tptr tvoid, tulong, tint, tint, tptr t_cmem ]
    PROP (readable_share sh; readable_share shm; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          is_pointer_or_null pk; pk = nullval -> b = nil; pk <> nullval -> buf_ok W sh (Zlength b) pk;
          method = 0 \/ method = 1; ctype = 0 \/ ctype = 1 \/ ctype = 2;
          cmem_ok am; cm_room am h (sizeof t_ddict + Zlength b))
    PARAMS (pk; Vlong (Int64.repr (Zlength b)); Vint (Int.repr method); Vint (Int.repr ctype); pm)
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h;
         bytes_at sh b pk)
  POST [ tptr t_ddict ]
    EX q: val,
    PROP (is_pointer_or_null q)
    RETURN (q)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; data_at shm t_cmem (cmem_v am) pm;
         bytes_at sh b pk;
         if eq_dec q nullval then cm_have am h
         else EX buf: val, EX ores: option (dstate * Z),
              !! (ctype = 2 -> dict_formatted b = true) &&
              (ddict_rep_at DENT gv (ddx_of3 am q pk b method ctype ores) buf *
               cm_have am (h + ddx_held (ddx_of3 am q pk b method ctype ores)))).

(* ----- the DDict hash set (the set part proves these; it chooses the specifications of getIndex, emplaceDDict,
   expand) ----- *)

(* the set's blocks go through the context's allocator am at pm, which has given out h bytes *)
Definition ZSTD_createDDictHashSet_spec : ident * funspec :=
  DECLARE _ZSTD_createDDictHashSet
  WITH gv: globals, shm: share, pm: val, am: option cmem, h: Z
  PRE [ tptr t_cmem ]
    PROP (readable_share shm; cmem_ok am; cm_room am h set_new_bytes) PARAMS (pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h)
  POST [ tptr t_hset ]
    EX sp: val,
    PROP (is_pointer_or_null sp) RETURN (sp)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
         if eq_dec sp nullval then cm_have am h
         else hset_at am sp nil (set_bytes am 64) * cm_have am (h + set_bytes am 64)).

Definition ZSTD_freeDDictHashSet_spec : ident * funspec :=
  DECLARE _ZSTD_freeDDictHashSet
  WITH gv: globals, sp: val, l: list (val * ddict_st), shm: share, pm: val, am: option cmem, h: Z, hb: Z
  PRE [ tptr t_hset, tptr t_cmem ]
    PROP (readable_share shm; cmem_ok am; sp <> nullval -> hb <= h) PARAMS (sp; pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h;
         if eq_dec sp nullval then emp else hset_at am sp l hb)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (if eq_dec sp nullval then h else h - hb)).

(* add the DDict q (not in the set; dd its ZSTD_DDict state, of ID dd_id dd): the set of set_add, or a memory
   error (zstd's expansion failed) and the set unchanged; an expansion replaces the table by one twice its size
   (set_grow: the room it needs while the old one is still held) *)
Definition ZSTD_DDictHashSet_addDDict_spec : ident * funspec :=
  DECLARE _ZSTD_DDictHashSet_addDDict
  WITH gv: globals, sp: val, l: list (val * ddict_st), q: val, dd: ddict_st, shm: share, pm: val,
       am: option cmem, h: Z, hb: Z
  PRE [ tptr t_hset, tptr t_ddict, tptr t_cmem ]
    PROP (readable_share shm; isptr q; ~ In q (map fst l); Zlength l < 2 ^ 20;
          cmem_ok am; hb <= h; cm_room am h (set_grow hb))
    PARAMS (sp; q; pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am h; hset_at am sp l hb; set_ids l;
         ddid q (dd_id dd) (ddb dd))
  POST [ tulong ]
    EX r: Z, EX hb': Z,
    PROP ((r = 0 \/ r = err_code ZSTD_error_memory_allocation) /\ (l = nil -> r = 0); hb <= hb' <= hb + set_grow hb)
    RETURN (Vlong (Int64.repr r))
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am (h - hb + hb');
         hset_at am sp (if Z.eq_dec r 0 then set_add l q dd else l) hb';
         set_ids l; ddid q (dd_id dd) (ddb dd)).

Definition ZSTD_DDictHashSet_getDDict_spec : ident * funspec :=
  DECLARE _ZSTD_DDictHashSet_getDDict
  WITH sp: val, l: list (val * ddict_st), tbl: list val, id: Z, am: option cmem
  PRE [ tptr t_hset, tuint ]
    PROP (0 <= id <= Int.max_unsigned) PARAMS (sp; Vint (Int.repr id))
    SEP (hset_tbl am sp l tbl; set_ids l)
  POST [ tptr t_ddict ]
    PROP () RETURN (hs_probe l tbl id) SEP (hset_tbl am sp l tbl; set_ids l).

(* ZSTD_DCtx_selectFrameDDict(dctx): with a current DDict, the set's DDict for the frame's Dictionary_ID (id, in
   fParams) becomes the context's (local DDict freed), with its ID *)
Definition ZSTD_DCtx_selectFrameDDict_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_selectFrameDDict
  WITH gv: globals, p: val, fs: fstate, id: Z, d: dfields, sp: val, l: list (val * ddict_st),
       tbl: list val, xq: option (val * val), am: option cmem, hb: Z
  PRE [ tptr t_dctx ]
    PROP (fp_dictID (fs_fParams fs) = Vint (Int.repr id); 0 <= id <= Int.max_unsigned; sp <> nullval;
          cur_ok d l xq; local_mem am d; cmem_ok am; 0 <= hb)
    PARAMS (p) GLOBALS (gv)
    SEP (mem_mgr gv; zstd_globals gv; frame_fields p fs; dgroup DENT gv p d; cm_have am (hb + local_held d);
         field_at Ews t_dctx (DOT _ddictSet) sp p; hset_tbl am sp l tbl; set_ids l; opt_token xq)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_mgr gv; zstd_globals gv;
         frame_fields p (if eq_dec (sel_r d l tbl id) nullval then fs else fsu_dictID fs (Vint (Int.repr id)));
         dgroup DENT gv p (sel_dict d (sel_r d l tbl id));
         cm_have am (hb + local_held (sel_dict d (sel_r d l tbl id)));
         field_at Ews t_dctx (DOT _ddictSet) sp p; hset_tbl am sp l tbl; set_ids l; opt_token xq).

(* ----- contexts ----- *)

(* ZSTD_initDCtx_internal on a fresh struct whose customMem is set (the allocator am, which has given out the
   struct only): the initial context *)
Definition ZSTD_initDCtx_internal_spec3 : ident * funspec :=
  DECLARE _ZSTD_initDCtx_internal
  WITH gv: globals, p: val, am: option cmem
  PRE [ tptr t_dctx ]
    PROP () PARAMS (p)
    SEP (mgroup am p dctx_size;
         field_at Ews t_dctx (DOT _fParams) (fh_val fh_zero) p; dctx_fields_nofp p)
  POST [ tvoid ]
    PROP () RETURN () SEP (ctx_body3 DENT TABS gv p (k03m am)).

(* ZSTD_createDCtx_internal(&mem) with the allocator am at pm (the default one: ZSTD_defaultCMem, whose bytes
   are in zstd_globals, or a context's own, which has given out nothing yet and has room for the context) *)
Definition ZSTD_createDCtx_internal_spec3 : ident * funspec :=
  DECLARE _ZSTD_createDCtx_internal
  WITH gv: globals, shm: share, pm: val, am: option cmem
  PRE [ tptr t_cmem ]
    PROP (readable_share shm; cmem_ok am; cm_room am 0 dctx_size)
    PARAMS (pm) GLOBALS (gv)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm; cm_have am 0)
  POST [ tptr t_dctx ]
    EX q: val,
    PROP (is_pointer_or_null q)
    RETURN (q)
    SEP (mem_mgr gv; data_at shm t_cmem (cmem_v am) pm;
         if eq_dec q nullval then cm_have am 0 else ctx_rep3 DENT TABS gv q (k03m am)).

(* ZSTD_DCtx_refDDict's result on the concrete state: refused while a frame is being streamed (streamStage not
   zdss_init), else the local DDict freed (clearDict), q referenced, the set extended (refddict_res3); the context's
   allocator then holds h' bytes besides the context and the stream buffer (the set's, which may have been created
   or expanded through it) *)
Definition refddict_int_res (k: cst3) (q: val) (dd: ddict_st) (r: Z) (k': cst3) : Prop :=
  (sf_stage (c3_s k) <> 0 /\ is_error_code r = true /\ k' = k) \/
  (sf_stage (c3_s k) = 0 /\
   exists sp' l' h', refddict_res3 (dp_multi (c3_par k)) (c3_sp k) (c3_set k) q dd r sp' l' /\
     0 <= h' <= 3 * set_new_bytes + 3 * sf_held (c3_s k) /\ (sf_mem (c3_s k) = None -> h' = 0) /\
     (q = nullval -> h' = sf_held (c3_s k) - local_held (c3_dict k)) /\
     k' = c3_with_set (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) h'))
                         (if eq_dec q nullval then df_none else ddict_ref_fields q)) sp' l').

(* ZSTD_DCtx_refDDict on a context in any stage, with NULL or a weakly valid q, any allocator (internal; the API
   specification follows).  With refMultipleDDicts, q (not yet in the set) joins the set: its ID and the IDs of the
   set's DDicts are read; the set's blocks go through the context's allocator, which needs room for them *)
Definition ZSTD_DCtx_refDDict_int_spec3 : ident * funspec :=
  DECLARE _ZSTD_DCtx_refDDict
  WITH W: list ptr_witness, gv: globals, p: val, k: cst3, q: val, dd: ddict_st
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP (q = nullval \/ (isptr q /\ (dp_multi (c3_par k) = 1 \/ (pws_pred W |-- weak_valid_pointer q)));
          q <> nullval -> dp_multi (c3_par k) = 1 ->
            ~ In q (map fst (c3_set k)) /\ Zlength (c3_set k) < 2 ^ 20;
          local_mem (sf_mem (c3_s k)) (c3_dict k);
          sf_stage (c3_s k) = 0 -> q <> nullval ->
            cm_room (sf_mem (c3_s k)) (sf_given (c3_s k)) (3 * set_new_bytes + 2 * sf_held (c3_s k)))
    PARAMS (p; q) GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k;
         if andb (negb (veqb q nullval)) (dp_multi (c3_par k) =? 1)
         then set_ids (c3_set k) * ddid q (dd_id dd) (ddb dd) else emp)
  POST [ tulong ]
    EX r: Z, EX k': cst3,
    PROP (0 <= r <= Int64.max_unsigned; refddict_int_res k q dd r k')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k';
         if andb (negb (veqb q nullval)) (dp_multi (c3_par k) =? 1)
         then set_ids (c3_set k) * ddid q (dd_id dd) (ddb dd) else emp).

(* ZSTD_dParam_getBoundsP / ZSTD_dParam_withinBounds for the parameters the laws reach *)
Definition ZSTD_dParam_getBoundsP_spec3 : ident * funspec :=
  DECLARE _ZSTD_dParam_getBoundsP
  WITH sh: share, pb: val, k: Z
  PRE [ tptr t_bounds, tint ]
    PROP (writable_share sh; dparam_known k) PARAMS (pb; Vint (Int.repr k))
    SEP (data_at_ sh t_bounds pb)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh t_bounds
           (Vlong (Int64.repr 0), (Vint (Int.repr (fst (dparam_bounds k))), Vint (Int.repr (snd (dparam_bounds k)))))
           pb).

Definition ZSTD_dParam_withinBounds_spec3 : ident * funspec :=
  DECLARE _ZSTD_dParam_withinBounds
  WITH k: Z, v: Z
  PRE [ tint, tint ]
    PROP (dparam_known k; Int.min_signed <= v <= Int.max_signed)
    PARAMS (Vint (Int.repr k); Vint (Int.repr v))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if andb (fst (dparam_bounds k) <=? v) (v <=? snd (dparam_bounds k)) then 1 else 0)))
    SEP ().

(* ----- dictionary loading (zstd creates the local DDict through the context's allocator) ----- *)

(* ZSTD_DCtx_loadDictionary_advanced's result on the concrete state: refused while a frame is being streamed, else
   the new dictionary fields (the old local DDict freed, the new one made through the context's allocator) *)
Definition load_int_res (k: cst3) (pk: val) (b: list Z) (method ctype r: Z) (k': cst3) : Prop :=
  (sf_stage (c3_s k) <> 0 /\ is_error_code r = true /\ k' = k) \/
  (sf_stage (c3_s k) = 0 /\
   exists d', load_res3 (sf_mem (c3_s k)) pk b method ctype r d' /\
     k' = c3_with_dict (c3_with_s k (sf_with_held (c3_s k)
                                       (sf_held (c3_s k) - local_held (c3_dict k) + local_held d'))) d').

Definition ZSTD_DCtx_loadDictionary_advanced_spec3 : ident * funspec :=
  DECLARE _ZSTD_DCtx_loadDictionary_advanced
  WITH W: list ptr_witness, gv: globals, p: val, k: cst3, sh: share, pk: val, b: list Z,
       method: Z, ctype: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tint, tint ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          buf_ok W sh (Zlength b) pk; method = 0 \/ method = 1; ctype = 0 \/ ctype = 1 \/ ctype = 2;
          local_mem (sf_mem (c3_s k)) (c3_dict k);
          sf_stage (c3_s k) = 0 -> cm_room (sf_mem (c3_s k)) (sf_given (c3_s k)) (sizeof t_ddict + Zlength b))
    PARAMS (p; pk; Vlong (Int64.repr (Zlength b)); Vint (Int.repr method); Vint (Int.repr ctype))
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk)
  POST [ tulong ]
    EX r: Z, EX k': cst3,
    PROP (0 <= r <= Int64.max_unsigned; load_int_res k pk b method ctype r k')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k';
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk).

Definition ZSTD_DCtx_refPrefix_advanced_spec3 : ident * funspec :=
  DECLARE _ZSTD_DCtx_refPrefix_advanced
  WITH W: list ptr_witness, gv: globals, p: val, k: cst3, sh: share, pk: val, b: list Z, ctype: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tint ]
    PROP (sf_stage (c3_s k) = 0; readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b;
          buf_ok W sh (Zlength b) pk; ctype = 0 \/ ctype = 1 \/ ctype = 2; sf_mem (c3_s k) = None;
          local_mem (sf_mem (c3_s k)) (c3_dict k))
    PARAMS (p; pk; Vlong (Int64.repr (Zlength b)); Vint (Int.repr ctype))
    GLOBALS (gv)
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk)
  POST [ tulong ]
    EX r: Z, EX d': dfields,
    PROP (exists d0, load_res3 None pk b 1 ctype r d0 /\ d' = (if r =? 0 then df_set_uses d0 1 else d0))
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p (c3_with_dict k d');
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk).

(* ----- frames ----- *)

(* ZSTD_decodeFrameHeader(dctx, src, headerSize) on the header bytes s (any), the parameters pr, with the selection
   when sel_on *)
Definition ZSTD_decodeFrameHeader_spec3 : ident * funspec :=
  DECLARE _ZSTD_decodeFrameHeader
  WITH gv: globals, p: val, fs: fstate, did: Z, pcs: Z, pr: dparams, sp: val, d: dfields,
       l: list (val * ddict_st), tbl: list val, xq: option (val * val),
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, am: option cmem, hb: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (win_ok sh N c off (Zlength s) s; fs_dictID fs = Vint (Int.repr did); 0 <= did <= Int.max_unsigned;
          fs_processedCSize fs = Vlong (Int64.repr pcs); sel_on pr sp = true -> cur_ok d l xq;
          sel_mem pr sp d am hb)
    PARAMS (p; offset_val off base; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; fcore3 p fs pr sp; sel_res gv p pr sp d l tbl xq am hb; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX fs': fstate, EX d': dfields,
    PROP (0 <= r <= Int64.max_unsigned; dfh_post3 (dmode_of pr) (sel_on pr sp) d l tbl fs did pcs s r fs' d')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; fcore3 p fs' pr sp; sel_res gv p pr sp d' l tbl xq am hb;
         data_at sh (tarray tuchar N) c base).

(* the exact one-shot result (model/Exact.v's os_res) of the bytes s with capacity cap: an error iff os_res fails,
   else exactly its content at the start of the output out *)
Definition os_match (s: list Z) (cap r: Z) (out: list val) : Prop :=
  match os_res s cap with
  | None => is_error_code r = true
  | Some c => r = Zlength c /\ sublist 0 r out = zbytes c
  end.

(* ----- one-shot decoding (the statements for the contract fix by which ZSTD_decompressMultiFrame begins each
   frame with the set's DDict of its Dictionary_ID; claims under the probe's selection psel) ----- *)

(* the selection of the probe: the model of the DDict hs_probe finds (None: not found) *)
Definition psel (l: list (val * ddict_st)) (tbl: list val) (id: Z) : option dict_model :=
  let q := hs_probe l tbl id in
  if eq_dec q nullval then None
  else match find (fun e => veqb (fst e) q) l with
       | Some e => ddx_model (dd_x (fst e) (snd e))
       | None => None
       end.

(* the darg is the context's local DDict (ZSTD_decompressDCtx after ZSTD_DCtx_loadDictionary): its DDict is in
   dgroup *)
Definition darg_local (d: dfields) (a: darg) : bool :=
  andb (veqb (darg_ddict a) (df_local d)) (negb (veqb (df_local d) nullval)).

(* the current DDict, tested by the selection: none, the local one, one of the set, or the argument q0 *)
Definition cur_ok3 (d: dfields) (l: list (val * ddict_st)) (q0: val) : Prop :=
  (df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1) /\
  (df_ddict d = nullval \/ df_ddict d = df_local d \/ In (df_ddict d) (map fst l) \/ df_ddict d = q0).

(* the conditions under the selection: the current DDict as above; the local darg is the one of dgroup; a darg
   that is in the set is the set's entry; the set's by-reference DDicts as the API requires (D4) *)
Definition msel_ok (W: list ptr_witness) (d: dfields) (l: list (val * ddict_st)) (a: darg) (shk shd: share)
    (cap: Z) (dst: val) : Prop :=
  cur_ok3 d l (darg_ddict a) /\ readable_share shk /\
  (darg_local d a = true -> exists x buf sh, a = DA_ddict x buf sh /\ df_lx d = Some (x, buf)) /\
  (forall x buf sh dd, a = DA_ddict x buf sh -> In (dx_q x, dd) l -> x = dd_x (dx_q x) dd /\ buf = dd_buf dd) /\
  Forall (fun e => fst e <> darg_ddict a -> ddict_buf_ok0 W shk (snd e) shd cap dst) l /\
  (* the local DDict is not in the set (separation: dgroup's DDict vs set_res/dict_res) *)
  (darg_local d a = true -> ~ In (darg_ddict a) (map fst l)).

(* the set's DDicts other than the argument's (whose memory darg_res holds) *)
Definition set_full (gv: globals) (shk: share) (l: list (val * ddict_st)) (q0: val) : mpred :=
  fold_right sepcon emp
    (map (fun e => if Val.eq (fst e) q0 then emp else ddict_res (DD3_of DENT) gv shk (fst e) (snd e)) l).

(* MultiFrame's selection resources: mem_mgr and the context's allocator am (clearDict frees the local DDict; hb
   bytes given out besides it), dgroup, the set, its DDicts *)
Definition msel_res (gv: globals) (p: val) (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st))
    (tbl: list val) (shk: share) (a: darg) (am: option cmem) (hb: Z) : mpred :=
  if sel_on pr sp
  then mem_mgr gv * dgroup DENT gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl *
       set_full gv shk l (darg_ddict a)
  else emp.

(* the argument's memory: with the selection and the local darg, its DDict is in dgroup (the bytes of a
   by-reference local DDict stay the caller's) *)
Definition darg_res3 (gv: globals) (pr: dparams) (sp: val) (d: dfields) (a: darg) : mpred :=
  if andb (sel_on pr sp) (darg_local d a)
  then match a with
       | DA_ddict x buf sh => if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf
       | _ => emp
       end
  else darg_res gv a.

(* ZSTD_decompressMultiFrame on the frame group: ANY bytes s, the dictionary a, the parameters pr.  The result
   is the model's (Params.decode_series_m under dmode_of pr): without the selection (or without a DDict
   argument) with a's dictionary; with it, the probe's selection psel l tbl (fix F4).  Afterwards the tables
   are uninitialised; the dictionary fields are d or a set member's (switch_fields).  Code fix F10: the function
   first sets streamStage = zdss_init (0), so that one-shot decoding ends a streaming frame left unfinished; the
   field is taken with any value and given back as zdss_init.  Code fix F9: dst may be NULL when cap = 0 (mbuf). *)
Definition ZSTD_decompressMultiFrame_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompressMultiFrame
  WITH W: list ptr_witness, gv: globals, p: val, fs: fstate, tabs: tabs3, pr: dparams, sp: val, d: dfields,
       l: list (val * ddict_st), tbl: list val, shk: share,
       shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z, a: darg, am: option cmem, hb: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tptr tvoid, tulong, tptr t_ddict ]
    PROP (buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; writable_share shd; readable_share shs;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s; darg_ok3 W a shd cap dst;
          sel_on pr sp = true -> msel_ok W d l a shk shd cap dst; sel_mem pr sp d am hb)
    PARAMS (p; dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s));
            darg_dict a; Vlong (Int64.repr (darg_size a)); darg_ddict a)
    GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs tabs pr sp; msel_res gv p pr sp d l tbl shk a am hb;
         darg_res3 gv pr sp d a; mbuf shd cap (Zrepeat Vundef cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at_ Ews t_dctx (DOT _streamStage) p)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX fs': fstate, EX d': dfields, EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap; is_error_code r = false -> r <= cap;
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out;
          sel_on pr sp = true -> darg_ddict a <> nullval ->
            oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out;
          is_error_code r = false -> exists c, bytes_ok c /\ Zlength c = r /\ sublist 0 r out = zbytes c;
          is_error_code r = true -> dec_err r;
          d' = d \/ (sel_on pr sp = true /\ exists q, In q (map fst l) /\ d' = switch_fields q);
          (* one frame: selectFrameDDict ran once, on its Dictionary_ID *)
          is_error_code r = false -> sel_on pr sp = true ->
            frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              d' = d \/ (exists q, In q (map fst l) /\ d' = switch_fields q /\ q = hs_probe l tbl (fh_dictID h));
          (* D-S2 (441): after a success on bytes starting with a Zstandard frame, with a current DDict *)
          is_error_code r = false -> sel_on pr sp = true -> df_ddict d <> nullval ->
            (exists h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h /\ fh_frameType h = 0) ->
            exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
              (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d');
          (* fParams' dictID stays a 32-bit value *)
          fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs');
          (* the error codes (Spec_codes.oneshot_codes) *)
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r;
          sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_codes (dmode_of pr) (psel l tbl) (darg_model a) s cap r;
          (* the end-of-frame check: a success on one Zstandard frame that declares its content size decodes
             exactly that many bytes (the single-pass shortcut of ZSTD_decompressStream, fix F7) *)
          is_error_code r = false -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h;
          (* the exact result, without a dictionary and with the default parameters (model/Exact.v) *)
          a = DA_none -> pr = dparams_dflt -> os_match s cap r out;
          (* litExtraBuffer afterwards, when s is exactly one Zstandard frame (not a skippable one, which
             ZSTD_decompressMultiFrame skips while x_frame would read it as a frame) that the model decodes from the
             tables' litExtraBuffer: the frame's (model/ExFrame.v's x_frame applies ZSTD_decompressBegin itself; the
             stream's single-pass shortcut goes on streaming with these bytes, ExStream.d_after_shortcut) *)
          a = DA_none -> pr = dparams_dflt -> is_skippable_magic (le_field s 0 4) = false ->
            forall (st e: xstate) (c: list Z), x_lxb xhuf st = tabs_lxb tabs ->
            x_frame xstate (xst_begin xhuf) xblock st s cap = Some (c, Zlength s, e) -> lxb' = x_lxb xhuf e)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs' (TUninit lxb') pr sp; msel_res gv p pr sp d' l tbl shk a am hb;
         darg_res3 gv pr sp d a; mbuf shd cap out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p).

(* ZSTD_decompress_usingDDict with NULL or a DDict, on the frame group: as MultiFrame (internal: ZSTD_decompressDCtx
   passes the context's DDict, ZSTD_decompressStream calls it mid-stream; the API specification follows); streamStage
   ends as zdss_init (F10) *)
Definition ZSTD_decompress_usingDDict_int_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompress_usingDDict
  WITH W: list ptr_witness, gv: globals, p: val, fs: fstate, tabs: tabs3, pr: dparams, sp: val, d: dfields,
       l: list (val * ddict_st), tbl: list val, shk: share,
       shd: share, dst: val, cap: Z, shs: share, src: val, s: list Z, a: darg, am: option cmem, hb: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tptr t_ddict ]
    PROP (darg_is_ddict a;
          buf_ok W shd cap dst; buf_ok W shs (Zlength s) src; writable_share shd; readable_share shs;
          0 <= cap <= 2 ^ 63 - 1; Zlength s <= 2 ^ 63 - 1; bytes_ok s; darg_ok3 W a shd cap dst;
          sel_on pr sp = true -> msel_ok W d l a shk shd cap dst; sel_mem pr sp d am hb)
    PARAMS (p; dst; Vlong (Int64.repr cap); src; Vlong (Int64.repr (Zlength s)); darg_ddict a)
    GLOBALS (gv)
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs tabs pr sp; msel_res gv p pr sp d l tbl shk a am hb;
         darg_res3 gv pr sp d a; mbuf shd cap (Zrepeat Vundef cap) dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at_ Ews t_dctx (DOT _streamStage) p)
  POST [ tulong ]
    EX r: Z, EX out: list val, EX fs': fstate, EX d': dfields, EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap; is_error_code r = false -> r <= cap;
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_ok (dmode_of pr) (darg_model a) s cap r out;
          sel_on pr sp = true -> darg_ddict a <> nullval ->
            oneshot_sel (dmode_of pr) (psel l tbl) (darg_model a) s cap r out;
          is_error_code r = false -> exists c, bytes_ok c /\ Zlength c = r /\ sublist 0 r out = zbytes c;
          is_error_code r = true -> dec_err r;
          d' = d \/ (sel_on pr sp = true /\ exists q, In q (map fst l) /\ d' = switch_fields q);
          (* one frame: selectFrameDDict ran once, on its Dictionary_ID *)
          is_error_code r = false -> sel_on pr sp = true ->
            frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              d' = d \/ (exists q, In q (map fst l) /\ d' = switch_fields q /\ q = hs_probe l tbl (fh_dictID h));
          is_error_code r = false -> sel_on pr sp = true -> df_ddict d <> nullval ->
            (exists h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h /\ fh_frameType h = 0) ->
            exists id, fp_dictID (fs_fParams fs') = Vint (Int.repr id) /\ 0 <= id <= Int.max_unsigned /\
              (hs_probe l tbl id = nullval \/ hs_probe l tbl id = df_ddict d');
          (* fParams' dictID stays a 32-bit value *)
          fp_ok (fs_fParams fs) -> fp_ok (fs_fParams fs');
          (* the error codes (Spec_codes.oneshot_codes) *)
          sel_on pr sp = false \/ darg_ddict a = nullval -> oneshot_codes (dmode_of pr) sel_none (darg_model a) s cap r;
          sel_on pr sp = true -> darg_ddict a <> nullval -> oneshot_codes (dmode_of pr) (psel l tbl) (darg_model a) s cap r;
          (* the end-of-frame check: a success on one Zstandard frame that declares its content size decodes
             exactly that many bytes (the single-pass shortcut of ZSTD_decompressStream, fix F7) *)
          is_error_code r = false -> frame_compressed_size_m (dp_fmt pr =? 1) s = Some (Zlength s) ->
            forall h, get_frame_header_m (dp_fmt pr =? 1) s = FH_ok h -> fh_frameType h = 0 ->
              fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> r = fh_contentSize h;
          (* the exact result, without a dictionary and with the default parameters (model/Exact.v) *)
          a = DA_none -> pr = dparams_dflt -> os_match s cap r out;
          (* litExtraBuffer afterwards, when s is exactly one Zstandard frame (not a skippable one, which
             ZSTD_decompressMultiFrame skips while x_frame would read it as a frame) that the model decodes from the
             tables' litExtraBuffer: the frame's (model/ExFrame.v's x_frame applies ZSTD_decompressBegin itself; the
             stream's single-pass shortcut goes on streaming with these bytes, ExStream.d_after_shortcut) *)
          a = DA_none -> pr = dparams_dflt -> is_skippable_magic (le_field s 0 4) = false ->
            forall (st e: xstate) (c: list Z), x_lxb xhuf st = tabs_lxb tabs ->
            x_frame xstate (xst_begin xhuf) xblock st s cap = Some (c, Zlength s, e) -> lxb' = x_lxb xhuf e)
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; fgroup3 TABS gv p fs' (TUninit lxb') pr sp; msel_res gv p pr sp d' l tbl shk a am hb;
         darg_res3 gv pr sp d a; mbuf shd cap out dst;
         data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p).

End Specs.

(* ===================================================================================
   the small streaming helpers (v2's StreamSpecs, unchanged; fixed here so that the streaming and the
   buffer-less parts share them)
   =================================================================================== *)

Definition zdss_init : Z := 0.
Definition zdss_loadHeader : Z := 1.
Definition zdss_read : Z := 2.
Definition zdss_load : Z := 3.
Definition zdss_flush : Z := 4.

Definition ds_getFrameHeaderSize : Z := 0.
Definition ds_decodeBlockHeader : Z := 2.
Definition ds_decompressBlock : Z := 3.
Definition ds_decompressLastBlock : Z := 4.
Definition ds_checkChecksum : Z := 5.
Definition ds_skipFrame : Z := 7.

Definition vlong (z: Z) : val := Vlong (Int64.repr z).

Definition ZSTD_WORKSPACETOOLARGE_FACTOR : Z := 3.
Definition ZSTD_WORKSPACETOOLARGE_MAXDURATION : Z := 128.
Definition ZSTD_error_dstBuffer_wrong : Z := 104.

(* ---------- ZSTD_limitCopy ---------- *)

(* the cells oc with the bytes cells cs[os, os + m) copied at od *)
Definition copy_cells (oc: list val) (od: Z) (cs: list val) (os m: Z) : list val :=
  sublist 0 od oc ++ sublist os (os + m) cs ++ sublist (od + m) (Zlength oc) oc.

Definition ZSTD_limitCopy_spec : ident * funspec :=
  DECLARE _ZSTD_limitCopy
  WITH shd: share, bd: val, cd: list val, od: Z, cap: Z, shs: share, bs: val, cs: list val, os: Z, n: Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (writable_share shd; readable_share shs;
          0 <= od; 0 <= cap <= Int64.max_unsigned; od + Z.min cap n <= Zlength cd;
          0 <= os; 0 <= n <= Int64.max_unsigned; os + Z.min cap n <= Zlength cs;
          Zlength cd <= Int64.max_unsigned; Zlength cs <= Int64.max_unsigned;
          (* the copied bytes are defined (memcpy is libc.c's byte loop) *)
          byte_cells (sublist os (os + Z.min cap n) cs))
    PARAMS (offset_val od bd; Vlong (Int64.repr cap); offset_val os bs; Vlong (Int64.repr n))
    SEP (data_at shd (tarray tuchar (Zlength cd)) cd bd; data_at shs (tarray tuchar (Zlength cs)) cs bs)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Z.min cap n)))
    SEP (data_at shd (tarray tuchar (Zlength cd)) (copy_cells cd od cs os (Z.min cap n)) bd;
         data_at shs (tarray tuchar (Zlength cs)) cs bs).

(* ---------- the frame stage readers ---------- *)

Definition ZSTD_nextSrcSizeToDecompress_spec : ident * funspec :=
  DECLARE _ZSTD_nextSrcSizeToDecompress
  WITH p: val, e: Z
  PRE [ tptr t_dctx ]
    PROP (0 <= e <= Int64.max_unsigned) PARAMS (p) SEP (field_at Ews t_dctx (DOT _expected) (vlong e) p)
  POST [ tulong ]
    PROP () RETURN (vlong e) SEP (field_at Ews t_dctx (DOT _expected) (vlong e) p).

(* BOUNDED(1, n, e) in a raw block, else e *)
Definition next_size (stage bt e n: Z) : Z :=
  if andb (orb (stage =? ds_decompressBlock) (stage =? ds_decompressLastBlock)) (bt =? 0)
  then Z.max 1 (Z.min n e) else e.

Definition ZSTD_nextSrcSizeToDecompressWithInputSize_spec : ident * funspec :=
  DECLARE _ZSTD_nextSrcSizeToDecompressWithInputSize
  WITH p: val, stage: Z, bt: val, e: Z, n: Z
  PRE [ tptr t_dctx, tulong ]
    PROP (Int.min_signed <= stage <= Int.max_signed; 0 <= e <= Int64.max_unsigned; 0 <= n <= Int64.max_unsigned;
          (stage = ds_decompressBlock \/ stage = ds_decompressLastBlock) ->
            exists b, bt = Vint (Int.repr b) /\ Int.min_signed <= b <= Int.max_signed)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p;
         field_at Ews t_dctx (DOT _bType) bt p;
         field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (next_size stage (match bt with Vint b => Int.signed b | _ => 0 end) e n)))
    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p;
         field_at Ews t_dctx (DOT _bType) bt p;
         field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p).

(* ZSTD_nextInputType_e of a frame stage 0..7 *)
Definition next_input_type (stage: Z) : Z :=
  if stage <=? 1 then 0 else if stage <=? 5 then stage - 1 else 5.

Definition ZSTD_nextInputType_spec : ident * funspec :=
  DECLARE _ZSTD_nextInputType
  WITH p: val, stage: Z
  PRE [ tptr t_dctx ]
    PROP (0 <= stage <= 7) PARAMS (p) SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (next_input_type stage)))
    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p).

Definition ZSTD_isSkipFrame_spec : ident * funspec :=
  DECLARE _ZSTD_isSkipFrame
  WITH p: val, stage: Z
  PRE [ tptr t_dctx ]
    PROP (Int.min_signed <= stage <= Int.max_signed) PARAMS (p)
    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if stage =? ds_skipFrame then 1 else 0)))
    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p).
(* ---------- the small helpers of the buffer management ---------- *)

Definition ZSTD_decodingBufferSize_internal_spec : ident * funspec :=
  DECLARE _ZSTD_decodingBufferSize_internal
  WITH ws: Z, fcs: Z, bsm: Z
  PRE [ tulong, tulong, tulong ]
    PROP (0 <= ws <= 2 ^ 40; 0 <= fcs <= Int64.max_unsigned; 0 <= bsm <= 2 ^ 40)
    PARAMS (Vlong (Int64.repr ws); Vlong (Int64.repr fcs); Vlong (Int64.repr bsm))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (Z.min fcs (ws + Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm * 2 + WILDCOPY_OVERLENGTH * 2))))
    SEP ().

(* ZSTD_decodingBufferSize_internal with blockSizeMax = ZSTD_BLOCKSIZE_MAX (ZSTD_estimateDStreamSize) *)
Definition ZSTD_decodingBufferSize_min_spec : ident * funspec :=
  DECLARE _ZSTD_decodingBufferSize_min
  WITH ws: Z, fcs: Z
  PRE [ tulong, tulong ]
    PROP (0 <= ws <= 2 ^ 40; 0 <= fcs <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr ws); Vlong (Int64.repr fcs))
    SEP ()
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (Z.min fcs (ws + Z.min ws ZSTD_BLOCKSIZE_MAX * 2 + WILDCOPY_OVERLENGTH * 2))))
    SEP ().

Definition is_overflow (ins outs nin nout: Z) : bool :=
  (nin + nout) * ZSTD_WORKSPACETOOLARGE_FACTOR mod 2 ^ 64 <=? (ins + outs) mod 2 ^ 64.

Definition ZSTD_DCtx_isOverflow_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_isOverflow
  WITH p: val, ins: Z, outs: Z, nin: Z, nout: Z
  PRE [ tptr t_dctx, tulong, tulong ]
    PROP (0 <= ins <= Int64.max_unsigned; 0 <= outs <= Int64.max_unsigned;
          0 <= nin <= Int64.max_unsigned; 0 <= nout <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr nin); Vlong (Int64.repr nout))
    SEP (field_at Ews t_dctx (DOT _inBuffSize) (vlong ins) p; field_at Ews t_dctx (DOT _outBuffSize) (vlong outs) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if is_overflow ins outs nin nout then 1 else 0)))
    SEP (field_at Ews t_dctx (DOT _inBuffSize) (vlong ins) p; field_at Ews t_dctx (DOT _outBuffSize) (vlong outs) p).

Definition ZSTD_DCtx_updateOversizedDuration_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_updateOversizedDuration
  WITH p: val, ins: Z, outs: Z, nin: Z, nout: Z, ov: Z
  PRE [ tptr t_dctx, tulong, tulong ]
    PROP (0 <= ins <= Int64.max_unsigned; 0 <= outs <= Int64.max_unsigned;
          0 <= nin <= Int64.max_unsigned; 0 <= nout <= Int64.max_unsigned; 0 <= ov <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr nin); Vlong (Int64.repr nout))
    SEP (field_at Ews t_dctx (DOT _inBuffSize) (vlong ins) p; field_at Ews t_dctx (DOT _outBuffSize) (vlong outs) p;
         field_at Ews t_dctx (DOT _oversizedDuration) (vlong ov) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (field_at Ews t_dctx (DOT _inBuffSize) (vlong ins) p; field_at Ews t_dctx (DOT _outBuffSize) (vlong outs) p;
         field_at Ews t_dctx (DOT _oversizedDuration)
           (vlong (if is_overflow ins outs nin nout then (ov + 1) mod 2 ^ 64 else 0)) p).

Definition ZSTD_DCtx_isOversizedTooLong_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_isOversizedTooLong
  WITH p: val, ov: Z
  PRE [ tptr t_dctx ]
    PROP (0 <= ov <= Int64.max_unsigned) PARAMS (p)
    SEP (field_at Ews t_dctx (DOT _oversizedDuration) (vlong ov) p)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if ZSTD_WORKSPACETOOLARGE_MAXDURATION <=? ov then 1 else 0)))
    SEP (field_at Ews t_dctx (DOT _oversizedDuration) (vlong ov) p).

Definition ZSTD_outBuffer_copy_spec : ident * funspec :=
  DECLARE _ZSTD_outBuffer_copy
  WITH shd: share, d: val, shs: share, s: val, b: val, sz: Z, pos: Z
  PRE [ tptr t_outBuffer, tptr t_outBuffer ]
    PROP (writable_share shd; readable_share shs; is_pointer_or_null b;
          0 <= sz <= Int64.max_unsigned; 0 <= pos <= Int64.max_unsigned)
    PARAMS (d; s)
    SEP (data_at_ shd t_outBuffer d; data_at shs t_outBuffer (b, (vlong sz, vlong pos)) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd t_outBuffer (b, (vlong sz, vlong pos)) d; data_at shs t_outBuffer (b, (vlong sz, vlong pos)) s).

(* ZSTD_checkOutBuffer: in stable mode, after zdss_init, the output buffer must be the recorded one
   (the caller passes the same dst: the comparison is defined) *)
Definition check_out (stable: bool) (stage: Z) (ev: reptype t_outBuffer) (ob: val) (osz opos: Z) : Z :=
  if andb stable (negb (stage =? zdss_init)) then
    (let '(b, (sz, pos)) := (ev : val * (val * val)) in
     if andb (veqb b ob) (andb (veqb pos (vlong opos)) (veqb sz (vlong osz))) then 0
     else err_code ZSTD_error_dstBuffer_wrong)
  else 0.

(* the output buffer's pointer ob as the caller's struct holds it, and the buffer at obb: ob itself, or for an empty
   buffer passed as NULL (F9) any base *)
Definition ZSTD_checkOutBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_checkOutBuffer
  WITH p: val, stable: bool, stage: Z, ev: reptype t_outBuffer, sho: share, outp: val,
       ob: val, osz: Z, opos: Z, W: list ptr_witness, shob: share, oc: list val, obb: val
  PRE [ tptr t_dctx, tptr t_outBuffer ]
    PROP (readable_share sho; readable_share shob; Int.min_signed <= stage <= Int.max_signed;
          0 <= osz <= Int64.max_unsigned; 0 <= opos <= Int64.max_unsigned; buf_ok W shob osz obb;
          stable = true -> stage <> zdss_init ->
            exists esz epos, @eq (val * (val * val)) ev (ob, (vlong esz, vlong epos)) /\
              0 <= esz <= Int64.max_unsigned /\ 0 <= epos <= Int64.max_unsigned;
          ob = obb \/ ob = nullval)
    PARAMS (p; outp)
    SEP (field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr stage)) p;
         field_at Ews t_dctx (DOT _expectedOutBuffer) ev p;
         data_at sho t_outBuffer (ob, (vlong osz, vlong opos)) outp;
         pws_pred W; data_at shob (tarray tuchar osz) oc obb)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (check_out stable stage ev ob osz opos)))
    SEP (field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr stage)) p;
         field_at Ews t_dctx (DOT _expectedOutBuffer) ev p;
         data_at sho t_outBuffer (ob, (vlong osz, vlong opos)) outp;
         pws_pred W; data_at shob (tarray tuchar osz) oc obb).

