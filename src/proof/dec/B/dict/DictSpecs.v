(* Group DICT of subtree B: the internal specifications and the context of its body lemmas (fixed: the bodies are proved
   against them).

   ids_DICT (BGroups.v), 11 functions; exports (BIface.DICT_exports): begin_usingDict, begin_usingDDict,
   initDDict_internal, DDict_dictContent, DDict_dictSize.  Internal: ZSTD_decompressBegin,
   ZSTD_refDictContent, ZSTD_loadDEntropy, ZSTD_decompress_insertDictionary, ZSTD_copyDDictParameters,
   ZSTD_loadEntropy_intoDDict. *)
Require Export Zstd.proof.dec.B.BGroups.
Local Open Scope logic.

(* ---------- the entropy struct (ZSTD_entropyDTables_t) at pe: a context's or a DDict's field ---------- *)

Definition ent_huf (pe: val) : val := field_address t_entropy (DOT _hufTable) pe.
Definition ent_seq (k: seqkind) (pe: val) : val := field_address t_entropy (DOT sk_tfield k) pe.
Definition ctx_ent (p: val) : val := field_address t_dctx (DOT _entropy) p.
Definition dd_ent (q: val) : val := field_address t_entropy_dd (DOT _entropy) q.

(* the tables before ZSTD_loadDEntropy: hufTable's descriptor says maxTableLog = 12 (hufTable[0] =
   12 * 0x1000001), the three sequence tables anything *)
Definition ent_blank (pe: val) : mpred :=
  hufhdr_at Ews (ent_huf pe) *
  seqspace_at Ews KLL None (ent_seq KLL pe) *
  seqspace_at Ews KOF None (ent_seq KOF pe) *
  seqspace_at Ews KML None (ent_seq KML pe).

(* the whole struct after a successful ZSTD_loadDEntropy: the tables of st, its repeat offsets *)
Definition ent_full (pe: val) (st: dstate) : mpred :=
  match st_huf st, st_seq st with
  | Some ht, Some (a, b, c) =>
      hufdt_at Ews ht (ent_huf pe) *
      seqspace_at Ews KLL (Some a) (ent_seq KLL pe) *
      seqspace_at Ews KOF (Some b) (ent_seq KOF pe) *
      seqspace_at Ews KML (Some c) (ent_seq KML pe) *
      field_at Ews t_entropy (DOT _rep) (rep_vals (st_rep st)) pe *
      field_at_ Ews t_entropy (DOT _workspace) pe
  | _, _ => FF
  end.

(* ---------- the context's tables after ZSTD_decompressBegin ---------- *)

(* the table pointers at the context's own tables, no entropy, the initial repeat offsets, the Huffman
   descriptor written, litExtraBuffer holding lxb; the paths are those of BRep.tabs_def *)
Definition begin_tabs (p: val) (lxb: list Z) : mpred :=
  field_at Ews t_dctx (DOT _HUFptr) (ctx_huf p) p *
  field_at Ews t_dctx (DOT _LLTptr) (ctx_seq KLL p) p *
  field_at Ews t_dctx (DOT _MLTptr) (ctx_seq KML p) p *
  field_at Ews t_dctx (DOT _OFTptr) (ctx_seq KOF p) p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 0)) p *
  hufhdr_at Ews (ctx_huf p) *
  seqspace_at Ews KLL None (ctx_seq KLL p) *
  seqspace_at Ews KOF None (ctx_seq KOF p) *
  seqspace_at Ews KML None (ctx_seq KML p) *
  field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (1, 4, 8)) p *
  tabs_scratch p * lit_extra_at p lxb.

(* zstd's results vs the model: ld_rel, dict_auto_c, ddict_ent_c and their lemmas are in DecRep (C-result
   form) *)

(* ---------- specifications ---------- *)

(* ZSTD_decompressBegin(dctx): a new frame without dictionary (format 0: expected = 5); litExtraBuffer kept *)
Definition ZSTD_decompressBegin_spec : ident * funspec :=
  DECLARE _ZSTD_decompressBegin
  WITH gv: globals, p: val, fs: fstate, lxb: list Z
  PRE [ tptr t_dctx ]
    PROP () PARAMS (p) GLOBALS (gv)
    SEP (zstd_globals gv; cfg_b p; frame_fields p fs; tables_uninit p lxb)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; cfg_b p; frame_fields p (fs_begin fs); begin_tabs p lxb).

(* ZSTD_refDictContent(dctx, dict, n) on a context without history (previousDstEnd = dictEnd = NULL, as
   after ZSTD_decompressBegin): the n bytes at d become the prefix; dictID unchanged (= id) *)
Definition ZSTD_refDictContent_spec : ident * funspec :=
  DECLARE _ZSTD_refDictContent
  WITH p: val, fs: fstate, d: val, n: Z, id: Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (isptr d; 0 <= n <= Int64.max_unsigned; fs_previousDstEnd fs = nullval; fs_dictEnd fs = nullval;
          fs_dictID fs = Vint (Int.repr id))
    PARAMS (p; d; Vlong (Int64.repr n))
    SEP (frame_fields p fs)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (frame_fields p (fs_with_dict fs d (offset_val n d) 0 id)).

(* ZSTD_loadDEntropy(entropy, dict, |b|): zstd's result ores, Series.load_dentropy's when the model loads
   (ld_rel); on success the tables in the entropy struct pe (the three sequence tables are
   HUF_readDTableX2_wksp's workspace) and the size es <= |b| of the entropy header *)
Definition ZSTD_loadDEntropy_spec : ident * funspec :=
  DECLARE _ZSTD_loadDEntropy
  WITH gv: globals, pe: val, sh: share, d: val, b: list Z
  PRE [ tptr t_entropy, tptr tvoid, tulong ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (pe; d; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; ent_blank pe;
         field_at_ Ews t_entropy (DOT _rep) pe; field_at_ Ews t_entropy (DOT _workspace) pe;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) d)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores;
          match ores with
          | Some (st, es) => r = es /\ dstate_ok st /\ es <= Zlength b
          | None => is_error_code r = true
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv;
         match ores with
         | Some (st, _) => ent_full pe st
         | None => data_at_ Ews t_entropy pe
         end;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) d).

(* ZSTD_decompress_insertDictionary(dctx, dict, |b|), after ZSTD_decompressBegin, |b| > 0: the
   dictionary in ZSTD_dct_auto mode as zstd loads it (dict_auto_c b ores, ores: ZSTD_loadDEntropy's result);
   litExtraBuffer kept *)
Definition ZSTD_decompress_insertDictionary_spec : ident * funspec :=
  DECLARE _ZSTD_decompress_insertDictionary
  WITH gv: globals, p: val, fs: fstate, shk: share, dk: val, b: list Z, lxb: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (readable_share shk; 0 < Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (p; dk; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; frame_fields p (fs_begin fs); begin_tabs p lxb;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (0 <= r <= Int64.max_unsigned; ld_rel b ores)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv;
         match dict_auto_c b ores with
         | None => !! (is_error_code r = true) &&
             EX fs': fstate, !! (fs_dictEnd fs' = nullval /\ fs_ddictIsCold fs' = fs_ddictIsCold fs) &&
               frame_fields p fs' * tables_uninit p lxb
         | Some dm =>
             !! (r = 0) &&
             frame_fields p (fs_with_dict (fs_begin fs) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                               (offset_val (Zlength b) dk) 0 (dm_id dm)) *
             EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb)
         end;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk).

(* the bytes of a DDict's copy (nothing for a DDict by reference), without the allocation tokens: comparing
   dictBuffer with NULL needs a valid pointer to them *)
Definition ddict_copy (x: ddx) (buf: val) : mpred :=
  if ddx_copied x then data_at Ews (tarray tuchar (Zlength (dx_bytes x))) (zbytes (dx_bytes x)) buf else emp.

(* ZSTD_copyDDictParameters(dctx, ddict), after ZSTD_decompressBegin: the DDict x's content as the prefix
   (dictEnd = its end), its tables by reference (TDict), its repeat offsets.  Code fix F12: dictEnd is
   dictContent + dictSize only for a nonzero size, so the DDict without content (buf = NULL) ends at NULL.  The
   DDict's tokens are the caller's (a frame) *)
Definition ZSTD_copyDDictParameters_spec : ident * funspec :=
  DECLARE _ZSTD_copyDDictParameters
  WITH gv: globals, p: val, fs: fstate, x: ddx, buf: val, lxb: list Z
  PRE [ tptr t_dctx, tptr t_ddict ]
    PROP () PARAMS (p; dx_q x) GLOBALS (gv)
    SEP (frame_fields p fs; begin_tabs p lxb;
         ddict_struct x buf; dent_def gv (dx_q x) (ddx_ent x); ddict_copy x buf)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (frame_fields p
           (fs_set_dictEnd
              (fs_with_dict fs buf (ddx_end x buf) (if ddx_copied x then 1 else 0)
                 (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
              (ddx_end x buf));
         tabs_def gv p (Some x) (mk_tstate (ddx_state x) false lxb);
         ddict_struct x buf; dent_def gv (dx_q x) (ddx_ent x); ddict_copy x buf).

(* ZSTD_loadEntropy_intoDDict(ddict, ctype), ctype 0 (auto) or 1 (raw content): dictID, entropyPresent and
   the entropy of the DDict whose content (dictContent = buf, dictSize) is b, as zstd loads it (ores:
   ZSTD_loadDEntropy's result); an error iff auto and dict_auto_c b ores = None *)
Definition ZSTD_loadEntropy_intoDDict_spec : ident * funspec :=
  DECLARE _ZSTD_loadEntropy_intoDDict
  WITH gv: globals, q: val, sh: share, buf: val, b: list Z, ctype: Z
  PRE [ tptr t_ddict, tint ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b; ctype = 0 \/ ctype = 1)
    PARAMS (q; Vint (Int.repr ctype)) GLOBALS (gv)
    SEP (zstd_globals gv;
         field_at Ews t_ddict (DOT _dictContent) buf q;
         field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
         field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
         ent_blank (dd_ent q);
         field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) buf)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (ld_rel b ores;
          match (if ctype =? 1 then Some (dict_raw b) else dict_auto_c b ores) with
          | Some _ => r = 0
          | None => r = err_code 30
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv;
         field_at Ews t_ddict (DOT _dictContent) buf q;
         field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
         if Z.eq_dec r 0
         then field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q *
              field_at Ews t_ddict (DOT _entropyPresent)
                (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q *
              dent_def gv q (ddict_ent_c b (ctype =? 1) ores)
         else field_at_ Ews t_ddict (DOT _dictID) q * field_at_ Ews t_ddict (DOT _entropyPresent) q *
              field_at_ Ews t_ddict (DOT _entropy) q;
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) buf).

(* ---------- the group ---------- *)

(* one specification per function of ids_DICT, in that order *)
Definition DICT_specs : funspecs :=
  [ ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec; ZSTD_copyDDictParameters_spec;
    ZSTD_loadEntropy_intoDDict_spec; ZSTD_initDDict_internal_spec dent_def; ZSTD_refDictContent_spec;
    ZSTD_loadDEntropy_spec; ZSTD_decompress_insertDictionary_spec; ZSTD_decompressBegin_spec;
    ZSTD_decompressBegin_usingDict_spec tabs_def; ZSTD_decompressBegin_usingDDict_spec dent_def tabs_def ].

(* the context of every body lemma of the group *)
Definition DICT_G : funspecs := (G_B0 ++ ENT_exports ++ HUF_exports) ++ DICT_specs.

Lemma DICT_specs_ids : map fst DICT_specs = ids_DICT.
Proof. reflexivity. Qed.
