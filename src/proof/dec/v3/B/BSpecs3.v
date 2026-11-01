(* API v3, subtree B: the specifications of B's functions that change from v2.
   LIT/TOP: the block decoder holds cfg_lit (disableHufAsm) only, the format field stays with the caller
   (DecIface3.ZSTD_decompressBlock_internal_spec3).  DICT: ZSTD_decompressBegin in a context of format f
   (expected = ZSTD_startingInputLength(f), DecIface3.fs_begin3) and the dictionary functions after it;
   ZSTD_loadEntropy_intoDDict with ZSTD_dct_fullDict (ctype 2). *)
Require Export Zstd.proof.dec.v3.DecSubtrees3 Zstd.proof.dec.B.blk.BlkGroups Zstd.proof.dec.B.dict.DictSpecs.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* ===================== LIT and TOP (group BLK) ===================== *)

(* v2's BlkIface.ZSTD_decodeLiteralsBlock_spec with cfg_lit p in place of cfg_b p *)
Definition ZSTD_decodeLiteralsBlock_spec3 : ident * funspec :=
  DECLARE _ZSTD_decodeLiteralsBlock
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, oh: option huf_table, x2: bool, lxb: list Z, bsm: Z,
       streaming: Z, W: list ptr_witness, o: outarr, i: inwin
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (outarr_ok o; inwin_ok i; streaming = 0 \/ streaming = 1; 0 <= bsm <= ZSTD_BLOCKSIZE_MAX;
          Zlength (iw_s i) <= bsm;
          fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          match oh with Some ht => huf_ok ht | None => True end)
    PARAMS (p; offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i)));
            offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o)); Vint (Int.repr streaming))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p fs; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; lit_scratch_x p lxb;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i))
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX l: litloc, EX lits: list Z, EX oh': option huf_table, EX x2': bool,
    EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          streaming = 1 -> unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) bsm);
          is_error_code r = false -> lits_ok oh o i bsm streaming r oc' l lits oh';
          match decode_literals oh (iw_s i) bsm with
          | Some (lits0, _, _) => is_error_code r = false \/ Z.min (oa_cap o) bsm < Zlength lits0
          | None => True
          end;
          is_error_code r = true -> dec_err r;
          byte_cells (oa_c o) -> byte_cells (iw_c i) -> byte_cells oc';
          (* every write is a defined byte (Huffman output, the RLE byte, input bytes, the zeroed slack): a defined
             cell stays defined *)
          is_error_code r = false -> forall j, 0 <= j < oa_N o -> is_byte_val (Znth j (oa_c o)) -> is_byte_val (Znth j oc');
          (* exactly ExBlock's literals section (BlkIface.lits_exact), for the context's own Huffman table *)
          ox = None ->
          lits_exact (option_map (xhuf_of x2) oh) lxb o i bsm streaming r oc' l lits
            (option_map (xhuf_of x2') oh') lxb')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_lit p; frame_fields p fs; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i);
         if is_error_code r then huf_junk p * lit_scratch p
         else tabs_huf gv p ox oh' x2' * litfields p (oa_base o) (iw_base i) l lits lxb').

Definition LIT3_exports : funspecs := [ ZSTD_blockSizeMax_spec; ZSTD_decodeLiteralsBlock_spec3 ].

(* v2's LIT_obligation (BlkGroups) with the v3 literals spec; context: v2's G_BLK (lifted to v3 by DecLift) *)
Definition LIT3_obligation : Prop := subtree_ok ids_LIT LIT3_exports (G_BLK ++ LIT_imports).

Definition TOP3_imports : funspecs :=
  [ ZSTD_blockSizeMax_spec; ZSTD_decodeLiteralsBlock_spec3; ZSTD_decodeSeqHeaders_spec;
    ZSTD_decompressSequences_spec; ZSTD_decompressSequencesSplitLitBuffer_spec;
    ZSTD_decompressSequencesLong_spec ].
Definition TOP3_exports : funspecs := [ ZSTD_decompressBlock_internal_spec3 dent_def tabs_def ].

Definition TOP3_obligation : Prop := subtree_ok ids_TOP TOP3_exports (G_BLK ++ TOP3_imports).

(* ===================== DICT ===================== *)

(* ZSTD_decompressBegin(dctx) in a context of format f: v2's DictSpecs.ZSTD_decompressBegin_spec with
   cfg_fmt p f (cfg_lit is not read) and dctx->expected = ZSTD_startingInputLength(f).  Its post begin_tabs
   implies DecIface3's TABS None (tstate_begin lxb) (begin_tabs_init); B's own callers need begin_tabs (the table
   pointers at the context's tables: ZSTD_loadDEntropy fills the tables but sets no pointer). *)
Definition ZSTD_decompressBegin_spec3s : ident * funspec :=
  DECLARE _ZSTD_decompressBegin
  WITH gv: globals, p: val, fs: fstate, f: Z, lxb: list Z
  PRE [ tptr t_dctx ]
    PROP (f = 0 \/ f = 1)
    PARAMS (p) GLOBALS (gv)
    SEP (zstd_globals gv; cfg_fmt p f; frame_fields p fs; tables_uninit p lxb)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; cfg_fmt p f; frame_fields p (fs_begin3 fs f); begin_tabs p lxb).

(* v2's spec after ZSTD_decompressBegin in a context of format f (fs_begin3 fs f in place of fs_begin fs) *)
Definition ZSTD_decompress_insertDictionary_spec3 : ident * funspec :=
  DECLARE _ZSTD_decompress_insertDictionary
  WITH gv: globals, p: val, fs: fstate, shk: share, dk: val, b: list Z, f: Z, lxb: list Z
  PRE [ tptr t_dctx, tptr tvoid, tulong ]
    PROP (readable_share shk; 0 < Zlength b <= 2 ^ 63 - 1; bytes_ok b)
    PARAMS (p; dk; Vlong (Int64.repr (Zlength b))) GLOBALS (gv)
    SEP (zstd_globals gv; frame_fields p (fs_begin3 fs f); begin_tabs p lxb;
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
             frame_fields p (fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                               (offset_val (Zlength b) dk) 0 (dm_id dm)) *
             EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb)
         end;
         data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk).

(* v2's spec with ctype 2 (ZSTD_dct_fullDict): dictionary_corrupted unless dict_formatted b; the content may be
   NULL for none (the DDict ZSTD_createDDict(NULL, 0) makes: dictSize 0 < 8, nothing is read) *)
Definition ZSTD_loadEntropy_intoDDict_spec3 : ident * funspec :=
  DECLARE _ZSTD_loadEntropy_intoDDict
  WITH gv: globals, q: val, sh: share, buf: val, b: list Z, ctype: Z
  PRE [ tptr t_ddict, tint ]
    PROP (readable_share sh; Zlength b <= 2 ^ 63 - 1; bytes_ok b; ctype = 0 \/ ctype = 1 \/ ctype = 2;
          buf = nullval -> b = nil)
    PARAMS (q; Vint (Int.repr ctype)) GLOBALS (gv)
    SEP (zstd_globals gv;
         field_at Ews t_ddict (DOT _dictContent) buf q;
         field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
         field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
         ent_blank (dd_ent q);
         field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
         bytes_at sh b buf)
  POST [ tulong ]
    EX r: Z, EX ores: option (dstate * Z),
    PROP (ld_rel b ores;
          match (if ctype =? 1 then Some (dict_raw b)
                 else if andb (ctype =? 2) (negb (dict_formatted b)) then None
                 else dict_auto_c b ores) with
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
         bytes_at sh b buf).

(* the group's specifications and context for an allocator class: ZSTD_initDDict_internal copies a DDict's bytes
   through the DDict's allocator (H_exports3's ZSTD_customMallocP) *)
Section DICT3.
Context {CMI: cmem_preds}.

(* one specification per function of ids_DICT, in that order *)
Definition DICT3_specs : funspecs :=
  [ ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec; ZSTD_copyDDictParameters_spec;
    ZSTD_loadEntropy_intoDDict_spec3; ZSTD_initDDict_internal_spec3 dent_def; ZSTD_refDictContent_spec;
    ZSTD_loadDEntropy_spec; ZSTD_decompress_insertDictionary_spec3; ZSTD_decompressBegin_spec3s;
    ZSTD_decompressBegin_usingDict_spec3 tabs_def; ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def ].

(* the context of the group's bodies in v3 (H's v3 exports: ZSTD_startingInputLength with the format) *)
Definition G_B03 : funspecs := Gprog ++ H_exports3.
Definition DICT3_G : funspecs := (G_B03 ++ ENT_exports ++ HUF_exports) ++ DICT3_specs.

Lemma DICT3_specs_ids : map fst DICT3_specs = ids_DICT.
Proof. reflexivity. Qed.

End DICT3.
