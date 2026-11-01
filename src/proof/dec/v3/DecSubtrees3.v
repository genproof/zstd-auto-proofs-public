(* API v3: the decoder's proof split into subtrees (fixed: each subtree proves its obligation).
   v2's DecSubtrees.v (subtree_ok, subtree_api_ok, ids_H/B/FS/DEAD, H_api)
   stays in force; this file adds the v3 obligations:

     DecH3.H3_ok   : H3_obligation    (H with the format; + ZSTD_getDecompressedSize, getFrameHeader_advanced API)
     DecB3.B3_ok   : B3_obligation    (B with any format, exporting ZSTD_decompressBegin; fullDict DDicts; B's
                                       specifications imply the exports up to funspec_sub: B's own
                                       decompressBegin spec keeps the table pointers)
     DecFS3.FS3_ok : FS3_obligation   (FS with parameters, the DDict set, the buffer-less API; chooses DC, DD;
                                       also proves the API specifications of the three ZSTD_decompressBegin*,
                                       whose bodies are B's, from B's exported specifications)
   assembled with L0 and the dead functions into Zstd6.zstd_ok (DecAsm3.dec_assemble3).
   Six functions dead in v2 are reached by the v3 laws: ZSTD_getDecompressedSize (H) and
   ZSTD_initDStream_usingDict, ZSTD_initDStream_usingDDict, ZSTD_resetDStream, ZSTD_DCtx_setMaxWindowSize,
   ZSTD_DCtx_setFormat (FS). *)
Require Export Zstd.proof.dec.DecSubtrees.
Require Export Zstd.proof.dec.v3.DecIface3.

Definition ids_H3 : list ident := ids_H ++ [ _ZSTD_getDecompressedSize ].

Definition ids_B3 : list ident := ids_B.

Definition ids_FS3 : list ident :=
  ids_FS ++ [ _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict; _ZSTD_resetDStream;
              _ZSTD_DCtx_setMaxWindowSize; _ZSTD_DCtx_setFormat;
              (* contexts with their own allocator (the res_ laws) *)
              _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_decodingBufferSize_min;
              _ZSTD_estimateDStreamSize ].

Definition ids_DEAD3 : list ident :=
  [ _ERR_getErrorName;
    _FSE_versionNumber;
    _FSE_getErrorName;
    _HUF_isError;
    _HUF_getErrorName;
    _HUF_readStats;
    _ERR_getErrorString;
    _FSE_buildDTable_wksp;
    _XXH_malloc;
    _XXH_free;
    _XXH_swap32;
    _XXH_readBE32;
    _ZSTD_XXH_versionNumber;
    _XXH32_round;
    _XXH32_avalanche;
    _XXH32_finalize;
    _XXH32_endian_align;
    _ZSTD_XXH32;
    _ZSTD_XXH32_createState;
    _ZSTD_XXH32_freeState;
    _ZSTD_XXH32_copyState;
    _ZSTD_XXH32_reset;
    _ZSTD_XXH32_update;
    _ZSTD_XXH32_digest;
    _ZSTD_XXH32_canonicalFromHash;
    _ZSTD_XXH32_hashFromCanonical;
    _XXH_swap64;
    _XXH_readBE64;
    _ZSTD_XXH64_createState;
    _ZSTD_XXH64_freeState;
    _ZSTD_XXH64_copyState;
    _ZSTD_XXH64_canonicalFromHash;
    _ZSTD_XXH64_hashFromCanonical;
    _ZSTD_versionNumber;
    _ZSTD_versionString;
    _ZSTD_getErrorName;
    _ZSTD_getErrorString;
    _ZSTD_isDeterministicBuild;
    _HUF_decompress1X2_DCtx_wksp;
    _HUF_decompress1X_DCtx_wksp;
    _ZSTD_initStaticDDict;
    _ZSTD_estimateDDictSize;
    _ZSTD_sizeof_DDict;
    _ZSTD_sizeof_DCtx;
    _ZSTD_initStaticDCtx;
    _ZSTD_copyDCtx;
    _ZSTD_decompressionMargin;
    _ZSTD_insertBlock;
    _ZSTD_initStaticDStream;
    _ZSTD_DStreamInSize;
    _ZSTD_DCtx_getParameter;
    _ZSTD_sizeof_DStream;
    _ZSTD_estimateDStreamSize_fromFrame;
    _ZSTD_decompressStream_simpleArgs;
    _ZSTD_decodeLiteralsBlock_wrapper;
    _ZSTD_decompressBlock_deprecated;
    _ZSTD_decompressBlock
  ].

(* the API specifications H proves: v2's H_api and ZSTD_getDecompressedSize literally (FS's bodies may call
   them), ZSTD_getFrameHeader_advanced up to funspec_sub (its specification in S is the export
   ZSTD_getFrameHeader_advanced_spec3) *)
Definition H_api3 : funspecs := H_api ++ [ ZSTD_getDecompressedSize_aspec ].

(* H's exports hold for any allocator class (the allocation helpers' specifications mention CM, CB) *)
Definition H3_obligation : Prop :=
  forall {CMI: cmem_preds},
  exists S: funspecs, map fst S = ids_H3 /\ incl (H_exports3 (CMI:=CMI) ++ H_api3) S /\
    api_sub [ ZSTD_getFrameHeader_advanced_aspec ] S /\ Forall (body_ok (Gprog ++ S)) S.

(* B's representation does not depend on the allocator class; its exports do through ZSTD_initDDict_internal, which
   copies a DDict's bytes through the DDict's allocator (ZSTD_customMallocP): for any class.  (B's other bodies call
   no allocation helper: they can be proved with the default class's H exports and lifted, the helpers'
   specifications for any class implying those of cmem_none.) *)
Definition B3_obligation : Prop :=
  exists (DENT: dent_pred) (TABS: tabs_pred),
    DENT_OK DENT /\ TABS_OK TABS /\
    forall {CMI: cmem_preds},
      subtree_api_ok ids_B3 (B_exports3 (CMI:=CMI) DENT TABS) (Gprog ++ H_exports3 (CMI:=CMI)).

Section FSApi.
Context {CMI: cmem_preds}.

(* the API specifications FS proves for its own functions *)
Definition FS_api3 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    : funspecs :=
  [ ZSTD_decompress_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDict_spec DC;
    ZSTD_decompress_usingDDict_spec DC DD;
    ZSTD_createDCtx_spec DC; ZSTD_createDStream_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_freeDStream_spec DC;
    ZSTD_DCtx_reset_spec DC; ZSTD_initDStream_spec DC; ZSTD_DCtx_setParameter_spec DC;
    ZSTD_createDDict_spec DD; ZSTD_createDDict_byReference_spec DD; ZSTD_freeDDict_spec DD;
    ZSTD_getDictID_fromDDict_spec DD;
    ZSTD_DCtx_loadDictionary_byReference_spec DC; ZSTD_DCtx_loadDictionary_spec DC;
    ZSTD_DCtx_refPrefix_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
    ZSTD_decompressStream_spec DC DD;
    ZSTD_DCtx_setFormat_aspec DC; ZSTD_DCtx_setMaxWindowSize_aspec DC; ZSTD_resetDStream_aspec DC;
    ZSTD_DCtx_loadDictionary_advanced_aspec DC; ZSTD_DCtx_refPrefix_advanced_aspec DC;
    ZSTD_initDStream_usingDict_aspec DC; ZSTD_initDStream_usingDDict_aspec DC DD;
    ZSTD_nextSrcSizeToDecompress_aspec DC; ZSTD_nextInputType_aspec DC;
    ZSTD_decompressContinue_aspec DC DD;
    ZSTD_createDCtx_advancedP_spec DC; ZSTD_estimateDCtxSize_spec; ZSTD_estimateDStreamSize_spec ].

(* the API specifications of B's functions ZSTD_decompressBegin*, which FS proves (they mention DC, DD) *)
Definition B_api3 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    : funspecs :=
  [ ZSTD_decompressBegin_aspec DC; ZSTD_decompressBegin_usingDict_aspec DC;
    ZSTD_decompressBegin_usingDDict_aspec DC DD ].

End FSApi.

(* for any allocator class; the contexts DC hold their own allocator's state (dc_cm_ok) *)
Definition FS3_obligation : Prop :=
  forall {CMI: cmem_preds} (DENT: dent_pred) (TABS: tabs_pred), DENT_OK DENT -> TABS_OK TABS ->
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    subtree_api_ok ids_FS3 (FS_api3 (CMI:=CMI) DC DD)
      (Gprog ++ H_exports3 (CMI:=CMI) ++ H_api3 ++ B_exports3 (CMI:=CMI) DENT TABS) /\
    api_sub (B_api3 DC DD) (B_exports3 (CMI:=CMI) DENT TABS) /\ dc_cm_ok (CMI:=CMI) DC.
