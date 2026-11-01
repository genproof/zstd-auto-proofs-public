(* The decoder's proof split into subtrees, each proved against the fixed interfaces of DecIface.v.

   subtree_ok ids exports G: some list S of specifications of exactly the functions ids (in this order)
   contains the exported specifications, and every function satisfies its specification in the context
   G ++ S (Layer.body_ok).  G = the L0 layer (Gprog) and the exports of the subtrees it may call.
   A subtree may give a function no law reaches (a dead branch: the fast Huffman loops, the DDict hash
   set, ...) the vacuous specification (Layer.body_ok_vacuous) when its callers show the call unreachable.

   The obligations (one file each):
     DecH.H_ok   : H_obligation      (headers, inspection API, allocation helpers)
     DecB.B_ok   : B_obligation      (blocks, entropy, dictionary entropy; chooses DENT, TABS)
     DecFS.FS_ok : FS_obligation     (frames, streaming, contexts, dictionaries; chooses DC, DD)
   Zstd6.zstd_ok assembles them with L0 and the dead functions. *)
Require Export Zstd.proof.zstd.Layer.
Require Export Zstd.proof.dec.DecIface.
Require Export Zstd.proof.top.ZstdOK6.

Definition subtree_ok (ids: list ident) (exports: funspecs) (G: funspecs) : Prop :=
  exists S: funspecs, map fst S = ids /\ incl exports S /\ Forall (body_ok (G ++ S)) S.

(* the same for a subtree whose exports are API specifications, which its own specifications need only
   imply (ZstdOK6.api_sub: up to funspec_sub; the decoder also calls some API functions internally) *)
Definition subtree_api_ok (ids: list ident) (api: funspecs) (G: funspecs) : Prop :=
  exists S: funspecs, map fst S = ids /\ api_sub api S /\ Forall (body_ok (G ++ S)) S.

Definition ids_H : list ident :=
  [ _ZSTD_customMallocP;
    _ZSTD_customCallocP;
    _ZSTD_customFreeP;
    _ZSTD_customMem_copy;
    _ZSTD_startingInputLength;
    _ZSTD_isFrame;
    _ZSTD_isSkippableFrame;
    _ZSTD_frameHeaderSize_internal;
    _ZSTD_frameHeaderSize;
    _ZSTD_getFrameHeader_advanced;
    _ZSTD_getFrameHeader;
    _ZSTD_getFrameContentSize;
    _readSkippableFrameSize;
    _ZSTD_readSkippableFrame;
    _ZSTD_findDecompressedSize;
    _ZSTD_errorFrameSizeInfo;
    _ZSTD_findFrameSizeInfo;
    _ZSTD_findFrameCompressedSize_advanced;
    _ZSTD_findFrameCompressedSize;
    _ZSTD_decompressBound;
    _ZSTD_getDictID_fromDict;
    _ZSTD_getDictID_fromFrame;
    _ZSTD_DStreamOutSize;
    _ZSTD_getcBlockSize ].

Definition ids_B : list ident :=
  [ _FSE_decode_copy;
    _FSE_initDState;
    _FSE_decodeSymbol;
    _FSE_decodeSymbolFast;
    _FSE_readNCount_body;
    _FSE_readNCount_body_default;
    _FSE_readNCount_bmi2;
    _FSE_readNCount;
    _HUF_readStats_body;
    _HUF_readStats_body_default;
    _HUF_readStats_wksp;
    _FSE_buildDTable_internal;
    _FSE_decompress_usingDTable_generic;
    _FSE_decompress_wksp_body;
    _FSE_decompress_wksp_body_default;
    _FSE_decompress_wksp_bmi2;
    _ZSTD_wildcopy;
    _HUF_getDTableDesc;
    _HUF_getDTableLog;
    _HUF_initFastDStream;
    _HUF_DecompressFastArgs_init;
    _HUF_initRemainingDStream;
    _HUF_DEltX1_set4;
    _HUF_rescaleStats;
    _HUF_readDTableX1_wksp;
    _HUF_decodeSymbolX1;
    _HUF_decodeStreamX1;
    _HUF_decompress1X1_usingDTable_internal_body;
    _HUF_decompress4X1_usingDTable_internal_body;
    _HUF_decompress4X1_usingDTable_internal_default;
    _HUF_decompress4X1_usingDTable_internal_fast_c_loop;
    _HUF_decompress4X1_usingDTable_internal_fast;
    _HUF_decompress1X1_usingDTable_internal;
    _HUF_decompress4X1_usingDTable_internal;
    _HUF_decompress4X1_DCtx_wksp;
    _HUF_buildDEltX2U32;
    _HUF_buildDEltX2;
    _HUF_fillDTableX2ForWeight;
    _HUF_fillDTableX2Level2;
    _HUF_fillDTableX2;
    _HUF_readDTableX2_wksp;
    _HUF_decodeSymbolX2;
    _HUF_decodeLastSymbolX2;
    _HUF_decodeStreamX2;
    _HUF_decompress1X2_usingDTable_internal_body;
    _HUF_decompress4X2_usingDTable_internal_body;
    _HUF_decompress4X2_usingDTable_internal_default;
    _HUF_decompress4X2_usingDTable_internal_fast_c_loop;
    _HUF_decompress4X2_usingDTable_internal_fast;
    _HUF_decompress4X2_usingDTable_internal;
    _HUF_decompress1X2_usingDTable_internal;
    _HUF_decompress4X2_DCtx_wksp;
    _HUF_selectDecoder;
    _HUF_decompress1X_usingDTable;
    _HUF_decompress1X1_DCtx_wksp;
    _HUF_decompress4X_usingDTable;
    _HUF_decompress4X_hufOnly_wksp;
    _ZSTD_DDict_dictContent;
    _ZSTD_DDict_dictSize;
    _ZSTD_copyDDictParameters;
    _ZSTD_loadEntropy_intoDDict;
    _ZSTD_initDDict_internal;
    _ZSTD_refDictContent;
    _ZSTD_loadDEntropy;
    _ZSTD_decompress_insertDictionary;
    _ZSTD_decompressBegin;
    _ZSTD_decompressBegin_usingDict;
    _ZSTD_decompressBegin_usingDDict;
    _ZSTD_blockSizeMax;
    _ZSTD_allocateLiteralsBuffer;
    _ZSTD_decodeLiteralsBlock;
    _ZSTD_buildSeqTable_rle;
    _ZSTD_buildFSETable_body;
    _ZSTD_buildFSETable_body_default;
    _ZSTD_buildFSETable;
    _ZSTD_buildSeqTable;
    _ZSTD_decodeSeqHeaders;
    _ZSTD_seqCopy;
    _ZSTD_overlapCopy8;
    _ZSTD_safecopy;
    _ZSTD_safecopyDstBeforeSrc;
    _ZSTD_execSequenceEnd;
    _ZSTD_execSequenceEndSplitLitBuffer;
    _ZSTD_execSequence;
    _ZSTD_execSequenceSplitLitBuffer;
    _ZSTD_initFseState;
    _ZSTD_updateFseStateWithDInfo;
    _ZSTD_decodeSequence;
    _ZSTD_decompressSequences_bodySplitLitBuffer;
    _ZSTD_decompressSequences_body;
    _ZSTD_decompressSequences_default;
    _ZSTD_decompressSequencesSplitLitBuffer_default;
    _ZSTD_prefetchMatch;
    _ZSTD_decompressSequencesLong_body;
    _ZSTD_decompressSequencesLong_default;
    _ZSTD_decompressSequences;
    _ZSTD_decompressSequencesSplitLitBuffer;
    _ZSTD_decompressSequencesLong;
    _ZSTD_totalHistorySize;
    _ZSTD_getOffsetInfo;
    _ZSTD_maxShortOffset;
    _ZSTD_decompressBlock_internal ].

Definition ids_FS : list ident :=
  [ _ZSTD_limitCopy;
    _ZSTD_createDDict_advancedP;
    _ZSTD_createDDict;
    _ZSTD_createDDict_byReference;
    _ZSTD_freeDDict;
    _ZSTD_getDictID_fromDDict;
    _ZSTD_DDictHashSet_getIndex;
    _ZSTD_DDictHashSet_emplaceDDict;
    _ZSTD_DDictHashSet_expand;
    _ZSTD_DDictHashSet_getDDict;
    _ZSTD_createDDictHashSet;
    _ZSTD_freeDDictHashSet;
    _ZSTD_DDictHashSet_addDDict;
    _ZSTD_DCtx_resetParameters;
    _ZSTD_initDCtx_internal;
    _ZSTD_createDCtx_internal;
    _ZSTD_createDCtx;
    _ZSTD_clearDict;
    _ZSTD_freeDCtx;
    _ZSTD_DCtx_selectFrameDDict;
    _ZSTD_decodeFrameHeader;
    _ZSTD_copyRawBlock;
    _ZSTD_setRleBlock;
    _ZSTD_DCtx_trace_end;
    _ZSTD_decompressFrame;
    _ZSTD_decompressMultiFrame;
    _ZSTD_decompress_usingDict;
    _ZSTD_getDDict;
    _ZSTD_decompressDCtx;
    _ZSTD_decompress;
    _ZSTD_nextSrcSizeToDecompress;
    _ZSTD_nextSrcSizeToDecompressWithInputSize;
    _ZSTD_nextInputType;
    _ZSTD_isSkipFrame;
    _ZSTD_decompressContinue;
    _ZSTD_decompress_usingDDict;
    _ZSTD_createDStream;
    _ZSTD_freeDStream;
    _ZSTD_DCtx_loadDictionary_advanced;
    _ZSTD_DCtx_loadDictionary_byReference;
    _ZSTD_DCtx_loadDictionary;
    _ZSTD_DCtx_refPrefix_advanced;
    _ZSTD_DCtx_refPrefix;
    _ZSTD_initDStream;
    _ZSTD_DCtx_refDDict;
    _ZSTD_dParam_getBoundsP;
    _ZSTD_dParam_withinBounds;
    _ZSTD_DCtx_setParameter;
    _ZSTD_DCtx_reset;
    _ZSTD_decodingBufferSize_internal;
    _ZSTD_DCtx_isOverflow;
    _ZSTD_DCtx_updateOversizedDuration;
    _ZSTD_DCtx_isOversizedTooLong;
    _ZSTD_outBuffer_copy;
    _ZSTD_checkOutBuffer;
    _ZSTD_decompressContinueStream;
    _ZSTD_decompressStream;
    _ZSTD_checkContinuity ].

Definition ids_DEAD : list ident :=
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
    _ZSTD_estimateDCtxSize;
    _ZSTD_initStaticDCtx;
    _ZSTD_copyDCtx;
    _ZSTD_getDecompressedSize;
    _ZSTD_decompressionMargin;
    _ZSTD_insertBlock;
    _ZSTD_initStaticDStream;
    _ZSTD_DStreamInSize;
    _ZSTD_initDStream_usingDict;
    _ZSTD_initDStream_usingDDict;
    _ZSTD_resetDStream;
    _ZSTD_DCtx_setMaxWindowSize;
    _ZSTD_DCtx_setFormat;
    _ZSTD_DCtx_getParameter;
    _ZSTD_sizeof_DStream;
    _ZSTD_decodingBufferSize_min;
    _ZSTD_estimateDStreamSize;
    _ZSTD_estimateDStreamSize_fromFrame;
    _ZSTD_decompressStream_simpleArgs;
    _ZSTD_decodeLiteralsBlock_wrapper;
    _ZSTD_decompressBlock_deprecated;
    _ZSTD_decompressBlock ].

(* the API specifications H proves (they do not mention DC or DD) *)
Definition H_api : funspecs :=
  [ ZSTD_findFrameCompressedSize_spec; ZSTD_getFrameContentSize_spec; ZSTD_findDecompressedSize_spec;
    ZSTD_decompressBound_spec; ZSTD_frameHeaderSize_spec; ZSTD_getDictID_fromFrame_spec;
    ZSTD_isFrame_spec; ZSTD_isSkippableFrame_spec; ZSTD_getFrameHeader_spec; ZSTD_readSkippableFrame_spec;
    ZSTD_getDictID_fromDict_spec; ZSTD_DStreamOutSize_spec ].

(* the API specifications FS proves *)
Definition FS_api (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    : funspecs :=
  [ ZSTD_decompress_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDict_spec DC;
    ZSTD_decompress_usingDDict_spec DC DD;
    ZSTD_createDCtx_spec DC; ZSTD_createDStream_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_freeDStream_spec DC;
    ZSTD_DCtx_reset_spec DC; ZSTD_initDStream_spec DC; ZSTD_DCtx_setParameter_spec DC;
    ZSTD_createDDict_spec DD; ZSTD_createDDict_byReference_spec DD; ZSTD_freeDDict_spec DD;
    ZSTD_getDictID_fromDDict_spec DD;
    ZSTD_DCtx_loadDictionary_byReference_spec DC; ZSTD_DCtx_loadDictionary_spec DC;
    ZSTD_DCtx_refPrefix_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
    ZSTD_decompressStream_spec DC DD ].

Definition H_obligation : Prop :=
  subtree_ok ids_H (H_exports ++ H_api) Gprog.

Definition B_obligation : Prop :=
  exists (DENT: dent_pred) (TABS: tabs_pred),
    DENT_OK DENT /\ TABS_OK TABS /\
    subtree_ok ids_B (B_exports DENT TABS) (Gprog ++ H_exports).

Definition FS_obligation : Prop :=
  forall (DENT: dent_pred) (TABS: tabs_pred), DENT_OK DENT -> TABS_OK TABS ->
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    subtree_api_ok ids_FS (FS_api DC DD) (Gprog ++ H_exports ++ H_api ++ B_exports DENT TABS).
