(* Subtree B split into four groups, each a subtree_ok obligation of its own, and the
   lemma that assembles them (subtree_compose).  The groups are proved against this split. *)
Require Export Zstd.proof.dec.B.BIface.
Local Open Scope logic.

Definition ids_ENT : list ident :=
  [ _FSE_decode_copy; _FSE_initDState; _FSE_decodeSymbol; _FSE_decodeSymbolFast;
    _FSE_readNCount_body; _FSE_readNCount_body_default; _FSE_readNCount_bmi2; _FSE_readNCount;
    _HUF_readStats_body; _HUF_readStats_body_default; _HUF_readStats_wksp;
    _FSE_buildDTable_internal; _FSE_decompress_usingDTable_generic; _FSE_decompress_wksp_body;
    _FSE_decompress_wksp_body_default; _FSE_decompress_wksp_bmi2;
    _ZSTD_buildFSETable_body; _ZSTD_buildFSETable_body_default; _ZSTD_buildFSETable ].

Definition ids_HUF : list ident :=
  [ _HUF_getDTableDesc; _HUF_getDTableLog; _HUF_initFastDStream; _HUF_DecompressFastArgs_init;
    _HUF_initRemainingDStream; _HUF_DEltX1_set4; _HUF_rescaleStats; _HUF_readDTableX1_wksp;
    _HUF_decodeSymbolX1; _HUF_decodeStreamX1; _HUF_decompress1X1_usingDTable_internal_body;
    _HUF_decompress4X1_usingDTable_internal_body; _HUF_decompress4X1_usingDTable_internal_default;
    _HUF_decompress4X1_usingDTable_internal_fast_c_loop; _HUF_decompress4X1_usingDTable_internal_fast;
    _HUF_decompress1X1_usingDTable_internal; _HUF_decompress4X1_usingDTable_internal;
    _HUF_decompress4X1_DCtx_wksp; _HUF_buildDEltX2U32; _HUF_buildDEltX2;
    _HUF_fillDTableX2ForWeight; _HUF_fillDTableX2Level2; _HUF_fillDTableX2; _HUF_readDTableX2_wksp;
    _HUF_decodeSymbolX2; _HUF_decodeLastSymbolX2; _HUF_decodeStreamX2;
    _HUF_decompress1X2_usingDTable_internal_body; _HUF_decompress4X2_usingDTable_internal_body;
    _HUF_decompress4X2_usingDTable_internal_default; _HUF_decompress4X2_usingDTable_internal_fast_c_loop;
    _HUF_decompress4X2_usingDTable_internal_fast; _HUF_decompress4X2_usingDTable_internal;
    _HUF_decompress1X2_usingDTable_internal; _HUF_decompress4X2_DCtx_wksp; _HUF_selectDecoder;
    _HUF_decompress1X_usingDTable; _HUF_decompress1X1_DCtx_wksp; _HUF_decompress4X_usingDTable;
    _HUF_decompress4X_hufOnly_wksp ].

Definition ids_BLK : list ident :=
  [ _ZSTD_wildcopy; _ZSTD_blockSizeMax; _ZSTD_allocateLiteralsBuffer; _ZSTD_decodeLiteralsBlock;
    _ZSTD_buildSeqTable_rle; _ZSTD_buildSeqTable; _ZSTD_decodeSeqHeaders; _ZSTD_seqCopy;
    _ZSTD_overlapCopy8; _ZSTD_safecopy; _ZSTD_safecopyDstBeforeSrc; _ZSTD_execSequenceEnd;
    _ZSTD_execSequenceEndSplitLitBuffer; _ZSTD_execSequence; _ZSTD_execSequenceSplitLitBuffer;
    _ZSTD_initFseState; _ZSTD_updateFseStateWithDInfo; _ZSTD_decodeSequence;
    _ZSTD_decompressSequences_bodySplitLitBuffer; _ZSTD_decompressSequences_body;
    _ZSTD_decompressSequences_default; _ZSTD_decompressSequencesSplitLitBuffer_default;
    _ZSTD_prefetchMatch; _ZSTD_decompressSequencesLong_body; _ZSTD_decompressSequencesLong_default;
    _ZSTD_decompressSequences; _ZSTD_decompressSequencesSplitLitBuffer; _ZSTD_decompressSequencesLong;
    _ZSTD_totalHistorySize; _ZSTD_getOffsetInfo; _ZSTD_maxShortOffset; _ZSTD_decompressBlock_internal ].

Definition ids_DICT : list ident :=
  [ _ZSTD_DDict_dictContent; _ZSTD_DDict_dictSize; _ZSTD_copyDDictParameters; _ZSTD_loadEntropy_intoDDict;
    _ZSTD_initDDict_internal; _ZSTD_refDictContent; _ZSTD_loadDEntropy; _ZSTD_decompress_insertDictionary;
    _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict; _ZSTD_decompressBegin_usingDDict ].

(* the context of every group: L0, H's exports *)
Definition G_B0 : funspecs := Gprog ++ H_exports.

Definition ENT_obligation : Prop := subtree_ok ids_ENT ENT_exports G_B0.
Definition HUF_obligation : Prop := subtree_ok ids_HUF HUF_exports (G_B0 ++ ENT_exports).
Definition BLK_obligation : Prop := subtree_ok ids_BLK BLK_exports (G_B0 ++ ENT_exports ++ HUF_exports).
Definition DICT_obligation : Prop := subtree_ok ids_DICT DICT_exports (G_B0 ++ ENT_exports ++ HUF_exports).
