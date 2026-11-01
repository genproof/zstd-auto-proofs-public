(* Group BLK split into four sub-groups, each a subtree_ok obligation of its own
   against the group's context G_BLK and the exports of the sub-groups it calls.  BBlk.v assembles them
   with BCompose.subtree_compose. *)
Require Export Zstd.proof.dec.B.blk.BlkIface.
Local Open Scope logic.

(* the context of group BLK (BGroups.BLK_obligation) *)
Definition G_BLK : funspecs := G_B0 ++ ENT_exports ++ HUF_exports.

(* LIT: the literals section *)
Definition ids_LIT : list ident :=
  [ _ZSTD_blockSizeMax; _ZSTD_allocateLiteralsBuffer; _ZSTD_decodeLiteralsBlock ].
Definition LIT_exports : funspecs := [ ZSTD_blockSizeMax_spec; ZSTD_decodeLiteralsBlock_spec ].
Definition LIT_imports : funspecs := [].

(* HDR: the sequences section's header and tables *)
Definition ids_HDR : list ident :=
  [ _ZSTD_buildSeqTable_rle; _ZSTD_buildSeqTable; _ZSTD_decodeSeqHeaders ].
Definition HDR_exports : funspecs := [ ZSTD_decodeSeqHeaders_spec ].
Definition HDR_imports : funspecs := [].

(* SEQ: the sequence decoders (internal specifications are SEQ's choice) *)
Definition ids_SEQ : list ident :=
  [ _ZSTD_wildcopy; _ZSTD_seqCopy; _ZSTD_overlapCopy8; _ZSTD_safecopy; _ZSTD_safecopyDstBeforeSrc;
    _ZSTD_execSequenceEnd; _ZSTD_execSequenceEndSplitLitBuffer; _ZSTD_execSequence;
    _ZSTD_execSequenceSplitLitBuffer; _ZSTD_initFseState; _ZSTD_updateFseStateWithDInfo;
    _ZSTD_decodeSequence; _ZSTD_decompressSequences_bodySplitLitBuffer; _ZSTD_decompressSequences_body;
    _ZSTD_decompressSequences_default; _ZSTD_decompressSequencesSplitLitBuffer_default;
    _ZSTD_prefetchMatch; _ZSTD_decompressSequencesLong_body; _ZSTD_decompressSequencesLong_default;
    _ZSTD_decompressSequences; _ZSTD_decompressSequencesSplitLitBuffer; _ZSTD_decompressSequencesLong ].
Definition SEQ_exports : funspecs :=
  [ ZSTD_decompressSequences_spec; ZSTD_decompressSequencesSplitLitBuffer_spec;
    ZSTD_decompressSequencesLong_spec ].
Definition SEQ_imports : funspecs := [].

(* TOP: ZSTD_decompressBlock_internal and its helpers *)
Definition ids_TOP : list ident :=
  [ _ZSTD_totalHistorySize; _ZSTD_getOffsetInfo; _ZSTD_maxShortOffset; _ZSTD_decompressBlock_internal ].
Definition TOP_exports : funspecs := BLK_exports.
Definition TOP_imports : funspecs :=
  [ ZSTD_blockSizeMax_spec; ZSTD_decodeLiteralsBlock_spec; ZSTD_decodeSeqHeaders_spec;
    ZSTD_decompressSequences_spec; ZSTD_decompressSequencesSplitLitBuffer_spec;
    ZSTD_decompressSequencesLong_spec ].

Definition LIT_obligation : Prop := subtree_ok ids_LIT LIT_exports (G_BLK ++ LIT_imports).
Definition HDR_obligation : Prop := subtree_ok ids_HDR HDR_exports (G_BLK ++ HDR_imports).
Definition SEQ_obligation : Prop := subtree_ok ids_SEQ SEQ_exports (G_BLK ++ SEQ_imports).
Definition TOP_obligation : Prop := subtree_ok ids_TOP TOP_exports (G_BLK ++ TOP_imports).

(* The predefined sequence tables in the globals (BRep.predef_cells): the three tables, each with its
   header cell {1,1,1,log} read as ZSTD_seqSymbol_header {fastMode = predef_fm; tableLog}, and the rest of
   the globals.  Used by SEQ (reading the tables) and TOP (ZSTD_getOffsetInfo); proved in BlkGlobals.v. *)
Definition predef_tabs (gv: globals) : mpred :=
  seqtab_at_fm Ers KLL LL_predef predef_fm (gv _LL_defaultDTable) *
  seqtab_at_fm Ers KOF OF_predef predef_fm (gv _OF_defaultDTable) *
  seqtab_at_fm Ers KML ML_predef predef_fm (gv _ML_defaultDTable).

Definition GLOBALS_obligation : Prop := forall gv: globals, exists R: mpred, zstd_globals gv = predef_tabs gv * R.
