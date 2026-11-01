(* Subtree FS of the decoder, API v3: the context of every FS3 body and the obligations of the FS3 parts (fixed: each
   part is proved against them).

   FS3_G DENT TABS SR BR = Gprog ++ H's v3 exports and API ++ B's v3 exports ++ FS3_fixed: the specifications
   fixed by FSSpecs3 (internal) and Spec_api6 (API, with DC3_of SR BR and DD_of).  Every fixed body holds for ANY
   stream relation SR and ANY buffer-less relation BR (chosen by the streaming / buffer-less parts) and any
   DENT/TABS of B. *)
Require Export Zstd.proof.dec.v3.FS.FSSpecs3.
Local Open Scope logic.

Section G.
Context {CMI: cmem_preds}.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.

Definition DC3x : globals -> val -> dctx_st -> mpred := DC3_of DENT TABS SR BR.
Definition DD3x : globals -> val -> ddict_st -> mpred := DD3_of DENT.

Definition FS3_fixed : funspecs :=
  [ (* DDicts *)
    ZSTD_createDDict_advancedP_spec3 DENT; ZSTD_createDDict_spec DD3x; ZSTD_createDDict_byReference_spec DD3x;
    ZSTD_freeDDict_int_spec; ZSTD_getDictID_fromDDict_int_spec;
    (* the DDict set *)
    ZSTD_DDictHashSet_getDDict_spec; ZSTD_createDDictHashSet_spec; ZSTD_freeDDictHashSet_spec;
    ZSTD_DDictHashSet_addDDict_spec; ZSTD_DCtx_selectFrameDDict_spec DENT;
    (* contexts *)
    ZSTD_DCtx_resetParameters_spec; ZSTD_initDCtx_internal_spec3 DENT TABS;
    ZSTD_createDCtx_internal_spec3 DENT TABS; ZSTD_createDCtx_spec DC3x; ZSTD_createDStream_spec DC3x;
    ZSTD_freeDCtx_spec DC3x; ZSTD_freeDStream_spec DC3x;
    ZSTD_clearDict_spec DENT; ZSTD_getDDict_spec DENT; ZSTD_DCtx_refDDict_int_spec3 DENT TABS;
    ZSTD_dParam_getBoundsP_spec3; ZSTD_dParam_withinBounds_spec3; ZSTD_DCtx_setParameter_spec DC3x;
    ZSTD_DCtx_reset_spec DC3x; ZSTD_initDStream_spec DC3x; ZSTD_resetDStream_aspec DC3x;
    ZSTD_DCtx_setMaxWindowSize_aspec DC3x; ZSTD_DCtx_setFormat_aspec DC3x;
    (* dictionary loading *)
    ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS; ZSTD_DCtx_loadDictionary_byReference_spec DC3x;
    ZSTD_DCtx_loadDictionary_spec DC3x; ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS; ZSTD_DCtx_refPrefix_spec DC3x;
    ZSTD_initDStream_usingDict_aspec DC3x; ZSTD_initDStream_usingDDict_aspec DC3x DD3x;
    (* frames *)
    ZSTD_DCtx_trace_end_spec; ZSTD_checkContinuity_spec; ZSTD_decodeFrameHeader_spec3 DENT;
    ZSTD_copyRawBlock_spec; ZSTD_setRleBlock_spec;
    (* one-shot *)
    ZSTD_decompressMultiFrame_spec3 DENT TABS; ZSTD_decompress_usingDDict_int_spec3 DENT TABS;
    ZSTD_decompress_usingDict_spec DC3x; ZSTD_decompressDCtx_spec DC3x DD3x; ZSTD_decompress_spec;
    (* the small streaming helpers *)
    ZSTD_limitCopy_spec; ZSTD_nextSrcSizeToDecompress_spec; ZSTD_nextSrcSizeToDecompressWithInputSize_spec;
    ZSTD_nextInputType_spec; ZSTD_isSkipFrame_spec; ZSTD_decodingBufferSize_internal_spec;
    ZSTD_DCtx_isOverflow_spec; ZSTD_DCtx_updateOversizedDuration_spec; ZSTD_DCtx_isOversizedTooLong_spec;
    ZSTD_outBuffer_copy_spec; ZSTD_checkOutBuffer_spec;
    (* contexts with their own allocator, and the estimates *)
    ZSTD_createDCtx_advancedP_spec DC3x; ZSTD_estimateDCtxSize_spec; ZSTD_decodingBufferSize_min_spec;
    ZSTD_estimateDStreamSize_spec ].

Definition FS3_G : funspecs := Gprog ++ H_exports3 ++ H_api3 ++ B_exports3 DENT TABS ++ FS3_fixed.

End G.

Section Obl.
Context {CMI: cmem_preds}.

(* ---------- the obligations of the parts ---------- *)

(* a fixed body: for ANY DENT/TABS of B (with the OK facts), ANY SR and ANY BR *)
Definition FS3_body (f: dent_pred -> tabs_pred -> srel3 -> blrel -> ident * funspec) : Prop :=
  forall DENT TABS SR BR, DENT_OK DENT -> TABS_OK TABS -> body_ok (FS3_G DENT TABS SR BR) (f DENT TABS SR BR).

(* the internal specifications imply the API ones (the API functions the decoder also calls internally) *)
Definition FS3_sub (fi fa: dent_pred -> tabs_pred -> srel3 -> blrel -> ident * funspec) : Prop :=
  forall DENT TABS SR BR, DENT_OK DENT -> TABS_OK TABS -> funspec_sub (snd (fi DENT TABS SR BR)) (snd (fa DENT TABS SR BR)).

(* the frames part chooses ZSTD_decompressFrame's specification sf; ZSTD_decompressMultiFrame is proved with it *)
Definition FRAMES3_obligation : Prop :=
  forall DENT TABS, DENT_OK DENT -> TABS_OK TABS ->
  exists sf: funspec, forall SR BR,
    body_ok (FS3_G DENT TABS SR BR ++ [(_ZSTD_decompressFrame, sf)]) (_ZSTD_decompressFrame, sf) /\
    body_ok (FS3_G DENT TABS SR BR ++ [(_ZSTD_decompressFrame, sf)]) (ZSTD_decompressMultiFrame_spec3 DENT TABS).

(* the set part chooses the specifications of the hash set's internals (this order) and proves them, the four
   fixed set functions, and what the probe means *)
Definition set3_ids : list ident :=
  [ _ZSTD_DDictHashSet_getIndex; _ZSTD_DDictHashSet_emplaceDDict; _ZSTD_DDictHashSet_expand ].

Definition SET3_obligation : Prop :=
  hs_probe_ok /\
  forall DENT TABS, DENT_OK DENT -> TABS_OK TABS ->
  exists ss: funspecs, map fst ss = set3_ids /\ forall SR BR,
    Forall (body_ok (FS3_G DENT TABS SR BR ++ ss))
      (ss ++ [ ZSTD_DDictHashSet_getDDict_spec; ZSTD_createDDictHashSet_spec; ZSTD_freeDDictHashSet_spec;
               ZSTD_DDictHashSet_addDDict_spec ]).

(* the streaming part chooses the stream relation SR and the specifications of ZSTD_decompressContinue (its
   streaming use) and ZSTD_decompressContinueStream (this order), and proves them and ZSTD_decompressStream *)
Definition stream3_ids : list ident := [ _ZSTD_decompressContinue; _ZSTD_decompressContinueStream ].

Definition STREAM3_obligation : Prop :=
  forall DENT TABS, DENT_OK DENT -> TABS_OK TABS ->
  exists (SR: srel3) (ss: funspecs),
    map fst ss = stream3_ids /\ forall BR,
    Forall (body_ok (FS3_G DENT TABS SR BR ++ ss)) (ZSTD_decompressStream_spec (DC3x DENT TABS SR BR) (DD3x DENT) :: ss).

(* the buffer-less part chooses the buffer-less relation BR and proves the buffer-less API: ZSTD_decompressContinue
   (its body, against the API specification), ZSTD_nextSrcSizeToDecompress and ZSTD_nextInputType (from the small
   helpers' specifications), and the three ZSTD_decompressBegin* (from B's exports) *)
Definition BL3_obligation : Prop :=
  forall DENT TABS, DENT_OK DENT -> TABS_OK TABS ->
  exists BR: blrel, forall SR: srel3,
    body_ok (FS3_G DENT TABS SR BR) (ZSTD_decompressContinue_aspec (DC3x DENT TABS SR BR) (DD3x DENT)) /\
    funspec_sub (snd ZSTD_nextSrcSizeToDecompress_spec)
                (snd (ZSTD_nextSrcSizeToDecompress_aspec (DC3x DENT TABS SR BR))) /\
    funspec_sub (snd ZSTD_nextInputType_spec) (snd (ZSTD_nextInputType_aspec (DC3x DENT TABS SR BR))) /\
    api_sub (B_api3 (DC3x DENT TABS SR BR) (DD3x DENT)) (B_exports3 DENT TABS).

End Obl.
