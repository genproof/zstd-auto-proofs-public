(* v2's FSRep (src/proof/dec/FS/FSRep.v) for API v3.1+, as a NEW file: everything but the parts that mention v2's
   ddict_st / dsrc (DD_of, dict_rel, last_rel, base_rel, srel, DC_of), which FSRep3 restates. *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Local Open Scope logic.

(* ---------- updates of the frame fields ---------- *)
Definition fsu_previousDstEnd (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := v; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_gpDictCopy (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := v; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_prefixStart (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := v; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_virtualStart (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := v; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_dictEnd (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := v; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_expected (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := v; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_fParams (fs: fstate) (v: reptype t_fh) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := v; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_processedCSize (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := v; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_decodedSize (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := v; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_bType (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := v; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_stage (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := v; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_xxh (fs: fstate) (v: option (list Z)) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := v; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_headerSize (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := v; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_validateChecksum (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := v; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_rleSize (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := v; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_isFrameDecompression (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := v; fs_dictID := fs_dictID fs; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_dictID (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := v; fs_ddictIsCold := fs_ddictIsCold fs |}.
Definition fsu_ddictIsCold (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs; fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs; fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs; fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs; fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs; fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs; fs_dictID := fs_dictID fs; fs_ddictIsCold := v |}.

Definition veqb (a b: val) : bool := if Val.eq a b then true else false.

(* the distance a - b of two pointers (0 otherwise) *)
Definition vptr_diff (a b: val) : Z :=
  match a, b with Vptr _ x, Vptr _ y => Ptrofs.unsigned x - Ptrofs.unsigned y | _, _ => 0 end.

(* bytes bs written at offset d of the cells oc *)
Definition put_bytes (oc: list val) (d: Z) (bs: list Z) : list val :=
  sublist 0 d oc ++ zbytes bs ++ sublist (d + Zlength bs) (Zlength oc) oc.

Definition t_bounds : type := Tstruct ___gp_ZSTD_bounds noattr.
Definition ZSTD_MAXWINDOWSIZE_DEFAULT : Z := 2 ^ 27 + 1.

(* ---------- all fields uninitialised (malloc'd struct) ---------- *)
(* the padding of the two structs (sizeof ZSTD_DCtx_s = 95976, of ZSTD_DDict_s = 27352): bytes no field
   covers; data_at_ of the struct = its fields * its padding *)
Definition dctx_pad (p: val) : mpred :=
  memory_block Ews 4 (offset_val 29884 p) * memory_block Ews 4 (offset_val 29900 p) *
  memory_block Ews 4 (offset_val 30124 p) * memory_block Ews 4 (offset_val 30188 p) *
  memory_block Ews 4 (offset_val 30220 p) * memory_block Ews 4 (offset_val 30332 p) *
  memory_block Ews 2 (offset_val 95966 p).

Definition ddict_pad (q: val) : mpred := memory_block Ews 4 (offset_val 27324 q).

Definition dctx_fields_ (p: val) : mpred :=
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
  field_at_ Ews t_dctx (DOT _fParams) p *
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
  field_at_ Ews t_dctx (DOT _customMem) p *
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
  field_at_ Ews t_dctx (DOT _litExtraBuffer) p *
  field_at_ Ews t_dctx (DOT _headerBuffer) p *
  field_at_ Ews t_dctx (DOT _oversizedDuration) p *
  dctx_pad p.

Definition ddict_fields_ (q: val) : mpred :=
  field_at_ Ews t_ddict (DOT _dictBuffer) q *
  field_at_ Ews t_ddict (DOT _dictContent) q *
  field_at_ Ews t_ddict (DOT _dictSize) q *
  field_at_ Ews t_ddict (DOT _entropy) q *
  field_at_ Ews t_ddict (DOT _dictID) q *
  field_at_ Ews t_ddict (DOT _entropyPresent) q *
  field_at_ Ews t_ddict (DOT _cMem) q *
  ddict_pad q.

(* all fields but customMem, of a context zstd just calloc'd (litExtraBuffer: bytes, lit_extra_bytes) *)
Definition dctx_fields_nocm (p: val) : mpred :=
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
  field_at_ Ews t_dctx (DOT _fParams) p *
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
  lit_extra_bytes p *
  field_at_ Ews t_dctx (DOT _headerBuffer) p *
  field_at_ Ews t_dctx (DOT _oversizedDuration) p.

(* the context's struct is a well-aligned block (its allocation token, of the context's own allocator or of
   malloc, is in the streaming group: FSRepC.mgroup) *)
Definition dctx_token (p: val) : mpred :=
  !! field_compatible t_dctx nil p && emp.

Section Rep.
Context {CMI: cmem_preds}.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* ---------- DDicts ---------- *)

(* a DDict x whose content is at buf (the copy, or the caller's bytes), with the struct's padding *)
Definition ddict_rep_at (gv: globals) (x: ddx) (buf: val) : mpred :=
  ddict_struct x buf * DENT gv (dx_q x) (ddx_ent x) * ddict_mem x buf *
  ddict_pad (dx_q x).

(* any DDict ZSTD_freeDDict can free (a live one, a leftover, or one whose initialisation failed) *)
Definition ddict_any (q: val) : mpred :=
  EX n: Z, ddict_failed q n * ddict_pad q * malloc_token Ews t_ddict q.

Definition cold01 (fs: fstate) : Prop :=
  fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1).

Definition fgroup (gv: globals) (p: val) (fs: fstate) (tabs: option tstate) : mpred :=
  !! cold01 fs &&
  (cfg_b p * frame_fields p fs *
   (match tabs with None => EX lxb: list Z, tables_uninit p lxb | Some ts => TABS gv p None ts end) *
   field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr 0)) p *
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr 0)) p *
   field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr 0)) p *
   field_at Ews t_dctx (DOT _ddictSet) nullval p).

Definition cgroup (p: val) (stable: bool) : mpred :=
  field_at Ews t_dctx (DOT _customMem) cmem_null p *
  field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr ZSTD_MAXWINDOWSIZE_DEFAULT)) p *
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p.

(* the dictionary fields: df_lx describes the local DDict: Some (x, buf) a live DDict, None a leftover *)
Record dfields := { df_local : val; df_ddict : val; df_uses : Z; df_lx : option (ddx * val) }.

Definition df_none : dfields := {| df_local := nullval; df_ddict := nullval; df_uses := 0; df_lx := None |}.

Definition local_rep (gv: globals) (q: val) (lx: option (ddx * val)) : mpred :=
  if eq_dec q nullval then emp
  else match lx with
       | Some (x, buf) => !! (dx_q x = q) && ddict_rep_at gv x buf
       | None => ddict_any q
       end.

(* the bytes the local DDict holds from a context's own allocator (DecRep.ddx_held; a leftover: the default one's) *)
Definition local_held (d: dfields) : Z :=
  if eq_dec (df_local d) nullval then 0
  else match df_lx d with Some (x, _) => ddx_held x | None => 0 end.

Definition dgroup (gv: globals) (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p *
  local_rep gv (df_local d) (df_lx d).

(* the streaming fields; the stream buffer is one block of inSize + outSize bytes at inBuff (or NULL), calloc'd,
   so its cells are always bytes (byte_cells: contract patch item 17), and it is never empty (at least 4 input bytes).  sf_mem: the context's allocator
   (CMem.cmem_v: its ZSTD_customMem; None the default one), which allocated the context and its stream buffer;
   sf_held: the bytes it gave out for the context's other blocks, its local DDict and its DDict set (FSRep3.ctx_body3;
   0 for the default allocator) *)
Record sfields := {
  sf_stage : Z; sf_inBuff : val; sf_inSize : Z; sf_inPos : val; sf_outBuff : val; sf_outSize : Z;
  sf_outStart : val; sf_outEnd : val; sf_lhSize : val; sf_hostage : val; sf_nfp : Z;
  sf_expOut : reptype t_outBuffer; sf_hbuf : list val; sf_over : Z; sf_ring : list val;
  sf_mem : option cmem; sf_held : Z }.

(* the streaming fields with the other blocks' bytes h *)
Definition sf_with_held (s: sfields) (h: Z) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s; sf_outEnd := sf_outEnd s;
     sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s; sf_expOut := sf_expOut s;
     sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := h |}.

Definition sf_with_mem (s: sfields) (am: option cmem) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s; sf_outEnd := sf_outEnd s;
     sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s; sf_expOut := sf_expOut s;
     sf_hbuf := sf_hbuf s; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := am; sf_held := sf_held s |}.

(* the stream buffer of n bytes at b (NULL: none), allocated by am *)
Definition ring_rep (am: option cmem) (b: val) (n: Z) (c: list val) : mpred :=
  if eq_dec b nullval then !! (n = 0) && emp
  else !! (Zlength c = n) &&
       (blk_tok am (tarray tuchar n) b * data_at Ews (tarray tuchar n) c b).

(* the context's allocator am: its customMem field, the token of the context's own block (zstd calloc's
   sizeof t_dctx bytes, contract patch item 17; VST's malloc_token is typed and cannot change type, so it is the
   byte array's) and, for its own allocator, the functions and the state with h bytes given out *)
Definition mgroup (am: option cmem) (p: val) (h: Z) : mpred :=
  !! cmem_ok am &&
  (field_at Ews t_dctx (DOT _customMem) (cmem_v am) p * blk_tok am (tarray tuchar (sizeof t_dctx)) p *
   cm_have am h).

(* the bytes a context's own allocator has given out: the context, its other blocks, the stream buffer *)
Definition sf_given (s: sfields) : Z := dctx_size + sf_held s + sf_inSize s + sf_outSize s.

Definition sgroup (p: val) (s: sfields) : mpred :=
  !! (0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
      Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
      0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
      (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
      (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s)) &&
  (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
   field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
   field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
   field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
   field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
   field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
   field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
   field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
   field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
   field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
   field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
   field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
   field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
   field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
   ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
   mgroup (sf_mem s) p (sf_given s)).

(* the concrete state of a context *)
Record cst := { c_fs : fstate; c_tabs : option tstate; c_stable : bool; c_dict : dfields; c_s : sfields }.

Definition cst_set_fs (k: cst) (fs: fstate) (tabs: option tstate) : cst :=
  {| c_fs := fs; c_tabs := tabs; c_stable := c_stable k; c_dict := c_dict k; c_s := c_s k |}.
Definition cst_set_dict (k: cst) (d: dfields) : cst :=
  {| c_fs := c_fs k; c_tabs := c_tabs k; c_stable := c_stable k; c_dict := d; c_s := c_s k |}.
Definition cst_set_s (k: cst) (s: sfields) : cst :=
  {| c_fs := c_fs k; c_tabs := c_tabs k; c_stable := c_stable k; c_dict := c_dict k; c_s := s |}.
Definition cst_set_stable (k: cst) (b: bool) : cst :=
  {| c_fs := c_fs k; c_tabs := c_tabs k; c_stable := b; c_dict := c_dict k; c_s := c_s k |}.

(* the context without its malloc token, and with it *)
Definition ctx_body (gv: globals) (p: val) (k: cst) : mpred :=
  fgroup gv p (c_fs k) (c_tabs k) * cgroup p (c_stable k) * dgroup gv p (c_dict k) * sgroup p (c_s k).

Definition ctx_rep (gv: globals) (p: val) (k: cst) : mpred :=
  dctx_token p * dctx_pad p * ctx_body gv p k.


End Rep.
