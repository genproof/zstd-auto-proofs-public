(* FS3-bl BODY, stage 5: the frame group split into the six fields the case touches and the rest. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Facts.
Local Open Scope logic.

Section CM_BL5Sep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without the six fields the case touches *)
Definition bl5_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma bl5_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr &&
  (field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p * xxh_field p (fs_xxh fs) *
   field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
   field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
   bl5_rest p fs pr).
Proof. unfold fcore3, frame_fields, bl5_rest. Intros. apply andp_right; [apply prop_right; auto | cancel]. Qed.

Lemma bl5_xxh_fold p fs l :
  fs_xxh fs = Some l -> xxh64_state Ews 0 l (field_address t_dctx (DOT _xxhState) p) |-- xxh_field p (fs_xxh fs).
Proof. intros ->. unfold xxh_field. apply derives_refl. Qed.

End CM_BL5Sep_1.
