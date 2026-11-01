(* FS3-bl BODY stage 1: more separation helpers of BLStage1 (the globals fold, the frame-group join with
   headerSize read, the headerBuffer after the copy). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s1.S1Pure.
Local Open Scope logic.

Section CM_S1Vst_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s1_globals_fold gv :
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) * eb_res gv |-- zstd_globals gv.
Proof. unfold zstd_globals. cancel. Qed.

Lemma s1_fcore3_join_hs p fs pr hv :
  par_ok pr -> fs_headerSize fs = hv ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _headerSize) hv p * s1_fc_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros Hp <-. apply s1_fcore3_join; auto. Qed.

Lemma s1_hb_after' (hb: list val) (c: list Z) sl hs q :
  Zlength hb = 18 -> 0 <= sl -> Zlength c = hs - sl -> sl <= hs <= 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar (Zlength c)) (zbytes c) (offset_val sl q) *
  data_at Ews (tarray tuchar sl) (sublist 0 sl hb) q *
  data_at Ews (tarray tuchar (18 - hs)) (sublist hs 18 hb) (offset_val hs q) |--
  data_at Ews (tarray tuchar 18) (s1_hb hb c sl hs) q.
Proof.
  intros Hh Hs Hc Hr Hf. rewrite <- (s1_hb_after hb c sl hs q) by auto. rewrite Hc. cancel.
Qed.

End CM_S1Vst_1.
