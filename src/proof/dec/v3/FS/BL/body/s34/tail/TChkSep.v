(* FS3-bl BODY, stages 3/4, the tail: helpers of TChk.v (split from it for the check time): the frame group
   without fParams, and the DEBUGLOG loops as semax lemmas (copied from TS4Sep.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Local Open Scope logic.

Section CM_TChkSep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the frame group without fParams *)
Definition tchk_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma tchk_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p * tchk_rest p fs pr).
Proof.
  unfold fcore3, tchk_rest, frame_fields; apply derives_extract_prop; intros; apply andp_right;
    [apply prop_right; auto | cancel].
Qed.

Lemma tchk_join p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p * tchk_rest p fs pr |-- fcore3 p fs pr nullval.
Proof.
  intros. unfold fcore3, tchk_rest, frame_fields; apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma tchk_m20 : Vlong (Int64.repr (-20)) = Vlong (Int64.repr (2 ^ 64 - 20)).
Proof. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

(* the DEBUGLOG loops as lemmas (copied from s5/BL5Facts.v): for(;;break){} and
   for(;;break){ if (0) s } before c *)
Lemma tchk_loop_break {cs: compspecs} {Espec: OracleKind} Delta P body Post :
  semax Delta P body (loop1_ret_assert P (overridePost P Post)) ->
  semax Delta P (Sloop body Sbreak) (overridePost P Post).
Proof.
  intros H. eapply semax_loop; [exact H |].
  eapply semax_pre; [| apply semax_break]. intros rho. destruct Post; cbn. apply andp_left2, derives_refl.
Qed.

Lemma tchk_dw_skip {cs: compspecs} {Espec: OracleKind} Delta P c Post :
  semax Delta P c Post -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply tchk_loop_break.
  destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
    first [apply derives_refl | apply FF_left].
Qed.

Lemma tchk_dw_if0 {cs: compspecs} {Espec: OracleKind} Delta P s c Post :
  semax Delta P c Post ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply tchk_loop_break.
  eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
  - apply andp_left2. eapply derives_trans; [| apply now_later]. apply andp_right; [| apply derives_refl].
    intros rho. cbn. apply TT_right.
  - eapply semax_pre; [| apply semax_ff]. apply andp_left2.
    intros rho. unfold local, lift1, liftx. cbn. apply andp_left2. apply prop_left. intros Hf.
    cbv in Hf. inversion Hf.
  - destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
      first [apply andp_left1, derives_refl | apply FF_left].
Qed.

End CM_TChkSep_1.

Ltac tchk_dw :=
  repeat apply -> seq_assoc;
  first [ apply tchk_dw_skip | apply tchk_dw_if0 ];
  try (match goal with |- semax _ _ ?c _ => is_var c; subst c end; unfold abbreviate).

