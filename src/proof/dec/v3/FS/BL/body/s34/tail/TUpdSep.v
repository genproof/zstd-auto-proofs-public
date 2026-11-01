(* FS3-bl BODY, stages 3/4, the tail: helpers of TUpd.v (split from it for the check time): the frame
   group without the five fields the tail updates touch, the output array around the new content. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Local Open Scope logic.

Section CM_TUpdSep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without the five fields the tail updates touch *)
Definition tu_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma tu_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr &&
  (field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
   field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p * xxh_field p (fs_xxh fs) *
   field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
   field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p * tu_rest p fs pr).
Proof. unfold fcore3, frame_fields, tu_rest. Intros. apply andp_right; [apply prop_right; auto | cancel]. Qed.

Lemma tu_join p fs pr vc ds r x ob opos :
  par_ok pr -> vc = fs_validateChecksum fs ->
  field_at Ews t_dctx (DOT _decodedSize) (vlong (ds + r)) p *
  field_at Ews t_dctx (DOT _validateChecksum) vc p * xxh_field p x *
  field_at Ews t_dctx (DOT _previousDstEnd) (offset_val (opos + r) ob) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (Vint (Int.repr 0)) p * tu_rest p fs pr
  |-- fcore3 p (t34_fsB fs ds r x ob opos) pr nullval.
Proof.
  intros Hp ->. unfold fcore3, frame_fields, tu_rest, t34_fsB. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma tu_fa0_sub N p k :
  field_compatible (tarray tuchar N) [] p -> 0 <= k <= N ->
  field_address0 (Tarray tuchar N noattr) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Definition tu_arr_rest (sh: share) (N: Z) (c: list val) (base: val) (off k: Z) : mpred :=
  data_at sh (Tarray tuchar off noattr) (sublist 0 off c) base *
  data_at sh (Tarray tuchar (N - (off + k)) noattr) (sublist (off + k) N c) (offset_val (off + k) base).

Lemma tu_arr_split sh N c base off (s: list Z) :
  field_compatible (tarray tuchar N) [] base -> Zlength c = N -> 0 <= off -> off + Zlength s <= N ->
  sublist off (off + Zlength s) c = zbytes s ->
  data_at sh (tarray tuchar N) c base =
  tu_arr_rest sh N c base off (Zlength s) * data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base).
Proof.
  intros Fc HN Ho Hs Hw. unfold tu_arr_rest. pose proof (Zlength_nonneg s).
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s) c base) by lia.
  rewrite !tu_fa0_sub by (auto; lia). replace (off + Zlength s - off) with (Zlength s) by lia.
  rewrite Hw. apply pred_ext; cancel.
Qed.

Lemma tu_arr_join sh N c base off (s: list Z) :
  field_compatible (tarray tuchar N) [] base -> Zlength c = N -> 0 <= off -> off + Zlength s <= N ->
  sublist off (off + Zlength s) c = zbytes s ->
  tu_arr_rest sh N c base off (Zlength s) * data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base)
  |-- data_at sh (tarray tuchar N) c base.
Proof. intros. rewrite (tu_arr_split sh N c base off s) by auto. apply derives_refl. Qed.

Lemma tu_arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.


(* the frame fields after t34_dsz; t34_xx (decodedSize ds + r, the checksum state x) *)
Definition t34_fs1 (fsx: fstate) (ds r: Z) (x: option (list Z)) : fstate :=
  fsu_xxh (fsu_decodedSize fsx (vlong (ds + r))) x.

(* ... and after t34_pe; t34_gp *)
Definition t34_fs2 (fsx: fstate) (pe: val) : fstate :=
  fsu_gpDictCopy (fsu_previousDstEnd fsx pe) (Vint (Int.repr 0)).

Lemma t34_fsB_eq fsx ds r x ob opos :
  t34_fsB fsx ds r x ob opos = t34_fs2 (t34_fs1 fsx ds r x) (offset_val (opos + r) ob).
Proof. reflexivity. Qed.

Lemma tu_join1 p fs pr vc ds r x :
  par_ok pr -> vc = fs_validateChecksum fs ->
  field_at Ews t_dctx (DOT _decodedSize) (vlong (ds + r)) p *
  field_at Ews t_dctx (DOT _validateChecksum) vc p * xxh_field p x *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p * tu_rest p fs pr
  |-- fcore3 p (t34_fs1 fs ds r x) pr nullval.
Proof.
  intros Hp ->. unfold fcore3, frame_fields, tu_rest, t34_fs1. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma tu_join2 p fs pr pe :
  par_ok pr ->
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p * xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _previousDstEnd) pe p *
  field_at Ews t_dctx (DOT _gpDictCopy) (Vint (Int.repr 0)) p * tu_rest p fs pr
  |-- fcore3 p (t34_fs2 fs pe) pr nullval.
Proof.
  intros Hp. unfold fcore3, frame_fields, tu_rest, t34_fs2. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma tu_join_ds p fs pr d :
  par_ok pr ->
  field_at Ews t_dctx (DOT _decodedSize) d p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p * xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p * tu_rest p fs pr
  |-- fcore3 p (fsu_decodedSize fs d) pr nullval.
Proof.
  intros Hp. unfold fcore3, frame_fields, tu_rest. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

Lemma tu_join_xx p fs pr vc x :
  par_ok pr -> vc = fs_validateChecksum fs ->
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) vc p * xxh_field p x *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p * tu_rest p fs pr
  |-- fcore3 p (fsu_xxh fs x) pr nullval.
Proof.
  intros Hp ->. unfold fcore3, frame_fields, tu_rest. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

End CM_TUpdSep_1.
