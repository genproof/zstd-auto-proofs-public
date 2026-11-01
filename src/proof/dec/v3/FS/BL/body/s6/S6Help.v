(* FS3-bl BODY stage 6: helpers of BLStage6 (copies of BLHelp's frame-group lemmas: BLHelp imports
   BLDispatch, which imports BLStage6; the headerBuffer splits; the 4-byte field bound). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Local Open Scope logic.

Section CM_S6Help_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s6_le_value_bound (l: list Z) : Forall is_byte l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction 1 as [|x l Hx Hl IH]; cbn [le_value length]; [simpl; lia|].
  unfold is_byte in Hx. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
  change (2 ^ 8) with 256. nia.
Qed.

Lemma s6_le_field_range (b: list Z) (i: Z) : bytes_ok b -> 0 <= le_field b i 4 < 2 ^ 32.
Proof.
  intros Hb. unfold le_field, slice.
  assert (HF: Forall is_byte (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b))).
  { apply Forall_firstn, Forall_skipn, Hb. }
  pose proof (s6_le_value_bound _ HF) as [H0 H1]. split; [lia|].
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. pose proof (Nat.le_min_l (Z.to_nat 4) (length (skipn (Z.to_nat i) b))).
  change (Z.to_nat 4) with 4%nat in *. lia.
Qed.

(* the frame group without the three fields stage, bType, expected *)
Definition s6_fc_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
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

Lemma s6_fcore3_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * s6_fc_rest p fs pr).
Proof. unfold fcore3, s6_fc_rest, frame_fields. entailer!. Qed.

Lemma s6_fcore3_join p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * s6_fc_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3, s6_fc_rest, frame_fields. entailer!. Qed.

(* headerBuffer as an array *)
Lemma s6_hb_eq sh c q :
  data_at sh (tarray tuchar 18) c (field_address t_dctx (DOT _headerBuffer) q) =
  field_at sh t_dctx (DOT _headerBuffer) c q.
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma s6_split3 {cs: compspecs} sh N lo hi (c: list val) q :
  0 <= lo <= hi -> hi <= N -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar N) c q =
  data_at sh (tarray tuchar lo) (sublist 0 lo c) q *
  data_at sh (tarray tuchar (hi - lo)) (sublist lo hi c) (offset_val lo q) *
  data_at sh (tarray tuchar (N - hi)) (sublist hi N c) (offset_val hi q).
Proof.
  intros Hl Hh Hc Hf. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh N lo hi) by lia.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl. rewrite !Z.mul_1_l, !Z.add_0_l. reflexivity.
Qed.

(* the header buffer after the copy: the 5 bytes read, the 3 copied, the rest *)
Definition s6_hb (hb: list val) (c: list Z) : list val := sublist 0 5 hb ++ zbytes c ++ sublist 8 18 hb.

Lemma s6_hb_len (hb: list val) (c: list Z) : Zlength hb = 18 -> Zlength c = 3 -> Zlength (s6_hb hb c) = 18.
Proof. intros. unfold s6_hb. list_solve. Qed.

Lemma s6_hb_before (hb: list val) q :
  Zlength hb = 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar 18) hb q =
  data_at Ews (tarray tuchar 5) (sublist 0 5 hb) q *
  data_at Ews (tarray tuchar 3) (sublist 5 8 hb) (offset_val 5 q) *
  data_at Ews (tarray tuchar 10) (sublist 8 18 hb) (offset_val 8 q).
Proof. intros. rewrite (s6_split3 Ews 18 5 8 hb q) by (auto; lia). reflexivity. Qed.

Lemma s6_hb_after (hb: list val) (c: list Z) q :
  Zlength hb = 18 -> Zlength c = 3 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar 5) (sublist 0 5 hb) q *
  data_at Ews (tarray tuchar 3) (zbytes c) (offset_val 5 q) *
  data_at Ews (tarray tuchar 10) (sublist 8 18 hb) (offset_val 8 q) =
  data_at Ews (tarray tuchar 18) (s6_hb hb c) q.
Proof.
  intros Hh Hc Hf. rewrite (s6_split3 Ews 18 5 8 (s6_hb hb c) q) by (auto using s6_hb_len; lia).
  unfold s6_hb. f_equal; [f_equal|]; f_equal; list_solve.
Qed.

Lemma s6_hb_read (hb: list val) (h c: list Z) q :
  Zlength hb = 18 -> Zlength c = 3 -> Zlength h = 5 -> sublist 0 5 hb = zbytes h ->
  field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar 18) (s6_hb hb c) q =
  data_at Ews (tarray tuchar (Zlength (h ++ c))) (zbytes (h ++ c)) q *
  data_at Ews (tarray tuchar 10) (sublist 8 18 hb) (offset_val 8 q).
Proof.
  intros Hh Hc Hl E Hf. pose proof (s6_hb_len hb c Hh Hc) as Hl2. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar Ews 18 8 (s6_hb hb c) q) by lia.
  rewrite field_address0_offset by auto with field_compatible.
  simpl.
  rewrite Zlength_app, Hc, Hl. change (5 + 3) with 8.
  unfold s6_hb. rewrite E. f_equal; f_equal; [| list_solve].
  rewrite map_app. list_solve.
Qed.

End CM_S6Help_1.
