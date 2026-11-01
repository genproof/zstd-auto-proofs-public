(* FS3-bl BODY stage 0: helpers of BLStage0 (the frame group without stage, expected, headerSize; the
   headerBuffer split at the prefix length; the skippable magic test; header size bounds). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Local Open Scope logic.

Section CM_S0Help_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s0_le_value_bound (l: list Z) : Forall is_byte l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction 1 as [|x l Hx Hl IH]; cbn [le_value length]; [simpl; lia|].
  unfold is_byte in Hx. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
  change (2 ^ 8) with 256. nia.
Qed.

Lemma s0_le_field_range (b: list Z) (i: Z) : bytes_ok b -> 0 <= le_field b i 4 < 2 ^ 32.
Proof.
  intros Hb. unfold le_field, slice.
  assert (HF: Forall is_byte (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b))).
  { apply Forall_firstn, Forall_skipn, Hb. }
  pose proof (s0_le_value_bound _ HF) as [H0 H1]. split; [lia|].
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. pose proof (Nat.le_min_l (Z.to_nat 4) (length (skipn (Z.to_nat i) b))).
  change (Z.to_nat 4) with 4%nat in *. lia.
Qed.

Lemma s0_skip_magic_eq : forall m, 0 <= m < 2 ^ 32 ->
  Int.eq (Int.and (Int.repr m) (Int.repr (-16))) (Int.repr 407710288) = is_skippable_magic m.
Proof.
intros m Hm. unfold Int.and. rewrite (Int.unsigned_repr m) by rep_lia.
change (Int.unsigned (Int.repr (-16))) with ZSTD_MAGIC_SKIPPABLE_MASK.
unfold Int.eq. rewrite Int.unsigned_repr_eq.
change (Int.unsigned (Int.repr 407710288)) with ZSTD_MAGIC_SKIPPABLE_START.
change Int.modulus with (2 ^ 32). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
change (Z.land ZSTD_MAGIC_SKIPPABLE_MASK (Z.ones 32)) with ZSTD_MAGIC_SKIPPABLE_MASK.
unfold is_skippable_magic.
destruct (zeq (Z.land m ZSTD_MAGIC_SKIPPABLE_MASK) ZSTD_MAGIC_SKIPPABLE_START) as [E|E].
- symmetry. apply Z.eqb_eq. auto.
- symmetry. apply Z.eqb_neq. auto.
Qed.

(* the header sizes *)
Lemma s0_nth4 (k: nat) (a b c d: Z) : nth k [a; b; c; d] 0 = a \/ nth k [a; b; c; d] 0 = b \/
  nth k [a; b; c; d] 0 = c \/ nth k [a; b; c; d] 0 = d \/ nth k [a; b; c; d] 0 = 0.
Proof. destruct k as [|[|[|[|k]]]]; simpl; auto. destruct k; auto. Qed.

Lemma s0_fhd_range (x: Z) : 5 <= fhd_header_size x <= 18.
Proof.
  unfold fhd_header_size.
  assert (Hs: 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { pose proof (Z.land_ones (Z.shiftr x 5) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E. rewrite E.
    pose proof (Z.mod_pos_bound (Z.shiftr x 5) (2 ^ 1) ltac:(lia)). lia. }
  destruct ((Z.land (Z.shiftr x 5) 1 =? 1) && (Z.shiftr x 6 =? 0))%bool eqn:B.
  - apply andb_prop in B. destruct B as [B1 B2]. apply Z.eqb_eq in B1, B2. rewrite B1, B2.
    destruct (s0_nth4 (Z.to_nat (Z.land x 3)) 0 1 2 4) as [E1|[E1|[E1|[E1|E1]]]]; rewrite E1; simpl; lia.
  - destruct (s0_nth4 (Z.to_nat (Z.land x 3)) 0 1 2 4) as [E1|[E1|[E1|[E1|E1]]]]; rewrite E1;
    destruct (s0_nth4 (Z.to_nat (Z.shiftr x 6)) 0 2 4 8) as [E2|[E2|[E2|[E2|E2]]]]; rewrite E2; lia.
Qed.

Lemma s0_hs_range (mg: bool) (s: list Z) : starting_len mg <= header_size_m mg s <= 18.
Proof.
  unfold header_size_m, starting_len. change ZSTD_FRAMEHEADERSIZE_PREFIX with 5.
  destruct mg; pose proof (s0_fhd_range (byte_at s 0)); pose proof (s0_fhd_range (byte_at s 4)); lia.
Qed.

Lemma s0_fhs (mg: bool) (s: list Z) : Zlength s = starting_len mg -> frame_header_size_m mg s = Some (header_size_m mg s).
Proof.
  intros H. unfold frame_header_size_m, header_size_m, frame_header_size. unfold starting_len in H.
  destruct mg; cbn [negb]; rewrite H; reflexivity.
Qed.

(* the frame group without the fields format, stage, expected, headerSize *)
Definition s0_fc_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma s0_fcore3_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p *
                   field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
                   field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p * s0_fc_rest p fs pr).
Proof. unfold fcore3, cfg_fmt, s0_fc_rest, frame_fields. Intros. apply andp_right; [apply prop_right; auto | cancel]. Qed.

(* the fields after the call: stage st, expected e, headerSize h *)
Definition s0_fs (fs: fstate) (h e st: val) : fstate := fsu_stage (fsu_expected (fsu_headerSize fs h) e) st.

Lemma s0_fcore3_join p fs pr h e st :
  par_ok pr ->
  field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p *
  field_at Ews t_dctx (DOT _stage) st p * field_at Ews t_dctx (DOT _expected) e p *
  field_at Ews t_dctx (DOT _headerSize) h p * s0_fc_rest p fs pr |-- fcore3 p (s0_fs fs h e st) pr nullval.
Proof. intros. unfold fcore3, cfg_fmt, s0_fc_rest, frame_fields, s0_fs, fsu_stage, fsu_expected, fsu_headerSize. cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold]. apply andp_right; [apply prop_right; auto | cancel]. Qed.

(* headerBuffer as an array, split at n *)
Lemma s0_hb_eq sh c q :
  field_at sh t_dctx (DOT _headerBuffer) c q =
  data_at sh (tarray tuchar 18) c (field_address t_dctx (DOT _headerBuffer) q).
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma s0_split2 {cs: compspecs} sh N k (c: list val) q :
  0 <= k <= N -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar N) c q =
  data_at sh (tarray tuchar k) (sublist 0 k c) q *
  data_at sh (tarray tuchar (N - k)) (sublist k N c) (offset_val k q).
Proof.
  intros Hk Hc Hf. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh N k) by lia.
  rewrite field_address0_offset by auto with field_compatible.
  simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* the header buffer after the copy of c *)
Definition s0_hb (hb: list val) (c: list Z) : list val := zbytes c ++ sublist (Zlength c) 18 hb.

Lemma s0_hb_len (hb: list val) (c: list Z) : Zlength hb = 18 -> 0 <= Zlength c <= 18 -> Zlength (s0_hb hb c) = 18.
Proof. intros. unfold s0_hb. list_solve. Qed.

Lemma s0_hb_pre (hb: list val) (c: list Z) :
  Zlength hb = 18 -> 0 <= Zlength c <= 18 -> sublist 0 (Zlength c) (s0_hb hb c) = zbytes c.
Proof. intros. unfold s0_hb. list_solve. Qed.

Lemma s0_hb_before (hb: list val) (n: Z) q :
  Zlength hb = 18 -> 0 <= n <= 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar 18) hb q |--
  data_at_ Ews (tarray tuchar n) q * data_at Ews (tarray tuchar (18 - n)) (sublist n 18 hb) (offset_val n q).
Proof.
  intros. rewrite (s0_split2 Ews 18 n hb q) by auto. cancel.
Qed.

Lemma s0_hb_after (hb: list val) (c: list Z) q :
  Zlength hb = 18 -> 0 <= Zlength c <= 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar (Zlength c)) (zbytes c) q *
  data_at Ews (tarray tuchar (18 - Zlength c)) (sublist (Zlength c) 18 hb) (offset_val (Zlength c) q) =
  data_at Ews (tarray tuchar 18) (s0_hb hb c) q.
Proof.
  intros Hh Hc Hf. rewrite (s0_split2 Ews 18 (Zlength c) (s0_hb hb c) q) by (auto using s0_hb_len).
  unfold s0_hb. f_equal; f_equal; list_solve.
Qed.

End CM_S0Help_1.
