(* FS3-bl BODY stage 1: separation helpers of BLStage1 (copies of BLHelp's frame-group split/join with
   the fields stage 1 touches: stage, expected, headerSize; the headerBuffer splits; the DEBUGLOG loops). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s1.S1Hdr.
Local Open Scope logic.

Ltac s1_head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => s1_head_dw0 a end.
Ltac s1_dw0 :=
  match goal with |- semax _ ?P ?c _ => s1_head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_S1Help_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without stage, expected, headerSize *)
Definition s1_fc_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
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

Lemma s1_fcore3_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
                   field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p * s1_fc_rest p fs pr).
Proof. unfold fcore3, s1_fc_rest, frame_fields. entailer!. Qed.

Lemma s1_fcore3_join p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p * s1_fc_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3, s1_fc_rest, frame_fields. entailer!. Qed.

(* the state after stage 1: expected = ZSTD_blockHeaderSize, stage = 2 *)
Definition s1_fs2 (fs: fstate) : fstate := fsu_stage (fsu_expected fs (vlong 3)) (Vint (Int.repr 2)).

Lemma s1_fcore3_join2 p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 2)) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 3)) p *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p * s1_fc_rest p fs pr |-- fcore3 p (s1_fs2 fs) pr nullval.
Proof. intros. apply (s1_fcore3_join p (s1_fs2 fs) pr); auto. Qed.

(* headerBuffer as an array *)
Lemma s1_hb_eq sh c q :
  data_at sh (tarray tuchar 18) c (field_address t_dctx (DOT _headerBuffer) q) =
  field_at sh t_dctx (DOT _headerBuffer) c q.
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma s1_split3 {cs: compspecs} sh N lo hi (c: list val) q :
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

(* the header buffer after the copy of c at sl: the prefix, c, the rest *)
Definition s1_hb (hb: list val) (c: list Z) (sl hs: Z) : list val :=
  sublist 0 sl hb ++ zbytes c ++ sublist hs 18 hb.

Lemma s1_hb_len (hb: list val) (c: list Z) sl hs :
  Zlength hb = 18 -> 0 <= sl -> Zlength c = hs - sl -> sl <= hs <= 18 -> Zlength (s1_hb hb c sl hs) = 18.
Proof. intros. unfold s1_hb. list_solve. Qed.

Lemma s1_hb_before (hb: list val) sl hs q :
  Zlength hb = 18 -> 0 <= sl <= hs -> hs <= 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar 18) hb q =
  data_at Ews (tarray tuchar sl) (sublist 0 sl hb) q *
  data_at Ews (tarray tuchar (hs - sl)) (sublist sl hs hb) (offset_val sl q) *
  data_at Ews (tarray tuchar (18 - hs)) (sublist hs 18 hb) (offset_val hs q).
Proof. intros. rewrite (s1_split3 Ews 18 sl hs hb q) by auto. reflexivity. Qed.

Lemma s1_hb_after (hb: list val) (c: list Z) sl hs q :
  Zlength hb = 18 -> 0 <= sl -> Zlength c = hs - sl -> sl <= hs <= 18 -> field_compatible (tarray tuchar 18) [] q ->
  data_at Ews (tarray tuchar sl) (sublist 0 sl hb) q *
  data_at Ews (tarray tuchar (hs - sl)) (zbytes c) (offset_val sl q) *
  data_at Ews (tarray tuchar (18 - hs)) (sublist hs 18 hb) (offset_val hs q) =
  data_at Ews (tarray tuchar 18) (s1_hb hb c sl hs) q.
Proof.
  intros Hh Hs Hc Hr Hf. rewrite (s1_split3 Ews 18 sl hs (s1_hb hb c sl hs) q) by (auto using s1_hb_len; lia).
  unfold s1_hb. f_equal; [f_equal|]; f_equal; list_solve.
Qed.

(* the window ZSTD_decodeFrameHeader reads: the header bytes h (at [0, sl)) and c *)
Lemma s1_hb_win (hb: list val) (h c: list Z) sl hs :
  Zlength hb = 18 -> Zlength h = sl -> 0 <= sl -> Zlength c = hs - sl -> sl <= hs <= 18 ->
  sublist 0 sl hb = zbytes h -> bytes_ok h -> bytes_ok c ->
  win_ok Ews 18 (s1_hb hb c sl hs) 0 hs (h ++ c).
Proof.
  intros Hh Hl Hs Hc Hr E Bh Bc. unfold win_ok.
  split; [auto |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [apply s1_hb_len; auto |].
  split; [rewrite Zlength_app; lia |]. split; [apply Forall_app; auto |].
  unfold s1_hb. rewrite E, map_app. list_solve.
Qed.

Lemma s1_sel_res_emp {DENT: dent_pred} gv p pr d l tbl xq am hb :
  sel_res DENT gv p pr nullval d l tbl xq am hb = emp.
Proof. unfold sel_res, sel_on. rewrite andb_false_r. reflexivity. Qed.

(* what the prologue (checkContinuity, processedCSize) leaves of the fields stage 1 reads *)
Lemma s1_fs1_eq fs ob osz opos pcs n :
  let fs1 := bl_fs1 fs ob osz opos pcs n in
  fs_headerSize fs1 = fs_headerSize fs /\ fs_dictID fs1 = fs_dictID fs /\
  fs_processedCSize fs1 = vlong (pcs + n) /\ fs_ddictIsCold fs1 = fs_ddictIsCold fs /\
  fs_isFrameDecompression fs1 = fs_isFrameDecompression fs /\ fs_decodedSize fs1 = fs_decodedSize fs /\
  fs_xxh fs1 = fs_xxh fs.
Proof. unfold bl_fs1, continuity. destruct (cont_moves fs (offset_val opos ob) (osz - opos)); repeat split; reflexivity. Qed.

Lemma s1_hsize_rng md v :
  Zlength (bv_hdr v) = starting_len (md_magicless md) ->
  bv_hs v = header_size_m (md_magicless md) (bv_hdr v) ->
  0 < bv_hs v - starting_len (md_magicless md) ->
  (starting_len (md_magicless md) = 1 \/ starting_len (md_magicless md) = 5) /\ bv_hs v <= 18.
Proof.
  intros _ Hhs _. split; [unfold starting_len; destruct (md_magicless md); auto |].
  rewrite Hhs. apply s1_hsize_le.
Qed.

End CM_S1Help_1.
