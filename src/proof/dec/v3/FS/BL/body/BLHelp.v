(* FS3-bl BODY: helpers of BLBody / BLRest / BLRest2: tactics, small lemmas, the statements after the
   srcSize check (bl_rest) and after ZSTD_checkContinuity (bl_rest2), the state there (bl_pre0). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCont Zstd.proof.dec.v3.FS.BL.body.BLDispatch.
Local Open Scope logic.

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.
Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_BLHelp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bl_btz (fs: fstate) : Z := match fs_bType fs with Vint b => Int.signed b | _ => 0 end.

Lemma bl_next_ok md v e fs hb n :
  bl_cstage md v e fs hb -> 0 <= n -> 0 < e ->
  n = next_size (bl_stz (bv_stage v)) (bl_btz fs) e n -> bl_size_ok v e n.
Proof.
  intros Hc Hn He E. unfold bl_size_ok.
  destruct (bv_stage v) eqn:Es; cbn [bl_stz next_size] in E; unfold next_size in E; cbn in E; auto.
  all: cbv [bl_cstage] in Hc; rewrite Es in Hc; destruct Hc as (_ & Hbt & Hbr & _).
  all: unfold bl_btz in E; rewrite Hbt in E; rewrite Int.signed_repr in E by rep_lia.
  all: destruct (bv_bt v =? 0); simpl in E; auto; lia.
Qed.

Lemma bl_next_eq md v e fs hb :
  bl_cstage md v e fs hb -> 0 < e -> next_size (bl_stz (bv_stage v)) (bl_btz fs) e e = e.
Proof.
  intros Hc He. unfold next_size. destruct (andb _ _); [lia | reflexivity].
Qed.

Lemma bl_stage_pre md v e fs hb :
  bl_cstage md v e fs hb ->
  Int.min_signed <= bl_stz (bv_stage v) <= Int.max_signed /\
  (bl_stz (bv_stage v) = ds_decompressBlock \/ bl_stz (bv_stage v) = ds_decompressLastBlock ->
   exists b : Z, fs_bType fs = Vint (Int.repr b) /\ Int.min_signed <= b <= Int.max_signed).
Proof.
  intros Hc. split; [destruct (bv_stage v); simpl; rep_lia |].
  intros Hs. destruct (bv_stage v) eqn:Es; simpl in Hs; unfold ds_decompressBlock, ds_decompressLastBlock in Hs;
    try lia.
  all: cbv [bl_cstage] in Hc; rewrite Es in Hc; destruct Hc as (_ & Hbt & Hbr & _).
  all: exists (bv_bt v); split; [exact Hbt | rep_lia].
Qed.

Lemma next_size_range st bt e n : 0 <= e -> 0 <= n -> 0 <= next_size st bt e n <= Z.max 1 e.
Proof. intros. unfold next_size. destruct (andb _ _); lia. Qed.

Lemma bl_claim_size md ba ba' c r opos osz oc' fs ts v hb :
  bl_mrel md ba fs ts v -> bl_cstage md v (ba_expect ba) fs hb -> 0 < ba_expect ba ->
  Zlength c <> next_size (bl_stz (bv_stage v)) (bl_btz fs) (ba_expect ba) (Zlength c) ->
  bl_claim_nc md ba ba' c r opos osz oc'.
Proof.
  intros Hmr Hc He Hn. unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto.
  destruct (dictref_model _); auto. intros Hl. exfalso.
  destruct (Hmr b B) as (_ & Hbe & _). rewrite Hl, Hbe in Hn.
  rewrite (bl_next_eq md v (ba_expect ba) fs hb) in Hn; auto.
Qed.

Lemma frame_fields_fold p fs :
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p |-- frame_fields p fs.
Proof. unfold frame_fields. cancel. Qed.

Lemma frame_fields_fold_pc p fs v :
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) v p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p |-- frame_fields p (fsu_processedCSize fs v).
Proof. unfold frame_fields, fsu_processedCSize. simpl. cancel. Qed.

Lemma fcore3_fold p fs pr :
  par_ok pr ->
  cfg_fmt p (dp_fmt pr) * cfg_lit p * frame_fields p fs *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3. entailer!. Qed.

Lemma cont_same fs dst n :
  fs_processedCSize (continuity fs dst n) = fs_processedCSize fs /\ fs_stage (continuity fs dst n) = fs_stage fs.
Proof. unfold continuity. destruct (cont_moves fs dst n); split; reflexivity. Qed.

Lemma pws_cons2_fold sh N c base w W :
  data_at sh (tarray tuchar N) c base * pw_pred w * pws_pred W |-- pws_pred (pw_bytes sh N c base :: w :: W).
Proof. unfold pws_pred; simpl. cancel. Qed.

Lemma pws_cons2_unfold sh N c base w W :
  pws_pred (pw_bytes sh N c base :: w :: W) |-- data_at sh (tarray tuchar N) c base * pw_pred w * pws_pred W.
Proof. unfold pws_pred; simpl. cancel. Qed.

(* the frame group without the three fields the srcSize check reads *)
Definition fc_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
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

Lemma fcore3_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * fc_rest p fs pr).
Proof. unfold fcore3, fc_rest, frame_fields. entailer!. Qed.

Lemma fcore3_join p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * fc_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3, fc_rest, frame_fields. entailer!. Qed.

(* the statement after the srcSize check, and after ZSTD_checkContinuity *)
Definition bl_rest : statement :=
  ltac:(let b := eval cbv [f_ZSTD_decompressContinue fn_body] in (fn_body f_ZSTD_decompressContinue) in
        lazymatch b with Ssequence _ (Ssequence _ ?r) => exact r end).
Definition bl_rest2 : statement :=
  ltac:(let b := eval cbv [bl_rest] in bl_rest in lazymatch b with Ssequence _ ?r => exact r end).

Section Rest.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition bl_pre0 (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; fcore3 p fs pr nullval; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).
End Rest.

End CM_BLHelp_1.
