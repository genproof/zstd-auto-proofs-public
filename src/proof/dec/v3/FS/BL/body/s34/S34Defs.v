(* FS3-bl BODY, stages 3/4: the shared statements of the block case of ZSTD_decompressContinue
   (bl_cmd 3).

   bl_cmd 3 = Ssequence (Ssequence DEBUGLOG (Ssequence (Ssequence (_t'36 = dctx->bType) (switch (_t'36) s34_ls))
                                               s34_t))
                        s34_rest
   - s34_ls: the cases of the switch on the block type (2 compressed, 0 raw, 1 RLE, 3/default error);
   - s34_t: from FORWARD_IF_ERROR(rSize) to `return rSize`; s34_rest: the later stage cases (unreachable);
   - s34_mid: the state after the switch on the block type (rSize = r, the output oc', expected = e',
     ddictIsCold = cold, the tables t'), with s34_mid_ok: what the block case established;
   - s34_case_spec k: case k of the block-type switch, from the state at the stage switch (bl_case_pre) to s34_mid;
   - s34_tail_spec: from s34_mid, Ssequence s34_t s34_rest establishes the ispec's POST. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Local Open Scope logic.

Section CM_S34Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the statements ---------- *)

Definition s34_s3 : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with context [LScons (Some 3) ?s3 _] => exact s3 end).

Definition s34_ls : labeled_statements :=
  ltac:(let s := eval cbv [s34_s3] in s34_s3 in
        lazymatch s with Ssequence _ (Ssequence (Ssequence _ (Sswitch _ ?ls)) _) => exact ls end).

Definition s34_t : statement :=
  ltac:(let s := eval cbv [s34_s3] in s34_s3 in
        lazymatch s with Ssequence _ (Ssequence (Ssequence _ (Sswitch _ _)) ?t) => exact t end).

Definition s34_rest : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with context [LScons (Some 3) _ ?r] => exact (seq_of_labeled_statement r) end).

(* ---------- the model of one block ---------- *)

(* the model follows the call: a described stage, a loaded dictionary, the size the model asks for *)
Definition s34_fol (ba: blabs) (c: list Z) (b: blst) (dm: dict_model) : Prop :=
  ba_st ba = Some b /\ dictref_model (ba_dict ba) = Some dm /\ Zlength c = bs_expect b.

(* the block's content and the entropy state after it, as Params.bl_step decodes it (None: no claim for a
   compressed block, an error for the reserved type) *)
Definition blk_model (dm: dict_model) (b: blst) (c: list Z) : option (dstate * list Z) :=
  if bs_btype b =? 0 then Some (bs_ds b, c)
  else if bs_btype b =? 1 then Some (bs_ds b, repeat (byte_at c 0) (Z.to_nat (bs_rle b)))
  else if bs_btype b =? 2 then
    decode_block (bs_ds b) (dm_content dm) (bs_out b) c (fh_blockSizeMax (bs_hdr b)) (fh_windowSize (bs_hdr b))
  else None.

(* ---------- the state after the switch on the block type ---------- *)

(* r = rSize; oc' the output array; e' = dctx->expected; cold = ddictIsCold; t' the tables *)
Definition s34_mid_ok (od: option bldict) (ba: blabs) (v: blv) (osz opos: Z) (oc: list val) (c: list Z)
    (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) : Prop :=
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = osz /\ sublist 0 opos oc' = sublist 0 opos oc /\
  (cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)) /\
  (is_error_code r = true ->
     forall b dm, s34_fol ba c b dm ->
       match blk_model dm b c with Some (_, cnt) => osz - opos < Zlength cnt | None => True end) /\
  (is_error_code r = false ->
     r <= osz - opos /\ e' = (if bv_bt v =? 0 then ba_expect ba - r else 0) /\ (bv_bt v = 0 -> r = Zlength c) /\
     exists cnt ts',
       sublist opos (opos + r) oc' = zbytes cnt /\ bytes_ok cnt /\ Zlength cnt = r /\
       t' = TInit (bd_oxo od) ts' /\
       (forall b dm x, s34_fol ba c b dm -> blk_model dm b c = Some x -> x = (ts_d ts', cnt))).

Section Mid.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition s34_mid (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (fs1: fstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) (v: blv) : environ -> mpred :=
  (EX r: Z, EX oc': list val, EX e': Z, EX cold: val, EX t': tabs3,
   PROP (s34_mid_ok od ba v osz opos oc c r oc' e' cold t')
   LOCAL (temp _rSize (Vlong (Int64.repr r)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
          temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
          temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
   SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
        pws_pred W; zstd_globals gv; fcore3 p (fsu_ddictIsCold (fsu_expected fs1 (vlong e')) cold) pr nullval;
        tabs_rep TABS gv p t';
        field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
        data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src))%assert.

End Mid.

(* ---------- the obligations ---------- *)

(* case k of the switch on the block type (bv_bt v = k), from the state at the stage switch *)
Definition s34_case_spec (k: Z) : Prop :=
  forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs st: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bl_stz (bv_stage v) = st ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  bv_bt v = k ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp st)
    (seq_of_labeled_statement (select_switch k s34_ls))
    (switch_ret_assert
       (overridePost
          (s34_mid DENT TABS W gv p pr od ba (bl_fs1 fs ob osz opos pcs (Zlength c)) hb shk shd ob osz opos oc shs src
             c v_bp v)
          (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)))).

(* after the switch on the block type: the checks, decodedSize, the checksum, the history, the next stage *)
Definition s34_tail_spec : Prop :=
  forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs st: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bl_stz (bv_stage v) = st ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (s34_mid DENT TABS W gv p pr od ba (bl_fs1 fs ob osz opos pcs (Zlength c)) hb shk shd ob osz opos oc shs src
       c v_bp v)
    (Ssequence s34_t s34_rest)
    (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).

(* the block case with the switch and the tail folded *)
Definition s34_s3f : statement :=
  ltac:(let s := eval cbv [s34_s3] in s34_s3 in
        lazymatch s with Ssequence ?d (Ssequence (Ssequence ?a (Sswitch ?e _)) _) =>
          exact (Ssequence d (Ssequence (Ssequence a (Sswitch e s34_ls)) s34_t)) end).

End CM_S34Defs_1.


(* ---------- helpers (copied from BLHelp.v, which this file cannot import: BLHelp -> BLDispatch -> BLStage34) ---------- *)

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.
Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_S34Defs_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


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

Lemma fcore3_fold p fs pr :
  par_ok pr ->
  cfg_fmt p (dp_fmt pr) * cfg_lit p * frame_fields p fs *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3. entailer!. Qed.

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

End CM_S34Defs_2.
