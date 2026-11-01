(* FS3-bl BODY, stages 3/4, the tail: t34_stg; t34_ret in a block that is not the last (stage 3,
   VST): stage = 2, expected = ZSTD_blockHeaderSize, return rSize; the post is a hypothesis (TPOk.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Local Open Scope logic.

Section CM_TS3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* zstd_globals without ZSTD_blockHeaderSize *)
Definition ts3_grest (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
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
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

Lemma ts3_gsplit gv :
  zstd_globals gv = data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * ts3_grest gv.
Proof.
  unfold zstd_globals, ts3_grest. change ZSTD_blockHeaderSize_val with (Vlong (Int64.repr 3)).
  apply pred_ext; cancel.
Qed.

Lemma ts3_fc_rest p fsx stg e pr : fc_rest p (t34_fsE fsx stg e) pr = fc_rest p fsx pr.
Proof. reflexivity. Qed.

Lemma ts3_gfold gv :
  data_at Ers tulong (Vlong (Int64.repr 3)) (gv _ZSTD_blockHeaderSize) * ts3_grest gv |-- zstd_globals gv.
Proof. rewrite ts3_gsplit. apply derives_refl. Qed.

Lemma ts3_fold p fsx pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 2)) p * field_at Ews t_dctx (DOT _bType) (fs_bType fsx) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 3)) p * fc_rest p fsx pr
  |-- fcore3 p (t34_fsE fsx BBlkHdr 3) pr nullval.
Proof.
  intros Hp. rewrite <- (ts3_fc_rest p fsx BBlkHdr 3 pr).
  exact (fcore3_join p (t34_fsE fsx BBlkHdr 3) pr Hp).
Qed.

Lemma t34_s3_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (Q: environ -> mpred),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  e' = 0 -> bv_stage v = BBlk ->
  (Forall (tc_val' tuchar) oc' ->
     exists ba', t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba' (t34_fsE (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) (fst (t34_next v 0)) (snd (t34_next v 0))) t' hb) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) oc' t') (Ssequence t34_stg t34_ret) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs r oc'
    e' cold t' ds cnt ts' Q HH Hmid Her Hbm Hcnt Hds Hdsr He' Hst Hpost.
  unfold t34_st, t34_R, bl_R, bl_post, t34_stg, t34_ret. simplify_func_tycontext. abbreviate_semax.
  destruct HH as (Hpr & Hpre & Hci & Hmr & Hmd & _ & _ & Hpcs & Hpcsr & Hsz & Hlay).
  pose proof Hci as Hci'. destruct Hci' as (Hexp & Hexr & Hstg & _).
  rewrite Hst in Hstg.
  set (fsB := t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) in *.
  assert (Fst: fs_stage fsB = Vint (Int.repr 3)).
  { change (fs_stage fsB) with (fs_stage (t34_fsm fs ob osz opos pcs c e' cold)). destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (_&_&_&_&_&_&_&_&_&E&_).
    rewrite E, Hstg. reflexivity. }
  sep_apply (fcore3_split p fsB pr). Intros. rewrite Fst.
  rewrite ts3_gsplit. Intros.
  assert_PROP (Forall (tc_val' tuchar) oc') as Htc by entailer!.
  destruct (Hpost Htc) as [ba' Hpp].
  freeze [1; 3; 4; 5; 7; 8; 9; 10; 11; 12; 13] FR.
  forward.
  assert (Hn: t34_next v 0 = (BBlkHdr, 3)) by (unfold t34_next; rewrite Hst; reflexivity).
  rewrite Hn in Hpp; cbn [fst snd] in Hpp.
  apply semax_if_seq. forward_if.
  { exfalso. lia. }
  forward. forward. forward.
  thaw FR.
  sep_apply (ts3_gfold gv).
  sep_apply (ts3_fold p fsB pr Hpr).
  forward.
  Exists r oc' ba' (t34_fsE fsB BBlkHdr 3) t' hb.
  unfold t34_pp in Hpp.
  entailer!.
  destruct Hpp as (_ & _ & P3 & P4 & _ & P8 & P6 & P7). auto.
Qed.

End CM_TS3_1.
