(* FS3-bl BODY stage 7: helpers (copies of BLHelp's fcore3 split/join, and the pure facts). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Local Open Scope logic.

Section CM_BL7Help_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without the three fields the srcSize check reads *)
Definition fc7_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
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

Lemma fcore3_split7 p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * fc7_rest p fs pr).
Proof. unfold fcore3, fc7_rest, frame_fields. entailer!. Qed.

Lemma fcore3_join7 p fs pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * fc7_rest p fs pr |-- fcore3 p fs pr nullval.
Proof. intros. unfold fcore3, fc7_rest, frame_fields. entailer!. Qed.

(* ---------- stage 7 (ZSTDds_skipFrame): expected = 0; stage = 0; return 0 ---------- *)

Lemma cont7_same fs dst n :
  fs_ddictIsCold (continuity fs dst n) = fs_ddictIsCold fs /\
  fs_isFrameDecompression (continuity fs dst n) = fs_isFrameDecompression fs /\
  fs_dictID (continuity fs dst n) = fs_dictID fs /\
  fs_decodedSize (continuity fs dst n) = fs_decodedSize fs.
Proof. unfold continuity. destruct (cont_moves fs dst n); repeat split; reflexivity. Qed.

Definition fs7 (fs1: fstate) : fstate :=
  fsu_stage (fsu_expected fs1 (Vlong (Int64.repr 0))) (Vint (Int.repr 0)).

Definition ba7 (ba: blabs) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := option_map (fun b => bl_set b BHdrPrefix 0) (ba_st ba); ba_expect := 0;
     ba_out := Some (pair (pair ob (bl_start ba opos)) opos) |}.

Definition v7 (v: blv) : blv :=
  {| bv_stage := BHdrPrefix; bv_hdr := bv_hdr v; bv_hs := bv_hs v; bv_h := bv_h v; bv_bt := bv_bt v;
     bv_rle := bv_rle v |}.

Lemma bl7_hist ba ob opos oc :
  bl_hist_ok ba ob opos oc -> 0 <= opos -> bl_hist_ok (ba7 ba ob opos) ob opos oc.
Proof.
  unfold bl_hist_ok, ba7, bl_start; cbn [ba_out ba_st].
  destruct (ba_out ba) as [[[ob' f] pe] |]; intros H Ho.
  - destruct H as (-> & -> & Hf & H). repeat split; auto; try lia.
    destruct (ba_st ba); exact H.
  - repeat split; auto; try lia. rewrite sublist_nil.
    destruct (ba_st ba) as [b |]; cbn.
    + rewrite H. reflexivity.
    + exists nil. split; [reflexivity | constructor].
Qed.

Lemma bl7_pure md od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs :
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv md od osz0 ba fs hb v -> bl_mrel md ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  bv_stage v = BSkip ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  cold01 (fs7 (bl_fs1 fs ob osz opos pcs (Zlength c))) /\
  bl_hist_ok (ba7 ba ob opos) ob opos oc /\
  BRc md od osz (ba7 ba ob opos) (fs7 (bl_fs1 fs ob osz opos pcs (Zlength c))) ts hb /\
  bl_claim_nc md ba (ba7 ba ob opos) c 0 opos osz oc.
Proof.
  intros Hpre Hci Hmr Hbd Hs Hlay.
  destruct Hpre as (_ & Hh & _ & _ & _ & _ & _ & _ & _ & Ho & _).
  destruct Hci as (_ & _ & _ & Hfd & Hcold & Hid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & _ & _).
  destruct (cont7_same fs (offset_val opos ob) (osz - opos)) as (C1 & C2 & C3 & C4).
  unfold fs7, bl_fs1.
  split; [| split; [| split]].
  - unfold cold01 in *. cbn. rewrite C1. exact Hcold.
  - apply bl7_hist; auto; lia.
  - exists (v7 v). split; [| split].
    + unfold bl_cinv. cbn. rewrite C2, C3, C4.
      split; [reflexivity |]. split; [lia |]. split; [reflexivity |]. split; [exact Hfd |].
      split; [unfold cold01 in *; cbn; rewrite C1; exact Hcold |]. split; [exact Hid |].
      split; [exists (Int64.unsigned (Int64.repr (pcs + Zlength c))); split;
              [unfold vlong; rewrite Int64.repr_unsigned; reflexivity | rep_lia] |].
      split; [exists ds; auto |]. split; [exact Hhb |]. split; [exact Hwf |].
      split; [cbn; left; reflexivity |].
      unfold bl_lay in *. cbn in *. exact Hlay.
    + intros b Hb. unfold ba7 in Hb. cbn in Hb.
      destruct (ba_st ba) as [b0 |] eqn:B; [| discriminate]. cbn in Hb. injection Hb as <-.
      destruct (Hmr b0 B) as (_ & _ & Hts & Hdo & Hbo & _).
      cbn. rewrite C4. repeat split; auto. intros X; exfalso; apply X; reflexivity.
    + exact Hbd.
  - unfold bl_claim_nc. destruct (ba_st ba) as [b |] eqn:B; auto.
    destruct (dictref_model (ba_dict ba)); auto. intros _.
    destruct (Hmr b B) as (Hbs & _).
    unfold bl_step_nc. rewrite Hbs, Hs. unfold bl_step. rewrite Hbs, Hs.
    split; [| intros Hr; discriminate Hr].
    intros _. rewrite Z.add_0_r, sublist_nil. unfold ba7; cbn; rewrite B. auto.
Qed.

Lemma fcore3_join7' p fs1 pr :
  par_ok pr ->
  field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 0)) p * field_at Ews t_dctx (DOT _bType) (fs_bType fs1) p *
  field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 0)) p * fc7_rest p fs1 pr |-- fcore3 p (fs7 fs1) pr nullval.
Proof. intros. apply (fcore3_join7 p (fs7 fs1) pr); auto. Qed.

End CM_BL7Help_1.
