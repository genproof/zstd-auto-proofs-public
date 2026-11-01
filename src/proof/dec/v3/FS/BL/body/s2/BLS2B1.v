(* FS3-bl BODY stage 2: a block header of a block larger than blockSizeMax (corruption_detected) *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2B1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_xe_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs cs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength c = 3 -> cblock_size c = Some cs -> fh_blockSizeMax (bv_h v) < cs ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc
       shs src c v_bp cs)
    bl2_x
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Hc3 Ec Hcb.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & _ & _) & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc & _ & Hbc).
  pose proof (cblock_size_range3 _ _ Hbc Ec) as Hcr.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  unfold bl2_mid, bl_R, bl_post. bl2_delta. unfold bl2_x. abbreviate_semax.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  sep_apply (fcore3_split2 p fs1 pr _ Hfp1). Intros.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr) (zstd_globals gv).
  unfold fh_val, bp_val.
  assert (Hcold1: cold01 fs1) by (apply bh_cold; destruct Hci as (_ & _ & _ & _ & H & _); exact H).
  assert (Hcl: bl_claim_nc (dmode_of pr) ba ba c (2 ^ 64 - 20) opos osz oc).
  { eapply bh_err_claim; eauto. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (@FF (environ -> mpred) _) end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    - dwq. dwq. dwq. dwq. forward.
      thaw FR.
      sep_apply (data_at_data_at_ Tsh t_bp (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)),
        Vint (Int.repr (bp_origSize bp)))) v_bp).
      sep_apply (fcore3_join2 p fs1 fs1 pr (fh_val (bv_h v)) (fs_stage fs1) (fs_bType fs1) (fs_expected fs1)
        (fs_rleSize fs1) Hpr Hfp1 eq_refl eq_refl eq_refl eq_refl eq_refl).
      Exists (2 ^ 64 - 20) oc ba fs1 (TInit (bd_oxo od) ts) hb. unfold tabs_rep. entailer!.
      split; [unfold fs1; rewrite bl_fs1_fParams; exact Hfo |].
      split; [intros X; vm_compute in X; discriminate X |].
      f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
    - exfalso. unfold ZSTD_BLOCKSIZE_MAX in Hbsm.
      match goal with Hx: Int.unsigned (Int.repr (fh_blockSizeMax _)) >= _ |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end. lia. }
Qed.

End CM_BLS2B1_1.
