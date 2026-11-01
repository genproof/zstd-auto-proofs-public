(* FS3-bl BODY: ZSTD_decompressContinue after ZSTD_checkContinuity: processedCSize, the stage, the
   switch (BLDispatch). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLHelp.
Local Open Scope logic.

Section CM_BLRest2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_rest2_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_pre0 DENT TABS W gv p pr od (continuity fs (offset_val opos ob) (osz - opos)) ts hb shk shd ob osz opos oc shs src c v_bp)
    bl_rest2
    (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros H Hpre Hci Hmr Hmd Hfp Hpcs Hpcsr Hsz Cl.
  pose proof Hci as (Hex & Hexr & Hst & Hfd & Hcold & Hdid & _ & Hds & Hhb & Hwf & Hcs & Hlay).
  pose proof Hpre as (H0 & H1 & H2 & H3 & H4 & H5 & SH & SH0 & SH1 & H6 & H7 & H8 & H9 & H10).
  unfold bl_pre0, bl_rest2. simplify_func_tycontext. abbreviate_semax.
  unfold fcore3. Intros.
  destruct (cont_same fs (offset_val opos ob) (osz - opos)) as [Ep1 Est1].
  set (fs1 := continuity fs (offset_val opos ob) (osz - opos)) in *.
  unfold frame_fields at 1. rewrite Ep1, Hpcs. unfold vlong. Intros.
  forward. forward. forward. { rewrite Est1, Hst. entailer!. }
  rewrite add64_repr.
  sep_apply (frame_fields_fold_pc p fs1 (Vlong (Int64.repr (pcs + Zlength c)))).
  sep_apply (fcore3_fold p (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + Zlength c)))) pr H).
  rewrite Est1, Hst.
  change (fsu_processedCSize fs1 (Vlong (Int64.repr (pcs + Zlength c)))) with (bl_fs1 fs ob osz opos pcs (Zlength c)).
  apply semax_pre with (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob
                          osz opos oc shs src c v_bp (bl_stz (bv_stage v))).
  { unfold bl_case_pre. go_lower. entailer!. }
  subst fs1.
  exact (@bl_switch_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs H Hpre Hci Hmr Hmd Hfp Hpcs Hpcsr Hsz Cl).
Qed.

End CM_BLRest2_1.
