(* FS3-bl BODY stage 2: the block header after ZSTD_getcBlockSize succeeded (BLS2B1..4, BLS2L, BLS2S). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2B1 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2B2 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2B3 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2B4 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2L Zstd.proof.dec.v3.FS.BL.body.s2.BLS2S.
Local Open Scope logic.

Section CM_BLS2X_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_x_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs cs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength c = 3 -> cblock_size c = Some cs ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc
       shs src c v_bp cs)
    bl2_x
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Hc3 Ec.
  destruct (Z_lt_le_dec (fh_blockSizeMax (bv_h v)) cs) as [Hcb | Hcb].
  { eapply bl2_xe_ok; eauto. }
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc).
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  rewrite bl2_x_eq.
  eapply semax_seq; [eapply bl2_loop_ok; eauto |].
  apply (@bl2_y_ok CMI Espec DENT TABS SR BR' W gv p pr od _ (bv_h v) ts hb shk shd ob osz opos oc shs src c v_bp cs _
    Hpr Hfp1 Hbc).
  destruct (Z.eq_dec cs 0) as [E0 | Hc0].
  - eapply bl2_x0_ok; eauto.
  - destruct (bp_last01_3 c) as [El | El].
    + eapply bl2_x2_ok; eauto.
    + eapply bl2_x1_ok; eauto.
Qed.

End CM_BLS2X_1.
