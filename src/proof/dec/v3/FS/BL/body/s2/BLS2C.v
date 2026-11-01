(* FS3-bl BODY stage 2: a block header of a 0-byte block (last: end of frame or checksum; else the next
   block header). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2C1 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2C2 Zstd.proof.dec.v3.FS.BL.body.s2.BLS2C3.
Local Open Scope logic.

Section CM_BLS2C_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_z_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  cblock_size c = Some 0 ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid2 DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) ts hb shk shd ob osz opos oc
       shs src c v_bp)
    bl2_z
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Ec.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [((_ & Hck & _ & _) & _) _].
  destruct (bp_last01_3 c) as [El | El].
  - eapply bl2_z3_ok; eauto.
  - destruct Hck as [Ef | Ef].
    + eapply bl2_z2_ok; eauto.
    + eapply bl2_z1_ok; eauto.
Qed.

End CM_BLS2C_1.
