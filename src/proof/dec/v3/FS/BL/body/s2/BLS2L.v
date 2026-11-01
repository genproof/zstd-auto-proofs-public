(* FS3-bl BODY stage 2: the blockSizeMax check of a block header that passes it *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2L_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_loop_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs cs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength c = 3 -> cblock_size c = Some cs -> cs <= fh_blockSizeMax (bv_h v) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc
       shs src c v_bp cs)
    bl2_loop
    (overridePost
       (bl2_mid DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc
          shs src c v_bp cs)
       (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hv Hpcs Hpcsr Hlay Hc3 Ec Hcb.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & _ & _) & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc & _ & Hbc).
  pose proof (cblock_size_range3 _ _ Hbc Ec) as Hcr.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  unfold bl2_mid at 1. unfold bl_R, bl_post. bl2_delta. unfold bl2_loop. abbreviate_semax.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  sep_apply (fcore3_split2 p fs1 pr _ Hfp1). Intros.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr) (zstd_globals gv).
  unfold fh_val, bp_val.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R))) break: (PROPx P (LOCALx Q (SEPx R))) end.
  { apply ENTAIL_refl. }
  { forward. forward_if.
    - exfalso. unfold ZSTD_BLOCKSIZE_MAX in Hbsm.
      match goal with Hx: Int.unsigned (Int.repr (fh_blockSizeMax _)) < _ |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end. lia.
    - forward. entailer!. }
  thaw FR.
  sep_apply (fcore3_join2 p fs1 fs1 pr (fh_val (bv_h v)) (fs_stage fs1) (fs_bType fs1) (fs_expected fs1)
    (fs_rleSize fs1) Hpr Hfp1 eq_refl eq_refl eq_refl eq_refl eq_refl).
  unfold bl2_mid. entailer!.
Qed.

End CM_BLS2L_1.
