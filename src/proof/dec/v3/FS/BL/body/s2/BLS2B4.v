(* FS3-bl BODY stage 2: a block header of a 0-byte block: the stores, then BLS2C *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2C.
Local Open Scope logic.

Section CM_BLS2B4_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_x0_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs cs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength c = 3 -> cblock_size c = Some cs -> cs <= fh_blockSizeMax (bv_h v) -> cs = 0 ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid3 DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) ts hb shk shd ob osz opos oc
       shs src c v_bp cs)
    bl2_w
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Hc3 Ec Hcb E0.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & _ & _) & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc & _ & Hbc).
  pose proof (cblock_size_range3 _ _ Hbc Ec) as Hcr.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  unfold bl2_mid3, bl_R, bl_post. bl2_delta. unfold bl2_w. abbreviate_semax.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr) (zstd_globals gv).
  unfold fh_val, bp_val.
  subst cs.
  apply semax_if_seq. forward_if;
    [exfalso; match goal with Hz: Int64.repr 0 <> Int64.zero |- _ => exact (Hz eq_refl) end |].
  thaw FR.
  eapply semax_pre; [| apply (@bl2_z_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz
    opos oc shs src c v_bp v pcs Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Ec)].
  unfold bl2_mid2. entailer!. apply derives_refl.
Qed.

End CM_BLS2B4_1.
