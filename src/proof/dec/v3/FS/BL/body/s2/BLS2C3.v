(* FS3-bl BODY stage 2: a 0-byte block, not the last *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2C3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_z3_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  cblock_size c = Some 0 -> bp_last (block_props_of c) = 0 ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid2 DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) ts hb shk shd ob osz opos oc
       shs src c v_bp)
    bl2_z
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Ec El.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & _ & _) & _).
  pose proof (bh_ok_post (dmode_of pr) od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs 0
    Hpre Hci Hmr Hmd Hv Hpcs Hpcsr Ec ltac:(lia) Hlay
    (bh_fcs_nl _ _ _ _ El)) as Hpost.
  rewrite !Z.add_0_r in Hpost. destruct Hpost as (P1 & P2 & P3).
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc & _).
  unfold bl2_mid2, bl_R, bl_post. bl2_delta. unfold bl2_z. abbreviate_semax.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr).
  unfold fh_val, bp_val.
  forward.
  pose proof (bp_last01_3 c) as Hl01.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  set (fs' := bh_fs fs1 (bv_h v) 0 bp) in *.
  assert (Elast: Z.land (le_field c 0 3) 1 = bp_last bp) by reflexivity.
  apply semax_if_seq. forward_if;
    [exfalso; match goal with Hz: Int.repr (Z.land _ _) <> Int.zero |- _ =>
       rewrite Elast, El in Hz; exact (Hz eq_refl) end |].
    unfold zstd_globals. Intros.
    forward.
    sep_apply (zstd_globals_fold3 gv).
    forward. forward. forward.
      thaw FR.
      sep_apply (data_at_data_at_ Tsh t_bp (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)),
        Vint (Int.repr (bp_origSize bp)))) v_bp).
      sep_apply (fcore3_join2 p fs1 fs' pr (fh_val (bv_h v)) (Vint (Int.repr 2)) (Vint (Int.repr (bp_type bp)))
        ZSTD_blockHeaderSize_val (vlong (bp_origSize bp)) Hpr Hfp1
        ltac:(subst fs'; unfold bh_fs, bh_stg; cbn [fs_stage fsu_stage]; rewrite El; reflexivity)
        eq_refl
        ltac:(subst fs'; unfold bh_fs, bh_e; cbn [fs_expected fsu_stage fsu_expected]; rewrite El; reflexivity)
        eq_refl eq_refl).
  assert (Hfo': fp_ok (fs_fParams fs')) by (unfold fs'; rewrite bh_fs_fParams; unfold fs1; rewrite bl_fs1_fParams; exact Hfo).
      Exists 0 oc (bh_ba ba ob opos (bv_h v) 0 bp) fs' (TInit (bd_oxo od) ts) hb. unfold tabs_rep. entailer!.
Qed.

End CM_BLS2C3_1.
