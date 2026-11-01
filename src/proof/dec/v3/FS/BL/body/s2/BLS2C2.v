(* FS3-bl BODY stage 2: a 0-byte last block, no checksum *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2C2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_z2_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  cblock_size c = Some 0 -> bp_last (block_props_of c) = 1 -> fh_checksumFlag (bv_h v) = 0 ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid2 DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) ts hb shk shd ob osz opos oc
       shs src c v_bp)
    bl2_z
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Ec El Ef.
  pose proof Hci as (_ & _ & _ & _ & Hcold & _ & _ & (ds & Eds & Hdsr) & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & Hfcr & _) & _).
  pose proof (bh_ok_post (dmode_of pr) od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs 0
    Hpre Hci Hmr Hmd Hv Hpcs Hpcsr Ec ltac:(lia) Hlay) as Hpost.
  rewrite !Z.add_0_r in Hpost.
  pose proof Hpre as (_ & Hhist & _ & _ & _ & _ & _ & _ & _ & Hop & Hosz & Hoc & _).
  (* decodedSize is the length of the model's content so far *)
  assert (Hdsb: forall b, ba_st ba = Some b -> Zlength (bs_out b) = ds).
  { intros b B. destruct (Hmr b B) as (_ & _ & _ & Edec & _). rewrite Eds in Edec.
    pose proof (bl_out_len ba ob opos oc b Hhist ltac:(lia) B). pose proof (Zlength_nonneg (bs_out b)).
    assert (E64: Int64.repr ds = Int64.repr (Zlength (bs_out b))) by (unfold vlong in Edec; congruence).
    apply (f_equal Int64.unsigned) in E64. rewrite !Int64.unsigned_repr in E64 by rep_lia. lia. }
  assert (Eds1: fs_decodedSize (bl_fs1 fs ob osz opos pcs (Zlength c)) = vlong ds).
  { unfold bl_fs1, fsu_processedCSize; cbn [fs_decodedSize].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & _ & _ & C4 & _). rewrite C4. exact Eds. }
  unfold bl2_mid2, bl_R, bl_post. bl2_delta. unfold bl2_z. abbreviate_semax.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src).
  unfold fh_val, bp_val.
  forward.
  pose proof (bp_last01_3 c) as Hl01.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  assert (Hcold1: cold01 (bl_fs1 fs ob osz opos pcs (Zlength c))) by (apply bh_cold; exact Hcold).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  set (fs' := bh_fs fs1 (bv_h v) 0 bp) in *.
  assert (Elast: Z.land (le_field c 0 3) 1 = bp_last bp) by reflexivity.
  apply semax_if_seq. forward_if; [| exfalso; match goal with Hz: Int.repr (Z.land _ _) = Int.zero |- _ => rewrite Elast, El in Hz; exact (Int.one_not_zero Hz) end].
    (* the end of the frame: the content size check *)
    unfold fc2_rest. Intros.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_loop (PROPx P (LOCALx Q (SEPx R)))
        break: (PROPx ((bh_fcs_t (fh_contentSize (bv_h v)) ds = 0) :: P) (LOCALx Q (SEPx R))) end.
    { entailer!. }
    { rewrite Eds1. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'10 (Vint (Int.repr (bh_fcs_t (fh_contentSize (bv_h v)) ds))) :: Q)
          (SEPx R))) end.
      - forward. forward. forward. entailer!. apply bh_fcs_then; [rep_lia | auto].
      - forward. entailer!.
        match goal with Hx: Int64.eq _ _ = true |- _ =>
          apply Int64.same_if_eq in Hx; rewrite bh_fcs_else; auto; rep_lia end.
      - pose proof (bh_fcs_01 ds (fh_contentSize (bv_h v))) as F01.
        forward_if.
        + (* the frame declares another content size: corruption_detected *)
          assert (F1: bh_fcs_t (fh_contentSize (bv_h v)) ds <> 0) by (intros E; rewrite E in *; contradiction).
          destruct (bh_fcs_fail ds (fh_contentSize (bv_h v)) ltac:(rep_lia) F1) as [Q1 Q2].
          assert (Hcl: bl_claim_nc (dmode_of pr) ba ba c (2 ^ 64 - 20) opos osz oc).
          { eapply bh_err_fcs_claim; eauto. intros b B. rewrite (Hdsb b B). exact Q2. }
          dwq. dwq. dwq. dwq. forward.
          thaw FR. rewrite <- Eds1.
          sep_apply (fc2_rest_fold p fs1 pr).
          sep_apply (data_at_data_at_ Tsh t_bp (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)),
            Vint (Int.repr (bp_origSize bp)))) v_bp).
          set (fsE := fsu_expected (fsu_rleSize (fsu_bType fs1 (Vint (Int.repr (bp_type bp))))
                        (vlong (bp_origSize bp))) (vlong 0)).
          sep_apply (fcore3_join2 p fs1 fsE pr (fh_val (bv_h v)) (fs_stage fs1) (Vint (Int.repr (bp_type bp)))
            (vlong 0) (vlong (bp_origSize bp)) Hpr Hfp1 eq_refl eq_refl eq_refl eq_refl eq_refl).
          assert (Hcold2: cold01 fsE) by exact Hcold1.
          assert (Hfo2: fp_ok (fs_fParams fsE)) by (change (fp_ok (fs_fParams fs1)); unfold fs1; rewrite bl_fs1_fParams; exact Hfo).
          Exists (2 ^ 64 - 20) oc ba fsE (TInit (bd_oxo od) ts) hb. unfold tabs_rep. entailer!.
          split; [intros X; vm_compute in X; discriminate X |].
          f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
        + forward. entailer!.
          all: try (rewrite Eds1; apply derives_refl).
          destruct F01 as [E | E]; [exact E | rewrite E in *; exfalso;
            match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end]. }
    Intros.
    assert (Hfcs: bh_fcs_ok ba (bv_h v) 0 bp).
    { intros _ _ b B. rewrite (Hdsb b B). apply bh_fcs_pass; [rep_lia | auto]. }
    destruct (Hpost Hfcs) as (P1 & P2 & P3).
    forward. apply semax_if_seq. forward_if;
      [exfalso; match goal with Hz: Int.repr (fh_checksumFlag _) <> Int.zero |- _ =>
           rewrite Ef in Hz; exact (Hz eq_refl) end |].
      forward. forward. forward.
      thaw FR.
      sep_apply (fc2_rest_fold p fs1 pr).
      sep_apply (data_at_data_at_ Tsh t_bp (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)),
        Vint (Int.repr (bp_origSize bp)))) v_bp).
      sep_apply (fcore3_join2 p fs1 fs' pr (fh_val (bv_h v)) (Vint (Int.repr 0)) (Vint (Int.repr (bp_type bp)))
        (Vlong (Int64.repr 0)) (vlong (bp_origSize bp)) Hpr Hfp1
        ltac:(subst fs'; unfold bh_fs, bh_stg; cbn [fs_stage fsu_stage]; rewrite El, Ef; reflexivity)
        eq_refl
        ltac:(subst fs'; unfold bh_fs, bh_e; cbn [fs_expected fsu_stage fsu_expected]; rewrite El, Ef; reflexivity)
        eq_refl eq_refl).
  assert (Hfo': fp_ok (fs_fParams fs')) by (unfold fs'; rewrite bh_fs_fParams; unfold fs1; rewrite bl_fs1_fParams; exact Hfo).
      Exists 0 oc (bh_ba ba ob opos (bv_h v) 0 bp) fs' (TInit (bd_oxo od) ts) hb. unfold tabs_rep. entailer!.
Qed.

End CM_BLS2C2_1.
