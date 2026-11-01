(* FS3-bl BODY stage 2: a block header of a last block of cs > 0 bytes *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2B2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_x1_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs cs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BBlkHdr -> fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength c = 3 -> cblock_size c = Some cs -> cs <= fh_blockSizeMax (bv_h v) -> cs <> 0 -> bp_last (block_props_of c) = 1 ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid3 DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (bv_h v) ts hb shk shd ob osz opos oc
       shs src c v_bp cs)
    bl2_w
    (overridePost FF (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Hpr Hpre Hci Hmr Hmd Hfo Hv Hpcs Hpcsr Hlay Hc3 Ec Hcb Hc0 El.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf _].
  pose proof Hhf as ((Hbsm & Hck & _ & _) & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoc & _ & Hbc).
  pose proof (cblock_size_range3 _ _ Hbc Ec) as Hcr.
  assert (Hfp1: fs_fParams (bl_fs1 fs ob osz opos pcs (Zlength c)) = fh_val (bv_h v)).
  { destruct Hhf as (_ & Hfp & _). unfold bl_fs1, fsu_processedCSize; cbn [fs_fParams].
    destruct (cont_fields fs (offset_val opos ob) (osz - opos)) as (_ & C2 & _). rewrite C2. exact Hfp. }
  pose proof (bh_ok_post (dmode_of pr) od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs cs
    Hpre Hci Hmr Hmd Hv Hpcs Hpcsr Ec Hcb Hlay
    (bh_fcs_nz _ _ _ _ Hc0)) as Hpost.
  rewrite !Z.add_0_r in Hpost. destruct Hpost as (P1 & P2 & P3).
  unfold bl2_mid3, bl_R, bl_post. bl2_delta. unfold bl2_w. abbreviate_semax.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (bp := block_props_of c) in *.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr) (zstd_globals gv).
  unfold fh_val, bp_val.
  forward_if;
    [| exfalso; match goal with Hz: Int64.repr cs = Int64.zero |- _ =>
         apply (f_equal Int64.unsigned) in Hz; rewrite Int64.unsigned_repr in Hz by rep_lia; apply Hc0; exact Hz end].
  forward.
  assert (Elast: Z.land (le_field c 0 3) 1 = bp_last bp) by reflexivity.
  apply semax_if_seq. forward_if; [| exfalso; match goal with Hz: Int.repr (Z.land _ _) = Int.zero |- _ => rewrite Elast, El in Hz; exact (Int.one_not_zero Hz) end].
  forward. forward. forward.
  thaw FR.
  set (fs' := bh_fs fs1 (bv_h v) cs bp).
  assert (Est: fs_stage fs' = Vint (Int.repr 4)).
  { subst fs'; unfold bh_fs, bh_stg; cbn [fs_stage fsu_stage].
    replace (cs =? 0) with false by (symmetry; apply Z.eqb_neq; auto). rewrite El. reflexivity. }
  assert (Eex: fs_expected fs' = Vlong (Int64.repr cs)).
  { subst fs'; unfold bh_fs, bh_e; cbn [fs_expected fsu_stage fsu_expected].
    replace (cs =? 0) with false by (symmetry; apply Z.eqb_neq; auto). reflexivity. }
  sep_apply (data_at_data_at_ Tsh t_bp (Vint (Int.repr (bp_type bp)), (Vint (Int.repr (bp_last bp)),
    Vint (Int.repr (bp_origSize bp)))) v_bp).
  sep_apply (fcore3_join2 p fs1 fs' pr (fh_val (bv_h v)) (Vint (Int.repr 4)) (Vint (Int.repr (bp_type bp)))
    (Vlong (Int64.repr cs)) (vlong (bp_origSize bp)) Hpr Hfp1 Est eq_refl Eex eq_refl eq_refl).
  assert (Hfo': fp_ok (fs_fParams fs')) by (unfold fs'; rewrite bh_fs_fParams; unfold fs1; rewrite bl_fs1_fParams; exact Hfo).
  Exists 0 oc (bh_ba ba ob opos (bv_h v) cs bp) fs' (TInit (bd_oxo od) ts) hb. unfold tabs_rep. entailer!.
Qed.

End CM_BLS2B2_1.
