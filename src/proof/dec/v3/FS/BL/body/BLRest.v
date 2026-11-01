(* FS3-bl BODY: ZSTD_decompressContinue after the srcSize check: ZSTD_checkContinuity (BLCont), then
   BLRest2. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLRest2.
Local Open Scope logic.

Section CM_BLRest_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_rest_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_pre0 DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp)
    bl_rest
    (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros H Hpre Hci Hmr Hmd Hfp Hpcs Hpcsr Hsz.
  pose proof Hci as (Hex & Hexr & Hst & Hfd & Hcold & Hdid & _ & Hds & Hhb & Hwf & Hcs & Hlay).
  pose proof Hpre as (H0 & H1 & H2 & H3 & H4 & H5 & SH & SH0 & SH1 & H6 & H7 & H8 & H9 & H10).
  unfold bl_pre0, bl_rest. simplify_func_tycontext. abbreviate_semax.
  unfold fcore3. Intros.
  assert_PROP (field_compatible (tarray tuchar osz) [] ob) as Fob by entailer!.
  assert_PROP (match od with
               | None => True
               | Some d => isptr (bd_eb d) -> field_compatible (tarray tuchar (Zlength (bd_b d))) nil (bd_eb d)
               end) as Fod.
  { destruct od as [d|]; [| entailer!]. unfold bd_res, bytes_at.
    destruct (eq_dec (bd_eb d) nullval) as [E|E]; [rewrite E; entailer!; contradiction | entailer!]. }
  destruct (bl_cont_ok W (dmode_of pr) od osz0 ba fs hb v shk shd ob osz opos oc shs src c Hpre Hci Fob Fod)
    as (Cg & Ct & Cm & Cl).
  rewrite <- bd_pw_res.
  sep_apply (pws_cons2_fold shd osz oc ob (bd_pw shk od) W).
  forward_call (p, fs, pw_bytes shd osz oc ob :: bd_pw shk od :: W, offset_val opos ob, osz - opos).
  sep_apply (pws_cons2_unfold shd osz oc ob (bd_pw shk od) W). rewrite bd_pw_res.
  sep_apply (fcore3_fold p (continuity fs (offset_val opos ob) (osz - opos)) pr H).
  apply semax_pre with (bl_pre0 DENT TABS W gv p pr od (continuity fs (offset_val opos ob) (osz - opos)) ts hb shk shd ob
                          osz opos oc shs src c v_bp).
  { unfold bl_pre0. entailer!. }
  exact (@bl_rest2_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs H Hpre Hci Hmr Hmd Hfp Hpcs Hpcsr Hsz Cl).
Qed.

End CM_BLRest_1.
