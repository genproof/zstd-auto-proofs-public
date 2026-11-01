(* FS3-bl BODY: ZSTD_decompressContinue from its first statement: the srcSize check
   (ZSTD_nextSrcSizeToDecompressWithInputSize; its error return), then BLRest. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLRest.
Local Open Scope logic.

Section CM_BLPro_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_pro_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  BRc (dmode_of pr) od osz0 ba fs ts hb -> fp_ok (fs_fParams fs) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_pre0 DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp)
    (fn_body f_ZSTD_decompressContinue)
    (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros H Hpre HB Hfp.
  destruct HB as (v & Hci & Hmr & Hmd).
  pose proof Hci as (Hex & Hexr & Hst & Hfd & Hcold & Hdid & (pcs & Hpcs & Hpcsr) & Hds & Hhb & Hwf & Hcs & Hlay).
  pose proof Hpre as (H0 & H1 & H2 & H3 & H4 & H5 & SH & SH0 & SH1 & H6 & H7 & H8 & H9 & H10).
  unfold bl_pre0, bl_R, bl_post. simplify_func_tycontext.
  change (fn_body f_ZSTD_decompressContinue)
    with ltac:(let b := eval cbv [f_ZSTD_decompressContinue fn_body] in (fn_body f_ZSTD_decompressContinue) in exact b).
  abbreviate_semax.
  dw0.
  sep_apply (fcore3_split p fs pr). Intros.
  rewrite Hst, Hex. unfold vlong.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx (bl_size_ok v (ba_expect ba) (Zlength c) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_call (p, bl_stz (bv_stage v), fs_bType fs, ba_expect ba, Zlength c).
    { eapply bl_stage_pre; eauto. }
    change (match fs_bType fs with Vint b => Int.signed b | _ => 0 end) with (bl_btz fs).
    pose proof (next_size_range (bl_stz (bv_stage v)) (bl_btz fs) (ba_expect ba) (Zlength c)
                  ltac:(lia) (Zlength_nonneg c)) as Hnr.
    forward_if.
    { assert (Hne: Zlength c <> next_size (bl_stz (bv_stage v)) (bl_btz fs) (ba_expect ba) (Zlength c))
        by (intro E; apply H11; rewrite <- E; reflexivity).
      change (Vlong (Int64.repr (ba_expect ba))) with (vlong (ba_expect ba)).
      rewrite <- Hex, <- Hst. sep_apply (fcore3_join p fs pr H).
      dw0. dw0. dw0. dw0. forward.
      Exists (2 ^ 64 - 72) oc ba fs (TInit (bd_oxo od) ts) hb.
      unfold tabs_rep.
      entailer!.
      split; [intros X; exfalso; vm_compute in X; discriminate X |].
      split; [eapply bl_claim_size; eauto; lia |].
      f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity. }
    forward. entailer!.
    apply Int64.same_if_eq in H11. apply (f_equal Int64.unsigned) in H11.
    rewrite !Int64.unsigned_repr in H11 by rep_lia.
    apply (bl_next_ok (dmode_of pr) v (ba_expect ba) fs hb); [exact Hcs | apply Zlength_nonneg | lia | exact H11]. }
  Intros. rename H11 into Hsz.
  change (Vlong (Int64.repr (ba_expect ba))) with (vlong (ba_expect ba)).
  rewrite <- Hex, <- Hst. sep_apply (fcore3_join p fs pr H).
  apply semax_pre with (bl_pre0 DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp).
  { unfold bl_pre0. entailer!. }
  eapply (@bl_rest_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs);
    eauto.
Qed.

End CM_BLPro_1.
