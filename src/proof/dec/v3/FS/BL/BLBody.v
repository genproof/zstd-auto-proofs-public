(* FS3-bl: the body of ZSTD_decompressContinue against its buffer-less internal specification (BLDefs), in the
   FS3 context for ANY stream relation and ANY buffer-less relation (the body calls no function whose
   specification mentions them).  The srcSize check in body/BLPro.v,
   the rest in body/BLRest.v, BLRest2.v, the cases in body/BLStage*.v. *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Require Import Zstd.proof.dec.v3.FS.BL.body.BLPro.
Local Open Scope logic.

Section CM_BLBody_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma BL_body_ok : forall (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  semax_body Vprog (FS3_G DENT TABS SR BR') f_ZSTD_decompressContinue (ZSTD_decompressContinue_ispec DENT TABS).
Proof.
  intros DENT TABS SR BR' HD HT.
  start_function.
  assert (Hpre: bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c)
    by (unfold bl_pre_ok; repeat (split; [assumption|]); assumption).
  assert_PROP (par_ok pr) as Hpr by (unfold fcore3; entailer!).
  apply semax_pre with (bl_pre0 DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp).
  { unfold bl_pre0. entailer!. }
  exact (@bl_pro_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           Hpr Hpre H ltac:(assumption)).
Qed.

End CM_BLBody_1.
