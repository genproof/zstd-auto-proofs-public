(* FS3-bl BODY: the switch on dctx->stage, dispatched to the stage lemmas (one small lemma per stage). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.BLStage0 Zstd.proof.dec.v3.FS.BL.body.BLStage1 Zstd.proof.dec.v3.FS.BL.body.BLStage2 Zstd.proof.dec.v3.FS.BL.body.BLStage34 Zstd.proof.dec.v3.FS.BL.body.BLStage5 Zstd.proof.dec.v3.FS.BL.body.BLStage6 Zstd.proof.dec.v3.FS.BL.body.BLStage7.
Local Open Scope logic.

Section CM_BLDispatch_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bl_disp_spec (P: blv -> Prop) : Prop :=
  forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  P v ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp (bl_stz (bv_stage v)))
    (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr (bl_stz (bv_stage v)))) bl_switch))
    (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).

Lemma bl_dispatch_ok : bl_disp_spec (fun _ => True).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    Hpr Hpre Hci Hmr Hmd Hfp _ Hpcs Hpcsr Hsz Hlay.
  destruct (bv_stage v) eqn:Ev; cbn [bl_stz]; rewrite Int.unsigned_repr by rep_lia.
  - change (seq_of_labeled_statement (select_switch 0 bl_switch)) with (bl_cmd 0).
    eapply bl_stage0_ok; eauto; rewrite Ev; reflexivity.
  - change (seq_of_labeled_statement (select_switch 1 bl_switch)) with (bl_cmd 1).
    eapply bl_stage1_ok; eauto; rewrite Ev; reflexivity.
  - change (seq_of_labeled_statement (select_switch 2 bl_switch)) with (bl_cmd 2).
    eapply bl_stage2_ok; eauto; rewrite Ev; reflexivity.
  - change (seq_of_labeled_statement (select_switch 3 bl_switch)) with (bl_cmd 3).
    eapply bl_stage34_ok; eauto; rewrite Ev; auto.
  - change (seq_of_labeled_statement (select_switch 4 bl_switch)) with (Ssequence Sskip (bl_cmd 3)).
    apply -> semax_skip_seq.
    eapply bl_stage34_ok; eauto; rewrite Ev; auto.
  - change (seq_of_labeled_statement (select_switch 5 bl_switch)) with (bl_cmd 5).
    eapply bl_stage5_ok; eauto; rewrite Ev; reflexivity.
  - change (seq_of_labeled_statement (select_switch 6 bl_switch)) with (bl_cmd 6).
    eapply bl_stage6_ok; eauto; rewrite Ev; reflexivity.
  - change (seq_of_labeled_statement (select_switch 7 bl_switch)) with (bl_cmd 7).
    eapply bl_stage7_ok; eauto; rewrite Ev; reflexivity.
Qed.

Lemma bl_switch_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (HD: DENT_OK DENT) (HT: TABS_OK TABS)
    W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs :
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp (bl_stz (bv_stage v)))
    (Sswitch (Etempvar _t'20 tint) bl_switch)
    (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
Proof.
  intros.
  apply semax_switch_PQR with (n := bl_stz (bv_stage v));
    [reflexivity | unfold bl_case_pre; entailer! | unfold bl_case_pre; entailer! |].
  eapply bl_dispatch_ok; eauto.
Qed.

End CM_BLDispatch_1.
