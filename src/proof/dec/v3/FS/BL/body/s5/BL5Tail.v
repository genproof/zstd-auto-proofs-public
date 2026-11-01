(* FS3-bl BODY, stage 5: case 5 after `if (validateChecksum) {..}` (BL5Mid.bl5_mid):
   ZSTD_DCtx_trace_end, expected = 0, stage = 0, return 0: the frame ends, the model's BHdrPrefix. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Mid.
Local Open Scope logic.

Section CM_BL5Tail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl5_tail_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  bv_stage v = BCk ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl5_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs)
    (Ssequence bl5_tl (seq_of_labeled_statement bl5_ls6))
    (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).
Proof.
  intros HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    Hpr Hpre Hci Hmr Hmd Hfpo Hst Hpcs Hpcsr Hlay.
  unfold bl5_mid, bl_R, bl_post, bl5_tl, bl5_ls6; cbn [seq_of_labeled_statement];
    simplify_func_tycontext; abbreviate_semax.
  pose proof Hci as Hci'.
  destruct Hci' as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs. rewrite Hst in Hcs. destruct Hcs as ((Hhok & Hfp & Hvc & Hxs) & Hck & He4).
  pose proof Hpre as Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hop & Hosz & Hoc & _ & Hbc).
  destruct (bl5_fs1 fs ob osz opos pcs (Zlength c)) as (Fv & Fx & Fd & Fp & Fi & Fdi & Fc & Ff).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  assert (Hc1: cold01 fs1) by (unfold cold01; rewrite Fc; exact Hcold).
  assert (Hfp1: fp_ok (fs_fParams (bl5_fs fs1))) by (change (fs_fParams (bl5_fs fs1)) with (fs_fParams fs1); rewrite Ff; exact Hfpo).
  Intros. rename H into Hckp.
  destruct (bl5_ok W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs Hpre Hci Hmr Hmd Hst Hpcs Hlay
    Hckp) as (A1 & A2 & A3 & A4).
  freeze [0; 1; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] FR.
  rewrite Fd, Hds, Fp. unfold vlong.
  forward. forward.
  forward_call (p, ds, pcs + Zlength c, 1).
  forward. forward.
  forward.
  thaw FR.
  sep_apply (bl5_fold_new p fs1 pr _ (Vlong (Int64.repr ds)) (Vlong (Int64.repr (pcs + Zlength c)))
               (Vlong (Int64.repr 0)) (Vint (Int.repr 0)) Hpr
               ltac:(rewrite Fv, Hvc; reflexivity) ltac:(rewrite Fd, Hds; reflexivity) ltac:(rewrite Fp; reflexivity)).
  Exists 0 oc (bl5_ba ba ob opos) (bl5_fs fs1) (TInit (bd_oxo od) ts) hb.
  unfold tabs_rep.
  entailer!.
  rewrite Z.add_0_r in A1.
  repeat match goal with |- _ /\ _ => split | |- _ -> _ => intros _ end.
  all: first [ exact Hc1 | exact Hfp1 | exact A1 | exact A2 | lia | reflexivity
             | (exists nil; split; [rewrite sublist_nil; reflexivity | constructor])
             | (unfold bl5_ba; cbn; rewrite Z.add_0_r; reflexivity)
             | (exists ts; split; [reflexivity | exact A3]) ].
Qed.

End CM_BL5Tail_1.
