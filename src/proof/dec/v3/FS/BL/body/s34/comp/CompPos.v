(* FS3-bl stages 3/4, compressed block: the call with capacity > 0 (the whole output array). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompPost.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.S34Delta.
Local Open Scope logic.

Section CM_CompPos_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma comp_pos_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs st: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bl_stz (bv_stage v) = st ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  bv_bt v = 2 -> 0 < osz - opos -> (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp st)
    (seq_of_labeled_statement (select_switch 2 s34_ls))
    (switch_ret_assert
       (overridePost
          (s34_mid DENT TABS W gv p pr od ba (bl_fs1 fs ob osz opos pcs (Zlength c)) hb shk shd ob osz opos oc shs src
             c v_bp v)
          (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)))).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hbm Hst Hstz Hpcs Hpcsr Hsz Hlay Hbt Hcap HD13.
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)).
  destruct Hpre as (Hne & Hh & Hoz & Hbo & Hbs & Hbdb & Hwsd & Hrs & Hrk & Hop & Hosz & Hloc & Hlc & Hbc).
  destruct (comp_cinv _ _ _ _ _ _ _ Hci Hst) as (Hhdr & Hfp & Hifd & Hc01 & Hwf).
  destruct (fs1_keep fs ob osz opos pcs (Zlength c)) as (Kf & Ki & Kc). fold fs1 in Kf, Ki, Kc.
  destruct (comp_lay_pos od osz ba ob opos _ shk Hwf Hrk ltac:(lia) Hlay) as (Hob & Hlo & Hde).
  unfold bl_case_pre, bl_R, bl_post. s34c_simplify. abbreviate_semax.
  simpl seq_of_labeled_statement.
  dw0.
  assert_PROP (isptr src) as Hsrc by entailer!.
  unfold fcore3. Intros. rewrite <- (comp_ext_res shk od).
  forward_call (gv, p, fs1, bd_oxo od, ts, fh_blockSizeMax (bv_h v), 1, W,
    {| oa_sh := shd; oa_base := ob; oa_N := osz; oa_c := oc; oa_d := opos; oa_cap := osz - opos |},
    {| iw_sh := shs; iw_base := src; iw_N := Zlength c; iw_c := zbytes c; iw_off := 0; iw_s := c |},
    comp_h shk od ba v opos).
  { cbn [oa_cap oa_d oa_base hc_ext comp_h].
    split; [unfold outarr_ok; cbn [oa_sh oa_c oa_N oa_d oa_cap]; split; [exact Hwsd |]; repeat split; lia |].
    split; [apply comp_win; auto |].
    split; [destruct Hhdr; lia |].
    split; [rewrite Kf, Hfp; reflexivity |].
    split; [rewrite Kc; exact Hc01 |].
    split; [intros; lia |].
    split; [destruct od as [d0 |]; [unfold comp_ext; destruct (eq_dec (bd_eb d0) nullval) |]; exact I |].
    split; [apply (comp_hpo od osz ba ob opos); [exact Hwf | exact Hlay] |].
    assert (Hx0: ext0_ok W fs1 (comp_ext shk od))
      by (apply (comp_ext0 W shk od shd (osz - opos) (offset_val opos ob)); auto).
    (* the history the block's matches copy: the frame's output so far, then the dictionary *)
    assert (Hhd0: hist_def oc opos (bl_start ba opos) (comp_ext shk od))
      by (apply (comp_hist_def shk od ba ob opos oc); auto; lia).
    first [exact Hx0 | exact (conj Hx0 Hhd0)]. }
  Intros vret. destruct vret as [[[r oc'] cold] ts'].
  cbn [fst snd oa_c oa_d oa_cap oa_N oa_sh oa_base iw_s iw_c iw_N iw_sh iw_base hc_ext hc_ps hc_hist hc_out hc_wsize
       comp_h] in *.
  rewrite comp_ext_res. sep_apply (comp_tabs TABS gv p (bd_oxo od) ts'). Intros lxb.
  sep_apply (fcore3_fold p (fs_set_cold fs1 cold) pr Hpr).
  sep_apply (fcore3_split p (fs_set_cold fs1 cold) pr). Intros.
  forward.
  change (Int.signed (Int.repr 0)) with 0.
  sep_apply (comp_join p fs1 cold pr Hpr).
  assert (Hmid: s34_mid_ok od ba v osz opos oc c r oc' 0 cold (comp_t (bd_oxo od) ts' lxb)).
  { eapply (comp_pos_post (dmode_of pr) od ba fs ts v ob osz opos oc c r oc' cold ts' lxb fs1 shk); eauto; try lia.
    unfold cold01; rewrite Kc; exact Hc01. }
  forward.
  unfold s34_mid. Exists r oc' 0 cold (comp_t (bd_oxo od) ts' lxb).
  entailer!.
Qed.

End CM_CompPos_1.
