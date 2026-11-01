(* FS3-bl stages 3/4, compressed block: the call with capacity 0 (an empty window at dst, the output
   array lent to the witnesses). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.CompPost.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.S34Delta.
Local Open Scope logic.

Section CM_CompZero_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma comp_pws_cons sh N (oc: list val) b W :
  pws_pred (pw_bytes sh N oc b :: W) = (data_at sh (tarray tuchar N) oc b * pws_pred W)%logic.
Proof. reflexivity. Qed.

Lemma comp_arr0 sh (q: val) : isptr q -> emp |-- data_at sh (tarray tuchar 0) [] q.
Proof. intros Hq. rewrite data_at_zero_array_eq; auto. Qed.

Lemma comp_arr0_drop sh (q: val) (l: list val) : isptr q -> Zlength l = 0 -> data_at sh (tarray tuchar 0) l q |-- emp.
Proof.
  intros Hq Hl. destruct l; [| rewrite Zlength_cons in Hl; pose proof (Zlength_nonneg l); lia].
  rewrite data_at_zero_array_eq; auto.
Qed.

(* the end of the output array is weakly valid through the array (lent to the witnesses) or W *)
Lemma comp_end_wvp W shd osz (oc: list val) ob :
  writable_share shd -> buf_ok W shd osz ob -> 0 <= osz -> isptr ob ->
  pws_pred (pw_bytes shd osz oc ob :: W) |-- weak_valid_pointer (offset_val osz ob).
Proof.
  intros Hw Hb Ho Hp. rewrite comp_pws_cons.
  assert (Hni: sepalg.nonidentity shd) by (apply readable_nonidentity, writable_readable; auto).
  destruct (zlt 0 osz).
  - apply sepcon_weak_valid_pointer1. eapply derives_trans; [apply data_at_memory_block |].
    apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
  - assert (osz = 0) by lia. subst osz. apply sepcon_weak_valid_pointer2.
    unfold buf_ok in Hb. eapply derives_trans; [| eapply derives_trans; [exact Hb | apply andp_left2, derives_refl]].
    rewrite data_at__eq, data_at_zero_array_eq; auto. rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma comp_out_lend shd osz (oc: list val) ob W opos :
  isptr ob -> opos = osz ->
  data_at shd (tarray tuchar osz) oc ob * pws_pred W
  |-- pws_pred (pw_bytes shd osz oc ob :: W) * data_at shd (tarray tuchar 0) [] (offset_val opos ob).
Proof.
  intros Hp ->. rewrite comp_pws_cons, data_at_zero_array_eq; auto.
  - rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma comp_out_back shd osz (oc: list val) ob W opos (ocm: list val) :
  isptr ob -> Zlength ocm = 0 ->
  pws_pred (pw_bytes shd osz oc ob :: W) * data_at shd (tarray tuchar 0) ocm (offset_val opos ob)
  |-- data_at shd (tarray tuchar osz) oc ob * pws_pred W.
Proof.
  intros Hp Hl. rewrite comp_pws_cons.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply comp_arr0_drop; auto] |].
  rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma comp_zero_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
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
  bv_bt v = 2 -> osz - opos = 0 -> (forall b, ba_st ba = Some b -> bytes_ok (bs_out b)) ->
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
  destruct (comp_lay_ptrs od osz ba ob opos _ Hwf Hlay) as (_ & _ & Hde).
  assert (Eop: opos = osz) by lia.
  unfold bl_case_pre, bl_R, bl_post. s34c_simplify. abbreviate_semax.
  simpl seq_of_labeled_statement.
  dw0.
  assert_PROP (isptr ob) as Hob by entailer!.
  assert_PROP (isptr src) as Hsrc by entailer!.
  unfold fcore3. Intros. rewrite <- (comp_ext_res shk od).
  sep_apply (comp_out_lend shd osz oc ob W opos Hob Eop).
  forward_call (gv, p, fs1, bd_oxo od, ts, fh_blockSizeMax (bv_h v), 1, pw_bytes shd osz oc ob :: W,
    {| oa_sh := shd; oa_base := offset_val opos ob; oa_N := 0; oa_c := []; oa_d := 0; oa_cap := osz - opos |},
    {| iw_sh := shs; iw_base := src; iw_N := Zlength c; iw_c := zbytes c; iw_off := 0; iw_s := c |},
    comp_h shk od ba v opos).
  { cbn [oa_sh oa_N oa_c oa_base]. cancel. }
  { cbn [oa_cap oa_d oa_base oa_N hc_ext hc_ps comp_h].
    split; [unfold outarr_ok; cbn [oa_sh oa_c oa_N oa_d oa_cap]; split; [exact Hwsd |];
            split; [reflexivity |]; repeat split; lia |].
    split; [apply comp_win; auto |].
    split; [destruct Hhdr; lia |].
    split; [rewrite Kf, Hfp; reflexivity |].
    split; [rewrite Kc; exact Hc01 |].
    split; [intros _; rewrite isptr_offset_val_zero by (destruct ob; try contradiction; exact I);
            rewrite Eop; apply comp_end_wvp; auto; lia |].
    split; [intros; lia |].
    split; [destruct od as [d0 |]; [unfold comp_ext; destruct (eq_dec (bd_eb d0) nullval) |]; exact I |].
    split; [apply (comp_hpo od osz ba ob opos); [exact Hwf | exact Hlay] |].
    assert (Hx0: ext0_ok (pw_bytes shd osz oc ob :: W) fs1 (comp_ext shk od))
      by (apply ext0_ok_cons; apply (comp_ext0 W shk od shd (osz - opos) (offset_val opos ob)); auto).
    (* the empty window's history: the dictionary only *)
    assert (Hhd0: hist_def [] 0 (bl_start ba opos) (comp_ext shk od)).
    { apply comp_hist_def0; [| exact Hwf].
      destruct (comp_seg ba ob opos oc Hh ltac:(lia)) as (Hf & _). lia. }
    first [exact Hx0 | exact (conj Hx0 Hhd0)]. }
  Intros vret. destruct vret as [[[r ocm] cold] ts'].
  cbn [fst snd oa_c oa_d oa_cap oa_N oa_sh oa_base iw_s iw_c iw_N iw_sh iw_base hc_ext hc_ps hc_hist hc_out hc_wsize
       comp_h] in *.
  rewrite comp_ext_res. sep_apply (comp_tabs TABS gv p (bd_oxo od) ts'). Intros lxb.
  match goal with Hl: Zlength ocm = 0 |- _ => sep_apply (comp_out_back shd osz oc ob W opos ocm Hob Hl) end.
  sep_apply (fcore3_fold p (fs_set_cold fs1 cold) pr Hpr).
  sep_apply (fcore3_split p (fs_set_cold fs1 cold) pr). Intros.
  forward.
  change (Int.signed (Int.repr 0)) with 0.
  sep_apply (comp_join p fs1 cold pr Hpr).
  assert (Hmid: s34_mid_ok od ba v osz opos oc c r oc 0 cold (comp_t (bd_oxo od) ts' lxb)).
  { eapply (comp_zero_post (dmode_of pr) od ba fs ts v osz opos oc c r ocm cold ts' lxb fs1 (osz - opos)); eauto.
    unfold cold01; rewrite Kc; exact Hc01. }
  forward.
  unfold s34_mid. Exists r oc 0 cold (comp_t (bd_oxo od) ts' lxb).
  entailer!.
Qed.

End CM_CompZero_1.
