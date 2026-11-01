(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): ts4_s2, the end of the content size
   check of the last block: if (t'16) { DEBUGLOGs; return -20 } (the error post: a hypothesis). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4Sep.
Local Open Scope logic.

Section CM_TS4F2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ts4_s2_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    (v_bp: val) (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) (Q: environ -> mpred),
  par_ok pr -> fs_fParams fsB = fh_val (bv_h v) -> fs_decodedSize fsB = vlong (ds + r) ->
  fs_processedCSize fsB = vlong (pcs + Zlength c) -> fs_expected fsB = vlong 0 ->
  fs_stage fsB = Vint (Int.repr (bl_stz BLastBlk)) ->
  0 <= fh_contentSize (bv_h v) <= Int64.max_unsigned ->
  (~ t34_fcs_ok v ds r -> t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba fsB t' hb) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_m15 DENT TABS nil W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t')
    ts4_s2
    (loop1_ret_assert
       (ts4_m15 DENT TABS (t34_fcs_ok v ds r :: nil) W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs
          fsB oc' t')
       (overridePost
          (ts4_m15 DENT TABS (t34_fcs_ok v ds r :: nil) W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds
             pcs fsB oc' t')
          (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q))).
Proof.
  intros W gv p pr od ba hb shk shd ob osz opos oc shs src c v_bp r v ds pcs fsB oc' t' Q
    Hpr Bp Bd Bq Be Bs Hfcs Hbad.
  unfold ts4_m15, ts4_s2, t34_R, bl_R, bl_post. simplify_func_tycontext. abbreviate_semax. unfold fh_val.
  pose proof (ts4_t15_01 (fh_contentSize (bv_h v)) (ds + r)) as F01.
  forward_if.
  - ts4_dw. ts4_dw. ts4_dw. ts4_dw. forward.
    assert (F1: ts4_t15 (fh_contentSize (bv_h v)) (ds + r) <> 0)
      by (destruct F01 as [E | E]; rewrite E in *; [contradiction | lia]).
    destruct (Hbad (ts4_bad_of v ds r ltac:(rep_lia) F1)) as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
    sep_apply (ts4_fold p fsB pr BLastBlk 0 _ _ _ Hpr (eq_sym Bp) (eq_sym Bd) (eq_sym Bq)).
    rewrite (t34_fsE_same fsB BLastBlk 0 Be Bs).
    Exists (2 ^ 64 - 20) oc' ba fsB t' hb.
    rewrite (Int64.eqm_samerepr (- (20)) (2 ^ 64 - 20)) by (exists (-1); reflexivity).
    apply andp_right;
      [apply prop_right; exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P8 (conj P6 (conj P7 eq_refl))))))))
      | cancel].
  - forward. entailer!.
    destruct F01 as [E | E]; [apply ts4_ok_of; exact E |].
    rewrite E in *. exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end.
Qed.

End CM_TS4F2_1.
