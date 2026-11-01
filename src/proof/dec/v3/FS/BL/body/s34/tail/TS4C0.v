(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): the branch ts4_c0 of the last block
   without a checksum (ZSTD_DCtx_trace_end; expected = 0; stage = 0: the frame ends), then return rSize. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4C1.
Local Open Scope logic.

Section CM_TS4C0_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ts4_c0_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba ba': blabs)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    (v_bp: val) (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) (Q: environ -> mpred),
  par_ok pr -> fs_fParams fsB = fh_val (bv_h v) -> fs_decodedSize fsB = vlong (ds + r) ->
  fs_processedCSize fsB = vlong (pcs + Zlength c) ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba' (t34_fsE fsB BHdrPrefix 0) t' hb ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_m25 DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t')
    (Ssequence ts4_c0 t34_ret)
    (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros W gv p pr od ba ba' hb shk shd ob osz opos oc shs src c v_bp r v ds pcs fsB oc' t' Q
    Hpr Bp Bd Bq HP.
  unfold ts4_m25, ts4_c0, t34_ret, t34_R, bl_R, bl_post. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward_call (p, ds + r, pcs + Zlength c, 1).
  forward. forward. forward.
  sep_apply (ts4_fold p fsB pr BHdrPrefix 0 _ _ _ Hpr (eq_sym Bp) (eq_sym Bd) (eq_sym Bq)).
  Exists r oc' ba' (t34_fsE fsB BHdrPrefix 0) t' hb.
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
  apply andp_right;
    [apply prop_right; exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P8 (conj P6 (conj P7 eq_refl))))))))
    | cancel].
Qed.

End CM_TS4C0_1.
