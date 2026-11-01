(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): the content size test of the last block,
   ts4_s1: t'29 = fParams.frameContentSize; t'16 = (t'29 != -1) ? (decodedSize != fcs) : 0. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4Sep.
Local Open Scope logic.

Section CM_TS4F1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ts4_s1_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z)
    (v_bp: val) (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) (R: ret_assert),
  0 <= fh_contentSize (bv_h v) <= Int64.max_unsigned ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_mid DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t')
    ts4_s1
    (overridePost (ts4_m15 DENT TABS nil W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t') R).
Proof.
  intros W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t' R Hfcs.
  unfold ts4_mid, ts4_m15, ts4_s1. simplify_func_tycontext. abbreviate_semax. unfold fh_val.
  forward. ts4_fif _t'16 (Vint (Int.repr (ts4_t15 (fh_contentSize (bv_h v)) (ds + r)))).
  - forward. forward. forward. entailer!. apply ts4_fthen; [rep_lia | auto].
  - forward. entailer!.
    match goal with Hx: Int64.eq _ _ = true |- _ =>
      apply Int64.same_if_eq in Hx; rewrite ts4_felse; auto; rep_lia end.
  - destruct R. apply andp_left2. apply derives_refl.
Qed.

End CM_TS4F1_1.
