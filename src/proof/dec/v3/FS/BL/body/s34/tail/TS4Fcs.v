(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): the last block's content size check
   (for (;;break) { ts4_s1; ts4_s2 }: return -20 when fcs != UNKNOWN && decodedSize != fcs), CPS: the
   continuation K runs from ts4_m15 knowing t34_fcs_ok. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4F1.
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4F2.
Local Open Scope logic.

Section CM_TS4Fcs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ts4_fcs_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    (v_bp: val) (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) (Q: environ -> mpred)
    (K: statement),
  par_ok pr -> fs_fParams fsB = fh_val (bv_h v) -> fs_decodedSize fsB = vlong (ds + r) ->
  fs_processedCSize fsB = vlong (pcs + Zlength c) -> fs_expected fsB = vlong 0 ->
  fs_stage fsB = Vint (Int.repr (bl_stz BLastBlk)) ->
  0 <= fh_contentSize (bv_h v) <= Int64.max_unsigned ->
  (~ t34_fcs_ok v ds r -> t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba fsB t' hb) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_m15 DENT TABS (t34_fcs_ok v ds r :: nil) W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs
       fsB oc' t')
    K (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_mid DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t')
    (Ssequence ts4_loop K)
    (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros W gv p pr od ba hb shk shd ob osz opos oc shs src c v_bp r v ds pcs fsB oc' t' Q K
    Hpr Bp Bd Bq Be Bs Hfcs Hbad HK.
  apply semax_seq with
    (Q := ts4_m15 DENT TABS (t34_fcs_ok v ds r :: nil) W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs
            fsB oc' t'); [| exact HK].
  rewrite ts4_loop_eq.
  apply semax_loop with
    (Q' := ts4_m15 DENT TABS (t34_fcs_ok v ds r :: nil) W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs
             fsB oc' t').
  - apply semax_seq with
      (Q := ts4_m15 DENT TABS nil W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t').
    + apply ts4_s1_ok; exact Hfcs.
    + apply ts4_s2_ok; assumption.
  - eapply semax_pre; [| apply semax_break].
    destruct (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
    simpl. intros rho. apply andp_left2, derives_refl.
Qed.

End CM_TS4Fcs_1.
