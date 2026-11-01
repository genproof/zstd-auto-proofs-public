(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): after the content size check of the last
   block, `t'26 = checksumFlag; if (t'26) ts4_c1 else ts4_c0` then `return rSize`: the state after the load
   (ts4_m25) and the branch ts4_c1 (expected = 4; stage = 5: the checksum follows). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4Sep.
Local Open Scope logic.

Section CM_TS4C1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition ts4_c1 : statement :=
  ltac:(let s := eval cbv [ts4_ck] in ts4_ck in lazymatch s with Ssequence _ (Sifthenelse _ ?a _) => exact a end).
Definition ts4_c0 : statement :=
  ltac:(let s := eval cbv [ts4_ck] in ts4_ck in lazymatch s with Ssequence _ (Sifthenelse _ _ ?a) => exact a end).

Section M25.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the state after `t'26 = fParams.checksumFlag` *)
Definition ts4_m25 (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val)
    (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) : environ -> mpred :=
  PROPx nil
  (LOCALx (temp _t'26 (Vint (Int.repr (fh_checksumFlag (bv_h v)))) ::
           temp _t'16 (Vint (Int.repr (ts4_t15 (fh_contentSize (bv_h v)) (ds + r)))) ::
           temp _t'29 (Vlong (Int64.repr (fh_contentSize (bv_h v)))) ::
           temp _t'24 (Vint (Int.repr 4)) :: temp _rSize (Vlong (Int64.repr r)) ::
           lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp :: gvars gv ::
           temp _dctx p :: temp _dst (offset_val opos ob) :: temp _dstCapacity (Vlong (Int64.repr (osz - opos))) ::
           temp _src src :: temp _srcSize (Vlong (Int64.repr (Zlength c))) :: nil)
  (SEPx (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 4)) p ::
       field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 0)) p ::
       field_at Ews t_dctx (DOT _fParams) (fh_val (bv_h v)) p ::
       field_at Ews t_dctx (DOT _decodedSize) (Vlong (Int64.repr (ds + r))) p ::
       field_at Ews t_dctx (DOT _processedCSize) (Vlong (Int64.repr (pcs + Zlength c))) p ::
       ts4_rest p fsB pr ::
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp ::
       pws_pred W :: zstd_globals gv :: tabs_rep TABS gv p t' ::
       field_at Ews t_dctx (DOT _headerBuffer) hb p :: dent_of DENT gv (bd_oxo od) :: bd_res shk od ::
       data_at shd (tarray tuchar osz) oc' ob :: data_at shs (tarray tuchar (Zlength c)) (zbytes c) src :: nil))).

End M25.

Lemma ts4_c1_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba ba': blabs)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    (v_bp: val) (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) (Q: environ -> mpred),
  par_ok pr -> fs_fParams fsB = fh_val (bv_h v) -> fs_decodedSize fsB = vlong (ds + r) ->
  fs_processedCSize fsB = vlong (pcs + Zlength c) ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba' (t34_fsE fsB BCk 4) t' hb ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (ts4_m25 DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r v ds pcs fsB oc' t')
    (Ssequence ts4_c1 t34_ret)
    (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros W gv p pr od ba ba' hb shk shd ob osz opos oc shs src c v_bp r v ds pcs fsB oc' t' Q
    Hpr Bp Bd Bq HP.
  unfold ts4_m25, ts4_c1, t34_ret, t34_R, bl_R, bl_post. simplify_func_tycontext. abbreviate_semax.
  forward. forward. forward.
  sep_apply (ts4_fold p fsB pr BCk 4 _ _ _ Hpr (eq_sym Bp) (eq_sym Bd) (eq_sym Bq)).
  Exists r oc' ba' (t34_fsE fsB BCk 4) t' hb.
  destruct HP as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
  apply andp_right;
    [apply prop_right; exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P8 (conj P6 (conj P7 eq_refl))))))))
    | cancel].
Qed.

End CM_TS4C1_1.
