(* FS3-bl BODY, stages 3/4, the tail (split for the check time): t34_dsz (VST): decodedSize += rSize. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpdSep.
Local Open Scope logic.

Section CM_TUpdD_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_upd_dsz_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (hb: list val) (shk shd: share)
    (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val) (r: Z) (fsx: fstate) (oc': list val)
    (t': tabs3) (ds: Z) (R: ret_assert) (K: statement),
  par_ok pr -> fs_decodedSize fsx = vlong ds ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (fsu_decodedSize fsx (vlong (ds + r))) oc' t') K R ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r fsx oc' t') (Ssequence t34_dsz K) R.
Proof.
  intros Espec DENT TABS SR BR' W gv p pr od hb shk shd ob osz opos shs src c v_bp r fsx oc' t' ds R K Hpr Hds Hk.
  unfold t34_st in Hk |- *. unfold t34_dsz.
  sep_apply (tu_split p fsx pr). Intros.
  simplify_func_tycontext.
  abbreviate_semax.
  rewrite Hds. unfold vlong.
  forward. forward.
  rewrite add64_repr.
  sep_apply (tu_join_ds p fsx pr (vlong (ds + r)) Hpr).
  eapply semax_pre; [| exact Hk].
  entailer!.
Qed.

End CM_TUpdD_1.
