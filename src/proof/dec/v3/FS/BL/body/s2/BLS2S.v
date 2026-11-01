(* FS3-bl BODY stage 2: the stores of a block header (expected, bType, rleSize). *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Local Open Scope logic.

Section CM_BLS2S_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl2_y_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    W gv p pr od fs1 h ts hb shk shd ob osz opos oc shs src c v_bp cs R :
  par_ok pr -> fs_fParams fs1 = fh_val h -> bytes_ok c ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid3 DENT TABS W gv p pr od fs1 h ts hb shk shd ob osz opos oc shs src c v_bp cs) bl2_w R ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl2_mid DENT TABS W gv p pr od fs1 ts hb shk shd ob osz opos oc shs src c v_bp cs) bl2_y R.
Proof.
  intros Hpr Hfp Hbc H.
  unfold bl2_mid. bl2_delta. unfold bl2_y. abbreviate_semax.
  sep_apply (fcore3_split2 p fs1 pr _ Hfp). Intros.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob) (data_at shs _ _ src)
    (fc2_rest p _ pr) (zstd_globals gv) (field_at Ews t_dctx (DOT _fParams) _ p).
  unfold bp_val.
  forward. forward. forward. forward. forward.
  thaw FR.
  assert (Hor: 0 <= Z.shiftr (le_field c 0 3) 3 < 2 ^ 21) by exact (bp_orig_range c Hbc).
  rewrite (Int.unsigned_repr (Z.shiftr (le_field c 0 3) 3)) by rep_lia.
  eapply semax_pre; [| exact H].
  unfold bl2_mid3. entailer!.
Qed.

End CM_BLS2S_1.
