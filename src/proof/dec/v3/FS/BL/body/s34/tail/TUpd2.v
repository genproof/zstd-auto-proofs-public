(* FS3-bl BODY, stages 3/4, the tail (split for the check time): t34_pe; t34_gp (VST):
   previousDstEnd = dst + rSize, gpDictCopy = 0. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpdSep.
Local Open Scope logic.

Section CM_TUpd2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_upd2_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (hb: list val) (shk shd: share)
    (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val) (r: Z) (fsx: fstate) (oc': list val)
    (t': tabs3) (R: ret_assert) (K: statement),
  par_ok pr -> 0 <= r <= Int64.max_unsigned ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fs2 fsx (offset_val (opos + r) ob)) oc' t') K R ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r fsx oc' t') (Ssequence t34_pe (Ssequence t34_gp K)) R.
Proof.
  intros Espec DENT TABS SR BR' W gv p pr od hb shk shd ob osz opos shs src c v_bp r fsx oc' t' R K Hpr Hr Hk.
  unfold t34_st in Hk |- *. unfold t34_pe, t34_gp.
  assert_PROP (field_compatible (tarray tuchar osz) [] ob) as Fob by entailer!.
  assert (Pob: isptr ob) by (destruct Fob; auto).
  sep_apply (tu_split p fsx pr). Intros.
  simplify_func_tycontext.
  abbreviate_semax.
  assert (Eprev: force_val (sem_add_ptr_long tschar (offset_val opos ob) (Vlong (Int64.repr r)))
                 = offset_val (opos + r) ob).
  { destruct ob; try contradiction. simpl. unfold sem_add_ptr_long. simpl. f_equal. rewrite Ptrofs.add_assoc. f_equal.
    change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia. apply ptrofs_add_repr. }
  forward.
  rewrite Eprev. forward.
  sep_apply (tu_join2 p fsx pr (offset_val (opos + r) ob) Hpr).
  eapply semax_pre; [| exact Hk].
  entailer!.
Qed.

End CM_TUpd2_1.
