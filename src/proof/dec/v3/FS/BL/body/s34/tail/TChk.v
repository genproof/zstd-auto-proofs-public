(* FS3-bl BODY, stages 3/4, the tail: t34_chk; t34_bsm; t34_dw (VST): FORWARD_IF_ERROR(rSize) and
   rSize > fParams.blockSizeMax -> return -20; the posts of the two returns are hypotheses (TPErr.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TChkSep.
Local Open Scope logic.

Section CM_TChk_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_chk_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (Q: environ -> mpred) (K: statement),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  (is_error_code r = true -> t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba (t34_fsm fs ob osz opos pcs c e' cold) t' hb) ->
  (is_error_code r = false -> fh_blockSizeMax (bv_h v) < r -> t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba (t34_fsm fs ob osz opos pcs c e' cold) t' hb) ->
  (is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) ->
     semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsm fs ob osz opos pcs c e' cold) oc' t') K (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsm fs ob osz opos pcs c e' cold) oc' t') (Ssequence t34_chk (Ssequence t34_bsm (Ssequence t34_dw K))) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs r
    oc' e' cold t' Q K HH Hmid Herr Hbig HK.
  destruct HH as (Hpr & Hpre & Hci & Hmr & Hbd & Hfpo & Hstg & Hpcs & Hpcsr & Hsz & Hlay).
  assert (Hhf: hdr_fields (md_ignore (dmode_of pr)) v fs).
  { destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
    destruct Hstg as [E | E]; cbv [bl_cstage] in Hcs; rewrite E in Hcs; exact (proj1 Hcs). }
  destruct Hhf as ((Hbm & _) & Hfp & _).
  destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (_ & _ & _ & _ & _ & _ & _ & Ffp & _).
  set (fsx := t34_fsm fs ob osz opos pcs c e' cold) in *.
  pose proof Hmid as (Hr & _).
  unfold t34_st, t34_R, bl_R, bl_post, t34_chk, t34_bsm, t34_dw. simplify_func_tycontext. abbreviate_semax.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((is_error_code r = false) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_call r. forward_if.
    - tchk_dw. tchk_dw. tchk_dw. tchk_dw.
      assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
      destruct (Herr Er) as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
      forward.
      Exists r oc' ba fsx t' hb.
      entailer!.
    - forward. entailer!. destruct (is_error_code r); auto.
      exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
  Intros. rename H into Ner.
  assert (Hfx: fs_fParams fsx = fh_val (bv_h v)) by (rewrite Ffp; exact Hfp).
  unfold ZSTD_BLOCKSIZE_MAX in Hbm.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((r <= fh_blockSizeMax (bv_h v)) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { sep_apply (tchk_split p fsx pr). Intros. rewrite Hfx. unfold fh_val.
    forward.
    fold (fh_val (bv_h v)). rewrite <- Hfx. sep_apply (tchk_join p fsx pr Hpr).
    forward_if.
    - tchk_dw. tchk_dw. tchk_dw. tchk_dw.
      match goal with Hx: Int.unsigned (Int.repr (fh_blockSizeMax _)) < _ |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      destruct (Hbig Ner ltac:(lia)) as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
      forward. Exists (2 ^ 64 - 20) oc' ba fsx t' hb. entailer!.
      exact tchk_m20.
    - forward. entailer!.
      match goal with Hx: Int.unsigned (Int.repr (fh_blockSizeMax _)) >= _ |- _ =>
        rewrite Int.unsigned_repr in Hx by rep_lia end.
      lia. }
  Intros. rename H into Hrb.
  tchk_dw.
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION Delta.
  unfold abbreviate.
  eapply semax_pre; [| apply (HK Ner Hrb)].
  unfold t34_st. entailer!.
Qed.

End CM_TChk_1.
