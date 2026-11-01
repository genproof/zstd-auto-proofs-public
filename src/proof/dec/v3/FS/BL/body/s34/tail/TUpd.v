(* FS3-bl BODY, stages 3/4, the tail: t34_dsz; t34_xx; t34_pe; t34_gp (VST): decodedSize += rSize,
   the checksum update, previousDstEnd = dst + rSize, gpDictCopy = 0. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpdD.
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpdX.
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpd2.
Local Open Scope logic.

Section CM_TUpd_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_upd_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (Q: environ -> mpred) (K: statement),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) oc' t') K (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsm fs ob osz opos pcs c e' cold) oc' t') (Ssequence t34_dsz (Ssequence t34_xx (Ssequence t34_pe (Ssequence t34_gp K)))) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    r oc' e' cold t' ds cnt ts' Q K HH Hmid Herr Hrb Hcnt Hds Hdsr Hk.
  pose proof HH as (Hpr & _).
  pose proof Hmid as (Hr & _).
  destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (_ & _ & Fd & _).
  apply (t34_upd_dsz_ok Espec DENT TABS SR BR' W gv p pr od hb shk shd ob osz opos shs src c v_bp r _ oc' t' ds _ _ Hpr
           ltac:(rewrite Fd; exact Hds)).
  apply (t34_upd_xx_ok Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs r oc' e' cold t' ds cnt ts' Q _ HH Hmid Herr Hrb Hcnt Hds Hdsr).
  apply (t34_upd2_ok Espec DENT TABS SR BR' W gv p pr od hb shk shd ob osz opos shs src c v_bp r _ oc' t' _ K Hpr Hr).
  rewrite <- t34_fsB_eq. exact Hk.
Qed.

End CM_TUpd_1.
