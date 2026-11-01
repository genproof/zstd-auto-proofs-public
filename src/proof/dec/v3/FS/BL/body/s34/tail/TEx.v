(* FS3-bl BODY, stages 3/4, the tail: t34_ex (VST): if (expected > 0) return rSize (a raw block fed
   in part); the post of the return is a hypothesis (from TPOk.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Local Open Scope logic.

Section CM_TEx_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_ex_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (Q: environ -> mpred) (K: statement),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  (0 < e' -> Forall (tc_val' tuchar) oc' -> exists ba', t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba' (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) t' hb) ->
  (e' = 0 -> semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) oc' t') K (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) oc' t') (Ssequence t34_ex K) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs r oc'
    e' cold t' ds cnt ts' Q K HH Hmid Herr Hbsm Hcnt Hds Hdsr Hret Hcont.
  unfold t34_st, t34_R, bl_R, bl_post, t34_ex.
  simplify_func_tycontext; abbreviate_semax.
  destruct Hmid as (Hr & Hloc & Hpre0 & Hcold & _ & Hok). destruct (Hok Herr) as (Hro & He' & Hbt0 & _).
  destruct HH as (Hpr & Hpre & Hci & Hmr & Hmd & Hfpo & Hstg & Hpcs & Hpcsr & Hsz & Hlay).
  assert (He'r: 0 <= e' < 2 ^ 32).
  { destruct Hci as (_ & Hexr & _). unfold bl_size_ok in Hsz. rewrite He'. destruct (bv_bt v =? 0) eqn:Ebt.
    - pose proof Ebt as Ebt'. apply Z.eqb_eq in Ebt'. specialize (Hbt0 Ebt').
      destruct Hstg as [Hs|Hs]; rewrite Hs in Hsz; lia.
    - lia. }
  clear He' Hok Hbt0.
  set (fsB := t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos)
    in *.
  assert (Hex: fs_expected fsB = vlong e').
  { unfold fsB, t34_fsB. destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (_ & _ & _ & _ & _ & _ & _ & _ & Hx & _).
    rewrite <- Hx. reflexivity. }
  assert_PROP (Forall (tc_val' tuchar) oc') as Htc by entailer!.
  sep_apply (fcore3_split p fsB pr). Intros.
  rewrite Hex. unfold vlong.
  forward.
  forward_if.
  - rewrite Int64.unsigned_repr in H by rep_lia. rewrite Int64.unsigned_repr in H by rep_lia.
    destruct (Hret ltac:(lia) Htc) as (ba' & Hpp).
    forward.
    Exists r oc' ba' fsB t' hb.
    replace (Vlong (Int64.repr e')) with (fs_expected fsB) by (rewrite Hex; reflexivity).
    sep_apply (fcore3_join p fsB pr Hpr).
    destruct Hpp as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
    entailer!.
  - rewrite Int64.unsigned_repr in H by rep_lia. rewrite Int64.unsigned_repr in H by rep_lia.
    eapply semax_pre; [| apply Hcont; lia].
    unfold t34_st.
    replace (Vlong (Int64.repr e')) with (fs_expected fsB) by (rewrite Hex; reflexivity).
    sep_apply (fcore3_join p fsB pr Hpr).
    entailer!.
Qed.

End CM_TEx_1.
