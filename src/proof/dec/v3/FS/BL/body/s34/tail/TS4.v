(* FS3-bl BODY, stages 3/4, the tail: t34_stg; t34_ret at the last block (stage 4, VST): the content
   size check (return -20), then checksumFlag ? (expected 4, stage 5) : (trace_end, expected 0, stage 0), return
   rSize; the posts are hypotheses (TPFcs.v, TPOk.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4Fcs.
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4C0.
Local Open Scope logic.

Section CM_TS4_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_s4_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (Q: environ -> mpred),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  e' = 0 -> bv_stage v = BLastBlk ->
  (~ t34_fcs_ok v ds r -> t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) t' hb) ->
  (t34_fcs_ok v ds r -> Forall (tc_val' tuchar) oc' ->
     exists ba', t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba' (t34_fsE (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) (fst (t34_next v 0)) (snd (t34_next v 0))) t' hb) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) oc' t') (Ssequence t34_stg t34_ret) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    r oc' e' cold t' ds cnt ts' Q HH Hmid Her Hrb Hcnt Hds Hdsr He' Hst Hbad Hgood.
  destruct HH as (Hpr & Hpre & Hci & Hmr & Hmd & _ & _ & Hpcs & Hpcsr & Hsz & Hlay).
  destruct Hci as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & _ & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs. rewrite Hst in Hcs. destruct Hcs as ((Hhok & Hfp & Hvc & Hxs) & _).
  destruct Hhok as (Hbsm & Hck & Hfcs & Hft).
  destruct Hmid as (Hr & Hoc' & _ & Hcold' & _).
  destruct (t34_fsm_fields fs ob osz opos pcs c e' cold)
    as (Fv & Fx & Fd & Fq & Fi & Fdi & Fc & Ff & Fe & Fs & Fb & Fr & Fh).
  set (fsm := t34_fsm fs ob osz opos pcs c e' cold) in *. clearbody fsm.
  set (fsB := t34_fsB fsm ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) ob opos) in *.
  assert (Bs: fs_stage fsB = Vint (Int.repr (bl_stz BLastBlk))) by (unfold fsB; cbn; rewrite Fs, Hstg, Hst; reflexivity).
  assert (Bp: fs_fParams fsB = fh_val (bv_h v)) by (unfold fsB; cbn; rewrite Ff; exact Hfp).
  assert (Bd: fs_decodedSize fsB = vlong (ds + r)) by reflexivity.
  assert (Bq: fs_processedCSize fsB = vlong (pcs + Zlength c)) by (unfold fsB; cbn; exact Fq).
  assert (Be: fs_expected fsB = vlong 0) by (unfold fsB; cbn; rewrite Fe, He'; reflexivity).
  assert (Bc: cold01 fsB) by (unfold cold01, fsB; cbn; rewrite Fc; exact Hcold').
  clearbody fsB.
  unfold t34_st, t34_stg. simplify_func_tycontext. abbreviate_semax.
  sep_apply (ts4_split p fsB pr). Intros.
  rewrite Bs, Be, Bd, Bq, Bp.
  forward.
  assert_PROP (Forall (tc_val' tuchar) oc') as Htc by entailer!.
  apply semax_if_seq. forward_if.
  2: { exfalso. match goal with Hx: 4 <> 4 |- _ => apply Hx; reflexivity end. }
  apply -> seq_assoc. ts4_dw. apply -> seq_assoc.
  (* the lemmas below are stated over func_tycontext: unifying it with the computed Delta is very slow, the
     conversion check of change is not *)
  change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil).
  eapply (ts4_fcs_ok Espec DENT TABS SR BR' W gv p pr od ba hb shk shd ob osz opos oc shs src c v_bp r v ds pcs fsB
            oc' t' Q); try eassumption.
  change (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) with Delta.
  unfold ts4_m15. Intros. match goal with Hx: t34_fcs_ok v ds r |- _ => rename Hx into HF end.
  destruct (Hgood HF Htc) as [ba' HP].
  unfold fh_val. forward.
  apply semax_if_seq. forward_if.
  - assert (Ef: fh_checksumFlag (bv_h v) = 1).
    { destruct Hck as [E | E]; auto. rewrite E in *. exfalso.
      match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
    replace (t34_next v 0) with (BCk, 4) in HP by (unfold t34_next; rewrite Hst, Ef; reflexivity).
    change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil).
    exact (ts4_c1_ok Espec DENT TABS SR BR' W gv p pr od ba ba' hb shk shd ob osz opos oc shs src c v_bp r v ds pcs
             fsB oc' t' Q Hpr Bp Bd Bq HP).
  - assert (Ef: fh_checksumFlag (bv_h v) = 0).
    { destruct Hck as [E | E]; auto. rewrite E in *. exfalso.
      match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    replace (t34_next v 0) with (BHdrPrefix, 0) in HP by (unfold t34_next; rewrite Hst, Ef; reflexivity).
    change Delta with (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil).
    exact (ts4_c0_ok Espec DENT TABS SR BR' W gv p pr od ba ba' hb shk shd ob osz opos oc shs src c v_bp r v ds pcs
             fsB oc' t' Q Hpr Bp Bd Bq HP).
Qed.

End CM_TS4_1.
