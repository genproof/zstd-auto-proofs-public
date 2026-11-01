(* FS3-bl BODY stage 1: after ZSTD_decodeFrameHeader succeeded: expected = ZSTD_blockHeaderSize;
   stage = ZSTDds_decodeBlockHeader; return 0. *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s1.S1Defs.
Local Open Scope logic.

Section CM_S1Tail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s1_tail_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z),
  s1_hyps pr W od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (s1_Q DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (pcs + Zlength c) (bv_hdr v ++ c) ts
       (s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)) shk shd ob osz oc shs src c v_bp)
    (Ssequence s1_rest s1_more)
    (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    Hh.
  destruct Hh as (Hpr & Hpre & Hci0 & Hmr & Hmd & Hst & Hpcs & Hpcsr & Hsz & Hlay & Hfp).
  assert (Hnsk: md_magicless (dmode_of pr) = false -> is_skippable_magic (le_field (bv_hdr v) 0 4) = false).
  { destruct Hci0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
    cbv [bl_cstage] in Hcs; rewrite Hst in Hcs. destruct Hcs as (_ & _ & _ & _ & _ & _ & Hk). exact Hk. }
  assert (Hout: forall b, ba_st ba = Some b -> bs_out b = nil).
  { intros b B. destruct (Hmr b B) as (_ & _ & _ & _ & _ & Hm). rewrite Hst in Hm. exact (proj2 Hm). }
  destruct Hpre as (Hne & Hho & Hoz & Hbo & Hbs & Hbd & Hwd & Hrs & Hrk & Hop & Hosz & Hoc & Hcl & Hcb).
  unfold bl_size_ok in Hsz; rewrite Hst in Hsz.
  unfold s1_Q, bl_R, bl_post. s1_delta. unfold s1_rest, s1_more. abbreviate_semax.
  Intros r fs' d'.
  set (hb' := s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)).
  sep_apply (s1_fcore3_split p fs' pr). Intros.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (dent_of DENT gv (bd_oxo od)) (bd_res shk od)
    (data_at shd _ _ ob) (data_at shs _ _ src) (data_at Ews (tarray tuchar 18) _ _).
  unfold zstd_globals. Intros.
  forward.
  sep_apply (s1_globals_fold gv).
  forward. forward.
  sep_apply (s1_fcore3_join2 p fs' pr Hpr).
  thaw FR.
  forward.
  destruct (s1_ok_pure (dmode_of pr) od osz0 ba fs ts hb v c ob (Zlength oc) opos oc pcs df_none nil nil r fs' d'
              Hho ltac:(lia) eq_refl Hci0 Hmr Hmd Hst Hcb Hsz Hlay Hnsk Hout H H0)
    as (Hr0 & Hc2 & Hhb2 & Hfp2 & Hh2 & Hbe2 & Hbr2 & Hcl2).
  subst r.
  Exists 0 oc (s1_ba ba c (s1_h (md_magicless (dmode_of pr)) (bv_hdr v ++ c)) ob opos) (s1_fs2 fs')
    (TInit (bd_oxo od) ts) hb'.
  unfold tabs_rep. rewrite s1_hb_eq.
  entailer!.
  split; [lia |]. split; [rewrite sublist_nil; exists nil; split; [reflexivity | constructor] |].
  split; [reflexivity |]. split; [reflexivity |]. split; [exact Hh2 |]. split; [exact Hbe2 |].
  exists ts. split; [reflexivity | exact Hbr2].
Qed.

End CM_S1Tail_1.
