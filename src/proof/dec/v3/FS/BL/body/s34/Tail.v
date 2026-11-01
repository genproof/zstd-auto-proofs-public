(* FS3-bl BODY, stages 3/4: the tail (after the block-type switch) part (S34Defs.v).
   Assembly of the parts in s34/tail/ (TDefs.v): the VST parts TChk, TUpd, TEx, TS4/TS3 take the posts
   of their returns as hypotheses, given here by the pure parts TPErr, TPFcs, TPOk. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TPErr.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TPFcs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TPOk.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TChk.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpd.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TEx.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS4.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.tail.TS3.
Local Open Scope logic.

Section CM_Tail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s34_tail_ok : s34_tail_spec.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfpo Hst Hstz Hpcs Hpcsr Hsz Hlay.
  assert (HH: t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs)
    by exact (conj Hpr (conj Hpre (conj Hci (conj Hmr (conj Hmd (conj Hfpo (conj Hst (conj Hpcs (conj Hpcsr
                (conj Hsz Hlay)))))))))).
  pose proof Hci as (_ & _ & Hstg & _ & _ & _ & _ & (ds & Hds & Hdsr) & _).
  unfold s34_mid. Intros r oc' e' cold t'.
  match goal with Hm: s34_mid_ok _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hm into Hmid end.
  apply semax_seq with (Q := PROP (False) LOCAL () SEP ()).
  2: { Intros. contradiction. }
  rewrite t34_t_eq.
  apply (@t34_chk_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs r oc' e' cold t' _ _ HH Hmid).
  { exact (t34_err_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' e' cold t' HH Hmid). }
  { exact (t34_bsm_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' e' cold t' HH Hmid). }
  intros Ner Hbsm.
  pose proof Hmid as (_ & _ & _ & _ & _ & Hsucc).
  destruct (Hsucc Ner) as (_ & _ & _ & cnt & ts' & Hcnt).
  assert (HC: t34_cnt od ba c opos oc' r t' cnt ts') by exact Hcnt.
  apply (@t34_upd_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs r oc' e' cold t' ds cnt ts' _ _ HH Hmid Ner Hbsm HC Hds Hdsr).
  apply (@t34_ex_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
           v pcs r oc' e' cold t' ds cnt ts' _ _ HH Hmid Ner Hbsm HC Hds Hdsr).
  { intros He0 Hfit.
    destruct (t34_ok_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' e' cold t' ds cnt ts'
                HH Hmid Ner Hbsm HC Hds Hdsr ltac:(intros _ E; lia) Hfit) as [ba' Hpp].
    exists ba'.
    assert (En: t34_next v e' = (bv_stage v, e'))
      by (unfold t34_next; rewrite (proj2 (Z.ltb_lt _ _) He0); reflexivity).
    rewrite En in Hpp. cbn [fst snd] in Hpp.
    destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (_ & _ & _ & _ & _ & _ & _ & _ & Fe & Fs & _).
    rewrite t34_fsE_same in Hpp; [exact Hpp | exact Fe | exact (eq_trans Fs Hstg)]. }
  intros He0. subst e'.
  destruct Hst as [Hb | Hl].
  - apply (@t34_s3_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
             v pcs r oc' 0 cold t' ds cnt ts' _ HH Hmid Ner Hbsm HC Hds Hdsr eq_refl Hb).
    intros Hfit.
    exact (t34_ok_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' 0 cold t' ds cnt ts'
             HH Hmid Ner Hbsm HC Hds Hdsr ltac:(intros E; rewrite Hb in E; discriminate) Hfit).
  - apply (@t34_s4_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp
             v pcs r oc' 0 cold t' ds cnt ts' _ HH Hmid Ner Hbsm HC Hds Hdsr eq_refl Hl).
    + intros Hn.
      exact (t34_fcs_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' 0 cold t' ds cnt ts' _
               HH Hmid Ner Hbsm HC Hds Hdsr eq_refl Hl Hn).
    + intros Hf Hfit.
      exact (t34_ok_pp W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs r oc' 0 cold t' ds cnt ts'
               HH Hmid Ner Hbsm HC Hds Hdsr (fun _ _ => Hf) Hfit).
Qed.

End CM_Tail_1.
