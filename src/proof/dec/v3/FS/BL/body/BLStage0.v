(* FS3-bl BODY: stage 0 (ZSTDds_getFrameHeaderSize): skippable magic test, ZSTD_frameHeaderSize_internal, headerBuffer.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s0.S0SkipA.
Require Import Zstd.proof.dec.v3.FS.BL.body.s0.S0HdrA.
Local Open Scope logic.

Section CM_BLStage0_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the pieces: s0/S0SkipA (zstd1: the skippable magic test), s0/S0SkipB (a skippable frame), s0/S0HdrA
   (ZSTD_frameHeaderSize_internal), s0/S0HdrB (a Zstandard frame); the model step in s0/S0Pure *)
Lemma bl_stage0_ok : bl_case_spec (fun v => bv_stage v = BHdrPrefix) 0.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfp Hst Hstz Hpcs Hpcsr Hsz Hlay.
  pose proof Hci as Hci0.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs.
  destruct Hpre as (Hne & Hho & Hoz & Hbo & Hbs & Hbd & Hwd & Hrs & Hrk & Hop & Hosz & Hoc & Hcl & Hcb).
  assert (Hn: Zlength c = starting_len (md_magicless (dmode_of pr))).
  { unfold bl_size_ok in Hsz; rewrite Hst in Hsz. destruct Hcs; lia. }
  assert (Hok: s0_ok pr od osz0 ba fs ts hb v ob osz opos oc shs c)
    by (unfold s0_ok; repeat match goal with |- _ /\ _ => split end; auto; lia).
  assert (Hfmt: dp_fmt pr = 0 \/ dp_fmt pr = 1) by (destruct Hpr; tauto).
  unfold bl_case_pre, bl_cmd. change (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    with (s0_D DENT TABS SR BR').
  change (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))
    with (s0_RA DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).
  change (seq_of_labeled_statement (select_switch 0 _)) with s0_full.
  unfold s0_full. fold s0_A. fold s0_REST.
  sep_apply (s0_fcore3_split p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  assert_PROP (isptr src) as Hsrc by entailer!.
  apply -> seq_assoc.
  apply semax_seq with (Q := s0_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st).
  2:{ exact (@s0_hdrA_ok CMI Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v
               pcs st _ Hok Hsrc). }
  unfold s0_D, s0_A, s0_RA, s0_mid, bl_R, bl_post. s0_simplify. abbreviate_semax.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((dp_fmt pr = 0 -> is_skippable_magic (le_field c 0 4) = false) :: P) (LOCALx Q (SEPx R))) end.
  - assert (Hf0: dp_fmt pr = 0) by (destruct Hfmt as [E|E]; rewrite E in *; [auto | discriminate]).
    unfold POSTCONDITION, abbreviate.
    exact (@s0_skipA_ok CMI Espec DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v
             pcs st Hok Hsrc Hf0).
  - forward. entailer!.
Qed.

End CM_BLStage0_1.
