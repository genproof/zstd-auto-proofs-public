(* FS3-bl BODY: stage 7 (ZSTDds_skipFrame).  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s7.BL7Help.
Local Open Scope logic.

Section CM_BLStage7_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage7_ok : bl_case_spec (fun v => bv_stage v = BSkip) 7.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hbd Hfp Hs Hst Hpcs Hpcs' Hsz Hlay.
  unfold bl_case_pre, bl_cmd, bl_R, bl_post; simplify_func_tycontext; abbreviate_semax.
  simpl seq_of_labeled_statement.
  sep_apply (fcore3_split7 p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  forward. forward.
  forward.
  destruct (bl7_pure (dmode_of pr) od osz0 ba fs ts hb v W shk shd ob osz opos oc shs src c pcs)
    as (Hc7 & Hh7 & Hb7 & Hcl7); auto.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & _ & Hoc & _).
  Exists 0 oc (ba7 ba ob opos) (fs7 (bl_fs1 fs ob osz opos pcs (Zlength c))) (TInit (bd_oxo od) ts) hb.
  unfold tabs_rep.
  sep_apply (fcore3_join7' p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr Hpr).
  assert (Hfp7: fp_ok (fs_fParams (fs7 (bl_fs1 fs ob osz opos pcs (Zlength c))))).
  { unfold fs7, fsu_stage, fsu_expected; cbn [fs_fParams]. rewrite bl_fs1_fParams. exact Hfp. }
  entailer!.
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _).
  split; [exact Hhb |]. intros _. rewrite sublist_nil.
  split; [lia |]. split; [exists nil; split; [reflexivity | constructor] |].
  split; [reflexivity |]. split; [reflexivity |]. split; [exact Hh7 |].
  split; [intros b' Hb'; unfold ba7 in Hb'; cbn in Hb'; destruct (ba_st ba); inversion Hb'; reflexivity |].
  exists ts. split; [reflexivity | exact Hb7].
Qed.

End CM_BLStage7_1.
