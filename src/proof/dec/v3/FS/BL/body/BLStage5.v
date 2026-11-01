(* FS3-bl BODY: stage 5 (ZSTDds_checkChecksum): XXH64_digest against the 4 bytes.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s5.BL5Tail.
Require Import Zstd.proof.dec.v3.FS.BL.body.s5.BL5Then.
Local Open Scope logic.

Section CM_BLStage5_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage5_ok : bl_case_spec (fun v => bv_stage v = BCk) 5.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfpo Hst Hstz Hpcs Hpcsr Hsz Hlay.
  subst st. rewrite Hst. cbn [bl_stz].
  rewrite bl5_cmd_eq. apply -> seq_assoc.
  eapply semax_seq;
    [| exact (@bl5_tail_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
                v_bp v pcs Hpr Hpre Hci Hmr Hmd Hfpo Hst Hpcs Hpcsr Hlay)].
  unfold bl_case_pre, bl5_if, bl_R, bl_post; simplify_func_tycontext; abbreviate_semax.
  pose proof Hsz as Hsz0.
  pose proof Hci as Hci'.
  destruct Hci' as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs. rewrite Hst in Hcs. destruct Hcs as ((Hhok & Hfp & Hvc & Hxs) & Hck & He4).
  unfold bl_size_ok in Hsz. rewrite Hst, He4 in Hsz.
  pose proof Hpre as Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & Hbs & _ & _ & Hrs & _ & Hop & Hosz & Hoc & _ & Hbc).
  destruct (bl5_fs1 fs ob osz opos pcs (Zlength c)) as (Fv & Fx & Fd & Fp & Fi & Fdi & Fc & Ff).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  assert (Hc1: cold01 fs1) by (unfold cold01; rewrite Fc; exact Hcold).
  sep_apply (bl5_split p fs1 pr). Intros.
  rewrite Fv, Hvc.
  freeze [6; 7; 8; 9; 10; 11; 12; 13; 14] FR.
  forward.
  remember (bl_val (md_ignore (dmode_of pr)) (bv_h v)) as bv eqn:Ebv.
  forward_if.
  { destruct bv.
    2: { exfalso. match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
    thaw FR.
    eapply semax_pre;
      [| exact (@bl5_then_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src
                  c v_bp v pcs Hpr Hpre Hci Hmr Hfpo Hst (eq_sym Ebv) Hsz0)].
    unfold bl5_pth. change (bl_fs1 fs ob osz opos pcs (Zlength c)) with fs1.
    entailer!. }
  { destruct bv.
    { exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
    forward. thaw FR.
    unfold bl5_mid. change (bl_fs1 fs ob osz opos pcs (Zlength c)) with fs1. rewrite <- Ebv.
    entailer!. }
Qed.

End CM_BLStage5_1.
