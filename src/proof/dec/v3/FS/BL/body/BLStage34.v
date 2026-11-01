(* FS3-bl BODY: stages 3/4 (ZSTDds_decompressBlock / decompressLastBlock): compressed, raw and RLE blocks, checksum update, content size check at the last block.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.Comp Zstd.proof.dec.v3.FS.BL.body.s34.Raw Zstd.proof.dec.v3.FS.BL.body.s34.Rle Zstd.proof.dec.v3.FS.BL.body.s34.Tail.
Local Open Scope logic.

Section CM_BLStage34_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage34_ok : bl_case_spec (fun v => bv_stage v = BBlk \/ bv_stage v = BLastBlk) 3.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfp Hst Est Hpcs Hpcsr Hsz Hlay.
  change (bl_cmd 3) with (Ssequence s34_s3f s34_rest).
  unfold s34_s3f.
  apply seq_assoc. apply seq_assoc.
  pose proof Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
  assert (Hcs' := Hcs). unfold bl_cstage in Hcs'.
  assert (Hbt: fs_bType fs = Vint (Int.repr (bv_bt v)) /\ 0 <= bv_bt v <= 2)
    by (destruct Hst as [E | E]; rewrite E in Hcs'; tauto).
  clear Hcs'. destruct Hbt as [Hbt Hbtr].
  unfold bl_case_pre, bl_R, bl_post. abbreviate_semax.
  dw0.
  sep_apply (fcore3_split p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  assert (Ebt1: fs_bType (bl_fs1 fs ob osz opos pcs (Zlength c)) = Vint (Int.repr (bv_bt v))).
  { unfold bl_fs1, fsu_processedCSize, continuity. destruct (cont_moves _ _ _); exact Hbt. }
  rewrite Ebt1. forward.
  rewrite <- Ebt1.
  sep_apply (fcore3_join p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr Hpr).
  rewrite Ebt1.
  eapply semax_seq.
  2: { apply (@s34_tail_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st Hpr Hpre Hci Hmr Hmd Hfp Hst Est Hpcs Hpcsr Hsz Hlay). }
  apply semax_switch_PQR with (n := bv_bt v); [reflexivity | entailer! | entailer! |].
  rewrite Int.unsigned_repr by rep_lia.
  apply semax_pre with
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp st).
  { unfold bl_case_pre. entailer!. }
  assert (Hb3: bv_bt v = 0 \/ bv_bt v = 1 \/ bv_bt v = 2) by lia.
  destruct Hb3 as [E | [E | E]]; rewrite E.
  - apply (@s34_raw_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st Hpr Hpre Hci Hmr Hmd Hfp Hst Est Hpcs Hpcsr Hsz Hlay E).
  - apply (@s34_rle_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st Hpr Hpre Hci Hmr Hmd Hfp Hst Est Hpcs Hpcsr Hsz Hlay E).
  - apply (@s34_comp_ok CMI Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st Hpr Hpre Hci Hmr Hmd Hfp Hst Est Hpcs Hpcsr Hsz Hlay E).
Qed.

End CM_BLStage34_1.
