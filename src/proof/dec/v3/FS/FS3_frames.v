(* FS3: one-shot frames: ZSTD_decompressFrame's specification and ZSTD_decompressMultiFrame. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frame3_loop Zstd.proof.dec.v3.FS.frames.Frame3_B1 Zstd.proof.dec.v3.FS.frames.Frame3_raw Zstd.proof.dec.v3.FS.frames.Frame3_rle Zstd.proof.dec.v3.FS.frames.Frame3_cmp Zstd.proof.dec.v3.FS.frames.Frame3_B2 Zstd.proof.dec.v3.FS.frames.Frame3_B3 Zstd.proof.dec.v3.FS.frames.Frame3_end Zstd.proof.dec.v3.FS.frames.Frame3_main Zstd.proof.dec.v3.FS.frames.Multi3_body.
Local Open Scope logic.

Section CM_FS3_frames_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma FRAMES3_ok : FRAMES3_obligation.
Proof.
  intros DENT TABS HD HT.
  exists (snd (ZSTD_decompressFrame_spec3 DENT TABS)); intros SR BR.
  split.
  - apply (@body_decompressFrame3 CMI DENT TABS SR BR HD HT).
    intros W gv p fs ox dm e osh obase oN oc od ocap ish ibase iN ic ioff s sp ssp v_bp pr dsp d l tbl xq lent am hb
      h hs fdid d1 ts0.
    split.
    + apply (@fr_loop_ok3 CMI); auto.
      * apply (@fr_B1_ok3 CMI); auto.
      * apply (@fr_B2_ok3 CMI); auto; [apply (@fr_raw_ok3 CMI) | apply (@fr_rle_ok3 CMI) | apply (@fr_cmp_ok3 CMI)]; auto.
      * apply (@fr_B3_ok3 CMI); auto.
    + apply (@fr_end_ok3 CMI); auto.
  - exact (@body_decompressMultiFrame3 CMI DENT TABS SR BR HD HT).
Qed.

End CM_FS3_frames_1.
