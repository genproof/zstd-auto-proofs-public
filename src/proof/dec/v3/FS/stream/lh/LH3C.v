(* FS3 streaming, case zdss_loadHeader: piece C (s7..s13: stable check, Begin_usingDDict(getDDict), skippable / decodeFrameHeader, window). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib Zstd.proof.dec.v3.FS.stream.lh.LH3C_s7 Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s9 Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10 Zstd.proof.dec.v3.FS.stream.lh.LH3C_s12 Zstd.proof.dec.v3.FS.stream.lh.LH3C_s13.
Local Open Scope logic.

Section CM_LH3C_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the segments compose (LH3C_lib.lhC_compose); each segment is proved in its file LH3C_s<n>.v; the normal exit
   keeps litExtraBuffer (LH3C_lib.lhC_post_l) *)
Lemma lhC_l_ok : lhC_l_stmt.
Proof.
exact (lhC_compose lhC_seg7_ok lhC_seg9_ok lhC_seg10_ok lhC_seg12_ok lhC_seg13_ok).
Qed.

End CM_LH3C_1.
