(* FS3 streaming: case zdss_loadHeader of ZSTD_decompressStream with the exact claim (model/ExStream.v's
   st_load_header and st_header_done: the header load, the hint, the single-pass shortcut, the frame's beginning, the
   buffers), then case zdss_read.  The pieces and the glue are in stream/lh/: the statements in LH3XDefs.v, the
   assembly in LH3MainX.v (the relational pieces of LH3Stmts.v are their template). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs Zstd.proof.dec.v3.FS.stream.lh.LH3MainX.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Gfh Zstd.proof.dec.v3.FS.stream.lh.LH3Lend Zstd.proof.dec.v3.FS.stream.lh.LH3G4.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3AX Zstd.proof.dec.v3.FS.stream.lh.LH3BX Zstd.proof.dec.v3.FS.stream.lh.LH3CX Zstd.proof.dec.v3.FS.stream.lh.LH3DX.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3G1X Zstd.proof.dec.v3.FS.stream.lh.LH3G2X Zstd.proof.dec.v3.FS.stream.lh.LH3G4X.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3RetX Zstd.proof.dec.v3.FS.stream.lh.LH3HintX Zstd.proof.dec.v3.FS.stream.lh.LH3XShort.
Require Import Zstd.proof.dec.v3.FS.set.SetProbe.
Local Open Scope logic.

Section CM_S3Seg_lh_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* case zdss_loadHeader with the exact claim, then case zdss_read; the set's probe fact by SetProbe.sp_probe_ok *)
Lemma seg_lh_x_ok : MF3 -> RET3x -> seg_case_x 2 -> seg_case_x 1.
Proof.
destruct lend_ok as (Lsel & Luse & Lbeg).
exact (seg_lh_x_pieces lhA_x_ok lhB_x_ok lhC_x_ok lhD_x_ok gfh3_ok Lsel Luse Lbeg sp_probe_ok lh_short_model_ok
         lh_brkA_x_ok lh_brkB_x_ok lh_read_ok lh_read_x_ok lh_ret_x_ok lh_hint_x_ok).
Qed.

End CM_S3Seg_lh_1.
