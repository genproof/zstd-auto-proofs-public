(* FS3 streaming: case zdss_read, then case zdss_load (fall-through), with
   the exact claim (ExStream.st_read); the proof is read/R3VMain.v (the model side: read/R3X.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.read.R3VMain.
Local Open Scope logic.

Section CM_S3Seg_read_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma seg_read_x_ok : MF3 -> RET3x -> seg_case_x 3 -> seg_case_x 2.
Proof.
exact seg_read_gen.
Qed.

End CM_S3Seg_read_1.
