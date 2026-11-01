(* FS3 streaming: case zdss_load (template v2 StreamSeg_load.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3All.
Local Open Scope logic.

Section CM_S3Seg_load_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* case zdss_load with the exact claim (ExStream.st_load): load/L3VRest.v from the pure obligations, the model side in
   load/L3Ex.v *)
Lemma seg_load_x_ok : MF3 -> RET3x -> seg_case_x 3.
Proof.
exact seg_load_all.
Qed.

End CM_S3Seg_load_1.
