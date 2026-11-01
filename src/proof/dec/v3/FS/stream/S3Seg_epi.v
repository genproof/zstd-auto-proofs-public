(* FS3 streaming: the epilogue of ZSTD_decompressStream. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.epi.E3Pure Zstd.proof.dec.v3.FS.stream.epi.E3Main.
Local Open Scope logic.

Section CM_S3Seg_epi_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the epilogue with the exact claim: from ex_call at the loop exit (the call's loop outcome LStop and zrel_end),
   the return value, positions, noForwardProgress and hostage byte are ExStreamFacts.z_epi's, so stream_exact holds
   and the next state carries the exact relation.  The proof is in src/proof/dec/v3/FS/stream/epi/: the VST walk
   in pieces (E3T*.v tail, E3H*.v head), the pure obligations (E3Pure.v), the model's side (E3X.v),
   seg_epilogue_x_all (E3Main.v). *)
Lemma seg_epilogue_x_ok : MF3 -> RET3x -> seg_epilogue_x.
Proof.
intros _ _. exact seg_epilogue_x_all.
Qed.

End CM_S3Seg_epi_1.
