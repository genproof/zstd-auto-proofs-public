(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: piece D (the buffer sizes, oversizedDuration, the (re)allocation) as the model sizes the buffers (LH3XDefs.lhD_x).  The proof is LH3D.lhD_x_okp. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3D.
Local Open Scope logic.

Section CM_LH3DX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma lhD_x_ok : lhD_x_stmt.
Proof. exact Zstd.proof.dec.v3.FS.stream.lh.LH3D.lhD_x_okp. Qed.

End CM_LH3DX_1.
