(* FS3 streaming, case zdss_load: an error of the call (P_load_err_why, statement in L3Stmts). *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3ErMain.
Local Open Scope logic.

Section CM_L3ErrWhy_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_err_why_ok : P_load_err_why.
Proof.
exact load_err_why3.
Qed.

End CM_L3ErrWhy_1.
