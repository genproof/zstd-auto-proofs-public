(* Subtree FS of the decoder, API v3.  Prove FS3_obligation (DecSubtrees3.v). *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Import Zstd.proof.dec.v3.FS.FSAsm3.

(* the assembly is FSAsm3.FS3_assemble *)
Lemma FS3_ok : FS3_obligation.
Proof.
  exact FS3_assemble.
Qed.
