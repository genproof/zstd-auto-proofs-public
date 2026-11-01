(* Subtree B of the decoder, API v3.  Prove B3_obligation (DecSubtrees3.v).
   v3.4 and the revised usingDict specification: B/BAsm34.v (insertDictionary's error branch keeps fParams; B's files on
   DecLiftP34). *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Import Zstd.proof.dec.v3.B.BAsm34.

Lemma B3_ok : B3_obligation.
Proof.
  exact B3_ok_api34.
Qed.
