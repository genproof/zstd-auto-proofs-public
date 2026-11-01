(* The bodies of vp_windows_within and vp_blocks_within (harness/valid_params.c: read the static sr) against their
   specifications in the v3 template WTopSpecs; their proofs are in WB3_within_vp.v. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_params.WB_new3_valid_params.
Require Zstd.proof.harness.writer.WB3_within_vp.

Theorem wb3_within :
  Zstd.proof.harness.valid_params.WSpecs_valid_params.body_vp_windows_within /\
  Zstd.proof.harness.valid_params.WSpecs_valid_params.body_vp_blocks_within.
Proof.
  split.
  - exact Zstd.proof.harness.writer.WB3_within_vp.wb_vp_windows_within.
  - exact Zstd.proof.harness.writer.WB3_within_vp.wb_vp_blocks_within.
Qed.
