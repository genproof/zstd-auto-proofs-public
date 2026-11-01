(* The writer-internals body group `block`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_block_<u>.v (template WB_block); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_block_detect.
Require Zstd.proof.harness.stable_out.WB_block_stable_out.
Require Zstd.proof.harness.valid_dict.WB_block_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_block_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_block_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_block_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_block_valid_stream.

Theorem wb_block :
  (Zstd.proof.harness.detect.WSpecs_detect.body_w_compressed_block) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_w_compressed_block) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_compressed_block) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_compressed_block) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_compressed_block) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_w_compressed_block) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_w_compressed_block).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_block_detect.wb_block_body
    (conj Zstd.proof.harness.stable_out.WB_block_stable_out.wb_block_body
    (conj Zstd.proof.harness.valid_dict.WB_block_valid_dict.wb_block_body
    (conj Zstd.proof.harness.valid_dict_copy.WB_block_valid_dict_copy.wb_block_body
    (conj Zstd.proof.harness.valid_info.WB_block_valid_info.wb_block_body
    (conj Zstd.proof.harness.valid_oneshot.WB_block_valid_oneshot.wb_block_body
    Zstd.proof.harness.valid_stream.WB_block_valid_stream.wb_block_body)))))).
Qed.
