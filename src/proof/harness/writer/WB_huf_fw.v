(* The writer-internals body group `huf_fw`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_huf_fw_<u>.v (template WB_huf_fw); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_huf_fw_detect.
Require Zstd.proof.harness.stable_out.WB_huf_fw_stable_out.
Require Zstd.proof.harness.valid_dict.WB_huf_fw_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_huf_fw_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_huf_fw_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_huf_fw_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_huf_fw_valid_stream.

Theorem wb_huf_fw :
  (Zstd.proof.harness.detect.WSpecs_detect.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_huf_put_fse_weights) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_huf_put_fse_weights).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_huf_fw_detect.body_huf_put_fse_weights_detect
        (conj Zstd.proof.harness.stable_out.WB_huf_fw_stable_out.body_huf_put_fse_weights_stable_out
        (conj Zstd.proof.harness.valid_dict.WB_huf_fw_valid_dict.body_huf_put_fse_weights_valid_dict
        (conj Zstd.proof.harness.valid_dict_copy.WB_huf_fw_valid_dict_copy.body_huf_put_fse_weights_valid_dict_copy
        (conj Zstd.proof.harness.valid_info.WB_huf_fw_valid_info.body_huf_put_fse_weights_valid_info
        (conj Zstd.proof.harness.valid_oneshot.WB_huf_fw_valid_oneshot.body_huf_put_fse_weights_valid_oneshot Zstd.proof.harness.valid_stream.WB_huf_fw_valid_stream.body_huf_put_fse_weights_valid_stream)))))).
Qed.
