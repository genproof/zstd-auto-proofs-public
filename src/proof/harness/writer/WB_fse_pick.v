(* The writer-internals body group `fse_pick`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_fse_pick_<u>.v (template WB_fse_pick); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_fse_pick_detect.
Require Zstd.proof.harness.stable_out.WB_fse_pick_stable_out.
Require Zstd.proof.harness.valid_dict.WB_fse_pick_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_fse_pick_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_fse_pick_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_fse_pick_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_fse_pick_valid_stream.

Theorem wb_fse_pick :
  (Zstd.proof.harness.detect.WSpecs_detect.body_fse_pick) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_pick) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_pick) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_pick) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_pick) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_pick) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_pick).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_fse_pick_detect.body_fse_pick_detect (conj Zstd.proof.harness.stable_out.WB_fse_pick_stable_out.body_fse_pick_stable_out (conj Zstd.proof.harness.valid_dict.WB_fse_pick_valid_dict.body_fse_pick_valid_dict (conj Zstd.proof.harness.valid_dict_copy.WB_fse_pick_valid_dict_copy.body_fse_pick_valid_dict_copy (conj Zstd.proof.harness.valid_info.WB_fse_pick_valid_info.body_fse_pick_valid_info (conj Zstd.proof.harness.valid_oneshot.WB_fse_pick_valid_oneshot.body_fse_pick_valid_oneshot Zstd.proof.harness.valid_stream.WB_fse_pick_valid_stream.body_fse_pick_valid_stream)))))).
Qed.
