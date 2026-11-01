(* The writer-internals body group `init`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_init_<u>.v (template WB_init); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_init_detect.
Require Zstd.proof.harness.stable_out.WB_init_stable_out.
Require Zstd.proof.harness.valid_dict.WB_init_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_init_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_init_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_init_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_init_valid_stream.

Theorem wb_init :
  (Zstd.proof.harness.detect.WSpecs_detect.init_ok) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.init_ok) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.init_ok) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.init_ok) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.init_ok) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.init_ok) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.init_ok).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_init_detect.init_ok_detect (conj Zstd.proof.harness.stable_out.WB_init_stable_out.init_ok_stable_out (conj Zstd.proof.harness.valid_dict.WB_init_valid_dict.init_ok_valid_dict (conj Zstd.proof.harness.valid_dict_copy.WB_init_valid_dict_copy.init_ok_valid_dict_copy (conj Zstd.proof.harness.valid_info.WB_init_valid_info.init_ok_valid_info (conj Zstd.proof.harness.valid_oneshot.WB_init_valid_oneshot.init_ok_valid_oneshot Zstd.proof.harness.valid_stream.WB_init_valid_stream.init_ok_valid_stream)))))).
Qed.
