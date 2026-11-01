(* The writer-internals body group `fse_desc`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_fse_desc_<u>.v (template WB_fse_desc); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_fse_desc_detect.
Require Zstd.proof.harness.stable_out.WB_fse_desc_stable_out.
Require Zstd.proof.harness.valid_dict.WB_fse_desc_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_fse_desc_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_fse_desc_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_fse_desc_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_fse_desc_valid_stream.
Require Zstd.proof.harness.writer.WB_fse_states.

Theorem wb_fse_desc :
  (Zstd.proof.harness.detect.WSpecs_detect.body_fse_put_description /\
   Zstd.proof.harness.detect.WSpecs_detect.body_fse_states) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_put_description /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_fse_states) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_put_description /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_fse_states) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_put_description /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_fse_states) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_put_description /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_fse_states) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_put_description /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_fse_states) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_put_description /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_fse_states).
Proof.
  destruct Zstd.proof.harness.writer.WB_fse_states.wb_fse_states as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  exact (conj (conj Zstd.proof.harness.detect.WB_fse_desc_detect.wb_fse_put_description_detect S1)
    (conj (conj Zstd.proof.harness.stable_out.WB_fse_desc_stable_out.wb_fse_put_description_stable_out S2)
    (conj (conj Zstd.proof.harness.valid_dict.WB_fse_desc_valid_dict.wb_fse_put_description_valid_dict S3)
    (conj (conj Zstd.proof.harness.valid_dict_copy.WB_fse_desc_valid_dict_copy.wb_fse_put_description_valid_dict_copy S4)
    (conj (conj Zstd.proof.harness.valid_info.WB_fse_desc_valid_info.wb_fse_put_description_valid_info S5)
    (conj (conj Zstd.proof.harness.valid_oneshot.WB_fse_desc_valid_oneshot.wb_fse_put_description_valid_oneshot S6)
    (conj Zstd.proof.harness.valid_stream.WB_fse_desc_valid_stream.wb_fse_put_description_valid_stream S7))))))).
Qed.
