(* The writer-internals body group `huf_desc`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_huf_desc_<u>.v (template WB_huf_desc); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_huf_desc_detect.
Require Zstd.proof.harness.stable_out.WB_huf_desc_stable_out.
Require Zstd.proof.harness.valid_dict.WB_huf_desc_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_huf_desc_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_huf_desc_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_huf_desc_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_huf_desc_valid_stream.

Theorem wb_huf_desc :
  (Zstd.proof.harness.detect.WSpecs_detect.body_huf_put_description /\
   Zstd.proof.harness.detect.WSpecs_detect.body_huf_put_stream) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_huf_put_description /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_huf_put_stream) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_huf_put_description /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_huf_put_stream) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_huf_put_description /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_huf_put_stream) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_huf_put_description /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_huf_put_stream) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_huf_put_description /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_huf_put_stream) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_huf_put_description /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_huf_put_stream).
Proof.
  exact (conj (conj Zstd.proof.harness.detect.WB_huf_desc_detect.wb_body_huf_put_description Zstd.proof.harness.detect.WB_huf_desc_detect.wb_body_huf_put_stream)
    (conj (conj Zstd.proof.harness.stable_out.WB_huf_desc_stable_out.wb_body_huf_put_description Zstd.proof.harness.stable_out.WB_huf_desc_stable_out.wb_body_huf_put_stream)
    (conj (conj Zstd.proof.harness.valid_dict.WB_huf_desc_valid_dict.wb_body_huf_put_description Zstd.proof.harness.valid_dict.WB_huf_desc_valid_dict.wb_body_huf_put_stream)
    (conj (conj Zstd.proof.harness.valid_dict_copy.WB_huf_desc_valid_dict_copy.wb_body_huf_put_description Zstd.proof.harness.valid_dict_copy.WB_huf_desc_valid_dict_copy.wb_body_huf_put_stream)
    (conj (conj Zstd.proof.harness.valid_info.WB_huf_desc_valid_info.wb_body_huf_put_description Zstd.proof.harness.valid_info.WB_huf_desc_valid_info.wb_body_huf_put_stream)
    (conj (conj Zstd.proof.harness.valid_oneshot.WB_huf_desc_valid_oneshot.wb_body_huf_put_description Zstd.proof.harness.valid_oneshot.WB_huf_desc_valid_oneshot.wb_body_huf_put_stream)
    (conj Zstd.proof.harness.valid_stream.WB_huf_desc_valid_stream.wb_body_huf_put_description Zstd.proof.harness.valid_stream.WB_huf_desc_valid_stream.wb_body_huf_put_stream))))))).
Qed.
