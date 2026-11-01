(* The writer-internals body group `lit`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_lit_<u>.v (template WB_lit); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_lit_detect.
Require Zstd.proof.harness.stable_out.WB_lit_stable_out.
Require Zstd.proof.harness.valid_dict.WB_lit_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_lit_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_lit_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_lit_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_lit_valid_stream.

Theorem wb_lit :
  (Zstd.proof.harness.detect.WSpecs_detect.body_put_literals_raw_rle /\
   Zstd.proof.harness.detect.WSpecs_detect.body_put_literals_huf) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_put_literals_raw_rle /\
   Zstd.proof.harness.stable_out.WSpecs_stable_out.body_put_literals_huf) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_put_literals_raw_rle /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_put_literals_huf) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_put_literals_raw_rle /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_put_literals_huf) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_put_literals_raw_rle /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_put_literals_huf) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_put_literals_raw_rle /\
   Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_put_literals_huf) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_put_literals_raw_rle /\
   Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_put_literals_huf).
Proof.
  exact (conj (conj Zstd.proof.harness.detect.WB_lit_detect.wb_body_put_literals_raw_rle Zstd.proof.harness.detect.WB_lit_detect.wb_body_put_literals_huf)
   (conj (conj Zstd.proof.harness.stable_out.WB_lit_stable_out.wb_body_put_literals_raw_rle Zstd.proof.harness.stable_out.WB_lit_stable_out.wb_body_put_literals_huf)
   (conj (conj Zstd.proof.harness.valid_dict.WB_lit_valid_dict.wb_body_put_literals_raw_rle Zstd.proof.harness.valid_dict.WB_lit_valid_dict.wb_body_put_literals_huf)
   (conj (conj Zstd.proof.harness.valid_dict_copy.WB_lit_valid_dict_copy.wb_body_put_literals_raw_rle Zstd.proof.harness.valid_dict_copy.WB_lit_valid_dict_copy.wb_body_put_literals_huf)
   (conj (conj Zstd.proof.harness.valid_info.WB_lit_valid_info.wb_body_put_literals_raw_rle Zstd.proof.harness.valid_info.WB_lit_valid_info.wb_body_put_literals_huf)
   (conj (conj Zstd.proof.harness.valid_oneshot.WB_lit_valid_oneshot.wb_body_put_literals_raw_rle Zstd.proof.harness.valid_oneshot.WB_lit_valid_oneshot.wb_body_put_literals_huf)
   (conj Zstd.proof.harness.valid_stream.WB_lit_valid_stream.wb_body_put_literals_raw_rle Zstd.proof.harness.valid_stream.WB_lit_valid_stream.wb_body_put_literals_huf))))))).
Qed.
