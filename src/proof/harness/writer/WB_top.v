(* The writer-internals body group `top`:
   the body obligations of its functions in the 7 writer units.  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_top_<u>.v (template WB_top); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.writer.WB_wseries Zstd.proof.harness.writer.WB_wdict.

Theorem wb_top :
  (Zstd.proof.harness.detect.WSpecs_detect.body_w_series) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_w_series) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_series /\
   Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_dict) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_series /\
   Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_dict) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_series /\
   Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_dict) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_w_series) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_w_series).
Proof.
  destruct Zstd.proof.harness.writer.WB_wseries.wb_wseries as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct Zstd.proof.harness.writer.WB_wdict.wb_wdict as (D3 & D4 & D5).
  exact (conj S1 (conj S2 (conj (conj S3 D3) (conj (conj S4 D4) (conj (conj S5 D5) (conj S6 S7)))))).
Qed.
