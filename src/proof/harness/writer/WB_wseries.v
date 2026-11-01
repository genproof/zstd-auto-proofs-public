(* The body of w_series in the 7 writer units (part of wb_top).  Each unit's proof
   is in the generated src/proof/harness/<u>/WB_wseries_<u>.v (template WB_wseries), math in TopMath.v. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.detect.WB_wseries_detect.
Require Zstd.proof.harness.stable_out.WB_wseries_stable_out.
Require Zstd.proof.harness.valid_dict.WB_wseries_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_wseries_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_wseries_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_wseries_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_wseries_valid_stream.

Theorem wb_wseries :
  Zstd.proof.harness.detect.WSpecs_detect.body_w_series
  /\ Zstd.proof.harness.stable_out.WSpecs_stable_out.body_w_series
  /\ Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_series
  /\ Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_series
  /\ Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_series
  /\ Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_w_series
  /\ Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_w_series
.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_wseries_detect.wb_body_w_series (conj Zstd.proof.harness.stable_out.WB_wseries_stable_out.wb_body_w_series (conj Zstd.proof.harness.valid_dict.WB_wseries_valid_dict.wb_body_w_series (conj Zstd.proof.harness.valid_dict_copy.WB_wseries_valid_dict_copy.wb_body_w_series (conj Zstd.proof.harness.valid_info.WB_wseries_valid_info.wb_body_w_series (conj Zstd.proof.harness.valid_oneshot.WB_wseries_valid_oneshot.wb_body_w_series Zstd.proof.harness.valid_stream.WB_wseries_valid_stream.wb_body_w_series)))))).
Qed.
