(* The body of w_series in the 3 writer units, whose post also has series_dwin.
   Each unit's proof is in the generated src/proof/harness/<u>/WB_wseries_<u>.v (v3 template WB_wseries). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB_wseriesD_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB_wseriesD_valid_dict_api.
Require Zstd.proof.harness.valid_params.WB_wseriesD_valid_params.

Theorem wb3_wseries :
  Zstd.proof.harness.valid_bufferless.WSpecs_valid_bufferless.body_w_series /\
  Zstd.proof.harness.valid_dict_api.WSpecs_valid_dict_api.body_w_series /\
  Zstd.proof.harness.valid_params.WSpecs_valid_params.body_w_series.
Proof.
  split; [exact Zstd.proof.harness.valid_bufferless.WB_wseriesD_valid_bufferless.wb_body_w_series |].
  split; [exact Zstd.proof.harness.valid_dict_api.WB_wseriesD_valid_dict_api.wb_body_w_series |].
  exact Zstd.proof.harness.valid_params.WB_wseriesD_valid_params.wb_body_w_series.
Qed.
