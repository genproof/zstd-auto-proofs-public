(* The body of w_dict (valid_bufferless, valid_dict_api), whose post also has wd_formatted wd = true -> wd_id wd <> 0.
   Each unit's proof is in the generated src/proof/harness/<u>/WB_wdict_<u>.v (v3 template WB_wdict). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB_wdict_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB_wdict_valid_dict_api.

Theorem wb3_wdict :
  Zstd.proof.harness.valid_bufferless.WSpecs_valid_bufferless.body_w_dict /\
  Zstd.proof.harness.valid_dict_api.WSpecs_valid_dict_api.body_w_dict.
Proof.
  split.
  - exact Zstd.proof.harness.valid_bufferless.WB_wdict_valid_bufferless.wb_body_w_dict.
  - exact Zstd.proof.harness.valid_dict_api.WB_wdict_valid_dict_api.wb_body_w_dict.
Qed.
