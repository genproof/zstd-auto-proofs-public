(* The body of w_dict in the 3 writer units that have it (part of wb_top).  Prove
   each unit's in the generated src/proof/harness/<u>/WB_wdict_<u>.v (template WB_wdict), math in
   TopMath.v. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_dict.WB_wdict_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_wdict_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_wdict_valid_info.

Theorem wb_wdict :
  Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_dict
  /\ Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_dict
  /\ Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_dict
.
Proof.
  exact (conj Zstd.proof.harness.valid_dict.WB_wdict_valid_dict.wb_body_w_dict
          (conj Zstd.proof.harness.valid_dict_copy.WB_wdict_valid_dict_copy.wb_body_w_dict
                Zstd.proof.harness.valid_info.WB_wdict_valid_info.wb_body_w_dict)).
Qed.
