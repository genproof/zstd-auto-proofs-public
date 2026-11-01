(* Statements 0..23 of w_frame's body (the header) and the
   assembly of its segments, in the 3 writer units of API v3, with the dictionary argument wdarg (WAExt:
   valid_dict_api mode 2).  Each unit's proof is in the generated
   src/proof/harness/<u>/WB_frame_hdr_<u>.v (v3 template WB_frame_hdr, from the template WB_frame_hdr). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB_frame_hdr_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB_frame_hdr_valid_dict_api.
Require Zstd.proof.harness.valid_params.WB_frame_hdr_valid_params.

Theorem wb3_frame_main :
  (Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg2_stmt -> Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg3_stmt -> Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg4_stmt ->
   Zstd.proof.harness.valid_bufferless.WSpecs_valid_bufferless.body_w_frame) /\
  (Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg2_stmt -> Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg3_stmt -> Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg4_stmt ->
   Zstd.proof.harness.valid_dict_api.WSpecs_valid_dict_api.body_w_frame) /\
  (Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg2_stmt -> Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg3_stmt -> Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg4_stmt ->
   Zstd.proof.harness.valid_params.WSpecs_valid_params.body_w_frame).
Proof.
  exact (conj Zstd.proof.harness.valid_bufferless.WB_frame_hdr_valid_bufferless.wf_main
         (conj Zstd.proof.harness.valid_dict_api.WB_frame_hdr_valid_dict_api.wf_main
               Zstd.proof.harness.valid_params.WB_frame_hdr_valid_params.wf_main)).
Qed.
