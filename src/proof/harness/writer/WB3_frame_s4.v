(* Segment 4 of w_frame's body in the 3 writer units of API v3.2, whose end state wf_P4 also has zframe_w.  Each unit's
   proof is WB_frame_s4w_<u>.wf_seg4, in the
   generated src/proof/harness/<u>/WB_frame_s4w_<u>.v (v3 template WB_frame_s4w). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB_frame_s4w_valid_bufferless Zstd.proof.harness.valid_dict_api.WB_frame_s4w_valid_dict_api Zstd.proof.harness.valid_params.WB_frame_s4w_valid_params.

Theorem wb3_frame_s4 :
  Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg4_stmt /\
  Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg4_stmt /\
  Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg4_stmt.
Proof.
  split; [| split].
  - exact Zstd.proof.harness.valid_bufferless.WB_frame_s4w_valid_bufferless.wf_seg4.
  - exact Zstd.proof.harness.valid_dict_api.WB_frame_s4w_valid_dict_api.wf_seg4.
  - exact Zstd.proof.harness.valid_params.WB_frame_s4w_valid_params.wf_seg4.
Qed.
