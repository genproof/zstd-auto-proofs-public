(* Segment 3 of w_frame's body (the blocks loop) in the 3 writer units, whose end state wf_P3 also has wblocks_pre_w / wblock_w.
   Each unit's proof is in the generated src/proof/harness/<u>/WB_frame_s3p_<u>.v (v3 template WB_frame_s3p). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WB3S3_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB3S3_valid_dict_api.
Require Zstd.proof.harness.valid_params.WB3S3_valid_params.

Theorem wb3_frame_s3 :
  Zstd.proof.harness.valid_bufferless.WB_frame_defs_valid_bufferless.wf_seg3_stmt /\
  Zstd.proof.harness.valid_dict_api.WB_frame_defs_valid_dict_api.wf_seg3_stmt /\
  Zstd.proof.harness.valid_params.WB_frame_defs_valid_params.wf_seg3_stmt.
Proof.
  split; [exact Zstd.proof.harness.valid_bufferless.WB3S3_valid_bufferless.wf_seg3 |].
  split; [exact Zstd.proof.harness.valid_dict_api.WB3S3_valid_dict_api.wf_seg3 |].
  exact Zstd.proof.harness.valid_params.WB3S3_valid_params.wf_seg3.
Qed.
