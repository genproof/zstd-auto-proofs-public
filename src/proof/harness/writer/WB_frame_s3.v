(* Segment 3 of w_frame's body, statement 28 (the blocks loop), in the 7 writer units.  Each unit's proof is
   WB_frame_s3p_<u>.wf_seg3, in the generated
   src/proof/harness/<u>/WB_frame_s3p_<u>.v (template WB_frame_s3p). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WB_frame_s3p_detect.
Require Zstd.proof.harness.stable_out.WB_frame_s3p_stable_out.
Require Zstd.proof.harness.valid_dict.WB_frame_s3p_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_frame_s3p_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_frame_s3p_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_frame_s3p_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_frame_s3p_valid_stream.

Theorem wb_frame_s3 :
  (Zstd.proof.harness.detect.WB_frame_defs_detect.wf_seg3_stmt) /\
  (Zstd.proof.harness.stable_out.WB_frame_defs_stable_out.wf_seg3_stmt) /\
  (Zstd.proof.harness.valid_dict.WB_frame_defs_valid_dict.wf_seg3_stmt) /\
  (Zstd.proof.harness.valid_dict_copy.WB_frame_defs_valid_dict_copy.wf_seg3_stmt) /\
  (Zstd.proof.harness.valid_info.WB_frame_defs_valid_info.wf_seg3_stmt) /\
  (Zstd.proof.harness.valid_oneshot.WB_frame_defs_valid_oneshot.wf_seg3_stmt) /\
  (Zstd.proof.harness.valid_stream.WB_frame_defs_valid_stream.wf_seg3_stmt).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_frame_s3p_detect.wf_seg3 (conj Zstd.proof.harness.stable_out.WB_frame_s3p_stable_out.wf_seg3 (conj Zstd.proof.harness.valid_dict.WB_frame_s3p_valid_dict.wf_seg3 (conj Zstd.proof.harness.valid_dict_copy.WB_frame_s3p_valid_dict_copy.wf_seg3 (conj Zstd.proof.harness.valid_info.WB_frame_s3p_valid_info.wf_seg3 (conj Zstd.proof.harness.valid_oneshot.WB_frame_s3p_valid_oneshot.wf_seg3 Zstd.proof.harness.valid_stream.WB_frame_s3p_valid_stream.wf_seg3)))))).
Qed.
