(* The header of w_frame's body (statements 0..23) and the assembly of its segments, in the 7 writer units.  Each unit's
   proof is WB_frame_hdr_<u>.wf_main, in the generated
   src/proof/harness/<u>/WB_frame_hdr_<u>.v. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WB_frame_hdr_detect.
Require Zstd.proof.harness.stable_out.WB_frame_hdr_stable_out.
Require Zstd.proof.harness.valid_dict.WB_frame_hdr_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_frame_hdr_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_frame_hdr_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_frame_hdr_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_frame_hdr_valid_stream.

Theorem wb_frame_main :
  (Zstd.proof.harness.detect.WB_frame_defs_detect.wf_seg2_stmt -> Zstd.proof.harness.detect.WB_frame_defs_detect.wf_seg3_stmt -> Zstd.proof.harness.detect.WB_frame_defs_detect.wf_seg4_stmt -> Zstd.proof.harness.detect.WSpecs_detect.body_w_frame) /\
  (Zstd.proof.harness.stable_out.WB_frame_defs_stable_out.wf_seg2_stmt -> Zstd.proof.harness.stable_out.WB_frame_defs_stable_out.wf_seg3_stmt -> Zstd.proof.harness.stable_out.WB_frame_defs_stable_out.wf_seg4_stmt -> Zstd.proof.harness.stable_out.WSpecs_stable_out.body_w_frame) /\
  (Zstd.proof.harness.valid_dict.WB_frame_defs_valid_dict.wf_seg2_stmt -> Zstd.proof.harness.valid_dict.WB_frame_defs_valid_dict.wf_seg3_stmt -> Zstd.proof.harness.valid_dict.WB_frame_defs_valid_dict.wf_seg4_stmt -> Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_frame) /\
  (Zstd.proof.harness.valid_dict_copy.WB_frame_defs_valid_dict_copy.wf_seg2_stmt -> Zstd.proof.harness.valid_dict_copy.WB_frame_defs_valid_dict_copy.wf_seg3_stmt -> Zstd.proof.harness.valid_dict_copy.WB_frame_defs_valid_dict_copy.wf_seg4_stmt -> Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_frame) /\
  (Zstd.proof.harness.valid_info.WB_frame_defs_valid_info.wf_seg2_stmt -> Zstd.proof.harness.valid_info.WB_frame_defs_valid_info.wf_seg3_stmt -> Zstd.proof.harness.valid_info.WB_frame_defs_valid_info.wf_seg4_stmt -> Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_frame) /\
  (Zstd.proof.harness.valid_oneshot.WB_frame_defs_valid_oneshot.wf_seg2_stmt -> Zstd.proof.harness.valid_oneshot.WB_frame_defs_valid_oneshot.wf_seg3_stmt -> Zstd.proof.harness.valid_oneshot.WB_frame_defs_valid_oneshot.wf_seg4_stmt -> Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_w_frame) /\
  (Zstd.proof.harness.valid_stream.WB_frame_defs_valid_stream.wf_seg2_stmt -> Zstd.proof.harness.valid_stream.WB_frame_defs_valid_stream.wf_seg3_stmt -> Zstd.proof.harness.valid_stream.WB_frame_defs_valid_stream.wf_seg4_stmt -> Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_w_frame).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_frame_hdr_detect.wf_main (conj Zstd.proof.harness.stable_out.WB_frame_hdr_stable_out.wf_main (conj Zstd.proof.harness.valid_dict.WB_frame_hdr_valid_dict.wf_main (conj Zstd.proof.harness.valid_dict_copy.WB_frame_hdr_valid_dict_copy.wf_main (conj Zstd.proof.harness.valid_info.WB_frame_hdr_valid_info.wf_main (conj Zstd.proof.harness.valid_oneshot.WB_frame_hdr_valid_oneshot.wf_main Zstd.proof.harness.valid_stream.WB_frame_hdr_valid_stream.wf_main)))))).
Qed.
