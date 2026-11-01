(* Segment 4 of w_frame's body, statements 29..33 (blocks, gp_assert, content copy, checksum) and the post, in the
   7 writer units.  Each unit's proof is WB_frame_s4p_<u>.wf_seg4, in the generated
   src/proof/harness/<u>/WB_frame_s4p_<u>.v. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WB_frame_s4p_detect.
Require Zstd.proof.harness.stable_out.WB_frame_s4p_stable_out.
Require Zstd.proof.harness.valid_dict.WB_frame_s4p_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_frame_s4p_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_frame_s4p_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_frame_s4p_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_frame_s4p_valid_stream.

Theorem wb_frame_s4 :
  (Zstd.proof.harness.detect.WB_frame_defs_detect.wf_seg4_stmt) /\
  (Zstd.proof.harness.stable_out.WB_frame_defs_stable_out.wf_seg4_stmt) /\
  (Zstd.proof.harness.valid_dict.WB_frame_defs_valid_dict.wf_seg4_stmt) /\
  (Zstd.proof.harness.valid_dict_copy.WB_frame_defs_valid_dict_copy.wf_seg4_stmt) /\
  (Zstd.proof.harness.valid_info.WB_frame_defs_valid_info.wf_seg4_stmt) /\
  (Zstd.proof.harness.valid_oneshot.WB_frame_defs_valid_oneshot.wf_seg4_stmt) /\
  (Zstd.proof.harness.valid_stream.WB_frame_defs_valid_stream.wf_seg4_stmt).
Proof.
  exact (conj Zstd.proof.harness.detect.WB_frame_s4p_detect.wf_seg4 ( conj Zstd.proof.harness.stable_out.WB_frame_s4p_stable_out.wf_seg4 ( conj Zstd.proof.harness.valid_dict.WB_frame_s4p_valid_dict.wf_seg4 ( conj Zstd.proof.harness.valid_dict_copy.WB_frame_s4p_valid_dict_copy.wf_seg4 ( conj Zstd.proof.harness.valid_info.WB_frame_s4p_valid_info.wf_seg4 ( conj Zstd.proof.harness.valid_oneshot.WB_frame_s4p_valid_oneshot.wf_seg4 (Zstd.proof.harness.valid_stream.WB_frame_s4p_valid_stream.wf_seg4))))))).
Qed.
