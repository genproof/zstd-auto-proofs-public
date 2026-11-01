(* The writer-internals body group `frame`:
   the body obligations of its functions in the 7 writer units, from the header with the assembly (WB_frame_main)
   and the three segments of w_frame's body (WB_frame_s2, WB_frame_s3, WB_frame_s4). *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WSpecs_detect.
Require Zstd.proof.harness.stable_out.WSpecs_stable_out.
Require Zstd.proof.harness.valid_dict.WSpecs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WSpecs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WSpecs_valid_stream.
Require Zstd.proof.harness.writer.WB_frame_main Zstd.proof.harness.writer.WB_frame_s2
  Zstd.proof.harness.writer.WB_frame_s3 Zstd.proof.harness.writer.WB_frame_s4.

Theorem wb_frame :
  (Zstd.proof.harness.detect.WSpecs_detect.body_w_frame) /\
  (Zstd.proof.harness.stable_out.WSpecs_stable_out.body_w_frame) /\
  (Zstd.proof.harness.valid_dict.WSpecs_valid_dict.body_w_frame) /\
  (Zstd.proof.harness.valid_dict_copy.WSpecs_valid_dict_copy.body_w_frame) /\
  (Zstd.proof.harness.valid_info.WSpecs_valid_info.body_w_frame) /\
  (Zstd.proof.harness.valid_oneshot.WSpecs_valid_oneshot.body_w_frame) /\
  (Zstd.proof.harness.valid_stream.WSpecs_valid_stream.body_w_frame).
Proof.
  destruct Zstd.proof.harness.writer.WB_frame_main.wb_frame_main as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
  destruct Zstd.proof.harness.writer.WB_frame_s2.wb_frame_s2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  destruct Zstd.proof.harness.writer.WB_frame_s3.wb_frame_s3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct Zstd.proof.harness.writer.WB_frame_s4.wb_frame_s4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  exact (conj (M1 A1 B1 C1) (conj (M2 A2 B2 C2) (conj (M3 A3 B3 C3) (conj (M4 A4 B4 C4)
        (conj (M5 A5 B5 C5) (conj (M6 A6 B6 C6) (M7 A7 B7 C7))))))).
Qed.
