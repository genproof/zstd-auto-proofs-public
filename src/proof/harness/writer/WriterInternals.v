(* The writer's internals for the 7 writer units: WriterOK of each unit. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WriterOK_detect.
Require Zstd.proof.harness.stable_out.WriterOK_stable_out.
Require Zstd.proof.harness.valid_dict.WriterOK_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WriterOK_valid_info.
Require Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WriterOK_valid_stream.

Require Zstd.proof.harness.writer.WB_bits.
Require Zstd.proof.harness.writer.WB_misc.
Require Zstd.proof.harness.writer.WB_copy.
Require Zstd.proof.harness.writer.WB_xxh.
Require Zstd.proof.harness.writer.WB_fse_build.
Require Zstd.proof.harness.writer.WB_fse_pick.
Require Zstd.proof.harness.writer.WB_fse_desc.
Require Zstd.proof.harness.writer.WB_huf_pick.
Require Zstd.proof.harness.writer.WB_huf_fw.
Require Zstd.proof.harness.writer.WB_huf_desc.
Require Zstd.proof.harness.writer.WB_lit.
Require Zstd.proof.harness.writer.WB_block.
Require Zstd.proof.harness.writer.WB_frame.
Require Zstd.proof.harness.writer.WB_top.
Require Zstd.proof.harness.writer.WB_init.
Require Zstd.proof.harness.detect.WAsm_detect.
Require Zstd.proof.harness.stable_out.WAsm_stable_out.
Require Zstd.proof.harness.valid_dict.WAsm_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WAsm_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WAsm_valid_info.
Require Zstd.proof.harness.valid_oneshot.WAsm_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WAsm_valid_stream.

Theorem writer_internals_ok :
  Zstd.proof.harness.detect.WriterOK_detect.WriterOK /\
  Zstd.proof.harness.stable_out.WriterOK_stable_out.WriterOK /\
  Zstd.proof.harness.valid_dict.WriterOK_valid_dict.WriterOK /\
  Zstd.proof.harness.valid_dict_copy.WriterOK_valid_dict_copy.WriterOK /\
  Zstd.proof.harness.valid_info.WriterOK_valid_info.WriterOK /\
  Zstd.proof.harness.valid_oneshot.WriterOK_valid_oneshot.WriterOK /\
  Zstd.proof.harness.valid_stream.WriterOK_valid_stream.WriterOK.
Proof.
  pose proof Zstd.proof.harness.writer.WB_bits.wb_bits.
  pose proof Zstd.proof.harness.writer.WB_misc.wb_misc.
  pose proof Zstd.proof.harness.writer.WB_copy.wb_copy.
  pose proof Zstd.proof.harness.writer.WB_xxh.wb_xxh.
  pose proof Zstd.proof.harness.writer.WB_fse_build.wb_fse_build.
  pose proof Zstd.proof.harness.writer.WB_fse_pick.wb_fse_pick.
  pose proof Zstd.proof.harness.writer.WB_fse_desc.wb_fse_desc.
  pose proof Zstd.proof.harness.writer.WB_huf_pick.wb_huf_pick.
  pose proof Zstd.proof.harness.writer.WB_huf_fw.wb_huf_fw.
  pose proof Zstd.proof.harness.writer.WB_huf_desc.wb_huf_desc.
  pose proof Zstd.proof.harness.writer.WB_lit.wb_lit.
  pose proof Zstd.proof.harness.writer.WB_block.wb_block.
  pose proof Zstd.proof.harness.writer.WB_frame.wb_frame.
  pose proof Zstd.proof.harness.writer.WB_top.wb_top.
  pose proof Zstd.proof.harness.writer.WB_init.wb_init.
  repeat match goal with H: _ /\ _ |- _ => destruct H end.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); [apply Zstd.proof.harness.detect.WAsm_detect.writer_ok_of | apply Zstd.proof.harness.stable_out.WAsm_stable_out.writer_ok_of | apply Zstd.proof.harness.valid_dict.WAsm_valid_dict.writer_ok_of | apply Zstd.proof.harness.valid_dict_copy.WAsm_valid_dict_copy.writer_ok_of | apply Zstd.proof.harness.valid_info.WAsm_valid_info.writer_ok_of | apply Zstd.proof.harness.valid_oneshot.WAsm_valid_oneshot.writer_ok_of | apply Zstd.proof.harness.valid_stream.WAsm_valid_stream.writer_ok_of];
    first [assumption | repeat match goal with |- _ /\ _ => split end; assumption].
Qed.
