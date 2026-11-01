(* The writer's internals for the 3 writer units added by API v3: WriterOK of each unit
   (the v3 template WriterOK: every helper body but vd_stream, in Gprog), from the per-unit body lemmas (generated into
   src/proof/harness/<u>/ by a script that is not part of this repository), the per-group conjunctions WB3_*.v (w_frame,
   w_compressed_block,
   w_series, w_dict, vp_*_within: the parts changed by API v3.2) and WAsm_<u>.writer_ok_of. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.valid_bufferless.WriterOK_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.
Require Zstd.proof.harness.valid_params.WriterOK_valid_params.
Require Zstd.proof.harness.writer.WB3_frame_s2 Zstd.proof.harness.writer.WB3_frame_hdr Zstd.proof.harness.writer.WB3_frame_s3 Zstd.proof.harness.writer.WB3_frame_s4 Zstd.proof.harness.writer.WB3_block Zstd.proof.harness.writer.WB3_wseries Zstd.proof.harness.writer.WB3_wdict Zstd.proof.harness.writer.WB3_within.
Require Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_copy_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_fse_build_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_fse_desc_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_fse_pick_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_fse_states_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_huf_desc_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_huf_fw_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_huf_pick_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_lit_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_misc_pre_body_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_misc_within_body_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless Zstd.proof.harness.valid_bufferless.WB_init_valid_bufferless Zstd.proof.harness.valid_bufferless.WAsm_valid_bufferless.
Require Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_copy_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_fse_build_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_fse_desc_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_fse_pick_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_fse_states_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_huf_desc_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_huf_fw_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_huf_pick_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_lit_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_misc_pre_body_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_misc_within_body_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_new3_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api Zstd.proof.harness.valid_dict_api.WB_init_valid_dict_api Zstd.proof.harness.valid_dict_api.WAsm_valid_dict_api.
Require Zstd.proof.harness.valid_params.WB_bits_valid_params Zstd.proof.harness.valid_params.WB_copy_valid_params Zstd.proof.harness.valid_params.WB_fse_build_valid_params Zstd.proof.harness.valid_params.WB_fse_desc_valid_params Zstd.proof.harness.valid_params.WB_fse_pick_valid_params Zstd.proof.harness.valid_params.WB_fse_states_valid_params Zstd.proof.harness.valid_params.WB_huf_desc_valid_params Zstd.proof.harness.valid_params.WB_huf_fw_valid_params Zstd.proof.harness.valid_params.WB_huf_pick_valid_params Zstd.proof.harness.valid_params.WB_lit_valid_params Zstd.proof.harness.valid_params.WB_misc_pre_body_valid_params Zstd.proof.harness.valid_params.WB_misc_valid_params Zstd.proof.harness.valid_params.WB_misc_within_body_valid_params Zstd.proof.harness.valid_params.WB_new3_valid_params Zstd.proof.harness.valid_params.WB_xxh_valid_params Zstd.proof.harness.valid_params.WB_init_valid_params Zstd.proof.harness.valid_params.WAsm_valid_params.

Lemma writer_ok3_valid_bufferless : Zstd.proof.harness.valid_bufferless.WriterOK_valid_bufferless.WriterOK.
Proof.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_bits_end_mark as H_bits_end_mark.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_bits_pad as H_bits_pad.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_bits_put as H_bits_put.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_choose as H_choose.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_choose_in as H_choose_in.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_exact_copy as H_exact_copy.
  pose proof Zstd.proof.harness.valid_bufferless.WB_fse_build_valid_bufferless.body_fse_build_valid_bufferless as H_fse_build.
  pose proof Zstd.proof.harness.valid_bufferless.WB_copy_valid_bufferless.body_fse_copy_ok as H_fse_copy.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_fse_has as H_fse_has.
  pose proof Zstd.proof.harness.valid_bufferless.WB_fse_pick_valid_bufferless.body_fse_pick_valid_bufferless as H_fse_pick.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_pre_body_valid_bufferless.wb_fse_predefined as H_fse_predefined.
  pose proof Zstd.proof.harness.valid_bufferless.WB_fse_desc_valid_bufferless.wb_fse_put_description_valid_bufferless as H_fse_put_description.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_fse_rle as H_fse_rle.
  pose proof Zstd.proof.harness.valid_bufferless.WB_fse_states_valid_bufferless.wb_body_fse_states as H_fse_states.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_highbit as H_highbit.
  pose proof Zstd.proof.harness.valid_bufferless.WB_copy_valid_bufferless.body_huf_copy_ok as H_huf_copy.
  pose proof Zstd.proof.harness.valid_bufferless.WB_huf_pick_valid_bufferless.wb_body_huf_pick as H_huf_pick.
  pose proof Zstd.proof.harness.valid_bufferless.WB_huf_desc_valid_bufferless.wb_body_huf_put_description as H_huf_put_description.
  pose proof Zstd.proof.harness.valid_bufferless.WB_huf_fw_valid_bufferless.body_huf_put_fse_weights_valid_bufferless as H_huf_put_fse_weights.
  pose proof Zstd.proof.harness.valid_bufferless.WB_huf_desc_valid_bufferless.wb_body_huf_put_stream as H_huf_put_stream.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_ll_code as H_ll_code.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_valid_bufferless.wb_ml_code as H_ml_code.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_put8 as H_put8.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_put_bytes as H_put_bytes.
  pose proof Zstd.proof.harness.valid_bufferless.WB_bits_valid_bufferless.wb_body_put_le as H_put_le.
  pose proof Zstd.proof.harness.valid_bufferless.WB_lit_valid_bufferless.wb_body_put_literals_huf as H_put_literals_huf.
  pose proof Zstd.proof.harness.valid_bufferless.WB_lit_valid_bufferless.wb_body_put_literals_raw_rle as H_put_literals_raw_rle.
  pose proof (proj1 Zstd.proof.harness.writer.WB3_block.wb3_block) as H_w_compressed_block.
  pose proof (proj1 Zstd.proof.harness.writer.WB3_wdict.wb3_wdict) as H_w_dict.
  pose proof ((proj1 Zstd.proof.harness.writer.WB3_frame_hdr.wb3_frame_main) (proj1 Zstd.proof.harness.writer.WB3_frame_s2.wb3_frame_s2) (proj1 Zstd.proof.harness.writer.WB3_frame_s3.wb3_frame_s3) (proj1 Zstd.proof.harness.writer.WB3_frame_s4.wb3_frame_s4)) as H_w_frame.
  pose proof (proj1 Zstd.proof.harness.writer.WB3_wseries.wb3_wseries) as H_w_series.
  pose proof Zstd.proof.harness.valid_bufferless.WB_misc_within_body_valid_bufferless.wb_within_oneshot as H_within_oneshot.
  pose proof Zstd.proof.harness.valid_bufferless.WB_copy_valid_bufferless.body_wstate_copy_ok as H_wstate_copy.
  pose proof Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless.body_xmerge_ok as H_xmerge.
  pose proof Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless.body_xread_ok as H_xread.
  pose proof Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless.body_xrotl_ok as H_xrotl.
  pose proof Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless.body_xround_ok as H_xround.
  pose proof Zstd.proof.harness.valid_bufferless.WB_xxh_valid_bufferless.body_xxh64_ok as H_xxh64.
  apply Zstd.proof.harness.valid_bufferless.WAsm_valid_bufferless.writer_ok_of; [exact Zstd.proof.harness.valid_bufferless.WB_init_valid_bufferless.init_ok_valid_bufferless |].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma writer_ok3_valid_dict_api : Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.WriterOK.
Proof.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_bits_end_mark as H_bits_end_mark.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_bits_pad as H_bits_pad.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_bits_put as H_bits_put.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_choose as H_choose.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_choose_in as H_choose_in.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_exact_copy as H_exact_copy.
  pose proof Zstd.proof.harness.valid_dict_api.WB_fse_build_valid_dict_api.body_fse_build_valid_dict_api as H_fse_build.
  pose proof Zstd.proof.harness.valid_dict_api.WB_copy_valid_dict_api.body_fse_copy_ok as H_fse_copy.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_fse_has as H_fse_has.
  pose proof Zstd.proof.harness.valid_dict_api.WB_fse_pick_valid_dict_api.body_fse_pick_valid_dict_api as H_fse_pick.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_pre_body_valid_dict_api.wb_fse_predefined as H_fse_predefined.
  pose proof Zstd.proof.harness.valid_dict_api.WB_fse_desc_valid_dict_api.wb_fse_put_description_valid_dict_api as H_fse_put_description.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_fse_rle as H_fse_rle.
  pose proof Zstd.proof.harness.valid_dict_api.WB_fse_states_valid_dict_api.wb_body_fse_states as H_fse_states.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_highbit as H_highbit.
  pose proof Zstd.proof.harness.valid_dict_api.WB_copy_valid_dict_api.body_huf_copy_ok as H_huf_copy.
  pose proof Zstd.proof.harness.valid_dict_api.WB_huf_pick_valid_dict_api.wb_body_huf_pick as H_huf_pick.
  pose proof Zstd.proof.harness.valid_dict_api.WB_huf_desc_valid_dict_api.wb_body_huf_put_description as H_huf_put_description.
  pose proof Zstd.proof.harness.valid_dict_api.WB_huf_fw_valid_dict_api.body_huf_put_fse_weights_valid_dict_api as H_huf_put_fse_weights.
  pose proof Zstd.proof.harness.valid_dict_api.WB_huf_desc_valid_dict_api.wb_body_huf_put_stream as H_huf_put_stream.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_ll_code as H_ll_code.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_ml_code as H_ml_code.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_put8 as H_put8.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_put_bytes as H_put_bytes.
  pose proof Zstd.proof.harness.valid_dict_api.WB_bits_valid_dict_api.wb_body_put_le as H_put_le.
  pose proof Zstd.proof.harness.valid_dict_api.WB_lit_valid_dict_api.wb_body_put_literals_huf as H_put_literals_huf.
  pose proof Zstd.proof.harness.valid_dict_api.WB_lit_valid_dict_api.wb_body_put_literals_raw_rle as H_put_literals_raw_rle.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_valid_dict_api.wb_stall_error as H_stall_error.
  pose proof Zstd.proof.harness.valid_dict_api.WB_new3_valid_dict_api.wb_vd_chunk as H_vd_chunk.
  pose proof (proj1 (proj2 Zstd.proof.harness.writer.WB3_block.wb3_block)) as H_w_compressed_block.
  pose proof (proj2 Zstd.proof.harness.writer.WB3_wdict.wb3_wdict) as H_w_dict.
  pose proof ((proj1 (proj2 Zstd.proof.harness.writer.WB3_frame_hdr.wb3_frame_main)) (proj1 (proj2 Zstd.proof.harness.writer.WB3_frame_s2.wb3_frame_s2)) (proj1 (proj2 Zstd.proof.harness.writer.WB3_frame_s3.wb3_frame_s3)) (proj1 (proj2 Zstd.proof.harness.writer.WB3_frame_s4.wb3_frame_s4))) as H_w_frame.
  pose proof (proj1 (proj2 Zstd.proof.harness.writer.WB3_wseries.wb3_wseries)) as H_w_series.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_within_body_valid_dict_api.wb_within_oneshot as H_within_oneshot.
  pose proof Zstd.proof.harness.valid_dict_api.WB_misc_within_body_valid_dict_api.wb_within_stream as H_within_stream.
  pose proof Zstd.proof.harness.valid_dict_api.WB_copy_valid_dict_api.body_wstate_copy_ok as H_wstate_copy.
  pose proof Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api.body_xmerge_ok as H_xmerge.
  pose proof Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api.body_xread_ok as H_xread.
  pose proof Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api.body_xrotl_ok as H_xrotl.
  pose proof Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api.body_xround_ok as H_xround.
  pose proof Zstd.proof.harness.valid_dict_api.WB_xxh_valid_dict_api.body_xxh64_ok as H_xxh64.
  apply Zstd.proof.harness.valid_dict_api.WAsm_valid_dict_api.writer_ok_of; [exact Zstd.proof.harness.valid_dict_api.WB_init_valid_dict_api.init_ok_valid_dict_api |].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma writer_ok3_valid_params : Zstd.proof.harness.valid_params.WriterOK_valid_params.WriterOK.
Proof.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_bits_end_mark as H_bits_end_mark.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_bits_pad as H_bits_pad.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_bits_put as H_bits_put.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_choose as H_choose.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_choose_in as H_choose_in.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_exact_copy as H_exact_copy.
  pose proof Zstd.proof.harness.valid_params.WB_fse_build_valid_params.body_fse_build_valid_params as H_fse_build.
  pose proof Zstd.proof.harness.valid_params.WB_copy_valid_params.body_fse_copy_ok as H_fse_copy.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_fse_has as H_fse_has.
  pose proof Zstd.proof.harness.valid_params.WB_fse_pick_valid_params.body_fse_pick_valid_params as H_fse_pick.
  pose proof Zstd.proof.harness.valid_params.WB_misc_pre_body_valid_params.wb_fse_predefined as H_fse_predefined.
  pose proof Zstd.proof.harness.valid_params.WB_fse_desc_valid_params.wb_fse_put_description_valid_params as H_fse_put_description.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_fse_rle as H_fse_rle.
  pose proof Zstd.proof.harness.valid_params.WB_fse_states_valid_params.wb_body_fse_states as H_fse_states.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_highbit as H_highbit.
  pose proof Zstd.proof.harness.valid_params.WB_copy_valid_params.body_huf_copy_ok as H_huf_copy.
  pose proof Zstd.proof.harness.valid_params.WB_huf_pick_valid_params.wb_body_huf_pick as H_huf_pick.
  pose proof Zstd.proof.harness.valid_params.WB_huf_desc_valid_params.wb_body_huf_put_description as H_huf_put_description.
  pose proof Zstd.proof.harness.valid_params.WB_huf_fw_valid_params.body_huf_put_fse_weights_valid_params as H_huf_put_fse_weights.
  pose proof Zstd.proof.harness.valid_params.WB_huf_desc_valid_params.wb_body_huf_put_stream as H_huf_put_stream.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_ll_code as H_ll_code.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_ml_code as H_ml_code.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_put8 as H_put8.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_put_bytes as H_put_bytes.
  pose proof Zstd.proof.harness.valid_params.WB_bits_valid_params.wb_body_put_le as H_put_le.
  pose proof Zstd.proof.harness.valid_params.WB_lit_valid_params.wb_body_put_literals_huf as H_put_literals_huf.
  pose proof Zstd.proof.harness.valid_params.WB_lit_valid_params.wb_body_put_literals_raw_rle as H_put_literals_raw_rle.
  pose proof Zstd.proof.harness.valid_params.WB_misc_valid_params.wb_stall_error as H_stall_error.
  pose proof (proj2 Zstd.proof.harness.writer.WB3_within.wb3_within) as H_vp_blocks_within.
  pose proof Zstd.proof.harness.valid_params.WB_new3_valid_params.wb_vp_chunk as H_vp_chunk.
  pose proof (proj1 Zstd.proof.harness.writer.WB3_within.wb3_within) as H_vp_windows_within.
  pose proof (proj2 (proj2 Zstd.proof.harness.writer.WB3_block.wb3_block)) as H_w_compressed_block.
  pose proof ((proj2 (proj2 Zstd.proof.harness.writer.WB3_frame_hdr.wb3_frame_main)) (proj2 (proj2 Zstd.proof.harness.writer.WB3_frame_s2.wb3_frame_s2)) (proj2 (proj2 Zstd.proof.harness.writer.WB3_frame_s3.wb3_frame_s3)) (proj2 (proj2 Zstd.proof.harness.writer.WB3_frame_s4.wb3_frame_s4))) as H_w_frame.
  pose proof (proj2 (proj2 Zstd.proof.harness.writer.WB3_wseries.wb3_wseries)) as H_w_series.
  pose proof Zstd.proof.harness.valid_params.WB_misc_within_body_valid_params.wb_within_oneshot as H_within_oneshot.
  pose proof Zstd.proof.harness.valid_params.WB_copy_valid_params.body_wstate_copy_ok as H_wstate_copy.
  pose proof Zstd.proof.harness.valid_params.WB_xxh_valid_params.body_xmerge_ok as H_xmerge.
  pose proof Zstd.proof.harness.valid_params.WB_xxh_valid_params.body_xread_ok as H_xread.
  pose proof Zstd.proof.harness.valid_params.WB_xxh_valid_params.body_xrotl_ok as H_xrotl.
  pose proof Zstd.proof.harness.valid_params.WB_xxh_valid_params.body_xround_ok as H_xround.
  pose proof Zstd.proof.harness.valid_params.WB_xxh_valid_params.body_xxh64_ok as H_xxh64.
  apply Zstd.proof.harness.valid_params.WAsm_valid_params.writer_ok_of; [exact Zstd.proof.harness.valid_params.WB_init_valid_params.init_ok_valid_params |].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Theorem writer_internals3_ok :
  Zstd.proof.harness.valid_bufferless.WriterOK_valid_bufferless.WriterOK /\
  Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.WriterOK /\
  Zstd.proof.harness.valid_params.WriterOK_valid_params.WriterOK.
Proof.
  exact (conj writer_ok3_valid_bufferless (conj writer_ok3_valid_dict_api writer_ok3_valid_params)).
Qed.
