(* The w_compressed_block segment A:
   statements 0..11 of w_compressed_block (out_t blk, the counters, the literals mode): blk_entry -> blk_gen,
   for the 7 writer units (the template WBlkDefs: the assertions and seg_A).  Each unit's proof is in a
   template WB_blk_A (generated: src/proof/harness/<u>/WB_blk_A_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blk_A_detect.
Require Zstd.proof.harness.stable_out.WB_blk_A_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blk_A_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blk_A_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blk_A_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blk_A_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blk_A_valid_stream.

Theorem wb_blk_A :
  Zstd.proof.harness.detect.WBlkDefs_detect.seg_A /\
  Zstd.proof.harness.stable_out.WBlkDefs_stable_out.seg_A /\
  Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.seg_A /\
  Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.seg_A /\
  Zstd.proof.harness.valid_info.WBlkDefs_valid_info.seg_A /\
  Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.seg_A /\
  Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.seg_A.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blk_A_detect.seg_A_ok
    (conj Zstd.proof.harness.stable_out.WB_blk_A_stable_out.seg_A_ok
    (conj Zstd.proof.harness.valid_dict.WB_blk_A_valid_dict.seg_A_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blk_A_valid_dict_copy.seg_A_ok
    (conj Zstd.proof.harness.valid_info.WB_blk_A_valid_info.seg_A_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blk_A_valid_oneshot.seg_A_ok
    Zstd.proof.harness.valid_stream.WB_blk_A_valid_stream.seg_A_ok)))))).
Qed.
