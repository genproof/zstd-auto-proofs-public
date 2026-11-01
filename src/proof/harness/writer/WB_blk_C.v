(* The w_compressed_block segment C:
   statement 13 of w_compressed_block (the trailing literals): blk_gen -> blk_trail,
   for the 7 writer units (the template WBlkDefs: the assertions and seg_C).  Each unit's proof is in a
   template WB_blk_C (generated: src/proof/harness/<u>/WB_blk_C_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blk_C_detect.
Require Zstd.proof.harness.stable_out.WB_blk_C_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blk_C_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blk_C_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blk_C_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blk_C_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blk_C_valid_stream.

Theorem wb_blk_C :
  Zstd.proof.harness.detect.WBlkDefs_detect.seg_C /\
  Zstd.proof.harness.stable_out.WBlkDefs_stable_out.seg_C /\
  Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.seg_C /\
  Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.seg_C /\
  Zstd.proof.harness.valid_info.WBlkDefs_valid_info.seg_C /\
  Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.seg_C /\
  Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.seg_C.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blk_C_detect.seg_C_ok
    (conj Zstd.proof.harness.stable_out.WB_blk_C_stable_out.seg_C_ok
    (conj Zstd.proof.harness.valid_dict.WB_blk_C_valid_dict.seg_C_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blk_C_valid_dict_copy.seg_C_ok
    (conj Zstd.proof.harness.valid_info.WB_blk_C_valid_info.seg_C_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blk_C_valid_oneshot.seg_C_ok
    Zstd.proof.harness.valid_stream.WB_blk_C_valid_stream.seg_C_ok)))))).
Qed.
