(* The w_compressed_block segment B:
   statement 12 of w_compressed_block (the loop drawing the sequences): blk_gen -> blk_gen,
   for the 7 writer units (the template WBlkDefs: the assertions and seg_B).  Each unit's proof is in a
   template WB_blk_B (generated: src/proof/harness/<u>/WB_blk_B_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blk_B_detect.
Require Zstd.proof.harness.stable_out.WB_blk_B_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blk_B_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blk_B_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blk_B_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blk_B_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blk_B_valid_stream.
Require Zstd.proof.harness.writer.WB_blkB_lit Zstd.proof.harness.writer.WB_blkB_match Zstd.proof.harness.writer.WB_blkB_codes.

Theorem wb_blk_B :
  Zstd.proof.harness.detect.WBlkDefs_detect.seg_B /\
  Zstd.proof.harness.stable_out.WBlkDefs_stable_out.seg_B /\
  Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.seg_B /\
  Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.seg_B /\
  Zstd.proof.harness.valid_info.WBlkDefs_valid_info.seg_B /\
  Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.seg_B /\
  Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.seg_B.
Proof.
  destruct Zstd.proof.harness.writer.WB_blkB_lit.wb_blkB_lit as (l1 & l2 & l3 & l4 & l5 & l6 & l7).
  destruct Zstd.proof.harness.writer.WB_blkB_match.wb_blkB_match as (m1 & m2 & m3 & m4 & m5 & m6 & m7).
  destruct Zstd.proof.harness.writer.WB_blkB_codes.wb_blkB_codes as (c1 & c2 & c3 & c4 & c5 & c6 & c7).
  exact (conj (Zstd.proof.harness.detect.WB_blk_B_detect.seg_B_ok l1 m1 c1)
        (conj (Zstd.proof.harness.stable_out.WB_blk_B_stable_out.seg_B_ok l2 m2 c2)
        (conj (Zstd.proof.harness.valid_dict.WB_blk_B_valid_dict.seg_B_ok l3 m3 c3)
        (conj (Zstd.proof.harness.valid_dict_copy.WB_blk_B_valid_dict_copy.seg_B_ok l4 m4 c4)
        (conj (Zstd.proof.harness.valid_info.WB_blk_B_valid_info.seg_B_ok l5 m5 c5)
        (conj (Zstd.proof.harness.valid_oneshot.WB_blk_B_valid_oneshot.seg_B_ok l6 m6 c6)
              (Zstd.proof.harness.valid_stream.WB_blk_B_valid_stream.seg_B_ok l7 m7 c7))))))).
Qed.
