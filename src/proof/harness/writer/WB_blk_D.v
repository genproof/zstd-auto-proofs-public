(* The w_compressed_block segment D:
   statements 14..15 of w_compressed_block (the literals section; the new Huffman code into st): blk_trail -> blk_seqs,
   for the 7 writer units (the template WBlkDefs: the assertions and seg_D).  Each unit's proof is in a
   template WB_blk_D (generated: src/proof/harness/<u>/WB_blk_D_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blk_D_detect.
Require Zstd.proof.harness.stable_out.WB_blk_D_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blk_D_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blk_D_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blk_D_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blk_D_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blk_D_valid_stream.

Theorem wb_blk_D :
  Zstd.proof.harness.detect.WBlkDefs_detect.seg_D /\
  Zstd.proof.harness.stable_out.WBlkDefs_stable_out.seg_D /\
  Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.seg_D /\
  Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.seg_D /\
  Zstd.proof.harness.valid_info.WBlkDefs_valid_info.seg_D /\
  Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.seg_D /\
  Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.seg_D.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blk_D_detect.seg_D_ok
    (conj Zstd.proof.harness.stable_out.WB_blk_D_stable_out.seg_D_ok
    (conj Zstd.proof.harness.valid_dict.WB_blk_D_valid_dict.seg_D_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blk_D_valid_dict_copy.seg_D_ok
    (conj Zstd.proof.harness.valid_info.WB_blk_D_valid_info.seg_D_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blk_D_valid_oneshot.seg_D_ok
          Zstd.proof.harness.valid_stream.WB_blk_D_valid_stream.seg_D_ok)))))).
Qed.
