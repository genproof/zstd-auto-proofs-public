(* A part of w_compressed_block's segment B:
   statement 14 of the loop body (the literals loop): blk_it .. [] 0 -> blk_it .. L 0 with |L| = ll, for the 7 writer units (the template WBlkBDefs: blk_it and segB_lit).  Each unit's proof is in a new
   template WB_blkB_lit (generated: src/proof/harness/<u>/WB_blkB_lit_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkBDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkB_lit_detect.
Require Zstd.proof.harness.stable_out.WB_blkB_lit_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkB_lit_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkB_lit_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkB_lit_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkB_lit_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkB_lit_valid_stream.

Theorem wb_blkB_lit :
  Zstd.proof.harness.detect.WBlkBDefs_detect.segB_lit /\
  Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.segB_lit /\
  Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.segB_lit /\
  Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.segB_lit /\
  Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.segB_lit /\
  Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.segB_lit /\
  Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.segB_lit.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkB_lit_detect.segB_lit_ok ( conj Zstd.proof.harness.stable_out.WB_blkB_lit_stable_out.segB_lit_ok ( conj Zstd.proof.harness.valid_dict.WB_blkB_lit_valid_dict.segB_lit_ok ( conj Zstd.proof.harness.valid_dict_copy.WB_blkB_lit_valid_dict_copy.segB_lit_ok ( conj Zstd.proof.harness.valid_info.WB_blkB_lit_valid_info.segB_lit_ok ( conj Zstd.proof.harness.valid_oneshot.WB_blkB_lit_valid_oneshot.segB_lit_ok Zstd.proof.harness.valid_stream.WB_blkB_lit_valid_stream.segB_lit_ok)))))).
Qed.
