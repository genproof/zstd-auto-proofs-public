(* A part of w_compressed_block's segment B:
   statement 15 of the loop body (the match copy loop): blk_it .. L 0 -> blk_it .. L ml, for the 7 writer units (the template WBlkBDefs: blk_it and segB_match).  Each unit's proof is in a new
   template WB_blkB_match (generated: src/proof/harness/<u>/WB_blkB_match_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkBDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkB_match_detect.
Require Zstd.proof.harness.stable_out.WB_blkB_match_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkB_match_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkB_match_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkB_match_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkB_match_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkB_match_valid_stream.

Theorem wb_blkB_match :
  Zstd.proof.harness.detect.WBlkBDefs_detect.segB_match /\
  Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.segB_match /\
  Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.segB_match /\
  Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.segB_match /\
  Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.segB_match /\
  Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.segB_match /\
  Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.segB_match.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkB_match_detect.segB_match_ok
    (conj Zstd.proof.harness.stable_out.WB_blkB_match_stable_out.segB_match_ok
    (conj Zstd.proof.harness.valid_dict.WB_blkB_match_valid_dict.segB_match_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blkB_match_valid_dict_copy.segB_match_ok
    (conj Zstd.proof.harness.valid_info.WB_blkB_match_valid_info.segB_match_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blkB_match_valid_oneshot.segB_match_ok
    (Zstd.proof.harness.valid_stream.WB_blkB_match_valid_stream.segB_match_ok))))))).
Qed.
