(* A part of w_compressed_block's segment B:
   statements 16..23 of the loop body (w_code / w_extra, nseq++, rem -= ll + ml): blk_it .. L ml -> the loop invariant blkB_inv, for the 7 writer units (the template WBlkBDefs: blk_it and segB_codes).  Each unit's proof is in a new
   template WB_blkB_codes (generated: src/proof/harness/<u>/WB_blkB_codes_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkBDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkB_codes_detect.
Require Zstd.proof.harness.stable_out.WB_blkB_codes_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkB_codes_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkB_codes_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkB_codes_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkB_codes_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkB_codes_valid_stream.

Theorem wb_blkB_codes :
  Zstd.proof.harness.detect.WBlkBDefs_detect.segB_codes /\
  Zstd.proof.harness.stable_out.WBlkBDefs_stable_out.segB_codes /\
  Zstd.proof.harness.valid_dict.WBlkBDefs_valid_dict.segB_codes /\
  Zstd.proof.harness.valid_dict_copy.WBlkBDefs_valid_dict_copy.segB_codes /\
  Zstd.proof.harness.valid_info.WBlkBDefs_valid_info.segB_codes /\
  Zstd.proof.harness.valid_oneshot.WBlkBDefs_valid_oneshot.segB_codes /\
  Zstd.proof.harness.valid_stream.WBlkBDefs_valid_stream.segB_codes.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkB_codes_detect.segB_codes_ok (conj Zstd.proof.harness.stable_out.WB_blkB_codes_stable_out.segB_codes_ok (conj Zstd.proof.harness.valid_dict.WB_blkB_codes_valid_dict.segB_codes_ok (conj Zstd.proof.harness.valid_dict_copy.WB_blkB_codes_valid_dict_copy.segB_codes_ok (conj Zstd.proof.harness.valid_info.WB_blkB_codes_valid_info.segB_codes_ok (conj Zstd.proof.harness.valid_oneshot.WB_blkB_codes_valid_oneshot.segB_codes_ok Zstd.proof.harness.valid_stream.WB_blkB_codes_valid_stream.segB_codes_ok)))))).
Qed.
