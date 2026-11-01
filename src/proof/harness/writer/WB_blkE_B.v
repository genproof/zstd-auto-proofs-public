(* The w_compressed_block segment E, phase B:
   statement 10 of blkE_else (the bitstream: b = {&blk,0,0}, the while loop over q with bits_put of the state updates and extra bits, the initial states, bits_end_mark): blkE_states -> blkE_bits,
   for the 7 writer units (the template WBlkEDefs: the assertions and segE_B).  Each unit's proof is in a
   template WB_blkE_B (generated: src/proof/harness/<u>/WB_blkE_B_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkEDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkE_B_detect.
Require Zstd.proof.harness.stable_out.WB_blkE_B_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkE_B_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkE_B_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkE_B_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkE_B_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkE_B_valid_stream.

Theorem wb_blkE_B :
  Zstd.proof.harness.detect.WBlkEDefs_detect.segE_B /\
  Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.segE_B /\
  Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.segE_B /\
  Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.segE_B /\
  Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.segE_B /\
  Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.segE_B /\
  Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.segE_B.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkE_B_detect.segE_B_ok (conj Zstd.proof.harness.stable_out.WB_blkE_B_stable_out.segE_B_ok (conj Zstd.proof.harness.valid_dict.WB_blkE_B_valid_dict.segE_B_ok (conj Zstd.proof.harness.valid_dict_copy.WB_blkE_B_valid_dict_copy.segE_B_ok (conj Zstd.proof.harness.valid_info.WB_blkE_B_valid_info.segE_B_ok (conj Zstd.proof.harness.valid_oneshot.WB_blkE_B_valid_oneshot.segE_B_ok Zstd.proof.harness.valid_stream.WB_blkE_B_valid_stream.segE_B_ok)))))).
Qed.
