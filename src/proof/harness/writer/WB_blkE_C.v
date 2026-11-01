(* The w_compressed_block segment E, phase C:
   statements 11..12 of blkE_else (fse_copy of ntab into st->tab, have_tab = 1) and the entailment into blk_done (seqsec_ok by WM_BlkHdr.seq_hdr_ok + WM_BlkStream.seq_stream_ok): blkE_bits -> blk_done,
   for the 7 writer units (the template WBlkEDefs: the assertions and segE_C).  Each unit's proof is in a
   template WB_blkE_C (generated: src/proof/harness/<u>/WB_blkE_C_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkEDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkE_C_detect.
Require Zstd.proof.harness.stable_out.WB_blkE_C_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkE_C_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkE_C_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkE_C_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkE_C_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkE_C_valid_stream.

Theorem wb_blkE_C :
  Zstd.proof.harness.detect.WBlkEDefs_detect.segE_C /\
  Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.segE_C /\
  Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.segE_C /\
  Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.segE_C /\
  Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.segE_C /\
  Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.segE_C /\
  Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.segE_C.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkE_C_detect.segE_C_ok (conj Zstd.proof.harness.stable_out.WB_blkE_C_stable_out.segE_C_ok (conj Zstd.proof.harness.valid_dict.WB_blkE_C_valid_dict.segE_C_ok (conj Zstd.proof.harness.valid_dict_copy.WB_blkE_C_valid_dict_copy.segE_C_ok (conj Zstd.proof.harness.valid_info.WB_blkE_C_valid_info.segE_C_ok (conj Zstd.proof.harness.valid_oneshot.WB_blkE_C_valid_oneshot.segE_C_ok Zstd.proof.harness.valid_stream.WB_blkE_C_valid_stream.segE_C_ok)))))).
Qed.
