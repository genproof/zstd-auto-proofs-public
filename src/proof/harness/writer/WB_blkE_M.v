(* The w_compressed_block segment E, phase M:
   statement 6 of blkE_else (the modes loop: per type the options pre/same/covers, mode[ty], ntab[ty] by fse_predefined / fse_rle / need[] + fse_pick / fse_copy from st->tab): blkE_hdr -> blkE_modes,
   for the 7 writer units (the template WBlkEDefs: the assertions and segE_M).  Each unit's proof is in a
   template WB_blkE_M (generated: src/proof/harness/<u>/WB_blkE_M_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkEDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkE_M_detect.
Require Zstd.proof.harness.stable_out.WB_blkE_M_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkE_M_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkE_M_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkE_M_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkE_M_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkE_M_valid_stream.

Theorem wb_blkE_M :
  Zstd.proof.harness.detect.WBlkEDefs_detect.segE_M /\
  Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.segE_M /\
  Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.segE_M /\
  Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.segE_M /\
  Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.segE_M /\
  Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.segE_M /\
  Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.segE_M.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkE_M_detect.segE_M_ok (conj Zstd.proof.harness.stable_out.WB_blkE_M_stable_out.segE_M_ok (conj Zstd.proof.harness.valid_dict.WB_blkE_M_valid_dict.segE_M_ok (conj Zstd.proof.harness.valid_dict_copy.WB_blkE_M_valid_dict_copy.segE_M_ok (conj Zstd.proof.harness.valid_info.WB_blkE_M_valid_info.segE_M_ok (conj Zstd.proof.harness.valid_oneshot.WB_blkE_M_valid_oneshot.segE_M_ok Zstd.proof.harness.valid_stream.WB_blkE_M_valid_stream.segE_M_ok)))))).
Qed.
