(* The w_compressed_block segment E, phase D:
   statements 7..8 of blkE_else (the modes byte, the descriptions loop: put8 of the RLE symbol / fse_put_description): blkE_modes -> blkE_desc,
   for the 7 writer units (the template WBlkEDefs: the assertions and segE_D).  Each unit's proof is in a
   template WB_blkE_D (generated: src/proof/harness/<u>/WB_blkE_D_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkEDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkE_D_detect.
Require Zstd.proof.harness.stable_out.WB_blkE_D_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkE_D_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkE_D_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkE_D_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkE_D_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkE_D_valid_stream.

Theorem wb_blkE_D :
  Zstd.proof.harness.detect.WBlkEDefs_detect.segE_D /\
  Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.segE_D /\
  Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.segE_D /\
  Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.segE_D /\
  Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.segE_D /\
  Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.segE_D /\
  Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.segE_D.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkE_D_detect.segE_D_ok
    (conj Zstd.proof.harness.stable_out.WB_blkE_D_stable_out.segE_D_ok
    (conj Zstd.proof.harness.valid_dict.WB_blkE_D_valid_dict.segE_D_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blkE_D_valid_dict_copy.segE_D_ok
    (conj Zstd.proof.harness.valid_info.WB_blkE_D_valid_info.segE_D_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blkE_D_valid_oneshot.segE_D_ok
    Zstd.proof.harness.valid_stream.WB_blkE_D_valid_stream.segE_D_ok)))))).
Qed.
