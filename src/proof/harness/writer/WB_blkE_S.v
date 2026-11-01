(* The w_compressed_block segment E, phase S:
   statement 9 of blkE_else (the fse_states loop over the three tables into w_st): blkE_desc -> blkE_states,
   for the 7 writer units (the template WBlkEDefs: the assertions and segE_S).  Each unit's proof is in a
   template WB_blkE_S (generated: src/proof/harness/<u>/WB_blkE_S_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkEDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blkE_S_detect.
Require Zstd.proof.harness.stable_out.WB_blkE_S_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blkE_S_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blkE_S_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blkE_S_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blkE_S_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blkE_S_valid_stream.

Theorem wb_blkE_S :
  Zstd.proof.harness.detect.WBlkEDefs_detect.segE_S /\
  Zstd.proof.harness.stable_out.WBlkEDefs_stable_out.segE_S /\
  Zstd.proof.harness.valid_dict.WBlkEDefs_valid_dict.segE_S /\
  Zstd.proof.harness.valid_dict_copy.WBlkEDefs_valid_dict_copy.segE_S /\
  Zstd.proof.harness.valid_info.WBlkEDefs_valid_info.segE_S /\
  Zstd.proof.harness.valid_oneshot.WBlkEDefs_valid_oneshot.segE_S /\
  Zstd.proof.harness.valid_stream.WBlkEDefs_valid_stream.segE_S.
Proof.
  exact (conj Zstd.proof.harness.detect.WB_blkE_S_detect.segE_S_ok
    (conj Zstd.proof.harness.stable_out.WB_blkE_S_stable_out.segE_S_ok
    (conj Zstd.proof.harness.valid_dict.WB_blkE_S_valid_dict.segE_S_ok
    (conj Zstd.proof.harness.valid_dict_copy.WB_blkE_S_valid_dict_copy.segE_S_ok
    (conj Zstd.proof.harness.valid_info.WB_blkE_S_valid_info.segE_S_ok
    (conj Zstd.proof.harness.valid_oneshot.WB_blkE_S_valid_oneshot.segE_S_ok
    Zstd.proof.harness.valid_stream.WB_blkE_S_valid_stream.segE_S_ok)))))).
Qed.
