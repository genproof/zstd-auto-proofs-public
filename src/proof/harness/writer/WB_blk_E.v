(* The w_compressed_block segment E:
   statement 16 of w_compressed_block (the sequences section: header, tables, bitstream, tables into st): blk_seqs -> blk_done,
   for the 7 writer units (the template WBlkDefs: the assertions and seg_E).  Each unit's proof is in a
   template WB_blk_E (generated: src/proof/harness/<u>/WB_blk_E_<u>.v); this file concludes from them. *)
Require Import VST.floyd.proofauto.
Require Zstd.proof.harness.detect.WBlkDefs_detect.
Require Zstd.proof.harness.stable_out.WBlkDefs_stable_out.
Require Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WBlkDefs_valid_info.
Require Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.
Require Zstd.proof.harness.detect.WB_blk_E_detect.
Require Zstd.proof.harness.stable_out.WB_blk_E_stable_out.
Require Zstd.proof.harness.valid_dict.WB_blk_E_valid_dict.
Require Zstd.proof.harness.valid_dict_copy.WB_blk_E_valid_dict_copy.
Require Zstd.proof.harness.valid_info.WB_blk_E_valid_info.
Require Zstd.proof.harness.valid_oneshot.WB_blk_E_valid_oneshot.
Require Zstd.proof.harness.valid_stream.WB_blk_E_valid_stream.
Require Zstd.proof.harness.writer.WB_blkE_M.
Require Zstd.proof.harness.writer.WB_blkE_D.
Require Zstd.proof.harness.writer.WB_blkE_S.
Require Zstd.proof.harness.writer.WB_blkE_B.
Require Zstd.proof.harness.writer.WB_blkE_C.

Theorem wb_blk_E :
  Zstd.proof.harness.detect.WBlkDefs_detect.seg_E /\
  Zstd.proof.harness.stable_out.WBlkDefs_stable_out.seg_E /\
  Zstd.proof.harness.valid_dict.WBlkDefs_valid_dict.seg_E /\
  Zstd.proof.harness.valid_dict_copy.WBlkDefs_valid_dict_copy.seg_E /\
  Zstd.proof.harness.valid_info.WBlkDefs_valid_info.seg_E /\
  Zstd.proof.harness.valid_oneshot.WBlkDefs_valid_oneshot.seg_E /\
  Zstd.proof.harness.valid_stream.WBlkDefs_valid_stream.seg_E.
Proof.
  destruct Zstd.proof.harness.writer.WB_blkE_M.wb_blkE_M as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
  destruct Zstd.proof.harness.writer.WB_blkE_D.wb_blkE_D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  destruct Zstd.proof.harness.writer.WB_blkE_S.wb_blkE_S as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  destruct Zstd.proof.harness.writer.WB_blkE_B.wb_blkE_B as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  destruct Zstd.proof.harness.writer.WB_blkE_C.wb_blkE_C as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  exact (conj (Zstd.proof.harness.detect.WB_blk_E_detect.seg_E_of Zstd.proof.harness.detect.WB_blk_E_detect.segE_H_ok M1 D1 S1 B1 C1)
    (conj (Zstd.proof.harness.stable_out.WB_blk_E_stable_out.seg_E_of Zstd.proof.harness.stable_out.WB_blk_E_stable_out.segE_H_ok M2 D2 S2 B2 C2)
    (conj (Zstd.proof.harness.valid_dict.WB_blk_E_valid_dict.seg_E_of Zstd.proof.harness.valid_dict.WB_blk_E_valid_dict.segE_H_ok M3 D3 S3 B3 C3)
    (conj (Zstd.proof.harness.valid_dict_copy.WB_blk_E_valid_dict_copy.seg_E_of Zstd.proof.harness.valid_dict_copy.WB_blk_E_valid_dict_copy.segE_H_ok M4 D4 S4 B4 C4)
    (conj (Zstd.proof.harness.valid_info.WB_blk_E_valid_info.seg_E_of Zstd.proof.harness.valid_info.WB_blk_E_valid_info.segE_H_ok M5 D5 S5 B5 C5)
    (conj (Zstd.proof.harness.valid_oneshot.WB_blk_E_valid_oneshot.seg_E_of Zstd.proof.harness.valid_oneshot.WB_blk_E_valid_oneshot.segE_H_ok M6 D6 S6 B6 C6)
    (Zstd.proof.harness.valid_stream.WB_blk_E_valid_stream.seg_E_of Zstd.proof.harness.valid_stream.WB_blk_E_valid_stream.segE_H_ok M7 D7 S7 B7 C7))))))).
Qed.
