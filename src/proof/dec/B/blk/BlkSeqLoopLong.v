(* LOOP: the long loop (any literals; 8 sequences decoded ahead in sequences[8], ZSTD_prefetchMatch).
   ZSTD_decompressSequencesLong_body gets the dispatchers' seqs_spec (BlkIface) itself, in the loop bodies' context LOOP_GB
   (BlkSeqLoopCommon); BlkSeqLOOP.LOOP_ok lifts it.  The assembly from the segments: BlkSeqLoopLongAsm; the exact model's
   steps: BlkSeqLoopLongX. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongAsm.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongTabs Zstd.proof.dec.B.blk.BlkSeqLoopLongDstep Zstd.proof.dec.B.blk.BlkSeqLoopLongPro Zstd.proof.dec.B.blk.BlkSeqLoopLongInit Zstd.proof.dec.B.blk.BlkSeqLoopLongAdv Zstd.proof.dec.B.blk.BlkSeqLoopLongMain Zstd.proof.dec.B.blk.BlkSeqLoopLongFin Zstd.proof.dec.B.blk.BlkSeqLoopLongEnd Zstd.proof.dec.B.blk.BlkSeqLoopLongEpi.
Local Open Scope logic.

Lemma body_ZSTD_decompressSequencesLong_body :
  GLOBALS_obligation ->
  semax_body Vprog LOOP_GB f_ZSTD_decompressSequencesLong_body (_ZSTD_decompressSequencesLong_body, seqs_spec (fun _ => True)).
Proof.
  intros HG. destruct lg_tabs_ok as (TI & TE & TB). destruct lg_endreps_ok as (SEND & SREPS).
  exact (long_body_of_segs TI TE TB lg_dstep_ok lg_pro_ok lg_init_ok lg_adv_ok lg_main_ok SEND lg_fin_ok SREPS lg_epi_ok HG).
Qed.
