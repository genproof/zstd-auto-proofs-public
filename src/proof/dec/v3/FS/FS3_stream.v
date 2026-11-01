(* FS3: streaming: SR, ZSTD_decompressContinue (streaming use), ZSTD_decompressContinueStream,
   ZSTD_decompressStream. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.S3Model Zstd.proof.dec.v3.FS.stream.S3Ret Zstd.proof.dec.v3.FS.stream.body3_stream_main Zstd.proof.dec.v3.FS.stream.body3_stream_continue Zstd.proof.dec.v3.FS.stream.body3_stream_cstream.
Require Import Zstd.proof.dec.v3.FS.stream.S3Exact.
Require Import Zstd.proof.dec.v3.FS.stream.S3Seg_pro Zstd.proof.dec.v3.FS.stream.S3Seg_init Zstd.proof.dec.v3.FS.stream.S3Seg_lh Zstd.proof.dec.v3.FS.stream.S3Seg_read Zstd.proof.dec.v3.FS.stream.S3Seg_load Zstd.proof.dec.v3.FS.stream.S3Seg_flush Zstd.proof.dec.v3.FS.stream.S3Seg_epi.
Local Open Scope logic.

Section CM_FS3_stream_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma MF3_all : MF3.
Proof. exact MF3_ok. Qed.

Lemma STREAM3_ok : STREAM3_obligation.
Proof.
intros DENT TABS HD HT.
exists SR3, (stream_ss3 DENT TABS).
split; [apply stream_ss3_ids |].
intros BR.
constructor.
{ exact (body3_stream_exact DENT TABS BR HD HT). }
constructor; [exact (body3_stream_continue DENT TABS BR HD HT) |].
constructor; [exact (body3_stream_cstream DENT TABS BR HD HT) |].
constructor.
Qed.

End CM_FS3_stream_1.
