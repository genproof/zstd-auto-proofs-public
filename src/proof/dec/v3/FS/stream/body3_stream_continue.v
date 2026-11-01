(* FS3 streaming: the body of ZSTD_decompressContinue against its streaming specification, the exact claim included
   (S3Specs.cont_exact: the call is ExStream.d_continue on any model state the frame fields and the tables represent).
   The proof is in stream/cont/ (C3Base .. C3Main; the exact part: C3XModel, C3XDefs, C3XKit, C3XHdr, C3XBlk,
   C3XDec); stuck_gap / dd_gap hold since the stream relation's revision R1a. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Base.
Require Import Zstd.proof.dec.v3.FS.stream.cont.C3Main.
Local Open Scope logic.

Section CM_body3_stream_continue_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma body3_stream_continue : stream_body3 (fun DENT TABS BR => ZSTD_decompressContinue_spec3 DENT TABS).
Proof.
  exact (body3_stream_continue_gen stuck_gap_holds dd_gap_holds).
Qed.

End CM_body3_stream_continue_1.
