(* ZSTD_decompressStream against its full specification (Spec_api6.ZSTD_decompressStream_spec, whose last PROP is
   stream_exact).

   From the configuration of a new context (Spec_api6.fresh_cfg, with dc_ex: the stream is what its calls since the
   context was new or reset with the parameters did to a clean context), a call returns model/Exact.v's zs_call on
   the calls before it (ss_calls) and its own input and room: the return value, the input consumed, the bytes
   delivered and the hostage byte, and the next abstract state (up to a memory-allocation error).  The context's
   representation carries the exact relation (FSRep3.ex_on3 with S3XRel.xrel3: the concrete stream state is
   model/ExStream.v's image of ss_calls); the loop invariant carries the model's loop (S3Main.ex_call); the body is
   assembled (body3_stream_main.v) from the prologue, the five cases of the switch and the epilogue with that
   claim (S3Seg_*.v), the error returns from RET3x (S3Ret.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.dec.v3.FS.stream.S3Model Zstd.proof.dec.v3.FS.stream.S3Ret.
Require Import Zstd.proof.dec.v3.FS.stream.body3_stream_main.
Require Import Zstd.proof.dec.v3.FS.stream.S3Seg_pro Zstd.proof.dec.v3.FS.stream.S3Seg_init Zstd.proof.dec.v3.FS.stream.S3Seg_lh Zstd.proof.dec.v3.FS.stream.S3Seg_read Zstd.proof.dec.v3.FS.stream.S3Seg_load Zstd.proof.dec.v3.FS.stream.S3Seg_flush Zstd.proof.dec.v3.FS.stream.S3Seg_epi.
Local Open Scope logic.

Section Exact.
Context {CMI: cmem_preds}.

(* the cases of the switch with the exact claim (each falls through to the next) *)
Lemma seg3_cases_x : forall k, 0 <= k <= 4 -> seg_case_x k.
Proof.
pose proof MF3_ok as M. pose proof RET3x_ok as T.
assert (H4: seg_case_x 4) by exact (seg_flush_x_ok M T).
assert (H3: seg_case_x 3) by exact (seg_load_x_ok M T).
assert (H2: seg_case_x 2) by exact (seg_read_x_ok M T H3).
assert (H1: seg_case_x 1) by exact (seg_lh_x_ok M T H2).
assert (H0: seg_case_x 0) by exact (seg_init_x_ok M T H1).
intros k Hk.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as Hc by lia.
destruct Hc as [->|[->|[->|[->| ->]]]]; assumption.
Qed.

(* the body of ZSTD_decompressStream against its full specification, with the stream relation SR3 *)
Lemma body3_stream_exact :
  stream_body3 (fun DENT TABS BR => ZSTD_decompressStream_spec (DC3x DENT TABS SR3 BR) (DD3x DENT)).
Proof.
apply body3_stream_main_of_segs.
- exact (seg_prologue_x_ok MF3_ok RET3x_ok).
- exact seg3_cases_x.
- exact (seg_epilogue_x_ok MF3_ok RET3x_ok).
Qed.

End Exact.
