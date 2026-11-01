(* A compressed block the exact model decodes (Exact.xblock) keeps the repeat offsets in [1, 2^32) and the sequence
   tables' codes within the format's (ExAgreeDefs.reps_ok, of_ok).  New offsets are below 2^32 (the OF codes are at
   most MaxOff), ZSTD_decodeSequence maps an invalid repeat offset to (size_t)-1, which later sequences of the block
   may decrement but never to a multiple of 2^32 (the context stores the U32 truncation), and the tables a sequences header builds have codes within MaxLL, MaxOff, MaxML.

   Every block of a one-shot frame therefore starts with nonzero repeat offsets, which is what
   ExBlockIndep.xblock_indep needs to show the block does not depend on litExtraBuffer's stale bytes.  The body must
   hold bytes (as every input zstd reads does): a negative "byte" would pass the sequences header's symbol check.
   The proof is in ExBlockRepsKit.v.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExBlockRepsKit.
Local Open Scope Z_scope.

Lemma xblock_reps (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  bytes_ok body -> reps_ok (x_rep xhuf st) -> of_ok (x_seq xhuf st) ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  reps_ok (x_rep xhuf st') /\ of_ok (x_seq xhuf st').
Proof. exact (xblock_reps_bytes st st' mem m' ps op ds de body bsm cap str n). Qed.
