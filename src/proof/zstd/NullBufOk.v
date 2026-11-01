(* The buffer witness of the base a body computes with for a buffer that may be NULL (NullBuf.nbase): the caller's
   buf_ok for a pointer, the lent part of ZSTD_emptyBuffer (NullBuf.eb_wit) for an empty buffer passed as NULL.
   Used by ZSTD_decompressStream's and ZSTD_decompressMultiFrame's proofs. *)
Require Import Zstd.proof.zstd.Spec_api6 Zstd.proof.zstd.NullBuf.
Local Open Scope logic.

Lemma buf_ok_base : forall gv shw W sh cap dst,
  readable_share shw -> (dst = nullval -> cap = 0) -> buf_ok W sh cap dst ->
  buf_ok (eb_wit gv shw :: W) sh cap (nbase gv dst).
Proof.
  intros gv shw W sh cap dst Hr Hc H.
  destruct (nbase_cases gv dst) as [[Hn ->] | [Hn ->]].
  - apply buf_ok_cons; exact H.
  - subst dst. rewrite (Hc eq_refl). apply buf_ok_eb; exact Hr.
Qed.
