(* ZSTD_decompressDCtx against its full specification, with its exact result (Spec_api6.oneshot_exact, the last
   PROP of ZSTD_decompressDCtx_spec).

   From the configuration of a new context (Spec_api6.fresh_cfg: no dictionary, default parameters, no DDict set,
   buffered output), ZSTD_decompressDCtx returns model/Exact.v's os_res on its input and capacity: an error iff
   os_res fails, else exactly its content (up to a memory-allocation error).  The proof goes through the exact
   postconditions of ZSTD_decompress_usingDDict, ZSTD_decompressMultiFrame and ZSTD_decompressFrame
   (model/ExFrame.v's x_series over the block layer's block_exact, DecIface).  The body is proved in O3DCtxDef.v
   given the lending of the context's dictionary resources, whose cases are O3DCtx.v's dctx_cases_of. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3DCtx.
Local Open Scope logic.

Section Exact.
Context {CMI: cmem_preds}.
(* the body of ZSTD_decompressDCtx against its full specification, for any tables and stream relations *)
Lemma body_decompressDCtx3_exact :
  FS3_body (fun DENT TABS SR BR => ZSTD_decompressDCtx_spec (DC3x DENT TABS SR BR) (DD3x DENT)).
Proof.
  intros DENT TABS SR BR _ _. apply body_decompressDCtx3_of. apply dctx_cases_of.
Qed.

End Exact.
