(* FS3 bodies, oneshot3: one-shot API (port of v2 body_FS_oneshot.v and FSSub.v) and the API specifications of
   ZSTD_decompress_usingDDict and ZSTD_freeDDict.
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR).
   The proofs are in oneshot3/ (one body per file: start_function alone takes ~20 s in FS3_G). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3UsingDict Zstd.proof.dec.v3.FS.oneshot3.O3Dec Zstd.proof.dec.v3.FS.oneshot3.O3Sub Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3DCtx Zstd.proof.dec.v3.FS.oneshot3.O3Exact.
Local Open Scope logic.

Section CM_body3_oneshot_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bodies_oneshot3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_decompress_usingDict_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_decompress_usingDDict_int_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_decompressDCtx_spec (DC3x DENT TABS SR BR) (DD3x DENT)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_decompress_spec) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_decompress_usingDDict_int_spec3 DENT TABS) (fun DENT TABS SR BR => ZSTD_decompress_usingDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT)) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_freeDDict_int_spec) (fun DENT TABS SR BR => ZSTD_freeDDict_spec (DD3x DENT)).
Proof.
  split; [ | split; [ | split; [ | split; [ | split]]]]; intros DENT TABS SR BR HD HT.
  - apply body_usingDict3.
  - apply body_usingDDict_int3.
  - apply body_decompressDCtx3_exact; auto.
  - apply body_decompress3.
  - apply usingDDict_sub3; auto.
  - apply freeDDict_sub3; auto.
Qed.

End CM_body3_oneshot_1.
