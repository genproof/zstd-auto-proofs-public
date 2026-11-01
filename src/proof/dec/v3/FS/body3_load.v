(* FS3 bodies, load3: dictionary loading and referencing (port of v2 body_FS_load.v; ctype 2, the DDict set) and the
   API specifications of the three functions specified internally.
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Pre Zstd.proof.dec.v3.FS.load3.Load3Api Zstd.proof.dec.v3.FS.load3.Load3Init Zstd.proof.dec.v3.FS.load3.Load3Sub Zstd.proof.dec.v3.FS.load3.Load3Ref Zstd.proof.dec.v3.FS.load3.Load3All.
Local Open Scope logic.

Section CM_body3_load_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bodies_load3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_byReference_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_spec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_int_spec3 DENT TABS) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_initDStream_usingDict_aspec (DC3x DENT TABS SR BR)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_initDStream_usingDDict_aspec (DC3x DENT TABS SR BR) (DD3x DENT)) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_int_spec3 DENT TABS) (fun DENT TABS SR BR => ZSTD_DCtx_refDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT)) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS) (fun DENT TABS SR BR => ZSTD_DCtx_loadDictionary_advanced_aspec (DC3x DENT TABS SR BR)) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS) (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_aspec (DC3x DENT TABS SR BR)).
Proof.
  split; [exact body_loadDictionary_advanced3 |].
  split; [exact body_loadDictionary_byReference3 |].
  split; [exact body_loadDictionary3 |].
  split; [exact body_refPrefix_advanced3 |].
  split; [exact body_refPrefix3 |].
  split; [exact body_refDDict_int3 |].
  split; [exact body_initDStream_usingDict3 |].
  split; [exact body_initDStream_usingDDict3 |].
  split; [exact refDDict_sub3 |].
  split; [exact loadDictionary_advanced_sub3 |].
  exact refPrefix_advanced_sub3.
Qed.

End CM_body3_load_1.
