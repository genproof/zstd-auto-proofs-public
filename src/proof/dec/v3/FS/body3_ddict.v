(* FS3 bodies, ddict3: the DDict functions (port of v2 body_FS_ddict.v; createDDict_advancedP with ctype 2).
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR).
   The bodies are in ddict3/ (one file each, for the per-file check budget). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.ddict3.DDictAdv3 Zstd.proof.dec.v3.FS.ddict3.DDictCreate3r Zstd.proof.dec.v3.FS.ddict3.DDictCreateRef3r Zstd.proof.dec.v3.FS.ddict3.DDictFree3 Zstd.proof.dec.v3.FS.ddict3.DDictID3r Zstd.proof.dec.v3.FS.ddict3.DDictIDSub3r.
Local Open Scope logic.

Section CM_body3_ddict_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bodies_ddict3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_advancedP_spec3 DENT) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_spec (DD3x DENT)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_createDDict_byReference_spec (DD3x DENT)) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_freeDDict_int_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_int_spec) /\
  FS3_sub (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_int_spec)
          (fun DENT TABS SR BR => ZSTD_getDictID_fromDDict_spec (DD3x DENT)).
Proof.
  split; [exact body_createDDict_advancedP | ].
  split; [exact body_createDDict_r | ].
  split; [exact body_createDDict_byReference_r | ].
  split; [exact body_freeDDict | ].
  split; [exact body_getDictID_fromDDict_int | exact getDictID_fromDDict_sub3].
Qed.

End CM_body3_ddict_1.
