(* The harness obligation of harness/any_dict.c under the decoder's API v3.2 (Spec_api6):
   the proof is MainBody_any_dict_v32.v (adapted from MainBody_any_dict_v3.v, the API v3 proof). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_dict.HOK_any_dict.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.any_dict.MainBody_any_dict_v32.

Theorem any_dict_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. exact (Zstd.proof.harness.any_dict.MainBody_any_dict_v32.any_dict_harness_ok DC DD).
Qed.
