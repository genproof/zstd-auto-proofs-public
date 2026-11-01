(* The decoder's obligation: some predicates DC (contexts) and DD
   (digested dictionaries) and some list Int of specifications of the decoder unit's functions such that
   every function satisfies its specification (ZstdOK) and implies its API specification of Spec_api6
   (api_sub: up to funspec_sub; the decoder also calls some API functions internally, e.g. usingDDict,
   freeDDict and refDDict, with arguments the API specification does not cover).
   API v3: dec_assemble3 H3_ok B3_ok FS3_ok
   (src/proof/dec/v3/; the v2 proof was dec_assemble H_ok B_ok FS_ok, in src/proof/dec/). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.top.ZstdOK6.
Require Export Zstd.proof.zstd.Spec_api6.
Require Import Zstd.proof.dec.v3.DecAsm3 Zstd.proof.dec.v3.DecH3 Zstd.proof.dec.v3.DecB3 Zstd.proof.dec.v3.DecFS3.

(* for any allocator class of a law (CMem.cmem_preds: contexts with their own allocator, the res_ laws); the contexts
   DC hold their allocator's state, which a law may read between two calls (Spec_api6.dc_cm_ok) *)
Theorem zstd_ok_cm : forall {CMI: cmem_preds},
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
    ZstdOK Int /\ api_sub (Specs_api DC DD) Int /\ dc_cm_ok DC.
Proof.
  intros CMI. exact (dec_assemble3 H3_ok B3_ok FS3_ok).
Qed.

(* the laws whose contexts all have the default allocator (class cmem_none) *)
Theorem zstd_ok :
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
    ZstdOK Int /\ api_sub (Specs_api DC DD) Int.
Proof.
  destruct (@zstd_ok_cm cmem_none) as (DC & DD & Int & Hok & Hapi & _). exists DC, DD, Int. split; assumption.
Qed.

(* The API's specifications are stated for an allocator class (zstd/CMem.v); contexts with the default allocator use
   the instance cmem_none. CMem exports it only to files that Import CMem; this makes it available to every file that
   Requires this one (the law files and the contract suite). *)
#[global] Existing Instance Zstd.proof.zstd.CMem.cmem_none.
