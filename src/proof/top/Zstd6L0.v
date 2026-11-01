(* The decoder's obligation with the specifications of its layer L0 exposed (Gprog.Specs_L0: the util,
   bits and xxh groups, among them Spec_xxh.ZSTD_XXH64_spec).  A harness that calls ZSTD_XXH64 (law
   ck_xxh64, and the frame writer of harness/frames.h for its checksums) imports it besides the API of
   Spec_api6, which does not list it.  The proof is DecAsm3.dec_assemble3_full's (Int holds Specs_L0 itself:
   Int = memcpy_spec :: Specs_L0 ++ ...), at the default allocator's class cmem_none. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.top.ZstdOK6.
Require Export Zstd.proof.zstd.Spec_api6.
Require Import Zstd.proof.dec.v3.DecAsm3 Zstd.proof.dec.v3.DecH3 Zstd.proof.dec.v3.DecB3 Zstd.proof.dec.v3.DecFS3.
Require Import Zstd.proof.zstd.Gprog.
Import compcert.lib.Maps.

Theorem zstd_ok_L0 :
  exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
    ZstdOK Int /\ api_sub (Specs_api DC DD) Int /\ api_sub Specs_L0 Int.
Proof.
  destruct (dec_assemble3_full H3_ok B3_ok FS3_ok) as (DC & DD & Int & H1 & H2 & _ & H4).
  exists DC, DD, Int. auto.
Qed.

(* As in top/Zstd6: contexts with the default allocator use the instance cmem_none, which CMem exports only to files
   that Import CMem; this makes it available to every file that Requires this one (the law files that assemble
   through zstd_ok_L0). *)
#[global] Existing Instance Zstd.proof.zstd.CMem.cmem_none.
