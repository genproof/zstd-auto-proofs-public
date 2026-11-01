(* The law rj_reserved_block (harness/rj_reserved_block.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.rj_reserved_block.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_rj_reserved_block Zstd.proof.harness.rj_reserved_block.Main_rj_reserved_block.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through
   Asm6HV2_rj_reserved_block): the decoder's obligation, the libc unit's bodies and the harness's obligation, with
   the API [ZSTD_isError; ZSTD_getErrorCode; ZSTD_decompress; ZSTD_createDStream; ZSTD_decompressStream;
   ZSTD_XXH64] (new_frame hashes its content with ZSTD_XXH64); the decoder's list Int holds all of them: Spec_api6's
   and those of the layer L0 (the shape of Zstd6L0.zstd_ok_L0). *)
Lemma rj_reserved_block_from :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.rj_reserved_block.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub
                  (Zstd.proof.harness.rj_reserved_block.Main_rj_reserved_block.API DC DD) Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub in *. rewrite Forall_forall in HA, HL0.
    unfold Zstd.proof.harness.rj_reserved_block.Main_rj_reserved_block.API.
    repeat constructor.
    1-5: apply HA; unfold Zstd.proof.zstd.Spec_api6.Specs_api;
         repeat match goal with
                | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
                end.
    apply HL0.
    unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
    unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
    repeat match goal with
           | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
           end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy
                   (map fst (Zstd.proof.harness.rj_reserved_block.Main_rj_reserved_block.API DC DD))).
  { simpl. intros H. repeat destruct H as [H | H]; try (vm_compute in H; discriminate H); exact H. }
  exact (Zstd.proof.asm6.Asm6HV2_rj_reserved_block.safe_rj_reserved_block Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           (Zstd.proof.harness.rj_reserved_block.Main_rj_reserved_block.rj_reserved_block_ok DC DD)).
Qed.

Lemma rj_reserved_block_safe : harness_safe Zstd.contracts.rj_reserved_block.whole_prog.
Proof.
  exact (rj_reserved_block_from Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
