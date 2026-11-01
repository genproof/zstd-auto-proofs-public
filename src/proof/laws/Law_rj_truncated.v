(* The law rj_truncated (harness/rj_truncated.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.rj_truncated.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_rj_truncated Zstd.proof.harness.rj_truncated.Main_rj_truncated.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through Asm6HV2_rj_truncated):
   the decoder's obligation, the libc unit's bodies and the harness's obligation, with the API
   Main_rj_truncated.API DC DD (ZSTD_isError, ZSTD_getErrorCode, ZSTD_decompress, ZSTD_createDStream,
   ZSTD_decompressStream, ZSTD_XXH64) for the decoder's own DC, DD.  The decoder's list Int holds them all (the
   statement of Zstd6L0.zstd_ok_L0: the first five are in Spec_api6.Specs_api, the last in Gprog.Specs_L0). *)
Lemma rj_truncated_from :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.rj_truncated.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.harness.rj_truncated.Main_rj_truncated.API DC DD) Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub in *. rewrite Forall_forall in HA, HL0.
    unfold Zstd.proof.harness.rj_truncated.Main_rj_truncated.API.
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
                  (map fst (Zstd.proof.harness.rj_truncated.Main_rj_truncated.API DC DD))).
  { simpl. intros H. repeat destruct H as [H | H]; try (vm_compute in H; discriminate H). exact H. }
  exact (Zstd.proof.asm6.Asm6HV2_rj_truncated.safe_rj_truncated Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           (Zstd.proof.harness.rj_truncated.Main_rj_truncated.rj_truncated_ok DC DD)).
Qed.

Lemma rj_truncated_safe : harness_safe Zstd.contracts.rj_truncated.whole_prog.
Proof. exact (rj_truncated_from Zstd.proof.top.Zstd6L0.zstd_ok_L0). Qed.
