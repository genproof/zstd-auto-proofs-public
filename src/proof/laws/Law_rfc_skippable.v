(* The law rfc_skippable (harness/rfc_skippable.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.rfc_skippable.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_rfc_skippable Zstd.proof.harness.rfc_skippable.Main_rfc_skippable.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through Asm6HV2_rfc_skippable):
   the decoder's obligation, the libc unit's bodies and the harness's obligation, with the API
   [ZSTD_decompress_spec; ZSTD_getErrorCode_spec; ZSTD_XXH64_spec] (Main_rfc_skippable.API).  The decoder's list
   Int holds them (the first two are in Spec_api6.Specs_api, the third in Gprog.Specs_L0); the law follows from
   any decoder obligation of the form of Zstd6L0.zstd_ok_L0. *)
Lemma rfc_skippable_from :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.rfc_skippable.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.harness.rfc_skippable.Main_rfc_skippable.API Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub in *. rewrite Forall_forall in HA, HL0.
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply HA. unfold Zstd.proof.zstd.Spec_api6.Specs_api.
      repeat match goal with
             | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
             end.
    - apply HA. unfold Zstd.proof.zstd.Spec_api6.Specs_api.
      repeat match goal with
             | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
             end.
    - apply HL0.
      unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
      unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
      repeat match goal with
             | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
             end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy
                  (map fst Zstd.proof.harness.rfc_skippable.Main_rfc_skippable.API)).
  { simpl. intros [H | [H | [H | []]]]; vm_compute in H; discriminate H. }
  exact (Zstd.proof.asm6.Asm6HV2_rfc_skippable.safe_rfc_skippable Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _ Zstd.proof.harness.rfc_skippable.Main_rfc_skippable.rfc_skippable_ok).
Qed.

Lemma rfc_skippable_safe : harness_safe Zstd.contracts.rfc_skippable.whole_prog.
Proof. exact (rfc_skippable_from Zstd.proof.top.Zstd6L0.zstd_ok_L0). Qed.
