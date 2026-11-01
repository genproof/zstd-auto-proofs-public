(* The law api_content_size (harness/api_content_size.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_content_size.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_content_size Zstd.proof.harness.api_content_size.Main_api_content_size.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through
   Asm6HV2_api_content_size): the decoder's obligation, the libc unit's bodies and the harness's obligation, with
   the API [ZSTD_getFrameContentSize_spec; ZSTD_XXH64_spec] (new_frame hashes its content with ZSTD_XXH64); the
   decoder's list Int holds both specifications: Spec_api6's and those of the layer L0 (the shape of
   Zstd6L0.zstd_ok_L0). *)
Lemma api_content_size_from :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.api_content_size.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.harness.api_content_size.Main_api_content_size.API Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub in *. rewrite Forall_forall in HA, HL0.
    constructor; [| constructor; [| constructor]].
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
                   (map fst Zstd.proof.harness.api_content_size.Main_api_content_size.API)).
  { simpl. intros [H | [H | []]]; vm_compute in H; discriminate H. }
  exact (Zstd.proof.asm6.Asm6HV2_api_content_size.safe_api_content_size Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           Zstd.proof.harness.api_content_size.Main_api_content_size.api_content_size_ok).
Qed.

Lemma api_content_size_safe : harness_safe Zstd.contracts.api_content_size.whole_prog.
Proof.
  exact (api_content_size_from Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
