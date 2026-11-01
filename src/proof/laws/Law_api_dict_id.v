(* The law api_dict_id (harness/api_dict_id.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_dict_id.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_dict_id Zstd.proof.harness.api_dict_id.Main_api_dict_id.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through Asm6HV2_api_dict_id): the
   decoder's obligation, the libc unit's bodies and the harness's obligation, with the API
   [ZSTD_getDictID_fromFrame_spec; ZSTD_XXH64_spec] (Main_api_dict_id.API).  The decoder's list Int holds both
   (Zstd6L0.zstd_ok_L0: the first is in Spec_api6.Specs_api, the second in Gprog.Specs_L0). *)
Lemma api_dict_id_safe : harness_safe Zstd.contracts.api_dict_id.whole_prog.
Proof.
  destruct Zstd.proof.top.Zstd6L0.zstd_ok_L0 as (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.harness.api_dict_id.Main_api_dict_id.API Int).
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
                  (map fst Zstd.proof.harness.api_dict_id.Main_api_dict_id.API)).
  { simpl. intros [H | [H | []]]; vm_compute in H; discriminate H. }
  exact (Zstd.proof.asm6.Asm6HV2_api_dict_id.safe_api_dict_id Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _ Zstd.proof.harness.api_dict_id.Main_api_dict_id.api_dict_id_ok).
Qed.
