(* The law api_short_output (harness/api_short_output.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_short_output.

Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_short_output.
Require Zstd.proof.harness.api_short_output.Main_api_short_output.

(* The API of the harness, [ZSTD_decompress_spec; ZSTD_getErrorCode_spec; ZSTD_XXH64_spec], is in the decoder's
   list Int: ZSTD_decompress from Spec_api6.Specs_api, the other two from Gprog.Specs_L0 (Zstd6L0.zstd_ok_L0) *)
Lemma api_short_output_safe_of :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.api_short_output.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  unfold Zstd.proof.top.ZstdOK6.api_sub in HA, HL0. rewrite Forall_forall in HA, HL0.
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.harness.api_short_output.Main_api_short_output.API Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub, Zstd.proof.harness.api_short_output.Main_api_short_output.API.
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply HA. unfold Zstd.proof.zstd.Spec_api6.Specs_api. right. right. left. reflexivity.
    - apply HL0. unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app. left.
      unfold Zstd.proof.zstd.Spec_util.Specs_util.
      repeat match goal with
             | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
             end.
    - apply HL0. unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
      unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
      repeat match goal with
             | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
             end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy
                 (map fst Zstd.proof.harness.api_short_output.Main_api_short_output.API)).
  { simpl. intros H. vm_compute in H. repeat (destruct H as [H | H]; [discriminate H |]). exact H. }
  exact (Zstd.proof.asm6.Asm6HV2_api_short_output.safe_api_short_output Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           Zstd.proof.harness.api_short_output.Main_api_short_output.api_short_output_ok).
Qed.

Lemma api_short_output_safe : harness_safe Zstd.contracts.api_short_output.whole_prog.
Proof.
  exact (api_short_output_safe_of Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
