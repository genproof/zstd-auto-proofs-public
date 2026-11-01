(* The law api_frame_size (harness/api_frame_size.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_frame_size.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_frame_size Zstd.proof.harness.api_frame_size.Main_api_frame_size.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through Asm6HV2_api_frame_size):
   the decoder's obligation, the libc unit's bodies and the harness's obligation, with the API of Spec_api6 and
   ZSTD_XXH64 (new_frame's checksum).  The decoder's list Int holds all of them: Zstd6L0.zstd_ok_L0 gives the
   API of Spec_api6 and Gprog.Specs_L0, which has ZSTD_XXH64_spec.  Stated for any decoder obligation of
   zstd_ok_L0's form, then applied to it. *)
Lemma api_frame_size_safe_of :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\ Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.api_frame_size.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.harness.api_frame_size.Main_api_frame_size.API DC DD) Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub, Zstd.proof.harness.api_frame_size.Main_api_frame_size.API in *.
    apply Forall_app. split; [exact HA |].
    rewrite Forall_forall in HL0. constructor; [| constructor]. apply HL0.
    unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
    unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
    repeat match goal with
           | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
           end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy
                  (map fst (Zstd.proof.harness.api_frame_size.Main_api_frame_size.API DC DD))).
  { unfold Zstd.proof.harness.api_frame_size.Main_api_frame_size.API.
    rewrite map_app. intro H. simpl in H. vm_compute in H.
    repeat (destruct H as [H | H]; [discriminate H |]). exact H. }
  exact (Zstd.proof.asm6.Asm6HV2_api_frame_size.safe_api_frame_size Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           (Zstd.proof.harness.api_frame_size.Main_api_frame_size.api_frame_size_ok DC DD)).
Qed.

Lemma api_frame_size_safe : harness_safe Zstd.contracts.api_frame_size.whole_prog.
Proof.
  exact (api_frame_size_safe_of Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
