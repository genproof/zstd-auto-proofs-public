(* The law api_split_invariant (harness/api_split_invariant.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_split_invariant.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_split_invariant Zstd.proof.harness.api_split_invariant.Main_api_split_invariant.
Require Zstd.proof.harness.api_split_invariant.SI_Model Zstd.proof.harness.api_split_invariant.SI_Stream.

Module M := Zstd.proof.harness.api_split_invariant.Main_api_split_invariant.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through
   Asm6HV2_api_split_invariant): the decoder's obligation, the libc unit's bodies and the harness's obligation, with
   the API Spec_api6.Specs_api and ZSTD_XXH64_spec (new_frame hashes its content with ZSTD_XXH64); the decoder's
   list Int holds both: Spec_api6's specifications and those of the layer L0 (the shape of Zstd6L0.zstd_ok_L0).
   The harness's obligation takes the facts of the series' model (SI_Model) and of stream_all's trace
   (SI_Stream). *)
Lemma api_split_invariant_from :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.api_split_invariant.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HA & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub (M.API DC DD) Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub, M.API in *. apply Forall_app. split; [exact HA |].
    rewrite Forall_forall in HL0. constructor; [| constructor].
    apply HL0.
    unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
    unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
    repeat match goal with
           | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
           end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (M.API DC DD))).
  { assert (B: existsb (Pos.eqb Zstd.proof.libc.LibcSpec._memcpy) (map fst (M.API DC DD)) = false)
      by (vm_compute; reflexivity).
    intro Hin. assert (E: existsb (Pos.eqb Zstd.proof.libc.LibcSpec._memcpy) (map fst (M.API DC DD)) = true)
      by (apply existsb_exists; exists Zstd.proof.libc.LibcSpec._memcpy; split; [exact Hin | apply Pos.eqb_refl]).
    congruence. }
  exact (Zstd.proof.asm6.Asm6HV2_api_split_invariant.safe_api_split_invariant Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _
           (M.api_split_invariant_ok_from DC DD Zstd.proof.harness.api_split_invariant.SI_Stream.si_stream
              (Zstd.proof.harness.api_split_invariant.SI_Model.si_decode
                 Zstd.proof.harness.api_split_invariant.SI_Model.si_sk_size)
              Zstd.proof.harness.api_split_invariant.SI_Model.si_sk_size)).
Qed.

Lemma api_split_invariant_safe : harness_safe Zstd.contracts.api_split_invariant.whole_prog.
Proof.
  exact (api_split_invariant_from Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
