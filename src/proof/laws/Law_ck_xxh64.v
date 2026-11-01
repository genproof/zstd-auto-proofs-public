(* The law ck_xxh64 (harness/ck_xxh64.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.ck_xxh64.
Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6L0 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_ck_xxh64 Zstd.proof.harness.ck_xxh64.Main_ck_xxh64.

(* As suite_x assembles a law (the generic assembly Asm6GenericV2.law_safe, here through Asm6HV2_ck_xxh64): the
   decoder's obligation, the libc unit's bodies and the harness's obligation, with the API [ZSTD_XXH64_spec]; the
   decoder's list Int holds that specification (Zstd6L0.zstd_ok_L0: Int contains Gprog.Specs_L0). *)
Lemma ck_xxh64_safe : harness_safe Zstd.contracts.ck_xxh64.whole_prog.
Proof.
  destruct Zstd.proof.top.Zstd6L0.zstd_ok_L0 as (DC & DD & Int & HZ & _ & HL0).
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.harness.ck_xxh64.Specs_ck_xxh64.API Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub in *. rewrite Forall_forall in HL0.
    constructor; [| constructor]. apply HL0.
    unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
    unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
    repeat match goal with
           | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
           end. }
  assert (NMC: ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst Zstd.proof.harness.ck_xxh64.Specs_ck_xxh64.API)).
  { simpl. intros [H | []]. vm_compute in H. discriminate H. }
  exact (Zstd.proof.asm6.Asm6HV2_ck_xxh64.safe_ck_xxh64 Int _ HZ ASUB NMC
           Zstd.proof.libc.LibcAllBodies.libc_bodies _ Zstd.proof.harness.ck_xxh64.Main_ck_xxh64.ck_xxh64_ok).
Qed.
