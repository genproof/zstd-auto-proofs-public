(* The law api_flush_bound (harness/api_flush_bound.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_flush_bound.

Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_flush_bound.
Require Zstd.proof.harness.api_flush_bound.Main_api_flush_bound.

(* the decoder's API (Spec_api6) does not contain memcpy, as the assembly requires *)
Lemma api_no_memcpy DC DD : ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (Zstd.proof.zstd.Spec_api6.Specs_api DC DD)).
Proof.
  intro H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* as suite_x assembles the x_ laws: the decoder's obligation (Zstd6), the libc unit's bodies and the
   harness's obligation, all with the API of Spec_api6 *)
Lemma api_flush_bound_safe : harness_safe Zstd.contracts.api_flush_bound.whole_prog.
Proof.
  destruct Zstd.proof.top.Zstd6.zstd_ok as (DC & DD & Int & HZ & HI).
  destruct (Zstd.proof.harness.api_flush_bound.Main_api_flush_bound.api_flush_bound_ok DC DD) as [Hs W].
  exact (Zstd.proof.asm6.Asm6HV2_api_flush_bound.safe_api_flush_bound Int (Zstd.proof.zstd.Spec_api6.Specs_api DC DD)
           HZ HI (api_no_memcpy DC DD) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.
