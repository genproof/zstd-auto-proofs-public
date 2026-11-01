(* The law rj_any_stream (harness/rj_any_stream.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.rj_any_stream.

Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_rj_any_stream.
Require Zstd.proof.harness.rj_any_stream.Main_rj_any_stream.

(* the decoder's API (Spec_api6) does not contain memcpy, as the assembly requires *)
Lemma api_no_memcpy DC DD : ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (Zstd.proof.zstd.Spec_api6.Specs_api DC DD)).
Proof.
  intro H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* as suite_x assembles the x_ laws: the decoder's obligation (Zstd6), the libc unit's bodies and the
   harness's obligation, all with the API of Spec_api6 *)
Lemma rj_any_stream_safe : harness_safe Zstd.contracts.rj_any_stream.whole_prog.
Proof.
  destruct Zstd.proof.top.Zstd6.zstd_ok as (DC & DD & Int & HZ & HI).
  destruct (Zstd.proof.harness.rj_any_stream.Main_rj_any_stream.rj_any_stream_ok DC DD) as [Hs W].
  exact (Zstd.proof.asm6.Asm6HV2_rj_any_stream.safe_rj_any_stream Int (Zstd.proof.zstd.Spec_api6.Specs_api DC DD)
           HZ HI (api_no_memcpy DC DD) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.
