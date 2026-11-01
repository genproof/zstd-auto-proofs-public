(* The law res_memory_stream (harness/res_memory_stream.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.res_memory_stream.

Require Import VST.floyd.proofauto.
Require Import Zstd.proof.top.ZstdOK6.
Require Zstd.proof.top.Zstd6 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_res_memory_stream.
Require Zstd.proof.harness.res_memory_stream.Main_res_memory_stream.

Module AL := Zstd.proof.harness.res_memory_stream.Alloc_res_memory_stream.

(* the decoder's API (Spec_api6) does not contain memcpy, as the assembly requires *)
Lemma api_no_memcpy DC DD :
  ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD AL.count_cm)).
Proof.
  intro H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* as suite_x assembles the x_ laws: the decoder's obligation for contexts with their own allocator (here the
   harness's counting allocator), the libc unit's bodies and the harness's obligation, all with the API of
   Spec_api6 *)
Lemma res_memory_stream_safe_of :
  (exists DC DD Int, ZstdOK Int /\
     api_sub (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD AL.count_cm) Int /\
     @Zstd.proof.zstd.Spec_api6.dc_cm_ok DC AL.count_cm) ->
  harness_safe Zstd.contracts.res_memory_stream.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HI & HCM).
  destruct (Zstd.proof.harness.res_memory_stream.Main_res_memory_stream.res_memory_stream_ok DC DD HCM) as [Hs W].
  exact (Zstd.proof.asm6.Asm6HV2_res_memory_stream.safe_res_memory_stream Int
           (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD AL.count_cm)
           HZ HI (api_no_memcpy DC DD) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.

Lemma res_memory_stream_safe : harness_safe Zstd.contracts.res_memory_stream.whole_prog.
Proof. exact (res_memory_stream_safe_of (@Zstd.proof.top.Zstd6.zstd_ok_cm AL.count_cm)). Qed.
