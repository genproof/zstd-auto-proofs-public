(* The law res_free (harness/res_free.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.res_free.

Require Import VST.floyd.proofauto.
Require Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_res_free.
Require Zstd.proof.harness.res_free.Main_res_free.
Require Zstd.proof.top.Zstd6.
Import Zstd.proof.zstd.CMem.

(* the decoder's API (Spec_api6) does not contain memcpy, as the assembly requires *)
Lemma api_no_memcpy DC DD (CMI: cmem_preds) :
  ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD CMI)).
Proof.
  intro H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* as suite_x assembles the x_ laws: the decoder's obligation for contexts with the harness's counting allocator
   (an API whose contexts let the harness read the allocator's state), the libc unit's bodies and the harness's
   obligation (Main_res_free.res_free_ok) *)
Lemma res_free_safe_of :
  (exists DC DD Int, Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub
       (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD Zstd.proof.harness.res_free.Alloc_res_free.count_cm) Int /\
     @Zstd.proof.zstd.Spec_api6.dc_cm_ok DC Zstd.proof.harness.res_free.Alloc_res_free.count_cm) ->
  harness_safe Zstd.contracts.res_free.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HI & HM).
  destruct (Zstd.proof.harness.res_free.Main_res_free.res_free_ok DC DD HM) as [Hs W].
  exact (Zstd.proof.asm6.Asm6HV2_res_free.safe_res_free Int
           (@Zstd.proof.zstd.Spec_api6.Specs_api DC DD Zstd.proof.harness.res_free.Alloc_res_free.count_cm)
           HZ HI (api_no_memcpy DC DD _) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.

(* the decoder's obligation for contexts with their own allocator (Zstd6.zstd_ok_cm), at the harness's counting
   allocator *)
Lemma res_free_safe : harness_safe Zstd.contracts.res_free.whole_prog.
Proof.
  exact (res_free_safe_of (@Zstd.proof.top.Zstd6.zstd_ok_cm Zstd.proof.harness.res_free.Alloc_res_free.count_cm)).
Qed.
