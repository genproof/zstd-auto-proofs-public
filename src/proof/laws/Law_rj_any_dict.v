(* The law rj_any_dict (harness/rj_any_dict.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.rj_any_dict.

Require Import VST.floyd.proofauto.
Require Zstd.proof.top.Zstd6 Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_rj_any_dict.
Require Zstd.proof.harness.rj_any_dict.Main_rj_any_dict.
Import Zstd.proof.zstd.Spec_api6.

(* the decoder's API does not contain memcpy, as the assembly requires *)
Lemma api_no_memcpy DC DD : ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (Specs_api DC DD)).
Proof.
  intro H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* as suite_x assembles the x_ laws: the decoder's obligation, the libc unit's bodies and the harness's
   obligation, all with the decoder's API *)
Lemma rj_any_dict_from :
  (exists (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\ Zstd.proof.top.ZstdOK6.api_sub (Specs_api DC DD) Int) ->
  harness_safe Zstd.contracts.rj_any_dict.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HI).
  destruct (Zstd.proof.harness.rj_any_dict.Main_rj_any_dict.rj_any_dict_ok DC DD) as [Hs W].
  exact (Zstd.proof.asm6.Asm6HV2_rj_any_dict.safe_rj_any_dict Int (Specs_api DC DD)
           HZ HI (api_no_memcpy DC DD) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.

Lemma rj_any_dict_safe : harness_safe Zstd.contracts.rj_any_dict.whole_prog.
Proof. exact (rj_any_dict_from Zstd.proof.top.Zstd6.zstd_ok). Qed.
