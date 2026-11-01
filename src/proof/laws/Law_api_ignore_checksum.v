(* The law api_ignore_checksum (harness/api_ignore_checksum.c; its first comment is the claim): the program of the
   harness linked with all units is safe.  `suite` (src/contracts/suite.v) uses this lemma. *)
Require Import QuickProof.Contract.
Require Zstd.contracts.api_ignore_checksum.

Require Import VST.floyd.proofauto.
Require Zstd.proof.top.ZstdOK6 Zstd.proof.zstd.Gprog Zstd.proof.zstd.Spec_xxh Zstd.proof.libc.LibcAllBodies.
Require Zstd.proof.asm6.Asm6HV2_api_ignore_checksum.
Require Zstd.proof.harness.api_ignore_checksum.Main_api_ignore_checksum.
Require Zstd.proof.top.Zstd6L0.

Module M := Zstd.proof.harness.api_ignore_checksum.Main_api_ignore_checksum.

(* the harness's API (Spec_api6 and ZSTD_XXH64, which new_frame calls) does not contain memcpy, as the assembly
   requires *)
Lemma api_no_memcpy DC DD : ~ In Zstd.proof.libc.LibcSpec._memcpy (map fst (M.API DC DD)).
Proof.
  intro H. unfold M.API in H. rewrite map_app in H. simpl in H. vm_compute in H.
  repeat (destruct H as [H | H]; [discriminate H |]). exact H.
Qed.

(* As ck_xxh64 assembles its law: the decoder's obligation with its layer L0 exposed (statement of
   Zstd6L0.zstd_ok_L0: the list Int holds Spec_api6's API and ZSTD_XXH64's specification), the libc unit's bodies
   and the harness's obligation *)
Lemma api_ignore_checksum_from_L0 :
  (exists (DC: globals -> val -> Zstd.proof.zstd.Spec_api6.dctx_st -> mpred)
          (DD: globals -> val -> Zstd.proof.zstd.Spec_api6.ddict_st -> mpred) (Int: funspecs),
     Zstd.proof.top.ZstdOK6.ZstdOK Int /\
     Zstd.proof.top.ZstdOK6.api_sub (Zstd.proof.zstd.Spec_api6.Specs_api DC DD) Int /\
     Zstd.proof.top.ZstdOK6.api_sub Zstd.proof.zstd.Gprog.Specs_L0 Int) ->
  harness_safe Zstd.contracts.api_ignore_checksum.whole_prog.
Proof.
  intros (DC & DD & Int & HZ & HI & HL0).
  destruct (M.api_ignore_checksum_ok DC DD) as [Hs W].
  assert (ASUB: Zstd.proof.top.ZstdOK6.api_sub (M.API DC DD) Int).
  { unfold Zstd.proof.top.ZstdOK6.api_sub, M.API in *. apply Forall_app. split; [exact HI |].
    rewrite Forall_forall in HL0. constructor; [| constructor]. apply HL0.
    unfold Zstd.proof.zstd.Gprog.Specs_L0. apply in_or_app; right. apply in_or_app; right.
    unfold Zstd.proof.zstd.Spec_xxh.Specs_xxh.
    repeat match goal with
           | |- In ?a (?b :: _) => tryif constr_eq a b then (left; reflexivity) else right
           end. }
  exact (Zstd.proof.asm6.Asm6HV2_api_ignore_checksum.safe_api_ignore_checksum Int (M.API DC DD) HZ ASUB
           (api_no_memcpy DC DD) Zstd.proof.libc.LibcAllBodies.libc_bodies Hs W).
Qed.

Lemma api_ignore_checksum_safe : harness_safe Zstd.contracts.api_ignore_checksum.whole_prog.
Proof.
  exact (api_ignore_checksum_from_L0 Zstd.proof.top.Zstd6L0.zstd_ok_L0).
Qed.
