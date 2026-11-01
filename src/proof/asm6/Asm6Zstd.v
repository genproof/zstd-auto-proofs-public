(* The decoder unit as a VSU Component, for any whole-program compspecs CSW containing its own.
   Never unfolds a specification beyond its identifier and calling convention. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import Zstd.proof.asm6.Asm6Lib Zstd.proof.asm6.Asm6CS.
Require Zstd.units.
Import compcert.lib.Maps.

Lemma OK_Zstd : QPprogram_OK Zstd.units.Zstd.qp.
Proof.
  split; [apply compute_list_norepet_e; reflexivity | ].
  let HA := fresh in let LA := fresh in
  assert (HA: PTree_samedom (@cenv_cs Zstd.units.Zstd.CS) (@ha_env_cs Zstd.units.Zstd.CS)) by repeat constructor;
  assert (LA: PTree_samedom (@cenv_cs Zstd.units.Zstd.CS) (@la_env_cs Zstd.units.Zstd.CS)) by repeat constructor;
  exact (@QPcompspecs_OK_i Zstd.units.Zstd.CS HA LA).
Qed.

Lemma CSeq_Zstd : Zstd.units.Zstd.CS = compspecs_of_QPcomposite_env _ (proj2 OK_Zstd).
Proof. apply (compspecs_eq_of_QPcomposite_env Zstd.units.Zstd.CS Zstd.zstd.code.prog). reflexivity. Qed.

Lemma funs_ok_Zstd : prog_funs_ok Zstd.units.Zstd.CS Zstd.units.Zstd.qp = true.
Proof. Time vm_compute. reflexivity. Qed.

