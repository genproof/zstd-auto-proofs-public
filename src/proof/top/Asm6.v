(* The assembly: each law of suite from the proof obligations of its units.
   Generic in every specification: the decoder's list Int (ZstdOK), the API a harness imports (any
   sublist of Int), the harness's helper specifications Hs (HarnessOK).  The malloc unit has no
   obligation (its only function is a placeholder; malloc/free are externals of QuickProof.Env).
   Each law comes from its src/proof/asm6/Asm6HV2_<h>.v and the generic Asm6GenericV2.law_safe. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Contract.
Require Import Zstd.proof.top.ZstdOK6.
Require Import Zstd.proof.libc.LibcBodies.
Require Zstd.proof.harness.any_bufferless.HOK_any_bufferless.
Require Zstd.proof.harness.any_dict.HOK_any_dict.
Require Zstd.proof.harness.any_dict_copy.HOK_any_dict_copy.
Require Zstd.proof.harness.any_info.HOK_any_info.
Require Zstd.proof.harness.any_info_extra.HOK_any_info_extra.
Require Zstd.proof.harness.any_oneshot.HOK_any_oneshot.
Require Zstd.proof.harness.any_params.HOK_any_params.
Require Zstd.proof.harness.any_stream.HOK_any_stream.
Require Zstd.proof.harness.bound.HOK_bound.
Require Zstd.proof.harness.detect.HOK_detect.
Require Zstd.proof.harness.stable_out.HOK_stable_out.
Require Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.
Require Zstd.proof.harness.valid_dict.HOK_valid_dict.
Require Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.
Require Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.
Require Zstd.proof.harness.valid_info.HOK_valid_info.
Require Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.
Require Zstd.proof.harness.valid_params.HOK_valid_params.
Require Zstd.proof.harness.valid_stream.HOK_valid_stream.
Require Zstd.proof.asm6.Asm6HV2_any_bufferless.
Require Zstd.proof.asm6.Asm6HV2_any_dict.
Require Zstd.proof.asm6.Asm6HV2_any_dict_copy.
Require Zstd.proof.asm6.Asm6HV2_any_info.
Require Zstd.proof.asm6.Asm6HV2_any_info_extra.
Require Zstd.proof.asm6.Asm6HV2_any_oneshot.
Require Zstd.proof.asm6.Asm6HV2_any_params.
Require Zstd.proof.asm6.Asm6HV2_any_stream.
Require Zstd.proof.asm6.Asm6HV2_bound.
Require Zstd.proof.asm6.Asm6HV2_detect.
Require Zstd.proof.asm6.Asm6HV2_stable_out.
Require Zstd.proof.asm6.Asm6HV2_valid_bufferless.
Require Zstd.proof.asm6.Asm6HV2_valid_dict.
Require Zstd.proof.asm6.Asm6HV2_valid_dict_api.
Require Zstd.proof.asm6.Asm6HV2_valid_dict_copy.
Require Zstd.proof.asm6.Asm6HV2_valid_info.
Require Zstd.proof.asm6.Asm6HV2_valid_oneshot.
Require Zstd.proof.asm6.Asm6HV2_valid_params.
Require Zstd.proof.asm6.Asm6HV2_valid_stream.
Require Zstd.contracts.x_any_bufferless.
Require Zstd.contracts.x_any_dict.
Require Zstd.contracts.x_any_dict_copy.
Require Zstd.contracts.x_any_info.
Require Zstd.contracts.x_any_info_extra.
Require Zstd.contracts.x_any_oneshot.
Require Zstd.contracts.x_any_params.
Require Zstd.contracts.x_any_stream.
Require Zstd.contracts.x_bound.
Require Zstd.contracts.x_detect.
Require Zstd.contracts.x_stable_out.
Require Zstd.contracts.x_valid_bufferless.
Require Zstd.contracts.x_valid_dict.
Require Zstd.contracts.x_valid_dict_api.
Require Zstd.contracts.x_valid_dict_copy.
Require Zstd.contracts.x_valid_info.
Require Zstd.contracts.x_valid_oneshot.
Require Zstd.contracts.x_valid_params.
Require Zstd.contracts.x_valid_stream.

Theorem assembly :
  forall (Int API: funspecs),
  ZstdOK Int -> api_sub API Int -> ~ In _memcpy (map fst API) -> LibcBodies ->
  (forall Hs, Zstd.proof.harness.any_bufferless.HOK_any_bufferless.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_bufferless.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_dict.HOK_any_dict.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_dict.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_dict_copy.HOK_any_dict_copy.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_dict_copy.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_info.HOK_any_info.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_info.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_info_extra.HOK_any_info_extra.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_info_extra.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_oneshot.HOK_any_oneshot.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_oneshot.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_params.HOK_any_params.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_params.whole_prog) /\
  (forall Hs, Zstd.proof.harness.any_stream.HOK_any_stream.HarnessOK API Hs -> harness_safe Zstd.contracts.x_any_stream.whole_prog) /\
  (forall Hs, Zstd.proof.harness.bound.HOK_bound.HarnessOK API Hs -> harness_safe Zstd.contracts.x_bound.whole_prog) /\
  (forall Hs, Zstd.proof.harness.detect.HOK_detect.HarnessOK API Hs -> harness_safe Zstd.contracts.x_detect.whole_prog) /\
  (forall Hs, Zstd.proof.harness.stable_out.HOK_stable_out.HarnessOK API Hs -> harness_safe Zstd.contracts.x_stable_out.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_bufferless.HOK_valid_bufferless.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_bufferless.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_dict.HOK_valid_dict.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_dict.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_dict_api.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_dict_copy.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_info.HOK_valid_info.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_info.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_oneshot.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_params.HOK_valid_params.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_params.whole_prog) /\
  (forall Hs, Zstd.proof.harness.valid_stream.HOK_valid_stream.HarnessOK API Hs -> harness_safe Zstd.contracts.x_valid_stream.whole_prog).
Proof.
  intros Int API ZOK ASUB NMC LB.
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_bufferless.safe_any_bufferless Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_dict.safe_any_dict Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_dict_copy.safe_any_dict_copy Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_info.safe_any_info Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_info_extra.safe_any_info_extra Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_oneshot.safe_any_oneshot Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_params.safe_any_params Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_any_stream.safe_any_stream Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_bound.safe_bound Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_detect.safe_detect Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_stable_out.safe_stable_out Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_bufferless.safe_valid_bufferless Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_dict.safe_valid_dict Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_dict_api.safe_valid_dict_api Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_dict_copy.safe_valid_dict_copy Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_info.safe_valid_info Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_oneshot.safe_valid_oneshot Int API ZOK ASUB NMC LB) |].
  split; [exact (Zstd.proof.asm6.Asm6HV2_valid_params.safe_valid_params Int API ZOK ASUB NMC LB) |].
  exact (Zstd.proof.asm6.Asm6HV2_valid_stream.safe_valid_stream Int API ZOK ASUB NMC LB).
Qed.
