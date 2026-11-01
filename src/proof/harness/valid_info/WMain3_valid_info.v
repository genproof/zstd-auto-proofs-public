(* MainOK of the unit valid_info: the main of valid_info adapted to API v3.
   The inspection functions it calls kept their v2 specifications up to v3.2's exact FH_err code of getFrameHeader;
   WMain32_valid_info.v is the v2 proof (WMain_valid_info.v) adapted to it. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_info.WTopSpecs_valid_info.
Require Zstd.proof.harness.valid_info.WMain32_valid_info.

Theorem main_ok3_valid_info : MainOK.
Proof. exact Zstd.proof.harness.valid_info.WMain32_valid_info.main_ok_valid_info. Qed.
