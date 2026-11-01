(* The proof obligation of the harness unit harness/valid_dict.c.

   HarnessOK API Hs: Hs are the specifications of the harness's own functions other than main (in the
   order of helper_ids; chosen by the harness's proof), and every function of the unit (helpers and
   main) satisfies its specification in the context Gprog API Hs, where API are the decoder's
   specifications the harness imports (the top-level theorem takes API = Spec_api6's, which the
   decoder's ZstdOK list must contain).  main's specification is VST's QPmain_spec_ext' of the whole
   program, as WholeComponent_semax_prog requires. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Export Zstd.proof.top.HarnessDefs.
Require Zstd.contracts.x_valid_dict.
Require Export Zstd.harness.x_valid_dict.code.
Import compcert.lib.Maps.

#[export] Instance CompSpecs : compspecs := Zstd.contracts.x_valid_dict.Harness.CS.

(* main sees every global of the whole program *)
Definition Vprog : varspecs := QPvarspecs Zstd.contracts.x_valid_dict.whole_prog.

Definition main_spec : ident * funspec :=
  (_main, QPmain_spec_ext' Zstd.contracts.x_valid_dict.whole_prog tt (fun _ _ => TT)).

(* malloc/free of the environment and the decoder's API (at the decoder's compspecs) *)
Definition Imports (API: funspecs) : funspecs :=
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') :: API.

(* the environment's functions the harness declares, at this unit's compspecs *)
Definition Externals : funspecs := present (ExtIDs Zstd.contracts.x_valid_dict.Harness.qp) env_harness.

(* the harness's own functions besides main *)
Definition helper_ids : list ident :=
  filter (fun i => negb (Pos.eqb i _main)) (IntIDs Zstd.contracts.x_valid_dict.Harness.qp).

Definition Gprog (API Hs: funspecs) : funspecs := Imports API ++ Externals ++ Hs ++ [main_spec].

Definition hbody_ok (G: funspecs) (ix: ident * funspec) : Prop :=
  exists f, (QP.prog_defs Zstd.contracts.x_valid_dict.Harness.qp) ! (fst ix) = Some (Gfun (Internal f)) /\
            fn_callconv f = callingconvention_of_funspec (snd ix) /\
            semax_body Vprog G f ix.

Definition HarnessOK (API Hs: funspecs) : Prop :=
  map fst Hs = helper_ids /\ Forall (hbody_ok (Gprog API Hs)) (Hs ++ [main_spec]).
