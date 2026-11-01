(* The proof obligations of the libc unit (quickproof/libc/libc.c).  Body lemmas:
     Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.   etc.
   memcpy is proved against its byte specification (memcpy_bytes_spec); the callers' typed memcpy_spec and
   memmove_spec at their compspecs follow (sub_memcpy, sub_memmove). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Env.
Require Import Zstd.libc.code.
Require Export Zstd.proof.libc.LibcSpec.
Require Zstd.units.

(* The specifications at the decoder's compspecs, as the decoder imports them (Zstd.proof.zstd.Gprog). *)
Section AtZstd.
#[local] Instance Zstd_CS : compspecs := Zstd.units.Zstd.CS.
Definition memset_spec_Zstd := memset_spec.
Definition calloc_spec_Zstd := calloc_spec.
End AtZstd.

#[export] Instance CompSpecs : compspecs := Zstd.units.Libc.CS.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Libc_Imports : funspecs := [ (_quickproof_malloc, malloc_spec') ].
Definition Libc_Internal : funspecs := [ memset_spec; memcmp_spec; calloc_spec; memcpy_bytes_spec; memmove_spec ].
Definition Gprog : funspecs := Libc_Imports ++ Libc_Internal.

Record LibcBodies : Prop := {
  bd_memset : semax_body Vprog Gprog f_memset memset_spec;
  bd_memcmp : semax_body Vprog Gprog f_memcmp memcmp_spec;
  bd_calloc : semax_body Vprog Gprog f_calloc calloc_spec;
  bd_memcpy : semax_body Vprog Gprog f_memcpy memcpy_bytes_spec;
  bd_memmove : semax_body Vprog Gprog f_memmove memmove_spec;
  (* The decoder imports memset/calloc at its own compspecs (Zstd.units.Zstd.CS), this unit
     proves them at Zstd.units.Libc.CS: the link needs the export to be a funspec_sub of the import.
     Specs on byte arrays: VST's change_compspecs / data_at_change_composite with the instance
     `change_composite_env Zstd.units.Libc.CS Zstd.units.Zstd.CS` (make_cs_preserve). *)
  sub_memset : funspec_sub (snd memset_spec) (snd memset_spec_Zstd);
  sub_calloc : funspec_sub (snd calloc_spec) (snd calloc_spec_Zstd);
  (* memcpy and memmove, exported at this unit's compspecs, imported at any (byte arrays only) *)
  sub_memcpy : forall cs: compspecs, funspec_sub (snd (@memcpy_bytes_spec CompSpecs)) (snd (@memcpy_spec cs));
  sub_memmove : forall cs: compspecs, funspec_sub (snd (@memmove_spec CompSpecs)) (snd (@memmove_spec cs))
}.
