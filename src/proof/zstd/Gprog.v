(* The function context of the LOWER LAYER (L0) of the decoder unit: the imports (malloc/free of the
   environment, the libc unit), memcpy, and the fixed specifications of util, bits and xxh
   (Spec_util, Spec_bits, Spec_xxh).  The body lemmas of L0 (files body_util_..., body_bits_..., body_xxh_...) are
     Lemma body_X : semax_body Vprog Gprog f_X X_spec.
   with THIS Gprog; they only call L0 functions.

   Higher layers do NOT use this Gprog: a body lemma of a higher function is stated against the list
   of the specifications it calls (any sublist of the final context, e.g. `Gprog ++ [callee specs]`),
   and lifted to the final context by Layer.body_ok_mono. *)
Require Export Zstd.proof.zstd.Spec_xxh.
Require Export Zstd.proof.libc.LibcSpec.

Definition Zstd_Imports : funspecs :=
  [ (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
    memmove_spec; memset_spec; calloc_spec ].

Definition Specs_L0 : funspecs := Specs_util ++ Specs_bits ++ Specs_xxh.

Definition Gprog : funspecs := Zstd_Imports ++ memcpy_spec :: Specs_L0.
