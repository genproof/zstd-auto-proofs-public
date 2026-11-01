(* The proof obligation of one function of the decoder unit, against ANY function context G.

     body_ok G (i, spec)  :=  the unit defines i as an internal function f, with the calling convention of
                              spec, and  semax_body Vprog G f (i, spec).

   A body lemma of the decoder states body_ok (or semax_body) against the specifications its function
   calls; `body_ok_mono` lifts it to any larger context, in particular to the final context
   Zstd_Imports ++ Int of ZstdOK.v.  So a body lemma depends only on its own specification and on those
   of its callees: changing any other specification never invalidates it. *)
Require Export Zstd.proof.zstd.Gprog.
Require Zstd.units.
Import compcert.lib.Maps.

Definition zstd_fun (i: ident) (f: function) : Prop :=
  (QP.prog_defs Zstd.units.Zstd.qp) ! i = Some (Gfun (Internal f)).

Definition body_ok (G: funspecs) (ix: ident * funspec) : Prop :=
  exists f, zstd_fun (fst ix) f /\
            fn_callconv f = callingconvention_of_funspec (snd ix) /\
            semax_body Vprog G f ix.

Lemma body_ok_mono (G G': funspecs) (ix: ident * funspec) :
  body_ok G ix -> incl G G' -> NoDup (map fst Vprog ++ map fst G') -> body_ok G' ix.
Proof.
  intros [f [Hf [Hcc Hb]]] Hinc Hnd. exists f; split; [exact Hf | split; [exact Hcc | ]].
  eapply semax_body_subsumption; [exact Hb | ].
  apply semax_prog.func_tycontext_sub; auto. apply incl_refl.
Qed.

(* A function whose specification is vacuous (precondition FF) needs no proof. *)
Lemma body_ok_vacuous (G: funspecs) (i: ident) (f: function) :
  zstd_fun i f -> body_ok G (i, vacuous_funspec (Internal f)).
Proof.
  intros Hf. exists f; split; [exact Hf | split].
  - destruct f; reflexivity.
  - apply semax_body_vacuous.
Qed.
