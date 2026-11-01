(* The common base of every specification and body proof of the decoder unit (patch/decoder.c).
   Body lemmas have the form
     Lemma body_X : semax_body Vprog Gprog f_X X_spec.
   with Vprog below and Gprog of Zstd.proof.zstd.Gprog. *)
Require Export VST.floyd.proofauto.
Require Export VST.floyd.library.
Require Export VST.floyd.VSU.
Require Export QuickProof.Env.
Require Export Zstd.proof.libc.LibcOk.
Require Export Zstd.zstd.code.
Require Export Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Xxh64.
Require Zstd.units.

(* The unit's composite environment: the one units.v computed (make_compspecs Zstd.zstd.code.prog). *)
#[export] Instance CompSpecs : compspecs := Zstd.units.Zstd.CS.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* A function with a vacuous specification (precondition FF) needs no proof. *)
Lemma semax_body_vacuous {cs: compspecs} :
  forall V G f i, semax_body V G f (i, vacuous_funspec (Internal f)).
Proof.
  intros. unfold semax_body, vacuous_funspec. destruct f; simpl.
  split3; [reflexivity | reflexivity | ]. intros ? ? x. destruct x.
Qed.
