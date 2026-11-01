(* Changing the compspecs of byte arrays.  The decoder's API (Spec_api6) is stated
   at the decoder's compspecs (Zstd.units.Zstd.CS); a harness main works at its own (Harness.CS).  A byte
   array means the same under any two compspecs: no composite is involved, so cs_preserve_type is true by
   computation.  cce_any: the change_composite_env of any two compspecs, built without computing it. *)
Require Import VST.floyd.proofauto.

Definition cce_any (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma data_at_bytes_cs (cs1 cs2: compspecs) sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  pose proof (@data_at_change_composite cs1 cs2 (cce_any cs1 cs2) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma data_at__bytes_cs (cs1 cs2: compspecs) sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  pose proof (@data_at__change_composite cs1 cs2 (cce_any cs1 cs2) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.
