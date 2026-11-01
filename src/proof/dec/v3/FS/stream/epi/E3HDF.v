(* FS3 streaming: the epilogue's head, piece: the 16th call without progress, the output full (destFull). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0.
Local Open Scope logic.

Section CM_E3HDF_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma head_df : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) (n: Z),
  TABS_OK TABS -> dsa_ok a -> a_opos a <= opc <= a_osz a -> Zlength oc1 = a_osz a -> opc = a_osz a ->
  epi_ok a (k_nfp a k opc n) (2 ^ 64 - ZSTD_error_noForwardProgress_destFull) ipc opc oc1 ->
  semax epi_Delta0 (hpre DENT TABS a (k_nfp a k opc n) ipc ipc opc opc oc1 []) ds_errs
    (overridePost (emid DENT TABS a k ipc opc oc1) (ds_R_x DENT TABS BR a)).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 n HT Ha Hop Hloc Eo P80.
pose proof Ha as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                  Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hstpos & _).
unfold emid. epi_fstart. unfold ds_errs.
assert_PROP (isptr (a_ob a)) as Pob by entailer!.
apply semax_seq with (Q := PROP (False) LOCAL () SEP ()); [| Intros; contradiction].
apply semax_dowhile0_gen.
match goal with |- semax _ _ _ ?Q =>
  let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
abbreviate_semax.
forward.
forward_if.
{ entailer!. apply epi_tc_test_eq; auto; epi_wvp (a_W a) (a_shob a) oc1 (a_ob a). }
{ apply semax_dowhile0. unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
  { apply semax_dowhile0_gen.
    match goal with |- semax _ _ _ ?Q =>
      let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
    abbreviate_semax.
    forward_if.
    { match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end. }
    forward. entailer!. }
  abbreviate_semax. unfold MORE_COMMANDS, abbreviate.
  apply semax_dowhile0. apply semax_dowhile0.
  forward.
  eapply epi_close_gen; [exact HT | exact P80 | apply epi_neg_repr |].
  entailer!. }
{ match goal with H: offset_val opc _ <> offset_val (a_osz a) _ |- _ => rewrite Eo in H; contradiction H; reflexivity end. }
Time Qed.

End CM_E3HDF_1.
