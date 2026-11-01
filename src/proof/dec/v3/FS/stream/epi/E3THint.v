(* FS3 streaming: the epilogue's tail, piece: a frame in progress, the hint. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0.
Local Open Scope logic.

Section CM_E3THint_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tail_hint : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val)
    (e fstg ip0: Z),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a ->
  fs_stage (c3_fs k) = Vint (Int.repr fstg) -> 0 <= fstg <= 7 ->
  sf_inPos (c3_s k) = vlong ip0 -> 0 <= ip0 <= Int64.max_unsigned ->
  epi_ok a k (e + ZSTD_blockHeaderSize * nit_blk fstg - ip0) ipc opc oc1 ->
  semax (epi_Delta1 ZSTD_nextInputType_spec) (tpre DENT TABS a k ipc opc oc1 [temp _nextSrcSizeHint (vlong e)]) ds_tail_hint
    (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 e fstg ip0 HT Ha Hip Hfst Hfr Hip0 Hip0r Phint.
epi_piece_start. unfold ds_tail_hint.
rewrite Hfst. forward_call (a_d a, fstg).
rewrite epi_zg. Intros.
forward. forward. rewrite Hip0. forward. forward. forward.
eapply epi_close_gen; [exact HT | exact Phint | apply epi_hint_val; auto |].
epi_fold. rewrite epi_zg. rewrite Hfst, Hip0. entailer!.
Time Qed.

End CM_E3THint_1.
