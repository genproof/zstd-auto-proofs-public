(* FS3 streaming: the epilogue's tail, piece: the hostage byte released (in.pos + 1, return 0). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0.
Local Open Scope logic.

Section CM_E3TRel_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tail_relr : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc < a_isz a -> epi_ok a k 0 (ipc + 1) opc oc1 ->
  semax epi_Delta0 (tpre DENT TABS a k ipc opc oc1 []) ds_tail_relr (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Hok.
pose proof Ha as (_ & _ & _ & Hwso & Hwsi & Hwsob & Hrsb & _ & _ & Hopos & Hosz & _ & Hipos & Hisz & _).
epi_piece_start. unfold ds_tail_relr.
forward. forward. forward.
eapply epi_close_gen; [exact HT | exact Hok | reflexivity |].
epi_fold. entailer!.
Time Qed.

End CM_E3TRel_1.
