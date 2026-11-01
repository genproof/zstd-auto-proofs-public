(* FS3 streaming: the epilogue's tail, piece: the hostage byte cannot be released (streamStage := zdss_read, return 1). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0.
Local Open Scope logic.

Section CM_E3TCr_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tail_cr : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> epi_ok a (k_sh k zdss_read (sf_hostage (c3_s k))) 1 ipc opc oc1 ->
  semax epi_Delta0 (tpre DENT TABS a k ipc opc oc1 []) ds_tail_cr (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Hok.
epi_piece_start. unfold ds_tail_cr.
forward. forward.
eapply epi_close_gen; [exact HT | exact Hok | reflexivity |].
epi_fold. entailer!.
Time Qed.

End CM_E3TCr_1.
