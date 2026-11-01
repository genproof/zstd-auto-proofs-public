(* FS3 streaming: the epilogue's tail, piece: hostageByte set, nothing pending (release or not). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3TCr Zstd.proof.dec.v3.FS.stream.epi.E3TRel.
Local Open Scope logic.

Section CM_E3TH1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tail_h1r : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a ->
  (a_isz a <= ipc -> epi_ok a (k_sh k zdss_read (sf_hostage (c3_s k))) 1 ipc opc oc1) ->
  (ipc < a_isz a -> epi_ok a k 0 (ipc + 1) opc oc1) ->
  semax epi_Delta0 (tpre DENT TABS a k ipc opc oc1 []) ds_tail_h1r (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Pcr Prel.
pose proof Ha as (_ & _ & _ & Hwso & Hwsi & Hwsob & Hrsb & _ & _ & Hopos & Hosz & _ & Hipos & Hisz & _).
epi_piece_start. unfold ds_tail_h1r.
forward. forward. apply semax_if_seq. forward_if.
{ epi_norm. apply epi_seq_ret. apply (@epi_R_sub CMI _ DENT TABS BR a); [reflexivity|].
  eapply semax_pre; [| apply (@tail_cr CMI Espec DENT TABS BR a k ipc opc oc1 HT); apply Pcr; lia]. epi_to_tpre. }
{ epi_norm. unfold MORE_COMMANDS, abbreviate.
  eapply semax_pre; [| apply (@tail_relr CMI Espec DENT TABS BR a k ipc opc oc1 HT Ha); [lia | apply Prel; lia]].
  epi_to_tpre. }
Time Qed.

End CM_E3TH1_1.
