(* FS3 streaming: the epilogue's tail, piece: a frame complete, nothing pending (outStart = outEnd). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3TH1.
Local Open Scope logic.

Section CM_E3TE_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tail_e : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) (h: int),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a -> sf_hostage (c3_s k) = Vint h ->
  (h <> Int.zero -> a_isz a <= ipc -> epi_ok a (k_sh k zdss_read (sf_hostage (c3_s k))) 1 ipc opc oc1) ->
  (h <> Int.zero -> ipc < a_isz a -> epi_ok a k 0 (ipc + 1) opc oc1) ->
  (h = Int.zero -> epi_ok a k 0 ipc opc oc1) ->
  semax epi_Delta0 (tpre DENT TABS a k ipc opc oc1 []) ds_tail_E (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 h HT Ha Hip Hh Pcr Prel P0.
pose proof Ha as (_ & _ & _ & Hwso & Hwsi & Hwsob & Hrsb & _ & _ & Hopos & Hosz & _ & Hipos & Hisz & _).
epi_piece_start. unfold ds_tail_E.
rewrite Hh. forward. unfold MORE_COMMANDS, abbreviate. apply semax_if_seq. forward_if.
{ eapply semax_pre; [| apply (@tail_h1r CMI Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip); auto].
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; rewrite Hh; entailer!. }
{ forward. epi_norm.
  eapply epi_close_gen; [exact HT | apply P0; auto | reflexivity |].
  epi_fold. rewrite Hh. entailer!. }
Time Qed.

End CM_E3TE_1.
