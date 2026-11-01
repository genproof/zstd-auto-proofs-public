(* FS3 streaming: the epilogue's tail, piece: the frame complete (expected = 0). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3TE Zstd.proof.dec.v3.FS.stream.epi.E3TNeq.
Local Open Scope logic.

Section CM_E3TZ_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_ok_ipos : forall (a: dsa) (k: cst3) (r ipos' opc: Z) (oc1: list val),
  epi_ok a k r ipos' opc oc1 -> a_ipos a <= ipos'.
Proof.
intros a k r ipos' opc oc1 (_ & st' & (Hp & _) & _).
destruct Hp as (dl & stall' & a' & Hp). cbv zeta in Hp. destruct Hp as (_ & Hip & _). lia.
Qed.

Lemma tail_z : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val)
    (os oe: Z) (h: int),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a ->
  sf_outStart (c3_s k) = vlong os -> sf_outEnd (c3_s k) = vlong oe -> sf_hostage (c3_s k) = Vint h ->
  0 <= os <= Int64.max_unsigned -> 0 <= oe <= Int64.max_unsigned ->
  (os = oe -> h <> Int.zero -> a_isz a <= ipc -> epi_ok a (k_sh k zdss_read (sf_hostage (c3_s k))) 1 ipc opc oc1) ->
  (os = oe -> h <> Int.zero -> ipc < a_isz a -> epi_ok a k 0 (ipc + 1) opc oc1) ->
  (os = oe -> h = Int.zero -> epi_ok a k 0 ipc opc oc1) ->
  (os <> oe -> h = Int.zero -> epi_ok a (k_sh k (sf_stage (c3_s k)) (Vint (Int.repr 1))) 1 (ipc - 1) opc oc1) ->
  (os <> oe -> h <> Int.zero -> epi_ok a k 1 ipc opc oc1) ->
  semax epi_Delta0 (tpre DENT TABS a k ipc opc oc1 []) ds_tail_Z (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 os oe h HT Ha Hip Hos Hoe Hh Hosr Hoer Pcr Prel P0 Ptake Pheld.
pose proof Ha as (_ & _ & _ & Hwso & Hwsi & Hwsob & Hrsb & _ & _ & Hopos & Hosz & _ & Hipos & Hisz & _).
epi_piece_start. unfold ds_tail_Z.
rewrite Hos, Hoe. forward. forward. forward_if.
{ epi_norm. apply epi_seq_ret. apply (@epi_R_sub CMI _ DENT TABS BR a); [reflexivity|].
  eapply semax_pre; [| apply (@tail_e CMI Espec DENT TABS BR a k ipc opc oc1 h HT Ha Hip Hh); auto].
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; rewrite Hos, Hoe; entailer!. }
{ epi_norm.
  assert (Hi1: h = Int.zero -> 1 <= ipc).
  { intros Hz. pose proof (epi_ok_ipos _ _ _ _ _ _ (Ptake ltac:(lia) Hz)). lia. }
  unfold MORE_COMMANDS, abbreviate.
  eapply semax_pre; [| apply (@tail_neq CMI Espec DENT TABS BR a k ipc opc oc1 h HT Ha Hip Hh Hi1); auto].
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; rewrite Hos, Hoe; entailer!. }
Time Qed.

End CM_E3TZ_1.
