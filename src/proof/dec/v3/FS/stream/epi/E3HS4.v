(* FS3 streaming: the epilogue's head, piece: the progress test and the no-progress guard. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0 Zstd.proof.dec.v3.FS.stream.epi.E3H62 Zstd.proof.dec.v3.FS.stream.epi.E3H62b Zstd.proof.dec.v3.FS.stream.epi.E3HNP.
Local Open Scope logic.

Section CM_E3HS4_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma head_s4 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a -> a_opos a <= opc <= a_osz a -> Zlength oc1 = a_osz a ->
  head_ok a k ipc opc oc1 ->
  semax epi_Delta0 (hpre DENT TABS a (k_nfp a k opc (sf_nfp (c3_s k))) ipc ipc opc opc oc1 [])
    (Ssequence ds_h62 ds_hnp) (overridePost (emid DENT TABS a k ipc opc oc1) (ds_R_x DENT TABS BR a)).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Hop Hloc Hh.
destruct Hh as (Hn & P80 & P82 & Pnp & Pp).
eapply semax_seq; [apply epi_normal_over; destruct (Z.eq_dec ipc (a_ipos a)); [apply head_62_eq | apply head_62_ne]; auto|].
destruct (andb (ipc =? a_ipos a) (opc =? a_opos a)) eqn:Enp.
- apply andb_prop in Enp. destruct Enp as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
  epi_fstart. unfold ds_hnp.
  forward_if.
  2: { exfalso. match goal with H: _ |- _ => solve [inversion H] end. }
  eapply semax_pre; [| apply (@head_np CMI Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Hop Hloc Hn);
                       [intros; apply P80; auto | intros; apply P82; auto | intros; apply Pnp; auto]].
  unfold hpre, hS, epi_L; cbn [app]; entailer!.
- epi_fstart. rewrite ctx_rep_nfp. cbn [k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage]. Intros. unfold ds_hnp.
  forward_if.
  { exfalso. match goal with H: _ |- _ => solve [inversion H | contradiction H; reflexivity] end. }
  forward.
  assert (Hpr: ipc <> a_ipos a \/ opc <> a_opos a).
  { destruct (Z.eqb_spec ipc (a_ipos a)); destruct (Z.eqb_spec opc (a_opos a)); simpl in Enp;
      try discriminate; auto. }
  unfold emid. Exists 0. unfold epi_S, epi_L.
  rewrite (ctx_rep_nfp _ _ _ _ (k_nfp _ _ _ 0)).
  rewrite (ctx_nrest_nfp _ _ _ _ _ _ _ 0 (sf_nfp (c3_s k))).
  cbn [k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage].
  pose proof (Pp Hpr). entailer!.
Time Qed.

End CM_E3HS4_1.
