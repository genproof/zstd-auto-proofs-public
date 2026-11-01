(* FS3 streaming: the epilogue's tail (the hint, the hostage byte): the dispatch to its pieces. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3TZ Zstd.proof.dec.v3.FS.stream.epi.E3THint.
Local Open Scope logic.

Section CM_E3TTop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_tail : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a -> a_opos a <= opc <= a_osz a ->
  tail_ok a k ipc opc oc1 ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (epi_L a ipc) (SEPx (epi_S DENT TABS a k ipc opc oc1))))
    ds_epi_tail (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Hop Ht.
destruct Ht as (e & He & Her & H0 & Hn0).
unfold ds_epi_tail, ds_Delta, ds_R_x, ds_post_x. abbreviate_semax.
unfold epi_S, epi_L. rewrite ctx_rep_epi. unfold sg_seven. Intros.
forward_call (a_d a, e).
forward_if.
{ (* the frame is complete *)
  assert (E: e = 0).
  { match goal with H: Int64.repr e = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
      rewrite Int64.unsigned_zero in H; exact H end. }
  destruct (H0 E) as (os & oe & h & Hos & Hoe & Hh & Hosr & Hoer & Pcr & Prel & P0 & Ptake & Pheld).
  apply epi_seq_ret. apply (@epi_R_sub CMI _ DENT TABS BR a); [reflexivity|].
  apply (@epi_Delta_lift CMI _ DENT TABS BR).
  eapply semax_pre; [| apply (@tail_z CMI Espec DENT TABS BR a k ipc opc oc1 os oe h HT Ha Hip Hos Hoe Hh Hosr Hoer
                               Pcr Prel P0 Ptake Pheld)].
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; rewrite He; entailer!. }
{ (* a frame in progress: the hint *)
  assert (E: e <> 0).
  { match goal with H: Int64.repr e <> Int64.zero |- _ => intro E'; apply H; rewrite E'; reflexivity end. }
  destruct (Hn0 E) as (fstg & ip0 & Hfst & Hfr & Hip0 & Hip0r & Phint).
  unfold MORE_COMMANDS, abbreviate.
  apply (@epi_Delta_lift1 CMI _ DENT TABS BR ZSTD_nextInputType_spec); [apply epi_nit_in|].
  eapply semax_pre; [| apply (@tail_hint CMI Espec DENT TABS BR a k ipc opc oc1 e fstg ip0 HT Ha Hip Hfst Hfr Hip0 Hip0r
                               Phint)].
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; rewrite He; entailer!. }
Time Qed.

End CM_E3TTop_1.
