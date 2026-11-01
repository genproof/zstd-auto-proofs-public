(* FS3 streaming: the epilogue's head and tail assembled: from the loop invariant at someMoreWork = 0. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0 Zstd.proof.dec.v3.FS.stream.epi.E3HIn Zstd.proof.dec.v3.FS.stream.epi.E3HOut Zstd.proof.dec.v3.FS.stream.epi.E3HCopy Zstd.proof.dec.v3.FS.stream.epi.E3HS4 Zstd.proof.dec.v3.FS.stream.epi.E3TTop.
Local Open Scope logic.

Section CM_E3HTop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_head : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= w_ipc w <= a_isz a -> a_opos a <= w_opc w <= a_osz a ->
  Zlength (w_oc w) = a_osz a -> head_ok a (w_k w) (w_ipc w) (w_opc w) (w_oc w) ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
    ds_epilogue (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a w HT Ha Hip Hop Hloc Hh.
rewrite ds_epilogue_eq.
eapply semax_pre with (P' := hpre DENT TABS a (w_k w) (w_ipc w) (a_ipos a) (a_opos a) (w_opc w) (w_oc w) [temp _src (a_ib a); temp _dst (a_ob a)]).
{ unfold hpre, hS, epi_L, ds_LI_L, ds_LI_S. cbn [app]. apply andp_left2.
  apply LOCALx_shuffle_derives. intros q Hq. simpl in Hq |- *. tauto. }
pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _).
eapply semax_seq; [apply epi_normal_over; apply (@epi_Delta_lift CMI _ DENT TABS BR); apply head_in; auto|].
eapply semax_seq; [apply epi_normal_over; apply (@epi_Delta_lift CMI _ DENT TABS BR); apply head_out; auto|].
eapply semax_seq; [apply epi_normal_over; apply (@epi_Delta_lift1 CMI _ DENT TABS BR ZSTD_outBuffer_copy_spec); [apply epi_obc_in|]; apply head_copy; auto|].
eapply semax_seq; [apply (@epi_Delta_lift CMI _ DENT TABS BR); apply head_s4; auto|].
unfold emid. Intros n. eapply (@epi_tail CMI Espec DENT TABS BR); eauto.
Time Qed.

End CM_E3HTop_1.
