(* FS3 streaming: the epilogue's head, piece: no progress in this call (noForwardProgress++, the guard). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0 Zstd.proof.dec.v3.FS.stream.epi.E3H0 Zstd.proof.dec.v3.FS.stream.epi.E3HDF Zstd.proof.dec.v3.FS.stream.epi.E3HL1 Zstd.proof.dec.v3.FS.stream.epi.E3HL2 Zstd.proof.dec.v3.FS.stream.epi.E3HL2b.
Local Open Scope logic.

Section CM_E3HNP_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the context split at noForwardProgress only (the only field this piece touches) *)
Definition ctx_nrest DENT TABS (gv: globals) (p: val) (k: cst3) : mpred :=
  field_at Ews t_dctx (DOT _expected) (fs_expected (c3_fs k)) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs k)) p *
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos (c3_s k)) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart (c3_s k)) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd (c3_s k)) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage (c3_s k)) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut (c3_s k)) p *
  epi_rest DENT TABS gv p k.

Lemma ctx_rep_nfp : forall DENT TABS gv p k,
  ctx_rep3 DENT TABS gv p k =
  !! (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed /\ Int.min_signed <= sf_nfp (c3_s k) <= Int.max_signed) &&
  (field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp (c3_s k)))) p * ctx_nrest DENT TABS gv p k).
Proof.
intros. rewrite ctx_rep_epi. unfold sg_seven, ctx_nrest. f_equal. apply pred_ext; cancel.
Qed.

Lemma ctx_nrest_nfp : forall DENT TABS gv p (a: dsa) k opc m m',
  ctx_nrest DENT TABS gv p (k_nfp a k opc m) = ctx_nrest DENT TABS gv p (k_nfp a k opc m').
Proof. reflexivity. Qed.

Ltac np_fold t m :=
  unfold hpre, hS, epi_L; cbn [app];
  rewrite (ctx_rep_nfp _ _ _ _ (k_nfp _ _ _ t)); rewrite (ctx_nrest_nfp _ _ _ _ _ _ _ t m);
  cbn [k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage]; entailer!.

Lemma head_np : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val),
  TABS_OK TABS -> dsa_ok a -> a_ipos a <= ipc <= a_isz a -> a_opos a <= opc <= a_osz a -> Zlength oc1 = a_osz a ->
  let n := sf_nfp (c3_s k) in
  0 <= n <= 16 ->
  (n + 1 >= 16 -> opc = a_osz a ->
     epi_ok a (k_nfp a k opc (n + 1)) (2 ^ 64 - ZSTD_error_noForwardProgress_destFull) ipc opc oc1) ->
  (n + 1 >= 16 -> opc <> a_osz a -> ipc = a_isz a ->
     epi_ok a (k_nfp a k opc (n + 1)) (2 ^ 64 - ZSTD_error_noForwardProgress_inputEmpty) ipc opc oc1) ->
  (~ (n + 1 >= 16 /\ (opc = a_osz a \/ ipc = a_isz a)) -> tail_ok a (k_nfp a k opc (n + 1)) ipc opc oc1) ->
  semax epi_Delta0 (hpre DENT TABS a (k_nfp a k opc n) ipc ipc opc opc oc1 []) ds_np
    (overridePost (emid DENT TABS a k ipc opc oc1) (ds_R_x DENT TABS BR a)).
Proof.
intros Espec DENT TABS BR a k ipc opc oc1 HT Ha Hip Hop Hloc n Hn P80 P82 Pnp.
subst n.
epi_fstart. rewrite ctx_rep_nfp. cbn [k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage]. Intros. unfold ds_np.
forward. forward. forward.
forward_if.
- (* the 16th call without progress *)
  rewrite add_repr.
  match goal with H: sf_nfp (c3_s k) + 1 >= 16 |- _ => rename H into Hge end.
  destruct (Z.eq_dec opc (a_osz a)) as [Eo|Eo].
  + eapply semax_pre; [| apply (@head_df CMI Espec DENT TABS BR a k ipc opc oc1 (sf_nfp (c3_s k) + 1) HT Ha Hop Hloc Eo);
                         apply P80; auto].
    np_fold (sf_nfp (c3_s k) + 1) (sf_nfp (c3_s k)).
  + eapply semax_seq.
    { apply epi_normal_over.
      eapply semax_pre; [| apply (@head_l1 CMI Espec DENT TABS a (k_nfp a k opc (sf_nfp (c3_s k) + 1)) ipc opc oc1 Ha Hop Hloc Eo)].
      np_fold (sf_nfp (c3_s k) + 1) (sf_nfp (c3_s k)). }
    destruct (Z.eq_dec ipc (a_isz a)) as [Ei|Ei].
    * apply (@head_l2_ie CMI Espec DENT TABS BR a k ipc opc oc1 (sf_nfp (c3_s k) + 1) HT Ha Hip Hop Hloc Ei).
      apply P82; auto.
    * apply (@head_l2_ok CMI Espec DENT TABS BR a k ipc opc oc1 (sf_nfp (c3_s k) + 1) Ha Hip Hop Hloc Ei).
      apply Pnp. intros [_ [C|C]]; contradiction.
- (* below the limit *)
  rewrite add_repr. forward.
  unfold emid. Exists (sf_nfp (c3_s k) + 1). unfold epi_S, epi_L.
  rewrite (ctx_rep_nfp _ _ _ _ (k_nfp _ _ _ (sf_nfp (c3_s k) + 1))).
  rewrite (ctx_nrest_nfp _ _ _ _ _ _ _ (sf_nfp (c3_s k) + 1) (sf_nfp (c3_s k))).
  cbn [k_nfp k_epi sf_epi c3_with_s c3_s sf_nfp sf_stage].
  pose proof (Pnp ltac:(lia)). entailer!.
Time Qed.

End CM_E3HNP_1.
