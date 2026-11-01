(* FS3-bl: DC3_of with the stage field taken out, for BLSmall. *)
Require Export Zstd.proof.dec.v3.FS.BL.BLSmallSplit.
Local Open Scope logic.

Section CM_BLSmallSplit2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma DC3_stage_split DENT TABS (SR: srel3) gv p st k :
  base_rel3 st k ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false ->
     SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ex_on3 SR st k ->
  ctx_rep3 DENT TABS gv p k |--
    field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs k)) p *
    (field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs k)) p -* DC3_of DENT TABS SR BR gv p st).
Proof.
  intros H1 H2 H3 H4.
  unfold ctx_rep3, ctx_body3, fgroup3, frame_fields. Intros. cancel.
  repeat rewrite <- wand_sepcon_adjoint. unfold DC3_of. Exists k.
  unfold ctx_rep3, ctx_body3, fgroup3, frame_fields. entailer!.
Qed.

End CM_BLSmallSplit2_1.
