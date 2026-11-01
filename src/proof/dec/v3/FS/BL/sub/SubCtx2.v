(* FS3-bl SUB: the context joined back after ZSTD_decompressContinue_ispec (split in SubCtx.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.sub.SubCtx.
Local Open Scope logic.

Section CM_SubCtx2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Ctx2.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Lemma ctx3_join gv p k fs t hb :
  cold01 fs -> Zlength hb = 18 ->
  fcore3 p fs (c3_par k) (c3_sp k) * tabs_rep TABS gv p t * field_at Ews t_dctx (DOT _headerBuffer) hb p *
  ctx_rest3 DENT gv p k |-- ctx_rep3 DENT TABS gv p (c3_bl k fs t hb).
Proof.
  intros Hc Hh.
  unfold ctx_rep3, ctx_body3, fgroup3, fcore3, sgroup, ctx_rest3, sgroup_nohb, c3_bl, c3_with_s, c3_with_fs,
    sf_with_hbuf, sf_given; simpl. Intros. entailer!.
Qed.

End Ctx2.

End CM_SubCtx2_1.
