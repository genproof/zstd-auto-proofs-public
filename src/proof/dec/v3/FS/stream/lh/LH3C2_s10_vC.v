(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the view of the state for
   ZSTD_decodeFrameHeader. *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_vA.
Local Open Scope logic.

Section CM_LH3C2_s10_vC_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section VC.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the stream group without lhSize, headerBuffer and the allocator's count (cm_have, which the selection takes) *)
Definition c10_sgr0 (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
  ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
  field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem s)) p *
  blk_tok (sf_mem s) (tarray tuchar (sizeof t_dctx)) p.

Definition c10_rC (a: dsa) (w: lw) (K: cst3) : mpred :=
  data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a) * pws_pred (a_W a) *
  dctx_token (a_d a) * dctx_pad (a_d a) * cgroup3 (a_d a) (c3_stable K) (dp_wmax (c3_par K)) *
  c10_sgr0 (a_d a) (c3_s K) *
  data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a) *
  data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong (a_ipos a))) (a_inp a) *
  data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a) *
  data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a).

Lemma c10_vC (a: dsa) (w: lw) (K: cst3) (tbl: list val) :
  fold_right_sepcon (ds_LI_St DENT TABS a (lw_k w K) tbl) =
  !! (c10_pp K /\ cmem_ok (sf_mem (c3_s K))) &&
  fold_right_sepcon [field_at Ews t_dctx (DOT _lhSize) (sf_lhSize (c3_s K)) (a_d a);
                     field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s K)) (a_d a);
                     fcore3 (a_d a) (c3_fs K) (c3_par K) (c3_sp K);
                     tabs_rep TABS (a_gv a) (a_d a) (c3_tabs K);
                     zstd_globals (a_gv a); mem_mgr (a_gv a); dgroup DENT (a_gv a) (a_d a) (c3_dict K);
                     hset_t (sf_mem (c3_s K)) (c3_sp K) (c3_set K) (sf_held (c3_s K) - local_held (c3_dict K)) tbl;
                     cm_have (sf_mem (c3_s K)) (sf_given (c3_s K));
                     dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
                     set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
                     c10_rC a w K].
Proof.
unfold ds_LI_St, ctx_rep3t, c10_rC, c10_pp. rewrite c10_fg_split, c10_sg_eq.
unfold c10_sgr, c10_sgr0, mgroup.
cbn [fold_right_sepcon w_opc w_oc w_k lw_k].
apply pred_ext; normalize; cancel.
Qed.

End VC.

End CM_LH3C2_s10_vC_1.
