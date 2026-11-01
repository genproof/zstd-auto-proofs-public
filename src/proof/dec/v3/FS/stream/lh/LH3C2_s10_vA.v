(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the view of the state for the format and
   headerBuffer reads. *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_g.
Local Open Scope logic.

Section CM_LH3C2_s10_vA_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the pure facts of the context's groups *)
Definition c10_pp (K: cst3) : Prop := (cold01 (c3_fs K) /\ par_ok (c3_par K)) /\ c10_sgp (c3_s K).

Section VA.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition c10_rA (a: dsa) (w: lw) (K: cst3) (tbl: list val) : mpred :=
  data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a) * pws_pred (a_W a) * mem_mgr (a_gv a) *
  zstd_globals (a_gv a) * dctx_token (a_d a) * dctx_pad (a_d a) * frame_fields (a_d a) (c3_fs K) *
  c10_fgr TABS (a_gv a) (a_d a) (c3_tabs K) (c3_par K) (c3_sp K) *
  cgroup3 (a_d a) (c3_stable K) (dp_wmax (c3_par K)) * dgroup DENT (a_gv a) (a_d a) (c3_dict K) *
  field_at Ews t_dctx (DOT _lhSize) (sf_lhSize (c3_s K)) (a_d a) * c10_sgr (a_d a) (c3_s K) *
  hset_t (sf_mem (c3_s K)) (c3_sp K) (c3_set K) (sf_held (c3_s K) - local_held (c3_dict K)) tbl *
  dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
  set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a)) *
  data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a) *
  data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong (a_ipos a))) (a_inp a) *
  data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a) *
  data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a).

Lemma c10_vA (a: dsa) (w: lw) (K: cst3) (tbl: list val) :
  fold_right_sepcon (ds_LI_St DENT TABS a (lw_k w K) tbl) =
  !! (c10_pp K) &&
  fold_right_sepcon [field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt (c3_par K)))) (a_d a);
                     field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s K)) (a_d a); c10_rA a w K tbl].
Proof.
unfold ds_LI_St, ctx_rep3t, c10_rA, c10_pp. rewrite c10_fg_eq, c10_sg_eq. unfold cfg_fmt.
cbn [fold_right_sepcon w_opc w_oc w_k lw_k].
apply pred_ext.
- normalize. cancel.
- normalize. cancel.
Qed.

End VA.

End CM_LH3C2_s10_vA_1.
