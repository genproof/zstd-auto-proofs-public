(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: after ZSTD_decodeFrameHeader
   (expected = ZSTD_blockHeaderSize, stage = ZSTDds_decodeBlockHeader). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_vT Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10t.
Local Open Scope logic.

Section CM_LH3C2_s10r_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c10_Lr_core : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w1: lw) (e st: val) (c: list val)
    (FR: mpred) (P P': list Prop) (R: ret_assert),
  (fold_right and True P -> fold_right and True P') ->
  semax (ds_Delta DENT TABS BR)
    (PROPx P (LOCALx (ds_LI_L a w1)
      (SEPx [field_at Ews t_dctx (DOT _expected) e (a_d a); field_at Ews t_dctx (DOT _stage) st (a_d a);
             field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); zstd_globals (a_gv a); FR]))) c10_r
    (overridePost (PROPx P' (LOCALx (ds_LI_L a w1)
      (SEPx [field_at Ews t_dctx (DOT _expected) (vlong ZSTD_blockHeaderSize) (a_d a);
             field_at Ews t_dctx (DOT _stage) (Vint (Int.repr ds_decodeBlockHeader)) (a_d a);
             field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); zstd_globals (a_gv a); FR]))) R).
Proof.
intros Espec DENT TABS BR a w1 e st c FR P P' R HPP.
apply c10_props_pre; intro HP.
match goal with |- semax ?D ?Pre ?cc (overridePost (PROPx _ ?LS) ?RR) =>
  apply (c10_post_n D Pre cc _ (PROPx [] LS) RR); [| apply andp_left2; apply c10_props_post; auto] end.
destruct R as [Rn Rb Rc Rr]. cbv beta iota delta [overridePost].
unfold ds_Delta. simplify_func_tycontext. unfold c10_r, ds_LI_L. abbreviate_semax.
rewrite c10_zg_eq. flatten_sepcon_in_SEP.
forward. forward. forward.
rewrite c10_zg_eq. unfold vlong, ZSTD_blockHeaderSize, ds_decodeBlockHeader. entailer!.
Qed.

Lemma c10_Lr : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) dd cold lxb (R: ret_assert),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 -> fh_frameType h <> 1 ->
  lxb = tabs_lxb (c3_tabs (k_A (w_k w) (fh_val h) d1 did1)) ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (c10_S2c DENT TABS a w k1 hb h tbl dd cold lxb) c10_r
    (overridePost (lhC_S3 DENT TABS a w k1 hb h tbl) R).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 dd cold lxb R HP Hft Hlxb k1. subst k1.
unfold c10_S2c. Intros did'.
rewrite (c10_prop_sep _ _ _ _ _
  (c10_vT DENT TABS a w (lhC_kx (k_A (w_k w) (fh_val h) d1 did1)
     (c10_fsok (k_A (w_k w) (fh_val h) d1 did1) hb h dd cold did') dd lxb) tbl)).
apply semax_extract_PROP; intros ((Hcold & Hpar) & Hsg).
eapply c10_post_n.
{ eapply (c10_Lr_core _ _ _ _ a (lw_k w (k_A (w_k w) (fh_val h) d1 did1)))
    with (P' := [lhC_small a w (k_A (w_k w) (fh_val h) d1 did1) h = false;
            lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1);
            0 <= did' <= Int.max_unsigned; fh_dictID h = 0 \/ fh_dictID h = did'; dd = None -> did' = 0]).
  intros _. cbn [fold_right]. tauto. }
unfold lhC_S3.
Exists {| lc_dd := dd; lc_cold := cold; lc_did := did'; lc_lxb := lxb |}.
cbn [lc_dd lc_cold lc_did lc_lxb].
rewrite c10_fs0_ok by exact Hft. cbn [lc_dd lc_cold lc_did lc_lxb].
rewrite (c10_prop_sep _ _ _ _ _ (c10_vT DENT TABS a w _ tbl)).
rewrite c10_rT_es.
cbn [lhC_kx c3_fs fs_expected fs_stage fsu_stage fsu_expected c3_s].
unfold ds_LI_L. entailer!.
split; [exact (conj (conj Hcold Hpar) Hsg) |].
unfold lhC_cfacts. cbn [lc_dd lc_cold lc_did lc_lxb]. repeat split; auto; lia.
Qed.

End CM_LH3C2_s10r_1.
