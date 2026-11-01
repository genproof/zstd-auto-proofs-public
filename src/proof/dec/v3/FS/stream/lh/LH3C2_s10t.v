(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the skippable frame
   (expected = MEM_readLE32(headerBuffer + 4), stage = ZSTDds_skipFrame). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_vT.
Local Open Scope logic.

Section CM_LH3C2_s10t_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c10_Lt_core : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w1: lw) (v38 e st: val) (c: list val)
    (hb: list Z) (G FR: mpred) (P P': list Prop) (R: ret_assert),
  Zlength c = 18 -> Zlength hb <= 18 -> sublist 0 (Zlength hb) c = zbytes hb -> bytes_ok hb -> 8 <= Zlength hb ->
  (fold_right and True P -> fold_right and True P') ->
  semax (ds_Delta DENT TABS BR)
    (PROPx P (LOCALx (temp _t'40 v38 :: ds_LI_L a w1)
      (SEPx [field_at Ews t_dctx (DOT _expected) e (a_d a); field_at Ews t_dctx (DOT _stage) st (a_d a);
             field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); G; FR]))) c10_t
    (overridePost (PROPx P' (LOCALx (ds_LI_L a w1)
      (SEPx [field_at Ews t_dctx (DOT _expected) (vlong (le_field hb 4 4)) (a_d a);
             field_at Ews t_dctx (DOT _stage) (Vint (Int.repr ds_skipFrame)) (a_d a);
             field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); G; FR]))) R).
Proof.
intros Espec DENT TABS BR a w1 v38 e st c hb G FR P P' R Hc Hhb18 Hsub Hbok Hhb8 HPP.
apply c10_props_pre; intro HP.
match goal with |- semax ?D ?Pre ?cc (overridePost (PROPx _ ?LS) ?RR) =>
  apply (c10_post_n D Pre cc _ (PROPx [] LS) RR); [| apply andp_left2; apply c10_props_post; auto] end.
destruct R as [Rn Rb Rc Rr]. cbv beta iota delta [overridePost].
pose proof (Zlength_nonneg hb) as Hhb0.
unfold ds_Delta. simplify_func_tycontext. unfold c10_t, ds_LI_L. abbreviate_semax.
rewrite (c10_hbuf_split (a_d a) c (Zlength hb)) by lia.
rewrite Hsub. flatten_sepcon_in_SEP.
assert_PROP (isptr (field_address t_dctx (DOT _headerBuffer) (a_d a))) as Hhbp by entailer!.
forward_call (Ews, field_address t_dctx (DOT _headerBuffer) (a_d a), hb, 4).
{ entailer!. clear - Hhbp. unfold field_address in *.
  destruct (field_compatible_dec _ _ _); [| contradiction]. simpl. rewrite offset_offset_val. reflexivity. }
{ unfold mem_read_pre. repeat split; auto; try lia. apply Forall_sublist. auto. }
forward. forward.
rewrite <- Hsub.
sep_apply (c10_hbuf_merge (a_d a) c (Zlength hb)); [lia | auto].
rewrite Int.unsigned_repr by (pose proof (c10_le_field4_range hb 4 Hbok); rep_lia).
unfold vlong, ds_skipFrame. entailer!.
Qed.

Lemma c10_rT_es DENT TABS (a: dsa) (w: lw) (k1: cst3) (fs: fstate) dd lxb (e st: val) tbl :
  c10_rT DENT TABS a w (lhC_kx k1 (fsu_stage (fsu_expected fs e) st) dd lxb) tbl = c10_rT DENT TABS a w (lhC_kx k1 fs dd lxb) tbl.
Proof. reflexivity. Qed.

Lemma c10_Lt : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) dd cold lxb (R: ret_assert),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 -> fh_frameType h = 1 ->
  lxb = tabs_lxb (c3_tabs (k_A (w_k w) (fh_val h) d1 did1)) ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (c10_S2b DENT TABS a w k1 h tbl dd cold lxb) c10_t
    (overridePost (lhC_S3 DENT TABS a w k1 hb h tbl) R).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 dd cold lxb R HP Hft Hlxb k1. subst k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hsp & Hg & Hf & HA).
destruct He as (Hstg & Hlh & Hhb18 & Hhbok & Hhbsub & Hhost & Hinp & Hos & Hoe & Hipc & Hopc & Hoc & Hsmw & Hbc & Hlen).
destruct Hf as (_ & _ & _ & _ & _ & _ & _ & _ & Hft2 & _).
destruct (Hft2 Hft) as (Hhb8 & _). unfold ZSTD_SKIPPABLEHEADERSIZE in Hhb8.
unfold c10_S2b.
rewrite (c10_prop_sep _ _ _ _ _
  (c10_vT DENT TABS a w (lhC_kx (k_A (w_k w) (fh_val h) d1 did1) (c10_fsB (k_A (w_k w) (fh_val h) d1 did1) dd cold) dd lxb) tbl)).
apply semax_extract_PROP; intros ((Hcold & Hpar) & Hsg).
eapply c10_post_n.
{ eapply (c10_Lt_core _ _ _ _ a (lw_k w (k_A (w_k w) (fh_val h) d1 did1))) with (hb := hb)
    (P' := [lhC_small a w (k_A (w_k w) (fh_val h) d1 did1) h = false;
            lhC_dd a (k_A (w_k w) (fh_val h) d1 did1) dd; cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)]).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsg))))))).
  - exact Hhb18.
  - exact Hhbsub.
  - exact Hhbok.
  - lia.
  - auto. }
unfold lhC_S3.
Exists {| lc_dd := dd; lc_cold := cold; lc_did := 0; lc_lxb := lxb |}.
cbn [lc_dd lc_cold lc_did lc_lxb].
rewrite c10_fs0_skip by exact Hft. cbn [lc_dd lc_cold].
rewrite (c10_prop_sep _ _ _ _ _ (c10_vT DENT TABS a w _ tbl)).
rewrite c10_rT_es.
cbn [lhC_kx c3_fs fs_expected fs_stage fsu_stage fsu_expected c3_s].
unfold ds_LI_L. entailer!.
split; [exact (conj (conj Hcold Hpar) Hsg) |].
unfold lhC_cfacts. cbn [lc_dd lc_cold lc_did lc_lxb]. repeat split; auto; try rep_lia; try (intro E; contradiction).
Qed.

End CM_LH3C2_s10t_1.
