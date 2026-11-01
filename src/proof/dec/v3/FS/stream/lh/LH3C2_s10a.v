(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the skippable test
   (t'40 = format == zstd1 && (MEM_readLE32(headerBuffer) & ZSTD_MAGIC_SKIPPABLE_MASK) == ZSTD_MAGIC_SKIPPABLE_START). 
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_vA.
Local Open Scope logic.

Section CM_LH3C2_s10a_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* on the two fields it reads, any frame FR *)
Lemma c10_La_core : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w1: lw) (fmt: Z) (c: list val) (hb: list Z)
    (b: bool) (FR: mpred) (P P': list Prop) (R: ret_assert),
  fmt = 0 \/ fmt = 1 -> Zlength c = 18 -> Zlength hb <= 18 -> sublist 0 (Zlength hb) c = zbytes hb ->
  bytes_ok hb -> (fmt = 0 -> 4 <= Zlength hb) ->
  b = (if fmt =? 0 then is_skippable_magic (le_field hb 0 4) else false) ->
  (fold_right and True P -> fold_right and True P') ->
  semax (ds_Delta DENT TABS BR)
    (PROPx P (LOCALx (ds_LI_L a w1) (SEPx [field_at Ews t_dctx (DOT _format) (Vint (Int.repr fmt)) (a_d a);
       field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); FR]))) c10_a
    (overridePost (PROPx P' (LOCALx (temp _t'40 (Vint (Int.repr (if b then 1 else 0))) :: ds_LI_L a w1)
       (SEPx [field_at Ews t_dctx (DOT _format) (Vint (Int.repr fmt)) (a_d a);
              field_at Ews t_dctx (DOT _headerBuffer) c (a_d a); FR]))) R).
Proof.
intros Espec DENT TABS BR a w1 fmt c hb b FR P P' R Hfmt Hc Hhb18 Hsub Hbok Hhb4 Hb HPP.
apply c10_props_pre; intro HP.
match goal with |- semax ?D ?Pre ?cc (overridePost (PROPx _ ?LS) ?RR) =>
  apply (c10_post_n D Pre cc _ (PROPx [] LS) RR); [| apply andp_left2; apply c10_props_post; auto] end.
destruct R as [Rn Rb Rc Rr]. cbv beta iota delta [overridePost].
pose proof (Zlength_nonneg hb) as Hhb0.
unfold ds_Delta. simplify_func_tycontext. unfold c10_a, ds_LI_L. abbreviate_semax.
forward.
eapply semax_pre; [apply andp_left2; apply now_later |].
destruct Hfmt as [Hf0|Hf0]; subst fmt.
- apply semax_ifthenelse_PQR' with (v := Vint Int.one); [reflexivity | entailer! | entailer! | |].
  2: { apply semax_extract_PROP; intro Hcc. exfalso. cbv in Hcc. congruence. }
  apply semax_extract_PROP; intros _.
  rewrite (c10_hbuf_split (a_d a) c (Zlength hb)) by lia.
  rewrite Hsub. flatten_sepcon_in_SEP.
  assert_PROP (isptr (field_address t_dctx (DOT _headerBuffer) (a_d a))) as Hhbp by entailer!.
  forward_call (Ews, field_address t_dctx (DOT _headerBuffer) (a_d a), hb, 0).
  { entailer!. clear - Hhbp. unfold field_address in *.
    destruct (field_compatible_dec _ _ _); [reflexivity | contradiction]. }
  { unfold mem_read_pre. specialize (Hhb4 eq_refl).
    repeat split; auto; try lia. apply Forall_sublist. auto. }
  forward.
  rewrite <- Hsub.
  sep_apply (c10_hbuf_merge (a_d a) c (Zlength hb)); [lia | auto].
  entailer!.
  rewrite c10_skip_magic_eq' by (apply c10_le_field4_range; auto).
  destruct (is_skippable_magic _); reflexivity.
- apply semax_ifthenelse_PQR' with (v := Vint Int.zero); [reflexivity | entailer! | entailer! | |].
  { apply semax_extract_PROP; intro Hcc. exfalso. cbv in Hcc. congruence. }
  apply semax_extract_PROP; intros _.
  forward.
  entailer!.
Qed.

Lemma c10_La : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) dd cold lxb (R: ret_assert),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (c10_S2x DENT TABS a w k1 h tbl dd cold lxb) c10_a
    (overridePost (c10_S2b DENT TABS a w k1 h tbl dd cold lxb) R).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 dd cold lxb R HP k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hsp & Hg & Hf & HA).
assert (Hsk := c10_sk_flag (w_k w) hb h Hf).
destruct He as (Hstg & Hlh & Hhb18 & Hhbok & Hhbsub & Hhost & Hinp & Hos & Hoe & Hipc & Hopc & Hoc & Hsmw & Hbc & Hlen).
destruct Hf as (Hhb5 & _). unfold lh_mg in Hhb5.
unfold c10_S2x, c10_S2b.
rewrite (c10_prop_sep _ _ _ _ _ (c10_vA DENT TABS a w (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb) tbl)).
rewrite (c10_prop_sep _ _ _ _ _ (c10_vA DENT TABS a w (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb) tbl)).
apply semax_extract_PROP; intros ((Hcold & Hpar) & Hsg).
eapply c10_La_core with (hb := hb).
- exact (proj1 Hpar).
- exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsg))))))).
- exact Hhb18.
- exact Hhbsub.
- exact Hhbok.
- intros E. change (c3_par (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)) with (c3_par (w_k w)) in E.
  rewrite E in Hhb5. cbn in Hhb5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hhb5. lia.
- symmetry. exact (Hsk Hpar).
- intros H. cbn [fold_right] in H |- *. split; [exact (conj (conj Hcold Hpar) Hsg) | exact H].
Qed.

End CM_LH3C2_s10a_1.
