(* FS3 streaming, case zdss_loadHeader: G1, the break after the header bytes are loaded -> loop invariant. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib.
Local Open Scope logic.

Section CM_LH3G1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g1_dec_nohdr : forall md d wl s, (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  forall out k, decode_frame_m md d wl s <> FOk out k.
Proof.
intros md d wl s H out k. unfold decode_frame_m. cbv zeta.
destruct (get_frame_header_m (md_magicless md) s) eqn:E; try (exfalso; exact (H _ eq_refl));
repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma g1_walk_cur_none : forall fuel md wl s, walk_cur fuel md sel_none None wl s = None.
Proof.
induction fuel; intros md wl s; cbn [walk_cur]; auto.
destruct (Zlength s <? starting_len (md_magicless md)); auto.
destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
- destruct (skippable_frame_size s); auto.
  replace (skip_cd md sel_none s None) with (@None dict_model)
    by (unfold skip_cd, sel_none; destruct (md_dwin md); reflexivity).
  apply IHfuel.
- unfold frame_dict, sel_none. destruct (get_frame_header_m _ s) eqn:E; auto;
  destruct (decode_frame_m md no_dict wl s) eqn:D; auto;
  exfalso; refine (g1_dec_nohdr md no_dict wl s _ _ _ D); intros h; rewrite E; discriminate.
Qed.

Lemma g1_clean_ids : forall l, set_clean l = true -> Forall (fun e => dd_id (snd e) <> 0) l.
Proof.
intros l Hc. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. apply Forall_forall. intros e He. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.

Lemma g1_find0 : forall l, Forall (fun e => dd_id (snd e) <> 0) l -> set_find l 0 = nullval.
Proof.
intros l Hl. unfold set_find. destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:E; auto.
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
rewrite Forall_forall in Hl. exfalso. exact (Hl _ Hin Heq).
Qed.

Lemma g1_cd : hs_probe_ok -> forall st k hb kk v tbl d1 did1 cd k',
  base_call st k -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  lhA_sel k hb kk v tbl d1 did1 -> get_frame_header_m (lh_mg k) hb = FH_more kk ->
  (st_sel st = (sel_none, None) -> cd = None) ->
  cur_dict_ok st k cd -> c3_dict k' = d1 -> fs_fParams (c3_fs k') = v -> cur_dict_ok st k' cd.
Proof.
intros Hpr st k hb kk v tbl d1 did1 cd k' Hb Hsp Hsel Hk Hcd Hold Hd' Hv'.
intros dm Hdm. destruct (Hold dm Hdm) as [H1 | (Hne & Huses & (dd & Hin & Hauto) & (id0 & Hid0 & Hr0 & Hf0))].
{ left; exact H1. }
right.
destruct Hb as (Hstab & Hpar & Hset & Hdr & Hsco).
assert (Hon: dp_multi (dc_par st) = 1 /\ set_clean (dc_set st) = true).
{ unfold st_sel in Hcd. destruct (dc_set st) eqn:Es; [ congruence | ].
  destruct (dc_dict st); [ | rewrite Hcd in Hdm by auto; discriminate ].
  destruct (dp_multi (dc_par st) =? 1) eqn:Em; [ | rewrite Hcd in Hdm by auto; discriminate ].
  destruct (set_clean (_ :: _)) eqn:Ec; [ | rewrite Hcd in Hdm by auto; discriminate ].
  split; [ apply Z.eqb_eq; auto | auto ]. }
destruct Hon as [Hmulti Hclean].
assert (Hso: sel_on (c3_par k) (c3_sp k) = true).
{ unfold sel_on. rewrite Hpar, Hmulti. cbn.
  assert (c3_sp k <> nullval) by (apply Hsp; rewrite Hset; auto).
  unfold veqb. destruct (Val.eq (c3_sp k) _) as [E|E]; [ exfalso; apply H; exact E | reflexivity ]. }
destruct Hsel as (_ & Hfh & id & Hid & Hsb).
specialize (Hid Hso). unfold sel_by in Hsb. rewrite Hso in Hsb. destruct Hsb as (Hinv & Hidr & Hd1 & _).
pose proof (g1_clean_ids _ Hclean) as Hnz. rewrite <- Hset in Hnz.
assert (Hdd: df_ddict (c3_dict k) <> nullval).
{ destruct Hinv as (_ & _ & _ & _ & _ & Hptr & _). rewrite Forall_forall in Hptr.
  rewrite <- Hset in Hin. specialize (Hptr _ Hin). cbn in Hptr. intro E; rewrite E in Hptr; exact Hptr. }
assert (Hr: sel_r (c3_dict k) (c3_set k) tbl id = set_find (c3_set k) id).
{ unfold sel_r. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf]. apply Hf; auto. }
rewrite Hr in Hd1. rewrite Hd', Hv'. subst d1.
unfold fh_post_m in Hfh. rewrite Hk in Hfh. destruct Hfh as [_ Hv].
assert (Hcase: id = id0 \/ id = 0).
{ destruct (Zlength hb <? starting_len (lh_mg k)).
  - left. subst v. rewrite Hid0 in Hid. apply Vint_inj in Hid.
    apply (f_equal Int.unsigned) in Hid. rewrite !Int.unsigned_repr in Hid by lia. lia.
  - right. subst v. cbn in Hid. apply Vint_inj in Hid.
    apply (f_equal Int.unsigned) in Hid. rewrite (Int.unsigned_repr id) in Hid by lia.
    change (Int.unsigned (Int.repr 0)) with 0 in Hid. lia. }
rewrite Hset in *.
destruct Hcase as [-> | ->].
- destruct Hf0 as [Hf0 | Hf0].
  + unfold sel_dict. rewrite Hf0. destruct (eq_dec nullval nullval); [ | congruence ].
    split; [ exact Hne | split; [ exact Huses | split; [ exists dd; split; [ exact Hin | exact Hauto ] | exists id0; auto ] ] ].
  + unfold sel_dict. rewrite Hf0. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
    cbn. split; [ exact Hne | split; [ auto | split; [ exists dd; split; [ exact Hin | exact Hauto ] | exists id0; auto ] ] ].
- rewrite (g1_find0 _ Hnz). unfold sel_dict. destruct (eq_dec nullval nullval); [ | congruence ].
  split; [ exact Hne | split; [ exact Huses | split; [ exists dd; split; [ exact Hin | exact Hauto ] | ] ] ].
  exists 0. split; [ auto | split; [ cbn; lia | left; apply g1_find0; auto ] ].
Qed.

Lemma g1_dict_rel : hs_probe_ok -> forall st k hb kk v tbl d1 did1,
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> dict_rel3 st d1.
Proof.
intros Hpr st k hb kk v tbl d1 did1 Hb Hsel.
destruct Hb as (_ & _ & Hset & Hdr & _).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb.
destruct (sel_on (c3_par k) (c3_sp k)).
- destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict.
  destruct (eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval) as [E|E]; [ exact Hdr | ].
  right. unfold sel_r in *.
  destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [[Hn | Hin] _]; [ contradiction | ].
  rewrite Hset in Hin. split.
  + intro Hnil. rewrite Hnil in Hin. contradiction.
  + unfold dict_switched, switch_fields. cbn. rewrite Hset. auto.
- destruct Hsb as [Hd1 _]. subst d1. exact Hdr.
Qed.

Lemma g1_hsize_rng : forall fhd, 5 <= fhd_header_size fhd <= 18.
Proof.
  intros fhd. unfold fhd_header_size.
  assert (Hs: Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1).
  { rewrite (Z.land_ones _ 1) by lia. pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) 2). change (2 ^ 1) with 2. lia. }
  assert (Hd: forall n, 0 <= nth n [0; 1; 2; 4] 0 <= 4).
  { intros [|[|[|[|n]]]]; simpl; try destruct n; lia. }
  assert (Hf: forall n, 0 <= nth n [0; 2; 4; 8] 0 <= 8).
  { intros [|[|[|[|n]]]]; simpl; try destruct n; lia. }
  pose proof (Hd (Z.to_nat (Z.land fhd 3))). pose proof (Hf (Z.to_nat (Z.shiftr fhd 6))).
  remember (nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) as d.
  remember (nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0) as f.
  destruct Hs as [Hs|Hs]; rewrite Hs.
  - change (0 =? 1) with false. cbn [andb]. lia.
  - change (1 =? 1) with true. cbn [andb]. destruct (Z.shiftr fhd 6 =? 0); lia.
Qed.

Lemma g1_more_rng0 : forall x k, get_frame_header x = FH_more k -> 0 < k <= 18.
Proof.
intros x k H. unfold get_frame_header in H. cbv zeta in H.
pose proof (g1_hsize_rng (byte_at x 4)).
repeat match type of H with
| context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
end; try discriminate; inversion H; subst; unfold ZSTD_SKIPPABLEHEADERSIZE; lia.
Qed.

Lemma g1_more_rng : forall mg x k, get_frame_header_m mg x = FH_more k -> k <= 18.
Proof.
intros mg x k H. unfold get_frame_header_m in H. destruct mg; cbn [negb] in H.
- destruct (Zlength x <? 1); [ inversion H; lia | ].
  destruct (get_frame_header (magic_bytes ++ x)) eqn:E; try discriminate.
  inversion H; subst. apply g1_more_rng0 in E. lia.
- apply g1_more_rng0 in H. lia.
Qed.

Lemma g1_fp_more : forall mg hb kk v0 v, fh_post_m mg hb kk v0 v -> get_frame_header_m mg hb = FH_more kk ->
  fp_ok v0 -> fp_ok v.
Proof.
intros mg hb kk v0 v H E H0. unfold fh_post_m in H. rewrite E in H. destruct H as [_ ->].
destruct (_ <? _); auto. exists 0. split; [ reflexivity | rep_lia ].
Qed.

Lemma g1_PROP_intro : forall (P: Prop) Ps QR, P -> PROPx Ps QR |-- PROPx (P :: Ps) QR.
Proof.
intros. unfold PROPx. apply andp_right.
- apply andp_left1. intro rho. simpl. apply prop_derives. tauto.
- apply andp_left2. apply derives_refl.
Qed.

Lemma g1_PROP_intro2 : forall (P: Prop) Ps Qs QR, P -> PROPx Qs QR |-- PROPx Ps QR -> PROPx Qs QR |-- PROPx (P :: Ps) QR.
Proof. intros. eapply derives_trans; [ exact H0 | apply g1_PROP_intro; auto ]. Qed.

Lemma g1_sp : forall DENT TABS a w,
  lh_st DENT TABS a w |-- !! (c3_set (w_k w) <> nil -> c3_sp (w_k w) <> nullval).
Proof.
intros. unfold lh_st, ds_LI_S, ctx_rep3, ctx_body3, hset_rep.
destruct (eq_dec (c3_sp (w_k w)) nullval).
- go_lowerx. Intros. apply prop_right. intros Hn. contradiction.
- go_lowerx. apply prop_right. auto.
Qed.

(* the loop state after the break: the header bytes hb followed by the m = kk - |hb| input bytes u at ipc *)
Definition g1_w (a: dsa) (w: lw) (hb: list Z) (kk: Z) (v: reptype t_fh) (d1: dfields) (did1: val) : lw :=
  let m := kk - Zlength hb in
  let u := sublist (w_ipc w) (w_ipc w + m) (a_ibs a) in
  {| w_smw := w_smw w; w_k := w_k (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk);
     w_sv := {| sv_fp := FP_hdr (hb ++ u); sv_pend := nil; sv_ahead := nil; sv_lay := sv_lay (w_sv w);
                sv_dd := sv_dd (w_sv w) |};
     w_ipc := w_ipc w + m; w_opc := w_opc w; w_oc := w_oc w; w_dl := nil |}.

(* G1 with its witness: the relational loop invariant holds of g1_w (the exact version adds ex_call for it) *)
Lemma lh_brkA_w : MF3 -> hs_probe_ok ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (kk: Z) (v: reptype t_fh) (tbl: list val) (d1: dfields) (did1: val),
    lh_ctx a w hb -> lhA_sel (w_k w) hb kk v tbl d1 did1 ->
    get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> kk - Zlength hb <= a_isz a - w_ipc w ->
    lh_st DENT TABS a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk) |--
    PROPx (ds_LI_P a (g1_w a w hb kk v d1 did1))
      (LOCALx (ds_LI_L a (g1_w a w hb kk v d1 did1)) (SEPx (ds_LI_S DENT TABS a (g1_w a w hb kk v d1 did1)))).
Proof.
intros MFh Hpr DENT TABS a w hb kk v tbl d1 did1 Hctx Hsel Hk Hkk.
eapply derives_trans; [ apply andp_right; [ apply g1_sp | apply derives_refl ] | ].
apply derives_extract_prop. intros Hsp.
eapply derives_trans; [ apply andp_right; [ apply rl_st_held | apply derives_refl ] | ].
apply derives_extract_prop. intros Hheld.
destruct Hctx as (Ha & Hstart & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hentry & Hunt).
pose proof (mf_hdr_more_size MFh _ hb kk Hk) as Hlt.
pose proof (g1_more_rng _ hb kk Hk) as Hk18.
set (m := kk - Zlength hb) in *.
assert (Hm0: 0 < m /\ kk = Zlength hb + m) by (unfold m; lia).
set (u := sublist (w_ipc w) (w_ipc w + m) (a_ibs a)).
set (k1 := k_A (w_k w) v d1 did1).
unfold g1_w. cbv zeta. fold m. fold u. fold k1.
unfold lh_st, ds_LI_P.
apply g1_PROP_intro2; [ | apply g1_PROP_intro2; [ | apply g1_PROP_intro2; [ | apply g1_PROP_intro2;
  [ | apply g1_PROP_intro2; [ | apply g1_PROP_intro2; [ | ] ] ] ] ] ].
7: { apply derives_refl. }
6: { exact Hunt. }
5: { unfold entry_ok. cbn. intros _ Hs0. exfalso. destruct He as (Hst0 & _). rewrite Hst0 in Hs0.
     unfold zdss_loadHeader, zdss_init in Hs0. lia. }
4: { unfold exit_ok. intros Hs0. cbn in Hs0. lia. }
3: { intros _ _. cbn. auto. }
2: { cbn. auto. }
assert (Hdr1: dict_rel3 (a_st a) d1).
{ destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb0 & _). eapply g1_dict_rel; eauto. }
destruct Hci as (Hipc & Hopc & Hloc & Hpre & Hdll & Hdlc & Hdlb & Hbase & Hsinb & Hnfp1 & Hnfp2 & Hnfp0 & Hcore &
                 Hddok & Hstout & Hahd & Hblk & Halive & Hlh & Hsin & Hexp & HTf).
destruct He as (Hst & Hlh' & H18 & Hbo & Hsub & Hhost & HinPos & Hos & Hoe & Hipc' & Hopc' & Hlo & Hsmw' & Hbase' & Hlenok).
destruct Hcore as (_ & Hcold & Hsz & _).
assert (Hib: Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\ 0 <= a_ipos a) by (unfold dsa_ok in Ha; tauto).
destruct Hib as (Hibl & Hibb & Hip0).
rewrite Hdl, Hah, Hpend, Hfp in *.
assert (Hop: w_opc w = a_opos a) by (rewrite Zlength_nil in Hdll; lia).
assert (Hlu: Zlength u = m) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hub: bytes_ok u) by (unfold u, bytes_ok in *; apply Forall_sublist; auto).
assert (Hbu: bytes_ok (hb ++ u)) by (unfold bytes_ok in *; apply Forall_app; auto).
assert (Hx: hdr_lenok (lh_mg (w_k w)) (hb ++ u)).
{ pose proof (mf_hdr_more_ext MFh _ hb u kk Hbu Hk ltac:(rewrite Zlength_app; lia)) as Hx.
  unfold hdr_lenok. destruct (get_frame_header_m _ (hb ++ u)); auto.
  intro Hnil. apply (f_equal (@Zlength Z)) in Hnil. rewrite Zlength_app, Zlength_nil in Hnil.
  pose proof (Zlength_nonneg hb). lia. }
(* base_call (closed by the assumption below) *)
assert (Hbase1: base_call (a_st a) (w_k (lhA_brk a w k1 hb kk))).
{ apply (rl_base_with _ (w_k w)); [ exact Hbase | exact Hdr1 | reflexivity | reflexivity | reflexivity | |
    exact (lhA_sel_redict _ _ _ _ _ _ _ Hsel) | reflexivity | exact (held_redict_set _ _ _) | exact Hheld ].
  destruct Hsel as (_ & Hfh & _). exact (g1_fp_more _ _ _ _ _ Hfh Hk (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hbase))))))). }
unfold call_inv.
change (kk - Zlength hb) with m.
unfold k1. cbn [lhA_brk w_k w_sv w_ipc w_opc w_oc w_dl].
unfold lh_k_load, k_A, k_redict, held_redict, sf_with_held. change (kk - Zlength hb) with m. fold u.
cbn [lhA_brk w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_with_fs c3_with_dict c3_s c3_fs c3_tabs c3_stable
     c3_dict c3_par c3_sp c3_set sf_lh sv_fp sv_pend sv_ahead sv_lay sv_dd sf_nfp sf_stage sf_expOut sf_hostage
     fsu_fParams fsu_dictID fs_fParams fs_ddictIsCold].
repeat match goal with |- _ /\ _ => split end.
all: try lia.
all: try (left; lia).
all: try assumption.
all: try (intros; congruence).
all: unfold c3_with_s, c3_with_fs, c3_with_dict, sf_lh, fsu_fParams, fsu_dictID.
all: cbn [c3_s c3_fs c3_tabs c3_stable c3_dict c3_par c3_sp c3_set sf_stage sf_hostage sf_inPos sf_outStart
          sf_outEnd sf_lhSize sf_hbuf sf_inSize sf_outSize sf_nfp sf_expOut fs_ddictIsCold fs_fParams sv_fp sv_pend
          sv_ahead sv_lay sv_dd].
- (* c_core, stage loadHeader *)
  unfold c_core.
  cbn [c3_s c3_fs c3_par sf_stage sf_hostage sf_inPos sf_outStart sf_outEnd sf_lhSize sf_hbuf sf_inSize sf_outSize
       fs_ddictIsCold sv_fp sv_pend sv_ahead].
  rewrite Hst. split; [ right; left; auto | ]. split; [ exact Hcold | ]. split; [ exact Hsz | ].
  unfold zdss_init, zdss_loadHeader. change (1 =? 0) with false. change (1 =? 1) with true. cbv beta iota.
  split; [ auto | ]. split; [ exact Hhost | ]. split; [ exact HinPos | ]. split; [ exact Hos | ].
  split; [ exact Hoe | ].
  exists (hb ++ u). split; [ auto | ]. split; [ rewrite Zlength_app; lia | ].
  split; [ exact Hbu | ].
  split; [ rewrite Zlength_app, Hlu; auto | ].
  split; [ | exact Hx ].
  unfold hb_splice. rewrite Hsub, map_app, app_assoc.
  replace (Zlength (hb ++ u)) with (Zlength (zbytes hb ++ zbytes u)) by (rewrite !Zlength_app, !Zlength_map; auto).
  rewrite sublist0_app1 by (split; [ apply Zlength_nonneg | rewrite !Zlength_app, !Zlength_map; lia ]).
  apply sublist_same; auto.
- (* sv_dd_ok *)
  unfold sv_dd_ok. cbn [c3_s sf_stage]. rewrite Hst. unfold zdss_read, zdss_loadHeader. lia.
- (* the model *)
  unfold alive_ok in *. rewrite !app_nil_r in *.
  rewrite (sublist_split (a_ipos a) (w_ipc w) (w_ipc w + m)) by lia. fold u. rewrite app_assoc.
  destruct Halive as [Hd | (cd & Hm & Hcd & Hh)].
  + left. apply (mf_dead_app MFh); auto.
  + right. exists cd.
    destruct Hm as (dsin & fb & recs & Hsin' & Hser & Hcur & Hcr & Hout).
    rewrite Hfp in Hcr, Hcd, Hout; rewrite Hpend in Hout. cbn [cur_rel] in Hcr. destruct Hcr as [Hfb _]. subst fb.
    split; [ | split ].
    * exists dsin, (hb ++ u), recs. split; [ rewrite Hsin', app_assoc; auto | ]. split; [ exact Hser | ].
      split; [ exact Hcur | ]. split; [ | exact Hout ].
      cbn [cur_rel]. split; [ auto | ].
      replace (md_magicless (sm_md (sm_of (a_st a)))) with (lh_mg (w_k w)); [ exact Hx | ].
      unfold lh_mg. cbn. destruct Hbase as (_ & Hpar & _). rewrite Hpar. reflexivity.
    * cbn [next_cd] in *.
      apply (g1_cd Hpr (a_st a) (w_k w) hb kk v tbl d1 did1 cd); auto.
      intro E. rewrite <- Hcur. unfold series_cur, sm_of. cbn [sm_sel sm_cur]. rewrite E. cbn [fst snd].
      apply g1_walk_cur_none.
    * unfold hist_ok. intros _ _ Hne. exfalso. apply Hne. cbn. exact Hst.
- (* the header's bytes *)
  intros _ hb0 Heq. inversion Heq; subst hb0.
  destruct (Hlh Hst hb eq_refl) as (pre & j & Hj & Hhb & ->).
  exists pre, (a_ipos a). split; [ lia | ]. split; [ | auto ].
  rewrite Hhb, <- app_assoc. f_equal. unfold u.
  rewrite (sublist_split (a_ipos a) (w_ipc w) (w_ipc w + m)) by lia. reflexivity.
Qed.

Lemma lh_brkA_ok : lh_brkA_stmt.
Proof.
intros MFh Hpr DENT TABS a w hb kk v tbl d1 did1 Hctx Hsel Hk Hkk.
eapply derives_trans; [ exact (lh_brkA_w MFh Hpr DENT TABS a w hb kk v tbl d1 did1 Hctx Hsel Hk Hkk) | ].
unfold ds_inv. Exists (g1_w a w hb kk v d1 did1). apply derives_refl.
Qed.

End CM_LH3G1_1.
