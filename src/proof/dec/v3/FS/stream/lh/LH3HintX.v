(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: the hint return (the input ends inside the header): stream_exact by the model's early return, and the next context's exact relation. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Hint.
Require Import Zstd.proof.model.ParamsH Zstd.proof.model.ExCall Zstd.proof.model.ExStreamFacts.
Require Zstd.proof.model.ExStream Zstd.proof.model.Exact.
Local Open Scope logic.

Section CM_LH3HintX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the configuration of a new context reads the format zstd1 *)
Lemma hx_mg : forall a w hb, lh_ctx a w hb -> fresh_cfg (a_st a) -> lh_mg (w_k w) = false.
Proof.
intros a w hb Hc (_ & Hp & _). rewrite (h_mg a w hb Hc), Hp. reflexivity.
Qed.

Lemma hx_slice : forall (l: list Z) i k, 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof.
intros l i k Hi Hk. unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.

(* the model's hint (ExStream.st_load_header) is the C's (lh_hint, format zstd1) *)
Lemma hx_hint : forall (hb1: list Z) (kk: Z),
  (if orb (Zlength hb1 <? ExStream.ZS_FRAMEIDSIZE) (is_skippable_magic (le_field hb1 0 4))
   then (if Zlength hb1 <? ExStream.ZS_FRAMEIDSIZE then ZSTD_SKIPPABLEHEADERSIZE else kk) - Zlength hb1
   else Z.max ZSTD_FRAMEHEADERSIZE_MIN kk - Zlength hb1 + ZSTD_blockHeaderSize) = lh_hint false hb1 kk.
Proof.
intros. unfold lh_hint, is_skippable_frame, ExStream.ZS_FRAMEIDSIZE, ZSTD_FRAMEHEADERSIZE_MIN. cbn [negb andb].
destruct (Zlength hb1 <? 4); cbn [orb]; [reflexivity|].
destruct (is_skippable_magic _); reflexivity.
Qed.

Lemma hx_model : forall a w hb r ipos' w',
  lh_ctx a w hb -> lhx_entry a w -> lh_rc_hint a w hb r ipos' w' -> fresh_cfg (a_st a) ->
  exists z1,
    Exact.zs_call (ss_calls (dc_ss (a_st a))) (a_xin a, a_xroom a) =
      Some (r, Zlength (a_xin a), nil, ExStream.zs_nfp XS z1, 0) /\
    zs_run_x (ss_calls (dc_ss (a_st a)) ++ [(a_xin a, a_xroom a)]) = Some z1 /\
    zinv_x z1 /\ zrel z1 (sf_strip (c3_s (w_k w'))) (c3_fs (w_k w')) (c3_tabs (w_k w')).
Proof.
intros a w hb r ipos' w' Hc Hx Hrc Hf.
destruct Hrc as (kk & v & tbl & d1 & did1 & r' & v' & Hsel & Hk & Hlt0 & Hfh2 & Hne2 & Hfpv & -> & -> & ->).
destruct (h_facts a w hb Hc) as (Hah0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
fold (h_u a w) in *.
pose proof Hc as (Ha & _ & _ & _ & _ & He & _).
destruct (lhx_view a w hb He Hx Hf) as (z0 & zi & f & Hl & Hz & Hst & Hhb & Hone).
pose proof (hx_mg a w hb Hc Hf) as Hmg.
rewrite Hmg, get_frame_header_zstd1 in Hk, Hne2.
assert (Hlx: Zlength (a_xin a) = a_isz a - a_ipos a) by (unfold a_xin; rewrite Zlength_sublist; lia).
assert (Hsl: slice (a_xin a) (w_ipc w - a_ipos a) (Zlength (a_xin a) - (w_ipc w - a_ipos a)) = h_u a w).
{ rewrite hx_slice by lia. unfold a_xin, h_u. rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia. }
assert (Hearly: one_iter_x (a_xin a) (a_xroom a) zi (w_ipc w - a_ipos a) nil =
                ExStream.LEarly XS (ExStream.z_hbuf XS zi (hb ++ h_u a w)) (lh_hint false (hb ++ h_u a w) kk)).
{ rewrite Hone. unfold ExStream.st_load_header. rewrite Hhb, Hk. cbv zeta.
  rewrite Hsl. destruct (Z.gtb_spec (kk - Zlength hb) (Zlength (a_xin a) - (w_ipc w - a_ipos a))); [|lia].
  rewrite <- hx_hint. destruct (get_frame_header (hb ++ h_u a w)); [contradiction| |]; reflexivity. }
assert (Hro: 0 <= a_xroom a).
{ destruct Ha as (_&_&_&_&_&_&_&_&_&Hop&_). unfold a_xroom; lia. }
assert (Hip': 0 <= w_ipc w - a_ipos a <= Zlength (a_xin a)) by lia.
destruct (ex_loop_early a z0 zi f _ nil _ _ Hro Hip' Hl Hearly) as [Hcall Hrun].
exists (ExStream.z_hbuf XS zi (hb ++ h_u a w)). rewrite Hmg.
split; [exact Hcall|]. split; [exact Hrun|]. split.
{ destruct Hl as (_ & _ & Hzi & _). unfold zinv_x in *. apply zinv_hbuf; [exact Hzi | exact Hbu]. }
destruct (h_kfacts a w hb (w_k w) v d1 did1 v') as (Hs' & _).
cbn [w_k lw_k]. rewrite Hs'.
pose proof (LHH4Model.lhh_more_le18 false hb kk ltac:(rewrite get_frame_header_zstd1; exact Hk)) as Hk18.
assert (Hhs: sublist 0 (Zlength (hb ++ h_u a w)) (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) (h_u a w)) =
             zbytes (hb ++ h_u a w)).
{ destruct He as (_ & _ & _ & _ & Hsub & _).
  unfold hb_splice. rewrite Hsub, map_app, app_assoc.
  replace (Zlength (hb ++ h_u a w)) with (Zlength (zbytes hb ++ zbytes (h_u a w)))
    by (rewrite !Zlength_app, !Zlength_map; auto).
  rewrite sublist0_app1 by (split; [ apply Zlength_nonneg | rewrite !Zlength_app, !Zlength_map; lia ]).
  apply sublist_same; auto. }
unfold w_sx, w_fs, w_tabs in Hz. unfold zrel in Hz |- *.
unfold sf_lh, held_redict, sf_with_held, sf_strip in Hz |- *. cbn in Hz, Hhs |- *.
rewrite Hhb in Hz.
destruct Hz as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Zl & Zr).
split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|]. split; [exact Z10|].
split; [| intros Hr; rewrite Hst in Hr; unfold ExStream.ZDSS_read, ExStream.ZDSS_loadHeader in Hr; lia].
intros _. destruct (Zl Hst) as (L1 & L2 & L3 & L4 & L5).
split; [rewrite Zlength_app, Hlu; reflexivity|].
split; [rewrite Zlength_app in *; lia|].
split; [exact Hbu|].
split; [exact Hhs|exact L5].
Qed.

(* the context after the hint return is in the exact relation (FSRep3.ex_on3 with S3XRel.xrel3): the call was added
   to the history, so the stream is not a new one and its configuration is the call's, a new context's *)
Lemma hx_ex_on : forall a w hb r ipos' w',
  lh_ctx a w hb -> lhx_entry a w -> lh_rc_hint a w hb r ipos' w' -> ex_on3 SR3 (hint_st a r) (w_k w').
Proof.
intros a w hb r ipos' w' Hc Hx Hrc. unfold ex_on3. intros Hex _ Hcfg.
assert (Hf: fresh_cfg (a_st a)).
{ destruct Hcfg as [E | (D & P & S & B)].
  - exfalso. apply (f_equal ss_calls) in E. unfold hint_st, ss_init in E. cbn in E.
    destruct (ss_calls (dc_ss (a_st a))); discriminate.
  - unfold hint_st in *. cbn in *. unfold fresh_cfg. tauto. }
destruct (hx_model a w hb r ipos' w' Hc Hx Hrc Hf) as (z1 & _ & Hrun & Hinv & Hzr).
exists z1. split; [exact Hrun|]. split; assumption.
Qed.

(* stream_exact for the hint return: the model's call returns the hint, takes all the input and writes nothing *)
Lemma hx_exact : forall a w hb r ipos' w' oc',
  lh_ctx a w hb -> lhx_entry a w -> lh_rc_hint a w hb r ipos' w' ->
  stream_exact (a_st a) (hint_st a r) r (a_osz a) (a_opos a) (a_opos a) oc' (a_ibs a) (a_isz a) (a_ipos a) (a_isz a).
Proof.
intros a w hb r ipos' w' oc' Hc Hx Hrc Hf. right. cbv zeta.
destruct (hx_model a w hb r ipos' w' Hc Hx Hrc Hf) as (z1 & Hcall & _).
destruct (h_facts a w hb Hc) as (Hah0 & _ & _ & _ & _ & Hip & Hipc & Hibl & _).
change (sublist (a_ipos a) (a_isz a) (a_ibs a), a_osz a - a_opos a) with (a_xin a, a_xroom a).
rewrite Hcall.
assert (Hlx: Zlength (a_xin a) = a_isz a - a_ipos a) by (unfold a_xin; rewrite Zlength_sublist; lia).
split; [reflexivity|]. split; [lia|]. split; [rewrite Zlength_nil; lia|].
split; [rewrite sublist_nil; reflexivity|].
exists (if a_ipos a =? a_isz a then ss_stall (dc_ss (a_st a)) + 1 else 0).
destruct Hf as (_ & _ & _ & Hstab & _).
unfold hint_st, ss_after. rewrite Hstab, Hah0. f_equal. f_equal. f_equal.
rewrite !Z.add_0_r, Hlx. unfold a_xin. rewrite (sublist_same 0 (a_isz a - a_ipos a) (sublist (a_ipos a) (a_isz a) (a_ibs a)))
  by (rewrite ?Zlength_sublist; lia). reflexivity.
Qed.

(* the context after the hint return in DC3x with the exact relation *)
Lemma hx_DC : forall DENT TABS BR (gv: globals) (p: val) (k: cst3) (st: dctx_st),
  TABS_OK TABS -> base_rel3 st k -> SR3 gv st k -> dc_bl st = None -> ex_on3 SR3 st k ->
  ctx_rep3 DENT TABS gv p k |-- DC3x DENT TABS SR3 BR gv p st && valid_pointer p.
Proof.
intros DENT TABS BR gv p k st HT Hb HS Hbl Hex.
apply andp_right; [| apply h_ctx_valid; auto].
unfold DC3x, DC3_of. Exists k. apply andp_right; [| apply derives_refl].
apply prop_right. split; [exact Hb|]. split; [|split].
- intros _ _; left; exact HS.
- intros ba H; congruence.
- exact Hex.
Qed.

Lemma lh_hint_x_ok : lh_hint_x_stmt.
Proof.
intros HMF Hpr DENT TABS BR a w hb r ipos' w' HT Hc Hx Hr0 Hrc.
pose proof (hx_ex_on a w hb r ipos' w' Hc Hx Hrc) as Hexo.
pose proof (hx_exact a w hb r ipos' w' (w_oc w) Hc Hx Hrc) as Hexa.
destruct Hrc as (kk & v & tbl & d1 & did1 & r' & v' & Hsel & Hk & Hlt0 & Hfh2 & Hne2 & Hfpv & -> & -> & ->).
destruct (h_facts a w hb Hc) as (Hah0 & Hsin & Hnil & Hbu & Hlu & Hip & Hipc & Hibl & Hibb & Hstall).
fold (h_u a w) in *.
assert (Hlt: Zlength (hb ++ h_u a w) < kk) by (rewrite Zlength_app; lia).
set (r := lh_hint (lh_mg (w_k w)) (hb ++ h_u a w) kk) in *.
unfold lh_ret_goal_x.
eapply derives_trans; [ apply andp_right; [ apply h_held | apply derives_refl ] | ].
apply derives_extract_prop. intros Hheld. cbn [w_k lw_k] in Hheld, Hexo.
set (k' := lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v') in *.
pose proof Hc as (Ha & _ & Hci & _).
destruct Hci as (_ & _ & Hloc & Hpre & _).
pose proof (h_post HMF a w hb kk (w_oc w) Hc Hk Hlt Hloc Hpre) as Hpost. fold r in Hpost.
pose proof (h_prog a w hb kk Hc Hk Hlt) as Hprog. fold r in Hprog.
change (stream_progress (a_st a) (hint_st a r) r (a_osz a) (a_opos a) (a_opos a) (a_isz a) (a_ipos a) (a_isz a)
          (a_ibs a)) in Hprog.
pose proof (h_base Hpr a w hb kk v tbl d1 did1 v' r Hc Hsel Hk Hlt Hfpv Hheld) as Hbase. fold k' in Hbase.
pose proof (h_SR HMF Hpr a w hb kk v tbl d1 did1 r' v' r Hc Hsel Hk Hlt Hfh2 Hne2) as HSR. fold k' in HSR.
assert (Hbl: dc_bl (hint_st a r) = None)
  by (destruct Ha as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hbl) & _); exact Hbl).
(* nothing was delivered (w_opc = a_opos): the output cells are the caller's *)
assert (Hun: stream_untouched (a_st a) r (a_osz a) (a_opos a) (a_oc a) (w_oc w)).
{ pose proof Hc as (_ & _ & Hci' & _ & _ & _ & _ & Hdl & _ & _ & _ & Hunt).
  pose proof Hci' as (_ & _ & _ & _ & Hdll & _).
  rewrite Hdl, Zlength_nil in Hdll.
  intros Hs _. replace (a_opos a) with (w_opc w) by lia. exact (Hunt Hs). }
unfold lh_ret_goal_x, ds_R_x, RA_return, frame_ret_assert, function_body_ret_assert.
unfold ds_LI_L, ds_S_ip, ds_post_x, stackframe_of; simpl fn_vars.
unfold lw_k; cbn [w_k w_opc w_oc w_ipc w_smw].
go_lowerx.
sep_apply (hx_DC DENT TABS BR (a_gv a) (a_d a) k' (hint_st a r) HT Hbase HSR Hbl Hexo).
unfold liftx, lift; simpl.
Exists r (a_opos a) (a_isz a) (w_oc w) (hint_st a r).
unfold var_block, eval_lvar; simpl.
unfold lvar_denote in H0.
destruct (Map.get (ve_of rho) _op) as [[b t]|] eqn:E; [|contradiction].
destruct H0 as [<- ->].
unfold liftx, lift; simpl. rewrite E. simpl.
sep_apply (data_at_data_at_ Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (Vptr b Ptrofs.zero)).
rewrite data_at__memory_block. entailer!.
apply derives_refl.
Qed.

End CM_LH3HintX_1.
