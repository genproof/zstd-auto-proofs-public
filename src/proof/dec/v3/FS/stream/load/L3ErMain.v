(* FS3 streaming, case zdss_load: an error of ZSTD_decompressContinueStream on the loaded unit:
   why it is allowed (S3Main.err_why; v2 StreamSeg_load.v load_err_why, v3 read/R3Err.v read_err_why3). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3ErRing.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3ErModelA Zstd.proof.dec.v3.FS.stream.load.L3ErModelB.
Local Open Scope logic.

Section CM_L3ErMain_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma er_is_prefix_app_r : forall (x y r: list Z), is_prefix (x ++ y) (x ++ y ++ r).
Proof.
intros. unfold is_prefix. rewrite app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r.
Qed.

Lemma er_is_prefix_trans : forall (x y s: list Z), is_prefix x y -> is_prefix y s -> is_prefix x s.
Proof.
unfold is_prefix. intros x y s H1 H2. rewrite <- H1 at 2. rewrite <- H2.
rewrite firstn_firstn. f_equal. rewrite <- H1, length_firstn. lia.
Qed.

Lemma er_ring_load_out : forall fp ring P ibs ipc L N1 N2,
  0 <= P -> 0 <= L -> P + L <= N1 -> 0 <= N2 -> Zlength ring = N1 + N2 -> 0 <= ipc -> ipc + L <= Zlength ibs ->
  sublist N1 (N1 + N2) (ring_load fp ring P ibs ipc L) = sublist N1 (N1 + N2) ring.
Proof.
intros fp ring P ibs ipc L N1 N2 HP HL HPL HN2 Hr Hi Hie. unfold ring_load.
destruct (is_skip fp); [reflexivity|].
unfold copy_cells.
assert (Hz: Zlength (zbytes ibs) = Zlength ibs) by list_solve.
rewrite app_assoc. rewrite sublist_app2; rewrite !Zlength_app, !Zlength_sublist by lia; [|lia].
rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* P_zunit_err without its 0 < zp_bsm *)
Lemma er_zunit_err0 : MF3 -> forall sm cd fb hdr z H u cap, bytes_ok fb -> 0 <= zp_bsm z -> zhist_ok sm z H ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cont_err (FP_zstd hdr z) H u cap -> cap_room z cap ->
  fbad sm cd (fb ++ u).
Proof.
intros M sm cd fb hdr z H u cap Hbf Hb Hz Hc Hg Hu Hbu He Hr.
destruct (Z.eq_dec (zp_bsm z) 0) as [E|E].
- eapply zunit_err0_3; eauto.
- eapply (mf_zunit_err M); eauto. lia.
Qed.

Lemma load_err_why3 : P_load_err_why.
Proof.
intros a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' M Hld0 Hs0 Hcb Hos Hor Hres Herr.
pose proof Hld0 as Hld1.
destruct Hld1 as (Ha&Hi&Hs&HE&HE0&HL&HLE&Hin&Hout&Hrl0&Hrl&Hbc&Hdd).
pose proof Ha as Ha'.
destruct Ha' as (_&_&_&_&_&_&_&_&_&Hopos&_&_&Hipos&_&Hlibs&Hbibs&_).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&H14&Hstout&H16&H17&Hmodel&_&Hsah&_).
destruct (load_facts _ _ _ _ _ Hcore Hs) as (E2&st2&HE2&_&HPE2&HE232&_&_&_&HEin&_).
rewrite HE in HE2. apply vlong_eq in HE2; [|lia|lia]. subst E2.
unfold c_core in Hcore. cbv zeta in Hcore.
destruct Hcore as (Hhost&Hcold&Hsz&Hrest). rewrite Hs in Hrest.
replace (zdss_load =? zdss_init) with false in Hrest by reflexivity.
replace (zdss_load =? zdss_loadHeader) with false in Hrest by reflexivity.
destruct Hrest as (_&Hcf&Hring&_&Hldd&_&_).
destruct (Hldd eq_refl) as (Hpend&Hnc&Hnraw&Hoso&Hinpos&Hpref).
assert (Hah: sv_ahead sv = nil).
{ destruct Hhost as [[Hx _]|[Hh|(_&_&_&_&_&Hx)]]; [rewrite Hs in Hx| apply Hh |rewrite Hs in Hx].
  - unfold zdss_load, zdss_init in Hx; lia.
  - unfold zdss_load, zdss_init, zdss_read, zdss_flush in Hx; lia. }
assert (Hah0: ss_ahead (dc_ss (a_st a)) = 0).
{ destruct Hs0 as (_&Hah01&Hahl&_). rewrite Hah, app_nil_r in Hsah. unfold a_sin in Hsah.
  apply (f_equal (@Zlength Z)) in Hsah. rewrite Zlength_sublist in Hsah by lia. lia. }
destruct Hres as (_&_&_&_&Hres). rewrite Herr in Hres. destruct Hres as (Hce&Hn80&Hn82).
assert (Hde: dec_err rr) by (split; [exact Herr|split; assumption]).
assert (Hsin0: a_sin a = ss_in (dc_ss (a_st a))).
{ unfold a_sin. rewrite Hah0, Z.sub_0_r. apply sublist_same; reflexivity. }
assert (HiL: ipc + L <= a_isz a) by lia.
assert (Hall: forall j, a_ipos a <= j <= a_isz a -> forall s, is_prefix (a_all a) s ->
                is_prefix (a_sin a ++ sublist (a_ipos a) j (a_ibs a)) s).
{ intros j Hj s Hs'. apply (er_is_prefix_trans _ (a_all a)); [|exact Hs'].
  unfold a_all. rewrite Hah0, Z.add_0_r, <- Hsin0.
  rewrite (sublist_split (a_ipos a) j (a_isz a)) by lia. apply er_is_prefix_app_r. }
assert (Hbsin: bytes_ok (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a))).
{ apply Forall_app; split; [exact Hbin|apply Forall_sublist; exact Hbibs]. }
rewrite Hah, app_nil_r in Hmodel.
set (sm := sm_of (a_st a)) in *.
assert (Hser: forall s, a_series a s = sm_series sm (sm_cur sm) (sm_wl sm) s) by reflexivity.
destruct Hmodel as [Hd|(cd&Hm&_&Hho)].
{ split; [exact Hde|right; left]. intros s Hbs Hs'. rewrite Hser.
  apply (dead_not_end3 _ _ s Hd). apply Hall; [lia|exact Hs']. }
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst pend ahead.
destruct fp as [|hb|hdr got|hdr z]; [unfold c_frame in Hcf; destruct Hcf as (_&_&_&_&_&F); contradiction F ..| |].
{ (* a skippable frame never fails *)
  exfalso. exact (Hce I). }
change (sm_of (a_st a)) with sm in Hm.
destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcr&Ho').
assert (Hph: match zp_ph z with ZP_body bh => bp_type (block_props_of bh) <> 0 | ZP_end => False | _ => True end).
{ cbn [fp_rawbody fp_complete] in Hnraw, Hnc. destruct (zp_ph z); auto; try discriminate.
  intro Hb. rewrite Hb in Hnraw. discriminate. }
destruct (cur_rel_unget _ _ _ fb hdr z Hcr Hph) as (fb0&Hfb&Hcur0).
assert (Hbfb: bytes_ok dsin /\ bytes_ok fb0).
{ rewrite Esin, Hfb in Hbsin. apply Forall_app in Hbsin. destruct Hbsin as [B1 B2].
  apply Forall_app in B2. tauto. }
cbn [fp_inpos] in HL, HLE, HPE2.
set (new := sublist ipc (ipc + L) (a_ibs a)) in *.
set (u := zp_got z ++ new).
assert (Hu: ld_u {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}
              (a_ibs a) ipc L = u) by reflexivity.
rewrite Hu in Hce.
assert (Hgotb: bytes_ok (zp_got z)).
{ destruct Hcf as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hg). exact Hg. }
assert (Hnew: Zlength new = L) by (unfold new; rewrite Zlength_sublist; lia).
assert (Hlu: Zlength u = E) by (unfold u; rewrite Zlength_app, Hnew; lia).
assert (Hbu: bytes_ok u) by (apply Forall_app; split; [exact Hgotb|apply Forall_sublist; exact Hbibs]).
pose proof (lcp_unit_z _ _ hdr z l dd E Hcf Hnc Hnraw HE HE0) as Hunit.
rewrite <- Hlu in Hunit.
assert (Hu_eq: dsin ++ fb0 ++ u = a_sin a ++ sublist (a_ipos a) (ipc + L) (a_ibs a)).
{ rewrite (sublist_split (a_ipos a) ipc (ipc + L)) by lia. rewrite (app_assoc (a_sin a)), Esin, Hfb.
  unfold u, new. rewrite !app_assoc. reflexivity. }
destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&Hb0&Hbsm&Hws&_).
assert (Hgot0: match zp_ph (zp_set_got z nil) with
               | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got (zp_set_got z nil) = nil
               | _ => zp_got (zp_set_got z nil) = nil end)
  by (cbn [zp_set_got zp_with zp_ph zp_got]; destruct (zp_ph z); auto).
assert (Hbad: forall H cap, zhist_ok sm (zp_set_got z nil) H -> cont_err (FP_zstd hdr (zp_set_got z nil)) H u cap ->
                cap_room (zp_set_got z nil) cap -> err_why a rr).
{ intros H cap Hz Hce' Hroom.
  pose proof (er_zunit_err0 M sm cd fb0 hdr (zp_set_got z nil) H u cap (proj2 Hbfb) ltac:(exact (proj1 Hb0))
                Hz Hcur0 Hgot0 Hunit Hbu Hce' Hroom) as Hfb'.
  split; [exact Hde|right; left]. intros s Hbs Hs'. rewrite Hser.
  apply (mf_bad_of_fbad M sm cd dsin recs (fb0 ++ u) s (proj1 Hbfb) Ef Ecd Hfb').
  rewrite Hu_eq. apply Hall; [lia|exact Hs']. }
destruct (dc_stable (a_st a)) eqn:Hst.
- (* stable: the caller's buffer at op *)
  destruct (ld_st_facts _ _ _ _ _ _ _ _ _ Hld0 Hst)
    as (_&_&_&_&Hring1&_&_&_&_&_&_&_&Hstout1&Hls&Hopc&Hloc&_&_&_&Hdds).
  cbn [sv_fp sv_lay sv_dd] in Hring1, Hdds.
  destruct (hist_pre_stable (a_shob a) (a_ob a) (a_osz a) oc _ _ _ _ hdr z l dd opc Hring1 Hcf Hdds Hstout1 Hls Hopc)
    as [Hhp HlH].
  specialize (Hce Hhp).
  match type of Hce with cont_err _ ?H _ _ => assert (HH: H = zp_hist z) by exact HlH; rewrite HH in Hce end.
  cbn [oa_cap o_st is_skip sv_fp] in Hce.
  assert (Hz: zhist_ok sm (zp_set_got z nil) (zp_hist z)) by (left; reflexivity).
  destruct (Z_le_gt_dec (zp_bsm z) (a_osz a - opc)) as [Hr1|Hr1].
  { exact (Hbad _ _ Hz Hce (or_introl Hr1)). }
  destruct (Z.eq_dec (fh_contentSize (zp_h z)) ZSTD_CONTENTSIZE_UNKNOWN) as [Hr2|Hr2].
  2: destruct (Z_le_gt_dec (fh_contentSize (zp_h z) - Zlength (zp_out z)) (a_osz a - opc)) as [Hr3|Hr3].
  2: { exact (Hbad _ _ Hz Hce (or_intror (conj Hr2 Hr3))). }
  all: split; [exact Hde|right; right]; split; [exact Hst|];
    intros s Hbs Hs' Hend; rewrite Hser in Hend |- *;
    assert (Hbsmf: cont_err (FP_zstd hdr (zp_set_got z nil)) (zp_hist z) u (zp_bsm (zp_set_got z nil)) ->
                   fbad sm (sm_curafter sm (sm_cur sm) dsin) (fb0 ++ u))
      by (intros Hc; unfold sm_curafter; rewrite Ecd;
          exact (er_zunit_err0 M sm cd fb0 hdr (zp_set_got z nil) (zp_hist z) u _ (proj2 Hbfb) ltac:(exact (proj1 Hb0)) Hz Hcur0 Hgot0 Hunit
                   Hbu Hc (or_introl (Z.le_refl _))));
    pose proof (zunit_err_cap3 M sm dsin recs fb0 hdr (zp_set_got z nil) (zp_hist z) u (a_osz a - opc) s
                  (proj1 Hbfb) (proj2 Hbfb) Ef ltac:(unfold sm_curafter; rewrite Ecd; exact Hcur0) Hgot0 Hunit Hbu
                  Hz Hce ltac:(lia) Hbsmf Hbs) as Hc;
    rewrite Hu_eq in Hc; specialize (Hc (Hall (ipc + L) ltac:(lia) _ Hs') Hend);
    apply (f_equal (@Zlength Z)) in Ho';
    rewrite !Zlength_app in Ho'; rewrite Zlength_app in Hls; cbn [fp_content] in Ho'; rewrite Zlength_nil in Ho';
    cbn [zp_set_got zp_with zp_out] in Hc; lia.
- (* buffered: the ring's out part at outStart *)
  specialize (Hcb eq_refl).
  assert (Hdds: dd_small dd) by (intros x buf Hx; exact (proj1 (proj2 (Hdd x buf Hx)))).
  assert (HN: sf_outSize (c3_s k0) <= 2 ^ 32) by lia.
  assert (Hoe': sf_outEnd (c3_s k0) = vlong ostart) by (rewrite <- Hoso; exact Hos).
  unfold hist_ok in Hho. cbn [c3_s sv_lay sv_fp fp_content fp_ws fp_hist] in Hho.
  specialize (Hho eq_refl ltac:(rewrite Hs; unfold zdss_load, zdss_init; lia)
                ltac:(rewrite Hs; unfold zdss_load, zdss_loadHeader; lia)).
  assert (Hold: old_hist (ring_cells (c3_s k0)) l z).
  { unfold old_hist, ring_cells. destruct l; auto. }
  assert (HEin': E <= sf_inSize (c3_s k0)) by (apply HEin; reflexivity).
  assert (Hout_eq: sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0))
                     (ld_ring {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                 sv_dd := dd |} (c3_s k0) (a_ibs a) ipc L) =
                   sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) (sf_ring (c3_s k0))).
  { unfold ld_ring. cbn [sv_fp fp_inpos]. apply er_ring_load_out; lia. }
  assert (Ho: o_bf (c3_s k0) (ld_ring {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                         sv_dd := dd |} (c3_s k0) (a_ibs a) ipc L) ostart
                {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |} =
              oa_ring (c3_s k0) (FP_zstd hdr z) ostart)
    by (unfold o_bf, oa_ring; rewrite Hout_eq; reflexivity).
  rewrite Ho in Hce.
  pose proof (hist_pre_buf3 _ _ _ hdr z l dd ostart Hring Hld Hdm Hdds Hcb Hos Hoe' Hor HN Hws Hbsm Hb0 Hold)
    as Hpre.
  specialize (Hce Hpre). cbn [oa_cap oa_ring is_skip fp_unit] in Hce.
  apply (Hbad _ (sf_outSize (c3_s k0) - ostart)
           (zhist_buf3 _ _ _ hdr z l dd ostart sm Hring Hld Hdm Hdds Hcb Hos Hoe' Hor HN Hws Hbsm Hb0 eq_refl) Hce).
  exact (buf_cap_room3 _ _ _ hdr z l ostart Hring Hos Hoe' Hor HN Hws Hbsm Hb0).
Qed.

End CM_L3ErMain_1.
