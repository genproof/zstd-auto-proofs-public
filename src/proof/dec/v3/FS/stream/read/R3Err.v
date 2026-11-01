(* FS3 streaming, case zdss_read: an error of ZSTD_decompressContinueStream, returned as it is
   (positions unchanged): why it is allowed (S3Main.err_why; v2 StreamSeg_read.v read_err_why). *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3Ring.
Require Import Zstd.proof.dec.v3.FS.stream.read.R3ModelA Zstd.proof.dec.v3.FS.stream.read.R3ModelB.
Local Open Scope logic.

Section CM_R3Err_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma is_prefix_app_r3 : forall (x y r: list Z), is_prefix (x ++ y) (x ++ y ++ r).
Proof.
intros. unfold is_prefix. rewrite app_assoc. rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r.
Qed.

(* P_zunit_err without its 0 < zp_bsm *)
Lemma zunit_err0' : MF3 -> forall sm cd fb hdr z H u cap, bytes_ok fb -> 0 <= zp_bsm z -> zhist_ok sm z H ->
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

(* the stable layout never has the wrapped extDict: zstd's block decoder gets the frame's dictionary *)
Lemma lay_H_stable : forall ob osz sout s hdr z l sh oc opc,
  c_ring true (Some (ob, osz)) sout s (FP_zstd hdr z) nil l -> Zlength sout = opc ->
  lay_H z l (oa_stable sh ob osz (FP_zstd hdr z) oc opc) = zp_hist z.
Proof.
intros ob osz sout s hdr z l sh oc opc Hr Hl.
destruct Hr as (_&_&_&os&oe&_&_&_&Hr). destruct Hr as (_&_&_&ob'&osz'&Hob&Hly).
inversion Hob; subst ob' osz'.
unfold lay_H, oa_stable, lmove. cbn [oa_base oa_d oa_cap is_skip].
destruct (osz - opc <=? 0).
- destruct l as [| | |b ps pe e]; auto. destruct Hly as (_&Hne&_). destruct e; auto. contradiction.
- destruct l as [| | |b ps pe e]; auto. destruct Hly as (_&Hne&Hpe&_).
  rewrite (proj2 (Z.eqb_eq pe opc)) by lia. destruct e; auto. contradiction.
Qed.

Lemma read_err_why3 : MF3 -> forall a k sv ipc opc oc1 dl ns rr o oc' fs' tabs',
  dsa_ok a -> start_ok a -> call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read ->
  fp_complete (sv_fp sv) = false -> unit_ok (sv_fp sv) ns -> 0 < ns -> ipc + ns <= a_isz a ->
  dd_facts (a_W a) (sv_dd sv) -> (dc_stable (a_st a) = false -> lay_cbound (sv_fp sv) (sv_lay sv)) ->
  cont_res (sv_fp sv) (sv_lay sv) (sv_dd sv) o (sublist ipc (ipc + ns) (a_ibs a)) rr oc' fs' tabs' ->
  is_error_code rr = true ->
  (dc_stable (a_st a) = true -> o = oa_stable (a_shob a) (a_ob a) (a_osz a) (sv_fp sv) oc1 opc) ->
  (dc_stable (a_st a) = false ->
     exists ostart, sf_outStart (c3_s k) = vlong ostart /\ 0 <= ostart <= sf_outSize (c3_s k) /\
       o = oa_ring (c3_s k) (sv_fp sv) ostart) ->
  err_why a rr.
Proof.
intros M a k sv ipc opc oc1 dl ns rr o oc' fs' tabs' Ha Hs0 Hi Hs Hnc Hun Hns Hisz Hdf Hcb Hres Herr
  Hos_st Hos_bf.
pose proof Ha as Ha'.
destruct Ha' as (_&_&_&_&_&_&_&_&_&Hopos&_&_&Hipos&_&Hlibs&Hbibs&_).
pose proof Hi as Hi'.
destruct Hi' as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&Hstout&H16&H17&Hmodel&_&Hsah&_).
assert (Hcore0 := Hcore).
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&Hcf&Hring&_&_&Hnld&Hrd).
destruct Hnld as (Hinpos&Hraw&Hsk); [unfold zdss_read, zdss_load; lia|].
destruct Hrd as (Hpend&Hoso); [reflexivity|].
assert (Hah: sv_ahead sv = nil).
{ destruct Hhost as [[Hx _]|[Hx|Hx]]; [rewrite Hs in Hx; discriminate|apply Hx|].
  destruct Hx as (_&_&Hx&_). congruence. }
assert (Hah0: ss_ahead (dc_ss (a_st a)) = 0).
{ destruct Hs0 as (_&Hah01&Hahl&_). rewrite Hah, app_nil_r in Hsah. unfold a_sin in Hsah.
  apply (f_equal (@Zlength Z)) in Hsah. rewrite Zlength_sublist in Hsah by lia. lia. }
destruct Hres as (_&_&_&_&Hres). rewrite Herr in Hres. destruct Hres as (Hce&Hn80&Hn82).
assert (Hde: dec_err rr) by (split; [exact Herr|split; assumption]).
assert (Hsin0: a_sin a = ss_in (dc_ss (a_st a))).
{ unfold a_sin. rewrite Hah0, Z.sub_0_r. apply sublist_same; reflexivity. }
assert (Hall: forall j, a_ipos a <= j <= a_isz a -> forall s, is_prefix (a_all a) s ->
                is_prefix (a_sin a ++ sublist (a_ipos a) j (a_ibs a)) s).
{ intros j Hj s Hs'. apply (is_prefix_trans _ (a_all a)); [|exact Hs'].
  unfold a_all. rewrite Hah0, Z.add_0_r, <- Hsin0.
  rewrite (sublist_split (a_ipos a) j (a_isz a)) by lia. apply is_prefix_app_r3. }
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
destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcr&Ho').
change (sm_of (a_st a)) with sm in Ef, Ecd, Hcr.
assert (Hbfb: bytes_ok dsin /\ bytes_ok fb).
{ rewrite Esin in Hbsin. apply Forall_app in Hbsin. exact Hbsin. }
set (u := sublist ipc (ipc + ns) (a_ibs a)) in *.
assert (Hbu: bytes_ok u) by (unfold u; apply Forall_sublist; exact Hbibs).
assert (Hul: Zlength u = ns) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hu_eq: dsin ++ fb ++ u = a_sin a ++ sublist (a_ipos a) (ipc + ns) (a_ibs a)).
{ rewrite (sublist_split (a_ipos a) ipc (ipc + ns)) by lia. rewrite (app_assoc (a_sin a)), Esin.
  rewrite !app_assoc. reflexivity. }
destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&Hb0&Hbsm&Hws&_).
assert (Hgot: match zp_ph z with
              | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
              | _ => zp_got z = nil end).
{ cbn [fp_rawbody fp_loaded fp_complete] in Hraw, Hnc. rewrite Hnc in Hraw.
  destruct (zp_ph z); destruct Hraw as [Hr|[Hr|Hr]]; try discriminate; auto.
  left. apply Z.eqb_eq; exact Hr. }
assert (Hun': unit_ok (FP_zstd hdr z) (Zlength u)) by (rewrite Hul; exact Hun).
assert (Hbad: forall H cap, zhist_ok sm z H -> cont_err (FP_zstd hdr z) H u cap -> cap_room z cap -> err_why a rr).
{ intros H cap Hz Hce' Hroom.
  pose proof (zunit_err0' M sm cd fb hdr z H u cap (proj2 Hbfb) ltac:(lia) Hz Hcr Hgot Hun' Hbu Hce' Hroom) as Hfb'.
  split; [exact Hde|right; left]. intros s Hbs Hs'. rewrite Hser.
  apply (mf_bad_of_fbad M sm cd dsin recs (fb ++ u) s (proj1 Hbfb) Ef Ecd Hfb').
  rewrite app_assoc, <- (app_assoc dsin), Hu_eq. apply Hall; [lia|exact Hs']. }
destruct (dc_stable (a_st a)) eqn:Hst.
- (* stable: the caller's buffer at op *)
  rewrite (Hos_st eq_refl) in Hce.
  destruct (read_pre_stable3 a k {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                    sv_dd := dd |} ipc opc oc1 dl Ha Hi Hs Hst Hnc Hdf) as [_ Hhp].
  specialize (Hce Hhp). cbn [sv_fp sv_lay] in Hce.
  specialize (Hstout eq_refl).
  assert (Hls: Zlength (ss_out (dc_ss (a_st a)) ++ dl) = opc).
  { apply (f_equal (@Zlength val)) in Hstout. rewrite Zlength_map, Zlength_sublist in Hstout by lia. lia. }
  rewrite (lay_H_stable _ _ _ _ _ _ _ _ _ _ Hring Hls) in Hce.
  assert (Hz: zhist_ok sm z (zp_hist z)) by (left; reflexivity).
  cbn [oa_cap oa_stable is_skip] in Hce.
  destruct (Z_le_gt_dec (zp_bsm z) (a_osz a - opc)) as [Hr1|Hr1].
  { exact (Hbad _ _ Hz Hce (or_introl Hr1)). }
  destruct (Z.eq_dec (fh_contentSize (zp_h z)) ZSTD_CONTENTSIZE_UNKNOWN) as [Hr2|Hr2].
  2: destruct (Z_le_gt_dec (fh_contentSize (zp_h z) - Zlength (zp_out z)) (a_osz a - opc)) as [Hr3|Hr3].
  2: { exact (Hbad _ _ Hz Hce (or_intror (conj Hr2 Hr3))). }
  all: split; [exact Hde|right; right]; split; [exact Hst|];
    intros s Hbs Hs' Hend; rewrite Hser in Hend |- *;
    assert (Hbsmf: cont_err (FP_zstd hdr z) (zp_hist z) u (zp_bsm z) ->
                   fbad sm (sm_curafter sm (sm_cur sm) dsin) (fb ++ u))
      by (intros Hc; unfold sm_curafter; rewrite Ecd;
          exact (zunit_err0' M sm cd fb hdr z _ u _ (proj2 Hbfb) ltac:(lia) Hz Hcr Hgot Hun' Hbu Hc
                   (or_introl (Z.le_refl _))));
    unfold sm_curafter in Hbsmf; rewrite Ecd in Hbsmf;
    pose proof (zunit_err_cap3 M sm dsin recs fb hdr z (zp_hist z) u (a_osz a - opc) s (proj1 Hbfb) (proj2 Hbfb)
                  Ef ltac:(unfold sm_curafter; rewrite Ecd; exact Hcr) Hgot Hun' Hbu Hz Hce ltac:(lia)
                  ltac:(unfold sm_curafter; rewrite Ecd; exact Hbsmf) Hbs) as Hc;
    rewrite Hu_eq in Hc; specialize (Hc (Hall (ipc + ns) ltac:(lia) _ Hs') Hend);
    apply (f_equal (@Zlength Z)) in Ho';
    rewrite !Zlength_app in Ho'; rewrite Zlength_app in Hls; cbn [fp_content] in Ho'; rewrite Zlength_nil in Ho';
    lia.
- (* buffered: the ring's out part at outStart *)
  destruct (Hos_bf eq_refl) as (ostart & Hos & Hos1 & ->). specialize (Hcb eq_refl).
  assert (HN: sf_outSize (c3_s k) <= 2 ^ 32).
  { pose proof Hring as Hr0. destruct Hr0 as (_&_&Hin&_). pose proof (Z.le_max_r (fp_bsm (FP_zstd hdr z)) 4).
    lia. }
  assert (Hoe': sf_outEnd (c3_s k) = vlong ostart) by (rewrite <- Hoso; exact Hos).
  unfold hist_ok in Hho. cbn [c3_s sv_lay sv_fp fp_content fp_ws fp_hist] in Hho.
  specialize (Hho eq_refl ltac:(rewrite Hs; unfold zdss_read, zdss_init; lia)
                ltac:(rewrite Hs; unfold zdss_read, zdss_loadHeader; lia)).
  assert (Hold: old_hist (ring_cells (c3_s k)) l z).
  { unfold old_hist, ring_cells. destruct l; auto. }
  assert (Hpre: hist_pre (FP_zstd hdr z) l (oa_ring (c3_s k) (FP_zstd hdr z) ostart))
    by (exact (hist_pre_buf3 _ _ _ hdr z l dd _ ostart Hring Hld Hdm Hdf Hcb Hos Hoe' Hos1 HN Hws Hbsm Hb0 Hold)).
  specialize (Hce Hpre). cbn [oa_cap oa_ring is_skip sv_fp] in Hce.
  apply (Hbad _ (sf_outSize (c3_s k) - ostart)
           (zhist_buf3 _ _ _ hdr z l dd _ ostart sm Hring Hld Hdm Hdf Hcb Hos Hoe' Hos1 HN Hws Hbsm Hb0 eq_refl) Hce).
  exact (buf_cap_room3 _ _ _ hdr z l ostart Hring Hos Hoe' Hos1 HN Hws Hbsm Hb0).
Qed.

End CM_R3Err_1.
