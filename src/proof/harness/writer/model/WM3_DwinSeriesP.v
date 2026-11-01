(* A proved copy of model/WM3_DwinSeries.v's wm3_series_all: dwin_snoc_p, dwin_series_p are
   WM3_DwinSeries.dwin_snoc, dwin_series (same statements, about the same dwin_ok). *)
Require Import Zstd.proof.harness.writer.TopMath.
Require Import Zstd.proof.harness.writer.model.WM3_Dwin.
Require Import Zstd.proof.model.Params.
Require Import Zstd.proof.harness.writer.model.WM3_DwinSeries.

(* ---------- helpers of wm3_series_all_p ---------- *)

Lemma ds_bounds : forall dm fs bs cs, written dm fs bs cs ->
  Forall (fun f => 0 <= wi_start f /\ 0 <= wi_size f /\ wi_start f + wi_size f <= Zlength bs) fs.
Proof.
  intros dm fs bs cs H. induction H as [|fs bs cs f fb c Hw IH Hst Hcst Hsz Hcsz Hfw Hwf Hz].
  - constructor.
  - pose proof (tm_Zlength_nonneg bs). pose proof (tm_Zlength_nonneg fb).
    apply Forall_app. split.
    + eapply Forall_impl; [|exact IH]. intros g (G1 & G0 & G2). rewrite tm_Zlength_app. lia.
    + constructor; [|constructor]. rewrite tm_Zlength_app. lia.
Qed.

Lemma ds_slice_app : forall (l1 l2: list Z) a k, 0 <= a -> 0 <= k -> a + k <= Zlength l1 ->
  slice (l1 ++ l2) a k = slice l1 a k.
Proof.
  intros l1 l2 a k Ha Hk Hl. unfold slice. rewrite skipn_app, firstn_app.
  rewrite length_skipn. rewrite Zlength_correct in Hl.
  replace (Z.to_nat k - (length l1 - Z.to_nat a))%nat with O by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma ds_slice_full : forall (pre fb bs: list Z), slice (pre ++ fb ++ bs) (Zlength pre) (Zlength fb) = fb.
Proof. intros. rewrite tm_slice_app. apply tm_slice0_app. Qed.

Lemma ds_walk : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs ->
  forall pre, Zlength pre = off ->
  Forall (fun f => wi_skippable f = false -> zframe_w dm (slice (pre ++ bs) (wi_start f) (wi_size f))) fs ->
  forall n wl o, walk_m n (dmode_w md_dflt) sel_none (Some dm) wl bs o = walk n dm wl bs o.
Proof.
  intros dm fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH];
    intros pre Hpre Hok n wl o.
  - destruct n; reflexivity.
  - destruct n as [|n]; [reflexivity|].
    inversion Hok as [|? ? Hf Hfs]; subst.
    assert (IH' : forall o', walk_m n (dmode_w md_dflt) sel_none (Some dm) wl bs o' = walk n dm wl bs o').
    { intros o'. apply (IH (pre ++ fb)); [rewrite tm_Zlength_app; congruence|].
      rewrite <- app_assoc. exact Hfs. }
    simpl. unfold starting_len.
    destruct (Zlength (fb ++ bs) <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E5; [reflexivity|].
    unfold frame_written in Hfw. destruct (wi_skippable f) eqn:Esk.
    + destruct Hfw as (data & -> & Hok' & Hd & Hv & Hn & Hh & ->).
      destruct (tm_skip_bytes (wi_variant f) data bs Hv Hd) as (L & L0 & M & N & D & K & SM & NM).
      destruct (tm_skip_info (wi_variant f) data bs _ eq_refl Hv Hd) as (_ & _ & I3 & _).
      rewrite M, SM, I3. cbn [negb andb]. rewrite K, IH'. reflexivity.
    + destruct Hfw as (Hb & Hcok & _ & Hfcs & Hhs & Hall).
      destruct (Hall bs) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & _).
      assert (Hns : is_skippable_magic (le_field (fb ++ bs) 0 4) = false).
      { unfold is_skippable_frame in I2. destruct (Zlength (fb ++ bs) <? 4) eqn:E4.
        - apply Z.ltb_lt in E4. apply Z.ltb_ge in E5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in E5. lia.
        - destruct (is_skippable_magic _); [discriminate|reflexivity]. }
      rewrite Hns. cbn [negb andb].
      assert (Hd : frame_dict false sel_none (Some dm) (fb ++ bs) = Some dm).
      { unfold frame_dict, sel_none. destruct (get_frame_header_m false (fb ++ bs)); reflexivity. }
      rewrite Hd.
      specialize (Hf eq_refl). rewrite Hsz, <- Hpre, ds_slice_full in Hf.
      unfold zframe_w in Hf. rewrite (Hf wl bs), I9.
      destruct (wi_rejected wl f); [reflexivity|].
      rewrite tm_skipn_app, IH'. reflexivity.
Qed.

Theorem wm3_series_all_p :
  (forall dm fs bs cs f fb,
    written dm fs bs cs -> dwin_ok dm fs bs ->
    wi_start f = Zlength bs -> wi_size f = Zlength fb ->
    (wi_skippable f = false -> zframe_w dm fb) ->
    dwin_ok dm (fs ++ [f]) (bs ++ fb)) /\
  (* the series: the strict walk is Series.v's (the post series_dwin of w_series_spec) *)
  (forall dm fs bs cs,
    written dm fs bs cs -> dwin_ok dm fs bs ->
    forall wl, series_frames_m (dmode_w md_dflt) sel_none (Some dm) wl bs = series_frames dm wl bs).
Proof.
  split.
  - intros dm fs bs cs f fb Hw Hok Hst Hsz Hf. unfold dwin_ok in *.
    pose proof (ds_bounds _ _ _ _ Hw) as Hbd.
    apply Forall_app. split.
    + rewrite Forall_forall in *. intros g Hg Hs. destruct (Hbd g Hg) as (H1 & H0 & H2).
      rewrite ds_slice_app by lia. apply Hok; auto.
    + constructor; [|constructor]. intros Hs. rewrite Hst, Hsz.
      rewrite <- (app_nil_r fb) at 1. rewrite ds_slice_full. auto.
  - intros dm fs bs cs Hw Hok wl. unfold series_frames_m, series_frames.
    apply (ds_walk dm fs 0 0 bs cs (tm_written _ _ _ _ Hw) nil eq_refl); auto.
Qed.

Lemma dwin_nil_p : forall dm, dwin_ok dm [] [].
Proof. intros. constructor. Qed.

Lemma dwin_snoc_p : forall dm fs bs cs f fb,
  written dm fs bs cs -> dwin_ok dm fs bs ->
  wi_start f = Zlength bs -> wi_size f = Zlength fb ->
  (wi_skippable f = false -> zframe_w dm fb) ->
  dwin_ok dm (fs ++ [f]) (bs ++ fb).
Proof. exact (proj1 wm3_series_all_p). Qed.

Theorem dwin_series_p : forall dm fs bs cs,
  written dm fs bs cs -> dwin_ok dm fs bs ->
  forall wl, series_frames_m (dmode_w md_dflt) sel_none (Some dm) wl bs = series_frames dm wl bs.
Proof. exact (proj2 wm3_series_all_p). Qed.
