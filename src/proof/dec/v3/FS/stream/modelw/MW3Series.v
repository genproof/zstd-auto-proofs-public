(* FS3 streaming model facts: the series facts of S3ModelStmts (finished frames, dead/bad,
   complete current frame, the one-shot shortcut). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.ParamsW Zstd.proof.model.Refuse Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM Zstd.proof.dec.v3.FS.stream.modelw.MW3Walk Zstd.proof.dec.v3.FS.stream.modelw.MW3Ref.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma m3_dead_app : P_dead_app.
Proof.
  intros sm x y [H1 H2]. split.
  - intros s Hp. apply H1. eapply is_prefix_app_l; eauto.
  - intros s Hb Hp. apply H2; auto. eapply is_prefix_app_l; eauto.
Qed.

Lemma m3_fdead_app : P_fdead_app.
Proof.
  intros sm cd x y [H1 H2]. split.
  - intros s Hp. apply H1. eapply is_prefix_app_l; eauto.
  - intros s Hb Hp. apply H2; auto. eapply is_prefix_app_l; eauto.
Qed.

Lemma m3_fbad_app : P_fbad_app.
Proof. intros sm cd x y H s Hp. apply H. eapply is_prefix_app_l; eauto. Qed.

(* the finished frames dsin are the first frames of every extension, and a refusal of an extension is a refusal of
   its rest after dsin (MW3Ref.series_refused_app) *)
Lemma m3_dead_of_fdead : P_dead_of_fdead.
Proof.
  intros sm cd dsin recs x Hb H Hc [Hx1 Hx2]. unfold sm_series, sm_curafter in *. split.
  - intros s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- app_assoc.
    rewrite (proj1 (series_app _ _ _ _ _ _ _ H Hb)), Hc. apply Hx1. apply is_prefix_app.
  - intros s Hbs Hp R. apply is_prefix_ex in Hp. destruct Hp as [r ->]. rewrite <- app_assoc in R, Hbs.
    apply (series_refused_app _ _ _ _ _ recs) in R; auto. rewrite Hc in R.
    apply bytes_ok_app in Hbs. apply (Hx2 (x ++ r)); [tauto | apply is_prefix_app | exact R].
Qed.

Lemma m3_bad_of_fbad : P_bad_of_fbad.
Proof.
  intros sm cd dsin recs x s Hb H Hc Hx Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold sm_series, sm_curafter in *. rewrite <- app_assoc.
  destruct (series_app_wlim _ _ (sm_wl sm) _ _ _ (x ++ r) H Hb) as [E|E]; rewrite E; [discriminate|].
  rewrite Hc. apply Hx. apply is_prefix_app.
Qed.

Lemma fcs_ok_cond : forall h out, fcs_ok h out ->
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) = false.
Proof.
  unfold fcs_ok; intros h out [E|E]; rewrite E, Z.eqb_refl; auto. apply Bool.andb_false_r.
Qed.

(* a mode with the format md and the selection sel (next_cd reads only these) *)
Definition smk (md: dmode) (sel: Z -> option dict_model) : smode :=
  {| sm_md := md; sm_sel := sel; sm_cur := None; sm_wl := 0 |}.

Lemma next_cd_smk : forall sm fp cd, next_cd (smk (sm_md sm) (sm_sel sm)) fp cd = next_cd sm fp cd.
Proof. intros. destruct fp; reflexivity. Qed.

(* the first frame of a complete current frame *)
Lemma cur_complete_wfirst : forall md sel cd fb fp, bytes_ok fb ->
  cur_rel md sel cd fb fp -> fp_complete fp = true ->
  wfirst md sel cd no_wlim fb = inl (Zlength fb, fp_content fp, is_skip fp, next_cd (smk md sel) fp cd).
Proof.
  intros md sel cd fb fp Hb H Hc. destruct fp as [|hb|hdr got|hdr z]; simpl in Hc; try discriminate.
  - unfold cur_rel in H. destruct H as [Hmg [H8 [Hm [Hg [sk [-> Hsk]]]]]]. apply Z.eqb_eq in Hc. subst got.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *. pose proof (Zlength_nonneg sk).
    unfold wfirst. unfold next_cd, skip_cd. cbn [smk sm_md sm_sel].
    rewrite Hmg. rewrite Zlength_app. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX.
    replace (Zlength hdr + Zlength sk <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite le_field_app by lia. rewrite Hm. cbn [negb andb].
    unfold skippable_frame_size. rewrite Zlength_app, !le_field_app by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
    replace (Zlength hdr + Zlength sk <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (le_field hdr 4 4 + 8 >? Zlength hdr + Zlength sk) with false by (symmetry; apply Zgtb_le; lia).
    simpl. do 4 f_equal. lia.
  - destruct (zp_ph z) eqn:Eph; try discriminate. unfold cur_rel in H. rewrite Eph in H.
    destruct H as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb [-> [Ho [Hf Hck]]]]]]]]]]]]]]. subst fb.
    apply bytes_ok_app in Hb. destruct Hb as [Hbh _].
    pose proof (bytes_ok_byte_at hdr (fpos (md_magicless md)) Hbh) as B4.
    destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [Hst [Hm [Hs _]]]]]; [congruence|].
    pose proof (bp_last_len _ _ _ _ _ _ _ _ Hbp).
    pose proof (Zlength_nonneg (zp_got z)).
    unfold wfirst. rewrite !Zlength_app.
    replace (Zlength hdr + (Zlength (zp_bl z) + Zlength (zp_got z)) <? starting_len (md_magicless md)) with false
      by (symmetry; apply Z.ltb_ge; lia).
    replace (negb (md_magicless md) && is_skippable_magic (le_field (hdr ++ zp_bl z ++ zp_got z) 0 4)) with false.
    2:{ destruct (md_magicless md) eqn:Emg; [reflexivity|]. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hst.
        rewrite le_field_app by lia. rewrite Hm by auto. reflexivity. }
    rewrite (frame_dict_ext _ _ _ _ _ _ G B4), Hfd.
    unfold zp_hist in Hbp. rewrite Hbsm in Hbp.
    rewrite (dfm_cur_last _ _ _ _ _ _ _ _ _ G Hl Ht Hd Hbh Hbp).
    replace (fh_windowSize (zp_h z) >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfhm_ws; eauto).
    unfold df_fin. cbv zeta. rewrite fcs_ok_cond by auto.
    rewrite !Zlength_app. simpl fp_content. simpl is_skip. simpl next_cd. rewrite Ho.
    destruct Hck as [[Hc0 Hg0]|[Hc1 [Hg4 Hx]]].
    + rewrite Hc0. simpl. rewrite Hg0. change (Zlength (@nil Z)) with 0. do 4 f_equal. lia.
    + rewrite Hc1, Z.eqb_refl.
      replace (Zlength hdr + (Zlength (zp_bl z) + Zlength (zp_got z)) - fh_headerSize (zp_h z) - Zlength (zp_bl z) <? 4)
        with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite app_assoc. replace (fh_headerSize (zp_h z) + Zlength (zp_bl z)) with (Zlength (hdr ++ zp_bl z) + 0)
        by (rewrite Zlength_app; lia).
      rewrite le_field_app_r by lia.
      rewrite <- Hign. destruct Hx as [Hx|Hx].
      * rewrite Hx. simpl. do 4 f_equal. rewrite Zlength_app. lia.
      * rewrite Hx, Z.eqb_refl, Bool.andb_false_r. do 4 f_equal. rewrite Zlength_app. lia.
Qed.

Lemma m3_cur_complete : P_cur_complete.
Proof.
  intros sm cd fb fp Hb H Hc.
  destruct (walk_single _ _ _ _ _ _ _ _ (cur_complete_wfirst _ _ _ _ _ Hb H Hc)) as [E1 E2].
  exists (mkrec 0 (Zlength fb) (fp_content fp) (is_skip fp)). unfold sm_series, sm_curafter.
  repeat split; auto.
Qed.

Lemma m3_frames_done_app : P_frames_done_app.
Proof.
  intros sm cd dsin recs fb fp Hd Hf H Hcd Hc Hcp.
  unfold sm_series, sm_curafter in *.
  destruct (walk_single _ _ _ _ _ _ _ _ (cur_complete_wfirst _ _ _ _ _ Hf Hc Hcp)) as [E1 E2].
  rewrite <- Hcd in E1, E2.
  rewrite (series_app_full _ _ _ _ _ _ _ _ _ H Hd E1) by discriminate.
  eexists. split; [eauto|]. split; [|split].
  - rewrite flat_map_app. simpl. rewrite app_nil_r. auto.
  - rewrite length_app. simpl. lia.
  - rewrite (proj2 (series_app _ _ _ _ _ _ _ H Hd)). rewrite E2, Hcd. auto.
Qed.

(* ---------- the shortcut: one Zstandard frame decoded in one shot ---------- *)

Definition fres_w (dm: option dict_model) (r: fres) : (Z * list Z * bool * option dict_model) + Zstd.proof.model.Series.tail :=
  match r with
  | FOk c k => inl (k, c, false, dm)
  | FDetHdr => inr TDetHdr
  | FDetCk => inr TDetCk
  | FUnk => inr TUnk
  end.

Lemma sc_wfirst : forall sm cd x dm, shortcut_frame sm cd x dm -> forall w,
  wfirst (sm_md sm) (sm_sel sm) cd w x = fres_w (Some dm) (decode_frame_m (sm_md sm) dm w x) /\
  wfirst (sm_md sm) sel_none (Some dm) w x = fres_w (Some dm) (decode_frame_m (sm_md sm) dm w x).
Proof.
  intros sm cd x dm [Hfc [[h [G Ht]] Hfd]] w. unfold sm_mg in *.
  pose proof (gfhm_len _ _ _ G) as Hst.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hm _]]]]; [congruence|].
  assert (Hsk: negb (md_magicless (sm_md sm)) && is_skippable_magic (le_field x 0 4) = false).
  { destruct (md_magicless (sm_md sm)); [reflexivity|]. rewrite Hm by auto. reflexivity. }
  assert (Hfd0: frame_dict (md_magicless (sm_md sm)) sel_none (Some dm) x = Some dm).
  { unfold frame_dict. destruct (get_frame_header_m _ x); reflexivity. }
  unfold wfirst. replace (Zlength x <? starting_len (md_magicless (sm_md sm))) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hsk, Hfd, Hfd0. split; destruct (decode_frame_m _ _ _ _); reflexivity.
Qed.

Lemma sc_ext : forall sm cd x dm, shortcut_frame sm cd x dm -> bytes_ok x -> forall w r,
  wfirst (sm_md sm) (sm_sel sm) cd w (x ++ r) = wfirst (sm_md sm) (sm_sel sm) cd w x.
Proof.
  intros sm cd x dm Hs Hb w r. pose proof Hs as [Hfc [[h [G Ht]] Hfd]]. unfold sm_mg in *.
  pose proof (gfhm_len _ _ _ G) as Hst. pose proof (Zlength_nonneg r).
  pose proof (bytes_ok_byte_at x (fpos (md_magicless (sm_md sm))) Hb) as B.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hm _]]]]; [congruence|].
  assert (Hsk: negb (md_magicless (sm_md sm)) && is_skippable_magic (le_field x 0 4) = false).
  { destruct (md_magicless (sm_md sm)); [reflexivity|]. rewrite Hm by auto. reflexivity. }
  unfold wfirst. rewrite Zlength_app.
  replace (Zlength x <? starting_len (md_magicless (sm_md sm))) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength x + Zlength r <? starting_len (md_magicless (sm_md sm))) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite skip_test_app, Hsk by auto.
  rewrite (frame_dict_ext _ _ _ _ _ _ G B), Hfd.
  rewrite (dfm_ext _ _ _ _ _ _ Hfc B). auto.
Qed.

Lemma sc_single : forall sm cd x dm c k, shortcut_frame sm cd x dm ->
  decode_frame_m (sm_md sm) dm no_wlim x = FOk c k -> k = Zlength x.
Proof.
  intros sm cd x dm c k [Hfc _] D. pose proof (dfm_fcs _ _ _ _ _ _ D). unfold sm_mg in Hfc. congruence.
Qed.

(* R0's shortcut facts on the stream's own model *)
Lemma sc_ok_strict : forall sm cd x dm c, shortcut_frame sm cd x dm ->
  decode_series_m (sm_md sm) sel_none (Some dm) no_wlim x = SOk c ->
  exists rec, sm_series sm cd no_wlim x = ([rec], TEnd) /\ fr_content rec = c /\
              fr_start rec = 0 /\ fr_size rec = Zlength x /\ sm_curafter sm cd x = Some dm.
Proof.
  intros sm cd x dm c Hs Hd. destruct (sc_wfirst _ _ _ _ Hs no_wlim) as [W1 W2].
  unfold decode_series_m, series_frames_m in Hd. rewrite walk_S, W2 in Hd.
  destruct (decode_frame_m (sm_md sm) dm no_wlim x) as [c1 k| | |] eqn:D; cbn [fres_w] in *; try discriminate.
  pose proof (sc_single _ _ _ _ _ _ Hs D). subst k.
  destruct (walk_single _ _ _ _ _ _ _ _ W2) as [E2 _].
  unfold series_frames_m in E2. rewrite walk_S, W2 in E2. rewrite E2 in Hd. inversion Hd; subst. clear Hd.
  destruct (walk_single _ _ _ _ _ _ _ _ W1) as [E1 E1c].
  exists (mkrec 0 (Zlength x) c1 false). unfold sm_series, sm_curafter. repeat split; auto.
  simpl. rewrite app_nil_r. auto.
Qed.

(* the series x (one frame) decoded with sel_none and the frame's dictionary *)
Lemma sc_series : forall sm cd x dm, shortcut_frame sm cd x dm ->
  decode_series_m (sm_md sm) sel_none (Some dm) no_wlim x =
  match decode_frame_m (sm_md sm) dm no_wlim x with
  | FOk c _ => SOk c
  | FDetHdr | FDetCk => SDet
  | FUnk => SUnk
  end.
Proof.
  intros sm cd x dm Hs. destruct (sc_wfirst _ _ _ _ Hs no_wlim) as [_ W2].
  destruct (decode_frame_m (sm_md sm) dm no_wlim x) as [c1 k| | |] eqn:D; cbn [fres_w] in W2;
    try (unfold decode_series_m, series_frames_m; rewrite walk_S, W2; reflexivity).
  pose proof (sc_single _ _ _ _ _ _ Hs D). subst k.
  unfold decode_series_m. rewrite (proj1 (walk_single _ _ _ _ _ _ _ _ W2)). simpl. rewrite app_nil_r. auto.
Qed.

(* the stream's model gives no answer on the shortcut's frame x, which the lenient one-shot model does not refuse:
   no extension of x is decoded, and none is refused (a refusal of an extension is one of the frame x, the frame is
   complete in x, and a refusal with the dictionary window rule is one without it) *)
Lemma sc_unk_strict : forall sm cd x dm, bytes_ok x -> shortcut_frame sm cd x dm ->
  decode_series_m (sm_md sm) sel_none (Some dm) no_wlim x = SUnk ->
  ~ frame_refused_m (md_len (sm_md sm)) dm no_wlim x -> fdead sm cd x.
Proof.
  intros sm cd x dm Hb Hs Hd Hnr. rewrite (sc_series _ _ _ _ Hs) in Hd.
  destruct (decode_frame_m (sm_md sm) dm no_wlim x) eqn:D; try discriminate. split.
  - intros s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
    unfold series_frames_m. rewrite walk_S, (sc_ext _ _ _ _ Hs Hb), (proj1 (sc_wfirst _ _ _ _ Hs no_wlim)), D.
    reflexivity.
  - intros s Hbs Hp R. apply is_prefix_ex in Hp. destruct Hp as [r ->].
    pose proof Hs as [Hfc [[h [G Ht]] Hfd]]. unfold sm_mg in *.
    unfold series_refused_m in R.
    rewrite wref_S, (sc_ext _ _ _ _ Hs Hb), (proj1 (sc_wfirst _ _ _ _ Hs no_wlim)), D in R. cbn [fres_w] in R.
    pose proof (gfhm_len _ _ _ G) as Hst. pose proof (Zlength_nonneg r).
    destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hm _]]]]; [congruence|].
    assert (Hsk: negb (md_magicless (sm_md sm)) && is_skippable_magic (le_field x 0 4) = false).
    { destruct (md_magicless (sm_md sm)); [reflexivity|]. rewrite Hm by auto. reflexivity. }
    rewrite (wref_dict _ _ _ _ _ dm) in R.
    + rewrite (dfm_ext _ _ _ _ _ r Hfc (bytes_ok_byte_at _ _ Hb)), D in R.
      apply Hnr, frame_refused_len. eapply frame_refused_prefix; eauto.
    + rewrite Zlength_app. lia.
    + rewrite skip_test_app by auto. exact Hsk.
    + rewrite (frame_dict_ext _ _ _ _ _ _ G (bytes_ok_byte_at _ _ Hb)). exact Hfd.
Qed.

(* the window limit: a frame Ok under some limit is Ok without limit (its window is at most 2^64) *)
Lemma sc_wl : forall sm cd x dm w c k, shortcut_frame sm cd x dm -> bytes_ok x ->
  decode_frame_m (sm_md sm) dm w x = FOk c k -> decode_frame_m (sm_md sm) dm no_wlim x = FOk c k.
Proof.
  intros sm cd x dm w c k Hs Hb D. destruct (dfm_wshape _ _ _ _ _ _ D) as [h [G Hw]].
  rewrite Hw. replace (fh_windowSize h >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfhm_ws; eauto). auto.
Qed.

(* ---------- R1: the shortcut's claims are on the lenient one-shot model md_len ---------- *)

(* one Zstandard frame x, the whole series, under any mode, selection and current dictionary *)
Definition sc_frame (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (x: list Z) (dm: dict_model) : Prop :=
  frame_compressed_size_m (md_magicless md) x = Some (Zlength x) /\
  (exists h, get_frame_header_m (md_magicless md) x = FH_ok h /\ fh_frameType h = 0) /\
  frame_dict (md_magicless md) sel cur x = Some dm.

Lemma sc_frame_len : forall sm cd x dm, shortcut_frame sm cd x dm -> sc_frame (md_len (sm_md sm)) (sm_sel sm) cd x dm.
Proof. intros sm cd x dm H. exact H. Qed.

Lemma sc_frame_none : forall md sel cur x dm, sc_frame md sel cur x dm -> sc_frame md sel_none (Some dm) x dm.
Proof.
  intros md sel cur x dm [Hfc [Hh _]]. split; [exact Hfc|]. split; [exact Hh|].
  unfold frame_dict. destruct (get_frame_header_m _ x); reflexivity.
Qed.

Lemma scg_wfirst : forall md sel cur x dm, sc_frame md sel cur x dm -> forall w,
  wfirst md sel cur w x = fres_w (Some dm) (decode_frame_m md dm w x).
Proof.
  intros md sel cur x dm [Hfc [[h [G Ht]] Hfd]] w.
  pose proof (gfhm_len _ _ _ G) as Hst.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hm _]]]]; [congruence|].
  assert (Hsk: negb (md_magicless md) && is_skippable_magic (le_field x 0 4) = false).
  { destruct (md_magicless md); [reflexivity|]. rewrite Hm by auto. reflexivity. }
  unfold wfirst. replace (Zlength x <? starting_len (md_magicless md)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hsk, Hfd. destruct (decode_frame_m _ _ _ _); reflexivity.
Qed.

Lemma scg_single : forall md sel cur x dm c k, sc_frame md sel cur x dm ->
  decode_frame_m md dm no_wlim x = FOk c k -> k = Zlength x.
Proof. intros md sel cur x dm c k [Hfc _] D. pose proof (dfm_fcs _ _ _ _ _ _ D). congruence. Qed.

Lemma scg_series : forall md sel cur x dm, sc_frame md sel cur x dm ->
  decode_series_m md sel cur no_wlim x =
  match decode_frame_m md dm no_wlim x with
  | FOk c _ => SOk c
  | FDetHdr | FDetCk => SDet
  | FUnk => SUnk
  end.
Proof.
  intros md sel cur x dm Hs. pose proof (scg_wfirst _ _ _ _ _ Hs no_wlim) as W2.
  destruct (decode_frame_m md dm no_wlim x) as [c1 k| | |] eqn:D; cbn [fres_w] in W2;
    try (unfold decode_series_m, series_frames_m; rewrite walk_S, W2; reflexivity).
  pose proof (scg_single _ _ _ _ _ _ _ Hs D). subst k.
  unfold decode_series_m. rewrite (proj1 (walk_single _ _ _ _ _ _ _ _ W2)). simpl. rewrite app_nil_r. auto.
Qed.

(* a single frame x is refused exactly when the model gives no answer on it and its frame is refused *)
Lemma scg_refused : forall md sel cur x dm, sc_frame md sel cur x dm ->
  series_refused_m md sel cur no_wlim x <-> decode_frame_m md dm no_wlim x = FUnk /\ frame_refused_m md dm no_wlim x.
Proof.
  intros md sel cur x dm Hs. pose proof Hs as [Hfc [[h [G Ht]] Hfd]].
  pose proof (gfhm_len _ _ _ G) as Hst.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hm _]]]]; [congruence|].
  assert (Hsk: negb (md_magicless md) && is_skippable_magic (le_field x 0 4) = false).
  { destruct (md_magicless md); [reflexivity|]. rewrite Hm by auto. reflexivity. }
  unfold series_refused_m. rewrite wref_S, (scg_wfirst _ _ _ _ _ Hs), (wref_dict _ _ _ _ _ _ Hst Hsk Hfd).
  destruct (decode_frame_m md dm no_wlim x) as [c k| | |] eqn:D; cbn [fres_w].
  - pose proof (scg_single _ _ _ _ _ _ _ Hs D). subst k.
    rewrite skipn_all2 by (rewrite Zlength_correct, Nat2Z.id; lia).
    split; [|intros [E _]; discriminate]. intros R. destruct (length x); [simpl in R; tauto|].
    cbn [walk_refused] in R. pose proof (starting_len_pos (md_magicless md)).
    change (Zlength (@nil Z)) with 0 in R.
    replace (0 <? starting_len (md_magicless md)) with true in R by (symmetry; apply Z.ltb_lt; lia).
    exfalso. apply R. reflexivity.
  - split; [tauto|]. intros [E _]; discriminate.
  - split; [tauto|]. intros [E _]; discriminate.
  - tauto.
Qed.

Lemma m3_shortcut_sel : P_shortcut_sel.
Proof.
  intros md sel cur x dm Hfc Hh Hfd.
  assert (Hs: sc_frame md sel cur x dm) by (split; [|split]; assumption).
  rewrite (scg_series _ _ _ _ _ Hs), (scg_series _ _ _ _ _ (sc_frame_none _ _ _ _ _ Hs)). reflexivity.
Qed.

(* a single frame is refused with a selection exactly when it is refused with the dictionary its header selects *)
Lemma m3_shortcut_sel_ref : P_shortcut_sel_ref.
Proof.
  intros md sel cur x dm Hfc Hh Hfd R.
  assert (Hs: sc_frame md sel cur x dm) by (split; [|split]; assumption).
  apply (scg_refused _ _ _ _ _ Hs). apply (scg_refused _ _ _ _ _ (sc_frame_none _ _ _ _ _ Hs)). exact R.
Qed.

(* where the stream's model decides a frame, the lenient one agrees (ParamsW) *)
Lemma dfm_strict_len : forall md dm w s r, decode_frame_m md dm w s = r -> r <> FUnk ->
  decode_frame_m (md_len md) dm w s = r.
Proof.
  intros [a b c [|]] dm w s r H Hr.
  - exact (decode_frame_m_w_lenient {| md_magicless := a; md_ignore := b; md_bmax := c; md_dwin := false |} dm w s r H Hr).
  - exact H.
Qed.

(* P_shortcut_ok with bytes_ok x (the strict model's fdead quantifies over extensions) *)
Definition P_shortcut_ok_b : Prop :=
  forall sm cd x dm c, bytes_ok x -> shortcut_frame sm cd x dm ->
  decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x = SOk c ->
  (exists rec, sm_series sm cd no_wlim x = ([rec], TEnd) /\ fr_content rec = c /\
               fr_start rec = 0 /\ fr_size rec = Zlength x /\ sm_curafter sm cd x = Some dm) \/
  fdead sm cd x.

Lemma m3_shortcut_ok_b : P_shortcut_ok_b.
Proof.
  intros sm cd x dm c Hb Hs Hd.
  rewrite (scg_series _ _ _ _ _ (sc_frame_none _ _ _ _ _ (sc_frame_len _ _ _ _ Hs))) in Hd.
  destruct (decode_frame_m (sm_md sm) dm no_wlim x) as [c1 k| | |] eqn:D.
  - left. apply (sc_ok_strict sm cd x dm c Hs). rewrite (sc_series _ _ _ _ Hs), D.
    rewrite (dfm_strict_len _ _ _ _ _ D) in Hd by discriminate. exact Hd.
  - rewrite (dfm_strict_len _ _ _ _ _ D) in Hd by discriminate. discriminate.
  - rewrite (dfm_strict_len _ _ _ _ _ D) in Hd by discriminate. discriminate.
  - right. apply (sc_unk_strict sm cd x dm Hb Hs). { rewrite (sc_series _ _ _ _ Hs), D. reflexivity. }
    (* a refused frame is one the lenient model gives no answer on, but it decodes x *)
    intro R. pose proof Hs as [_ [[h [G Ht]] _]]. unfold sm_mg in G.
    destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [Hst [Hm _]]]]; [congruence|].
    rewrite (frame_refused_funk _ _ _ _ Hb) in Hd; [discriminate|exact Hst| |exact R].
    cbn [md_len md_magicless]. destruct (md_magicless (sm_md sm)); auto.
Qed.

Lemma m3_shortcut_unk : P_shortcut_unk.
Proof.
  intros sm cd x dm Hb Hs Hd Hnr.
  pose proof (sc_frame_none _ _ _ _ _ (sc_frame_len _ _ _ _ Hs)) as Hs0.
  rewrite (scg_series _ _ _ _ _ Hs0) in Hd.
  apply (sc_unk_strict sm cd x dm Hb Hs).
  - rewrite (sc_series _ _ _ _ Hs).
    destruct (decode_frame_m (sm_md sm) dm no_wlim x) as [c1 k| | |] eqn:D; [| | |reflexivity];
      rewrite (dfm_strict_len _ _ _ _ _ D) in Hd by discriminate; discriminate.
  - intro R. apply Hnr. apply (scg_refused _ _ _ _ _ Hs0). split; auto.
    destruct (decode_frame_m (md_len (sm_md sm)) dm no_wlim x); try discriminate; reflexivity.
Qed.

Lemma m3_shortcut_det : P_shortcut_det.
Proof.
  intros sm cd x dm Hb Hs Hd s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  rewrite (scg_series _ _ _ _ _ (sc_frame_none _ _ _ _ _ (sc_frame_len _ _ _ _ Hs))) in Hd.
  unfold sm_series, series_frames_m. rewrite walk_S, (sc_ext _ _ _ _ Hs Hb), (proj1 (sc_wfirst _ _ _ _ Hs (sm_wl sm))).
  destruct (decode_frame_m (sm_md sm) dm (sm_wl sm) x) eqn:D; cbn [fres_w]; try discriminate.
  rewrite (dfm_strict_len _ _ _ _ _ (sc_wl _ _ _ _ _ _ _ Hs Hb D)) in Hd by discriminate. discriminate.
Qed.

Lemma m3_shortcut_capacity : P_shortcut_capacity.
Proof.
  intros sm cd x dm s Hb Hs Hp He. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold sm_series, series_frames_m in He.
  rewrite walk_S, (sc_ext _ _ _ _ Hs Hb), (proj1 (sc_wfirst _ _ _ _ Hs (sm_wl sm))) in He.
  destruct (decode_frame_m (sm_md sm) dm (sm_wl sm) x) as [c1 k| | |] eqn:D; cbn [fres_w] in He; try discriminate.
  pose proof (sc_wl _ _ _ _ _ _ _ Hs Hb D) as D0.
  exists c1. split.
  { rewrite (scg_series _ _ _ _ _ (sc_frame_none _ _ _ _ _ (sc_frame_len _ _ _ _ Hs))).
    rewrite (dfm_strict_len _ _ _ _ _ D0) by discriminate. reflexivity. }
  intros h G Hu.
  destruct (dfm_hdr_inv (sm_md sm) dm no_wlim x) as [h' [G' [_ [_ [_ [_ [_ D']]]]]]]; try congruence.
  unfold sm_mg in G. rewrite G in G'. inversion G'; subst h'. rewrite D0 in D'.
  unfold df_tail in D'. cbv zeta in D'.
  destruct (dblocks _ _ _ _ _ _ _ _) as [[out kb]|]; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) eqn:C;
    [discriminate|].
  assert (out = c1).
  { repeat match type of D' with context [if ?b then _ else _] => destruct b end; congruence. }
  subst out. apply Bool.andb_false_iff in C. destruct C as [C|C].
  - apply Bool.negb_false_iff, Z.eqb_eq in C. contradiction.
  - apply Bool.negb_false_iff, Z.eqb_eq in C. auto.
Qed.
