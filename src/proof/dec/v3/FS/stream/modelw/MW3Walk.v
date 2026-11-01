(* FS3 streaming model facts: walks over series (walk_m) with the dictionary threading (walk_cur). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition mkrec (off k: Z) (c: list Z) (sk: bool) : frec :=
  {| fr_start := off; fr_size := k; fr_content := c; fr_skippable := sk |}.

Definition fshift (d: Z) (f: frec) : frec :=
  {| fr_start := d + fr_start f; fr_size := fr_size f; fr_content := fr_content f; fr_skippable := fr_skippable f |}.

Section W.
Variable md : dmode.
Variable sel : Z -> option dict_model.
Local Notation mg := (md_magicless md).

(* the first frame of s: its size, content, whether skippable, and the dictionary current after it *)
Definition wfirst (cur: option dict_model) (w: Z) (s: list Z)
    : (Z * list Z * bool * option dict_model) + Zstd.proof.model.Series.tail :=
  if Zlength s <? starting_len mg then inr (if Zlength s =? 0 then TEnd else TUnk) else
  if negb mg && is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with None => inr TUnk | Some k => inl (k, nil, true, skip_cd md sel s cur) end
  else
    match frame_dict mg sel cur s with
    | None => inr TUnk
    | Some d =>
        match decode_frame_m md d w s with
        | FOk c k => inl (k, c, false, Some d)
        | FDetHdr => inr TDetHdr
        | FDetCk => inr TDetCk
        | FUnk => inr TUnk
        end
    end.

Lemma walk_S : forall f cur w s off, walk_m (S f) md sel cur w s off =
  match wfirst cur w s with
  | inr t => (nil, t)
  | inl (k, c, sk, cur') =>
      let '(l, t) := walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k) in (mkrec off k c sk :: l, t)
  end.
Proof.
  intros. unfold wfirst. cbn [walk_m]. unfold skip_cd.
  destruct (Zlength s <? starting_len mg); auto.
  destruct (negb mg && _); [destruct (skippable_frame_size s); auto|].
  destruct (frame_dict _ _ _ _); auto. destruct (decode_frame_m _ _ _ _); auto.
Qed.

Lemma walk_cur_S : forall f cur w s, walk_cur (S f) md sel cur w s =
  match wfirst cur w s with
  | inr t => cur
  | inl (k, c, sk, cur') => walk_cur f md sel cur' w (skipn (Z.to_nat k) s)
  end.
Proof.
  intros. unfold wfirst. cbn [walk_cur].
  destruct (Zlength s <? starting_len mg); auto.
  destruct (negb mg && _); [destruct (skippable_frame_size s); auto|].
  destruct (frame_dict _ _ _ _); auto. destruct (decode_frame_m _ _ _ _); auto.
Qed.

Lemma walk_off : forall f cur w s off,
  walk_m f md sel cur w s off = (map (fshift off) (fst (walk_m f md sel cur w s 0)), snd (walk_m f md sel cur w s 0)).
Proof.
  induction f; intros; [auto|]. rewrite !walk_S.
  destruct (wfirst cur w s) as [[[[k c] sk] cur']|t]; auto.
  rewrite (IHf cur' w _ (off + k)), (IHf cur' w _ (0 + k)). simpl. f_equal. f_equal.
  - unfold fshift, mkrec. simpl. f_equal. lia.
  - rewrite map_map. apply map_ext. intros. unfold fshift. simpl. f_equal. lia.
Qed.

Lemma walk_mono : forall f cur w s off l t, walk_m f md sel cur w s off = (l, t) -> t <> TUnk ->
  forall f', (f <= f')%nat -> walk_m f' md sel cur w s off = (l, t) /\ walk_cur f' md sel cur w s = walk_cur f md sel cur w s.
Proof.
  induction f; intros. { simpl in H. inversion H; subst. congruence. }
  destruct f' as [|f']; [lia|]. rewrite walk_S in *. rewrite !walk_cur_S.
  destruct (wfirst cur w s) as [[[[k c] sk] cur']|t0]; auto.
  destruct (walk_m f md sel cur' w _ _) as [l0 t0] eqn:E. inversion H; subst.
  destruct (IHf _ _ _ _ _ _ E H0 f' ltac:(lia)) as [-> ->]. auto.
Qed.

Lemma walk_len : forall f cur w s off l t, walk_m f md sel cur w s off = (l, t) -> t <> TUnk -> (length l < f)%nat.
Proof.
  induction f; intros. { simpl in H. inversion H; subst. congruence. }
  rewrite walk_S in H. destruct (wfirst cur w s) as [[[[k c] sk] cur']|t0].
  - destruct (walk_m f md sel cur' w _ _) as [l0 t0] eqn:E. inversion H; subst.
    simpl. specialize (IHf _ _ _ _ _ _ E H0). lia.
  - inversion H; subst. simpl. lia.
Qed.

Lemma wfirst_len : forall cur w s k c sk cur', wfirst cur w s = inl (k, c, sk, cur') -> starting_len mg <= Zlength s.
Proof.
  unfold wfirst; intros. destruct (Zlength s <? starting_len mg) eqn:E; [discriminate|].
  apply Z.ltb_ge in E. auto.
Qed.

Lemma starting_len_pos : forall b, 1 <= starting_len b.
Proof. intros [|]; unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; lia. Qed.

Lemma wfirst_loop_cur : forall cur w s k c sk cur', wfirst cur w s = inl (k, c, sk, cur') ->
  wfirst cur' w s = inl (k, c, sk, cur').
Proof.
  unfold wfirst; intros cur w s k c sk cur' H.
  destruct (Zlength s <? starting_len mg); [discriminate|].
  destruct (negb mg && _).
  { destruct (skippable_frame_size s); inversion H; subst.
    unfold skip_cd. destruct (md_dwin md); auto. destruct (sel _); auto. }
  destruct (frame_dict mg sel cur s) as [d|] eqn:F; [|discriminate].
  destruct (decode_frame_m md d w s) eqn:D; try discriminate. inversion H; subst.
  unfold frame_dict in *. destruct (get_frame_header_m mg s); try (inversion F; subst; rewrite D; auto).
  destruct (sel (fh_dictID h)); inversion F; subst; rewrite D; auto.
Qed.

Lemma walk_loop : forall cur w s k c sk cur', wfirst cur w s = inl (k, c, sk, cur') -> (Z.to_nat k = 0)%nat ->
  forall f off, snd (walk_m f md sel cur' w s off) = TUnk.
Proof.
  intros cur w s k c sk cur' H Hk. apply wfirst_loop_cur in H. clear cur. induction f; intros; [auto|].
  rewrite walk_S, H, Hk. simpl skipn.
  specialize (IHf (off + k)). destruct (walk_m f md sel cur' w s (off + k)). auto.
Qed.

Lemma walk_snd_fuel : forall n s, (length s <= n)%nat -> forall cur w f1 f2 off1 off2,
  (S (length s) <= f1)%nat -> (S (length s) <= f2)%nat ->
  snd (walk_m f1 md sel cur w s off1) = snd (walk_m f2 md sel cur w s off2) /\
  walk_cur f1 md sel cur w s = walk_cur f2 md sel cur w s.
Proof.
  induction n; intros.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    rewrite !walk_S, !walk_cur_S. destruct (wfirst cur w s) as [[[[k c] sk] cur']|t] eqn:E; auto.
    apply wfirst_len in E. pose proof (starting_len_pos mg). rewrite Zlength_correct in E. lia.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    rewrite !walk_S, !walk_cur_S.
    destruct (wfirst cur w s) as [[[[k c] sk] cur']|t] eqn:E; auto.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [e|e].
    + pose proof (wfirst_loop_cur _ _ _ _ _ _ _ E) as E'.
      rewrite e. simpl skipn.
      assert (A: forall f off, snd (let '(l, t) := walk_m f md sel cur' w s (off + k) in (mkrec off k c sk :: l, t)) = TUnk).
      { intros. pose proof (walk_loop _ _ _ _ _ _ _ E' e f (off + k)).
        destruct (walk_m f md sel cur' w s (off + k)). auto. }
      rewrite !A. split; auto.
      (* the dictionary: a loop repeats the same frame *)
      assert (B: forall f, walk_cur f md sel cur' w s = cur').
      { induction f; auto. rewrite walk_cur_S, E', e. simpl skipn. auto. }
      rewrite !B. auto.
    + pose proof (wfirst_len _ _ _ _ _ _ _ E). pose proof (starting_len_pos mg). rewrite Zlength_correct in *.
      assert (length (skipn (Z.to_nat k) s) < length s)%nat by (rewrite length_skipn; lia).
      destruct (IHn (skipn (Z.to_nat k) s) ltac:(lia) cur' w f1 f2 (off1 + k) (off2 + k) ltac:(lia) ltac:(lia)) as [IH1 IH2].
      split; auto.
      destruct (walk_m f1 _ _ _ _ _ (off1 + k)), (walk_m f2 _ _ _ _ _ (off2 + k)). simpl in *. auto.
Qed.

End W.

Lemma sfs_ext : forall s y k, skippable_frame_size s = Some k ->
  skippable_frame_size (s ++ y) = Some k /\ k <= Zlength s.
Proof.
  unfold skippable_frame_size; intros.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  unfold ZSTD_SKIPPABLEHEADERSIZE in *. pose proof (Zlength_nonneg y).
  rewrite le_field_app by lia. rewrite Zlength_app.
  replace (Zlength s + Zlength y <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (le_field s 4 4 + 8 >? Zlength s) eqn:E2; [discriminate|]. apply Zgtb_le in E2.
  replace (le_field s 4 4 + 8 >? Zlength s + Zlength y) with false by (symmetry; apply Zgtb_le; lia).
  split; [auto|]. inversion H. lia.
Qed.

Lemma fcs_le : forall s k, frame_compressed_size s = Some k -> k <= Zlength s.
Proof.
  unfold frame_compressed_size; intros.
  destruct (_ && _). { apply (sfs_ext s nil) in H. tauto. }
  destruct (get_frame_header s) as [| |h] eqn:G; try discriminate. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  destruct (bs_len _ _ _ _ B) as [B3 Bk].
  destruct (gfh_info _ _ G) as [[_ [H8 [_ [_ [Hs _]]]]]|[_ [_ [_ [Hs [Hle _]]]]]].
  - rewrite Hs in *. rewrite Zlength_skipn in B3, Bk by lia.
    destruct (fh_checksumFlag h =? 1); [destruct (Zlength s - (8 + kb) <? 4) eqn:E4; [discriminate|]; apply Z.ltb_ge in E4|];
    some_eq H; lia.
  - assert (0 <= fh_headerSize h) by (rewrite Hs; pose proof (fhs_ge5 (byte_at s 4)); lia).
    rewrite Zlength_skipn in B3, Bk by lia.
    destruct (fh_checksumFlag h =? 1); [destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|]; apply Z.ltb_ge in E4|];
    some_eq H; lia.
Qed.


Lemma fcsm_le : forall mg s k, frame_compressed_size_m mg s = Some k -> k <= Zlength s.
Proof.
  intros [|] s k H; [|rewrite frame_compressed_size_zstd1 in H; eapply fcs_le; eauto].
  unfold frame_compressed_size_m in H. cbn [negb] in H.
  destruct (get_frame_header_m true s) as [| |h] eqn:G; try discriminate. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  destruct (bs_len _ _ _ _ B) as [B3 Bk].
  destruct (gfhm_info _ _ _ G) as [[E _]|[_ [_ [_ [Hs [Hle _]]]]]]; [discriminate|].
  assert (0 <= fh_headerSize h) by (rewrite Hs; pose proof (fhs_ge5 (byte_at s (fpos true))); cbn [fsh]; lia).
  rewrite Zlength_skipn in B3, Bk by lia.
  destruct (fh_checksumFlag h =? 1); [destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|]; apply Z.ltb_ge in E4|];
  some_eq H; lia.
Qed.

Section W2.
Variable md : dmode.
Variable sel : Z -> option dict_model.
Local Notation mg := (md_magicless md).

Lemma skip_test_app : forall s y, starting_len mg <= Zlength s ->
  negb mg && is_skippable_magic (le_field (s ++ y) 0 4) = negb mg && is_skippable_magic (le_field s 0 4).
Proof.
  intros. destruct mg eqn:E; [reflexivity|]. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in H.
  rewrite le_field_app by lia. auto.
Qed.

Lemma wfirst_ext : forall cur w s k c sk cur' y, wfirst md sel cur w s = inl (k, c, sk, cur') -> bytes_ok s ->
  k <= Zlength s /\ forall cur2 w2, wfirst md sel cur2 w2 (s ++ y) = wfirst md sel cur2 w2 s.
Proof.
  intros cur w s k c sk cur' y H Hb. pose proof (wfirst_len _ _ _ _ _ _ _ _ _ H) as H5.
  pose proof (Zlength_nonneg y).
  unfold wfirst in *.
  replace (Zlength s <? starting_len mg) with false in * by (symmetry; apply Z.ltb_ge; lia).
  rewrite Zlength_app. replace (Zlength s + Zlength y <? starting_len mg) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite skip_test_app by auto.
  destruct (negb mg && is_skippable_magic (le_field s 0 4)) eqn:Esk.
  - destruct (skippable_frame_size s) as [k'|] eqn:E; [|discriminate].
    destruct (sfs_ext _ y _ E) as [-> Hk]. inversion H; subst. split; [auto|]. intros.
    pose proof Esk as Hmg. apply andb_prop in Hmg as [Hmg _]. apply Bool.negb_true_iff in Hmg.
    rewrite Hmg in H5. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in H5.
    unfold skip_cd. rewrite le_field_app by lia. reflexivity.
  - destruct (frame_dict mg sel cur s) as [d|] eqn:F; [|discriminate].
    destruct (decode_frame_m md d w s) eqn:E; try discriminate. inversion H; subst.
    pose proof (dfm_fcs _ _ _ _ _ _ E) as Fc.
    destruct (dfm_hdr_inv md d w s) as [h [G _]]; try congruence.
    split; [eapply fcsm_le; eauto|].
    intros. rewrite (frame_dict_ext _ _ _ _ _ _ G (bytes_ok_byte_at _ _ Hb)).
    destruct (frame_dict mg sel cur2 s) as [d2|]; auto.
    rewrite (dfm_ext md d2 w2 s k y Fc (bytes_ok_byte_at _ _ Hb)). auto.
Qed.

Lemma wfirst_end : forall cur w s, wfirst md sel cur w s = inr TEnd -> s = nil.
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? starting_len mg).
  - destruct (Zlength s =? 0) eqn:E; [|discriminate]. apply Z.eqb_eq in E.
    rewrite Zlength_correct in E. destruct s; [auto|simpl in E; lia].
  - destruct (negb mg && _); [destruct (skippable_frame_size s); discriminate|].
    destruct (frame_dict _ _ _ _); [|discriminate]. destruct (decode_frame_m _ _ _ _); discriminate.
Qed.

Lemma wfirst_wlim : forall cur w1 w2 s k c sk cur', wfirst md sel cur w1 s = inl (k, c, sk, cur') ->
  wfirst md sel cur w2 s = inl (k, c, sk, cur') \/ wfirst md sel cur w2 s = inr TDetHdr.
Proof.
  unfold wfirst; intros.
  destruct (Zlength s <? starting_len mg); [discriminate|].
  destruct (negb mg && _); auto.
  destruct (frame_dict _ _ _ _) as [d|]; [|discriminate].
  destruct (decode_frame_m md d w1 s) eqn:E; try discriminate. inversion H; subst.
  destruct (dfm_wshape _ _ _ _ _ _ E) as [h [_ Hw]]. rewrite Hw.
  destruct (fh_windowSize h >? w2); auto.
Qed.

Lemma walk_app : forall f cur w s off l, walk_m f md sel cur w s off = (l, TEnd) -> bytes_ok s ->
  forall y F, (length l <= F)%nat ->
  walk_m F md sel cur w (s ++ y) off =
    (l ++ fst (walk_m (F - length l) md sel (walk_cur f md sel cur w s) w y (off + Zlength s)),
     snd (walk_m (F - length l) md sel (walk_cur f md sel cur w s) w y (off + Zlength s))) /\
  walk_cur F md sel cur w (s ++ y) = walk_cur (F - length l) md sel (walk_cur f md sel cur w s) w y.
Proof.
  induction f; intros cur w s off l H Hs y F HF; [discriminate|].
  rewrite walk_S in H. rewrite walk_cur_S. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ _ _ y E Hs) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite walk_S, walk_cur_S, Hext, E.
    rewrite skipn_app_le by (rewrite Zlength_correct in Hkl; lia).
    destruct (IHf _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F ltac:(lia)) as [IH1 IH2].
    rewrite IH1, IH2.
    rewrite Zlength_skipn by (pose proof (wfirst_len _ _ _ _ _ _ _ _ _ E); pose proof (starting_len_pos mg); lia).
    replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia.
    simpl. auto.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    simpl. rewrite Nat.sub_0_r, Z.add_0_r. destruct (walk_m F _ _ _ _ _ _); auto.
Qed.

Lemma walk_app_wlim : forall f cur w1 w2 s off l, walk_m f md sel cur w1 s off = (l, TEnd) -> bytes_ok s ->
  forall y F, (length l <= F)%nat ->
  snd (walk_m F md sel cur w2 (s ++ y) off) = TDetHdr \/
  snd (walk_m F md sel cur w2 (s ++ y) off) = snd (walk_m (F - length l) md sel (walk_cur f md sel cur w1 s) w2 y (off + Zlength s)).
Proof.
  induction f; intros cur w1 w2 s off l H Hs y F HF; [discriminate|].
  rewrite walk_S in H. rewrite walk_cur_S. destruct (wfirst md sel cur w1 s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w1 (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ _ _ y E Hs) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite walk_S, Hext.
    destruct (wfirst_wlim _ _ w2 _ _ _ _ _ E) as [E'|E']; rewrite E'; [|auto].
    rewrite skipn_app_le by (rewrite Zlength_correct in Hkl; lia).
    destruct (IHf cur' w1 w2 _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F ltac:(lia)) as [IH|IH];
    destruct (walk_m F md sel cur' w2 (skipn (Z.to_nat k) s ++ y) (off + k)) eqn:W; simpl in *; auto.
    right. rewrite IH.
    rewrite Zlength_skipn by (pose proof (wfirst_len _ _ _ _ _ _ _ _ _ E); pose proof (starting_len_pos mg); lia).
    replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia. auto.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    simpl. rewrite Nat.sub_0_r, Z.add_0_r. auto.
Qed.

(* ---------- series ---------- *)

Lemma series_app : forall w cur dsin recs y, series_frames_m md sel cur w dsin = (recs, TEnd) -> bytes_ok dsin ->
  snd (series_frames_m md sel cur w (dsin ++ y)) = snd (series_frames_m md sel (series_cur md sel cur w dsin) w y) /\
  series_cur md sel cur w (dsin ++ y) = series_cur md sel (series_cur md sel cur w dsin) w y.
Proof.
  unfold series_frames_m, series_cur. intros.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app _ _ _ _ _ _ H H0 y (S (length (dsin ++ y)))) as [A1 A2]; [rewrite length_app; lia|].
  rewrite A1, A2. cbn [snd].
  apply walk_snd_fuel with (n := length y); auto; rewrite length_app in *; lia.
Qed.

Lemma series_app_full : forall w cur dsin recs y l t, series_frames_m md sel cur w dsin = (recs, TEnd) -> bytes_ok dsin ->
  series_frames_m md sel (series_cur md sel cur w dsin) w y = (l, t) -> t <> TUnk ->
  series_frames_m md sel cur w (dsin ++ y) = (recs ++ map (fshift (Zlength dsin)) l, t).
Proof.
  unfold series_frames_m, series_cur. intros.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app _ _ _ _ _ _ H H0 y (S (length (dsin ++ y)))) as [A1 _]; [rewrite length_app; lia|].
  rewrite A1. rewrite walk_off.
  rewrite (proj1 (walk_mono _ _ _ _ _ _ _ _ _ H1 H2 (S (length (dsin ++ y)) - length recs) ltac:(rewrite length_app; lia))).
  cbn [fst snd]. auto.
Qed.

Lemma series_app_wlim : forall w2 cur dsin recs y, series_frames_m md sel cur no_wlim dsin = (recs, TEnd) -> bytes_ok dsin ->
  snd (series_frames_m md sel cur w2 (dsin ++ y)) = TDetHdr \/
  snd (series_frames_m md sel cur w2 (dsin ++ y)) = snd (series_frames_m md sel (series_cur md sel cur no_wlim dsin) w2 y).
Proof.
  unfold series_frames_m, series_cur. intros.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app_wlim _ _ _ w2 _ _ _ H H0 y (S (length (dsin ++ y)))) as [E|E]; [rewrite length_app; lia|auto|].
  right. rewrite E. apply walk_snd_fuel with (n := length y); auto; rewrite length_app in *; lia.
Qed.

Lemma walk_single : forall cur w s c sk cur', wfirst md sel cur w s = inl (Zlength s, c, sk, cur') ->
  series_frames_m md sel cur w s = ([mkrec 0 (Zlength s) c sk], TEnd) /\ series_cur md sel cur w s = cur'.
Proof.
  intros. pose proof (wfirst_len _ _ _ _ _ _ _ _ _ H) as H5. pose proof (starting_len_pos mg).
  unfold series_frames_m, series_cur. rewrite walk_S, walk_cur_S, H.
  replace (skipn (Z.to_nat (Zlength s)) s) with (@nil Z)
    by (symmetry; apply skipn_all2; rewrite Zlength_correct; lia).
  rewrite Zlength_correct in H5. destruct (length s) as [|n] eqn:E; [simpl in H5; lia|].
  rewrite walk_S, walk_cur_S.
  assert (Wn: wfirst md sel cur' w [] = inr TEnd).
  { unfold wfirst. replace (Zlength (@nil Z) <? starting_len mg) with true
      by (symmetry; apply Z.ltb_lt; change (Zlength (@nil Z)) with 0; lia). reflexivity. }
  rewrite Wn. auto.
Qed.

End W2.
