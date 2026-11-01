(* FS3 streaming, case zdss_loadHeader: the hint returned when the input ends inside a frame header
   asks for no more than the rest of the frame the header starts (plain Coq; v2 template LHH in
   src/proof/dec/FS/StreamSeg_lhHint.v, with the format and the dictionary selection). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.lh.LHH4Base Zstd.proof.dec.v3.FS.stream.lh.LHH4Frame Zstd.proof.dec.v3.FS.stream.lh.LHH4FrameM Zstd.proof.dec.v3.FS.stream.lh.LHH4Walk.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* LH3Defs.lh_hint *)
Definition lhh_hint (mg: bool) (hb': list Z) (hSize: Z) : Z :=
  if andb (negb mg) (orb (Zlength hb' <? 4) (is_skippable_frame hb' =? 1))
  then (if Zlength hb' <? 4 then ZSTD_SKIPPABLEHEADERSIZE else hSize) - Zlength hb'
  else Z.max (if mg then 2 else 6) hSize - Zlength hb' + ZSTD_blockHeaderSize.

Lemma lhh_ce_app : forall l1 l2 ipos got cacc dflt,
  (forall f, In f l1 -> fr_end f <= ipos) -> cacc + Zlength (flat_map fr_content l1) <= got ->
  cur_end_aux (l1 ++ l2) ipos got cacc dflt =
    cur_end_aux l2 ipos got (cacc + Zlength (flat_map fr_content l1)) dflt.
Proof.
  induction l1 as [|a l1 IH]; intros l2 ipos got cacc dflt H Hg.
  - cbn [app flat_map]. rewrite Zlength_nil, Z.add_0_r. reflexivity.
  - assert (Ha: fr_end a <= ipos) by (apply H; left; auto).
    cbn [flat_map] in Hg |- *. rewrite Zlength_app in Hg |- *.
    pose proof (Zlength_nonneg (flat_map fr_content l1)).
    cbn [app cur_end_aux].
    replace (fr_end a >? ipos) with false by (symmetry; apply Zgtb_le; lia).
    replace (got <? cacc + Zlength (fr_content a)) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. cbn [orb].
    rewrite IH; [ f_equal; lia | intros; apply H; right; auto | lia ].
Qed.

Lemma lhh_ce_cons : forall f l ipos got cacc dflt, fr_end f > ipos -> cur_end_aux (f :: l) ipos got cacc dflt = fr_end f.
Proof.
  intros. cbn [cur_end_aux]. replace (fr_end f >? ipos) with true by (symmetry; apply Z.gtb_lt; lia). auto.
Qed.

Lemma lhh_walk_ends : forall md sel f cur w s off l t, walk_m f md sel cur w s off = (l, t) -> t <> TUnk ->
  bytes_ok s -> forall x, In x l -> fr_end x <= off + Zlength s.
Proof.
  intros md sel. induction f; intros cur w s off l t H Ht Hb x Hx. { simpl in H. inversion H; subst. destruct Hx. }
  rewrite walk_S in H. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t'] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    destruct (wfirst_ext md sel cur w s k c sk cur' nil E Hb) as [Hkl _].
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop md sel cur w s k c sk cur' E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. simpl in H. congruence. }
    destruct Hx as [<-|Hx].
    + unfold fr_end, mkrec. simpl. lia.
    + specialize (IHf _ _ _ _ _ _ E2 Ht (bytes_ok_skipn _ _ Hb) x Hx). rewrite Zlength_skipn in IHf by lia. lia.
  - inversion H; subst. destruct Hx.
Qed.

Lemma lhh_sf_first : forall md sel cur x l t, series_frames_m md sel cur no_wlim x = (l, t) ->
  match wfirst md sel cur no_wlim x with
  | inl (k, c, sk, _) => exists l', l = mkrec 0 k c sk :: l'
  | inr t' => l = nil /\ t = t'
  end.
Proof.
  unfold series_frames_m. intros. rewrite walk_S in H. destruct (wfirst md sel cur no_wlim x) as [[[[k c] sk] cur']|t'].
  - destruct (walk_m _ _ _ _ _ _ _). inversion H; subst; eauto.
  - inversion H; auto.
Qed.

(* the size K of a Zstandard frame at the start of y (or of y, when the frame decoder rejects its header) *)
Lemma lhh_dfm_K : forall md d w y K, bytes_ok y ->
  ((exists c, decode_frame_m md d w y = FOk c K) \/ (decode_frame_m md d w y = FDetHdr /\ K = Zlength y)) ->
  (md_magicless md = false -> le_field y 0 4 = ZSTD_MAGICNUMBER) /\
  fhd_header_size (byte_at y (fpos (md_magicless md))) - fsh (md_magicless md) + 3 <= K /\
  9 - fsh (md_magicless md) <= K.
Proof.
  intros md d w y K Hb HK.
  pose proof (fhs_ge6 _ (bytes_ok_byte_at y (fpos (md_magicless md)) Hb)) as H6.
  assert (HD: decode_frame_m md d w y <> FUnk) by (destruct HK as [[c E]|[E _]]; rewrite E; discriminate).
  unfold decode_frame_m in HD, HK. cbv zeta in HD, HK.
  change (if md_dwin md then decode_blocks_w else decode_blocks) with (dbs (md_dwin md)) in HD, HK.
  destruct md as [mg ig bm dw]. cbn [md_magicless md_ignore md_bmax md_dwin] in *.
  unfold fpos, fsh in *.
  destruct (Zlength y <? ZSTD_FRAMEHEADERSIZE_MIN - (if mg then 4 else 0) + ZSTD_blockHeaderSize) eqn:E1;
    [ congruence | apply Z.ltb_ge in E1 ].
  destruct (negb mg && negb (le_field y 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [ congruence | ].
  assert (Hm: mg = false -> le_field y 0 4 = ZSTD_MAGICNUMBER).
  { intros ->. destruct (le_field y 0 4 =? ZSTD_MAGICNUMBER) eqn:E; [ apply Z.eqb_eq; auto | ].
    discriminate. }
  replace (4 - (if mg then 4 else 0)) with (if mg then 0 else 4) in * by (destruct mg; reflexivity).
  destruct (Zlength y <? fhd_header_size (byte_at y (if mg then 0 else 4)) - (if mg then 4 else 0) + ZSTD_blockHeaderSize) eqn:E3;
    [ congruence | apply Z.ltb_ge in E3 ].
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *.
  destruct HK as [[c HK]|[HK ->]].
  2: { split; [ exact Hm | split; lia ]. }
  split; [ exact Hm | ].
  destruct (get_frame_header_m mg y) as [ | | h] eqn:G;
    try (repeat match type of HK with context [if ?b then _ else _] => destruct b end; discriminate).
  destruct (negb (Z.land (byte_at y _) 8 =? 0)); [ discriminate | ].
  destruct (negb (Z.land (Z.shiftr _ 5) 1 =? 1) && _); [ discriminate | ].
  destruct (gfhm_info _ _ _ G) as [(_ & Ht & _) | (Ht & _ & _ & Hhs & Hhl & _)].
  { destruct (fh_windowSize h >? w); [ discriminate | ]. rewrite Ht in HK. discriminate. }
  unfold fpos, fsh in Hhs.
  destruct (fh_windowSize h >? w); [ discriminate | ].
  destruct (negb (fh_frameType h =? 0)); [ discriminate | ].
  destruct (negb (fh_dictID h =? 0) && _); [ discriminate | ].
  destruct (dbs _ _ _ _ _ _ _ _) as [[out kb]|] eqn:DB; [ | discriminate ].
  pose proof (db_pos _ _ _ _ _ _ _ _ _ _ DB (bytes_ok_skipn _ _ Hb)) as H3.
  repeat match type of HK with context [if ?b then _ else _] => destruct b end; try discriminate;
    inversion HK; subst; lia.
Qed.

(* what the first frame of y says about its size K *)
Definition FBm (mg: bool) (y: list Z) (K: Z) : Prop :=
  (mg = false -> is_skippable_magic (le_field y 0 4) = true -> 8 <= K) /\
  (mg = false -> is_skippable_magic (le_field y 0 4) = false ->
     le_field y 0 4 = ZSTD_MAGICNUMBER /\ fhd_header_size (byte_at y 4) + 3 <= K /\ 9 <= K) /\
  (mg = true -> fhd_header_size (byte_at y 0) - 1 <= K /\ 5 <= K).

Lemma lhh_wfirst_FB : forall md sel cur y, bytes_ok y ->
  match wfirst md sel cur no_wlim y with
  | inl (k, _, _, _) => FBm (md_magicless md) y k
  | inr t => t = TDetHdr -> FBm (md_magicless md) y (Zlength y)
  end.
Proof.
  intros md sel cur y Hb. unfold wfirst.
  destruct (Zlength y <? starting_len (md_magicless md)) eqn:E5.
  { intros Ht. destruct (Zlength y =? 0); discriminate. }
  destruct (negb (md_magicless md) && is_skippable_magic (le_field y 0 4)) eqn:Es.
  - apply andb_prop in Es. destruct Es as [Emg Es]. apply Bool.negb_true_iff in Emg.
    destruct (skippable_frame_size y) as [k|] eqn:Ek; [|intros; discriminate].
    unfold skippable_frame_size in Ek.
    try (destruct (Zlength y <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|]).
    destruct (_ >? Zlength y); [discriminate|].
    inversion Ek; subst. pose proof (le_field_bound y 4 4 Hb ltac:(lia)).
    split; [ intros; unfold ZSTD_SKIPPABLEHEADERSIZE; lia | split; [ intros; congruence | intros; congruence ] ].
  - destruct (frame_dict _ _ _ _) as [d|]; [ | intros; discriminate ].
    assert (HF: forall K, ((exists c, decode_frame_m md d no_wlim y = FOk c K) \/
                           (decode_frame_m md d no_wlim y = FDetHdr /\ K = Zlength y)) -> FBm (md_magicless md) y K).
    { intros K HK. destruct (lhh_dfm_K md d no_wlim y K Hb HK) as (Hm & Hh & H9).
      unfold fpos, fsh in *.
      split; [ | split ].
      - intros Emg Hs. rewrite Emg in *. rewrite (Hm eq_refl), skip_magic_false in Hs. discriminate.
      - intros Emg _. rewrite Emg in *. split; [ auto | lia ].
      - intros Emg. rewrite Emg in *. lia. }
    destruct (decode_frame_m md d no_wlim y) as [c k| | |] eqn:D; try (intros; discriminate).
    + apply HF. left. eauto.
    + intros _. apply HF. right. auto.
Qed.

Lemma lhh_more_cases0 : forall hb kk, get_frame_header hb = FH_more kk ->
  (Zlength hb < 5 /\ kk = 5) \/
  (5 <= Zlength hb /\ is_skippable_magic (le_field hb 0 4) = true /\ kk = 8) \/
  (5 <= Zlength hb /\ le_field hb 0 4 = ZSTD_MAGICNUMBER /\ kk = fhd_header_size (byte_at hb 4) /\
   Zlength hb < kk).
Proof.
  intros hb kk H. unfold get_frame_header in H. cbv zeta in H.
  destruct (Zlength hb <? 5) eqn:E5.
  - left. apply Z.ltb_lt in E5. split; auto.
    destruct (Zlength hb >? 0); [ destruct (_ && _); [ discriminate | ] | ]; inversion H; auto.
  - right. apply Z.ltb_ge in E5.
    destruct (le_field hb 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; cbn [negb] in H.
    + right. apply Z.eqb_eq in Em. destruct (Zlength hb <? fhd_header_size (byte_at hb 4)) eqn:E;
        [ inversion H; apply Z.ltb_lt in E; auto | ].
      repeat match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
    + left. destruct (is_skippable_magic (le_field hb 0 4)) eqn:Es; [ | discriminate ].
      destruct (Zlength hb <? ZSTD_SKIPPABLEHEADERSIZE); [ inversion H; auto | discriminate ].
Qed.

Lemma lhh_more_true : forall hb kk, get_frame_header_m true hb = FH_more kk ->
  (Zlength hb < 1 /\ kk = 1) \/ (1 <= Zlength hb /\ kk = fhd_header_size (byte_at hb 0) - 4).
Proof.
  intros hb kk H. unfold get_frame_header_m in H. cbn [negb] in H.
  destruct (Zlength hb <? 1) eqn:E1; [ left; inversion H; apply Z.ltb_lt in E1; auto | apply Z.ltb_ge in E1 ].
  right. split; [ exact E1 | ].
  destruct (get_frame_header (magic_bytes ++ hb)) as [ |k| ] eqn:G; try discriminate.
  inversion H; subst kk.
  destruct (lhh_more_cases0 _ _ G) as [(Hl & _) | [(_ & Hs & _) | (_ & _ & -> & _)]].
  - rewrite Zlength_app, magic_len in Hl. lia.
  - rewrite magic_field_app in Hs. discriminate.
  - rewrite <- (magic_byte hb 0) by lia. reflexivity.
Qed.

(* the range of the hint *)
Lemma lhh_hint_rng : forall mg hb u kk, get_frame_header_m mg hb = FH_more kk -> Zlength (hb ++ u) < kk ->
  0 < lhh_hint mg (hb ++ u) kk <= 21.
Proof.
  intros mg hb u kk Hk Hlt.
  pose proof (Zlength_app hb u) as Hl. pose proof (Zlength_nonneg u). pose proof (Zlength_nonneg hb).
  assert (Hr: forall fhd, 5 <= fhd_header_size fhd <= 18).
  { intros fhd. split; [ apply fhs_ge5 | ]. unfold fhd_header_size.
    assert (Hs: Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) by apply land1_cases.
    assert (Hd: forall n, nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|n]]]]; simpl; try destruct n; lia).
    assert (Hf: forall n, nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|n]]]]; simpl; try destruct n; lia).
    pose proof (Hd (Z.to_nat (Z.land fhd 3))). pose proof (Hf (Z.to_nat (Z.shiftr fhd 6))).
    destruct Hs as [Hs|Hs]; rewrite Hs.
    - change (0 =? 1) with false. cbn [andb]. lia.
    - change (1 =? 1) with true. cbn [andb]. destruct (Z.shiftr fhd 6 =? 0); lia. }
  unfold lhh_hint, ZSTD_SKIPPABLEHEADERSIZE, ZSTD_blockHeaderSize.
  destruct mg.
  - cbn [negb andb]. destruct (lhh_more_true hb kk Hk) as [(_ & ->) | (_ & ->)]; [ lia | ].
    pose proof (Hr (byte_at hb 0)). lia.
  - cbn [get_frame_header_m negb] in Hk. cbn [negb andb].
    destruct (lhh_more_cases0 hb kk Hk) as [(_ & ->) | [(_ & _ & ->) | (_ & _ & -> & _)]];
      [ | | pose proof (Hr (byte_at hb 4)) ];
      destruct (Zlength (hb ++ u) <? 4) eqn:E; destruct (is_skippable_frame (hb ++ u) =? 1); cbn [orb];
      try (apply Z.ltb_lt in E || apply Z.ltb_ge in E); lia.
Qed.

Lemma lhh_hint_T : forall mg hb u y kk K, bytes_ok y -> is_prefix (hb ++ u) y ->
  get_frame_header_m mg hb = FH_more kk -> Zlength (hb ++ u) < kk -> FBm mg y K ->
  Zlength (hb ++ u) + lhh_hint mg (hb ++ u) kk <= K.
Proof.
  intros mg hb u y kk K Hb Hp Hk Hlt [FS [FN FT]].
  destruct (is_prefix_ex _ _ Hp) as [r ->].
  pose proof (Zlength_app hb u) as Hl. pose proof (Zlength_nonneg u). pose proof (Zlength_nonneg hb).
  destruct mg.
  - (* magicless *)
    destruct (FT eq_refl) as [Fh F5]. unfold lhh_hint. cbn [negb andb].
    destruct (lhh_more_true hb kk Hk) as [(H1 & ->) | (H1 & ->)].
    + unfold ZSTD_blockHeaderSize. lia.
    + rewrite <- app_assoc, byte_at_app in Fh by lia. unfold ZSTD_blockHeaderSize. lia.
  - clear FT. specialize (FS eq_refl). specialize (FN eq_refl).
    pose proof (bytes_ok_byte_at ((hb ++ u) ++ r) 4 Hb) as Hb4.
    assert (Ey: Zlength (hb ++ u) >= 4 -> le_field ((hb ++ u) ++ r) 0 4 = le_field (hb ++ u) 0 4)
      by (intros; apply le_field_app_max; lia).
    assert (Eh: Zlength hb >= 5 -> le_field (hb ++ u) 0 4 = le_field hb 0 4)
      by (intros; apply le_field_app_max; lia).
    assert (Eb: Zlength hb >= 5 -> byte_at ((hb ++ u) ++ r) 4 = byte_at hb 4).
    { intros. rewrite <- app_assoc, byte_at_app; auto. lia. }
    pose proof skip_magic_false as Hsm.
    cbn [get_frame_header_m negb] in Hk.
    unfold lhh_hint, is_skippable_frame. cbn [negb andb].
    destruct (Zlength (hb ++ u) <? 4) eqn:E4.
    + cbn [orb].
      destruct (is_skippable_magic (le_field ((hb ++ u) ++ r) 0 4)).
      * specialize (FS eq_refl). unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
      * destruct (FN eq_refl) as (_ & _ & H9). unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
    + apply Z.ltb_ge in E4. rewrite Ey in FS, FN by lia. cbn [orb].
      destruct (lhh_more_cases0 hb kk Hk) as [(H5 & ->) | [(H5 & Hs & ->) | (H5 & Hm & -> & _)]].
      * destruct (is_skippable_magic (le_field (hb ++ u) 0 4)); cbn [orb andb negb Z.eqb Pos.eqb Z.max].
        -- specialize (FS eq_refl). lia.
        -- destruct (FN eq_refl) as (_ & _ & H9). unfold ZSTD_blockHeaderSize. lia.
      * rewrite Eh, Hs in FS, FN by lia. rewrite Eh, Hs by lia. cbn [orb andb negb Z.eqb Pos.eqb Z.max]. specialize (FS eq_refl). lia.
      * rewrite Eh, Hm in FS, FN by lia. rewrite Eh, Hm, Hsm by lia. cbn [orb andb negb Z.eqb Pos.eqb Z.max].
        destruct (FN eq_refl) as (_ & Hf & _). rewrite Eb in Hf by lia.
        pose proof (fhs_ge6 (byte_at hb 4)) as H6.
        assert (Hbh: 0 <= byte_at hb 4 < 256) by (rewrite <- Eb by lia; exact Hb4).
        specialize (H6 Hbh). unfold ZSTD_blockHeaderSize. lia.
Qed.

(* the hint clause for the header bytes hb ++ u after the complete frames dsin *)
Lemma lhh_hint_bound : forall md sel cur dsin recs hb u kk got s,
  bytes_ok dsin -> series_frames_m md sel cur no_wlim dsin = (recs, TEnd) ->
  get_frame_header_m (md_magicless md) hb = FH_more kk -> Zlength (hb ++ u) < kk ->
  Zlength (flat_map fr_content recs) <= got ->
  is_prefix (dsin ++ hb ++ u) s -> bytes_ok s -> (s <> dsin ++ hb ++ u \/ hb ++ u <> nil) ->
  (snd (series_frames_m md sel cur no_wlim s) = TEnd \/ snd (series_frames_m md sel cur no_wlim s) = TDetHdr) ->
  lhh_hint (md_magicless md) (hb ++ u) kk <=
    cur_end (fst (series_frames_m md sel cur no_wlim s)) (Zlength (dsin ++ hb ++ u)) got (Zlength s) -
    Zlength (dsin ++ hb ++ u).
Proof.
  intros md sel cur dsin recs hb u kk got s Bd Hrecs Hk Hlt Hgot Hp Hs Hne Ht.
  destruct (is_prefix_ex _ _ Hp) as [r ->].
  set (hb' := hb ++ u) in *.
  rewrite <- app_assoc in *. set (y := hb' ++ r) in *.
  apply bytes_ok_app in Hs. destruct Hs as [_ By].
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg dsin). pose proof (Zlength_nonneg hb').
  assert (Hpy: is_prefix hb' y) by apply is_prefix_app.
  destruct (series_frames_m md sel (series_cur md sel cur no_wlim dsin) no_wlim y) as [l t] eqn:SF.
  assert (Ht': t <> TUnk).
  { destruct (series_app md sel no_wlim cur dsin recs y Hrecs Bd) as [E _].
    rewrite E, SF in Ht. cbn [snd] in Ht. destruct Ht; subst; discriminate. }
  rewrite (series_app_full md sel no_wlim cur dsin recs y l t Hrecs Bd SF Ht') in Ht |- *. cbn [fst snd] in Ht |- *.
  pose proof (lhh_sf_first _ _ _ _ _ _ SF) as Hf.
  pose proof (lhh_wfirst_FB md sel (series_cur md sel cur no_wlim dsin) y By) as HF.
  assert (Hends: forall f, In f recs -> fr_end f <= Zlength (dsin ++ hb')).
  { intros f Hin. unfold series_frames_m in Hrecs.
    pose proof (lhh_walk_ends _ _ _ _ _ _ _ _ _ Hrecs ltac:(discriminate) Bd f Hin). rewrite Zlength_app. lia. }
  unfold cur_end. rewrite (lhh_ce_app recs _ _ got 0 _ Hends ltac:(lia)).
  rewrite !Zlength_app in *.
  destruct (wfirst md sel (series_cur md sel cur no_wlim dsin) no_wlim y) as [[[[k c] sk] cur']|t0] eqn:EW.
  - destruct Hf as [l' ->].
    pose proof (lhh_hint_T _ hb u y kk k By Hpy Hk Hlt HF) as HT. fold hb' in HT.
    pose proof (lhh_hint_rng _ hb u kk Hk Hlt) as Hrng. fold hb' in Hrng.
    destruct (Z_lt_le_dec (Zlength hb') k) as [Hgt|Hle]; [ | lia ].
    cbn [map]. rewrite lhh_ce_cons; unfold fr_end, fshift, mkrec; cbn [fr_start fr_size]; lia.
  - destruct Hf as [-> ->]. cbn [map cur_end_aux].
    destruct Ht as [Ht|Ht].
    + subst t0. exfalso. apply wfirst_end in EW. unfold y in EW.
      destruct hb'; [ | discriminate ]. destruct r; [ | discriminate ].
      destruct Hne as [Hne|Hne]; apply Hne; [ rewrite !app_nil_r | ]; reflexivity.
    + pose proof (lhh_hint_T _ hb u y kk (Zlength y) By Hpy Hk Hlt (HF Ht)) as HT. fold hb' in HT.
      unfold y in HT |- *. rewrite Zlength_app in HT |- *. lia.
Qed.

(* the header after this call's bytes: still incomplete (zstd asked for more than it has) *)
Lemma lhh_more_ext : forall mg hb u kk, bytes_ok (hb ++ u) -> get_frame_header_m mg hb = FH_more kk ->
  Zlength (hb ++ u) < kk -> get_frame_header_m mg (hb ++ u) <> FH_err ->
  (forall h, get_frame_header_m mg (hb ++ u) = FH_ok h -> fh_headerSize h = Zlength (hb ++ u)) ->
  exists k0, get_frame_header_m mg (hb ++ u) = FH_more k0.
Proof.
  intros mg hb u kk Hb Hk Hlt Hne Hok.
  destruct (get_frame_header_m mg (hb ++ u)) as [ |k0|h] eqn:G; [ congruence | eauto | exfalso ].
  specialize (Hok h eq_refl).
  pose proof (Zlength_app hb u) as Hl. pose proof (Zlength_nonneg u). pose proof (Zlength_nonneg hb).
  destruct (gfhm_info _ _ _ G) as [(Hmg & _ & H8 & Hm' & Hs' & Hhs & _) | (_ & Hsl & Hmag & Hhs & _)].
  - subst mg. cbn [get_frame_header_m negb] in Hk.
    assert (Eh: Zlength hb >= 5 -> le_field (hb ++ u) 0 4 = le_field hb 0 4)
      by (intros; apply le_field_app_max; lia).
    destruct (lhh_more_cases0 hb kk Hk) as [(H5' & ->) | [(H5' & Hs & ->) | (H5' & Hm & -> & _)]].
    + lia.
    + lia.
    + rewrite Eh, Hm, skip_magic_false in Hs' by lia. discriminate.
  - destruct mg.
    + destruct (lhh_more_true hb kk Hk) as [(H1 & ->) | (H1 & ->)].
      * unfold starting_len in Hsl. unfold fpos, fsh in Hhs.
        pose proof (fhs_ge5 (byte_at (hb ++ u) 0)). lia.
      * unfold fpos, fsh in Hhs. rewrite byte_at_app in Hhs by lia. lia.
    + cbn [get_frame_header_m negb] in Hk. unfold fpos, fsh in Hhs.
      assert (Eh: Zlength hb >= 5 -> le_field (hb ++ u) 0 4 = le_field hb 0 4)
        by (intros; apply le_field_app_max; lia).
      destruct (lhh_more_cases0 hb kk Hk) as [(H5' & ->) | [(H5' & Hs & ->) | (H5' & Hm & -> & _)]].
      * unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hsl. lia.
      * specialize (Hmag eq_refl). rewrite Eh in Hmag by lia. rewrite Hmag, skip_magic_false in Hs. discriminate.
      * rewrite byte_at_app in Hhs by lia. lia.
Qed.


Lemma lhh_more_le18 : forall mg hb kk, get_frame_header_m mg hb = FH_more kk -> kk <= 18.
Proof.
  intros mg hb kk Hk.
  assert (Hr: forall fhd, fhd_header_size fhd <= 18).
  { intros fhd. unfold fhd_header_size.
    assert (Hs: Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) by apply land1_cases.
    assert (Hd: forall n, nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|n]]]]; simpl; try destruct n; lia).
    assert (Hf: forall n, nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|n]]]]; simpl; try destruct n; lia).
    pose proof (Hd (Z.to_nat (Z.land fhd 3))). pose proof (Hf (Z.to_nat (Z.shiftr fhd 6))).
    destruct Hs as [Hs|Hs]; rewrite Hs.
    - change (0 =? 1) with false. cbn [andb]. lia.
    - change (1 =? 1) with true. cbn [andb]. destruct (Z.shiftr fhd 6 =? 0); lia. }
  destruct mg.
  - destruct (lhh_more_true hb kk Hk) as [(_ & ->) | (_ & ->)]; [ lia | ]. pose proof (Hr (byte_at hb 0)). lia.
  - cbn [get_frame_header_m negb] in Hk.
    destruct (lhh_more_cases0 hb kk Hk) as [(_ & ->) | [(_ & _ & ->) | (_ & _ & -> & _)]]; [ lia | lia | ].
    apply Hr.
Qed.
