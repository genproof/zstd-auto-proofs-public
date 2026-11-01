(* FS3 streaming model facts (a copy of modelw/MW3FrameM.v): frames in both formats (md_magicless md = mg).  fpos mg: the position
   of the Frame_Header_Descriptor. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.lh.LH3R2MBase Zstd.proof.dec.v3.FS.stream.lh.LH3R2MFrame.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition fpos (mg: bool) : Z := if mg then 0 else 4.
Definition fsh (mg: bool) : Z := if mg then 4 else 0.

Lemma dfm_eq0 : forall md dm w s, md_magicless md = false -> decode_frame_m md dm w s = dfz md dm w s.
Proof.
  intros md dm w s Hmg. unfold decode_frame_m, get_frame_header_m, dfz, df_tail. rewrite Hmg.
  cbv zeta. cbn [negb andb]. rewrite !Z.sub_0_r. reflexivity.
Qed.

(* ---------- headers ---------- *)

Lemma gfhm_true : forall s h, get_frame_header_m true s = FH_ok h ->
  exists h', get_frame_header (magic_bytes ++ s) = FH_ok h' /\ h = fh_unshift h' /\ 1 <= Zlength s.
Proof.
  unfold get_frame_header_m; intros s h H. cbn [negb] in H.
  destruct (Zlength s <? 1) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
  destruct (get_frame_header (magic_bytes ++ s)) as [| |h'] eqn:G; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma gfhm_len : forall mg s h, get_frame_header_m mg s = FH_ok h -> starting_len mg <= Zlength s.
Proof.
  intros [|] s h H; unfold starting_len.
  - destruct (gfhm_true _ _ H) as [h' [_ [_ L]]]. lia.
  - eapply gfh_len; eauto.
Qed.

Lemma gfhm_ext : forall mg x r h, get_frame_header_m mg x = FH_ok h -> 0 <= byte_at x (fpos mg) < 256 ->
  get_frame_header_m mg (x ++ r) = FH_ok h.
Proof.
  intros [|] x r h H Hb; unfold fpos in Hb.
  - destruct (gfhm_true _ _ H) as [h' [G [-> L]]].
    unfold get_frame_header_m. cbn [negb]. rewrite Zlength_app.
    pose proof (Zlength_nonneg r).
    replace (Zlength x + Zlength r <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite app_assoc, (gfh_ext _ r _ G); auto.
  - exact (gfh_ext _ r _ H Hb).
Qed.

Lemma frame_dict_ext : forall mg sel cur x r h, get_frame_header_m mg x = FH_ok h -> 0 <= byte_at x (fpos mg) < 256 ->
  frame_dict mg sel cur (x ++ r) = frame_dict mg sel cur x.
Proof. intros. unfold frame_dict. rewrite (gfhm_ext _ _ _ _ H H0), H. auto. Qed.

(* a frame header (both formats) *)
Lemma gfhm_info : forall mg s h, get_frame_header_m mg s = FH_ok h ->
  (mg = false /\ fh_frameType h = 1 /\ 8 <= Zlength s /\ (le_field s 0 4 =? ZSTD_MAGICNUMBER) = false /\
   is_skippable_magic (le_field s 0 4) = true /\ fh_headerSize h = 8 /\ fh_contentSize h = le_field s 4 4) \/
  (fh_frameType h = 0 /\ starting_len mg <= Zlength s /\ (mg = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) /\
   fh_headerSize h = fhd_header_size (byte_at s (fpos mg)) - fsh mg /\ fh_headerSize h <= Zlength s /\
   Z.land (byte_at s (fpos mg)) 8 = 0 /\
   (negb (Z.land (Z.shiftr (byte_at s (fpos mg)) 5) 1 =? 1) &&
     (Z.shiftr (byte_at s (fpos mg + 1)) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) = false).
Proof.
  intros [|] s h H.
  - right. destruct (gfhm_true _ _ H) as [h' [G [-> L]]].
    destruct (gfh_info _ _ G) as [[_ [_ [Hm _]]]|[Ht [_ [_ [Hs [Hle [Hr Hw]]]]]]].
    { rewrite magic_field_app, Z.eqb_refl in Hm. discriminate. }
    rewrite Zlength_app, magic_len in Hle. cbn [fpos fsh starting_len fh_unshift fh_frameType fh_headerSize].
    replace (byte_at (magic_bytes ++ s) 4) with (byte_at s 0) in *
      by (rewrite <- (magic_byte s 0) by lia; reflexivity).
    replace (byte_at (magic_bytes ++ s) 5) with (byte_at s 1) in *
      by (rewrite <- (magic_byte s 1) by lia; reflexivity).
    change (0 + 1) with 1. repeat split; auto; try lia.
  - pose proof (gfh_len _ _ H). destruct (gfh_info _ _ H) as [A|[Ht [_ [Hm [Hs [Hle [Hr Hw]]]]]]].
    + left. tauto.
    + right. cbn [fpos fsh starting_len]. change (4 + 1) with 5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
      rewrite Z.sub_0_r. repeat split; auto.
Qed.

Lemma gfhm_magicless : forall x h, get_frame_header_m true x = FH_ok h -> fh_frameType h = 0.
Proof. intros. destruct (gfhm_info _ _ _ H) as [[E _]|[E _]]; [discriminate|auto]. Qed.

(* ---------- one Zstandard frame ---------- *)

Section M.
Variable md : dmode.
Variable dm : dict_model.
Local Notation mg := (md_magicless md).

Lemma dfm_unfold : forall w s h, get_frame_header_m mg s = FH_ok h -> fh_frameType h = 0 ->
  9 - fsh mg <= Zlength s -> fh_headerSize h + 3 <= Zlength s ->
  decode_frame_m md dm w s =
    if fh_windowSize h >? w then FDetHdr else if dict_bad dm h then FUnk else df_tail md dm h s.
Proof.
  intros w s h H Ht H9 H3. destruct (md_magicless md) eqn:Hmg.
  - destruct (gfhm_info _ _ _ H) as [[E _]|[_ [_ [_ [Hs [_ [Hr Hw]]]]]]]; [discriminate|].
    cbn [fpos fsh] in *. change (0 + 1) with 1 in Hw.
    unfold decode_frame_m. rewrite Hmg. cbv zeta. cbn [negb andb].
    change (4 - 4) with 0. change (5 - 4) with 1. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
    replace (Zlength s <? 6 - 4 + 3) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength s <? fhd_header_size (byte_at s 0) - 4 + 3) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Hr. cbn [Z.eqb negb]. rewrite Hw, H, Ht. cbn [Z.eqb negb].
    destruct (fh_windowSize h >? w); [reflexivity|]. unfold dict_bad. destruct (_ && _); reflexivity.
  - rewrite dfm_eq0 by auto. cbn [fsh] in H9.
    rewrite (df_unfold md dm w s h); auto.
Qed.

Lemma dfm_hdr_inv : forall w s, decode_frame_m md dm w s <> FUnk -> decode_frame_m md dm w s <> FDetHdr ->
  exists h, get_frame_header_m mg s = FH_ok h /\ fh_frameType h = 0 /\ 9 - fsh mg <= Zlength s /\
    fh_headerSize h + 3 <= Zlength s /\ fh_windowSize h <= w /\ dict_bad dm h = false /\
    decode_frame_m md dm w s = df_tail md dm h s.
Proof.
  intros w s H1 H2.
  assert (A: exists h, get_frame_header_m mg s = FH_ok h /\ fh_frameType h = 0 /\ 9 - fsh mg <= Zlength s /\
                       fh_headerSize h + 3 <= Zlength s).
  { destruct (md_magicless md) eqn:Hmg.
    - unfold decode_frame_m in H1, H2. rewrite Hmg in H1, H2. cbv zeta in H1, H2. cbn [negb andb] in H1, H2.
      destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN - 4 + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
      destruct (Zlength s <? fhd_header_size (byte_at s (4 - 4)) - 4 + ZSTD_blockHeaderSize) eqn:E3; [congruence|].
      destruct (negb (Z.land (byte_at s (4 - 4)) 8 =? 0)) eqn:E4; [congruence|].
      destruct (_ && _) eqn:E5; [congruence|].
      destruct (get_frame_header_m true s) as [| |h] eqn:G; try congruence.
      destruct (fh_windowSize h >? w); [congruence|].
      destruct (negb (fh_frameType h =? 0)) eqn:E6; [congruence|].
      exists h. apply Z.ltb_ge in E1, E3. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *.
      destruct (gfhm_info _ _ _ G) as [[E _]|[Ht [_ [_ [Hs _]]]]]; [discriminate|].
      cbn [fsh fpos] in *. change (4 - 4) with 0 in E3. repeat split; auto; lia.
    - rewrite dfm_eq0 in H1, H2 by auto.
      destruct (df_hdr_inv md dm w s H1 H2) as [h [G [Ht [H9 [H3 _]]]]].
      exists h. cbn [fsh]. rewrite get_frame_header_zstd1. repeat split; auto; lia. }
  destruct A as [h [G [Ht [H9 H3]]]].
  rewrite (dfm_unfold w s h G Ht H9 H3) in *.
  exists h. repeat split; auto.
  - destruct (fh_windowSize h >? w) eqn:E; [congruence|]. apply Zgtb_le in E; auto.
  - destruct (fh_windowSize h >? w); [congruence|]. destruct (dict_bad dm h); congruence.
  - destruct (fh_windowSize h >? w); [congruence|]. destruct (dict_bad dm h); congruence.
Qed.

Lemma dfm_fcs : forall w s c k, decode_frame_m md dm w s = FOk c k -> frame_compressed_size_m mg s = Some k.
Proof.
  intros w s c k H. destruct (md_magicless md) eqn:Hmg.
  2:{ rewrite frame_compressed_size_zstd1. rewrite dfm_eq0 in H by auto. eapply df_fcs; eauto. }
  destruct (dfm_hdr_inv w s) as [h [G [Ht [H9 [H3 [_ [_ E]]]]]]]; try congruence.
  rewrite Hmg in G.
  rewrite E in H. clear E.
  unfold frame_compressed_size_m. cbn [negb]. rewrite G. cbv zeta.
  unfold df_tail in H. cbv zeta in H.
  destruct (dblocks (md_dwin md) _ _ _ _ _ _ _) as [[out kb]|] eqn:D; [|discriminate].
  destruct (db_bs _ _ _ _ _ _ _ _ _ _ D) as [nb ->].
  destruct (_ && _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength s - fh_headerSize h - kb <? 4) eqn:E4; [discriminate|].
    replace (Zlength s - (fh_headerSize h + kb) <? 4) with false by (rewrite <- E4; f_equal; lia).
    destruct (_ && _); [discriminate|]. congruence.
  - congruence.
Qed.

Lemma fhs_m_ge : forall s, 0 <= byte_at s (fpos mg) < 256 ->
  9 - fsh mg <= fhd_header_size (byte_at s (fpos mg)) - fsh mg + 3.
Proof. intros. pose proof (fhs_ge6 _ H). lia. Qed.

Lemma dfm_ext : forall w x k r, frame_compressed_size_m mg x = Some k -> 0 <= byte_at x (fpos mg) < 256 ->
  decode_frame_m md dm w (x ++ r) = decode_frame_m md dm w x.
Proof.
  intros w x k r H Hb. destruct (md_magicless md) eqn:Hmg.
  2:{ rewrite !dfm_eq0 by auto. rewrite frame_compressed_size_zstd1 in H. eapply df_ext; eauto. }
  unfold frame_compressed_size_m in H. cbn [negb] in H.
  destruct (get_frame_header_m true x) as [| |h] eqn:G; try discriminate. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  destruct (gfhm_info _ _ _ G) as [[E _]|[Ht [H5 [_ [Hs [Hle _]]]]]]; [discriminate|].
  pose proof (fhs_m_ge x) as H6. rewrite Hmg in H6. specialize (H6 Hb).
  cbn [fsh fpos] in *. rewrite <- Hs in H6.
  destruct (bs_len _ _ _ _ B) as [B3 Bk].
  rewrite Zlength_skipn in B3, Bk by lia.
  pose proof (Zlength_nonneg r).
  assert (G' := gfhm_ext true x r h G Hb).
  assert (Hm: mg = true) by auto.
  rewrite (dfm_unfold w x h), (dfm_unfold w (x ++ r) h); try rewrite Hm; auto; cbn [fsh]; try (rewrite ?Zlength_app; lia).
  destruct (fh_windowSize h >? w); auto. destruct (dict_bad dm h); auto.
  unfold df_tail. cbv zeta.
  rewrite skipn_app_le by (rewrite Zlength_correct in *; lia).
  rewrite (db_ext_bs _ (dm_content dm) _ _ _ _ B).
  rewrite (db_fuel_bs _ (dm_content dm) _ _ _ _ B) by (rewrite length_app; lia).
  destruct (dblocks (md_dwin md) _ _ _ _ _ _ _) as [[out kb']|] eqn:D; auto.
  destruct (db_bs _ _ _ _ _ _ _ _ _ _ D) as [nb' D']. rewrite B in D'. inversion D'; subst kb' nb'.
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)); auto.
  destruct (fh_checksumFlag h =? 1); auto.
  destruct (Zlength x - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4.
  rewrite Zlength_app.
  replace (Zlength x + Zlength r - fh_headerSize h - kb <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength x - fh_headerSize h - kb <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite le_field_app_max by lia. auto.
Qed.

Lemma dfm_cur_pre : forall w hdr h r,
  get_frame_header_m mg hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr -> 3 <= Zlength r ->
  decode_frame_m md dm w (hdr ++ r) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin md h (hdr ++ r) (dblocks (md_dwin md) (length r) (dm_state dm) (dm_content dm) r nil
                              (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h)).
Proof.
  intros w hdr h r G Hl Ht Hd Hb H3.
  pose proof (bytes_ok_byte_at hdr (fpos mg) Hb) as B4.
  pose proof (gfhm_ext _ _ r _ G B4) as G'.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [_ [Hs _]]]]]; [congruence|].
  pose proof (fhs_m_ge _ B4).
  rewrite (dfm_unfold w _ h G' Ht) by (rewrite Zlength_app; lia).
  destruct (fh_windowSize h >? w); auto. rewrite (dict_ok_bad dm h Hd). cbv iota.
  unfold df_tail. cbv zeta. rewrite <- Hl.
  replace (skipn (Z.to_nat (Zlength hdr)) (hdr ++ r)) with r.
  2:{ rewrite skipn_app, Zlength_correct, Nat2Z.id, skipn_all, Nat.sub_diag. auto. }
  unfold df_fin. rewrite <- Hl. auto.
Qed.

Lemma dfm_cur : forall w hdr h bl ts outc t,
  get_frame_header_m mg hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr ->
  blocks_pre (md_dwin md) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) (dm_state dm) bl ts outc false ->
  3 <= Zlength (bl ++ t) ->
  exists fuel, (length t <= fuel)%nat /\
    decode_frame_m md dm w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin md h (hdr ++ bl ++ t) (oshift (Zlength bl) (dblocks (md_dwin md) fuel ts (dm_content dm) t outc
                                     (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h))).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp H3.
  destruct (bp_db _ _ _ _ _ _ _ _ _ Hbp eq_refl) as [n [Hn Hdb]].
  exists (length (bl ++ t) - n)%nat. split; [rewrite length_app; lia|].
  rewrite (dfm_cur_pre w hdr h (bl ++ t)) by auto.
  replace (length (bl ++ t)) with (n + (length (bl ++ t) - n))%nat at 1 by (rewrite length_app; lia).
  rewrite Hdb. auto.
Qed.

Lemma dfm_cur_last : forall w hdr h bl ts outc t,
  get_frame_header_m mg hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr ->
  blocks_pre (md_dwin md) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) (dm_state dm) bl ts outc true ->
  decode_frame_m md dm w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else df_fin md h (hdr ++ bl ++ t) (Some (outc, Zlength bl)).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp.
  pose proof (bp_last_len _ _ _ _ _ _ _ _ Hbp).
  rewrite (dfm_cur_pre w hdr h (bl ++ t)) by (auto; rewrite Zlength_app; pose proof (Zlength_nonneg t); lia).
  rewrite (bp_db_last _ _ _ _ _ _ _ _ Hbp) by (rewrite length_app; lia). auto.
Qed.

(* the window limit only decides between the result and FDetHdr *)
Lemma dfm_wshape : forall w1 s c k, decode_frame_m md dm w1 s = FOk c k ->
  exists h, get_frame_header_m mg s = FH_ok h /\
    forall w, decode_frame_m md dm w s = if fh_windowSize h >? w then FDetHdr else FOk c k.
Proof.
  intros w1 s c k H.
  destruct (dfm_hdr_inv w1 s) as [h [G [Ht [H9 [H3 [Hw [Hd E]]]]]]]; try congruence.
  exists h. split; auto. intros w. rewrite (dfm_unfold w s h G Ht H9 H3), Hd. rewrite E in H. rewrite H. reflexivity.
Qed.

Lemma dfm_bad_hdr : forall w s c k,
  Z.land (byte_at s (fpos mg)) 8 <> 0 \/
  ((Z.land (Z.shiftr (byte_at s (fpos mg)) 5) 1 =? 0) &&
   (Z.shiftr (byte_at s (fpos mg + 1)) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) = true ->
  decode_frame_m md dm w s <> FOk c k.
Proof.
  intros w s c k H E.
  destruct (dfm_hdr_inv w s) as [h [G [Ht _]]]; try congruence.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [_ [_ [_ [Hr Hw]]]]]]]; [congruence|].
  destruct H as [H|H]; [congruence|].
  destruct (land1_cases (Z.shiftr (byte_at s (fpos mg)) 5)) as [E1|E1]; rewrite E1 in *; [|discriminate].
  simpl in H, Hw. congruence.
Qed.

End M.

Lemma gfhm_ws : forall mg s h, get_frame_header_m mg s = FH_ok h -> bytes_ok s -> fh_windowSize h <= no_wlim.
Proof.
  intros [|] s h H Hb.
  - destruct (gfhm_true _ _ H) as [h' [G [-> _]]]. cbn [fh_unshift fh_windowSize].
    eapply gfh_ws; eauto. apply bytes_ok_app. split; auto. apply magic_bytes_ok.
  - eapply gfh_ws; eauto.
Qed.

Lemma dfm_nonmagic : forall md dm w s, md_magicless md = false -> le_field s 0 4 <> ZSTD_MAGICNUMBER ->
  decode_frame_m md dm w s = FUnk.
Proof. intros. rewrite dfm_eq0 by auto. apply df_nonmagic; auto. Qed.

Lemma dfm_skip : forall md dm w s, md_magicless md = false -> 4 <= Zlength s -> is_skippable_magic (le_field s 0 4) = true ->
  decode_frame_m md dm w s = FUnk.
Proof. intros. rewrite dfm_eq0 by auto. apply df_skip; auto. Qed.
