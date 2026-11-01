(* FS3 streaming: the hint claim of ZSTD_decompressStream's epilogue (plain Coq; v2 template
   src/proof/dec/FS/StreamEpiHint.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.epi.E3Rem.
Require Import Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base Zstd.proof.dec.v3.FS.stream.epi.content.EC3Frame Zstd.proof.dec.v3.FS.stream.epi.content.EC3FrameM Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------- helpers (v2 template src/proof/dec/FS/StreamEpiHint.v) ---------- *)

Local Open Scope bool_scope.

Lemma eh3_ce_ge : forall fl ipos got cacc dflt, ipos <= dflt -> ipos <= cur_end_aux fl ipos got cacc dflt.
Proof.
  induction fl; intros; simpl; auto.
  destruct ((fr_end a >? ipos) || ((fr_end a =? ipos) && (got <? cacc + Zlength (fr_content a)))) eqn:E; auto.
  apply Bool.orb_true_iff in E. destruct E as [E|E].
  - apply Z.gtb_lt in E. lia.
  - apply Bool.andb_true_iff in E. destruct E as [E _]. apply Z.eqb_eq in E. lia.
Qed.

Lemma eh3_ce_app : forall l1 l2 ipos got cacc dflt, (forall f, In f l1 -> fr_end f < ipos) ->
  exists cacc', cur_end_aux (l1 ++ l2) ipos got cacc dflt = cur_end_aux l2 ipos got cacc' dflt.
Proof.
  induction l1; intros; simpl; [eauto|].
  assert (fr_end a < ipos) by (apply H; simpl; auto).
  replace (fr_end a >? ipos) with false by (symmetry; apply Zgtb_le; lia).
  replace (fr_end a =? ipos) with false by (symmetry; apply Z.eqb_neq; lia). simpl.
  apply IHl1. intros. apply H. simpl. auto.
Qed.

Lemma eh3_ce_cons : forall f l ipos got cacc dflt, fr_end f > ipos -> cur_end_aux (f :: l) ipos got cacc dflt = fr_end f.
Proof.
  intros. simpl. replace (fr_end f >? ipos) with true by (symmetry; apply Z.gtb_lt; lia). auto.
Qed.

Lemma eh3_walk_ends : forall md sel f cur w s off l t, walk_m f md sel cur w s off = (l, t) -> t <> TUnk ->
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

Lemma eh3_sf_first : forall md sel cur x l t, series_frames_m md sel cur no_wlim x = (l, t) ->
  match wfirst md sel cur no_wlim x with
  | inl (k, c, sk, _) => exists l', l = mkrec 0 k c sk :: l'
  | inr t' => l = nil /\ t = t'
  end.
Proof.
  unfold series_frames_m. intros. rewrite walk_S in H. destruct (wfirst md sel cur no_wlim x) as [[[[k c] sk] cur']|t'].
  - destruct (walk_m _ _ _ _ _ _ _). inversion H; subst; eauto.
  - inversion H; auto.
Qed.

Lemma eh3_df_fin : forall md h x r c k, df_fin md h x r = FOk c k ->
  exists o kb, r = Some (o, kb) /\ fh_headerSize h + kb + (if fh_checksumFlag h =? 1 then 4 else 0) <= k.
Proof.
  unfold df_fin; intros. destruct r as [[o kb]|]; [|discriminate]. exists o, kb. split; auto.
  destruct (_ && _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (_ <? 4); [discriminate|]. destruct (negb _ && _); [discriminate|]. inversion H; lia.
  - inversion H; lia.
Qed.

Lemma eh3_df_fin_det : forall md h x r, df_fin md h x r <> FDetHdr.
Proof.
  unfold df_fin; intros md h x r E. destruct r as [[o kb]|]; [|discriminate].
  destruct (_ && _); [discriminate|].
  destruct (fh_checksumFlag h =? 1); [|discriminate].
  destruct (_ <? 4); [discriminate|]. destruct (negb _ && _); discriminate.
Qed.

Lemma eh3_wfirst_skip : forall md sel cur hdr got sk rest, md_magicless md = false -> bytes_ok (hdr ++ sk ++ rest) ->
  Zlength hdr = ZSTD_SKIPPABLEHEADERSIZE -> is_skippable_magic (le_field hdr 0 4) = true ->
  Zlength sk = got ->
  match wfirst md sel cur no_wlim (hdr ++ sk ++ rest) with
  | inl (k, _, _, _) => Zlength (hdr ++ sk) + (le_field hdr 4 4 - got) <= k
  | inr t => t <> TEnd /\ t <> TDetHdr
  end.
Proof.
  intros md sel cur hdr got sk rest Hmg Hb Hl Hm Hsk. unfold ZSTD_SKIPPABLEHEADERSIZE in *.
  pose proof (Zlength_nonneg sk). pose proof (Zlength_nonneg rest).
  unfold wfirst. rewrite Hmg, !Zlength_app.
  replace (Zlength hdr + (Zlength sk + Zlength rest) <? starting_len false) with false
    by (symmetry; apply Z.ltb_ge; unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
  rewrite le_field_app, Hm by lia. simpl negb. cbn [andb].
  unfold skippable_frame_size. rewrite le_field_app by lia. rewrite !Zlength_app.
  unfold ZSTD_SKIPPABLEHEADERSIZE.
  replace (Zlength hdr + (Zlength sk + Zlength rest) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (_ >? _); [split; discriminate|]. lia.
Qed.

Lemma eh3_dfm_short : forall md dm w hdr h r, get_frame_header_m (md_magicless md) hdr = FH_ok h ->
  fh_frameType h = 0 -> Zlength hdr = fh_headerSize h -> bytes_ok hdr -> Zlength r < 3 ->
  decode_frame_m md dm w (hdr ++ r) = FUnk.
Proof.
  intros md dm w hdr h r G Ht Hl Hb Hr.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [Hsl [Hmag [Hhs [_ _]]]]]]; [congruence|].
  pose proof (fhs_ge5 (byte_at hdr (fpos (md_magicless md)))) as H5.
  unfold decode_frame_m. rewrite Zlength_app.
  destruct (md_magicless md) eqn:Emg; unfold fpos, fsh in *; cbn [negb andb].
  - replace (4 - 4) with 0 by reflexivity. rewrite (byte_at_app hdr r 0) by (unfold starting_len in Hsl; lia).
    destruct (_ <? _); auto. replace (Zlength hdr + Zlength r <? fhd_header_size (byte_at hdr 0) - 4 + ZSTD_blockHeaderSize) with true
      by (symmetry; apply Z.ltb_lt; unfold ZSTD_blockHeaderSize; lia). auto.
  - destruct (_ <? _); auto. rewrite le_field_app by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hsl; lia).
    rewrite Hmag by auto. rewrite Z.eqb_refl. cbn [negb].
    replace (4 - 0) with 4 by reflexivity.
    rewrite (byte_at_app hdr r 4) by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hsl; lia).
    replace (Zlength hdr + Zlength r <? fhd_header_size (byte_at hdr 4) - 0 + ZSTD_blockHeaderSize) with true
      by (symmetry; apply Z.ltb_lt; unfold ZSTD_blockHeaderSize; lia). auto.
Qed.


Lemma eh3_wfirst_zstd : forall md sel cd fb hdr z rest, bytes_ok (fb ++ rest) -> cur_rel md sel cd fb (FP_zstd hdr z) ->
  0 < fp_rem (FP_zstd hdr z) ->
  match wfirst md sel cd no_wlim (fb ++ rest) with
  | inl (k, _, _, _) => Zlength fb + fp_rem (FP_zstd hdr z) <= k
  | inr t => t <> TEnd /\ t <> TDetHdr
  end.
Proof.
  intros md sel cd fb hdr z rest Hb Hc Hr.
  destruct Hc as [G [Hl [Ht [Hfd [Hid [Hbsm [_ [outc [last [Hbp [Hfb Hph]]]]]]]]]]].
  pose proof (gfhm_len _ _ _ G) as H5.
  subst fb. repeat rewrite <- app_assoc in Hb |- *. apply bytes_ok_app in Hb. destruct Hb as [Bh Bt].
  assert (Hws: (fh_windowSize (zp_h z) >? no_wlim) = false) by (apply Zgtb_le; eapply gfhm_ws; eauto).
  assert (Hwf: forall X, wfirst md sel cd no_wlim (hdr ++ X) =
    match decode_frame_m md (zp_dm z) no_wlim (hdr ++ X) with
    | FOk c k => inl (k, c, false, Some (zp_dm z)) | FDetHdr => inr TDetHdr | FDetCk => inr TDetCk
    | FUnk => inr TUnk end).
  { intros X. unfold wfirst. rewrite Zlength_app. pose proof (Zlength_nonneg X).
    replace (_ <? starting_len _) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite skip_test_app by auto.
    replace (negb (md_magicless md) && is_skippable_magic (le_field hdr 0 4)) with false.
    2:{ destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [Hmag _]]]]; [congruence|].
        destruct (md_magicless md); auto. rewrite Hmag by auto. rewrite skip_magic_false. auto. }
    rewrite (frame_dict_ext _ _ _ _ _ _ G (bytes_ok_byte_at _ _ Bh)), Hfd. reflexivity. }
  rewrite Hwf. clear Hwf.
  rewrite Hbsm in Hbp. unfold zp_hist in Hbp.
  repeat rewrite Zlength_app.
  destruct (zp_ph z) as [|bh| |] eqn:Eph; unfold fp_rem in *; rewrite Eph in *.
  - (* ZP_bhdr *)
    destruct Hph as [-> [_ Hg]].
    assert (Bg: bytes_ok (zp_got z ++ rest)).
    { apply bytes_ok_app in Bt. tauto. }
    destruct (Z_lt_dec (Zlength (zp_bl z ++ zp_got z ++ rest)) 3) as [Hs|Hs].
    + rewrite (eh3_dfm_short md (zp_dm z) no_wlim hdr (zp_h z) _ G Ht Hl Bh Hs). split; discriminate.
    + destruct (dfm_cur md (zp_dm z) no_wlim hdr (zp_h z) (zp_bl z) (zp_ts z) outc (zp_got z ++ rest) G Hl Ht Hid Bh Hbp
                  ltac:(lia)) as [fuel [_ E]].
      rewrite E, Hws.
      destruct (df_fin _ _ _ _) as [c k| | |] eqn:DF; try (split; discriminate).
      * apply eh3_df_fin in DF. destruct DF as [o [kb [E1 E2]]].
        unfold oshift in E1. destruct (dbs _ _ _ _ _ _ _ _) as [[o2 k2]|] eqn:E3; [|discriminate].
        inversion E1; subst. apply db_pos in E3; auto.
        destruct (fh_checksumFlag _ =? 1) in E2; unfold ZSTD_blockHeaderSize; lia.
      * exfalso; eapply eh3_df_fin_det; eauto.
  - (* ZP_body *)
    destruct Hph as [-> [Hbh [c [Ec [Hc [Hg _]]]]]].
    rewrite Ec in *. unfold ZSTD_blockHeaderSize in *.
    repeat rewrite <- app_assoc in Bt |- *. repeat rewrite Zlength_app.
    pose proof (Zlength_nonneg (zp_got z)). pose proof (Zlength_nonneg rest). pose proof (Zlength_nonneg (zp_bl z)).
    assert (Bg: bytes_ok (bh ++ zp_got z ++ rest)).
    { apply bytes_ok_app in Bt. tauto. }
    destruct (dfm_cur md (zp_dm z) no_wlim hdr (zp_h z) (zp_bl z) (zp_ts z) outc (bh ++ zp_got z ++ rest) G Hl Ht Hid Bh Hbp
                ltac:(rewrite !Zlength_app; lia)) as [fuel [_ E]].
    rewrite E, Hws.
    destruct (df_fin _ _ _ _) as [c0 k| | |] eqn:DF; try (split; discriminate).
    + apply eh3_df_fin in DF. destruct DF as [o [kb [E1 E2]]].
      unfold oshift in E1. destruct (dbs _ _ _ _ _ _ _ _) as [[o2 k2]|] eqn:E3; [|discriminate].
      try (inversion E1; subst).
      destruct fuel as [|fuel]; [unfold dbs in E3; destruct (md_dwin md); discriminate|]. rewrite db_S_eq in E3.
      destruct (block_res _ _ _ _ _ _ _) as [[[[st' out'] k1] last']|] eqn:Eb; [|discriminate].
      destruct (br_inv _ _ _ _ _ _ _ _ _ _ _ Eb) as [c' [Ec' [_ [Hk1 Hlast]]]].
      rewrite cblock_size_app, Ec in Ec' by lia. inversion Ec'; subst c'.
      rewrite block_props_app in Hlast by lia.
      rewrite <- Hlast.
      destruct last'.
      * inversion E3; subst. destruct (fh_checksumFlag _ =? 1) in E2; lia.
      * unfold oshift in E3. destruct (dbs _ _ _ _ _ _ _ _) as [[o3 k3]|] eqn:E4; [|discriminate].
        inversion E3; subst. apply db_pos in E4; [|apply bytes_ok_skipn; auto].
        destruct (fh_checksumFlag _ =? 1) in E2; lia.
    + exfalso; eapply eh3_df_fin_det; eauto.
  - (* ZP_ck *)
    destruct Hph as [-> [_ [_ [Hck Hg]]]].
    rewrite (dfm_cur_last md (zp_dm z) no_wlim hdr (zp_h z) (zp_bl z) (zp_ts z) outc (zp_got z ++ rest) G Hl Ht Hid Bh Hbp), Hws.
    destruct (df_fin _ _ _ _) as [c0 k| | |] eqn:DF; try (split; discriminate).
    + apply eh3_df_fin in DF. destruct DF as [o [kb [E1 E2]]]. inversion E1; subst.
      rewrite Hck in E2. simpl in E2. lia.
    + exfalso; eapply eh3_df_fin_det; eauto.
  - lia.
Qed.


Lemma eh3_fb_pos : forall md sel cd fb fp, cur_rel md sel cd fb fp -> 0 < fp_rem fp -> 0 < Zlength fb.
Proof.
  intros md sel cd fb fp Hc Hr. destruct fp as [|hb|hdr got|hdr z]; cbn [fp_rem] in Hr; try lia.
  - destruct Hc as [_ [Hl [_ [_ [sk [-> _]]]]]]. rewrite Zlength_app.
    pose proof (Zlength_nonneg sk). unfold ZSTD_SKIPPABLEHEADERSIZE in Hl. lia.
  - destruct Hc as [G [_ [_ [_ [_ [_ [_ [outc [last [_ [-> _]]]]]]]]]]]. apply gfhm_len in G.
    pose proof (starting_len_pos (md_magicless md)).
    rewrite Zlength_app. pose proof (Zlength_nonneg (zp_bl z ++ match zp_ph z with ZP_body bh => bh ++ zp_got z | _ => zp_got z end)).
    lia.
Qed.


(* the hint (fp_rem: what remains of the current frame's unit, plus the next block header) never reaches past
   the end of the current frame of any extension the model decodes (stream_claims_m's third clause) *)
Lemma epi3_hint : forall sm sin sout fp pend cd, bytes_ok sin ->
  m_rel_cd sm sin sout fp pend cd ->
  forall s, is_prefix sin s -> bytes_ok s ->
  (snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s) = TEnd \/
   snd (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s) = TDetHdr) ->
  Zlength sin + fp_rem fp <=
    cur_end (fst (series_frames_m (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim s)) (Zlength sin) (Zlength sout) (Zlength s).
Proof.
  intros sm sin sout fp pend cd Hsin Hm s Hp Hs Ht.
  destruct sm as [md sel cur wl]. cbn [sm_md sm_sel sm_cur] in *.
  destruct Hm as [dsin [fb [recs [-> [Hrecs [Hcd [Hc _]]]]]]]. subst cd.
  destruct (is_prefix_ex _ _ Hp) as [r ->].
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg dsin). pose proof (Zlength_nonneg fb).
  destruct (Z_le_gt_dec (fp_rem fp) 0) as [Hle|Hgt].
  { unfold cur_end.
    pose proof (eh3_ce_ge (fst (series_frames_m md sel cur no_wlim ((dsin ++ fb) ++ r))) (Zlength (dsin ++ fb))
                  (Zlength sout) 0 (Zlength ((dsin ++ fb) ++ r)) ltac:(rewrite (Zlength_app _ r); lia)).
    lia. }
  pose proof (eh3_fb_pos _ _ _ _ _ Hc ltac:(lia)) as Hfb.
  rewrite <- app_assoc in *. rewrite Zlength_app.
  apply bytes_ok_app in Hs. destruct Hs as [Bd Bfr].
  destruct (series_frames_m md sel (series_cur md sel cur no_wlim dsin) no_wlim (fb ++ r)) as [l t] eqn:SF.
  assert (Ht': t <> TUnk).
  { destruct (series_app md sel no_wlim cur dsin recs (fb ++ r) Hrecs Bd) as [E _].
    rewrite E, SF in Ht. cbn [snd] in Ht. destruct Ht; subst; discriminate. }
  rewrite (series_app_full md sel no_wlim cur dsin recs (fb ++ r) l t Hrecs Bd SF Ht') in Ht |- *. cbn [fst snd] in Ht |- *.
  pose proof (eh3_sf_first _ _ _ _ _ _ SF) as Hf.
  assert (Hw: match wfirst md sel (series_cur md sel cur no_wlim dsin) no_wlim (fb ++ r) with
              | inl (k, _, _, _) => Zlength fb + fp_rem fp <= k
              | inr t => t <> TEnd /\ t <> TDetHdr
              end).
  { destruct fp as [|hb|hdr got|hdr z]; cbn [fp_rem] in Hgt; try lia.
    - destruct Hc as [Hmg [Hl [Hm [Hg [sk [-> Hsk]]]]]]. rewrite <- app_assoc in Bfr |- *.
      exact (eh3_wfirst_skip md sel _ hdr got sk r Hmg Bfr Hl Hm Hsk).
    - apply eh3_wfirst_zstd; auto. cbn [fp_rem]. lia. }
  destruct (wfirst md sel (series_cur md sel cur no_wlim dsin) no_wlim (fb ++ r)) as [[[[k c] sk] cur']|t0].
  - destruct Hf as [l' ->].
    assert (Hends: forall f, In f recs -> fr_end f < Zlength dsin + Zlength fb).
    { intros f Hin. unfold series_frames_m in Hrecs.
      pose proof (eh3_walk_ends _ _ _ _ _ _ _ _ _ Hrecs ltac:(discriminate) Bd f Hin). lia. }
    unfold cur_end. destruct (eh3_ce_app recs (map (fshift (Zlength dsin)) (mkrec 0 k c sk :: l'))
                                (Zlength dsin + Zlength fb) (Zlength sout) 0 (Zlength (dsin ++ fb ++ r)) Hends)
      as [cacc' ->].
    cbn [map]. rewrite eh3_ce_cons; unfold fr_end, fshift, mkrec; cbn [fr_start fr_size]; lia.
  - destruct Hf as [-> ->]. destruct Hw, Ht; contradiction.
Qed.
