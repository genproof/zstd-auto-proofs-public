(* FS3 streaming model facts: the series facts of S3ModelStmts (finished frames, bad,
   complete current frame, the one-shot shortcut). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base Zstd.proof.dec.v3.FS.stream.epi.content.EC3Frame Zstd.proof.dec.v3.FS.stream.epi.content.EC3FrameM Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma m3_fbad_app : P_fbad_app.
Proof. intros sm cd x y H s Hp. apply H. eapply is_prefix_app_l; eauto. Qed.

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

