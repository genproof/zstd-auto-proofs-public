(* FS3 streaming model facts: the frame-header facts of S3ModelStmts. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM Zstd.proof.dec.v3.FS.stream.modelw.MW3Walk.
Require Import Zstd.proof.model.Refuse Zstd.proof.dec.v3.FS.stream.modelw.MW3Ref.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- arithmetic of a partial magic number (v2 StreamModelFacts) ---------- *)

Lemma skip_char : forall m, is_skippable_magic m = true <-> (m mod 2 ^ 32) / 16 = 25481893.
Proof.
  intros. unfold is_skippable_magic, ZSTD_MAGIC_SKIPPABLE_MASK, ZSTD_MAGIC_SKIPPABLE_START.
  replace 4294967280 with (Z.ldiff (Z.ones 32) (Z.ones 4)) by reflexivity.
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land, Z.ldiff_ones_r, Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  rewrite Z.eqb_eq. lia.
Qed.

Lemma le_value_app : forall a b, le_value (a ++ b) = le_value a + 2 ^ (8 * Zlength a) * le_value b.
Proof.
  induction a; intros.
  - cbn [app]. change (Zlength (@nil Z)) with 0. change (le_value []) with 0. change (2 ^ (8 * 0)) with 1. lia.
  - cbn [app le_value]. rewrite IHa. rewrite Zlength_cons.
    replace (8 * Z.succ (Zlength a0)) with (8 + 8 * Zlength a0) by lia.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg a0); lia). change (2 ^ 8) with 256. ring.
Qed.

Lemma prefix_arith : forall n lv K, 1 <= n <= 4 -> 0 <= lv < 2 ^ (8 * n) ->
  (lv + 2 ^ (8 * n) * K = ZSTD_MAGICNUMBER ->
   lv + 2 ^ (8 * n) * le_value (skipn (Z.to_nat n) (le_bytes 4 ZSTD_MAGICNUMBER)) = ZSTD_MAGICNUMBER) /\
  (is_skippable_magic (lv + 2 ^ (8 * n) * K) = true ->
   is_skippable_magic (lv + 2 ^ (8 * n) * le_value (skipn (Z.to_nat n) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) = true).
Proof.
  intros n lv K Hn Hl. rewrite !skip_char. unfold ZSTD_MAGICNUMBER.
  assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | ->]]].
  - replace (le_value (skipn (Z.to_nat 1) (le_bytes 4 4247762216))) with 16592821 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 1) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 1592618 by (vm_compute; reflexivity).
    change (2 ^ (8 * 1)) with 256 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 2) (le_bytes 4 4247762216))) with 64815 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 2) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 6221 by (vm_compute; reflexivity).
    change (2 ^ (8 * 2)) with 65536 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 3) (le_bytes 4 4247762216))) with 253 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 3) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 24 by (vm_compute; reflexivity).
    change (2 ^ (8 * 3)) with 16777216 in *. split; intros; Z.div_mod_to_equations; lia.
  - replace (le_value (skipn (Z.to_nat 4) (le_bytes 4 4247762216))) with 0 by (vm_compute; reflexivity).
    replace (le_value (skipn (Z.to_nat 4) (le_bytes 4 ZSTD_MAGIC_SKIPPABLE_START))) with 0 by (vm_compute; reflexivity).
    change (2 ^ (8 * 4)) with 4294967296 in *. split; intros; Z.div_mod_to_equations; lia.
Qed.

(* ---------- frames that cannot be decoded ---------- *)

Lemma series_not_end_m : forall md sel cd w s, s <> nil ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4)) = false ->
  (forall d c k, decode_frame_m md d w s <> FOk c k) ->
  snd (series_frames_m md sel cd w s) <> TEnd.
Proof.
  intros md sel cd w s Hs Hk Hd. unfold series_frames_m. rewrite walk_S.
  unfold wfirst. destruct (Zlength s <? starting_len _).
  - destruct (Zlength s =? 0) eqn:E; [|discriminate]. apply Z.eqb_eq in E. rewrite Zlength_correct in E.
    destruct s; [congruence|simpl in E; lia].
  - rewrite Hk. destruct (frame_dict _ _ _ _) as [d|]; [|discriminate].
    destruct (decode_frame_m md d w s) eqn:D; try discriminate. exfalso; eapply Hd; eauto.
Qed.

Lemma dfm_short : forall md dm w s,
  Zlength s < fhd_header_size (byte_at s (fpos (md_magicless md))) - fsh (md_magicless md) + 3 ->
  decode_frame_m md dm w s = FUnk.
Proof.
  intros md dm w s. destruct (md_magicless md) eqn:Hmg; intros H.
  - unfold decode_frame_m. rewrite Hmg. cbv zeta. cbn [negb andb fpos fsh] in *.
    destruct (Zlength s <? _); auto. change (4 - 4) with 0. unfold ZSTD_blockHeaderSize.
    replace (Zlength s <? fhd_header_size (byte_at s 0) - 4 + 3) with true by (symmetry; apply Z.ltb_lt; auto). auto.
  - rewrite dfm_eq0 by auto. apply df_short. cbn [fpos fsh] in H. lia.
Qed.

(* a frame behind a complete Zstandard header x *)
Lemma dfm_after_hdr : forall md dm w x h r, bytes_ok x ->
  get_frame_header_m (md_magicless md) x = FH_ok h -> fh_frameType h = 0 -> Zlength x = fh_headerSize h ->
  decode_frame_m md dm w (x ++ r) = FUnk \/
  (3 <= Zlength r /\ decode_frame_m md dm w (x ++ r) =
     if fh_windowSize h >? w then FDetHdr else if dict_bad dm h then FUnk else df_tail md dm h (x ++ r)).
Proof.
  intros md dm w x h r Hb G Ht Hl.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [H5 [_ [Hs [Hle _]]]]]]; [congruence|].
  pose proof (bytes_ok_byte_at x (fpos (md_magicless md)) Hb) as B.
  pose proof (fhs_m_ge md x B) as H9.
  pose proof (Zlength_nonneg r).
  assert (Hp: byte_at (x ++ r) (fpos (md_magicless md)) = byte_at x (fpos (md_magicless md))).
  { apply byte_at_app. clear -H5. destruct (md_magicless md); cbn [fpos starting_len] in *;
    unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *; lia. }
  destruct (Z_lt_dec (Zlength r) 3).
  - left. apply dfm_short. rewrite Hp, Zlength_app. lia.
  - right. split; [lia|]. apply dfm_unfold; auto.
    + apply gfhm_ext; auto.
    + rewrite Zlength_app; lia.
    + rewrite Zlength_app; lia.
Qed.

(* ---------- P_hdr_err_bad ---------- *)

Lemma hdr_err_z : forall md sel cd w x r, md_magicless md = false -> bytes_ok x -> x <> nil ->
  get_frame_header x = FH_err -> snd (series_frames_m md sel cd w (x ++ r)) <> TEnd.
Proof.
  intros md sel cd w x r Hmg Hb Hx H.
  pose proof (Zlength_nonneg r).
  assert (Hs: x ++ r <> nil) by (destruct x; [congruence|discriminate]).
  destruct (Z_lt_dec (Zlength x) 5) as [Hn|Hn].
  - (* fewer than 5 bytes: the magic number is already wrong *)
    unfold get_frame_header in H. cbv zeta in H.
    replace (Zlength x <? 5) with true in H by (symmetry; apply Z.ltb_lt; auto).
    assert (Hn0: 0 < Zlength x) by (rewrite Zlength_correct; destruct x; [congruence|simpl; lia]).
    replace (Zlength x >? 0) with true in H by (symmetry; apply Zgtb_gt; lia).
    destruct (negb (magic_prefix x ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER) &&
              negb (is_skippable_magic (magic_prefix x ZSTD_MAGIC_SKIPPABLE_START))) eqn:E; [|discriminate].
    apply Bool.andb_true_iff in E. destruct E as [E1 E2].
    apply Bool.negb_true_iff, Z.eqb_neq in E1. apply Bool.negb_true_iff in E2.
    destruct (Z_lt_dec (Zlength (x ++ r)) 5) as [Hl|Hl].
    { unfold series_frames_m. rewrite walk_S. unfold wfirst. rewrite Hmg. cbn [starting_len].
      unfold ZSTD_FRAMEHEADERSIZE_PREFIX.
      rewrite (proj2 (Z.ltb_lt _ _) Hl). rewrite Zlength_app.
      replace (Zlength x + Zlength r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). discriminate. }
    rewrite Zlength_app in Hl.
    assert (Hm: exists K, le_field (x ++ r) 0 4 = le_value x + 2 ^ (8 * Zlength x) * K).
    { unfold le_field, slice. simpl skipn. rewrite firstn_app.
      replace (firstn (Z.to_nat 4) x) with x by (symmetry; apply firstn_all2; rewrite Zlength_correct in Hn; lia).
      rewrite le_value_app. eauto. }
    destruct Hm as [K Hm].
    assert (Hp: forall fill, magic_prefix x fill =
               le_value x + 2 ^ (8 * Zlength x) * le_value (skipn (Z.to_nat (Zlength x)) (le_bytes 4 fill))).
    { intros. unfold magic_prefix. rewrite Z.min_r by lia.
      rewrite firstn_all2 by (rewrite Zlength_correct; lia). apply le_value_app. }
    rewrite Hp in E1, E2. clear Hp.
    destruct (le_value_bound x Hb) as [L0 L1]. rewrite <- Zlength_correct in L1.
    assert (HM: le_field (x ++ r) 0 4 <> ZSTD_MAGICNUMBER /\
                is_skippable_magic (le_field (x ++ r) 0 4) = false).
    { destruct (prefix_arith (Zlength x) (le_value x) K ltac:(lia) ltac:(lia)) as [A1 A2].
      rewrite Hm. split.
      - intro E. apply E1. auto.
      - destruct (is_skippable_magic (le_value x + 2 ^ (8 * Zlength x) * K)) eqn:S; auto.
        specialize (A2 eq_refl). congruence. }
    destruct HM as [HM1 HM2].
    apply series_not_end_m; auto.
    + rewrite Hmg. exact HM2.
    + intros d c k. rewrite dfm_nonmagic; auto. discriminate.
  - (* a complete prefix: magic number, descriptor, window byte *)
    unfold get_frame_header in H. cbv zeta in H.
    replace (Zlength x <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
    destruct (le_field x 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; cbn [negb] in H.
    + apply Z.eqb_eq in Em.
      destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:Ef; [discriminate|]. apply Z.ltb_ge in Ef.
      pose proof (fhs_ge6 _ (bytes_ok_byte_at x 4 Hb)).
      apply series_not_end_m; auto.
      { rewrite Hmg. cbn [negb andb]. rewrite le_field_app, Em by lia. apply skip_magic_false. }
      intros d c k. apply (dfm_bad_hdr md d w (x ++ r) c k). rewrite Hmg. cbn [fpos]. change (4 + 1) with 5.
      rewrite (byte_at_app x r 4), (byte_at_app x r 5) by lia.
      destruct (Z.land (byte_at x 4) 8 =? 0) eqn:Er; cbn [negb] in H.
      * right.
        destruct ((Z.land (Z.shiftr (byte_at x 4) 5) 1 =? 0) &&
                  (Z.shiftr (byte_at x 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew;
          [reflexivity|discriminate].
      * left. apply Z.eqb_neq. auto.
    + destruct (is_skippable_magic (le_field x 0 4)) eqn:Es; [destruct (_ <? _); discriminate|].
      apply series_not_end_m; auto.
      { rewrite Hmg. cbn [negb andb]. rewrite le_field_app by lia. auto. }
      intros d c k. rewrite dfm_nonmagic; auto; [discriminate|]. rewrite le_field_app by lia. apply Z.eqb_neq. auto.
Qed.

Lemma hdr_err_mg : forall md sel cd w x r, md_magicless md = true -> bytes_ok x -> x <> nil ->
  get_frame_header_m true x = FH_err -> snd (series_frames_m md sel cd w (x ++ r)) <> TEnd.
Proof.
  intros md sel cd w x r Hmg Hb Hx H.
  assert (Hn: 1 <= Zlength x) by (destruct x; [congruence|rewrite Zlength_cons; pose proof (Zlength_nonneg x); lia]).
  unfold get_frame_header_m in H. cbn [negb] in H.
  replace (Zlength x <? 1) with false in H by (symmetry; apply Z.ltb_ge; lia).
  destruct (get_frame_header (magic_bytes ++ x)) eqn:G; try discriminate. clear H.
  assert (HbX: bytes_ok (magic_bytes ++ x)) by (apply bytes_ok_app; split; [apply magic_bytes_ok|auto]).
  pose proof (fhs_ge6 _ (bytes_ok_byte_at _ 4 HbX)) as H6.
  replace (byte_at (magic_bytes ++ x) 4) with (byte_at x 0) in *
    by (rewrite <- (magic_byte x 0) by lia; reflexivity).
  replace (byte_at (magic_bytes ++ x) 5) with (byte_at x 1) in *
    by (rewrite <- (magic_byte x 1) by lia; reflexivity).
  unfold get_frame_header in G. cbv zeta in G.
  rewrite magic_field_app, Z.eqb_refl in G. cbn [negb] in G.
  rewrite Zlength_app, magic_len in G.
  replace (4 + Zlength x <? 5) with false in G by (symmetry; apply Z.ltb_ge; lia).
  replace (byte_at (magic_bytes ++ x) 4) with (byte_at x 0) in G
    by (rewrite <- (magic_byte x 0) by lia; reflexivity).
  replace (byte_at (magic_bytes ++ x) 5) with (byte_at x 1) in G
    by (rewrite <- (magic_byte x 1) by lia; reflexivity).
  destruct (4 + Zlength x <? fhd_header_size (byte_at x 0)) eqn:Ef; [discriminate|]. apply Z.ltb_ge in Ef.
  pose proof (Zlength_nonneg r).
  apply series_not_end_m.
  - destruct x; [congruence|discriminate].
  - rewrite Hmg. reflexivity.
  - intros d c k. apply (dfm_bad_hdr md d w (x ++ r) c k). rewrite Hmg. cbn [fpos]. change (0 + 1) with 1.
    rewrite (byte_at_app x r 0), (byte_at_app x r 1) by lia.
    destruct (Z.land (byte_at x 0) 8 =? 0) eqn:Er; cbn [negb] in G.
    + right.
      destruct ((Z.land (Z.shiftr (byte_at x 0) 5) 1 =? 0) &&
                (Z.shiftr (byte_at x 1) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew;
        [reflexivity|discriminate].
    + left. apply Z.eqb_neq. auto.
Qed.

Lemma hdr_err_bad_m : P_hdr_err_bad.
Proof.
  intros sm cd x Hb Hx H s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
  unfold sm_mg in H. revert H. destruct (md_magicless (sm_md sm)) eqn:Hmg; intros H.
  - apply hdr_err_mg; auto.
  - apply hdr_err_z; auto.
Qed.

(* ---------- P_hdr_skip, P_hdr_magicless ---------- *)

Lemma hdr_skip_m : P_hdr_skip.
Proof.
  intros sm cd x h Hb Hmg G Ht Hl. unfold sm_mg in Hmg.
  destruct (gfh_info _ _ G) as [[_ [H8 [_ [Hs [Hhs Hc]]]]]|[Ht' _]]; [|congruence].
  unfold ZSTD_SKIPPABLEHEADERSIZE. rewrite Hhs in Hl.
  split; auto. split; auto. split; auto.
  unfold cur_rel. cbv zeta. rewrite Hmg. unfold ZSTD_SKIPPABLEHEADERSIZE in *.
  pose proof (le_field_bound x 4 4 Hb ltac:(lia)).
  repeat split; auto; try lia.
  exists nil. rewrite app_nil_r. auto.
Qed.

Lemma hdr_magicless_m : P_hdr_magicless.
Proof. exact gfhm_magicless. Qed.

(* ---------- P_hdr_zstd ---------- *)

(* a complete Zstandard frame header: without a dictionary, or with another Dictionary_ID than the dictionary's,
   no extension is decoded and none is refused (the refusal walk stops at such a frame) *)
Lemma hdr_zstd_m : P_hdr_zstd.
Proof.
  intros sm cd x h Hb G Ht Hl. unfold sm_mg in *.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [H5 [Hm [Hs [Hle _]]]]]]; [congruence|].
  pose proof (bytes_ok_byte_at x (fpos (md_magicless (sm_md sm))) Hb) as B.
  assert (Hsk: forall r, negb (md_magicless (sm_md sm)) && is_skippable_magic (le_field (x ++ r) 0 4) = false).
  { intros r. clear -H5 Hm. destruct (md_magicless (sm_md sm)) eqn:E; auto. cbn [negb andb].
    cbn [starting_len] in H5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H5.
    rewrite le_field_app, (Hm eq_refl) by lia. apply skip_magic_false. }
  assert (Hsl: forall r, starting_len (md_magicless (sm_md sm)) <= Zlength (x ++ r)).
  { intros r. rewrite Zlength_app. pose proof (Zlength_nonneg r). lia. }
  assert (Hwf: forall w r cur, wfirst (sm_md sm) (sm_sel sm) cur w (x ++ r) =
     match frame_dict (md_magicless (sm_md sm)) (sm_sel sm) cur x with
     | None => inr TUnk
     | Some d => match decode_frame_m (sm_md sm) d w (x ++ r) with
                 | FOk c k => inl (k, c, false, Some d) | FDetHdr => inr TDetHdr
                 | FDetCk => inr TDetCk | FUnk => inr TUnk end
     end).
  { intros. unfold wfirst.
    replace (Zlength (x ++ r) <? starting_len _) with false by (symmetry; apply Z.ltb_ge; apply Hsl).
    rewrite Hsk, (frame_dict_ext _ _ _ _ _ _ G B). reflexivity. }
  assert (Hws: forall d w, fh_windowSize h > w -> forall r c k, decode_frame_m (sm_md sm) d w (x ++ r) <> FOk c k).
  { intros d w Hw r c k. destruct (dfm_after_hdr (sm_md sm) d w x h r Hb G Ht Hl) as [E|[_ E]]; rewrite E;
      [discriminate|]. replace (fh_windowSize h >? w) with true by (symmetry; apply Zgtb_gt; lia). discriminate. }
  split; [|split; [|split]].
  - intros Hn. split.
    + intros s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
      unfold series_frames_m. rewrite walk_S, Hwf, Hn. reflexivity.
    + intros s Hbs Hp R. apply is_prefix_ex in Hp. destruct Hp as [r ->].
      unfold series_refused_m in R. rewrite wref_S, Hwf, Hn in R.
      unfold wref in R. replace (Zlength (x ++ r) <? starting_len _) with false in R
        by (symmetry; apply Z.ltb_ge; apply Hsl).
      rewrite Hsk, (frame_dict_ext _ _ _ _ _ _ G B), Hn in R. exact R.
  - intros dm Hd Hd0 Hd1.
    assert (Hdec: forall r, decode_frame_m (sm_md sm) dm no_wlim (x ++ r) = FUnk).
    { intros r. destruct (dfm_after_hdr (sm_md sm) dm no_wlim x h r Hb G Ht Hl) as [E|[_ E]]; rewrite E; [reflexivity|].
      replace (fh_windowSize h >? no_wlim) with false by (symmetry; apply Zgtb_le; eapply gfhm_ws; eauto).
      replace (dict_bad dm h) with true. { reflexivity. }
      unfold dict_bad. symmetry. apply Bool.andb_true_iff. split; apply Bool.negb_true_iff, Z.eqb_neq; auto. }
    split.
    + intros s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
      unfold series_frames_m. rewrite walk_S, Hwf, Hd, Hdec. reflexivity.
    + intros s Hbs Hp R. apply is_prefix_ex in Hp. destruct Hp as [r ->].
      unfold series_refused_m in R. rewrite wref_S, Hwf, Hd, Hdec in R.
      rewrite (wref_dict _ _ _ _ _ dm (Hsl r) (Hsk r)) in R by (rewrite (frame_dict_ext _ _ _ _ _ _ G B); exact Hd).
      rewrite Hdec in R. apply (frame_refused_prefix _ _ _ _ _ _ Hb G) in R.
      destruct (frame_refused_dict _ _ _ _ _ G Ht ltac:(lia) R); auto.
  - intros Hw0 Hw s Hp. apply is_prefix_ex in Hp. destruct Hp as [r ->].
    apply series_not_end_m.
    + intro E. apply (f_equal (@length Z)) in E. rewrite length_app in E. simpl in E.
      pose proof (starting_len_pos (md_magicless (sm_md sm))). rewrite Zlength_correct in H5. lia.
    + apply Hsk.
    + intros d. apply Hws. lia.
  - intros dm Hd Hdi. unfold cur_rel, z_start, sm_bsm. cbv zeta. cbn [zp_h zp_bl zp_ts zp_out zp_ph zp_got zp_dm zp_bsm zp_ign].
    repeat split; auto. exists nil, false. split; [constructor|]. rewrite !app_nil_r. repeat split; auto.
    all: change (Zlength (@nil Z)) with 0; unfold ZSTD_blockHeaderSize; lia.
Qed.

(* ---------- P_hdr_more_size, P_hdr_more_ext ---------- *)

Lemma hdr_more_size_z : forall x k, get_frame_header x = FH_more k -> Zlength x < k.
Proof.
  intros x k H. unfold get_frame_header in H. cbv zeta in H.
  destruct (Zlength x <? 5) eqn:E1.
  { apply Z.ltb_lt in E1. destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion H; subst; lia. }
  destruct (negb (le_field x 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E; [|discriminate].
    inversion H; subst. apply Z.ltb_lt in E. auto. }
  destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:E.
  { inversion H; subst. apply Z.ltb_lt in E. auto. }
  destruct (negb _); [discriminate|]. destruct (_ && _); discriminate.
Qed.

Lemma hdr_more_size_m : P_hdr_more_size.
Proof.
  intros [|] x k H; unfold get_frame_header_m in H; cbn [negb] in H; [|apply hdr_more_size_z; exact H].
  destruct (Zlength x <? 1) eqn:E. { inversion H; subst. apply Z.ltb_lt in E. lia. }
  destruct (get_frame_header (magic_bytes ++ x)) eqn:G; inversion H; subst.
  apply hdr_more_size_z in G. rewrite Zlength_app, magic_len in G. lia.
Qed.

Lemma hdr_more_ext_z : forall x y k, bytes_ok (x ++ y) ->
  get_frame_header x = FH_more k -> Zlength (x ++ y) <= k ->
  match get_frame_header (x ++ y) with
  | FH_ok h => fh_headerSize h = Zlength (x ++ y)
  | FH_more k' => Zlength (x ++ y) < k'
  | FH_err => True
  end.
Proof.
  intros x y k Hb Hx Hk.
  destruct (get_frame_header (x ++ y)) as [|k'|h] eqn:G; auto.
  { eapply hdr_more_size_z; eauto. }
  pose proof (Zlength_nonneg y).
  unfold get_frame_header in Hx. cbv zeta in Hx.
  destruct (gfh_info _ _ G) as [[Ht [H8 [Em [Es [Hs _]]]]]|[Ht [H5 [Em [Hs [Hle _]]]]]].
  - destruct (Zlength x <? 5) eqn:E5.
    { destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion Hx; subst; lia. }
    apply Z.ltb_ge in E5. rewrite Zlength_app in *.
    rewrite le_field_app in Em, Es by lia. rewrite Em, Es in Hx. cbn [negb] in Hx.
    destruct (Zlength x <? ZSTD_SKIPPABLEHEADERSIZE); inversion Hx; subst.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *. lia.
  - apply bytes_ok_app in Hb. destruct Hb as [Hbx Hby].
    destruct (Zlength x <? 5) eqn:E5.
    { pose proof (fhs_ge6 (byte_at (x ++ y) 4) (bytes_ok_byte_at _ _ (proj2 (bytes_ok_app x y) (conj Hbx Hby)))).
      destruct (Zlength x >? 0); [destruct (_ && _)|]; inversion Hx; subst; lia. }
    apply Z.ltb_ge in E5. rewrite Zlength_app in *.
    rewrite le_field_app in Em by lia. rewrite (byte_at_app x y 4) in Hs by lia.
    rewrite Em, Z.eqb_refl in Hx. cbn [negb] in Hx.
    destruct (Zlength x <? fhd_header_size (byte_at x 4)) eqn:Ef.
    + inversion Hx; subst. lia.
    + destruct (negb _); [discriminate|]. destruct (_ && _); discriminate.
Qed.

Lemma gfh_magic_nil : get_frame_header magic_bytes = FH_more 5.
Proof. vm_compute. reflexivity. Qed.

Lemma gfhm_true_more : forall x k, get_frame_header_m true x = FH_more k ->
  get_frame_header (magic_bytes ++ x) = FH_more (k + 4).
Proof.
  intros x k H. unfold get_frame_header_m in H. cbn [negb] in H.
  destruct (Zlength x <? 1) eqn:E.
  - inversion H; subst. apply Z.ltb_lt in E.
    destruct x; [|rewrite Zlength_cons in E; pose proof (Zlength_nonneg x); lia].
    rewrite app_nil_r. exact gfh_magic_nil.
  - destruct (get_frame_header (magic_bytes ++ x)); inversion H; subst. f_equal; lia.
Qed.

Lemma hdr_more_ext_m : P_hdr_more_ext.
Proof.
  intros [|] x y k Hb H Hk; [|exact (hdr_more_ext_z x y k Hb H Hk)].
  apply gfhm_true_more in H.
  pose proof (hdr_more_ext_z (magic_bytes ++ x) y (k + 4)) as V.
  rewrite <- app_assoc in V.
  assert (Hb': bytes_ok (magic_bytes ++ x ++ y)) by (apply bytes_ok_app; split; [apply magic_bytes_ok|auto]).
  specialize (V Hb' H ltac:(rewrite !Zlength_app, magic_len; rewrite Zlength_app in Hk; lia)).
  unfold get_frame_header_m. cbn [negb].
  destruct (Zlength (x ++ y) <? 1) eqn:E.
  { change (Zlength (x ++ y) < 1). apply Z.ltb_lt. exact E. }
  destruct (get_frame_header (magic_bytes ++ x ++ y)) as [|k'|h]; [exact I| |];
    rewrite !Zlength_app, magic_len in V; cbn [fh_unshift fh_headerSize]; rewrite Zlength_app; lia.
Qed.

Lemma M3_hdr : P_hdr_err_bad /\ P_hdr_skip /\ P_hdr_magicless /\ P_hdr_zstd /\ P_hdr_more_size /\ P_hdr_more_ext.
Proof.
  split; [exact hdr_err_bad_m|]. split; [exact hdr_skip_m|]. split; [exact hdr_magicless_m|].
  split; [exact hdr_zstd_m|]. split; [exact hdr_more_size_m|exact hdr_more_ext_m].
Qed.
