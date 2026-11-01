(* FS3 streaming model facts (a copy of modelw/MW3Frame.v): one Zstandard frame under a mode md and a dictionary dm.
   dfz = decode_frame_m in the zstd1 format (with md's checksum policy and block size cap); a magicless
   frame is the zstd1 frame of the same bytes behind the magic number (dfm_eq). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.lh.LH3R2MBase.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition df_tail (md: dmode) (dm: dict_model) (h: frame_header) (s: list Z) : fres :=
  let hs := fh_headerSize h in
  let rest := skipn (Z.to_nat hs) s in
  match dblocks (md_dwin md) (length rest) (dm_state dm) (dm_content dm) rest nil
          (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) with
  | None => FUnk
  | Some (out, k) =>
      if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
      then FUnk else
      if fh_checksumFlag h =? 1 then
        (if Zlength s - hs - k <? 4 then FUnk
         else if negb (md_ignore md) && negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
         else FOk out (hs + k + 4))
      else FOk out (hs + k)
  end.

(* the zstd1 frame decoder under md *)
Definition dfz (md: dmode) (dm: dict_model) (w: Z) (s: list Z) : fres :=
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize then FUnk else
  if negb (le_field s 0 4 =? ZSTD_MAGICNUMBER) then FUnk else
  let fhd := byte_at s 4 in
  if Zlength s <? fhd_header_size fhd + ZSTD_blockHeaderSize then FUnk else
  if negb (Z.land fhd 8 =? 0) then FDetHdr else
  let single := Z.land (Z.shiftr fhd 5) 1 =? 1 in
  if negb single && (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)
  then FDetHdr else
  match get_frame_header s with
  | FH_ok h =>
      if fh_windowSize h >? w then FDetHdr else
      if negb (fh_frameType h =? 0) then FUnk else
      if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
      df_tail md dm h s
  | _ => FUnk
  end.

Definition fsub4 (r: fres) : fres := match r with FOk c k => FOk c (k - 4) | _ => r end.

Lemma magic_len : Zlength magic_bytes = 4.
Proof. reflexivity. Qed.

Lemma magic_field : le_field magic_bytes 0 4 = ZSTD_MAGICNUMBER.
Proof. vm_compute. reflexivity. Qed.

Lemma magic_bytes_ok : bytes_ok magic_bytes.
Proof. unfold bytes_ok, is_byte. vm_compute. repeat constructor; discriminate. Qed.

Lemma byte_at_app_r : forall a b i, 0 <= i -> byte_at (a ++ b) (Zlength a + i) = byte_at b i.
Proof.
  intros. unfold byte_at. rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (length a) + i)) with (length a + Z.to_nat i)%nat by lia.
  rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma magic_field_app : forall s, le_field (magic_bytes ++ s) 0 4 = ZSTD_MAGICNUMBER.
Proof. intros. rewrite le_field_app by (rewrite ?magic_len; lia). apply magic_field. Qed.

Lemma magic_byte : forall s i, 0 <= i -> byte_at (magic_bytes ++ s) (4 + i) = byte_at s i.
Proof. intros. rewrite <- magic_len at 1. apply byte_at_app_r; auto. Qed.

Lemma fhs_ge5 : forall fhd, 5 <= fhd_header_size fhd.
Proof.
  intros. unfold fhd_header_size.
  assert (forall n l, Forall (fun v => 0 <= v) l -> 0 <= nth n l 0).
  { induction n; destruct l; simpl; intros; try lia; inversion H; auto. }
  pose proof (H (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] ltac:(repeat constructor; lia)).
  pose proof (H (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] ltac:(repeat constructor; lia)).
  destruct (land1_cases (Z.shiftr fhd 5)) as [E|E]; rewrite E;
  destruct (_ && _); lia.
Qed.

Lemma skipn_magic : forall s n, 4 <= n -> skipn (Z.to_nat n) (magic_bytes ++ s) = skipn (Z.to_nat (n - 4)) s.
Proof.
  intros. rewrite skipn_app. rewrite skipn_all2 by (change (length magic_bytes) with 4%nat; lia).
  change (length magic_bytes) with 4%nat. simpl. f_equal. lia.
Qed.

Lemma gfh_magic : forall s h, get_frame_header (magic_bytes ++ s) = FH_ok h ->
  fh_frameType h = 0 /\ 5 <= fh_headerSize h /\ fh_headerSize h = fhd_header_size (byte_at s 0) /\ fh_headerSize h <= 4 + Zlength s.
Proof.
  intros s h G. destruct (gfh_info _ _ G) as [[_ [_ [Hm _]]]|[Ht [_ [_ [Hs [Hle _]]]]]].
  - rewrite magic_field_app, Z.eqb_refl in Hm. discriminate.
  - rewrite Zlength_app, magic_len in Hle. rewrite <- (magic_byte s 0) by lia. simpl Z.add in Hs.
    pose proof (fhs_ge5 (byte_at (magic_bytes ++ s) 4)). rewrite Z.add_0_r. repeat split; lia.
Qed.

Lemma dfm_eq : forall md dm w s, bytes_ok s ->
  decode_frame_m md dm w s = if md_magicless md then fsub4 (dfz md dm w (magic_bytes ++ s)) else dfz md dm w s.
Proof.
  intros md dm w s Hb. destruct (md_magicless md) eqn:Hmg.
  2:{ unfold decode_frame_m, get_frame_header_m, dfz, df_tail. rewrite Hmg. cbv zeta. cbn [negb andb]. rewrite !Z.sub_0_r. reflexivity. }
  unfold decode_frame_m, get_frame_header_m, dfz. rewrite Hmg. cbv zeta. cbn [negb andb].
  rewrite Zlength_app, magic_len, magic_field_app, Z.eqb_refl. cbn [negb].
  replace (byte_at (magic_bytes ++ s) 4) with (byte_at s 0) by (rewrite <- (magic_byte s 0) by lia; reflexivity).
  replace (byte_at (magic_bytes ++ s) 5) with (byte_at s 1) by (rewrite <- (magic_byte s 1) by lia; reflexivity).
  change (4 - 4) with 0. change (5 - 4) with 1. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
  destruct (Zlength s <? 6 - 4 + 3) eqn:E1;
    [replace (4 + Zlength s <? 6 + 3) with true by (symmetry; apply Z.ltb_lt; apply Z.ltb_lt in E1; lia); reflexivity|].
  apply Z.ltb_ge in E1. replace (4 + Zlength s <? 6 + 3) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? fhd_header_size (byte_at s 0) - 4 + 3) with (4 + Zlength s <? fhd_header_size (byte_at s 0) + 3)
    by (apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia).
  destruct (4 + Zlength s <? _); [reflexivity|].
  destruct (negb _); [reflexivity|]. destruct (_ && _); [reflexivity|].
  replace (Zlength s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (get_frame_header (magic_bytes ++ s)) as [|k|h] eqn:G; try reflexivity.
  destruct (gfh_magic _ _ G) as [Ht [H5 _]].
  cbn [fh_unshift fh_windowSize fh_frameType fh_dictID fh_blockSizeMax fh_contentSize fh_checksumFlag fh_headerSize].
  destruct (fh_windowSize h >? w); [reflexivity|]. destruct (negb _); [reflexivity|]. destruct (_ && _); [reflexivity|].
  unfold df_tail. rewrite skipn_magic by lia.
  change (if md_dwin md then decode_blocks_w else decode_blocks) with (dblocks (md_dwin md)).
  destruct (dblocks (md_dwin md) _ _ _ _ _ _ _) as [[out k]|] eqn:D; [|reflexivity].
  pose proof (db_pos _ _ _ _ _ _ _ _ _ _ D (bytes_ok_skipn _ _ Hb)).
  destruct (_ && _); [reflexivity|].
  destruct (fh_checksumFlag h =? 1); [|simpl; f_equal; lia].
  rewrite Zlength_app, magic_len.
  replace (4 + Zlength s - fh_headerSize h - k) with (Zlength s - (fh_headerSize h - 4) - k) by lia.
  destruct (_ <? 4); [reflexivity|].
  replace (fh_headerSize h + k) with (Zlength magic_bytes + (fh_headerSize h - 4 + k)) by (rewrite magic_len; lia).
  rewrite le_field_app_r by lia.
  destruct (_ && _); [reflexivity|]. rewrite magic_len. cbn [fsub4]. f_equal. lia.
Qed.

(* ---------- the zstd1 frame decoder dfz ---------- *)

Definition dict_bad (dm: dict_model) (h: frame_header) : bool :=
  negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm).

Lemma dict_ok_bad : forall dm h, fh_dictID h = 0 \/ fh_dictID h = dm_id dm -> dict_bad dm h = false.
Proof.
  unfold dict_bad; intros dm h [E|E]; rewrite E, Z.eqb_refl; [reflexivity|apply Bool.andb_false_r].
Qed.

Lemma bp_last_len : forall dw hist bsm ws ts0 bl ts out, blocks_pre dw hist bsm ws ts0 bl ts out true -> 3 <= Zlength bl.
Proof.
  intros. inversion H; subst.
  unfold block_res in H1. destruct (cblock_size b) eqn:Ec; [|discriminate].
  apply cblock_size_len in Ec. rewrite Zlength_app. pose proof (Zlength_nonneg bl0). lia.
Qed.

Lemma skip_magic_false : is_skippable_magic ZSTD_MAGICNUMBER = false.
Proof. reflexivity. Qed.

Definition df_fin (md: dmode) (h: frame_header) (s: list Z) (r: option (list Z * Z)) : fres :=
  let hs := fh_headerSize h in
  match r with
  | None => FUnk
  | Some (out, k) =>
      if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
      then FUnk else
      if fh_checksumFlag h =? 1 then
        (if Zlength s - hs - k <? 4 then FUnk
         else if negb (md_ignore md) && negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
         else FOk out (hs + k + 4))
      else FOk out (hs + k)
  end.

Section Z1.
Variable md : dmode.
Variable dm : dict_model.

Lemma df_unfold : forall w s h, get_frame_header s = FH_ok h -> fh_frameType h = 0 ->
  9 <= Zlength s -> fh_headerSize h + 3 <= Zlength s ->
  dfz md dm w s =
    if fh_windowSize h >? w then FDetHdr else if dict_bad dm h then FUnk else df_tail md dm h s.
Proof.
  intros w s h H Ht H9 H3.
  destruct (gfh_info _ _ H) as [[Ht' _]|[_ [_ [Hm [Hs [_ [Hr Hw]]]]]]]; [congruence|].
  unfold dfz. cbv zeta.
  replace (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) with false
    by (symmetry; apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize; lia).
  rewrite Hm, Z.eqb_refl. cbn [negb].
  replace (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) with false
    by (symmetry; apply Z.ltb_ge; unfold ZSTD_blockHeaderSize; lia).
  rewrite Hr. cbn [negb Z.eqb]. rewrite Hw, H, Ht. cbn [negb Z.eqb].
  destruct (fh_windowSize h >? w); auto.
Qed.


Lemma df_skip : forall w s, 4 <= Zlength s -> is_skippable_magic (le_field s 0 4) = true ->
  dfz md dm w s = FUnk.
Proof.
  intros. unfold dfz. destruct (Zlength s <? _); auto. rewrite skip_not_magic by auto. auto.
Qed.

Lemma df_hdr_inv : forall w s, dfz md dm w s <> FUnk -> dfz md dm w s <> FDetHdr ->
  exists h, get_frame_header s = FH_ok h /\ fh_frameType h = 0 /\ 9 <= Zlength s /\
    fh_headerSize h + 3 <= Zlength s /\ fh_windowSize h <= w /\ dict_bad dm h = false /\
    dfz md dm w s = df_tail md dm h s.
Proof.
  intros w s H1 H2.
  assert (A: exists h, get_frame_header s = FH_ok h /\ fh_frameType h = 0 /\ 9 <= Zlength s /\
                       fh_headerSize h + 3 <= Zlength s).
  { unfold dfz in H1, H2. cbv zeta in H1, H2.
    destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
    destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
    destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) eqn:E3; [congruence|].
    destruct (negb (Z.land (byte_at s 4) 8 =? 0)) eqn:E4; [congruence|].
    destruct (_ && _) eqn:E5; [congruence|].
    destruct (get_frame_header s) as [| |h] eqn:G; try congruence.
    destruct (fh_windowSize h >? w); [congruence|].
    destruct (negb (fh_frameType h =? 0)) eqn:E6; [congruence|].
    exists h. apply Z.ltb_ge in E1, E3. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *.
    destruct (gfh_info _ _ G) as [[Ht _]|[Ht [_ [_ [Hs _]]]]].
    - rewrite Ht in E6. discriminate.
    - repeat split; auto; lia. }
  destruct A as [h [G [Ht [H9 H3]]]].
  rewrite (df_unfold w s h G Ht H9 H3) in *.
  exists h. repeat split; auto.
  - destruct (fh_windowSize h >? w) eqn:E; [congruence|]. apply Zgtb_le in E; auto.
  - destruct (fh_windowSize h >? w); [congruence|].
    destruct (dict_bad dm h); congruence.
  - destruct (fh_windowSize h >? w); [congruence|].
    destruct (dict_bad dm h); congruence.
Qed.

Lemma df_fcs : forall w s c k, dfz md dm w s = FOk c k -> frame_compressed_size s = Some k.
Proof.
  intros w s c k H.
  destruct (df_hdr_inv w s) as [h [G [Ht [H9 [H3 [_ [_ E]]]]]]]; try congruence.
  rewrite E in H. clear E.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [Hm _]]]]; [congruence|].
  unfold frame_compressed_size. rewrite Hm. change (is_skippable_magic ZSTD_MAGICNUMBER) with false.
  rewrite Bool.andb_false_r. rewrite G. cbv zeta.
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

Lemma df_ext : forall w x k r, frame_compressed_size x = Some k -> 0 <= byte_at x 4 < 256 ->
  dfz md dm w (x ++ r) = dfz md dm w x.
Proof.
  intros w x k r H Hb. unfold frame_compressed_size in H.
  destruct ((Zlength x >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field x 0 4)) eqn:Ea.
  - apply Bool.andb_true_iff in Ea. destruct Ea as [E8 Es]. apply Z.geb_le in E8.
    unfold ZSTD_SKIPPABLEHEADERSIZE in E8. pose proof (Zlength_nonneg r).
    rewrite !df_skip; auto; try (rewrite ?Zlength_app; lia).
    rewrite le_field_app by lia. auto.
  - destruct (get_frame_header x) as [| |h] eqn:G; try discriminate. cbv zeta in H.
    destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
    destruct (gfh_info _ _ G) as [[_ [E8 [_ [Es _]]]]|[Ht [H5 [Hm [Hs [Hle _]]]]]].
    { unfold ZSTD_SKIPPABLEHEADERSIZE in Ea. rewrite Es in Ea.
      replace (Zlength x >=? 8) with true in Ea by (symmetry; apply Z.geb_le; lia). discriminate. }
    pose proof (fhs_ge6 _ Hb) as H6. rewrite <- Hs in H6.
    destruct (bs_len _ _ _ _ B) as [B3 Bk].
    rewrite Zlength_skipn in B3, Bk by lia.
    pose proof (Zlength_nonneg r).
    assert (G' := gfh_ext x r h G Hb).
    rewrite (df_unfold w x h), (df_unfold w (x ++ r) h); auto; try (rewrite ?Zlength_app; lia).
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



Lemma gfh_ws : forall s h, get_frame_header s = FH_ok h -> bytes_ok s -> fh_windowSize h <= no_wlim.
Proof.
  intros s h H Hb. pose proof (gfh_len _ _ H) as Hn.
  unfold get_frame_header in H. cbv zeta in H.
  replace (Zlength s <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
  unfold no_wlim.
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|]. inversion H; subst. simpl. lia. }
  destruct (Zlength s <? _); [discriminate|].
  destruct (negb _); [discriminate|].
  destruct (_ && _) eqn:Ew; [discriminate|].
  inversion H; subst; clear H. cbn [fh_windowSize].
  pose proof (bytes_ok_byte_at s 5 Hb) as B5.
  destruct (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1) eqn:Es.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    try match goal with |- context [byte_at s ?p] => pose proof (bytes_ok_byte_at s p Hb) end;
    try match goal with |- context [le_field s ?p ?k] => pose proof (le_field_bound s p k Hb ltac:(lia)) end;
    unfold ZSTD_CONTENTSIZE_UNKNOWN in *; simpl in *; lia.
  - destruct (land1_cases (Z.shiftr (byte_at s 4) 5)) as [E|E]; rewrite E in *; [|discriminate].
    simpl in Ew. apply Zgtb_le in Ew. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in *.
    set (wl := Z.shiftr (byte_at s 5) 3 + 10) in *.
    assert (0 <= Z.shiftr (byte_at s 5) 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
    assert (0 <= 2 ^ wl <= 2 ^ 31) by (split; [apply Z.pow_nonneg; lia|apply Z.pow_le_mono_r; lia]).
    assert (0 <= Z.land (byte_at s 5) 7 <= 7).
    { pose proof (Z.land_ones (byte_at s 5) 3 ltac:(lia)) as E7.
      change (Z.ones 3) with 7 in E7. change (2 ^ 3) with 8 in E7. rewrite E7.
      pose proof (Z.mod_pos_bound (byte_at s 5) 8). lia. }
    rewrite (Z.shiftr_div_pow2 (2 ^ wl) 3) by lia. change (2 ^ 3) with 8.
    assert (0 <= 2 ^ wl / 8 <= 2 ^ 31) by (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia]).
    nia.
Qed.



Lemma df_cur_pre : forall w hdr h r,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr -> 3 <= Zlength r ->
  dfz md dm w (hdr ++ r) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin md h (hdr ++ r) (dblocks (md_dwin md) (length r) (dm_state dm) (dm_content dm) r nil (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h)).
Proof.
  intros w hdr h r G Hl Ht Hd Hb H3.
  pose proof (bytes_ok_byte_at hdr 4 Hb) as B4.
  pose proof (gfh_ext _ r _ G B4) as G'.
  destruct (gfh_info _ _ G) as [[Ht' _]|[_ [_ [_ [Hs _]]]]]; [congruence|].
  pose proof (fhs_ge6 _ B4).
  rewrite (df_unfold w _ h G' Ht) by (rewrite Zlength_app; lia).
  destruct (fh_windowSize h >? w); auto. rewrite (dict_ok_bad dm h Hd). cbv iota.
  unfold df_tail. cbv zeta. rewrite <- Hl.
  replace (skipn (Z.to_nat (Zlength hdr)) (hdr ++ r)) with r.
  2:{ rewrite skipn_app, Zlength_correct, Nat2Z.id, skipn_all, Nat.sub_diag. auto. }
  unfold df_fin. rewrite <- Hl. auto.
Qed.

Lemma df_cur : forall w hdr h bl ts outc t,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr ->
  blocks_pre (md_dwin md) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) (dm_state dm) bl ts outc false -> 3 <= Zlength (bl ++ t) ->
  exists fuel, (length t <= fuel)%nat /\
    dfz md dm w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else
    df_fin md h (hdr ++ bl ++ t) (oshift (Zlength bl) (dblocks (md_dwin md) fuel ts (dm_content dm) t outc (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h))).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp H3.
  destruct (bp_db _ _ _ _ _ _ _ _ _ Hbp eq_refl) as [n [Hn Hdb]].
  exists (length (bl ++ t) - n)%nat. split; [rewrite length_app; lia|].
  rewrite (df_cur_pre w hdr h (bl ++ t)) by auto.
  replace (length (bl ++ t)) with (n + (length (bl ++ t) - n))%nat at 1 by (rewrite length_app; lia).
  rewrite Hdb. auto.
Qed.

Lemma df_cur_last : forall w hdr h bl ts outc t,
  get_frame_header hdr = FH_ok h -> Zlength hdr = fh_headerSize h -> fh_frameType h = 0 ->
  (fh_dictID h = 0 \/ fh_dictID h = dm_id dm) -> bytes_ok hdr ->
  blocks_pre (md_dwin md) (dm_content dm) (Z.min (fh_blockSizeMax h) (md_bmax md)) (fh_windowSize h) (dm_state dm) bl ts outc true ->
  dfz md dm w (hdr ++ bl ++ t) =
    if fh_windowSize h >? w then FDetHdr else df_fin md h (hdr ++ bl ++ t) (Some (outc, Zlength bl)).
Proof.
  intros w hdr h bl ts outc t G Hl Ht Hd Hb Hbp.
  pose proof (bp_last_len _ _ _ _ _ _ _ _ Hbp).
  rewrite (df_cur_pre w hdr h (bl ++ t)) by (auto; rewrite Zlength_app; pose proof (Zlength_nonneg t); lia).
  rewrite (bp_db_last _ _ _ _ _ _ _ _ Hbp) by (rewrite length_app; lia). auto.
Qed.



Lemma df_wlim_rev : forall w1 w2 s c k, w2 <= w1 -> dfz md dm w2 s = FOk c k ->
  dfz md dm w1 s = FOk c k.
Proof.
  intros. destruct (df_hdr_inv w2 s) as [h [G [Ht [H9 [H3 [Hw [Hd E]]]]]]]; try congruence.
  rewrite (df_unfold w1 s h G Ht H9 H3).
  replace (fh_windowSize h >? w1) with false by (symmetry; apply Zgtb_le; lia).
  rewrite Hd. congruence.
Qed.


Lemma df_nonmagic : forall w s, le_field s 0 4 <> ZSTD_MAGICNUMBER -> dfz md dm w s = FUnk.
Proof.
  intros. unfold dfz. destruct (Zlength s <? _); auto.
  replace (le_field s 0 4 =? ZSTD_MAGICNUMBER) with false by (symmetry; apply Z.eqb_neq; auto). auto.
Qed.

Lemma df_short : forall w s, Zlength s < fhd_header_size (byte_at s 4) + 3 -> dfz md dm w s = FUnk.
Proof.
  intros. unfold dfz. destruct (Zlength s <? _); auto. destruct (negb _); auto. cbv zeta.
  unfold ZSTD_blockHeaderSize. replace (Zlength s <? fhd_header_size (byte_at s 4) + 3) with true
    by (symmetry; apply Z.ltb_lt; auto). auto.
Qed.

Lemma df_bad_hdr : forall w s c k,
  Z.land (byte_at s 4) 8 <> 0 \/
  ((Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0) &&
   (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) = true ->
  dfz md dm w s <> FOk c k.
Proof.
  intros w s c k H. unfold dfz. cbv zeta.
  destruct (Zlength s <? _); [discriminate|]. destruct (negb _); [discriminate|].
  destruct (Zlength s <? _); [discriminate|].
  destruct H as [H|H].
  - replace (Z.land (byte_at s 4) 8 =? 0) with false by (symmetry; apply Z.eqb_neq; auto). discriminate.
  - destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
    destruct (land1_cases (Z.shiftr (byte_at s 4) 5)) as [E|E]; rewrite E in *; [|discriminate].
    simpl in H. simpl. rewrite H. discriminate.
Qed.


End Z1.
