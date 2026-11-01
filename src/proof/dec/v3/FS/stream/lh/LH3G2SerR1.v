(* FS3 streaming, G2: appending a complete series to a complete series (Params.walk_m, the
   dictionary threading series_cur).  Plain Coq. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.Params Zstd.proof.model.ParamsW Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.FS.StreamModelFacts.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Local Open Scope bool_scope.

(* ---------- blocks: prefix stability, any history ---------- *)

Lemma g2_zlen_skipn_le : forall (l: list Z) n, n <= Zlength l -> Zlength (skipn (Z.to_nat n) l) <= Zlength l - n.
Proof.
  intros. destruct (Z_lt_dec n 0).
  - replace (Z.to_nat n) with O by lia. simpl. lia.
  - rewrite Zlength_skipn by lia. lia.
Qed.

Lemma g2_db_ext : forall f st hist s out bsm ws o k,
  decode_blocks f st hist s out bsm ws = Some (o, k) ->
  k <= Zlength s /\ forall y f', (f <= f')%nat -> decode_blocks f' st hist (s ++ y) out bsm ws = Some (o, k).
Proof.
  induction f; intros st hist s out bsm ws o k H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec) as H3.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:Eg; [discriminate|].
  apply Zgtb_le in Eg. unfold ZSTD_blockHeaderSize in *.
  assert (Hslice: forall y, slice (s ++ y) 3 c = slice s 3 c) by (intros; apply slice_app'; lia).
  assert (Hrest: forall y, skipn (Z.to_nat (3 + c)) (s ++ y) = skipn (Z.to_nat (3 + c)) s ++ y)
    by (intros; apply skipn_app_le; rewrite Zlength_correct in *; lia).
  cbv zeta in H.
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Er end; [|discriminate].
  assert (Hy: forall y f', (f <= f')%nat ->
    decode_blocks (S f') st hist (s ++ y) out bsm ws =
    if bp_last (block_props_of s) =? 1 then Some (out', 3 + c)
    else match decode_blocks f' st' hist (skipn (Z.to_nat (3 + c)) s ++ y) out' bsm ws with
         | Some (o0, k0) => Some (o0, 3 + c + k0) | None => None end).
  { intros y f' Hf. cbn [decode_blocks].
    rewrite (cblock_size_app s y H3), Ec. pose proof (Zlength_nonneg y).
    replace (c >? Zlength (s ++ y) - ZSTD_blockHeaderSize) with false
      by (symmetry; apply Zgtb_le; rewrite Zlength_app; unfold ZSTD_blockHeaderSize; lia).
    rewrite (block_props_app s y H3). unfold ZSTD_blockHeaderSize. rewrite Hslice. cbv zeta. rewrite Er.
    rewrite Hrest. auto. }
  destruct (bp_last (block_props_of s) =? 1) eqn:El.
  - assert (k = 3 + c) by congruence. split; [lia|].
    intros y f' Hf. destruct f' as [|f']; [lia|]. rewrite Hy by lia. congruence.
  - destruct (decode_blocks f st' hist (skipn (Z.to_nat (3 + c)) s) out' bsm ws) as [[o2 k2]|] eqn:E2;
      [|discriminate].
    assert (k = 3 + c + k2) by congruence. destruct (IHf _ _ _ _ _ _ _ _ E2) as [Hk IH].
    split. { pose proof (g2_zlen_skipn_le s (3 + c) ltac:(lia)). lia. }
    intros y f' Hf. destruct f' as [|f']; [lia|]. rewrite Hy by lia. rewrite IH by lia. congruence.
Qed.

Lemma g2_dbw_ext : forall f st hist s out bsm ws o k,
  decode_blocks_w f st hist s out bsm ws = Some (o, k) ->
  k <= Zlength s /\ forall y f', (f <= f')%nat -> decode_blocks_w f' st hist (s ++ y) out bsm ws = Some (o, k).
Proof.
  induction f; intros st hist s out bsm ws o k H; [discriminate|].
  cbn [decode_blocks_w] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_len _ _ Ec) as H3.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:Eg; [discriminate|].
  apply Zgtb_le in Eg. unfold ZSTD_blockHeaderSize in *.
  assert (Hslice: forall y, slice (s ++ y) 3 c = slice s 3 c) by (intros; apply slice_app'; lia).
  assert (Hrest: forall y, skipn (Z.to_nat (3 + c)) (s ++ y) = skipn (Z.to_nat (3 + c)) s ++ y)
    by (intros; apply skipn_app_le; rewrite Zlength_correct in *; lia).
  cbv zeta in H.
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Er end; [|discriminate].
  assert (Hy: forall y f', (f <= f')%nat ->
    decode_blocks_w (S f') st hist (s ++ y) out bsm ws =
    if bp_last (block_props_of s) =? 1 then Some (out', 3 + c)
    else match decode_blocks_w f' st' hist (skipn (Z.to_nat (3 + c)) s ++ y) out' bsm ws with
         | Some (o0, k0) => Some (o0, 3 + c + k0) | None => None end).
  { intros y f' Hf. cbn [decode_blocks_w].
    rewrite (cblock_size_app s y H3), Ec. pose proof (Zlength_nonneg y).
    replace (c >? Zlength (s ++ y) - ZSTD_blockHeaderSize) with false
      by (symmetry; apply Zgtb_le; rewrite Zlength_app; unfold ZSTD_blockHeaderSize; lia).
    rewrite (block_props_app s y H3). unfold ZSTD_blockHeaderSize. rewrite Hslice. cbv zeta. rewrite Er.
    rewrite Hrest. auto. }
  destruct (bp_last (block_props_of s) =? 1) eqn:El.
  - assert (k = 3 + c) by congruence. split; [lia|].
    intros y f' Hf. destruct f' as [|f']; [lia|]. rewrite Hy by lia. congruence.
  - destruct (decode_blocks_w f st' hist (skipn (Z.to_nat (3 + c)) s) out' bsm ws) as [[o2 k2]|] eqn:E2;
      [|discriminate].
    assert (k = 3 + c + k2) by congruence. destruct (IHf _ _ _ _ _ _ _ _ E2) as [Hk IH].
    split. { pose proof (g2_zlen_skipn_le s (3 + c) ltac:(lia)). lia. }
    intros y f' Hf. destruct f' as [|f']; [lia|]. rewrite Hy by lia. rewrite IH by lia. congruence.
Qed.

(* the selected block decoder of decode_frame_m (md_dwin, R1) *)
Definition g2_dbsel (b: bool) := if b then decode_blocks_w else decode_blocks.

Lemma g2_dbsel_ext : forall b f st hist s out bsm ws o k,
  g2_dbsel b f st hist s out bsm ws = Some (o, k) ->
  k <= Zlength s /\ forall y f', (f <= f')%nat -> g2_dbsel b f' st hist (s ++ y) out bsm ws = Some (o, k).
Proof. intros [|]; unfold g2_dbsel; [apply g2_dbw_ext|apply g2_db_ext]. Qed.

Lemma g2_db_nonneg : forall f st hist s out bsm ws o k,
  decode_blocks f st hist s out bsm ws = Some (o, k) -> bytes_ok s -> 0 <= k.
Proof.
  induction f; intros st hist s out bsm ws o k H Hs; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_nonneg _ _ Hs Ec).
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [discriminate|]. unfold ZSTD_blockHeaderSize in *.
  cbv zeta in H.
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] end; [|discriminate].
  destruct (bp_last _ =? 1). { assert (k = 3 + c) by congruence. lia. }
  destruct (decode_blocks f st' hist _ out' bsm ws) as [[o2 k2]|] eqn:E2; [|discriminate].
  assert (k = 3 + c + k2) by congruence. pose proof (IHf _ _ _ _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs)). lia.
Qed.

Lemma g2_dbsel_nonneg : forall b f st hist s out bsm ws o k,
  g2_dbsel b f st hist s out bsm ws = Some (o, k) -> bytes_ok s -> 0 <= k.
Proof.
  intros [|]; unfold g2_dbsel; intros; [|eapply g2_db_nonneg; eauto].
  apply decode_blocks_w_lenient in H. eapply g2_db_nonneg; eauto.
Qed.


(* ---------- frame headers ---------- *)

Lemma g2_magic_bytes : magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma g2_gfh_hs : forall s h, get_frame_header s = FH_ok h -> 5 <= fh_headerSize h <= Zlength s.
Proof.
  intros s h G. destruct (gfh_info _ _ G) as [[_ [H8 [_ [_ [Hs _]]]]]|[_ [_ [_ [Hs [Hle _]]]]]].
  - lia.
  - pose proof (fhs_ge5 (byte_at s 4)). lia.
Qed.

Lemma g2_gfhm_hs : forall mg s h, get_frame_header_m mg s = FH_ok h -> 0 <= fh_headerSize h <= Zlength s.
Proof.
  intros mg s h G. unfold get_frame_header_m in G. destruct mg; simpl negb in G.
  - destruct (Zlength s <? 1); [discriminate|].
    destruct (get_frame_header (magic_bytes ++ s)) as [| |h0] eqn:G0; try discriminate.
    inversion G; subst. apply g2_gfh_hs in G0. rewrite Zlength_app in G0.
    rewrite g2_magic_bytes in G0. simpl. change (Zlength [40; 181; 47; 253]) with 4 in G0. lia.
  - apply g2_gfh_hs in G. lia.
Qed.

Lemma g2_gfhm_ext : forall mg s y h, get_frame_header_m mg s = FH_ok h -> bytes_ok s ->
  get_frame_header_m mg (s ++ y) = FH_ok h.
Proof.
  intros mg s y h G Hs. unfold get_frame_header_m in *. destruct mg; simpl negb in *.
  - destruct (Zlength s <? 1) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
    pose proof (Zlength_nonneg y).
    replace (Zlength (s ++ y) <? 1) with false by (symmetry; apply Z.ltb_ge; rewrite Zlength_app; lia).
    destruct (get_frame_header (magic_bytes ++ s)) as [| |h0] eqn:G0; try discriminate.
    rewrite app_assoc, (gfh_ext _ _ _ G0); auto.
    rewrite g2_magic_bytes. unfold byte_at. simpl. apply (bytes_ok_byte_at s 0 Hs).
  - apply gfh_ext; auto. apply bytes_ok_byte_at; auto.
Qed.

Lemma g2_fd_ext : forall mg sel cur s y h, get_frame_header_m mg s = FH_ok h -> bytes_ok s ->
  frame_dict mg sel cur (s ++ y) = frame_dict mg sel cur s.
Proof. intros. unfold frame_dict. rewrite (g2_gfhm_ext _ _ _ _ H H0), H. auto. Qed.

(* ---------- one Zstandard frame: prefix stability ---------- *)

Lemma g2_df_ext : forall md dm wl s c k y, decode_frame_m md dm wl s = FOk c k -> bytes_ok s ->
  0 <= k <= Zlength s /\ decode_frame_m md dm wl (s ++ y) = FOk c k.
Proof.
  intros md dm wl s c k y H Hs.
  unfold decode_frame_m in *.
  set (mg := md_magicless md) in *. set (sh := if mg then 4 else 0) in *.
  assert (Hsh: sh = 0 \/ sh = 4) by (unfold sh; destruct mg; auto).
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN - sh + ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
  apply Z.ltb_ge in E1. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *.
  pose proof (Zlength_nonneg y).
  rewrite Zlength_app.
  replace (Zlength s + Zlength y <? 6 - sh + 3) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (le_field_app s y 0 4) by lia.
  rewrite (byte_at_app s y (4 - sh)) by lia.
  rewrite (byte_at_app s y (5 - sh)) by lia.
  destruct (negb mg && negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [discriminate|].
  destruct (Zlength s <? fhd_header_size (byte_at s (4 - sh)) - sh + 3) eqn:E3; [discriminate|].
  apply Z.ltb_ge in E3.
  replace (Zlength s + Zlength y <? fhd_header_size (byte_at s (4 - sh)) - sh + 3) with false
    by (symmetry; apply Z.ltb_ge; lia).
  destruct (negb (Z.land (byte_at s (4 - sh)) 8 =? 0)); [discriminate|].
  destruct (negb (Z.land (Z.shiftr (byte_at s (4 - sh)) 5) 1 =? 1) &&
            (Z.shiftr (byte_at s (5 - sh)) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX));
    [discriminate|].
  destruct (get_frame_header_m mg s) as [| |h] eqn:G; try discriminate.
  rewrite (g2_gfhm_ext _ _ _ _ G Hs).
  destruct (fh_windowSize h >? wl); [discriminate|].
  destruct (negb (fh_frameType h =? 0)); [discriminate|].
  destruct (negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm)); [discriminate|].
  pose proof (g2_gfhm_hs _ _ _ G) as Hhs.
  rewrite skipn_app_le by (rewrite Zlength_correct in Hhs; lia).
  change (if md_dwin md then decode_blocks_w else decode_blocks) with (g2_dbsel (md_dwin md)) in *.
  destruct (g2_dbsel (md_dwin md) (length (skipn (Z.to_nat (fh_headerSize h)) s)) (dm_state dm) (dm_content dm)
              (skipn (Z.to_nat (fh_headerSize h)) s) nil (Z.min (fh_blockSizeMax h) (md_bmax md))
              (fh_windowSize h)) as [[out kb]|] eqn:D; [|discriminate].
  destruct (g2_dbsel_ext _ _ _ _ _ _ _ _ _ _ D) as [Hkb Hext].
  rewrite Hext by (rewrite length_app; lia).
  rewrite Zlength_skipn in Hkb by lia.
  pose proof (g2_dbsel_nonneg _ _ _ _ _ _ _ _ _ _ D (bytes_ok_skipn _ _ Hs)).
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h));
    [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength s - fh_headerSize h - kb <? 4) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4.
    replace (Zlength s + Zlength y - fh_headerSize h - kb <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite le_field_app_max by lia.
    destruct (negb (md_ignore md) && negb (le_field s (fh_headerSize h + kb) 4 =? Zstd.proof.model.Xxh64.xxh64 out 0 mod 2 ^ 32));
      [discriminate|].
    split; [|auto]. assert (k = fh_headerSize h + kb + 4) by congruence. lia.
  - split; [|auto]. assert (k = fh_headerSize h + kb) by congruence. lia.
Qed.

Lemma g2_df_hdr : forall md dm wl s c k, decode_frame_m md dm wl s = FOk c k ->
  exists h, get_frame_header_m (md_magicless md) s = FH_ok h.
Proof.
  intros md dm wl s c k H. unfold decode_frame_m in H. cbv zeta in H.
  change (if md_dwin md then decode_blocks_w else decode_blocks) with (g2_dbsel (md_dwin md)) in H.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b; [try discriminate|]
  end.
  destruct (get_frame_header_m _ s) as [| |h]; try discriminate. eauto.
Qed.

(* ---------- walks ---------- *)

Definition g2_wfirst (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (wl: Z) (s: list Z)
    : (Z * list Z * bool * option dict_model) + Zstd.proof.model.Series.tail :=
  if Zlength s <? starting_len (md_magicless md) then inr (if Zlength s =? 0 then TEnd else TUnk) else
  if negb (md_magicless md) && is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with None => inr TUnk | Some k => inl (k, nil, true, skip_cd md sel s cur) end
  else
    match frame_dict (md_magicless md) sel cur s with
    | None => inr TUnk
    | Some d =>
        match decode_frame_m md d wl s with
        | FOk c k => inl (k, c, false, Some d)
        | FDetHdr => inr TDetHdr
        | FDetCk => inr TDetCk
        | FUnk => inr TUnk
        end
    end.

Lemma g2_walk_S : forall f md sel cur wl s off, walk_m (S f) md sel cur wl s off =
  match g2_wfirst md sel cur wl s with
  | inr t => (nil, t)
  | inl (k, c, sk, cur') =>
      let '(l, t) := walk_m f md sel cur' wl (skipn (Z.to_nat k) s) (off + k) in (mkrec off k c sk :: l, t)
  end.
Proof.
  intros. unfold g2_wfirst. cbn [walk_m]. cbv zeta.
  destruct (Zlength s <? starting_len (md_magicless md)); auto.
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool; [destruct (skippable_frame_size s); unfold skip_cd; auto|].
  destruct (frame_dict _ _ _ _); auto. destruct (decode_frame_m _ _ _ _); auto.
Qed.

Lemma g2_cur_S : forall f md sel cur wl s, walk_cur (S f) md sel cur wl s =
  match g2_wfirst md sel cur wl s with
  | inr _ => cur
  | inl (k, _, _, cur') => walk_cur f md sel cur' wl (skipn (Z.to_nat k) s)
  end.
Proof.
  intros. unfold g2_wfirst. cbn [walk_cur]. cbv zeta.
  destruct (Zlength s <? starting_len (md_magicless md)); auto.
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool; [destruct (skippable_frame_size s); unfold skip_cd; auto|].
  destruct (frame_dict _ _ _ _); auto. destruct (decode_frame_m _ _ _ _); auto.
Qed.

Lemma g2_wfirst_ext : forall md sel cur wl s k c sk cur' y, g2_wfirst md sel cur wl s = inl (k, c, sk, cur') ->
  bytes_ok s -> 0 <= k <= Zlength s /\ g2_wfirst md sel cur wl (s ++ y) = inl (k, c, sk, cur').
Proof.
  intros md sel cur wl s k c sk cur' y H Hs. unfold g2_wfirst in *.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E0; [discriminate|]. apply Z.ltb_ge in E0.
  assert (1 <= starting_len (md_magicless md) <= 5)
    by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; destruct (md_magicless md); lia).
  pose proof (Zlength_nonneg y).
  rewrite Zlength_app.
  replace (Zlength s + Zlength y <? starting_len (md_magicless md)) with false by (symmetry; apply Z.ltb_ge; lia).
  assert (Hsk: negb (md_magicless md) && is_skippable_magic (le_field (s ++ y) 0 4) =
               negb (md_magicless md) && is_skippable_magic (le_field s 0 4)).
  { unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in E0.
    destruct (md_magicless md); simpl; auto. rewrite le_field_app by lia. auto. }
  rewrite Hsk. destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4)) eqn:Esk.
  - destruct (skippable_frame_size s) as [k'|] eqn:E; [|discriminate].
    assert (Hs4: 4 <= Zlength s).
    { apply andb_prop in Esk. destruct Esk as [Em _]. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in E0.
      destruct (md_magicless md); [discriminate|lia]. }
    assert (Hsc: skip_cd md sel (s ++ y) cur = skip_cd md sel s cur).
    { unfold skip_cd. rewrite le_field_app by lia. reflexivity. }
    rewrite Hsc.
    destruct (sfs_ext _ y _ E) as [-> Hk]. inversion H; subst. split; auto. split; auto.
    unfold skippable_frame_size in E.
    destruct (_ <? _); [discriminate|]. destruct (_ >? _); [discriminate|].
    inversion E. pose proof (le_field_bound s 4 4 Hs ltac:(lia)). unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
  - destruct (frame_dict (md_magicless md) sel cur s) as [d|] eqn:Fd; [|discriminate].
    destruct (decode_frame_m md d wl s) eqn:D; try discriminate. inversion H; subst.
    destruct (g2_df_hdr _ _ _ _ _ _ D) as [h G].
    rewrite (g2_fd_ext _ _ _ _ y _ G Hs), Fd.
    destruct (g2_df_ext _ _ _ _ _ _ y D Hs) as [Hk ->]. auto.
Qed.

Lemma g2_wfirst_end : forall md sel cur wl s, g2_wfirst md sel cur wl s = inr TEnd -> s = nil.
Proof.
  unfold g2_wfirst; intros.
  destruct (Zlength s <? starting_len (md_magicless md)).
  - destruct (Zlength s =? 0) eqn:E; [|discriminate]. apply Z.eqb_eq in E.
    rewrite Zlength_correct in E. destruct s; [auto|simpl in E; lia].
  - destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool; [destruct (skippable_frame_size s); discriminate|].
    destruct (frame_dict _ _ _ _); [|discriminate]. destruct (decode_frame_m _ _ _ _); discriminate.
Qed.

Lemma g2_walk_off : forall f md sel cur wl s off,
  walk_m f md sel cur wl s off =
    (map (fshift off) (fst (walk_m f md sel cur wl s 0)), snd (walk_m f md sel cur wl s 0)).
Proof.
  induction f; intros; [auto|]. rewrite !g2_walk_S.
  destruct (g2_wfirst md sel cur wl s) as [[[[k c] sk] cur']|t]; auto.
  rewrite (IHf _ _ _ _ _ (off + k)), (IHf _ _ _ _ _ (0 + k)). simpl. f_equal. f_equal.
  - unfold fshift, mkrec. simpl. f_equal. lia.
  - rewrite map_map. apply map_ext. intros. unfold fshift. simpl. f_equal. lia.
Qed.

Lemma g2_walk_mono : forall f md sel cur wl s off l t, walk_m f md sel cur wl s off = (l, t) -> t <> TUnk ->
  forall f', (f <= f')%nat ->
  walk_m f' md sel cur wl s off = (l, t) /\ walk_cur f' md sel cur wl s = walk_cur f md sel cur wl s.
Proof.
  induction f; intros md sel cur wl s off l t H Ht f' Hf. { simpl in H. inversion H; subst. congruence. }
  destruct f' as [|f']; [lia|]. rewrite !g2_walk_S in *. rewrite !g2_cur_S.
  destruct (g2_wfirst md sel cur wl s) as [[[[k c] sk] cur']|t0]; auto.
  destruct (walk_m f md sel cur' wl _ _) as [l0 t0] eqn:E. inversion H; subst.
  destruct (IHf _ _ _ _ _ _ _ _ E Ht f' ltac:(lia)) as [-> ->]. auto.
Qed.

Lemma g2_walk_len : forall f md sel cur wl s off l t, walk_m f md sel cur wl s off = (l, t) -> t <> TUnk ->
  (length l < f)%nat.
Proof.
  induction f; intros md sel cur wl s off l t H Ht. { simpl in H. inversion H; subst. congruence. }
  rewrite g2_walk_S in H. destruct (g2_wfirst md sel cur wl s) as [[[[k c] sk] cur']|t0].
  - destruct (walk_m f md sel cur' wl _ _) as [l0 t0] eqn:E. inversion H; subst.
    simpl. specialize (IHf _ _ _ _ _ _ _ _ E Ht). lia.
  - inversion H; subst. simpl. lia.
Qed.

Lemma g2_walk_app : forall f md sel cur wl s off l, walk_m f md sel cur wl s off = (l, TEnd) -> bytes_ok s ->
  forall y F, (length l <= F)%nat ->
  walk_m F md sel cur wl (s ++ y) off =
    (l ++ fst (walk_m (F - length l) md sel (walk_cur f md sel cur wl s) wl y (off + Zlength s)),
     snd (walk_m (F - length l) md sel (walk_cur f md sel cur wl s) wl y (off + Zlength s))) /\
  walk_cur F md sel cur wl (s ++ y) = walk_cur (F - length l) md sel (walk_cur f md sel cur wl s) wl y.
Proof.
  induction f; intros md sel cur wl s off l H Hs y F HF; [discriminate|].
  rewrite g2_walk_S in H. rewrite g2_cur_S.
  destruct (g2_wfirst md sel cur wl s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' wl (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    destruct (g2_wfirst_ext _ _ _ _ _ _ _ _ _ y E Hs) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite g2_walk_S, g2_cur_S, Hext.
    rewrite skipn_app_le by (rewrite Zlength_correct in Hkl; lia).
    destruct (IHf _ _ _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F ltac:(lia)) as [W C].
    rewrite W, C.
    rewrite Zlength_skipn by lia.
    replace (off + k + (Zlength s - k)) with (off + Zlength s) by lia.
    simpl. auto.
  - inversion H; subst; clear H. apply g2_wfirst_end in E. subst s.
    simpl. rewrite Nat.sub_0_r, Z.add_0_r. destruct (walk_m F _ _ _ _ _ _); auto.
Qed.

(* the series dsin (complete, recs) followed by a complete series y read from the dictionary current after dsin *)
Lemma g2_series_app : forall md sel cur dsin recs y l,
  bytes_ok dsin -> bytes_ok y ->
  series_frames_m md sel cur no_wlim dsin = (recs, TEnd) ->
  series_frames_m md sel (series_cur md sel cur no_wlim dsin) no_wlim y = (l, TEnd) ->
  series_frames_m md sel cur no_wlim (dsin ++ y) = (recs ++ map (fshift (Zlength dsin)) l, TEnd) /\
  series_cur md sel cur no_wlim (dsin ++ y) = series_cur md sel (series_cur md sel cur no_wlim dsin) no_wlim y.
Proof.
  unfold series_frames_m, series_cur. intros md sel cur dsin recs y l Hd Hy H1 H2.
  pose proof (g2_walk_len _ _ _ _ _ _ _ _ _ H1 ltac:(discriminate)) as HL.
  destruct (g2_walk_app _ _ _ _ _ _ _ _ H1 Hd y (S (length (dsin ++ y)))) as [W C];
    [rewrite length_app; lia|].
  rewrite W, C. rewrite g2_walk_off.
  destruct (g2_walk_mono _ _ _ _ _ _ _ _ _ H2 ltac:(discriminate) (S (length (dsin ++ y)) - length recs))
    as [M1 M2]; [rewrite length_app; lia|].
  rewrite M1, M2. simpl. auto.
Qed.
