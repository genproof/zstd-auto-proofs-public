(* FS3 one-shot frames: the model facts of a SERIES under the decoding mode md (Params.decode_series_m without
   the selection), one step of ZSTD_decompressMultiFrame's loop.  Plain Coq; the v2
   analogues (zstd1, default mode) are in FramesSeries.v.  Target of this file: frames3_series_all. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Pure.
Local Open Scope Z_scope.

Section CM_Frames3Series_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers: walk_m with no selection and a known dictionary ---------- *)

Lemma frame_dict3_none: forall mg dm s, frame_dict mg sel_none (Some dm) s = Some dm.
Proof. intros. unfold frame_dict, sel_none. destruct (get_frame_header_m mg s); reflexivity. Qed.

Lemma walk3_step: forall n md dm wlim s off,
  wres (walk_m (S n) md sel_none (Some dm) wlim s off) =
  if Zlength s <? starting_len (md_magicless md) then (if Zlength s =? 0 then SOk nil else SUnk) else
  if (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool then
    match skippable_frame_size s with
    | None => SUnk
    | Some k => wres (walk_m n md sel_none (Some dm) wlim (skipn (Z.to_nat k) s) (off + k))
    end
  else
    match decode_frame_m md dm wlim s with
    | FOk c k => sres_prepend c (wres (walk_m n md sel_none (Some dm) wlim (skipn (Z.to_nat k) s) (off + k)))
    | FDetHdr | FDetCk => SDet
    | FUnk => SUnk
    end.
Proof.
  intros. cbn [walk_m]. rewrite frame_dict3_none.
  assert (Hc: forall b: bool, (if b then match sel_none (Z.land (le_field s 0 4) 15) with Some d0 => Some d0 | None => Some dm end
                         else Some dm) = @Some dict_model dm) by (intros []; reflexivity).
  rewrite Hc.
  destruct (Zlength s <? starting_len (md_magicless md)); [destruct (Zlength s =? 0); reflexivity|].
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool).
  - destruct (skippable_frame_size s); [|reflexivity].
    destruct (walk_m n md sel_none (Some dm) wlim _ _) as [l []]; reflexivity.
  - destruct (decode_frame_m md dm wlim s); try reflexivity.
    destruct (walk_m n md sel_none (Some dm) wlim _ _) as [l []]; reflexivity.
Qed.

Lemma starting_len_pos: forall mg, 1 <= starting_len mg.
Proof. intros []; unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; lia. Qed.

Lemma skipn3_shorter: forall mg (s: list Z) k,
  starting_len mg <= Zlength s -> Z.to_nat k <> 0%nat ->
  (length (skipn (Z.to_nat k) s) < length s)%nat.
Proof.
  intros. pose proof (starting_len_pos mg). rewrite skipn_length. rewrite Zlength_correct in H. lia.
Qed.

Lemma walk3_loop_skip: forall md dm wlim s k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = true ->
  skippable_frame_size s = Some k -> Z.to_nat k = 0%nat ->
  forall n off, wres (walk_m n md sel_none (Some dm) wlim s off) = SUnk.
Proof.
  intros md dm wlim s k H1 H2 H3 H4 n. induction n; intros off; [reflexivity|].
  rewrite walk3_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3, H4. apply IHn.
Qed.

Lemma walk3_loop_frame: forall md dm wlim s c k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false ->
  decode_frame_m md dm wlim s = FOk c k -> Z.to_nat k = 0%nat ->
  forall n off, wres (walk_m n md sel_none (Some dm) wlim s off) = SUnk.
Proof.
  intros md dm wlim s c k H1 H2 H3 H4 n. induction n; intros off; [reflexivity|].
  rewrite walk3_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3, H4. simpl skipn. rewrite IHn. reflexivity.
Qed.

Lemma walk3_fuel: forall n md dm wlim s off m off',
  (length s < n)%nat -> (length s < m)%nat ->
  wres (walk_m n md sel_none (Some dm) wlim s off) = wres (walk_m m md sel_none (Some dm) wlim s off').
Proof.
  induction n; intros md dm wlim s off m off' Hn Hm; [lia|].
  destruct m as [|m]; [lia|].
  rewrite !walk3_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E.
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool) eqn:Es.
  - destruct (skippable_frame_size s) as [k|] eqn:Ek; [|reflexivity].
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn. rewrite !(walk3_loop_skip md dm wlim s k); auto.
    + pose proof (skipn3_shorter _ s k E Hk). apply IHn; lia.
  - destruct (decode_frame_m md dm wlim s) as [c k| | |] eqn:Ef; try reflexivity.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn.
      rewrite !(walk3_loop_frame md dm wlim s c k); auto.
    + pose proof (skipn3_shorter _ s k E Hk). f_equal. apply IHn; lia.
Qed.

Lemma decode_series3_wres: forall md dm wlim s,
  decode_series_m md sel_none (Some dm) wlim s = wres (series_frames_m md sel_none (Some dm) wlim s).
Proof. intros. unfold decode_series_m. destruct (series_frames_m md sel_none (Some dm) wlim s) as [l []]; reflexivity. Qed.

Lemma walk3_series: forall n md dm wlim s off,
  (length s < n)%nat -> wres (walk_m n md sel_none (Some dm) wlim s off) = decode_series_m md sel_none (Some dm) wlim s.
Proof.
  intros. rewrite decode_series3_wres. unfold series_frames_m. apply walk3_fuel; lia.
Qed.

(* fewer bytes than ZSTD_startingInputLength(format): the loop ends *)
Lemma decode_series3_short: forall md dm wlim s,
  Zlength s < starting_len (md_magicless md) ->
  decode_series_m md sel_none (Some dm) wlim s = if Zlength s =? 0 then SOk nil else SUnk.
Proof.
  intros. rewrite <- (walk3_series (S (length s)) md dm wlim s 0) by lia. rewrite walk3_step.
  apply Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

(* a skippable frame (zstd1 only) *)
Lemma decode_series3_skip: forall md dm wlim s k,
  md_magicless md = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k ->
  decode_series_m md sel_none (Some dm) wlim s = decode_series_m md sel_none (Some dm) wlim (skipn (Z.to_nat k) s).
Proof.
  intros md dm wlim s k H0 H1 H2 H3.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk]; [rewrite Hk; reflexivity|].
  assert (H1': starting_len (md_magicless md) <= Zlength s) by (rewrite H0; exact H1).
  rewrite <- (walk3_series (S (length s)) md dm wlim s 0) by lia. rewrite walk3_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H0, H2. cbn [negb andb]. rewrite H3. apply walk3_series. pose proof (skipn3_shorter _ s k H1' Hk). lia.
Qed.

Lemma decode_series3_skip_bad: forall md dm wlim s,
  md_magicless md = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = None ->
  decode_series_m md sel_none (Some dm) wlim s = SUnk.
Proof.
  intros md dm wlim s H0 H1 H2 H3.
  assert (H1': starting_len (md_magicless md) <= Zlength s) by (rewrite H0; exact H1).
  rewrite <- (walk3_series (S (length s)) md dm wlim s 0) by lia. rewrite walk3_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H0, H2. cbn [negb andb]. rewrite H3. reflexivity.
Qed.

(* a Zstandard frame: the series is the frame's content followed by the series of the rest *)
Lemma decode_series3_frame: forall md dm wlim s,
  starting_len (md_magicless md) <= Zlength s ->
  (md_magicless md = true \/ is_skippable_magic (le_field s 0 4) = false) ->
  decode_series_m md sel_none (Some dm) wlim s =
    match decode_frame_m md dm wlim s with
    | FOk c k => sres_prepend c (decode_series_m md sel_none (Some dm) wlim (skipn (Z.to_nat k) s))
    | FDetHdr | FDetCk => SDet
    | FUnk => SUnk
    end.
Proof.
  intros md dm wlim s H1 H2.
  assert (H2': (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false)
    by (destruct H2 as [-> | ->]; [reflexivity | destruct (negb _); reflexivity]).
  rewrite <- (walk3_series (S (length s)) md dm wlim s 0) by lia. rewrite walk3_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2'. destruct (decode_frame_m md dm wlim s) as [c k| | |] eqn:Ef; try reflexivity.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
  - rewrite Hk. simpl skipn. rewrite (walk3_loop_frame md dm wlim s c k) by auto.
    rewrite <- (walk3_series (S (length s)) md dm wlim s 0) by lia.
    rewrite (walk3_loop_frame md dm wlim s c k) by auto. reflexivity.
  - f_equal. apply walk3_series. pose proof (skipn3_shorter _ s k H1 Hk). lia.
Qed.

(* ---------- helpers: header sizes ---------- *)

Lemma magic_bytes_eq: magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma magic_le_field: forall s, le_field (magic_bytes ++ s) 0 4 = ZSTD_MAGICNUMBER.
Proof. intros. rewrite magic_bytes_eq. reflexivity. Qed.

Lemma magic_byte_at: forall s i, 0 <= i -> byte_at (magic_bytes ++ s) (i + 4) = byte_at s i.
Proof.
  intros. rewrite magic_bytes_eq. unfold byte_at. rewrite Z2Nat.inj_add by lia. 
  replace (Z.to_nat i + Z.to_nat 4)%nat with (S (S (S (S (Z.to_nat i))))) by lia. reflexivity.
Qed.

Lemma magic_Zlength: forall s, Zlength (magic_bytes ++ s) = Zlength s + 4.
Proof. intros. rewrite Zlength_app, magic_bytes_eq. change (Zlength [40; 181; 47; 253]) with 4. lia. Qed.

Lemma gfhm_hs: forall mg s h,
  (mg = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) -> starting_len mg <= Zlength s ->
  get_frame_header_m mg s = FH_ok h ->
  fh_headerSize h = header_size_m mg s.
Proof.
  intros [] s h Hm Hl H; unfold get_frame_header_m, header_size_m in *; cbn [negb] in H.
  - destruct (Zlength s <? 1) eqn:E; [discriminate|].
    destruct (get_frame_header (magic_bytes ++ s)) as [| |h0] eqn:E0; try discriminate.
    inversion H; subst. apply get_frame_header_hs in E0;
      [| apply magic_le_field | rewrite magic_Zlength; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; unfold starting_len in Hl; lia].
    cbn [fh_unshift fh_headerSize]. rewrite E0. rewrite <- (magic_byte_at s 0) by lia. reflexivity.
  - apply get_frame_header_hs; auto.
Qed.

Lemma decode_frame3_size_ok: forall md dm wlim s c k,
  md_dwin md = false -> bytes_ok s ->
  decode_frame_m md dm wlim s = FOk c k -> 0 < k <= Zlength s.
Proof.
  intros md dm wlim s c k Hdw Hb H. unfold decode_frame_m in H. rewrite Hdw in H. cbv zeta in H.
  destruct (Zlength s <? _ - _ + ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
  apply Z.ltb_ge in E1.
  destruct (negb (md_magicless md) && negb (le_field s 0 4 =? ZSTD_MAGICNUMBER))%bool eqn:Em; [discriminate|].
  destruct (Zlength s <? fhd_header_size _ - _ + ZSTD_blockHeaderSize) eqn:E2; [discriminate|].
  apply Z.ltb_ge in E2.
  destruct (negb (Z.land _ 8 =? 0)); [discriminate|].
  destruct (negb (Z.land (Z.shiftr _ 5) 1 =? 1) && _)%bool; [discriminate|].
  destruct (get_frame_header_m _ s) as [|?|h] eqn:Eh; try discriminate.
  assert (Hhs: fh_headerSize h = header_size_m (md_magicless md) s /\ 1 <= header_size_m (md_magicless md) s /\
               header_size_m (md_magicless md) s + ZSTD_blockHeaderSize <= Zlength s).
  { split.
    - apply gfhm_hs in Eh; auto.
      + intros Hf. rewrite Hf in Em. cbn [negb andb] in Em. destruct (le_field s 0 4 =? ZSTD_MAGICNUMBER) eqn:X;
          [apply Z.eqb_eq in X; exact X | discriminate].
      + destruct (md_magicless md); unfold starting_len, ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_FRAMEHEADERSIZE_PREFIX,
          ZSTD_blockHeaderSize in *; lia.
    - unfold header_size_m. destruct (md_magicless md); rewrite ?Z.sub_diag, ?Z.sub_0_r in E2;
        [pose proof (fhd_header_size_pos (byte_at s 0)) | pose proof (fhd_header_size_pos (byte_at s 4))];
        unfold ZSTD_blockHeaderSize in *; lia. }
  destruct Hhs as (Hhs & Hhs1 & Hhs2). rewrite Hhs in H.
  destruct (fh_windowSize h >? wlim); [discriminate|].
  destruct (negb (fh_frameType h =? 0)); [discriminate|].
  destruct (negb (fh_dictID h =? 0) && _)%bool; [discriminate|].
  destruct (decode_blocks _ _ _ _ _ _ _) as [[out k']|] eqn:Eb; [|discriminate].
  apply decode_blocks_size in Eb; [|apply Forall_skipn_Z; exact Hb].
  rewrite Zlength_skipn_le in Eb by (unfold ZSTD_blockHeaderSize in *; lia).
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && _)%bool; [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength s - _ - k' <? 4) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
    destruct (negb (md_ignore md) && _)%bool; [discriminate|].
    assert (k = header_size_m (md_magicless md) s + k' + 4) by congruence. subst k. unfold ZSTD_blockHeaderSize in *. lia.
  - assert (k = header_size_m (md_magicless md) s + k') by congruence. subst k. unfold ZSTD_blockHeaderSize in *. lia.
Qed.

(* a frame decoded by the model takes bytes of s *)
Lemma decode_frame3_size: forall md dm wlim s c k,
  md_dwin md = false -> bytes_ok s ->
  decode_frame_m md dm wlim s = FOk c k -> 0 < k <= Zlength s.
Proof.
  exact decode_frame3_size_ok.
Qed.

Lemma sublist0_firstn: forall (s: list Z) n, sublist 0 n s = firstn (Z.to_nat n) s.
Proof. intros. unfold sublist. replace (n - 0) with n by lia. reflexivity. Qed.

Lemma gfh_not_magic: forall s,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  le_field s 0 4 <> ZSTD_MAGICNUMBER -> is_skippable_magic (le_field s 0 4) = false ->
  get_frame_header s = FH_err.
Proof.
  intros s Hl Hm Hs. unfold get_frame_header. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl.
  destruct (Z.ltb_spec (Zlength s) 5); [lia|].
  destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER); [contradiction|]. cbn [negb]. rewrite Hs. reflexivity.
Qed.

(* a skippable magic number: the header is not a Zstandard frame's *)
Lemma gfh_skip_type: forall s h, is_skippable_magic (le_field s 0 4) = true ->
  get_frame_header_m false s = FH_ok h -> fh_frameType h <> 0.
Proof.
  intros s h Hm H. unfold get_frame_header_m in H. cbn [negb] in H. unfold get_frame_header in H.
  destruct (Zlength s <? 5); [destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; discriminate|].
  replace (le_field s 0 4 =? ZSTD_MAGICNUMBER) with false in H.
  2:{ symmetry. apply Z.eqb_neq. intro E. rewrite E in Hm. discriminate. }
  cbn [negb] in H. rewrite Hm in H. destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  inversion H; subst. simpl. discriminate.
Qed.

(* the header ZSTD_decompressMultiFrame reads (ZSTD_getFrameHeader_advanced on all of s) is the one
   ZSTD_decodeFrameHeader reads (its header bytes), for a frame that is not skippable *)
Lemma gfh3_prefix: forall mg s,
  bytes_ok s -> starting_len mg <= Zlength s ->
  (mg = true \/ is_skippable_magic (le_field s 0 4) = false) ->
  get_frame_header_m mg (sublist 0 (header_size_m mg s) s) = get_frame_header_m mg s \/
  ((forall h, get_frame_header_m mg (sublist 0 (header_size_m mg s) s) <> FH_ok h) /\
   (forall h, get_frame_header_m mg s <> FH_ok h)).
Proof.
  intros mg s Hb Hl Hns.
  destruct (Z_le_gt_dec (Zlength s) (header_size_m mg s)) as [Hle|Hgt].
  { left. rewrite sublist0_firstn. rewrite firstn_all2; [reflexivity|]. rewrite Zlength_correct in Hle. lia. }
  rewrite sublist0_firstn. destruct mg.
  - left. pose proof (fh_hs_range _ (fh_byte_at_bound s 0 Hb)) as Hr.
    unfold header_size_m in *. unfold starting_len in Hl.
    unfold get_frame_header_m. cbn [negb].
    rewrite fh_Zlength_firstn by lia.
    destruct (Z.ltb_spec (fhd_header_size (byte_at s 0) - 4) 1); [lia|].
    destruct (Z.ltb_spec (Zlength s) 1); [lia|].
    replace (magic_bytes ++ firstn (Z.to_nat (fhd_header_size (byte_at s 0) - 4)) s)
      with (firstn (Z.to_nat (fhd_header_size (byte_at (magic_bytes ++ s) 4))) (magic_bytes ++ s)).
    2:{ rewrite (magic_byte_at s 0 ltac:(lia) : byte_at (magic_bytes ++ s) 4 = byte_at s 0). rewrite magic_bytes_eq.
        replace (Z.to_nat (fhd_header_size (byte_at s 0)))
          with (S (S (S (S (Z.to_nat (fhd_header_size (byte_at s 0) - 4)))))) by lia. reflexivity. }
    rewrite fh_gfh_prefix; [reflexivity | | | apply magic_le_field | ].
    + rewrite (magic_byte_at s 0 ltac:(lia) : byte_at (magic_bytes ++ s) 4 = byte_at s 0). apply fh_byte_at_bound; exact Hb.
    + rewrite magic_Zlength. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia.
    + rewrite (magic_byte_at s 0 ltac:(lia) : byte_at (magic_bytes ++ s) 4 = byte_at s 0), magic_Zlength. lia.
  - pose proof (fh_hs_range _ (fh_byte_at_bound s 4 Hb)) as Hr.
    unfold header_size_m in *. unfold starting_len in Hl. unfold get_frame_header_m. cbn [negb].
    destruct Hns as [Hns|Hns]; [discriminate|].
    destruct (Z.eq_dec (le_field s 0 4) ZSTD_MAGICNUMBER) as [Hm|Hm].
    + left. apply fh_gfh_prefix; auto; [apply fh_byte_at_bound; exact Hb | lia].
    + right. rewrite (gfh_not_magic s) by auto. rewrite (gfh_not_magic (firstn _ s)).
      * split; intros h; discriminate.
      * rewrite fh_Zlength_firstn by lia. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia.
      * rewrite fh_le_field_firstn by lia. exact Hm.
      * rewrite fh_le_field_firstn by lia. exact Hns.
Qed.

(* all the lemmas above (the target of this file: its assumptions are theirs) *)
Lemma frames3_series_all : True.
Proof.
  pose proof decode_series3_short. pose proof decode_series3_skip. pose proof decode_series3_skip_bad.
  pose proof decode_series3_frame. pose proof decode_frame3_size. pose proof gfh3_prefix. exact I.
Qed.

End CM_Frames3Series_1.
