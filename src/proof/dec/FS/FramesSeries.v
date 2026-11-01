(* FS one-shot frames: the model facts of a series (ZSTD_decompressMultiFrame's body).
   Plain Coq over model/Series.v. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Block Zstd.proof.model.Xxh64
  Zstd.proof.model.Series.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- the series (ZSTD_decompressMultiFrame's loop) ---------- *)

(* the outcome of the series after the content c already delivered *)
Definition sres_prepend (c: list Z) (r: sres) : sres :=
  match r with SOk c' => SOk (c ++ c') | _ => r end.

(* ---------- helpers: the walk's outcome does not depend on the fuel (beyond length s) ---------- *)

Definition wres (p: list frec * tail) : sres :=
  match p with
  | (l, TEnd) => SOk (flat_map fr_content l)
  | (_, TDetHdr) => SDet
  | (_, TDetCk) => SDet
  | (_, TUnk) => SUnk
  end.

Lemma decode_series_wres: forall dm wlim s, decode_series dm wlim s = wres (series_frames dm wlim s).
Proof. intros. unfold decode_series. destruct (series_frames dm wlim s) as [l []]; reflexivity. Qed.

Lemma walk_step: forall n dm wlim s off,
  wres (walk (S n) dm wlim s off) =
  if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (if Zlength s =? 0 then SOk nil else SUnk) else
  if is_skippable_magic (le_field s 0 4) then
    match skippable_frame_size s with
    | None => SUnk
    | Some k => wres (walk n dm wlim (skipn (Z.to_nat k) s) (off + k))
    end
  else
    match decode_frame dm wlim s with
    | FOk c k => sres_prepend c (wres (walk n dm wlim (skipn (Z.to_nat k) s) (off + k)))
    | FDetHdr | FDetCk => SDet
    | FUnk => SUnk
    end.
Proof.
  intros. cbn [walk].
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [destruct (Zlength s =? 0); reflexivity|].
  destruct (is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s); [|reflexivity].
    destruct (walk n dm wlim _ _) as [l []]; reflexivity.
  - destruct (decode_frame dm wlim s); try reflexivity.
    destruct (walk n dm wlim _ _) as [l []]; reflexivity.
Qed.

Lemma walk_loop_skip: forall dm wlim s k,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k -> Z.to_nat k = 0%nat ->
  forall n off, wres (walk n dm wlim s off) = SUnk.
Proof.
  intros dm wlim s k H1 H2 H3 H4 n. induction n; intros off; [reflexivity|].
  rewrite walk_step. destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3, H4. apply IHn.
Qed.

Lemma walk_loop_frame: forall dm wlim s c k,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = false ->
  decode_frame dm wlim s = FOk c k -> Z.to_nat k = 0%nat ->
  forall n off, wres (walk n dm wlim s off) = SUnk.
Proof.
  intros dm wlim s c k H1 H2 H3 H4 n. induction n; intros off; [reflexivity|].
  rewrite walk_step. destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3, H4. simpl skipn. rewrite IHn. reflexivity.
Qed.

Lemma skipn_shorter: forall (s: list Z) k,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s -> Z.to_nat k <> 0%nat ->
  (length (skipn (Z.to_nat k) s) < length s)%nat.
Proof.
  intros. rewrite skipn_length. rewrite Zlength_correct in H.
  unfold ZSTD_FRAMEHEADERSIZE_PREFIX in H. lia.
Qed.

Lemma walk_fuel: forall n dm wlim s off m off',
  (length s < n)%nat -> (length s < m)%nat ->
  wres (walk n dm wlim s off) = wres (walk m dm wlim s off').
Proof.
  induction n; intros dm wlim s off m off' Hn Hm; [lia|].
  destruct m as [|m]; [lia|].
  rewrite !walk_step.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E.
  destruct (is_skippable_magic (le_field s 0 4)) eqn:Es.
  - destruct (skippable_frame_size s) as [k|] eqn:Ek; [|reflexivity].
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn. rewrite !(walk_loop_skip dm wlim s k); auto.
    + pose proof (skipn_shorter s k E Hk). apply IHn; lia.
  - destruct (decode_frame dm wlim s) as [c k| | |] eqn:Ef; try reflexivity.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn.
      rewrite !(walk_loop_frame dm wlim s c k); auto.
    + pose proof (skipn_shorter s k E Hk). f_equal. apply IHn; lia.
Qed.

Lemma walk_series: forall n dm wlim s off,
  (length s < n)%nat -> wres (walk n dm wlim s off) = decode_series dm wlim s.
Proof.
  intros. rewrite decode_series_wres. unfold series_frames. apply walk_fuel; lia.
Qed.

(* ---------- helpers: sizes (byte strings) ---------- *)

Lemma Forall_skipn_Z: forall (P: Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros P n. induction n; intros l H; [exact H|]. destruct l; [constructor|]. simpl.
  inversion H; subst. auto.
Qed.

Lemma Forall_firstn_Z: forall (P: Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n. induction n; intros l H; [constructor|]. destruct l; [constructor|]. simpl.
  inversion H; subst. constructor; auto.
Qed.

Lemma le_value_nonneg: forall l, bytes_ok l -> 0 <= le_value l.
Proof.
  induction l; intros H; cbn [le_value]; [lia|]. inversion H; subst.
  specialize (IHl H3). unfold is_byte in *. lia.
Qed.

Lemma le_field_nonneg: forall s i k, bytes_ok s -> 0 <= le_field s i k.
Proof.
  intros. apply le_value_nonneg. unfold slice. apply Forall_firstn_Z, Forall_skipn_Z. exact H.
Qed.

Lemma Zlength_skipn_le: forall (s: list Z) k, 0 <= k <= Zlength s ->
  Zlength (skipn (Z.to_nat k) s) = Zlength s - k.
Proof.
  intros. rewrite !Zlength_correct in *. rewrite skipn_length. lia.
Qed.

Lemma cblock_size_nonneg: forall s c, bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  unfold cblock_size. intros s c Hb H.
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type (block_props_of s) =? 1); [inversion H; lia|].
  destruct (bp_type (block_props_of s) =? 3); [discriminate|]. inversion H; subst.
  unfold block_props_of; simpl. apply Z.shiftr_nonneg. apply le_field_nonneg; auto.
Qed.

Lemma decode_blocks_size: forall fuel st hist s out bsm wsize o k,
  bytes_ok s -> decode_blocks fuel st hist s out bsm wsize = Some (o, k) ->
  ZSTD_blockHeaderSize <= k <= Zlength s.
Proof.
  induction fuel; intros st hist s out bsm wsize o k Hb H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_size_nonneg s c Hb Ec).
  destruct (c >? Zlength s - ZSTD_blockHeaderSize) eqn:Ecl; [discriminate|]. rewrite Z.gtb_ltb in Ecl; apply Z.ltb_ge in Ecl.
  destruct (if bp_type _ =? 0 then _ else _) as [[st' out']|]; [|discriminate].
  destruct (bp_last (block_props_of s) =? 1).
  - assert (k = ZSTD_blockHeaderSize + c) by congruence. subst k. unfold ZSTD_blockHeaderSize in *. lia.
  - destruct (decode_blocks fuel _ _ _ _ _ _) as [[o' k']|] eqn:Er; [|discriminate].
    assert (k = ZSTD_blockHeaderSize + c + k') by congruence. subst k.
    apply IHfuel in Er; [|apply Forall_skipn_Z; exact Hb].
    rewrite Zlength_skipn_le in Er; unfold ZSTD_blockHeaderSize in *; lia.
Qed.

Lemma nth_hdr_nonneg: forall i (l: list Z), Forall (fun x => 0 <= x) l -> 0 <= nth i l 0.
Proof.
  intros i l H. revert i. induction H; intros [|i]; simpl; auto; lia.
Qed.

Lemma fhd_header_size_pos: forall fhd, 5 <= fhd_header_size fhd.
Proof.
  intros. unfold fhd_header_size.
  assert (0 <= Z.land (Z.shiftr fhd 5) 1 <= 1).
  { replace (Z.land (Z.shiftr fhd 5) 1) with (Z.land (Z.shiftr fhd 5) (Z.ones 1)) by reflexivity.
    rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) (2 ^ 1) ltac:(lia)). simpl in *. lia. }
  pose proof (nth_hdr_nonneg (Z.to_nat (Z.land fhd 3)) [0;1;2;4] ltac:(repeat constructor; lia)).
  pose proof (nth_hdr_nonneg (Z.to_nat (Z.shiftr fhd 6)) [0;2;4;8] ltac:(repeat constructor; lia)).
  destruct (_ && _); lia.
Qed.

Lemma get_frame_header_hs: forall s h,
  le_field s 0 4 = ZSTD_MAGICNUMBER -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  get_frame_header s = FH_ok h -> fh_headerSize h = fhd_header_size (byte_at s 4).
Proof.
  intros s h Hm Hl H. unfold get_frame_header in H.
  destruct (Zlength s <? 5) eqn:E; [apply Z.ltb_lt in E; unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hl; lia|].
  rewrite Hm, Z.eqb_refl in H. simpl negb in H. cbv iota in H.
  destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  destruct (_ && _); [discriminate|].
  inversion H; subst. reflexivity.
Qed.

Lemma decode_frame_size_ok: forall dm wlim s c k,
  bytes_ok s -> decode_frame dm wlim s = FOk c k -> 0 < k <= Zlength s.
Proof.
  intros dm wlim s c k Hb H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
  apply Z.ltb_ge in E1.
  destruct (le_field s 0 4 =? ZSTD_MAGICNUMBER) eqn:Em; [|discriminate]. apply Z.eqb_eq in Em.
  simpl negb in H; cbv iota in H.
  destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) eqn:E2; [discriminate|].
  apply Z.ltb_ge in E2.
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  destruct (_ && _); [discriminate|].
  destruct (get_frame_header s) as [|?|h] eqn:Eh; try discriminate.
  apply get_frame_header_hs in Eh; [|exact Em|unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize, ZSTD_FRAMEHEADERSIZE_PREFIX in *; lia].
  pose proof (fhd_header_size_pos (byte_at s 4)).
  destruct (fh_windowSize h >? wlim); [discriminate|].
  destruct (negb (fh_frameType h =? 0)); [discriminate|].
  destruct (_ && _); [discriminate|].
  destruct (decode_blocks _ _ _ _ _ _ _) as [[out k']|] eqn:Eb; [|discriminate].
  apply decode_blocks_size in Eb; [|apply Forall_skipn_Z; exact Hb].
  rewrite Zlength_skipn_le in Eb by (unfold ZSTD_blockHeaderSize in *; lia).
  rewrite Eh in *.
  destruct (_ && _); [discriminate|].
  destruct (fh_checksumFlag h =? 1).
  - destruct (Zlength s - _ - k' <? 4) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
    destruct (negb _); [discriminate|].
    assert (k = fhd_header_size (byte_at s 4) + k' + 4) by congruence. subst k. unfold ZSTD_blockHeaderSize in *. lia.
  - assert (k = fhd_header_size (byte_at s 4) + k') by congruence. subst k. unfold ZSTD_blockHeaderSize in *. lia.
Qed.

Lemma skippable_frame_size_bound_ok: forall s k,
  bytes_ok s -> skippable_frame_size s = Some k -> ZSTD_SKIPPABLEHEADERSIZE <= k <= Zlength s.
Proof.
  intros s k Hb H. unfold skippable_frame_size in H.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  destruct (le_field s 4 4 + ZSTD_SKIPPABLEHEADERSIZE >? Zlength s) eqn:E; [discriminate|].
  rewrite Z.gtb_ltb in E; apply Z.ltb_ge in E. inversion H; subst.
  pose proof (le_field_nonneg s 4 4 Hb). lia.
Qed.

Lemma decode_series_short: forall dm wlim s,
  Zlength s < ZSTD_FRAMEHEADERSIZE_PREFIX ->
  decode_series dm wlim s = if Zlength s =? 0 then SOk nil else SUnk.
Proof.
  intros. rewrite <- (walk_series (S (length s)) dm wlim s 0) by lia. rewrite walk_step.
  apply Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma decode_series_skip: forall dm wlim s k,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k ->
  decode_series dm wlim s = decode_series dm wlim (skipn (Z.to_nat k) s).
Proof.
  intros dm wlim s k H1 H2 H3.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk]; [rewrite Hk; reflexivity|].
  rewrite <- (walk_series (S (length s)) dm wlim s 0) by lia. rewrite walk_step.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3. apply walk_series. pose proof (skipn_shorter s k H1 Hk). lia.
Qed.

Lemma decode_series_skip_bad: forall dm wlim s,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = None ->
  decode_series dm wlim s = SUnk.
Proof.
  intros dm wlim s H1 H2 H3.
  rewrite <- (walk_series (S (length s)) dm wlim s 0) by lia. rewrite walk_step.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3. reflexivity.
Qed.

Lemma decode_series_frame: forall dm wlim s,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = false ->
  decode_series dm wlim s =
    match decode_frame dm wlim s with
    | FOk c k => sres_prepend c (decode_series dm wlim (skipn (Z.to_nat k) s))
    | FDetHdr | FDetCk => SDet
    | FUnk => SUnk
    end.
Proof.
  intros dm wlim s H1 H2.
  rewrite <- (walk_series (S (length s)) dm wlim s 0) by lia. rewrite walk_step.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2. destruct (decode_frame dm wlim s) as [c k| | |] eqn:Ef; try reflexivity.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
  - rewrite Hk. simpl skipn. rewrite (walk_loop_frame dm wlim s c k) by auto.
    rewrite <- (walk_series (S (length s)) dm wlim s 0) by lia.
    rewrite (walk_loop_frame dm wlim s c k) by auto. reflexivity.
  - f_equal. apply walk_series. pose proof (skipn_shorter s k H1 Hk). lia.
Qed.

(* a frame decoded by the model takes bytes of s *)
Lemma decode_frame_size: forall dm wlim s c k,
  bytes_ok s ->
  decode_frame dm wlim s = FOk c k -> 0 < k <= Zlength s.
Proof.
  exact decode_frame_size_ok.
Qed.

Lemma skippable_frame_size_bound: forall s k,
  bytes_ok s ->
  skippable_frame_size s = Some k -> ZSTD_SKIPPABLEHEADERSIZE <= k <= Zlength s.
Proof.
  exact skippable_frame_size_bound_ok.
Qed.

(* ---------- dictionaries ---------- *)

(* the content of a dictionary is the tail of its bytes (zstd's history is the whole buffer or the
   content: both end with the content) *)
Lemma dict_auto_suffix: forall b dm,
  dict_auto b = Some dm -> exists pre, b = pre ++ dm_content dm.
Proof.
  unfold dict_auto. intros b dm H.
  destruct (Zlength b <? 8); [inversion H; subst; exists nil; reflexivity|].
  destruct (negb _); [inversion H; subst; exists nil; reflexivity|].
  destruct (load_dentropy b) as [[st esize]|]; [|discriminate].
  inversion H; subst. exists (firstn (Z.to_nat esize) b). simpl. symmetry. apply firstn_skipn.
Qed.

(* all the lemmas above (the target of this file: its assumptions are theirs) *)
Lemma frames_series_all : True.
Proof.
  pose proof decode_series_short. pose proof decode_series_skip. pose proof decode_series_skip_bad.
  pose proof decode_series_frame. pose proof decode_frame_size. pose proof skippable_frame_size_bound.
  pose proof dict_auto_suffix. exact I.
Qed.
