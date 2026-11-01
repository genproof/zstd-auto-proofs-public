(* Decoding a written series (plain Coq): what the model's walk over the bytes of a
   series ws with series_facts gives, for the harness mains (valid_oneshot, valid_dict(_copy), valid_stream,
   stable_out, detect).  From WriterFacts.series_facts only (tiles + frame_facts). *)
Require Export Zstd.proof.harness.writer.WTop.
Local Open Scope bool_scope.

(* the frame record the model's walk gives for a written frame *)
Definition frec_of (ws: wseries) (f: winfo) : frec :=
  {| fr_start := wi_start f; fr_size := wi_size f; fr_content := wi_content ws f;
     fr_skippable := wi_skippable f |}.

(* the frames before the first one rejected at its header with window limit wl *)
Fixpoint ok_prefix (wl: Z) (fs: list winfo) : list winfo :=
  match fs with
  | nil => nil
  | f :: fs' => if wi_rejected wl f then nil else f :: ok_prefix wl fs'
  end.

Definition all_ok (wl: Z) (fs: list winfo) : bool := forallb (fun f => negb (wi_rejected wl f)) fs.

(* ---------- helpers ---------- *)

Lemma sl_firstn_agree : forall (a b: list Z) m i j,
  firstn m a = firstn m b -> (i + j <= m)%nat -> firstn j (skipn i a) = firstn j (skipn i b).
Proof.
  intros a b m i j H Hle. rewrite !firstn_skipn_comm.
  replace (i + j)%nat with (Nat.min (i + j) m) by lia.
  rewrite <- !firstn_firstn, H. reflexivity.
Qed.

Lemma sl_length_firstn_eq : forall (a b: list Z) m,
  firstn m a = firstn m b -> (m <= length b)%nat -> (m <= length a)%nat.
Proof.
  intros a b m H Hb. assert (length (firstn m a) = length (firstn m b)) by now rewrite H.
  rewrite !length_firstn in H0. lia.
Qed.

Lemma sl_le_field_app : forall (a b: list Z) p k,
  0 <= p -> 0 <= k -> p + k <= Zlength a -> le_field (a ++ b) p k = le_field a p k.
Proof.
  intros a b p k Hp Hk H. unfold le_field, slice. f_equal.
  rewrite Zlength_correct in H. rewrite skipn_app, firstn_app, length_skipn.
  replace (Z.to_nat k - (length a - Z.to_nat p))%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma sl_tiles_bounds : forall fs off coff n cn, tiles fs off coff n cn ->
  off <= n /\ coff <= cn /\
  Forall (fun f => off <= wi_start f /\ 0 < wi_size f /\ wi_end f <= n /\ coff <= wi_cstart f /\
                   wi_cstart f + wi_csize f <= cn) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H.
  - split; [lia|split; [lia|constructor]].
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). apply IH in H6. destruct H6 as (A & B & C).
    unfold wi_end in *. split; [lia|]. split; [lia|]. constructor; [lia|].
    eapply Forall_impl; [|exact C]. simpl. intros g Hg. lia.
Qed.

Lemma sl_tiles_firstn : forall fs off coff n cn k, tiles fs off coff n cn -> (k < length fs)%nat ->
  tiles (firstn k fs) off coff (wi_start (nth k fs winfo0)) (wi_cstart (nth k fs winfo0)).
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn k H Hk; [lia|].
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6). destruct k as [|k]; simpl.
  - lia.
  - repeat split; auto. apply (IH _ _ n cn); auto. lia.
Qed.

Lemma sl_Forall_firstn : forall {A} (P: A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof.
  intros A P k l H. revert k. induction H; intros [|k]; simpl; auto.
Qed.

Lemma sl_decode_frame_not_unk : forall dm wl s, decode_frame dm wl s <> FUnk ->
  9 <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros dm wl s H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
  apply Z.ltb_ge in E1. apply Bool.negb_false_iff, Z.eqb_eq in E2.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in E1. split; [lia|exact E2].
Qed.

Lemma sl_walk_S : forall f dm wlim s off, walk (S f) dm wlim s off =
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match decode_frame dm wlim s with
        | FOk c k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
        | FDetHdr => (nil, TDetHdr)
        | FDetCk => (nil, TDetCk)
        | FUnk => (nil, TUnk)
        end.
Proof. reflexivity. Qed.

(* the walk over S from off, where the frames fs (with their facts) lie at their places in S, up to n
   where the walk gives (nil, T) *)
Lemma sl_walk_frames : forall dm ws wl S n cn T fs off coff fuel,
  tiles fs off coff n cn -> 0 <= off ->
  Forall (frame_facts dm ws) fs ->
  Forall (fun f => firstn (Z.to_nat (wi_size f)) (skipn (Z.to_nat (wi_start f)) S) = wi_bytes ws f /\
                   wi_end f <= Zlength S) fs ->
  (forall fuel, (length (skipn (Z.to_nat n) S) < fuel)%nat -> walk fuel dm wl (skipn (Z.to_nat n) S) n = (nil, T)) ->
  (length (skipn (Z.to_nat off) S) < fuel)%nat ->
  walk fuel dm wl (skipn (Z.to_nat off) S) off =
    (map (frec_of ws) (ok_prefix wl fs), if all_ok wl fs then T else TDetHdr).
Proof.
  intros dm ws wl S n cn T fs. induction fs as [|f fs IH]; intros off coff fuel Ht Hoff Hff Hpl HT Hfuel.
  - simpl in Ht. destruct Ht as [-> ->]. simpl. apply HT; auto.
  - simpl in Ht. destruct Ht as (Hst & Hcst & Hsz & Hcsz & Hskc & Ht).
    inversion Hff as [|? ? Hf Hff']; subst. inversion Hpl as [|? ? [Hfb Hend] Hpl']; subst.
    set (fb := wi_bytes ws f) in *.
    set (r := skipn (Z.to_nat (wi_start f + wi_size f)) S).
    assert (Hlenfb : length fb = Z.to_nat (wi_size f)).
    { subst fb. rewrite <- Hfb, length_firstn, length_skipn. unfold wi_end in Hend.
      rewrite Zlength_correct in Hend. lia. }
    assert (Hs : skipn (Z.to_nat (wi_start f)) S = fb ++ r).
    { subst r. rewrite <- Hfb, Z2Nat.inj_add by lia. rewrite Nat.add_comm, <- skipn_skipn.
      symmetry. apply firstn_skipn. }
    assert (Hskr : skipn (Z.to_nat (wi_size f)) (fb ++ r) = r).
    { rewrite skipn_app, Hlenfb, Nat.sub_diag, skipn_all2 by lia. reflexivity. }
    rewrite Hs in Hfuel |- *. rewrite length_app in Hfuel.
    destruct fuel as [|fuel]; [lia|].
    assert (Hfr : (length (skipn (Z.to_nat (wi_start f + wi_size f)) S) < fuel)%nat).
    { fold r. assert (0 < length fb)%nat by lia. lia. }
    destruct Hf as (_ & _ & _ & _ & _ & _ & _ & Hsk & Hdec). fold fb in Hsk, Hdec.
    rewrite sl_walk_S. destruct (wi_skippable f) eqn:Eskip.
    + destruct (Hsk eq_refl) as (_ & Hl8 & Hmag & Hsfs & _).
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. rewrite Zlength_correct, length_app. rewrite Zlength_correct in Hl8.
        unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_FRAMEHEADERSIZE_PREFIX in *. lia. }
      rewrite sl_le_field_app, Hmag, Hsfs, Hskr
        by (unfold ZSTD_SKIPPABLEHEADERSIZE in Hl8; lia).
      subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
      assert (Hrej : wi_rejected wl f = false) by (unfold wi_rejected; rewrite Eskip; reflexivity).
      simpl. rewrite Hrej. simpl. f_equal. f_equal. unfold frec_of, wi_content, slice.
      rewrite Eskip, (Hskc eq_refl). simpl. f_equal; auto.
    + destruct (Hdec eq_refl) as (Hd & _ & _). specialize (Hd wl r).
      assert (decode_frame dm wl (fb ++ r) <> FUnk) as Hnu
        by (rewrite Hd; destruct (wi_rejected wl f); discriminate).
      apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
      rewrite Hmag. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbv iota beta.
      rewrite Hd. simpl ok_prefix. simpl all_ok. destruct (wi_rejected wl f) eqn:Erej.
      * reflexivity.
      * rewrite Hskr. subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
        simpl. f_equal. f_equal. unfold frec_of. rewrite Eskip. f_equal; auto.
Qed.

(* ---------- decode_frame's header rejection depends only on the header bytes and the length ---------- *)

Lemma sl_byte_at_agree : forall (a b: list Z) m i, firstn m a = firstn m b -> 0 <= i -> (Z.to_nat i < m)%nat ->
  byte_at a i = byte_at b i.
Proof.
  intros a b m i H Hi Hm. unfold byte_at. apply Nat.ltb_lt in Hm.
  transitivity (nth (Z.to_nat i) (firstn m a) 0); [rewrite nth_firstn, Hm; reflexivity|].
  rewrite H, nth_firstn, Hm. reflexivity.
Qed.

Lemma sl_le_field_agree : forall (a b: list Z) m p k, firstn m a = firstn m b -> 0 <= p -> 0 <= k ->
  (Z.to_nat p + Z.to_nat k <= m)%nat -> le_field a p k = le_field b p k.
Proof.
  intros a b m p k H Hp Hk Hm. unfold le_field, slice. f_equal. apply (sl_firstn_agree _ _ m); auto.
Qed.

Lemma sl_fhd_bits : forall fhd, 0 <= fhd < 256 ->
  (Z.land fhd 3 = 0 \/ Z.land fhd 3 = 1 \/ Z.land fhd 3 = 2 \/ Z.land fhd 3 = 3) /\
  (Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) /\
  (Z.shiftr fhd 6 = 0 \/ Z.shiftr fhd 6 = 1 \/ Z.shiftr fhd 6 = 2 \/ Z.shiftr fhd 6 = 3).
Proof.
  intros fhd Hf.
  assert (0 <= Z.land fhd 3 <= 3).
  { assert (Z.land fhd 3 = fhd mod 4) as -> by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound fhd 4). lia. }
  assert (0 <= Z.land (Z.shiftr fhd 5) 1 <= 1).
  { assert (Z.land (Z.shiftr fhd 5) 1 = Z.shiftr fhd 5 mod 2) as ->
      by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) 2). lia. }
  assert (0 <= Z.shiftr fhd 6 <= 3).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6) with 64.
    split; [apply Z.div_pos; lia | apply Z.lt_succ_r, Z.div_lt_upper_bound; lia]. }
  lia.
Qed.

Lemma sl_fhd_header_size_ge6 : forall fhd, 0 <= fhd < 256 -> 6 <= fhd_header_size fhd.
Proof.
  intros fhd Hb. pose proof (sl_fhd_bits _ Hb) as (Hd & Hsg & Hfc). unfold fhd_header_size.
  destruct Hd as [Hd | [Hd | [Hd | Hd]]], Hsg as [Hsg | Hsg], Hfc as [Hfc | [Hfc | [Hfc | Hfc]]];
    rewrite Hd, Hsg, Hfc; simpl; lia.
Qed.

Lemma sl_gfh_agree : forall s s' m, firstn m s = firstn m s' -> length s = length s' ->
  5 <= Zlength s -> le_field s 0 4 = ZSTD_MAGICNUMBER -> 0 <= byte_at s 4 < 256 ->
  (Z.to_nat (fhd_header_size (byte_at s 4)) <= m)%nat ->
  get_frame_header s = get_frame_header s'.
Proof.
  intros s s' m Hf Hl H5 Hmag Hb Hm.
  assert (Hz : Zlength s' = Zlength s) by (rewrite !Zlength_correct, Hl; reflexivity).
  pose proof (sl_fhd_bits _ Hb) as (Hd & Hsg & Hfc).
  assert (H6 : (6 <= m)%nat) by (pose proof (sl_fhd_header_size_ge6 _ Hb); lia).
  assert (E0 : le_field s' 0 4 = le_field s 0 4) by (symmetry; apply (sl_le_field_agree _ _ m); auto; lia).
  assert (E4 : byte_at s' 4 = byte_at s 4) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; lia).
  assert (E5 : byte_at s' 5 = byte_at s 5) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; lia).
  unfold get_frame_header. rewrite Hz, E0, E4, E5, Hmag.
  assert (Zlength s <? 5 = false) as -> by (apply Z.ltb_ge; lia).
  change (negb (ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER)) with false. cbv iota zeta beta.
  set (fhd := byte_at s 4) in *.
  destruct (Zlength s <? fhd_header_size fhd) eqn:En; [reflexivity|].
  unfold fhd_header_size in Hm.
  destruct Hd as [Hd | [Hd | [Hd | Hd]]], Hsg as [Hsg | Hsg], Hfc as [Hfc | [Hfc | [Hfc | Hfc]]];
    cbv zeta in Hm; rewrite ?Hd, ?Hsg, ?Hfc in Hm |- *; simpl in Hm;
    cbn -[le_field byte_at Zlength Z.pow]; cbv [Pos.to_nat Pos.iter_op Nat.add];
    repeat (rewrite (sl_le_field_agree s s' m) by (auto; lia));
    repeat (rewrite (sl_byte_at_agree s s' m) by (auto; lia));
    reflexivity.
Qed.

Lemma sl_decode_hdr_agree : forall dm wl s s' m, firstn m s = firstn m s' -> length s = length s' ->
  0 <= byte_at s 4 < 256 -> (Z.to_nat (fhd_header_size (byte_at s 4)) <= m)%nat ->
  decode_frame dm wl s = FDetHdr -> decode_frame dm wl s' = FDetHdr.
Proof.
  intros dm wl s s' m Hf Hl Hb Hm H.
  assert (Hnu : decode_frame dm wl s <> FUnk) by (rewrite H; discriminate).
  apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
  pose proof (sl_fhd_header_size_ge6 _ Hb) as H6.
  assert (Hz : Zlength s' = Zlength s) by (rewrite !Zlength_correct, Hl; reflexivity).
  assert (E0 : le_field s' 0 4 = le_field s 0 4) by (symmetry; apply (sl_le_field_agree _ _ m); auto; lia).
  assert (E4 : byte_at s' 4 = byte_at s 4) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; lia).
  assert (E5 : byte_at s' 5 = byte_at s 5) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; lia).
  assert (Eg : get_frame_header s' = get_frame_header s)
    by (symmetry; apply (sl_gfh_agree _ _ m); auto; unfold ZSTD_FRAMEHEADERSIZE_MIN in *; lia).
  unfold decode_frame in H |- *. rewrite Hz, E0, E4, E5, Eg.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize); [discriminate|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [discriminate|].
  destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [reflexivity|].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  destruct (get_frame_header s) as [| |h]; try discriminate.
  destruct (fh_windowSize h >? wl); [reflexivity|].
  exfalso. clear - H.
  repeat match type of H with
         | context [if ?c then _ else _] => destruct c
         | context [match ?x with Some _ => _ | None => _ end] => destruct x
         | context [match ?x with (_, _) => _ end] => destruct x
         end; discriminate.
Qed.

Lemma sl_nth_map_seq : forall (g: nat -> Z) n i, (i < n)%nat -> nth i (map g (seq 0 n)) 0 = g i.
Proof.
  intros g n i H. rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma sl_xor4_length : forall b pos x, length (xor4 b pos x) = length b.
Proof. intros. unfold xor4. rewrite length_map, length_seq. reflexivity. Qed.

Lemma sl_xor4_prefix : forall b pos x, 0 <= pos ->
  firstn (Z.to_nat pos) (xor4 b pos x) = firstn (Z.to_nat pos) b.
Proof.
  intros b pos x Hp. apply nth_ext with (d := 0) (d' := 0).
  - rewrite !length_firstn, sl_xor4_length. reflexivity.
  - intros i Hi. rewrite length_firstn, sl_xor4_length in Hi. rewrite !nth_firstn.
    destruct (i <? Z.to_nat pos)%nat eqn:E; [|reflexivity]. apply Nat.ltb_lt in E.
    unfold xor4. rewrite sl_nth_map_seq by lia.
    assert (pos <=? Z.of_nat i = false) as -> by (apply Z.leb_gt; lia).
    simpl. unfold byte_at. rewrite Nat2Z.id. reflexivity.
Qed.

(* decode_checksum_corrupt, given that the Content_Checksum lies after the header *)
Lemma sl_checksum_corrupt_core : forall dm ws f wl t x,
  series_facts dm ws -> In f (ws_frames ws) -> wi_skippable f = false -> wi_checksum f = true ->
  0 < x < 2 ^ 32 -> wi_hsize f + 4 <= wi_size f ->
  decode_frame dm wl (xor4 (wi_bytes ws f) (wi_size f - 4) x ++ t) =
    if wi_rejected wl f then FDetHdr else FDetCk.
Proof.
  intros dm ws f wl t x (Hb & _ & _ & _ & _ & Ht & Hff & _) Hin Hnsk Hck Hx Hhs.
  rewrite Forall_forall in Hff. specialize (Hff f Hin).
  pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd). rewrite Forall_forall in Hbd.
  destruct (Hbd f Hin) as (Hs0 & Hsz & Hend & _). unfold wi_end in Hend.
  destruct Hff as (_ & _ & _ & _ & _ & _ & Hfhs & _ & Hdec).
  destruct (Hdec Hnsk) as (Hd & _ & Hcs).
  destruct (wi_rejected wl f) eqn:Erej; [|apply Hcs; auto].
  set (fb := wi_bytes ws f) in *.
  assert (Hlen : length fb = Z.to_nat (wi_size f)).
  { subst fb. unfold wi_bytes, slice. rewrite length_firstn, length_skipn.
    rewrite Zlength_correct in Hend. lia. }
  assert (Hfb : fb ++ skipn (Z.to_nat (wi_end f)) (ws_bytes ws) = skipn (Z.to_nat (wi_start f)) (ws_bytes ws)).
  { subst fb. unfold wi_bytes, slice, wi_end. rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn by lia.
    apply firstn_skipn. }
  specialize (Hfhs Hnsk). rewrite <- Hfb in Hfhs.
  assert (Hnu : decode_frame dm wl (fb ++ t) <> FUnk) by (rewrite Hd, Erej; discriminate).
  apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 _].
  assert (Hfb9 : (9 <= length fb)%nat).
  { assert (Hnu : decode_frame dm wl (fb ++ nil) <> FUnk) by (rewrite Hd, Erej; discriminate).
    apply sl_decode_frame_not_unk in Hnu. rewrite app_nil_r, Zlength_correct in Hnu. lia. }
  assert (E4 : byte_at (fb ++ t) 4 = byte_at fb 4).
  { unfold byte_at. rewrite app_nth1 by (simpl; lia). reflexivity. }
  assert (E4' : byte_at (fb ++ skipn (Z.to_nat (wi_end f)) (ws_bytes ws)) 4 = byte_at fb 4).
  { unfold byte_at. rewrite app_nth1 by (simpl; lia). reflexivity. }
  assert (Hbyte : 0 <= byte_at fb 4 < 256).
  { assert (Hok : bytes_ok fb).
    { subst fb. unfold wi_bytes, slice, bytes_ok in *.
      apply sl_Forall_firstn. rewrite <- (firstn_skipn (Z.to_nat (wi_start f)) (ws_bytes ws)) in Hb.
      apply Forall_app in Hb. apply Hb. }
    unfold byte_at, bytes_ok in *. rewrite Forall_forall in Hok. apply Hok, nth_In. simpl. lia. }
  unfold Info.frame_header_size in Hfhs.
  destruct (Zlength _ <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|].
  injection Hfhs as Hfhs. rewrite E4' in Hfhs.
  apply (sl_decode_hdr_agree dm wl (fb ++ t) _ (Z.to_nat (wi_size f - 4))).
  - rewrite !firstn_app, sl_xor4_length, Hlen, sl_xor4_prefix by lia.
    replace (Z.to_nat (wi_size f - 4) - Z.to_nat (wi_size f))%nat with 0%nat by lia. reflexivity.
  - rewrite !length_app, sl_xor4_length. reflexivity.
  - rewrite E4. exact Hbyte.
  - rewrite E4, Hfhs. lia.
  - rewrite Hd, Erej. reflexivity.
Qed.

(* the walk over the series: its frames up to the first rejected one, then the end or TDetHdr *)
Theorem series_frames_written : forall dm ws wl,
  series_facts dm ws ->
  series_frames dm wl (ws_bytes ws) =
    (map (frec_of ws) (ok_prefix wl (ws_frames ws)), if all_ok wl (ws_frames ws) then TEnd else TDetHdr).
Proof.
  intros dm ws wl (Hb & Hc & _ & _ & _ & Ht & Hff & _).
  pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  unfold series_frames. change (ws_bytes ws) with (skipn (Z.to_nat 0) (ws_bytes ws)) at 1.
  apply (sl_walk_frames dm ws wl (ws_bytes ws) (Zlength (ws_bytes ws)) (Zlength (ws_content ws))
           TEnd _ 0 0); auto; try lia.
  - eapply Forall_impl; [|exact Hbd]. simpl. intros f Hf. split; [reflexivity|lia].
  - intros fuel Hfuel. rewrite Zlength_correct, Nat2Z.id, skipn_all.
    destruct fuel; [simpl in Hfuel; lia|]. reflexivity.
Qed.

Theorem written_content : forall dm ws,
  series_facts dm ws -> flat_map fr_content (map (frec_of ws) (ws_frames ws)) = ws_content ws.
Proof.
  intros dm ws (_ & _ & _ & _ & _ & Ht & _).
  assert (forall fs coff off n, tiles fs off coff n (Zlength (ws_content ws)) -> 0 <= coff ->
            flat_map fr_content (map (frec_of ws) fs) = skipn (Z.to_nat coff) (ws_content ws)).
  { induction fs as [|f fs IH]; simpl; intros coff off n H Hc.
    - destruct H as [_ ->]. rewrite Zlength_correct, Nat2Z.id, skipn_all. reflexivity.
    - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite (IH _ _ _ H6) by lia.
      unfold wi_content, slice. rewrite H2, Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn by lia.
      apply firstn_skipn. }
  apply (H _ 0 0 _ Ht). lia.
Qed.

Theorem within_oneshot_all_ok : forall ws,
  wseries_wf ws -> within_oneshot_b (ws_frames ws) = all_ok no_wlim (ws_frames ws).
Proof.
  intros ws [Hwf _]. unfold within_oneshot_b, all_ok.
  induction Hwf as [|f fs Hf _ IH]; simpl; auto. rewrite IH. f_equal. f_equal.
  unfold winfo_wf, u64 in Hf. unfold wi_rejected, wi_big, no_wlim.
  assert (wi_window f >? 2 ^ 64 = false) as -> by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  destruct (wi_skippable f), (wi_single f), (wi_window_log f >? ZSTD_WINDOWLOG_MAX); reflexivity.
Qed.

Theorem within_stream_all_ok : forall ws,
  wseries_wf ws -> within_stream_b (ws_frames ws) = true -> all_ok stream_wlim (ws_frames ws) = true.
Proof.
  intros ws _. unfold within_stream_b, within_oneshot_b, all_ok.
  induction (ws_frames ws) as [|f fs IH]; simpl; auto. intros H.
  apply andb_prop in H. destruct H as [H1 H2]. apply andb_prop in H1. apply andb_prop in H2.
  destruct H1 as [Ha Hb]. destruct H2 as [Hc Hd]. rewrite IH by (apply andb_true_intro; split; [exact Hb | exact Hd]).
  rewrite Bool.andb_true_r. unfold wi_rejected. rewrite Bool.negb_true_iff in Hc. rewrite Hc.
  destruct (wi_skippable f) eqn:E; [reflexivity|]. simpl in Ha |- *. unfold stream_wlim.
  apply Z.leb_le in Ha. assert (wi_window f >? 2 ^ 27 + 1 = false) as -> by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* a series whose frame k (a Zstandard frame) is replaced, from its start on, by bytes the model rejects:
   the walk gives the frames before k (up to a rejected one) and a certain rejection *)
Definition tail_of (r: fres) : tail := match r with FDetCk => TDetCk | _ => TDetHdr end.

Theorem series_frames_corrupt : forall dm ws wl k s' r,
  series_facts dm ws -> (k < length (ws_frames ws))%nat ->
  wi_skippable (nth k (ws_frames ws) winfo0) = false ->
  firstn (Z.to_nat (wi_start (nth k (ws_frames ws) winfo0))) s' =
    firstn (Z.to_nat (wi_start (nth k (ws_frames ws) winfo0))) (ws_bytes ws) ->
  decode_frame dm wl (skipn (Z.to_nat (wi_start (nth k (ws_frames ws) winfo0))) s') = r ->
  (r = FDetHdr \/ r = FDetCk) ->
  series_frames dm wl s' =
    (map (frec_of ws) (ok_prefix wl (firstn k (ws_frames ws))),
     if all_ok wl (firstn k (ws_frames ws)) then tail_of r else TDetHdr).
Proof.
  intros dm ws wl k s' r (Hb & Hc & _ & _ & _ & Ht & Hff & _) Hk Hnsk Hpre Hr Hr2.
  set (g := nth k (ws_frames ws) winfo0) in *.
  pose proof (sl_tiles_firstn _ _ _ _ _ k Ht Hk) as Htk. fold g in Htk.
  pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  pose proof (sl_tiles_bounds _ _ _ _ _ Htk) as (Hgs & _ & Hbdk).
  assert (Hg : In g (ws_frames ws)) by (apply nth_In; exact Hk).
  rewrite Forall_forall in Hbd. pose proof (Hbd g Hg) as (Hg1 & Hg0 & Hg2 & _).
  unfold wi_end in Hg2.
  assert (Hlen : (Z.to_nat (wi_start g) <= length s')%nat).
  { apply (sl_length_firstn_eq _ _ _ Hpre). rewrite Zlength_correct in Hg2. lia. }
  unfold series_frames. change s' with (skipn (Z.to_nat 0) s') at 1.
  apply (sl_walk_frames dm ws wl s' (wi_start g) (wi_cstart g) (tail_of r) _ 0 0); auto; try lia.
  - apply sl_Forall_firstn; auto.
  - eapply Forall_impl; [|exact Hbdk]. simpl. intros f (Hf1 & Hf0 & Hf2 & _). unfold wi_end in Hf2.
    split.
    + unfold wi_bytes, slice. apply (sl_firstn_agree _ _ _ _ _ Hpre). lia.
    + unfold wi_end. rewrite Zlength_correct. lia.
  - intros fuel Hfuel. destruct fuel as [|fuel]; [lia|].
    assert (decode_frame dm wl (skipn (Z.to_nat (wi_start g)) s') <> FUnk) as Hnu
      by (rewrite Hr; destruct Hr2 as [-> | ->]; discriminate).
    apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
    rewrite sl_walk_S.
    assert (Zlength (skipn (Z.to_nat (wi_start g)) s') <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->
      by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
    rewrite Hmag. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbv iota beta.
    rewrite Hr. destruct Hr2 as [-> | ->]; reflexivity.
Qed.

(* harness/detect.c's corruption of a frame's Content_Checksum, whatever the window limit *)
Theorem decode_checksum_corrupt : forall dm ws f wl t x,
  series_facts dm ws -> wseries_wf ws -> In f (ws_frames ws) -> wi_skippable f = false -> wi_checksum f = true ->
  0 < x < 2 ^ 32 ->
  decode_frame dm wl (xor4 (wi_bytes ws f) (wi_size f - 4) x ++ t) =
    if wi_rejected wl f then FDetHdr else FDetCk.
Proof.
  intros dm ws f wl t x Hs (_ & _ & Hl) Hin Hnsk Hck Hx.
  apply sl_checksum_corrupt_core; auto.
  rewrite Forall_forall in Hl. specialize (Hl f Hin Hnsk Hck). lia.
Qed.
