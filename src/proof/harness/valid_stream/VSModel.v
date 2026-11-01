(* harness/valid_stream.c against the model (plain Coq): what main's checks compute on the series (h_end,
   h_at_end), and how the claims of ZSTD_decompressStream (StreamModel.stream_claims) on the stream of a
   written series (WriterFacts.series_facts) give them.  Used by WMain_valid_stream.v. *)
Require Export Zstd.proof.harness.writer.SeriesLemmas.
Local Open Scope bool_scope.

(* main's `end` loop (k from nframes down to 1): the end of the first frame that ends after ipos, or ends at
   ipos with its content not all delivered (got = bytes delivered); dflt (= sr.n) if none *)
Fixpoint h_end (fs: list winfo) (ipos got dflt: Z) : Z :=
  match fs with
  | nil => dflt
  | f :: fs' =>
      if (wi_end f >? ipos) || ((wi_end f =? ipos) && (got <? wi_cstart f + wi_csize f)) then wi_end f
      else h_end fs' ipos got dflt
  end.

(* main's `at_end` loop: some frame ends at ipos with all content up to its end delivered *)
Definition h_at_end (fs: list winfo) (ipos got: Z) : bool :=
  existsb (fun f => (wi_end f =? ipos) && (got =? wi_cstart f + wi_csize f)) fs.

(* the hint clause of stream_claims (on the model without a window limit), for a series whose walk ends
   (TEnd) or stops at a frame zstd rejects at its header (TDetHdr) *)
Definition hint_claim (sin sout: list Z) (r: Z) : Prop :=
  forall s, is_prefix sin s ->
  let fl := fst (series_frames no_dict no_wlim s) in
  let t := snd (series_frames no_dict no_wlim s) in
  (t = TEnd \/ t = TDetHdr) -> is_error_code r = false -> 0 < r ->
  r <= Z.max 1 (cur_end fl (Zlength sin) (Zlength sout) (Zlength s) - Zlength sin).

Lemma VS_h_end_ge fs ipos got dflt : ipos <= dflt -> ipos <= h_end fs ipos got dflt.
Proof.
  intros H. induction fs as [|f fs IH]; simpl; auto.
  destruct (wi_end f >? ipos) eqn:E1; simpl.
  - apply Z.gtb_lt in E1. lia.
  - destruct ((wi_end f =? ipos) && (got <? wi_cstart f + wi_csize f)) eqn:E2; auto.
    apply Bool.andb_true_iff in E2 as [E2 _]. apply Z.eqb_eq in E2. lia.
Qed.

(* ---------- helpers for VS_hint (from SeriesLemmas' proof) ---------- *)

Lemma vsh_firstn_agree : forall (a b: list Z) m i j,
  firstn m a = firstn m b -> (i + j <= m)%nat -> firstn j (skipn i a) = firstn j (skipn i b).
Proof.
  intros a b m i j H Hle. rewrite !firstn_skipn_comm.
  replace (i + j)%nat with (Nat.min (i + j) m) by lia.
  rewrite <- !firstn_firstn, H. reflexivity.
Qed.

Lemma vsh_le_field_app : forall (a b: list Z) p k,
  0 <= p -> 0 <= k -> p + k <= Zlength a -> le_field (a ++ b) p k = le_field a p k.
Proof.
  intros a b p k Hp Hk H. unfold le_field, slice. f_equal.
  rewrite Zlength_correct in H. rewrite skipn_app, firstn_app, length_skipn.
  replace (Z.to_nat k - (length a - Z.to_nat p))%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma vsh_tiles_bounds : forall fs off coff n cn, tiles fs off coff n cn ->
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

Lemma vsh_Forall_firstn : forall {A} (P: A -> Prop) k l, Forall P l -> Forall P (firstn k l).
Proof.
  intros A P k l H. revert k. induction H; intros [|k]; simpl; auto.
Qed.

Lemma vsh_decode_frame_not_unk : forall dm wl s, decode_frame dm wl s <> FUnk ->
  9 <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros dm wl s H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
  apply Z.ltb_ge in E1. apply Bool.negb_false_iff, Z.eqb_eq in E2.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in E1. split; [lia|exact E2].
Qed.

Lemma vsh_walk_S : forall f dm wlim s off, walk (S f) dm wlim s off =
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

Lemma vsh_walk_frames : forall dm ws wl S n cn T fs off coff fuel,
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
    rewrite vsh_walk_S. destruct (wi_skippable f) eqn:Eskip.
    + destruct (Hsk eq_refl) as (_ & Hl8 & Hmag & Hsfs & _).
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. rewrite Zlength_correct, length_app. rewrite Zlength_correct in Hl8.
        unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_FRAMEHEADERSIZE_PREFIX in *. lia. }
      rewrite vsh_le_field_app, Hmag, Hsfs, Hskr
        by (unfold ZSTD_SKIPPABLEHEADERSIZE in Hl8; lia).
      subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
      assert (Hrej : wi_rejected wl f = false) by (unfold wi_rejected; rewrite Eskip; reflexivity).
      simpl. rewrite Hrej. simpl. f_equal. f_equal. unfold frec_of, wi_content, slice.
      rewrite Eskip, (Hskc eq_refl). simpl. f_equal; auto.
    + destruct (Hdec eq_refl) as (Hd & _ & _). specialize (Hd wl r).
      assert (decode_frame dm wl (fb ++ r) <> FUnk) as Hnu
        by (rewrite Hd; destruct (wi_rejected wl f); discriminate).
      apply vsh_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
      rewrite Hmag. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbv iota beta.
      rewrite Hd. simpl ok_prefix. simpl all_ok. destruct (wi_rejected wl f) eqn:Erej.
      * reflexivity.
      * rewrite Hskr. subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
        simpl. f_equal. f_equal. unfold frec_of. rewrite Eskip. f_equal; auto.
Qed.

Lemma vsh_tiles_csize : forall fs off coff n cn, tiles fs off coff n cn -> Forall (fun f => 0 <= wi_csize f) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H; constructor.
  - lia.
  - destruct H as (_ & _ & _ & _ & _ & H). eapply IH; exact H.
Qed.

(* main's `end` over the frames up to the current one: the frames before it, tiling up to its end *)
Lemma vsh_h_end_prefix : forall fs off coff n cn ipos got, tiles fs off coff n cn ->
  exists j cE, tiles (firstn j fs) off coff (h_end fs ipos got n) cE /\ h_end fs ipos got n <= n /\
    h_end (firstn j fs) ipos got (h_end fs ipos got n) = h_end fs ipos got n.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn ipos got Ht.
  - exists O, coff. simpl. destruct Ht as [-> ->]. split; [auto|]. split; [lia|reflexivity].
  - destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6).
    pose proof (vsh_tiles_bounds _ _ _ _ _ H6) as (Hb & _).
    destruct ((wi_end f >? ipos) || ((wi_end f =? ipos) && (got <? wi_cstart f + wi_csize f))) eqn:E.
    + exists 1%nat, (coff + wi_csize f). simpl. rewrite E. unfold wi_end in *.
      split; [repeat split; auto; lia|]. split; [lia|reflexivity].
    + destruct (IH _ _ _ _ ipos got H6) as (j & cE & Hj1 & Hj2 & Hj3).
      exists (S j), cE. simpl. rewrite E. split; [repeat split; auto|]. split; [lia|exact Hj3].
Qed.

(* cur_end over the walk's frames, with main's `end` as the default, is main's `end` *)
Lemma vsh_cur_end_h_end : forall ws wl fs off coff n cn ipos got d, tiles fs off coff n cn ->
  Forall (fun f => Zlength (wi_content ws f) = wi_csize f) fs ->
  cur_end_aux (map (frec_of ws) (ok_prefix wl fs)) ipos got coff (h_end fs ipos got d) = h_end fs ipos got d.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn ipos got d Ht Hc; [reflexivity|].
  destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6). inversion Hc as [|? ? Hcf Hc']; subst.
  destruct (wi_rejected wl f); [reflexivity|]. simpl. unfold fr_end. simpl. rewrite Hcf.
  change (wi_start f + wi_size f) with (wi_end f).
  destruct ((wi_end f >? ipos) || ((wi_end f =? ipos) && (got <? wi_cstart f + wi_csize f))); [reflexivity|].
  eapply IH; eauto.
Qed.

(* a positive return: main's bound with its `end` *)
Lemma VS_hint ws sin sout r :
  series_facts no_dict ws -> is_prefix sin (ws_bytes ws) -> hint_claim sin sout r ->
  is_error_code r = false -> 0 < r ->
  r <= Z.max 1 (h_end (ws_frames ws) (Zlength sin) (Zlength sout) (Zlength (ws_bytes ws)) - Zlength sin).
Proof.
  intros Hsf Hpre Hh Herr Hr.
  pose proof Hsf as (Hb & Hc & _ & _ & _ & Ht & Hff & _).
  set (fs := ws_frames ws) in *. set (ipos := Zlength sin). set (got := Zlength sout).
  set (N := Zlength (ws_bytes ws)) in *.
  destruct (vsh_h_end_prefix fs 0 0 N (Zlength (ws_content ws)) ipos got Ht) as (j & cE & Hj1 & HEN & Hj3).
  set (E := h_end fs ipos got N) in *.
  assert (HsinN : ipos <= N).
  { unfold is_prefix in Hpre. assert (length (firstn (length sin) (ws_bytes ws)) = length sin) by now rewrite Hpre.
    rewrite length_firstn in H. unfold ipos, N. rewrite !Zlength_correct. lia. }
  assert (HiE : ipos <= E) by (apply VS_h_end_ge; exact HsinN).
  assert (HE0 : 0 <= E) by (unfold ipos in HiE; rewrite Zlength_correct in HiE; lia).
  set (s := firstn (Z.to_nat E) (ws_bytes ws)).
  assert (Hls : Zlength s = E).
  { unfold s. rewrite Zlength_correct, length_firstn. unfold N in HEN. rewrite Zlength_correct in HEN. lia. }
  assert (Hps : is_prefix sin s).
  { unfold is_prefix, s in *. rewrite firstn_firstn.
    replace (Nat.min (length sin) (Z.to_nat E)) with (length sin) by (unfold ipos in HiE; rewrite Zlength_correct in HiE; lia).
    exact Hpre. }
  pose proof (vsh_tiles_bounds _ _ _ _ _ Hj1) as (_ & _ & Hbd).
  pose proof (vsh_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd0).
  assert (Hwalk : series_frames no_dict no_wlim s =
     (map (frec_of ws) (ok_prefix no_wlim (firstn j fs)),
      if all_ok no_wlim (firstn j fs) then TEnd else TDetHdr)).
  { unfold series_frames. change s with (skipn (Z.to_nat 0) s) at 1.
    apply (vsh_walk_frames no_dict ws no_wlim s E cE TEnd _ 0 0); auto; try lia.
    - apply vsh_Forall_firstn; auto.
    - eapply Forall_impl; [|exact Hbd]. simpl. intros f (Hf1 & Hf0 & Hf2 & _). split.
      + unfold wi_bytes, slice. apply (vsh_firstn_agree _ _ (Z.to_nat E)).
        * unfold s. rewrite firstn_firstn, Nat.min_id. reflexivity.
        * unfold wi_end in Hf2. lia.
      + rewrite Hls. exact Hf2.
    - intros fuel Hfuel.
      assert (skipn (Z.to_nat E) s = nil) as Hn
        by (apply skipn_all2; rewrite <- Hls, Zlength_correct, Nat2Z.id; lia).
      rewrite Hn in Hfuel |- *. destruct fuel; [simpl in Hfuel; lia|]. reflexivity.
    }
  specialize (Hh s Hps). rewrite Hwalk in Hh. simpl in Hh.
  assert (Ht' : (if all_ok no_wlim (firstn j fs) then TEnd else TDetHdr) = TEnd \/
                (if all_ok no_wlim (firstn j fs) then TEnd else TDetHdr) = TDetHdr)
    by (destruct (all_ok _ _); auto).
  specialize (Hh Ht' Herr Hr). rewrite Hls in Hh. fold ipos got in Hh.
  unfold cur_end in Hh. rewrite <- Hj3 in Hh at 1.
  rewrite (vsh_cur_end_h_end ws no_wlim (firstn j fs) 0 0 E cE ipos got E Hj1) in Hh.
  - rewrite Hj3 in Hh. exact Hh.
  - apply vsh_Forall_firstn. pose proof (vsh_tiles_csize _ _ _ _ _ Ht) as Hcs.
    rewrite Forall_forall in Hbd0, Hcs |- *. intros f Hf. destruct (Hbd0 f Hf) as (_ & _ & _ & Hc1 & Hc2).
    specialize (Hcs f Hf).
    unfold wi_content, slice. rewrite Zlength_correct, length_firstn, length_skipn.
    rewrite Zlength_correct in Hc2. lia.
Qed.
