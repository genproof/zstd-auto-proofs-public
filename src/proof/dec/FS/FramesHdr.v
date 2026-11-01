(* FS one-shot frames: the model facts of one frame (ZSTD_decompressFrame's body).
   Plain Coq over model/Series.v. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Block Zstd.proof.model.Xxh64
  Zstd.proof.model.Series.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- helpers ---------- *)

Lemma fh_Zlength_firstn: forall (s: list Z) n, 0 <= n <= Zlength s -> Zlength (firstn (Z.to_nat n) s) = n.
Proof.
  intros. rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in H. lia.
Qed.

Lemma fh_byte_at_firstn: forall s n i, 0 <= i < n -> byte_at (firstn (Z.to_nat n) s) i = byte_at s i.
Proof.
  intros. unfold byte_at. rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat n)); [reflexivity | lia].
Qed.

Lemma fh_le_field_firstn: forall s n i k, 0 <= i -> 0 <= k -> i + k <= n ->
  le_field (firstn (Z.to_nat n) s) i k = le_field s i k.
Proof.
  intros. unfold le_field, slice. rewrite skipn_firstn_comm, firstn_firstn. f_equal. f_equal. lia.
Qed.

Lemma fh_le_value_bound: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l; intros H; cbn [le_value length]. simpl. lia.
  inversion H; subst. unfold is_byte in *. destruct (IHl H3).
  replace (8 * Z.of_nat (S (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite Z.pow_add_r by lia. change (2^8) with 256. nia.
Qed.

Lemma fh_Forall_firstn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma fh_Forall_skipn: forall (P: Z -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof. induction n; intros; destruct l; simpl; auto. inversion H; subst; auto. Qed.

Lemma fh_le_field_bound: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros. unfold le_field, slice.
  assert (bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply fh_Forall_firstn, fh_Forall_skipn. auto. }
  destruct (fh_le_value_bound _ H1). split; auto.
  eapply Z.lt_le_trans; [eassumption|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. lia.
Qed.

Lemma fh_byte_at_bound: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length s)).
  - unfold bytes_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma fh_land_mod: forall x n, 0 <= n -> Z.land x (Z.ones n) = x mod 2 ^ n.
Proof. intros. apply Z.land_ones. auto. Qed.

Lemma fh_fhd_bits: forall fhd, 0 <= fhd < 256 ->
  0 <= Z.land fhd 3 < 4 /\ 0 <= Z.land (Z.shiftr fhd 5) 1 < 2 /\ 0 <= Z.shiftr fhd 6 < 4 /\
  0 <= Z.land (Z.shiftr fhd 2) 1 < 2.
Proof.
  intros.
  change 3 with (Z.ones 2). change 1 with (Z.ones 1).
  rewrite !fh_land_mod by lia. rewrite !Z.shiftr_div_pow2 by lia.
  repeat split; try apply Z.mod_pos_bound; try lia.
  apply Z.div_pos; lia. apply Z.div_lt_upper_bound; simpl; lia.
Qed.

Lemma fh_hs_range: forall fhd, 0 <= fhd < 256 -> 6 <= fhd_header_size fhd <= 18.
Proof.
  intros. destruct (fh_fhd_bits fhd H) as (Hd & Hss & Hfc & _). unfold fhd_header_size.
  assert (Z.land fhd 3 = 0 \/ Z.land fhd 3 = 1 \/ Z.land fhd 3 = 2 \/ Z.land fhd 3 = 3) as Ed by lia.
  assert (Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1) as Es by lia.
  assert (Z.shiftr fhd 6 = 0 \/ Z.shiftr fhd 6 = 1 \/ Z.shiftr fhd 6 = 2 \/ Z.shiftr fhd 6 = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    simpl; lia.
Qed.

Lemma fh_gfh_prefix: forall s,
  0 <= byte_at s 4 < 256 ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) <= Zlength s ->
  get_frame_header (firstn (Z.to_nat (fhd_header_size (byte_at s 4))) s) = get_frame_header s.
Proof.
  intros s Hb Hn Hm Hhs.
  pose proof (fh_hs_range _ Hb) as Hr.
  unfold get_frame_header.
  rewrite fh_Zlength_firstn by lia.
  rewrite (fh_le_field_firstn s _ 0 4) by lia.
  rewrite (fh_byte_at_firstn s _ 4) by lia.
  rewrite Hm. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in Hn.
  destruct (Z.ltb_spec (fhd_header_size (byte_at s 4)) 5); [lia|].
  destruct (Z.ltb_spec (Zlength s) 5); [lia|].
  rewrite Z.eqb_refl. cbn [negb].
  destruct (Z.ltb_spec (fhd_header_size (byte_at s 4)) (fhd_header_size (byte_at s 4))); [lia|].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))); [lia|].
  rewrite (fh_byte_at_firstn s _ 5) by lia.
  destruct (fh_fhd_bits _ Hb) as (Hd & Hss & Hfc & _).
  clear H H0 H1 H2.
  revert Hhs Hr. unfold fhd_header_size.
  remember (Z.land (byte_at s 4) 3) as d. remember (Z.land (Z.shiftr (byte_at s 4) 5) 1) as ss.
  remember (Z.shiftr (byte_at s 4) 6) as fc.
  intros Hhs Hr.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as Ed by lia.
  assert (ss = 0 \/ ss = 1) as Es by lia.
  assert (fc = 0 \/ fc = 1 \/ fc = 2 \/ fc = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    cbn [Z.eqb Pos.eqb andb]; simpl in Hhs, Hr;
    rewrite ?fh_le_field_firstn, ?fh_byte_at_firstn by (simpl; lia); reflexivity.
Qed.

Lemma fh_window_bound: forall b, 0 <= b < 256 ->
  Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN <= ZSTD_WINDOWLOG_MAX ->
  0 <= 2 ^ (Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr b 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land b 7 < 2 ^ 64.
Proof.
  intros b Hb Hw. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in *.
  rewrite Z.shiftr_div_pow2 in * by lia.
  rewrite (Z.shiftr_div_pow2 (2 ^ _)) by lia.
  change 7 with (Z.ones 3). rewrite fh_land_mod by lia.
  assert (0 <= b / 2 ^ 3) by (apply Z.div_pos; lia).
  assert (0 < 2 ^ (b / 2 ^ 3 + 10)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (b / 2 ^ 3 + 10) <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  assert (0 <= 2 ^ (b / 2 ^ 3 + 10) / 2 ^ 3 <= 2 ^ (b / 2 ^ 3 + 10)).
  { split. apply Z.div_pos; lia. apply Z.div_le_upper_bound. lia. change (2 ^ 3) with 8. lia. }
  assert (0 <= b mod 2 ^ 3 < 2 ^ 3) by (apply Z.mod_pos_bound; lia).
  change (2 ^ 3) with 8 in *. change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616.
  nia.
Qed.

Ltac fh_bnd s Hb :=
  repeat match goal with
  | |- context [le_field s ?i ?k] =>
      let H := fresh "Hf" in
      pose proof (fh_le_field_bound s i k Hb ltac:(simpl; lia)) as H;
      revert H; generalize (le_field s i k); intros ? H
  | |- context [byte_at s ?i] =>
      tryif constr_eq i 4 then fail else
      let H := fresh "Hy" in
      pose proof (fh_byte_at_bound s i Hb) as H;
      revert H; generalize (byte_at s i); intros ? H
  end.

Lemma fh_gfh_ok: forall s h,
  bytes_ok s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  get_frame_header s = FH_ok h ->
  fh_frameType h = 0 /\ fh_headerSize h = fhd_header_size (byte_at s 4) /\
  fh_headerSize h <= Zlength s /\ 6 <= fh_headerSize h <= 18 /\
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX /\
  0 <= fh_windowSize h < 2 ^ 64 /\ 0 <= fh_contentSize h < 2 ^ 64 /\
  (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\ 0 <= fh_dictID h < 2 ^ 32.
Proof.
  intros s h Hb Hm H. unfold get_frame_header in H.
  destruct (Z.ltb_spec (Zlength s) 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate. }
  rewrite Hm, Z.eqb_refl in H. cbn [negb] in H.
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4))); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  pose proof (fh_byte_at_bound s 4 Hb) as B4. pose proof (fh_byte_at_bound s 5 Hb) as B5.
  pose proof (fh_hs_range _ B4) as Hr.
  destruct (fh_fhd_bits _ B4) as (Hd & Hss & Hfc & Hck).
  destruct ((Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0) &&
            (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:Ew;
    [discriminate|].
  injection H as <-. cbn [fh_frameType fh_headerSize fh_blockSizeMax fh_windowSize fh_contentSize
    fh_checksumFlag fh_dictID].
  assert (Hck': Z.land (Z.shiftr (byte_at s 4) 2) 1 = 0 \/ Z.land (Z.shiftr (byte_at s 4) 2) 1 = 1) by lia.
  remember (Z.land (byte_at s 4) 3) as d. remember (Z.land (Z.shiftr (byte_at s 4) 5) 1) as ss.
  remember (Z.shiftr (byte_at s 4) 6) as fc.
  assert (Hwin: ss = 0 -> 0 <= 2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land (byte_at s 5) 7 < 2 ^ 64).
  { intros ->. apply fh_window_bound; auto. cbn [Z.eqb andb] in Ew. rewrite Z.gtb_ltb in Ew. apply Z.ltb_ge in Ew. lia. }
  clear Ew.
  generalize dependent (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN) +
       Z.shiftr (2 ^ (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN)) 3 * Z.land (byte_at s 5) 7).
  intros w Hwin.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as Ed by lia.
  assert (ss = 0 \/ ss = 1) as Es by lia.
  assert (fc = 0 \/ fc = 1 \/ fc = 2 \/ fc = 3) as Ef by lia.
  destruct Ed as [-> | [-> | [-> | ->]]]; destruct Es as [-> | ->]; destruct Ef as [-> | [-> | [-> | ->]]];
    cbn [Z.eqb Pos.eqb andb];
    try specialize (Hwin eq_refl);
    fh_bnd s Hb; unfold ZSTD_BLOCKSIZE_MAX, ZSTD_CONTENTSIZE_UNKNOWN in *; simpl in *;
    repeat split; try lia; try tauto.
Qed.

Lemma fh_decode_frame_short: forall dm s,
  Zlength s < ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize \/
  le_field s 0 4 <> ZSTD_MAGICNUMBER \/
  Zlength s < fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize ->
  decode_frame dm no_wlim s = FUnk.
Proof.
  intros dm s H. unfold decode_frame.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [reflexivity|].
  destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER); [|reflexivity]. cbn [negb].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [reflexivity|].
  lia.
Qed.

Lemma fh_decode_frame_header_bad: forall dm s,
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  (forall h, get_frame_header s <> FH_ok h) ->
  decode_frame dm no_wlim s = FDetHdr \/ decode_frame dm no_wlim s = FUnk.
Proof.
  intros dm s H1 H2 H3 H4. unfold decode_frame.
  destruct (Zlength s <? _); [auto|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [auto|].
  destruct (Zlength s <? _); [auto|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [auto|].
  destruct (_ && _); [auto|].
  destruct (get_frame_header s) eqn:E; auto. exfalso; eapply H4; eauto.
Qed.

Lemma fh_decode_frame_header_ok: forall dm s h,
  bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  get_frame_header s = FH_ok h ->
  decode_frame dm no_wlim s =
    if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
    let hs := fh_headerSize h in
    let rest := skipn (Z.to_nat hs) s in
    match decode_blocks (length rest) (dm_state dm) (dm_content dm) rest nil (fh_blockSizeMax h) (fh_windowSize h) with
    | None => FUnk
    | Some (out, k) =>
        if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
        then FUnk else
        if fh_checksumFlag h =? 1 then
          (if Zlength s - hs - k <? 4 then FUnk
           else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
           else FOk out (hs + k + 4))
        else FOk out (hs + k)
    end.
Proof.
  intros dm s h Hb H1 Hm H3 Hg.
  destruct (fh_gfh_ok s h Hb Hm Hg) as (Ht & _ & _ & _ & _ & _ & Hw & _).
  unfold decode_frame.
  destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize)); [lia|].
  rewrite Hm, Z.eqb_refl. cbn [negb].
  destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize)); [lia|].
  assert (Hg' := Hg). unfold get_frame_header in Hg'.
  destruct (Z.ltb_spec (Zlength s) 5); [unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia|].
  rewrite Hm, Z.eqb_refl in Hg'. cbn [negb] in Hg'.
  destruct (Zlength s <? fhd_header_size (byte_at s 4)); [discriminate|].
  destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
  replace (negb (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 1)) with (Z.land (Z.shiftr (byte_at s 4) 5) 1 =? 0).
  2:{ pose proof (fh_byte_at_bound s 4 Hb) as B4. destruct (fh_fhd_bits _ B4) as (_ & Hss & _).
      assert (Z.land (Z.shiftr (byte_at s 4) 5) 1 = 0 \/ Z.land (Z.shiftr (byte_at s 4) 5) 1 = 1) as [-> | ->] by lia;
      reflexivity. }
  destruct (_ && _); [discriminate|].
  rewrite Hg.
  destruct (Z.gtb_spec (fh_windowSize h) no_wlim); [unfold no_wlim in *; lia|].
  rewrite Ht. reflexivity.
Qed.

Lemma fh_cblock_size_nonneg: forall s c, bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  intros s c Hb H. unfold cblock_size in H.
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type (block_props_of s) =? 1); [injection H as <-; lia|].
  destruct (bp_type (block_props_of s) =? 3); [discriminate|].
  injection H as <-. unfold block_props_of; cbn [bp_origSize].
  pose proof (fh_le_field_bound s 0 3 Hb ltac:(lia)). apply Z.shiftr_nonneg. lia.
Qed.

Lemma fh_Zlength_skipn: forall (s: list Z) n, 0 <= n <= Zlength s -> Zlength (skipn (Z.to_nat n) s) = Zlength s - n.
Proof.
  intros. rewrite !Zlength_correct, skipn_length. rewrite Zlength_correct in H. lia.
Qed.

Lemma fh_decode_blocks_prefix: forall f st hist s out bsm wsize o k,
  bytes_ok s ->
  decode_blocks f st hist s out bsm wsize = Some (o, k) ->
  (exists t, o = out ++ t) /\ ZSTD_blockHeaderSize <= k <= Zlength s.
Proof.
  induction f; intros st hist s out bsm wsize o k Hb H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (fh_cblock_size_nonneg s c Hb Ec) as Hc0.
  destruct (Z.gtb_spec c (Zlength s - ZSTD_blockHeaderSize)); [discriminate|].
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Er; [|discriminate] end.
  assert (Ho: exists t, out' = out ++ t).
  { destruct (bp_type (block_props_of s) =? 0).
    - destruct (c >? bsm); [discriminate|]. injection Er as _ <-. eauto.
    - destruct (bp_type (block_props_of s) =? 1).
      + destruct (_ || _); [discriminate|]. injection Er as _ <-. eauto.
      + destruct (decode_block _ _ _ _ _ _) as [[? ?]|]; [|discriminate]. injection Er as _ <-. eauto. }
  destruct Ho as [t Ht].
  destruct (bp_last (block_props_of s) =? 1).
  - assert (o = out' /\ k = ZSTD_blockHeaderSize + c) as [-> ->] by (split; congruence).
    unfold ZSTD_blockHeaderSize in *. split; [eauto | lia].
  - destruct (decode_blocks f st' hist _ out' bsm wsize) as [[o' k']|] eqn:Ed; [|discriminate].
    assert (o = o' /\ k = ZSTD_blockHeaderSize + c + k') as [-> ->] by (split; congruence).
    assert (Hb': bytes_ok (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s)) by (apply fh_Forall_skipn; auto).
    destruct (IHf _ _ _ _ _ _ _ _ Hb' Ed) as [[t' Ht'] Hk].
    rewrite fh_Zlength_skipn in Hk by (unfold ZSTD_blockHeaderSize in *; lia).
    split.
    + exists (t ++ t'). subst. rewrite app_assoc. reflexivity.
    + unfold ZSTD_blockHeaderSize in *. lia.
Qed.

(* ---------- the frame header ---------- *)

(* ZSTD_frameHeaderSize_internal reads the 5-byte prefix *)
Lemma frame_header_size_prefix: forall s,
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  frame_header_size (firstn (Z.to_nat ZSTD_FRAMEHEADERSIZE_PREFIX) s) = Some (fhd_header_size (byte_at s 4)).
Proof.
  intros s H. unfold frame_header_size, ZSTD_FRAMEHEADERSIZE_PREFIX in *.
  rewrite fh_Zlength_firstn by lia. rewrite fh_byte_at_firstn by lia. reflexivity.
Qed.

(* ZSTD_decodeFrameHeader reads the header bytes only *)
Lemma get_frame_header_prefix: forall s,
  bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) <= Zlength s ->
  get_frame_header (firstn (Z.to_nat (fhd_header_size (byte_at s 4))) s) = get_frame_header s.
Proof.
  intros s Hb. apply fh_gfh_prefix. apply fh_byte_at_bound. exact Hb.
Qed.

(* the header of a Zstandard frame: the values the C reads back from fParams *)
Lemma get_frame_header_ok: forall s h,
  bytes_ok s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  get_frame_header s = FH_ok h ->
  fh_frameType h = 0 /\ fh_headerSize h = fhd_header_size (byte_at s 4) /\
  fh_headerSize h <= Zlength s /\ 6 <= fh_headerSize h <= 18 /\
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ fh_blockSizeMax h = Z.min (fh_windowSize h) ZSTD_BLOCKSIZE_MAX /\
  0 <= fh_windowSize h < 2 ^ 64 /\ 0 <= fh_contentSize h < 2 ^ 64 /\
  (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\ 0 <= fh_dictID h < 2 ^ 32.
Proof.
  exact fh_gfh_ok.
Qed.

(* decode_frame after a successful header, as ZSTD_decompressFrame proceeds (no window limit) *)
Lemma decode_frame_header_ok: forall dm s h,
  bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  get_frame_header s = FH_ok h ->
  decode_frame dm no_wlim s =
    if negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm) then FUnk else
    let hs := fh_headerSize h in
    let rest := skipn (Z.to_nat hs) s in
    match decode_blocks (length rest) (dm_state dm) (dm_content dm) rest nil (fh_blockSizeMax h) (fh_windowSize h) with
    | None => FUnk
    | Some (out, k) =>
        if negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)
        then FUnk else
        if fh_checksumFlag h =? 1 then
          (if Zlength s - hs - k <? 4 then FUnk
           else if negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32) then FDetCk
           else FOk out (hs + k + 4))
        else FOk out (hs + k)
    end.
Proof.
  exact fh_decode_frame_header_ok.
Qed.

(* a header the C rejects (getFrameHeader: an error) is never Ok in the model *)
Lemma decode_frame_header_bad: forall dm s,
  ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize <= Zlength s ->
  le_field s 0 4 = ZSTD_MAGICNUMBER ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s ->
  (forall h, get_frame_header s <> FH_ok h) ->
  decode_frame dm no_wlim s = FDetHdr \/ decode_frame dm no_wlim s = FUnk.
Proof.
  exact fh_decode_frame_header_bad.
Qed.

(* every other early exit of ZSTD_decompressFrame: the model does not decode the frame *)
Lemma decode_frame_short: forall dm s,
  Zlength s < ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize \/
  le_field s 0 4 <> ZSTD_MAGICNUMBER \/
  Zlength s < fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize ->
  decode_frame dm no_wlim s = FUnk.
Proof.
  exact fh_decode_frame_short.
Qed.

(* ---------- the blocks ---------- *)

(* one step of decode_blocks (the C loop body) *)
Lemma decode_blocks_step: forall f st hist s out bsm wsize,
  decode_blocks (S f) st hist s out bsm wsize =
      match cblock_size s with
      | None => None
      | Some c =>
          if c >? Zlength s - ZSTD_blockHeaderSize then None else
          let bp := block_props_of s in
          let body := slice s ZSTD_blockHeaderSize c in
          let res :=
            if bp_type bp =? 0 then
              (if c >? bsm then None else Some (st, out ++ body))
            else if bp_type bp =? 1 then
              (if (bp_origSize bp >? bsm) || (c >? bsm) then None
               else Some (st, out ++ repeat (byte_at body 0) (Z.to_nat (bp_origSize bp))))
            else
              match decode_block st hist out body bsm wsize with
              | Some (st', content) => Some (st', out ++ content)
              | None => None
              end in
          match res with
          | None => None
          | Some (st', out') =>
              if bp_last bp =? 1 then Some (out', ZSTD_blockHeaderSize + c)
              else match decode_blocks f st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' bsm wsize with
                   | Some (o, k) => Some (o, ZSTD_blockHeaderSize + c + k)
                   | None => None
                   end
          end
      end.
Proof. reflexivity. Qed.

(* the output only grows, and the blocks are within s *)
Lemma decode_blocks_prefix: forall f st hist s out bsm wsize o k,
  bytes_ok s ->
  decode_blocks f st hist s out bsm wsize = Some (o, k) ->
  (exists t, o = out ++ t) /\ ZSTD_blockHeaderSize <= k <= Zlength s.
Proof.
  exact fh_decode_blocks_prefix.
Qed.


(* all the lemmas above (the target of this file: its assumptions are theirs) *)
Lemma frames_hdr_all : True.
Proof.
  pose proof frame_header_size_prefix. pose proof get_frame_header_prefix. pose proof get_frame_header_ok.
  pose proof decode_frame_header_ok. pose proof decode_frame_header_bad. pose proof decode_frame_short.
  pose proof decode_blocks_prefix. exact I.
Qed.
