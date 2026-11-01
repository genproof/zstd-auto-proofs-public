(* What zstd's format model makes of a frame written by new_frame (FModel.v): its header as
   ZSTD_getFrameHeader reads it, its size as ZSTD_findFrameCompressedSize finds it, and its content as
   ZSTD_decompressFrame decodes it (model/Frame.v, model/Params.v).  Plain Coq.  These are the facts the
   laws on hand-built frames need from the writer.

   F = nf_bytes d fcs did c, the frame for data d (n = |d| bytes), declared content size fcs, Dictionary_ID
   did, and choices c with nf_ok n fcs maxw did c. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FModel.
Local Open Scope bool_scope.

(* the header zstd reads from F *)
Definition nf_header_of (fcs did: Z) (h: nf_header) : frame_header :=
  {| fh_contentSize :=
       if (nh_fcs_flag h =? 0) && negb (nh_single h) then ZSTD_CONTENTSIZE_UNKNOWN else fcs;
     fh_windowSize := nh_window fcs h;
     fh_blockSizeMax := nh_max_block fcs h;
     fh_frameType := 0;
     fh_headerSize := Zlength (nh_bytes fcs did h);
     fh_dictID := did;
     fh_checksumFlag := zb (nh_checksum h) |}.

(* a window zstd can represent: Single_Segment, or Window_Log = 10 + Exponent at most ZSTD_WINDOWLOG_MAX (31) *)
Definition nh_wlog_ok (h: nf_header) : Prop :=
  nh_single h = true \/ 10 + nh_wd h / 8 <= ZSTD_WINDOWLOG_MAX.

(* ---------- helpers: lists of bytes ---------- *)

Lemma ff_Zlength_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

Lemma ff_Zlength_nonneg : forall (a: list Z), 0 <= Zlength a.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma ff_le_bytes_length : forall k v, length (le_bytes k v) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma ff_le_bytes_Zlength : forall k v, Zlength (le_bytes k v) = Z.of_nat k.
Proof. intros. rewrite Zlength_correct, ff_le_bytes_length. reflexivity. Qed.

Lemma ff_le_bytes_ok : forall k v, bytes_ok (le_bytes k v).
Proof.
  induction k; intros; cbn [le_bytes]; constructor.
  - unfold is_byte. apply Z.mod_pos_bound. lia.
  - apply IHk.
Qed.

Lemma ff_le_value_le_bytes : forall k v, le_value (le_bytes k v) = v mod 2 ^ (8 * Z.of_nat k).
Proof.
  induction k; intros; cbn [le_bytes le_value].
  - rewrite Z.mod_1_r. reflexivity.
  - rewrite IHk, Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite Z.rem_mul_r; [lia | lia | apply Z.pow_pos_nonneg; lia].
Qed.

Lemma ff_skipn_app : forall (a b: list Z) k, k = Zlength a -> skipn (Z.to_nat k) (a ++ b) = b.
Proof.
  intros a b k ->. rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

(* a field read right at the start of the bytes b, behind a *)
Lemma ff_le_field_at : forall (a b t: list Z) i k, i = Zlength a -> k = Zlength b ->
  le_field (a ++ b ++ t) i k = le_value b.
Proof.
  intros a b t i k -> ->. unfold le_field, slice. rewrite ff_skipn_app by reflexivity.
  rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  reflexivity.
Qed.

Lemma ff_byte_at_le_field : forall l i, 0 <= i -> byte_at l i = le_field l i 1.
Proof.
  intros l i Hi. unfold byte_at, le_field, slice. change (Z.to_nat 1) with 1%nat.
  rewrite <- (Nat.add_0_r (Z.to_nat i)) at 1. rewrite <- nth_skipn.
  destruct (skipn (Z.to_nat i) l); simpl; lia.
Qed.

Lemma ff_slice_length : forall (l: list Z) i k, 0 <= i -> 0 <= k -> i + k <= Zlength l ->
  Zlength (slice l i k) = k.
Proof.
  intros l i k Hi Hk H. unfold slice. rewrite Zlength_correct in *.
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma ff_slice_ok : forall (l: list Z) i k, bytes_ok l -> bytes_ok (slice l i k).
Proof.
  intros l i k H. unfold slice, bytes_ok in *.
  rewrite <- (firstn_skipn (Z.to_nat i) l) in H. apply Forall_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) l)) in H. apply Forall_app in H. apply H.
Qed.

Lemma ff_byte_at_ok : forall (l: list Z) i, bytes_ok l -> is_byte (byte_at l i).
Proof.
  intros l i H. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)).
  - eapply Forall_forall; [exact H | apply nth_In; auto].
  - rewrite nth_overflow by auto. unfold is_byte. lia.
Qed.

Lemma ff_repeat_ok : forall x k, is_byte x -> bytes_ok (repeat x k).
Proof. intros. unfold bytes_ok. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst. auto. Qed.

Lemma ff_bytes_ok_app : forall a b, bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros. apply Forall_app. auto. Qed.

(* ---------- helpers: the blocks ---------- *)

(* every block of the cut takes at most the bytes left, and ends inside the data *)
Lemma ff_block_size : forall mb n done b bl, 0 <= done <= n -> nf_blocks_ok mb n done (b :: bl) ->
  0 <= nb_size b /\ done + nb_size b <= n.
Proof.
  intros mb n done b bl Hd H. destruct H as (H0 & H1 & _).
  destruct (Z.eq_dec done n) as [E | E]; [rewrite H0 by auto; lia |].
  specialize (H1 ltac:(lia)). lia.
Qed.

Lemma ff_content_length : forall d mb done bl, 0 <= done <= Zlength d ->
  nf_blocks_ok mb (Zlength d) done bl -> Zlength (nf_content d done bl) = Zlength d - done.
Proof.
  intros d mb done bl. revert done. induction bl as [| b bl IH]; intros done Hd H; [destruct H |].
  pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  cbn [nf_content]. rewrite ff_Zlength_app.
  assert (Hb: Zlength (if nb_rle b then repeat (byte_at d done) (Z.to_nat (nb_size b))
                       else slice d done (nb_size b)) = nb_size b).
  { destruct (nb_rle b).
    - rewrite Zlength_correct, repeat_length. lia.
    - apply ff_slice_length; lia. }
  rewrite Hb. destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - cbn [nf_content]. change (Zlength (@nil Z)) with 0. lia.
  - destruct Hr as (_ & Hr). rewrite IH by (auto; lia). lia.
Qed.

Lemma ff_content_ok : forall d done bl, bytes_ok d -> bytes_ok (nf_content d done bl).
Proof.
  intros d done bl Hd. revert done. induction bl as [| b bl IH]; intros done; cbn [nf_content].
  - constructor.
  - apply ff_bytes_ok_app; auto. destruct (nb_rle b).
    + apply ff_repeat_ok, ff_byte_at_ok; auto.
    + apply ff_slice_ok; auto.
Qed.

Lemma ff_blocks_bytes_ok : forall d mb n done bl, bytes_ok d -> nf_blocks_ok mb n done bl ->
  bytes_ok (nf_blocks_bytes d done bl).
Proof.
  intros d mb n done bl Hd. revert done. induction bl as [| b bl IH]; intros done H; [destruct H |].
  cbn [nf_blocks_bytes]. destruct H as (_ & _ & _ & Hbyte & Hr).
  apply ff_bytes_ok_app; [apply ff_le_bytes_ok |]. apply ff_bytes_ok_app.
  - destruct (nb_rle b); [| apply ff_slice_ok; auto].
    constructor; [| constructor]. destruct (nb_size b =? 0); [exact Hbyte | apply ff_byte_at_ok; auto].
  - destruct bl as [| b' bl']; [constructor |]. destruct Hr as (_ & Hr). apply IH. exact Hr.
Qed.

(* each block takes 3 + 1 or 3 + its size bytes: from 3 to 4 per byte of data, plus 4 *)
Lemma ff_blocks_bytes_length : forall d mb done bl, 0 <= done <= Zlength d ->
  nf_blocks_ok mb (Zlength d) done bl ->
  3 <= Zlength (nf_blocks_bytes d done bl) <= 4 * (Zlength d - done) + 4.
Proof.
  intros d mb done bl. revert done. induction bl as [| b bl IH]; intros done Hd H; [destruct H |].
  pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  cbn [nf_blocks_bytes]. unfold nb_header. rewrite !ff_Zlength_app, ff_le_bytes_Zlength.
  assert (Hb: Zlength (if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
                       else slice d done (nb_size b)) = if nb_rle b then 1 else nb_size b).
  { destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. }
  rewrite Hb. destruct H as (_ & _ & _ & _ & Hr). change (Z.of_nat 3) with 3.
  destruct bl as [| b' bl'].
  - cbn [nf_blocks_bytes]. change (Zlength (@nil Z)) with 0.
    destruct (nb_rle b); lia.
  - destruct Hr as (Hpos & Hr). specialize (IH (done + nb_size b) ltac:(lia) Hr).
    destruct (nb_rle b); lia.
Qed.

Local Ltac ff_pw := change (2 ^ 1) with 2 in *; change (2 ^ 2) with 4 in *; change (2 ^ 3) with 8 in *; lia.

(* the Block_Header new_frame writes, read back *)
Lemma ff_block_props : forall last b t, 0 <= nb_size b < 2 ^ 21 ->
  block_props_of (nb_header last b ++ t) =
  {| bp_last := zb last; bp_type := zb (nb_rle b); bp_origSize := nb_size b |}.
Proof.
  intros last b t Hb. unfold nb_header.
  set (v := zb last + 2 * zb (nb_rle b) + 8 * nb_size b).
  assert (Hl: 0 <= zb last <= 1) by (destruct last; simpl; lia).
  assert (Hr: 0 <= zb (nb_rle b) <= 1) by (destruct (nb_rle b); simpl; lia).
  unfold block_props_of. rewrite <- (app_nil_l (le_bytes 3 v ++ t)).
  rewrite ff_le_field_at by (rewrite ?ff_le_bytes_Zlength; reflexivity).
  rewrite ff_le_value_le_bytes. change (2 ^ (8 * Z.of_nat 3)) with (2 ^ 24).
  rewrite Z.mod_small by (unfold v; change (2 ^ 24) with 16777216; change (2 ^ 21) with 2097152 in Hb; lia).
  unfold v. f_equal.
  - change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
    replace (zb last + 2 * zb (nb_rle b) + 8 * nb_size b) with
      (zb last + (zb (nb_rle b) + 4 * nb_size b) * 2 ^ 1) by ff_pw.
    rewrite Z.mod_add by ff_pw. apply Z.mod_small. ff_pw.
  - change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (zb last + 2 * zb (nb_rle b) + 8 * nb_size b) with
      (zb last + (zb (nb_rle b) + 4 * nb_size b) * 2 ^ 1) by ff_pw.
    rewrite Z.div_add by ff_pw. rewrite (Z.div_small (zb last)) by ff_pw.
    replace (0 + (zb (nb_rle b) + 4 * nb_size b)) with (zb (nb_rle b) + nb_size b * 2 ^ 2) by ff_pw.
    rewrite Z.mod_add by ff_pw. apply Z.mod_small. ff_pw.
  - rewrite Z.shiftr_div_pow2 by lia.
    replace (zb last + 2 * zb (nb_rle b) + 8 * nb_size b) with
      ((zb last + 2 * zb (nb_rle b)) + nb_size b * 2 ^ 3) by ff_pw.
    rewrite Z.div_add by ff_pw. rewrite Z.div_small by ff_pw. lia.
Qed.

Lemma ff_slice_mid : forall (a b t: list Z) i k, i = Zlength a -> k = Zlength b -> slice (a ++ b ++ t) i k = b.
Proof.
  intros a b t i k -> ->. unfold slice. rewrite ff_skipn_app by reflexivity.
  rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma ff_skipn_mid : forall (a b t: list Z) k, k = Zlength a + Zlength b -> skipn (Z.to_nat k) (a ++ b ++ t) = t.
Proof.
  intros a b t k ->. rewrite app_assoc. apply ff_skipn_app. rewrite ff_Zlength_app. reflexivity.
Qed.

(* a block of the cut is at most 128 KiB *)
Lemma ff_block_bound : forall mb n done b bl, 0 <= done <= n -> mb <= 131072 ->
  nf_blocks_ok mb n done (b :: bl) -> 0 <= nb_size b <= 131072 /\ done + nb_size b <= n.
Proof.
  intros mb n done b bl Hd Hmb H. pose proof (ff_block_size _ _ _ _ _ Hd H) as Hs.
  destruct H as (H0 & H1 & _). destruct (Z.eq_dec done n) as [E | E]; [rewrite H0 by auto; lia |].
  specialize (H1 ltac:(lia)). lia.
Qed.

(* ZSTD_findFrameSizeInfo's walk over the blocks, followed by anything *)
Lemma ff_blocks_size : forall d mb bl done fuel t, 0 <= done <= Zlength d -> mb <= 131072 ->
  nf_blocks_ok mb (Zlength d) done bl -> (length (nf_blocks_bytes d done bl) <= fuel)%nat ->
  blocks_size fuel (nf_blocks_bytes d done bl ++ t) =
    Some (Zlength (nf_blocks_bytes d done bl), Z.of_nat (length bl)).
Proof.
  intros d mb bl. induction bl as [| b bl IH]; intros done fuel t Hd Hmb H Hf; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  set (body := if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
               else slice d done (nb_size b)).
  assert (Hbody: Zlength body = if nb_rle b then 1 else nb_size b).
  { unfold body. destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. }
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes] in *. fold body in Hf |- *.
  set (rest := nf_blocks_bytes d (done + nb_size b) bl) in *.
  rewrite !length_app in Hf. destruct fuel as [| f]; [rewrite Zlength_correct in Hh3; lia |].
  rewrite <- !app_assoc. cbn [blocks_size]. unfold cblock_size.
  rewrite ff_block_props by lia. cbn [bp_type bp_last bp_origSize].
  rewrite !ff_Zlength_app, Hh3.
  pose proof (ff_Zlength_nonneg rest). pose proof (ff_Zlength_nonneg t). pose proof (ff_Zlength_nonneg body).
  unfold ZSTD_blockHeaderSize.
  rewrite (proj2 (Z.ltb_ge _ 3)) by lia.
  assert (Hc: (if zb (nb_rle b) =? 1 then Some 1 else if zb (nb_rle b) =? 3 then None else Some (nb_size b))
              = Some (Zlength body)) by (rewrite Hbody; destruct (nb_rle b); reflexivity).
  rewrite Hc. rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite ff_skipn_mid by (rewrite Hh3; reflexivity).
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - cbn [is_nil zb]. change (1 =? 1) with true. cbv iota.
    unfold rest. cbn [nf_blocks_bytes length]. rewrite Zlength_nil. f_equal. f_equal. lia.
  - cbn [is_nil zb]. change (0 =? 1) with false. cbv iota. destruct Hr as (Hpos & Hr).
    assert (Hf': (length rest <= f)%nat) by (rewrite Zlength_correct in Hh3; lia).
    unfold rest in *. rewrite (IH (done + nb_size b) f t ltac:(lia) Hmb Hr Hf').
    f_equal. f_equal; [lia |]. cbn [length]. lia.
Qed.

(* the comparisons of the block walk that lia decides *)
Local Ltac ff_cmp := repeat match goal with
  | |- context [?a <? ?b] => rewrite (proj2 (Z.ltb_ge a b)) by lia
  | |- context [?a >? ?b] => rewrite (Z.gtb_ltb a b)
  end.

(* the end of one step of the block walk: the last block, or the walk goes on with the next ones *)
Local Ltac ff_walk_end Hr Hrest :=
  let bl := match type of Hr with match ?bl with _ => _ end => bl end in
  destruct bl as [| b' bl']; cbn [is_nil zb Z.eqb Pos.eqb]; cbv iota;
  [ cbn [nf_content nf_blocks_bytes]; rewrite !app_nil_r, Zlength_nil; f_equal; f_equal; lia
  | rewrite Hrest by discriminate; rewrite !app_assoc; f_equal; f_equal; lia ].

(* an empty RLE block's byte is never repeated *)
Lemma ff_repeat_rle : forall (x y: Z) k, repeat (if k =? 0 then x else y) (Z.to_nat k) = repeat y (Z.to_nat k).
Proof. intros x y k. destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; subst; reflexivity | reflexivity]. Qed.

(* ZSTD_decompressFrame's walk over the blocks (with or without the dictionary window rule: Raw and RLE
   blocks do not reference the history), followed by anything: the blocks decode to the changed data *)
Lemma ff_decode_blocks : forall (w: bool) d mb bsm wsize st hist bl done out fuel t,
  0 <= done <= Zlength d -> 0 <= mb <= 131072 -> mb <= bsm -> (done < Zlength d -> 1 <= mb) ->
  nf_blocks_ok mb (Zlength d) done bl -> (length (nf_blocks_bytes d done bl) <= fuel)%nat ->
  (if w then decode_blocks_w else decode_blocks) fuel st hist (nf_blocks_bytes d done bl ++ t) out bsm wsize =
    Some (out ++ nf_content d done bl, Zlength (nf_blocks_bytes d done bl)).
Proof.
  intros w d mb bsm wsize st hist bl.
  induction bl as [| b bl IH]; intros done out fuel t Hd Hmb Hbsm H1 H Hf; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd (proj2 Hmb) H) as Hs.
  assert (Hbs: nb_size b <= bsm).
  { destruct H as (H0 & H2 & _). destruct (Z.eq_dec done (Zlength d)) as [E | E]; [rewrite H0 by auto; lia |].
    specialize (H2 ltac:(lia)). specialize (H1 ltac:(lia)). lia. }
  assert (Hrle: nb_rle b = true -> 1 <= bsm) by (destruct H as (_ & _ & H3 & _); intros E; specialize (H3 E); lia).
  destruct H as (_ & _ & _ & _ & Hr).
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes nf_content] in *.
  set (rest := nf_blocks_bytes d (done + nb_size b) bl) in *.
  rewrite !length_app in Hf. destruct fuel as [| f]; [rewrite Zlength_correct in Hh3; lia |].
  pose proof (ff_Zlength_nonneg rest). pose proof (ff_Zlength_nonneg t).
  assert (Hrest: forall out', bl <> [] ->
    (if w then decode_blocks_w else decode_blocks) f st hist (rest ++ t) out' bsm wsize =
      Some (out' ++ nf_content d (done + nb_size b) bl, Zlength rest)).
  { intros out' Hne. destruct bl as [| b' bl']; [congruence |]. destruct Hr as (Hpos & Hr).
    apply IH; auto; try lia. rewrite Zlength_correct in Hh3. fold rest. lia. }
  rewrite <- !app_assoc.
  destruct w; cbn [decode_blocks decode_blocks_w] in Hrest |- *; unfold cblock_size;
    rewrite ff_block_props by lia; cbn [bp_type bp_last bp_origSize];
    rewrite !ff_Zlength_app, Hh3; unfold ZSTD_blockHeaderSize;
    destruct (nb_rle b) eqn:Er; cbn [zb]; cbn [Z.eqb Pos.eqb]; cbv iota.
  all: try (set (x := if nb_size b =? 0 then nb_byte b else byte_at d done) in *;
            change (Zlength [x]) with 1 in *).
  all: try (assert (Hbl: Zlength (slice d done (nb_size b)) = nb_size b) by (apply ff_slice_length; lia);
            rewrite Hbl).
  all: ff_cmp; cbn [orb]; cbv iota.
  all: try (rewrite ff_slice_mid by (rewrite ?Hh3, ?Hbl; reflexivity)).
  all: rewrite ff_skipn_mid by (rewrite Hh3, ?Hbl; reflexivity).
  all: try (change (byte_at [x] 0) with x; unfold x; rewrite ff_repeat_rle).
  all: ff_walk_end Hr Hrest.
Qed.

(* ---------- helpers: the header ---------- *)

Lemma ff_flag_cases : forall x, 0 <= x <= 3 -> x = 0 \/ x = 1 \/ x = 2 \/ x = 3.
Proof. intros. lia. Qed.

Lemma ff_field_sizes : forall fcs maxw did h, nh_ok fcs maxw did h ->
  0 <= nh_did_size h <= 4 /\ 0 <= nh_fcs_size h <= 8.
Proof.
  intros fcs maxw did h (Hf & _ & _ & _ & _ & _ & Hd & _).
  unfold nh_did_size, nh_fcs_size.
  destruct (ff_flag_cases _ Hf) as [E | [E | [E | E]]]; rewrite E;
  destruct (ff_flag_cases _ Hd) as [E' | [E' | [E' | E']]]; rewrite E';
  destruct (nh_single h); simpl; lia.
Qed.

(* a Single_Segment header always has a Frame_Content_Size field *)
Lemma ff_fcs_size_single : forall fcs maxw did h, nh_ok fcs maxw did h ->
  0 <= zb (nh_single h) <= nh_fcs_size h.
Proof.
  intros fcs maxw did h (Hf & _). unfold nh_fcs_size.
  destruct (ff_flag_cases _ Hf) as [E | [E | [E | E]]]; rewrite E; destruct (nh_single h); simpl; lia.
Qed.

Lemma ff_nh_bytes_Zlength : forall fcs maxw did h, nh_ok fcs maxw did h ->
  Zlength (nh_bytes fcs did h) = 6 - zb (nh_single h) + nh_did_size h + nh_fcs_size h.
Proof.
  intros fcs maxw did h H. pose proof (ff_field_sizes _ _ _ _ H) as Hs.
  unfold nh_bytes. rewrite !ff_Zlength_app, !ff_le_bytes_Zlength, !Z2Nat.id by lia.
  destruct (nh_single h); unfold zb; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

(* the Frame_Header_Descriptor new_frame writes, read back bit by bit (finitely many cases) *)
Lemma ff_fhd_facts : forall h, 0 <= nh_fcs_flag h <= 3 -> In (nh_bits h) [0; 4; 16; 20] ->
  0 <= nh_did_flag h <= 3 ->
  0 <= nh_fhd h < 256 /\
  Z.land (nh_fhd h) 3 = nh_did_flag h /\
  Z.land (Z.shiftr (nh_fhd h) 5) 1 = zb (nh_single h) /\
  Z.shiftr (nh_fhd h) 6 = nh_fcs_flag h /\
  Z.land (nh_fhd h) 8 = 0 /\
  Z.land (Z.shiftr (nh_fhd h) 2) 1 = zb (nh_checksum h) /\
  nth (Z.to_nat (Z.land (nh_fhd h) 3)) [0; 1; 2; 4] 0 = nh_did_size h /\
  fhd_header_size (nh_fhd h) = 6 - zb (nh_single h) + nh_did_size h + nh_fcs_size h.
Proof.
  intros [f sg b df wd] Hf Hb Hd. cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd] in *.
  unfold nh_fhd, nh_checksum, nh_did_size, nh_fcs_size, fhd_header_size;
    cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd].
  destruct (ff_flag_cases _ Hf) as [-> | [-> | [-> | ->]]];
  destruct (ff_flag_cases _ Hd) as [-> | [-> | [-> | ->]]];
  destruct Hb as [<- | [<- | [<- | [<- | []]]]]; destruct sg; vm_compute; repeat split; discriminate.
Qed.

(* the header's fields, read back *)
Lemma ff_nh_read : forall fcs maxw did h t, nh_ok fcs maxw did h -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  le_field (nh_bytes fcs did h ++ t) 0 4 = ZSTD_MAGICNUMBER /\
  byte_at (nh_bytes fcs did h ++ t) 4 = nh_fhd h /\
  (nh_single h = false -> byte_at (nh_bytes fcs did h ++ t) 5 = nh_wd h) /\
  le_field (nh_bytes fcs did h ++ t) (6 - zb (nh_single h)) (nh_did_size h) = did /\
  (nh_fcs_flag h <> 0 \/ nh_single h = true ->
   le_field (nh_bytes fcs did h ++ t) (6 - zb (nh_single h) + nh_did_size h) (nh_fcs_size h) =
     nh_fcs_value fcs h).
Proof.
  intros fcs maxw did h t H Hfcs Hdid.
  pose proof (ff_field_sizes _ _ _ _ H) as [Hds Hfs].
  destruct H as (Hf & Hf0 & Hf1 & Hf2 & _ & _ & Hd & Hd0 & Hd1 & Hd2 & Hwd & _).
  unfold nh_bytes.
  change (le_bytes 4 ZSTD_MAGICNUMBER) with [40; 181; 47; 253].
  set (W := if nh_single h then [] else [nh_wd h]).
  set (D := le_bytes (Z.to_nat (nh_did_size h)) did).
  set (F := le_bytes (Z.to_nat (nh_fcs_size h)) (nh_fcs_value fcs h)).
  assert (HW: Zlength ([40; 181; 47; 253] ++ [nh_fhd h] ++ W) = 6 - zb (nh_single h)).
  { unfold W; destruct (nh_single h); reflexivity. }
  assert (HD: Zlength D = nh_did_size h) by (unfold D; rewrite ff_le_bytes_Zlength; lia).
  assert (HF: Zlength F = nh_fcs_size h) by (unfold F; rewrite ff_le_bytes_Zlength; lia).
  split; [reflexivity |]. split; [reflexivity |].
  split; [intros E; unfold W; rewrite E; reflexivity |].
  split.
  - replace (([40; 181; 47; 253] ++ [nh_fhd h] ++ W ++ D ++ F) ++ t)
      with (([40; 181; 47; 253] ++ [nh_fhd h] ++ W) ++ D ++ (F ++ t)) by (rewrite <- !app_assoc; reflexivity).
    rewrite ff_le_field_at by (symmetry; auto).
    unfold D. rewrite ff_le_value_le_bytes, Z2Nat.id by lia. unfold nh_did_size in *.
    apply Z.mod_small.
    destruct (ff_flag_cases _ Hd) as [E | [E | [E | E]]]; rewrite E in *; simpl; lia.
  - intros Hsf. replace (([40; 181; 47; 253] ++ [nh_fhd h] ++ W ++ D ++ F) ++ t)
      with (([40; 181; 47; 253] ++ [nh_fhd h] ++ W ++ D) ++ F ++ t) by (rewrite <- !app_assoc; reflexivity).
    rewrite ff_le_field_at; [| | lia].
    2: { replace ([40; 181; 47; 253] ++ [nh_fhd h] ++ W ++ D) with (([40; 181; 47; 253] ++ [nh_fhd h] ++ W) ++ D)
           by (rewrite <- !app_assoc; reflexivity).
         rewrite ff_Zlength_app. lia. }
    unfold F. rewrite ff_le_value_le_bytes, Z2Nat.id by lia. unfold nh_fcs_size, nh_fcs_value in *.
    apply Z.mod_small.
    destruct (ff_flag_cases _ Hf) as [E | [E | [E | E]]]; rewrite E in *; simpl.
    + destruct (nh_single h); [simpl; lia | destruct Hsf; [lia | discriminate]].
    + lia.
    + lia.
    + lia.
Qed.

(* ---------- sizes, bytes ---------- *)

Lemma nf_data_length : forall d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c -> Zlength (nf_data d c) = Zlength d.
Proof.
  intros d fcs maxw did c [_ H]. unfold nf_data.
  pose proof (ff_Zlength_nonneg d).
  rewrite (ff_content_length d _ 0 _ ltac:(lia) H). lia.
Qed.

Lemma nf_data_ok : forall d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> bytes_ok (nf_data d c).
Proof. intros. apply ff_content_ok. auto. Qed.

Lemma nf_bytes_ok : forall d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> bytes_ok (nf_bytes d fcs did c).
Proof.
  intros d fcs maxw did c [Hh Hb] Hd. unfold nf_bytes.
  apply ff_bytes_ok_app; [| apply ff_bytes_ok_app].
  - destruct Hh as (Hf & _ & _ & _ & _ & Hbits & Hdf & _ & _ & _ & Hwd & _).
    destruct (ff_fhd_facts _ Hf Hbits Hdf) as (Hfhd & _).
    unfold nh_bytes. apply ff_bytes_ok_app; [apply ff_le_bytes_ok |].
    apply ff_bytes_ok_app; [constructor; [exact Hfhd | constructor] |].
    apply ff_bytes_ok_app; [destruct (nh_single (nc_hdr c));
      [apply Forall_nil | apply Forall_cons; [unfold is_byte; lia | apply Forall_nil]] |].
    apply ff_bytes_ok_app; apply ff_le_bytes_ok.
  - eapply ff_blocks_bytes_ok; eauto.
  - unfold nf_checksum. destruct (nh_checksum (nc_hdr c)); [apply ff_le_bytes_ok | constructor].
Qed.

(* the frame takes 9 to 26 + 4 n bytes (new_frame allocates 26 + 4 n) *)
Lemma nf_bytes_length : forall d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c ->
  9 <= Zlength (nf_bytes d fcs did c) <= 26 + 4 * Zlength d.
Proof.
  intros d fcs maxw did c [Hh Hb]. unfold nf_bytes.
  pose proof (ff_Zlength_nonneg d) as Hn.
  rewrite !ff_Zlength_app, (ff_nh_bytes_Zlength _ _ _ _ Hh).
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hs.
  pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as Hbl.
  assert (Hck: 0 <= Zlength (nf_checksum d c) <= 4).
  { unfold nf_checksum. destruct (nh_checksum (nc_hdr c)); [rewrite ff_le_bytes_Zlength; simpl; lia | rewrite Zlength_nil; lia]. }
  lia.
Qed.

(* a window limit below 2^32 (ONE_CALL_WINDOW = 2^31, STREAM_WINDOW = 2^27) keeps Window_Log representable *)
Lemma nf_wlog_ok : forall fcs maxw did h,
  nh_ok fcs maxw did h -> maxw < 2 ^ 32 -> nh_wlog_ok h.
Proof.
  intros fcs maxw did h Hh Hm. unfold nh_wlog_ok, ZSTD_WINDOWLOG_MAX.
  destruct (nh_single h) eqn:Es; [left; reflexivity | right].
  destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwd & Hw).
  unfold nh_window in Hw. rewrite Es in Hw.
  destruct (Z.le_gt_cases (10 + nh_wd h / 8) 31) as [L | L]; [exact L | exfalso].
  assert (2 ^ 32 <= 2 ^ (10 + nh_wd h / 8)) by (apply Z.pow_le_mono_r; lia).
  assert (0 <= 2 ^ (10 + nh_wd h / 8) / 8 * (nh_wd h mod 8)).
  { apply Z.mul_nonneg_nonneg; [apply Z.div_pos | apply Z.mod_pos_bound]; lia. }
  lia.
Qed.

(* ---------- what zstd reads ---------- *)

(* the header alone, followed by anything *)
Lemma ff_get_frame_header : forall fcs maxw did h t,
  nh_ok fcs maxw did h -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> nh_wlog_ok h ->
  get_frame_header (nh_bytes fcs did h ++ t) = FH_ok (nf_header_of fcs did h).
Proof.
  intros fcs maxw did h t Hh Hfcs Hdid Hw.
  destruct (ff_nh_read fcs maxw did h t Hh Hfcs Hdid) as (Hm & H4 & H5 & Hd & Hf).
  pose proof Hh as (Hf03 & Hf0 & Hf1 & Hf2 & Hsg & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (Hfb & Hd3 & Hs5 & Hf6 & H8 & Hck & Hnth & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  unfold get_frame_header. cbv zeta.
  set (s := nh_bytes fcs did h ++ t) in *.
  assert (Hs: Zlength s = Zlength (nh_bytes fcs did h) + Zlength t) by apply ff_Zlength_app.
  pose proof (ff_Zlength_nonneg t).
  assert (Hzb: 0 <= zb (nh_single h) <= 1) by (destruct (nh_single h); simpl; lia).
  rewrite H4, Hm, Hhs, H8, Hnth, Hck, Hs5, Hf6.
  replace (5 + (1 - zb (nh_single h))) with (6 - zb (nh_single h)) by lia. rewrite Hd.
  rewrite (proj2 (Z.ltb_ge (Zlength s) 5)) by lia.
  rewrite (proj2 (Z.ltb_ge (Zlength s) (6 - zb (nh_single h) + nh_did_size h + nh_fcs_size h))) by lia.
  rewrite Z.eqb_refl, <- Hlen. cbn [negb andb].
  unfold nf_header_of, nh_max_block, nh_window, nh_fcs_size, nh_fcs_value in *.
  destruct (nh_single h) eqn:Es; cbn [zb] in *.
  - change (1 =? 0) with false. change (1 =? 1) with true. cbn [andb negb].
    destruct (ff_flag_cases _ Hf03) as [E | [E | [E | E]]]; rewrite E in *; cbn [Z.eqb Pos.eqb andb] in *;
      change (2 ^ 1) with 2 in *; change (2 ^ 2) with 4 in *; change (2 ^ 3) with 8 in *.
    + rewrite ff_byte_at_le_field by lia. rewrite Hf by auto. reflexivity.
    + rewrite Hf by (left; discriminate). replace (fcs - 256 + 256) with fcs by lia. reflexivity.
    + rewrite Hf by (left; discriminate). reflexivity.
    + rewrite Hf by (left; discriminate). reflexivity.
  - change (0 =? 0) with true. change (0 =? 1) with false. cbn [andb negb].
    rewrite H5 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold nh_wlog_ok in Hw. rewrite Es in Hw. destruct Hw as [Hw | Hw]; [discriminate |].
    unfold ZSTD_WINDOWLOG_ABSOLUTEMIN. rewrite Z.add_comm.
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by (unfold ZSTD_WINDOWLOG_MAX in *; lia). cbn [andb].
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    rewrite Bool.andb_true_r.
    destruct (ff_flag_cases _ Hf03) as [E | [E | [E | E]]]; rewrite E in *; cbn [Z.eqb Pos.eqb] in *;
      change (2 ^ 1) with 2 in *; change (2 ^ 2) with 4 in *; change (2 ^ 3) with 8 in *.
    + reflexivity.
    + rewrite Hf by (left; discriminate). replace (fcs - 256 + 256) with fcs by lia. reflexivity.
    + rewrite Hf by (left; discriminate). reflexivity.
    + rewrite Hf by (left; discriminate). reflexivity.
Qed.

(* F followed by anything: header, blocks, checksum, the rest *)
Lemma ff_frame_split : forall d fcs did c rest,
  nf_bytes d fcs did c ++ rest =
  nh_bytes fcs did (nc_hdr c) ++ nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c ++ rest.
Proof. intros. unfold nf_bytes. rewrite <- !app_assoc. reflexivity. Qed.

Lemma ff_checksum_length : forall d c, Zlength (nf_checksum d c) = 4 * zb (nh_checksum (nc_hdr c)).
Proof.
  intros. unfold nf_checksum. destruct (nh_checksum (nc_hdr c)); [rewrite ff_le_bytes_Zlength |]; reflexivity.
Qed.

(* ZSTD_getFrameHeader *)
Theorem nf_get_frame_header : forall d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> nh_wlog_ok (nc_hdr c) ->
  get_frame_header (nf_bytes d fcs did c ++ rest) = FH_ok (nf_header_of fcs did (nc_hdr c)).
Proof.
  intros d fcs maxw did c rest [Hh _] Hfcs Hdid Hw. rewrite ff_frame_split.
  apply (ff_get_frame_header fcs maxw); auto.
Qed.

(* ZSTD_getFrameContentSize *)
Corollary nf_frame_content_size : forall d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> nh_wlog_ok (nc_hdr c) ->
  frame_content_size (nf_bytes d fcs did c ++ rest) = fh_contentSize (nf_header_of fcs did (nc_hdr c)).
Proof.
  intros. unfold frame_content_size. erewrite nf_get_frame_header by eauto. reflexivity.
Qed.

(* ZSTD_findFrameCompressedSize *)
Theorem nf_frame_compressed_size : forall d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> nh_wlog_ok (nc_hdr c) ->
  frame_compressed_size (nf_bytes d fcs did c ++ rest) = Some (Zlength (nf_bytes d fcs did c)).
Proof.
  intros d fcs maxw did c rest Hok Hfcs Hdid Hw.
  pose proof (nf_get_frame_header d fcs maxw did c rest Hok Hfcs Hdid Hw) as Hg.
  destruct Hok as [Hh Hb].
  destruct (ff_nh_read fcs maxw did (nc_hdr c) (nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c ++ rest)
              Hh Hfcs Hdid) as (Hm & _).
  pose proof (ff_Zlength_nonneg d) as Hn.
  assert (Hmb: nh_max_block fcs (nc_hdr c) <= 131072) by apply Z.le_min_r.
  unfold frame_compressed_size. rewrite Hg. rewrite ff_frame_split in *. rewrite Hm.
  change (is_skippable_magic ZSTD_MAGICNUMBER) with false. rewrite Bool.andb_false_r.
  cbn [nf_header_of fh_headerSize fh_checksumFlag].
  rewrite ff_skipn_app by reflexivity.
  rewrite ff_blocks_size with (mb := nh_max_block fcs (nc_hdr c)) by (auto; lia || (rewrite length_app; lia)).
  unfold nf_bytes. rewrite !ff_Zlength_app, ff_checksum_length.
  pose proof (ff_Zlength_nonneg rest).
  destruct (nh_checksum (nc_hdr c)); cbn [zb Z.eqb Pos.eqb]; cbv iota.
  - rewrite (proj2 (Z.ltb_ge _ 4)) by lia. f_equal. lia.
  - f_equal. lia.
Qed.

(* ZSTD_decompressFrame, any parameters with the magic number and the default (or a larger) block maximum:
   the frame decodes to the data new_frame left (nf_data), when the window is within the limit wlim, the
   dictionary is the frame's (or the frame names none), and the declared content size is the data's (or the
   header declares none). *)
Theorem nf_decode_frame_m : forall md dm wlim d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  nh_wlog_ok (nc_hdr c) ->
  md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  nh_window fcs (nc_hdr c) <= wlim ->
  (did = 0 \/ did = dm_id dm) ->
  (fcs = Zlength d \/ (nh_fcs_flag (nc_hdr c) = 0 /\ nh_single (nc_hdr c) = false)) ->
  decode_frame_m md dm wlim (nf_bytes d fcs did c ++ rest) =
  FOk (nf_data d c) (Zlength (nf_bytes d fcs did c)).
Proof.
  intros md dm wlim d fcs maxw did c rest Hok Hd Hfcs Hdid Hw Hmg Hbmax Hwl Hdm Hcs.
  pose proof (nf_get_frame_header d fcs maxw did c rest Hok Hfcs Hdid Hw) as Hg.
  pose proof (nf_data_length d fcs maxw did c Hok) as Hdl.
  destruct Hok as [Hh Hb].
  set (h := nc_hdr c) in *.
  set (B := nf_blocks_bytes d 0 (nc_blocks c)) in *.
  set (K := nf_checksum d c) in *.
  destruct (ff_nh_read fcs maxw did h (B ++ K ++ rest) Hh Hfcs Hdid) as (Hm & H4 & H5 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (Hfb & _ & Hs5 & _ & H8 & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
  pose proof (ff_Zlength_nonneg d) as Hn.
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as HB.
  pose proof (ff_Zlength_nonneg rest) as Hr.
  assert (HK: Zlength K = 4 * zb (nh_checksum h)) by apply ff_checksum_length.
  assert (Hzb: 0 <= zb (nh_single h) <= 1) by (destruct (nh_single h); simpl; lia).
  assert (Hzc: 0 <= zb (nh_checksum h) <= 1) by (destruct (nh_checksum h); simpl; lia).
  unfold decode_frame_m. rewrite Hmg. cbv iota beta zeta.
  rewrite ff_frame_split in *. fold h B K in Hg |- *.
  set (s := nh_bytes fcs did h ++ B ++ K ++ rest) in *.
  assert (Hs: Zlength s = Zlength (nh_bytes fcs did h) + Zlength B + Zlength K + Zlength rest)
    by (unfold s; rewrite !ff_Zlength_app; lia).
  change (4 - 0) with 4. change (5 - 0) with 5.
  rewrite H4, Hm, Hhs, H8, Hs5, Z.eqb_refl, <- Hlen. fold B in HB.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
  rewrite (proj2 (Z.ltb_ge (Zlength s) (6 - 0 + 3))) by lia.
  rewrite (proj2 (Z.ltb_ge (Zlength s) (Zlength (nh_bytes fcs did h) - 0 + 3))) by lia.
  change (0 =? 0) with true. cbn [negb andb].
  (* the window *)
  assert (Hwd: 0 <= nh_wd h) by (destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); lia).
  assert (Hwin: negb (zb (nh_single h) =? 1) &&
                (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX) = false).
  { destruct (nh_single h) eqn:Es; [reflexivity |].
    rewrite H5 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold nh_wlog_ok in Hw. rewrite Es in Hw. destruct Hw as [Hw | Hw]; [discriminate |].
    cbn [zb]. change (0 =? 1) with false. cbn [negb andb].
    rewrite Z.gtb_ltb. apply Z.ltb_ge. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN. lia. }
  rewrite Hwin.
  assert (Hwin0: 0 <= nh_window fcs h /\ (0 < Zlength d -> 1 <= nh_window fcs h)).
  { unfold nh_window. destruct (nh_single h) eqn:Es.
    - split; [lia |]. destruct Hcs as [-> | [_ E]]; [lia | discriminate].
    - assert (1 <= 2 ^ (10 + nh_wd h / 8)).
      { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; [lia |]. pose proof (Z.div_pos (nh_wd h) 8). lia. }
      assert (0 <= 2 ^ (10 + nh_wd h / 8) / 8 * (nh_wd h mod 8)).
      { apply Z.mul_nonneg_nonneg; [apply Z.div_pos | apply Z.mod_pos_bound]; lia. }
      lia. }
  change (get_frame_header_m false s) with (get_frame_header s). rewrite Hg.
  cbn [nf_header_of fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize
       fh_checksumFlag].
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge wlim _)) by lia. change (0 =? 0) with true. cbn [negb andb].
  (* the dictionary *)
  assert (Hdd: negb (did =? 0) && negb (did =? dm_id dm) = false).
  { destruct Hdm as [-> | ->]; [reflexivity | rewrite Z.eqb_refl, Bool.andb_false_r; reflexivity]. }
  rewrite Hdd.
  (* the blocks *)
  unfold s at 1 2. rewrite ff_skipn_app by reflexivity.
  rewrite Z.min_l by (unfold nh_max_block; unfold ZSTD_BLOCKSIZE_MAX in Hbmax; lia).
  unfold B. rewrite ff_decode_blocks with (mb := nh_max_block fcs h);
    [| lia | unfold nh_max_block; lia | lia | unfold nh_max_block; lia | exact Hb | rewrite length_app; lia].
  fold B. rewrite app_nil_l. change (nf_content d 0 (nc_blocks c)) with (nf_data d c).
  (* the content size *)
  assert (Hcsz: negb ((if (nh_fcs_flag h =? 0) && negb (nh_single h) then ZSTD_CONTENTSIZE_UNKNOWN else fcs)
                      =? ZSTD_CONTENTSIZE_UNKNOWN) &&
                negb (Zlength (nf_data d c) =?
                      (if (nh_fcs_flag h =? 0) && negb (nh_single h) then ZSTD_CONTENTSIZE_UNKNOWN else fcs))
                = false).
  { destruct Hcs as [-> | [E1 E2]].
    - destruct ((nh_fcs_flag h =? 0) && negb (nh_single h)).
      + rewrite Z.eqb_refl. reflexivity.
      + rewrite Hdl, Z.eqb_refl, Bool.andb_false_r. reflexivity.
    - rewrite E1, E2. cbn [Z.eqb negb andb]. rewrite Z.eqb_refl. reflexivity. }
  rewrite Hcsz.
  (* the checksum *)
  assert (HF: Zlength (nf_bytes d fcs did c) = Zlength (nh_bytes fcs did h) + Zlength B + Zlength K).
  { unfold nf_bytes. fold h B K. rewrite !ff_Zlength_app. lia. }
  rewrite HF.
  destruct (nh_checksum h) eqn:Eck; cbn [zb] in *.
  - change (1 =? 1) with true. cbv iota.
    rewrite (proj2 (Z.ltb_ge _ 4)) by lia.
    unfold s. rewrite app_assoc.
    rewrite ff_le_field_at by (rewrite ?ff_Zlength_app; lia).
    unfold K, nf_checksum. fold h. rewrite Eck, ff_le_value_le_bytes. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite Z.eqb_refl, Bool.andb_false_r. rewrite ff_le_bytes_Zlength. reflexivity.
  - change (0 =? 1) with false. cbv iota. f_equal. lia.
Qed.
