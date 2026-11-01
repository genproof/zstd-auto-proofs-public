(* Subtree H: the loops over frames.  Prove each body against H_G (HSpecs.v); helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

(* ---------- ranges of the model (copied from body_H_fsi.v, prefixed lp_) ---------- *)

Lemma lp_win_ok_len: forall sh N c off n s, win_ok sh N c off n s ->
  0 <= n <= 2 ^ 63 - 1 /\ 0 <= off /\ off + n <= N /\ Zlength s = n /\ Zlength c = N.
Proof. intros. destruct H as [? [? [? [? [? [? ?]]]]]]. subst. pose proof (Zlength_nonneg s). lia. Qed.

Lemma lp_le_value_rng: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Zlength l).
Proof.
  intros l H. induction H; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons.
    rewrite <- Z.add_1_r, Z.mul_add_distr_l, Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    unfold is_byte in H. change (2^(8*1)) with 256. nia.
Qed.

Lemma lp_le_field_rng: forall s i k, bytes_ok s -> 0 <= k -> 0 <= le_field s i k < 2 ^ (8 * k).
Proof.
  intros s i k H Hk. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply Forall_firstn. apply Forall_skipn. auto. }
  pose proof (lp_le_value_rng _ Hb).
  assert (Zlength (firstn (Z.to_nat k) (skipn (Z.to_nat i) s)) <= k).
  { rewrite Zlength_correct, firstn_length. lia. }
  split; [lia|]. eapply Z.lt_le_trans; [apply H0|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lp_skipn_sublist_Z: forall (l: list Z) k, 0 <= k <= Zlength l ->
  skipn (Z.to_nat k) l = sublist k (Zlength l) l.
Proof.
  intros l k Hk. unfold sublist. rewrite firstn_all2; auto.
  rewrite Zlength_correct, Nat2Z.id. lia.
Qed.

Lemma lp_bytes_ok_skipn: forall n l, bytes_ok l -> bytes_ok (skipn n l).
Proof. intros. unfold bytes_ok in *. apply Forall_skipn. auto. Qed.

Lemma lp_cblock_size_nonneg: forall l c, bytes_ok l -> cblock_size l = Some c -> 3 <= Zlength l /\ 0 <= c.
Proof.
  intros l c Hb H. unfold cblock_size in H. unfold ZSTD_blockHeaderSize in H.
  destruct (Zlength l <? 3) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
  destruct (bp_type (block_props_of l) =? 1); [inversion H; lia|].
  destruct (bp_type (block_props_of l) =? 3); [discriminate|]. inversion H; subst.
  split; auto. unfold block_props_of; simpl. apply Z.shiftr_nonneg.
  apply (lp_le_field_rng l 0 3 Hb); lia.
Qed.

Lemma lp_byte_at_rng: forall s i, bytes_ok s -> 0 <= byte_at s i < 256.
Proof.
  intros s i Hb. unfold byte_at. destruct (nth_in_or_default (Z.to_nat i) s 0) as [Hin|Heq].
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb in Hin. unfold is_byte in Hin. lia.
  - rewrite Heq. lia.
Qed.

Lemma lp_land1_rng: forall x, 0 <= Z.land x 1 <= 1.
Proof.
  intros. replace (Z.land x 1) with (Z.land x (Z.ones 1)) by reflexivity. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2^1) ltac:(lia)). change (2^1) with 2 in *. lia.
Qed.

Lemma lp_nth4_rng: forall n a b c d, 0 <= a <= 8 -> 0 <= b <= 8 -> 0 <= c <= 8 -> 0 <= d <= 8 ->
  0 <= nth n [a; b; c; d] 0 <= 8.
Proof. intros. destruct n as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. Qed.

Lemma lp_fhd_header_size_rng: forall fhd, 5 <= fhd_header_size fhd <= 18.
Proof.
  intros. unfold fhd_header_size. pose proof (lp_land1_rng (Z.shiftr fhd 5)).
  assert (0 <= nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0 <= 4).
  { destruct (Z.to_nat _) as [|[|[|[|]]]]; simpl; try lia. destruct n; lia. }
  assert (0 <= nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0 <= 8) by (apply lp_nth4_rng; lia).
  set (a := nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) in *. clearbody a.
  destruct (Z.shiftr fhd 6 =? 0) eqn:E6.
  - apply Z.eqb_eq in E6. rewrite E6. change (nth (Z.to_nat 0) [0; 2; 4; 8] 0) with 0.
    destruct (_ && _)%bool; lia.
  - rewrite andb_false_r. lia.
Qed.

Lemma lp_fcs_rng: forall s p (A B C D: bool), bytes_ok s ->
  0 <= (if A then (if B then byte_at s p else ZSTD_CONTENTSIZE_UNKNOWN)
        else (if C then le_field s p 2 + 256 else if D then le_field s p 4 else le_field s p 8))
    <= Int64.max_unsigned.
Proof.
  intros s p A B C D Hb.
  pose proof (lp_byte_at_rng s p Hb). pose proof (lp_le_field_rng s p 2 Hb ltac:(lia)).
  pose proof (lp_le_field_rng s p 4 Hb ltac:(lia)). pose proof (lp_le_field_rng s p 8 Hb ltac:(lia)).
  unfold ZSTD_CONTENTSIZE_UNKNOWN. destruct A, B, C, D; simpl in *; rep_lia.
Qed.

Lemma lp_gfh_more: forall s k, get_frame_header s = FH_more k -> 5 <= k <= 18.
Proof.
  intros s k H. unfold get_frame_header in H.
  destruct (Zlength s <? 5).
  { destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; inversion H; lia. }
  destruct (negb _).
  { destruct (is_skippable_magic _); [|discriminate]. destruct (_ <? _); inversion H. unfold ZSTD_SKIPPABLEHEADERSIZE; lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _).
  { inversion H. apply lp_fhd_header_size_rng. }
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; discriminate.
Qed.

Lemma lp_gfh_ok: forall s h, bytes_ok s -> get_frame_header s = FH_ok h ->
  0 <= fh_headerSize h <= Zlength s /\ fh_headerSize h <= 18 /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
  0 <= fh_contentSize h <= Int64.max_unsigned /\ 0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  intros s h Hb H. unfold get_frame_header in H.
  destruct (Zlength s <? 5) eqn:E5.
  { destruct (Zlength s >? 0); [destruct (_ && _)%bool|]; discriminate. }
  apply Z.ltb_ge in E5.
  destruct (negb _).
  { destruct (is_skippable_magic _); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|].
    apply Z.ltb_ge in E8. inversion H; subst; clear H. simpl.
    pose proof (lp_le_field_rng s 4 4 Hb ltac:(lia)).
    unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_BLOCKSIZE_MAX in *. rep_lia. }
  cbv zeta in H. destruct (Zlength s <? fhd_header_size _) eqn:Ef; [discriminate|].
  apply Z.ltb_ge in Ef.
  destruct (negb _); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
  inversion H; subst; clear H. simpl.
  pose proof (lp_fhd_header_size_rng (byte_at s 4)).
  pose proof (lp_land1_rng (Z.shiftr (byte_at s 4) 2)).
  pose proof (lp_byte_at_rng s 5 Hb) as H5.
  match goal with |- context [if ?A then (if ?B then byte_at s ?p else ZSTD_CONTENTSIZE_UNKNOWN)
                             else (if ?C then le_field s ?p 2 + 256 else if ?D then le_field s ?p 4
                                   else le_field s ?p 8)] =>
    pose proof (lp_fcs_rng s p A B C D Hb) as Hfcs;
    set (fcs := (if A then (if B then byte_at s p else ZSTD_CONTENTSIZE_UNKNOWN)
                 else (if C then le_field s p 2 + 256 else if D then le_field s p 4 else le_field s p 8))) in *
  end.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|].
  split; [| apply Z.le_min_r]. apply Z.min_glb; [| unfold ZSTD_BLOCKSIZE_MAX; lia].
  destruct (_ =? 1); [lia|].
  assert (0 <= Z.shiftr (byte_at s 5) 3) by (apply Z.shiftr_nonneg; lia).
  assert (0 <= Z.land (byte_at s 5) 7) by (apply Z.land_nonneg; lia).
  set (w := Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN).
  assert (0 < 2 ^ w) by (apply Z.pow_pos_nonneg; unfold w, ZSTD_WINDOWLOG_ABSOLUTEMIN; lia).
  assert (0 <= Z.shiftr (2 ^ w) 3) by (apply Z.shiftr_nonneg; lia).
  nia.
Qed.

(* ---------- frame sizes: each frame takes at least one byte and at most the rest ---------- *)

Lemma lp_Zlength_skipn: forall (l: list Z) k, 0 <= k <= Zlength l ->
  Zlength (skipn (Z.to_nat k) l) = Zlength l - k.
Proof. intros. rewrite lp_skipn_sublist_Z by lia. rewrite Zlength_sublist by lia. lia. Qed.

Lemma lp_blocks_size_rng: forall f l k nb, bytes_ok l -> blocks_size f l = Some (k, nb) -> 3 <= k <= Zlength l.
Proof.
  induction f as [|f IH]; intros l k nb Hb H; [discriminate|].
  cbn [blocks_size] in H. destruct (cblock_size l) as [c|] eqn:E; [|discriminate].
  destruct (lp_cblock_size_nonneg _ _ Hb E) as [Hl Hc]. unfold ZSTD_blockHeaderSize in H.
  destruct (3 + c >? Zlength l) eqn:E2; [discriminate|].
  rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2.
  destruct (bp_last (block_props_of l) =? 1).
  - inversion H; subst. lia.
  - destruct (blocks_size f (skipn (Z.to_nat (3 + c)) l)) as [[k' nb']|] eqn:E3; [|discriminate].
    inversion H; subst. apply IH in E3; [|apply lp_bytes_ok_skipn; auto].
    rewrite lp_Zlength_skipn in E3 by lia. lia.
Qed.

Lemma lp_sfs_rng: forall s k, bytes_ok s -> skippable_frame_size s = Some k -> 8 <= k <= Zlength s.
Proof.
  intros s k Hb H. unfold skippable_frame_size, ZSTD_SKIPPABLEHEADERSIZE in H.
  pose proof (lp_le_field_rng s 4 4 Hb ltac:(lia)).
  destruct (Zlength s <? 8); [discriminate|].
  destruct (_ >? _) eqn:E; [discriminate|]. rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E.
  inversion H; subst. lia.
Qed.

Lemma lp_fsi_rng: forall s k b, bytes_ok s -> frame_size_info s = Some (k, b) -> 1 <= k <= Zlength s.
Proof.
  intros s k b Hb H. unfold frame_size_info in H.
  destruct (andb _ _).
  { destruct (skippable_frame_size s) as [k'|] eqn:E; [|discriminate]. inversion H; subst.
    apply lp_sfs_rng in E; auto. lia. }
  destruct (get_frame_header s) as [| |h] eqn:Eh; try discriminate.
  destruct (lp_gfh_ok s h Hb Eh) as [Hh _].
  destruct (blocks_size _ _) as [[k' nb]|] eqn:Eb; [|discriminate].
  apply lp_blocks_size_rng in Eb; [|apply lp_bytes_ok_skipn; auto].
  rewrite lp_Zlength_skipn in Eb by lia.
  destruct (fh_checksumFlag h =? 1).
  - destruct (_ <? 4) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4. inversion H; subst. lia.
  - inversion H; subst. lia.
Qed.

Lemma lp_fcs_size_rng: forall s k, bytes_ok s -> frame_compressed_size s = Some k -> 1 <= k <= Zlength s.
Proof.
  intros s k Hb H. rewrite frame_compressed_size_info in H.
  destruct (frame_size_info s) as [[k' b]|] eqn:E; [|discriminate]. inversion H; subst.
  eapply lp_fsi_rng; eauto.
Qed.

Lemma lp_Zlength_length: forall (l: list Z), Zlength l = Z.of_nat (length l).
Proof. intros. apply Zlength_correct. Qed.

Lemma lp_length_skipn_lt: forall (l: list Z) k, 1 <= k <= Zlength l ->
  (length (skipn (Z.to_nat k) l) < length l)%nat.
Proof. intros. rewrite length_skipn. rewrite Zlength_correct in H. lia. Qed.

Lemma bound_loop_fuel: forall f1 f2 l acc, bytes_ok l -> (length l < f1)%nat -> (length l < f2)%nat ->
  bound_loop f1 l acc = bound_loop f2 l acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 l acc Hb H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|]. cbn [bound_loop].
  destruct (Zlength l =? 0); auto.
  destruct (frame_size_info l) as [[k b]|] eqn:E; auto.
  destruct (b =? ZSTD_CONTENTSIZE_ERROR); auto.
  apply lp_fsi_rng in E; auto. pose proof (lp_length_skipn_lt l k E).
  apply IH; [apply lp_bytes_ok_skipn; auto | lia | lia].
Qed.

Lemma fds_loop_fuel: forall f1 f2 l acc, bytes_ok l -> (length l < f1)%nat -> (length l < f2)%nat ->
  fds_loop f1 l acc = fds_loop f2 l acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 l acc Hb H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|]. cbn [fds_loop].
  destruct (Zlength l <? ZSTD_FRAMEHEADERSIZE_PREFIX); auto.
  destruct (is_skippable_magic (le_field l 0 4)).
  - destruct (skippable_frame_size l) as [k|] eqn:E; auto.
    apply lp_sfs_rng in E; auto. pose proof (lp_length_skipn_lt l k ltac:(lia)).
    apply IH; [apply lp_bytes_ok_skipn; auto | lia | lia].
  - destruct (_ >=? _); auto. destruct (_ >=? _); auto.
    destruct (frame_compressed_size l) as [k|] eqn:E; auto.
    apply lp_fcs_size_rng in E; auto. pose proof (lp_length_skipn_lt l k E).
    apply IH; [apply lp_bytes_ok_skipn; auto | lia | lia].
Qed.

(* the rest of s after k bytes, after k' more bytes *)
Lemma lp_skipn_rest: forall (s: list Z) k k', 0 <= k -> 0 <= k' -> k + k' <= Zlength s ->
  skipn (Z.to_nat k') (sublist k (Zlength s) s) = sublist (k + k') (Zlength s) s.
Proof.
  intros. rewrite lp_skipn_sublist_Z by (rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma bound_loop_S: forall f l acc, bound_loop (S f) l acc =
  if Zlength l =? 0 then acc else
  match frame_size_info l with
  | None => ZSTD_CONTENTSIZE_ERROR
  | Some (k, b) =>
      if b =? ZSTD_CONTENTSIZE_ERROR then ZSTD_CONTENTSIZE_ERROR
      else bound_loop f (skipn (Z.to_nat k) l) ((acc + b) mod 2 ^ 64)
  end.
Proof. reflexivity. Qed.

Lemma bound_loop_step: forall s k acc k' b, bytes_ok s -> 0 <= k < Zlength s ->
  frame_size_info (sublist k (Zlength s) s) = Some (k', b) -> b <> ZSTD_CONTENTSIZE_ERROR ->
  1 <= k' <= Zlength s - k /\
  bound_loop (S (length (sublist k (Zlength s) s))) (sublist k (Zlength s) s) acc =
  bound_loop (S (length (sublist (k + k') (Zlength s) s))) (sublist (k + k') (Zlength s) s) ((acc + b) mod 2 ^ 64).
Proof.
  intros s k acc k' b Hb Hk E Hne.
  assert (Hbr: bytes_ok (sublist k (Zlength s) s)) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  pose proof (lp_fsi_rng _ _ _ Hbr E) as Hr. rewrite Zlength_sublist in Hr by lia.
  split; [lia|]. rewrite bound_loop_S.
  rewrite (proj2 (Z.eqb_neq (Zlength (sublist k (Zlength s) s)) 0)) by (rewrite Zlength_sublist; lia).
  rewrite E, (proj2 (Z.eqb_neq _ _)) by auto.
  rewrite lp_skipn_rest by lia. apply bound_loop_fuel.
  - unfold bytes_ok in *; apply Forall_sublist; auto.
  - rewrite <- (lp_skipn_rest s k k') by lia. apply lp_length_skipn_lt.
    rewrite Zlength_sublist; lia.
  - lia.
Qed.

Lemma lp_sublist_end: forall (s: list Z), sublist (Zlength s) (Zlength s) s = [].
Proof. intros. apply sublist_nil. Qed.

(* ---------- ZSTD_findDecompressedSize: the model side ---------- *)

Lemma fds_loop_S: forall f l acc, fds_loop (S f) l acc =
  if Zlength l <? ZSTD_FRAMEHEADERSIZE_PREFIX then
    (if Zlength l =? 0 then acc else ZSTD_CONTENTSIZE_ERROR)
  else if is_skippable_magic (le_field l 0 4) then
    match skippable_frame_size l with
    | None => ZSTD_CONTENTSIZE_ERROR
    | Some k => fds_loop f (skipn (Z.to_nat k) l) acc
    end
  else
    let fcs := frame_content_size l in
    if fcs >=? ZSTD_CONTENTSIZE_ERROR then fcs else
    if acc + fcs >=? 2 ^ 64 then ZSTD_CONTENTSIZE_ERROR else
    match frame_compressed_size l with
    | None => ZSTD_CONTENTSIZE_ERROR
    | Some k => fds_loop f (skipn (Z.to_nat k) l) (acc + fcs)
    end.
Proof. reflexivity. Qed.

(* moving the rest from k to k + k' (1 <= k') *)
Lemma fds_loop_move: forall s k k' acc, bytes_ok s -> 0 <= k -> 1 <= k' -> k + k' <= Zlength s ->
  fds_loop (Datatypes.length (sublist k (Zlength s) s)) (skipn (Z.to_nat k') (sublist k (Zlength s) s)) acc =
  fds_loop (S (Datatypes.length (sublist (k + k') (Zlength s) s))) (sublist (k + k') (Zlength s) s) acc.
Proof.
  intros s k k' acc Hb Hk Hk' Hle. rewrite lp_skipn_rest by lia. apply fds_loop_fuel.
  - unfold bytes_ok in *; apply Forall_sublist; auto.
  - rewrite <- (lp_skipn_rest s k k') by lia. apply lp_length_skipn_lt. rewrite Zlength_sublist; lia.
  - lia.
Qed.

Lemma lp_fcs_val_rng: forall s, bytes_ok s -> 0 <= frame_content_size s <= Int64.max_unsigned.
Proof.
  intros s Hb. unfold frame_content_size.
  destruct (get_frame_header s) as [| |h] eqn:E; try (unfold ZSTD_CONTENTSIZE_ERROR; rep_lia).
  destruct (fh_frameType h =? 1); [rep_lia|]. apply (lp_gfh_ok s h Hb E).
Qed.

Lemma lp_ovf: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.add (Int64.repr a) (Int64.repr b)) (Int64.repr a) = (a + b >=? 2 ^ 64).
Proof.
  intros a b Ha Hb. unfold Int64.ltu, Int64.add. rewrite (Int64.unsigned_repr a) by rep_lia.
  rewrite (Int64.unsigned_repr b) by rep_lia. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64). change Int64.max_unsigned with (2 ^ 64 - 1) in *.
  destruct (Z_lt_le_dec (a + b) (2 ^ 64)).
  - rewrite Z.mod_small by lia. destruct (zlt (a + b) a); [lia|].
    symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia.
  - rewrite <- (Z.mod_unique (a + b) (2 ^ 64) 1 (a + b - 2 ^ 64)) by lia.
    destruct (zlt (a + b - 2 ^ 64) a); [|lia].
    symmetry. rewrite Z.geb_leb. apply Z.leb_le. lia.
Qed.

Lemma lp_ovf2: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr (a + b)) (Int64.repr a) = (a + b >=? 2 ^ 64).
Proof. intros. rewrite <- add64_repr. apply lp_ovf; auto. Qed.

Lemma lp_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value length].
  - simpl. lia.
  - unfold is_byte in Hb. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma lp_le4: forall s i, bytes_ok s -> 0 <= le_field s i 4 <= Int.max_unsigned.
Proof.
  intros s i H. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. rewrite Forall_forall in *. intros x Hx.
    apply H. apply firstn_In in Hx. apply skipn_In in Hx. exact Hx. }
  pose proof (lp_le_value_range _ Hb).
  assert (length (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s)) <= 4)%nat by (rewrite firstn_length; lia).
  assert (2 ^ (8 * Z.of_nat (length (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s)))) <= 2 ^ 32)
    by (apply Z.pow_le_mono_r; lia).
  rep_lia.
Qed.

Lemma lp_skip_magic: forall m, 0 <= m <= Int.max_unsigned ->
  (Int.and (Int.repr m) (Int.repr (-16)) = Int.repr 407710288 <-> is_skippable_magic m = true).
Proof.
  intros m Hm. unfold Int.and. rewrite (Int.unsigned_repr m) by lia.
  change (Int.unsigned (Int.repr (-16))) with 4294967280.
  unfold is_skippable_magic, ZSTD_MAGIC_SKIPPABLE_MASK, ZSTD_MAGIC_SKIPPABLE_START. rewrite Z.eqb_eq.
  assert (0 <= Z.land m 4294967280 < 2 ^ 32).
  { replace (Z.land m 4294967280) with (Z.land m (Z.land 4294967280 (Z.ones 32))) by reflexivity.
    rewrite Z.land_assoc, Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  split; intro E.
  - apply repr_inj_unsigned in E; rep_lia.
  - rewrite E. reflexivity.
Qed.

Lemma lp_m2: Int64.repr (Z.opp 2) = Int64.repr ZSTD_CONTENTSIZE_ERROR.
Proof. unfold ZSTD_CONTENTSIZE_ERROR. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma lp_ltu: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* the array as its first k bytes and the rest, an array of its own *)
Lemma lp_arr_view: forall sh (s: list Z) k p, 0 <= k <= Zlength s ->
  field_compatible (tarray tuchar (Zlength s)) [] p ->
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) p =
  (data_at sh (tarray tuchar k) (zbytes (sublist 0 k s)) p *
   data_at sh (tarray tuchar (Zlength (sublist k (Zlength s) s))) (zbytes (sublist k (Zlength s) s)) (offset_val k p)).
Proof.
  intros sh s k p Hk Hfc.
  rewrite (split2_data_at_Tarray_tuchar sh (Zlength s) k) by (rewrite ?Zlength_map; lia).
  change (Tarray tuchar (Zlength s) noattr) with (tarray tuchar (Zlength s)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite !sublist_map, Zlength_sublist by lia. reflexivity.
Qed.

Lemma body_decompressBound: semax_body Vprog H_G f_ZSTD_decompressBound ZSTD_decompressBound_spec.
Proof.
  start_function.
  destruct H as [Hsh [Hs30 Hb]].
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  forward.
  forward_while (EX k: Z, EX acc: Z,
    PROP (0 <= k <= Zlength s; 0 <= acc <= Int64.max_unsigned;
          decompress_bound s = bound_loop (S (length (sublist k (Zlength s) s))) (sublist k (Zlength s) s) acc)
    LOCAL (temp _bound (Vlong (Int64.repr acc)); temp _src (offset_val k src);
           temp _srcSize (Vlong (Int64.repr (Zlength s - k)));
           lvar _frameSizeInfo t_fsi v_frameSizeInfo; gvars gv)
    SEP (zstd_globals gv; data_at_ Tsh t_fsi v_frameSizeInfo;
         data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)).
  - Exists 0 0. entailer!. rewrite sublist_same by lia. reflexivity.
  - entailer!.
  - set (r := sublist k (Zlength s) s) in *.
    assert (Hr: Zlength r = Zlength s - k) by (unfold r; rewrite Zlength_sublist; lia).
    assert (Hw: win_ok sh (Zlength s) (zbytes s) k (Zlength r) r).
    { pose proof (win_ok_skip _ _ _ _ _ k (win_ok_full sh s (conj Hsh (conj Hs30 Hb))) ltac:(lia)) as W.
      rewrite Z.add_0_l in W. rewrite Hr. exact W. }
    forward_call (gv, Tsh, v_frameSizeInfo, sh, src, Zlength s, zbytes s, k, r).
    { rewrite Hr. entailer!. }
    Intros vret. destruct vret as [[nb cs] db]. simpl fst in *; simpl snd in *.
    forward. forward.
    forward_call cs.
    forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (if orb (is_error_code cs) (db =? ZSTD_CONTENTSIZE_ERROR) then 1 else 0)));
       temp _decompressedBound (Vlong (Int64.repr db)); temp _compressedSize (Vlong (Int64.repr cs));
       temp _bound (Vlong (Int64.repr acc)); temp _src (offset_val k src);
       temp _srcSize (Vlong (Int64.repr (Zlength s - k)));
       lvar _frameSizeInfo t_fsi v_frameSizeInfo; gvars gv)
      SEP (zstd_globals gv; data_at Tsh t_fsi (nb, (Vlong (Int64.repr cs), Vlong (Int64.repr db))) v_frameSizeInfo;
           data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)).
    { forward. entailer!. destruct (is_error_code cs); [reflexivity | contradiction H5'; reflexivity]. }
    { forward. entailer!.
      destruct (is_error_code cs).
      { apply (f_equal Int.unsigned) in H5. rewrite Int.unsigned_repr in H5 by rep_lia. discriminate. }
      simpl orb. unfold Int64.cmpu. unfold ZSTD_CONTENTSIZE_ERROR.
      destruct (Z.eqb_spec db (2 ^ 64 - 2)) as [E|E].
      { subst db. reflexivity. }
      { unfold Int64.eq. rewrite (Int64.unsigned_repr db) by rep_lia.
        change (Int64.unsigned (Int64.repr (-(2)))) with (2^64-2).
        destruct (zeq db (2^64-2)); [contradiction | reflexivity]. } }
    assert (Hbr: bytes_ok r) by (unfold r, bytes_ok in *; apply Forall_sublist; auto).
    destruct (orb (is_error_code cs) (db =? ZSTD_CONTENTSIZE_ERROR)) eqn:Ebad.
    + forward_if; [| exfalso; apply (f_equal Int.unsigned) in H5;
                     rewrite Int.unsigned_repr, Int.unsigned_zero in H5 by rep_lia; lia].
      forward. entailer!.
      assert (Hdb: decompress_bound s = ZSTD_CONTENTSIZE_ERROR).
      { rewrite H1, bound_loop_S. rewrite (proj2 (Z.eqb_neq (Zlength r) 0)) by lia.
        destruct (frame_size_info r) as [[k' b]|] eqn:Ef; [|reflexivity].
        destruct H4; subst k' b. apply orb_true_iff in Ebad. destruct Ebad as [Ee|Ee].
        - exfalso. pose proof (lp_fsi_rng _ _ _ Hbr Ef). unfold is_error_code in Ee.
          apply Z.ltb_lt in Ee. lia.
        - rewrite Ee. reflexivity. }
      rewrite Hdb. unfold ZSTD_CONTENTSIZE_ERROR. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
    + forward_if; [contradiction H5; reflexivity |].
      apply orb_false_iff in Ebad. destruct Ebad as [Ee1 Ee2]. apply Z.eqb_neq in Ee2.
      destruct (frame_size_info r) as [[k' b]|] eqn:Ef; [| rewrite H4 in Ee1; discriminate].
      destruct H4; subst k' b.
      destruct (bound_loop_step s k acc cs db Hb ltac:(lia) Ef Ee2) as [Hcs Hstep].
      forward. forward. forward.
      Exists (k + cs, (acc + db) mod 2 ^ 64). simpl fst; simpl snd.
      entailer!.
      { change (Z.pow_pos 2 64) with (2 ^ 64).
        split; [pose proof (Z.mod_pos_bound (acc + db) (2 ^ 64) ltac:(lia)); rep_lia|].
        split; [rewrite H1; exact Hstep|].
        split; [|f_equal; f_equal; lia].
        f_equal. rewrite <- (Int64.repr_unsigned (Int64.repr (acc + db))), Int64.unsigned_repr_eq. reflexivity. }
  - forward. entailer!.
    assert (k = Zlength s) by lia. subst k. rewrite sublist_nil in H1. rewrite H1. reflexivity.
Qed.

Ltac ltu_tac H := unfold Int64.ltu, ZSTD_FRAMEHEADERSIZE_PREFIX in H;
  rewrite !Int64.unsigned_repr in H by rep_lia;
  destruct (zlt _ _) in H; [try discriminate | try discriminate]; try lia.

Ltac fif_same := match goal with |- semax _ ?P _ _ => forward_if P end.
Ltac fif_false := forward_if (PROP (False) LOCAL () SEP ()).
Ltac ltu_hyp := match goal with Hc: Int64.ltu _ _ = _ |- _ =>
  rewrite ?lp_m2 in Hc; rewrite lp_ltu in Hc by (unfold ZSTD_CONTENTSIZE_ERROR in *; rep_lia) end.
Ltac merge_tac sh s k src r := rewrite (lp_arr_view sh s k src) by (auto; lia); subst r; cancel.

Ltac call0 W := apply -> seq_assoc; forward_call W; [entailer! | .. ].

Lemma body_findDecompressedSize: semax_body Vprog H_G f_ZSTD_findDecompressedSize ZSTD_findDecompressedSize_spec.
Proof.
  start_function.
  destruct H as [Hsh [Hs30 Hb]].
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  forward.
  forward_loop (EX k: Z, EX acc: Z,
    PROP (0 <= k <= Zlength s; 0 <= acc <= Int64.max_unsigned;
          find_decompressed_size s = fds_loop (S (length (sublist k (Zlength s) s))) (sublist k (Zlength s) s) acc)
    LOCAL (temp _totalDstSize (Vlong (Int64.repr acc)); temp _src (offset_val k src);
           temp _srcSize (Vlong (Int64.repr (Zlength s - k))); gvars gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src))
  break: (EX k: Z, EX acc: Z,
    PROP (0 <= k <= Zlength s; Zlength s - k < 5; 0 <= acc <= Int64.max_unsigned;
          find_decompressed_size s = fds_loop (S (length (sublist k (Zlength s) s))) (sublist k (Zlength s) s) acc)
    LOCAL (temp _totalDstSize (Vlong (Int64.repr acc)); temp _src (offset_val k src);
           temp _srcSize (Vlong (Int64.repr (Zlength s - k))); gvars gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)).
  - Exists 0 0. entailer!. rewrite sublist_same by lia. reflexivity.
  - Intros k acc.
    forward_call tt.
    forward_if (PROP (5 <= Zlength s - k)
      LOCAL (temp _totalDstSize (Vlong (Int64.repr acc)); temp _src (offset_val k src);
             temp _srcSize (Vlong (Int64.repr (Zlength s - k))); gvars gv)
      SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)).
    { forward. entailer!. ltu_tac H2. }
    { forward. Exists k acc. entailer!. ltu_tac H2. }
    Intros.
    set (r := sublist k (Zlength s) s) in *.
    assert (Hr: Zlength r = Zlength s - k) by (unfold r; rewrite Zlength_sublist; lia).
    assert (Hbr: bytes_ok r) by (unfold r, bytes_ok in *; apply Forall_sublist; auto).
    assert (Hr30: Zlength r <= 2 ^ 63 - 1) by lia.
    assert_PROP (field_compatible (tarray tuchar (Zlength s)) [] src) as Hfc by entailer!.
    rewrite (lp_arr_view sh s k src) by (auto; lia). fold r. Intros.
    apply -> seq_assoc. forward_call (sh, offset_val k src, r, 0).
    { unfold mem_read_pre. repeat split; auto; try lia. unfold bytes_ok in *; apply Forall_sublist; auto. }
    forward.
    pose proof (lp_le4 r 0 Hbr) as Hm4.
    destruct (is_skippable_magic (le_field r 0 4)) eqn:Em.
    + (* a skippable frame *)
      forward_if (PROP (False) LOCAL () SEP ()).
      2: { exfalso. apply H3. apply (proj2 (lp_skip_magic _ Hm4)). exact Em. }
      apply -> seq_assoc. forward_call (sh, offset_val k src, Zlength r, zbytes r, 0, r).
      { rewrite Hr. entailer!. }
      { apply win_ok_full. split; auto. }
      Intros r0.
      assert (Hfs: fds_loop (S (Datatypes.length r)) r acc =
                   match skippable_frame_size r with
                   | None => ZSTD_CONTENTSIZE_ERROR
                   | Some k => fds_loop (Datatypes.length r) (skipn (Z.to_nat k) r) acc
                   end).
      { rewrite fds_loop_S. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
        rewrite Em. reflexivity. }
      destruct (skippable_frame_size r) as [k'|] eqn:Es.
      * subst r0. pose proof (lp_sfs_rng _ _ Hbr Es) as Hk'.
        assert (Hne: is_error_code k' = false).
        { unfold is_error_code. apply Z.ltb_ge. lia. }
        forward. forward_call k'. rewrite Hne.
        forward_if; [contradiction H5; reflexivity |].
        forward. forward. forward.
        Exists (k + k') acc. entailer!.
        { split; [rewrite H1, Hfs; apply fds_loop_move; auto; lia | f_equal; f_equal; lia]. }
        rewrite (lp_arr_view sh s k src) by (auto; lia). subst r. cancel.
      * apply dec_err_is_error in H5. forward. forward_call r0. rewrite H5.
        forward_if; [| exfalso; apply (f_equal Int.unsigned) in H6;
                       rewrite Int.unsigned_repr, Int.unsigned_zero in H6 by rep_lia; lia].
        forward. entailer!. rewrite H1, Hfs, lp_m2. reflexivity.
        rewrite (lp_arr_view sh s k src) by (auto; lia). subst r. cancel.
    + (* a Zstandard frame (or garbage) *)
      forward_if (PROP ()
        LOCAL (temp _magicNumber (Vint (Int.repr (le_field r 0 4))); temp _t'2 (Vint (Int.repr (le_field r 0 4)));
               temp _totalDstSize (Vlong (Int64.repr acc)); temp _src (offset_val k src);
               temp _srcSize (Vlong (Int64.repr (Zlength s - k))); gvars gv)
        SEP (data_at sh (tarray tuchar (Zlength r)) (zbytes r) (offset_val k src); zstd_globals gv;
             data_at sh (tarray tuchar k) (zbytes (sublist 0 k s)) src)).
      { exfalso. rewrite (proj1 (lp_skip_magic _ Hm4) H3) in Em. discriminate. }
      { forward. entailer!. }
      set (F := frame_content_size r).
      pose proof (lp_fcs_val_rng r Hbr) as HF. fold F in HF.
      assert (Hfs: fds_loop (S (Datatypes.length r)) r acc =
        if F >=? ZSTD_CONTENTSIZE_ERROR then F else
        if acc + F >=? 2 ^ 64 then ZSTD_CONTENTSIZE_ERROR else
        match frame_compressed_size r with
        | None => ZSTD_CONTENTSIZE_ERROR
        | Some k => fds_loop (Datatypes.length r) (skipn (Z.to_nat k) r) (acc + F)
        end).
      { rewrite fds_loop_S. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
        rewrite Em. reflexivity. }
      forward_call (gv, sh, offset_val k src, r).
      { rewrite Hr. entailer!. }
      { repeat split; auto. }
      fold F.
      destruct (F >=? ZSTD_CONTENTSIZE_ERROR) eqn:EF.
      { fif_false.
        - forward. entailer!. merge_tac sh s k src r.
        - exfalso. match goal with Hc: Int64.unsigned _ < Int64.unsigned _ |- _ =>
            try rewrite (Int64.unsigned_repr F) in Hc by rep_lia;
            try change (Int64.unsigned (Int64.repr (- (2)))) with (2 ^ 64 - 2) in Hc;
            try change (Int64.unsigned (Int64.sub (Int64.repr 0) (Int64.repr 2))) with (2 ^ 64 - 2) in Hc end.
          apply Z.geb_le in EF. unfold ZSTD_CONTENTSIZE_ERROR in EF. lia. }
      fif_same.
      { exfalso. match goal with Hc: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
            try rewrite (Int64.unsigned_repr F) in Hc by rep_lia;
            try change (Int64.unsigned (Int64.repr (- (2)))) with (2 ^ 64 - 2) in Hc;
            try change (Int64.unsigned (Int64.sub (Int64.repr 0) (Int64.repr 2))) with (2 ^ 64 - 2) in Hc end.
        rewrite Z.geb_leb in EF; apply Z.leb_gt in EF. unfold ZSTD_CONTENTSIZE_ERROR in EF. lia. }
      { forward. entailer!. }
      destruct (acc + F >=? 2 ^ 64) eqn:EO.
      { fif_false.
        - forward. entailer!.
          + rewrite H1, Hfs, lp_m2. reflexivity.
          + merge_tac sh s k src r.
        - exfalso. match goal with Hc: Int64.ltu _ _ = false |- _ => rewrite ?add64_repr in Hc; rewrite lp_ovf2 in Hc by rep_lia end.
          congruence. }
      fif_same.
      { exfalso. match goal with Hc: Int64.ltu _ _ = true |- _ => rewrite ?add64_repr in Hc; rewrite lp_ovf2 in Hc by rep_lia end.
        congruence. }
      { forward. entailer!. }
      forward.
      forward_call (gv, sh, offset_val k src, r).
      { rewrite Hr. entailer!. }
      { repeat split; auto. }
      Intros cs.
      destruct (frame_compressed_size r) as [k'|] eqn:Ec.
      * subst cs. pose proof (lp_fcs_size_rng _ _ Hbr Ec) as Hk'.
        assert (Hne: is_error_code k' = false).
        { unfold is_error_code. apply Z.ltb_ge. lia. }
        forward_call k'. rewrite Hne.
        forward_if; [match goal with Hc: Int.repr 0 <> Int.zero |- _ => contradiction Hc; reflexivity end |].
        forward. forward.
        Exists (k + k') (acc + F). entailer!.
        { split; [rewrite H1, Hfs; apply fds_loop_move; auto; lia | f_equal; f_equal; lia]. }
        merge_tac sh s k src r.
      * forward_call cs. rewrite H4.
        forward_if; [| exfalso; match goal with Hc: Int.repr 1 = Int.zero |- _ =>
                         apply (f_equal Int.unsigned) in Hc;
                         rewrite Int.unsigned_repr, Int.unsigned_zero in Hc by rep_lia; lia end].
        forward. entailer!.
        { rewrite H1, Hfs, lp_m2. reflexivity. }
        merge_tac sh s k src r.
  - Intros k acc.
    forward_if.
    + forward. entailer!.
      rewrite H2, fds_loop_S. rewrite Zlength_sublist by lia.
      rewrite (proj2 (Z.ltb_lt _ _)) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
      rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite lp_m2. reflexivity.
    + assert (Hk: k = Zlength s).
      { apply (f_equal Int64.unsigned) in H3. rewrite Int64.unsigned_repr, Int64.unsigned_zero in H3 by rep_lia. lia. }
      subst k. forward. entailer!. rewrite H2, sublist_nil. reflexivity.
Qed.

Lemma bodies_H_loops :
  semax_body Vprog H_G f_ZSTD_findDecompressedSize ZSTD_findDecompressedSize_spec /\
  semax_body Vprog H_G f_ZSTD_decompressBound ZSTD_decompressBound_spec.
Proof. split; [apply body_findDecompressedSize | apply body_decompressBound]. Qed.
