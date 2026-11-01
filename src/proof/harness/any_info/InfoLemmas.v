(* The checks of harness/any_info.c as facts about the inspection functions of the format model
   (model/Frame.v, model/Info.v), on ANY bytes. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Info.
Local Open Scope bool_scope.

Ltac IL_some H :=
  lazymatch type of H with
  | Some (?a, _) = Some (?k, _) => assert (k = a) by congruence; subst k
  | Some ?a = Some ?k => assert (k = a) by congruence; subst k
  | FH_ok ?a = FH_ok ?h => assert (h = a) by congruence; subst h
  | FH_more ?a = FH_more ?h => assert (h = a) by congruence; subst h
  end.

Lemma IL_gtb_false x y : (x >? y) = false -> x <= y.
Proof. rewrite Z.gtb_ltb. apply Z.ltb_ge. Qed.

Lemma IL_to_nat_nonpos x : x <= 0 -> Z.to_nat x = 0%nat.
Proof. intros H. destruct x; try reflexivity. lia. Qed.

Lemma IL_Zlength_skipn {A} (x: Z) (l: list A) :
  Zlength (skipn (Z.to_nat x) l) = Zlength l - Z.max 0 (Z.min x (Zlength l)).
Proof.
  rewrite !Zlength_correct, skipn_length.
  destruct (Z.le_gt_cases x 0).
  - rewrite (IL_to_nat_nonpos x) by lia. rewrite Nat.sub_0_r. lia.
  - destruct (Nat.le_ge_cases (Z.to_nat x) (length l)) as [Hl|Hl].
    + rewrite Nat2Z.inj_sub, Z2Nat.id by lia. apply Nat2Z.inj_le in Hl. rewrite Z2Nat.id in Hl by lia. lia.
    + replace (length l - Z.to_nat x)%nat with 0%nat by lia.
      apply Nat2Z.inj_le in Hl. rewrite Z2Nat.id in Hl by lia. lia.
Qed.

Lemma IL_blocks_size_S f s : blocks_size (S f) s =
  match cblock_size s with
  | None => None
  | Some c =>
      if ZSTD_blockHeaderSize + c >? Zlength s then None else
      if bp_last (block_props_of s) =? 1 then Some (ZSTD_blockHeaderSize + c, 1)
      else match blocks_size f (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) with
           | Some (k, nb) => Some (ZSTD_blockHeaderSize + c + k, nb + 1)
           | None => None
           end
  end.
Proof. reflexivity. Qed.

Lemma IL_blocks_size_le fuel s k nb :
  blocks_size fuel s = Some (k, nb) -> k <= Zlength s.
Proof.
  revert s k nb; induction fuel as [|f IH]; intros s k nb H; [discriminate|].
  rewrite IL_blocks_size_S in H.
  destruct (cblock_size s) as [c|]; [|discriminate].
  destruct (ZSTD_blockHeaderSize + c >? Zlength s) eqn:E; [discriminate|].
  apply IL_gtb_false in E.
  destruct (bp_last (block_props_of s) =? 1).
  - IL_some H. lia.
  - destruct (blocks_size f (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s)) as [[k' nb']|] eqn:B;
      [|discriminate].
    IL_some H. apply IH in B. rewrite IL_Zlength_skipn in B. lia.
Qed.

Lemma IL_skippable_frame_size_le s k : skippable_frame_size s = Some k -> k <= Zlength s.
Proof.
  unfold skippable_frame_size. intros H.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  destruct (_ >? Zlength s) eqn:E; [discriminate|].
  apply IL_gtb_false in E. IL_some H. lia.
Qed.

Lemma IL_nth4 m i (l: list Z) : 0 <= m -> Forall (fun x => 0 <= x <= m) l -> 0 <= nth i l 0 <= m.
Proof.
  intros Hm; revert i; induction l as [|a l IH]; intros i Hl; destruct i; simpl; try lia;
    inversion Hl; subst; auto.
Qed.

Lemma IL_fhd_header_size_range fhd : 5 <= fhd_header_size fhd <= 18.
Proof.
  unfold fhd_header_size.
  pose proof (IL_nth4 4 (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] ltac:(lia) ltac:(repeat constructor; lia)).
  pose proof (IL_nth4 8 (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] ltac:(lia) ltac:(repeat constructor; lia)).
  assert (0 <= Z.land (Z.shiftr fhd 5) 1 <= 1).
  { rewrite (Z.land_ones _ 1) by lia. pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) 2 ltac:(lia)). change (2^1) with 2. lia. }
  set (ss := Z.land (Z.shiftr fhd 5) 1) in *.
  set (a := nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) in *.
  set (b := nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0) in *.
  destruct (Z.eqb_spec ss 1); destruct (Z.shiftr fhd 6 =? 0); cbn [andb]; lia.
Qed.

(* getFrameHeader returns 0: the header is complete *)
Lemma IL_gfh_ok s h : get_frame_header s = FH_ok h -> 0 <= fh_headerSize h <= Zlength s.
Proof.
  unfold get_frame_header. intros H.
  destruct (Zlength s <? 5) eqn:E5.
  - destruct (Zlength s >? 0); [destruct (_ && _)|]; discriminate.
  - apply Z.ltb_ge in E5.
    destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
    + destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
      destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [discriminate|].
      apply Z.ltb_ge in E8. IL_some H. simpl. unfold ZSTD_SKIPPABLEHEADERSIZE in *. lia.
    + pose proof (IL_fhd_header_size_range (byte_at s 4)).
      destruct (Zlength s <? fhd_header_size (byte_at s 4)) eqn:Ef; [discriminate|].
      apply Z.ltb_ge in Ef.
      destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
      destruct (_ && _); [discriminate|].
      IL_some H. simpl. lia.
Qed.

(* getFrameHeader returns k > 0: more bytes wanted *)
Lemma IL_gfh_more s k : get_frame_header s = FH_more k -> Zlength s < k <= 18.
Proof.
  unfold get_frame_header. intros H.
  destruct (Zlength s <? 5) eqn:E5.
  - apply Z.ltb_lt in E5.
    destruct (Zlength s >? 0); [destruct (_ && _)|]; try discriminate; IL_some H; lia.
  - destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
    + destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
      destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; [|discriminate].
      apply Z.ltb_lt in E8. IL_some H. unfold ZSTD_SKIPPABLEHEADERSIZE in *. lia.
    + pose proof (IL_fhd_header_size_range (byte_at s 4)).
      destruct (Zlength s <? fhd_header_size (byte_at s 4)) eqn:Ef.
      * apply Z.ltb_lt in Ef. IL_some H. lia.
      * destruct (negb (Z.land (byte_at s 4) 8 =? 0)); [discriminate|].
        destruct (_ && _); discriminate.
Qed.

(* findFrameCompressedSize: the size of a frame within src *)
Lemma IL_fcs_le s k : frame_compressed_size s = Some k -> k <= Zlength s.
Proof.
  unfold frame_compressed_size. intros H.
  destruct (_ && _).
  - apply IL_skippable_frame_size_le; auto.
  - destruct (get_frame_header s) as [| |h] eqn:G; try discriminate.
    apply IL_gfh_ok in G.
    destruct (blocks_size _ _) as [[k' nb]|] eqn:B; [|discriminate].
    apply IL_blocks_size_le in B. rewrite IL_Zlength_skipn in B.
    destruct (fh_checksumFlag h =? 1).
    + destruct (Zlength s - (fh_headerSize h + k') <? 4) eqn:E; [discriminate|].
      apply Z.ltb_ge in E. IL_some H. lia.
    + IL_some H. lia.
Qed.

(* isFrame, isSkippableFrame: 0 when size < 4 *)
Lemma IL_is_frame_small s : Zlength s < 4 -> is_frame s = 0.
Proof. intros H. unfold is_frame. apply Z.ltb_lt in H. rewrite H. reflexivity. Qed.

Lemma IL_is_skippable_small s : Zlength s < 4 -> is_skippable_frame s = 0.
Proof. intros H. unfold is_skippable_frame. apply Z.ltb_lt in H. rewrite H. reflexivity. Qed.

(* readSkippableFrame: the bytes written fit dstCapacity *)
Lemma IL_read_skippable_le s cap u var : 0 <= cap -> read_skippable s cap = Some (u, var) -> Zlength u <= cap.
Proof.
  unfold read_skippable. intros Hc H.
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  destruct (negb _); [discriminate|].
  destruct (skippable_frame_size s) as [k|]; [|discriminate].
  destruct (k - ZSTD_SKIPPABLEHEADERSIZE >? cap) eqn:E; [discriminate|].
  apply IL_gtb_false in E. IL_some H.
  unfold slice. rewrite Zlength_correct, firstn_length.
  destruct (Z.le_gt_cases (k - ZSTD_SKIPPABLEHEADERSIZE) 0).
  - rewrite (IL_to_nat_nonpos (k - ZSTD_SKIPPABLEHEADERSIZE)) by lia. simpl. lia.
  - rewrite Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.
