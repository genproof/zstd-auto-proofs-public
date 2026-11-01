(* FS3 streaming, case zdss_loadHeader: facts of a header parsed by Params.get_frame_header_m. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.
Local Open Scope Z_scope.

Section CM_LH3Gfh_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma gfh3h_le_value_rng : forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction l as [|b l IH]; intros H.
  - simpl. lia.
  - inversion H as [|? ? Hb Hl]; subst. unfold is_byte in Hb. specialize (IH Hl).
    replace (8 * Z.of_nat (length (b :: l))) with (8 * Z.of_nat (length l) + 8) by (simpl length; lia).
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. simpl le_value. nia.
Qed.

Lemma gfh3h_le_field_rng : forall l i k, bytes_ok l -> 0 <= k -> 0 <= le_field l i k < 2 ^ (8 * k).
Proof.
  intros l i k H Hk. unfold le_field, slice.
  assert (Hs: bytes_ok (firstn (Z.to_nat k) (skipn (Z.to_nat i) l))).
  { apply Forall_firstn, Forall_skipn, H. }
  pose proof (gfh3h_le_value_rng _ Hs) as [H0 H1]. split; [lia|].
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. lia.
Qed.

Lemma gfh3h_byte_at_rng : forall l i, bytes_ok l -> 0 <= byte_at l i < 256.
Proof.
  intros l i H. unfold byte_at.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [Hl|Hl].
  - eapply Forall_forall in H; [exact H|]. apply nth_In; exact Hl.
  - rewrite nth_overflow by exact Hl. lia.
Qed.

Lemma gfh3h_hsize_rng : forall fhd, 5 <= fhd_header_size fhd <= 18.
Proof.
  intros fhd. unfold fhd_header_size.
  assert (Hs: Z.land (Z.shiftr fhd 5) 1 = 0 \/ Z.land (Z.shiftr fhd 5) 1 = 1).
  { rewrite (Z.land_ones _ 1) by lia. pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) 2). change (2 ^ 1) with 2. lia. }
  assert (Hd: forall n, 0 <= nth n [0; 1; 2; 4] 0 <= 4).
  { intros [|[|[|[|n]]]]; simpl; try destruct n; lia. }
  assert (Hf: forall n, 0 <= nth n [0; 2; 4; 8] 0 <= 8 /\ (n <> O -> 0 <= nth n [0; 2; 4; 8] 0 <= 8)).
  { intros [|[|[|[|n]]]]; simpl; try destruct n; split; lia. }
  pose proof (Hd (Z.to_nat (Z.land fhd 3))).
  destruct (Hf (Z.to_nat (Z.shiftr fhd 6))) as [Hf1 _].
  remember (nth (Z.to_nat (Z.land fhd 3)) [0; 1; 2; 4] 0) as a.
  remember (nth (Z.to_nat (Z.shiftr fhd 6)) [0; 2; 4; 8] 0) as b.
  destruct Hs as [Hs|Hs]; rewrite Hs; simpl.
  - lia.
  - destruct (Z.shiftr fhd 6 =? 0) eqn:E; simpl.
    + apply Z.eqb_eq in E. rewrite E in Heqb. simpl in Heqb. lia.
    + lia.
Qed.

Lemma gfh3h_land_le : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha. apply (Z.ldiff_le (Z.land a b) a Ha).
  apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
Qed.

Lemma gfh3h_bit1 : forall x, Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  intros x. rewrite (Z.land_ones _ 1) by lia. pose proof (Z.mod_pos_bound x 2). change (2 ^ 1) with 2. lia.
Qed.

Lemma gfh3_base : forall hb h, get_frame_header hb = FH_ok h -> bytes_ok hb ->
  gfh3_facts false hb h /\ 5 <= fh_headerSize h.
Proof.
  intros hb h E Hb. unfold get_frame_header in E. cbv zeta in E.
  destruct (Zlength hb <? 5) eqn:L5.
  { destruct (Zlength hb >? 0); [destruct (_ && _)%bool|]; discriminate. }
  apply Z.ltb_ge in L5.
  pose proof (gfh3h_le_field_rng hb 0 4 Hb ltac:(lia)) as Hm.
  destruct (le_field hb 0 4 =? ZSTD_MAGICNUMBER) eqn:M; cbn [negb] in E.
  - (* a Zstandard frame *)
    apply Z.eqb_eq in M.
    destruct (Zlength hb <? fhd_header_size (byte_at hb 4)) eqn:L; [discriminate|].
    destruct (negb (Z.land (byte_at hb 4) 8 =? 0)); [discriminate|].
    destruct ((Z.land (Z.shiftr (byte_at hb 4) 5) 1 =? 0) &&
              (Z.shiftr (byte_at hb 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX))%bool eqn:W;
      [discriminate|].
    injection E as <-.
    pose proof (gfh3h_byte_at_rng hb 4 Hb) as Hfhd. pose proof (gfh3h_byte_at_rng hb 5 Hb) as Hwlb.
    set (fhd := byte_at hb 4) in *. set (wlb := byte_at hb 5) in *.
    pose proof (gfh3h_bit1 (Z.shiftr fhd 5)) as Hss.
    set (SS := Z.land (Z.shiftr fhd 5) 1) in *.
    match goal with |- context [le_field hb (5 + (1 - SS)) ?d] => set (D := d) in * end.
    assert (HD: 0 <= D <= 4) by (unfold D; destruct (Z.to_nat _) as [|[|[|[|n]]]]; try destruct n; cbn; lia).
    clearbody D.
    match goal with |- context [Build_frame_header ?c _ _ _ _ _ _] => set (C := c) in * end.
    assert (HC: 0 <= C <= Int64.max_unsigned).
    { unfold C. change Int64.max_unsigned with (2 ^ 64 - 1).
      pose proof (gfh3h_byte_at_rng hb (5 + (1 - SS) + D) Hb).
      pose proof (gfh3h_le_field_rng hb (5 + (1 - SS) + D) 2 Hb ltac:(lia)).
      pose proof (gfh3h_le_field_rng hb (5 + (1 - SS) + D) 4 Hb ltac:(lia)).
      pose proof (gfh3h_le_field_rng hb (5 + (1 - SS) + D) 8 Hb ltac:(lia)).
      change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 4)) with 4294967296 in *.
      change (2 ^ (8 * 8)) with 18446744073709551616 in *. change (2 ^ 64) with 18446744073709551616.
      unfold ZSTD_CONTENTSIZE_UNKNOWN. change (2 ^ 64) with 18446744073709551616.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. }
    clearbody C.
    match goal with |- context [Build_frame_header _ ?w _ _ _ _ _] => set (Wd := w) in * end.
    assert (HW: 0 <= Wd <= Int64.max_unsigned).
    { unfold Wd. destruct (SS =? 1) eqn:E1; [lia|].
      assert (SS = 0) as E0 by (apply Z.eqb_neq in E1; lia). rewrite E0 in W. cbn [Z.eqb andb] in W.
      rewrite Z.gtb_ltb in W. apply Z.ltb_ge in W. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN, ZSTD_WINDOWLOG_MAX in *.
      assert (0 <= Z.shiftr wlb 3) by (apply Z.shiftr_nonneg; lia).
      set (wl := Z.shiftr wlb 3 + 10) in *.
      assert (Hp: 0 < 2 ^ wl <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite (Z.land_ones _ 3) by lia. change (2 ^ 3) with 8.
      pose proof (Z.mod_pos_bound wlb 8 ltac:(lia)). pose proof (Z.div_pos (2 ^ wl) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (2 ^ wl) 8 (2 ^ wl) ltac:(lia) ltac:(lia)).
      change Int64.max_unsigned with 18446744073709551615. change (2 ^ 31) with 2147483648 in Hp. nia. }
    clearbody Wd.
    pose proof (gfh3h_le_field_rng hb (5 + (1 - SS)) D Hb ltac:(lia)) as Hdi.
    assert (2 ^ (8 * D) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    pose proof (gfh3h_bit1 (Z.shiftr fhd 2)).
    pose proof (gfh3h_hsize_rng fhd).
    unfold gfh3_facts, starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType fh_headerSize fh_dictID fh_checksumFlag].
    rewrite M. change (is_skippable_magic ZSTD_MAGICNUMBER) with false.
    unfold ZSTD_BLOCKSIZE_MAX. change Int.max_unsigned with 4294967295.
    change (2 ^ 32) with 4294967296 in *.
    split; [|lia].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [split; [discriminate|intros [_ ?]; discriminate]|].
    split; [discriminate|]. lia.
  - destruct (is_skippable_magic (le_field hb 0 4)) eqn:S; [|discriminate].
    destruct (Zlength hb <? ZSTD_SKIPPABLEHEADERSIZE) eqn:L8; [discriminate|].
    apply Z.ltb_ge in L8.
    injection E as <-.
    pose proof (gfh3h_le_field_rng hb 4 4 Hb ltac:(lia)) as Hc.
    assert (Hs: ZSTD_MAGIC_SKIPPABLE_START <= le_field hb 0 4).
    { unfold is_skippable_magic in S. apply Z.eqb_eq in S. rewrite <- S. apply gfh3h_land_le. lia. }
    unfold gfh3_facts, starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; cbn -[Z.min le_field Z.pow].
    unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_BLOCKSIZE_MAX, ZSTD_MAGIC_SKIPPABLE_START in *.
    change (2 ^ (8 * 4)) with 4294967296 in *.
    change Int64.max_unsigned with 18446744073709551615. change Int.max_unsigned with 4294967295.
    intuition (try lia; try reflexivity).
Qed.

Lemma gfh3_ok : gfh3_stmt.
Proof.
  intros mg hb h E Hb. destruct mg; cbn [get_frame_header_m negb] in E.
  2: { apply (gfh3_base hb h E Hb). }
  destruct (Zlength hb <? 1) eqn:L1; [discriminate|]. apply Z.ltb_ge in L1.
  destruct (get_frame_header (magic_bytes ++ hb)) as [h0| |] eqn:E0; try discriminate.
  injection E as <-.
  assert (Hm: bytes_ok (magic_bytes ++ hb)).
  { apply Forall_app; split; [|exact Hb]. unfold magic_bytes, ZSTD_MAGICNUMBER; cbn.
    repeat constructor; unfold is_byte; lia. }
  destruct (gfh3_base _ _ E0 Hm) as [F H5].
  assert (HM: le_field (magic_bytes ++ hb) 0 4 = ZSTD_MAGICNUMBER).
  { unfold le_field, slice. change (Z.to_nat 0) with O. rewrite skipn_O.
    change (Z.to_nat 4) with (length magic_bytes). rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all. reflexivity. }
  unfold gfh3_facts in F |- *. rewrite HM in F. change (is_skippable_magic ZSTD_MAGICNUMBER) with false in F.
  destruct F as (_ & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  assert (T0: fh_frameType h0 = 0).
  { destruct F6 as [T|T]; [exact T|]. apply F7 in T. destruct T; discriminate. }
  unfold fh_unshift; cbn [fh_contentSize fh_windowSize fh_blockSizeMax fh_frameType fh_headerSize fh_dictID
    fh_checksumFlag]. unfold starting_len.
  rewrite T0.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F3|]. split; [lia|].
  split; [exact F5|]. split; [left; reflexivity|]. split; [split; [discriminate|intros [? _]; discriminate]|].
  split; [discriminate|]. lia.
Qed.

End CM_LH3Gfh_1.
