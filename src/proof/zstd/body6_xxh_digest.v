(* Body of ZSTD_XXH64_digest (group xxh).  Run 6: the proof of this body (body_xxh_state.v holds the group's other lemmas). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.
Require Import Zstd.proof.zstd.body_xxh_state.

(* ---------- the lanes are 64-bit values; the rest has length mod 32 ---------- *)

Definition xd_in_range (v: Z * Z * Z * Z) : Prop :=
  match v with (v1, v2, v3, v4) =>
    0 <= v1 <= Int64.max_unsigned /\ 0 <= v2 <= Int64.max_unsigned /\
    0 <= v3 <= Int64.max_unsigned /\ 0 <= v4 <= Int64.max_unsigned
  end.

Lemma xd_stripes_facts: forall n v l, xd_in_range v -> (length l <= n)%nat ->
  xd_in_range (fst (xxh_stripes n v l)) /\
  Z.of_nat (length (snd (xxh_stripes n v l))) = Z.of_nat (length l) mod 32.
Proof.
  induction n; intros v l Hv Hn.
  - destruct l; simpl in Hn; [|lia]. simpl. destruct v as [[[? ?] ?] ?]. auto.
  - cbn [xxh_stripes]. destruct v as [[[v1 v2] v3] v4].
    destruct (Z.of_nat (length l) <? 32) eqn:E.
    + apply Z.ltb_lt in E. simpl. split; auto. rewrite Z.mod_small; lia.
    + apply Z.ltb_ge in E. destruct (IHn (xxh_round v1 (le_field l 0 8), xxh_round v2 (le_field l 8 8),
          xxh_round v3 (le_field l 16 8), xxh_round v4 (le_field l 24 8)) (skipn 32 l)) as [A B].
      { simpl. auto using xxh_round_range. }
      { rewrite length_skipn. lia. }
      split; auto. rewrite B, length_skipn.
      rewrite Nat2Z.inj_sub by lia.
      replace (Z.of_nat (length l)) with ((Z.of_nat (length l) - 32) + 1 * 32) at 2 by lia.
      rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma xd_stripes_bytes: forall n v l, bytes_ok l -> bytes_ok (snd (xxh_stripes n v l)).
Proof.
  induction n; intros v l H. exact H.
  cbn [xxh_stripes]. destruct v as [[[v1 v2] v3] v4].
  destruct (Z.of_nat (length l) <? 32). exact H.
  apply IHn. unfold bytes_ok in *. rewrite <- (firstn_skipn 32 l) in H.
  apply Forall_app in H. tauto.
Qed.

Lemma xd_lanes_range: forall seed l, xd_in_range (xxh_lanes seed l).
Proof.
  intros. unfold xxh_lanes. apply xd_stripes_facts; auto.
  unfold xxh_init. simpl. auto using m64_range.
Qed.

Lemma xd_rest_length: forall seed l, Zlength (xxh_rest seed l) = m64 (Zlength l) mod 32.
Proof.
  intros. unfold xxh_rest. rewrite !Zlength_correct.
  destruct (xd_stripes_facts (length l) (xxh_init seed) l) as [_ B].
  { unfold xxh_init. simpl. auto using m64_range. }
  { lia. }
  rewrite B. unfold m64.
  apply Znumtheory.Zmod_div_mod; try lia. exists (2^59). reflexivity.
Qed.

Lemma xd_rest_bytes: forall seed l, bytes_ok l -> bytes_ok (xxh_rest seed l).
Proof. intros. apply xd_stripes_bytes; auto. Qed.

Definition xd_h (seed: Z) (l: list Z) : Z :=
  let v := xxh_lanes seed l in
  if m64 (Zlength l) >=? 32 then
    let h := m64 (rotl64 (xxh_lane1 v) 1 + rotl64 (xxh_lane2 v) 7 + rotl64 (xxh_lane3 v) 12 + rotl64 (xxh_lane4 v) 18) in
    xxh_merge (xxh_merge (xxh_merge (xxh_merge h (xxh_lane1 v)) (xxh_lane2 v)) (xxh_lane3 v)) (xxh_lane4 v)
  else m64 (xxh_lane3 v + XXH_P5).

Lemma xd_model: forall seed l,
  xxh64_digest_model seed l = xxh_finalize (m64 (xd_h seed l + m64 (Zlength l))) (xxh_rest seed l).
Proof. reflexivity. Qed.

(* ---------- mem64: the rest, then the junk; 8-aligned ---------- *)

Lemma xd_split: forall sh r junk p, 0 <= Zlength r <= 32 -> Zlength r + Zlength junk = 32 ->
  field_compatible (tarray tuchar 32) [] p ->
  data_at sh (tarray tuchar 32) (xxh_bytes r ++ junk) p =
  (data_at sh (tarray tuchar (Zlength r)) (xxh_bytes r) p *
   data_at sh (tarray tuchar (32 - Zlength r)) junk (offset_val (Zlength r) p))%logic.
Proof.
  intros. assert (Zlength (xxh_bytes r) = Zlength r) by (unfold xxh_bytes; apply Zlength_map).
  rewrite (split2_data_at_Tarray_tuchar sh 32 (Zlength r)) by (rewrite ?Zlength_app; lia).
  rewrite field_address0_offset by (apply arr_field_compatible0; auto; lia).
  simpl nested_field_offset. rewrite Z.add_0_l, Z.mul_1_l.
  rewrite sublist_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite H2, Z.sub_diag. rewrite sublist_same by lia.
  reflexivity.
Qed.

Lemma xd_mem64_align: forall st, field_compatible t_xxh64_state [] st ->
  exists b o, field_address t_xxh64_state (DOT _mem64) st = Vptr b o /\ (8 | Ptrofs.unsigned o).
Proof.
  intros st H.
  assert (F: field_compatible t_xxh64_state (DOT _mem64) st) by auto with field_compatible.
  rewrite field_compatible_field_address by auto.
  pose proof (field_compatible_nested_field _ _ _ F) as F2.
  destruct st; try (destruct H; contradiction).
  simpl in F2 |- *. eexists _, _; split; [reflexivity|].
  destruct F2 as [_ [_ [_ [A _]]]].
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ A 0 ltac:(lia)) as A'.
  apply align_compatible_rec_by_value_inv with (ch := Mint64) in A'; [|reflexivity].
  change (align_chunk Mint64) with 8 in A'. rewrite Z.mul_0_r, Z.add_0_r in A'. exact A'.
Qed.

Lemma body6_ZSTD_XXH64_digest: semax_body Vprog Gprog f_ZSTD_XXH64_digest ZSTD_XXH64_digest_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_xxh64_state [] st)
    by (sep_apply (xxh64_state_local_facts sh seed l st); entailer!).
  unfold xxh64_state. Intros junk.
  pose proof (xd_lanes_range seed l) as Hv.
  destruct (xxh_lanes seed l) as [[[v1 v2] v3] v4] eqn:Ev. simpl in Hv |- *.
  forward.
  forward_if (PROP () LOCAL (temp _h64 (Vlong (Int64.repr (xd_h seed l))); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l))) st;
         field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [v1; v2; v3; v4])) st;
         data_at sh (tarray tuchar 32) (xxh_bytes (xxh_rest seed l) ++ junk)
           (field_address t_xxh64_state (DOT _mem64) st);
         field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr (Zlength (xxh_rest seed l)))) st;
         field_at_ sh t_xxh64_state (DOT _reserved32) st;
         field_at_ sh t_xxh64_state (DOT _reserved64) st)).
  - forward. forward. forward. forward. forward. forward. forward. forward.
    forward.
    change (Int.unsigned (Int.repr 1)) with 1. change (Int.unsigned (Int.repr 7)) with 7.
    change (Int.unsigned (Int.repr 12)) with 12. change (Int.unsigned (Int.repr 18)) with 18.
    change (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 1))) with (64 - 1).
    change (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 7))) with (64 - 7).
    change (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 12))) with (64 - 12).
    change (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 18))) with (64 - 18).
    rewrite !rotl64_repr by lia. rewrite !add64_repr.
    set (h0 := rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18).
    rewrite <- (repr_m64 h0).
    deadvars!.
    forward. unfold Znth; simpl.
    forward_call (m64 h0, v1). { apply m64_range. }
    forward. forward. unfold Znth; simpl.
    forward_call (xxh_merge (m64 h0) v1, v2). { apply xxh_merge_range. }
    forward. forward. unfold Znth; simpl.
    forward_call (xxh_merge (xxh_merge (m64 h0) v1) v2, v3). { apply xxh_merge_range. }
    forward. forward. unfold Znth; simpl.
    forward_call (xxh_merge (xxh_merge (xxh_merge (m64 h0) v1) v2) v3, v4). { apply xxh_merge_range. }
    forward.
    entailer!.
    rewrite !unsigned_repr_m64 in H2. unfold xd_h. rewrite Ev. simpl xxh_lane1; simpl xxh_lane2; simpl xxh_lane3; simpl xxh_lane4.
    replace (m64 (Zlength l) >=? 32) with true by (symmetry; apply Z.geb_le; change (m64 32) with 32 in H2; lia).
    reflexivity.
  - forward. unfold Znth; simpl. forward.
    entailer!.
    rewrite !unsigned_repr_m64 in H2. unfold xd_h. rewrite Ev. simpl xxh_lane3.
    replace (m64 (Zlength l) >=? 32) with false by (rewrite Z.geb_leb; symmetry; apply Z.leb_gt; change (m64 32) with 32 in H2; lia).
    rewrite repr_m64. reflexivity.
  - forward. forward. forward.
    pose proof (xd_rest_length seed l) as Hr.
    assert (Hr32: 0 <= Zlength (xxh_rest seed l) < 32) by (rewrite Hr; apply Z.mod_pos_bound; lia).
    destruct (xd_mem64_align st H) as [b [o [Hp Ho]]].
    assert_PROP (field_compatible (tarray tuchar 32) [] (field_address t_xxh64_state (DOT _mem64) st)) by entailer!.
    rewrite (xd_split sh (xxh_rest seed l) junk) by (auto; lia).
    rewrite Hp in *. Intros.
    rewrite add64_repr, <- (repr_m64 (xd_h seed l + Zlength l)).
    forward_call (sh, m64 (xd_h seed l + Zlength l), Vptr b o, xxh_rest seed l, m64 (Zlength l), 0,
      pw_bytes sh (32 - Zlength (xxh_rest seed l)) junk (offset_val (Zlength (xxh_rest seed l)) (Vptr b o))).
    { entailer!. simpl. rewrite <- Hp.
      rewrite field_compatible_field_address by auto with field_compatible. rewrite !repr_m64. reflexivity. }
    { split; [apply m64_range|]. split; [apply m64_range|]. split; [apply xd_rest_bytes; auto|].
      split; [right; split; eauto|].
      intros E. simpl pw_pred. rewrite E. rewrite Ptrofs.add_zero. apply valid_pointer_weak'.
      apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia]. }
    assert (Heq: xxh_finalize (m64 (xd_h seed l + Zlength l)) (xxh_rest seed l) = xxh64_digest_model seed l).
    { rewrite xd_model. f_equal. unfold m64. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite Heq. forward.
    unfold xxh64_state. Exists junk. rewrite Ev. simpl pw_pred.
    simpl xxh_lane1; simpl xxh_lane2; simpl xxh_lane3; simpl xxh_lane4.
    rewrite Hp. rewrite (xd_split sh (xxh_rest seed l) junk) by (auto; lia).
    entailer!.
Qed.
