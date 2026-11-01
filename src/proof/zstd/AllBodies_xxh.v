(* The proof obligations of group(s) xxh (fields of ZstdBodies, in order).  Prove each
   conjunct by a body lemma `body_X` (in src/proof/zstd/body_<group>*.v files that this file Requires),
   or by `semax_body_vacuous` for a function whose specification stays vacuous. *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.body_xxh_read Zstd.proof.zstd.body_xxh_finalize Zstd.proof.zstd.body_xxh_oneshot Zstd.proof.zstd.body_xxh_update Zstd.proof.zstd.body_xxh_state.
Require Import Zstd.proof.zstd.body6_xxh_finalize Zstd.proof.zstd.body6_xxh_oneshot Zstd.proof.zstd.body6_xxh_update Zstd.proof.zstd.body6_xxh_reset Zstd.proof.zstd.body6_xxh_digest.

(* API v2 adaptations, kept local to this file: the model's xxh64 now tests m64 len >=? 32
   (eo_result*_v2 need the length bound), and ZSTD_XXH64_update_spec lends a list of witnesses. *)
Lemma eo_result_v2: forall seed bs, 32 <= Zlength bs -> Zlength bs <= Int64.max_unsigned ->
  xxh64 bs seed =
  xxh_finalize
    (m64 (xxh_merge (xxh_merge (xxh_merge (xxh_merge
       (m64 (rotl64 (xxh_lane1 (eo_v seed bs (Zlength bs / 32))) 1 + rotl64 (xxh_lane2 (eo_v seed bs (Zlength bs / 32))) 7 +
             rotl64 (xxh_lane3 (eo_v seed bs (Zlength bs / 32))) 12 + rotl64 (xxh_lane4 (eo_v seed bs (Zlength bs / 32))) 18))
       (xxh_lane1 (eo_v seed bs (Zlength bs / 32)))) (xxh_lane2 (eo_v seed bs (Zlength bs / 32))))
       (xxh_lane3 (eo_v seed bs (Zlength bs / 32)))) (xxh_lane4 (eo_v seed bs (Zlength bs / 32))) + Zlength bs))
    (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs).
Proof.
  intros seed bs Hn Hm. rewrite xxh64_br_eq by (rewrite <- Zlength_correct; rep_lia). unfold xxh64_br.
  rewrite <- Zlength_correct.
  rewrite (XxhLemmas.m64_small (Zlength bs)) by lia.
  replace (Zlength bs >=? 32) with true by (symmetry; apply Z.geb_le; lia).
  pose proof (Z.mul_div_le (Zlength bs) 32 ltac:(lia)).
  pose proof (Z_mod_lt (Zlength bs) 32 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (Zlength bs) 32).
  rewrite (xo_stripes_all (Z.to_nat (Zlength bs / 32))) by (rewrite <- Zlength_correct; lia).
  unfold eo_v. fold (xxh_init seed).
  replace (skipn (32 * Z.to_nat (Zlength bs / 32)) bs) with (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs).
  2: { unfold sublist. rewrite firstn_all2 by (rewrite <- ZtoNat_Zlength; lia). f_equal. lia. }
  destruct (fst _) as [[[a b] c] d]. reflexivity.
Qed.

Lemma eo_result_short_v2: forall seed bs, Zlength bs < 32 -> Zlength bs <= Int64.max_unsigned ->
  xxh64 bs seed = xxh_finalize (m64 (m64 (seed + XXH_P5) + Zlength bs)) (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs).
Proof.
  intros seed bs Hn Hm. pose proof (Zlength_nonneg bs).
  rewrite Z.div_small by lia. rewrite Z.mul_0_r, sublist_same by lia.
  rewrite xxh64_br_eq by (rewrite <- Zlength_correct; rep_lia). unfold xxh64_br. rewrite <- Zlength_correct.
  rewrite (XxhLemmas.m64_small (Zlength bs)) by lia.
  replace (Zlength bs >=? 32) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma body_XXH64_endian_align_v2: semax_body Vprog Gprog f_XXH64_endian_align XXH64_endian_align_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC. { entailer!. }
  forward_if (PROP () LOCAL (temp _input p; temp _len (Vlong (Int64.repr (Zlength bs)));
                 temp _seed (Vlong (Int64.repr seed)); temp _align (Vint (Int.repr 1)))
              SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { pose proof FC as [Pp _]. destruct p; try contradiction.
    change (denote_tc_test_eq (Vptr b i) (Vlong (Int64.repr 0)))
      with (!! (Int64.repr 0 = Int64.zero) && weak_valid_pointer (Vptr b i)).
    apply andp_right. apply prop_right; auto.
    destruct (zeq (Zlength bs) 0).
    - apply sepcon_weak_valid_pointer2. apply H1; auto.
    - apply sepcon_weak_valid_pointer1. eapply derives_trans; [|apply valid_pointer_weak].
      apply data_at_valid_ptr. auto. simpl. rep_lia. }
  { destruct FC as [Pp _]. subst p. contradiction. }
  { forward. entailer!. }
  assert (Pp: isptr p) by (destruct FC; auto).
  assert (Hlen: 0 <= Zlength bs < Ptrofs.modulus).
  { destruct FC as [_ [_ [Hs _]]]. destruct p; try contradiction. simpl in Hs.
    pose proof (Ptrofs.unsigned_range i). rewrite Z.max_r in Hs by rep_lia. rep_lia. }
  forward_if (EX h: Z,
    PROP (0 <= h <= Int64.max_unsigned;
          xxh64 bs seed = xxh_finalize (m64 (h + Zlength bs)) (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs))
    LOCAL (temp _input (offset_val (32 * (Zlength bs / 32)) p); temp _h64 (Vlong (Int64.repr h));
           temp _len (Vlong (Int64.repr (Zlength bs))); temp _align (Vint (Int.repr 1)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
  { rewrite Int64.unsigned_repr in H2 by rep_lia. change (Int64.unsigned (Int64.repr 32)) with 32 in H2.
    forward. forward. forward. forward. forward. forward.
    forward_loop (EX k: Z,
    PROP (0 <= k; 32 * k + 32 <= Zlength bs)
    LOCAL (temp _v4 (Vlong (Int64.repr (xxh_lane4 (eo_v seed bs (k)))));
           temp _v3 (Vlong (Int64.repr (xxh_lane3 (eo_v seed bs (k)))));
           temp _v2 (Vlong (Int64.repr (xxh_lane2 (eo_v seed bs (k)))));
           temp _v1 (Vlong (Int64.repr (xxh_lane1 (eo_v seed bs (k)))));
           temp _limit (offset_val (Zlength bs - 31) p); temp _input (offset_val (32 * k) p);
           temp _len (Vlong (Int64.repr (Zlength bs))); temp _seed (Vlong (Int64.repr seed)); temp _align (Vint (Int.repr 1)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w))
    continue: (EX k: Z,
    PROP (1 <= k; 32 * k <= Zlength bs)
    LOCAL (temp _v4 (Vlong (Int64.repr (xxh_lane4 (eo_v seed bs (k)))));
           temp _v3 (Vlong (Int64.repr (xxh_lane3 (eo_v seed bs (k)))));
           temp _v2 (Vlong (Int64.repr (xxh_lane2 (eo_v seed bs (k)))));
           temp _v1 (Vlong (Int64.repr (xxh_lane1 (eo_v seed bs (k)))));
           temp _limit (offset_val (Zlength bs - 31) p); temp _input (offset_val (32 * k) p);
           temp _len (Vlong (Int64.repr (Zlength bs))); temp _seed (Vlong (Int64.repr seed)); temp _align (Vint (Int.repr 1)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w))
    break: (PROP ()
    LOCAL (temp _v4 (Vlong (Int64.repr (xxh_lane4 (eo_v seed bs (Zlength bs / 32)))));
           temp _v3 (Vlong (Int64.repr (xxh_lane3 (eo_v seed bs (Zlength bs / 32)))));
           temp _v2 (Vlong (Int64.repr (xxh_lane2 (eo_v seed bs (Zlength bs / 32)))));
           temp _v1 (Vlong (Int64.repr (xxh_lane1 (eo_v seed bs (Zlength bs / 32)))));
           temp _input (offset_val (32 * (Zlength bs / 32)) p);
           temp _len (Vlong (Int64.repr (Zlength bs))); temp _seed (Vlong (Int64.repr seed)); temp _align (Vint (Int.repr 1)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)).
    { Exists 0. rewrite eo_limit by (auto; rep_lia).
      unfold eo_v, xxh_init. simpl fst. cbn [xxh_lane1 xxh_lane2 xxh_lane3 xxh_lane4].
      rewrite !XxhLemmas.repr_m64, XxhLemmas.P1_neg, XxhLemmas.P2_neg.
      entailer!. }
    { Intros k. pose proof (eo_v_range seed bs k) as [R1 [R2 [R3 R4]]].
    rewrite (xo_window sh bs (32 * k) p) by (auto; lia). Intros.
    forward_call (sh, offset_val (32 * k) p, sublist (32 * k) (32 * k + 8) bs, 1).
    { split; [rewrite Zlength_sublist by lia; lia | apply Forall_sublist; auto]. }
    forward_call (xxh_lane1 (eo_v seed bs k), le_value (sublist (32 * k) (32 * k + 8) bs)).
    { assert (0 <= le_value (sublist (32 * k) (32 * k + 8) bs) <= Int64.max_unsigned)
        by (apply eo_le8_range; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia]).
      repeat split; lia. }
    forward.
    gather_SEP (data_at _ (tarray tuchar 8) _ _) (xo_frame _ _ _ _).
    rewrite <- (xo_window sh bs (32 * k) p) by (auto; lia).
    forward.
    rewrite eo_add8, offset_offset_val by auto.
    replace (offset_val (32 * k + 8) p) with (offset_val (32 * k + 8) p) by (f_equal; lia).
    rewrite (xo_window sh bs (32 * k + 8) p) by (auto; lia). Intros.
    forward_call (sh, offset_val (32 * k + 8) p, sublist (32 * k + 8) (32 * k + 8 + 8) bs, 1).
    { split; [rewrite Zlength_sublist by lia; lia | apply Forall_sublist; auto]. }
    forward_call (xxh_lane2 (eo_v seed bs k), le_value (sublist (32 * k + 8) (32 * k + 8 + 8) bs)).
    { assert (0 <= le_value (sublist (32 * k + 8) (32 * k + 8 + 8) bs) <= Int64.max_unsigned)
        by (apply eo_le8_range; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia]).
      repeat split; lia. }
    forward.
    gather_SEP (data_at _ (tarray tuchar 8) _ _) (xo_frame _ _ _ _).
    rewrite <- (xo_window sh bs (32 * k + 8) p) by (auto; lia).
    forward.
    rewrite eo_add8, offset_offset_val by auto.
    replace (offset_val (32 * k + 8 + 8) p) with (offset_val (32 * k + 16) p) by (f_equal; lia).
    rewrite (xo_window sh bs (32 * k + 16) p) by (auto; lia). Intros.
    forward_call (sh, offset_val (32 * k + 16) p, sublist (32 * k + 16) (32 * k + 16 + 8) bs, 1).
    { split; [rewrite Zlength_sublist by lia; lia | apply Forall_sublist; auto]. }
    forward_call (xxh_lane3 (eo_v seed bs k), le_value (sublist (32 * k + 16) (32 * k + 16 + 8) bs)).
    { assert (0 <= le_value (sublist (32 * k + 16) (32 * k + 16 + 8) bs) <= Int64.max_unsigned)
        by (apply eo_le8_range; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia]).
      repeat split; lia. }
    forward.
    gather_SEP (data_at _ (tarray tuchar 8) _ _) (xo_frame _ _ _ _).
    rewrite <- (xo_window sh bs (32 * k + 16) p) by (auto; lia).
    forward.
    rewrite eo_add8, offset_offset_val by auto.
    replace (offset_val (32 * k + 16 + 8) p) with (offset_val (32 * k + 24) p) by (f_equal; lia).
    rewrite (xo_window sh bs (32 * k + 24) p) by (auto; lia). Intros.
    forward_call (sh, offset_val (32 * k + 24) p, sublist (32 * k + 24) (32 * k + 24 + 8) bs, 1).
    { split; [rewrite Zlength_sublist by lia; lia | apply Forall_sublist; auto]. }
    forward_call (xxh_lane4 (eo_v seed bs k), le_value (sublist (32 * k + 24) (32 * k + 24 + 8) bs)).
    { assert (0 <= le_value (sublist (32 * k + 24) (32 * k + 24 + 8) bs) <= Int64.max_unsigned)
        by (apply eo_le8_range; [apply Forall_sublist; auto | rewrite Zlength_sublist by lia; lia]).
      repeat split; lia. }
    forward.
    gather_SEP (data_at _ (tarray tuchar 8) _ _) (xo_frame _ _ _ _).
    rewrite <- (xo_window sh bs (32 * k + 24) p) by (auto; lia).
    forward.
    rewrite eo_add8, offset_offset_val by auto.
    replace (offset_val (32 * k + 24 + 8) p) with (offset_val (32 * (k + 1)) p) by (f_equal; lia).
    Exists (k + 1). rewrite (eo_step seed bs k) by lia.
    cbn [xxh_lane1 xxh_lane2 xxh_lane3 xxh_lane4]. entailer!. }
    { Intros k. forward_if.
      { apply eo_test_order; auto; lia. }
      { rewrite (eo_cmp (Zlength bs)) in H5 by (auto; lia).
        destruct (zlt _ _) as [Hlt|Hge]; [|unfold typed_true in H5; simpl in H5; discriminate].
        forward. Exists k. entailer!. }
      { rewrite (eo_cmp (Zlength bs)) in H5 by (auto; lia).
        destruct (zlt _ _) as [Hlt|Hge]; [unfold typed_false in H5; simpl in H5; discriminate|].
        assert (Hk: Zlength bs / 32 = k) by (symmetry; apply Z.div_unique with (Zlength bs - 32 * k); lia).
        forward. rewrite Hk. entailer!. } }
    pose proof (eo_v_range seed bs (Zlength bs / 32)) as [R1 [R2 [R3 R4]]].
    forward.
    change (Int64.repr (Int.unsigned (Int.repr 1))) with (Int64.repr 1).
    change (Int64.repr (Int.unsigned (Int.repr 7))) with (Int64.repr 7).
    change (Int64.repr (Int.unsigned (Int.repr 12))) with (Int64.repr 12).
    change (Int64.repr (Int.unsigned (Int.repr 18))) with (Int64.repr 18).
    change (Int64.repr (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 1)))) with (Int64.repr (64 - 1)).
    change (Int64.repr (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 7)))) with (Int64.repr (64 - 7)).
    change (Int64.repr (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 12)))) with (Int64.repr (64 - 12)).
    change (Int64.repr (Int.unsigned (Int.sub (Int.repr 64) (Int.repr 18)))) with (Int64.repr (64 - 18)).
    rewrite !XxhLemmas.rotl64_repr by lia. rewrite !add64_repr.
    set (V := eo_v seed bs (Zlength bs / 32)) in *.
    match goal with |- context [temp _h64 (Vlong (Int64.repr ?x))] => set (S0 := x) end.
    rewrite <- (XxhLemmas.repr_m64 S0).
    pose proof (XxhLemmas.m64_range S0) as RS.
    forward_call (m64 S0, xxh_lane1 V).
    pose proof (XxhLemmas.xxh_merge_range (m64 S0) (xxh_lane1 V)) as RM1.
    forward_call (xxh_merge (m64 S0) (xxh_lane1 V), xxh_lane2 V).
    pose proof (XxhLemmas.xxh_merge_range (xxh_merge (m64 S0) (xxh_lane1 V)) (xxh_lane2 V)) as RM2.
    forward_call (xxh_merge (xxh_merge (m64 S0) (xxh_lane1 V)) (xxh_lane2 V), xxh_lane3 V).
    pose proof (XxhLemmas.xxh_merge_range (xxh_merge (xxh_merge (m64 S0) (xxh_lane1 V)) (xxh_lane2 V)) (xxh_lane3 V)) as RM3.
    forward_call (xxh_merge (xxh_merge (xxh_merge (m64 S0) (xxh_lane1 V)) (xxh_lane2 V)) (xxh_lane3 V), xxh_lane4 V).
    forward.
    Exists (xxh_merge (xxh_merge (xxh_merge (xxh_merge (m64 S0) (xxh_lane1 V)) (xxh_lane2 V)) (xxh_lane3 V)) (xxh_lane4 V)).
    entailer!.
    split. apply XxhLemmas.xxh_merge_range. subst S0 V. apply eo_result_v2; rep_lia. }
  { forward. Exists (m64 (seed + XXH_P5)). entailer!.
    rewrite Int64.unsigned_repr in H2 by rep_lia. change (Int64.unsigned (Int64.repr 32)) with 32 in H2.
    split3. apply XxhLemmas.m64_range. apply eo_result_short_v2; auto; rep_lia. split.
    rewrite Z.div_small by lia. rewrite Z.mul_0_r, isptr_offset_val_zero by auto. auto.
    rewrite XxhLemmas.repr_m64. reflexivity. }
  Intros h. forward.
  rewrite add64_repr, <- (XxhLemmas.repr_m64 (h + Zlength bs)).
  pose proof (Z.mul_div_le (Zlength bs) 32 ltac:(lia)).
  pose proof (Z_mod_lt (Zlength bs) 32 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (Zlength bs) 32).
  assert (Hm: 0 <= 32 * (Zlength bs / 32)) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]).
  rewrite (xo_split sh bs (32 * (Zlength bs / 32)) p) by (auto; lia).
  assert (Hsub: Zlength (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs) = Zlength bs mod 32)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hok: bytes_ok (sublist (32 * (Zlength bs / 32)) (Zlength bs) bs)) by (apply Forall_sublist; auto).
  Intros.
  destruct (zeq (Zlength bs) 0) as [E|E].
  - forward_call (sh, m64 (h + Zlength bs), offset_val (32 * (Zlength bs / 32)) p,
                  sublist (32 * (Zlength bs / 32)) (Zlength bs) bs, Zlength bs, 1, w).
    { split. apply XxhLemmas.m64_range.
      intros _. rewrite E. change (32 * (0 / 32)) with 0. rewrite isptr_offset_val_zero by auto. apply H1; auto. }
    rewrite <- H3. forward.
    rewrite (xo_split sh bs (32 * (Zlength bs / 32)) p) by (auto; lia). entailer!.
  - forward_call (sh, m64 (h + Zlength bs), offset_val (32 * (Zlength bs / 32)) p,
                  sublist (32 * (Zlength bs / 32)) (Zlength bs) bs, Zlength bs, 1,
                  pw_bytes sh (32 * (Zlength bs / 32)) (xxh_bytes (sublist 0 (32 * (Zlength bs / 32)) bs)) p).
    { split. apply XxhLemmas.m64_range.
      intros Hz. unfold pw_pred.
      eapply derives_trans; [apply data_at_memory_block|].
      apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia. }
    rewrite <- H3. forward. unfold pw_pred.
    rewrite (xo_split sh bs (32 * (Zlength bs / 32)) p) by (auto; lia). entailer!.
Qed.

Lemma body_ZSTD_XXH64_update_v2: semax_body Vprog Gprog f_ZSTD_XXH64_update ZSTD_XXH64_update_spec.
Proof.
  start_function.
  assert_PROP (field_compatible t_xxh64_state [] st)
    by (sep_apply (XxhLemmas.xxh64_state_local_facts sh seed l st); entailer!).
  unfold xxh64_state. Intros junk.
  set (r := xxh_rest seed l) in *.
  set (v := xxh_lanes seed l) in *.
  pose proof (xxh_rest_length seed l) as Hr. fold r in Hr.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) by entailer!.
  assert_PROP (Zlength junk = 32 - Zlength r) by entailer!.
  forward_if (PROP () LOCAL (temp _state st; temp _input p; temp _len (Vlong (Int64.repr (Zlength bs)))) SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 v; xxh_lane2 v; xxh_lane3 v; xxh_lane4 v])) st; data_at sh (tarray tuchar 32) (xxh_bytes r ++ junk) (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr (Zlength r))) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws)).
  { assert (Hp: isptr p) by (destruct H5; auto). destruct p; try contradiction.
    eapply derives_trans; [|apply xu_test_eq_ptr].
    destruct (Z.eq_dec (Zlength bs) 0) as [E|E].
    - sep_apply (H1 E). repeat apply sepcon_weak_valid_pointer1. apply derives_refl.
    - apply sepcon_weak_valid_pointer1. repeat apply sepcon_weak_valid_pointer2.
      apply xu_bytes_wvp; auto. pose proof (Zlength_nonneg bs). lia. }
  { assert (Hp: isptr p) by (destruct H5; auto). subst p. contradiction. }
  { forward. entailer!. }
  assert (Hp: isptr p) by (destruct H5; auto).
  pose proof (Zlength_nonneg bs) as Hbs0.
  pose proof (Zlength_nonneg r) as Hr0.
  forward. forward. forward. forward. forward.
  assert (EB: force_val (sem_binary_operation' Oadd (tptr tuchar) tulong p (Vlong (Int64.repr (Zlength bs)))) = offset_val (Zlength bs) p)
    by (destruct p; try contradiction; simpl; rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_int64;
        rewrite Int64.unsigned_repr by rep_lia; reflexivity).
  rewrite EB, add64_repr. clear EB.
  forward_if (PROP (32 <= Zlength r + Zlength bs) LOCAL (temp _bEnd (offset_val (Zlength bs) p); temp _p p; temp _state st; temp _input p) SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 v; xxh_lane2 v; xxh_lane3 v; xxh_lane4 v])) st; data_at sh (tarray tuchar 32) (xxh_bytes r ++ junk) (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr (Zlength r))) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws)).
  { (* small: buffer the input *)
    rewrite Int.unsigned_repr, add64_repr, !Int64.unsigned_repr in H7 by rep_lia.
    assert_PROP (field_compatible (tarray tuchar 32) [] (field_address t_xxh64_state (DOT _mem64) st)) by entailer!.
    forward.
    sep_apply (xu_mem_split sh r junk (Zlength bs) (field_address t_xxh64_state (DOT _mem64) st)); try lia; auto.
    Intros.
    forward_call (shi, sh, p, offset_val (Zlength r) (field_address t_xxh64_state (DOT _mem64) st), existT (fun t => reptype t) (tarray tuchar (Zlength bs)) (xxh_bytes bs)).
    1: entailer!; rewrite field_address_offset by auto with field_compatible; rewrite offset_offset_val; simpl; rewrite Z.max_r, Z.mul_1_l by lia; reflexivity.
    1: (unfold xxh_bytes; memcpy_side).
    simpl projT1; simpl projT2.
    forward. forward. forward.
    rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    destruct (xxh_app_small seed l bs) as [E1 E2]. { fold r. rewrite Zlength_app; lia. }
    unfold xxh64_state. rewrite E1, E2. fold r. fold v. Exists (sublist (Zlength bs) (Zlength junk) junk).
    sep_apply (xu_mem_join sh r bs (sublist (Zlength bs) (Zlength junk) junk) (Zlength bs) (field_address t_xxh64_state (DOT _mem64) st)).
    { rewrite Zlength_sublist by lia. lia. }
    rewrite !Zlength_app. entailer!. apply Forall_app; auto. }
  { rewrite Int.unsigned_repr, add64_repr, !Int64.unsigned_repr in H7 by rep_lia.
    forward. entailer!. }
  Intros.
  forward.
  forward_if (EX k: Z, EX m: list val,
    PROP (0 <= k <= Zlength bs; xxh_rest seed (l ++ sublist 0 k bs) = []; Zlength m = 32)
    LOCAL (temp _bEnd (offset_val (Zlength bs) p); temp _p (offset_val k p); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed (l ++ sublist 0 k bs)); xxh_lane2 (xxh_lanes seed (l ++ sublist 0 k bs)); xxh_lane3 (xxh_lanes seed (l ++ sublist 0 k bs)); xxh_lane4 (xxh_lanes seed (l ++ sublist 0 k bs))])) st; data_at sh (tarray tuchar 32) m (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr 0)) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws))%assert.
  { (* fill the buffer to 32 bytes and consume it *)
    assert (Er: Zlength r <> 0) by (intro E; apply H8; rewrite E; reflexivity).
    assert_PROP (field_compatible (tarray tuchar 32) [] (field_address t_xxh64_state (DOT _mem64) st)) by entailer!.
    forward. forward.
    sep_apply (xu_mem_split sh r junk (Zlength junk) (field_address t_xxh64_state (DOT _mem64) st)); try lia; auto.
    rewrite (xu_split2 shi bs (Zlength junk) p) by (auto; lia).
    Intros.
    forward_call (shi, sh, p, offset_val (Zlength r) (field_address t_xxh64_state (DOT _mem64) st), existT (fun t => reptype t) (tarray tuchar (Zlength junk)) (xxh_bytes (sublist 0 (Zlength junk) bs))).
    1: entailer!; rewrite field_address_offset by auto with field_compatible; rewrite offset_offset_val; simpl; rewrite Int.unsigned_repr by rep_lia; rewrite Z.max_r, Z.mul_1_l by lia; rewrite H4; reflexivity.
    1: (unfold xxh_bytes; memcpy_side).
    simpl projT1; simpl projT2.
    sep_apply (xu_split2_fold shi bs (Zlength junk) p); try lia.
    sep_apply (xu_mem_join sh r (sublist 0 (Zlength junk) bs) (sublist (Zlength junk) (Zlength junk) junk) (Zlength junk) (field_address t_xxh64_state (DOT _mem64) st)); try (rewrite Zlength_sublist by lia; lia).
    rewrite sublist_nil, app_nil_r.
    set (c := sublist 0 (Zlength junk) bs).
    assert (Hc: Zlength (r ++ c) = 32) by (unfold c; rewrite Zlength_app, Zlength_sublist by lia; lia).
    assert (Hcb: bytes_ok (r ++ c)) by (apply Forall_app; split; [apply xu_rest_bytes; auto | apply xu_bytes_ok_sublist; auto]).
    pose proof (xu_lanes_rng seed l) as Hv. fold v in Hv. destruct Hv as [Hv1 [Hv2 [Hv3 Hv4]]].
    rewrite (xu_window sh 32 (r ++ c) 0) by (auto; lia). Intros.
    forward_call (sh, offset_val 0 (field_address t_xxh64_state (DOT _mem64) st), sublist 0 (0 + 8) (r ++ c)).
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane1 v, le_value (sublist 0 (0 + 8) (r ++ c))).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold sh 32 (r ++ c) 0 (field_address t_xxh64_state (DOT _mem64) st)); try lia.
    rewrite (xu_window sh 32 (r ++ c) 8) by (auto; lia). Intros.
    forward_call (sh, offset_val 8 (field_address t_xxh64_state (DOT _mem64) st), sublist 8 (8 + 8) (r ++ c)).
    1: entailer!; rewrite field_address_offset by auto with field_compatible; rewrite offset_offset_val; reflexivity.
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane2 v, le_value (sublist 8 (8 + 8) (r ++ c))).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold sh 32 (r ++ c) 8 (field_address t_xxh64_state (DOT _mem64) st)); try lia.
    rewrite (xu_window sh 32 (r ++ c) 16) by (auto; lia). Intros.
    forward_call (sh, offset_val 16 (field_address t_xxh64_state (DOT _mem64) st), sublist 16 (16 + 8) (r ++ c)).
    1: entailer!; rewrite field_address_offset by auto with field_compatible; rewrite offset_offset_val; reflexivity.
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane3 v, le_value (sublist 16 (16 + 8) (r ++ c))).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold sh 32 (r ++ c) 16 (field_address t_xxh64_state (DOT _mem64) st)); try lia.
    rewrite (xu_window sh 32 (r ++ c) 24) by (auto; lia). Intros.
    forward_call (sh, offset_val 24 (field_address t_xxh64_state (DOT _mem64) st), sublist 24 (24 + 8) (r ++ c)).
    1: entailer!; rewrite field_address_offset by auto with field_compatible; rewrite offset_offset_val; reflexivity.
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane4 v, le_value (sublist 24 (24 + 8) (r ++ c))).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold sh 32 (r ++ c) 24 (field_address t_xxh64_state (DOT _mem64) st)); try lia.
    forward. forward. forward.
    destruct (xxh_app_fill seed l c Hc) as [F1 F2].
    Exists (Zlength junk) (xxh_bytes (r ++ c)). fold c.
    rewrite F1, F2, xu_round4_eq, !xu_le_field by lia. fold v. simpl app.
    entailer!. f_equal. lia. }
  { (* empty buffer *)
    assert (Er: Zlength r = 0) by (apply repr_inj_unsigned; [rep_lia | rep_lia | auto]).
    assert (Er': xxh_rest seed l = []) by (apply Zlength_nil_inv; auto).
    forward. Exists 0 (xxh_bytes r ++ junk).
    rewrite sublist_nil, app_nil_r. fold r v. rewrite Er. entailer!. }
  Intros k m.
  assert (Hsb: forall a c, is_true (sameblock (offset_val a p) (offset_val c p)))
    by (intros; destruct p; try contradiction; unfold sameblock; simpl; destruct (peq b b); [reflexivity | contradiction]).
  forward_if (EX j: Z,
    PROP (k <= j <= Zlength bs; Zlength bs - j < 32; xxh_rest seed (l ++ sublist 0 j bs) = [])
    LOCAL (temp _bEnd (offset_val (Zlength bs) p); temp _p (offset_val j p); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs))])) st; data_at sh (tarray tuchar 32) m (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr 0)) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws))%assert.
  { rewrite xu_sub_pp in H11 by auto. unfold typed_true in H11. simpl in H11. change (Int.signed (Int.repr 32)) with 32 in H11.
    assert (Hge: 32 <= Zlength bs - k).
    { destruct (Int64.ltu _ _) eqn:E in H11; simpl in H11; try discriminate. unfold Int64.ltu in E.
      rewrite !Int64.unsigned_repr in E by rep_lia. destruct (zlt _ _) in E; try discriminate. lia. }
    clear H11. forward. rewrite xu_sub_pi by auto.
    forward_loop (EX j: Z,
    PROP (k <= j; j + 32 <= Zlength bs; xxh_rest seed (l ++ sublist 0 j bs) = [])
    LOCAL (temp _limit (offset_val (Zlength bs - 32) p); temp _bEnd (offset_val (Zlength bs) p); temp _p (offset_val j p); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs))])) st; data_at sh (tarray tuchar 32) m (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr 0)) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws))%assert
      continue: (EX j: Z,
    PROP (k + 32 <= j <= Zlength bs; xxh_rest seed (l ++ sublist 0 j bs) = [])
    LOCAL (temp _limit (offset_val (Zlength bs - 32) p); temp _bEnd (offset_val (Zlength bs) p); temp _p (offset_val j p); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs))])) st; data_at sh (tarray tuchar 32) m (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr 0)) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws))%assert
      break: (EX j: Z,
    PROP (k <= j <= Zlength bs; Zlength bs - j < 32; xxh_rest seed (l ++ sublist 0 j bs) = [])
    LOCAL (temp _bEnd (offset_val (Zlength bs) p); temp _p (offset_val j p); temp _state st)
    SEP (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l + Zlength bs))) st; field_at sh t_xxh64_state (DOT _v) (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs)); xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs))])) st; data_at sh (tarray tuchar 32) m (field_address t_xxh64_state (DOT _mem64) st); field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr 0)) st; field_at_ sh t_xxh64_state (DOT _reserved32) st; field_at_ sh t_xxh64_state (DOT _reserved64) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws))%assert.
    { Exists k. entailer!. }
    { Intros j. pose proof (xu_lanes_rng seed (l ++ sublist 0 j bs)) as Hv. destruct Hv as [Hv1 [Hv2 [Hv3 Hv4]]].
    rewrite (xu_window shi (Zlength bs) bs j p) by (auto; lia). Intros.
    forward_call (shi, offset_val j p, sublist j (j + 8) bs).
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane1 (xxh_lanes seed (l ++ sublist 0 j bs)), le_value (sublist j (j + 8) bs)).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold shi (Zlength bs) bs j p); try lia.
    forward. rewrite xu_add_pi by auto. 
    rewrite (xu_window shi (Zlength bs) bs (j + 8) p) by (auto; lia). Intros.
    forward_call (shi, offset_val (j + 8) p, sublist (j + 8) ((j + 8) + 8) bs).
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane2 (xxh_lanes seed (l ++ sublist 0 j bs)), le_value (sublist (j + 8) ((j + 8) + 8) bs)).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold shi (Zlength bs) bs (j + 8) p); try lia.
    forward. rewrite xu_add_pi by auto. replace (j + 8 + 8) with (j + 16) by lia.
    rewrite (xu_window shi (Zlength bs) bs (j + 16) p) by (auto; lia). Intros.
    forward_call (shi, offset_val (j + 16) p, sublist (j + 16) ((j + 16) + 8) bs).
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane3 (xxh_lanes seed (l ++ sublist 0 j bs)), le_value (sublist (j + 16) ((j + 16) + 8) bs)).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold shi (Zlength bs) bs (j + 16) p); try lia.
    forward. rewrite xu_add_pi by auto. replace (j + 16 + 8) with (j + 24) by lia.
    rewrite (xu_window shi (Zlength bs) bs (j + 24) p) by (auto; lia). Intros.
    forward_call (shi, offset_val (j + 24) p, sublist (j + 24) ((j + 24) + 8) bs).
    1: split; [rewrite Zlength_sublist by lia; lia | apply xu_bytes_ok_sublist; auto].
    forward.
    forward_call (xxh_lane4 (xxh_lanes seed (l ++ sublist 0 j bs)), le_value (sublist (j + 24) ((j + 24) + 8) bs)).
    1: apply xu_le8_range; [apply xu_bytes_ok_sublist; auto | rewrite Zlength_sublist by lia; lia].
    forward.
    sep_apply (xu_window_fold shi (Zlength bs) bs (j + 24) p); try lia.
    forward. rewrite xu_add_pi by auto. replace (j + 24 + 8) with (j + 32) by lia.
    destruct (xu_chunk_lanes seed l bs j) as [F1 F2]; auto; try lia.
    Exists (j + 32). rewrite F1, F2. entailer!.
    cbn [xxh_lane1 xxh_lane2 xxh_lane3 xxh_lane4].
    replace (j + 8 + 8) with (j + 16) by lia. replace (j + 16 + 8) with (j + 24) by lia.
    replace (j + 24 + 8) with (j + 32) by lia. apply derives_refl. }
    { Intros j.
      assert (Hwv: forall a, 0 <= a <= Zlength bs -> data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p |-- weak_valid_pointer (offset_val a p))
        by (intros; apply xu_wvp_off; auto; lia).
      destruct (xu_cmp p (Zlength bs) j (Zlength bs - 32)) as [Cle Clt]; auto; try lia.
      forward_if.
      { apply xu_test_order'; auto.
        - sep_apply (Hwv j ltac:(lia)). xu_wvp_find.
        - sep_apply (Hwv (Zlength bs - 32) ltac:(lia)). xu_wvp_find. }
      { rewrite Cle in H13. unfold typed_true in H13. simpl in H13.
        destruct (j <=? Zlength bs - 32) eqn:E; simpl in H13; try discriminate. apply Z.leb_le in E.
        forward. Exists j. entailer!. }
      { rewrite Cle in H13. unfold typed_false in H13. simpl in H13.
        destruct (j <=? Zlength bs - 32) eqn:E; simpl in H13; try discriminate. apply Z.leb_gt in E.
        forward. Exists j. entailer!. } }
    { Intros j. Exists j. entailer!. } }
  { rewrite xu_sub_pp in H11 by auto. unfold typed_false in H11. simpl in H11. change (Int.signed (Int.repr 32)) with 32 in H11.
    assert (Hlt: Zlength bs - k < 32).
    { destruct (Int64.ltu _ _) eqn:E in H11; simpl in H11; try discriminate. unfold Int64.ltu in E.
      rewrite !Int64.unsigned_repr in E by rep_lia. destruct (zlt _ _) in E; try discriminate. lia. }
    forward. Exists k. entailer!. }
  Intros j.
  assert (Hwv: forall a, 0 <= a <= Zlength bs -> data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p |-- weak_valid_pointer (offset_val a p))
    by (intros; apply xu_wvp_off; auto; lia).
  destruct (xu_cmp p (Zlength bs) j (Zlength bs)) as [Cle Clt]; auto; try lia.
  forward_if (PROP () LOCAL (temp _state st)
    SEP (xxh64_state sh seed (l ++ bs) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws)).
  { apply xu_test_order'; auto.
    - sep_apply (Hwv j ltac:(lia)). xu_wvp_find.
    - sep_apply (Hwv (Zlength bs) ltac:(lia)). xu_wvp_find. }
  { rewrite Clt in H14. unfold typed_true in H14. simpl in H14.
    destruct (j <? Zlength bs) eqn:E; simpl in H14; try discriminate. apply Z.ltb_lt in E.
    assert_PROP (field_compatible (tarray tuchar 32) [] (field_address t_xxh64_state (DOT _mem64) st)) by entailer!.
    sep_apply (xu_mem_split0 sh m (Zlength bs - j) (field_address t_xxh64_state (DOT _mem64) st)); auto; try lia.
    rewrite (xu_split2 shi bs j p) by (auto; lia). Intros.
    forward_call (shi, sh, offset_val j p, (field_address t_xxh64_state (DOT _mem64) st), existT (fun t => reptype t) (tarray tuchar (Zlength bs - j)) (xxh_bytes (sublist j (Zlength bs) bs))).
    1: entailer!.
    1: (simpl; intros; try apply prop_right; rewrite xu_sub_pp by auto; rewrite field_address_offset by auto with field_compatible; simpl;
        rewrite Z.max_r, Z.mul_1_l by lia; reflexivity).
    1: (unfold xxh_bytes; memcpy_side).
    simpl projT1; simpl projT2.
    forward.
    1: entailer!; apply prop_right; apply Hsb.
    rewrite xu_sub_pp by auto. simpl force_val. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    set (c := sublist j (Zlength bs) bs).
    assert (Hc: Zlength c = Zlength bs - j) by (unfold c; rewrite Zlength_sublist by lia; lia).
    destruct (xxh_app_small seed (l ++ sublist 0 j bs) c) as [F1 F2]. { rewrite H13. simpl. lia. }
    assert (El: l ++ bs = (l ++ sublist 0 j bs) ++ c) by (unfold c; rewrite <- app_assoc, sublist_rejoin, sublist_same by lia; reflexivity).
    unfold xxh64_state. Exists (sublist (Zlength bs - j) 32 m).
    rewrite El, F1, F2, H13. simpl app.
    sep_apply (xu_split2_fold shi bs j p); try lia.
    sep_apply (xu_mem_join0 sh c (sublist (Zlength bs - j) 32 m) (Zlength bs - j) (field_address t_xxh64_state (DOT _mem64) st)); auto; try (rewrite Zlength_sublist by lia; lia).
    entailer!.
    - rewrite <- El. split. apply Forall_app; auto. rewrite Zlength_sublist by lia; lia.
    - rewrite <- El, Zlength_app, Hc. apply derives_refl. }
  { rewrite Clt in H14. unfold typed_false in H14. simpl in H14.
    destruct (j <? Zlength bs) eqn:E; simpl in H14; try discriminate. apply Z.ltb_ge in E.
    assert (j = Zlength bs) by lia. subst j.
    forward. unfold xxh64_state. Exists m. rewrite sublist_same in * by lia.
    rewrite H13. entailer!.
    - apply Forall_app; auto.
    - rewrite Zlength_app. apply derives_refl. }
  forward.
Qed.

Lemma bodies_xxh :
  semax_body Vprog Gprog f_XXH_memcpy XXH_memcpy_spec /\
  semax_body Vprog Gprog f_XXH_read32 XXH_read32_spec /\
  semax_body Vprog Gprog f_XXH_readLE32 XXH_readLE32_spec /\
  semax_body Vprog Gprog f_XXH_readLE32_align XXH_readLE32_align_spec /\
  semax_body Vprog Gprog f_XXH_read64 XXH_read64_spec /\
  semax_body Vprog Gprog f_XXH_readLE64 XXH_readLE64_spec /\
  semax_body Vprog Gprog f_XXH_readLE64_align XXH_readLE64_align_spec /\
  semax_body Vprog Gprog f_XXH64_round XXH64_round_spec /\
  semax_body Vprog Gprog f_XXH64_mergeRound XXH64_mergeRound_spec /\
  semax_body Vprog Gprog f_XXH64_avalanche XXH64_avalanche_spec /\
  semax_body Vprog Gprog f_XXH64_finalize XXH64_finalize_spec /\
  semax_body Vprog Gprog f_XXH64_endian_align XXH64_endian_align_spec /\
  semax_body Vprog Gprog f_ZSTD_XXH64 ZSTD_XXH64_spec /\
  semax_body Vprog Gprog f_ZSTD_XXH64_reset ZSTD_XXH64_reset_spec /\
  semax_body Vprog Gprog f_ZSTD_XXH64_update ZSTD_XXH64_update_spec /\
  semax_body Vprog Gprog f_ZSTD_XXH64_digest ZSTD_XXH64_digest_spec.
Proof.
  split; [exact body_XXH_memcpy |].
  split; [exact body_XXH_read32 |].
  split; [exact body_XXH_readLE32 |].
  split; [exact body_XXH_readLE32_align |].
  split; [exact body_XXH_read64 |].
  split; [exact body_XXH_readLE64 |].
  split; [exact body_XXH_readLE64_align |].
  split; [exact body_XXH64_round |].
  split; [exact body_XXH64_mergeRound |].
  split; [exact body_XXH64_avalanche |].
  split; [exact body6_XXH64_finalize |].
  split; [exact body_XXH64_endian_align_v2 |].
  split; [exact body_ZSTD_XXH64 |].
  split; [exact body6_ZSTD_XXH64_reset |].
  split; [exact body_ZSTD_XXH64_update_v2 |].
  exact body6_ZSTD_XXH64_digest.
Qed.