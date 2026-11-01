(* The body of the harness's own XXH64 (harness/ck_xxh64.c, xxh64): it computes the model's xxh64 bs seed
   (src/proof/model/Xxh64.v) for any length and seed.  The plain-Coq lemmas on 64-bit words and on the
   model's stripes and tails are the writer's (src/proof/harness/writer/XxhLemmas.v, there for seed 0). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.ck_xxh64.Specs_ck_xxh64.
Require Import Zstd.proof.harness.writer.XxhLemmas.
Local Open Scope logic.

(* the four accumulators of the stripes for a seed *)
Definition xxh_init_seed (seed: Z) : Z * Z * Z * Z :=
  (m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)).

(* XXH64 of at least 32 bytes: the stripes, the merge of the accumulators, then the tail *)
Lemma xxh64_long_seed (bs: list Z) (seed v1 v2 v3 v4: Z) (rest: list Z) :
  32 <= Zlength bs -> Zlength bs <= Int64.max_unsigned ->
  xxh_stripes (length bs) (xxh_init_seed seed) bs = ((v1, v2, v3, v4), rest) ->
  xxh64 bs seed = xxh_fin8 4 (m64 (xxh_mergeall v1 v2 v3 v4 + Zlength bs)) rest.
Proof.
  intros H Hb E. rewrite xxh64_br_eq by (rewrite <- Zlength_correct; rep_lia). unfold xxh64_br.
  rewrite <- Zlength_correct.
  replace (m64 (Zlength bs)) with (Zlength bs)
    by (unfold m64; rewrite Z.mod_small; [reflexivity | rep_lia]).
  destruct (Zlength bs >=? 32) eqn:E2; [|lia].
  unfold xxh_init_seed in E. rewrite E, xxh_finalize_fin8. unfold xxh_mergeall. reflexivity.
Qed.

(* XXH64 of fewer than 32 bytes: the tail alone, from seed + PRIME64_5 *)
Lemma xxh64_short_seed (bs: list Z) (seed: Z) :
  Zlength bs < 32 -> 0 <= Zlength bs ->
  xxh64 bs seed = xxh_fin8 4 (m64 (m64 (seed + XXH_P5) + Zlength bs)) bs.
Proof.
  intros H Hb. rewrite xxh64_br_eq by (rewrite <- Zlength_correct; lia). unfold xxh64_br.
  rewrite <- Zlength_correct.
  replace (m64 (Zlength bs)) with (Zlength bs)
    by (unfold m64; rewrite Z.mod_small; [reflexivity | lia]).
  destruct (Zlength bs >=? 32) eqn:E2; [lia|]. rewrite xxh_finalize_fin8. reflexivity.
Qed.

Ltac rng := first [ assumption | apply m64_range | apply xxh_merge_range | apply xxh_round_range
                  | apply rotl64_range | (apply le_field_range; auto; lia) | (apply lxor_range; rng)
                  | (apply shiftr_range; [rng | lia]) | split; rng | lia ].

(* The pointer p advances through the input: in every loop, after i bytes, p holds offset_val i p and left holds
   len - i; the model's state is the rest of the input, skipn i bs.  Each loop keeps the equation between
   xxh64 bs seed and the model's remaining computation (stripes, 8-byte, 4-byte, 1-byte steps, avalanche). *)
Lemma body_xxh64 : semax_body Vprog G f_xxh64 xxh64_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength bs)) [] p) as FC by entailer!.
  assert (ISP: isptr p) by (destruct FC; auto).
  forward. forward.
  forward_if (EX i: Z, EX h: Z,
    PROP (0 <= i <= Zlength bs; Zlength bs - i < 32; 0 <= h <= Int64.max_unsigned;
          xxh64 bs seed = xxh_fin8 4 (m64 (h + Zlength bs)) (skipn (Z.to_nat i) bs))
    LOCAL (temp _acc (Vlong (Int64.repr h)); temp _left (Vlong (Int64.repr (Zlength bs - i)));
           temp _p (offset_val i p); temp _len (Vlong (Int64.repr (Zlength bs))))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)).
  - rewrite !Int64.unsigned_repr in H2 by rep_lia.
    forward. forward. forward. forward.
    forward_loop (EX i: Z, EX v1: Z, EX v2: Z, EX v3: Z, EX v4: Z, EX n: nat,
      PROP (0 <= i <= Zlength bs; 32 * Z.of_nat n >= Zlength bs - i;
            0 <= v1 <= Int64.max_unsigned; 0 <= v2 <= Int64.max_unsigned;
            0 <= v3 <= Int64.max_unsigned; 0 <= v4 <= Int64.max_unsigned;
            xxh_stripes (length bs) (xxh_init_seed seed) bs = xxh_stripes n (v1, v2, v3, v4) (skipn (Z.to_nat i) bs))
      LOCAL (temp _acc1 (Vlong (Int64.repr v1)); temp _acc2 (Vlong (Int64.repr v2));
             temp _acc3 (Vlong (Int64.repr v3)); temp _acc4 (Vlong (Int64.repr v4));
             temp _left (Vlong (Int64.repr (Zlength bs - i))); temp _p (offset_val i p);
             temp _len (Vlong (Int64.repr (Zlength bs))))
      SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p))
    break: (EX i: Z, EX v1: Z, EX v2: Z, EX v3: Z, EX v4: Z,
      PROP (0 <= i <= Zlength bs; Zlength bs - i < 32;
            0 <= v1 <= Int64.max_unsigned; 0 <= v2 <= Int64.max_unsigned;
            0 <= v3 <= Int64.max_unsigned; 0 <= v4 <= Int64.max_unsigned;
            xxh_stripes (length bs) (xxh_init_seed seed) bs = ((v1, v2, v3, v4), skipn (Z.to_nat i) bs))
      LOCAL (temp _acc1 (Vlong (Int64.repr v1)); temp _acc2 (Vlong (Int64.repr v2));
             temp _acc3 (Vlong (Int64.repr v3)); temp _acc4 (Vlong (Int64.repr v4));
             temp _left (Vlong (Int64.repr (Zlength bs - i))); temp _p (offset_val i p);
             temp _len (Vlong (Int64.repr (Zlength bs))))
      SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)).
    + Exists 0 (m64 (seed + XXH_P1 + XXH_P2)) (m64 (seed + XXH_P2)) (m64 seed) (m64 (seed - XXH_P1)) (length bs).
      entailer!.
      split. { rewrite Zlength_correct; lia. }
      refine (conj (m64_range _) (conj (m64_range _) (conj (m64_range _) (conj (m64_range _) _)))).
      rewrite !repr64_m64.
      split; [|split; [|split]]; f_equal; apply repr64_eq_mod; try reflexivity.
      * apply mod64_shift with (-2); unfold XXH_P1, XXH_P2; lia.
      * apply mod64_shift with (-1); unfold XXH_P1, XXH_P2; lia.
      * apply mod64_shift with 1; unfold XXH_P1, XXH_P2; lia.
    + Intros i v1 v2 v3 v4 n.
      forward_if.
      2: { rewrite !Int64.unsigned_repr in H10 by rep_lia. forward. Exists i v1 v2 v3 v4. entailer!.
           rewrite H9, xxh_stripes_done by (rewrite length_skipn_Z by lia; lia). reflexivity. }
      rewrite !Int64.unsigned_repr in H10 by rep_lia.
      destruct n as [|n]; [simpl in H4; lia|].
      forward_call (sh, p, bs, i, 8).
      forward_call (v1, le_field bs i 8). { apply le_field_range; auto; lia. }
      forward.
      forward_call (sh, p, bs, i + 8, 8).
      forward_call (v2, le_field bs (i + 8) 8). { apply le_field_range; auto; lia. }
      forward.
      forward_call (sh, p, bs, i + 16, 8).
      forward_call (v3, le_field bs (i + 16) 8). { apply le_field_range; auto; lia. }
      forward.
      forward_call (sh, p, bs, i + 24, 8).
      forward_call (v4, le_field bs (i + 24) 8). { apply le_field_range; auto; lia. }
      forward.
      forward. forward.
      Exists (i + 32) (xxh_round v1 (le_field bs i 8)) (xxh_round v2 (le_field bs (i + 8) 8))
        (xxh_round v3 (le_field bs (i + 16) 8)) (xxh_round v4 (le_field bs (i + 24) 8)) n.
      entailer!.
      refine (conj (xxh_round_range _ _) (conj (xxh_round_range _ _) (conj (xxh_round_range _ _)
        (conj (xxh_round_range _ _) _)))).
      split.
      { rewrite H9, xxh_stripes_step by (rewrite length_skipn_Z by lia; lia).
        rewrite !le_field_skipn by lia. rewrite Z.add_0_r.
        rewrite <- (skipn_skipn_Z bs i 32) by lia. reflexivity. }
      f_equal. f_equal. lia.
    + Intros i v1 v2 v3 v4.
      forward_call (v1, 1). forward_call (v2, 7). forward_call (v3, 12). forward_call (v4, 18).
      forward.
      rewrite !add64_repr, <- (repr64_m64 (rotl64 v1 1 + _ + _ + _)).
      forward_call (m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18), v1). { rng. }
      forward_call (xxh_merge (m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18)) v1, v2).
      { rng. }
      forward_call (xxh_merge (xxh_merge (m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18))
        v1) v2, v3). { rng. }
      forward_call (xxh_merge (xxh_merge (xxh_merge
        (m64 (rotl64 v1 1 + rotl64 v2 7 + rotl64 v3 12 + rotl64 v4 18)) v1) v2) v3, v4). { rng. }
      forward.
      Exists i (xxh_mergeall v1 v2 v3 v4). entailer!.
      split. { unfold xxh_mergeall. apply xxh_merge_range. }
      apply xxh64_long_seed; [lia | lia | assumption].
  - rewrite !Int64.unsigned_repr in H2 by rep_lia.
    forward. Exists 0 (m64 (seed + XXH_P5)). entailer!.
    split; [rng|]. split.
    + rewrite xxh64_short_seed by (pose proof (Zlength_nonneg bs); lia). reflexivity.
    + rewrite repr64_m64. reflexivity.
  - Intros i h.
    forward.
    rewrite add64_repr, <- (repr64_m64 (h + Zlength bs)).
    forward_loop (EX i: Z, EX h: Z, EX n: nat,
      PROP (0 <= i <= Zlength bs; 8 * Z.of_nat n >= Zlength bs - i; 0 <= h <= Int64.max_unsigned;
            xxh64 bs seed = xxh_fin8 n h (skipn (Z.to_nat i) bs))
      LOCAL (temp _acc (Vlong (Int64.repr h)); temp _left (Vlong (Int64.repr (Zlength bs - i)));
             temp _p (offset_val i p); temp _len (Vlong (Int64.repr (Zlength bs))))
      SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p))
    break: (EX i: Z, EX h: Z,
      PROP (0 <= i <= Zlength bs; Zlength bs - i < 8; 0 <= h <= Int64.max_unsigned;
            xxh64 bs seed = xxh_fin4 h (skipn (Z.to_nat i) bs))
      LOCAL (temp _acc (Vlong (Int64.repr h)); temp _left (Vlong (Int64.repr (Zlength bs - i)));
             temp _p (offset_val i p); temp _len (Vlong (Int64.repr (Zlength bs))))
      SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)).
    + Exists i (m64 (h + Zlength bs)) 4%nat. entailer!. apply m64_range.
    + Intros i0 h0 n. forward_if.
      2: { rewrite !Int64.unsigned_repr in H10 by rep_lia. forward. Exists i0 h0. entailer!.
           rewrite H9, xxh_fin8_done by (rewrite length_skipn_Z by lia; lia). reflexivity. }
      rewrite !Int64.unsigned_repr in H10 by rep_lia.
      destruct n as [|n]; [simpl in H7; lia|].
      forward_call (sh, p, bs, i0, 8).
      forward_call (0, le_field bs i0 8). { rng. }
      forward_call (Z.lxor h0 (xxh_round 0 (le_field bs i0 8)), 27).
      { entailer!. rewrite repr64_lxor. reflexivity. }
      { rng. }
      forward.
      rewrite XP1_c, XP4_c, mul64_repr, add64_repr, <- (repr64_m64 (_ * XXH_P1 + XXH_P4)).
      forward. forward.
      Exists (i0 + 8) (m64 (rotl64 (Z.lxor h0 (xxh_round 0 (le_field bs i0 8))) 27 * XXH_P1 + XXH_P4)) n.
      entailer!.
      split. { rng. }
      split.
      { rewrite H9, xxh_fin8_step by (rewrite length_skipn_Z by lia; lia).
        rewrite le_field_skipn, Z.add_0_r by lia. rewrite <- (skipn_skipn_Z bs i0 8) by lia. reflexivity. }
      f_equal. f_equal. lia.
    + clear i h H2 H3 H4 H5. Intros i h.
      forward_if (EX i: Z, EX h: Z,
        PROP (0 <= i <= Zlength bs; 0 <= h <= Int64.max_unsigned;
              xxh64 bs seed = xxh_avalanche (xxh_tail1 h (skipn (Z.to_nat i) bs)))
        LOCAL (temp _acc (Vlong (Int64.repr h)); temp _left (Vlong (Int64.repr (Zlength bs - i)));
               temp _p (offset_val i p); temp _len (Vlong (Int64.repr (Zlength bs))))
        SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)).
      * rewrite !Int64.unsigned_repr in H6 by rep_lia.
        forward_call (sh, p, bs, i, 4).
        forward_call (Z.lxor h (m64 (le_field bs i 4 * XXH_P1)), 23).
        { entailer!. rewrite repr64_lxor, repr64_m64.
          replace (Int64.repr (le_field bs i 4 * XXH_P1)) with (Int64.repr (le_field bs i 4 * -7046029288634856825));
            [reflexivity|].
          apply repr64_eq_mod. symmetry. apply mod64_shift with (- le_field bs i 4). unfold XXH_P1. lia. }
        { rng. }
        forward. forward. forward.
        Exists (i + 4) (m64 (rotl64 (Z.lxor h (m64 (le_field bs i 4 * XXH_P1))) 23 * XXH_P2 + XXH_P3)).
        entailer!.
        split. { rng. }
        split.
        { rewrite H5, xxh_fin4_yes by (rewrite length_skipn_Z by lia; lia).
          rewrite le_field_skipn, Z.add_0_r by lia. rewrite <- (skipn_skipn_Z bs i 4) by lia. reflexivity. }
        split.
        { rewrite repr64_m64. f_equal.
          apply repr64_eq_mod, mod64_shift with (- rotl64 (Z.lxor h (m64 (le_field bs i 4 * XXH_P1))) 23).
          unfold XXH_P2, XXH_P3. lia. }
        f_equal. f_equal. lia.
      * rewrite !Int64.unsigned_repr in H6 by rep_lia.
        forward. Exists i h. entailer!.
        rewrite H5, xxh_fin4_no by (rewrite length_skipn_Z by lia; lia). reflexivity.
      * clear i h H2 H3 H4 H5. Intros i h.
        forward_loop (EX i: Z, EX h: Z,
          PROP (0 <= i <= Zlength bs; 0 <= h <= Int64.max_unsigned;
                xxh64 bs seed = xxh_avalanche (xxh_tail1 h (skipn (Z.to_nat i) bs)))
          LOCAL (temp _acc (Vlong (Int64.repr h)); temp _left (Vlong (Int64.repr (Zlength bs - i)));
                 temp _p (offset_val i p); temp _len (Vlong (Int64.repr (Zlength bs))))
          SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p))
        break: (EX h: Z,
          PROP (0 <= h <= Int64.max_unsigned; xxh64 bs seed = xxh_avalanche h)
          LOCAL (temp _acc (Vlong (Int64.repr h)))
          SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)).
        -- Exists i h. entailer!.
        -- clear i h H2 H3 H4. Intros j g. forward_if.
           2: { rewrite !Int64.unsigned_repr in H5 by rep_lia. forward. Exists g. entailer!.
                rewrite H4. replace j with (Zlength bs) by lia. rewrite skipn_all_Z. reflexivity. }
           rewrite !Int64.unsigned_repr in H5 by rep_lia.
           pose proof (byte_Znth bs j H ltac:(lia)) as HB.
           (* the byte *p is the element j of the array *)
           assert_PROP (offset_val j p = field_address (tarray tuchar (Zlength bs)) [ArraySubsc j] p) as FA.
           { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia. }
           forward.
           { entailer!. simpl. rep_lia. }
           forward_call (Z.lxor g (m64 (Znth j bs * XXH_P5)), 11).
           { entailer!. rewrite repr64_lxor, repr64_m64. reflexivity. }
           { rng. }
           forward. forward. forward.
           Exists (j + 1) (m64 (rotl64 (Z.lxor g (m64 (Znth j bs * XXH_P5))) 11 * XXH_P1)).
           entailer!.
           split. { rng. }
           split.
           { rewrite H4, (skipn_Znth_cons bs j) by lia. rewrite xxh_tail1_cons. reflexivity. }
           split; [|f_equal; f_equal; lia].
           rewrite repr64_m64. f_equal.
           apply repr64_eq_mod, mod64_shift with (- rotl64 (Z.lxor g (m64 (Znth j bs * XXH_P5))) 11).
           unfold XXH_P1. lia.
        -- Intros g.
           forward.
           rewrite Int.unsigned_repr, shru_repr, <- repr64_lxor by rep_lia.
           forward.
           rewrite XP2_mul.
           rewrite Int.unsigned_repr, shru_repr, <- repr64_lxor by (try rng; rep_lia).
           rewrite mul64_repr, <- repr64_m64. replace 1609587929392839161 with XXH_P3 by reflexivity.
           forward.
           rewrite shru_repr, <- repr64_lxor by (try rng; rep_lia).
           entailer!. rewrite H6. unfold xxh_avalanche. reflexivity.
Qed.
