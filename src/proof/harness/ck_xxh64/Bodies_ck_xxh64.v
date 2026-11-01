(* The bodies of the small functions of harness/ck_xxh64.c: the helpers upto and any_bytes of
   harness/laws_common.h, and the pieces rotl, le, round64, merge of the harness's own XXH64 (their 64-bit
   arithmetic against the model, with the writer's lemmas of src/proof/harness/writer/XxhLemmas.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.ck_xxh64.Specs_ck_xxh64.
Require Import Zstd.proof.harness.writer.XxhLemmas.
Local Open Scope logic.

Lemma body_rotl : semax_body Vprog G f_rotl rotl_spec.
Proof.
  start_function.
  forward.
  - entailer!. unfold Int64.iwordsize'. rewrite !Int.unsigned_repr by rep_lia.
    unfold Int64.zwordsize; simpl. split; lia.
  - entailer!. f_equal. apply rotl64_ok; auto.
Qed.

Lemma body_round64 : semax_body Vprog G f_round64 round64_spec.
Proof.
  start_function.
  forward_call (m64 (acc + m64 (lane * XXH_P2)), 31).
  { entailer!.
    replace (Int64.repr (acc + lane * -4417276706812531889)) with (Int64.repr (m64 (acc + m64 (lane * XXH_P2))));
      [reflexivity|].
    apply repr64_eq_mod; unfold m64; rewrite Z.mod_mod, Z.add_mod_idemp_r by lia.
    symmetry; apply mod64_shift with lane; unfold XXH_P2; ring. }
  { apply m64_range. }
  forward.
  entailer!. unfold xxh_round. rewrite repr64_m64, <- (mul64_repr _ (-7046029288634856825)), XP1_c, mul64_repr. reflexivity.
Qed.

Lemma body_merge : semax_body Vprog G f_merge merge_spec.
Proof.
  start_function.
  forward_call (0, accn).
  forward.
  entailer!. f_equal. unfold xxh_merge.
  rewrite repr64_m64, XP1_c, XP4_c, <- repr64_lxor, mul64_repr, add64_repr. reflexivity.
Qed.

Lemma body_upto : semax_body Vprog G f_upto upto_spec.
Proof.
  start_function.
  forward_call tt.
  Intros v.
  forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr (Z.min v max)))) SEP ()).
  - forward. entailer!. rewrite Z.min_l by lia. reflexivity.
  - forward. entailer!. rewrite Z.min_r by lia. reflexivity.
  - forward. Exists (Z.min v max). entailer!.
Qed.

Lemma body_any_bytes : semax_body Vprog G f_any_bytes any_bytes_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rep_lia. }
  Intros p.
  destruct (eq_dec p nullval) as [Hp|Hp].
  - subst p. forward_if (PROP () LOCAL (temp _t'2 (Vint Int.zero); temp _bytes nullval) SEP (mem_mgr gv)).
    + discriminate.
    + forward. entailer!.
    + forward_if (PROP () LOCAL (temp _bytes nullval) SEP (mem_mgr gv)).
      { contradiction. }
      { forward. entailer!. }
      forward. Exists nullval (Zrepeat 0 n). entailer!. split; [apply Zlength_Zrepeat; lia |].
      unfold Zrepeat. apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst; unfold is_byte; lia.
  - Intros.
    forward_if (PROP () LOCAL (temp _t'2 (Vint (if Z.eq_dec n 0 then Int.zero else Int.one)); temp _bytes p;
                               temp _n (Vlong (Int64.repr n)))
                SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p; data_at_ Ews (tarray tuchar n) p)).
    + forward. entailer!. unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (Z.eq_dec n 0), (zeq n 0); try lia; reflexivity.
    + contradiction.
    + forward_if (EX bs: list Z, PROP (Zlength bs = n; bytes_ok bs) LOCAL (temp _bytes p)
                   SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p; data_at Ews (tarray tuchar n) (zbytes bs) p)).
      * forward_call (p, n, Ews). Intros bs. Exists bs. entailer!.
        eapply Forall_impl; [|eassumption]. intros a Ha. unfold is_byte. rep_lia.
      * forward. Exists (@nil Z). destruct (Z.eq_dec n 0); [|discriminate]. subst n. entailer!. constructor.
      * Intros bs. forward. Exists p bs. rewrite if_false by auto. entailer!.
Qed.

(* one more byte of le, read from the top: value << 8 | p[j] *)
Lemma le_value_cons_top (all: list Z) (i j k: Z) :
  bytes_ok all -> 0 <= i -> 0 <= j < k -> k <= 8 -> i + k <= Zlength all ->
  Z.lor (Z.shiftl (le_value (sublist (i + j + 1) (i + k) all)) 8) (Znth (i + j) all) =
  le_value (sublist (i + j) (i + k) all).
Proof.
  intros Hb Hi Hj Hk Hl.
  rewrite (sublist_next (i + j) (i + k) all) by lia. cbn [le_value].
  replace (i + j + 1) with (i + j + 1) by lia.
  pose proof (byte_Znth all (i + j) Hb ltac:(lia)) as Hy.
  rewrite Z.lor_comm, lor_shiftl_disjoint by (try lia; pose proof (le_value_sublist_range all (i + j + 1) (k - j - 1) Hb);
    replace (i + j + 1 + (k - j - 1)) with (i + k) in * by lia; lia).
  change (2 ^ 8) with 256. lia.
Qed.

Lemma body_le : semax_body Vprog G f_le le_spec.
Proof.
  start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength all)) [] base) as FC by entailer!.
  assert (SPLIT: data_at sh (tarray tuchar (Zlength all)) (zbytes all) base =
    data_at sh (tarray tuchar i) (zbytes (sublist 0 i all)) base *
    data_at sh (tarray tuchar (Zlength all - i)) (zbytes (sublist i (Zlength all) all)) (offset_val i base)).
  { rewrite (split2_data_at_Tarray_tuchar sh (Zlength all) i) by (rewrite ?Zlength_map; lia).
    change (Tarray tuchar (Zlength all) noattr) with (tarray tuchar (Zlength all)).
    rewrite arr_field_address0 by (auto; lia). rewrite !sublist_map. simpl sizeof. rewrite Z.mul_1_l. reflexivity. }
  rewrite SPLIT. Intros.
  forward.
  forward_loop (EX j: Z,
    PROP (-1 <= j < k)
    LOCAL (temp _value (Vlong (Int64.repr (le_value (sublist (i + j + 1) (i + k) all)))); temp _i (Vint (Int.repr j));
           temp _p (offset_val i base); temp _size (Vint (Int.repr k)))
    SEP (data_at sh (tarray tuchar i) (zbytes (sublist 0 i all)) base;
         data_at sh (tarray tuchar (Zlength all - i)) (zbytes (sublist i (Zlength all) all)) (offset_val i base)))
  continue: (EX j: Z,
    PROP (0 <= j < k)
    LOCAL (temp _value (Vlong (Int64.repr (le_value (sublist (i + j) (i + k) all)))); temp _i (Vint (Int.repr j));
           temp _p (offset_val i base); temp _size (Vint (Int.repr k)))
    SEP (data_at sh (tarray tuchar i) (zbytes (sublist 0 i all)) base;
         data_at sh (tarray tuchar (Zlength all - i)) (zbytes (sublist i (Zlength all) all)) (offset_val i base)))
  break: (
    PROP ()
    LOCAL (temp _value (Vlong (Int64.repr (le_value (sublist i (i + k) all)))))
    SEP (data_at sh (tarray tuchar i) (zbytes (sublist 0 i all)) base;
         data_at sh (tarray tuchar (Zlength all - i)) (zbytes (sublist i (Zlength all) all)) (offset_val i base))).
  - forward. Exists (k - 1). entailer!. replace (i + (k - 1) + 1) with (i + k) by lia. rewrite sublist_nil. reflexivity.
  - Intros j. forward_if.
    2: { forward. entailer!. assert (j = -1) by lia. subst j. replace (i + -1 + 1) with i by lia. reflexivity. }
    forward.
    { entailer!. rewrite Znth_sublist by lia. pose proof (byte_Znth all (j + i) H ltac:(lia)).
      simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    Exists j. entailer!.
    rewrite Znth_sublist by lia. replace (j + i) with (i + j) by lia.
    pose proof (byte_Znth all (i + j) H ltac:(lia)).
    pose proof (le_value_sublist_range all (i + j + 1) (k - j - 1) H ltac:(lia) ltac:(lia) ltac:(lia)) as Hv.
    replace (i + j + 1 + (k - j - 1)) with (i + k) in Hv by lia.
    rewrite Int.unsigned_repr by rep_lia. unfold Int64.shl.
    rewrite (Int64.unsigned_repr (le_value _)) by lia. rewrite (Int64.unsigned_repr 8) by rep_lia.
    rewrite <- repr64_lor, le_value_cons_top by first [exact H | lia]. reflexivity.
  - Intros j. forward. Exists (j - 1). entailer!. replace (i + (j - 1) + 1) with (i + j) by lia. reflexivity.
  - forward. rewrite SPLIT. entailer!. rewrite le_field_sublist by lia. reflexivity.
Qed.
