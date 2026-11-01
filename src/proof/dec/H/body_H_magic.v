(* Subtree H: ZSTD_isFrame, ZSTD_isSkippableFrame, ZSTD_getDictID_fromDict.  Prove each body against H_G (HSpecs.v); helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

Lemma hm_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value length].
  - simpl. lia.
  - unfold is_byte in Hb. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
    change (2 ^ 8) with 256. nia.
Qed.

Lemma hm_le4: forall s i, bytes_ok s -> 0 <= le_field s i 4 <= Int.max_unsigned.
Proof.
  intros s i H. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. rewrite Forall_forall in *. intros x Hx.
    apply H. apply firstn_In in Hx. apply skipn_In in Hx. exact Hx. }
  pose proof (hm_le_value_range _ Hb).
  assert (length (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s)) <= 4)%nat by (rewrite firstn_length; lia).
  assert (2 ^ (8 * Z.of_nat (length (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s)))) <= 2 ^ 32)
    by (apply Z.pow_le_mono_r; lia).
  rep_lia.
Qed.

Lemma hm_skip_magic: forall m, 0 <= m <= Int.max_unsigned ->
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

Lemma hm_read_pre: forall sh p s i, readable_share sh -> bytes_ok s -> 0 <= i -> i + 4 <= Zlength s ->
  mem_read_pre sh p s i 4.
Proof.
  intros. unfold mem_read_pre. repeat split; auto; try lia.
  unfold bytes_ok in *. apply Forall_sublist; auto.
Qed.

Lemma hm_repr_eq: forall m k c, 0 <= m <= Int.max_unsigned -> 0 <= k <= Int.max_unsigned ->
  Int.repr c = Int.repr k -> (Int.repr m = Int.repr c <-> m = k).
Proof.
  intros m k c Hm Hk Hc. rewrite Hc. split; intro E.
  - apply repr_inj_unsigned in E; auto.
  - subst; auto.
Qed.

Lemma bodies_H_magic :
  semax_body Vprog H_G f_ZSTD_isFrame ZSTD_isFrame_spec /\
  semax_body Vprog H_G f_ZSTD_isSkippableFrame ZSTD_isSkippableFrame_spec /\
  semax_body Vprog H_G f_ZSTD_getDictID_fromDict ZSTD_getDictID_fromDict_spec.
Proof.
  split; [|split].
  - start_function. destruct H as [Hsh [Hlen Hb]].
    assert_PROP (isptr src) as Hp by entailer!.
    pose proof (Zlength_nonneg s).
    forward_if.
    { rewrite !Int64.unsigned_repr in H0 by rep_lia.
      assert (E: is_frame s = 0) by (unfold is_frame; rewrite (proj2 (Z.ltb_lt _ _)) by lia; auto).
      forward. }
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    forward_call (sh, src, s, 0).
    { apply hm_read_pre; auto; lia. }
    pose proof (hm_le4 s 0 Hb) as Hr.
    assert (Hlt: (Zlength s <? 4) = false) by (apply Z.ltb_ge; lia).
    forward_if.
    { rewrite (hm_repr_eq _ ZSTD_MAGICNUMBER) in H1;
      [| rep_lia | unfold ZSTD_MAGICNUMBER; rep_lia | apply Int.eqm_samerepr; exists (-1); reflexivity].
      assert (E: is_frame s = 1) by (unfold is_frame; rewrite Hlt, H1, Z.eqb_refl; auto).
      forward. }
    rewrite (hm_repr_eq _ ZSTD_MAGICNUMBER) in H1;
      [| rep_lia | unfold ZSTD_MAGICNUMBER; rep_lia | apply Int.eqm_samerepr; exists (-1); reflexivity].
    forward_if.
    { rewrite hm_skip_magic in H2 by auto.
      assert (E: is_frame s = 1) by (unfold is_frame; rewrite Hlt, H2, orb_true_r; auto).
      forward. }
    rewrite hm_skip_magic in H2 by auto.
    assert (E: is_frame s = 0).
    { unfold is_frame. rewrite Hlt. apply Z.eqb_neq in H1. rewrite H1.
      destruct (is_skippable_magic _); [contradiction H2|]; auto. }
    forward.
  - start_function. destruct H as [Hsh [Hlen Hb]].
    assert_PROP (isptr src) as Hp by entailer!.
    pose proof (Zlength_nonneg s).
    forward_if.
    { rewrite !Int64.unsigned_repr in H0 by rep_lia.
      assert (E: is_skippable_frame s = 0)
        by (unfold is_skippable_frame; rewrite (proj2 (Z.ltb_lt _ _)) by lia; auto).
      forward. }
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    forward_call (sh, src, s, 0).
    { apply hm_read_pre; auto; lia. }
    pose proof (hm_le4 s 0 Hb) as Hr.
    assert (Hlt: (Zlength s <? 4) = false) by (apply Z.ltb_ge; lia).
    forward_if.
    { rewrite hm_skip_magic in H1 by auto.
      assert (E: is_skippable_frame s = 1) by (unfold is_skippable_frame; rewrite Hlt, H1; auto).
      forward. }
    rewrite hm_skip_magic in H1 by auto.
    assert (E: is_skippable_frame s = 0).
    { unfold is_skippable_frame. rewrite Hlt. destruct (is_skippable_magic _); [contradiction H1|]; auto. }
    forward.
  - start_function. rename SH into Hsh, H into Hlen, H0 into Hb.
    assert_PROP (isptr p) as Hp by entailer!.
    pose proof (Zlength_nonneg b).
    forward_if.
    { rewrite !Int64.unsigned_repr in H0 by rep_lia.
      assert (E: dict_id_of b = 0) by (unfold dict_id_of; rewrite (proj2 (Z.ltb_lt _ _)) by lia; auto).
      forward. }
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    assert (Hlt: (Zlength b <? 8) = false) by (apply Z.ltb_ge; lia).
    forward_call (sh, p, b, 0).
    { apply hm_read_pre; auto; lia. }
    pose proof (hm_le4 b 0 Hb) as Hr.
    forward_if.
    { assert (E: dict_id_of b = 0).
      { unfold dict_id_of. rewrite Hlt.
        destruct (Z.eqb_spec (le_field b 0 4) ZSTD_MAGIC_DICTIONARY) as [e|e]; auto.
        rewrite e in H1. contradiction H1. apply Int.eqm_samerepr; exists 1; reflexivity. }
      forward. }
    rewrite (hm_repr_eq _ ZSTD_MAGIC_DICTIONARY) in H1;
      [| rep_lia | unfold ZSTD_MAGIC_DICTIONARY; rep_lia | apply Int.eqm_samerepr; exists (-1); reflexivity].
    forward_call (sh, p, b, 4).
    { apply hm_read_pre; auto; lia. }
    assert (E: dict_id_of b = le_field b 4 4)
      by (unfold dict_id_of; rewrite Hlt, H1, Z.eqb_refl; auto).
    forward.
Qed.
