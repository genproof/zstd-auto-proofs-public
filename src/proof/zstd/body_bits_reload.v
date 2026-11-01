(* Bodies of BIT_reloadDStream_internal, BIT_reloadDStreamFast, BIT_reloadDStream, BIT_endOfDStream.
   Removed: the unproved body_BIT_reloadDStreamFast and bodies_bits_reload (proof: AllBodies_util_bits.v). *)
Require Import Zstd.proof.zstd.Gprog.

(* ---------- model: the container after a reload is the 8-byte field at the window base ---------- *)

Lemma br_le_value_split: forall j (l: list Z),
  le_value l = le_value (firstn j l) + 256 ^ Z.of_nat j * le_value (skipn j l).
Proof.
  induction j; intros l.
  - simpl. lia.
  - destruct l as [|b l']; cbn [le_value firstn skipn].
    + rewrite Z.mul_0_r. lia.
    + rewrite (IHj l'). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Lemma br_le_value_bound: forall l,
  bytes_ok l -> 0 <= le_value l < 256 ^ Z.of_nat (length l).
Proof.
  intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value length].
  - simpl. lia.
  - unfold is_byte in Hb. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma br_bit_C_field: forall s lo,
  bytes_ok s -> 0 <= lo -> lo mod 8 = 0 ->
  bit_C s lo = le_field s (lo / 8) 8.
Proof.
  intros s lo Hs Hlo Hm. unfold bit_C, bs_value, le_field, slice.
  set (k := Z.to_nat (lo / 8)).
  assert (E: 2 ^ lo = 256 ^ Z.of_nat k).
  { unfold k. rewrite Z2Nat.id by (apply Z.div_pos; lia). change 256 with (2 ^ 8).
    rewrite <- Z.pow_mul_r by (try apply Z.div_pos; lia). f_equal.
    pose proof (Z.div_mod lo 8 ltac:(lia)). lia. }
  rewrite E. rewrite (br_le_value_split k s).
  assert (Hf: 0 <= le_value (firstn k s) < 256 ^ Z.of_nat k).
  { pose proof (br_le_value_bound (firstn k s)) as B.
    assert (bytes_ok (firstn k s)) as Hok.
    { unfold bytes_ok in *. rewrite <- (firstn_skipn k s) in Hs. apply Forall_app in Hs. tauto. }
    specialize (B Hok). split; [lia|].
    eapply Z.lt_le_trans; [apply B|]. apply Z.pow_le_mono_r; [lia|].
    rewrite firstn_length. lia. }
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
  rewrite (br_le_value_split 8 (skipn k s)). change (Z.of_nat 8) with 8.
  change (256 ^ 8) with (2 ^ 64).
  assert (bytes_ok (firstn 8 (skipn k s))) as Hok.
  { unfold bytes_ok in *. rewrite <- (firstn_skipn k s) in Hs. apply Forall_app in Hs.
    destruct Hs as [_ Hs]. rewrite <- (firstn_skipn 8 (skipn k s)) in Hs.
    apply Forall_app in Hs. tauto. }
  pose proof (br_le_value_bound _ Hok) as B.
  assert (256 ^ Z.of_nat (length (firstn 8 (skipn k s))) <= 2 ^ 64).
  { change (2 ^ 64) with (256 ^ Z.of_nat 8). apply Z.pow_le_mono_r; [lia|].
    rewrite firstn_length. lia. }
  rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma br_field_sub: forall (buf: list Z) off n j,
  0 <= off -> 0 <= j -> j + 8 <= n -> off + n <= Zlength buf ->
  le_field buf (off + j) 8 = le_field (sublist off (off + n) buf) j 8.
Proof.
  intros. unfold le_field, slice.
  assert (Hs: forall (l: list Z) i, 0 <= i ->
            firstn (Z.to_nat 8) (skipn (Z.to_nat i) l) = sublist i (i + 8) l).
  { intros. unfold sublist. rewrite skipn_firstn_comm. f_equal. lia. }
  rewrite !Hs by lia. rewrite sublist_sublist by lia. f_equal. f_equal; lia.
Qed.

(* ---------- C arithmetic ---------- *)

Lemma br_tuchar_valid_ptr: forall sh N c p k, sepalg.nonidentity sh -> 0 <= k < N ->
  data_at sh (tarray tuchar N) c p |-- valid_pointer (offset_val k p).
Proof.
  intros. sep_apply data_at_memory_block. apply memory_block_valid_pointer; auto.
  rewrite sizeof_tarray_tuchar by lia. lia.
Qed.

Lemma br_sub_pi: forall v n,
  isptr v -> 0 <= n <= Int.max_unsigned ->
  force_val (sem_sub_pi tschar Unsigned v (Vint (Int.repr n))) = offset_val (- n) v.
Proof.
  intros v n Hv Hn. destruct v; try contradiction. simpl. f_equal.
  unfold ptrofs_of_int, Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp, Ptrofs.neg_repr. reflexivity.
Qed.

Lemma br_shru3: forall x,
  0 <= x <= Int.max_unsigned -> Int.shru (Int.repr x) (Int.repr 3) = Int.repr (x / 8).
Proof.
  intros. rewrite Int.shru_div_two_p, !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma br_offset_inj: forall b ofs x y,
  0 <= x -> 0 <= y -> Ptrofs.unsigned ofs + x < Ptrofs.modulus -> Ptrofs.unsigned ofs + y < Ptrofs.modulus ->
  offset_val x (Vptr b ofs) = offset_val y (Vptr b ofs) -> x = y.
Proof.
  intros. unfold offset_val in H3. injection H3 as H5.
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite !Ptrofs.Z_mod_modulus_eq, !Ptrofs.unsigned_repr in H5 by rep_lia.
  rewrite !Z.mod_small in H5 by lia. lia.
Qed.

Lemma br_ptr_sub: forall b o i m,
  0 <= m <= Int.max_unsigned ->
  Vptr b (Ptrofs.sub (Ptrofs.add o (Ptrofs.repr i)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_intu (Int.repr m)))) =
  offset_val (i - m) (Vptr b o).
Proof.
  intros b o i m Hm. simpl. f_equal.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by lia.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp, Ptrofs.neg_repr, Ptrofs.add_assoc.
  f_equal. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  replace (i - m) with (i + - m) by lia.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

(* ptr - start, both inside one object (no wrap-around) *)
Lemma br_sub_pp: forall b o i j,
  0 <= j <= i -> Ptrofs.unsigned o + i <= Ptrofs.max_unsigned ->
  force_val (sem_sub_pp tschar (offset_val i (Vptr b o)) (offset_val j (Vptr b o))) =
  Vlong (Int64.repr (i - j)).
Proof.
  intros b o i j Hij Ho. pose proof (Ptrofs.unsigned_range o).
  unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  unfold Vptrofs. simpl. f_equal.
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one.
  unfold Ptrofs.sub, Ptrofs.add. rewrite !(Ptrofs.unsigned_repr (i)) by rep_lia.
  rewrite !(Ptrofs.unsigned_repr (j)) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. f_equal. lia.
  reflexivity.
Qed.

Lemma body_BIT_reloadDStream_internal :
  semax_body Vprog Gprog f_BIT_reloadDStream_internal BIT_reloadDStream_internal_spec.
Proof.
  start_function.
  unfold BIT_DStream_rep. Intros ptr lim.
  destruct H2 as (Hok & Hn & Hlo0 & Hlom & Hlok & Hpos & Hbc).
  destruct H3 as [Hptr | [Hlt _]]; [| lia].
  destruct H as (Hst & Hoff & Hlen & Hsub). subst ptr start.
  unfold bit_src. assert_PROP (isptr bp) as Hbp by entailer!.
  rewrite offset_offset_val.
  remember (lo / 8) as k eqn:Hk.
  assert (Hlo: lo = 8 * k) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  set (nb := (lo + 64 - pos) / 8).
  assert (Hnb: 0 <= nb <= 8) by (unfold nb; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (Hnb2: 8 * nb <= lo + 64 - pos < 8 * nb + 8)
    by (unfold nb; pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia));
        pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)); lia).
  forward. forward. forward.
  rewrite br_shru3 by lia. fold nb. rewrite br_sub_pi by (first [rep_lia | destruct bp; try contradiction; exact I]).
  rewrite offset_offset_val.
  assert (Hk8: 8 <= k) by lia.
  assert (Hks: k + 8 <= Zlength s) by lia.
  forward. forward.
  assert (Hand: Int.and (Int.repr (lo + 64 - pos)) (Int.repr 7) = Int.repr (lo - 8 * nb + 64 - pos)).
  { unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. change 7 with (Z.ones 3).
    rewrite Z.land_ones by lia. f_equal. rewrite Zmod_eq_full by lia. unfold nb. change (2^3) with 8. lia. }
  rewrite Hand.
  forward.
  replace (off + k + - nb) with (off + (k - nb)) by lia.
  forward_call (shs, bp, buf, off + (k - nb)).
  { unfold mem_read_pre. split3; [auto | lia | split; [lia |]].
    replace (sublist (off + (k - nb)) (off + (k - nb) + 8) buf) with (sublist (k - nb) (k - nb + 8) s).
    - apply Forall_sublist. exact Hok.
    - rewrite <- Hsub. rewrite sublist_sublist by lia. f_equal; lia. }
  forward. forward.
  unfold BIT_DStream_rep. Exists (offset_val (off + (k - nb)) bp) lim.
  entailer!; fold nb; clearbody nb;
    assert (Hdiv: (8 * k - 8 * nb) / 8 = k - nb)
      by (rewrite <- Z.mul_sub_distr_l, Z.mul_comm, Z.div_mul; lia);
    assert (Hmod: (8 * k - 8 * nb) mod 8 = 0)
      by (rewrite <- Z.mul_sub_distr_l, Z.mul_comm, Z.mod_mul; lia).
  - rewrite Hdiv. split; [| left; reflexivity].
    unfold bit_inv. repeat split; auto; lia.
  - rewrite br_bit_C_field; [| exact Hok | lia | exact Hmod]. rewrite Hdiv.
    rewrite <- Hsub at 1. rewrite <- br_field_sub by lia. apply derives_refl.
Qed.

Lemma body_BIT_endOfDStream :
  semax_body Vprog Gprog f_BIT_endOfDStream BIT_endOfDStream_spec.
Proof.
  start_function.
  unfold BIT_DStream_rep. Intros ptr lim.
  rename H0 into Hinv, H1 into Hptr.
  pose proof Hinv as (Hok & Hn & Hlo0 & Hlom & Hlok & Hpos & Hbc).
  destruct H as (Hst & Hoff & Hlen & Hsub). subst start.
  unfold bit_src. assert_PROP (isptr bp) as Hbp by entailer!.
  destruct bp as [| | | | | b o]; try contradiction.
  assert_PROP (Ptrofs.unsigned o + Zlength buf < Ptrofs.modulus) as Hbo.
  { entailer!. match goal with H: field_compatible (Tarray _ _ _) _ _ |- _ => destruct H as (_ & _ & Hsz & _) end.
    simpl in Hsz. rewrite Z.max_r in Hsz by rep_lia. lia. }
  destruct Hptr as [Hptr | [Hlt Hptr]]; subst ptr.
  - rewrite offset_offset_val.
    remember (lo / 8) as k eqn:Hk.
    assert (Hlo: lo = 8 * k) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
    assert (Hkn: k < Zlength s) by lia.
    forward. forward.
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if ((lo =? 0) && (pos =? 0))%bool then 1 else 0))))
      SEP (data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
             (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)),
              (offset_val (off + k) (Vptr b o), (offset_val off (Vptr b o), lim)))) p;
           data_at shs (tarray tuchar (Zlength buf)) (zbytes buf) (Vptr b o); zstd_globals gv)).
    { apply denote_tc_test_eq_split; apply sepcon_valid_pointer1, sepcon_valid_pointer2.
      - change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)).
        apply br_tuchar_valid_ptr; [apply readable_nonidentity; auto | lia].
      - change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)).
        apply br_tuchar_valid_ptr; [apply readable_nonidentity; auto | lia]. }
    { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H.
      change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H.
      apply br_offset_inj in H; [| lia | lia | lia | lia].
      assert (Hl0: lo = 0) by lia. rewrite Hl0 in *.
      forward. forward. entailer!. simpl sizeof. unfold Int64.cmpu, Int64.eq.
      rewrite !Int64.unsigned_repr by rep_lia.
      destruct (Z.eqb_spec pos 0); simpl.
      - subst. reflexivity.
      - rewrite zeq_false by lia. reflexivity. }
    { assert (k <> 0) by (intro; subst k; apply H; f_equal; f_equal; f_equal; lia).
      forward. entailer!. replace (8 * k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    forward.
    unfold BIT_DStream_rep, bit_src. Exists (offset_val (off + k) (Vptr b o)) lim. entailer!.
    left. rewrite <- Hk. reflexivity.
  - assert_PROP (isptr (gv _zeroFilled)) as Hz by (unfold zstd_globals; entailer!).
    forward. forward.
    forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr 0)))
      SEP (data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
             (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)),
              (gv _zeroFilled, (offset_val off (Vptr b o), lim)))) p;
           data_at shs (tarray tuchar (Zlength buf)) (zbytes buf) (Vptr b o); zstd_globals gv)).
    { apply denote_tc_test_eq_split.
      - unfold zstd_globals. entailer!.
      - apply sepcon_valid_pointer1, sepcon_valid_pointer2.
        change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)).
        apply br_tuchar_valid_ptr; [apply readable_nonidentity; auto | lia]. }
    { forward. forward. entailer!. simpl sizeof. unfold Int64.cmpu, Int64.eq.
      rewrite !Int64.unsigned_repr by rep_lia. rewrite zeq_false by lia. reflexivity. }
    { forward. entailer!. }
    forward.
    replace ((lo =? 0) && (pos =? 0))%bool with false
      by (destruct (Z.eqb_spec lo 0), (Z.eqb_spec pos 0); auto; lia).
    unfold BIT_DStream_rep, bit_src. Exists (gv _zeroFilled) lim. entailer!.
Qed.

Lemma body_BIT_reloadDStream :
  semax_body Vprog Gprog f_BIT_reloadDStream BIT_reloadDStream_spec.
Proof.
  start_function.
  unfold BIT_DStream_rep. Intros ptr lim.
  rename H0 into Hinv, H1 into Hptr.
  pose proof Hinv as (Hok & Hn & Hlo0 & Hlom & Hlok & Hpos & Hbc).
  pose proof H as Hsrc.
  destruct H as (Hst & Hoff & Hlen & Hsub). subst start.
  unfold bit_src. assert_PROP (isptr bp) as Hbp by entailer!.
  destruct bp as [| | | | | b o]; try contradiction.
  assert_PROP (Ptrofs.unsigned o + Zlength buf < Ptrofs.modulus) as Hbo.
  { entailer!. match goal with H: field_compatible (Tarray _ _ _) _ _ |- _ => destruct H as (_ & _ & Hsz & _) end.
    simpl in Hsz. rewrite Z.max_r in Hsz by rep_lia. lia. }
  forward.
  forward_if.
  { change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H.
    rewrite Int.unsigned_repr, Int64.unsigned_repr in H by rep_lia.
    forward. forward. unfold bs_reload. destruct (Z.ltb_spec pos lo); [| lia]. simpl fst; simpl snd.
    unfold BIT_DStream_rep, bit_src. Exists (gv _zeroFilled) lim. entailer!. }
  change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H.
  rewrite Int.unsigned_repr, Int64.unsigned_repr in H by rep_lia.
  destruct Hptr as [Hptr | [Hlt _]]; [| lia]. subst ptr.
  rewrite offset_offset_val.
  remember (lo / 8) as k eqn:Hk.
  assert (Hlo: lo = 8 * k) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  assert (Hkn: k < Zlength s) by lia.
  forward. forward.
  forward_if.
  { entailer!. unfold sameblock. destruct (peq b b); [exact I | congruence]. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H0.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H0.
    rewrite br_sub_pp in H0 by rep_lia. replace (off + k - off) with k in H0 by lia.
    simpl in H0. unfold Int64.ltu in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
    change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H0.
    destruct (zlt k 8); [unfold typed_true in H0; simpl in H0; discriminate |].
    forward_call (sh, p, gv, s, offset_val off (Vptr b o), pos, lo, shs, Vptr b o, buf, off).
    { unfold BIT_DStream_rep. Exists (offset_val (off + k) (Vptr b o)) lim. entailer!.
      left. rewrite <- Hk. reflexivity. }
    forward. unfold bs_reload. destruct (Z.ltb_spec pos (8 * k)); [lia |]. rewrite <- Hk.
    destruct (Z.leb_spec 8 k); [| lia].
    simpl fst; simpl snd. entailer!. apply derives_refl. }
  change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H0.
  change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H0.
  rewrite br_sub_pp in H0 by rep_lia. replace (off + k - off) with k in H0 by lia.
  simpl in H0. unfold Int64.ltu in H0. rewrite !Int64.unsigned_repr in H0 by rep_lia.
  change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H0.
  destruct (zlt k 8); [| unfold typed_false in H0; simpl in H0; discriminate].
  clear H0.
  forward. forward.
  forward_if.
  { apply denote_tc_test_eq_split; apply sepcon_valid_pointer2.
    - change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)).
      apply br_tuchar_valid_ptr; [apply readable_nonidentity; auto | lia].
    - change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)).
      apply br_tuchar_valid_ptr; [apply readable_nonidentity; auto | lia]. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H0.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H0.
    apply br_offset_inj in H0; [| lia | lia | lia | lia].
    assert (Hl0: lo = 0) by lia. assert (Hk0: k = 0) by lia. rewrite Hl0, Hk0 in *.
    forward.
    forward_if.
    - change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H1.
      rewrite Int.unsigned_repr, Int64.unsigned_repr in H1 by rep_lia.
      forward. unfold bs_reload. destruct (Z.ltb_spec pos 0); [lia |]. destruct (Z.ltb_spec 0 pos); [| lia].
      simpl fst; simpl snd. unfold BIT_DStream_rep, bit_src. Exists (offset_val off (Vptr b o)) lim. entailer!.
    - change (Int64.unsigned (Int64.mul (Int64.repr 8) (Int64.repr 8))) with 64 in H1.
      rewrite Int.unsigned_repr, Int64.unsigned_repr in H1 by rep_lia.
      forward. unfold bs_reload. destruct (Z.ltb_spec pos 0); [lia |]. destruct (Z.ltb_spec 0 pos); [lia |].
      simpl fst; simpl snd. unfold BIT_DStream_rep, bit_src. Exists (offset_val off (Vptr b o)) lim. entailer!. }
  assert (Hk0: k <> 0) by (intro; subst k; apply H0; f_equal; f_equal; f_equal; lia).
  clear H0.
  assert (Hn9: 9 <= Zlength s) by lia.
  set (nb := (lo + 64 - pos) / 8).
  assert (Hnb: 0 <= nb <= 8) by (unfold nb; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (Hnb2: 8 * nb <= lo + 64 - pos < 8 * nb + 8)
    by (unfold nb; pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia));
        pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)); lia).
  forward. forward.
  rewrite br_shru3 by lia. fold nb.
  forward.
  forward. forward.
  forward_if (PROP () LOCAL (temp _nbBytes (Vint (Int.repr (Z.min k nb)));
                             temp _result (Vint (Int.repr (if k <? nb then 1 else 0))); temp _bitD p; gvars gv)
    SEP (data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
           (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)),
            (offset_val (off + k) (Vptr b o), (offset_val off (Vptr b o), lim)))) p;
         data_at shs (tarray tuchar (Zlength buf)) (zbytes buf) (Vptr b o))).
  { entailer!. unfold sameblock. destruct (peq b b); [exact I | congruence]. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H0.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H0.
    rewrite br_sub_pp in H0 by rep_lia. replace (off + k - off) with k in H0 by lia.
    simpl in H0. unfold Int64.ltu in H0. rewrite Int.unsigned_repr in H0 by rep_lia.
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    destruct (zlt k nb); [| unfold typed_true in H0; simpl in H0; discriminate].
    forward. forward. forward.
    { entailer!. unfold sameblock. destruct (peq b b); [exact I | congruence]. }
    forward.
    entailer!. split.
    - change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)).
      change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)).
      rewrite br_sub_pp by rep_lia. replace (off + k - off) with k by lia.
      rewrite Z.min_l by lia. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity.
    - destruct (Z.ltb_spec k nb); [reflexivity | lia]. }
  { change (Vptr b (Ptrofs.add o (Ptrofs.repr (off + k)))) with (offset_val (off + k) (Vptr b o)) in H0.
    change (Vptr b (Ptrofs.add o (Ptrofs.repr off))) with (offset_val off (Vptr b o)) in H0.
    rewrite br_sub_pp in H0 by rep_lia. replace (off + k - off) with k in H0 by lia.
    simpl in H0. unfold Int64.ltu in H0. rewrite Int.unsigned_repr in H0 by rep_lia.
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    destruct (zlt k nb); [unfold typed_false in H0; simpl in H0; discriminate |].
    forward. entailer!.
    split; [rewrite Z.min_r by lia; reflexivity | destruct (Z.ltb_spec k nb); [lia | reflexivity]]. }
  set (m := Z.min k nb).
  assert (Hm: 0 <= m <= k /\ m <= nb) by (unfold m; lia).
  forward. forward.
  rewrite br_ptr_sub by rep_lia.
  replace (off + k - m) with (off + (k - m)) by lia.
  forward. forward. forward.
  forward_call (shs, Vptr b o, buf, off + (k - m)).
  { unfold mem_read_pre. split3; [auto | lia | split; [lia |]].
    replace (sublist (off + (k - m)) (off + (k - m) + 8) buf) with (sublist (k - m) (k - m + 8) s).
    - apply Forall_sublist. exact Hok.
    - rewrite <- Hsub. rewrite sublist_sublist by lia. f_equal; lia. }
  forward. forward.
  assert (Hrl: bs_reload pos (8 * k) = (if k <? nb then 1 else 0, 8 * (k - m))).
  { unfold bs_reload. rewrite <- Hk. fold nb.
    destruct (Z.ltb_spec pos (8 * k)); [lia |]. destruct (Z.leb_spec 8 k); [lia |].
    destruct (Z.eqb_spec k 0); [lia |]. unfold m.
    destruct (Z.ltb_spec k nb); f_equal; lia. }
  rewrite Hrl. simpl fst; simpl snd. clearbody m. clear Hrl.
  unfold BIT_DStream_rep, bit_src. Exists (offset_val (off + (k - m)) (Vptr b o)) lim.
  assert (Hdiv: 8 * (k - m) / 8 = k - m) by (rewrite Z.mul_comm, Z.div_mul; lia).
  assert (Hmod: (8 * (k - m)) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_mul; lia).
  entailer!.
  - rewrite Hdiv. split; [| left; reflexivity].
    unfold bit_inv. repeat split; auto; lia.
  - rewrite br_bit_C_field; [| exact Hok | lia | exact Hmod]. rewrite Hdiv.
    replace (8 * k + 64 - pos - m * 8) with (8 * (k - m) + 64 - pos) by lia.
    rewrite <- Hsub at 1. rewrite <- br_field_sub by lia. apply derives_refl.
Qed.
