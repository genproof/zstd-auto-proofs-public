(* Subtree H: skippable frames.  Prove each body against H_G (HSpecs.v); helper lemmas go above. *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

Lemma skip_le_value_range: forall l, bytes_ok l ->
  0 <= le_value l < 256 ^ Z.of_nat (length l).
Proof.
  intros l H. induction H as [|b l Hb Hl IH]; cbn [le_value length].
  - simpl; lia.
  - unfold is_byte in Hb. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

Lemma skip_le_field4_range: forall s i, bytes_ok s -> 0 <= le_field s i 4 < 2 ^ 32.
Proof.
  intros s i H. unfold le_field, slice.
  assert (Hb: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn; auto. }
  pose proof (skip_le_value_range _ Hb) as [A B]. split; auto.
  assert (Hl: (length (firstn (Z.to_nat 4) (skipn (Z.to_nat i) s)) <= 4)%nat)
    by (rewrite firstn_length; lia).
  eapply Z.lt_le_trans; [exact B|]. change (2 ^ 32) with (256 ^ Z.of_nat 4).
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma skip_sfs: forall s, skippable_frame_size s =
  if Zlength s <? 8 then None else
  if le_field s 4 4 + 8 >? Zlength s then None else Some (le_field s 4 4 + 8).
Proof. reflexivity. Qed.

(* the model's skippable_frame_size is fix F5's single test (sizeU32 > srcSize - 8), on any input *)
Lemma skip_sfs5: forall s, skippable_frame_size s =
  if Zlength s <? 8 then None else
  if le_field s 4 4 + 8 >? Zlength s then None else Some (le_field s 4 4 + 8).
Proof. reflexivity. Qed.

Ltac u64 := repeat match goal with Hx: context [Int64.unsigned (Int64.repr ?a)] |- _ =>
  rewrite (Int64.unsigned_repr a) in Hx by rep_lia end.

(* `t = f(p, ...); x = t;` where the spec's pointer parameter is offset_val 0 p: forward_call's
   call-then-set path stalls; split the sequence so that it takes the plain call path, and prove
   the parameter equation with entailer! *)
Ltac call0 W := apply -> seq_assoc; forward_call W; [entailer! | .. ].

(* do { c } while (0), as Clight's Sloop c Sbreak: Q holds after it *)
Ltac reassoc := repeat match goal with
  |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.
Ltac once_loop Q := reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: Q; [apply andp_left2, derives_refl | | ] end.
Ltac once_body P :=
  first [ forward_if P;
          [ contradiction
          | forward; try (apply andp_left2, derives_refl)
          | forward; apply andp_left2, derives_refl ]
        | forward; apply andp_left2, derives_refl ].
Ltac once_skip := reassoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P; [apply andp_left2, derives_refl | once_body P | ] end.

Ltac once_loop_prop Pr := reassoc;
  match goal with |- semax _ (PROPx ?P ?LR) (Ssequence (Sloop _ Sbreak) _) _ =>
    once_loop (PROPx (Pr :: P) LR) end.

Ltac dec_err_c :=
  unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty;
  split; [reflexivity | split; let E := fresh "E" in intro E; compute in E; discriminate].

Lemma body_readSkippableFrameSize:
  semax_body Vprog H_G f_readSkippableFrameSize readSkippableFrameSize_spec.
Proof.
  start_function.
  pose proof H as Hw.
  destruct H as [Hsh [Hoff [HN [HN32 [Hc [_ [Hb Hsub]]]]]]].
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  forward.
  once_loop (PROP (Zlength s >= 8)
    LOCAL (temp _skippableHeaderSize (Vlong (Int64.repr 8)); temp _src (offset_val off base);
           temp _srcSize (Vlong (Int64.repr (Zlength s))))
    SEP (data_at sh (tarray tuchar N) c base)).
  { forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-72))). rewrite Int64.repr_unsigned. entailer!.
      unfold skippable_frame_size. rewrite !Int64.unsigned_repr in H by rep_lia.
      replace (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) with true by (symmetry; apply Z.ltb_lt; exact H).
      dec_err_c.
    - forward. entailer!. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
  Intros.
  assert_PROP (field_compatible (tarray tuchar N) [] base) as Hfc by entailer!.
  rewrite (win_split sh N c off s base Hw Hfc).
  Intros.
  forward_call (sh, offset_val off base, s, 4).
  { unfold mem_read_pre. repeat split; auto; try lia.
    unfold bytes_ok in *. apply Forall_sublist; auto. }
  pose proof (skip_le_field4_range s 4 Hb) as Hx. set (x := le_field s 4 4) in *.
  (* fix F5: one test, sizeU32 > srcSize - 8, in 64 bits (srcSize >= 8 here) *)
  once_loop (PROP (x + 8 <= Zlength s)
    LOCAL (temp _sizeU32 (Vint (Int.repr x)); temp _skippableHeaderSize (Vlong (Int64.repr 8));
           temp _src (offset_val off base); temp _srcSize (Vlong (Int64.repr (Zlength s))))
    SEP (data_at sh (tarray tuchar off) (sublist 0 off c) base;
         data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base);
         data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
           (offset_val (off + Zlength s) base))).
  { forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-72))). rewrite Int64.repr_unsigned.
      rewrite (win_split _ _ _ _ _ _ Hw Hfc). entailer!.
      rewrite skip_sfs5. fold x.
      match goal with Hc: Int64.unsigned _ < Int64.unsigned _ |- _ =>
        rewrite !Int64.unsigned_repr in Hc by rep_lia end.
      replace (Zlength s <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (x + 8 >? Zlength s) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
      dec_err_c.
    - forward. entailer!.
      match goal with Hc: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
        rewrite !Int64.unsigned_repr in Hc by rep_lia end. lia. }
  Intros.
  forward.
  Exists (8 + x).
  rewrite (win_split _ _ _ _ _ _ Hw Hfc). entailer!.
  rewrite skip_sfs5. fold x.
  replace (Zlength s <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (x + 8 >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  lia.
Qed.

Lemma skip_slice_sublist: forall (l: list Z) i k, 0 <= i -> 0 <= k ->
  slice l i k = sublist i (i + k) l.
Proof. intros. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia. Qed.

Lemma skip_rs: forall s cap, read_skippable s cap =
  if Zlength s <? 8 then None else
  if negb (is_skippable_magic (le_field s 0 4)) then None else
  match skippable_frame_size s with
  | None => None
  | Some k => if k - 8 >? cap then None else
      Some (slice s 8 (k - 8), le_field s 0 4 - ZSTD_MAGIC_SKIPPABLE_START)
  end.
Proof. reflexivity. Qed.

Lemma skip_sfs_range: forall s k, bytes_ok s ->
  skippable_frame_size s = Some k -> 8 <= k <= Zlength s.
Proof.
  intros s k Hb E. rewrite skip_sfs in E.
  pose proof (skip_le_field4_range s 4 Hb).
  destruct (Zlength s <? 8) eqn:E1; [discriminate|].
  destruct (le_field s 4 4 + 8 >? Zlength s) eqn:E3; [discriminate|].
  inversion E; subst. rewrite Z.gtb_ltb, Z.ltb_ge in E3. lia.
Qed.

(* the result of readSkippableFrameSize, within the input, is the frame's size *)
Lemma skip_sfs_r1: forall s r1, bytes_ok s -> Zlength s <= 2 ^ 63 - 1 ->
  match skippable_frame_size s with Some k => r1 = k | None => dec_err r1 end ->
  r1 <= Zlength s -> skippable_frame_size s = Some r1.
Proof.
  intros s r1 Hb Hs E Hr. destruct (skippable_frame_size s); [subst; auto|].
  destruct E as [E _]. unfold is_error_code in E. apply Z.ltb_lt in E. lia.
Qed.

Lemma skip_isf_range: forall s, 0 <= is_skippable_frame s <= 1.
Proof. intros. unfold is_skippable_frame. destruct (Zlength s <? 4), (is_skippable_magic (le_field s 0 4)); lia. Qed.

Lemma skip_rs_magic: forall s cap, Zlength s >= 8 -> is_skippable_frame s = 0 ->
  read_skippable s cap = None.
Proof.
  intros s cap Hs E. unfold is_skippable_frame in E. rewrite skip_rs.
  replace (Zlength s <? 4) with false in E by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (is_skippable_magic (le_field s 0 4)); [discriminate | reflexivity].
Qed.

Lemma skip_rs_size: forall s cap r1, bytes_ok s -> Zlength s <= 2 ^ 63 - 1 ->
  match skippable_frame_size s with Some k => r1 = k | None => dec_err r1 end ->
  r1 < 8 \/ r1 > Zlength s -> read_skippable s cap = None.
Proof.
  intros s cap r1 Hb Hs E Hr. rewrite skip_rs.
  destruct (Zlength s <? 8); [reflexivity|].
  destruct (negb _); [reflexivity|].
  destruct (skippable_frame_size s) eqn:E2; [|reflexivity].
  subst. apply skip_sfs_range in E2; auto. lia.
Qed.

Lemma skip_rs_cap: forall s cap r1, bytes_ok s -> Zlength s <= 2 ^ 63 - 1 ->
  match skippable_frame_size s with Some k => r1 = k | None => dec_err r1 end ->
  8 <= r1 <= Zlength s -> r1 - 8 > cap -> read_skippable s cap = None.
Proof.
  intros s cap r1 Hb Hs E Hr Hc. rewrite skip_rs.
  rewrite (skip_sfs_r1 s r1) by (auto; lia).
  destruct (Zlength s <? 8); [reflexivity|].
  destruct (negb _); [reflexivity|].
  replace (r1 - 8 >? cap) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma skip_rs_some: forall s cap r1, bytes_ok s -> Zlength s <= 2 ^ 63 - 1 -> Zlength s >= 8 ->
  is_skippable_frame s <> 0 ->
  match skippable_frame_size s with Some k => r1 = k | None => dec_err r1 end ->
  8 <= r1 <= Zlength s -> r1 - 8 <= cap ->
  read_skippable s cap = Some (sublist 8 r1 s, le_field s 0 4 - ZSTD_MAGIC_SKIPPABLE_START).
Proof.
  intros s cap r1 Hb Hs H8 Hm E Hr Hc. rewrite skip_rs.
  rewrite (skip_sfs_r1 s r1) by (auto; lia).
  unfold is_skippable_frame in Hm.
  replace (Zlength s <? 4) with false in Hm by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  destruct (is_skippable_magic (le_field s 0 4)); [|contradiction].
  replace (r1 - 8 >? cap) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  rewrite skip_slice_sublist by lia. simpl. do 3 f_equal. lia.
Qed.

Lemma body_ZSTD_readSkippableFrame:
  semax_body Vprog H_G f_ZSTD_readSkippableFrame ZSTD_readSkippableFrame_spec.
Proof.
  start_function.
  pose proof H0 as Hpre. destruct H0 as [Hsh [Hs30 Hb]].
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  once_loop (PROP (Zlength s >= 8)
    LOCAL (temp _dst dst; temp _dstCapacity (Vlong (Int64.repr cap)); temp _magicVariant pv;
           temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength s))))
    SEP (data_at_ shd (tarray tuchar cap) dst; data_at_ shv tuint pv;
         data_at sh (tarray tuchar (Zlength s)) (zbytes s) src)).
  { forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-72))) (Zrepeat Vundef cap) Vundef.
      rewrite Int64.repr_unsigned. entailer!.
      split; [list_solve |]. u64. rewrite skip_rs.
      replace (Zlength s <? 8) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    - forward. entailer!. u64. lia. }
  Intros.
  call0 (sh, src, s, 0).
  { unfold mem_read_pre. repeat split; auto; try lia.
    unfold bytes_ok in *. apply Forall_sublist; auto. }
  forward.
  call0 (sh, src, Zlength s, zbytes s, 0, s).
  { apply win_ok_full; auto. }
  Intros r1. forward.
  forward.
  once_loop_prop (is_skippable_frame s <> 0).
  { forward_call (sh, src, s).
    forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-14))) (Zrepeat Vundef cap) Vundef.
      rewrite Int64.repr_unsigned. entailer!.
      split; [list_solve |].
      match goal with Hx: Int.repr (is_skippable_frame s) = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx
          by (pose proof (skip_isf_range s); rep_lia) end.
      rewrite skip_rs_magic by auto. reflexivity.
    - forward. entailer!.
      match goal with Hx: Int.repr (is_skippable_frame s) <> Int.zero, Hy: is_skippable_frame s = 0 |- _ =>
        rewrite Hy in Hx; apply Hx; reflexivity end. }
  Intros.
  once_loop_prop (8 <= r1 <= Zlength s).
  { match goal with |- semax _ (PROPx ?P (LOCALx ?L ?R)) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'4 (Vint (if orb (r1 <? 8) (r1 >? Zlength s)
                                                     then Int.one else Int.zero)) :: L) R)) end.
    { forward. entailer!. u64. replace (r1 <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
    { forward. entailer!. u64.
      replace (r1 <? 8) with false by (symmetry; apply Z.ltb_ge; lia). simpl orb.
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.gtb_ltb.
      destruct (zlt (Zlength s) r1) as [Hl|Hl];
        [rewrite (proj2 (Z.ltb_lt _ _) Hl) | rewrite (proj2 (Z.ltb_ge (Zlength s) r1) ltac:(lia))]; reflexivity. }
    destruct (orb (r1 <? 8) (r1 >? Zlength s)) eqn:Eo; forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-72))) (Zrepeat Vundef cap) Vundef.
      rewrite Int64.repr_unsigned. entailer!.
      split; [list_solve |].
      rewrite (skip_rs_size s cap r1); auto.
      apply orb_true_iff in Eo. rewrite Z.ltb_lt, Z.gtb_ltb, Z.ltb_lt in Eo. lia.
    - match goal with Hx: Int.one = Int.zero |- _ => discriminate Hx end.
    - exfalso; lia.
    - forward.
      apply orb_false_iff in Eo. rewrite Z.ltb_ge, Z.gtb_ltb, Z.ltb_ge in Eo. entailer!. }
  Intros.
  change (Int.signed (Int.repr 8)) with 8. rewrite sub64_repr.
  once_loop_prop (r1 - 8 <= cap).
  { forward_if.
    - once_skip. once_skip. once_skip. once_skip. forward.
      Exists (Int64.unsigned (Int64.repr (-70))) (Zrepeat Vundef cap) Vundef.
      rewrite Int64.repr_unsigned. entailer!.
      split; [list_solve |]. u64.
      rewrite (skip_rs_cap s cap r1); auto. lia.
    - forward. entailer!; u64; lia. }
  Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L ?R)) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'5 (Vint (if r1 - 8 >? 0 then Int.one else Int.zero)) :: L) R)) end.
  { forward.
    - entailer!. u64. apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      assert (0 < cap) by lia. auto with valid_pointer.
    - entailer!. u64.
      replace (r1 - 8 >? 0) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
      match goal with Hf: field_compatible (tarray tuchar cap) [] dst |- _ =>
        destruct dst; try (destruct Hf; contradiction) end.
      reflexivity. }
  { forward. entailer!. u64.
    replace (r1 - 8 >? 0) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    reflexivity. }
  assert_PROP (field_compatible (tarray tuchar cap) [] dst) as Hfd by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength s)) [] src) as Hfs by entailer!.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L _)) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx [data_at sh (tarray tuchar (Zlength s)) (zbytes s) src;
      data_at shd (tarray tuchar cap) (zbytes (sublist 8 r1 s) ++ Zrepeat Vundef (cap - (r1 - 8))) dst;
      data_at_ shv tuint pv]))) end.
  { assert (Hk: 0 < r1 - 8).
    { destruct (r1 - 8 >? 0) eqn:Ec; [rewrite Z.gtb_ltb, Z.ltb_lt in Ec; lia |].
      match goal with Hx: Int.repr 0 <> Int.zero |- _ => contradiction Hx; reflexivity end. }
    rewrite (arr_split3 sh (Zlength s) 8 (r1 - 8) (zbytes s) src) by (auto; try list_solve; lia).
    change (data_at_ shd (tarray tuchar cap) dst) with (data_at_ shd (Tarray tuchar cap noattr) dst).
    rewrite (split2_data_at__Tarray_tuchar shd cap (r1 - 8) dst) by (auto; lia).
    rewrite !field_address0_offset by auto with field_compatible.
    simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. Intros.
    replace (8 + (r1 - 8)) with r1 by lia.
    forward_call (sh, shd, offset_val 8 src, dst,
                  existT (fun t => reptype t) (tarray tuchar (r1 - 8)) (sublist 8 r1 (zbytes s))).
    { cbn [projT1 projT2]. split; [rewrite sizeof_tarray_tuchar by lia; rep_lia |].
      rewrite sublist_map.
      apply memcpy_ok_zbytes; [list_solve | unfold bytes_ok in *; apply Forall_sublist; assumption]. }
    simpl projT1; simpl projT2. entailer!.
    rewrite (arr_split3 sh (Zlength s) 8 (r1 - 8) (zbytes s) src) by (auto; try list_solve; lia).
    replace (8 + (r1 - 8)) with r1 by lia.
    rewrite (split2_data_at_Tarray_app (r1 - 8) cap shd tuchar (zbytes (sublist 8 r1 s))
               (Zrepeat Vundef (cap - (r1 - 8))) dst) by list_solve.
    rewrite field_address0_offset by auto with field_compatible.
    simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. rewrite sublist_map.
    unfold data_at_. cancel. }
  { forward.
    assert (Hk: r1 = 8).
    { destruct (r1 - 8 >? 0) eqn:Ec; [| rewrite Z.gtb_ltb, Z.ltb_ge in Ec; lia].
      match goal with Hx: Int.one = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact Hx end. }
    subst r1. entailer!. rewrite sublist_nil. simpl app. replace (cap - (8 - 8)) with cap by lia.
    unfold data_at_. cancel. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L _)) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx [data_at sh (tarray tuchar (Zlength s)) (zbytes s) src;
      data_at shd (tarray tuchar cap) (zbytes (sublist 8 r1 s) ++ Zrepeat Vundef (cap - (r1 - 8))) dst;
      data_at shv tuint (Vint (Int.repr (le_field s 0 4 - ZSTD_MAGIC_SKIPPABLE_START))) pv]))) end.
  { forward. entailer!. }
  { assert_PROP (field_compatible tuint [] pv) as Hfp by entailer!.
    match goal with Hx: pv = nullval |- _ => rewrite Hx in Hfp end.
    destruct Hfp as [Hfp _]. contradiction. }
  forward.
  Exists (r1 - 8) (zbytes (sublist 8 r1 s) ++ Zrepeat Vundef (cap - (r1 - 8)))
    (Vint (Int.repr (le_field s 0 4 - ZSTD_MAGIC_SKIPPABLE_START))).
  entailer!.
  rewrite (skip_rs_some s cap r1) by auto.
  split; [list_solve |]. split; [list_solve | reflexivity].
Qed.

Lemma bodies_H_skip :
  semax_body Vprog H_G f_readSkippableFrameSize readSkippableFrameSize_spec /\
  semax_body Vprog H_G f_ZSTD_readSkippableFrame ZSTD_readSkippableFrame_spec.
Proof.
  exact (conj body_readSkippableFrameSize body_ZSTD_readSkippableFrame).
Qed.
