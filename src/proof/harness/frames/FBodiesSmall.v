(* The bodies of the small helpers of harness/laws_common.h and harness/frames.h satisfy their
   specifications (FSpecs.v), at any compspecs, in the context of the functions they call. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zstd.harness.api_split_invariant.code.
Require Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FLemmas.
Local Open Scope logic.

Section Bodies.
Context {cs: compspecs}.

Lemma body_put_le : semax_body [] G_put_le f_put_le put_le_spec.
Proof.
  start_function.
  forward_for_simple_bound k (EX j: Z,
    PROP ()
    LOCAL (temp _p (offset_val i p); temp _value (Vlong (Int64.repr v)); temp _size (Vlong (Int64.repr k)))
    SEP (data_at sh (tarray tuchar (Zlength c)) (Zstd.proof.zstd.Spec_util.mem_written c i j v) p)).
  - entailer!. unfold Zstd.proof.zstd.Spec_util.mem_written. simpl. autorewrite with sublist. auto.
  - assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val i p) (Vlong (Int64.repr i0))) =
                 field_address (tarray tuchar (Zlength c)) [ArraySubsc (i + i0)] p) as E.
    { entailer!. rewrite field_address_offset by auto with field_compatible. simpl. f_equal; lia. }
    forward.
    + entailer!. rewrite !Int64.Z_mod_modulus_eq.
      rewrite (Z.mod_small i0) by (change Int64.modulus with (2^64); lia).
      rewrite (Z.mod_small (8 * i0)) by (change Int64.modulus with (2^64); lia). lia.
    + entailer!. rewrite fk_byte_of_shift by lia. rewrite fk_mem_written_step by lia. unfold data_at. cancel.
  - entailer!.
Qed.


Lemma body_upto : semax_body [] G_upto f_upto upto_spec.
Proof.
  start_function.
  forward_call tt. Intros v.
  forward_if (PROP () LOCAL (temp _t'2 (Vlong (Int64.repr (Z.min v max)))) SEP ()).
  - forward. entailer!. rewrite Z.min_l by lia. reflexivity.
  - forward. entailer!. rewrite Z.min_r by lia. reflexivity.
  - forward. Exists (Z.min v max). entailer!.
Qed.

Lemma body_any_bytes : semax_body [] G_any_bytes f_any_bytes any_bytes_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rewrite Z.mul_1_l. rep_lia. }
  Intros p.
  (* the state after the call of nondet_bytes, if any *)
  set (Post := EX l: list Z, PROP (Zlength l = n; bytes_ok l) LOCAL (temp _bytes p; gvars gv)
                 SEP (mem_mgr gv; mbytes n l p)).
  destruct (eq_dec p nullval) as [Hp | Hp].
  - subst p.
    forward_if (PROP () LOCAL (temp _bytes nullval; gvars gv; temp _t'2 (Vint Int.zero)) SEP (mem_mgr gv)).
    + discriminate.
    + forward. entailer!.
    + forward_if Post. { exfalso; first [congruence | discriminate]. }
      { forward. unfold Post. Exists (Zrepeat 0 n). entailer!.
        split. apply Zlength_Zrepeat; lia. unfold Zrepeat. apply Forall_repeat. unfold is_byte; lia. }
      unfold Post. Intros l. forward. Exists nullval l. entailer!.
  - Intros.
    destruct (Z.eq_dec n 0) as [Hn | Hn].
    + subst n.
      forward_if (PROP () LOCAL (temp _bytes p; gvars gv; temp _t'2 (Vint Int.zero))
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar 0) p; data_at_ Ews (tarray tuchar 0) p)).
      * forward. entailer!.
      * contradiction.
      * forward_if Post. { exfalso; first [congruence | discriminate]. }
        { forward. unfold Post. Exists (@nil Z). entailer!.
          { constructor. }
          unfold mbytes. rewrite if_false by auto. cancel. }
        unfold Post. Intros l. forward. Exists p l. entailer!.
    + forward_if (PROP () LOCAL (temp _bytes p; gvars gv; temp _n (Vlong (Int64.repr n)); temp _t'2 (Vint Int.one))
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) p; data_at_ Ews (tarray tuchar n) p)).
      * forward. entailer!.
        unfold Int64.cmpu. rewrite Int64.eq_false; [reflexivity |].
        intro X. apply repr_inj_unsigned64 in X; rep_lia.
      * contradiction.
      * forward_if Post.
        { forward_call (p, n, Ews). Intros bs.
          unfold Post. Exists bs. entailer!.
          { eapply Forall_impl; [| eassumption]. unfold is_byte; simpl; rep_lia. }
          unfold mbytes. rewrite if_false by auto. cancel. }
        { exfalso; first [congruence | discriminate]. }
        unfold Post. Intros l. forward. Exists p l. entailer!.
Qed.

(* an array of n bytes in memory has n < 2^64 *)
Lemma fk_array_len : forall n p, field_compatible (tarray tuchar n) [] p -> n <= Int64.max_unsigned.
Proof.
  intros n p [Hp [_ [Hs _]]]. destruct p; try contradiction.
  unfold size_compatible in Hs. simpl sizeof in Hs.
  pose proof (Ptrofs.unsigned_range i). change Ptrofs.modulus with (2^64) in *.
  change Int64.max_unsigned with (2^64-1). lia.
Qed.

(* an element of a byte string is a byte *)
Lemma fk_Znth_byte : forall l i, bytes_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l <= Byte.max_unsigned.
Proof.
  intros l i Hl Hi. unfold bytes_ok in Hl. rewrite Forall_Znth in Hl. specialize (Hl i Hi). unfold is_byte in Hl. rep_lia.
Qed.

Lemma body_copy_of : semax_body [] G_copy_of f_copy_of copy_of_spec.
Proof.
  start_function.
  assert_PROP (Zlength l <= Int64.max_unsigned) as Hl.
  { entailer!. eapply fk_array_len; eassumption. }
  forward_call (tarray tuchar (Zlength l), gv).
  { simpl. rewrite Z.max_r by rep_lia. rewrite Z.mul_1_l. rep_lia. }
  Intros q.
  forward.
  destruct (eq_dec q nullval) as [Hq | Hq].
  - subst q.
    forward_loop (PROP () LOCAL (temp _copy nullval; gvars gv) SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p))
      break: (PROP () LOCAL (temp _copy nullval; gvars gv) SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p)).
    + entailer!.
    + forward_if (PROP () LOCAL (temp _copy nullval; gvars gv; temp _t'2 (Vint Int.zero))
                    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p)).
      * exfalso; first [congruence | discriminate].
      * forward. entailer!.
      * forward_if. { exfalso; first [congruence | discriminate]. }
        forward. entailer!.
    + forward. Exists nullval. entailer!.
  - Intros.
    forward_loop (EX i: Z, PROP (0 <= i <= Zlength l)
        LOCAL (temp _copy q; temp _i (Vlong (Int64.repr i)); temp _source p; temp _n (Vlong (Int64.repr (Zlength l))); gvars gv)
        SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p; malloc_token Ews (tarray tuchar (Zlength l)) q;
             data_at Ews (tarray tuchar (Zlength l)) (zbytes (sublist 0 i l) ++ Zrepeat Vundef (Zlength l - i)) q))
      continue: (EX i: Z, PROP (0 <= i < Zlength l)
        LOCAL (temp _copy q; temp _i (Vlong (Int64.repr i)); temp _source p; temp _n (Vlong (Int64.repr (Zlength l))); gvars gv)
        SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p; malloc_token Ews (tarray tuchar (Zlength l)) q;
             data_at Ews (tarray tuchar (Zlength l)) (zbytes (sublist 0 (i + 1) l) ++ Zrepeat Vundef (Zlength l - (i + 1))) q))
      break: (PROP () LOCAL (temp _copy q; gvars gv)
        SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p; malloc_token Ews (tarray tuchar (Zlength l)) q;
             data_at Ews (tarray tuchar (Zlength l)) (zbytes l) q)).
    + Exists 0. entailer!. autorewrite with sublist. unfold data_at_, field_at_, data_at. simpl.
      apply derives_refl.
    + Intros i.
      forward_if (PROP () LOCAL (temp _copy q; temp _i (Vlong (Int64.repr i)); temp _source p;
            temp _n (Vlong (Int64.repr (Zlength l))); gvars gv;
            temp _t'2 (Vint (if zlt i (Zlength l) then Int.one else Int.zero)))
          SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p;
               malloc_token Ews (tarray tuchar (Zlength l)) q;
               data_at Ews (tarray tuchar (Zlength l)) (zbytes (sublist 0 i l) ++ Zrepeat Vundef (Zlength l - i)) q)).
      { forward. entailer!. destruct (zlt i (Zlength l)); reflexivity. }
      { contradiction. }
      destruct (zlt i (Zlength l)) as [Hi | Hi].
      2: { forward_if. { exfalso; first [congruence | discriminate]. }
           forward. assert (i = Zlength l) by lia. subst i. entailer!.
           autorewrite with sublist. apply derives_refl. }
      forward_if. 2: { exfalso; first [congruence | discriminate]. }
      pose proof (fk_Znth_byte l i H ltac:(lia)) as Hb.
      forward.
      { entailer!. lia. }
      forward.
      Exists i. entailer!.
      apply derives_refl'. f_equal. list_solve.
    + Intros i. forward. Exists (i + 1). entailer!.
    + forward. Exists q. entailer!. unfold mbytes. rewrite if_false by auto. cancel.
Qed.

Lemma body_bytes_eq : semax_body [] G_bytes_eq f_bytes_eq bytes_eq_spec.
Proof.
  start_function.
  assert_PROP (Zlength la <= Int64.max_unsigned) as Hl.
  { entailer!. eapply fk_array_len; eassumption. }
  forward_for_simple_bound (Zlength la) (EX i: Z,
    PROP (sublist 0 i la = sublist 0 i lb)
    LOCAL (temp _a a; temp _b b; temp _n (Vlong (Int64.repr (Zlength la))))
    SEP (data_at sha (tarray tuchar (Zlength la)) (zbytes la) a;
         data_at shb (tarray tuchar (Zlength lb)) (zbytes lb) b)).
  - entailer!.
  - cbv beta. Intros. rename H3 into Hsub.
    pose proof (fk_Znth_byte la i H ltac:(lia)) as Ha.
    pose proof (fk_Znth_byte lb i H0 ltac:(lia)) as Hb.
    forward. { entailer!. lia. }
    forward. { entailer!. lia. }
    forward_if.
    + forward.
      destruct (list_eq_dec Z.eq_dec la lb) as [E | E]; [subst lb; contradiction | entailer!].
    + forward. entailer!.
      rewrite !(sublist_split 0 i (i + 1)) by lia. rewrite Hsub, !sublist_len_1 by lia. rewrite H3. reflexivity.
  - forward.
    rewrite sublist_same in H2 by lia. rewrite H1, sublist_same in H2 by lia. subst lb.
    rewrite if_true by auto. entailer!.
Qed.

(* the error code a result carries is below 120: an int that compares with 64 exactly *)
Lemma fk_error_of_range : forall r, 0 <= r <= Int64.max_unsigned ->
  0 <= Zstd.proof.zstd.Spec_util.error_of r < 120.
Proof.
  intros r Hr. unfold Zstd.proof.zstd.Spec_util.error_of, Zstd.proof.model.Bytes.is_error_code.
  destruct (2 ^ 64 - 120 <? r) eqn:E; [apply Z.ltb_lt in E | lia].
  change Int64.max_unsigned with (2 ^ 64 - 1) in Hr. lia.
Qed.

Lemma body_out_of_memory : semax_body [] G_out_of_memory f_out_of_memory out_of_memory_spec.
Proof.
  start_function.
  forward_call r.
  forward.
  pose proof (fk_error_of_range r H). entailer!.
  destruct (Z.eq_dec _ 64) as [E | E].
  - rewrite E. reflexivity.
  - rewrite Int.eq_false; [reflexivity |].
    intro X. apply repr_inj_unsigned in X; rep_lia.
Qed.

(* The two header words of a skippable frame written by put_le into a fresh object of 8 + s bytes: the
   magic number, then the size s; the s bytes of user data are still undefined. *)
Lemma fk_sk_header_written : forall m s, 0 <= s ->
  Zstd.proof.zstd.Spec_util.mem_written
    (Zstd.proof.zstd.Spec_util.mem_written (Zrepeat Vundef (8 + s)) 0 4 m) 4 4 s =
  zbytes (le_bytes 4 m ++ le_bytes 4 s) ++ Zrepeat Vundef s.
Proof.
  intros m s Hs. unfold Zstd.proof.zstd.Spec_util.mem_written.
  pose proof (Zstd.proof.zstd.PickLemmas.Zlength_le_bytes 4 m) as L1.
  pose proof (Zstd.proof.zstd.PickLemmas.Zlength_le_bytes 4 s) as L2.
  change (Z.of_nat 4) with 4 in L1, L2. change (Z.to_nat 4) with 4%nat.
  rewrite map_app. list_solve.
Qed.

(* a skippable frame is its 8 header bytes and its user data *)
Lemma fk_sk_bytes_length : forall k u, Zlength (sk_bytes k u) = 8 + Zlength u.
Proof.
  intros k u. unfold sk_bytes. rewrite !Zlength_app, !Zstd.proof.zstd.PickLemmas.Zlength_le_bytes. cbn; lia.
Qed.

Lemma body_new_skippable : semax_body [] G_new_skippable f_new_skippable new_skippable_spec.
Proof.
  start_function.
  forward_call 4294967295.
  Intros size.
  forward_call (tarray tuchar (8 + size), gv).
  { simpl. rep_lia. }
  Intros f.
  forward_if (f <> nullval).
  { if_tac; entailer!. }
  { forward. Exists nullval. rewrite if_true by auto. entailer!. }
  { forward. entailer!. }
  Intros. rewrite if_false by auto.
  forward_call tt.
  Intros b.
  set (c0 := Zrepeat Vundef (8 + size)).
  replace (data_at_ Ews (tarray tuchar (8 + size)) f) with (data_at Ews (tarray tuchar (Zlength c0)) c0 f)
    by (unfold c0, data_at_; rewrite Zlength_Zrepeat by lia; reflexivity).
  assert (Hk: 0 <= Z.land b 15 < 16).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (Lc0: Zlength c0 = 8 + size) by (unfold c0; rewrite Zlength_Zrepeat; lia).
  forward_call (Ews, f, c0, 0, ZSTD_MAGIC_SKIPPABLE_START + Z.land b 15, 4).
  { entailer!. simpl. rewrite !Int.signed_repr by rep_lia. reflexivity. }
  { unfold ZSTD_MAGIC_SKIPPABLE_START. rep_lia. }
  set (m := ZSTD_MAGIC_SKIPPABLE_START + Z.land b 15).
  set (c1 := Zstd.proof.zstd.Spec_util.mem_written c0 0 4 m).
  assert (Lc1: Zlength c1 = Zlength c0).
  { unfold c1, Zstd.proof.zstd.Spec_util.mem_written.
    pose proof (Zstd.proof.zstd.PickLemmas.Zlength_le_bytes 4 m) as L1. change (Z.of_nat 4) with 4 in L1.
    change (Z.to_nat 4) with 4%nat. rewrite !Zlength_app, Zlength_map, L1, !Zlength_sublist by lia. lia. }
  rewrite <- Lc1.
  forward_call (Ews, f, c1, 4, size, 4).
  { entailer!. }
  rewrite Lc1, Lc0. unfold c1, c0. rewrite fk_sk_header_written by lia.
  set (hd := le_bytes 4 m ++ le_bytes 4 size).
  assert (Lhd: Zlength hd = 8).
  { unfold hd. rewrite Zlength_app, !Zstd.proof.zstd.PickLemmas.Zlength_le_bytes. reflexivity. }
  forward_if (PROP ()
    LOCAL (temp _f f; temp _size (Vlong (Int64.repr size)); gvars gv; temp _len lp)
    SEP (EX u: list Z, !! (Zlength u = size /\ bytes_ok u) &&
           data_at Ews (tarray tuchar (8 + size)) (zbytes (sk_bytes (Z.land b 15) u)) f;
         mem_mgr gv; malloc_token Ews (tarray tuchar (8 + size)) f; data_at_ shl tulong lp)).
  - assert_PROP (field_compatible (tarray tuchar (8 + size)) [] f) as FC by entailer!.
    unfold tarray.
    rewrite (split2_data_at_Tarray_tuchar Ews (8 + size) 8) by (rewrite ?Zlength_app, ?Zlength_map; list_solve).
    replace (sublist 0 8 (zbytes hd ++ Zrepeat Vundef size)) with (zbytes hd) by list_solve.
    replace (sublist 8 (8 + size) (zbytes hd ++ Zrepeat Vundef size)) with (Zrepeat Vundef size) by list_solve.
    replace (8 + size - 8) with size by lia.
    change (data_at Ews (Tarray tuchar size noattr) (Zrepeat Vundef size))
      with (data_at_ Ews (tarray tuchar size)).
    forward_call (field_address0 (Tarray tuchar (8 + size) noattr) [ArraySubsc 8] f, size, Ews).
    { entailer!. }
    Intros u. Exists u.
    assert (E: sk_bytes (Z.land b 15) u = hd ++ u).
    { unfold sk_bytes, hd, m. rewrite H3, app_assoc. reflexivity. }
    rewrite E. unfold tarray.
    rewrite (split2_data_at_Tarray_tuchar Ews (8 + size) 8 (zbytes (hd ++ u)))
      by (rewrite ?Zlength_app, ?Zlength_map; list_solve).
    replace (sublist 0 8 (zbytes (hd ++ u))) with (zbytes hd) by list_solve.
    replace (sublist 8 (8 + size) (zbytes (hd ++ u))) with (zbytes u) by list_solve.
    replace (8 + size - 8) with size by lia.
    entailer!.
    eapply Forall_impl; [| eassumption]. intros x Hx. unfold is_byte. rep_lia.
  - assert (size = 0).
    { apply (f_equal Int64.unsigned) in H2. rewrite Int64.unsigned_repr in H2 by rep_lia. exact H2. }
    subst size. forward. Exists (@nil Z).
    assert (E: sk_bytes (Z.land b 15) [] = hd) by (unfold sk_bytes, hd, m; rewrite app_nil_r; reflexivity).
    rewrite E. entailer!. constructor.
  - Intros u.
    forward.
    forward.
    Exists f. rewrite if_false by auto. Exists (Z.land b 15) u.
    unfold mbytes. rewrite if_false by auto. rewrite fk_sk_bytes_length.
    entailer!.
Qed.

(* an object of malloc, or NULL, is a pointer that may be compared (with NULL) *)
Lemma mbytes_valid_pointer : forall n l p, mbytes n l p |-- valid_pointer p.
Proof.
  intros n l p. unfold mbytes. destruct (eq_dec p nullval) as [E|E].
  - subst. apply valid_pointer_null.
  - destruct (zlt 0 n).
    + apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
    + apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl; lia.
Qed.
#[local] Hint Resolve mbytes_valid_pointer : valid_pointer.

(* what free takes: the object of malloc, any contents, or NULL *)
Lemma mbytes_free_pre : forall n l p,
  mbytes n l p |-- if eq_dec p nullval then emp
                   else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p.
Proof.
  intros n l p. unfold mbytes. destruct (eq_dec p nullval); [auto|]. cancel.
Qed.

Lemma mbytes_nonnull : forall n l p, p <> nullval ->
  mbytes n l p = malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (zbytes l) p.
Proof. intros n l p E. unfold mbytes. destruct (eq_dec p nullval); [contradiction | reflexivity]. Qed.

Lemma mbytes_null : forall n l, mbytes n l nullval = emp.
Proof. intros n l. unfold mbytes. destruct (eq_dec nullval nullval); [reflexivity | contradiction]. Qed.

Lemma fk_byte_Znth : forall l i, bytes_ok l -> 0 <= i < Zlength l -> 0 <= Znth i l < 256.
Proof. intros l i H Hi. unfold bytes_ok in H. eapply Forall_Znth in H; [exact H | lia]. Qed.

(* the copy loop of join: byte i of l stored (as unsigned char) after bytes 0..i-1 *)
Lemma fk_copy_step : forall (l: list Z) i,
  bytes_ok l -> 0 <= i < Zlength l ->
  upd_Znth i (zbytes (sublist 0 i l) ++ Zrepeat Vundef (Zlength l - i))
    (Vint (Int.zero_ext 8 (Int.repr (Znth i l)))) =
  zbytes (sublist 0 (i + 1) l) ++ Zrepeat Vundef (Zlength l - (i + 1)).
Proof.
  intros l i Hl Hi. pose proof (fk_byte_Znth l i Hl Hi).
  rewrite zero_ext_inrange
    by (rewrite Int.unsigned_repr by rep_lia; change (two_p 8) with 256; lia).
  list_solve.
Qed.

(* the unsigned 64-bit comparisons of join, on values in range *)
Lemma fk_cmpu_eq0 : forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.cmpu Ceq (Int64.repr x) (Int64.repr (Int.signed (Int.repr 0))) = Z.eqb x 0.
Proof.
  intros x Hx. change (Int.signed (Int.repr 0)) with 0. simpl. unfold Int64.eq.
  rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zeq x 0), (Z.eqb_spec x 0); auto; lia.
Qed.

Lemma fk_cmpu_lt : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.cmpu Clt (Int64.repr x) (Int64.repr y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt x y), (Z.ltb_spec x y); auto; lia.
Qed.

(* join's size test a_len <= PTRDIFF_MAX - b_len (size_t), when b_len <= PTRDIFF_MAX *)
Lemma fk_cmpu_le_sub : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= PTRDIFF_MAX ->
  Int64.cmpu Cle (Int64.repr x) (Int64.sub (Int64.repr 9223372036854775807) (Int64.repr y)) = true ->
  x + y <= PTRDIFF_MAX.
Proof.
  intros x y Hx Hy C. unfold PTRDIFF_MAX in *. simpl in C. unfold Int64.ltu in C.
  rewrite Int64.sub_signed in C.
  rewrite (Int64.signed_repr 9223372036854775807) in C by rep_lia.
  rewrite (Int64.signed_repr y) in C by rep_lia.
  rewrite !Int64.unsigned_repr in C by rep_lia.
  destruct (zlt (9223372036854775807 - y) x); [discriminate | lia].
Qed.

Lemma body_join : semax_body [] G_join f_join join_spec.
Proof.
  start_function.
  forward_if (EX v1: int,
    PROP (v1 <> Int.zero -> a <> nullval \/ Zlength la = 0)
    LOCAL (temp _t'1 (Vint v1); gvars gv; temp _a a; temp _a_len (Vlong (Int64.repr (Zlength la)));
           temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
    SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b)).
  - forward. Exists Int.one. entailer!.
  - forward. rewrite fk_cmpu_eq0 by rep_lia.
    Exists (if Zlength la =? 0 then Int.one else Int.zero). entailer!.
    split; [intros N; destruct (Z.eqb_spec (Zlength la) 0); [auto | contradiction]
           | destruct (Zlength la =? 0); reflexivity].
  - Intros v1.
    forward_if (EX v2: int,
      PROP (v2 <> Int.zero -> (a <> nullval \/ Zlength la = 0) /\ (b <> nullval \/ Zlength lb = 0))
      LOCAL (temp _t'2 (Vint v2); gvars gv; temp _a a; temp _a_len (Vlong (Int64.repr (Zlength la)));
             temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
      SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b)).
    + forward_if.
      * forward. Exists Int.one. entailer!.
      * forward. forward. rewrite fk_cmpu_eq0 by rep_lia.
        Exists (if Zlength lb =? 0 then Int.one else Int.zero). entailer!.
        split; [intros N; destruct (Z.eqb_spec (Zlength lb) 0); [auto | contradiction]
               | destruct (Zlength lb =? 0); reflexivity].
    + forward. Exists Int.zero. entailer!.
    + Intros v2.
      forward_if (EX v3: int,
        PROP (v3 <> Int.zero -> ((a <> nullval \/ Zlength la = 0) /\ (b <> nullval \/ Zlength lb = 0)) /\
                                (Zlength lb <= PTRDIFF_MAX -> Zlength la + Zlength lb <= PTRDIFF_MAX))
        LOCAL (temp _t'3 (Vint v3); gvars gv; temp _a a; temp _a_len (Vlong (Int64.repr (Zlength la)));
               temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
        SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b)).
      * forward.
        match goal with |- context [bool2val ?c] => set (cc := c) end.
        assert (Hc: cc = true -> Zlength lb <= PTRDIFF_MAX -> Zlength la + Zlength lb <= PTRDIFF_MAX).
        { intros E Hlb. apply fk_cmpu_le_sub; [rep_lia | rep_lia | exact E]. }
        clearbody cc. Exists (Int.repr (Z.b2z cc)).
        destruct cc; entailer!.
      * forward. Exists Int.zero. entailer!.
      * Intros v3. forward.
        forward_if (EX ab: val,
          PROP (ab <> nullval -> ((a <> nullval \/ Zlength la = 0) /\ (b <> nullval \/ Zlength lb = 0)) /\
                                 (Zlength lb <= PTRDIFF_MAX -> Zlength la + Zlength lb <= PTRDIFF_MAX))
          LOCAL (temp _t'4 ab; gvars gv; temp _a a; temp _a_len (Vlong (Int64.repr (Zlength la)));
                 temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
          SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b;
               if eq_dec ab nullval then emp
               else malloc_token Ews (tarray tuchar (Zlength la + Zlength lb)) ab *
                    data_at_ Ews (tarray tuchar (Zlength la + Zlength lb)) ab)).
        -- forward_call (tarray tuchar (Zlength la + Zlength lb), gv).
           { simpl. rep_lia. }
           Intros ab. forward. Exists ab. entailer!.
        -- forward. Exists nullval. entailer!.
        -- Intros ab. forward. forward.
           change (Int.signed (Int.repr 0)) with 0.
           set (n := Zlength la + Zlength lb).
           forward_loop (EX i: Z,
             PROP (0 <= i <= n)
             LOCAL (temp _i (Vlong (Int64.repr i)); temp _ab ab; gvars gv; temp _a a;
                    temp _a_len (Vlong (Int64.repr (Zlength la)));
                    temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
             SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b;
                  if eq_dec ab nullval then emp
                  else malloc_token Ews (tarray tuchar n) ab *
                       data_at Ews (tarray tuchar n)
                         (zbytes (sublist 0 i (la ++ lb)) ++ Zrepeat Vundef (n - i)) ab))
           break: (
             PROP ()
             LOCAL (temp _ab ab; gvars gv; temp _a a; temp _b b)
             SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b;
                  mbytes n (la ++ lb) ab)).
           ++ Exists 0. entailer!.
              destruct (eq_dec ab nullval); [auto|]. rewrite data_at__eq. simpl app. cancel.
           ++ Intros i.
              forward_if (
                PROP ()
                LOCAL (temp _t'6 (Vint (if eq_dec ab nullval then Int.zero
                                        else if zlt i n then Int.one else Int.zero));
                       temp _i (Vlong (Int64.repr i)); temp _ab ab; gvars gv; temp _a a;
                       temp _a_len (Vlong (Int64.repr (Zlength la)));
                       temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
                SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b;
                     if eq_dec ab nullval then emp
                     else malloc_token Ews (tarray tuchar n) ab *
                          data_at Ews (tarray tuchar n)
                            (zbytes (sublist 0 i (la ++ lb)) ++ Zrepeat Vundef (n - i)) ab)).
              ** destruct (eq_dec ab nullval); entailer!.
              ** destruct (eq_dec ab nullval); [contradiction|].
                 Intros. forward. entailer!.
                 rewrite fk_cmpu_lt by rep_lia.
                 destruct (zlt i (Zlength la + Zlength lb)), (Z.ltb_spec i (Zlength la + Zlength lb));
                   try lia; reflexivity.
              ** forward. destruct (eq_dec ab nullval); [|contradiction]. entailer!.
              ** forward_if.
                 --- change (EqDec_val ab nullval) with (eq_dec ab nullval) in *.
                     destruct (eq_dec ab nullval) as [|Hab]; [contradiction|].
                     destruct (zlt i n) as [Hi|]; [|contradiction].
                     destruct (H7 Hab) as [[Ha Hb] _]. Intros.
                     forward_if (
                       PROP ()
                       LOCAL (temp _t'7 (Vint (Int.repr (Znth i (la ++ lb))));
                              temp _i (Vlong (Int64.repr i)); temp _ab ab; gvars gv; temp _a a;
                              temp _a_len (Vlong (Int64.repr (Zlength la)));
                              temp _b b; temp _b_len (Vlong (Int64.repr (Zlength lb))))
                       SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b;
                            malloc_token Ews (tarray tuchar n) ab;
                            data_at Ews (tarray tuchar n)
                              (zbytes (sublist 0 i (la ++ lb)) ++ Zrepeat Vundef (n - i)) ab)).
                     +++ destruct (eq_dec a nullval) as [Ea|Ea]; [destruct Ha; [contradiction|lia]|].
                         rewrite (mbytes_nonnull _ _ a Ea). Intros.
                         pose proof (fk_byte_Znth la i H ltac:(lia)).
                         forward.
                         { entailer!. rep_lia. }
                         forward. entailer!.
                         { rewrite app_Znth1 by lia. reflexivity. }
                         rewrite (mbytes_nonnull _ _ a Ea). cancel.
                     +++ destruct (eq_dec b nullval) as [Eb|Eb]; [destruct Hb; [contradiction|lia]|].
                         rewrite (mbytes_nonnull _ _ b Eb). Intros.
                         pose proof (fk_byte_Znth lb (i - Zlength la) H0 ltac:(lia)).
                         forward.
                         { entailer!. rep_lia. }
                         forward. entailer!.
                         { rewrite app_Znth2 by lia. reflexivity. }
                         rewrite (mbytes_nonnull _ _ b Eb). cancel.
                     +++ forward. forward.
                         Exists (i + 1). entailer!.
                         assert (bytes_ok (la ++ lb)) by (apply Forall_app; auto).
                         pose proof (fk_copy_step (la ++ lb) i ltac:(auto) ltac:(rewrite Zlength_app; lia)) as E.
                         rewrite Zlength_app in E. rewrite E. cancel.
                 --- change (EqDec_val ab nullval) with (eq_dec ab nullval) in *.
                     forward. destruct (eq_dec ab nullval) as [Eab|Hab].
                     +++ subst ab. rewrite mbytes_null. entailer!.
                     +++ destruct (zlt i n) as [|Hi]; [discriminate|].
                         rewrite (mbytes_nonnull _ _ ab Hab).
                         assert (i = n) by lia. subst i. entailer!.
                         rewrite sublist_same by (rewrite ?Zlength_app; lia).
                         rewrite Z.sub_diag, app_nil_r. cancel.
           ++ sep_apply (mbytes_free_pre (Zlength la) la a).
              forward_call (tarray tuchar (Zlength la), a, gv).
              sep_apply (mbytes_free_pre (Zlength lb) lb b).
              forward_call (tarray tuchar (Zlength lb), b, gv).
              forward. Exists ab. entailer!.
              { apply (proj2 (H7 H8) H9). }
              unfold n. cancel.
Qed.

End Bodies.
