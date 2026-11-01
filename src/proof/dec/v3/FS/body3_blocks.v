(* FS3 bodies, blocks3: frame-level helpers (port of v2 body_FS_blocks.v, specifications unchanged).
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Ltac fif_set id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Ltac head_dw0 c :=
  lazymatch c with Sloop _ Sbreak => idtac | Ssequence ?a _ => head_dw0 a end.

Ltac dw0 :=
  match goal with |- semax _ ?P ?c _ => head_dw0 c;
    first [ forward_loop P break: P; [entailer! | forward; entailer! | ]
          | forward_loop P break: P;
            [entailer! | forward_if P; [exfalso; lia | forward; entailer! | forward; entailer!] | ] ] end.

Section CM_body3_blocks_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* dst = p + d of an output array with d + cap <= N, compared with NULL *)
Lemma arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma dst_test_null W sh N (c: list val) p d cap :
  sepalg.nonidentity sh -> isptr p -> 0 <= d -> 0 <= cap -> d + cap <= N ->
  (cap = 0 -> pws_pred W |-- weak_valid_pointer (offset_val d p)) ->
  pws_pred W * data_at sh (tarray tuchar N) c p |-- denote_tc_test_eq (offset_val d p) (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Hp Hd Hc HN HW. destruct p; try contradiction.
  Transparent denote_tc_test_eq.
  unfold denote_tc_test_eq; simpl. apply andp_right; [apply prop_right; reflexivity |].
  change (Vptr b (Ptrofs.add i (Ptrofs.repr d))) with (offset_val d (Vptr b i)).
  destruct (zeq cap 0) as [-> | Hc0].
  - apply sepcon_weak_valid_pointer1. apply HW; auto.
  - apply sepcon_weak_valid_pointer2. apply arr_wvp; auto; lia.
Qed.

Lemma dst_test_null_R W sh N (c: list val) p d cap R :
  sepalg.nonidentity sh -> isptr p -> 0 <= d -> 0 <= cap -> d + cap <= N ->
  (cap = 0 -> pws_pred W |-- weak_valid_pointer (offset_val d p)) ->
  pws_pred W * data_at sh (tarray tuchar N) c p * R |-- denote_tc_test_eq (offset_val d p) (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Hp Hd Hc HN HW. destruct p; try contradiction.
  Transparent denote_tc_test_eq.
  unfold denote_tc_test_eq; simpl. apply andp_right; [apply prop_right; reflexivity |].
  change (Vptr b (Ptrofs.add i (Ptrofs.repr d))) with (offset_val d (Vptr b i)).
  apply sepcon_weak_valid_pointer1.
  destruct (zeq cap 0) as [-> | Hc0].
  - apply sepcon_weak_valid_pointer1. apply HW; auto.
  - apply sepcon_weak_valid_pointer2. apply arr_wvp; auto; lia.
Qed.

Lemma fa0_sub N p k :
  field_compatible (tarray tuchar N) [] p -> 0 <= k <= N ->
  field_address0 (Tarray tuchar N noattr) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

(* the output array around the written range [d, d + |bs|) *)
Lemma put_bytes_join sh N (oc: list val) p d (bs: list Z) n :
  field_compatible (tarray tuchar N) [] p -> Zlength oc = N -> Zlength bs = n -> 0 <= d -> d + n <= N ->
  data_at sh (Tarray tuchar d noattr) (sublist 0 d oc) p *
  data_at sh (tarray tuchar n) (zbytes bs) (offset_val d p) *
  data_at sh (Tarray tuchar (N - (d + n)) noattr) (sublist (d + n) N oc) (offset_val (d + n) p)
  |-- data_at sh (tarray tuchar N) (put_bytes oc d bs) p.
Proof.
  intros Fc HN Hn Hd Hb. subst n. unfold tarray at 2. pose proof (Zlength_nonneg bs).
  assert (Zlength (zbytes bs) = Zlength bs) as Hz by apply Zlength_map.
  assert (Zlength (put_bytes oc d bs) = N) by
    (unfold put_bytes; rewrite !Zlength_app, Hz, !Zlength_sublist by lia; lia).
  rewrite (split3_data_at_Tarray_tuchar sh N d (d + Zlength bs) (put_bytes oc d bs) p) by lia.
  rewrite !fa0_sub by (auto; lia).
  replace (d + Zlength bs - d) with (Zlength bs) by lia.
  unfold put_bytes. generalize dependent (zbytes bs); intros zb Hz.
  replace (sublist 0 d (sublist 0 d oc ++ zb ++ sublist (d + Zlength bs) (Zlength oc) oc))
    with (sublist 0 d oc) by list_solve.
  replace (sublist d (d + Zlength bs) (sublist 0 d oc ++ zb ++ sublist (d + Zlength bs) (Zlength oc) oc))
    with zb by list_solve.
  replace (sublist (d + Zlength bs) N (sublist 0 d oc ++ zb ++ sublist (d + Zlength bs) (Zlength oc) oc))
    with (sublist (d + Zlength bs) N oc) by list_solve.
  subst N. cancel.
Qed.

Lemma put_bytes_id (c: list val) d (bs: list Z) :
  0 <= d -> d + Zlength bs <= Zlength c -> sublist d (d + Zlength bs) c = zbytes bs -> put_bytes c d bs = c.
Proof.
  intros Hd Hb Hs. pose proof (Zlength_nonneg bs). unfold put_bytes. rewrite <- Hs.
  rewrite !sublist_rejoin by lia. apply sublist_same; lia.
Qed.

Lemma zbytes_tc (s: list Z) : bytes_ok s -> Forall (tc_val tuchar) (zbytes s).
Proof.
  intros Hs. apply Forall_map. eapply Forall_impl; [| exact Hs].
  intros x Hx. unfold is_byte in Hx. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* ---------- pointer comparisons (ZSTD_checkContinuity) ---------- *)

Lemma test_eq_sepcon_r x y R : denote_tc_test_eq x y * R |-- denote_tc_test_eq x y.
Proof.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq.
  destruct x, y; simpl; try (rewrite FF_sepcon; apply derives_refl).
  all: try (unfold test_eq_ptrs; destruct (sameblock _ _)).
  all: normalize.
  all: repeat apply andp_right; try (apply prop_right; auto; fail).
  1: { rewrite prop_sepcon. apply derives_extract_prop; intros; apply prop_right; auto. }
  all: first [apply sepcon_weak_valid_pointer1 | apply sepcon_valid_pointer1].
  all: first [apply derives_refl | apply andp_left1, derives_refl | apply andp_left2, derives_refl].
Qed.

Lemma test_eq_frame P R x y : (P |-- denote_tc_test_eq x y) -> P * R |-- denote_tc_test_eq x y.
Proof.
  intros H. eapply derives_trans; [apply sepcon_derives; [exact H | apply derives_refl] |].
  apply test_eq_sepcon_r.
Qed.

Lemma test_eq_pn x y :
  denote_tc_test_eq x y |-- !! (is_pointer_or_null x /\ is_pointer_or_null y).
Proof.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq.
  destruct x, y; simpl; try apply FF_left; normalize; apply prop_right; simpl; auto.
  all: unfold test_eq_ptrs; destruct (sameblock _ _); apply prop_right; simpl; auto.
Qed.

Lemma test_eq_cmp x y :
  denote_tc_test_eq x y |-- !! (sem_cmp_pp Cne x y = Some (Val.of_bool (negb (veqb x y)))).
Proof.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq.
  destruct x, y; simpl; try apply FF_left; normalize; apply prop_right.
  all: unfold sem_cmp_pp, veqb; simpl; try reflexivity.
  destruct (eq_block b b0) as [<- | Hb]; destruct (Val.eq (Vptr b i) (Vptr _ i0)) as [E | E].
  - inv E. rewrite Ptrofs.eq_true. reflexivity.
  - rewrite Ptrofs.eq_false by congruence. reflexivity.
  - inv E. congruence.
  - reflexivity.
Qed.

Lemma ptrdiff1 a b :
  Ptrofs.to_int64 (Ptrofs.divs (Ptrofs.sub a b) (Ptrofs.repr 1)) =
  Int64.repr (Ptrofs.unsigned a - Ptrofs.unsigned b).
Proof.
  unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
  unfold Ptrofs.to_int64, Ptrofs.sub. rewrite Ptrofs.unsigned_repr_eq.
  apply Int64.eqm_samerepr. apply Int64.eqm_sym. unfold Int64.eqm.
  change Ptrofs.modulus with Int64.modulus. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma sub_pl_offset o d :
  Ptrofs.sub o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr d))) = Ptrofs.add o (Ptrofs.repr (- d)).
Proof.
  change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one, Ptrofs.sub_add_opp. f_equal.
  unfold Ptrofs.of_int64. rewrite <- Ptrofs.neg_repr. f_equal.
  apply Ptrofs.eqm_samerepr. unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus.
  rewrite Int64.unsigned_repr_eq. apply Zbits.eqmod_sym, Zbits.eqmod_mod. reflexivity.
Qed.

Lemma veqb_01 : veqb (Vint (Int.repr 1)) (Vint (Int.repr 0)) = false.
Proof. reflexivity. Qed.

Lemma veqb_00 : veqb (Vint (Int.repr 0)) (Vint (Int.repr 0)) = true.
Proof. reflexivity. Qed.

Section Bodies.
Variables (DENT : dent_pred) (TABS : tabs_pred) (SR : srel3) (BR : blrel).

Lemma body_trace_end : body_ok (FS3_G DENT TABS SR BR) ZSTD_DCtx_trace_end_spec.
Proof.
  exists f_ZSTD_DCtx_trace_end; split; [reflexivity | split; [reflexivity | ]].
  start_function. forward. entailer!.
Qed.

Lemma body_setRleBlock : body_ok (FS3_G DENT TABS SR BR) ZSTD_setRleBlock_spec.
Proof.
  exists f_ZSTD_setRleBlock; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  destruct o as [osh obase oN oc od ocap]; unfold outarr_ok in H; simpl in H, H2.
  destruct H as (Hw & HN & HN32 & Hd & Hcap & Hdc).
  cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c].
  forward_loop (PROP () LOCAL (temp _dst (offset_val od obase); temp _dstCapacity (Vlong (Int64.repr ocap));
      temp _b (Vint (Int.repr b)); temp _regenSize (Vlong (Int64.repr n)))
      SEP (pws_pred W; data_at osh (tarray tuchar oN) oc obase))
    break: (PROP (n <= ocap) LOCAL (temp _dst (offset_val od obase); temp _dstCapacity (Vlong (Int64.repr ocap));
      temp _b (Vint (Int.repr b)); temp _regenSize (Vlong (Int64.repr n)))
      SEP (pws_pred W; data_at osh (tarray tuchar oN) oc obase)).
  - entailer!.
  - forward_if.
    + dw0.
      repeat dw0.
      forward.
      Exists (Int64.unsigned (Int64.repr (-70))) oc. cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c].
      replace (n >? ocap) with true by lia. rewrite Int64.repr_unsigned. entailer!. all: reflexivity.
    + forward. entailer!.
  - Intros.
    assert_PROP (isptr obase) by entailer!.
    match goal with |- semax _ ?P _ _ => forward_if P end.
    + apply dst_test_null with (cap := ocap); auto; try lia.
    + destruct obase; try contradiction; discriminate.
    + forward. entailer!.
    + assert_PROP (field_compatible (tarray tuchar oN) [] obase) as Fc by entailer!.
      unfold tarray. rewrite (split3_data_at_Tarray_tuchar osh oN od (od + n) oc obase) by lia.
      rewrite !fa0_sub by (auto; lia). replace (od + n - od) with n by lia.
      sep_apply (data_at_memory_block osh (Tarray tuchar n noattr) (sublist od (od + n) oc) (offset_val od obase)).
      replace (sizeof (Tarray tuchar n noattr)) with n by (simpl; lia).
      forward_call (osh, offset_val od obase, b, n).
      replace (Zrepeat (Vint (Int.repr b)) n) with (zbytes (Zrepeat b n)) by (unfold Zrepeat; apply map_repeat).
      sep_apply (put_bytes_join osh oN oc obase od (Zrepeat b n) n); auto; try lia.
      { apply Zlength_Zrepeat; lia. }
      forward.
      Exists n (put_bytes oc od (Zrepeat b n)). cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c].
      replace (n >? ocap) with false by lia. entailer!.
Qed.

Lemma body_copyRawBlock : body_ok (FS3_G DENT TABS SR BR) ZSTD_copyRawBlock_spec.
Proof.
  exists f_ZSTD_copyRawBlock; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  destruct o as [osh obase oN oc od ocap]; unfold outarr_ok in H; simpl in H, H1.
  destruct H as (Hw & HN & HN32 & Hd & Hcap & Hdc).
  destruct i as [ish ibase iN ic ioff s]; unfold inwin_ok, win_ok in H0; simpl in H0.
  destruct H0 as (Hr & Hoff & Hoffn & HiN32 & HiN & _ & Hbytes & Hsub).
  cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c iw_sh iw_base iw_N iw_c iw_off iw_s].
  pose proof (Zlength_nonneg s).
  dw0.
  forward_loop (PROP () LOCAL (temp _dst (offset_val od obase); temp _dstCapacity (Vlong (Int64.repr ocap));
      temp _src (offset_val ioff ibase); temp _srcSize (Vlong (Int64.repr (Zlength s))))
      SEP (pws_pred W; data_at osh (tarray tuchar oN) oc obase; data_at ish (tarray tuchar iN) ic ibase))
    break: (PROP (Zlength s <= ocap) LOCAL (temp _dst (offset_val od obase); temp _dstCapacity (Vlong (Int64.repr ocap));
      temp _src (offset_val ioff ibase); temp _srcSize (Vlong (Int64.repr (Zlength s))))
      SEP (pws_pred W; data_at osh (tarray tuchar oN) oc obase; data_at ish (tarray tuchar iN) ic ibase)).
  - entailer!.
  - forward_if.
    + dw0.
      repeat dw0.
      forward.
      Exists (Int64.unsigned (Int64.repr (-70))) oc. cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c iw_sh iw_base iw_N iw_c iw_off iw_s].
      replace (Zlength s >? ocap) with true by lia. rewrite Int64.repr_unsigned. entailer!. all: reflexivity.
    + forward. entailer!.
  - Intros.
    assert_PROP (isptr obase) by entailer!.
    match goal with |- semax _ ?P _ _ => forward_if P end.
    + apply dst_test_null_R with (cap := ocap); auto; try lia.
    + destruct obase; try contradiction; discriminate.
    + forward. entailer!.
    + assert_PROP (field_compatible (tarray tuchar oN) [] obase) as Fc by entailer!.
      assert_PROP (field_compatible (tarray tuchar iN) [] ibase) as Fi by entailer!.
      unfold tarray. rewrite (split3_data_at_Tarray_tuchar osh oN od (od + Zlength s) oc obase) by lia.
      rewrite (split3_data_at_Tarray_tuchar ish iN ioff (ioff + Zlength s) ic ibase) by lia.
      rewrite !fa0_sub by (auto; lia). replace (od + Zlength s - od) with (Zlength s) by lia.
      replace (ioff + Zlength s - ioff) with (Zlength s) by lia. rewrite Hsub.
      sep_apply (data_at_data_at_ osh (Tarray tuchar (Zlength s) noattr) (sublist od (od + Zlength s) oc)
                   (offset_val od obase)).
      forward_call (mm_disjoint ish osh (offset_val ioff ibase) (offset_val od obase) (Zlength s) (zbytes s)).
      { simpl mm_pre. unfold tarray. cancel. }
      { simpl. split3; auto. split; [apply Zlength_map |].
        split; [rep_lia | apply byte_val_zbytes; exact Hbytes]. }
      simpl mm_post.
      sep_apply (put_bytes_join osh oN oc obase od s (Zlength s)); auto; try lia.
      sep_apply (put_bytes_join ish iN ic ibase ioff s (Zlength s)); auto; try lia.
      rewrite put_bytes_id by (auto; lia).
      forward.
      Exists (Zlength s) (put_bytes oc od s).
      cbn [oa_d oa_base oa_cap oa_sh oa_N oa_c iw_sh iw_base iw_N iw_c iw_off iw_s].
      replace (Zlength s >? ocap) with false by lia. entailer!.
Qed.

Lemma body_checkContinuity : body_ok (FS3_G DENT TABS SR BR) ZSTD_checkContinuity_spec.
Proof.
  exists f_ZSTD_checkContinuity; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  unfold frame_fields. Intros.
  fif_set _t'2 (Vint (Int.repr (if cont_moves fs dst n then 1 else 0))).
  { assert (Hn: 0 < n) by (rewrite !Int64.unsigned_repr in H3 by rep_lia; lia).
    destruct H0 as [Hg | Hg]; rewrite Hg in *; forward.
    - assert_PROP (sem_cmp_pp Cne dst (fs_previousDstEnd fs) =
                   Some (Val.of_bool (negb (veqb dst (fs_previousDstEnd fs))))) as Hc.
      { go_lower. sep_apply (H1 Hn eq_refl). sep_apply (test_eq_cmp dst (fs_previousDstEnd fs)). entailer!. }
      assert_PROP (is_pointer_or_null dst /\ is_pointer_or_null (fs_previousDstEnd fs)) as Pdp.
      { go_lower. sep_apply (H1 Hn eq_refl). sep_apply (test_eq_pn dst (fs_previousDstEnd fs)). entailer!. }
      destruct Pdp as [Pd Pp].
      forward_if.
      { exfalso. auto. }
      forward. forward.
      { go_lower. apply test_eq_frame. apply H1; auto. }
      forward. entailer!.
      + rewrite Hc. unfold cont_moves. rewrite Hg, veqb_00.
        replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (veqb dst (fs_previousDstEnd fs)); reflexivity.
      + rewrite Hg; apply derives_refl.
    - forward_if.
      { forward. entailer!.
        - unfold cont_moves. rewrite Hg, veqb_01.
          replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        - rewrite Hg; apply derives_refl. }
      { exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
          change (Int.unsigned Int.zero) with 0 in Hx; lia end. } }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H3 by rep_lia.
    unfold cont_moves. replace (0 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct (orb _ _); reflexivity. }
  destruct (cont_moves fs dst n) eqn:Cm.
  - destruct (H2 eq_refl) as (Pdst & Htn & Hsb).
    destruct dst as [| | | | | bd od]; try contradiction.
    assert_PROP (is_pointer_or_null (fs_previousDstEnd fs)) as Pp.
    { go_lower. sep_apply Htn. sep_apply (test_eq_pn (fs_previousDstEnd fs) nullval). entailer!. }
    forward_if.
    2: { exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
          change (Int.unsigned Int.zero) with 0 in Hx; lia end. }
    forward. forward. forward.
    fif_set _t'1 (Vlong (Int64.repr (if veqb (fs_previousDstEnd fs) nullval then 0
                                     else vptr_diff (fs_previousDstEnd fs) (fs_prefixStart fs)))).
    { rewrite !sepcon_assoc. apply test_eq_frame. apply Htn. }
    { forward. entailer!. rewrite H4. reflexivity. }
    { specialize (Hsb H4).
      destruct (fs_previousDstEnd fs) as [| | | | | bp op] eqn:Epde; try contradiction.
      { simpl in Pp. subst. contradiction. }
      destruct (fs_prefixStart fs) as [| | | | | bs os] eqn:Eps; try discriminate.
      simpl in Hsb. destruct (peq bp bs) as [<- | ]; [| discriminate].
      forward. forward. forward.
      { entailer!. simpl. destruct (peq bp bp); [reflexivity | contradiction]. }
      entailer!. unfold veqb. destruct (Val.eq (Vptr bp op) nullval) as [E|E]; [discriminate|].
      unfold sem_sub_pp. simpl. destruct (eq_block bp bp); [|contradiction]. simpl.
      unfold Vptrofs. simpl. rewrite ptrdiff1. reflexivity. }
    forward. forward. forward. forward. unfold continuity. rewrite Cm. entailer!.
    unfold frame_fields. simpl. rewrite sub_pl_offset. cancel.
  - forward_if.
    { exfalso. auto. }
    forward. unfold continuity. rewrite Cm. entailer!. unfold frame_fields. cancel.
Qed.

End Bodies.

Lemma bodies_blocks3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_trace_end_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_checkContinuity_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_copyRawBlock_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_setRleBlock_spec).
Proof.
  split; [| split; [| split]]; intros DENT TABS SR BR _ _.
  - apply body_trace_end.
  - apply body_checkContinuity.
  - apply body_copyRawBlock.
  - apply body_setRleBlock.
Qed.

End CM_body3_blocks_1.
