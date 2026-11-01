(* X2T body: HUF_fillDTableX2ForWeight. *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Local Open Scope Z_scope.

(* the cells after i symbols and j cells of symbol i *)
Definition fwc (syms: list Z) (nb bs lv len i j: Z) : list val :=
  fw_u32s (sublist 0 i syms) nb bs lv len ++ Zrepeat (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) j ++
  Zrepeat Vundef (Zlength syms * len - i * len - j).

Lemma fw_u32s_len: forall syms nb bs lv len, 0 <= len ->
  Zlength (fw_u32s syms nb bs lv len) = Zlength syms * len.
Proof.
  intros. unfold fw_u32s. induction syms as [|s r IH]; simpl flat_map.
  - reflexivity.
  - rewrite Zlength_app, IH, Zlength_cons, Zlength_repeat by lia. lia.
Qed.

Lemma fw_u32s_snoc: forall syms nb bs lv len i, 0 <= i < Zlength syms ->
  fw_u32s (sublist 0 (i + 1) syms) nb bs lv len =
  fw_u32s (sublist 0 i syms) nb bs lv len ++ Zrepeat (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) len.
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
  unfold fw_u32s. rewrite flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma fwc_len: forall syms nb bs lv len i j, 0 <= len -> 0 <= i <= Zlength syms -> 0 <= j ->
  i * len + j <= Zlength syms * len ->
  Zlength (fwc syms nb bs lv len i j) = Zlength syms * len.
Proof.
  intros. unfold fwc. rewrite !Zlength_app, fw_u32s_len, !Zlength_Zrepeat by (try rewrite Zlength_sublist; lia).
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma fwc_init: forall syms nb bs lv len,
  fwc syms nb bs lv len 0 0 = Zrepeat Vundef (Zlength syms * len).
Proof.
  intros. unfold fwc. rewrite sublist_nil. unfold fw_u32s; simpl. f_equal. lia.
Qed.

Lemma fwc_final: forall syms nb bs lv len, 0 <= len ->
  fwc syms nb bs lv len (Zlength syms) 0 = fw_u32s syms nb bs lv len.
Proof.
  intros. unfold fwc. rewrite sublist_same by lia. simpl.
  replace (Zlength syms * len - Zlength syms * len - 0) with 0 by lia. simpl. apply app_nil_r.
Qed.

Lemma fwc_next: forall syms nb bs lv len i, 0 <= len -> 0 <= i < Zlength syms ->
  fwc syms nb bs lv len i len = fwc syms nb bs lv len (i + 1) 0.
Proof.
  intros. unfold fwc. rewrite fw_u32s_snoc by lia. rewrite <- app_assoc. f_equal. simpl.
  f_equal. f_equal. lia.
Qed.

Lemma fwc_step: forall syms nb bs lv len i j, 0 <= i < Zlength syms -> 0 <= j < len ->
  i * len + len <= Zlength syms * len ->
  upd_Znth (i * len + j) (fwc syms nb bs lv len i j) (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) =
  fwc syms nb bs lv len i (j + 1).
Proof.
  intros. unfold fwc.
  assert (Zlength (fw_u32s (sublist 0 i syms) nb bs lv len) = i * len)
    by (rewrite fw_u32s_len, Zlength_sublist by lia; lia).
  set (u := fw_u32s _ _ _ _ _) in *. clearbody u.
  list_solve.
Qed.

Local Open Scope logic.

(* one element of an array, borrowed *)
Lemma gen_borrow: forall {cs: compspecs} sh t N (l: list (reptype t)) p k v,
  naturally_aligned t -> 0 <= k < N -> Zlength l = N ->
  data_at sh (tarray t N) l p |--
  data_at sh t (Znth k l) (offset_val (sizeof t * k) p) *
  (data_at sh t v (offset_val (sizeof t * k) p) -* data_at sh (tarray t N) (upd_Znth k l v) p).
Proof.
  intros.
  assert_PROP (field_compatible (tarray t N) [] p) by entailer!.
  unfold tarray.
  rewrite (split3_data_at_Tarray sh t N k (k + 1) l l (sublist 0 k l) (sublist k (k + 1) l)
    (sublist (k + 1) N l) p); try (auto; lia); [| rewrite sublist_same; auto; lia].
  rewrite (split3_data_at_Tarray sh t N k (k + 1) (upd_Znth k l v) (upd_Znth k l v) (sublist 0 k l) [v]
    (sublist (k + 1) N l) p); try (auto; lia).
  2: rewrite Zlength_upd_Znth; lia.
  2: rewrite sublist_same; auto; rewrite Zlength_upd_Znth; lia.
  2: rewrite sublist_upd_Znth_l by lia; reflexivity.
  2: rewrite sublist_len_1 by (rewrite Zlength_upd_Znth; lia); rewrite upd_Znth_same by lia; reflexivity.
  2: rewrite sublist_upd_Znth_r by lia; reflexivity.
  rewrite sublist_len_1 by lia. replace (k + 1 - k) with 1 by lia.
  change (Tarray t 1 noattr) with (tarray t 1).
  rewrite !data_at_singleton_array_eq with (v := _) by reflexivity.
  replace (field_address0 (Tarray t N noattr) (SUB k) p) with (offset_val (sizeof t * k) p).
  2: { rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. }
  rewrite (sepcon_comm (data_at sh (Tarray t k noattr) _ _)). rewrite !sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite sepcon_assoc.
  apply sepcon_derives; [apply derives_refl |]. rewrite sepcon_comm. apply derives_refl.
Qed.

Lemma cell_borrow: forall {cs: compspecs} sh N (l: list val) p k v,
  0 <= k < N -> Zlength l = N ->
  data_at sh (tarray tuint N) l p |--
  data_at_ sh tuint (offset_val (4 * k) p) *
  (data_at sh tuint v (offset_val (4 * k) p) -* data_at sh (tarray tuint N) (upd_Znth k l v) p).
Proof.
  intros. sep_apply (gen_borrow sh tuint N l p k v); auto. simpl; auto.
  simpl sizeof. cancel.
Qed.

Lemma ssym_borrow: forall sh (ss: list val) ps k, 0 <= k < 256 -> Zlength ss = 256 ->
  data_at sh (tarray t_ssym 256) ss ps |--
  data_at sh t_ssym (Znth k ss) (offset_val k ps) *
  (data_at sh t_ssym (Znth k ss) (offset_val k ps) -* data_at sh (tarray t_ssym 256) ss ps).
Proof.
  intros. eapply derives_trans; [apply (@gen_borrow CompSpecs sh t_ssym 256 ss ps k (Znth k ss)) |]; auto.
  simpl; auto.
  rewrite upd_Znth_triv; [| change (0 <= k < Zlength ss); lia | reflexivity].
  change (sizeof t_ssym) with 1. rewrite Z.mul_1_l. apply derives_refl.
Qed.

(* pointer comparisons inside one array *)
Lemma arr_test_eq: forall {cs: compspecs} sh t n (l: reptype (tarray t n)) p x y (Q: mpred),
  readable_share sh -> 0 <= x <= sizeof (tarray t n) -> 0 <= y <= sizeof (tarray t n) ->
  0 < sizeof (tarray t n) ->
  data_at sh (tarray t n) l p * Q |-- denote_tc_test_eq (offset_val x p) (offset_val y p).
Proof.
  intros. assert_PROP (isptr p) by entailer!. destruct p; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. Opaque denote_tc_test_eq. simpl offset_val. unfold test_eq_ptrs. unfold sameblock.
  destruct (peq b b); [| congruence]. simpl.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    sep_apply (data_at_memory_block sh (tarray t n) l (Vptr b i));
    [ apply (memory_block_weak_valid_pointer sh _ (Vptr b i) x) | apply (memory_block_weak_valid_pointer sh _ (Vptr b i) y) ];
    auto; apply readable_nonidentity; auto.
Qed.

Lemma offset_val_inj: forall p x y, isptr p -> 0 <= x <= Ptrofs.max_unsigned -> 0 <= y <= Ptrofs.max_unsigned ->
  offset_val x p = offset_val y p -> x = y.
Proof.
  intros. destruct p; try contradiction. simpl in H2. inversion H2.
  assert (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr x)) i = Ptrofs.sub (Ptrofs.add i (Ptrofs.repr y)) i) by congruence.
  rewrite !Ptrofs.sub_add_l, Ptrofs.sub_idem, !Ptrofs.add_zero_l in H3.
  apply (f_equal Ptrofs.unsigned) in H3. rewrite !Ptrofs.unsigned_repr in H3 by lia. auto.
Qed.

Definition fw_locals (p ps: val) (e nb bs lv len: Z) (v1 v2 v3: val) : list localdef :=
  [temp _end (offset_val e ps); temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs));
   temp _level (Vint (Int.repr lv)); temp _length (Vint (Int.repr len));
   lvar _DElt2 tuint v1; lvar _DElt2__1 tuint v2; lvar _DElt2__2 tuint v3].

Definition fw_inv sh shs p ps ss b e syms nb bs lv len v1 v2 v3 : environ -> mpred :=
  EX i: Z, PROP (0 <= i <= e - b)
    LOCAL (temp _ptr (offset_val (b + i) ps); temp _DTableRank (offset_val (4 * (i * len)) p);
      temp _end (offset_val e ps); temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs));
      temp _level (Vint (Int.repr lv)); temp _length (Vint (Int.repr len));
      lvar _DElt2 tuint v1; lvar _DElt2__1 tuint v2; lvar _DElt2__2 tuint v3)
    SEP (data_at sh (tarray tuint ((e - b) * len)) (fwc syms nb bs lv len i 0) p;
      data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; data_at_ Tsh tuint v3).

Definition fw_cont sh shs p ps ss b e syms nb bs lv len v1 v2 v3 : environ -> mpred :=
  EX i: Z, PROP (0 <= i < e - b)
    LOCAL (temp _ptr (offset_val (b + i) ps); temp _DTableRank (offset_val (4 * ((i + 1) * len)) p);
      temp _end (offset_val e ps); temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs));
      temp _level (Vint (Int.repr lv)); temp _length (Vint (Int.repr len));
      lvar _DElt2 tuint v1; lvar _DElt2__1 tuint v2; lvar _DElt2__2 tuint v3)
    SEP (data_at sh (tarray tuint ((e - b) * len)) (fwc syms nb bs lv len (i + 1) 0) p;
      data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; data_at_ Tsh tuint v3).

Definition fw_post sh shs p ps ss (b e: Z) syms nb bs lv len (v1 v2 v3: val) : environ -> mpred :=
  PROP () LOCAL (lvar _DElt2 tuint v1; lvar _DElt2__1 tuint v2; lvar _DElt2__2 tuint v3)
    SEP (data_at sh (tarray tuint ((e - b) * len)) (fw_u32s syms nb bs lv len) p;
      data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v1; data_at_ Tsh tuint v2; data_at_ Tsh tuint v3).

Ltac fw_arg := entailer!; change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4 in *; simpl firstn; f_equal;
  simpl; rewrite ?offset_offset_val; f_equal; lia.

Ltac fw_side := lazymatch goal with
  | |- semax _ _ _ _ => idtac
  | |- (_ |-- !! _) => fw_arg
  | |- (_ |-- _) => idtac
  | |- _ => first [memcpy_side | simpl; rep_lia]
  end.

Lemma body_HUF_fillDTableX2ForWeight :
  semax_body Vprog G_X2 f_HUF_fillDTableX2ForWeight HUF_fillDTableX2ForWeight_spec.
Proof.
  start_function.
  assert (Hsyms: Zlength syms = e - b).
  { pose proof (f_equal (@Zlength val) H2) as Hz.
    rewrite Zlength_map, Zlength_sublist in Hz by lia. lia. }
  remember (2 ^ (L - nb)) as len eqn:Elen.
  assert (Hlen: 1 <= len <= 2048).
  { assert (0 <= L - nb <= 11) by (unfold HUF_TABLELOG_MAX in H5; lia).
    subst len. change 1 with (2 ^ 0). change 2048 with (2 ^ 11). split; apply Z.pow_le_mono_r; lia. }
  assert (Hshl: Int.shl (Int.repr 1) (Int.and (Int.sub (Int.repr L) (Int.repr nb)) (Int.repr 31)) =
    Int.repr len).
  { rewrite sub_repr. subst len. assert (0 <= L - nb <= 11) by (unfold HUF_TABLELOG_MAX in H5; lia).
    remember (L - nb) as k. clear - H8.
    assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/
      k = 11) by lia.
    repeat destruct H as [-> | H]; [..| subst k]; reflexivity. }
  forward.
  { entailer!. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
    assert (0 < 2 ^ 5) as H32 by lia. pose proof (Z.mod_pos_bound (L - nb) (2 ^ 5) H32).
    change (2 ^ 5) with 32 in *. rewrite Int.unsigned_repr by rep_lia.
    change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite Hshl.
  forward_if (PROP () LOCAL () SEP (data_at sh (tarray tuint ((e - b) * len)) (fw_u32s syms nb bs lv len) p;
    data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v_DElt2; data_at_ Tsh tuint v_DElt2__1;
    data_at_ Tsh tuint v_DElt2__2)).
  - (* case 1 *)
    forward_loop (fw_inv sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    continue: (fw_cont sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    break: (fw_post sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2).
    + forward. unfold fw_inv. Exists 0. rewrite fwc_init. entailer!.
      rewrite Hsyms, data_at__eq. apply derives_refl.
    + unfold fw_inv. Intros i.
      forward_if.
      { eapply derives_trans; [| apply (@arr_test_eq CompSpecs shs t_ssym 256 ss ps (b + i) e TT)]; auto.
        cancel. all: simpl; lia. }
      { assert (Hi: i < e - b) by (assert (i <> e - b) by (intro Hx; apply H9; f_equal; lia); lia).
        assert (Hsym: Znth (b + i) ss = Vint (Int.repr (Znth i syms))).
        { replace (b + i) with (i + b) by lia. rewrite <- (Znth_sublist b i e) by lia. rewrite H2, Znth_map by lia.
          reflexivity. }
        assert (Hsr: 0 <= Znth i syms < 256) by (rewrite Forall_Znth in H3; apply H3; lia).
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 0) p
          (i * 2 ^ (L - nb)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (sh, offset_val (4 * (i * 2 ^ (L - nb))) p, Znth i syms, nb, bs, lv).
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        sep_apply modus_ponens_wand.
        pose proof (fwc_step syms nb bs lv (2 ^ (L - nb)) i 0) as Hst. rewrite Z.add_0_r in Hst.
        rewrite Hst by (rewrite ?E; lia). clear Hst.
        forward.
        unfold fw_cont. Exists i. rewrite E in *. rewrite fwc_next by lia. entailer!.
        change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4. f_equal. lia.
      }
      { assert_PROP (isptr ps) by entailer!.
        assert (i = e - b) by (apply offset_val_inj in H9; auto; rep_lia). subst i.
        forward. unfold fw_post. rewrite <- Hsyms, fwc_final by lia. entailer!. }
    + unfold fw_cont. Intros i. forward. unfold fw_inv. Exists (i + 1). entailer!.
      change (sizeof (Tstruct ___gp_sortedSymbol_t noattr)) with 1. f_equal. lia.
    + forward. unfold fw_post. entailer!.
  - (* case 2 *)
    forward_loop (fw_inv sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    continue: (fw_cont sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    break: (fw_post sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2).
    + forward. unfold fw_inv. Exists 0. rewrite fwc_init. entailer!.
      rewrite Hsyms, data_at__eq. apply derives_refl.
    + unfold fw_inv. Intros i.
      forward_if.
      { eapply derives_trans; [| apply (@arr_test_eq CompSpecs shs t_ssym 256 ss ps (b + i) e TT)]; auto.
        cancel. all: simpl; lia. }
      { assert (Hi: i < e - b) by (assert (i <> e - b) by (intro Hx; apply H9; f_equal; lia); lia).
        assert (Hsym: Znth (b + i) ss = Vint (Int.repr (Znth i syms))).
        { replace (b + i) with (i + b) by lia. rewrite <- (Znth_sublist b i e) by lia. rewrite H2, Znth_map by lia.
          reflexivity. }
        assert (Hsr: 0 <= Znth i syms < 256) by (rewrite Forall_Znth in H3; apply H3; lia).
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 0) p
          (i * 2 ^ (L - nb) + 0) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (sh, offset_val (4 * (i * 2 ^ (L - nb) + 0)) p, Znth i syms, nb, bs, lv).
        { fw_arg. }
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        sep_apply modus_ponens_wand.
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 0) by (rewrite ?E; lia).
        change (0 + 1) with 1.
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 1) p
          (i * 2 ^ (L - nb) + 1) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (sh, offset_val (4 * (i * 2 ^ (L - nb) + 1)) p, Znth i syms, nb, bs, lv).
        { fw_arg. }
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        sep_apply modus_ponens_wand.
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 1) by (rewrite ?E; lia).
        change (1 + 1) with 2.
        forward.
        unfold fw_cont. Exists i. rewrite E in *. rewrite fwc_next by lia. entailer!.
        change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4. f_equal. lia.
      }
      { assert_PROP (isptr ps) by entailer!.
        assert (i = e - b) by (apply offset_val_inj in H9; auto; rep_lia). subst i.
        forward. unfold fw_post. rewrite <- Hsyms, fwc_final by lia. entailer!. }
    + unfold fw_cont. Intros i. forward. unfold fw_inv. Exists (i + 1). entailer!.
      change (sizeof (Tstruct ___gp_sortedSymbol_t noattr)) with 1. f_equal. lia.
    + forward. unfold fw_post. entailer!.
  - (* case 4 *)
    forward_loop (fw_inv sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    continue: (fw_cont sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    break: (fw_post sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2).
    + forward. unfold fw_inv. Exists 0. rewrite fwc_init. entailer!.
      rewrite Hsyms, data_at__eq. apply derives_refl.
    + unfold fw_inv. Intros i.
      forward_if.
      { eapply derives_trans; [| apply (@arr_test_eq CompSpecs shs t_ssym 256 ss ps (b + i) e TT)]; auto.
        cancel. all: simpl; lia. }
      { assert (Hi: i < e - b) by (assert (i <> e - b) by (intro Hx; apply H9; f_equal; lia); lia).
        assert (Hsym: Znth (b + i) ss = Vint (Int.repr (Znth i syms))).
        { replace (b + i) with (i + b) by lia. rewrite <- (Znth_sublist b i e) by lia. rewrite H2, Znth_map by lia.
          reflexivity. }
        assert (Hsr: 0 <= Znth i syms < 256) by (rewrite Forall_Znth in H3; apply H3; lia).
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        forward_call (Znth i syms, nb, bs, lv).
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        forward.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 0) p
          (i * 2 ^ (L - nb) + 0) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2, offset_val (4 * (i * 2 ^ (L - nb) + 0)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 0)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 0) by (rewrite ?E; lia).
        change (0 + 1) with 1.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 1) p
          (i * 2 ^ (L - nb) + 1) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2, offset_val (4 * (i * 2 ^ (L - nb) + 1)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 1)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 1) by (rewrite ?E; lia).
        change (1 + 1) with 2.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 2) p
          (i * 2 ^ (L - nb) + 2) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2, offset_val (4 * (i * 2 ^ (L - nb) + 2)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 2)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 2) by (rewrite ?E; lia).
        change (2 + 1) with 3.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 3) p
          (i * 2 ^ (L - nb) + 3) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2, offset_val (4 * (i * 2 ^ (L - nb) + 3)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 3)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 3) by (rewrite ?E; lia).
        change (3 + 1) with 4.
        forward.
        unfold fw_cont. Exists i. rewrite E in *. rewrite fwc_next by lia. entailer!.
        change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4. f_equal. lia.
      }
      { assert_PROP (isptr ps) by entailer!.
        assert (i = e - b) by (apply offset_val_inj in H9; auto; rep_lia). subst i.
        forward. unfold fw_post. rewrite <- Hsyms, fwc_final by lia. entailer!. }
    + unfold fw_cont. Intros i. forward. unfold fw_inv. Exists (i + 1). entailer!.
      change (sizeof (Tstruct ___gp_sortedSymbol_t noattr)) with 1. f_equal. lia.
    + forward. unfold fw_post. entailer!.
  - (* case 8 *)
    forward_loop (fw_inv sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    continue: (fw_cont sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2)
    break: (fw_post sh shs p ps ss b e syms nb bs lv (2 ^ (L - nb)) v_DElt2 v_DElt2__1 v_DElt2__2).
    + forward. unfold fw_inv. Exists 0. rewrite fwc_init. entailer!.
      rewrite Hsyms, data_at__eq. apply derives_refl.
    + unfold fw_inv. Intros i.
      forward_if.
      { eapply derives_trans; [| apply (@arr_test_eq CompSpecs shs t_ssym 256 ss ps (b + i) e TT)]; auto.
        cancel. all: simpl; lia. }
      { assert (Hi: i < e - b) by (assert (i <> e - b) by (intro Hx; apply H9; f_equal; lia); lia).
        assert (Hsym: Znth (b + i) ss = Vint (Int.repr (Znth i syms))).
        { replace (b + i) with (i + b) by lia. rewrite <- (Znth_sublist b i e) by lia. rewrite H2, Znth_map by lia.
          reflexivity. }
        assert (Hsr: 0 <= Znth i syms < 256) by (rewrite Forall_Znth in H3; apply H3; lia).
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        forward_call (Znth i syms, nb, bs, lv).
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        forward.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 0) p
          (i * 2 ^ (L - nb) + 0) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 0)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 0)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 0) by (rewrite ?E; lia).
        change (0 + 1) with 1.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 1) p
          (i * 2 ^ (L - nb) + 1) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 1)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 1)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 1) by (rewrite ?E; lia).
        change (1 + 1) with 2.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 2) p
          (i * 2 ^ (L - nb) + 2) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 2)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 2)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 2) by (rewrite ?E; lia).
        change (2 + 1) with 3.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 3) p
          (i * 2 ^ (L - nb) + 3) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 3)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 3)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 3) by (rewrite ?E; lia).
        change (3 + 1) with 4.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 4) p
          (i * 2 ^ (L - nb) + 4) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 4)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 4)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 4) by (rewrite ?E; lia).
        change (4 + 1) with 5.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 5) p
          (i * 2 ^ (L - nb) + 5) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 5)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 5)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 5) by (rewrite ?E; lia).
        change (5 + 1) with 6.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 6) p
          (i * 2 ^ (L - nb) + 6) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 6)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 6)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 6) by (rewrite ?E; lia).
        change (6 + 1) with 7.
        sep_apply (cell_borrow sh ((e - b) * 2 ^ (L - nb)) (fwc syms nb bs lv (2 ^ (L - nb)) i 7) p
          (i * 2 ^ (L - nb) + 7) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { rewrite E. lia. }
        { rewrite fwc_len; rewrite ?Hsyms; lia. }
        Intros.
        forward_call (Tsh, sh, v_DElt2__1, offset_val (4 * (i * 2 ^ (L - nb) + 7)) p,
          existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
        { fw_arg. }
        { memcpy_side. }
        simpl projT1; simpl projT2.
        sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * 2 ^ (L - nb) + 7)) p))).
        rewrite (fwc_step syms nb bs lv (2 ^ (L - nb)) i 7) by (rewrite ?E; lia).
        change (7 + 1) with 8.
        forward.
        unfold fw_cont. Exists i. rewrite E in *. rewrite fwc_next by lia. entailer!.
        change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4. f_equal. lia.
      }
      { assert_PROP (isptr ps) by entailer!.
        assert (i = e - b) by (apply offset_val_inj in H9; auto; rep_lia). subst i.
        forward. unfold fw_post. rewrite <- Hsyms, fwc_final by lia. entailer!. }
    + unfold fw_cont. Intros i. forward. unfold fw_inv. Exists (i + 1). entailer!.
      change (sizeof (Tstruct ___gp_sortedSymbol_t noattr)) with 1. f_equal. lia.
    + forward. unfold fw_post. entailer!.
  - (* default *)
    assert (Hl8: 16 <= len /\ len mod 8 = 0).
    { rewrite !Int.unsigned_repr in NE, NE0, NE1, NE2 by rep_lia.
      assert (0 <= L - nb <= 11) by (unfold HUF_TABLELOG_MAX in H5; lia). subst len.
      remember (L - nb) as k. clear - H8 NE NE0 NE1 NE2.
      assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/
        k = 11) by lia.
      repeat destruct H as [-> | H]; [..| subst k]; simpl in *; try lia.
      all: split; [vm_compute; intro Hc; discriminate | reflexivity]. }
    clear Elen.
    forward_loop (fw_inv sh shs p ps ss b e syms nb bs lv len v_DElt2 v_DElt2__1 v_DElt2__2)
    continue: (fw_cont sh shs p ps ss b e syms nb bs lv len v_DElt2 v_DElt2__1 v_DElt2__2)
    break: (fw_post sh shs p ps ss b e syms nb bs lv len v_DElt2 v_DElt2__1 v_DElt2__2).
    + forward. unfold fw_inv. Exists 0. rewrite fwc_init. entailer!.
      rewrite Hsyms, data_at__eq. apply derives_refl.
    + unfold fw_inv. Intros i.
      forward_if.
      { eapply derives_trans; [| apply (@arr_test_eq CompSpecs shs t_ssym 256 ss ps (b + i) e TT)]; auto.
        cancel. all: simpl; lia. }
      { assert (Hi: i < e - b) by (assert (i <> e - b) by (intro Hx; apply H9; f_equal; lia); lia).
        assert (Hsym: Znth (b + i) ss = Vint (Int.repr (Znth i syms))).
        { replace (b + i) with (i + b) by lia. rewrite <- (Znth_sublist b i e) by lia. rewrite H2, Znth_map by lia.
          reflexivity. }
        assert (Hsr: 0 <= Znth i syms < 256) by (rewrite Forall_Znth in H3; apply H3; lia).
        assert (Hil: i * len + len <= (e - b) * len) by nia.
        assert (Hnl: (e - b) * len <= 256 * 2048) by nia.
        sep_apply (ssym_borrow shs ss ps (b + i)); [lia | auto]. Intros.
        forward.
        { entailer!. rewrite Hsym. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        rewrite Hsym. sep_apply modus_ponens_wand.
        forward_call (Znth i syms, nb, bs, lv).
        { unfold HUF_TABLELOG_MAX in H5; rep_lia. }
        forward.
        forward.
        assert_PROP (isptr p) as Pp by entailer!.
        assert (HE: force_val (sem_binary_operation' Oadd (tptr (Tstruct ___gp_HUF_DEltX2 noattr)) tuint
          (offset_val (4 * (i * len)) p) (Vint (Int.repr len))) = offset_val (4 * (i * len + len)) p).
        { destruct p; try contradiction. simpl. unfold sem_add_ptr_int. simpl.
          f_equal. rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_intu, Ptrofs.of_int.
          rewrite Int.unsigned_repr by rep_lia. rewrite ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia. }
        rewrite HE. clear HE.
        forward_loop (EX m: Z, PROP (0 <= m <= len / 8)
          LOCAL (temp _DTableRankEnd (offset_val (4 * (i * len + len)) p);
          temp _DTableRank (offset_val (4 * (i * len + 8 * m)) p); temp _ptr (offset_val (b + i) ps); temp _end (offset_val e ps);
          temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs)); temp _level (Vint (Int.repr lv));
          temp _length (Vint (Int.repr len)); lvar _DElt2 tuint v_DElt2; lvar _DElt2__1 tuint v_DElt2__1;
          lvar _DElt2__2 tuint v_DElt2__2)
          SEP (data_at sh (tarray tuint ((e - b) * len)) (fwc syms nb bs lv len i (8 * m)) p; data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v_DElt2;
          data_at_ Tsh tuint v_DElt2__1; data_at Tsh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) v_DElt2__2))%assert
        continue: (EX m: Z, PROP (0 <= m < len / 8)
          LOCAL (temp _DTableRankEnd (offset_val (4 * (i * len + len)) p);
          temp _DTableRank (offset_val (4 * (i * len + 8 * m)) p); temp _ptr (offset_val (b + i) ps); temp _end (offset_val e ps);
          temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs)); temp _level (Vint (Int.repr lv));
          temp _length (Vint (Int.repr len)); lvar _DElt2 tuint v_DElt2; lvar _DElt2__1 tuint v_DElt2__1;
          lvar _DElt2__2 tuint v_DElt2__2)
          SEP (data_at sh (tarray tuint ((e - b) * len)) (fwc syms nb bs lv len i (8 * m + 8)) p; data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v_DElt2;
          data_at_ Tsh tuint v_DElt2__1; data_at Tsh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) v_DElt2__2))%assert
        break: (PROP ()
          LOCAL (temp _DTableRank (offset_val (4 * (i * len + len)) p); temp _ptr (offset_val (b + i) ps); temp _end (offset_val e ps);
          temp _nbBits (Vint (Int.repr nb)); temp _baseSeq (Vint (Int.repr bs)); temp _level (Vint (Int.repr lv));
          temp _length (Vint (Int.repr len)); lvar _DElt2 tuint v_DElt2; lvar _DElt2__1 tuint v_DElt2__1;
          lvar _DElt2__2 tuint v_DElt2__2)
          SEP (data_at sh (tarray tuint ((e - b) * len)) (fwc syms nb bs lv len i len) p; data_at shs (tarray t_ssym 256) ss ps; data_at_ Tsh tuint v_DElt2;
          data_at_ Tsh tuint v_DElt2__1; data_at Tsh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) v_DElt2__2)).
        { Exists 0. rewrite Z.mul_0_r, Z.add_0_r. entailer!. pose proof (Z.div_pos len 8). lia. }
        { Intros m.
          assert (Hq: (len = 8 * (len / 8))%Z) by (apply Z_div_exact_full_2; lia).
          forward_if.
          { eapply derives_trans; [| apply (@arr_test_eq CompSpecs sh tuint ((e - b) * len)
              (fwc syms nb bs lv len i (8 * m)) p (4 * (i * len + 8 * m)) (4 * (i * len + len)) TT)].
            cancel. all: try (apply writable_readable; auto). all: simpl sizeof; rewrite ?Z.max_r by nia; nia. }
          { assert (Hm: m < len / 8).
            { assert ((8 * m <> len)%Z) by (intro Hx; apply H11; f_equal; lia). lia. }
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m)) p
            (i * len + (8 * m)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m)) by nia.
          replace ((8 * m + 1)%Z) with ((8 * m + 1)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 1)) p
            (i * len + (8 * m + 1)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 1))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 1))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 1)) by nia.
          replace ((8 * m + 1 + 1)%Z) with ((8 * m + 2)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 2)) p
            (i * len + (8 * m + 2)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 2))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 2))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 2)) by nia.
          replace ((8 * m + 2 + 1)%Z) with ((8 * m + 3)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 3)) p
            (i * len + (8 * m + 3)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 3))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 3))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 3)) by nia.
          replace ((8 * m + 3 + 1)%Z) with ((8 * m + 4)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 4)) p
            (i * len + (8 * m + 4)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 4))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 4))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 4)) by nia.
          replace ((8 * m + 4 + 1)%Z) with ((8 * m + 5)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 5)) p
            (i * len + (8 * m + 5)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 5))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 5))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 5)) by nia.
          replace ((8 * m + 5 + 1)%Z) with ((8 * m + 6)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 6)) p
            (i * len + (8 * m + 6)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 6))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 6))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 6)) by nia.
          replace ((8 * m + 6 + 1)%Z) with ((8 * m + 7)%Z) by lia.
          sep_apply (cell_borrow sh ((e - b) * len) (fwc syms nb bs lv len i (8 * m + 7)) p
            (i * len + (8 * m + 7)) (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          { nia. }
          { rewrite fwc_len; rewrite ?Hsyms; nia. }
          Intros.
          forward_call (Tsh, sh, v_DElt2__2, offset_val (4 * (i * len + (8 * m + 7))) p,
            existT (fun t => reptype t) tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv)))).
          all: fw_side.
          simpl projT1; simpl projT2.
          sep_apply (modus_ponens_wand (data_at sh tuint (Vint (Int.repr (deltu (Znth i syms) nb bs lv))) (offset_val (4 * (i * len + (8 * m + 7))) p))).
          rewrite (fwc_step syms nb bs lv len i (8 * m + 7)) by nia.
          replace ((8 * m + 7 + 1)%Z) with ((8 * m + 8)%Z) by lia.
          Exists m. entailer!. }
          { assert (Hm: (8 * m = len)%Z).
            { assert (8 * m <= len) by lia. assert (0 <= i * len) by nia.
              apply offset_val_inj in H11; auto; rep_lia. }
            forward. rewrite Hm. entailer!. }
        }
        { Intros m. forward. Exists (m + 1). replace ((8 * (m + 1))%Z) with ((8 * m + 8)%Z) by lia. entailer!.
          { change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4. f_equal. lia. } }
        unfold fw_cont. Exists i. rewrite fwc_next by lia. entailer!.
        f_equal. lia.
      }
      { assert_PROP (isptr ps) by entailer!.
        assert (i = e - b) by (apply offset_val_inj in H9; auto; rep_lia). subst i.
        forward. unfold fw_post. rewrite <- Hsyms, fwc_final by lia. entailer!. }
    + unfold fw_cont. Intros i. forward. unfold fw_inv. Exists (i + 1). entailer!.
      change (sizeof (Tstruct ___gp_sortedSymbol_t noattr)) with 1. f_equal. lia.
    + forward. unfold fw_post. entailer!.
Qed.
