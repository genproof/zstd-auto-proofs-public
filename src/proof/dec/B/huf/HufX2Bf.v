(* X2T body: HUF_fillDTableX2.  The model facts are hypotheses
   (proved in HufX2M.v). *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Local Open Scope logic.

(* ---------- arrays: three pieces, and borrowing a region of the table ---------- *)

Lemma bf_arr3 sh t n j len (A B C: list (reptype t)) p :
  naturally_aligned t -> field_compatible (tarray t n) nil p ->
  0 <= j -> 0 <= len -> j + len <= n -> Zlength A = j -> Zlength B = len -> Zlength C = n - (j + len) ->
  data_at sh (tarray t n) (A ++ B ++ C) p =
  data_at sh (tarray t j) A p * data_at sh (tarray t len) B (offset_val (sizeof t * j) p) *
  data_at sh (tarray t (n - (j + len))) C (offset_val (sizeof t * (j + len)) p).
Proof.
  intros NA FC ? ? ? ? ? ?.
  unfold tarray.
  rewrite (split3_data_at_Tarray sh t n j (j + len) (A ++ B ++ C) (A ++ B ++ C) A B C); auto;
    [ | lia | autorewrite with sublist; lia | | | | ].
  all: try (rewrite sublist_same; auto; autorewrite with sublist; lia).
  2,3,4: subst j; autorewrite with sublist; auto.
  rewrite !field_address0_offset by (apply arr_field_compatible0; auto; lia).
  simpl nested_field_offset. rewrite !Z.add_0_l. replace (j + len - j) with len by lia. auto.
Qed.

Lemma bf_borrow sh n j len (X: list val) p :
  0 <= j -> 0 <= len -> j + len <= n -> Zlength X = n ->
  data_at sh (tarray tuint n) (sublist 0 j X ++ Zrepeat Vundef (n - j)) p |--
  data_at_ sh (tarray tuint len) (offset_val (4 * j) p) *
  (data_at sh (tarray tuint len) (sublist j (j + len) X) (offset_val (4 * j) p) -*
   data_at sh (tarray tuint n) (sublist 0 (j + len) X ++ Zrepeat Vundef (n - (j + len))) p).
Proof.
  intros.
  assert_PROP (field_compatible (tarray tuint n) nil p) as FC by entailer!.
  replace (sublist 0 j X ++ Zrepeat Vundef (n - j))
    with (sublist 0 j X ++ Zrepeat Vundef len ++ Zrepeat Vundef (n - (j + len))).
  2: { f_equal; unfold Zrepeat; rewrite <- repeat_app, <- Z2Nat.inj_add by lia; f_equal; f_equal; lia. }
  rewrite (bf_arr3 sh tuint n j len); auto; try reflexivity.
  all: try (autorewrite with sublist; lia).
  2: { hnf. intros. simpl. auto. }
  rewrite data_at__eq.
  change (default_val (tarray tuint len)) with (Zrepeat Vundef len).
  simpl sizeof.
  apply derives_trans with (data_at sh (tarray tuint len) (Zrepeat Vundef len) (offset_val (4 * j) p) *
    (data_at sh (tarray tuint j) (sublist 0 j X) p *
     data_at sh (tarray tuint (n - (j + len))) (Zrepeat Vundef (n - (j + len))) (offset_val (4 * (j + len)) p)));
    [cancel|].
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint.
  replace (sublist 0 (j + len) X ++ Zrepeat Vundef (n - (j + len)))
    with (sublist 0 j X ++ sublist j (j + len) X ++ Zrepeat Vundef (n - (j + len)))
    by (rewrite app_assoc; f_equal; rewrite sublist_rejoin; auto; lia).
  rewrite (bf_arr3 sh tuint n j len); auto; try reflexivity.
  all: try (autorewrite with sublist; lia).
  2: { hnf. intros. simpl. auto. }
  simpl sizeof. cancel.
Qed.

(* a row of the 12 x 13 rankVal array *)
Lemma bf_row sh (rv: list (list val)) prv c :
  0 <= c < 12 -> Zlength rv = 12 ->
  data_at sh (tarray (tarray tuint 13) 12) rv prv |--
  data_at sh (tarray tuint 13) (Znth c rv) (offset_val (52 * c) prv) *
  (data_at sh (tarray tuint 13) (Znth c rv) (offset_val (52 * c) prv) -*
   data_at sh (tarray (tarray tuint 13) 12) rv prv).
Proof.
  intros.
  assert_PROP (field_compatible (tarray (tarray tuint 13) 12) nil prv) as FC by entailer!.
  replace (data_at sh (tarray (tarray tuint 13) 12) rv prv) with
    (data_at sh (tarray (tarray tuint 13) 12) (sublist 0 c rv ++ [Znth c rv] ++ sublist (c + 1) 12 rv) prv).
  2: { f_equal. rewrite <- sublist_len_1 by lia. rewrite !sublist_rejoin by lia. apply sublist_same; lia. }
  rewrite (bf_arr3 sh (tarray tuint 13) 12 c 1); auto; try reflexivity.
  all: try (autorewrite with sublist; lia).
  2: { hnf. intros. simpl. auto. }
  rewrite (data_at_singleton_array_eq sh (tarray tuint 13) (Znth c rv) [Znth c rv]) by reflexivity.
  simpl sizeof.
  apply derives_trans with (data_at sh (tarray tuint 13) (Znth c rv) (offset_val (52 * c) prv) *
    (data_at sh (tarray (tarray tuint 13) c) (sublist 0 c rv) prv *
     data_at sh (tarray (tarray tuint 13) (12 - (c + 1))) (sublist (c + 1) 12 rv) (offset_val (52 * (c + 1)) prv)));
    [cancel|].
  apply sepcon_derives; [apply derives_refl|].
  rewrite <- wand_sepcon_adjoint. cancel.
Qed.

(* ---------- model arithmetic ---------- *)

Lemma bf_cnt_nonneg ht w : 0 <= cntw ht w.
Proof. unfold cntw. apply Zlength_nonneg. Qed.

Lemma bf_rv0_mono (XL: x2_layout) ht L w w' : x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= w' ->
  rv0 ht L w <= rv0 ht L w'.
Proof.
  intros Hok HL Hw.
  replace w' with (w + (w' - w)) by lia.
  assert (Hd: 0 <= w' - w) by lia. revert Hd. generalize (w' - w). intros d Hd.
  pattern d; apply natlike_ind; [rewrite Z.add_0_r; lia| |exact Hd].
  intros x Hx IH. replace (w + Z.succ x) with ((w + x) + 1) by lia.
  destruct (xl_rv0 XL ht L (w + x) Hok HL ltac:(lia)) as [_ [E _]]. rewrite E.
  pose proof (bf_cnt_nonneg ht (w + x)).
  assert (0 <= 2 ^ (L - nbw ht (w + x))) by (apply Z.pow_nonneg; lia).
  nia.
Qed.

Lemma bf_rstart_mono (XC: x2_count) ht w w' : x2_ht_ok ht -> 1 <= w <= w' ->
  rstart ht w <= rstart ht w'.
Proof.
  intros Hok Hw.
  replace w' with (w + (w' - w)) by lia.
  assert (Hd: 0 <= w' - w) by lia. revert Hd. generalize (w' - w). intros d Hd.
  pattern d; apply natlike_ind; [rewrite Z.add_0_r; lia| |exact Hd].
  intros x Hx IH. replace (w + Z.succ x) with ((w + x) + 1) by lia.
  destruct (xc_rstart XC ht (w + x) Hok ltac:(lia)) as [_ [E _]]. rewrite E.
  pose proof (bf_cnt_nonneg ht (w + x)). lia.
Qed.

Lemma bf_len (ht: huf_table) L : 0 <= L -> Zlength (x2_u32s ht L) = 2 ^ L.
Proof.
  intros. unfold x2_u32s. rewrite Zlength_map, Zlength_correct, seq_length.
  apply Z2Nat.id. apply Z.pow_nonneg; lia.
Qed.

Lemma bf_row0 sh (rv: list (list val)) prv :
  isptr prv -> Zlength rv = 12 ->
  data_at sh (tarray (tarray tuint 13) 12) rv prv |--
  data_at sh (tarray tuint 13) (Znth 0 rv) prv *
  (data_at sh (tarray tuint 13) (Znth 0 rv) prv -* data_at sh (tarray (tarray tuint 13) 12) rv prv).
Proof.
  intros. pose proof (bf_row sh rv prv 0 ltac:(lia) H0) as E.
  change (52 * 0) with 0 in E. rewrite isptr_offset_val_zero in E by auto. exact E.
Qed.

(* the sorted symbols of weight w in sortedSymbol *)
Lemma bf_ss_sub (XC: x2_count) ht ss w : x2_ht_ok ht -> x2_ss_ok ht ss -> 1 <= w <= maxw ht ->
  sublist (rstart ht w) (rstart ht (w + 1)) ss = map (fun s => Vint (Int.repr s)) (symsw ht w).
Proof.
  intros Hok [Hss_len Hss] Hw.
  destruct (xc_symsw XC ht w Hok Hw) as [_ [_ Esub]].
  destruct (xc_rstart XC ht w Hok ltac:(lia)) as [_ [Ers _]].
  destruct (xc_rstart XC ht 1 Hok ltac:(lia)) as [Ers1 [_ [Ess_len Ers_end]]].
  pose proof (bf_rstart_mono XC ht 1 w Hok ltac:(lia)).
  pose proof (bf_rstart_mono XC ht (w + 1) (maxw ht + 1) Hok ltac:(lia)).
  pose proof (bf_cnt_nonneg ht w). pose proof (bf_cnt_nonneg ht 0).
  assert (Zlength (ht_weights ht) <= 256) by (destruct Hok as [_ [? _]]; lia).
  rewrite <- Esub.
  apply Znth_eq_ext.
  { rewrite Zlength_map, !Zlength_sublist by lia. lia. }
  intros i Hi. rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_map by (rewrite Zlength_sublist by lia; lia).
  rewrite !Znth_sublist by lia.
  apply Hss. lia.
Qed.

Lemma bf_shl k : 0 <= k <= 12 -> Int.shl (Int.repr 1) (Int.and (Int.repr k) (Int.repr 31)) = Int.repr (2 ^ k).
Proof.
  intros.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/
          k = 11 \/ k = 12) as Hk by lia.
  repeat destruct Hk as [Hk|Hk]; subst; reflexivity.
Qed.

Lemma body_HUF_fillDTableX2 : x2_count -> x2_layout -> x2_fill ->
  semax_body Vprog G_X2 f_HUF_fillDTableX2 HUF_fillDTableX2_spec.
Proof.
  intros XC XL XF.
  start_function.
  destruct (xc_maxw XC ht H) as [Hmw [Hcpos [Hc0 _]]].
  unfold HUF_TABLELOG_MAX in H0.
  assert (HL0: 0 <= L) by lia.
  pose proof (bf_len ht L HL0) as Hlen.
  assert (H2L: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
  assert_PROP (isptr prv) as Pprv by entailer!.
  assert_PROP (isptr p /\ isptr ps) as Pp by entailer!. destruct Pp as [Pp Pps].
  forward. forward. forward. forward.
  rewrite add_repr, !sub_repr.
  destruct (xl_rv0 XL ht L 1 H ltac:(lia) ltac:(lia)) as [Erv1 [_ Erv_end]].
  forward_for_simple_bound (maxw ht + 1) (EX w: Z,
    PROP ()
    LOCAL (temp _wEnd (Vint (Int.repr (maxw ht + 1))); temp _minBits (Vint (Int.repr (ht_log ht + 1 - maxw ht)));
           temp _scaleLog (Vint (Int.repr (ht_log ht + 1 - L))); temp _rankVal prv; temp _DTable p;
           temp _targetLog (Vint (Int.repr L)); temp _sortedList ps; temp _rankStart prs;
           temp _rankValOrigin prv; temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))))
    SEP (data_at sh (tarray tuint (2 ^ L))
           (sublist 0 (rv0 ht L w) (x2_u32s ht L) ++ Zrepeat Vundef (2 ^ L - rv0 ht L w)) p;
         data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs;
         data_at shw (tarray (tarray tuint 13) 12) rv prv))%assert.
  { (* entry *)
    rewrite Erv1, sublist_nil, app_nil_l, Z.sub_0_r.
    destruct prv; try contradiction. simpl force_val.
    entailer!.
  }
  2: { (* exit *)
    rewrite Erv_end, Z.sub_diag, sublist_same by lia. simpl Zrepeat. rewrite app_nil_r.
    entailer!. }
  (* the body, weight w = i *)
  rename i into w.
  destruct (xc_rstart XC ht w H ltac:(lia)) as [_ [Ers _]].
  destruct (xc_rstart XC ht 1 H ltac:(lia)) as [Ers1 [_ [Ess_len Ers_end]]].
  destruct (xl_rv0 XL ht L w H ltac:(lia) ltac:(lia)) as [_ [Erv _]].
  pose proof (bf_rstart_mono XC ht 1 w H ltac:(lia)) as Hrs_lo.
  pose proof (bf_rstart_mono XC ht (w + 1) (maxw ht + 1) H ltac:(lia)) as Hrs_hi.
  pose proof (bf_rv0_mono XL ht L 1 w H ltac:(lia) ltac:(lia)) as Hrv_lo.
  pose proof (bf_rv0_mono XL ht L (w + 1) (maxw ht + 1) H ltac:(lia) ltac:(lia)) as Hrv_hi.
  pose proof (bf_cnt_nonneg ht w) as Hcw. pose proof (bf_cnt_nonneg ht 0) as Hc0w.
  assert (Hnw: Zlength (ht_weights ht) <= 256) by (destruct H as [_ [? _]]; lia).
  assert (Hpw: 0 < 2 ^ (L - nbw ht w)) by (apply Z.pow_pos_nonneg; unfold nbw; lia).
  destruct H2 as [Hrs_len Hrs].
  forward.
  { entailer!. rewrite Hrs by lia. auto. }
  rewrite Hrs by lia.
  forward.
  forward.
  { entailer!. rewrite Hrs by lia. auto. }
  rewrite Hrs by lia.
  forward.
  forward.
  rewrite sub_repr.
  destruct H3 as [Hrv_len [Hrv_rows Hrv]].
  pose proof (Hrv 0 ltac:(auto)) as [_ Hrow0].
  assert (Enbw: ht_log ht + 1 - w = nbw ht w) by reflexivity.
  forward_if.
  - (* room for a second symbol *)
    assert (Hn1: minbits ht <= nbw ht w <= L - minbits ht) by (unfold minbits, nbw in *; lia).
    sep_apply (bf_row0 shw rv prv Pprv Hrv_len). Intros.
    forward.
    { entailer!. rewrite Hrow0 by lia. auto. }
    rewrite Hrow0 by lia. rewrite Z.pow_0_r, Z.div_1_r.
    sep_apply (wand_frame_elim (data_at shw (tarray tuint 13) (Znth 0 rv) prv)).
    forward.
    { entailer!. change 31 with (Z.ones 5). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (L - (ht_log ht + 1 - w)) (2 ^ 5) ltac:(lia)).
      rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32.
      change (2 ^ 5) with 32 in *. lia. }
    rewrite sub_repr, Enbw, bf_shl by (unfold nbw; lia).
    forward.
    rewrite add_repr.
    forward_if (PROP ()
      LOCAL (temp _minWeight (Vint (Int.repr (Z.max 1 (nbw ht w + ht_log ht + 1 - L))));
             temp _length (Vint (Int.repr (2 ^ (L - nbw ht w)))); temp _start (Vint (Int.repr (rv0 ht L w)));
             temp _nbBits (Vint (Int.repr (nbw ht w))); temp _end (Vint (Int.repr (rstart ht (w + 1))));
             temp _begin (Vint (Int.repr (rstart ht w))); temp _w (Vint (Int.repr w));
             temp _wEnd (Vint (Int.repr (maxw ht + 1)));
             temp _minBits (Vint (Int.repr (ht_log ht + 1 - maxw ht)));
             temp _scaleLog (Vint (Int.repr (ht_log ht + 1 - L))); temp _rankVal prv; temp _DTable p;
             temp _targetLog (Vint (Int.repr L)); temp _sortedList ps; temp _rankStart prs;
             temp _rankValOrigin prv; temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))))
      SEP (data_at sh (tarray tuint (2 ^ L))
             (sublist 0 (rv0 ht L w) (x2_u32s ht L) ++ Zrepeat Vundef (2 ^ L - rv0 ht L w)) p;
           data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs;
           data_at shw (tarray (tarray tuint 13) 12) rv prv)).
    { forward. entailer!. rewrite Z.max_l by (unfold nbw in *; lia). auto. }
    { forward. entailer!. rewrite Z.max_r by (unfold nbw in *; lia). f_equal. f_equal. lia. }
    forward_loop (EX k: Z,
      PROP (0 <= k <= cntw ht w)
      LOCAL (temp _s (Vint (Int.repr (rstart ht w + k)));
             temp _start (Vint (Int.repr (rv0 ht L w + k * 2 ^ (L - nbw ht w))));
             temp _minWeight (Vint (Int.repr (Z.max 1 (nbw ht w + ht_log ht + 1 - L))));
             temp _length (Vint (Int.repr (2 ^ (L - nbw ht w))));
             temp _nbBits (Vint (Int.repr (nbw ht w))); temp _end (Vint (Int.repr (rstart ht (w + 1))));
             temp _w (Vint (Int.repr w));
             temp _wEnd (Vint (Int.repr (maxw ht + 1)));
             temp _minBits (Vint (Int.repr (ht_log ht + 1 - maxw ht)));
             temp _scaleLog (Vint (Int.repr (ht_log ht + 1 - L))); temp _rankVal prv; temp _DTable p;
             temp _targetLog (Vint (Int.repr L)); temp _sortedList ps; temp _rankStart prs;
             temp _rankValOrigin prv; temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))))
      SEP (data_at sh (tarray tuint (2 ^ L))
             (sublist 0 (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (x2_u32s ht L) ++ Zrepeat Vundef (2 ^ L - (rv0 ht L w + k * 2 ^ (L - nbw ht w)))) p;
           data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs;
           data_at shw (tarray (tarray tuint 13) 12) rv prv))%assert
    continue: (EX k: Z,
      PROP (0 <= k < cntw ht w)
      LOCAL (temp _s (Vint (Int.repr (rstart ht w + k)));
             temp _start (Vint (Int.repr (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w))));
             temp _minWeight (Vint (Int.repr (Z.max 1 (nbw ht w + ht_log ht + 1 - L))));
             temp _length (Vint (Int.repr (2 ^ (L - nbw ht w))));
             temp _nbBits (Vint (Int.repr (nbw ht w))); temp _end (Vint (Int.repr (rstart ht (w + 1))));
             temp _w (Vint (Int.repr w));
             temp _wEnd (Vint (Int.repr (maxw ht + 1)));
             temp _minBits (Vint (Int.repr (ht_log ht + 1 - maxw ht)));
             temp _scaleLog (Vint (Int.repr (ht_log ht + 1 - L))); temp _rankVal prv; temp _DTable p;
             temp _targetLog (Vint (Int.repr L)); temp _sortedList ps; temp _rankStart prs;
             temp _rankValOrigin prv; temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))))
      SEP (data_at sh (tarray tuint (2 ^ L))
             (sublist 0 (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) (x2_u32s ht L) ++ Zrepeat Vundef (2 ^ L - (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)))) p;
           data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs;
           data_at shw (tarray (tarray tuint 13) 12) rv prv))%assert
    break: (PROP ()
      LOCAL (temp _w (Vint (Int.repr w)); temp _wEnd (Vint (Int.repr (maxw ht + 1)));
             temp _minBits (Vint (Int.repr (ht_log ht + 1 - maxw ht)));
             temp _scaleLog (Vint (Int.repr (ht_log ht + 1 - L))); temp _rankVal prv; temp _DTable p;
             temp _targetLog (Vint (Int.repr L)); temp _sortedList ps; temp _rankStart prs;
             temp _rankValOrigin prv; temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))))
      SEP (data_at sh (tarray tuint (2 ^ L))
             (sublist 0 (rv0 ht L (w + 1)) (x2_u32s ht L) ++ Zrepeat Vundef (2 ^ L - (rv0 ht L (w + 1)))) p;
           data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs;
           data_at shw (tarray (tarray tuint 13) 12) rv prv)).
    { forward. Exists 0. rewrite Z.mul_0_l, !Z.add_0_r. entailer!. }
    { Intros k. forward_if.
      { assert (Hk: k < cntw ht w) by lia.
        destruct (xc_symsw XC ht w H ltac:(lia)) as [Hsl [Hsr _]].
        assert (Esym: Znth (rstart ht w + k) ss = Vint (Int.repr (Znth k (symsw ht w)))).
        { pose proof (bf_ss_sub XC ht ss w H H1 ltac:(lia)) as Esub.
          assert (E: Znth k (sublist (rstart ht w) (rstart ht (w + 1)) ss) =
                     Znth k (map (fun s => Vint (Int.repr s)) (symsw ht w))) by (rewrite Esub; auto).
          rewrite Znth_sublist in E by lia. rewrite Znth_map in E by lia.
          rewrite <- E. f_equal. lia. }
        assert (Hs1: 0 <= Znth k (symsw ht w) < 256).
        { rewrite Forall_forall in Hsr. apply Hsr. apply Znth_In. lia. }
        forward.
        { entailer!. match goal with |- context [@Znth ?A ?d (rstart ht w + k) ss] =>
            replace (@Znth A d (rstart ht w + k) ss) with (Vint (Int.repr (Znth k (symsw ht w))))
              by (rewrite <- Esym; reflexivity) end.
          simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        match goal with |- context [@Znth ?A ?d (rstart ht w + k) ss] =>
          replace (@Znth A d (rstart ht w + k) ss) with (Vint (Int.repr (Znth k (symsw ht w))))
            by (rewrite <- Esym; reflexivity) end.
        sep_apply (bf_borrow sh (2 ^ L) (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (2 ^ (L - nbw ht w))
          (x2_u32s ht L) p ltac:(nia) ltac:(lia) ltac:(nia) Hlen). Intros.
        sep_apply (bf_row shw rv prv (nbw ht w) ltac:(unfold minbits in Hn1; lia) Hrv_len). Intros.
        pose proof (Hrv (nbw ht w) (or_intror Hn1)) as Hrow.
        forward_call (sh, offset_val (4 * (rv0 ht L w + k * 2 ^ (L - nbw ht w))) p, shw, ht, L, nbw ht w,
          Znth k (symsw ht w), offset_val (52 * nbw ht w) prv, Znth (nbw ht w) rv, ps, ss, prs, rs).
        { entailer!. destruct p; try contradiction. destruct prv; try contradiction. simpl.
          assert (Hj: 0 <= rv0 ht L w + k * 2 ^ (L - nbw ht w) <= 4096) by nia.
          unfold Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int.
          rewrite Int.signed_repr by rep_lia. rewrite Int.unsigned_repr by (unfold nbw in *; rep_lia).
          rewrite !ptrofs_mul_repr, zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
          reflexivity. }
        { exact (conj Hrs_len Hrs). }
        replace (rv0 ht L w + k * 2 ^ (L - nbw ht w) + 2 ^ (L - nbw ht w))
          with (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) by ring.
        rewrite <- (xf_double XF ht L w k H ltac:(unfold HUF_TABLELOG_MAX; lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        sep_apply (wand_frame_elim (data_at shw (tarray tuint 13) (Znth (nbw ht w) rv)
          (offset_val (52 * nbw ht w) prv))).
        sep_apply (wand_frame_elim (data_at sh (tarray tuint (2 ^ (L - nbw ht w)))
          (sublist (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) (x2_u32s ht L))
          (offset_val (4 * (rv0 ht L w + k * 2 ^ (L - nbw ht w))) p))).
        forward.
        Exists k. rewrite add_repr.
        replace (rv0 ht L w + k * 2 ^ (L - nbw ht w) + 2 ^ (L - nbw ht w))
          with (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) by ring.
        entailer!. }
      { forward. entailer!.
        replace (rv0 ht L w + k * 2 ^ (L - nbw ht w)) with (rv0 ht L (w + 1))
          by (rewrite Erv; replace k with (cntw ht w) by lia; ring).
        apply derives_refl. } }
    { Intros k. forward. Exists (k + 1). rewrite add_repr, <- Z.add_assoc. entailer!. }
    unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.

  - (* a single symbol *)
    sep_apply (bf_row0 shw rv prv Pprv Hrv_len). Intros.
    forward.
    { entailer!. rewrite Hrow0 by lia. auto. }
    rewrite Hrow0 by lia. rewrite Z.pow_0_r, Z.div_1_r.
    sep_apply (wand_frame_elim (data_at shw (tarray tuint 13) (Znth 0 rv) prv)).
    sep_apply (bf_borrow sh (2 ^ L) (rv0 ht L w) ((rstart ht (w + 1) - rstart ht w) * 2 ^ (L - nbw ht w))
      (x2_u32s ht L) p ltac:(lia) ltac:(nia) ltac:(nia) Hlen). Intros.
    rewrite Enbw.
    forward_call (sh, offset_val (4 * rv0 ht L w) p, shw, ps, ss, rstart ht w, rstart ht (w + 1), symsw ht w,
      nbw ht w, L, 0, 1).
    { pose proof (bf_ss_sub XC ht ss w H H1 ltac:(lia)) as Esub. destruct H1 as [Hss_len _].
      destruct (xc_symsw XC ht w H ltac:(lia)) as [_ [Hsr _]].
      repeat split; auto; unfold HUF_TABLELOG_MAX; lia. }
    replace (rv0 ht L w + (rstart ht (w + 1) - rstart ht w) * 2 ^ (L - nbw ht w)) with (rv0 ht L (w + 1))
      by (rewrite Erv, Ers; ring).
    rewrite (xf_single XF ht L w H ltac:(unfold HUF_TABLELOG_MAX; lia) ltac:(lia) ltac:(unfold minbits; lia)).
    sep_apply (wand_frame_elim (data_at sh (tarray tuint ((rstart ht (w + 1) - rstart ht w) * 2 ^ (L - nbw ht w)))
      (fw_u32s (symsw ht w) (nbw ht w) 0 1 (2 ^ (L - nbw ht w))) (offset_val (4 * rv0 ht L w) p))).
    entailer!.
Qed.
