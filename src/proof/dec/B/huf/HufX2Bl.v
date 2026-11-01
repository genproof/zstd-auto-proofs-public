(* X2T body: HUF_fillDTableX2Level2.  The model facts are hypotheses
   (proved in HufX2M.v). *)
Require Import Zstd.proof.dec.B.huf.HufX2S.
Local Open Scope logic.

(* ---------- model facts used by the body ---------- *)

Lemma bl_mw : forall ht L n1, x2_count -> x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  minbits ht <= n1 <= L - minbits ht ->
  1 <= Z.max 1 (n1 + ht_log ht + 1 - L) <= maxw ht /\ maxw ht <= ht_log ht /\ 1 <= ht_log ht <= 12.
Proof.
  intros ht L n1 XC Hok HL Hn1.
  destruct (xc_maxw XC ht Hok) as [[Hm1 Hm2] _].
  destruct Hok as [[HT _] _]. unfold HUF_TABLELOG_MAX in *. unfold minbits in *. lia.
Qed.

Lemma bl_cntw_nonneg : forall ht w, 0 <= cntw ht w.
Proof. intros. unfold cntw. apply Zlength_nonneg. Qed.

Lemma bl_rstart_mono : forall ht w k, x2_count -> x2_ht_ok ht -> 1 <= w -> 0 <= k ->
  0 <= rstart ht w <= rstart ht (w + k).
Proof.
  intros ht w k XC Hok Hw Hk.
  assert (H0: forall w, 1 <= w -> 0 <= rstart ht w).
  { intros w' Hw'. pattern w'. apply Zlt_lower_bound_ind with (z := 1); [| lia].
    intros x IH Hx. destruct (Z.eq_dec x 1) as [->|Hne].
    - destruct (xc_rstart XC ht 1 Hok ltac:(lia)) as [-> _]. lia.
    - destruct (xc_rstart XC ht (x - 1) Hok ltac:(lia)) as [_ [Hs _]].
      replace (x - 1 + 1) with x in Hs by lia. rewrite Hs.
      pose proof (bl_cntw_nonneg ht (x - 1)). specialize (IH (x - 1) ltac:(lia)). lia. }
  split; [apply H0; lia|].
  pattern k. apply natlike_ind; [rewrite Z.add_0_r; lia| |lia].
  intros x Hx IH. destruct (xc_rstart XC ht (w + x) Hok ltac:(lia)) as [_ [Hs _]].
  replace (w + Z.succ x) with (w + x + 1) by lia. rewrite Hs.
  pose proof (bl_cntw_nonneg ht (w + x)). lia.
Qed.

Lemma bl_rstart_bound : forall ht w, x2_count -> x2_ht_ok ht -> 1 <= w <= maxw ht + 1 ->
  0 <= rstart ht w <= rstart ht (maxw ht + 1) /\ rstart ht (maxw ht + 1) <= 256 /\
  rstart ht (maxw ht + 1) = Zlength (sorted_syms ht).
Proof.
  intros ht w XC Hok Hw.
  pose proof (bl_rstart_mono ht w (maxw ht + 1 - w) XC Hok ltac:(lia) ltac:(lia)).
  replace (w + (maxw ht + 1 - w)) with (maxw ht + 1) in H by lia.
  destruct (xc_rstart XC ht 1 Hok ltac:(lia)) as [_ [_ [Hl Hc]]].
  pose proof (bl_cntw_nonneg ht 0). destruct Hok as [_ [Hz _]]. lia.
Qed.

Lemma bl_ss_sub : forall ht ss w, x2_count -> x2_ht_ok ht -> x2_ss_ok ht ss -> 1 <= w <= maxw ht ->
  sublist (rstart ht w) (rstart ht (w + 1)) ss = map (fun s => Vint (Int.repr s)) (symsw ht w).
Proof.
  intros ht ss w XC Hok [Hss Hz] Hw.
  destruct (xc_symsw XC ht w Hok Hw) as [Hlen [_ Hsub]].
  destruct (bl_rstart_bound ht w XC Hok ltac:(lia)) as [Hb1 [Hb2 Hb3]].
  destruct (bl_rstart_bound ht (w + 1) XC Hok ltac:(lia)) as [Hc1 _].
  destruct (xc_rstart XC ht w Hok ltac:(lia)) as [_ [Hs _]].
  pose proof (bl_cntw_nonneg ht w).
  rewrite <- Hsub.
  apply Znth_eq_ext.
  - rewrite Zlength_map, !Zlength_sublist; lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_map by (rewrite Zlength_sublist; lia).
    rewrite !Znth_sublist by lia. apply Hz. lia.
Qed.

Lemma bl_rv0_mono : forall ht L w k, x2_layout -> x2_ht_ok ht -> ht_log ht <= L -> 1 <= w -> 0 <= k ->
  0 <= rv0 ht L w <= rv0 ht L (w + k).
Proof.
  intros ht L w k XL Hok HL Hw Hk.
  assert (Hstep: forall x, 1 <= x -> rv0 ht L x <= rv0 ht L (x + 1)).
  { intros x Hx. destruct (xl_rv0 XL ht L x Hok HL Hx) as [_ [Hs _]]. rewrite Hs.
    pose proof (bl_cntw_nonneg ht x). pose proof (Z.pow_nonneg 2 (L - nbw ht x) ltac:(lia)). nia. }
  assert (Hm: forall x j, 1 <= x -> 0 <= j -> rv0 ht L x <= rv0 ht L (x + j)).
  { intros x j Hx Hj. pattern j. apply natlike_ind; [rewrite Z.add_0_r; lia| |lia].
    intros y Hy IH. replace (x + Z.succ y) with (x + y + 1) by lia. specialize (Hstep (x + y) ltac:(lia)). lia. }
  split.
  - destruct (xl_rv0 XL ht L 1 Hok HL ltac:(lia)) as [H1 _]. specialize (Hm 1 (w - 1) ltac:(lia) ltac:(lia)).
    replace (1 + (w - 1)) with w in Hm by lia. lia.
  - apply Hm; lia.
Qed.

Lemma bl_lvl2_len : forall ht L s1 n1, 0 <= L - n1 -> Zlength (lvl2_u32s ht L s1 n1) = 2 ^ (L - n1).
Proof.
  intros. unfold lvl2_u32s. rewrite Zlength_map, Zlength_correct, seq_length.
  rewrite Z2Nat.id; auto. apply Z.pow_nonneg; lia.
Qed.

Lemma bl_end : forall ht L n1, x2_layout -> x2_ht_ok ht -> ht_log ht <= L -> 0 <= n1 <= L ->
  rv0 ht L (maxw ht + 1) / 2 ^ n1 = 2 ^ (L - n1).
Proof.
  intros ht L n1 XL Hok HL Hn.
  destruct (xl_rv0 XL ht L 1 Hok HL ltac:(lia)) as [_ [_ ->]].
  replace L with ((L - n1) + n1) at 1 by lia. rewrite Z.pow_add_r by lia.
  apply Z.div_mul. pose proof (Z.pow_pos_nonneg 2 n1). lia.
Qed.

Lemma bl_prefix_upd : forall (al: list val) d n j, Zlength al = n -> 0 <= j < n ->
  sublist 0 j al = Zrepeat d j ->
  Zlength (upd_Znth j al d) = n /\ sublist 0 (j + 1) (upd_Znth j al d) = Zrepeat d (j + 1).
Proof.
  intros al d n j Hl Hj Hp. split.
  - rewrite upd_Znth_Zlength; lia.
  - rewrite (sublist_split 0 j (j + 1)) by (rewrite ?upd_Znth_Zlength; lia).
    rewrite sublist_upd_Znth_l by lia. rewrite Hp.
    rewrite sublist_len_1 by (rewrite upd_Znth_Zlength; lia). rewrite upd_Znth_same by lia.
    change [d] with (Zrepeat d 1). rewrite <- Zrepeat_app by lia. reflexivity.
Qed.

(* ---------- one cell / one segment of the U32 table ---------- *)

Lemma bl_cell_open : forall sh n (al: list val) p j, field_compatible (tarray tuint n) nil p -> 0 <= j < n ->
  data_at sh (tarray tuint n) al p |--
  data_at_ sh tuint (offset_val (4 * j) p) * SingletonHole.array_with_hole sh tuint j n al p.
Proof.
  intros. sep_apply (SingletonHole.array_with_hole_intro sh tuint j n al p H0).
  rewrite arr_field_address by auto. simpl sizeof. cancel. all: try apply data_at_data_at_.
Qed.

Lemma bl_cell_close : forall sh n (al: list val) p j v, field_compatible (tarray tuint n) nil p -> 0 <= j < n ->
  data_at sh tuint v (offset_val (4 * j) p) * SingletonHole.array_with_hole sh tuint j n al p |--
  data_at sh (tarray tuint n) (upd_Znth j al v) p.
Proof.
  intros. replace (offset_val (4 * j) p) with (field_address (tarray tuint n) (SUB j) p)
    by (rewrite arr_field_address by auto; reflexivity).
  apply SingletonHole.array_with_hole_elim.
Qed.

Lemma bl_seg_open : forall sh n (al: list val) p lo hi, field_compatible (tarray tuint n) nil p ->
  0 <= lo <= hi -> hi <= n ->
  data_at sh (tarray tuint n) al p |--
  data_at_ sh (tarray tuint (hi - lo)) (offset_val (4 * lo) p) * SegmentHole.array_with_hole sh tuint lo hi n al p.
Proof.
  intros. sep_apply (SegmentHole.array_with_hole_intro sh tuint lo hi n al p H0 H1).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. cancel. all: try apply data_at_data_at_.
Qed.

Lemma bl_seg_close : forall sh n (al: list val) p lo hi v, field_compatible (tarray tuint n) nil p ->
  0 <= lo <= hi -> hi <= n ->
  data_at sh (tarray tuint (hi - lo)) v (offset_val (4 * lo) p) * SegmentHole.array_with_hole sh tuint lo hi n al p |--
  data_at sh (tarray tuint n) (splice_into_list lo hi v al) p.
Proof.
  intros. replace (offset_val (4 * lo) p) with (field_address0 (tarray tuint n) (SUB lo) p)
    by (rewrite arr_field_address0 by (auto; lia); reflexivity).
  apply SegmentHole.array_with_hole_elim.
Qed.

Lemma bl_splice : forall (al lv v: list val) n a a', Zlength al = n -> Zlength lv = n -> 0 <= a <= a' -> a' <= n ->
  sublist 0 a al = sublist 0 a lv -> v = sublist a a' lv ->
  Zlength (splice_into_list a a' v al) = n /\ sublist 0 a' (splice_into_list a a' v al) = sublist 0 a' lv.
Proof.
  intros al lv v n a a' Hal Hlv Ha Ha' Hp ->. unfold splice_into_list. rewrite Hal.
  split.
  - rewrite !Zlength_app, !Zlength_sublist by lia. lia.
  - rewrite Hp, app_assoc, sublist_rejoin by lia.
    rewrite sublist0_app1 by (rewrite Zlength_sublist; lia).
    apply sublist_same; [lia | rewrite Zlength_sublist; lia].
Qed.

Lemma bl_land31 : forall k, 0 <= k < 32 -> Z.land k 31 = k.
Proof.
  intros k Hk. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia.
Qed.

Lemma bl_len_shl : forall k, 0 <= k < 32 ->
  Int.shl (Int.repr 1) (Int.and (Int.repr k) (Int.repr 31)) = Int.repr (2 ^ k).
Proof.
  intros k Hk.
  assert (Ha: Int.and (Int.repr k) (Int.repr 31) = Int.repr k).
  { unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. change 31 with (Z.ones 5).
    rewrite Z.land_ones by lia. rewrite Z.mod_small; auto. }
  rewrite Ha, Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  rewrite two_p_correct, Int.mul_commut, Int.mul_one. reflexivity.
Qed.

Definition bl_upd8 (al: list val) (d: val) (i: Z) : list val :=
  upd_Znth (i + 6 + 1) (upd_Znth (i + 6) (upd_Znth (i + 4 + 1) (upd_Znth (i + 4)
    (upd_Znth (i + 2 + 1) (upd_Znth (i + 2) (upd_Znth (i + 0 + 1) (upd_Znth (i + 0) al d) d) d) d) d) d) d) d.

Lemma bl_upd8_ok : forall (al: list val) d n i, Zlength al = n -> 0 <= i -> i + 8 <= n ->
  sublist 0 i al = Zrepeat d i ->
  Zlength (bl_upd8 al d i) = n /\ sublist 0 (i + 8) (bl_upd8 al d i) = Zrepeat d (i + 8).
Proof.
  intros al d n i Hl Hi Hn Hp. unfold bl_upd8. split; list_solve.
Qed.

(* one 4-byte memcpy of the local DElt2 (value d) into cell j of the table p (n U32 cells, contents al) *)
Ltac bl_side p :=
  match goal with
  | |- semax _ _ _ _ => fail 1
  | |- ENTAIL _, _ |-- !! _ =>
      entailer!; change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4;
      match goal with |- context [offset_val ?a p] => match goal with |- context [offset_val ?b p] =>
        assert (a = b)%Z as ->; [lia | reflexivity] end end
  | |- _ |-- _ => simpl projT1; cancel
  | |- _ => memcpy_side
  end.

Ltac bl_cpy sh p v d FC n j :=
  match goal with |- context [data_at sh (tarray tuint n) ?al p] =>
  sep_apply (bl_cell_open sh n al p j FC ltac:(lia));
  forward_call (Tsh, sh, v, offset_val (4 * j) p, existT (fun t => reptype t) tuint d);
  try bl_side p;
  simpl projT1; simpl projT2; sep_apply (bl_cell_close sh n al p j d FC ltac:(lia))
  end.

Lemma body_HUF_fillDTableX2Level2 : x2_count -> x2_layout -> x2_fill ->
  semax_body Vprog G_X2 f_HUF_fillDTableX2Level2 HUF_fillDTableX2Level2_spec.
Proof.
  intros XC XL XF.
  start_function.
  destruct (bl_mw ht L n1 XC H H0 H1) as [Hmw [HmT HT]].
  assert (Hmb: 1 <= minbits ht) by (unfold minbits; lia).
  assert (Hlen: 2 <= 2 ^ (L - n1) <= 4096).
  { split.
    - change 2 with (2 ^ 1). apply Z.pow_le_mono_r; lia.
    - change 4096 with (2 ^ 12). apply Z.pow_le_mono_r; unfold HUF_TABLELOG_MAX in *; lia. }
  pose proof (bl_lvl2_len ht L s1 n1 ltac:(lia)) as Hlv.
  remember (2 ^ (L - n1)) as len eqn:Hlen_eq.
  remember (Z.max 1 (n1 + ht_log ht + 1 - L)) as mw eqn:Hmw_eq.
  remember (lvl2_u32s ht L s1 n1) as lv eqn:Hlv_eq.
  assert_PROP (field_compatible (tarray tuint len) nil p) as FC by entailer!.
  set (a0 := rv0 ht L mw / 2 ^ n1).
  rewrite data_at__tarray. simpl default_val.
  forward_if (PROP () LOCAL (lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
     temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
     temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
     temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
   SEP (data_at_ Tsh tuint v_DElt2;
        EX al: list val, !! (Zlength al = len /\ sublist 0 a0 al = sublist 0 a0 lv) &&
          data_at sh (tarray tuint len) al p;
        data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
        data_at shw (tarray tuint 15) rs prs)).
  - forward.
    { entailer!. rewrite bl_land31 by lia. rewrite Int.unsigned_repr by rep_lia.
      change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite sub_repr, bl_len_shl, <- Hlen_eq by lia.
    forward_call (s1, n1, 0, 1).
    { unfold HUF_TABLELOG_MAX in *; rep_lia. }
    forward.
    destruct H3 as [Hrl Hrow].
    assert (Hsk: @Znth val Vundef mw row = Vint (Int.repr a0)) by (apply Hrow; lia).
    forward.
    { entailer!. rewrite Hsk. exact I. }
    rewrite Hsk.
    destruct (xf_skip XF ht L s1 n1 H H0 H1 ltac:(lia)) as [Ha0 Hpre].
    rewrite <- Hmw_eq in Ha0, Hpre. rewrite <- Hlen_eq in Ha0. rewrite <- Hlv_eq in Hpre. fold a0 in Ha0, Hpre.
    set (d := Vint (Int.repr (deltu s1 n1 0 1))).
    forward_switch'.
    + bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) 0.
      bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) 1.
      forward.
      Exists (upd_Znth 1 (upd_Znth 0 (Zrepeat Vundef (2 ^ (L - n1))) d) d).
      entailer!.
      clearbody a0. rewrite Hpre. rewrite E in *. change (repeat ?x (Z.to_nat a0)) with (Zrepeat x a0). list_solve.
    + bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) 0.
      bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) (0 + 1).
      bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) 2.
      bl_cpy sh p v_DElt2 d FC (2 ^ (L - n1)) (2 + 1).
      forward.
      Exists (upd_Znth (2 + 1) (upd_Znth 2 (upd_Znth (0 + 1) (upd_Znth 0 (Zrepeat Vundef (2 ^ (L - n1))) d) d) d) d).
      entailer!.
      clearbody a0. rewrite Hpre. rewrite E in *. change (repeat ?x (Z.to_nat a0)) with (Zrepeat x a0). list_solve.
    + assert (Hl3: len <> 2 /\ len <> 4).
      { rewrite !Int.unsigned_repr in NE, NE0 by rep_lia. lia. }
      assert (Hl8: exists q, len = (8 * q)%Z).
      { exists (2 ^ (L - n1 - 3)). rewrite Hlen_eq.
        assert (L - n1 <> 1 /\ L - n1 <> 2) as [? ?].
        { split; intro X; rewrite Hlen_eq, X in Hl3; simpl in Hl3; lia. }
        replace (L - n1) with (3 + (L - n1 - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
      destruct Hl8 as [q Hq].
      forward_loop (EX m: Z, EX al: list val,
        PROP (0 <= m; (8 * m)%Z <= len; Zlength al = len; sublist 0 (8 * m)%Z al = Zrepeat d (8 * m)%Z)
        LOCAL (temp _i (Vint (Int.repr (8 * m)%Z)); temp _skipSize (Vint (Int.repr a0)); temp _t'1 d; temp _length (Vint (Int.repr len));
           lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
           temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
           temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
           temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
        SEP (data_at Tsh tuint d v_DElt2; data_at sh (tarray tuint len) al p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert
      continue: (EX m: Z, EX al: list val,
        PROP (0 <= m; (8 * m + 8)%Z <= len; Zlength al = len; sublist 0 (8 * m + 8)%Z al = Zrepeat d (8 * m + 8)%Z)
        LOCAL (temp _i (Vint (Int.repr (8 * m)%Z)); temp _skipSize (Vint (Int.repr a0)); temp _t'1 d; temp _length (Vint (Int.repr len));
           lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
           temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
           temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
           temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
        SEP (data_at Tsh tuint d v_DElt2; data_at sh (tarray tuint len) al p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert
      break: (EX m: Z, EX al: list val,
        PROP (a0 <= (8 * m)%Z <= len; Zlength al = len; sublist 0 (8 * m)%Z al = Zrepeat d (8 * m)%Z)
        LOCAL (temp _i (Vint (Int.repr (8 * m)%Z)); temp _skipSize (Vint (Int.repr a0)); temp _t'1 d; temp _length (Vint (Int.repr len));
           lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
           temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
           temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
           temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
        SEP (data_at Tsh tuint d v_DElt2; data_at sh (tarray tuint len) al p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert.
      * forward. Exists 0 (Zrepeat Vundef len). entailer!.
      * Intros m al.
        forward_if.
        -- assert (Hm8: (8 * m + 8)%Z <= len) by lia.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 0)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 0 + 1)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 2)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 2 + 1)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 4)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 4 + 1)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 6)%Z.
           bl_cpy sh p v_DElt2 d FC len (8 * m + 6 + 1)%Z.
           destruct (bl_upd8_ok al d len (8 * m)%Z ltac:(assumption) ltac:(lia) ltac:(lia) ltac:(assumption))
             as [Hu1 Hu2].
           Exists m (bl_upd8 al d (8 * m)%Z). unfold bl_upd8 in Hu1, Hu2 |- *. entailer!.
        -- forward. Exists m al. entailer!.
      * Intros m al. forward. Exists (m + 1) al. entailer!.
        replace (8 * (m + 1))%Z with (8 * m + 8)%Z by lia. auto.
      * Intros m al. forward.
        Exists al. entailer!.
        clearbody a0. rewrite Hpre. change (repeat ?x (Z.to_nat a0)) with (Zrepeat x a0).
        rewrite <- (sublist_sublist00 a0 (8 * m)%Z) by lia. match goal with H: sublist 0 (8 * m)%Z al = _ |- _ => rewrite H end.
        list_solve.
  - assert (Ea0: a0 = 0).
    { unfold a0. replace mw with 1 by lia. destruct (xl_rv0 XL ht L 1 H ltac:(lia) ltac:(lia)) as [-> _].
      reflexivity. }
    clearbody a0. subst a0.
    forward. Exists (Zrepeat Vundef len). entailer!.
  - Intros al.
    destruct H3 as [Hrl Hrow]. destruct H5 as [Hrsl Hrs].
    pose proof (bl_end ht L n1 XL H ltac:(lia) ltac:(lia)) as Hend. rewrite <- Hlen_eq in Hend.
    forward_loop (EX w: Z, EX al: list val,
        PROP (mw <= w <= maxw ht + 1; Zlength al = len;
              sublist 0 (rv0 ht L w / 2 ^ n1) al = sublist 0 (rv0 ht L w / 2 ^ n1) lv)
        LOCAL (temp _w (Vint (Int.repr w)); lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
           temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
           temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
           temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
        SEP (data_at_ Tsh tuint v_DElt2; data_at sh (tarray tuint len) al p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert
      continue: (EX w: Z, EX al: list val,
        PROP (mw <= w <= maxw ht; Zlength al = len;
              sublist 0 (rv0 ht L (w + 1) / 2 ^ n1) al = sublist 0 (rv0 ht L (w + 1) / 2 ^ n1) lv)
        LOCAL (temp _w (Vint (Int.repr w)); lvar _DElt2 tuint v_DElt2; temp _DTable p; temp _targetLog (Vint (Int.repr L));
           temp _consumedBits (Vint (Int.repr n1)); temp _rankVal prow; temp _minWeight (Vint (Int.repr mw));
           temp _maxWeight1 (Vint (Int.repr (maxw ht + 1))); temp _sortedSymbols ps; temp _rankStart prs;
           temp _nbBitsBaseline (Vint (Int.repr (ht_log ht + 1))); temp _baseSeq (Vint (Int.repr s1)))
        SEP (data_at_ Tsh tuint v_DElt2; data_at sh (tarray tuint len) al p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert
      break: (PROP () LOCAL (lvar _DElt2 tuint v_DElt2) SEP (data_at_ Tsh tuint v_DElt2; data_at sh (tarray tuint len) lv p;
           data_at shw (tarray tuint 13) row prow; data_at shw (tarray t_ssym 256) ss ps;
           data_at shw (tarray tuint 15) rs prs))%assert.
    + forward. Exists mw al. entailer!.
    + Intros w al1.
      forward_if.
      * assert (Hw: mw <= w <= maxw ht) by lia.
        destruct (xf_weight XF ht L s1 n1 w H H0 H1 ltac:(lia)) as [Hnb [Hrec Hfw]].
        rewrite <- Hlv_eq in Hfw.
        set (lo := rv0 ht L w / 2 ^ n1) in *. set (hi := rv0 ht L (w + 1) / 2 ^ n1) in *.
        assert (Hlohi: 0 <= lo <= hi /\ hi <= len).
        { pose proof (Z.pow_pos_nonneg 2 n1 ltac:(lia)).
          pose proof (Z.pow_nonneg 2 (L - n1 - nbw ht w) ltac:(lia)).
          pose proof (bl_cntw_nonneg ht w).
          destruct (bl_rv0_mono ht L w 0 XL H ltac:(lia) ltac:(lia) ltac:(lia)) as [Hr0 _].
          destruct (bl_rv0_mono ht L (w + 1) (maxw ht - w) XL H ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Hr1].
          replace (w + 1 + (maxw ht - w)) with (maxw ht + 1) in Hr1 by lia.
          split; [split|].
          - apply Z.div_pos; lia.
          - nia.
          - rewrite <- Hend. unfold hi. apply Z.div_le_mono; lia. }
        destruct (xc_rstart XC ht w H ltac:(lia)) as [_ [Hrs1 _]].
        destruct (bl_rstart_bound ht w XC H ltac:(lia)) as [Hb1 [Hb2 _]].
        destruct (bl_rstart_bound ht (w + 1) XC H ltac:(lia)) as [Hb3 _].
        pose proof (bl_ss_sub ht ss w XC H H4 ltac:(lia)) as Hss.
        destruct (xc_symsw XC ht w H ltac:(lia)) as [Hsl [Hsr _]].
        assert (Hb: @Znth val Vundef w rs = Vint (Int.repr (rstart ht w))) by (apply Hrs; lia).
        assert (He: @Znth val Vundef (w + 1) rs = Vint (Int.repr (rstart ht (w + 1)))) by (apply Hrs; lia).
        assert (Hr: @Znth val Vundef w row = Vint (Int.repr lo)) by (apply Hrow; lia).
        forward.
        { entailer!. rewrite Hb. exact I. }
        rewrite Hb.
        forward.
        { entailer!. rewrite He. exact I. }
        rewrite He.
        forward. forward.
        forward.
        { entailer!. rewrite Hr. exact I. }
        rewrite Hr.
        rewrite sub_repr, add_repr.
        replace (ht_log ht + 1 - w + n1) with (n1 + nbw ht w) by (unfold nbw; lia).
        sep_apply (bl_seg_open sh len al1 p lo hi FC ltac:(lia) ltac:(lia)).
        replace (hi - lo) with ((rstart ht (w + 1) - rstart ht w) * 2 ^ (L - (n1 + nbw ht w)))%Z
          by (rewrite Hrec, Hrs1; replace (L - (n1 + nbw ht w)) with (L - n1 - nbw ht w) by lia; lia).
        forward_call (sh, offset_val (4 * lo) p, shw, ps, ss, rstart ht w, rstart ht (w + 1), symsw ht w,
                      n1 + nbw ht w, L, s1, 2).
        { entailer!. change (sizeof (Tstruct ___gp_HUF_DEltX2 noattr)) with 4.
          pose proof (field_compatible_isptr _ _ _ FC) as Pp.
          pose proof (field_compatible_isptr _ _ _ H16) as Pps.
          destruct p; try contradiction; destruct ps; try contradiction. simpl.
          rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia). reflexivity. }
        { cancel. }
        { split; [apply (proj1 H4) | unfold nbw in *; lia]. }
        rewrite Z.sub_add_distr.
        replace ((rstart ht (w + 1) - rstart ht w) * 2 ^ (L - n1 - nbw ht w))%Z with (hi - lo)
          by (rewrite Hrec, Hrs1; ring).
        rewrite <- Hfw.
        sep_apply (bl_seg_close sh len al1 p lo hi (sublist lo hi lv) FC ltac:(lia) ltac:(lia)).
        destruct (bl_splice al1 lv (sublist lo hi lv) len lo hi H5 Hlv ltac:(lia) ltac:(lia) H8 eq_refl)
          as [Hs1 Hs2].
        Exists w (splice_into_list lo hi (sublist lo hi lv) al1). entailer!.
      * forward. entailer!.
        assert (w = maxw ht + 1) as -> by lia.
        rewrite Hend in *. rewrite !sublist_same in * by lia. subst. cancel.
    + Intros w al1. forward. Exists (w + 1) al1. entailer!.
    + unfold abbreviate in POSTCONDITION; subst POSTCONDITION. simpl_ret_assert. entailer!.
Qed.
