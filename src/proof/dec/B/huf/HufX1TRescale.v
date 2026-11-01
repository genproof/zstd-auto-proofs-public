(* Sub-group X1T: the body of HUF_rescaleStats. *)
Require Export Zstd.proof.dec.B.huf.HufX1TSpecs.
Local Open Scope logic.

(* ---------- the counts of the rescaled weights ---------- *)

Definition rs_cnt (k: Z) (ws: list Z) : Z := Zlength (filter (fun x => x =? k) ws).

Definition rs_upto13 : list Z := map Z.of_nat (seq 0 13).

Lemma rs_Zlength_upto13 : Zlength rs_upto13 = 13.
Proof. reflexivity. Qed.

Lemma rs_Znth_upto13 (k: Z) : 0 <= k < 13 -> Znth k rs_upto13 = k.
Proof.
  intros.
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
          k = 10 \/ k = 11 \/ k = 12) by lia.
  repeat (destruct H0 as [-> | H0]; [reflexivity | ]); subst; reflexivity.
Qed.

Lemma rs_rank_stats (ws: list Z) :
  rank_stats ws = map (fun z => Vint (Int.repr z)) (map (fun k => rs_cnt k ws) rs_upto13).
Proof.
  unfold rank_stats, rs_upto13, rs_cnt. rewrite !map_map. reflexivity.
Qed.

Lemma rs_cnt_above (ws: list Z) (tl k: Z) :
  Forall (fun w => 0 <= w <= tl) ws -> tl < k -> rs_cnt k ws = 0.
Proof.
  intros H Hk. unfold rs_cnt. induction H as [ | w ws Hw H IH]; [reflexivity | ].
  simpl. destruct (Z.eqb_spec w k); [lia | exact IH].
Qed.

Lemma rs_cnt_map (f g: Z -> bool) (h: Z -> Z) (ws: list Z) :
  Forall (fun w => f (h w) = g w) ws -> Zlength (filter f (map h ws)) = Zlength (filter g ws).
Proof.
  intros H. induction H as [ | w ws Hw H IH]; [reflexivity | ].
  simpl. rewrite Hw. destruct (g w); rewrite ?Zlength_cons, IH; reflexivity.
Qed.

Lemma rs_cnt_false (ws: list Z) : Zlength (filter (fun _ => false) ws) = 0.
Proof. induction ws; [reflexivity | exact IHws]. Qed.

Lemma rs_cnt_rescale (ws: list Z) (tl tg k: Z) :
  Forall (fun w => 0 <= w <= tl) ws -> tl < tg ->
  rs_cnt k (x1_rescale_ws ws tl tg) =
    if k =? 0 then rs_cnt 0 ws else if k <=? tg - tl then 0 else rs_cnt (k - (tg - tl)) ws.
Proof.
  intros H Hlt. unfold rs_cnt, x1_rescale_ws.
  destruct (Z.eqb_spec k 0); [ | destruct (Z.leb_spec k (tg - tl))].
  - subst k. apply rs_cnt_map. eapply Forall_impl; [ | exact H]. intros w Hw. simpl in Hw |- *.
    destruct (Z.eqb_spec w 0); [subst; reflexivity | ].
    destruct (Z.eqb_spec (w + (tg - tl)) 0); [lia | reflexivity].
  - transitivity (Zlength (filter (fun _ : Z => false) ws)); [ | apply rs_cnt_false]. apply rs_cnt_map. eapply Forall_impl; [ | exact H]. intros w Hw. simpl in Hw |- *.
    destruct (Z.eqb_spec w 0); [subst; destruct (Z.eqb_spec 0 k); [lia | reflexivity] | ].
    destruct (Z.eqb_spec (w + (tg - tl)) k); [lia | reflexivity].
  - apply rs_cnt_map. eapply Forall_impl; [ | exact H]. intros w Hw. simpl in Hw |- *.
    destruct (Z.eqb_spec w 0).
    + subst. destruct (Z.eqb_spec 0 k); [lia | ]. destruct (Z.eqb_spec 0 (k - (tg - tl))); [lia | reflexivity].
    + destruct (Z.eqb_spec (w + (tg - tl)) k), (Z.eqb_spec w (k - (tg - tl))); try lia; reflexivity.
Qed.

Lemma rs_rescale_id (ws: list Z) (tl: Z) : x1_rescale_ws ws tl tl = ws.
Proof.
  unfold x1_rescale_ws. induction ws as [ | w ws IH]; [reflexivity | ].
  simpl. rewrite IH. destruct (Z.eqb_spec w 0); [subst; reflexivity | f_equal; lia].
Qed.

(* the rankVal array during the two shift loops: indices (s2, sc] zeroed, (s1, tg] shifted down by sc *)
Definition rs_rv (oz: list Z) (sc tg s1 s2: Z) (k: Z) : Z :=
  if andb (s2 <? k) (k <=? sc) then 0
  else if andb (s1 <? k) (k <=? tg) then Znth (k - sc) oz else Znth k oz.

Lemma rs_upd (f g: Z -> Z) (s: Z) :
  0 <= s < 13 -> (forall k, 0 <= k < 13 -> k <> s -> f k = g k) ->
  upd_Znth s (map (fun z => Vint (Int.repr z)) (map f rs_upto13)) (Vint (Int.repr (g s))) =
  map (fun z => Vint (Int.repr z)) (map g rs_upto13).
Proof.
  intros Hs Hfg.
  apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_map. reflexivity.
  - intros i Hi. rewrite Zlength_upd_Znth, !Zlength_map, rs_Zlength_upto13 in Hi.
    destruct (Z.eq_dec i s).
    + subst. rewrite upd_Znth_same by (rewrite !Zlength_map, rs_Zlength_upto13; lia).
      rewrite !Znth_map by (rewrite ?Zlength_map, rs_Zlength_upto13; lia).
      rewrite rs_Znth_upto13 by lia. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_map, ?rs_Zlength_upto13; lia).
      rewrite !Znth_map by (rewrite ?Zlength_map, rs_Zlength_upto13; lia).
      rewrite rs_Znth_upto13 by lia. rewrite Hfg by lia. reflexivity.
Qed.

Lemma rs_Znth_rv (f: Z -> Z) (k: Z) (d: val) :
  0 <= k < 13 -> @Znth val d k (map (fun z => Vint (Int.repr z)) (map f rs_upto13)) = Vint (Int.repr (f k)).
Proof.
  intros. rewrite !Znth_map by (rewrite ?Zlength_map, rs_Zlength_upto13; lia).
  rewrite rs_Znth_upto13 by lia. reflexivity.
Qed.

Lemma rs_init (oz: list Z) (sc tg: Z) :
  Zlength oz = 13 -> map (rs_rv oz sc tg tg sc) rs_upto13 = oz.
Proof.
  intros Hz. apply Znth_eq_ext; [rewrite Zlength_map, Hz; reflexivity | ].
  intros i Hi. rewrite Zlength_map, rs_Zlength_upto13 in Hi.
  rewrite Znth_map by (rewrite rs_Zlength_upto13; lia). rewrite rs_Znth_upto13 by lia.
  unfold rs_rv. destruct (Z.ltb_spec sc i), (Z.leb_spec i sc), (Z.ltb_spec tg i), (Z.leb_spec i tg);
    cbn [andb]; try lia; reflexivity.
Qed.

Lemma rs_rank_final (ws: list Z) (tl tg: Z) :
  Forall (fun w => 0 <= w <= tl) ws -> 1 <= tl -> tl < tg -> tg <= 12 ->
  map (rs_rv (map (fun k => rs_cnt k ws) rs_upto13) (tg - tl) tg (tg - tl) 0) rs_upto13 =
  map (fun k => rs_cnt k (x1_rescale_ws ws tl tg)) rs_upto13.
Proof.
  intros Hw H1 Hlt Htg.
  apply Znth_eq_ext; [rewrite !Zlength_map; reflexivity | ].
  intros i Hi. rewrite !Zlength_map, rs_Zlength_upto13 in Hi.
  rewrite !Znth_map by (rewrite rs_Zlength_upto13; lia).
  rewrite rs_Znth_upto13 by lia.
  rewrite rs_cnt_rescale by assumption.
  unfold rs_rv.
  destruct (Z.ltb_spec 0 i), (Z.leb_spec i (tg - tl)), (Z.eqb_spec i 0), (Z.ltb_spec (tg - tl) i),
    (Z.leb_spec i tg); cbn [andb]; try lia;
    rewrite ?Znth_map by (rewrite rs_Zlength_upto13; lia); rewrite ?rs_Znth_upto13 by lia;
    try reflexivity; subst; try reflexivity.
  rewrite !(rs_cnt_above ws tl) by (assumption || lia). reflexivity.
Qed.

Lemma rs_ze (a b: Z) :
  0 <= a -> 0 <= b -> a + b < 256 ->
  Int.zero_ext 8 (Int.add (Int.repr a) (Int.zero_ext 8 (Int.repr b))) = Int.repr (a + b).
Proof.
  intros.
  assert (E: forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x).
  { intros x Hx. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. }
  rewrite E by lia. rewrite add_repr. apply E; lia.
Qed.

Lemma rs_step1 (ws: list Z) (wr: list val) (tl tg i: Z) :
  0 <= i < Zlength ws ->
  upd_Znth i (zbytes (x1_rescale_ws (sublist 0 i ws) tl tg ++ sublist i (Zlength ws) ws) ++ wr)
    (Vint (Int.repr (if Znth i ws =? 0 then 0 else Znth i ws + (tg - tl)))) =
  zbytes (x1_rescale_ws (sublist 0 (i + 1) ws) tl tg ++ sublist (i + 1) (Zlength ws) ws) ++ wr.
Proof.
  intros Hi. unfold x1_rescale_ws.
  rewrite (sublist_split 0 i (i + 1) ws) by lia. rewrite sublist_len_1 by lia.
  rewrite (sublist_split i (i + 1) (Zlength ws) ws) by lia. rewrite sublist_len_1 by lia.
  rewrite !map_app. simpl map. rewrite <- !app_assoc.
  list_solve.
Qed.

Lemma body_HUF_rescaleStats : semax_body Vprog nil f_HUF_rescaleStats HUF_rescaleStats_spec.
Proof.
  start_function.
  assert (HTM: HUF_TABLELOG_MAX = 12) by reflexivity. rewrite HTM in *.
  assert (Hn: Zlength ws <= 256) by (pose proof (Zlength_nonneg wr); lia).
  forward_if.
  { rewrite ?Int.unsigned_repr in H3 by rep_lia. forward. rewrite Z.max_l by lia. rewrite rs_rescale_id. entailer!. }
  rewrite ?Int.unsigned_repr in H3 by rep_lia.
  forward_if (PROP () LOCAL (temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13) (rank_stats (x1_rescale_ws ws tl tg)) pr)).
  2: { forward. assert (tl = tg) by lia. subst tg. rewrite rs_rescale_id. entailer!. }
  2: { forward. rewrite Z.max_r by lia. entailer!. }
  rewrite ?Int.unsigned_repr in H4 by rep_lia.
  forward.
  rewrite sub_repr.
  forward_for_simple_bound (Zlength ws) (EX s: Z,
    PROP ()
    LOCAL (temp _scale (vint (tg - tl)); temp _huffWeight pw; temp _rankVal pr;
           temp _nbSymbols (vint (Zlength ws)); temp _tableLog (vint tl); temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256)
           (zbytes (x1_rescale_ws (sublist 0 s ws) tl tg ++ sublist s (Zlength ws) ws) ++ wr) pw;
         data_at shr (tarray tuint 13) (rank_stats ws) pr)).
  { entailer!. rewrite sublist_nil, sublist_same by lia. entailer!. }
  { assert (Hw: 0 <= Znth i ws <= tl) by (pose proof (proj1 (Forall_Znth _ _) H2 i) as Hx; simpl in Hx; apply Hx; lia).
    assert (HZ: forall d: val, @Znth val d i (zbytes (x1_rescale_ws (sublist 0 i ws) tl tg ++ sublist i (Zlength ws) ws) ++ wr)
                = vint (Znth i ws)).
    { intros d. unfold x1_rescale_ws. list_solve. }
    forward. { rewrite HZ. entailer!; rep_lia. }
    rewrite HZ.
    forward_if (PROP ()
      LOCAL (temp _t'1 (vint (if Znth i ws =? 0 then 0 else tg - tl)); temp _s (vint i);
             temp _scale (vint (tg - tl)); temp _huffWeight pw; temp _rankVal pr;
             temp _nbSymbols (vint (Zlength ws)); temp _tableLog (vint tl); temp _targetTableLog (vint tg))
      SEP (data_at shw (tarray tuchar 256)
             (zbytes (x1_rescale_ws (sublist 0 i ws) tl tg ++ sublist i (Zlength ws) ws) ++ wr) pw;
           data_at shr (tarray tuint 13) (rank_stats ws) pr)).
    { forward.
      rewrite H6. entailer!. }
    { forward. destruct (Z.eqb_spec (Znth i ws) 0); [subst; contradiction | ]. entailer!. }
    forward. { rewrite HZ. entailer!; rep_lia. }
    rewrite HZ.
    forward.
    rewrite rs_ze by (destruct (Znth i ws =? 0); lia).
    replace (Znth i ws + (if Znth i ws =? 0 then 0 else tg - tl))
      with (if Znth i ws =? 0 then 0 else Znth i ws + (tg - tl))
      by (destruct (Z.eqb_spec (Znth i ws) 0); lia).
    rewrite rs_step1 by lia.
    entailer!. }
  rewrite sublist_same, sublist_nil, app_nil_r by lia.
  rewrite rs_rank_stats.
  set (oz := map (fun k => rs_cnt k ws) rs_upto13).
  assert (Hoz: Zlength oz = 13) by (unfold oz; rewrite Zlength_map; reflexivity).
  forward_loop (EX s: Z,
    PROP (tg - tl <= s <= tg)
    LOCAL (temp _s (vint s); temp _scale (vint (tg - tl)); temp _rankVal pr; temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13) (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg s (tg - tl)) rs_upto13)) pr))
  continue: (EX s: Z,
    PROP (tg - tl < s <= tg)
    LOCAL (temp _s (vint s); temp _scale (vint (tg - tl)); temp _rankVal pr; temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13)
           (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg (s - 1) (tg - tl)) rs_upto13)) pr))
  break: (
    PROP ()
    LOCAL (temp _scale (vint (tg - tl)); temp _rankVal pr; temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13)
           (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg (tg - tl) (tg - tl)) rs_upto13)) pr)).
  { forward. Exists tg. entailer!. rewrite rs_init by exact Hoz. entailer!. }
  { Intros s. forward_if.
    - assert (0 <= s - (tg - tl) < Zlength (map (rs_rv oz (tg - tl) tg s (tg - tl)) rs_upto13))
        by (rewrite Zlength_map, rs_Zlength_upto13; lia).
      forward.
      rewrite rs_Znth_upto13 by lia.
      forward.
      Exists s. entailer!.
      replace (rs_rv oz (tg - tl) tg s (tg - tl) (s - (tg - tl))) with (rs_rv oz (tg - tl) tg (s - 1) (tg - tl) s).
      2: { unfold rs_rv. destruct (Z.ltb_spec (tg - tl) s), (Z.leb_spec s (tg - tl)), (Z.ltb_spec (s - 1) s),
             (Z.leb_spec s tg), (Z.ltb_spec (tg - tl) (s - (tg - tl))), (Z.leb_spec (s - (tg - tl)) (tg - tl)),
             (Z.ltb_spec s (s - (tg - tl))); cbn [andb]; try lia; reflexivity. }
      rewrite rs_upd by (try lia; intros k Hk Hks; unfold rs_rv;
        destruct (Z.ltb_spec s k), (Z.ltb_spec (s - 1) k); try lia; reflexivity).
      entailer!.
    - forward. assert (s = tg - tl) by lia. subst s. entailer!. }
  { Intros s. forward. Exists (s - 1). entailer!. }
  forward_loop (EX s: Z,
    PROP (0 <= s <= tg - tl)
    LOCAL (temp _s (vint s); temp _scale (vint (tg - tl)); temp _rankVal pr; temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13) (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg (tg - tl) s) rs_upto13)) pr))
  continue: (EX s: Z,
    PROP (0 < s <= tg - tl)
    LOCAL (temp _s (vint s); temp _scale (vint (tg - tl)); temp _rankVal pr; temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13)
           (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg (tg - tl) (s - 1)) rs_upto13)) pr))
  break: (
    PROP ()
    LOCAL (temp _targetTableLog (vint tg))
    SEP (data_at shw (tarray tuchar 256) (zbytes (x1_rescale_ws ws tl tg) ++ wr) pw;
         data_at shr (tarray tuint 13)
           (map (fun z => vint z) (map (rs_rv oz (tg - tl) tg (tg - tl) 0) rs_upto13)) pr)).
  { forward. Exists (tg - tl). entailer!. }
  { Intros s. forward_if.
    - forward.
      Exists s. entailer!.
      replace (Vint (Int.repr 0)) with (Vint (Int.repr (rs_rv oz (tg - tl) tg (tg - tl) (s - 1) s))).
      2: { unfold rs_rv. destruct (Z.ltb_spec (s - 1) s), (Z.leb_spec s (tg - tl)); cbn [andb]; try lia.
           reflexivity. }
      rewrite rs_upd by (try lia; intros k Hk Hks; unfold rs_rv;
        destruct (Z.ltb_spec s k), (Z.ltb_spec (s - 1) k); try lia; reflexivity).
      entailer!.
    - forward. assert (s = 0) by lia. subst s. entailer!. }
  { Intros s. forward. Exists (s - 1). entailer!. }
  unfold oz. rewrite rs_rank_final by (assumption || lia). rewrite <- rs_rank_stats.
  unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
Qed.
