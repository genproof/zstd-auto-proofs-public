(* Group ENT: body of HUF_readStats_body. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Local Open Scope logic.

(* ---------- model: the FSE-decoded weights are bytes, at most 255 ---------- *)

Definition is_b (x: Z) : Prop := 0 <= x < 256.

Lemma rs_upd_Forall : forall (P: Z -> Prop) l i x, Forall P l -> P x -> Forall P (upd l i x).
Proof.
  intros P l. induction l as [|y l IH]; intros i x Hl Hx; simpl; auto.
  destruct i; inversion Hl; subst; constructor; auto.
Qed.

Lemma rs_place_low_Forall : forall norm n s tab high,
  (s + n <= 256)%nat -> Forall is_b tab -> Forall is_b (fst (place_low norm s n tab high)).
Proof.
  intros norm n. induction n as [|n IH]; intros s tab high Hn Ht; simpl; auto.
  destruct (nth s norm 0 =? -1); apply IH; try lia; auto.
  apply rs_upd_Forall; auto. unfold is_b; lia.
Qed.

Lemma rs_spread_one_Forall : forall log k s high tab pos,
  is_b s -> Forall is_b tab -> Forall is_b (fst (spread_one log k s high tab pos)).
Proof.
  intros log k. induction k as [|k IH]; intros s high tab pos Hs Ht; simpl; auto.
  apply IH; auto. apply rs_upd_Forall; auto.
Qed.

Lemma rs_spread_Forall : forall norm log n s high tab pos,
  (s + n <= 256)%nat -> Forall is_b tab -> Forall is_b (spread norm log s n high tab pos).
Proof.
  intros norm log n. induction n as [|n IH]; intros s high tab pos Hn Ht; simpl; auto.
  destruct (nth s norm 0 >? 0) eqn:E.
  - destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos) as [tab' pos'] eqn:E2.
    apply IH; [lia|].
    replace tab' with (fst (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos)) by (rewrite E2; auto).
    apply rs_spread_one_Forall; auto. unfold is_b; lia.
  - apply IH; auto; lia.
Qed.

Lemma rs_states_Forall : forall log tab next,
  Forall is_b tab -> Forall (fun e => is_b (fe_sym e)) (states log tab next).
Proof.
  intros log tab. induction tab as [|x tab IH]; intros next Ht; simpl; auto.
  inversion Ht; subst. constructor; simpl; auto.
Qed.

Lemma rs_fse_build_sym : forall norm log st,
  Zlength norm <= 256 -> is_b (fe_sym (fse_cell (fse_build norm log) st)).
Proof.
  intros norm log st Hn. unfold fse_cell, fse_build.
  rewrite Zlength_correct in Hn.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [tab high] eqn:E.
  simpl.
  assert (Ht: Forall is_b tab).
  { replace tab with (fst (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)))
      by (rewrite E; auto).
    apply rs_place_low_Forall; [lia|]. apply Forall_forall. intros x Hx. apply repeat_spec in Hx.
    unfold is_b; lia. }
  pose proof (rs_states_Forall log (spread norm log 0 (length norm) high tab 0)
                (map (fun c => if c =? -1 then 1 else c) norm)
                (rs_spread_Forall norm log (length norm) 0 high tab 0 ltac:(lia) Ht)) as Hs.
  set (L := states _ _ _) in *.
  destruct (Nat.lt_ge_cases (Z.to_nat st) (length L)).
  - eapply (proj1 (Forall_forall _ _) Hs). apply nth_In; auto.
  - rewrite nth_overflow by auto. simpl. unfold is_b; lia.
Qed.

Lemma rs_fse2_loop_Forall : forall fuel t V pos s1 s2 acc r,
  (forall st, is_b (fe_sym (fse_cell t st))) ->
  fse2_loop fuel t V pos s1 s2 acc = Some r -> Forall is_b acc -> Forall is_b r.
Proof.
  intros fuel. induction fuel as [|f IH]; intros t V pos s1 s2 acc r Hc E Ha; simpl in E; [discriminate|].
  repeat match type of E with context [if ?b then _ else _] => destruct b end;
  try (inversion E; subst; repeat (apply Forall_app; split; auto); fail).
  eapply IH; [exact Hc | exact E |]. repeat (apply Forall_app; split; auto).
Qed.

Lemma rs_ncount_res_len : forall s norm log size,
  ncount_res s 255 = Some (norm, log, size) -> Zlength norm <= 256.
Proof.
  intros s norm log size E. unfold ncount_res in E.
  destruct (Zlength s <? 8).
  - destruct (read_ncount _ 255) as [[[n l] sz]|] eqn:R; [|discriminate].
    destruct (sz >? Zlength s); [discriminate|]. inversion E; subst.
    unfold read_ncount in R.
    destruct (_ =? 0); [discriminate|]. destruct (_ >? _); [discriminate|].
    destruct (ncount_loop _ _ _ _ _ _ _ _ _) as [[[a b] p]|]; [|discriminate].
    destruct (negb _); [discriminate|]. destruct (Z.gtb_spec (Zlength a) (255 + 1)); [discriminate|].
    destruct (_ >? _); [discriminate|]. inversion R; subst. lia.
  - unfold ncount_c in E.
    destruct (_ >? _); [discriminate|].
    destruct (ncount_loop_c _ _ _ _ _ _ _ _ _ _) as [[[a b] p]|]; [|discriminate].
    destruct (negb _); [discriminate|]. destruct (Z.gtb_spec (Zlength a) (255 + 1)); [discriminate|].
    destruct (_ >? _); [discriminate|]. inversion E; subst. lia.
Qed.

Lemma rs_weights_of_ok : forall nk x res ws,
  nc_rel x 255 res -> weights_of res nk x = Some ws -> Zlength ws <= 255 /\ Forall is_b ws.
Proof.
  intros nk x res ws Hrel E. unfold weights_of in E.
  destruct res as [[[norm log] nsize]|]; [|discriminate].
  assert (R: Zlength norm <= 256).
  { unfold nc_rel in Hrel. destruct (Zlength x <? 8).
    - destruct Hrel as [_ [_ (_ & Hl & _)]]. lia.
    - symmetry in Hrel. apply rs_ncount_res_len in Hrel. exact Hrel. }
  destruct (log >? 6); [discriminate|]. destruct (_ >? _); [discriminate|].
  unfold fse_weights_dec in E.
  destruct (negb _); [discriminate|]. destruct (_ <? 0); [discriminate|].
  destruct (fse2_loop _ _ _ _ _ _ _) as [l|] eqn:F; [|discriminate].
  destruct (Zlength l >? 255) eqn:L; [discriminate|]. inversion E; subst.
  split; [lia|].
  eapply rs_fse2_loop_Forall; [| exact F | constructor].
  intros st. apply rs_fse_build_sym; auto.
Qed.

Lemma rs_window_none : forall s, (Zlength s < 1 \/ 128 <= byte_at s 0 \/ Zlength s < byte_at s 0 + 1) ->
  rs_window s = None.
Proof.
  intros s H. unfold rs_window.
  destruct (Z.leb_spec 1 (Zlength s)); destruct (Z.ltb_spec (byte_at s 0) 128);
  destruct (Z.leb_spec (byte_at s 0 + 1) (Zlength s)); simpl; auto; lia.
Qed.

Lemma rs_window_some : forall s, 1 <= Zlength s -> byte_at s 0 < 128 -> byte_at s 0 + 1 <= Zlength s ->
  rs_window s = Some (slice s 1 (byte_at s 0)).
Proof.
  intros s H1 H2 H3. unfold rs_window.
  destruct (Z.leb_spec 1 (Zlength s)); destruct (Z.ltb_spec (byte_at s 0) 128);
  destruct (Z.leb_spec (byte_at s 0 + 1) (Zlength s)); simpl; auto; lia.
Qed.

(* ---------- model: huf_parse_w after the weights ---------- *)

Definition huf_fin (ws: list Z) (size: Z) : option (huf_table * Z) :=
  if existsb (fun w => w >? HUF_TABLELOG_MAX) ws then None else
  let total := fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 ws in
  if total =? 0 then None else
  let tableLog := highbit total + 1 in
  if tableLog >? HUF_TABLELOG_MAX then None else
  let rest := 2 ^ tableLog - total in
  if negb (2 ^ highbit rest =? rest) then None else
  let ws := ws ++ [highbit rest + 1] in
  let rank1 := Z.of_nat (length (filter (fun w => w =? 1) ws)) in
  if orb (rank1 <? 2) (Z.odd rank1) then None else
  Some ({| ht_log := tableLog; ht_weights := ws |}, size).

Lemma rs_parse_eq : forall res nk s, huf_parse_res res nk s =
  match huf_desc_weights_w (weights_of res nk) s with None => None | Some (ws, size) => huf_fin ws size end.
Proof. intros. reflexivity. Qed.

Lemma rs_fa : forall (base: val) N j, field_compatible (tarray tuchar N) [] base -> 0 <= j < N ->
  field_address (tarray tuchar N) [ArraySubsc j] base = offset_val j base.
Proof.
  intros. rewrite field_address_offset.
  - simpl. f_equal. lia.
  - apply field_compatible_cons; split; auto.
Qed.

Lemma rs_slice : forall (s: list Z) k, 0 <= k -> slice s 1 k = sublist 1 (1 + k) s.
Proof.
  intros. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma rs_win : forall sh c off s k,
  readable_share sh -> 0 <= off -> off + Zlength s <= Zlength c -> Zlength c <= 2 ^ 63 - 1 ->
  bytes_ok s -> sublist off (off + Zlength s) c = zbytes s -> 0 <= k -> 1 + k <= Zlength s ->
  win_ok sh (Zlength c) c (off + 1) k (slice s 1 k).
Proof.
  intros sh c off s k Hr Ho Hn HN Hb Hs Hk Hk2. rewrite rs_slice by lia.
  unfold win_ok. repeat split; auto; try lia.
  - rewrite Zlength_sublist by lia. lia.
  - unfold bytes_ok in *. apply Forall_sublist. auto.
  - rewrite <- sublist_map, <- Hs. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma rs_byte_at : forall (s: list Z) i, 0 <= i < Zlength s -> byte_at s i = Znth i s.
Proof.
  intros. unfold byte_at, Znth. rewrite if_false by lia. reflexivity.
Qed.

(* ---------- the direct weights ---------- *)

Definition rs_dw (s: list Z) (k: nat) : Z :=
  let byte := byte_at s (1 + Z.of_nat k / 2) in if Nat.even k then Z.shiftr byte 4 else Z.land byte 15.

Lemma rs_hdw_len : forall s n, 0 <= n -> Zlength (huf_direct_weights s n) = n.
Proof.
  intros. unfold huf_direct_weights. rewrite Zlength_map, Zlength_correct, length_seq. lia.
Qed.

Lemma rs_hdw_app : forall s n, 0 <= n ->
  huf_direct_weights s (n + 1) = huf_direct_weights s n ++ [rs_dw s (Z.to_nat n)].
Proof.
  intros. unfold huf_direct_weights. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite seq_S, map_app. reflexivity.
Qed.

Lemma rs_even2 : forall k, Nat.even (k + k) = true /\ Nat.even (S (k + k)) = false.
Proof.
  induction k as [|k IH]; simpl; auto. rewrite Nat.add_succ_r. simpl. auto.
Qed.

Lemma rs_dw_even : forall s k, 0 <= k -> rs_dw s (Z.to_nat (2 * k)%Z) = Z.shiftr (byte_at s (1 + k)) 4.
Proof.
  intros. unfold rs_dw. replace (Z.to_nat (2 * k)) with (Z.to_nat k + Z.to_nat k)%nat by lia.
  rewrite (proj1 (rs_even2 _)). f_equal. f_equal. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
  replace (k + k) with (k * 2)%Z by lia. rewrite Z.div_mul by lia. auto.
Qed.

Lemma rs_dw_odd : forall s k, 0 <= k -> rs_dw s (Z.to_nat (2 * k + 1)%Z) = Z.land (byte_at s (1 + k)) 15.
Proof.
  intros. unfold rs_dw. replace (Z.to_nat (2 * k + 1)) with (S (Z.to_nat k + Z.to_nat k))%nat by lia.
  rewrite (proj2 (rs_even2 _)). f_equal. f_equal.
  replace (Z.of_nat (S (Z.to_nat k + Z.to_nat k))) with (1 + k * 2)%Z by lia.
  rewrite Z.div_add by lia. auto.
Qed.

Lemma rs_hdw_prefix : forall s n m, 0 <= n <= m ->
  huf_direct_weights s n = sublist 0 n (huf_direct_weights s m).
Proof.
  intros. unfold huf_direct_weights. unfold sublist. simpl skipn.
  rewrite firstn_map. f_equal. replace (Z.to_nat n - 0)%nat with (Z.to_nat n) by lia.
  replace (Z.to_nat m) with (Z.to_nat n + (Z.to_nat m - Z.to_nat n))%nat by lia.
  rewrite seq_app, firstn_app, firstn_all2 by (rewrite length_seq; lia).
  rewrite length_seq, Nat.sub_diag, firstn_O, app_nil_r. auto.
Qed.

Lemma rs_byte_at_b : forall s i, bytes_ok s -> is_b (byte_at s i).
Proof.
  intros. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length s)).
  - apply (proj1 (Forall_forall _ _) H). apply nth_In; auto.
  - rewrite nth_overflow by auto. unfold is_b; lia.
Qed.

Lemma rs_hdw_b : forall s n, bytes_ok s -> Forall is_b (huf_direct_weights s n).
Proof.
  intros. unfold huf_direct_weights. apply Forall_forall. intros x Hx. apply in_map_iff in Hx.
  destruct Hx as (k & <- & _). pose proof (rs_byte_at_b s (1 + Z.of_nat k / 2) H) as Hb. unfold is_b in *.
  destruct (Nat.even k).
  - rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
  - change 15 with (Z.ones 4). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (byte_at s (1 + Z.of_nat k / 2)) (2 ^ 4)). lia.
Qed.

Lemma rs_shr4 : forall b, 0 <= b < 256 ->
  Int.zero_ext 8 (Int.shr (Int.repr b) (Int.repr 4)) = Int.repr (Z.shiftr b 4).
Proof.
  intros. unfold Int.shr. rewrite Int.signed_repr, Int.unsigned_repr by rep_lia.
  assert (0 <= Z.shiftr b 4 < 16).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8); auto. rewrite !Int.testbit_repr by lia.
  symmetry. apply (Z.bits_above_log2 (Z.shiftr b 4) i); [lia|].
  destruct (Z.eq_dec (Z.shiftr b 4) 0) as [E|E]; [rewrite E; simpl; lia|].
  pose proof (Z.log2_lt_pow2 (Z.shiftr b 4) 4 ltac:(lia)). apply proj1 in H1. lia.
Qed.

Lemma rs_and15 : forall b, 0 <= b < 256 ->
  Int.zero_ext 8 (Int.and (Int.repr b) (Int.repr 15)) = Int.repr (Z.land b 15).
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia.
  assert (0 <= Z.land b 15 < 16).
  { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8); auto. rewrite !Int.testbit_repr by lia.
  symmetry. apply (Z.bits_above_log2 (Z.land b 15) i); [lia|].
  destruct (Z.eq_dec (Z.land b 15) 0) as [E|E]; [rewrite E; simpl; lia|].
  pose proof (Z.log2_lt_pow2 (Z.land b 15) 4 ltac:(lia)). apply proj1 in H1. lia.
Qed.

Lemma rs_upd_tail : forall (A: list val) k v, 0 < k ->
  upd_Znth (Zlength A) (A ++ Zrepeat Vundef k) v = (A ++ [v]) ++ Zrepeat Vundef (k - 1).
Proof. intros. list_solve. Qed.

Lemma rs_upd_tail' : forall (A: list val) i k v, Zlength A = i -> 0 < k ->
  upd_Znth i (A ++ Zrepeat Vundef k) v = (A ++ [v]) ++ Zrepeat Vundef (k - 1).
Proof. intros. subst i. apply rs_upd_tail; auto. Qed.

Lemma rs_hdw_step_even : forall s k, 0 <= k -> 1 + k < Zlength s ->
  zbytes (huf_direct_weights s (2 * k)) ++ [Vint (Int.repr (Z.shiftr (Znth (1 + k) s) 4))] =
  zbytes (huf_direct_weights s (2 * k + 1)).
Proof.
  intros. rewrite (rs_hdw_app s (2 * k)%Z), rs_dw_even, map_app, rs_byte_at by lia. reflexivity.
Qed.

Lemma rs_hdw_step_odd : forall s k, 0 <= k -> 1 + k < Zlength s ->
  zbytes (huf_direct_weights s (2 * k + 1)) ++ [Vint (Int.repr (Z.land (Znth (1 + k) s) 15))] =
  zbytes (huf_direct_weights s (2 * k + 2)).
Proof.
  intros. replace (2 * k + 2) with (2 * k + 1 + 1) by lia.
  rewrite (rs_hdw_app s (2 * k + 1)%Z), rs_dw_odd, map_app, rs_byte_at by lia. reflexivity.
Qed.

(* ---------- the statistics ---------- *)

Definition rs_wsum (l: list Z) : Z := fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 l.

Lemma rs_wsum_app : forall l w, rs_wsum (l ++ [w]) = rs_wsum l + Z.shiftr (2 ^ w) 1.
Proof. intros. unfold rs_wsum. rewrite fold_right_app. simpl. induction l; simpl; lia. Qed.

Lemma rs_shiftr_pow : forall w, 0 <= w <= 12 -> 0 <= Z.shiftr (2 ^ w) 1 <= 2048.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  assert (0 < 2 ^ w <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  change (2 ^ 12) with 4096 in H0. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia].
Qed.

Lemma rs_wsum_bound : forall l, Forall (fun w => 0 <= w <= 12) l -> 0 <= rs_wsum l <= 2048 * Zlength l.
Proof.
  induction l as [|w l IH]; intros Hf; simpl; [lia|]. inversion Hf; subst.
  pose proof (rs_shiftr_pow w H1). specialize (IH H2). rewrite Zlength_cons. lia.
Qed.

Lemma rs_rank_len : forall l, Zlength (rank_stats l) = 13.
Proof. intros. unfold rank_stats. rewrite Zlength_map. reflexivity. Qed.

Lemma rs_rank_Znth : forall l w, 0 <= w <= 12 ->
  Znth w (rank_stats l) = Vint (Int.repr (Zlength (filter (fun x => x =? w) l))).
Proof.
  intros. unfold rank_stats. rewrite Znth_map by (rewrite Zlength_correct, length_seq; simpl; lia).
  unfold Znth. rewrite if_false by lia. rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma rs_rank_app : forall l w, 0 <= w <= 12 ->
  rank_stats (l ++ [w]) = upd_Znth w (rank_stats l) (Vint (Int.repr (Zlength (filter (fun x => x =? w) l) + 1))).
Proof.
  intros. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !rs_rank_len. auto.
  - intros j Hj. rewrite rs_rank_len in Hj. rewrite rs_rank_Znth by lia.
    rewrite filter_app, Zlength_app. simpl.
    destruct (Z.eq_dec j w) as [<-|E].
    + rewrite upd_Znth_same by (rewrite rs_rank_len; lia). rewrite Z.eqb_refl. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?rs_rank_len; lia). rewrite rs_rank_Znth by lia.
      replace (w =? j) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Zlength_nil, Z.add_0_r. auto.
Qed.

Lemma rs_shl_shr : forall w, 0 <= w <= 12 ->
  Int.shr (Int.shl (Int.repr 1) (Int.repr w)) (Int.repr 1) = Int.repr (Z.shiftr (2 ^ w) 1).
Proof.
  intros. unfold Int.shl, Int.shr. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftl_1_l.
  assert (0 < 2 ^ w <= 2 ^ 12) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  change (2 ^ 12) with 4096 in H0. rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

Ltac rs_zn := change (@Znth val Vundef) with (@Znth val Inhabitant_val) in *.

Lemma rs_fin_big : forall ws size i, 0 <= i < Zlength ws -> Znth i ws > 12 -> huf_fin ws size = None.
Proof.
  intros. unfold huf_fin.
  replace (existsb (fun w => w >? HUF_TABLELOG_MAX) ws) with true; auto.
  symmetry. apply existsb_exists. exists (Znth i ws). split; [apply Znth_In; lia|].
  unfold HUF_TABLELOG_MAX. lia.
Qed.

Lemma rs_fin_eq : forall ws size, Forall (fun w => 0 <= w <= 12) ws ->
  huf_fin ws size =
  if rs_wsum ws =? 0 then None else
  if highbit (rs_wsum ws) + 1 >? 12 then None else
  if negb (2 ^ highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) =? 2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws)
  then None else
  if orb (Zlength (filter (fun w => w =? 1)
            (ws ++ [highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) + 1])) <? 2)
         (Z.odd (Zlength (filter (fun w => w =? 1)
            (ws ++ [highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) + 1]))))
  then None else
  Some ({| ht_log := highbit (rs_wsum ws) + 1;
           ht_weights := ws ++ [highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) + 1] |}, size).
Proof.
  intros. unfold huf_fin.
  replace (existsb (fun w => w >? HUF_TABLELOG_MAX) ws) with false.
  2: { symmetry. apply Bool.not_true_iff_false. intro E. apply existsb_exists in E.
       destruct E as (x & Hx & Hx'). rewrite Forall_forall in H. specialize (H x Hx).
       unfold HUF_TABLELOG_MAX in Hx'. lia. }
  rewrite !Zlength_correct. reflexivity.
Qed.

Lemma rs_hb : forall T, 0 < T -> 2 ^ highbit T <= T < 2 ^ (highbit T + 1) /\ 0 <= highbit T.
Proof.
  intros. unfold highbit. pose proof (Z.log2_spec T H). pose proof (Z.log2_nonneg T).
  rewrite Z.add_1_r. lia.
Qed.

Lemma rs_zext8 : forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8); auto. rewrite !Int.testbit_repr by lia.
  symmetry. apply (Z.bits_above_log2 x i); [lia|].
  destruct (Z.eq_dec x 0) as [E|E]; [rewrite E; simpl; lia|].
  pose proof (Z.log2_lt_pow2 x 8 ltac:(lia)). apply proj1 in H0. lia.
Qed.

Lemma rs_shl1 : forall k, 0 <= k <= 30 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
  intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma rs_odd_bool : forall r, 2 <= r <= 256 ->
  Vint (Int.repr (if ((r <? 2) || Z.odd r)%bool then 1 else 0)) =
  Vint (if Int.eq (Int.repr (Z.land r 1)) Int.zero then Int.zero else Int.one).
Proof.
  intros. replace (r <? 2) with false by (symmetry; apply Z.ltb_ge; lia). simpl orb.
  assert (E: Z.land r 1 = r mod 2) by (change 2 with (2 ^ 1); rewrite <- (Z.land_ones r 1) by lia; reflexivity).
  rewrite E, Zodd_mod. pose proof (Z.mod_pos_bound r 2 ltac:(lia)).
  destruct (Z.eq_dec (r mod 2) 0) as [E0|E0].
  - rewrite E0. reflexivity.
  - replace (r mod 2) with 1 by lia. reflexivity.
Qed.

Ltac rs_neg := f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity.

Lemma body_ent_readstats :
  semax_body Vprog (G_B0 ++ [FSE_decompress_wksp_bmi2_spec]) f_HUF_readStats_body HUF_readStats_body_spec.
Proof.
  start_function.
  destruct H0 as (Hrd & Hoff & Hn & HN & Hc & _ & Hb & Hsub). subst N.
  forward.
  forward_if (Zlength s <> 0).
  { forward. Exists (Int64.unsigned (Int64.repr (-72))) (Zrepeat Vundef 256) (@None (list Z * Z * Z)).
    assert (Hz: Zlength s = 0).
    { apply (f_equal Int64.unsigned) in H0. rewrite Int64.unsigned_repr in H0 by rep_lia. auto. }
    rewrite (rs_window_none s) by lia.
    rewrite rs_parse_eq. unfold huf_desc_weights_w. rewrite Hz. simpl.
    entailer!. rs_neg. }
  { forward. entailer!. rewrite H10 in H0. contradiction. }
  assert (Hcat: forall i, 0 <= i < Zlength s -> Znth (off + i) c = Vint (Int.repr (Znth i s))).
  { intros i Hi. rewrite <- (Znth_map _ (fun b : Z => Vint (Int.repr b))) by lia. rewrite <- Hsub.
    rewrite Znth_sublist by lia. f_equal; lia. }
  assert (Hbyte: forall i, 0 <= i < Zlength s -> 0 <= Znth i s < 256).
  { intros i Hi. exact (proj1 (Forall_Znth _ _) Hb i Hi). }
  Intros. rename H0 into Hs0.
  assert (Hs1: 1 <= Zlength s).
  { destruct (Z.eq_dec (Zlength s) 0) as [E|E]; [|pose proof (Zlength_nonneg s); lia].
    rewrite E in Hs0. contradiction. }
  pose proof (Hcat 0 ltac:(lia)) as Hc0. rewrite Z.add_0_r in Hc0.
  pose proof (Hbyte 0 ltac:(lia)) as Hb0.
  assert_PROP (force_val (sem_add_ptr_int tuchar Signed (offset_val off base) (Vint (Int.repr 0))) =
               field_address (tarray tuchar (Zlength c)) [ArraySubsc off] base).
  { entailer!. rewrite rs_fa by (auto; lia). simpl. normalize. }
  forward.
  { entailer!. rs_zn. rewrite Hc0. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  rs_zn. rewrite Hc0.
  forward.
  set (hb := Znth 0 s) in *.
  rewrite Int.unsigned_repr by rep_lia.
  forward_if (EX ws: list Z, EX wc: list val, EX isz: Z, EX res: option (list Z * Z * Z),
    PROP (huf_desc_weights_w (weights_of res nk) s = Some (ws, (isz + 1)%Z); Zlength wc = 256;
          sublist 0 (Zlength ws) wc = zbytes ws; Zlength ws <= 255; Forall is_b ws; 0 <= isz < 256;
          match rs_window s with Some w => nc_rel w 255 res | None => True end;
          match rs_window s with Some w => res = x_ncount w 255 | None => True end)
    LOCAL (temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr (Zlength ws)));
           gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw; data_at_ shr (tarray tuint 13) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar (Zlength c)) c base;
         data_at_ shk (tarray tuint nk) pk)).
  { (* direct weights *)
    rewrite Int64.unsigned_repr in H1 by rep_lia. change (Int64.unsigned (Int64.repr 128)) with 128 in H1.
    forward. forward.
    set (osz := hb - 127).
    set (isz := (osz + 1) / 2).
    assert (Eo: Int64.sub (Int64.repr hb) (Int64.repr (Int.signed (Int.repr 127))) = Int64.repr osz).
    { change (Int.signed (Int.repr 127)) with 127. rewrite Int64.sub_signed, !Int64.signed_repr by rep_lia.
      reflexivity. }
    rewrite Eo.
    assert (Hosz: 1 <= osz <= 128) by lia.
    assert (Hisz: 1 <= isz <= 64).
    { unfold isz. pose proof (Z.div_mod (osz + 1) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (osz + 1) 2 ltac:(lia)).
      lia. }
    assert (Ei: Int64.divu (Int64.add (Int64.repr osz) (Int64.repr (Int.signed (Int.repr 1))))
                  (Int64.repr (Int.signed (Int.repr 2))) = Int64.repr isz).
    { change (Int.signed (Int.repr 1)) with 1. change (Int.signed (Int.repr 2)) with 2.
      unfold Int64.divu. rewrite Int64.add_unsigned, (Int64.unsigned_repr osz), (Int64.unsigned_repr 1),
        (Int64.unsigned_repr (osz + 1)), (Int64.unsigned_repr 2) by rep_lia. reflexivity. }
    rewrite Ei.
    forward_if (isz + 1 <= Zlength s).
    { rewrite Int64.add_unsigned, (Int64.unsigned_repr isz), (Int64.unsigned_repr 1), !Int64.unsigned_repr in H2
        by rep_lia.
      forward. Exists (Int64.unsigned (Int64.repr (-72))) (Zrepeat Vundef 256) (@None (list Z * Z * Z)).
      rewrite (rs_window_none s) by (rewrite rs_byte_at by lia; fold hb; lia).
      assert (Hd: huf_desc_weights_w (weights_of None nk) s = None).
      { unfold huf_desc_weights_w. rewrite rs_byte_at by lia. fold hb.
        destruct (Zlength s <? 1); auto. destruct (Z.geb_spec hb 128); [|lia].
        fold osz. fold isz. destruct (Z.ltb_spec (Zlength s) (isz + 1)); auto; lia. }
      rewrite rs_parse_eq, Hd. entailer!. rewrite Int64.repr_unsigned; reflexivity. }
    { rewrite Int64.add_unsigned, (Int64.unsigned_repr isz), (Int64.unsigned_repr 1), !Int64.unsigned_repr in H2
        by rep_lia.
      forward. entailer!. }
    Intros.
    forward_if.
    { exfalso. lia. }
    forward.
    forward_loop (EX k: Z,
      PROP (0 <= k; 2 * k <= osz + 1)
      LOCAL (temp _n (Vint (Int.repr (2 * k))); temp _ip (offset_val 1 (offset_val off base));
             temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr osz));
             gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
      SEP (zstd_globals gv;
           data_at shw (tarray tuchar 256) (zbytes (huf_direct_weights s (2 * k)) ++ Zrepeat Vundef (256 - 2 * k)) pw;
           data_at_ shr (tarray tuint 13) pr; data_at_ shs tuint ps; data_at_ sht tuint pt;
           data_at sh (tarray tuchar (Zlength c)) c base; data_at_ shk (tarray tuint nk) pk))
    continue: (EX k: Z,
      PROP (0 <= k; 2 * k + 2 <= osz + 1)
      LOCAL (temp _n (Vint (Int.repr (2 * k))); temp _ip (offset_val 1 (offset_val off base));
             temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr osz));
             gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
      SEP (zstd_globals gv;
           data_at shw (tarray tuchar 256)
             (zbytes (huf_direct_weights s (2 * k + 2)) ++ Zrepeat Vundef (256 - (2 * k + 2))) pw;
           data_at_ shr (tarray tuint 13) pr; data_at_ shs tuint ps; data_at_ sht tuint pt;
           data_at sh (tarray tuchar (Zlength c)) c base; data_at_ shk (tarray tuint nk) pk))
    break: (EX k: Z,
      PROP (0 <= k; osz <= 2 * k <= osz + 1)
      LOCAL (temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr osz));
             gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
      SEP (zstd_globals gv;
           data_at shw (tarray tuchar 256) (zbytes (huf_direct_weights s (2 * k)) ++ Zrepeat Vundef (256 - 2 * k)) pw;
           data_at_ shr (tarray tuint 13) pr; data_at_ shs tuint ps; data_at_ sht tuint pt;
           data_at sh (tarray tuchar (Zlength c)) c base; data_at_ shk (tarray tuint nk) pk)).
    { forward. Exists 0. entailer!. }
    { Intros k.
      forward_if (2 * k < osz).
      { forward. entailer!. rewrite Int.unsigned_repr in * by rep_lia. lia. }
      { forward. Exists k. entailer!. rewrite Int.unsigned_repr in * by rep_lia. lia. }
      Intros.
      assert (Hk1: 1 + k + 1 <= Zlength s).
      { assert (k + 1 <= isz); [|lia]. unfold isz. pose proof (Z.div_mod (osz + 1) 2 ltac:(lia)).
        pose proof (Z.mod_pos_bound (osz + 1) 2 ltac:(lia)). lia. }
      assert (Ek: (2 * k / 2)%Z = k) by (rewrite Z.mul_comm, Z.div_mul; lia).
      assert_PROP (force_val (sem_add_ptr_int tuchar Unsigned (offset_val 1 (offset_val off base))
                     (Vint (Int.divu (Int.repr (2 * k)) (Int.repr 2)))) =
                   field_address (tarray tuchar (Zlength c)) [ArraySubsc (off + (1 + k))] base).
      { entailer!. rewrite Ek, rs_fa by (auto; lia). simpl. f_equal. lia. }
      pose proof (Hcat (1 + k) ltac:(lia)) as Hck. pose proof (Hbyte (1 + k) ltac:(lia)) as Hbk.
      forward.
      { entailer!. rs_zn. rewrite Hck. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rs_zn. rewrite Hck.
      forward.
      rewrite rs_shr4 by auto.
      rewrite (rs_upd_tail' _ (2 * k)%Z) by (try rewrite Zlength_map, rs_hdw_len; lia).
      rewrite rs_hdw_step_even by lia.
      forward.
      { entailer!. rs_zn. rewrite Hck. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rs_zn. rewrite Hck.
      forward.
      rewrite rs_and15 by auto.
      rewrite (rs_upd_tail' _ (2 * k + 1)%Z) by (try rewrite Zlength_map, rs_hdw_len; lia).
      rewrite rs_hdw_step_odd by lia.
      Exists k. replace (256 - 2 * k - 1 - 1)%Z with (256 - (2 * k + 2))%Z by lia. entailer!. }
    { Intros k. forward. Exists (k + 1). replace (2 * (k + 1))%Z with (2 * k + 2)%Z by lia. entailer!. }
    Intros k.
    assert (Hl: Zlength (huf_direct_weights s osz) = osz) by (apply rs_hdw_len; lia).
    Exists (huf_direct_weights s osz) (zbytes (huf_direct_weights s (2 * k)) ++ Zrepeat Vundef (256 - 2 * k)) isz
      (@None (list Z * Z * Z)).
    rewrite Hl.
    rewrite (rs_window_none s) by (rewrite rs_byte_at by lia; fold hb; lia).
    assert (Hd: huf_desc_weights_w (weights_of None nk) s = Some (huf_direct_weights s osz, (isz + 1)%Z)).
    { unfold huf_desc_weights_w. rewrite rs_byte_at by lia. fold hb.
      destruct (Zlength s <? 1) eqn:E; [rewrite Z.ltb_lt in E; lia|]. destruct (Z.geb_spec hb 128); [|lia].
      fold osz isz. destruct (Z.ltb_spec (Zlength s) (isz+1)); [lia|]. reflexivity. }
    entailer!. split; [| apply rs_hdw_b; auto].
    rewrite sublist_app1 by (try rewrite Zlength_map, rs_hdw_len; lia).
    rewrite sublist_map, <- rs_hdw_prefix by lia. reflexivity. }
  { (* FSE-compressed weights *)
    rewrite Int64.unsigned_repr in H1 by rep_lia. change (Int64.unsigned (Int64.repr 128)) with 128 in H1.
    forward_if (hb + 1 <= Zlength s).
    { forward. Exists (Int64.unsigned (Int64.repr (-72))) (Zrepeat Vundef 256) (@None (list Z * Z * Z)).
      rewrite !Int64.unsigned_repr in H2 by rep_lia.
      rewrite (rs_window_none s) by (rewrite rs_byte_at by lia; fold hb; lia).
      assert (Hd: huf_desc_weights_w (weights_of None nk) s = None).
      { unfold huf_desc_weights_w. rewrite rs_byte_at by lia. fold hb.
        destruct (Zlength s <? 1); auto. destruct (Z.geb_spec hb 128); [lia|].
        destruct (Z.ltb_spec (Zlength s) (hb + 1)); auto; lia. }
      rewrite rs_parse_eq, Hd. entailer!.
      rewrite Int64.repr_unsigned; reflexivity. }
    { rewrite Int64.add_unsigned, (Int64.unsigned_repr hb), (Int64.unsigned_repr 1), !Int64.unsigned_repr in H2
        by rep_lia.
      forward. entailer!. }
    Intros.
    forward_call (gv, shw, pw, Zrepeat Vundef 256, sh, base, Zlength c, c, off + 1, slice s 1 hb, shk, pk, nk).
    { entailer!. simpl. rewrite rs_slice, Zlength_sublist by lia. replace (1 + hb - 1) with hb by lia. reflexivity. }
    { replace (Zlength (slice s 1 hb)) with hb by (rewrite rs_slice, Zlength_sublist by lia; lia).
      split; [apply rs_win; auto; lia | lia]. }
    Intros vret. destruct vret as [[r oc'] res]. simpl fst in *; simpl snd in *.
    rename H3 into Hr, H4 into Hoc, H5 into Hrel, H6 into Hw.
    assert (Hwin: rs_window s = Some (slice s 1 hb)).
    { unfold hb. rewrite <- rs_byte_at by lia. apply rs_window_some; try rewrite rs_byte_at by lia; fold hb; lia. }
    assert (Hd: huf_desc_weights_w (weights_of res nk) s =
                match weights_of res nk (slice s 1 hb) with Some ws => Some (ws, hb + 1) | None => None end).
    { unfold huf_desc_weights_w. rewrite rs_byte_at by lia. fold hb.
      destruct (Zlength s <? 1) eqn:E; [rewrite Z.ltb_lt in E; lia|]. destruct (Z.geb_spec hb 128); [lia|].
      destruct (Z.ltb_spec (Zlength s) (hb + 1)); [lia|]. reflexivity. }
    forward_call (r).
    forward_if.
    { (* error *)
      destruct (weights_of res nk (slice s 1 hb)) as [ws|] eqn:Ew.
      { destruct Hw as [-> _]. apply (rs_weights_of_ok _ _ _ _ Hrel) in Ew. destruct Ew as [Hl _].
        assert (He: is_error_code (Zlength ws) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
        rewrite He in *. match goal with Hx: 0 <> 0 |- _ => now elim Hx end. }
      forward. Exists r oc' (x_ncount (slice s 1 hb) 255). rewrite Hwin, rs_parse_eq, Hd. entailer!. }
    { destruct (weights_of res nk (slice s 1 hb)) as [ws|] eqn:Ew.
      2: { rewrite Hw in H3. discriminate. }
      destruct Hw as [-> Hw]. pose proof (rs_weights_of_ok _ _ _ _ Hrel Ew) as [Hl Hf].
      forward. Exists ws oc' hb (x_ncount (slice s 1 hb) 255). rewrite Hwin. entailer!. }
    }
  Intros ws wc isz res.
  clear H0. rename H1 into Hdw, H2 into Hwc, H3 into Hsw, H4 into Hlw, H5 into Hfw, H6 into Hisz, H7 into Hwin, H8 into Hwinx.
  assert (Hwz: forall i, 0 <= i < Zlength ws -> Znth i wc = Vint (Int.repr (Znth i ws))).
  { intros i Hi. rewrite <- (Znth_map _ (fun b : Z => Vint (Int.repr b))) by lia. rewrite <- Hsw.
    rewrite Znth_sublist by lia. f_equal; lia. }
  sep_apply (data_at__memory_block shr (tarray tuint 13) pr). Intros.
  change (sizeof (tarray tuint 13)) with 52.
  forward_call (shr, pr, 0, 52).
  pose proof (memset_zero_data_at shr (tarray tuint 13) pr) as Hz. rewrite zero_val_tarray in Hz.
  change (sizeof (tarray tuint 13)) with 52 in Hz. change (Vint Int.zero) with (Vint (Int.repr 0)) in Hz.
  assert (E: Zrepeat (zero_val tuint) 13 = rank_stats []) by (rewrite zero_val_eq; reflexivity).
  rewrite E in Hz. sep_apply Hz; auto. clear Hz E.
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= Zlength ws; Forall (fun w => 0 <= w <= 12) (sublist 0 i ws))
    LOCAL (temp _n__1 (Vint (Int.repr i)); temp _weightTotal (Vint (Int.repr (rs_wsum (sublist 0 i ws))));
           temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr (Zlength ws)));
           gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         data_at shr (tarray tuint 13) (rank_stats (sublist 0 i ws)) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar (Zlength c)) c base;
         data_at_ shk (tarray tuint nk) pk))
  continue: (EX i: Z,
    PROP (0 <= i < Zlength ws; Forall (fun w => 0 <= w <= 12) (sublist 0 (i + 1) ws))
    LOCAL (temp _n__1 (Vint (Int.repr i)); temp _weightTotal (Vint (Int.repr (rs_wsum (sublist 0 (i + 1) ws))));
           temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr (Zlength ws)));
           gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         data_at shr (tarray tuint 13) (rank_stats (sublist 0 (i + 1) ws)) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar (Zlength c)) c base;
         data_at_ shk (tarray tuint nk) pk))
  break: (
    PROP (Forall (fun w => 0 <= w <= 12) ws)
    LOCAL (temp _weightTotal (Vint (Int.repr (rs_wsum ws)));
           temp _iSize (Vlong (Int64.repr isz)); temp _oSize (Vlong (Int64.repr (Zlength ws)));
           gvars gv; temp _huffWeight pw; temp _rankStats pr; temp _nbSymbolsPtr ps; temp _tableLogPtr pt)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         data_at shr (tarray tuint 13) (rank_stats ws) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar (Zlength c)) c base;
         data_at_ shk (tarray tuint nk) pk)).
  { forward. Exists 0. rewrite sublist_nil. entailer!. }
  { Intros i.
    forward_if (i < Zlength ws).
    { forward. entailer!. rewrite Int.unsigned_repr in * by rep_lia. lia. }
    { forward. rewrite Int.unsigned_repr in * by rep_lia. assert (i = Zlength ws) by lia. subst i.
      rewrite sublist_same in * by lia. entailer!. }
    Intros.
    pose proof (Hwz i ltac:(lia)) as Hwi.
    assert (Hbi: is_b (Znth i ws)) by (apply Forall_Znth; auto; lia). unfold is_b in Hbi.
    forward.
    { entailer!. rs_zn. rewrite Hwi. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rs_zn. rewrite Hwi.
    forward_if (Znth i ws <= 12).
    { forward. Exists (Int64.unsigned (Int64.repr (-20))) wc res.
      rewrite rs_parse_eq, Hdw, (rs_fin_big ws (isz + 1) i) by (try rewrite Int.unsigned_repr in *; rep_lia).
      entailer!. rewrite Int64.repr_unsigned; reflexivity. }
    { forward. entailer!. }
    Intros.
    forward.
    { entailer!. rs_zn. rewrite Hwi. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rs_zn. rewrite Hwi.
    forward.
    { entailer!. rs_zn. rewrite Hwi. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rs_zn. rewrite Hwi.
    forward.
    { entailer!. rs_zn. rewrite rs_rank_Znth by lia. simpl. auto. }
    rs_zn. rewrite rs_rank_Znth by lia.
    forward.
    rewrite add_repr, <- rs_rank_app by lia.
    forward.
    { entailer!. rs_zn. rewrite Hwi. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rs_zn. rewrite Hwi.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite rs_shl_shr, add_repr by lia.
    Exists i. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia. rewrite rs_wsum_app.
    entailer!. apply Forall_app; split; auto. repeat constructor; lia. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  Intros. rename H1 into Hf12.
  pose proof (rs_wsum_bound ws Hf12) as HT.
  forward_if (rs_wsum ws <> 0).
  { forward. Exists (Int64.unsigned (Int64.repr (-20))) wc res.
    assert (Hm: huf_fin ws (isz + 1) = None) by (rewrite rs_fin_eq, H1 by auto; reflexivity).
    rewrite rs_parse_eq, Hdw, Hm. entailer!. rewrite Int64.repr_unsigned; reflexivity. }
  { forward. entailer!. }
  Intros.
  assert (HT0: 0 < rs_wsum ws) by lia.
  pose proof (rs_hb _ HT0) as [HhT HhT0].
  assert (HhT1: highbit (rs_wsum ws) < 19).
  { unfold highbit. apply Z.log2_lt_pow2; auto. lia. }
  forward_call (rs_wsum ws, gv).
  forward.
  forward_if (highbit (rs_wsum ws) + 1 <= 12).
  { forward. Exists (Int64.unsigned (Int64.repr (-20))) wc res.
    assert (Hm: huf_fin ws (isz + 1) = None).
    { rewrite rs_fin_eq by auto. destruct (Z.eqb_spec (rs_wsum ws) 0); [lia|].
      destruct (Z.gtb_spec (highbit (rs_wsum ws) + 1) 12); [reflexivity|].
      lia. }
    rewrite rs_parse_eq, Hdw, Hm. entailer!. rewrite Int64.repr_unsigned; reflexivity. }
  { forward. entailer!. }
  Intros. rewrite add_repr.
  forward.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite rs_shl1 by lia.
  forward.
  rewrite sub_repr.
  assert (Hp: 2 ^ (highbit (rs_wsum ws) + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 12) with 4096 in Hp.
  set (R := 2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws).
  assert (HR: 0 < R <= 4096) by (unfold R; lia).
  pose proof (rs_hb _ (proj1 HR)) as [HhR HhR0].
  assert (HhR2: highbit R < highbit (rs_wsum ws) + 1).
  { change (highbit R) with (Z.log2 R). apply Z.log2_lt_pow2. lia. unfold R. lia. }
  forward_call (R, gv).
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite rs_shl1 by lia.
  forward_call (R, gv).
  forward.
  rewrite add_repr.
  forward_if (2 ^ highbit R = R).
  { forward. Exists (Int64.unsigned (Int64.repr (-20))) wc res.
    assert (Hm: huf_fin ws (isz + 1) = None).
    { rewrite rs_fin_eq by auto. fold R. destruct (Z.eqb_spec (rs_wsum ws) 0); [lia|].
      destruct (Z.gtb_spec (highbit (rs_wsum ws) + 1) 12); [lia|].
      destruct (Z.eqb_spec (2 ^ highbit R) R); [|reflexivity]. rewrite e in *. contradiction. }
    rewrite rs_parse_eq, Hdw, Hm. entailer!. rewrite Int64.repr_unsigned; reflexivity. }
  { forward. entailer!. }
  Intros. rename H3 into HpR.
  forward.
  forward.
  { entailer!. rewrite rs_rank_Znth by lia. simpl; auto. }
  rs_zn. rewrite rs_rank_Znth by lia.
  forward.
  rewrite add_repr, <- rs_rank_app by lia.
  rewrite rs_zext8 by lia.
  set (L := ws ++ [highbit R + 1]).
  set (r1 := Zlength (filter (fun x => x =? 1) L)).
  assert (Hr1: 0 <= r1 <= 256).
  { unfold r1. split; [apply Zlength_nonneg|]. rewrite Zlength_correct. pose proof (filter_length_le (fun x => x =? 1) L).
    assert (Zlength L <= 256) by (unfold L; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    rewrite Zlength_correct in H4. lia. }
  forward.
  rs_zn. rewrite rs_rank_Znth by lia. fold r1.
  forward_if (temp _t'6 (Vint (Int.repr (if orb (r1 <? 2) (Z.odd r1) then 1 else 0)))).
  { forward. entailer!. destruct (Z.ltb_spec r1 2); [reflexivity | lia]. }
  { forward. rs_zn. rewrite rs_rank_Znth by lia. fold r1.
    forward. entailer!. apply rs_odd_bool. lia. }
  forward_if.
  { assert (Hm: huf_fin ws (isz + 1) = None).
    { rewrite rs_fin_eq by auto. fold R. fold L. fold r1. destruct (Z.eqb_spec (rs_wsum ws) 0); [lia|].
      destruct (Z.gtb_spec (highbit (rs_wsum ws) + 1) 12); [lia|].
      destruct (Z.eqb_spec (2 ^ highbit R) R); [|lia].
      destruct ((r1 <? 2) || Z.odd r1)%bool; [reflexivity|]. contradiction. }
    forward.
    Exists (Int64.unsigned (Int64.repr (-20)))
      (upd_Znth (Zlength ws) wc
         (Vint (Int.zero_ext 8 (Int.repr (highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) + 1)))))
      res.
    rewrite rs_parse_eq, Hdw, Hm. entailer!.
    rewrite Int64.repr_unsigned; reflexivity. }
  assert (Hb1: ((r1 <? 2) || Z.odd r1)%bool = false).
  { destruct ((r1 <? 2) || Z.odd r1)%bool; auto. exfalso; apply Int.one_not_zero; exact H3. }
  assert (Hm: huf_fin ws (isz + 1) =
              Some ({| ht_log := highbit (rs_wsum ws) + 1; ht_weights := L |}, (isz + 1)%Z)).
  { rewrite rs_fin_eq by auto. fold R. fold L. fold r1. destruct (Z.eqb_spec (rs_wsum ws) 0); [lia|].
    destruct (Z.gtb_spec (highbit (rs_wsum ws) + 1) 12); [lia|].
    destruct (Z.eqb_spec (2 ^ highbit R) R); [|lia]. rewrite Hb1. reflexivity. }
  assert (HL: Zlength L = Zlength ws + 1) by (unfold L; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (HwL: sublist 0 (Zlength L) (upd_Znth (Zlength ws) wc (Vint (Int.repr (highbit R + 1)))) = zbytes L).
  { rewrite HL. unfold L. rewrite map_app. rewrite <- Hsw. list_solve. }
  forward.
  forward.
  rewrite rs_zext8 by lia.
  Exists (isz + 1)
    (upd_Znth (Zlength ws) wc (Vint (Int.repr (highbit (2 ^ (highbit (rs_wsum ws) + 1) - rs_wsum ws) + 1))))
    res.
  rewrite rs_parse_eq, Hdw, Hm. simpl ht_weights; simpl ht_log.
  rewrite !Int64.Z_mod_modulus_eq, !(Z.mod_small (Zlength ws)) by rep_lia.
  rewrite Z.mod_small by rep_lia. rewrite <- HL.
  entailer!.
Qed.
