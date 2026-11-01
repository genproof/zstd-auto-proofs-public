(* Model lemma for group HUF: what a parsed tree description (Huffman.huf_parse_desc)
   guarantees. *)
Require Export Zstd.proof.dec.B.BRep.

(* ---------- FSE-decoded weights are symbols of fse_build: >= 0 ---------- *)

Lemma hmd_upd_Forall (P: Z -> Prop) (l: list Z) (i: nat) (x: Z) :
  Forall P l -> P x -> Forall P (upd l i x).
Proof.
  intros Hl Hx. revert i. induction Hl as [| y l' Hy Hl' IH]; intros i; destruct i; simpl; auto.
Qed.

Lemma hmd_place_low_nonneg (norm: list Z) (s n: nat) (tab: list Z) (high: Z) :
  Forall (fun x => 0 <= x) tab -> Forall (fun x => 0 <= x) (fst (place_low norm s n tab high)).
Proof.
  revert s tab high. induction n as [| n IH]; intros s tab high Ht; simpl; auto.
  destruct (nth s norm 0 =? -1); apply IH; auto.
  apply hmd_upd_Forall; auto. lia.
Qed.

Lemma hmd_spread_one_nonneg (log: Z) (k: nat) (s high: Z) (tab: list Z) (pos: Z) :
  0 <= s -> Forall (fun x => 0 <= x) tab -> Forall (fun x => 0 <= x) (fst (spread_one log k s high tab pos)).
Proof.
  revert tab pos. induction k as [| k IH]; intros tab pos Hs Ht; simpl; auto.
  apply IH; auto. apply hmd_upd_Forall; auto.
Qed.

Lemma hmd_spread_nonneg (norm: list Z) (log: Z) (s n: nat) (high: Z) (tab: list Z) (pos: Z) :
  Forall (fun x => 0 <= x) tab -> Forall (fun x => 0 <= x) (spread norm log s n high tab pos).
Proof.
  revert s tab pos. induction n as [| n IH]; intros s tab pos Ht; simpl; auto.
  destruct (nth s norm 0 >? 0) eqn:E.
  - destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos) as [tab' pos'] eqn:E1.
    apply IH.
    replace tab' with (fst (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos)) by (rewrite E1; auto).
    apply hmd_spread_one_nonneg; auto; lia.
  - apply IH; auto.
Qed.

Lemma hmd_states_nonneg (log: Z) (tab next: list Z) :
  Forall (fun x => 0 <= x) tab -> Forall (fun e => 0 <= fe_sym e) (states log tab next).
Proof.
  intros Ht. revert next. induction Ht as [| x tab' Hx Ht' IH]; intros next; simpl; constructor; auto.
Qed.

Lemma hmd_fse_build_sym (norm: list Z) (log st: Z) : 0 <= fe_sym (fse_cell (fse_build norm log) st).
Proof.
  unfold fse_cell, fse_build.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [tab high] eqn:E.
  simpl.
  assert (Ht: Forall (fun x => 0 <= x) tab).
  { replace tab with (fst (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)))
      by (rewrite E; auto).
    apply hmd_place_low_nonneg. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  pose proof (hmd_states_nonneg log (spread norm log 0 (length norm) high tab 0)
                (map (fun c => if c =? -1 then 1 else c) norm) (hmd_spread_nonneg _ _ _ _ _ _ _ Ht)) as Hs.
  destruct (Nat.lt_ge_cases (Z.to_nat st) (length (states log (spread norm log 0 (length norm) high tab 0)
                (map (fun c => if c =? -1 then 1 else c) norm)))) as [Hlt | Hge].
  - rewrite Forall_forall in Hs. apply Hs. apply nth_In; auto.
  - rewrite nth_overflow by auto. simpl. lia.
Qed.

Lemma hmd_fse2_loop_nonneg (fuel: nat) (t: fse_table) (V: list Z) (pos s1 s2: Z) (acc ws: list Z) :
  (forall st, 0 <= fe_sym (fse_cell t st)) -> Forall (fun x => 0 <= x) acc ->
  fse2_loop fuel t V pos s1 s2 acc = Some ws -> Forall (fun x => 0 <= x) ws.
Proof.
  intros Hc. revert pos s1 s2 acc. induction fuel as [| f IH]; intros pos s1 s2 acc Ha H; simpl in H.
  - discriminate.
  - destruct (pos - fe_nb (fse_cell t s1) <? 0).
    + inversion H; subst. repeat (apply Forall_app; split; auto).
    + destruct (pos - fe_nb (fse_cell t s1) - fe_nb (fse_cell t s2) <? 0).
      * inversion H; subst. repeat (apply Forall_app; split; auto).
      * eapply IH; [| exact H]. repeat (apply Forall_app; split; auto).
Qed.

Lemma hmd_fse_weights (b ws: list Z) :
  huf_fse_weights b = Some ws -> Forall (fun x => 0 <= x) ws /\ Zlength ws <= 255.
Proof.
  unfold huf_fse_weights. intros H.
  destruct (read_ncount b 255) as [[[norm log] nsize] |]; [| discriminate].
  destruct (log >? 6); [discriminate |].
  match type of H with context [if ?c then None else _] => destruct c; [discriminate |] end.
  destruct (negb (bs_okb (skipn (Z.to_nat nsize) b))); [discriminate |].
  destruct (bs_total (skipn (Z.to_nat nsize) b) - 2 * log <? 0); [discriminate |].
  match type of H with context [fse2_loop ?fu ?t ?V ?p ?a ?c ?acc] =>
    destruct (fse2_loop fu t V p a c acc) as [ws' |] eqn:E; [| discriminate] end.
  destruct (Zlength ws' >? 255) eqn:E2; [discriminate |]. inversion H; subst.
  split; [| lia].
  eapply hmd_fse2_loop_nonneg; [| | exact E]; auto. intros st. apply hmd_fse_build_sym.
Qed.

(* ---------- direct weights: nibbles ---------- *)

Lemma hmd_byte_at (b: list Z) (i: Z) : bytes_ok b -> 0 <= byte_at b i < 256.
Proof.
  intros Hb. unfold byte_at.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length b)) as [Hlt | Hge].
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb. apply nth_In; auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma hmd_direct_weights (b: list Z) (oSize: Z) :
  bytes_ok b -> 0 <= oSize ->
  Forall (fun x => 0 <= x <= 15) (huf_direct_weights b oSize) /\ Zlength (huf_direct_weights b oSize) = oSize.
Proof.
  intros Hb Ho. unfold huf_direct_weights. split.
  - apply Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as [n [<- _]].
    pose proof (hmd_byte_at b (1 + Z.of_nat n / 2) Hb) as Hy.
    destruct (Nat.even n).
    + rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      split; [apply Z.div_pos; lia |].
      assert (byte_at b (1 + Z.of_nat n / 2) / 16 < 16) by (apply Z.div_lt_upper_bound; lia). lia.
    + change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. change (Z.ones 4) with 15.
      pose proof (Z.mod_pos_bound (byte_at b (1 + Z.of_nat n / 2)) 16). lia.
  - rewrite Zlength_correct, length_map, length_seq. lia.
Qed.

Lemma hmd_desc_weights (b ws: list Z) (size: Z) :
  bytes_ok b -> huf_desc_weights b = Some (ws, size) ->
  Forall (fun x => 0 <= x) ws /\ Zlength ws <= 255 /\ 1 <= size <= Zlength b.
Proof.
  intros Hb. unfold huf_desc_weights.
  destruct (Zlength b <? 1) eqn:E1; [discriminate |].
  pose proof (hmd_byte_at b 0 Hb) as Hy.
  destruct (byte_at b 0 >=? 128) eqn:E2.
  - destruct (Zlength b <? (byte_at b 0 - 127 + 1) / 2 + 1) eqn:E3; [discriminate |].
    intros H; injection H as <- <-. apply Z.ltb_ge in E3. apply Z.geb_le in E2.
    destruct (hmd_direct_weights b (byte_at b 0 - 127) Hb) as [Hf Hl]; [lia |].
    split; [| split].
    + eapply Forall_impl; [| exact Hf]. simpl. lia.
    + lia.
    + change (let (q, _) := Z.div_eucl (byte_at b 0 - 127 + 1) 2 in q) with ((byte_at b 0 - 127 + 1) / 2).
      assert (0 <= (byte_at b 0 - 127 + 1) / 2) by (apply Z.div_pos; lia). lia.
  - destruct (Zlength b <? byte_at b 0 + 1) eqn:E3; [discriminate |].
    destruct (huf_fse_weights (slice b 1 (byte_at b 0))) as [ws' |] eqn:E4; [| discriminate].
    intros H; injection H as <- <-. apply Z.ltb_ge in E3. rewrite Z.geb_leb, Z.leb_gt in E2.
    destruct (hmd_fse_weights _ _ E4). split; [auto | lia].
Qed.

(* ---------- the Kraft sum and the number of cells ---------- *)

Definition hmd_kr (w: Z) : Z := Z.shiftr (2 ^ w) 1.
Definition hmd_total (ws: list Z) : Z := fold_right (fun w acc => hmd_kr w + acc) 0 ws.

Lemma hmd_kr_pos (w: Z) : 1 <= w -> hmd_kr w = 2 ^ (w - 1).
Proof.
  intros Hw. unfold hmd_kr. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ w) with (2 ^ (w - 1) * 2 ^ 1) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.div_mul; auto. lia.
Qed.

Lemma hmd_kr_nonpos (w: Z) : w <= 0 -> hmd_kr w = 0.
Proof.
  intros Hw. unfold hmd_kr. destruct (Z.eq_dec w 0) as [-> | Hn]; [reflexivity |].
  rewrite Z.pow_neg_r by lia. reflexivity.
Qed.

Lemma hmd_kr_nonneg (w: Z) : 0 <= hmd_kr w.
Proof.
  destruct (Z_le_gt_dec w 0); [rewrite hmd_kr_nonpos by lia; lia | rewrite hmd_kr_pos by lia].
  apply Z.pow_nonneg; lia.
Qed.

Lemma hmd_total_nonneg (ws: list Z) : 0 <= hmd_total ws.
Proof. induction ws; simpl; [lia |]. pose proof (hmd_kr_nonneg a). lia. Qed.

Lemma hmd_total_in (ws: list Z) (w: Z) : In w ws -> hmd_kr w <= hmd_total ws.
Proof.
  induction ws as [| a ws IH]; simpl; [tauto |]. intros [-> | Hi].
  - pose proof (hmd_total_nonneg ws). lia.
  - pose proof (hmd_kr_nonneg a). specialize (IH Hi). lia.
Qed.

Lemma hmd_total_app (l1 l2: list Z) : hmd_total (l1 ++ l2) = hmd_total l1 + hmd_total l2.
Proof. induction l1; simpl; [lia |]. unfold hmd_total in *. lia. Qed.

Lemma hmd_sum_add {A} (f g: A -> nat) (l: list A) :
  list_sum (map (fun x => (f x + g x)%nat) l) = (list_sum (map f l) + list_sum (map g l))%nat.
Proof. induction l; simpl; lia. Qed.

Lemma hmd_sum_swap {A B} (f: A -> B -> nat) (la: list A) (lb: list B) :
  list_sum (map (fun a => list_sum (map (fun b => f a b) lb)) la) =
  list_sum (map (fun b => list_sum (map (fun a => f a b) la)) lb).
Proof.
  induction la as [| a la IH]; simpl.
  - induction lb; simpl; auto.
  - rewrite IH. rewrite (hmd_sum_add (fun b => f a b) (fun b => list_sum (map (fun a0 => f a0 b) la))). auto.
Qed.

Lemma hmd_sum_one (x: Z) (v: nat) (m a: nat) :
  list_sum (map (fun w => if x =? Z.of_nat w then v else 0%nat) (seq a m)) =
  if andb (Z.of_nat a <=? x) (x <? Z.of_nat (a + m)) then v else 0%nat.
Proof.
  revert a. induction m as [| m IH]; intros a; simpl.
  - destruct (Z.leb_spec (Z.of_nat a) x), (Z.ltb_spec x (Z.of_nat (a + 0))); simpl; auto; lia.
  - rewrite IH.
    destruct (Z.eqb_spec x (Z.of_nat a)), (Z.leb_spec (Z.of_nat a) x), (Z.ltb_spec x (Z.of_nat (a + S m))),
      (Z.leb_spec (Z.of_nat (S a)) x), (Z.ltb_spec x (Z.of_nat (S a + m))); simpl; lia.
Qed.

Lemma hmd_map_nth_seq {A} (f: A -> nat) (ws: list A) (d: A) :
  map (fun s => f (nth s ws d)) (seq 0 (length ws)) = map f ws.
Proof.
  induction ws as [| a ws IH]; simpl; auto. f_equal.
  rewrite <- seq_shift, map_map. simpl. exact IH.
Qed.

Lemma hmd_cells_length (t: huf_table) :
  Forall (fun w => w <= ht_log t) (ht_weights t) -> Zlength (huf_cells t) = hmd_total (ht_weights t).
Proof.
  intros Hw. unfold huf_cells. rewrite Zlength_correct, length_flat_map, map_map.
  set (ws := ht_weights t). set (log := ht_log t). fold ws in Hw. fold log in Hw.
  set (c := fun (w: nat) (s: nat) =>
              if nth s ws 0 =? Z.of_nat w then Z.to_nat (2 ^ (Z.of_nat w - 1)) else 0%nat).
  transitivity (Z.of_nat (list_sum (map (fun w => list_sum (map (fun s => c w s) (seq 0 (length ws))))
                                     (seq 1 (Z.to_nat log))))).
  { f_equal. f_equal. apply map_ext. intros w. rewrite length_flat_map. f_equal. apply map_ext. intros s.
    unfold c. destruct (nth s ws 0 =? Z.of_nat w); simpl; [apply repeat_length | auto]. }
  rewrite hmd_sum_swap.
  transitivity (Z.of_nat (list_sum (map (fun s => Z.to_nat (hmd_kr (nth s ws 0))) (seq 0 (length ws))))).
  { f_equal. f_equal. apply map_ext_in. intros s Hs. apply in_seq in Hs.
    set (x := nth s ws 0).
    assert (Hx: x <= log). { rewrite Forall_forall in Hw. apply Hw. apply nth_In. lia. }
    unfold c. fold x.
    rewrite (map_ext (fun a => if x =? Z.of_nat a then Z.to_nat (2 ^ (Z.of_nat a - 1)) else 0%nat)
                     (fun a => if x =? Z.of_nat a then Z.to_nat (2 ^ (x - 1)) else 0%nat)).
    2: { intros a. destruct (Z.eqb_spec x (Z.of_nat a)) as [-> | ]; auto. }
    rewrite hmd_sum_one.
    destruct (Z.leb_spec (Z.of_nat 1) x), (Z.ltb_spec x (Z.of_nat (1 + Z.to_nat log))); simpl.
    - rewrite hmd_kr_pos by lia. auto.
    - lia.
    - rewrite hmd_kr_nonpos by lia. auto.
    - rewrite hmd_kr_nonpos by lia. auto. }
  rewrite (hmd_map_nth_seq (fun w => Z.to_nat (hmd_kr w))).
  clear. induction ws as [| a ws IH]; simpl; auto.
  rewrite Nat2Z.inj_add, IH, Z2Nat.id by apply hmd_kr_nonneg. auto.
Qed.

Lemma hmd_cells_in (t: huf_table) (c: Z * Z) :
  In c (huf_cells t) -> 0 <= fst c < Z.of_nat (length (ht_weights t)) /\ 1 <= snd c <= ht_log t.
Proof.
  unfold huf_cells. intros H. apply in_flat_map in H. destruct H as [w [Hw H]].
  apply in_flat_map in H. destruct H as [s [Hs H]].
  destruct (nth s (ht_weights t) 0 =? w); [| destruct H].
  apply repeat_spec in H. subst c. apply in_map_iff in Hw. destruct Hw as [n [<- Hn]].
  apply in_seq in Hn. apply in_seq in Hs. simpl. lia.
Qed.

Lemma huf_parse_desc_facts (s: list Z) (ht: huf_table) (h: Z) :
  bytes_ok s -> huf_parse_desc s = Some (ht, h) ->
  huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\
  Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht) /\ 1 <= h <= Zlength s.
Proof.
  intros Hb H. unfold huf_parse_desc in H.
  destruct (huf_desc_weights s) as [[ws0 size] |] eqn:Ed; [| discriminate].
  destruct (hmd_desc_weights _ _ _ Hb Ed) as (Hn & Hl & Hh).
  destruct (existsb (fun w => w >? HUF_TABLELOG_MAX) ws0) eqn:Ex; [discriminate |].
  cbv zeta in H. change (fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 ws0) with (hmd_total ws0) in H.
  unfold highbit in H.
  set (T := hmd_total ws0) in H. set (L := Z.log2 T + 1) in H. set (R := 2 ^ L - T) in H.
  destruct (Z.eqb_spec T 0); [discriminate |].
  destruct (L >? HUF_TABLELOG_MAX) eqn:E1; [discriminate |].
  rewrite Z.gtb_ltb, Z.ltb_ge in E1. unfold HUF_TABLELOG_MAX in E1.
  destruct (negb (2 ^ Z.log2 R =? R)) eqn:E2; [discriminate |].
  apply negb_false_iff, Z.eqb_eq in E2.
  match type of H with (if ?c then _ else _) = _ => destruct c; [discriminate |] end.
  injection H as <- <-. simpl.
  assert (Hw12: Forall (fun w => w <= 12) ws0).
  { apply Forall_forall. intros w Hi. destruct (Z_le_gt_dec w 12) as [| Hg]; auto. exfalso.
    assert (existsb (fun w => w >? HUF_TABLELOG_MAX) ws0 = true) as Ht.
    { apply existsb_exists. exists w. split; auto. unfold HUF_TABLELOG_MAX. apply Z.gtb_lt. lia. }
    congruence. }
  pose proof (hmd_total_nonneg ws0) as HT0. fold T in HT0.
  assert (HTp: 0 < T) by lia.
  pose proof (Z.log2_spec T HTp) as [HT1 HT2]. pose proof (Z.log2_nonneg T) as HL0.
  replace (Z.succ (Z.log2 T)) with L in HT2 by (unfold L; lia).
  assert (HLp: 2 ^ L = 2 * 2 ^ (L - 1)).
  { replace L with (Z.succ (L - 1)) at 1 by lia. apply Z.pow_succ_r. lia. }
  replace (Z.log2 T) with (L - 1) in HT1 by (unfold L; lia).
  assert (HR: 0 < R <= 2 ^ (L - 1)) by (unfold R; lia).
  pose proof (Z.log2_nonneg R) as HR0.
  assert (HRl: Z.log2 R <= L - 1).
  { rewrite <- (Z.log2_pow2 (L - 1)) by lia. apply Z.log2_le_mono. lia. }
  assert (HwL: Forall (fun w => 0 <= w <= L) (ws0 ++ [Z.log2 R + 1])).
  { apply Forall_app. split; [| constructor; [lia | constructor]].
    apply Forall_forall. intros w Hi. rewrite Forall_forall in Hn. specialize (Hn w Hi).
    split; auto. destruct (Z_le_gt_dec w L) as [| Hg]; auto. exfalso.
    pose proof (hmd_total_in ws0 w Hi) as Hk. fold T in Hk. rewrite hmd_kr_pos in Hk by lia.
    assert (2 ^ L <= 2 ^ (w - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hne: ws0 <> nil) by (intros ->; apply n; reflexivity).
  assert (Hl1: 1 <= Zlength ws0).
  { destruct ws0; [congruence |]. rewrite Zlength_cons. pose proof (Zlength_nonneg ws0). lia. }
  split; [| split; [| split]].
  - unfold huf_ok, HUF_TABLELOG_MAX. simpl. split; [lia |]. split.
    + rewrite hmd_cells_length.
      2: { simpl. eapply Forall_impl; [| exact HwL]. simpl. lia. }
      simpl. rewrite hmd_total_app. simpl. rewrite hmd_kr_pos by lia.
      replace (Z.log2 R + 1 - 1) with (Z.log2 R) by lia. rewrite E2. fold T. unfold R. lia.
    + apply Forall_forall. intros c Hc. apply hmd_cells_in in Hc. simpl in Hc.
      rewrite length_app in Hc. simpl in Hc. rewrite Zlength_correct in Hl. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - exact HwL.
  - exact Hh.
Qed.
