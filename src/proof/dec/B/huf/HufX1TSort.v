(* Sub-group X1T: statement 9 of HUF_readDTableX1_wksp (rankStart, then the
   symbols sorted by weight). *)
Require Export Zstd.proof.dec.B.huf.HufX1TSpecs.
Local Open Scope logic.

(* ---------- the model of the counting sort ---------- *)

(* the number of weights w in ws *)
Definition x1_cnt (ws: list Z) (w: Z) : Z := Zlength (filter (fun x => x =? w) ws).

(* the first position of weight w in x1_sorted ws: the number of weights < w (w >= 0) *)
Definition x1_start (ws: list Z) (w: Z) : Z :=
  fold_right Z.add 0 (map (fun v => x1_cnt ws (Z.of_nat v)) (seq 0 (Z.to_nat w))).

(* wksp->symbols once the symbols < i are placed: position p holds x1_sorted's entry when that entry is < i *)
Definition x1_syms (ws: list Z) (i: Z) : list val :=
  map (fun p => if andb (p <? Zlength ws) (Znth p (x1_sorted ws) <? i) then vint (Znth p (x1_sorted ws)) else Vundef)
      (map Z.of_nat (seq 0 256)).

(* ---------- helpers: x1_sorted is a permutation of 0..len-1, block by block ---------- *)

Definition x1_blk (ws: list Z) (w: Z) : list Z :=
  map Z.of_nat (filter (fun s => nth s ws 0 =? w) (seq 0 (length ws))).

Lemma x1_flat_map_app {A B: Type} (f: A -> list B) (l1 l2: list A) :
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. induction l1 as [|a l1 IH]; simpl; auto. rewrite IH, app_assoc. reflexivity. Qed.

Lemma x1_filter_map_len {A B: Type} (p: B -> bool) (g: A -> B) (l: list A) :
  length (filter (fun s => p (g s)) l) = length (filter p (map g l)).
Proof. induction l as [|a l IH]; simpl; auto. destruct (p (g a)); simpl; auto. Qed.

Lemma x1_map_nth_seq (ws: list Z) (k: nat) :
  (k <= length ws)%nat -> map (fun s => nth s ws 0) (seq 0 k) = firstn k ws.
Proof.
  revert k; induction ws as [|a ws IH]; intros k Hk.
  - simpl in Hk. assert (k = O) by lia. subst. reflexivity.
  - destruct k as [|k]; [reflexivity|]. simpl in Hk.
    simpl. rewrite <- seq_shift, map_map. f_equal. apply IH. lia.
Qed.

Lemma x1_prefix_cnt (ws: list Z) (w: Z) (k: nat) :
  (k <= length ws)%nat ->
  Zlength (filter (fun s => nth s ws 0 =? w) (seq 0 k)) = x1_cnt (firstn k ws) w.
Proof.
  intros Hk. unfold x1_cnt. rewrite !Zlength_correct. f_equal.
  rewrite (x1_filter_map_len (fun x => x =? w) (fun s => nth s ws 0)).
  rewrite x1_map_nth_seq by auto. reflexivity.
Qed.

Lemma x1_blk_len (ws: list Z) (w: Z) : Zlength (x1_blk ws w) = x1_cnt ws w.
Proof.
  unfold x1_blk. rewrite Zlength_map, x1_prefix_cnt by lia. rewrite firstn_all. reflexivity.
Qed.

Lemma x1_flat_len (ws: list Z) (l: list nat) :
  Zlength (flat_map (x1_blk ws) (map Z.of_nat l)) = fold_right Z.add 0 (map (fun v => x1_cnt ws (Z.of_nat v)) l).
Proof.
  induction l as [|a l IH]; simpl; auto. rewrite Zlength_app, IH, x1_blk_len. reflexivity.
Qed.

Lemma x1_blk_In (ws: list Z) (w x: Z) :
  In x (x1_blk ws w) <-> exists s, x = Z.of_nat s /\ (s < length ws)%nat /\ nth s ws 0 = w.
Proof.
  unfold x1_blk. rewrite in_map_iff. split.
  - intros [s [Hx Hin]]. rewrite filter_In, in_seq, Z.eqb_eq in Hin. exists s. split; [auto|lia].
  - intros [s [Hx [Hs Hw]]]. exists s. split; [auto|]. rewrite filter_In, in_seq, Z.eqb_eq. split; [lia|auto].
Qed.

Lemma x1_blk_NoDup (ws: list Z) (w: Z) : NoDup (x1_blk ws w).
Proof.
  unfold x1_blk. apply FinFun.Injective_map_NoDup.
  - intros a b H. lia.
  - apply NoDup_filter, seq_NoDup.
Qed.

Lemma x1_flat_NoDup (ws: list Z) (ks: list Z) : NoDup ks -> NoDup (flat_map (x1_blk ws) ks).
Proof.
  induction ks as [|k ks IH]; intros Hnd; simpl; [constructor|].
  inversion Hnd as [|? ? Hnk Hks]; subst.
  apply NoDup_app_iff. split; [apply x1_blk_NoDup|]. split; [auto|].
  intros x Hx1 Hx2.
  rewrite in_flat_map in Hx2. destruct Hx2 as [k' [Hk' Hx2]].
  rewrite x1_blk_In in Hx1, Hx2. destruct Hx1 as [s [-> [_ Hs]]]. destruct Hx2 as [s' [Hx [_ Hs']]].
  assert (s = s') by lia. subst. congruence.
Qed.

Lemma x1_sorted_eq (ws: list Z) : x1_sorted ws = flat_map (x1_blk ws) (map Z.of_nat (seq 0 13)).
Proof. reflexivity. Qed.

Lemma x1_sorted_In (ws: list Z) (x: Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws ->
  In x (x1_sorted ws) <-> In x (map Z.of_nat (seq 0 (length ws))).
Proof.
  intros Hf. rewrite x1_sorted_eq, in_flat_map, in_map_iff. split.
  - intros [w [_ H]]. rewrite x1_blk_In in H. destruct H as [s [-> [Hs _]]].
    exists s. rewrite in_seq. split; [auto|lia].
  - intros [s [<- Hs]]. rewrite in_seq in Hs.
    assert (Hw: 0 <= nth s ws 0 <= 12).
    { rewrite Forall_forall in Hf. apply (Hf (nth s ws 0)). apply nth_In. lia. }
    exists (nth s ws 0). split.
    + rewrite in_map_iff. exists (Z.to_nat (nth s ws 0)). rewrite in_seq. split; lia.
    + rewrite x1_blk_In. exists s. split; [auto|]. split; [lia|auto].
Qed.

Lemma x1_sorted_perm (ws: list Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws ->
  Permutation (x1_sorted ws) (map Z.of_nat (seq 0 (length ws))).
Proof.
  intros Hf. apply NoDup_Permutation.
  - rewrite x1_sorted_eq. apply x1_flat_NoDup. apply FinFun.Injective_map_NoDup.
    + intros a b H. lia.
    + apply seq_NoDup.
  - apply FinFun.Injective_map_NoDup; [intros a b H; lia | apply seq_NoDup].
  - intros x. apply x1_sorted_In; auto.
Qed.

Lemma x1_sorted_len (ws: list Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws -> Zlength (x1_sorted ws) = Zlength ws.
Proof.
  intros Hf. rewrite !Zlength_correct, (Permutation_length (x1_sorted_perm ws Hf)), map_length, seq_length.
  reflexivity.
Qed.

Lemma x1_sorted_range (ws: list Z) (p: Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws -> 0 <= p < Zlength ws ->
  0 <= Znth p (x1_sorted ws) < Zlength ws.
Proof.
  intros Hf Hp.
  assert (Hin: In (Znth p (x1_sorted ws)) (x1_sorted ws)).
  { apply Znth_In. rewrite x1_sorted_len; auto. }
  rewrite x1_sorted_In in Hin by auto. rewrite in_map_iff in Hin. destruct Hin as [s [Hs Hin]].
  rewrite in_seq in Hin. rewrite <- Hs, Zlength_correct. lia.
Qed.

Lemma x1_sorted_inj (ws: list Z) (p p': Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws -> 0 <= p < Zlength ws -> 0 <= p' < Zlength ws ->
  Znth p (x1_sorted ws) = Znth p' (x1_sorted ws) -> p = p'.
Proof.
  intros Hf Hp Hp' H.
  assert (Hnd: NoDup (x1_sorted ws)).
  { rewrite x1_sorted_eq. apply x1_flat_NoDup. apply FinFun.Injective_map_NoDup; [intros a b E; lia | apply seq_NoDup]. }
  rewrite <- (x1_sorted_len ws Hf) in Hp, Hp'.
  rewrite <- !nth_Znth in H by lia. rewrite Zlength_correct in Hp, Hp'.
  pose proof (proj1 (NoDup_nth (x1_sorted ws) 0) Hnd (Z.to_nat p) (Z.to_nat p')) as E.
  assert (Z.to_nat p = Z.to_nat p') by (apply E; [lia|lia|auto]). lia.
Qed.

Lemma x1_q_facts (ws: list Z) (i: Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws -> 0 <= i < Zlength ws ->
  let q := x1_start ws (Znth i ws) + x1_cnt (sublist 0 i ws) (Znth i ws) in
  0 <= q < Zlength ws /\ Znth q (x1_sorted ws) = i.
Proof.
  intros Hf Hi q.
  set (w := Znth i ws).
  assert (Hw: 0 <= w <= 12).
  { rewrite Forall_forall in Hf. apply (Hf w). subst w. apply Znth_In. lia. }
  assert (Hseq13: seq 0 13 = seq 0 (Z.to_nat w) ++ Z.to_nat w :: seq (S (Z.to_nat w)) (12 - Z.to_nat w)).
  { replace 13%nat with (Z.to_nat w + S (12 - Z.to_nat w))%nat at 1 by lia. rewrite seq_app. reflexivity. }
  rewrite Zlength_correct in Hi.
  assert (Hseqn: seq 0 (length ws) = seq 0 (Z.to_nat i) ++ Z.to_nat i :: seq (S (Z.to_nat i)) (length ws - S (Z.to_nat i))).
  { replace (length ws) with (Z.to_nat i + S (length ws - S (Z.to_nat i)))%nat at 1 by lia. rewrite seq_app. reflexivity. }
  assert (Hwi: nth (Z.to_nat i) ws 0 = w).
  { subst w. rewrite <- nth_Znth by (rewrite Zlength_correct; lia). reflexivity. }
  set (F := flat_map (x1_blk ws) (map Z.of_nat (seq 0 (Z.to_nat w)))).
  set (R := flat_map (x1_blk ws) (map Z.of_nat (seq (S (Z.to_nat w)) (12 - Z.to_nat w)))).
  set (A := map Z.of_nat (filter (fun s => nth s ws 0 =? w) (seq 0 (Z.to_nat i)))).
  set (B := map Z.of_nat (filter (fun s => nth s ws 0 =? w) (seq (S (Z.to_nat i)) (length ws - S (Z.to_nat i))))).
  assert (Hs: x1_sorted ws = F ++ A ++ i :: B ++ R).
  { rewrite x1_sorted_eq, Hseq13, map_app, x1_flat_map_app. subst F. f_equal.
    simpl. rewrite Z2Nat.id by lia. unfold x1_blk at 1. rewrite Hseqn, filter_app. simpl.
    rewrite Hwi, Z.eqb_refl, map_app. simpl. rewrite Z2Nat.id by lia. rewrite <- app_assoc. reflexivity. }
  assert (HF: Zlength F = x1_start ws w) by (subst F; rewrite x1_flat_len; reflexivity).
  assert (HA: Zlength A = x1_cnt (sublist 0 i ws) w).
  { subst A. rewrite Zlength_map, x1_prefix_cnt by lia. rewrite sublist_firstn. reflexivity. }
  assert (Hlen: Zlength (x1_sorted ws) = Zlength ws) by (apply x1_sorted_len; auto).
  rewrite Hs in Hlen. rewrite !Zlength_app, Zlength_cons, Zlength_app in Hlen.
  rewrite <- Zlength_correct in Hi.
  pose proof (Zlength_nonneg F). pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B).
  pose proof (Zlength_nonneg R).
  subst q. fold w. split; [lia|].
  rewrite Hs, app_Znth2 by lia. rewrite app_Znth2 by lia.
  replace (x1_start ws w + x1_cnt (sublist 0 i ws) w - Zlength F - Zlength A) with 0 by lia.
  apply Znth_0_cons.
Qed.

Lemma x1_Znth_syms (ws: list Z) (i p: Z) : 0 <= p < 256 ->
  Znth p (x1_syms ws i) =
  if andb (p <? Zlength ws) (Znth p (x1_sorted ws) <? i) then vint (Znth p (x1_sorted ws)) else Vundef.
Proof.
  intros Hp. unfold x1_syms. rewrite Znth_map.
  2: { rewrite Zlength_map, Zlength_correct, seq_length. lia. }
  rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. simpl Nat.add. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma x1_syms_len (ws: list Z) (i: Z) : Zlength (x1_syms ws i) = 256.
Proof. unfold x1_syms. rewrite !Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

(* the facts the loops need: no symbol placed, placing symbol i (of weight w) at rankStart[w], all placed *)
Lemma x1_syms_model (ws: list Z) :
  Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) ws -> Zlength ws <= 256 ->
  x1_syms ws 0 = Zrepeat Vundef 256 /\
  (forall i, 0 <= i < Zlength ws ->
     let q := x1_start ws (Znth i ws) + x1_cnt (sublist 0 i ws) (Znth i ws) in
     0 <= q < Zlength ws /\ upd_Znth q (x1_syms ws i) (vint i) = x1_syms ws (i + 1)) /\
  x1_syms ws (Zlength ws) = map (fun s => vint s) (x1_sorted ws) ++ Zrepeat Vundef (256 - Zlength ws).
Proof.
  intros Hf Hn. split; [|split].
  - apply Znth_eq_ext.
    { rewrite x1_syms_len, Zlength_Zrepeat; lia. }
    intros p Hp. rewrite x1_syms_len in Hp. rewrite x1_Znth_syms by lia. rewrite Znth_Zrepeat by lia.
    destruct (p <? Zlength ws) eqn:E; simpl; auto.
    rewrite Z.ltb_lt in E. pose proof (x1_sorted_range ws p Hf ltac:(lia)).
    destruct (Znth p (x1_sorted ws) <? 0) eqn:E2; auto. rewrite Z.ltb_lt in E2. lia.
  - intros i Hi q. destruct (x1_q_facts ws i Hf Hi) as [Hq Hqi]. fold q in Hq, Hqi.
    split; auto.
    apply Znth_eq_ext.
    { rewrite upd_Znth_Zlength by (rewrite x1_syms_len; lia). rewrite !x1_syms_len. reflexivity. }
    intros p Hp. rewrite upd_Znth_Zlength in Hp by (rewrite x1_syms_len; lia). rewrite x1_syms_len in Hp.
    rewrite x1_Znth_syms by lia.
    destruct (Z.eq_dec p q) as [->|Hne].
    + rewrite upd_Znth_same by (rewrite x1_syms_len; lia). rewrite Hqi.
      replace (q <? Zlength ws) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (i <? i + 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?x1_syms_len; lia). rewrite x1_Znth_syms by lia.
      destruct (p <? Zlength ws) eqn:E; simpl; auto.
      rewrite Z.ltb_lt in E.
      assert (Znth p (x1_sorted ws) <> i).
      { intros E2. apply Hne. apply (x1_sorted_inj ws p q Hf); [lia|lia|congruence]. }
      destruct (Znth p (x1_sorted ws) <? i) eqn:E3; destruct (Znth p (x1_sorted ws) <? i + 1) eqn:E4; auto;
        rewrite ?Z.ltb_lt, ?Z.ltb_ge in E3, E4; lia.
  - apply Znth_eq_ext.
    { rewrite x1_syms_len, Zlength_app, Zlength_map, Zlength_Zrepeat, x1_sorted_len by (auto; lia). lia. }
    intros p Hp. rewrite x1_syms_len in Hp. rewrite x1_Znth_syms by lia.
    pose proof (x1_sorted_len ws Hf) as Hl.
    destruct (p <? Zlength ws) eqn:E; simpl.
    + rewrite Z.ltb_lt in E. pose proof (x1_sorted_range ws p Hf ltac:(lia)).
      replace (Znth p (x1_sorted ws) <? Zlength ws) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
    + rewrite Z.ltb_ge in E. rewrite app_Znth2 by (rewrite Zlength_map; lia).
      rewrite Znth_Zrepeat by (rewrite Zlength_map; lia). reflexivity.
Qed.

Definition x1_upto (n: Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma x1_upto_len (n: Z) : 0 <= n -> Zlength (x1_upto n) = n.
Proof. intros. unfold x1_upto. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma x1_upto_S (n: Z) : 0 <= n -> x1_upto (n + 1) = x1_upto n ++ [n].
Proof.
  intros. unfold x1_upto. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite seq_S, map_app. simpl. f_equal. f_equal. lia.
Qed.

Lemma x1_upto_Znth (n i: Z) : 0 <= i < n -> Znth i (x1_upto n) = i.
Proof.
  intros. unfold x1_upto. rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. simpl. lia.
Qed.

Lemma x1_start_0 (ws: list Z) : x1_start ws 0 = 0.
Proof. reflexivity. Qed.

Lemma x1_start_S (ws: list Z) (w: Z) : 0 <= w -> x1_start ws (w + 1) = x1_start ws w + x1_cnt ws w.
Proof.
  intros. unfold x1_start. replace (Z.to_nat (w + 1)) with (S (Z.to_nat w)) by lia.
  rewrite seq_S, map_app, fold_right_app. simpl.
  rewrite Z2Nat.id by lia.
  generalize (map (fun v : nat => x1_cnt ws (Z.of_nat v)) (seq 0 (Z.to_nat w))).
  induction l; simpl; lia.
Qed.

Lemma x1_rank_stats_Znth {d: Inhabitant val} (ws: list Z) (w: Z) : 0 <= w < 13 -> @Znth val d w (rank_stats ws) = vint (x1_cnt ws w).
Proof.
  intros. unfold rank_stats. rewrite Znth_map by (rewrite Zlength_correct, seq_length; lia).
  rewrite <- nth_Znth by (rewrite Zlength_correct, seq_length; lia).
  rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma x1_rs1_upd (f: Z -> val) (n: Z) : 0 <= n < 13 ->
  upd_Znth n (map f (x1_upto n) ++ Zrepeat Vundef (13 - n)) (f n) =
  map f (x1_upto (n + 1)) ++ Zrepeat Vundef (13 - (n + 1)).
Proof.
  intros. rewrite x1_upto_S by lia. rewrite map_app, <- app_assoc.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, x1_upto_len, Zlength_Zrepeat; lia).
  rewrite Zlength_map, x1_upto_len by lia. replace (n - n) with 0 by lia.
  f_equal. replace (13 - n) with (1 + (13 - (n + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  reflexivity.
Qed.

(* wksp->rankStart once the symbols < i are placed (weights <= L; entries above L were never written) *)
Definition x1_rs (ws: list Z) (L i: Z) : list val :=
  map (fun w => vint (x1_start ws w + x1_cnt (sublist 0 i ws) w)) (x1_upto (L + 1)) ++ Zrepeat Vundef (12 - L).

Lemma x1_cnt_nil (w: Z) : x1_cnt [] w = 0.
Proof. reflexivity. Qed.

Lemma x1_cnt_app (l1 l2: list Z) (w: Z) : x1_cnt (l1 ++ l2) w = x1_cnt l1 w + x1_cnt l2 w.
Proof. unfold x1_cnt. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma x1_cnt_snoc (ws: list Z) (i v: Z) : 0 <= i < Zlength ws ->
  x1_cnt (sublist 0 (i + 1) ws) v = x1_cnt (sublist 0 i ws) v + (if Znth i ws =? v then 1 else 0).
Proof.
  intros. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite x1_cnt_app.
  rewrite sublist_len_1 by lia. f_equal. unfold x1_cnt. simpl.
  destruct (Znth i ws =? v); reflexivity.
Qed.

Lemma x1_rs_0 (ws: list Z) (L: Z) : 0 <= L ->
  map (fun w => vint (x1_start ws w)) (x1_upto (L + 1)) ++ Zrepeat Vundef (13 - (L + 1)) = x1_rs ws L 0.
Proof.
  intros. unfold x1_rs. rewrite sublist_nil. f_equal.
  - apply map_ext. intros. rewrite x1_cnt_nil, Z.add_0_r. reflexivity.
  - f_equal. lia.
Qed.

Lemma x1_rs_Znth {d: Inhabitant val} (ws: list Z) (L i w: Z) : 0 <= w <= L ->
  @Znth val d w (x1_rs ws L i) = vint (x1_start ws w + x1_cnt (sublist 0 i ws) w).
Proof.
  intros. unfold x1_rs. rewrite Znth_app1 by (rewrite Zlength_map, x1_upto_len; lia).
  rewrite Znth_map by (rewrite x1_upto_len; lia). rewrite x1_upto_Znth by lia. reflexivity.
Qed.

Lemma x1_rs_step (ws: list Z) (L i: Z) : 0 <= i < Zlength ws -> 0 <= Znth i ws <= L ->
  upd_Znth (Znth i ws) (x1_rs ws L i)
    (vint (x1_start ws (Znth i ws) + x1_cnt (sublist 0 i ws) (Znth i ws) + 1)) = x1_rs ws L (i + 1).
Proof.
  intros. unfold x1_rs. rewrite upd_Znth_app1 by (rewrite Zlength_map, x1_upto_len; lia). f_equal.
  apply Znth_eq_ext. { rewrite Zlength_upd_Znth, !Zlength_map. reflexivity. }
  intros j Hj. rewrite Zlength_upd_Znth, Zlength_map, x1_upto_len in Hj by lia.
  rewrite Znth_map by (rewrite x1_upto_len; lia). rewrite x1_upto_Znth by lia.
  rewrite x1_cnt_snoc by lia.
  destruct (Z.eq_dec j (Znth i ws)).
  - subst j. rewrite upd_Znth_same by (rewrite Zlength_map, x1_upto_len; lia). rewrite Z.eqb_refl. do 2 f_equal. lia.
  - rewrite upd_Znth_diff by (rewrite ?Zlength_map, ?x1_upto_len; lia).
    rewrite Znth_map by (rewrite x1_upto_len; lia). rewrite x1_upto_Znth by lia.
    replace (Znth i ws =? j) with false by (symmetry; apply Z.eqb_neq; lia). do 2 f_equal. lia.
Qed.

Lemma x1_hw_Znth {d: Inhabitant val} (ws: list Z) (wr: list val) (i: Z) : 0 <= i < Zlength ws ->
  @Znth val d i (zbytes ws ++ wr) = vint (Znth i ws).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma x1_sort : x1_sort_ok.
Proof.
  unfold x1_sort_ok; intros.
  unfold HUF_TABLELOG_MAX in H0.
  unfold x1_Delta, x1_sort_stmt.
  simplify_func_tycontext.
  abbreviate_semax.
  forward.
  forward.
  forward.
  forward.
  forward.
  set (nL := Int.add (Int.sub (Int.repr (Zlength rws)) (Int.repr 4)) (Int.repr 1)).
  forward_loop
    (EX n: Z,
     PROP (0 <= n <= L + 1)
     LOCAL (temp _n (vint n); temp _nLimit (Vint nL); temp _unroll (vint 4);
            temp _nextRankStart (vint (x1_start rws n));
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart)
            (map (fun w => vint (x1_start rws w)) (x1_upto n) ++ Zrepeat Vundef (13 - n)) pk;
          field_at_ shk t_x1wksp (DOT _symbols) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  continue:
    (EX n: Z,
     PROP (0 <= n < L + 1)
     LOCAL (temp _n (vint n); temp _nLimit (Vint nL); temp _unroll (vint 4);
            temp _nextRankStart (vint (x1_start rws (n + 1)));
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart)
            (map (fun w => vint (x1_start rws w)) (x1_upto (n + 1)) ++ Zrepeat Vundef (13 - (n + 1))) pk;
          field_at_ shk t_x1wksp (DOT _symbols) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  break:
    (PROP ()
     LOCAL (temp _nLimit (Vint nL); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart)
            (map (fun w => vint (x1_start rws w)) (x1_upto (L + 1)) ++ Zrepeat Vundef (13 - (L + 1))) pk;
          field_at_ shk t_x1wksp (DOT _symbols) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F)).
  { Exists 0. entailer!. unfold field_at_. simpl app. apply derives_refl. }
  { Intros n. forward. forward_if.
    2: { forward. entailer!. replace n with (L + 1) by lia. apply derives_refl. }
    assert (Hn: 0 <= n < L + 1) by lia.
    forward. forward.
    { entailer!. rewrite x1_rank_stats_Znth by lia. exact I. }
    rewrite x1_rank_stats_Znth by lia.
    forward. forward.
    Exists n.
    rewrite (x1_rs1_upd (fun w => vint (x1_start rws w))) by lia.
    entailer!.
    rewrite x1_start_S by lia. auto. }
  { Intros n. forward. Exists (n + 1). entailer!. }
  rewrite x1_rs_0 by lia.
  assert (HF: Forall (fun w => 0 <= w <= HUF_TABLELOG_MAX) rws).
  { eapply Forall_impl; [|exact H3]. unfold HUF_TABLELOG_MAX. simpl. lia. }
  destruct (x1_syms_model rws HF ltac:(lia)) as (Hm0 & Hm1 & Hm2).
  assert (HnL: nL = Int.repr (Zlength rws - 3)).
  { unfold nL. rewrite sub_repr, add_repr. f_equal. lia. }
  clearbody nL. subst nL.
  forward.
  forward_loop
    (EX n: Z,
     PROP (0 <= n <= Zlength rws)
     LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  continue:
    (EX n: Z,
     PROP (0 <= n; n + 4 <= Zlength rws)
     LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n + 4)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n + 4)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  break:
    (EX n: Z,
     PROP (0 <= n <= Zlength rws)
     LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert.
  { Exists 0. entailer!. }
  { Intros n. forward_if.
    2: { forward. Exists n. entailer!. }
    forward.
    forward_loop
      (EX u: Z,
       PROP (0 <= u <= 4)
       LOCAL (temp _u (vint u); temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n + u)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n + u)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
    continue:
      (EX u: Z,
       PROP (0 <= u < 4)
       LOCAL (temp _u (vint u); temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n + u + 1)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n + u + 1)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
    break:
      (PROP ()
       LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n + 4)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n + 4)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert.
    { Exists 0. rewrite !Z.add_0_r. entailer!. }
    { Intros u. forward_if.
      2: { forward. entailer!. replace u with 4 by lia. apply derives_refl. }
      assert (Hi: 0 <= n + u < Zlength rws) by lia.
      assert (Hw: 0 <= Znth (n + u) rws <= L) by (apply (proj1 (Forall_Znth _ _) H3); exact Hi).
      destruct (Hm1 (n + u) Hi) as [Hq Hstep].
      forward.
      { entailer!. rewrite x1_hw_Znth by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_hw_Znth by lia.
      forward.
      rewrite Int.unsigned_repr by rep_lia.
      pose proof (x1_rs_step rws L (n + u) Hi Hw) as Hrs.
      set (w := Znth (n + u) rws) in *.
      set (q := x1_start rws w + x1_cnt (sublist 0 (n + u) rws) w) in *.
      forward.
      { entailer!. rewrite x1_rs_Znth by lia. exact I. }
      rewrite x1_rs_Znth by lia. fold q.
      forward.
      forward.
      Exists u.
      assert (Hz: Int.zero_ext 8 (Int.repr (n + u)) = Int.repr (n + u)).
      { apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia. }
      rewrite !add_repr, !Hz, Hstep, Hrs.
      entailer!. }
    { Intros u. forward. Exists (u + 1). entailer!. rewrite Z.add_assoc. apply derives_refl. }
    Exists n. entailer!. }
  { Intros n. forward. Exists (n + 4). entailer!. }
  Intros n.
  forward_loop
    (EX n: Z,
     PROP (0 <= n <= Zlength rws)
     LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  continue:
    (EX n: Z,
     PROP (0 <= n < Zlength rws)
     LOCAL (temp _n (vint n); temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (n + 1)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (n + 1)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert
  break:
    (PROP ()
     LOCAL (temp _nLimit (vint (Zlength rws - 3)); temp _unroll (vint 4);
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _rankStart) (x1_rs rws L (Zlength rws)) pk;
          field_at shk t_x1wksp (DOT _symbols) (x1_syms rws (Zlength rws)) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (zbytes rws ++ wr) pk;
          F))%assert.
  { Exists n. entailer!. }
  { clear n H4. Intros n. forward. forward_if.
    2: { forward. entailer!. replace n with (Zlength rws) by lia. apply derives_refl. }
    assert (Hi: 0 <= n < Zlength rws) by lia.
    assert (Hw: 0 <= Znth n rws <= L) by (apply (proj1 (Forall_Znth _ _) H3); exact Hi).
    destruct (Hm1 n Hi) as [Hq Hstep].
    forward.
    { entailer!. rewrite x1_hw_Znth by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite x1_hw_Znth by lia.
    forward.
    rewrite Int.unsigned_repr by rep_lia.
    pose proof (x1_rs_step rws L n Hi Hw) as Hrs.
    set (w := Znth n rws) in *.
    set (q := x1_start rws w + x1_cnt (sublist 0 n rws) w) in *.
    forward.
    { entailer!. rewrite x1_rs_Znth by lia. exact I. }
    rewrite x1_rs_Znth by lia. fold q.
    forward.
    forward.
    Exists n.
    assert (Hz: Int.zero_ext 8 (Int.repr n) = Int.repr n).
    { apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. rep_lia. }
    rewrite !add_repr, !Hz, Hstep, Hrs.
    entailer!. }
  { clear n H4. Intros n. forward. Exists (n + 1). entailer!. }
  rewrite Hm2. unfold POSTCONDITION, abbreviate. simpl RA_normal. entailer!.
Qed.
