(* Local copy of the proved src/proof/harness/writer/model/WM_HufDec.v (same statements and proofs), used by
   wb_huf_desc in place of model.WM_HufDec. *)
(* Huffman codes drawn by huf_pick against the model's Huffman decoding (plain Coq): the canonical codes decode, tree
   descriptions parse. *)
Require Import Zstd.proof.harness.writer.model.WModel.

Require Import Zstd.proof.harness.writer.model.WM_Bits.
Local Open Scope bool_scope.

(* ---- sums ---- *)

Lemma hd_zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. unfold zsum. induction a; simpl; intros; [lia | rewrite IHa; lia]. Qed.

Lemma hd_zsum_map_add : forall {A} (f g: A -> Z) l,
  zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. unfold zsum. induction l; simpl; [lia | rewrite IHl; lia]. Qed.

Lemma hd_zsum_map_sub : forall {A} (f g: A -> Z) l,
  zsum (map (fun x => f x - g x) l) = zsum (map f l) - zsum (map g l).
Proof. unfold zsum. induction l; simpl; [lia | rewrite IHl; lia]. Qed.

Lemma hd_zsum_map_ext_in : forall {A} (f g: A -> Z) l,
  (forall x, In x l -> f x = g x) -> zsum (map f l) = zsum (map g l).
Proof. intros. f_equal. apply map_ext_in. auto. Qed.

Lemma hd_zsum_map_zero : forall {A} (f: A -> Z) l,
  (forall x, In x l -> f x = 0) -> zsum (map f l) = 0.
Proof. unfold zsum. induction l; simpl; intros; [lia | rewrite H, IHl; auto]. Qed.

Lemma hd_zsum_map_nonneg : forall {A} (f: A -> Z) l,
  (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. unfold zsum. induction l; simpl; intros; [lia |].
  assert (0 <= fold_right Z.add 0 (map f l)) by (apply IHl; auto).
  specialize (H a (or_introl eq_refl)). lia. Qed.

Lemma hd_zsum_map_ge : forall {A} (f: A -> Z) l y,
  (forall x, In x l -> 0 <= f x) -> In y l -> f y <= zsum (map f l).
Proof.
  intros A f l y Hn Hy. induction l as [|a l IH]; simpl in *; [contradiction|].
  assert (0 <= zsum (map f l)) by (apply hd_zsum_map_nonneg; auto).
  unfold zsum in *. simpl. destruct Hy as [<-|Hy].
  - lia.
  - specialize (IH (fun x Hx => Hn x (or_intror Hx)) Hy). specialize (Hn a (or_introl eq_refl)). lia.
Qed.

Lemma hd_zsum_map_divide : forall {A} (f: A -> Z) l d,
  (forall x, In x l -> (d | f x)) -> (d | zsum (map f l)).
Proof.
  unfold zsum. induction l; simpl; intros; [apply Z.divide_0_r|].
  apply Z.divide_add_r; auto.
Qed.

Lemma hd_zsum_swap : forall {A B} (f: A -> B -> Z) la lb,
  zsum (map (fun a => zsum (map (fun b => f a b) lb)) la) =
  zsum (map (fun b => zsum (map (fun a => f a b) la)) lb).
Proof.
  induction la; simpl; intros.
  - symmetry. apply hd_zsum_map_zero. reflexivity.
  - unfold zsum at 1. simpl. fold (zsum (map (fun a0 => zsum (map (fun b => f a0 b) lb)) la)).
    rewrite IHla.
    rewrite <- (hd_zsum_map_add (fun b => f a b) (fun b => zsum (map (fun a0 => f a0 b) la))).
    reflexivity.
Qed.

Lemma hd_len_flat_map : forall {A B} (f: A -> list B) l,
  Z.of_nat (length (flat_map f l)) = zsum (map (fun x => Z.of_nat (length (f x))) l).
Proof. unfold zsum. induction l; simpl; [reflexivity|]. rewrite length_app, Nat2Z.inj_add, IHl. reflexivity. Qed.

Lemma hd_nth_flat_map : forall {A B} (f: A -> list B) l1 x l2 j d,
  (j < length (f x))%nat ->
  nth (length (flat_map f l1) + j) (flat_map f (l1 ++ x :: l2)) d = nth j (f x) d.
Proof.
  intros. rewrite flat_map_app. simpl. rewrite app_nth2 by lia.
  replace (length (flat_map f l1) + j - length (flat_map f l1))%nat with j by lia.
  apply app_nth1. auto.
Qed.

Lemma hd_nth_map_seq : forall {A} (f: nat -> A) k n d, (n < k)%nat -> nth n (map f (seq 0 k)) d = f n.
Proof.
  intros. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma hd_sum_ind_seq1 : forall (x: Z) (g: Z -> Z) m,
  zsum (map (fun w' => if x =? w' then g w' else 0) (map Z.of_nat (seq 1 m))) =
  if (1 <=? x) && (x <=? Z.of_nat m) then g x else 0.
Proof.
  intros x g m. induction m.
  - simpl. destruct (Z.leb_spec 1 x), (Z.leb_spec x 0); simpl; auto; lia.
  - rewrite seq_S, !map_app, hd_zsum_app, IHm. unfold zsum. cbn [map fold_right].
    replace (Z.of_nat (1 + m)) with (Z.of_nat m + 1) by lia.
    replace (Z.of_nat (S m)) with (Z.of_nat m + 1) by lia.
    destruct (Z.eqb_spec x (Z.of_nat m + 1)), (Z.leb_spec 1 x), (Z.leb_spec x (Z.of_nat m)),
      (Z.leb_spec x (Z.of_nat m + 1)); simpl; subst; try lia.
Qed.

Lemma hd_sum_syms : forall (g: Z -> Z) l, length l = 256%nat ->
  zsum (map (fun s => g (zn l s)) syms256) = zsum (map g l).
Proof.
  intros g l Hl. unfold syms256. rewrite map_map. f_equal.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite !length_map, length_seq. auto.
  - intros n Hn. rewrite length_map, length_seq in Hn.
    rewrite (nth_indep _ 0 ((fun x => g (zn l (Z.of_nat x))) 0%nat)) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (fun x : nat => g (zn l (Z.of_nat x))) _ 0%nat). rewrite seq_nth by lia.
    rewrite (nth_indep _ 0 (g 0)) by (rewrite length_map; lia). rewrite map_nth.
    unfold zn. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma hd_pow_divide : forall a b, 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof. intros. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma hd_mod_mod_pow : forall W a b, 0 <= a <= b -> (W mod 2 ^ b) mod 2 ^ a = W mod 2 ^ a.
Proof.
  intros. replace (2 ^ b) with (2 ^ a * 2 ^ (b - a)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.rem_mul_r by (apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia).
  rewrite Z.mul_comm, Z.mod_add by (apply Z.pow_nonzero; lia). apply Z.mod_mod. apply Z.pow_nonzero; lia.
Qed.

(* ---- the cells of a table ---- *)

Definition hd_inner (ws: list Z) (log w0: Z) (s0: nat) : list (Z * Z) :=
  if nth s0 ws 0 =? w0 then repeat (Z.of_nat s0, log + 1 - w0) (Z.to_nat (2 ^ (w0 - 1))) else [].

Lemma hd_cells_eq : forall t, huf_cells t =
  flat_map (fun w0 => flat_map (hd_inner (ht_weights t) (ht_log t) w0) (seq 0 (length (ht_weights t))))
    (map Z.of_nat (seq 1 (Z.to_nat (ht_log t)))).
Proof. reflexivity. Qed.

Lemma hd_len_inner : forall ws log w0 s0,
  Z.of_nat (length (hd_inner ws log w0 s0)) = if nth s0 ws 0 =? w0 then 2 ^ (w0 - 1) else 0.
Proof.
  intros. unfold hd_inner. destruct (_ =? _); simpl; [|reflexivity].
  rewrite repeat_length. apply Z2Nat.id. apply Z.pow_nonneg. lia.
Qed.

Lemma hd_len_row : forall ws log w0 l,
  Z.of_nat (length (flat_map (hd_inner ws log w0) l)) =
  zsum (map (fun s0 => if nth s0 ws 0 =? w0 then 2 ^ (w0 - 1) else 0) l).
Proof. intros. rewrite hd_len_flat_map. f_equal. apply map_ext. intros. apply hd_len_inner. Qed.

Lemma hd_len_rows : forall ws log l m,
  Z.of_nat (length (flat_map (fun w0 => flat_map (hd_inner ws log w0) l) (map Z.of_nat (seq 1 m)))) =
  zsum (map (fun s0 => if (1 <=? nth s0 ws 0) && (nth s0 ws 0 <=? Z.of_nat m) then 2 ^ (nth s0 ws 0 - 1) else 0) l).
Proof.
  intros. rewrite hd_len_flat_map.
  rewrite (map_ext _ (fun w0 => zsum (map (fun s0 => if nth s0 ws 0 =? w0 then 2 ^ (w0 - 1) else 0) l)))
    by (intros; apply hd_len_row).
  rewrite (hd_zsum_swap (fun w0 s0 => if nth s0 ws 0 =? w0 then 2 ^ (w0 - 1) else 0)).
  f_equal. apply map_ext. intros s0.
  apply (hd_sum_ind_seq1 (nth s0 ws 0) (fun w0 => 2 ^ (w0 - 1))).
Qed.

(* ---- facts of huf_ok ---- *)

Lemma hd_filter_last : forall (p: Z -> bool) n x,
  In x (filter p (map Z.of_nat (seq 0 n))) -> x <= last (filter p (map Z.of_nat (seq 0 n))) 0.
Proof.
  intros p n. induction n; intros x Hx; [contradiction|].
  rewrite seq_S, map_app, filter_app in *. simpl in *.
  destruct (p (Z.of_nat n)) eqn:Hp.
  - rewrite last_last. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [|lia].
    apply filter_In in Hx. destruct Hx as [Hx _]. apply in_map_iff in Hx.
    destruct Hx as [k [<- Hk]]. apply in_seq in Hk. lia.
  - rewrite app_nil_r in *. auto.
Qed.

Section HufOk.
Context (H : whuf) (HH : huf_ok H).

Lemma hd_len_w : length (wh_w H) = 256%nat.
Proof. destruct HH as [HL _]. rewrite Zlength_correct in HL. lia. Qed.

Lemma hd_log : 1 <= wh_log H <= 11.
Proof. apply HH. Qed.

Lemma hd_w_range : forall i, 0 <= wh_weight H i <= wh_log H.
Proof.
  intros i. destruct HH as [_ [Hlog [HF _]]]. unfold wh_weight, zn.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length (wh_w H))).
  - rewrite Forall_forall in HF. apply HF. apply nth_In. auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma hd_kraft : zsum (map (fun s => if wh_weight H s =? 0 then 0 else 2 ^ (wh_weight H s - 1)) syms256) = 2 ^ wh_log H.
Proof.
  destruct HH as [_ [_ [_ [HK _]]]]. rewrite <- HK.
  apply (hd_sum_syms (fun w => if w =? 0 then 0 else 2 ^ (w - 1))). apply hd_len_w.
Qed.

Lemma hd_used_in : forall s, huf_present H s -> In s (wh_used H).
Proof.
  intros s [Hs Hw]. destruct HH as [_ [_ [_ [_ [HU _]]]]]. rewrite HU.
  apply filter_In. split.
  - unfold syms256. apply in_map_iff. exists (Z.to_nat s). split; [lia|]. apply in_seq. lia.
  - apply Z.eqb_neq in Hw. rewrite Hw. reflexivity.
Qed.

Lemma hd_present_le_last : forall s, huf_present H s -> s <= wh_last H.
Proof.
  intros s Hs. pose proof (hd_used_in s Hs) as Hi.
  destruct HH as [_ [_ [_ [_ [HU [_ [HL _]]]]]]]. rewrite HL. rewrite HU in *.
  apply hd_filter_last. auto.
Qed.

Lemma hd_last_range : 0 <= wh_last H < 256 /\ wh_weight H (wh_last H) <> 0.
Proof.
  destruct HH as [_ [_ [_ [_ [HU [H2 [HL _]]]]]]].
  assert (Hne: wh_used H <> nil) by (intro E; rewrite E, Zlength_nil in H2; lia).
  assert (Hin: In (wh_last H) (wh_used H)).
  { rewrite HL. rewrite (app_removelast_last 0 Hne) at 2. apply in_or_app. right. left. reflexivity. }
  rewrite HU in Hin. apply filter_In in Hin. destruct Hin as [Hin Hp].
  unfold syms256 in Hin. apply in_map_iff in Hin. destruct Hin as [k [Ek Hk]]. apply in_seq in Hk.
  split; [lia|]. intro E. rewrite E in Hp. discriminate.
Qed.

Lemma hd_above_last : forall s, wh_last H < s -> wh_weight H s = 0.
Proof.
  intros s Hs. pose proof hd_last_range as [HL _].
  destruct (Z.eq_dec (wh_weight H s) 0); auto.
  destruct (Z_lt_le_dec s 256).
  - assert (s <= wh_last H) by (apply hd_present_le_last; split; [lia|auto]). lia.
  - unfold wh_weight, zn. apply nth_overflow. rewrite hd_len_w. lia.
Qed.

Lemma hd_start_bound : forall s, huf_present H s ->
  0 <= huf_start H s /\ huf_start H s + 2 ^ (wh_weight H s - 1) <= 2 ^ wh_log H /\
  (2 ^ (wh_weight H s - 1) | huf_start H s).
Proof.
  intros s [Hs Hw]. pose proof (hd_w_range s) as Hws.
  set (w := wh_weight H s) in *.
  set (tT := fun s' => if wh_weight H s' =? 0 then 0 else 2 ^ (wh_weight H s' - 1)).
  set (tS := fun s' => let w' := wh_weight H s' in
                       if (0 <? w') && ((w' <? w) || ((w' =? w) && (s' <? s))) then 2 ^ (w' - 1) else 0).
  assert (Hst: huf_start H s = zsum (map tS syms256)) by reflexivity.
  assert (HT: zsum (map tT syms256) = 2 ^ wh_log H) by apply hd_kraft.
  assert (HD: 2 ^ wh_log H - huf_start H s = zsum (map (fun s' => tT s' - tS s') syms256)).
  { rewrite hd_zsum_map_sub, HT, Hst. reflexivity. }
  assert (Hnn: forall s', 0 <= tT s' - tS s').
  { intros s'. unfold tT, tS. cbv beta zeta. pose proof (hd_w_range s').
    pose proof (Z.pow_nonneg 2 (wh_weight H s' - 1)).
    destruct (Z.eqb_spec (wh_weight H s') 0), (Z.ltb_spec 0 (wh_weight H s')),
      (Z.ltb_spec (wh_weight H s') w), (Z.eqb_spec (wh_weight H s') w), (Z.ltb_spec s' s);
      simpl; lia. }
  assert (Hdv: forall s', (2 ^ (w - 1) | tT s' - tS s')).
  { intros s'. unfold tT, tS. cbv beta zeta. pose proof (hd_w_range s').
    destruct (Z.eqb_spec (wh_weight H s') 0), (Z.ltb_spec 0 (wh_weight H s')),
      (Z.ltb_spec (wh_weight H s') w), (Z.eqb_spec (wh_weight H s') w), (Z.ltb_spec s' s);
      simpl; try apply Z.divide_0_r; try (rewrite Z.sub_diag; apply Z.divide_0_r); try lia;
      rewrite Z.sub_0_r; apply hd_pow_divide; lia. }
  assert (Hat: tT s - tS s = 2 ^ (w - 1)).
  { unfold tT, tS. cbv beta zeta. fold w. rewrite Z.ltb_irrefl, Z.eqb_refl.
    destruct (Z.eqb_spec w 0); [contradiction|]. destruct (Z.ltb_spec 0 w); [|lia]. simpl. rewrite Z.ltb_irrefl. lia. }
  assert (Hin: In s syms256).
  { unfold syms256. apply in_map_iff. exists (Z.to_nat s). split; [lia|]. apply in_seq. lia. }
  pose proof (hd_zsum_map_ge (fun s' => tT s' - tS s') syms256 s (fun x _ => Hnn x) Hin) as Hge.
  cbv beta in Hge. rewrite Hat, <- HD in Hge.
  assert (Hst0: 0 <= huf_start H s).
  { rewrite Hst. apply hd_zsum_map_nonneg. intros x _. unfold tS. cbv beta zeta.
    destruct (_ && _); [apply Z.pow_nonneg|]; lia. }
  split; [auto|]. split; [lia|].
  replace (huf_start H s) with (2 ^ wh_log H - (2 ^ wh_log H - huf_start H s)) by lia.
  apply Z.divide_sub_r; [apply hd_pow_divide; lia|]. rewrite HD. apply hd_zsum_map_divide. auto.
Qed.

Lemma hd_cells_at : forall s j, huf_present H s -> 0 <= j < 2 ^ (wh_weight H s - 1) ->
  nth (Z.to_nat (huf_start H s + j)) (huf_cells (huf_model H)) (0, 0) = (s, huf_nb_of H s).
Proof.
  intros s j Hs Hj. pose proof (hd_start_bound s Hs) as [Hst0 [Hst1 _]].
  pose proof (hd_present_le_last s Hs) as Hsl. pose proof hd_last_range as [Hl _].
  pose proof (hd_w_range s) as Hws. pose proof hd_log as Hlog. destruct Hs as [Hs Hw].
  rewrite hd_cells_eq. unfold huf_model. cbn [ht_weights ht_log].
  set (w := wh_weight H s) in *. set (log := wh_log H) in *.
  set (ws := firstn (Z.to_nat (wh_last H + 1)) (wh_w H)).
  assert (Hn: length ws = Z.to_nat (wh_last H + 1)).
  { unfold ws. rewrite length_firstn, hd_len_w. lia. }
  assert (Hws_nth: forall i, (i < length ws)%nat -> nth i ws 0 = wh_weight H (Z.of_nat i)).
  { intros i Hi. unfold ws, wh_weight, zn. rewrite nth_firstn, Nat2Z.id.
    destruct (Nat.ltb_spec i (Z.to_nat (wh_last H + 1))); [reflexivity | lia]. }
  assert (Hsplit1: map Z.of_nat (seq 1 (Z.to_nat log)) =
    map Z.of_nat (seq 1 (Z.to_nat (w - 1))) ++ w :: map Z.of_nat (seq (S (Z.to_nat w)) (Z.to_nat (log - w)))).
  { replace (Z.to_nat log) with (Z.to_nat (w - 1) + S (Z.to_nat (log - w)))%nat by lia.
    rewrite seq_app, map_app. cbn [seq map]. f_equal. f_equal; [lia|]. f_equal. f_equal. lia. }
  assert (Hsplit2: seq 0 (length ws) = seq 0 (Z.to_nat s) ++ Z.to_nat s :: seq (S (Z.to_nat s)) (length ws - S (Z.to_nat s))).
  { replace (length ws) with (Z.to_nat s + S (length ws - S (Z.to_nat s)))%nat at 1 by lia.
    rewrite seq_app. reflexivity. }
  set (A := flat_map (fun w0 => flat_map (hd_inner ws log w0) (seq 0 (length ws))) (map Z.of_nat (seq 1 (Z.to_nat (w - 1))))).
  set (B := flat_map (hd_inner ws log w) (seq 0 (Z.to_nat s))).
  assert (Hcount: Z.of_nat (length A) + Z.of_nat (length B) = huf_start H s).
  { unfold A, B. rewrite hd_len_rows, hd_len_row.
    replace (Z.of_nat (Z.to_nat (w - 1))) with (w - 1) by lia.
    unfold huf_start. fold w. unfold syms256. rewrite map_map.
    replace 256%nat with (length ws + (256 - length ws))%nat by lia.
    rewrite seq_app, map_app, hd_zsum_app.
    rewrite (hd_zsum_map_zero _ (seq (0 + length ws) _)).
    2:{ intros x Hx. apply in_seq in Hx. rewrite (hd_above_last (Z.of_nat x)) by lia. reflexivity. }
    assert (Hsp: seq 0 (length ws) = seq 0 (Z.to_nat s) ++ seq (0 + Z.to_nat s) (length ws - Z.to_nat s)).
    { rewrite <- seq_app. f_equal. lia. }
    rewrite Hsp, !map_app, !hd_zsum_app.
    match goal with |- ?a1 + ?a2 + ?b = ?s1 + ?s2 + 0 =>
      enough (a1 + b = s1 /\ a2 = s2) by lia end.
    split.
    - rewrite <- hd_zsum_map_add. apply hd_zsum_map_ext_in. intros x Hx. apply in_seq in Hx.
      rewrite Hws_nth by lia. remember (wh_weight H (Z.of_nat x)) as v.
      assert (0 <= v <= log) by (subst v; apply hd_w_range).
      destruct (Z.leb_spec 1 v), (Z.leb_spec v (w - 1)), (Z.eqb_spec v w), (Z.ltb_spec 0 v),
        (Z.ltb_spec v w), (Z.ltb_spec (Z.of_nat x) s); simpl; try lia; subst w; rewrite e; lia.
    - apply hd_zsum_map_ext_in. intros x Hx. apply in_seq in Hx.
      rewrite Hws_nth by lia. remember (wh_weight H (Z.of_nat x)) as v.
      assert (0 <= v <= log) by (subst v; apply hd_w_range).
      destruct (Z.leb_spec 1 v), (Z.leb_spec v (w - 1)), (Z.eqb_spec v w), (Z.ltb_spec 0 v),
        (Z.ltb_spec v w), (Z.ltb_spec (Z.of_nat x) s); simpl; try lia. }
  assert (Hidx: Z.to_nat (huf_start H s + j) = (length A + (length B + Z.to_nat j))%nat) by lia.
  assert (Hin: nth (Z.to_nat s) ws 0 = w) by (rewrite Hws_nth by lia; unfold w; f_equal; lia).
  rewrite Hidx, Hsplit1. unfold A. rewrite hd_nth_flat_map.
  - unfold B. rewrite Hsplit2. rewrite hd_nth_flat_map.
    + unfold hd_inner. rewrite Hin, Z.eqb_refl.
      rewrite (nth_indep _ (0, 0) (Z.of_nat (Z.to_nat s), log + 1 - w)) by (rewrite repeat_length; lia).
      rewrite nth_repeat.
      unfold huf_nb_of. f_equal; lia.
    + unfold hd_inner. rewrite Hin, Z.eqb_refl, repeat_length. lia.
  - rewrite Hsplit2, flat_map_app, length_app. cbn [flat_map]. rewrite length_app.
    unfold hd_inner at 2. rewrite Hin, Z.eqb_refl, repeat_length. fold B. lia.
Qed.

Lemma hd_last_pos : 1 <= wh_last H.
Proof.
  pose proof hd_last_range as [[Hl0 Hl1] Hlw]. destruct (Z.eq_dec (wh_last H) 0) as [E|]; [|lia].
  exfalso. pose proof hd_kraft as HK. pose proof (hd_w_range 0) as Hw0. pose proof hd_log.
  rewrite E in Hlw.
  unfold syms256 in HK. replace 256%nat with (1 + 255)%nat in HK by reflexivity.
  rewrite seq_app, !map_app, hd_zsum_app in HK.
  rewrite (hd_zsum_map_zero _ (map Z.of_nat (seq (0 + 1) 255))) in HK.
  2:{ intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- Hk]]. apply in_seq in Hk.
      rewrite hd_above_last by lia. reflexivity. }
  unfold zsum in HK. cbn [map seq fold_right] in HK. change (Z.of_nat 0) with 0 in HK.
  destruct (Z.eqb_spec (wh_weight H 0) 0); [contradiction|].
  assert (2 ^ (wh_weight H 0 - 1) < 2 ^ wh_log H) by (apply Z.pow_lt_mono_r; lia). lia.
Qed.

End HufOk.

Lemma huf_code_range : forall H s,
  huf_ok H -> huf_present H s ->
  1 <= huf_nb_of H s <= 11 /\ 0 <= huf_code_of H s < 2 ^ huf_nb_of H s.
Proof.
  intros H s HH Hs. pose proof (hd_start_bound H HH s Hs) as [H0 [H1 _]].
  pose proof (hd_w_range H HH s). pose proof (hd_log H HH). destruct Hs as [_ Hw].
  unfold huf_nb_of, huf_code_of. split; [lia|]. split.
  - apply Z.div_pos; [lia|]. apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (wh_weight H s - 1 + (wh_log H + 1 - wh_weight H s)) with (wh_log H) by lia.
    pose proof (Z.pow_pos_nonneg 2 (wh_weight H s - 1)). lia.
Qed.

Lemma huf_stream_fields_ok : forall H lits,
  huf_ok H -> Forall (huf_present H) lits -> fields_ok (huf_stream_fields H lits).
Proof.
  intros H lits HH Hl. unfold fields_ok, huf_stream_fields. apply Forall_map.
  apply Forall_rev in Hl. eapply Forall_impl; [|exact Hl]. intros c Hc. cbn [fst snd].
  pose proof (huf_code_range H c HH Hc). lia.
Qed.

Lemma hd_fields_cons : forall H c l,
  huf_stream_fields H (c :: l) = huf_stream_fields H l ++ [(huf_code_of H c, huf_nb_of H c)].
Proof. intros. unfold huf_stream_fields. simpl. rewrite map_app. reflexivity. Qed.

Lemma hd_fields_range : forall H l, huf_ok H -> Forall (huf_present H) l ->
  0 <= fields_L (huf_stream_fields H l) /\
  0 <= fields_W (huf_stream_fields H l) < 2 ^ fields_L (huf_stream_fields H l).
Proof.
  intros. pose proof (fields_wl_range (huf_stream_fields H l) 0 0 (huf_stream_fields_ok H l H0 H1)).
  unfold fields_L, fields_W. simpl in H2. lia.
Qed.

(* one symbol: peeking log bits above the code of c lands in c's cells *)
Lemma hd_peek_code : forall H c V W' L', huf_ok H -> huf_present H c ->
  0 <= L' -> 0 <= W' < 2 ^ L' ->
  V mod 2 ^ (L' + huf_nb_of H c) = W' + huf_code_of H c * 2 ^ L' ->
  nth (Z.to_nat (bs_peek V (L' + huf_nb_of H c) (wh_log H))) (huf_cells (huf_model H)) (0, 0) =
  (c, huf_nb_of H c).
Proof.
  intros H c V W' L' HH Hc HL HW HV.
  pose proof (hd_start_bound H HH c Hc) as [Hs0 [Hs1 [k Hk]]].
  pose proof (hd_w_range H HH c). pose proof (hd_log H HH). pose proof Hc as [_ Hw].
  set (w := wh_weight H c) in *. set (nb := huf_nb_of H c) in *.
  assert (Hnb: nb = wh_log H + 1 - w) by reflexivity.
  assert (Hcode: huf_code_of H c * 2 ^ (w - 1) = huf_start H c).
  { unfold huf_code_of. fold w. rewrite Hk, Z.div_mul by (apply Z.pow_nonzero; lia). lia. }
  assert (Hpw: 0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (HpL: 0 < 2 ^ L') by (apply Z.pow_pos_nonneg; lia).
  assert (Hpn: 0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpeek: bs_peek V (L' + nb) (wh_log H) = huf_start H c + W' * 2 ^ (w - 1) / 2 ^ L').
  { unfold bs_peek. rewrite HV.
    replace (wh_log H) with ((w - 1) + nb) by lia.
    rewrite !Z.pow_add_r by lia.
    rewrite Z.mul_assoc, Z.div_mul_cancel_r by lia.
    replace ((W' + huf_code_of H c * 2 ^ L') * 2 ^ (w - 1)) with
      (W' * 2 ^ (w - 1) + (huf_code_of H c * 2 ^ (w - 1)) * 2 ^ L') by ring.
    rewrite Z.div_add by lia. lia. }
  rewrite Hpeek. apply hd_cells_at; auto.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. fold w. nia.
Qed.

Lemma hd_decode_syms : forall H Vb V L l, huf_ok H -> Forall (huf_present H) l ->
  (forall pos nb, 0 <= pos <= L -> 0 <= nb <= 32 -> bs_peek_s Vb pos nb = bs_peek V pos nb) ->
  fields_L (huf_stream_fields H l) <= L ->
  V mod 2 ^ fields_L (huf_stream_fields H l) = fields_W (huf_stream_fields H l) ->
  huf_decode_syms (huf_model H) Vb (length l) (fields_L (huf_stream_fields H l)) = Some (l, 0).
Proof.
  intros H Vb V L l HH. induction l as [|c l IH]; intros Hl Hpk HLe HV.
  - reflexivity.
  - inversion Hl as [|? ? Hc Hl']; subst.
    pose proof (hd_fields_range H l HH Hl') as [HL0 HW0].
    set (L' := fields_L (huf_stream_fields H l)) in *. set (W' := fields_W (huf_stream_fields H l)) in *.
    assert (Hwl: fields_wl (huf_stream_fields H (c :: l)) 0 0 = (W' + huf_code_of H c * 2 ^ L', L' + huf_nb_of H c)).
    { rewrite hd_fields_cons, fields_wl_app. reflexivity. }
    unfold fields_L, fields_W in *. rewrite Hwl in *. cbn [fst snd] in *.
    pose proof (huf_code_range H c HH Hc) as [Hnb _].
    cbn [huf_decode_syms length].
    assert (Hm: huf_model H = huf_model H) by reflexivity.
    replace (ht_log (huf_model H)) with (wh_log H) by reflexivity.
    rewrite Hpk by (pose proof (hd_log H HH); lia).
    rewrite (hd_peek_code H c V W' L' HH Hc HL0 HW0 HV).
    replace (L' + huf_nb_of H c - huf_nb_of H c) with L' by lia.
    destruct (Z.ltb_spec L' 0); [lia|].
    rewrite IH; auto; [lia|].
    rewrite <- (hd_mod_mod_pow V L' (L' + huf_nb_of H c)) by lia. rewrite HV.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Theorem huf_stream_decode : forall H lits,
  huf_ok H -> Forall (huf_present H) lits ->
  huf_decode_stream (huf_model H) (huf_stream_bytes H lits) (Zlength lits) = Some lits.
Proof.
  intros H lits HH Hl. pose proof (hd_fields_range H lits HH Hl) as [HL HW].
  unfold huf_decode_stream, huf_stream_bytes, fields_mark.
  set (L := fields_L (huf_stream_fields H lits)) in *. set (W := fields_W (huf_stream_fields H lits)) in *.
  destruct (bw_mark_stream W L HL HW) as [Hok Htot]. rewrite Hok, Htot. cbn [negb].
  rewrite Zlength_correct, Nat2Z.id.
  pose proof (hd_decode_syms H (bw_mark W L) W L lits HH Hl) as HD. fold L W in HD.
  rewrite HD; auto.
  - intros. apply bs_peek_mark; auto.
  - lia.
  - apply Z.mod_small. auto.
Qed.

Definition hd_kw (w: Z) : Z := if w =? 0 then 0 else 2 ^ (w - 1).

Lemma hd_fold_shiftr : forall l, Forall (fun w => 0 <= w) l ->
  fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 l = zsum (map hd_kw l).
Proof.
  unfold zsum. induction l as [|a l IH]; intros Hl; [reflexivity|]. inversion Hl; subst.
  simpl. rewrite IH by auto. f_equal. unfold hd_kw. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.eqb_spec a 0); [subst; reflexivity|].
  replace a with ((a - 1) + 1) at 1 by lia. rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2. apply Z.div_mul. lia.
Qed.

Lemma hd_count1_parity : forall l, Forall (fun w => 0 <= w) l ->
  (2 | zsum (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l))).
Proof.
  unfold zsum. induction l as [|a l IH]; intros Hl; [apply Z.divide_0_r|]. inversion Hl; subst.
  specialize (IH H2). cbn [map fold_right filter].
  unfold hd_kw at 1. destruct (Z.eqb_spec a 1).
  - subst. cbn [length]. rewrite Nat2Z.inj_succ. simpl (1 =? 0). replace (fold_right Z.add 0 (map hd_kw l)) with (fold_right Z.add 0 (map hd_kw l)) by reflexivity.
    replace (2 ^ (1 - 1) + fold_right Z.add 0 (map hd_kw l) - Z.succ (Z.of_nat (length (filter (fun w => w =? 1) l))))
      with (fold_right Z.add 0 (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l))) by (change (2 ^ (1 - 1)) with 1; lia).
    auto.
  - destruct (Z.eqb_spec a 0).
    + replace (0 + fold_right Z.add 0 (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l)))
        with (fold_right Z.add 0 (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l))) by lia. auto.
    + replace (2 ^ (a - 1) + fold_right Z.add 0 (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l)))
        with (2 ^ (a - 1) + (fold_right Z.add 0 (map hd_kw l) - Z.of_nat (length (filter (fun w => w =? 1) l)))) by lia.
      apply Z.divide_add_r; auto. replace (a - 1) with (1 + (a - 2)) by lia. rewrite Z.pow_add_r by lia.
      apply Z.divide_factor_l.
Qed.

Lemma hd_firstn_seq : forall (l: list Z) n, (n <= length l)%nat ->
  firstn n l = map (fun i => nth i l 0) (seq 0 n).
Proof.
  intros. apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_firstn, length_map, length_seq. lia.
  - intros i Hi. rewrite length_firstn in Hi. rewrite hd_nth_map_seq by lia. rewrite nth_firstn.
    destruct (Nat.ltb_spec i n); [reflexivity|lia].
Qed.

(* the weights of a description (all but the last symbol's) give the code H *)
Theorem huf_parse_of_weights : forall H b k,
  huf_ok H -> huf_desc_weights b = Some (hfw_weights H, k) -> huf_parse_desc b = Some (huf_model H, k).
Proof.
  intros H b k HH Hd.
  pose proof (hd_last_range H HH) as [[Hl0 Hl1] Hlw]. pose proof (hd_log H HH) as Hlog.
  pose proof (hd_w_range H HH (wh_last H)) as Hwl. pose proof (hd_len_w H HH) as Hlen.
  assert (HF: Forall (fun w => 0 <= w <= wh_log H) (wh_w H)) by apply HH.
  set (last := wh_last H) in *. set (log := wh_log H) in *. set (wl := wh_weight H last) in *.
  set (L1 := firstn (Z.to_nat (last + 1)) (wh_w H)).
  assert (HL1: L1 = hfw_weights H ++ [wl]).
  { unfold L1, hfw_weights. rewrite !hd_firstn_seq by lia.
    replace (Z.to_nat (last + 1)) with (S (Z.to_nat last)) by lia. rewrite seq_S, map_app.
    f_equal. }
  assert (HFL1: Forall (fun w => 0 <= w <= log) L1).
  { rewrite Forall_forall in *. intros x Hx. apply HF.
    rewrite <- (firstn_skipn (Z.to_nat (last + 1)) (wh_w H)). apply in_or_app. left. exact Hx. }
  assert (HK1: zsum (map hd_kw L1) = 2 ^ log).
  { pose proof (hd_kraft H HH) as HKr. fold log in HKr. rewrite <- HKr. unfold syms256. rewrite map_map.
    replace 256%nat with (Z.to_nat (last + 1) + (256 - Z.to_nat (last + 1)))%nat by lia.
    rewrite seq_app, map_app, hd_zsum_app.
    rewrite (hd_zsum_map_zero _ (seq (0 + _) _)).
    2:{ intros x Hx. apply in_seq in Hx. rewrite (hd_above_last H HH (Z.of_nat x)) by lia. reflexivity. }
    rewrite Z.add_0_r. unfold L1. rewrite hd_firstn_seq by lia. rewrite map_map. f_equal.
    apply map_ext. intros i. unfold hd_kw, wh_weight, zn. rewrite Nat2Z.id. reflexivity. }
  rewrite HL1 in HFL1, HK1. apply Forall_app in HFL1. destruct HFL1 as [HFW _].
  rewrite map_app, hd_zsum_app in HK1. unfold zsum at 2 in HK1. cbn [map fold_right] in HK1.
  unfold hd_kw at 2 in HK1. destruct (Z.eqb_spec wl 0); [contradiction|].
  assert (Htot: zsum (map hd_kw (hfw_weights H)) = 2 ^ log - 2 ^ (wl - 1)) by lia.
  assert (Hp1: 2 ^ (wl - 1) <= 2 ^ (log - 1)) by (apply Z.pow_le_mono_r; lia).
  assert (Hp2: 2 ^ log = 2 * 2 ^ (log - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (Hp3: 0 < 2 ^ (wl - 1)) by (apply Z.pow_pos_nonneg; lia).
  unfold huf_parse_desc. rewrite Hd.
  replace (existsb (fun w => w >? HUF_TABLELOG_MAX) (hfw_weights H)) with false.
  2:{ symmetry. apply Bool.not_true_iff_false. intro E. apply existsb_exists in E.
      destruct E as [x [Hx Hgt]]. rewrite Forall_forall in HFW. specialize (HFW x Hx).
      unfold HUF_TABLELOG_MAX in Hgt. apply Z.gtb_lt in Hgt. lia. }
  assert (HFW0: Forall (fun w => 0 <= w) (hfw_weights H)).
  { apply Forall_forall. intros x Hx. rewrite Forall_forall in HFW. specialize (HFW x Hx). lia. }
  cbv zeta. rewrite hd_fold_shiftr by exact HFW0.
  rewrite Htot.
  destruct (Z.eqb_spec (2 ^ log - 2 ^ (wl - 1)) 0); [lia|].
  unfold highbit.
  assert (Hlg: Z.log2 (2 ^ log - 2 ^ (wl - 1)) = log - 1).
  { apply Z.log2_unique; [lia|]. replace (Z.succ (log - 1)) with log by lia. lia. }
  rewrite Hlg.
  replace (log - 1 + 1) with log by lia.
  destruct (Z.gtb_spec log HUF_TABLELOG_MAX); [unfold HUF_TABLELOG_MAX in *; lia|].
  replace (2 ^ log - (2 ^ log - 2 ^ (wl - 1))) with (2 ^ (wl - 1)) by lia.
  rewrite Z.log2_pow2 by lia. rewrite Z.eqb_refl. cbn [negb].
  replace (wl - 1 + 1) with wl by lia. rewrite <- HL1.
  assert (HK2: zsum (map hd_kw L1) = 2 ^ log).
  { rewrite HL1, map_app, hd_zsum_app. change (zsum (map hd_kw [wl])) with (hd_kw wl + 0).
    unfold hd_kw at 2. destruct (Z.eqb_spec wl 0); [contradiction|]. lia. }
  assert (HF0L1: Forall (fun w => 0 <= w) L1).
  { rewrite HL1. apply Forall_app. split; [exact HFW0|]. constructor; [lia|constructor]. }
  pose proof (hd_count1_parity L1 HF0L1) as Hpar. rewrite HK2 in Hpar.
  set (c := Z.of_nat (length (filter (fun w => w =? 1) L1))) in *.
  assert (Hc2: (2 | c)).
  { replace c with (2 ^ log - (2 ^ log - c)) by lia.
    apply Z.divide_sub_r; [rewrite Hp2; apply Z.divide_factor_l | exact Hpar]. }
  assert (Hc1: 1 <= c).
  { pose proof HH as HH'. destruct HH' as [_ [_ [_ [_ [_ [_ [_ Hin1]]]]]]].
    apply (In_nth _ _ 0) in Hin1. destruct Hin1 as [i [Hi Hi1]].
    assert (Hpi: huf_present H (Z.of_nat i)).
    { split; [lia|]. unfold wh_weight, zn. rewrite Nat2Z.id, Hi1. lia. }
    pose proof (hd_present_le_last H HH (Z.of_nat i) Hpi) as Hile. fold last in Hile.
    assert (HinL1: In 1 L1).
    { rewrite <- Hi1. replace (nth i (wh_w H) 0) with (nth i L1 0).
      - apply nth_In. unfold L1. rewrite length_firstn. lia.
      - unfold L1. rewrite nth_firstn. destruct (Nat.ltb_spec i (Z.to_nat (last + 1))); [reflexivity|lia]. }
    assert (Hf: In 1 (filter (fun w => w =? 1) L1)) by (apply filter_In; split; [exact HinL1|reflexivity]).
    unfold c. destruct (filter (fun w => w =? 1) L1); [contradiction|]. cbn [length]. lia. }
  destruct Hc2 as [q Hq].
  replace (Z.odd c) with false by (rewrite Hq, Z.odd_mul, Bool.andb_false_r; reflexivity).
  destruct (Z.ltb_spec c 2); [lia|]. reflexivity.
Qed.

Lemma hd_direct_len : forall H, huf_ok H -> Zlength (huf_direct_bytes H) = 1 + (wh_last H + 1) / 2.
Proof.
  intros H HH. pose proof (hd_last_range H HH) as [[Hl0 Hl1] _]. unfold huf_direct_bytes.
  rewrite Zlength_cons, Zlength_correct, length_map, length_seq, Z2Nat.id; [lia|].
  apply Z.div_pos; lia.
Qed.

(* the direct form *)
Theorem huf_direct_weights : forall H rest,
  huf_ok H -> wh_last H <= 128 ->
  huf_desc_weights (huf_direct_bytes H ++ rest) = Some (hfw_weights H, Zlength (huf_direct_bytes H)).
Proof.
  intros H rest HH Hl128. pose proof (hd_direct_len H HH) as Hlen.
  pose proof (hd_last_pos H HH) as Hl1. pose proof (hd_last_range H HH) as [[Hl0 Hl2] _].
  pose proof (hd_log H HH).
  set (b := huf_direct_bytes H) in *. set (last := wh_last H) in *.
  unfold huf_desc_weights.
  assert (Hb0: byte_at (b ++ rest) 0 = 127 + last) by reflexivity.
  rewrite Hb0. replace (Zlength (b ++ rest)) with (Zlength b + Zlength rest) by (rewrite !Zlength_correct, length_app; lia). rewrite Hlen.
  assert (0 <= Zlength rest) by (rewrite Zlength_correct; lia).
  destruct (Z.ltb_spec (1 + (last + 1) / 2 + Zlength rest) 1); [pose proof (Z.div_pos (last + 1) 2); lia|].
  destruct (Z.geb_spec (127 + last) 128); [|lia].
  replace (127 + last - 127) with last by lia.
  destruct (Z.ltb_spec (1 + (last + 1) / 2 + Zlength rest) ((last + 1) / 2 + 1)); [lia|].
  f_equal. f_equal; [|lia].
  unfold huf_direct_weights, hfw_weights. fold last.
  assert (Hlw: length (wh_w H) = 256%nat) by apply (hd_len_w H HH).
  apply nth_ext with (d := 0) (d' := 0).
  { rewrite length_map, length_seq, length_firstn. lia. }
  intros n Hn. rewrite length_map, length_seq in Hn.
  rewrite hd_nth_map_seq by lia. rewrite nth_firstn. destruct (Nat.ltb_spec n (Z.to_nat last)); [|lia].
  cbv beta zeta. simpl (0 + n)%nat.
  assert (Hbyte: forall m, (2 * m < Z.to_nat last \/ 2 * m + 1 < Z.to_nat last)%nat ->
    byte_at (b ++ rest) (1 + Z.of_nat m) =
    wh_weight H (2 * Z.of_nat m) * 16 + (if 2 * Z.of_nat m + 1 <? last then wh_weight H (2 * Z.of_nat m + 1) else 0)).
  { intros m Hm. unfold byte_at. replace (Z.to_nat (1 + Z.of_nat m)) with (S m) by lia.
    assert (Hm2: (m < Z.to_nat ((last + 1) / 2))%nat).
    { pose proof (Z.div_mod (last + 1) 2). pose proof (Z.mod_pos_bound (last + 1) 2). lia. }
    rewrite app_nth1 by (unfold b, huf_direct_bytes; simpl; rewrite length_map, length_seq; fold last; lia).
    unfold b, huf_direct_bytes. cbn [nth]. fold last.
    rewrite hd_nth_map_seq by auto. reflexivity. }
  destruct (Nat.Even_or_Odd n) as [[m Hm]|[m Hm]]; subst n.
  - replace (Nat.even (2 * m)) with true by (symmetry; apply Nat.even_spec; exists m; reflexivity).
    replace (Z.of_nat (2 * m) / 2) with (Z.of_nat m) by (rewrite Nat2Z.inj_mul; change (Z.of_nat 2) with 2; rewrite Z.mul_comm, Z.div_mul; lia).
    rewrite Hbyte by lia.
    pose proof (hd_w_range H HH (2 * Z.of_nat m)). pose proof (hd_w_range H HH (2 * Z.of_nat m + 1)).
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    unfold wh_weight, zn. replace (Z.to_nat (2 * Z.of_nat m)) with (2 * m)%nat by lia.
    unfold wh_weight, zn in *. replace (Z.to_nat (2 * Z.of_nat m)) with (2 * m)%nat in * by lia.
    destruct (_ <? _); rewrite Z.div_add_l by lia; rewrite Z.div_small; lia.
  - replace (Nat.even (2 * m + 1)) with false.
    2:{ symmetry. apply Bool.not_true_iff_false. intro E. apply Nat.even_spec in E.
        destruct E as [k Hk]. lia. }
    replace (Z.of_nat (2 * m + 1) / 2) with (Z.of_nat m).
    2:{ rewrite Nat2Z.inj_add, Nat2Z.inj_mul. change (Z.of_nat 2) with 2. change (Z.of_nat 1) with 1. replace (2 * Z.of_nat m + 1) with (1 + Z.of_nat m * 2) by lia.
        rewrite Z.div_add by lia. reflexivity. }
    rewrite Hbyte by lia.
    destruct (Z.ltb_spec (2 * Z.of_nat m + 1) last); [|lia].
    pose proof (hd_w_range H HH (2 * Z.of_nat m)). pose proof (hd_w_range H HH (2 * Z.of_nat m + 1)).
    change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
    rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia.
    unfold wh_weight, zn. f_equal. lia.
Qed.

Lemma huf_direct_bytes_ok : forall H,
  huf_ok H -> wh_last H <= 128 ->
  bytes_ok (huf_direct_bytes H) /\ Zlength (huf_direct_bytes H) = 1 + (wh_last H + 1) / 2.
Proof.
  intros H HH Hl. pose proof (hd_last_range H HH) as [[Hl0 Hl1] _]. pose proof (hd_log H HH).
  unfold huf_direct_bytes. split.
  - constructor; [unfold is_byte; lia|]. apply Forall_forall. intros x Hx.
    apply in_map_iff in Hx. destruct Hx as [j [<- _]].
    pose proof (hd_w_range H HH (2 * Z.of_nat j)). pose proof (hd_w_range H HH (2 * Z.of_nat j + 1)).
    unfold is_byte. destruct (_ <? _); lia.
  - rewrite Zlength_cons, Zlength_correct, length_map, length_seq, Z2Nat.id; [lia|].
    apply Z.div_pos; lia.
Qed.

(* every lemma above together (huf_code_range, huf_stream_fields_ok, huf_stream_decode, huf_parse_of_weights, huf_direct_weights, huf_direct_bytes_ok) *)
Theorem wm_hufdec_all :
  (forall H s, huf_ok H -> huf_present H s -> 1 <= huf_nb_of H s <= 11 /\ 0 <= huf_code_of H s < 2 ^ huf_nb_of H s) /\
  (forall H lits, huf_ok H -> Forall (huf_present H) lits -> fields_ok (huf_stream_fields H lits)) /\
  (forall H lits, huf_ok H -> Forall (huf_present H) lits -> huf_decode_stream (huf_model H) (huf_stream_bytes H lits) (Zlength lits) = Some lits) /\
  (forall H b k, huf_ok H -> huf_desc_weights b = Some (hfw_weights H, k) -> huf_parse_desc b = Some (huf_model H, k)) /\
  (forall H rest, huf_ok H -> wh_last H <= 128 -> huf_desc_weights (huf_direct_bytes H ++ rest) = Some (hfw_weights H, Zlength (huf_direct_bytes H))) /\
  (forall H, huf_ok H -> wh_last H <= 128 -> bytes_ok (huf_direct_bytes H) /\ Zlength (huf_direct_bytes H) = 1 + (wh_last H + 1) / 2).
Proof.
  exact (conj huf_code_range (conj huf_stream_fields_ok (conj huf_stream_decode
    (conj huf_parse_of_weights (conj huf_direct_weights huf_direct_bytes_ok))))).
Qed.
