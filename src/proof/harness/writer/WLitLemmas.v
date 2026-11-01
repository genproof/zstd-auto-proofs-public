(* The literals sections written by put_literals_raw_rle / put_literals_huf (harness/writer.h) against
   the format model's decode_literals (src/proof/model/Block.v): plain Coq, unit-independent. *)
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Require Import Zstd.proof.harness.writer.model.WM_HufDec.
Require Import VST.zlist.sublist.
Local Open Scope Z_scope.

(* The Huffman stream lemmas of model/WM_HufDec.v (huf_code_range, huf_stream_fields_ok,
   huf_stream_decode), same statements and proofs, here as local
   helpers. *)
Section WLitHufDec.
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
  { intros i Hi. unfold ws, wh_weight, zn. rewrite List.nth_firstn, Nat2Z.id.
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

Lemma wl_huf_code_range : forall H s,
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

Lemma wl_huf_stream_fields_ok : forall H lits,
  huf_ok H -> Forall (huf_present H) lits -> fields_ok (huf_stream_fields H lits).
Proof.
  intros H lits HH Hl. unfold fields_ok, huf_stream_fields. apply List.Forall_map.
  apply Forall_rev in Hl. eapply Forall_impl; [|exact Hl]. intros c Hc. cbn [fst snd].
  pose proof (wl_huf_code_range H c HH Hc). lia.
Qed.

Lemma hd_fields_cons : forall H c l,
  huf_stream_fields H (c :: l) = huf_stream_fields H l ++ [(huf_code_of H c, huf_nb_of H c)].
Proof. intros. unfold huf_stream_fields. simpl. rewrite map_app. reflexivity. Qed.

Lemma hd_fields_range : forall H l, huf_ok H -> Forall (huf_present H) l ->
  0 <= fields_L (huf_stream_fields H l) /\
  0 <= fields_W (huf_stream_fields H l) < 2 ^ fields_L (huf_stream_fields H l).
Proof.
  intros. pose proof (fields_wl_range (huf_stream_fields H l) 0 0 (wl_huf_stream_fields_ok H l H0 H1)).
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
    pose proof (wl_huf_code_range H c HH Hc) as [Hnb _].
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

Theorem wl_huf_stream_decode : forall H lits,
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

End WLitHufDec.

(* put_literals_raw_rle's header: Size_Format x0 (1 byte, k <= 31), 01 (2 bytes, k <= 4095),
   11 (3 bytes, k <= 1048575) *)
Definition rawrle_hdr (f ty k: Z) : list Z :=
  if f =? 0 then le_bytes 1 (ty + 8 * k)
  else if f =? 1 then le_bytes 2 (ty + 4 + 16 * k)
  else le_bytes 3 (ty + 12 + 16 * k).

(* the header le_bytes n v in front of tl *)
Lemma rr_hdr : forall n v tl, (1 <= n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  byte_at (le_bytes n v ++ tl) 0 = v mod 256 /\
  le_field (le_bytes n v ++ tl) 0 (Z.of_nat n) = v /\
  (forall k, slice (le_bytes n v ++ tl) (Z.of_nat n) k = firstn (Z.to_nat k) tl) /\
  byte_at (le_bytes n v ++ tl) (Z.of_nat n) = nth 0 tl 0 /\
  Zlength (le_bytes n v ++ tl) = Z.of_nat n + Zlength tl.
Proof.
  intros n v tl Hn Hv. destruct n as [|n']; [lia |].
  split; [reflexivity |].
  split.
  { unfold le_field, slice. change (Z.to_nat 0) with O. rewrite skipn_O.
    rewrite wmb_firstn_le_bytes, Nat2Z.id, Nat.min_id, Nat.sub_diag. simpl firstn.
    rewrite app_nil_r, wmb_le_value_le_bytes. apply Z.mod_small; lia. }
  split.
  { intros k. unfold slice. rewrite Nat2Z.id, skipn_app, wmb_length_le_bytes, Nat.sub_diag.
    rewrite skipn_all2 by (rewrite wmb_length_le_bytes; lia). reflexivity. }
  split.
  { unfold byte_at. rewrite Nat2Z.id, app_nth2 by (rewrite wmb_length_le_bytes; lia).
    rewrite wmb_length_le_bytes, Nat.sub_diag. reflexivity. }
  rewrite Zlength_app, Zlength_correct, wmb_length_le_bytes. reflexivity.
Qed.

Lemma rr_raw : forall (lits rest: list Z), firstn (Z.to_nat (Zlength lits)) (lits ++ rest) = lits.
Proof.
  intros. rewrite ZtoNat_Zlength, List.firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r.
Qed.

Lemma rr_rle : forall (lits: list Z) (b: Z), lits = repeat (zn lits 0) (length lits) ->
  (0 < Zlength lits -> b = zn lits 0) -> repeat b (Z.to_nat (Zlength lits)) = lits.
Proof.
  intros lits b Hr Hb. rewrite ZtoNat_Zlength. destruct lits as [|x l]; [reflexivity |].
  rewrite Hb by (rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia). symmetry; exact Hr.
Qed.

Ltac rr_conds :=
  repeat (cbn [andb]; match goal with
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b); [try (exfalso; lia) |]
  | |- context [?a >? ?b] => destruct (Z.gtb_spec a b); [try (exfalso; lia) |]
  end); cbn [andb].

Lemma rr_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(* type 0: the literals; type 1: one byte b, lits[0] when there are literals *)
Lemma lit_rawrle_ok : forall f ty lits body bsm hprev,
  0 <= ty <= 1 -> bytes_ok lits ->
  (f = 0 /\ Zlength lits <= 31 \/ f = 1 /\ Zlength lits <= 4095 \/ f = 2 /\ Zlength lits <= 1048575) ->
  (ty = 0 -> body = lits) ->
  (ty = 1 -> lits = repeat (zn lits 0) (length lits) /\
             exists b, body = [b] /\ 0 <= b < 256 /\ (0 < Zlength lits -> b = zn lits 0)) ->
  Zlength lits <= bsm ->
  lit_ok hprev bsm lits hprev (rawrle_hdr f ty (Zlength lits) ++ body).
Proof.
  intros f ty lits body bsm hprev Hty Hlits Hf H0 H1 Hbsm.
  assert (Hk0: 0 <= Zlength lits) by apply Zlength_nonneg.
  split.
  { apply Forall_app; split.
    - unfold rawrle_hdr. destruct (f =? 0), (f =? 1); apply wmb_le_bytes_ok.
    - destruct (Z.eq_dec ty 0) as [E|E]; [rewrite H0 by auto; auto |].
      destruct (H1 ltac:(lia)) as [_ [b [-> [Hb _]]]]. repeat constructor; unfold is_byte; lia. }
  intros rest Hrest. rewrite <- app_assoc.
  assert (Hty': ty = 0 \/ ty = 1) by lia.
  destruct Hf as [[-> Hk] | [[-> Hk] | [-> Hk]]]; unfold rawrle_hdr; simpl Z.eqb; cbv iota.
  - set (k := Zlength lits) in *.
    destruct (rr_hdr 1 (ty + 8 * k) (body ++ rest)) as [Hb0 [Hlf [Hsl [Hbn Hlen]]]];
      [lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia |].
    simpl Z.of_nat in *.
    unfold decode_literals. rewrite Hlen, Hb0.
    rewrite (Z.mod_small (ty + 8 * k)) by lia. rewrite !Z.shiftr_div_pow2 by lia.
    change (2 ^ 2) with 4. change (2 ^ 3) with 8. rewrite !rr_land3.
    replace ((ty + 8 * k) mod 4) with ty by (Z.div_mod_to_equations; lia).
    replace ((ty + 8 * k) / 4) with (2 * k) by (Z.div_mod_to_equations; lia).
    replace ((ty + 8 * k) / 8) with k by (Z.div_mod_to_equations; lia).
    replace ((2 * k) mod 4 =? 1) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
    replace ((2 * k) mod 4 =? 3) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
    rewrite (Zlength_app _ (le_bytes _ _) body), (Zlength_correct (le_bytes _ _)), wmb_length_le_bytes. simpl Z.of_nat.
    destruct Hty' as [-> | ->].
    + rewrite H0 in Hsl, Hlen |- * by auto. simpl Z.eqb. cbv beta iota. rewrite Zlength_app.
      rr_conds.
      rewrite Hsl. unfold k. rewrite rr_raw. reflexivity.
    + destruct (H1 ltac:(lia)) as [Hr [b [-> [Hb Hb']]]].
      simpl Z.eqb. cbv beta iota.
      rewrite Zlength_app in *. change (Zlength [b]) with 1 in *. rr_conds.
      rewrite Hbn. simpl. unfold k. rewrite (rr_rle lits b Hr Hb'). reflexivity.
  - set (k := Zlength lits) in *.
    destruct (rr_hdr 2 (ty + 4 + 16 * k) (body ++ rest)) as [Hb0 [Hlf [Hsl [Hbn Hlen]]]];
      [lia | change (2 ^ (8 * Z.of_nat 2)) with 65536; lia |].
    simpl Z.of_nat in *.
    unfold decode_literals. rewrite Hlen, Hb0, Hlf. rewrite !Z.shiftr_div_pow2 by lia.
    change (2 ^ 2) with 4. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !rr_land3.
    replace ((ty + 4 + 16 * k) mod 256 mod 4) with ty by (Z.div_mod_to_equations; lia).
    replace ((ty + 4 + 16 * k) mod 256 / 4 mod 4) with 1 by (Z.div_mod_to_equations; lia).
    replace ((ty + 4 + 16 * k) / 16) with k by (Z.div_mod_to_equations; lia).
    simpl Z.eqb. cbv beta iota.
    rewrite (Zlength_app _ (le_bytes _ _) body), (Zlength_correct (le_bytes _ _)), wmb_length_le_bytes. simpl Z.of_nat.
    destruct Hty' as [-> | ->].
    + rewrite H0 in Hsl, Hlen |- * by auto. simpl Z.eqb. cbv beta iota. rewrite Zlength_app.
      rr_conds.
      rewrite Hsl. unfold k. rewrite rr_raw. reflexivity.
    + destruct (H1 ltac:(lia)) as [Hr [b [-> [Hb Hb']]]].
      simpl Z.eqb. cbv beta iota.
      rewrite Zlength_app in *. change (Zlength [b]) with 1 in *. rr_conds.
      rewrite Hbn. simpl. unfold k. rewrite (rr_rle lits b Hr Hb'). reflexivity.
  - set (k := Zlength lits) in *.
    destruct (rr_hdr 3 (ty + 12 + 16 * k) (body ++ rest)) as [Hb0 [Hlf [Hsl [Hbn Hlen]]]];
      [lia | change (2 ^ (8 * Z.of_nat 3)) with 16777216; lia |].
    simpl Z.of_nat in *.
    unfold decode_literals. rewrite Hlen, Hb0, Hlf. rewrite !Z.shiftr_div_pow2 by lia.
    change (2 ^ 2) with 4. change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !rr_land3.
    replace ((ty + 12 + 16 * k) mod 256 mod 4) with ty by (Z.div_mod_to_equations; lia).
    replace ((ty + 12 + 16 * k) mod 256 / 4 mod 4) with 3 by (Z.div_mod_to_equations; lia).
    replace ((ty + 12 + 16 * k) / 16) with k by (Z.div_mod_to_equations; lia).
    simpl Z.eqb. cbv beta iota.
    rewrite (Zlength_app _ (le_bytes _ _) body), (Zlength_correct (le_bytes _ _)), wmb_length_le_bytes. simpl Z.of_nat.
    destruct Hty' as [-> | ->].
    + rewrite H0 in Hsl, Hlen |- * by auto. simpl Z.eqb. cbv beta iota. rewrite Zlength_app.
      rr_conds.
      rewrite Hsl. unfold k. rewrite rr_raw. reflexivity.
    + destruct (H1 ltac:(lia)) as [Hr [b [-> [Hb Hb']]]].
      simpl Z.eqb. cbv beta iota.
      rewrite Zlength_app in *. change (Zlength [b]) with 1 in *. rr_conds.
      rewrite Hbn. simpl. unfold k. rewrite (rr_rle lits b Hr Hb'). reflexivity.
Qed.

(* put_literals_huf's header: Size_Format form (0: 1 stream, 1-3: 4 streams), Regenerated_Size k,
   Compressed_Size c *)
Definition huf_hdr (form ty k c: Z) : list Z :=
  if form <=? 1 then le_bytes 3 (ty + 4 * form + 16 * k + c * 2 ^ 14)
  else if form =? 2 then le_bytes 4 (ty + 8 + 16 * k + c * 2 ^ 18)
  else le_bytes 5 (ty + 12 + 16 * k + c * 2 ^ 22).

(* the jump table of the stream sizes a, b, c (each <= 65535) *)
Definition jump_table (a b c: Z) : list Z :=
  [a mod 256; a / 256; b mod 256; b / 256; c mod 256; c / 256].

(* the 4 streams: segments of (k+3)/4 literals, the last one the rest *)
Definition lit4_seg (lits: list Z) : Z := (Zlength lits + 3) / 4.

Definition lit4_streams (H: whuf) (lits: list Z) : list (list Z) :=
  let k := Zlength lits in
  let seg := lit4_seg lits in
  [huf_stream_bytes H (sublist 0 seg lits);
   huf_stream_bytes H (sublist seg (2 * seg) lits);
   huf_stream_bytes H (sublist (2 * seg) (3 * seg) lits);
   huf_stream_bytes H (sublist (3 * seg) k lits)].

Definition lit4_bytes (H: whuf) (lits: list Z) : list Z :=
  match lit4_streams H lits with
  | [s1; s2; s3; s4] => jump_table (Zlength s1) (Zlength s2) (Zlength s3) ++ s1 ++ s2 ++ s3 ++ s4
  | _ => nil
  end.

(* helpers of lit_huf_ok *)
Lemma wlh_slice_mid : forall (a b c: list Z) i n, i = Zlength a -> n = Zlength b ->
  slice (a ++ b ++ c) i n = b.
Proof.
  intros a b c i n -> ->. unfold slice. rewrite !Zlength_correct, !Nat2Z.id.
  rewrite skipn_app, skipn_all, Nat.sub_diag. simpl.
  rewrite List.firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r.
Qed.

Lemma wlh_div_split : forall a p Y, 0 <= p -> 0 <= a < 2 ^ p -> (a + 2 ^ p * Y) / 2 ^ p = Y.
Proof.
  intros a p Y Hp Ha. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma wlh_bits_mid : forall a x b p n, 0 <= p -> 0 <= n -> 0 <= a < 2 ^ p -> 0 <= x < 2 ^ n ->
  (a + 2 ^ p * (x + 2 ^ n * b)) / 2 ^ p mod 2 ^ n = x.
Proof.
  intros a x b p n Hp Hn Ha Hx. rewrite wlh_div_split by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma wlh_stream_ok : forall H l, huf_ok H -> Forall (huf_present H) l ->
  bytes_ok (huf_stream_bytes H l) /\ 1 <= Zlength (huf_stream_bytes H l).
Proof.
  intros H l HH Hl. pose proof (wl_huf_stream_fields_ok H l HH Hl) as F.
  pose proof (fields_wl_range _ 0 0 F ltac:(lia) ltac:(simpl; lia)) as [HL HW].
  unfold huf_stream_bytes, fields_mark, fields_W, fields_L.
  destruct (bw_mark_len (fst (fields_wl (huf_stream_fields H l) 0 0)) (snd (fields_wl (huf_stream_fields H l) 0 0)))
    as [A B]; try lia.
  split; auto. assert (0 <= snd (fields_wl (huf_stream_fields H l) 0 0) / 8) by (apply Z.div_pos; lia). lia.
Qed.

Lemma wlh_jump_field : forall (a: Z) (r: list Z), 0 <= a ->
  le_value (firstn 2 (a mod 256 :: a / 256 :: r)) = a.
Proof.
  intros a r Ha. cbn [firstn le_value]. pose proof (Z.div_mod a 256 ltac:(lia)). lia.
Qed.

Lemma wlh_lit4 : forall H lits, huf_ok H -> Forall (huf_present H) lits -> 6 <= Zlength lits ->
  Forall (fun s => Zlength s <= 65535) (firstn 3 (lit4_streams H lits)) ->
  bytes_ok (lit4_bytes H lits) /\ 1 <= Zlength (lit4_bytes H lits) /\
  huf_decode_4streams (huf_model H) (lit4_bytes H lits) (Zlength lits) = Some lits.
Proof.
  intros H lits HH Hp Hk H3.
  unfold lit4_bytes, lit4_streams, lit4_seg in *. cbv zeta in *.
  set (k := Zlength lits) in *. set (seg := (k + 3) / 4) in *.
  assert (Hseg: 2 <= seg /\ 3 * seg <= k).
  { pose proof (Z.div_mod (k + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 3) 4 ltac:(lia)). lia. }
  set (l1 := sublist 0 seg lits) in *. set (l2 := sublist seg (2 * seg) lits) in *.
  set (l3 := sublist (2 * seg) (3 * seg) lits) in *. set (l4 := sublist (3 * seg) k lits) in *.
  assert (Hz1: Zlength l1 = seg) by (unfold l1; rewrite Zlength_sublist; lia).
  assert (Hz2: Zlength l2 = seg) by (unfold l2; rewrite Zlength_sublist; lia).
  assert (Hz3: Zlength l3 = seg) by (unfold l3; rewrite Zlength_sublist; lia).
  assert (Hz4: Zlength l4 = k - 3 * seg) by (unfold l4; rewrite Zlength_sublist; lia).
  assert (Hl: l1 ++ l2 ++ l3 ++ l4 = lits).
  { unfold l1, l2, l3, l4. rewrite !sublist_rejoin by lia. apply sublist_same; lia. }
  assert (P1: Forall (huf_present H) l1) by apply Forall_sublist, Hp.
  assert (P2: Forall (huf_present H) l2) by apply Forall_sublist, Hp.
  assert (P3: Forall (huf_present H) l3) by apply Forall_sublist, Hp.
  assert (P4: Forall (huf_present H) l4) by apply Forall_sublist, Hp.
  destruct (wlh_stream_ok H l1 HH P1) as [B1 Z1].
  destruct (wlh_stream_ok H l2 HH P2) as [B2 Z2].
  destruct (wlh_stream_ok H l3 HH P3) as [B3 Z3].
  destruct (wlh_stream_ok H l4 HH P4) as [B4 Z4].
  set (s1 := huf_stream_bytes H l1) in *. set (s2 := huf_stream_bytes H l2) in *.
  set (s3 := huf_stream_bytes H l3) in *. set (s4 := huf_stream_bytes H l4) in *.
  simpl firstn in H3. inversion H3 as [| ? ? M1 H3']; inversion H3' as [| ? ? M2 H3'']; inversion H3'' as [| ? ? M3 _].
  clear H3 H3' H3''.
  set (jt := jump_table (Zlength s1) (Zlength s2) (Zlength s3)).
  assert (Hjt: Zlength jt = 6) by reflexivity.
  assert (Bjt: bytes_ok jt).
  { unfold jt, jump_table. pose proof (Zlength_nonneg s1). pose proof (Zlength_nonneg s2). pose proof (Zlength_nonneg s3).
    repeat (apply Forall_cons; [unfold is_byte; split;
      first [apply Z.mod_pos_bound; lia | apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia] |]).
    apply Forall_nil. }
  assert (Hlen: Zlength (jt ++ s1 ++ s2 ++ s3 ++ s4) = 6 + Zlength s1 + Zlength s2 + Zlength s3 + Zlength s4)
    by (rewrite !Zlength_app; lia).
  split; [| split].
  - repeat (apply Forall_app; split); auto.
  - lia.
  - unfold huf_decode_4streams. rewrite <- Zlength_correct, Hlen.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    assert (F1: le_field (jt ++ s1 ++ s2 ++ s3 ++ s4) 0 2 = Zlength s1)
      by (apply wlh_jump_field; apply Zlength_nonneg; auto).
    assert (F2: le_field (jt ++ s1 ++ s2 ++ s3 ++ s4) 2 2 = Zlength s2)
      by (apply wlh_jump_field; apply Zlength_nonneg; auto).
    assert (F3: le_field (jt ++ s1 ++ s2 ++ s3 ++ s4) 4 2 = Zlength s3)
      by (apply wlh_jump_field; apply Zlength_nonneg; auto).
    rewrite F1, F2, F3.
    replace (6 + Zlength s1 + Zlength s2 + Zlength s3 + Zlength s4 - 6 - Zlength s1 - Zlength s2 - Zlength s3)
      with (Zlength s4) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite (wlh_slice_mid jt s1 (s2 ++ s3 ++ s4)) by auto.
    replace (jt ++ s1 ++ s2 ++ s3 ++ s4) with ((jt ++ s1) ++ s2 ++ (s3 ++ s4)) by (rewrite <- !app_assoc; reflexivity).
    rewrite wlh_slice_mid by (rewrite ?Zlength_app; lia).
    replace ((jt ++ s1) ++ s2 ++ s3 ++ s4) with ((jt ++ s1 ++ s2) ++ s3 ++ s4) by (rewrite <- !app_assoc; reflexivity).
    rewrite wlh_slice_mid by (rewrite ?Zlength_app; lia).
    replace ((jt ++ s1 ++ s2) ++ s3 ++ s4) with ((jt ++ s1 ++ s2 ++ s3) ++ s4 ++ nil) by (rewrite <- !app_assoc, app_nil_r; reflexivity).
    rewrite wlh_slice_mid by (rewrite ?Zlength_app; lia).
    pose proof (wl_huf_stream_decode H l1 HH P1) as D1. pose proof (wl_huf_stream_decode H l2 HH P2) as D2.
    pose proof (wl_huf_stream_decode H l3 HH P3) as D3. pose proof (wl_huf_stream_decode H l4 HH P4) as D4.
    fold s1 s2 s3 s4 in D1, D2, D3, D4. rewrite Hz1 in D1. rewrite Hz2 in D2. rewrite Hz3 in D3. rewrite Hz4 in D4.
    fold seg. rewrite D1, D2, D3, D4, Hl. reflexivity.
Qed.

Definition wlh_hdr_fields (B: list Z) (form: Z) : Z * Z * Z * bool :=
  let lhc := le_field B 0 4 in
  if form =? 2 then (4, Z.land (Z.shiftr lhc 4) 16383, Z.shiftr lhc 18, false)
  else if form =? 3 then (5, Z.land (Z.shiftr lhc 4) 262143, Z.shiftr lhc 22 + byte_at B 4 * 1024, false)
  else (3, Z.land (Z.shiftr lhc 4) 1023, Z.land (Z.shiftr lhc 14) 1023, form =? 0).

Lemma wlh_decode : forall hprev B bsm ty form lh k c t hsize l,
  (ty = 2 \/ ty = 3) -> 0 <= form <= 3 ->
  Z.land (byte_at B 0) 3 = ty -> Z.land (Z.shiftr (byte_at B 0) 2) 3 = form ->
  5 <= Zlength B ->
  wlh_hdr_fields B form = (lh, k, c, form =? 0) ->
  k <= bsm -> (form <> 0 -> 6 <= k) -> c + lh <= Zlength B ->
  (ty = 3 -> hprev = Some t /\ hsize = 0) ->
  (ty = 2 -> huf_parse_desc (slice B lh c) = Some (t, hsize) /\ hsize < c) ->
  (if form =? 0 then huf_decode_stream t (skipn (Z.to_nat hsize) (slice B lh c)) k
   else huf_decode_4streams t (skipn (Z.to_nat hsize) (slice B lh c)) k) = Some l ->
  decode_literals hprev B bsm = Some (l, lh + c, Some t).
Proof.
  intros hprev B bsm ty form lh k c t hsize l Hty Hf Hb0 Hb1 HB Hhdr Hbsm H6 Hc H3 H2 Hdec.
  unfold decode_literals. cbv zeta. unfold wlh_hdr_fields in Hhdr. cbv zeta in Hhdr.
  rewrite Hb0, Hb1, Hhdr.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  assert (E4: (negb (form =? 0) && (k <? MIN_LITERALS_FOR_4_STREAMS))%bool = false).
  { destruct (form =? 0) eqn:E; [reflexivity |]. apply Z.eqb_neq in E.
    cbn [negb andb]. apply Z.ltb_ge. unfold MIN_LITERALS_FOR_4_STREAMS. auto. }
  rewrite (proj2 (Z.ltb_ge (Zlength B) 5)) by lia.
  rewrite E4, Z.gtb_ltb, (proj2 (Z.ltb_ge bsm k)) by lia.
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge (Zlength B) (c + lh))) by lia.
  destruct Hty as [-> | ->]; simpl Z.eqb; cbn [andb].
  - destruct (H2 eq_refl) as [Hp Hs]. rewrite Hp, Z.geb_leb, (proj2 (Z.leb_gt _ _)) by lia.
    rewrite Hdec. reflexivity.
  - destruct (H3 eq_refl) as [-> ->]. rewrite Hdec. reflexivity.
Qed.

Lemma wlh_b0 : forall V ty form Y, 0 <= ty < 4 -> 0 <= form < 4 -> V = ty + 2 ^ 2 * (form + 2 ^ 2 * Y) ->
  Z.land (V mod 256) 3 = ty /\ Z.land (Z.shiftr (V mod 256) 2) 3 = form.
Proof.
  intros V ty form Y Hty Hf HV.
  change 3 with (Z.ones 2). rewrite !Z.land_ones, Z.shiftr_div_pow2 by lia. change 256 with (2 ^ 8).
  split.
  - rewrite <- (Z.div_1_r (V mod 2 ^ 8)). change 1 with (2 ^ 0). rewrite wmb_mod_div_mod by lia.
    replace V with (0 + 2 ^ 0 * (ty + 2 ^ 2 * (form + 2 ^ 2 * Y))) by (subst; ring).
    apply wlh_bits_mid; simpl; lia.
  - rewrite wmb_mod_div_mod by lia. subst V. apply wlh_bits_mid; simpl; lia.
Qed.

Lemma wlh_le4_3 : forall V r0 R, 0 <= V < 2 ^ 24 ->
  le_field (le_bytes 3 V ++ r0 :: R) 0 4 = V + 2 ^ 24 * r0.
Proof.
  intros V r0 R HV. unfold le_field, slice. change (Z.to_nat 0) with O. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_O, wmb_firstn_le_bytes. simpl (Nat.min 4 3). simpl (firstn (4 - 3) (r0 :: R)).
  rewrite wmb_le_value_app, wmb_le_value_le_bytes, wmb_length_le_bytes.
  rewrite Z.mod_small by (simpl; lia). cbn [le_value]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.

Lemma wlh_le4_big : forall n V R, (4 <= n)%nat ->
  le_field (le_bytes n V ++ R) 0 4 = V mod 2 ^ 32.
Proof.
  intros n V R Hn. unfold le_field, slice. change (Z.to_nat 0) with O. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_O, wmb_firstn_le_bytes. replace (Nat.min 4 n) with 4%nat by lia.
  replace (4 - n)%nat with O by lia. simpl firstn. rewrite app_nil_r, wmb_le_value_le_bytes. reflexivity.
Qed.

Ltac wlh_zpow := repeat match goal with |- context [2 ^ ?n] =>
  lazymatch n with Z.pos _ => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v in * end end.

Lemma wlh_hdr : forall form ty k c R, (ty = 2 \/ ty = 3) -> 0 <= k -> 0 <= c ->
  (form = 0 /\ k <= 1023 /\ c <= 1023 \/ form = 1 /\ k <= 1023 /\ c <= 1023 \/
   form = 2 /\ k <= 16383 /\ c <= 16383 \/ form = 3 /\ k <= 262143 /\ c <= 262143) ->
  1 <= Zlength R ->
  Z.land (byte_at (huf_hdr form ty k c ++ R) 0) 3 = ty /\
  Z.land (Z.shiftr (byte_at (huf_hdr form ty k c ++ R) 0) 2) 3 = form /\
  wlh_hdr_fields (huf_hdr form ty k c ++ R) form = (Zlength (huf_hdr form ty k c), k, c, form =? 0).
Proof.
  intros form ty k c R Hty Hk Hc Hf HR.
  assert (Hty': 0 <= ty < 4) by lia.
  destruct R as [| r0 R']; [rewrite Zlength_nil in HR; lia |].
  destruct Hf as [(-> & ? & ?) | [(-> & ? & ?) | [(-> & ? & ?) | (-> & ? & ?)]]].
  - unfold huf_hdr. replace (0 <=? 1) with true by reflexivity. cbv beta iota.
    set (V := ty + 4 * 0 + 16 * k + c * 2 ^ 14).
    assert (HV: 0 <= V < 2 ^ 24) by (unfold V; change (2 ^ 14) with 16384; change (2 ^ 24) with 16777216; lia).
    change (byte_at (le_bytes 3 V ++ r0 :: R') 0) with (V mod 256).
    assert (EV: V = ty + 2 ^ 2 * (0 + 2 ^ 2 * (k + 2 ^ 10 * c))) by (unfold V; ring).
    destruct (wlh_b0 V ty 0 (k + 2 ^ 10 * c) ltac:(lia) ltac:(lia) EV) as [B1 B2].
    split; [exact B1 | split; [exact B2 |]].
    unfold wlh_hdr_fields. replace (0 =? 2) with false by reflexivity. replace (0 =? 3) with false by reflexivity.
    cbv beta iota zeta. rewrite wlh_le4_3 by lia.
    rewrite Zlength_correct, wmb_length_le_bytes.
    change 1023 with (Z.ones 10). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    assert (K1: (V + 2 ^ 24 * r0) / 2 ^ 4 mod 2 ^ 10 = k).
    { replace (V + 2 ^ 24 * r0) with ((ty + 4 * 0) + 2 ^ 4 * (k + 2 ^ 10 * (c + 2 ^ 10 * r0))) by (unfold V; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    assert (K2: (V + 2 ^ 24 * r0) / 2 ^ 14 mod 2 ^ 10 = c).
    { replace (V + 2 ^ 24 * r0) with ((ty + 4 * 0 + 16 * k) + 2 ^ 14 * (c + 2 ^ 10 * r0)) by (unfold V; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    rewrite K1, K2. reflexivity.
  - unfold huf_hdr. replace (1 <=? 1) with true by reflexivity. cbv beta iota.
    set (V := ty + 4 * 1 + 16 * k + c * 2 ^ 14).
    assert (HV: 0 <= V < 2 ^ 24) by (unfold V; change (2 ^ 14) with 16384; change (2 ^ 24) with 16777216; lia).
    change (byte_at (le_bytes 3 V ++ r0 :: R') 0) with (V mod 256).
    assert (EV: V = ty + 2 ^ 2 * (1 + 2 ^ 2 * (k + 2 ^ 10 * c))) by (unfold V; ring).
    destruct (wlh_b0 V ty 1 (k + 2 ^ 10 * c) ltac:(lia) ltac:(lia) EV) as [B1 B2].
    split; [exact B1 | split; [exact B2 |]].
    unfold wlh_hdr_fields. replace (1 =? 2) with false by reflexivity. replace (1 =? 3) with false by reflexivity.
    cbv beta iota zeta. rewrite wlh_le4_3 by lia.
    rewrite Zlength_correct, wmb_length_le_bytes.
    change 1023 with (Z.ones 10). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    assert (K1: (V + 2 ^ 24 * r0) / 2 ^ 4 mod 2 ^ 10 = k).
    { replace (V + 2 ^ 24 * r0) with ((ty + 4 * 1) + 2 ^ 4 * (k + 2 ^ 10 * (c + 2 ^ 10 * r0))) by (unfold V; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    assert (K2: (V + 2 ^ 24 * r0) / 2 ^ 14 mod 2 ^ 10 = c).
    { replace (V + 2 ^ 24 * r0) with ((ty + 4 * 1 + 16 * k) + 2 ^ 14 * (c + 2 ^ 10 * r0)) by (unfold V; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    rewrite K1, K2. reflexivity.
  - unfold huf_hdr. replace (2 <=? 1) with false by reflexivity. replace (2 =? 2) with true by reflexivity.
    cbv beta iota.
    set (V := ty + 8 + 16 * k + c * 2 ^ 18).
    assert (HV: 0 <= V < 2 ^ 32) by (unfold V; wlh_zpow; lia).
    change (byte_at (le_bytes 4 V ++ r0 :: R') 0) with (V mod 256).
    assert (EV: V = ty + 2 ^ 2 * (2 + 2 ^ 2 * (k + 2 ^ 14 * c))) by (unfold V; wlh_zpow; ring).
    destruct (wlh_b0 V ty 2 (k + 2 ^ 14 * c) ltac:(lia) ltac:(lia) EV) as [B1 B2].
    split; [exact B1 | split; [exact B2 |]].
    unfold wlh_hdr_fields. replace (2 =? 2) with true by reflexivity.
    cbv beta iota zeta. rewrite wlh_le4_big by lia. rewrite (Z.mod_small V) by lia.
    rewrite Zlength_correct, wmb_length_le_bytes.
    change 16383 with (Z.ones 14). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    assert (K1: V / 2 ^ 4 mod 2 ^ 14 = k).
    { replace V with ((ty + 8) + 2 ^ 4 * (k + 2 ^ 14 * c)) by (unfold V; wlh_zpow; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    assert (K2: V / 2 ^ 18 = c).
    { replace V with ((ty + 8 + 16 * k) + 2 ^ 18 * c) by (unfold V; ring).
      apply wlh_div_split; wlh_zpow; lia. }
    rewrite K1, K2. reflexivity.
  - unfold huf_hdr. replace (3 <=? 1) with false by reflexivity. replace (3 =? 2) with false by reflexivity.
    cbv beta iota.
    set (V := ty + 12 + 16 * k + c * 2 ^ 22).
    change (byte_at (le_bytes 5 V ++ r0 :: R') 0) with (V mod 256).
    assert (EV: V = ty + 2 ^ 2 * (3 + 2 ^ 2 * (k + 2 ^ 18 * c))) by (unfold V; wlh_zpow; ring).
    destruct (wlh_b0 V ty 3 (k + 2 ^ 18 * c) ltac:(lia) ltac:(lia) EV) as [B1 B2].
    split; [exact B1 | split; [exact B2 |]].
    unfold wlh_hdr_fields. replace (3 =? 2) with false by reflexivity. replace (3 =? 3) with true by reflexivity.
    cbv beta iota zeta. rewrite wlh_le4_big by lia.
    rewrite Zlength_correct, wmb_length_le_bytes.
    change 262143 with (Z.ones 18). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    assert (K1: (V mod 2 ^ 32) / 2 ^ 4 mod 2 ^ 18 = k).
    { rewrite wmb_mod_div_mod by lia.
      replace V with ((ty + 12) + 2 ^ 4 * (k + 2 ^ 18 * c)) by (unfold V; wlh_zpow; ring).
      apply wlh_bits_mid; wlh_zpow; lia. }
    pose proof (Z.div_mod c (2 ^ 10) ltac:(lia)) as Hcd. pose proof (Z.mod_pos_bound c (2 ^ 10) ltac:(lia)) as Hcm.
    assert (Hcq: 0 <= c / 2 ^ 10 < 2 ^ 8) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; wlh_zpow; lia).
    assert (EV2: V = (ty + 12 + 16 * k + 2 ^ 22 * (c mod 2 ^ 10)) + 2 ^ 32 * (c / 2 ^ 10)).
    { unfold V. rewrite Hcd at 1. wlh_zpow. ring. }
    assert (Hlo: 0 <= ty + 12 + 16 * k + 2 ^ 22 * (c mod 2 ^ 10) < 2 ^ 32) by (wlh_zpow; lia).
    assert (K2: (V mod 2 ^ 32) / 2 ^ 22 = c mod 2 ^ 10).
    { rewrite EV2, (Z.mul_comm (2 ^ 32) (c / 2 ^ 10)), Z.mod_add, Z.mod_small by (wlh_zpow; lia).
      apply wlh_div_split; wlh_zpow; lia. }
    assert (K3: byte_at (le_bytes 5 V ++ r0 :: R') 4 = c / 2 ^ 10).
    { change (byte_at (le_bytes 5 V ++ r0 :: R') 4) with (((((V / 256) / 256) / 256) / 256) mod 256).
      rewrite !Z.div_div by lia. change (256 * 256 * 256 * 256) with (2 ^ 32).
      rewrite EV2, wlh_div_split by lia. apply Z.mod_small. wlh_zpow; lia. }
    rewrite K1, K2, K3. f_equal. f_equal. wlh_zpow. lia.
Qed.

(* d: the tree description (type 2) or nothing (type 3, treeless) *)
Lemma lit_huf_ok : forall H lits ty d (streams4: bool) form bsm hprev,
  huf_ok H -> Forall (huf_present H) lits -> 2 <= ty <= 3 ->
  (ty = 2 -> huf_desc_ok H d) -> (ty = 3 -> d = nil) ->
  let k := Zlength lits in
  let st := if streams4 then lit4_bytes H lits else huf_stream_bytes H lits in
  let c := Zlength (d ++ st) in
  (if streams4 then
     6 <= k /\ Forall (fun s => Zlength s <= 65535) (firstn 3 (lit4_streams H lits)) /\
     (form = 1 /\ k <= 1023 /\ c <= 1023 \/ form = 2 /\ k <= 16383 /\ c <= 16383 \/
      form = 3 /\ k <= 262143 /\ c <= 262143)
   else form = 0 /\ k <= 1023 /\ c <= 1023) ->
  k <= bsm -> (ty = 3 -> hprev = Some (huf_model H)) ->
  lit_ok hprev bsm lits (Some (huf_model H)) (huf_hdr form ty k c ++ d ++ st).
Proof.
  intros H lits ty d streams4 form bsm hprev HH Hp Hty Hd2 Hd3 k st c Hcase Hk Hprev.
  assert (Hst: bytes_ok st /\ 1 <= Zlength st /\
    (if streams4 then huf_decode_4streams (huf_model H) st k else huf_decode_stream (huf_model H) st k) = Some lits).
  { unfold st, k. destruct streams4.
    - destruct Hcase as (H6 & H65 & _). apply wlh_lit4; auto.
    - destruct (wlh_stream_ok H lits HH Hp) as [A B]. split; [| split]; auto. apply wl_huf_stream_decode; auto. }
  destruct Hst as (Bst & Lst & Dst).
  assert (Hd: bytes_ok d /\ (ty = 2 -> forall rest, huf_parse_desc (d ++ rest) = Some (huf_model H, Zlength d))).
  { destruct (Z.eq_dec ty 2) as [E | E].
    - destruct (Hd2 E) as (A & _ & C). split; auto.
    - rewrite (Hd3 ltac:(lia)). split; [constructor | intros; lia]. }
  destruct Hd as [Bd Pd].
  assert (Hc: c = Zlength d + Zlength st) by (unfold c; apply Zlength_app).
  assert (Hk0: 0 <= k) by apply Zlength_nonneg.
  assert (Hd0: 0 <= Zlength d) by apply Zlength_nonneg.
  assert (Hf: (form = 0 /\ k <= 1023 /\ c <= 1023 \/ form = 1 /\ k <= 1023 /\ c <= 1023 \/
     form = 2 /\ k <= 16383 /\ c <= 16383 \/ form = 3 /\ k <= 262143 /\ c <= 262143) /\
     (form = 0 <-> streams4 = false) /\ (form <> 0 -> 6 <= k)).
  { destruct streams4; [destruct Hcase as (H6 & _ & [? | [? | ?]]) | ]; repeat split; try lia; discriminate. }
  destruct Hf as (Hf & Hf0 & Hf6).
  set (hdr := huf_hdr form ty k c).
  assert (Hh: bytes_ok hdr /\ 3 <= Zlength hdr).
  { unfold hdr, huf_hdr.
    destruct (form <=? 1); [| destruct (form =? 2)]; (split; [apply wmb_le_bytes_ok |]);
      rewrite Zlength_correct, wmb_length_le_bytes; simpl; lia. }
  destruct Hh as [Bh Lh].
  split.
  - unfold bytes_ok. repeat (apply Forall_app; split); auto.
  - intros rest Hrest.
    rewrite app_assoc_reverse.
    destruct (wlh_hdr form ty k c ((d ++ st) ++ rest)) as (B0 & B1 & Bf); try lia.
    { rewrite !Zlength_app. lia. }
    fold hdr in B0, B1, Bf.
    assert (Lb: Zlength (hdr ++ (d ++ st) ++ rest) = Zlength hdr + c + Zlength rest) by (rewrite !Zlength_app; lia).
    assert (Sl: slice (hdr ++ (d ++ st) ++ rest) (Zlength hdr) c = d ++ st) by (apply wlh_slice_mid; auto).
    rewrite (Zlength_app _ hdr (d ++ st)).
    fold c.
    apply (wlh_decode hprev _ bsm ty form (Zlength hdr) k c (huf_model H) (if ty =? 2 then Zlength d else 0));
      auto; try lia.
    + intros E. split; [auto | rewrite (proj2 (Z.eqb_neq ty 2)) by lia; reflexivity].
    + rewrite Sl. intros E. rewrite (proj2 (Z.eqb_eq ty 2) E). split; [apply Pd; auto | lia].
    + rewrite Sl.
      replace (skipn (Z.to_nat (if ty =? 2 then Zlength d else 0)) (d ++ st)) with st.
      * destruct streams4; destruct (form =? 0) eqn:E; auto.
        -- apply Z.eqb_eq in E. apply Hf0 in E. discriminate.
        -- apply Z.eqb_neq in E. exfalso. apply E, Hf0. reflexivity.
      * destruct (Z.eq_dec ty 2) as [E | E].
        -- rewrite (proj2 (Z.eqb_eq ty 2) E). rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
        -- rewrite (proj2 (Z.eqb_neq ty 2) E). rewrite (Hd3 ltac:(lia)). reflexivity.
Qed.
