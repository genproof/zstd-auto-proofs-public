(* Unit-independent lemmas for the writer's body group huf_desc (huf_put_description, huf_put_stream):
   see the template WB_huf_desc. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Require Import Zstd.proof.harness.writer.WHufDescSibDec.
Require Import Zstd.proof.harness.writer.WHufDescSibHfw.
From Coq Require Import Sorting.Sorted.
Require Import Zstd.proof.harness.writer.model.WB_BitsMath.
Local Open Scope Z_scope.

(* the fields of huf_put_stream after the literals lits[i..n) *)
Definition hs_fields (H: whuf) (lits: list Z) (i: Z) : list (Z * Z) :=
  huf_stream_fields H (sublist i (Zlength lits) lits).
Definition hs_W (H: whuf) (lits: list Z) (i: Z) : Z := fields_W (hs_fields H lits i).
Definition hs_L (H: whuf) (lits: list Z) (i: Z) : Z := fields_L (hs_fields H lits i).

Lemma hs_fields_step : forall H lits i, 0 < i <= Zlength lits ->
  hs_fields H lits (i - 1) =
  hs_fields H lits i ++ [(huf_code_of H (Znth (i - 1) lits), huf_nb_of H (Znth (i - 1) lits))].
Proof.
  intros. unfold hs_fields, huf_stream_fields.
  rewrite (sublist_split (i - 1) i (Zlength lits)) by lia.
  rewrite (sublist_one (i - 1) i) by lia. simpl app. simpl rev. rewrite map_app. reflexivity.
Qed.

Lemma hs_step_wl : forall H lits i, 0 < i <= Zlength lits ->
  hs_W H lits (i - 1) = hs_W H lits i + huf_code_of H (Znth (i - 1) lits) * 2 ^ hs_L H lits i /\
  hs_L H lits (i - 1) = hs_L H lits i + huf_nb_of H (Znth (i - 1) lits).
Proof.
  intros. unfold hs_W, hs_L, fields_W, fields_L. rewrite hs_fields_step by auto.
  rewrite fields_wl_app. simpl. auto.
Qed.

Lemma hs_fields_ok : forall H lits i, huf_ok H -> Forall (huf_present H) lits -> 0 <= i <= Zlength lits ->
  fields_ok (hs_fields H lits i).
Proof.
  intros. apply huf_stream_fields_ok; auto. apply Forall_sublist; auto.
Qed.

Lemma hs_range : forall H lits i, huf_ok H -> Forall (huf_present H) lits -> 0 <= i <= Zlength lits ->
  0 <= hs_L H lits i /\ 0 <= hs_W H lits i < 2 ^ hs_L H lits i.
Proof.
  intros. unfold hs_W, hs_L, fields_W, fields_L.
  destruct (fields_wl_range (hs_fields H lits i) 0 0) as [A B]; [apply hs_fields_ok; auto | lia | simpl; lia |].
  lia.
Qed.

Lemma hs_init : forall H lits, hs_W H lits (Zlength lits) = 0 /\ hs_L H lits (Zlength lits) = 0.
Proof. intros. unfold hs_W, hs_L, hs_fields. rewrite sublist_nil. split; reflexivity. Qed.

Lemma hs_final : forall H lits, bw_mark (hs_W H lits 0) (hs_L H lits 0) = huf_stream_bytes H lits.
Proof. intros. unfold hs_W, hs_L, hs_fields. rewrite sublist_same by lia. reflexivity. Qed.

(* the tail of an output after two appends *)
Lemma tl_sub_sub : forall (tl: list val) a b, 0 <= a -> 0 <= b ->
  sublist a (Zlength (sublist b (Zlength tl) tl)) (sublist b (Zlength tl) tl) =
  sublist (a + b) (Zlength tl) tl.
Proof.
  intros. destruct (Z.le_gt_cases b (Zlength tl)).
  - destruct (Z.le_gt_cases (a + b) (Zlength tl)).
    + rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
    + rewrite !sublist_nil_gen; auto; rewrite ?Zlength_sublist; lia.
  - rewrite (sublist_nil_gen _ b) by lia. rewrite (sublist_nil_gen _ (a + b)) by lia.
    rewrite Zlength_nil. apply sublist_nil_gen. lia.
Qed.

Lemma bw_full_len : forall W L, 0 <= L -> Zlength (bw_full W L) = L / 8.
Proof.
  intros. unfold bw_full. rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id.
  apply Z.div_pos; lia.
Qed.

(* Znth over a list of values with different (convertible) Inhabitant instances: normalize them all to
   @Znth val Vundef (as WMiscLemmas.norm_znth) *)
Ltac hd_norm_znth :=
  repeat match goal with
  | |- context [@Znth ?A ?d ?i ?l] =>
      tryif constr_eq d Vundef then fail
      else (unify A val; change (@Znth A d i l) with (@Znth val Vundef i l))
  | H: context [@Znth ?A ?d ?i ?l] |- _ =>
      tryif constr_eq d Vundef then fail
      else (unify A val; change (@Znth A d i l) with (@Znth val Vundef i l) in H)
  end.

(* ---------- huf_put_description ---------- *)

Lemma hd_sorted_filter : forall f n a,
  StronglySorted Z.lt (filter f (map Z.of_nat (seq a n))).
Proof.
  induction n; intros a; simpl; [constructor |].
  destruct (f (Z.of_nat a)); [| apply IHn].
  constructor; [apply IHn |].
  apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _].
  apply in_map_iff in Hx as (y & <- & Hy). apply in_seq in Hy. lia.
Qed.

Lemma hd_last_In : forall (l: list Z) d, l <> [] -> In (last l d) l.
Proof.
  induction l as [| a l IH]; intros d Hn; [congruence |].
  destruct l as [| b l]; [left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma hd_last_sorted : forall l, StronglySorted Z.lt l -> Forall (fun x => 0 <= x) l -> (2 <= length l)%nat ->
  1 <= last l 0.
Proof.
  intros l Hs Hp Hl. destruct l as [| a [| b l]]; simpl in Hl; try lia.
  inversion Hs; subst. inversion Hp; subst.
  assert (Hin: In (last (b :: l) 0) (b :: l)) by (apply hd_last_In; discriminate).
  change (last (a :: b :: l) 0) with (last (b :: l) 0).
  rewrite Forall_forall in H2. specialize (H2 _ Hin). lia.
Qed.

Lemma hd_last_pos : forall H, huf_ok H -> 1 <= wh_last H.
Proof.
  intros H (_ & _ & _ & _ & Hu & Hn & Hl & _). rewrite Hl, Hu. apply hd_last_sorted.
  - apply hd_sorted_filter.
  - apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. apply in_map_iff in Hx as (y & <- & _). lia.
  - rewrite Hu, Zlength_correct in Hn. lia.
Qed.

Lemma hd_last_le : forall H, huf_ok H -> wh_last H <= 255.
Proof.
  intros H (_ & _ & _ & _ & Hu & Hn & Hl & _). rewrite Hl.
  assert (Hne: wh_used H <> []) by (intro E; rewrite E, Zlength_nil in Hn; lia).
  pose proof (hd_last_In (wh_used H) 0 Hne) as Hin. rewrite Hu in Hin at 2.
  apply filter_In in Hin as [Hin _]. apply in_map_iff in Hin as (y & Hy & Hy'). apply in_seq in Hy'. lia.
Qed.

Lemma hd_direct_ok : forall H, huf_ok H -> wh_last H <= 128 -> huf_desc_ok H (huf_direct_bytes H).
Proof.
  intros H Hok Hl. destruct (huf_direct_bytes_ok H Hok Hl) as [Hb Hlen].
  pose proof (hd_last_pos H Hok).
  split; [auto | split].
  - rewrite Hlen.
    assert (1 <= (wh_last H + 1) / 2) by (apply Z.div_le_lower_bound; lia).
    assert ((wh_last H + 1) / 2 <= 129 / 2) by (apply Z.div_le_mono; lia).
    change (129 / 2) with 64 in *. lia.
  - intros rest. apply huf_parse_of_weights; auto. apply WHufDescSibDec.huf_direct_weights; auto.
Qed.

Lemma hd_fse_ok : forall H norm log sts,
  huf_ok H -> hfw_ok H norm log sts -> Zlength (hfw_bytes H norm log sts) <= 127 ->
  huf_desc_ok H (Zlength (hfw_bytes H norm log sts) :: hfw_bytes H norm log sts).
Proof.
  intros H norm log sts Hok Hw Hn.
  destruct (hfw_bytes_ok H norm log sts Hok Hw) as [Hb Hl].
  set (hb := hfw_bytes H norm log sts) in *.
  split; [constructor; [unfold is_byte; lia | auto] | split].
  - rewrite Zlength_cons. lia.
  - intros rest. apply huf_parse_of_weights; auto.
    unfold huf_desc_weights.
    simpl app. rewrite Zlength_cons.
    assert (Hz: 0 <= Zlength (hb ++ rest)) by apply Zlength_nonneg.
    destruct (Zlength (hb ++ rest) + 1 <? 1) eqn:E1; [apply Z.ltb_lt in E1; lia |].
    unfold byte_at. simpl nth.
    destruct (Zlength hb >=? 128) eqn:E2; [apply Z.geb_le in E2; lia |].
    rewrite Zlength_app.
    destruct (Zlength hb + Zlength rest + 1 <? Zlength hb + 1) eqn:E3;
      [apply Z.ltb_lt in E3; pose proof (Zlength_nonneg rest); lia |].
    replace (slice (Zlength hb :: hb ++ rest) 1 (Zlength hb)) with hb.
    + pose proof (hfw_decode H norm log sts Hok Hw) as Hd. fold hb in Hd. rewrite Hd.
      pose proof (Zlength_nonneg rest).
      destruct (Z.succ (Zlength hb + Zlength rest) <? 1) eqn:X1; [apply Z.ltb_lt in X1; lia |].
      destruct (Z.succ (Zlength hb + Zlength rest) <? Zlength hb + 1) eqn:X2; [apply Z.ltb_lt in X2; lia |].
      rewrite Zlength_cons. f_equal; f_equal; lia.
    + unfold slice. simpl. rewrite firstn_app, Zlength_correct, Nat2Z.id, firstn_all, Nat.sub_diag.
      simpl. rewrite app_nil_r. reflexivity.
Qed.

(* the direct form, byte by byte *)
Definition hd_byte (H: whuf) (k: Z) : Z :=
  wh_weight H (2 * k) * 16 + (if 2 * k + 1 <? wh_last H then wh_weight H (2 * k + 1) else 0).

Lemma hd_direct_len : forall H, 0 <= wh_last H -> Zlength (huf_direct_bytes H) = 1 + (wh_last H + 1) / 2.
Proof.
  intros. unfold huf_direct_bytes. rewrite Zlength_cons, Zlength_map, Zlength_correct, length_seq.
  rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
Qed.

Lemma hd_direct_head : forall H, sublist 0 1 (huf_direct_bytes H) = [127 + wh_last H].
Proof. intros. reflexivity. Qed.

Lemma hd_direct_nth : forall H k, 0 <= wh_last H -> 0 <= k < (wh_last H + 1) / 2 ->
  Znth (1 + k) (huf_direct_bytes H) = hd_byte H k.
Proof.
  intros. unfold huf_direct_bytes. rewrite Znth_pos_cons by lia. replace (1 + k - 1) with k by lia.
  rewrite Znth_map by (rewrite Zlength_correct, length_seq, Z2Nat.id by (apply Z.div_pos; lia); lia).
  unfold Znth. rewrite if_false by lia. rewrite seq_nth by lia. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma hd_direct_step : forall H k, 0 <= wh_last H -> 0 <= k < (wh_last H + 1) / 2 ->
  sublist 0 (1 + (k + 1)) (huf_direct_bytes H) = sublist 0 (1 + k) (huf_direct_bytes H) ++ [hd_byte H k].
Proof.
  intros. pose proof (hd_direct_len H ltac:(lia)).
  rewrite (sublist_split 0 (1 + k) (1 + (k + 1))) by lia.
  rewrite (sublist_one (1 + k)) by lia. rewrite hd_direct_nth by lia. reflexivity.
Qed.

Lemma hd_byte_range : forall H k, huf_ok H -> 0 <= hd_byte H k < 256.
Proof.
  intros H k (HL & Hlog & Hall & _).
  assert (Hw: forall s, 0 <= wh_weight H s <= 11).
  { intros s. unfold wh_weight, zn.
    destruct (lt_dec (Z.to_nat s) (length (wh_w H))) as [Hlt | Hge].
    - rewrite Forall_forall in Hall. specialize (Hall (nth (Z.to_nat s) (wh_w H) 0) (nth_In _ _ Hlt)). lia.
    - rewrite nth_overflow by lia. lia. }
  unfold hd_byte. pose proof (Hw (2 * k)). pose proof (Hw (2 * k + 1)).
  destruct (2 * k + 1 <? wh_last H); lia.
Qed.

Lemma hd_or : forall w lo, 0 <= w <= 15 -> 0 <= lo <= 15 ->
  Int.or (Int.shl (Int.repr w) (Int.repr 4)) (Int.repr lo) = Int.repr (w * 16 + lo).
Proof.
  intros. unfold Int.or, Int.shl. rewrite !(Int.unsigned_repr w), (Int.unsigned_repr 4) by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  rewrite (Int.unsigned_repr (w * 16)) by rep_lia. rewrite Int.unsigned_repr by rep_lia.
  rewrite Z.lor_comm. change 16 with (2 ^ 4). rewrite wbm_lor_add by lia. f_equal. lia.
Qed.

Lemma hd_znth_w : forall H s, 0 <= s -> Znth s (wh_w H) = wh_weight H s.
Proof. intros. unfold wh_weight, zn, Znth. rewrite if_false by lia. reflexivity. Qed.

Lemma hd_w_range : forall H s, huf_ok H -> 0 <= wh_weight H s <= 11.
Proof.
  intros H s (HL & Hlog & Hall & _). unfold wh_weight, zn.
  destruct (lt_dec (Z.to_nat s) (length (wh_w H))) as [Hlt | Hge].
  - rewrite Forall_forall in Hall. specialize (Hall (nth (Z.to_nat s) (wh_w H) 0) (nth_In _ _ Hlt)). lia.
  - rewrite nth_overflow by lia. lia.
Qed.
