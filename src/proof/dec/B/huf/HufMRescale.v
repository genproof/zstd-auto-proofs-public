(* Model lemma for group HUF: HUF_readDTableX1_wksp raises every nonzero weight by
   L - tableLog (HUF_rescaleStats) and fills the canonical cells of the rescaled table: they are
   BRep.x1_cells (each cell of the table repeated 2^(L - tableLog) times). *)
Require Export Zstd.proof.dec.B.BRep.

Definition huf_rescale (ht: huf_table) (L: Z) : huf_table :=
  {| ht_log := L;
     ht_weights := map (fun w => if w =? 0 then 0 else w + (L - ht_log ht)) (ht_weights ht) |}.

Lemma hmr_flat_map_flat_map {A B C} (f: A -> list B) (g: B -> list C) (l: list A) :
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite flat_map_app, IH; reflexivity. Qed.

Lemma hmr_flat_map_map {A B C} (f: B -> list C) (g: A -> B) (l: list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH; reflexivity. Qed.

Lemma hmr_flat_map_ext_in {A B} (f g: A -> list B) (l: list A) :
  (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; intros H; simpl; [reflexivity|].
  rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma hmr_flat_map_nil {A B} (f: A -> list B) (l: list A) :
  (forall x, In x l -> f x = nil) -> flat_map f l = nil.
Proof.
  intros H. transitivity (flat_map (fun _ : A => @nil B) l).
  - apply hmr_flat_map_ext_in; exact H.
  - clear H; induction l; simpl; auto.
Qed.

Lemma hmr_rep_repeat {A} (c: A) (n k: nat) :
  flat_map (fun c => repeat c k) (repeat c n) = repeat c (n * k).
Proof. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH, repeat_app; reflexivity. Qed.

Lemma hmr_map_add_seq (k s n: nat) : map (Nat.add k) (seq s n) = seq (k + s) n.
Proof.
  revert s; induction n as [|n IH]; intros s; simpl; [reflexivity|].
  rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma hmr_repeat_map {A} (a: A) (k: nat) : repeat a k = map (fun _ => a) (seq 0 k).
Proof.
  assert (H: forall s, repeat a k = map (fun _ => a) (seq s k)).
  { induction k as [|k IH]; intros s; simpl; [reflexivity|]. rewrite <- IH; reflexivity. }
  apply H.
Qed.

Lemma hmr_rep_each_nth {A} (k: nat) (l: list A) (d: A) : (0 < k)%nat ->
  flat_map (fun c => repeat c k) l = map (fun n => nth (n / k) l d) (seq 0 (length l * k)).
Proof.
  intros Hk. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite seq_app, map_app, IH. f_equal.
  - rewrite hmr_repeat_map. apply map_ext_in. intros n Hn. apply in_seq in Hn.
    rewrite Nat.div_small by lia. reflexivity.
  - replace (0 + k)%nat with (k + 0)%nat by lia.
    rewrite <- (hmr_map_add_seq k 0), map_map. apply map_ext. intros n.
    replace (k + n)%nat with (1 * k + n)%nat by lia. rewrite Nat.div_add_l by lia. reflexivity.
Qed.

Lemma hmr_cells_rescale (ht: huf_table) (L: Z) :
  1 <= ht_log ht -> Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht) -> ht_log ht <= L ->
  huf_cells (huf_rescale ht L) =
  flat_map (fun c => repeat c (Z.to_nat (2 ^ (L - ht_log ht)))) (huf_cells ht).
Proof.
  intros Hlog HF HL. destruct ht as [log ws]; simpl in *.
  unfold huf_cells, huf_rescale; simpl.
  remember (L - log) as d eqn:Hd.
  set (f := fun w => if w =? 0 then 0 else w + d).
  assert (Hnth: forall s, nth s (map f ws) 0 = f (nth s ws 0)).
  { intros s. change 0 with (f 0) at 1. apply map_nth. }
  assert (Hpos: forall s, 0 <= nth s ws 0).
  { intros s. destruct (Nat.lt_ge_cases s (length ws)).
    - rewrite Forall_forall in HF. apply HF, nth_In; assumption.
    - rewrite nth_overflow by assumption. lia. }
  rewrite length_map.
  replace (Z.to_nat L) with (Z.to_nat d + Z.to_nat log)%nat by (rewrite <- Z2Nat.inj_add by lia; f_equal; lia).
  rewrite seq_app, map_app, flat_map_app.
  rewrite hmr_flat_map_nil.
  2:{ intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- Hi]]. apply in_seq in Hi.
      apply hmr_flat_map_nil. intros s _. rewrite Hnth. specialize (Hpos s). unfold f.
      destruct (nth s ws 0 =? 0) eqn:E.
      - replace (0 =? Z.of_nat i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - replace (nth s ws 0 + d =? Z.of_nat i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  simpl.
  replace (S (Z.to_nat d)) with (Z.to_nat d + 1)%nat by lia.
  rewrite <- hmr_map_add_seq, map_map, hmr_flat_map_map, hmr_flat_map_flat_map, hmr_flat_map_map.
  apply hmr_flat_map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite hmr_flat_map_flat_map. apply hmr_flat_map_ext_in. intros s _.
  rewrite Hnth. specialize (Hpos s). unfold f.
  destruct (nth s ws 0 =? Z.of_nat i) eqn:E.
  - apply Z.eqb_eq in E. rewrite E.
    replace (Z.of_nat i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.of_nat i + d =? Z.of_nat (Z.to_nat d + i)) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite hmr_rep_repeat. f_equal.
    + f_equal. lia.
    + rewrite <- Z2Nat.inj_mul by lia. rewrite <- Z.pow_add_r by lia. f_equal. f_equal. lia.
  - simpl. destruct (nth s ws 0 =? 0) eqn:E0.
    + replace (0 =? Z.of_nat (Z.to_nat d + i)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    + replace (nth s ws 0 + d =? Z.of_nat (Z.to_nat d + i)) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma x1_cells_rescale (ht: huf_table) (L: Z) :
  huf_ok ht -> Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht) -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  map x1cell (huf_cells (huf_rescale ht L)) = x1_cells ht L.
Proof.
  intros [Hlog [Hlen _]] HF HL.
  rewrite hmr_cells_rescale by (auto; lia).
  assert (Hk: (0 < Z.to_nat (2 ^ (L - ht_log ht)))%nat).
  { assert (0 < 2 ^ (L - ht_log ht)) by (apply Z.pow_pos_nonneg; lia). lia. }
  rewrite (hmr_rep_each_nth _ _ (0, 0) Hk), map_map.
  unfold x1_cells.
  replace (length (huf_cells ht) * Z.to_nat (2 ^ (L - ht_log ht)))%nat with (Z.to_nat (2 ^ L)).
  2:{ rewrite Zlength_correct in Hlen.
      rewrite <- (Nat2Z.id (length _)), Hlen, <- Z2Nat.inj_mul by (apply Z.pow_nonneg; lia).
      rewrite <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
  apply map_ext_in. intros n _. unfold hsym. f_equal. f_equal.
  rewrite <- (Nat2Z.id (n / _)). f_equal. rewrite Nat2Z.inj_div, Z2Nat.id; [reflexivity|].
  apply Z.pow_nonneg; lia.
Qed.
