(* Sub-group X1T: statement 10 of HUF_readDTableX1_wksp (the fill of the X1
   cells). *)
Require Export Zstd.proof.dec.B.huf.HufX1TSpecs.
Local Open Scope logic.

(* ---------- the model of the fill ---------- *)

(* the symbols of weight w, increasing *)
Definition x1_wsyms (ws: list Z) (w: Z) : list Z :=
  map Z.of_nat (filter (fun s => nth s ws 0 =? w) (seq 0 (length ws))).

(* the index in x1_sorted ws of the first symbol of weight w *)
Definition x1_start (ws: list Z) (w: Z) : Z :=
  Zlength (flat_map (x1_wsyms ws) (map Z.of_nat (seq 0 (Z.to_nat w)))).

(* the cells of the symbols of weight w (each in 2^(w-1) cells of L + 1 - w bits) *)
Definition x1_block (ws: list Z) (L w: Z) : list (Z * Z) :=
  flat_map (fun s => repeat (s, L + 1 - w) (Z.to_nat (2 ^ (w - 1)))) (x1_wsyms ws w).

(* the cells of the weights 1 .. w-1 *)
Definition x1_done (ws: list Z) (L w: Z) : list (Z * Z) :=
  flat_map (x1_block ws L) (map Z.of_nat (seq 1 (Z.to_nat (w - 1)))).

(* the bytes of a list of cells (fields nbBits, byte) *)
Definition x1_flat (l: list (val * val)) : list val := flat_map (fun c => [fst c; snd c]) l.

(* ---------- pure facts ---------- *)

Lemma x1_sorted_eq (ws: list Z) : x1_sorted ws = flat_map (x1_wsyms ws) (map Z.of_nat (seq 0 13)).
Proof. reflexivity. Qed.

Lemma x1_sorted_at (ws: list Z) (w s: Z) :
  0 <= w <= 12 -> 0 <= s < Zlength (x1_wsyms ws w) ->
  Znth (x1_start ws w + s) (x1_sorted ws) = Znth s (x1_wsyms ws w).
Proof.
  intros Hw Hs. rewrite x1_sorted_eq. unfold x1_start.
  assert (E: seq 0 13 = seq 0 (Z.to_nat w) ++ Z.to_nat w :: seq (S (Z.to_nat w)) (12 - Z.to_nat w)).
  { replace 13%nat with (Z.to_nat w + S (12 - Z.to_nat w))%nat by lia. rewrite seq_app. reflexivity. }
  rewrite E, map_app, List.flat_map_app. cbn [map]. cbn [flat_map].
  rewrite Z2Nat.id by lia.
  rewrite app_Znth2 by (pose proof (Zlength_nonneg (flat_map (x1_wsyms ws) (map Z.of_nat (seq 0 (Z.to_nat w))))); lia).
  rewrite app_Znth1 by lia. f_equal. lia.
Qed.

Lemma x1_start_succ (ws: list Z) (w: Z) :
  0 <= w -> x1_start ws (w + 1) = x1_start ws w + Zlength (x1_wsyms ws w).
Proof.
  intros Hw. unfold x1_start.
  replace (Z.to_nat (w + 1)) with (S (Z.to_nat w)) by lia.
  rewrite seq_S, map_app, flat_map_app, Zlength_app. simpl.
  rewrite app_nil_r, Z2Nat.id by lia. reflexivity.
Qed.

Lemma x1_start_0 (ws: list Z) : x1_start ws 0 = 0.
Proof. reflexivity. Qed.

Lemma x1_start_bound (ws: list Z) (w: Z) :
  0 <= w <= 12 -> 0 <= x1_start ws w /\ x1_start ws w + Zlength (x1_wsyms ws w) <= Zlength (x1_sorted ws).
Proof.
  intros Hw. split; [unfold x1_start; apply Zlength_nonneg|].
  rewrite <- x1_start_succ by lia. rewrite x1_sorted_eq. unfold x1_start.
  replace 13%nat with (Z.to_nat (w + 1) + (13 - Z.to_nat (w + 1)))%nat by lia.
  rewrite seq_app, map_app, flat_map_app, Zlength_app.
  pose proof (Zlength_nonneg (flat_map (x1_wsyms ws) (map Z.of_nat (seq (0 + Z.to_nat (w + 1)) (13 - Z.to_nat (w + 1)))))).
  lia.
Qed.

Lemma x1_sorted_len_aux (ws: list Z) (l: list nat) :
  Forall (fun s => (0 <= nth s ws 0 <= 12)%Z) l ->
  length (flat_map (fun w => map Z.of_nat (filter (fun s => (nth s ws 0 =? w)%Z) l))
           (map Z.of_nat (seq 0 13))) = length l.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  inversion H; subst. specialize (IH H3). simpl in IH |- *.
  repeat rewrite length_app in IH |- *. repeat rewrite length_map in IH |- *.
  assert (Hc: nth a ws 0 = 0 \/ nth a ws 0 = 1 \/ nth a ws 0 = 2 \/ nth a ws 0 = 3 \/ nth a ws 0 = 4 \/
    nth a ws 0 = 5 \/ nth a ws 0 = 6 \/ nth a ws 0 = 7 \/ nth a ws 0 = 8 \/ nth a ws 0 = 9 \/
    nth a ws 0 = 10 \/ nth a ws 0 = 11 \/ nth a ws 0 = 12) by lia.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]]]]]]];
    rewrite Hc; simpl in IH |- *; repeat rewrite length_map; lia.
Qed.

Lemma x1_sorted_len (ws: list Z) :
  Forall (fun w => 0 <= w <= 12) ws -> Zlength (x1_sorted ws) = Zlength ws.
Proof.
  intros H. rewrite !Zlength_correct. f_equal. unfold x1_sorted.
  rewrite x1_sorted_len_aux, length_seq; [reflexivity|].
  apply Forall_forall. intros s Hs. apply in_seq in Hs.
  rewrite Forall_forall in H. apply H, nth_In. lia.
Qed.

Lemma x1_wsyms_range (ws: list Z) (w s: Z) : In s (x1_wsyms ws w) -> 0 <= s < Zlength ws.
Proof.
  unfold x1_wsyms. intros H. apply in_map_iff in H as [n [<- Hn]].
  apply filter_In in Hn as [Hn _]. apply in_seq in Hn. rewrite Zlength_correct. lia.
Qed.

Lemma rank_stats_filter_map_S (f: nat -> bool) (l: list nat) :
  length (filter f (map S l)) = length (filter (fun n => f (S n)) l).
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f (S a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma rank_stats_count (ws: list Z) (w: Z) :
  length (filter (fun x => x =? w) ws) = length (filter (fun s => nth s ws 0 =? w) (seq 0 (length ws))).
Proof.
  induction ws as [|a ws IH]; simpl; [reflexivity|].
  rewrite <- seq_shift.
  destruct (a =? w); simpl; rewrite rank_stats_filter_map_S, IH; reflexivity.
Qed.

Lemma rank_stats_at (ws: list Z) (w: Z) :
  0 <= w < 13 -> Znth w (rank_stats ws) = vint (Zlength (x1_wsyms ws w)).
Proof.
  intros Hw. unfold rank_stats, x1_wsyms.
  assert (Hl: Zlength (seq 0 13) = 13) by reflexivity.
  rewrite Znth_map by lia.
  assert (Hn: Znth w (seq 0 13) = Z.to_nat w).
  { rewrite <- (Z2Nat.id w) at 1 by lia. rewrite <- nth_Znth' .
    apply seq_nth. lia. }
  rewrite Hn, Z2Nat.id by lia.
  rewrite Zlength_map, !Zlength_correct, rank_stats_count. reflexivity.
Qed.

Lemma x1_done_1 (ws: list Z) (L: Z) : x1_done ws L 1 = [].
Proof. reflexivity. Qed.

Lemma x1_done_succ (ws: list Z) (L w: Z) :
  1 <= w -> x1_done ws L (w + 1) = x1_done ws L w ++ x1_block ws L w.
Proof.
  intros Hw. unfold x1_done.
  replace (Z.to_nat (w + 1 - 1)) with (S (Z.to_nat (w - 1))) by lia.
  rewrite seq_S, map_app, flat_map_app. simpl.
  rewrite app_nil_r. f_equal. f_equal. lia.
Qed.

Lemma x1_flat_map_filter {B: Type} (f: Z -> list B) (p: nat -> bool) (l: list nat) :
  flat_map f (map Z.of_nat (filter p l)) = flat_map (fun s => if p s then f (Z.of_nat s) else nil) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (p a); simpl; rewrite IH; auto.
Qed.

Lemma x1_done_full (ws: list Z) (L: Z) :
  0 <= L -> x1_done ws L (L + 1) = huf_cells {| ht_log := L; ht_weights := ws |}.
Proof.
  intros HL. unfold x1_done, huf_cells; simpl.
  replace (L + 1 - 1) with L by lia.
  apply flat_map_ext; intros w.
  unfold x1_block, x1_wsyms. rewrite x1_flat_map_filter. reflexivity.
Qed.

Lemma x1_block_len (ws: list Z) (L w: Z) :
  1 <= w -> Zlength (x1_block ws L w) = (Zlength (x1_wsyms ws w) * 2 ^ (w - 1))%Z.
Proof.
  intros Hw. unfold x1_block. generalize (x1_wsyms ws w). intros l.
  assert (H2: 0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite Zlength_app, IH, Zlength_cons, Zlength_correct, repeat_length, Z2Nat.id by lia. lia.
Qed.

(* the bytes of HUF_DEltX1_set4 sym nb, little-endian: nb, sym, nb, sym, ... *)
Lemma x1_set4_bytes (sym nb: Z) :
  0 <= sym < 256 -> 0 <= nb < 256 ->
  le_bytes 8 (set4_val sym nb) = [nb; sym; nb; sym; nb; sym; nb; sym].
Proof.
  intros Hs Hn.
  assert (Hstep: forall a r, 0 <= a < 256 -> (a + 256 * r) mod 256 = a /\ (a + 256 * r) / 256 = r).
  { intros a r Ha. split.
    - rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia.
    - rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (Hv: set4_val sym nb = nb + 256 * (sym + 256 * (nb + 256 * (sym + 256 * (nb + 256 *
            (sym + 256 * (nb + 256 * (sym + 256 * 0)))))))).
  { unfold set4_val. ring. }
  rewrite Hv. cbn [le_bytes].
  repeat match goal with
  | |- context [(?a + 256 * ?r) mod 256] =>
      let H := fresh in destruct (Hstep a r ltac:(lia)) as [H _]; rewrite H; clear H
  | |- context [(?a + 256 * ?r) / 256] =>
      let H := fresh in destruct (Hstep a r ltac:(lia)) as [_ H]; rewrite H; clear H
  end.
  reflexivity.
Qed.

(* ---------- the byte view of HUF_DEltX1 cells ---------- *)

Lemma x1_flat_len (l: list (val * val)) : Zlength (x1_flat l) = (2 * Zlength l)%Z.
Proof.
  induction l as [|c l IH]; [reflexivity|].
  change (x1_flat (c :: l)) with ([fst c; snd c] ++ x1_flat l).
  rewrite Zlength_app, IH, Zlength_cons. list_solve.
Qed.

Lemma x1_align_1 (t: type) (z: Z) :
  complete_legal_cosu_type t = true -> hardware_alignof ha_env_cs t = 1 ->
  align_compatible_rec cenv_cs t z.
Proof.
  intros. eapply align_compatible_rec_hardware_1 with (ha_env := ha_env_cs); eauto;
    [apply cenv_consistent | apply cenv_legal_su | apply ha_env_cs_consistent | apply ha_env_cs_complete].
Qed.

Lemma x1_fc (n: Z) (p: val) :
  0 <= n -> field_compatible (tarray t_deltx1 n) [] p <-> field_compatible (tarray tuchar (2 * n)%Z) [] p.
Proof.
  intros Hn.
  assert (A1: forall z, align_compatible_rec cenv_cs (tarray t_deltx1 n) z)
    by (intro; apply x1_align_1; reflexivity).
  assert (A2: forall z, align_compatible_rec cenv_cs (tarray tuchar (2 * n)%Z) z)
    by (intro; apply x1_align_1; reflexivity).
  assert (S1: sizeof (tarray t_deltx1 n) = (2 * n)%Z) by (simpl; lia).
  assert (S2: sizeof (tarray tuchar (2 * n)%Z) = (2 * n)%Z) by (simpl; lia).
  unfold field_compatible, size_compatible, align_compatible.
  destruct p; try tauto. rewrite S1, S2.
  split; intros (?&?&?&?&?); repeat split; auto.
Qed.

Lemma x1_cell1 (sh: share) (c: val * val) (p: val) :
  data_at sh (tarray t_deltx1 1) [c] p = data_at sh (tarray tuchar 2) [fst c; snd c] p.
Proof.
  destruct (field_compatible_dec (tarray t_deltx1 1) [] p) as [FC|NFC].
  - assert (FC2: field_compatible (tarray tuchar 2) [] p) by (apply (x1_fc 1); auto; lia).
    erewrite (data_at_singleton_array_eq sh t_deltx1) by reflexivity.
    change [fst c; snd c] with ([fst c] ++ [snd c]).
    rewrite (split2_data_at_Tarray_app 1 2) by reflexivity.
    erewrite !(data_at_singleton_array_eq sh tuchar) by reflexivity.
    rewrite field_address0_offset by auto with field_compatible.
    unfold_data_at (data_at _ _ _ p).
    rewrite !field_at_data_at.
    assert (FC3: field_compatible t_deltx1 [] p).
    { destruct FC as (?&?&?&?&?). destruct p; try contradiction.
      repeat split; auto. apply x1_align_1; reflexivity. }
    rewrite !field_address_offset by auto with field_compatible.
    simpl. rewrite isptr_offset_val_zero by auto with field_compatible.
    destruct c; reflexivity.
  - apply pred_ext; saturate_local; exfalso; apply NFC; auto.
    apply (x1_fc 1); auto; lia.
Qed.

Lemma x1_cells_bytes (sh: share) (l: list (val * val)) (p: val) :
  data_at sh (tarray t_deltx1 (Zlength l)) l p = data_at sh (tarray tuchar (2 * Zlength l)%Z) (x1_flat l) p.
Proof.
  revert p. induction l as [|c l IH]; intro p.
  - destruct (field_compatible_dec (tarray t_deltx1 0) [] p) as [FC|NFC].
    + rewrite !data_at_zero_array_eq by auto with field_compatible. reflexivity.
    + apply pred_ext; saturate_local; exfalso; apply NFC; auto.
      apply (x1_fc 0); auto; lia.
  - pose proof (Zlength_nonneg l).
    destruct (field_compatible_dec (tarray t_deltx1 (Zlength (c :: l))) [] p) as [FC|NFC].
    + assert (FC2: field_compatible (tarray tuchar (2 * Zlength (c :: l))%Z) [] p)
        by (apply x1_fc; auto; list_solve).
      change (x1_flat (c :: l)) with ([fst c; snd c] ++ x1_flat l).
      pose proof (split2_data_at_Tarray_app 1 (Zlength (c :: l)) sh t_deltx1 [c] l p) as E1.
      pose proof (split2_data_at_Tarray_app 2 (2 * Zlength (c :: l))%Z sh tuchar [fst c; snd c] (x1_flat l) p) as E2.
      etransitivity; [apply E1; list_solve|].
      etransitivity; [|symmetry; apply E2; rewrite ?x1_flat_len; list_solve].
      clear E1 E2.
      rewrite !field_address0_offset
        by (apply field_compatible0_cons; split; auto with field_compatible; list_solve).
      rewrite x1_cell1.
      replace (Zlength (c :: l) - 1)%Z with (Zlength l) by list_solve.
      replace (2 * Zlength (c :: l) - 2)%Z with (2 * Zlength l)%Z by list_solve.
      rewrite IH. simpl nested_field_offset. reflexivity.
    + apply pred_ext; saturate_local; exfalso; apply NFC; auto.
      apply x1_fc; auto; list_solve.
Qed.

(* a window of 4 cells at index u of an array of n cells, as 8 bytes *)
Lemma x1_window (sh: share) (n u: Z) (l: list (val * val)) (p: val) :
  field_compatible (tarray t_deltx1 n) nil p ->
  Zlength l = n -> 0 <= u -> u + 4 <= n ->
  data_at sh (tarray t_deltx1 n) l p =
  data_at sh (tarray t_deltx1 u) (sublist 0 u l) p *
  data_at sh (tarray tuchar 8) (x1_flat (sublist u (u + 4) l)) (offset_val (2 * u)%Z p) *
  data_at sh (tarray t_deltx1 (n - (u + 4))) (sublist (u + 4) n l) (offset_val (2 * (u + 4))%Z p).
Proof.
  intros FC Hl Hu Hu4. unfold tarray at 1.
  rewrite (@split3_data_at_Tarray CompSpecs sh t_deltx1 n u (u + 4) l l (sublist 0 u l) (sublist u (u + 4) l)
             (sublist (u + 4) n l) p).
  2: (red; simpl; auto).
  all: try lia.
  all: try (rewrite sublist_same by lia; reflexivity).
  all: try reflexivity.
  rewrite !field_address0_offset
    by (destruct FC as (?&?&?&?&?); repeat split; auto; simpl; lia).
  simpl nested_field_offset.
  replace (u + 4 - u) with (Zlength (sublist u (u + 4) l)) by (rewrite Zlength_sublist; lia).
  fold (tarray t_deltx1 (Zlength (sublist u (u + 4) l))).
  rewrite x1_cells_bytes.
  rewrite Zlength_sublist by lia.
  replace (2 * (u + 4 - u))%Z with 8 by lia.
  replace (0 + 2 * u)%Z with (2 * u)%Z by lia.
  replace (0 + 2 * (u + 4))%Z with (2 * (u + 4))%Z by lia.
  reflexivity.
  - change (@Zlength (@reptype CompSpecs t_deltx1) l) with (@Zlength (val * val) l). lia.
  - change (@sublist (@reptype CompSpecs t_deltx1) 0 n l) with (@sublist (val * val) 0 n l).
    rewrite sublist_same by lia. reflexivity.
Qed.

(* ---------- the state of the fill ---------- *)

(* the cells of the first s symbols of weight w *)
Definition x1_bpre (ws: list Z) (L w s: Z) : list (Z * Z) :=
  flat_map (fun sym => repeat (sym, L + 1 - w) (Z.to_nat (2 ^ (w - 1)))) (sublist 0 s (x1_wsyms ws w)).

(* the cell array: the cells written so far, then undefined cells *)
Definition x1_arr (cs: list (Z * Z)) : list (val * val) :=
  map x1cell cs ++ Zrepeat (Vundef, Vundef) (8192 - Zlength cs).

Lemma x1_rep_len (l: list Z) (c k: Z) :
  0 <= k -> Zlength (flat_map (fun s => repeat (s, c) (Z.to_nat k)) l) = (Zlength l * k)%Z.
Proof.
  intros Hk. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite Zlength_app, IH, Zlength_cons, Zlength_correct, repeat_length, Z2Nat.id by lia. lia.
Qed.

Lemma x1_bpre_0 (ws: list Z) (L w: Z) : x1_bpre ws L w 0 = [].
Proof. unfold x1_bpre. rewrite sublist_nil. reflexivity. Qed.

Lemma x1_bpre_succ (ws: list Z) (L w s: Z) :
  0 <= s < Zlength (x1_wsyms ws w) ->
  x1_bpre ws L w (s + 1) =
  x1_bpre ws L w s ++ repeat (Znth s (x1_wsyms ws w), L + 1 - w) (Z.to_nat (2 ^ (w - 1))).
Proof.
  intros Hs. unfold x1_bpre.
  rewrite (sublist_split 0 s (s + 1)) by lia. rewrite flat_map_app.
  rewrite sublist_len_1 by lia. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma x1_bpre_full (ws: list Z) (L w: Z) : x1_bpre ws L w (Zlength (x1_wsyms ws w)) = x1_block ws L w.
Proof. unfold x1_bpre, x1_block. rewrite sublist_same by lia. reflexivity. Qed.

Lemma x1_bpre_len (ws: list Z) (L w s: Z) :
  1 <= w -> 0 <= s <= Zlength (x1_wsyms ws w) -> Zlength (x1_bpre ws L w s) = (s * 2 ^ (w - 1))%Z.
Proof.
  intros Hw Hs. unfold x1_bpre. rewrite x1_rep_len by (apply Z.pow_nonneg; lia).
  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma x1_done_prefix (ws: list Z) (L w w': Z) :
  1 <= w -> w <= w' -> exists r, x1_done ws L w' = x1_done ws L w ++ r.
Proof.
  intros Hw Hw'. replace w' with (w + Z.of_nat (Z.to_nat (w' - w))) by lia.
  generalize (Z.to_nat (w' - w)). intros k. induction k as [|k IH].
  - exists []. rewrite app_nil_r. f_equal. lia.
  - destruct IH as [r Hr]. exists (r ++ x1_block ws L (w + Z.of_nat k)).
    replace (w + Z.of_nat (S k)) with (w + Z.of_nat k + 1) by lia.
    rewrite x1_done_succ, Hr, app_assoc by lia. reflexivity.
Qed.

(* the cells of the weights 1 .. w fit in the 2^L cells *)
Lemma x1_done_bound (ws: list Z) (L w: Z) :
  0 <= L -> 1 <= w <= L -> Zlength (huf_cells {| ht_log := L; ht_weights := ws |}) = 2 ^ L ->
  Zlength (x1_done ws L w) + Zlength (x1_block ws L w) <= 2 ^ L.
Proof.
  intros HL Hw Hk. rewrite <- Zlength_app, <- x1_done_succ by lia.
  destruct (x1_done_prefix ws L (w + 1) (L + 1)) as [r Hr]; try lia.
  rewrite x1_done_full in Hr by lia. rewrite <- Hk, Hr, Zlength_app.
  pose proof (Zlength_nonneg r). lia.
Qed.

Lemma x1_arr_full (sh: share) (cs: list (Z * Z)) (p: val) :
  Zlength cs <= 8192 ->
  data_at sh (tarray t_deltx1 8192) (x1_arr cs) p |--
  data_at sh (tarray t_deltx1 (Zlength cs)) (map x1cell cs) p *
  memory_block sh (HUF_CELLBYTES - 2 * Zlength cs) (offset_val (2 * Zlength cs) p).
Proof.
  intros Hn. unfold x1_arr.
  assert_PROP (field_compatible (tarray t_deltx1 8192) nil p) as FC by entailer!.
  change (@app (val*val) (map x1cell cs) (Zrepeat (Vundef,Vundef) (8192 - Zlength cs))) with
    (@app (reptype t_deltx1) (map x1cell cs) (Zrepeat (Vundef,Vundef) (8192 - Zlength cs))).
  rewrite (@split2_data_at_Tarray_app CompSpecs (Zlength cs) 8192 sh t_deltx1 (map x1cell cs)
             (Zrepeat (Vundef, Vundef) (8192 - Zlength cs)) p)
    by (try rewrite Zlength_map; try rewrite Zlength_Zrepeat; rep_lia).
  rewrite field_address0_offset
    by (destruct FC as (?&?&?&?&?); repeat split; auto; simpl; pose proof (Zlength_nonneg cs); lia).
  cancel.
  eapply derives_trans; [apply data_at_data_at_|].
  eapply derives_trans; [apply data_at__memory_block_cancel|].
  unfold HUF_CELLBYTES. simpl sizeof.
  replace (Z.max 0 (8192 - Zlength cs)) with (8192 - Zlength cs) by lia.
  replace (0 + 2 * Zlength cs)%Z with (2 * Zlength cs)%Z by lia.
  replace (2 * (8192 - Zlength cs))%Z with (16384 - 2 * Zlength cs)%Z by lia.
  apply derives_refl.
Qed.

Lemma x1_arr_init (sh: share) (p: val) :
  memory_block sh HUF_CELLBYTES p |-- data_at sh (tarray t_deltx1 8192) (x1_arr []) p.
Proof.
  unfold HUF_CELLBYTES.
  sep_apply (memory_block_field_compatible_tarraytuchar_ent sh 16384 p ltac:(rep_lia)).
  apply derives_extract_prop; intros FC.
  assert (FC': field_compatible (tarray t_deltx1 8192) nil p).
  { destruct FC as (?&?&?&?&?). repeat split; auto.
    destruct p; try contradiction. red. simpl.
    eapply align_compatible_rec_hardware_1;
      [exact cenv_consistent | exact cenv_legal_su | exact ha_env_cs_consistent
      | exact ha_env_cs_complete | reflexivity | reflexivity]. }
  change 16384 with (sizeof (tarray t_deltx1 8192)).
  rewrite memory_block_data_at_ by auto.
  unfold data_at_, x1_arr. apply derives_refl.
Qed.

(* reads of rankVal and symbols, for any default of Znth *)
Lemma x1_Znth_indep {A: Type} (d1 d2: A) (i: Z) (l: list A) :
  0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros H. unfold Znth. rewrite !if_false by lia. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.

Lemma x1_rank_at (ws: list Z) (w: Z) (d: val) :
  0 <= w < 13 -> @Znth val d w (rank_stats ws) = vint (Zlength (x1_wsyms ws w)).
Proof.
  intros Hw. rewrite <- (rank_stats_at ws w Hw). apply x1_Znth_indep.
  unfold rank_stats. rewrite Zlength_map, Zlength_correct, seq_length. simpl. lia.
Qed.

Lemma x1_sym_at (ws: list Z) (sr: list val) (w s: Z) (d: val) :
  0 <= w <= 12 -> 0 <= s < Zlength (x1_wsyms ws w) ->
  @Znth val d (x1_start ws w + s) (zbytes (x1_sorted ws) ++ sr) = vint (Znth s (x1_wsyms ws w)).
Proof.
  intros Hw Hs. destruct (x1_start_bound ws w Hw) as [H0 H1].
  rewrite (x1_Znth_indep d Vundef) by (rewrite Zlength_app, Zlength_map; pose proof (Zlength_nonneg sr); lia).
  rewrite Znth_app1 by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. rewrite x1_sorted_at by lia. reflexivity.
Qed.

Lemma x1_len_eq (w: Z) :
  1 <= w <= 12 -> Int.shr (Int.shl (Int.repr 1) (Int.repr w)) (Int.repr 1) = Int.repr (2 ^ (w - 1)).
Proof.
  intros Hw.
  assert (w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/
          w = 11 \/ w = 12) as Hc by lia.
  repeat destruct Hc as [Hc|Hc]; subst w; reflexivity.
Qed.

Lemma x1_nb_eq (L w: Z) :
  1 <= w <= L -> L <= 12 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.sub (Int.add (Int.repr L) (Int.repr 1)) (Int.repr w))) = Int.repr (L + 1 - w).
Proof.
  intros Hw HL. rewrite add_repr, sub_repr.
  assert (E: Int.zero_ext 8 (Int.repr (L + 1 - w)) = Int.repr (L + 1 - w)).
  { apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. }
  rewrite !E. reflexivity.
Qed.

Lemma x1_len_bound (w: Z) : 1 <= w <= 12 -> 1 <= 2 ^ (w - 1) <= 2048.
Proof.
  intros Hw. split.
  - apply (Z.pow_le_mono_r 2 0 (w - 1)); lia.
  - change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; lia.
Qed.

Lemma x1_w_of_len (w k: Z) : 1 <= w <= 12 -> 0 <= k -> 2 ^ (w - 1) = 2 ^ k -> w = k + 1.
Proof. intros Hw Hk E. apply Z.pow_inj_r in E; lia. Qed.

(* the cells written so far: weights 1 .. w-1, then the first s symbols of weight w *)
Definition x1_cur (ws: list Z) (L w s: Z) : list (Z * Z) := x1_done ws L w ++ x1_bpre ws L w s.

Lemma x1_cur_len (ws: list Z) (L w s: Z) :
  1 <= w -> 0 <= s <= Zlength (x1_wsyms ws w) ->
  Zlength (x1_cur ws L w s) = Zlength (x1_done ws L w) + s * 2 ^ (w - 1).
Proof. intros. unfold x1_cur. rewrite Zlength_app, x1_bpre_len by lia. lia. Qed.

Lemma x1_cur_bound (ws: list Z) (L w s: Z) :
  0 <= L -> 1 <= w <= L -> Zlength (huf_cells {| ht_log := L; ht_weights := ws |}) = 2 ^ L ->
  0 <= s <= Zlength (x1_wsyms ws w) ->
  Zlength (x1_done ws L w) + s * 2 ^ (w - 1) <= 2 ^ L.
Proof.
  intros HL Hw Hk Hs. pose proof (x1_done_bound ws L w HL Hw Hk).
  rewrite x1_block_len in H by lia.
  assert (0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.

Lemma x1_cur_succ (ws: list Z) (L w s: Z) :
  0 <= s < Zlength (x1_wsyms ws w) ->
  x1_cur ws L w (s + 1) =
  x1_cur ws L w s ++ repeat (Znth s (x1_wsyms ws w), L + 1 - w) (Z.to_nat (2 ^ (w - 1))).
Proof. intros. unfold x1_cur. rewrite x1_bpre_succ, app_assoc by lia. reflexivity. Qed.

Lemma x1_cur_full (ws: list Z) (L w: Z) :
  1 <= w -> x1_cur ws L w (Zlength (x1_wsyms ws w)) = x1_done ws L (w + 1).
Proof. intros. unfold x1_cur. rewrite x1_bpre_full, x1_done_succ by lia. reflexivity. Qed.

Lemma x1_cur_0 (ws: list Z) (L w: Z) : x1_cur ws L w 0 = x1_done ws L w.
Proof. unfold x1_cur. rewrite x1_bpre_0, app_nil_r. reflexivity. Qed.

(* one cell stored at the frontier *)
Lemma x1_arr_upd (cs: list (Z * Z)) (c: Z * Z) :
  Zlength cs < 8192 -> upd_Znth (Zlength cs) (x1_arr cs) (x1cell c) = x1_arr (cs ++ [c]).
Proof.
  intros Hn. unfold x1_arr. rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Z.sub_diag, map_app, <- app_assoc, Zlength_app, Zlength_cons, Zlength_nil.
  f_equal. replace (8192 - Zlength cs) with (1 + (8192 - (Zlength cs + 1))) by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  reflexivity.
Qed.

Lemma x1_zext (x: Z) : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

(* the two field stores of a cell *)
Lemma x1_upd2 {d: Inhabitant (val * val)} (l: list (val * val)) (k: Z) (a b: val) :
  0 <= k < Zlength l ->
  upd_Znth k (upd_Znth k l (a, snd (Znth k l))) (fst (Znth k (upd_Znth k l (a, snd (Znth k l)))), b) =
  upd_Znth k l (a, b).
Proof. intros. rewrite upd_Znth_same, upd_Znth_twice by lia. reflexivity. Qed.

Lemma x1_arr_len (cs: list (Z * Z)) : Zlength cs <= 8192 -> Zlength (x1_arr cs) = 8192.
Proof. intros. unfold x1_arr. rewrite Zlength_app, Zlength_map, Zlength_Zrepeat; lia. Qed.

Lemma x1_arr_cell {d: Inhabitant (val * val)} (cs: list (Z * Z)) (k sym nb: Z) :
  k = Zlength cs -> k < 8192 ->
  upd_Znth k (upd_Znth k (x1_arr cs) (vint nb, snd (Znth k (x1_arr cs))))
    (fst (Znth k (upd_Znth k (x1_arr cs) (vint nb, snd (Znth k (x1_arr cs))))), vint sym) =
  x1_arr (cs ++ [(sym, nb)]).
Proof.
  intros -> Hk. pose proof (Zlength_nonneg cs).
  rewrite x1_upd2 by (rewrite x1_arr_len by lia; lia).
  apply (x1_arr_upd cs (sym, nb)). lia.
Qed.

(* the 4 cells at the frontier, opened as 8 bytes for MEM_write64, and closed again *)
Lemma x1_open4 (sh: share) (cs: list (Z * Z)) (p: val) :
  field_compatible (tarray t_deltx1 8192) nil p -> Zlength cs + 4 <= 8192 ->
  data_at sh (tarray t_deltx1 8192) (x1_arr cs) p |--
  data_at sh (tarray t_deltx1 (Zlength cs)) (map x1cell cs) p *
  data_at sh (tarray tuchar 8) (Zrepeat Vundef 8) (offset_val (2 * Zlength cs) p) *
  data_at sh (tarray t_deltx1 (8192 - (Zlength cs + 4))) (Zrepeat (Vundef, Vundef) (8192 - (Zlength cs + 4)))
    (offset_val (2 * (Zlength cs + 4)) p).
Proof.
  intros FC Hn. pose proof (Zlength_nonneg cs).
  rewrite (x1_window sh 8192 (Zlength cs) (x1_arr cs) p FC) by (try rewrite x1_arr_len; lia).
  unfold x1_arr.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite !Zlength_map, Z.sub_diag.
  replace (Zlength cs + 4 - Zlength cs) with 4 by lia.
  rewrite !sublist_Zrepeat by lia.
  replace (8192 - Zlength cs - 4) with (8192 - (Zlength cs + 4)) by lia.
  change (x1_flat (Zrepeat (Vundef, Vundef) 4)) with (Zrepeat Vundef 8).
  apply derives_refl.
Qed.

Lemma x1_close4 (sh: share) (cs: list (Z * Z)) (p: val) (sym nb: Z) :
  field_compatible (tarray t_deltx1 8192) nil p -> Zlength cs + 4 <= 8192 ->
  data_at sh (tarray t_deltx1 (Zlength cs)) (map x1cell cs) p *
  data_at sh (tarray tuchar 8) (zbytes [nb; sym; nb; sym; nb; sym; nb; sym]) (offset_val (2 * Zlength cs) p) *
  data_at sh (tarray t_deltx1 (8192 - (Zlength cs + 4))) (Zrepeat (Vundef, Vundef) (8192 - (Zlength cs + 4)))
    (offset_val (2 * (Zlength cs + 4)) p) |--
  data_at sh (tarray t_deltx1 8192) (x1_arr (cs ++ repeat (sym, nb) 4)) p.
Proof.
  intros FC Hn. pose proof (Zlength_nonneg cs).
  assert (Hl: Zlength (cs ++ repeat (sym, nb) 4) = Zlength cs + 4)
    by (rewrite Zlength_app; reflexivity).
  rewrite (x1_window sh 8192 (Zlength cs) (x1_arr (cs ++ repeat (sym, nb) 4)) p FC)
    by (try rewrite x1_arr_len; lia).
  unfold x1_arr. rewrite Hl, map_app, <- app_assoc.
  rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite Zlength_map, Z.sub_diag.
  replace (Zlength cs + 4 - Zlength cs) with 4 by lia.
  assert (E1: sublist 0 4 (map x1cell (repeat (sym, nb) 4) ++ Zrepeat (Vundef, Vundef) (8192 - (Zlength cs + 4)))
              = map x1cell (repeat (sym, nb) 4)) by list_solve.
  assert (E2: sublist (Zlength cs + 4) 8192
                (map x1cell cs ++ map x1cell (repeat (sym, nb) 4) ++ Zrepeat (Vundef, Vundef) (8192 - (Zlength cs + 4)))
              = Zrepeat (Vundef, Vundef) (8192 - (Zlength cs + 4))) by list_solve.
  rewrite E1, E2. apply derives_refl.
Qed.

Lemma x1_written (sym nb: Z) :
  0 <= sym < 256 -> 0 <= nb < 256 ->
  mem_written (Zrepeat Vundef 8) 0 8 (set4_val sym nb) = zbytes [nb; sym; nb; sym; nb; sym; nb; sym].
Proof.
  intros. unfold mem_written. rewrite x1_set4_bytes by lia. reflexivity.
Qed.

Lemma x1_rep_snoc (base: list (Z * Z)) (c: Z * Z) (a: Z) :
  0 <= a -> (base ++ repeat c (Z.to_nat a)) ++ repeat c 4 = base ++ repeat c (Z.to_nat (a + 4)).
Proof.
  intros Ha. rewrite <- app_assoc, <- repeat_app. do 2 f_equal. lia.
Qed.

Lemma x1_rep_len2 (base: list (Z * Z)) (c: Z * Z) (a: Z) :
  0 <= a -> Zlength (base ++ repeat c (Z.to_nat a)) = Zlength base + a.
Proof.
  intros Ha. rewrite Zlength_app. f_equal. rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
Qed.

(* one MEM_write64 of the 4 cells (sym, nb) at the frontier base ++ repeat c a *)
Ltac x1_wr shd cells FCc base c a sym nb :=
  let Lc := fresh "Lc" in
  assert (Lc: Zlength (base ++ repeat c (Z.to_nat a)) = Zlength base + a) by (apply x1_rep_len2; lia);
  sep_apply (x1_open4 shd (base ++ repeat c (Z.to_nat a)) cells FCc ltac:(lia));
  forward_call (shd, offset_val (2 * Zlength (base ++ repeat c (Z.to_nat a))) cells, Zrepeat Vundef 8, 0,
                set4_val sym nb);
  [ entailer!; rewrite Lc; simpl;
    match goal with |- [offset_val ?a1 ?p; ?v] = [offset_val ?b1 ?p; ?v] =>
      replace a1 with b1 by lia; reflexivity end
  | idtac .. ];
  try (split; [auto|]; change (Zlength (Zrepeat Vundef 8)) with 8; lia);
  try (change (Zlength (Zrepeat Vundef 8)) with 8; cancel; fail);
  change (Zlength (Zrepeat Vundef 8)) with 8;
  rewrite x1_written by lia;
  sep_apply (x1_close4 shd (base ++ repeat c (Z.to_nat a)) cells sym nb FCc ltac:(lia));
  rewrite x1_rep_snoc by lia; clear Lc.

Lemma x1_fill : x1_fill_ok.
Proof.
  unfold x1_fill_ok. intros until L. intros Hshk Hshd HL Hn Hsr Hws Hkraft.
  unfold HUF_TABLELOG_MAX in HL.
  unfold x1_Delta, x1_fill_stmt. simplify_func_tycontext. abbreviate_semax.
  sep_apply (x1_arr_init shd cells).
  assert_PROP (field_compatible (tarray t_deltx1 8192) nil cells) as FCc by entailer!.
  assert (Hcnt: forall w, 0 <= w < 13 -> 0 <= Zlength (x1_wsyms rws w) <= Zlength rws).
  { intros w Hw. unfold x1_wsyms. rewrite Zlength_map. split; [apply Zlength_nonneg|].
    rewrite !Zlength_correct. apply inj_le. etransitivity; [apply filter_length_le|]. rewrite seq_length. lia. }
  forward.
  rewrite (x1_rank_at rws 0) by lia.
  forward.
  forward.
  forward_loop
    (EX w: Z,
     PROP (1 <= w <= L + 1)
     LOCAL (temp _w__2 (vint w); temp _symbol (vint (x1_start rws w));
            temp _rankStart (vint (Zlength (x1_done rws L w)));
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_done rws L w)) cells;
          data_at Tsh tuint (vint L) vtl;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
          data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert
  continue:
    (EX w: Z,
     PROP (1 <= w <= L)
     LOCAL (temp _w__2 (vint w); temp _symbol (vint (x1_start rws (w + 1)));
            temp _rankStart (vint (Zlength (x1_done rws L (w + 1))));
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_done rws L (w + 1))) cells;
          data_at Tsh tuint (vint L) vtl;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
          data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert
  break:
    (PROP ()
     LOCAL (temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_done rws L (L + 1))) cells;
          data_at Tsh tuint (vint L) vtl;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
          data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
  { Exists 1.
    assert (E1: x1_start rws 1 = Zlength (x1_wsyms rws 0)) by (unfold x1_start; simpl; rewrite app_nil_r; reflexivity).
    rewrite E1. entailer!. }
  2: { (* continue -> invariant *)
    Intros w. forward. Exists (w + 1). entailer!. }
  2: { (* after the loop *)
    rewrite x1_done_full by lia.
    assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
    sep_apply (x1_arr_full shd (huf_cells {| ht_log := L; ht_weights := rws |}) cells ltac:(lia)).
    rewrite Hkraft.
    unfold POSTCONDITION, abbreviate; simpl RA_normal. entailer!. }
  Intros w.
  forward.
  forward_if.
  2: { forward. assert (w = L + 1) by lia. subst w. entailer!. }
  forward.
  { entailer!. rewrite (x1_rank_at rws w) by lia. exact I. }
  rewrite (x1_rank_at rws w) by lia.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite x1_len_eq by lia.
  forward.
  forward.
  forward.
  rewrite x1_nb_eq by lia.
  pose proof (x1_len_bound w ltac:(lia)) as Hlen.
  remember (2 ^ (w - 1)) as len eqn:Hlen_def.
  forward_if
    (PROP ()
     LOCAL (temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L);
            temp _length (vint len);
            temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
            temp _symbol (vint (x1_start rws w));
            temp _rankStart (vint (Zlength (x1_done rws L w)));
            temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_done rws L (w + 1))) cells;
          data_at Tsh tuint (vint L) vtl;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
          data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F)).
  { (* case 1 *)
    assert (Hw1: w = 1) by (apply (x1_w_of_len w 0); [lia|lia|exact E]).
    forward_for_simple_bound (Zlength (x1_wsyms rws w))
      (EX s: Z,
       PROP ()
       LOCAL (temp _uStart (vint (Zlength (x1_cur rws L w s)));
              temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint (2 ^ (w - 1)));
              temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
              temp _symbol (vint (x1_start rws w));
              temp _rankStart (vint (Zlength (x1_done rws L w)));
              temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_cur rws L w s)) cells;
            data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
    { pose proof (Hcnt w ltac:(lia)). rep_lia. }
    { rewrite x1_cur_0. entailer!. }
    { pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
      assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
        by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
      assert (Hsym: 0 <= Znth i (x1_wsyms rws w) < 256).
      { pose proof (x1_wsyms_range rws w (Znth i (x1_wsyms rws w)) ltac:(apply Znth_In; lia)). lia. }
      pose proof (x1_cur_len rws L w i ltac:(lia) ltac:(lia)) as Hcl.
      pose proof (x1_cur_bound rws L w (i + 1) ltac:(lia) ltac:(lia) Hkraft ltac:(lia)) as Hcb.
      assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
      assert (Hfit: 0 <= Zlength (x1_cur rws L w i) /\ Zlength (x1_cur rws L w i) + 2 ^ (w - 1) <= 2 ^ L)
        by (split; [apply Zlength_nonneg|]; rewrite Hcl; nia).
      clear Hcl Hcb.
      forward.
      { entailer!. rewrite x1_sym_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_sym_at by lia.
      forward. forward.
      rewrite !x1_zext by lia.
      forward. forward. forward. forward. forward.
      rewrite !x1_zext by lia.
      rewrite x1_upd2 by (rewrite x1_arr_len; lia).
      rewrite (x1_cur_succ rws L w i) by lia.
      assert (Hr1: repeat (Znth i (x1_wsyms rws w), L + 1 - w) (Z.to_nat (2 ^ (w - 1))) =
                   [(Znth i (x1_wsyms rws w), L + 1 - w)]) by (subst w; reflexivity).
      rewrite Hr1, <- x1_arr_upd by lia.
      entailer!.
      rewrite Zlength_app, Zlength_cons, Zlength_nil. reflexivity. }
    rewrite x1_cur_full by lia. forward. entailer!. }
  { (* case 2 *)
    assert (Hw1: w = 2) by (apply (x1_w_of_len w 1); [lia|lia|exact E]).
    forward_for_simple_bound (Zlength (x1_wsyms rws w))
      (EX s: Z,
       PROP ()
       LOCAL (temp _uStart (vint (Zlength (x1_cur rws L w s)));
              temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint (2 ^ (w - 1)));
              temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
              temp _symbol (vint (x1_start rws w));
              temp _rankStart (vint (Zlength (x1_done rws L w)));
              temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_cur rws L w s)) cells;
            data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
    { pose proof (Hcnt w ltac:(lia)). rep_lia. }
    { rewrite x1_cur_0. entailer!. }
    { pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
      assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
        by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
      assert (Hsym: 0 <= Znth i (x1_wsyms rws w) < 256).
      { pose proof (x1_wsyms_range rws w (Znth i (x1_wsyms rws w)) ltac:(apply Znth_In; lia)). lia. }
      pose proof (x1_cur_len rws L w i ltac:(lia) ltac:(lia)) as Hcl.
      pose proof (x1_cur_bound rws L w (i + 1) ltac:(lia) ltac:(lia) Hkraft ltac:(lia)) as Hcb.
      assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
      assert (Hfit: 0 <= Zlength (x1_cur rws L w i) /\ Zlength (x1_cur rws L w i) + 2 ^ (w - 1) <= 2 ^ L)
        by (split; [apply Zlength_nonneg|]; rewrite Hcl; nia).
      clear Hcl Hcb. rewrite E in Hfit.
      forward.
      { entailer!. rewrite x1_sym_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_sym_at by lia.
      forward. forward.
      rewrite !x1_zext by lia.
      forward. forward. forward. forward. forward. forward. forward. forward. forward.
      rewrite !x1_zext by lia.
      rewrite (x1_cur_succ rws L w i) by lia.
      assert (Hr2: repeat (Znth i (x1_wsyms rws w), L + 1 - w) (Z.to_nat (2 ^ (w - 1))) =
                   [(Znth i (x1_wsyms rws w), L + 1 - w)] ++ [(Znth i (x1_wsyms rws w), L + 1 - w)])
        by (subst w; reflexivity).
      rewrite Hr2, app_assoc.
      rewrite x1_arr_cell by lia.
      rewrite x1_arr_cell by (try rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      entailer!.
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. do 2 f_equal. lia. }
    rewrite x1_cur_full by lia. forward. entailer!. }
  { (* case 4 *)
    assert (Hw1: w = 3) by (apply (x1_w_of_len w 2); [lia|lia|exact E]).
    forward_for_simple_bound (Zlength (x1_wsyms rws w))
      (EX s: Z,
       PROP ()
       LOCAL (temp _uStart (vint (Zlength (x1_cur rws L w s)));
              temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint (2 ^ (w - 1)));
              temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
              temp _symbol (vint (x1_start rws w));
              temp _rankStart (vint (Zlength (x1_done rws L w)));
              temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_cur rws L w s)) cells;
            data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
    { pose proof (Hcnt w ltac:(lia)). rep_lia. }
    { rewrite x1_cur_0. entailer!. }
    { pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
      assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
        by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
      assert (Hsym: 0 <= Znth i (x1_wsyms rws w) < 256).
      { pose proof (x1_wsyms_range rws w (Znth i (x1_wsyms rws w)) ltac:(apply Znth_In; lia)). lia. }
      pose proof (x1_cur_len rws L w i ltac:(lia) ltac:(lia)) as Hcl.
      pose proof (x1_cur_bound rws L w (i + 1) ltac:(lia) ltac:(lia) Hkraft ltac:(lia)) as Hcb.
      assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
      assert (Hfit: 0 <= Zlength (x1_cur rws L w i) /\ Zlength (x1_cur rws L w i) + 2 ^ (w - 1) <= 2 ^ L)
        by (split; [apply Zlength_nonneg|]; rewrite Hcl; nia).
      clear Hcl Hcb. rewrite E in Hfit.
      forward.
      { entailer!. rewrite x1_sym_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_sym_at by lia.
      forward_call (Znth i (x1_wsyms rws w), L + 1 - w).
      forward.
      assert (Hv: 0 <= set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w) < 2 ^ 64) by (unfold set4_val; nia).
      sep_apply (x1_open4 shd (x1_cur rws L w i) cells FCc ltac:(lia)).
      forward_call (shd, offset_val (2 * Zlength (x1_cur rws L w i)) cells, Zrepeat Vundef 8, 0,
                    set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w)).
      { entailer!. }
      all: try (split; [auto|]; change (Zlength (Zrepeat Vundef 8)) with 8; lia).
      all: try (change (Zlength (Zrepeat Vundef 8)) with 8; cancel; fail).
      change (Zlength (Zrepeat Vundef 8)) with 8.
      rewrite x1_written by lia.
      sep_apply (x1_close4 shd (x1_cur rws L w i) cells (Znth i (x1_wsyms rws w)) (L + 1 - w) FCc ltac:(lia)).
      forward.
      rewrite (x1_cur_succ rws L w i) by lia.
      replace (Z.to_nat (2 ^ (w - 1))) with 4%nat by (rewrite E; reflexivity).
      entailer!.
      rewrite Zlength_app. reflexivity. }
    rewrite x1_cur_full by lia. forward. entailer!. }
  { (* case 8 *)
    assert (Hw1: w = 4) by (apply (x1_w_of_len w 3); [lia|lia|exact E]).
    forward_for_simple_bound (Zlength (x1_wsyms rws w))
      (EX s: Z,
       PROP ()
       LOCAL (temp _uStart (vint (Zlength (x1_cur rws L w s)));
              temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint (2 ^ (w - 1)));
              temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
              temp _symbol (vint (x1_start rws w));
              temp _rankStart (vint (Zlength (x1_done rws L w)));
              temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_cur rws L w s)) cells;
            data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
    { pose proof (Hcnt w ltac:(lia)). rep_lia. }
    { rewrite x1_cur_0. entailer!. }
    { clear Hw1.
      pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
      assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
        by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
      assert (Hsym: 0 <= Znth i (x1_wsyms rws w) < 256).
      { pose proof (x1_wsyms_range rws w (Znth i (x1_wsyms rws w)) ltac:(apply Znth_In; lia)). lia. }
      pose proof (x1_cur_len rws L w i ltac:(lia) ltac:(lia)) as Hcl.
      pose proof (x1_cur_bound rws L w (i + 1) ltac:(lia) ltac:(lia) Hkraft ltac:(lia)) as Hcb.
      assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
      assert (Hfit: 0 <= Zlength (x1_cur rws L w i) /\ Zlength (x1_cur rws L w i) + 2 ^ (w - 1) <= 2 ^ L)
        by (split; [apply Zlength_nonneg|]; rewrite Hcl; nia).
      clear Hcl Hcb. rewrite E in Hfit.
      forward.
      { entailer!. rewrite x1_sym_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_sym_at by lia.
      forward_call (Znth i (x1_wsyms rws w), L + 1 - w).
      forward.
      assert (Hv: 0 <= set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w) < 2 ^ 64) by (unfold set4_val; nia).
      sep_apply (x1_open4 shd (x1_cur rws L w i) cells FCc ltac:(lia)).
      forward_call (shd, offset_val (2 * Zlength (x1_cur rws L w i)) cells, Zrepeat Vundef 8, 0,
                    set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w)).
      { entailer!. }
      all: try (split; [auto|]; change (Zlength (Zrepeat Vundef 8)) with 8; lia).
      all: try (change (Zlength (Zrepeat Vundef 8)) with 8; cancel; fail).
      change (Zlength (Zrepeat Vundef 8)) with 8.
      rewrite x1_written by lia.
      sep_apply (x1_close4 shd (x1_cur rws L w i) cells (Znth i (x1_wsyms rws w)) (L + 1 - w) FCc ltac:(lia)).
      set (c4 := x1_cur rws L w i ++ repeat (Znth i (x1_wsyms rws w), L + 1 - w) 4).
      assert (Hc4: Zlength c4 = Zlength (x1_cur rws L w i) + 4) by (unfold c4; rewrite Zlength_app; reflexivity).
      sep_apply (x1_open4 shd c4 cells FCc ltac:(lia)).
      forward_call (shd, offset_val (2 * Zlength c4) cells, Zrepeat Vundef 8, 0,
                    set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w)).
      { entailer!. rewrite Hc4. simpl. f_equal. f_equal. lia. }
      all: try (split; [auto|]; change (Zlength (Zrepeat Vundef 8)) with 8; lia).
      all: try (change (Zlength (Zrepeat Vundef 8)) with 8; cancel; fail).
      change (Zlength (Zrepeat Vundef 8)) with 8.
      rewrite x1_written by lia.
      sep_apply (x1_close4 shd c4 cells (Znth i (x1_wsyms rws w)) (L + 1 - w) FCc ltac:(lia)).
      forward.
      rewrite (x1_cur_succ rws L w i) by lia.
      replace (Z.to_nat (2 ^ (w - 1))) with (4 + 4)%nat by (rewrite E; reflexivity).
      rewrite repeat_app, app_assoc. fold c4.
      entailer!.
      rewrite Zlength_app, Hc4. match goal with |- context [Zlength (repeat ?x 4)] => change (Zlength (repeat x 4)) with 4 end. do 2 f_equal. lia. }
    rewrite x1_cur_full by lia. forward. entailer!. }
  { (* default: 16 .. 2048 cells per symbol *)
    rewrite !Int.unsigned_repr in NE, NE0, NE1, NE2 by rep_lia.
    assert (Hw5: 5 <= w).
    { destruct (zlt w 5); [|lia]. exfalso.
      assert (w = 1 \/ w = 2 \/ w = 3 \/ w = 4) as Hc by lia. subst len.
      repeat destruct Hc as [Hc|Hc]; subst w; simpl in *; lia. }
    set (m := 2 ^ (w - 5)).
    assert (Hm: len = (16 * m)%Z).
    { subst len m. replace (w - 1) with (4 + (w - 5)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (Hm0: 1 <= m) by lia.
    forward_for_simple_bound (Zlength (x1_wsyms rws w))
      (EX s: Z,
       PROP ()
       LOCAL (temp _uStart (vint (Zlength (x1_cur rws L w s)));
              temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint len);
              temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
              temp _symbol (vint (x1_start rws w));
              temp _rankStart (vint (Zlength (x1_done rws L w)));
              temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (x1_cur rws L w s)) cells;
            data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
    { pose proof (Hcnt w ltac:(lia)). rep_lia. }
    { rewrite x1_cur_0. entailer!. }
    { pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
      assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
        by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
      assert (Hsym: 0 <= Znth i (x1_wsyms rws w) < 256).
      { pose proof (x1_wsyms_range rws w (Znth i (x1_wsyms rws w)) ltac:(apply Znth_In; lia)). lia. }
      pose proof (x1_cur_len rws L w i ltac:(lia) ltac:(lia)) as Hcl.
      pose proof (x1_cur_bound rws L w (i + 1) ltac:(lia) ltac:(lia) Hkraft ltac:(lia)) as Hcb.
      assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
      assert (Hfit: 0 <= Zlength (x1_cur rws L w i) /\ Zlength (x1_cur rws L w i) + 2 ^ (w - 1) <= 2 ^ L)
        by (split; [apply Zlength_nonneg|]; rewrite Hcl; nia).
      clear Hcl Hcb. rewrite <- Hlen_def in Hfit.
      forward.
      { entailer!. rewrite x1_sym_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite x1_sym_at by lia.
      forward_call (Znth i (x1_wsyms rws w), L + 1 - w).
      forward.
      assert (Hv: 0 <= set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w) < 2 ^ 64) by (unfold set4_val; nia).
      set (base := x1_cur rws L w i) in *.
      set (c := (Znth i (x1_wsyms rws w), L + 1 - w)).
      forward.
      forward_loop
        (EX j: Z,
         PROP (0 <= j <= m)
         LOCAL (temp _u__1 (vint (16 * j)); temp _D4__2 (Vlong (Int64.repr (set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w))));
                temp _s (vint i); temp _uStart (vint (Zlength base));
                temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint len);
                temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
                temp _symbol (vint (x1_start rws w));
                temp _rankStart (vint (Zlength (x1_done rws L w)));
                temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
                lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
                lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
         SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (base ++ repeat c (Z.to_nat (16 * j)))) cells;
              data_at Tsh tuint (vint L) vtl;
              field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
              field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
              data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert
      continue:
        (EX j: Z,
         PROP (0 <= j < m)
         LOCAL (temp _u__1 (vint (16 * j)); temp _D4__2 (Vlong (Int64.repr (set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w))));
                temp _s (vint i); temp _uStart (vint (Zlength base));
                temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint len);
                temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
                temp _symbol (vint (x1_start rws w));
                temp _rankStart (vint (Zlength (x1_done rws L w)));
                temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
                lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
                lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
         SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (base ++ repeat c (Z.to_nat (16 * j + 16)))) cells;
              data_at Tsh tuint (vint L) vtl;
              field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
              field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
              data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert
      break:
        (PROP ()
         LOCAL (temp _D4__2 (Vlong (Int64.repr (set4_val (Znth i (x1_wsyms rws w)) (L + 1 - w))));
                temp _s (vint i); temp _uStart (vint (Zlength base));
                temp _nbBits (vint (L + 1 - w)); temp _t'21 (vint L); temp _length (vint len);
                temp _symbolCount (vint (Zlength (x1_wsyms rws w))); temp _t'22 (vint L); temp _w__2 (vint w);
                temp _symbol (vint (x1_start rws w));
                temp _rankStart (vint (Zlength (x1_done rws L w)));
                temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
                lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
                lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
         SEP (data_at shd (tarray t_deltx1 8192) (x1_arr (base ++ repeat c (Z.to_nat len))) cells;
              data_at Tsh tuint (vint L) vtl;
              field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
              field_at shk t_x1wksp (DOT _symbols) (zbytes (x1_sorted rws) ++ sr) pk;
              data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1; F))%assert.
      { Exists 0. rewrite Z.mul_0_r. simpl repeat. rewrite app_nil_r. entailer!. }
      { Intros j. forward_if.
        { assert (Hj: 16 * j + 16 <= len) by lia.
          x1_wr shd cells FCc base c (16 * j)%Z (Znth i (x1_wsyms rws w)) (L + 1 - w).
          x1_wr shd cells FCc base c (16 * j + 4)%Z (Znth i (x1_wsyms rws w)) (L + 1 - w).
          x1_wr shd cells FCc base c (16 * j + 4 + 4)%Z (Znth i (x1_wsyms rws w)) (L + 1 - w).
          x1_wr shd cells FCc base c (16 * j + 4 + 4 + 4)%Z (Znth i (x1_wsyms rws w)) (L + 1 - w).
          Exists j. replace (16 * j + 4 + 4 + 4 + 4)%Z with (16 * j + 16)%Z by lia. entailer!. }
        { forward. assert (j = m) by lia. subst j. rewrite <- Hm. entailer!. } }
      { Intros j. forward. Exists (j + 1). replace (16 * (j + 1))%Z with (16 * j + 16)%Z by lia. entailer!. }
      forward.
      rewrite (x1_cur_succ rws L w i) by lia. rewrite <- Hlen_def. fold base c.
      entailer!.
      rewrite x1_rep_len2 by lia. reflexivity. }
    rewrite x1_cur_full by lia. forward. entailer!. }
  pose proof (x1_done_bound rws L w ltac:(lia) ltac:(lia) Hkraft) as Hdb.
  rewrite x1_block_len in Hdb by lia. rewrite <- Hlen_def in Hdb.
  pose proof (Hcnt w ltac:(lia)) as Hc. pose proof (x1_start_bound rws w ltac:(lia)) as Hsb.
  pose proof (Zlength_nonneg (x1_done rws L w)).
  assert (H4096: 2 ^ L <= 4096) by (change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia).
  assert (Hs256: Zlength (x1_sorted rws) = Zlength rws)
    by (apply x1_sorted_len; eapply Forall_impl; [|exact Hws]; intros; simpl in *; lia).
  forward. forward.
  Exists w. entailer!.
  rewrite x1_start_succ, x1_done_succ, Zlength_app, x1_block_len by lia. split; reflexivity.
Qed.
