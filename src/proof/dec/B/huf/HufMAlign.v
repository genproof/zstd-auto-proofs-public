(* Model lemmas for group HUF: canonical codes are aligned (the cell of an index
   depends only on its top `code length` bits), hence the second symbol of a two-symbol X2 cell
   (BRep.x2_cell_ok, computed from the L peeked bits shifted by the first code length, zeros below) is the
   model's next symbol. *)
Require Export Zstd.proof.dec.B.huf.HufMPeek.

(* ---- helpers: runs of 2^e equal cells, aligned when exponents increase and divide the total ---- *)

Fixpoint mal_runs {A: Type} (R: list (A * Z)) : list A :=
  match R with
  | nil => nil
  | (a, e) :: R' => repeat a (Z.to_nat (2 ^ e)) ++ mal_runs R'
  end.

Fixpoint mal_nondecr {A: Type} (R: list (A * Z)) : Prop :=
  match R with
  | nil => True
  | p :: R' => Forall (fun q => snd p <= snd q) R' /\ mal_nondecr R'
  end.

Lemma mal_runs_app {A: Type} (R1 R2: list (A * Z)) : mal_runs (R1 ++ R2) = mal_runs R1 ++ mal_runs R2.
Proof.
  induction R1 as [|[a e] R1 IH]; simpl; auto. rewrite IH, app_assoc. auto.
Qed.

Lemma mal_runs_flat_map {A B: Type} (f: B -> list (A * Z)) (l: list B) :
  mal_runs (flat_map f l) = flat_map (fun x => mal_runs (f x)) l.
Proof.
  induction l as [|b l IH]; simpl; auto. rewrite mal_runs_app, IH. auto.
Qed.

Lemma mal_len_div {A: Type} (R: list (A * Z)) (e: Z) :
  0 <= e -> Forall (fun q => e <= snd q) R -> (2 ^ e | Z.of_nat (length (mal_runs R))).
Proof.
  induction R as [|[a e'] R IH]; simpl; intros He HF.
  - exists 0. auto.
  - inversion HF; subst. simpl in *.
    rewrite app_length, repeat_length, Nat2Z.inj_add, Z2Nat.id by (apply Z.pow_nonneg; lia).
    apply Z.divide_add_r; auto.
    exists (2 ^ (e' - e)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma mal_runs_aligned {A: Type} (E: A -> Z) (d: A) : forall (R: list (A * Z)) (off x y: Z),
  Forall (fun p => 0 <= snd p /\ snd p = E (fst p) /\ (2 ^ snd p | off + Z.of_nat (length (mal_runs R)))) R ->
  mal_nondecr R -> 0 <= x < Z.of_nat (length (mal_runs R)) ->
  (off + x) / 2 ^ E (nth (Z.to_nat x) (mal_runs R) d) = (off + y) / 2 ^ E (nth (Z.to_nat x) (mal_runs R) d) ->
  0 <= y < Z.of_nat (length (mal_runs R)) /\ nth (Z.to_nat y) (mal_runs R) d = nth (Z.to_nat x) (mal_runs R) d.
Proof.
  induction R as [|[a e] R IH]; intros off x y HF HN Hx Hd; cbn [mal_runs mal_nondecr length] in *.
  - lia.
  - destruct HN as [HN1 HN].
    inversion HF as [|? ? [He0 [HeE Hdiv]] HF']; subst. simpl in He0, HeE, Hdiv.
    assert (Hp: 0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
    rewrite app_length, repeat_length, Nat2Z.inj_add, Z2Nat.id in * by lia.
    assert (HlR := mal_len_div R e He0 HN1).
    assert (Hoff: (2 ^ e | off)).
    { replace off with (off + (2 ^ e + Z.of_nat (length (mal_runs R))) - 2 ^ e - Z.of_nat (length (mal_runs R))) by lia.
      apply Z.divide_sub_r; [apply Z.divide_sub_r|]; auto. apply Z.divide_refl. }
    destruct Hoff as [k Hk]. subst off.
    destruct (Z_lt_le_dec x (2 ^ e)) as [Hxs|Hxs].
    + assert (Hnx: nth (Z.to_nat x) (repeat a (Z.to_nat (2 ^ e)) ++ mal_runs R) d = a).
      { rewrite app_nth1 by (rewrite repeat_length; lia). apply (repeat_spec (Z.to_nat (2 ^ e))); apply nth_In; rewrite repeat_length; lia. }
      rewrite Hnx in Hd |- *. rewrite <- HeE in Hd.
      rewrite !Z.div_add_l in Hd by lia.
      rewrite (Z.div_small x) in Hd by lia.
      assert (Hy0: y / 2 ^ e = 0) by lia.
      apply Z.div_small_iff in Hy0; [|lia].
      split; [lia|].
      rewrite app_nth1 by (rewrite repeat_length; lia). apply (repeat_spec (Z.to_nat (2 ^ e))); apply nth_In; rewrite repeat_length; lia.
    + assert (Hnx: nth (Z.to_nat x) (repeat a (Z.to_nat (2 ^ e)) ++ mal_runs R) d =
                   nth (Z.to_nat (x - 2 ^ e)) (mal_runs R) d).
      { rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length. f_equal. lia. }
      rewrite Hnx in Hd |- *.
      destruct (IH (k * 2 ^ e + 2 ^ e) (x - 2 ^ e) (y - 2 ^ e)) as [Hy Heq].
      * eapply Forall_impl; [|exact HF']. simpl. intros q [? [? Hq]]. split; [auto|split; [auto|]].
        rewrite Z.add_assoc in Hq. exact Hq.
      * exact HN.
      * lia.
      * replace (k * 2 ^ e + 2 ^ e + (x - 2 ^ e)) with (k * 2 ^ e + x) by lia.
        replace (k * 2 ^ e + 2 ^ e + (y - 2 ^ e)) with (k * 2 ^ e + y) by lia. exact Hd.
      * split; [lia|].
        rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
        replace (Z.to_nat y - Z.to_nat (2 ^ e))%nat with (Z.to_nat (y - 2 ^ e)) by lia. exact Heq.
Qed.

Lemma mal_nondecr_app {A: Type} (R1 R2: list (A * Z)) :
  mal_nondecr R1 -> mal_nondecr R2 -> (forall p q, In p R1 -> In q R2 -> snd p <= snd q) ->
  mal_nondecr (R1 ++ R2).
Proof.
  induction R1 as [|p R1 IH]; simpl; intros H1 H2 H12; auto.
  destruct H1 as [H1a H1b]. split.
  - apply Forall_app. split; auto. apply Forall_forall. intros q Hq. apply H12; auto.
  - apply IH; auto.
Qed.

Lemma mal_nondecr_const {A: Type} (R: list (A * Z)) (c: Z) :
  (forall p, In p R -> snd p = c) -> mal_nondecr R.
Proof.
  induction R as [|p R IH]; simpl; intros H; auto. split.
  - apply Forall_forall. intros q Hq. rewrite (H p), (H q); auto. lia.
  - apply IH. auto.
Qed.

(* the runs of the canonical cells: symbol s of weight w, exponent w - 1 *)
Definition mal_R (ht: huf_table) : list ((Z * Z) * Z) :=
  flat_map (fun w =>
    flat_map (fun s =>
      if nth s (ht_weights ht) 0 =? w then [((Z.of_nat s, ht_log ht + 1 - w), w - 1)] else nil)
      (seq 0 (length (ht_weights ht))))
    (map Z.of_nat (seq 1 (Z.to_nat (ht_log ht)))).

Lemma mal_cells_runs (ht: huf_table) : huf_cells ht = mal_runs (mal_R ht).
Proof.
  unfold huf_cells, mal_R. rewrite mal_runs_flat_map. apply flat_map_ext. intros w.
  rewrite mal_runs_flat_map. apply flat_map_ext. intros s.
  destruct (nth s (ht_weights ht) 0 =? w); simpl; auto. rewrite app_nil_r. auto.
Qed.

Lemma mal_inner_snd (ht: huf_table) (w: Z) (p: (Z * Z) * Z) :
  In p (flat_map (fun s =>
      if nth s (ht_weights ht) 0 =? w then [((Z.of_nat s, ht_log ht + 1 - w), w - 1)] else nil)
      (seq 0 (length (ht_weights ht)))) ->
  exists s, p = ((Z.of_nat s, ht_log ht + 1 - w), w - 1).
Proof.
  intros H. apply in_flat_map in H. destruct H as [s [_ Hs]].
  destruct (nth s (ht_weights ht) 0 =? w); simpl in Hs; [|contradiction].
  destruct Hs as [<-|[]]. eauto.
Qed.

Lemma mal_R_in (ht: huf_table) (p: (Z * Z) * Z) :
  In p (mal_R ht) -> exists s w, p = ((Z.of_nat s, ht_log ht + 1 - w), w - 1) /\ 1 <= w <= ht_log ht.
Proof.
  unfold mal_R. intros H. apply in_flat_map in H. destruct H as [w [Hw Hp]].
  apply in_map_iff in Hw. destruct Hw as [k [<- Hk]]. apply in_seq in Hk.
  apply mal_inner_snd in Hp. destruct Hp as [s ->]. exists s, (Z.of_nat k). split; auto. lia.
Qed.

Lemma mal_R_nondecr_gen (ht: huf_table) : forall (n a: nat),
  mal_nondecr (flat_map (fun w =>
    flat_map (fun s =>
      if nth s (ht_weights ht) 0 =? w then [((Z.of_nat s, ht_log ht + 1 - w), w - 1)] else nil)
      (seq 0 (length (ht_weights ht))))
    (map Z.of_nat (seq a n))).
Proof.
  induction n as [|n IH]; intros a; simpl; auto.
  apply mal_nondecr_app; auto.
  - apply (mal_nondecr_const _ (Z.of_nat a - 1)). intros p Hp.
    apply mal_inner_snd in Hp. destruct Hp as [s ->]. auto.
  - intros p q Hp Hq. apply mal_inner_snd in Hp. destruct Hp as [s ->]. simpl.
    apply in_flat_map in Hq. destruct Hq as [w [Hw Hq]].
    apply in_map_iff in Hw. destruct Hw as [k [<- Hk]]. apply in_seq in Hk.
    apply mal_inner_snd in Hq. destruct Hq as [s' ->]. simpl. lia.
Qed.

Lemma huf_cells_aligned (ht: huf_table) (x y: Z) :
  huf_ok ht -> 0 <= x < 2 ^ ht_log ht -> 0 <= y < 2 ^ ht_log ht ->
  x / 2 ^ (ht_log ht - snd (nth (Z.to_nat x) (huf_cells ht) (0, 0))) =
  y / 2 ^ (ht_log ht - snd (nth (Z.to_nat x) (huf_cells ht) (0, 0))) ->
  nth (Z.to_nat y) (huf_cells ht) (0, 0) = nth (Z.to_nat x) (huf_cells ht) (0, 0).
Proof.
  intros Hok Hx Hy Hd.
  destruct Hok as [Hlog [Hlen _]].
  rewrite Zlength_correct in Hlen.
  rewrite mal_cells_runs in *.
  assert (H := mal_runs_aligned (fun c => ht_log ht - snd c) (0, 0) (mal_R ht) 0 x y).
  rewrite !Z.add_0_l in H. apply H; auto.
  - apply Forall_forall. intros p Hp. apply mal_R_in in Hp. destruct Hp as [s [w [-> Hw]]]. simpl.
    split; [lia|]. split; [lia|]. rewrite Hlen.
    exists (2 ^ (ht_log ht - (w - 1))). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  - apply mal_R_nondecr_gen.
  - lia.
Qed.

(* ---- a local copy of HufMPeek's proof, so that hsym_pair does not depend on HufMPeek.hsym_peek (proved
   separately, in HufMPeek.v) ---- *)

Lemma malp_le_value_range (s: list Z) : bytes_ok s -> 0 <= le_value s.
Proof.
  induction s as [|b s IH]; intros H; cbn [le_value]; [lia|].
  inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb. specialize (IH Hs). lia.
Qed.

Lemma malp_le_value_skipn (k: nat) (s: list Z) :
  bytes_ok s -> le_value s / 2 ^ (8 * Z.of_nat k) = le_value (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H.
  - replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.div_1_r. reflexivity.
  - destruct s as [|b s]; cbn [le_value skipn].
    + rewrite Zdiv_0_l. reflexivity.
    + inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb.
      rewrite <- (IH s Hs).
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
      assert (0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by lia.
      f_equal. change (2 ^ 8) with 256.
      rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma malp_le_value_firstn (k: nat) (s: list Z) :
  bytes_ok s -> le_value (firstn k s) = le_value s mod 2 ^ (8 * Z.of_nat k).
Proof.
  revert s; induction k as [|k IH]; intros s H.
  - replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.mod_1_r. reflexivity.
  - destruct s as [|b s]; cbn [le_value firstn].
    + rewrite Zmod_0_l. reflexivity.
    + inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb.
      rewrite (IH s Hs).
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
      assert (0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite Z.rem_mul_r by lia.
      rewrite (Z.add_comm b), (Z.mul_comm 256 (le_value s)), Z_mod_plus_full.
      rewrite (Z.mod_small b 256) by lia.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. lia.
Qed.

Lemma malp_bytes_ok_skipn (k: nat) (s: list Z) : bytes_ok s -> bytes_ok (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H; [exact H|].
  destruct s as [|b s]; [exact H|]. cbn [skipn]. inversion H; subst. auto.
Qed.

(* (a mod (b c)) / b = (a / b) mod c *)
Lemma malp_mod_div (a b c: Z) : 0 < b -> 0 < c -> (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros Hb Hc. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm b ((a / b) mod c)), Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma malp_mod_mod_pow (a k n: Z) : 0 <= k <= n -> (a mod 2 ^ n) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros H. replace n with (k + (n - k)) by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (n - k)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma malp_peek_scale (V pos nb L: Z) :
  0 <= pos -> 0 <= nb <= L -> bs_peek V pos L / 2 ^ (L - nb) = bs_peek V pos nb.
Proof.
  intros Hp Hn. unfold bs_peek.
  assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (L - nb)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_div by lia.
  replace L with (nb + (L - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z.div_mul_cancel_r; lia.
Qed.

Lemma malp_le_value_window (s: list Z) (q: Z) :
  bytes_ok s -> 0 <= q -> le_value (slice s q 5) = (le_value s / 2 ^ (8 * q)) mod 2 ^ 40.
Proof.
  intros H Hq. unfold slice.
  rewrite malp_le_value_firstn by (apply malp_bytes_ok_skipn; exact H).
  rewrite <- malp_le_value_skipn by exact H.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma malp_peek_eq (s: list Z) (pos nb: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= 32 -> bs_peek (bs_value s) pos nb = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn. unfold bs_peek_s, bs_peek, bs_value.
  destruct (pos <? 0) eqn:E; [lia|].
  set (V := le_value s).
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  destruct (pos - nb >=? 0) eqn:E2.
  - set (lo := pos - nb).
    assert (Hlo: 0 <= lo) by lia.
    assert (0 < 2 ^ lo) by (apply Z.pow_pos_nonneg; lia).
    replace pos with (lo + nb) by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.div_mul_cancel_r by lia. rewrite malp_mod_div by lia.
    rewrite malp_le_value_window by (auto; apply Z.div_pos; lia).
    fold V.
    assert (Hr: 0 <= lo mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (0 < 2 ^ (lo mod 8)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq: 0 <= lo / 8) by (apply Z.div_pos; lia).
    assert (0 < 2 ^ (8 * (lo / 8))) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ 40) with (2 ^ (lo mod 8) * 2 ^ (40 - lo mod 8))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite malp_mod_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite malp_mod_mod_pow by lia.
    rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia.
    rewrite <- (Z_div_mod_eq_full lo 8). reflexivity.
  - assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 2 ^ (- (pos - nb))) by (apply Z.pow_pos_nonneg; lia).
    replace nb with (pos + - (pos - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.mul_assoc, (Z.mul_comm _ (2 ^ pos)), <- Z.mul_assoc, (Z.mul_comm (2 ^ pos)), Z.div_mul by lia.
    f_equal. unfold slice. replace (Z.to_nat 0) with O by reflexivity. cbn [skipn].
    rewrite malp_le_value_firstn by exact Hs.
    replace (8 * Z.of_nat (Z.to_nat 5)) with 40 by reflexivity.
    rewrite malp_mod_mod_pow by lia. reflexivity.
Qed.

Lemma malp_bs_peek_div (s: list Z) (pos nb L: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= L -> L <= 32 ->
  bs_peek (bs_value s) pos L / 2 ^ (L - nb) = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn HL. rewrite malp_peek_scale by lia. apply malp_peek_eq; auto; lia.
Qed.

Lemma malp_hsym_peek (ht: huf_table) (s: list Z) (L pos: Z) :
  0 <= ht_log ht <= L -> L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  hsym ht L (bs_peek (bs_value s) pos L) = nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0).
Proof.
  intros Hl HL Hs Hp. unfold hsym. unfold HUF_TABLELOG_MAX in HL.
  rewrite malp_bs_peek_div by (auto; lia). reflexivity.
Qed.

Lemma mal_peek_bit (V p L i: Z) :
  0 <= p -> 0 <= L -> 0 <= i -> Z.testbit (bs_peek V p L) i = andb (i <? L) (Z.testbit V (i + p - L)).
Proof.
  intros Hp HL Hi. unfold bs_peek.
  rewrite <- Z.shiftl_mul_pow2, <- Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_spec, Z.shiftl_spec, Z.testbit_mod_pow2 by lia.
  replace (i + p - L) with (i + p - L) by lia.
  destruct (Z.ltb_spec (i + p - L) p), (Z.ltb_spec i L); auto; lia.
Qed.

Lemma mal_peek_range (V p L: Z) : 0 <= L -> 0 <= bs_peek V p L < 2 ^ L.
Proof.
  intros HL. unfold bs_peek. destruct (Z_lt_le_dec p 0) as [Hp|Hp].
  - rewrite (Z.pow_neg_r 2 p Hp), Zdiv_0_r. split; [lia|]. apply Z.pow_pos_nonneg; lia.
  - assert (H1: 0 < 2 ^ p) by (apply Z.pow_pos_nonneg; lia).
    assert (H2: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
    assert (H3 := Z.mod_pos_bound V (2 ^ p) H1).
    split.
    + apply Z.div_pos; [apply Z.mul_nonneg_nonneg|]; lia.
    + apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(* the top L - n1 bits of (v << n1) mod 2^L are the L-bit peek n1 bits further down *)
Lemma mal_peek_shift (V p L n1: Z) :
  0 <= n1 <= L -> n1 <= p ->
  ((bs_peek V p L * 2 ^ n1) mod 2 ^ L) / 2 ^ n1 = bs_peek V (p - n1) L / 2 ^ n1.
Proof.
  intros Hn Hp. apply Z.bits_inj'. intros i Hi.
  rewrite <- !Z.shiftr_div_pow2 by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.testbit_mod_pow2 by lia.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec by lia.
  rewrite !mal_peek_bit by lia.
  replace (i + n1 - n1) with i by lia.
  replace (i + n1 + (p - n1) - L) with (i + p - L) by lia.
  destruct (Z.ltb_spec (i + n1) L), (Z.ltb_spec i L); simpl; auto; lia.
Qed.

Lemma mal_hsym_range (ht: huf_table) (L u: Z) :
  huf_ok ht -> ht_log ht <= L -> 0 <= u < 2 ^ L ->
  0 <= u / 2 ^ (L - ht_log ht) < 2 ^ ht_log ht /\ 1 <= snd (hsym ht L u) <= ht_log ht.
Proof.
  intros [Hlog [Hlen HF]] HL Hu.
  assert (H1: 0 < 2 ^ (L - ht_log ht)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hi: 0 <= u / 2 ^ (L - ht_log ht) < 2 ^ ht_log ht).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (L - ht_log ht + ht_log ht) with L by lia. lia. }
  split; auto. unfold hsym. rewrite Forall_forall in HF.
  refine (proj2 (HF _ _)). apply nth_In. rewrite Zlength_correct in Hlen. lia.
Qed.

Lemma hsym_pair (ht: huf_table) (s: list Z) (L pos v n1: Z) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok s ->
  v = bs_peek (bs_value s) pos L -> n1 = snd (hsym ht L v) -> 0 <= pos - n1 ->
  n1 + snd (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) <= L ->
  hsym ht L ((v * 2 ^ n1) mod 2 ^ L) = nth (Z.to_nat (bs_peek_s s (pos - n1) (ht_log ht))) (huf_cells ht) (0, 0).
Proof.
  intros Hok HL Hs Hv Hn1 Hpos Hfit.
  assert (Hok' := Hok). destruct Hok' as [Hlog _].
  assert (Hvr: 0 <= v < 2 ^ L) by (subst v; apply mal_peek_range; lia).
  destruct (mal_hsym_range ht L v Hok ltac:(lia) Hvr) as [_ Hn1r]. rewrite <- Hn1 in Hn1r.
  assert (HP2: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (Hv2r: 0 <= (v * 2 ^ n1) mod 2 ^ L < 2 ^ L) by (apply Z.mod_pos_bound; lia).
  destruct (mal_hsym_range ht L _ Hok ltac:(lia) Hv2r) as [Hxr Hn2r].
  set (w := bs_peek (bs_value s) (pos - n1) L).
  assert (Hwr: 0 <= w < 2 ^ L) by (apply mal_peek_range; lia).
  destruct (mal_hsym_range ht L w Hok ltac:(lia) Hwr) as [Hyr _].
  rewrite <- (malp_hsym_peek ht s L (pos - n1)) by (auto; lia). fold w.
  revert Hfit Hn2r. unfold hsym. intros Hfit Hn2r.
  symmetry. apply huf_cells_aligned; auto.
  set (n2 := snd (nth (Z.to_nat ((v * 2 ^ n1) mod 2 ^ L / 2 ^ (L - ht_log ht))) (huf_cells ht) (0, 0))) in *.
  assert (Ha: 0 < 2 ^ (L - ht_log ht)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hb: 0 < 2 ^ (ht_log ht - n2)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hc: 0 < 2 ^ n1) by (apply Z.pow_pos_nonneg; lia).
  assert (Hd: 0 < 2 ^ (L - n2 - n1)) by (apply Z.pow_pos_nonneg; lia).
  rewrite !Z.div_div by lia.
  rewrite <- !Z.pow_add_r by lia.
  replace (L - ht_log ht + (ht_log ht - n2)) with (n1 + (L - n2 - n1)) by lia.
  rewrite Z.pow_add_r by lia. rewrite <- !Z.div_div by lia.
  subst v w. rewrite mal_peek_shift by lia. reflexivity.
Qed.
