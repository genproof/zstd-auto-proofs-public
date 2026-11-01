(* X1D: the body of HUF_decodeStreamX1 (spec in HufX1DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX1DSpecs.

(* HufMPeek.hsym_peek, proved here under local names so that this body does not depend on HufMPeek's
   lemmas. *)
Lemma hmp_le_value_range (s: list Z) : bytes_ok s -> 0 <= le_value s.
Proof.
  induction s as [|b s IH]; intros H; cbn [le_value]; [lia|].
  inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb. specialize (IH Hs). lia.
Qed.

Lemma hmp_le_value_skipn (k: nat) (s: list Z) :
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

Lemma hmp_le_value_firstn (k: nat) (s: list Z) :
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

Lemma hmp_bytes_ok_skipn (k: nat) (s: list Z) : bytes_ok s -> bytes_ok (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H; [exact H|].
  destruct s as [|b s]; [exact H|]. cbn [skipn]. inversion H; subst. auto.
Qed.

(* (a mod (b c)) / b = (a / b) mod c *)
Lemma hmp_mod_div (a b c: Z) : 0 < b -> 0 < c -> (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros Hb Hc. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm b ((a / b) mod c)), Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma hmp_mod_mod_pow (a k n: Z) : 0 <= k <= n -> (a mod 2 ^ n) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros H. replace n with (k + (n - k)) by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (n - k)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma hmp_peek_scale (V pos nb L: Z) :
  0 <= pos -> 0 <= nb <= L -> bs_peek V pos L / 2 ^ (L - nb) = bs_peek V pos nb.
Proof.
  intros Hp Hn. unfold bs_peek.
  assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (L - nb)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_div by lia.
  replace L with (nb + (L - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z.div_mul_cancel_r; lia.
Qed.

Lemma hmp_le_value_window (s: list Z) (q: Z) :
  bytes_ok s -> 0 <= q -> le_value (slice s q 5) = (le_value s / 2 ^ (8 * q)) mod 2 ^ 40.
Proof.
  intros H Hq. unfold slice.
  rewrite hmp_le_value_firstn by (apply hmp_bytes_ok_skipn; exact H).
  rewrite <- hmp_le_value_skipn by exact H.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma hmp_peek_eq (s: list Z) (pos nb: Z) :
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
    rewrite Z.div_mul_cancel_r by lia. rewrite hmp_mod_div by lia.
    rewrite hmp_le_value_window by (auto; apply Z.div_pos; lia).
    fold V.
    assert (Hr: 0 <= lo mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (0 < 2 ^ (lo mod 8)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq: 0 <= lo / 8) by (apply Z.div_pos; lia).
    assert (0 < 2 ^ (8 * (lo / 8))) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ 40) with (2 ^ (lo mod 8) * 2 ^ (40 - lo mod 8))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite hmp_mod_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite hmp_mod_mod_pow by lia.
    rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia.
    rewrite <- (Z_div_mod_eq_full lo 8). reflexivity.
  - assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 2 ^ (- (pos - nb))) by (apply Z.pow_pos_nonneg; lia).
    replace nb with (pos + - (pos - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.mul_assoc, (Z.mul_comm _ (2 ^ pos)), <- Z.mul_assoc, (Z.mul_comm (2 ^ pos)), Z.div_mul by lia.
    f_equal. unfold slice. replace (Z.to_nat 0) with O by reflexivity. cbn [skipn].
    rewrite hmp_le_value_firstn by exact Hs.
    replace (8 * Z.of_nat (Z.to_nat 5)) with 40 by reflexivity.
    rewrite hmp_mod_mod_pow by lia. reflexivity.
Qed.

Lemma x1s_bs_peek_div (s: list Z) (pos nb L: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= L -> L <= 32 ->
  bs_peek (bs_value s) pos L / 2 ^ (L - nb) = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn HL. rewrite hmp_peek_scale by lia. apply hmp_peek_eq; auto; lia.
Qed.

Lemma x1s_hsym_peek (ht: huf_table) (s: list Z) (L pos: Z) :
  0 <= ht_log ht <= L -> L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  hsym ht L (bs_peek (bs_value s) pos L) = nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0).
Proof.
  intros Hl HL Hs Hp. unfold hsym. unfold HUF_TABLELOG_MAX in HL.
  rewrite x1s_bs_peek_div by (auto; lia). reflexivity.
Qed.

Local Open Scope logic.

(* ---------- pure facts ---------- *)

Lemma bit_rep_inv sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

(* BIT_reloadDStream never raises the window base; from a non-overflowed state, unfinished leaves at
   least 57 bits in the container, any other status puts the window at the bottom. *)
Lemma bs_reload_facts (pos lo: Z) :
  0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
  snd (bs_reload pos lo) <= lo /\
  (lo <= pos ->
   (fst (bs_reload pos lo) = BIT_unfinished -> snd (bs_reload pos lo) + 57 <= pos) /\
   (fst (bs_reload pos lo) <> BIT_unfinished -> snd (bs_reload pos lo) = 0)).
Proof.
  intros H0 H8 H64. unfold bs_reload.
  pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)).
  pose proof (Z.div_mod lo 8 ltac:(lia)).
  assert (0 <= (lo + 64 - pos) / 8) by (apply Z.div_pos; lia).
  destruct (pos <? lo) eqn:E1; [cbn [fst snd]; split; [lia | intros; lia]|].
  destruct (8 <=? lo / 8) eqn:E2; [cbn [fst snd]; unfold BIT_unfinished; split; [lia|split; intros; lia]|].
  destruct (lo / 8 =? 0) eqn:E3.
  - assert (lo = 0) by lia. subst lo. cbn [fst snd].
    split; [lia|]. intros _. destruct (0 <? pos); unfold BIT_unfinished, BIT_endOfBuffer, BIT_completed;
    split; intros; lia.
  - destruct (lo / 8 <? (lo + 64 - pos) / 8) eqn:E4; cbn [fst snd];
      unfold BIT_unfinished, BIT_endOfBuffer; split; try lia; split; intros; lia.
Qed.

Section Model.
Variables (ht: huf_table) (s: list Z) (L: Z).
Hypotheses (Hht: huf_ok ht) (HL: ht_log ht <= L <= HUF_TABLELOG_MAX) (Hs: bytes_ok s).

Lemma bs_peek_range (V pos nb: Z) : 0 <= pos -> 0 <= nb -> 0 <= bs_peek V pos nb < 2 ^ nb.
Proof.
  intros Hp Hn. unfold bs_peek.
  assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound V (2 ^ pos) ltac:(lia)).
  split.
  - apply Z.div_pos; [apply Z.mul_nonneg_nonneg|]; lia.
  - apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma cell_nb_nonneg (i: nat) : 0 <= snd (nth i (huf_cells ht) (0, 0)).
Proof.
  destruct Hht as (_ & _ & Hall). destruct (lt_dec i (length (huf_cells ht))).
  - rewrite Forall_forall in Hall. specialize (Hall _ (nth_In _ (0, 0) l)). lia.
  - rewrite nth_overflow by lia. simpl. lia.
Qed.

(* one model step from pos is the C step at the exact peek *)
Lemma mstep (n: nat) (pos: Z) (r: list Z) :
  huf_decode_syms ht s (S n) pos = Some (r, 0) ->
  0 < pos /\
  exists r', r = fst (hsym ht L (bs_peek (bs_value s) pos L)) :: r' /\
     huf_decode_syms ht s n (pos - snd (hsym ht L (bs_peek (bs_value s) pos L))) = Some (r', 0).
Proof.
  intros H. simpl in H.
  destruct (Z_lt_le_dec pos 0) as [Hneg|Hpos].
  - exfalso. pose proof (cell_nb_nonneg (Z.to_nat (bs_peek_s s pos (ht_log ht)))).
    destruct (nth _ (huf_cells ht) (0, 0)) as [c nb] eqn:Ec. simpl in H0.
    destruct (pos - nb <? 0) eqn:E; [discriminate|]. lia.
  - assert (Hlog: 0 <= ht_log ht <= L) by (destruct Hht; lia).
    rewrite <- (x1s_hsym_peek ht s L pos Hlog ltac:(lia) Hs Hpos) in H.
    pose proof (bs_peek_range (bs_value s) pos L Hpos ltac:(lia)).
    pose proof (hsym_range ht L (bs_peek (bs_value s) pos L) Hht ltac:(lia) H0) as [_ Hnb].
    destruct (hsym ht L (bs_peek (bs_value s) pos L)) as [c nb] eqn:Ec. simpl in *.
    destruct (pos - nb <? 0) eqn:E; [discriminate|].
    destruct (huf_decode_syms ht s n (pos - nb)) as [[l p]|] eqn:E2; [|discriminate].
    inversion H; subst. split; [lia|]. eexists; split; [reflexivity|]. first [exact E2 | reflexivity].
Qed.

Variables (k pos0: Z).

(* the ghost validity: the model's run of k symbols from pos0 to 0 goes through (j, pos, l) *)
Definition vgood (j pos: Z) (l: list Z) : Prop :=
  forall l', huf_decode_syms ht s (Z.to_nat k) pos0 = Some (l', 0) ->
  exists r, huf_decode_syms ht s (Z.to_nat (k - j)) pos = Some (r, 0) /\ l' = l ++ r.

Lemma vgood_0 : vgood 0 pos0 [].
Proof. intros l' H. exists l'. rewrite Z.sub_0_r. auto. Qed.

Lemma vstep (j pos v: Z) (l: list Z) :
  0 <= j < k -> (exists l', huf_decode_syms ht s (Z.to_nat k) pos0 = Some (l', 0)) ->
  vgood j pos l -> (0 < pos -> v = bs_peek (bs_value s) pos L) ->
  0 < pos /\ v = bs_peek (bs_value s) pos L /\
  vgood (j + 1) (pos - snd (hsym ht L v)) (l ++ [fst (hsym ht L v)]).
Proof.
  intros Hj [l0 Hl0] Hg Hv.
  destruct (Hg l0 Hl0) as [r [Hr _]].
  replace (Z.to_nat (k - j)) with (S (Z.to_nat (k - (j + 1)))) in Hr by lia.
  destruct (mstep _ _ _ Hr) as [Hp _]. specialize (Hv Hp). subst v.
  split; [exact Hp|]. split; [reflexivity|].
  intros l' Hl'. destruct (Hg l' Hl') as [r1 [Hr1 ->]].
  replace (Z.to_nat (k - j)) with (S (Z.to_nat (k - (j + 1)))) in Hr1 by lia.
  destruct (mstep _ _ _ Hr1) as [_ [r' [-> Hr']]].
  exists r'. split; [exact Hr'|]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma vstep' (j pos v: Z) (l: list Z) :
  0 <= j < k -> vgood j pos l -> (0 < pos -> v = bs_peek (bs_value s) pos L) ->
  vgood (j + 1) (pos - snd (hsym ht L v)) (l ++ [fst (hsym ht L v)]).
Proof. intros Hj Hg Hv l0 Hl0. eapply vstep; eauto. Qed.

Lemma vgood_end (pos: Z) (l l': list Z) :
  vgood k pos l -> huf_decode_syms ht s (Z.to_nat k) pos0 = Some (l', 0) -> l = l' /\ pos = 0.
Proof.
  intros Hg Hl. destruct (Hg l' Hl) as [r [Hr ->]].
  rewrite Z.sub_diag in Hr. simpl in Hr. inversion Hr; subst. rewrite app_nil_r. auto.
Qed.

End Model.

(* ---------- the exact model (ExHuf.xh_x1_stream) as a forward invariant ---------- *)

(* the table's log is the reader's (kept folded, so that VST's substitutions leave L alone) *)
Definition x1_log_is (ht: huf_table) (L: Z) : Prop := L = xh_x1_log ht.

(* BIT_lookBitsFast reads only the container and bitsConsumed: equal on both descriptions of a state *)
Lemma xb_look_fast_rel (s: list Z) (p lo: Z) (d: xbit) (nb: Z) :
  xb_rel s p lo d -> xb_look_fast d nb = xb_look_fast (xb_of s p lo) nb.
Proof. intros (Hc & Hb & _). unfold xb_look_fast, xb_of. simpl. rewrite Hc, Hb. reflexivity. Qed.

(* HUF_decodeSymbolX1 at the C's peek v is the model's symbol step *)
Lemma x1_sym_of (ht: huf_table) (s: list Z) (L v p lo: Z) :
  x1_log_is ht L -> 0 <= v < 2 ^ L -> v = xb_look_fast (xb_of s p lo) L ->
  forall d, xb_rel s p lo d ->
  xh_x1_sym (xhuf_of false ht) d = (fst (hsym ht L v), xb_skip d (snd (hsym ht L v))).
Proof.
  intros HL Hv Hx d Hd. unfold xh_x1_sym, xh_cell. unfold x1_log_is in HL. cbn [xhuf_of xh_log xh_cells].
  rewrite <- HL, (xb_look_fast_rel s p lo d L Hd), <- Hx, xh_cells_x1_nth by exact Hv. reflexivity.
Qed.

Section Exact.
Variables (ht: huf_table) (s: list Z) (pos0 lo0 k: Z).

Local Notation t := (xhuf_of false ht).

(* the tail of HUF_decodeStreamX1 after the 4-symbol loop *)
Definition x1_fin (r: list Z * xbit * Z) : list Z * xbit :=
  let '(a, d, rem) := r in let '(b, d') := xh_x1_n t d (Z.to_nat rem) in (a ++ b, d').

(* inside the 4-symbol loop: j bytes l written, m symbols of the current body left, the reader at (p, lo);
   for every description dx of the initial state, the model's run is the continuation of a run from a
   description d1 of the current state *)
Definition xinv4 (m: nat) (j p lo: Z) (l: list Z) : Prop :=
  forall dx, xb_rel s pos0 lo0 dx -> exists d1 f, xb_rel s p lo d1 /\ k - (j + Z.of_nat m) < 4 * Z.of_nat f /\
    xh_x1_stream t s dx k =
    (let '(l4, d4) := xh_x1_n t d1 m in x1_fin (xh_x1_loop4 f s t d4 (k - j - Z.of_nat m) (l ++ l4))).

(* after the 4-symbol loop: the remaining k - j symbols without reload *)
Definition xinv3 (j p lo: Z) (l: list Z) : Prop :=
  forall dx, xb_rel s pos0 lo0 dx -> exists d1, xb_rel s p lo d1 /\
    xh_x1_stream t s dx k = (let '(b, d') := xh_x1_n t d1 (Z.to_nat (k - j)) in (l ++ b, d')).

Lemma xinv4_init : 3 < k -> xinv4 0 0 pos0 lo0 [].
Proof.
  intros Hk dx Hdx. exists dx, (Z.to_nat k + 1)%nat. split; [exact Hdx|]. split; [lia|].
  unfold xh_x1_stream. rewrite (proj2 (Z.ltb_lt 3 k) Hk). cbn [xh_x1_n app].
  replace (k - 0 - Z.of_nat 0) with k by lia. unfold x1_fin.
  destruct (xh_x1_loop4 _ s t dx k []) as [[a d] rem]. reflexivity.
Qed.

(* the loop test, reload unfinished and more than 3 left: a new body of 4 symbols *)
Lemma xinv4_reload_cont (j p lo: Z) (l: list Z) :
  xinv4 0 j p lo l -> bit_inv s p lo -> fst (bs_reload p lo) = 0 -> 3 < k - j ->
  xinv4 4 j p (snd (bs_reload p lo)) l.
Proof.
  intros X Hi Hst Hkj dx Hdx. destruct (X dx Hdx) as (d1 & f & Hd1 & Hf & E).
  destruct (xb_reload_rel s p lo d1 Hi Hd1) as [Hr1 Hr2].
  destruct f as [|f]; [lia|].
  exists (snd (xb_reload s d1)), f. split; [exact Hr2|]. split; [lia|].
  rewrite E. replace (xh_x1_n t d1 0) with (@nil Z, d1) by reflexivity. cbv iota beta.
  rewrite app_nil_r. replace (k - j - Z.of_nat 0) with (k - j) by lia.
  cbn [xh_x1_loop4]. destruct (xb_reload s d1) as [st d1'] eqn:Er. cbn [fst snd] in *.
  replace (st =? XB_unfinished) with true by (subst st; rewrite Hst; reflexivity).
  rewrite (proj2 (Z.ltb_lt 3 (k - j)) Hkj). cbn [andb].
  replace (k - j - Z.of_nat 4) with (k - j - 4) by lia.
  destruct (xh_x1_n t d1' 4) as [l4 d4]. reflexivity.
Qed.

(* the loop test fails: the loop ends, the tail decodes the rest *)
Lemma xinv4_exit (j p lo: Z) (l: list Z) :
  xinv4 0 j p lo l -> bit_inv s p lo -> (fst (bs_reload p lo) <> 0 \/ k - j <= 3) -> 0 <= k - j ->
  xinv3 j p (snd (bs_reload p lo)) l.
Proof.
  intros X Hi Hc Hkj dx Hdx. destruct (X dx Hdx) as (d1 & f & Hd1 & Hf & E).
  destruct (xb_reload_rel s p lo d1 Hi Hd1) as [Hr1 Hr2].
  destruct f as [|f]; [lia|].
  exists (snd (xb_reload s d1)). split; [exact Hr2|].
  rewrite E. replace (xh_x1_n t d1 0) with (@nil Z, d1) by reflexivity. cbv iota beta.
  rewrite app_nil_r. replace (k - j - Z.of_nat 0) with (k - j) by lia.
  cbn [xh_x1_loop4]. destruct (xb_reload s d1) as [st d1'] eqn:Er. cbn [fst snd] in *.
  rewrite Hr1. replace (andb (fst (bs_reload p lo) =? XB_unfinished) (3 <? k - j)) with false.
  2: { unfold XB_unfinished. destruct Hc as [Hc|Hc].
       - rewrite (proj2 (Z.eqb_neq _ _) Hc). reflexivity.
       - rewrite (proj2 (Z.ltb_ge 3 (k - j)) Hc). destruct (_ =? 0); reflexivity. }
  unfold x1_fin. destruct (xh_x1_n t d1' (Z.to_nat (k - j))) as [b d']. reflexivity.
Qed.

(* k <= 3: one reload, then the k symbols *)
Lemma xinv3_init : k <= 3 -> bit_inv s pos0 lo0 -> xinv3 0 pos0 (snd (bs_reload pos0 lo0)) [].
Proof.
  intros Hk Hi dx Hdx. destruct (xb_reload_rel s pos0 lo0 dx Hi Hdx) as [_ Hr2].
  exists (snd (xb_reload s dx)). split; [exact Hr2|].
  unfold xh_x1_stream. rewrite (proj2 (Z.ltb_ge 3 k) Hk). rewrite Z.sub_0_r.
  destruct (xb_reload s dx) as [st d1]. cbn [snd]. destruct (xh_x1_n t d1 (Z.to_nat k)). reflexivity.
Qed.

(* one symbol inside a body *)
Lemma xinv4_step (m: nat) (j p lo: Z) (l: list Z) (c nb: Z) :
  xinv4 (S m) j p lo l ->
  (forall d, xb_rel s p lo d -> xh_x1_sym t d = (c, xb_skip d nb)) ->
  0 <= nb -> 0 <= lo + 64 - (p - nb) <= Int.max_unsigned ->
  xinv4 m (j + 1) (p - nb) lo (l ++ [c]).
Proof.
  intros X Hsym Hnb Hb dx Hdx. destruct (X dx Hdx) as (d1 & f & Hd1 & Hf & E).
  exists (xb_skip d1 nb), f. split; [apply xb_skip_rel; auto|]. split; [lia|].
  rewrite E. cbn [xh_x1_n]. rewrite (Hsym d1 Hd1).
  destruct (xh_x1_n t (xb_skip d1 nb) m) as [l' d'']. rewrite <- app_assoc. cbn [app].
  replace (k - j - Z.of_nat (S m)) with (k - (j + 1) - Z.of_nat m) by lia. reflexivity.
Qed.

(* one symbol of the tail *)
Lemma xinv3_step (j p lo: Z) (l: list Z) (c nb: Z) :
  xinv3 j p lo l -> j < k ->
  (forall d, xb_rel s p lo d -> xh_x1_sym t d = (c, xb_skip d nb)) ->
  0 <= nb -> 0 <= lo + 64 - (p - nb) <= Int.max_unsigned ->
  xinv3 (j + 1) (p - nb) lo (l ++ [c]).
Proof.
  intros X Hj Hsym Hnb Hb dx Hdx. destruct (X dx Hdx) as (d1 & Hd1 & E).
  exists (xb_skip d1 nb). split; [apply xb_skip_rel; auto|].
  rewrite E. replace (Z.to_nat (k - j)) with (S (Z.to_nat (k - (j + 1)))) by lia.
  cbn [xh_x1_n]. rewrite (Hsym d1 Hd1).
  destruct (xh_x1_n t (xb_skip d1 nb) (Z.to_nat (k - (j + 1)))) as [l' d'']. rewrite <- app_assoc. reflexivity.
Qed.

Lemma xinv3_end (p lo: Z) (l: list Z) :
  xinv3 k p lo l -> forall dx, xb_rel s pos0 lo0 dx ->
  fst (xh_x1_stream t s dx k) = l /\ xb_rel s p lo (snd (xh_x1_stream t s dx k)).
Proof.
  intros X dx Hdx. destruct (X dx Hdx) as (d1 & Hd1 & E). rewrite E, Z.sub_diag. cbn [xh_x1_n Z.to_nat].
  rewrite app_nil_r. auto.
Qed.

End Exact.

Lemma upd_out (oc: list val) (a j c: Z) (l: list Z) :
  0 <= a -> Zlength l = j -> 0 <= j -> a + j < Zlength oc ->
  upd_Znth (a + j) (sublist 0 a oc ++ zbytes l ++ sublist (a + j) (Zlength oc) oc) (Vint (Int.repr c)) =
  sublist 0 a oc ++ zbytes (l ++ [c]) ++ sublist (a + (j + 1)) (Zlength oc) oc.
Proof. intros. rewrite map_app. simpl. list_solve. Qed.

Lemma sub_pp_uchar (ob: val) (a k: Z) :
  isptr ob -> 0 <= k <= Ptrofs.max_unsigned ->
  sem_sub_pp tuchar (offset_val (a + k) ob) (offset_val a ob) = Some (Vlong (Int64.repr k)).
Proof.
  destruct ob; try contradiction; intros _ Hk. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  replace (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr (a + k))) (Ptrofs.add i (Ptrofs.repr a))) with (Ptrofs.repr k).
  2: { rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted, ptrofs_sub_repr. f_equal; lia. }
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs, Ptrofs.to_int64. simpl. rewrite Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

Lemma sameblock_off (ob: val) (x y: Z) : isptr ob -> is_true (sameblock (offset_val x ob) (offset_val y ob)).
Proof. destruct ob; try contradiction; intros _. simpl. destruct (peq b b); [reflexivity|congruence]. Qed.

Lemma sub_pi_uchar (b: block) (o: ptrofs) (x: Z) :
  sem_sub_pi tuchar Signed (offset_val x (Vptr b o)) (Vint (Int.repr 3)) = Some (offset_val (x - 3) (Vptr b o)).
Proof.
  unfold sem_sub_pi. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  rewrite <- ptrofs_sub_repr, Ptrofs.sub_add_opp. reflexivity.
Qed.

Lemma cmp_lt_off (b: block) (o: ptrofs) (n x y: Z) :
  Ptrofs.unsigned o + n < Ptrofs.modulus -> 0 <= x <= n -> 0 <= y <= n ->
  sem_cmp_pp Clt (offset_val x (Vptr b o)) (offset_val y (Vptr b o)) = Some (bool2val (x <? y)).
Proof.
  intros Hm Hx Hy. pose proof (Ptrofs.unsigned_range o).
  unfold sem_cmp_pp. simpl. rewrite if_true by auto. simpl. f_equal. f_equal.
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned, !(Ptrofs.unsigned_repr x), !(Ptrofs.unsigned_repr y) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (Z.ltb_spec x y); auto; lia.
Qed.

Lemma out_wvp (sh: share) (n: Z) (cc: list val) (b: block) (o: ptrofs) (i: Z) :
  writable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) cc (Vptr b o) |-- weak_valid_pointer (offset_val i (Vptr b o)).
Proof.
  intros. sep_apply data_at_memory_block. simpl sizeof.
  apply memory_block_weak_valid_pointer; [lia | lia | auto].
Qed.

Lemma tc_order_out (sh: share) (n: Z) (cc: list val) (b: block) (o: ptrofs) (i m: Z) (R: mpred) :
  writable_share sh -> 0 <= i <= n -> 0 <= m <= n -> 0 < n ->
  R * data_at sh (tarray tuchar n) cc (Vptr b o) |--
  denote_tc_test_order (offset_val i (Vptr b o)) (offset_val m (Vptr b o)).
Proof.
  intros. rewrite isptr_denote_tc_test_order by exact I. unfold test_order_ptrs.
  simpl sameblock. destruct (peq b b); [|congruence]. simpl. apply andp_right; apply sepcon_weak_valid_pointer2; apply out_wvp; auto.
Qed.

Lemma and_true (x y: bool) :
  typed_true tint (force_val (sem_and tint tint (bool2val x) (bool2val y))) -> x = true /\ y = true.
Proof. destruct x, y; compute; intuition congruence. Qed.

Lemma and_false (x y: bool) :
  typed_false tint (force_val (sem_and tint tint (bool2val x) (bool2val y))) -> x = false \/ y = false.
Proof. destruct x, y; compute; intuition congruence. Qed.

Lemma semax_dowhile0 {CS: compspecs} {Espec: OracleKind} Delta P c R :
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
  intros H. eapply semax_loop; [exact H|]. destruct R.
  match goal with |- semax ?D _ _ ?Q => exact (semax_break D Q) end.
Qed.

Lemma int_eq_st (st: Z) : 0 <= st <= 3 -> Int.eq (Int.repr st) (Int.repr 0) = (st =? 0).
Proof. intros. assert (st = 0 \/ st = 1 \/ st = 2 \/ st = 3) as [-> | [-> | [-> | ->]]] by lia; reflexivity. Qed.

Lemma bs_reload_st (pos lo: Z) : 0 <= fst (bs_reload pos lo) <= 3.
Proof.
  unfold bs_reload, BIT_unfinished, BIT_endOfBuffer, BIT_completed, BIT_overflow.
  destruct (pos <? lo); [simpl; lia|]. destruct (8 <=? lo / 8); [simpl; lia|].
  destruct (lo / 8 =? 0); [destruct (0 <? pos); simpl; lia|]. destruct (lo / 8 <? _); simpl; lia.
Qed.

(* the state between two decodes: j bytes written, the stream at (pos1, lo1) *)
Definition dstate (sh: share) (gv: globals) (s: list Z) (start bD: val) (shs: share) (bp: val) (buf: list Z)
    (sht: share) (dt: val) (ht: huf_table) (L: Z) (sho: share) (ob: val) (oc: list val) (a k B: Z)
    (P: Z -> Z -> Z -> list Z -> Prop) : environ -> mpred :=
  (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z,
    PROP (0 <= j <= k; Zlength l = j; bytes_ok l; lo1 + 64 - pos1 <= B + 12 * j; P j pos1 lo1 l)
    LOCAL (temp _pStart (offset_val a ob); gvars gv; temp _p (offset_val (a + j) ob); temp _bitDPtr bD;
           temp _pEnd (offset_val (a + k) ob); temp _dt dt; temp _dtLog (Vint (Int.repr L)))
    SEP (BIT_DStream_rep sh gv s start pos1 lo1 bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) dt;
         data_at sho (tarray tuchar (Zlength oc)) (sublist 0 a oc ++ zbytes l ++ sublist (a + j) (Zlength oc) oc) ob))%assert.

Lemma fa_uchar (n: Z) (ob: val) (i: Z) :
  field_compatible (tarray tuchar n) [] ob -> 0 <= i < n ->
  offset_val i ob = field_address (tarray tuchar n) [ArraySubsc i] ob.
Proof.
  intros Hf Hi. unfold field_address. rewrite if_true.
  - simpl. f_equal. lia.
  - apply field_compatible_cons; simpl; split; [lia | auto].
Qed.

Lemma add_pi_uchar (ob: val) (x: Z) :
  isptr ob ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint (offset_val x ob) (Vint (Int.repr 1))) =
  offset_val (x + 1) ob.
Proof.
  destruct ob; try contradiction; intros _. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite ptrofs_mul_repr, ptrofs_add_repr. reflexivity.
Qed.

Lemma zext8 (c: Z) : 0 <= c < 256 -> Int.zero_ext 8 (Int.repr c) = Int.repr c.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

(* forward_if without the typecheck entailer (left as the first goal) *)
Ltac my_if :=
  repeat apply -> semax_seq_skip;
  repeat (apply seq_assoc1; try apply -> semax_seq_skip);
  hoist_later_in_pre;
  try lazymatch goal with |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ => apply semax_if_seq end;
  lazymatch goal with
  | |- @semax ?CS _ ?Delta (|> ?Pre) (Sifthenelse ?e ?c1 ?c2) _ =>
    let HRE := fresh "H" in let v := fresh "v" in
    do_compute_expr1 CS Delta Pre e;
    match goal with v' := _, H:_ |- _ => rename H into HRE; rename v' into v end;
    apply (semax_ifthenelse_PQR' _ v);
     [ reflexivity | idtac | assumption
     | simpl in v; clear HRE; subst v; apply semax_extract_PROP; intro Hcond;
       repeat (apply semax_extract_PROP; intro);
       repeat apply -> semax_skip_seq; abbreviate_semax
     | simpl in v; clear HRE; subst v; apply semax_extract_PROP; intro Hcond;
       repeat (apply semax_extract_PROP; intro);
       repeat apply -> semax_skip_seq; abbreviate_semax ]
  end.

Ltac close_ds J P1 LO L :=
  unfold dstate; Exists J P1 LO L; go_lower;
  apply andp_right;
  [ apply prop_right; cbv beta;
    refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
    [ | | | | | repeat split; try reflexivity; try (f_equal; lia) ]
  | ].

Ltac ds_intros J P1 LO L Hj Hl Hby Hbd HP :=
  unfold dstate; Intros J P1 LO L;
  match goal with H: _ |- _ => rename H into HP end;
  match goal with H: 0 <= J <= _ |- _ => rename H into Hj end;
  match goal with H: Zlength L = J |- _ => rename H into Hl end;
  match goal with H: bytes_ok L |- _ => rename H into Hby end;
  match goal with H: LO + 64 - P1 <= _ |- _ => rename H into Hbd end.

Ltac eq_elim X := match goal with H: X = _ |- _ => rewrite H in *; clear H; clear X end.

Ltac binv S P LO H :=
  assert_PROP (bit_inv S P LO) as H by (go_lower; sep_apply bit_rep_inv; Intros; apply prop_right; auto).

(* one HUF_DECODE_SYMBOLX1_0 body at state (p, lo): leaves the entailment to the post *)
Ltac dec_tac P LO :=
  forward; forward;
  match goal with |- context [BIT_DStream_rep ?sh ?gv ?s ?start _ _ ?bD] =>
  match goal with |- context [data_at ?sht (tarray t_deltx1 (2 ^ ?L)) (x1_cells ?ht ?L) ?dt] =>
    forward_call (sh, bD, gv, s, start, P, LO, sht, dt, ht, L, false); [ unfold BIT_DStream_rep_g; cancel | .. ]
  end end.

(* the whole decode-and-store at (J, P0, LO0, L0); leaves the validity part of the post *)
Ltac dec_core a ob oc ht L Hht J P0 LO0 L0 :=
  let Hbi := fresh "Hbi" in
  assert_PROP (P0 <= LO0 + 64) as Hbi
    by (go_lower; sep_apply bit_rep_inv; Intros; apply prop_right;
        match goal with H: bit_inv _ _ _ |- _ => destruct H as (_ & _ & _ & _ & _ & ? & _); lia end);
  dec_tac P0 LO0; [ unfold HUF_TABLELOG_MAX in *; lia | ];
  let v := fresh "v" in Intros v; unfold BIT_DStream_rep_g;
  let Hv := fresh "Hv" in let Hex := fresh "Hex" in
  match goal with H: 0 <= v < 2 ^ _ |- _ => rename H into Hv end;
  match goal with H: _ -> v = bs_peek _ _ _ |- _ => rename H into Hex end;
  (* the exact symbol, kept as the model's step (the equation on v itself would be substituted away) *)
  let Hsy := fresh "Hsy" in
  match goal with H: v = xb_look_fast _ _, HL: x1_log_is _ _ |- _ =>
    pose proof (x1_sym_of _ _ _ _ _ _ HL Hv H) as Hsy; clear H end;
  assert_PROP (offset_val (a + J) ob = field_address (tarray tuchar (Zlength oc)) [ArraySubsc (a + J)] ob)
    by (go_lower; apply prop_right; apply fa_uchar; auto; lia);
  forward;
  let Hc := fresh "Hc" in let Hnb := fresh "Hnb" in
  destruct (hsym_range ht L v Hht ltac:(lia) Hv) as [Hc Hnb];
  rewrite add_pi_uchar by auto; rewrite zext8 by lia; rewrite upd_out by lia;
  close_ds (J + 1) (P0 - snd (hsym ht L v)) LO0 (L0 ++ [fst (hsym ht L v)]);
  [ lia | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia
  | apply Forall_app; split; [auto | repeat constructor; unfold is_byte; lia]
  | unfold HUF_TABLELOG_MAX in *; lia | | cancel ].

(* a validity step of phase 1: the peek is exact (the window holds >= 21 bits) *)
(* an exact step inside a body *)
Ltac x4_step X := eapply xinv4_step; [exact X | eassumption | lia | unfold HUF_TABLELOG_MAX in *; lia].

Ltac v1_step VS V Hex :=
  let Hvv := fresh "Hvv" in let Hg := fresh "Hg" in let Hb := fresh "Hb" in
  intros Hvv; destruct (V Hvv) as [Hg Hb]; split;
  [ apply VS; [lia | exact Hg | intros _; apply Hex; left; unfold HUF_TABLELOG_MAX in *; lia]
  | unfold HUF_TABLELOG_MAX in *; lia ].


Lemma body_HUF_decodeStreamX1 :
  semax_body Vprog G_stream f_HUF_decodeStreamX1 HUF_decodeStreamX1_spec.
Proof.
  start_function.
  rename H7 into HLx. assert (HLt: x1_log_is ht L) by exact HLx. clear HLx.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as Hfc by entailer!.
  assert_PROP (bit_inv s pos lo) as Hinv by (sep_apply bit_rep_inv; entailer!).
  assert (Hob: isptr ob) by (destruct Hfc; auto).
  assert (exists b o, ob = Vptr b o) as (b & o & Eob) by (destruct ob; try contradiction; eauto).
  assert_PROP (Ptrofs.unsigned o + Zlength oc < Ptrofs.modulus) as Hmod.
  { sep_apply (data_at_memory_block sho (tarray tuchar (Zlength oc)) oc ob). simpl sizeof.
    sep_apply memory_block_local_facts. Intros. apply prop_right. subst ob. simpl in *. lia. }
  pose proof Hinv as Hinv0.
  destruct Hinv as (Hsb & Hs1 & Hlo0 & Hlo8 & Hlos & Hpl & Hbc).
  assert (Hk: 12 * k <= Int.max_unsigned) by lia.
  forward.
  forward_if (dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
    (fun j p1 lo1 l => xinv3 ht s pos lo k j p1 lo1 l /\
       (lo <= pos -> vgood ht s k pos j p1 l /\ (lo1 = 0 \/ lo1 + 21 + 12 * (k - j) <= p1)))).
  { apply prop_right. apply sameblock_off; auto. }
  { (* phase 1: four symbols per reload *)
    rewrite sub_pp_uchar in H7 by (auto; rep_lia). simpl in H7.
    assert (Hk3: 3 < k). { unfold Int64.lt in H7. rewrite Int.signed_repr, !Int64.signed_repr in H7 by rep_lia.
      destruct (zlt 3 k); [lia | discriminate]. }
    clear H7.
    forward_loop (dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
      (fun j p1 lo1 l => xinv4 ht s pos lo k 0 j p1 lo1 l /\ (lo <= pos -> vgood ht s k pos j p1 l /\ lo1 <= p1)))
      break: (dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
      (fun j p1 lo1 l => xinv3 ht s pos lo k j p1 lo1 l /\
       (lo <= pos -> vgood ht s k pos j p1 l /\ (lo1 = 0 \/ lo1 + 21 + 12 * (k - j) <= p1)))).
    { close_ds 0 pos lo (@nil Z);
        [lia | reflexivity | constructor | lia | split; [apply xinv4_init; lia | intros Hv; split; [apply vgood_0 | lia]] |].
      rewrite Z.add_0_r. simpl (zbytes []). rewrite app_nil_l, sublist_rejoin, sublist_same by lia. cancel. }
    ds_intros j pos1 lo1 l Hj Hl Hby Hbd HP.
    match goal with H: xinv4 _ _ _ _ _ _ j _ _ _ |- _ => rename H into X end.
    binv s pos1 lo1 Hinv1. pose proof Hinv1 as Hinv1c. destruct Hinv1 as (_ & _ & Hlo10 & Hlo18 & _ & Hpl1 & Hbc1).
    forward_call (sh, bD, gv, s, start, pos1, lo1, shs, bp, buf, off).
    destruct (bs_reload_facts pos1 lo1 Hlo10 Hlo18 Hpl1) as [Hr1 Hr2].
    pose proof (xinv4_reload_cont ht s pos lo k j pos1 lo1 l X Hinv1c) as HXc.
    pose proof (xinv4_exit ht s pos lo k j pos1 lo1 l X Hinv1c) as HXe. clear X.
    pose proof (bs_reload_st pos1 lo1) as Hst0.
    forget (bs_reload pos1 lo1) as R. destruct R as [st lo2]. cbn [fst snd] in *.
    my_if.
    { go_lower. rewrite Eob, sub_pi_uchar. simpl force_val. apply andp_right; [|apply prop_right; exact I].
      rewrite <- !sepcon_assoc. apply tc_order_out; auto; lia. }
    { rewrite Eob, sub_pi_uchar in Hcond. cbn [force_val typeof] in Hcond.
      rewrite (cmp_lt_off b o (Zlength oc)) in Hcond by lia. apply and_true in Hcond.
      destruct Hcond as [Hst Hjk]. rewrite int_eq_st in Hst by lia. apply Z.eqb_eq in Hst. apply Z.ltb_lt in Hjk.
      subst st. try rewrite <- Eob.
      pose proof (HXc eq_refl ltac:(lia)) as X0. clear HXc HXe.
      assert (V0: lo <= pos -> vgood ht s k pos j pos1 l /\ lo2 + 57 <= pos1 + 12 * 0).
      { intros Hv; destruct (HP Hv) as [Hg Hle]; split; auto; destruct (Hr2 Hle) as [Hu _]; specialize (Hu eq_refl); lia. }
      clear HP Hr2.
      (* symbol 1 *)
      apply -> seq_assoc.
      eapply semax_seq with (Q := dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
        (fun j' p' lo' l' => j' = j + 1 /\ lo' = lo2 /\ xinv4 ht s pos lo k 3 j' p' lo' l' /\ (lo <= pos -> vgood ht s k pos j' p' l' /\ lo2 + 57 <= p' + 12 * 1))).
      { apply semax_dowhile0. forward_call tt. my_if.
        3: { unfold typed_false in Hcond. simpl in Hcond. discriminate. }
        { go_lower; apply prop_right; auto. }
        clear Hcond. apply semax_dowhile0. dec_core a ob oc ht L H0 j pos1 lo2 l.
        split; [lia|]. split; [auto|]. split; [x4_step X0 | v1_step (vstep' ht s L H0 H1 Hsb k pos) V0 Hex]. }
      ds_intros j1 p1 lo3 l1 Hj1 Hl1 Hby1 Hbd1 HP1. eq_elim j1. eq_elim lo3. rename HP1 into V1.
      match goal with H: xinv4 _ _ _ _ _ _ _ _ _ _ |- _ => rename H into X1 end.
      (* symbol 2 *)
      apply -> seq_assoc.
      eapply semax_seq with (Q := dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
        (fun j' p' lo' l' => j' = j + 2 /\ lo' = lo2 /\ xinv4 ht s pos lo k 2 j' p' lo' l' /\ (lo <= pos -> vgood ht s k pos j' p' l' /\ lo2 + 57 <= p' + 12 * 2))).
      { apply semax_dowhile0. forward_call tt. my_if.
        3: { unfold typed_false in Hcond. simpl in Hcond. discriminate. }
        { go_lower; apply prop_right; auto. }
        clear Hcond. forward. my_if.
        3: { unfold typed_false in Hcond. simpl in Hcond. discriminate. }
        { go_lower; apply prop_right; auto. }
        clear Hcond. apply semax_dowhile0. dec_core a ob oc ht L H0 (j + 1) p1 lo2 l1.
        split; [lia|]. split; [auto|]. split; [x4_step X1 | v1_step (vstep' ht s L H0 H1 Hsb k pos) V1 Hex]. }
      ds_intros j2 p2 lo4 l2 Hj2 Hl2 Hby2 Hbd2 HP2. eq_elim j2. eq_elim lo4. rename HP2 into V2.
      match goal with H: xinv4 _ _ _ _ _ _ _ _ _ _ |- _ => rename H into X2 end.
      (* symbol 3 *)
      apply -> seq_assoc.
      eapply semax_seq with (Q := dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
        (fun j' p' lo' l' => j' = j + 3 /\ lo' = lo2 /\ xinv4 ht s pos lo k 1 j' p' lo' l' /\ (lo <= pos -> vgood ht s k pos j' p' l' /\ lo2 + 57 <= p' + 12 * 3))).
      { apply semax_dowhile0. forward_call tt. my_if.
        3: { unfold typed_false in Hcond. simpl in Hcond. discriminate. }
        { go_lower; apply prop_right; auto. }
        clear Hcond. apply semax_dowhile0. dec_core a ob oc ht L H0 (j + 2) p2 lo2 l2.
        split; [lia|]. split; [auto|]. split; [x4_step X2 | v1_step (vstep' ht s L H0 H1 Hsb k pos) V2 Hex]. }
      ds_intros j3 p3 lo5 l3 Hj3 Hl3 Hby3 Hbd3 HP3. eq_elim j3. eq_elim lo5. rename HP3 into V3.
      match goal with H: xinv4 _ _ _ _ _ _ _ _ _ _ |- _ => rename H into X3 end.
      (* symbol 4, back to the loop head *)
      unfold MORE_COMMANDS, abbreviate. apply -> semax_seq_skip. apply semax_dowhile0. dec_core a ob oc ht L H0 (j + 3) p3 lo2 l3.
      split; [x4_step X3 | v1_step (vstep' ht s L H0 H1 Hsb k pos) V3 Hex]. }
    { rewrite Eob, sub_pi_uchar in Hcond. cbn [force_val typeof] in Hcond.
      rewrite (cmp_lt_off b o (Zlength oc)) in Hcond by lia. apply and_false in Hcond.
      rewrite int_eq_st in Hcond by lia. try rewrite <- Eob.
      forward.
      close_ds j pos1 lo2 l; [lia | auto | auto | lia | |].
      { split.
        { apply HXe; [| lia]. destruct Hcond as [Hc|Hc]; [left; apply Z.eqb_neq; exact Hc|].
          right. apply Z.ltb_ge in Hc. lia. }
        intros Hv. destruct (HP Hv) as [Hg Hle]. split; [exact Hg|].
        destruct (Hr2 Hle) as [Hu Hn]. unfold BIT_unfinished in *.
        destruct (Z.eq_dec st 0) as [E|E]; [|left; auto].
        right. specialize (Hu E). destruct Hcond as [Hc|Hc]; [apply Z.eqb_neq in Hc; contradiction|].
        apply Z.ltb_ge in Hc. lia. }
      cancel. } }
  { (* k <= 3 *)
    rewrite sub_pp_uchar in H7 by (auto; rep_lia). simpl in H7.
    assert (Hk3: k <= 3). { unfold Int64.lt in H7. rewrite Int.signed_repr, !Int64.signed_repr in H7 by rep_lia.
      destruct (zlt 3 k); [discriminate | lia]. }
    clear H7.
    forward_call (sh, bD, gv, s, start, pos, lo, shs, bp, buf, off).
    destruct (bs_reload_facts pos lo Hlo0 Hlo8 Hpl) as [Hr1 Hr2].
    pose proof (xinv3_init ht s pos lo k Hk3 Hinv0) as X0.
    forget (bs_reload pos lo) as R.
    close_ds 0 pos (snd R) (@nil Z); [lia | reflexivity | constructor | lia | |].
    { split; [exact X0|]. intros Hv. split; [apply vgood_0|].
      destruct (Hr2 Hv) as [Hu Hn].
      destruct (Z.eq_dec (fst R) BIT_unfinished) as [E|E]; [specialize (Hu E); right; lia | left; auto]. }
    rewrite Z.add_0_r. simpl (zbytes []). rewrite app_nil_l, sublist_rejoin, sublist_same by lia. cancel. }
  (* the MEM_32bits loop is dead *)
  ds_intros j pos1 lo1 l Hj Hl Hby Hbd HP.
  forward_call tt.
  my_if.
  { go_lower; apply prop_right; auto. }
  { unfold typed_true in Hcond. simpl in Hcond. discriminate. }
  clear Hcond.
  (* phase 3: the remaining symbols *)
  forward_loop (dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
    (fun j p1 lo1 l => xinv3 ht s pos lo k j p1 lo1 l /\
       (lo <= pos -> vgood ht s k pos j p1 l /\ (lo1 = 0 \/ lo1 + 21 + 12 * (k - j) <= p1))))
    break: (dstate sh gv s start bD shs bp buf sht dt ht L sho ob oc a k (lo + 64 - pos)
    (fun j p1 lo1 l => j = k /\ xinv3 ht s pos lo k j p1 lo1 l /\
       (lo <= pos -> vgood ht s k pos j p1 l /\ (lo1 = 0 \/ lo1 + 21 + 12 * (k - j) <= p1)))).
  { close_ds j pos1 lo1 l; [lia | auto | auto | lia | split; assumption | cancel]. }
  ds_intros j3 p3 lo3 l3 Hj3 Hl3 Hby3 Hbd3 HP3.
  match goal with H: xinv3 _ _ _ _ _ j3 _ _ _ |- _ => rename H into X3h end.
  my_if.
  { go_lower. rewrite Eob. rewrite <- !sepcon_assoc. apply tc_order_out; auto; lia. }
  { cbn [typeof] in Hcond. rewrite Eob, (cmp_lt_off b o (Zlength oc)) in Hcond by lia. simpl force_val in Hcond.
    destruct (Z.ltb_spec (a + j3) (a + k)) as [Hjk|Hjk]; [|compute in Hcond; discriminate]. clear Hcond.
    apply semax_dowhile0. dec_core a ob oc ht L H0 j3 p3 lo3 l3.
    split; [eapply xinv3_step; [exact X3h | lia | eassumption | lia | unfold HUF_TABLELOG_MAX in *; lia] |].
    intros Hvv. destruct (HP3 Hvv) as [Hg Hb]. split.
    - apply (vstep' ht s L H0 H1 Hsb k pos); [lia | exact Hg |].
      intros Hp. apply Hex. destruct Hb as [Hb|Hb]; [right; split; auto | left; unfold HUF_TABLELOG_MAX in *; lia].
    - destruct Hb as [Hb|Hb]; [left; auto | right; unfold HUF_TABLELOG_MAX in *; lia]. }
  { cbn [typeof] in Hcond. rewrite Eob, (cmp_lt_off b o (Zlength oc)) in Hcond by lia. simpl force_val in Hcond.
    destruct (Z.ltb_spec (a + j3) (a + k)) as [Hjk|Hjk]; [compute in Hcond; discriminate|]. clear Hcond.
    forward.
    close_ds j3 p3 lo3 l3; [lia | auto | auto | lia | split; [lia | split; [exact X3h | auto]] | cancel]. }
  ds_intros jf pf lof lf Hjf Hlf Hbyf Hbdf HPf.
  binv s pf lof Hif.
  forward.
  { apply prop_right. apply sameblock_off. exact I. }
  Exists pf lof lf.
  apply andp_right; [apply prop_right | cancel].
  destruct Hif as (_ & _ & Hlof & _).
  split; [reflexivity|]. split; [auto|]. split; [lia|]. split.
  - intros Hv l' Hm. destruct (HPf Hv) as [Hg Hb].
    rewrite <- (Nat2Z.id (length lf)), <- Zlength_correct in Hm.
    eapply vgood_end in Hg; [|exact Hm]. destruct Hg as [-> ->]. split; [auto|]. split; [auto|]. lia.
  - split; [match goal with H: xinv3 _ _ _ _ _ _ pf lof lf |- _ => exact (xinv3_end _ _ _ _ _ _ _ _ H) end|].
    rewrite sub_pp_uchar by (try exact I; rep_lia). reflexivity.
Qed.
