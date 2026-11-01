(* X1D: the body of HUF_decompress4X1_usingDTable_internal_body against the byte_cells spec (HufX1DSpecsBC.v, contract item 17). *)
Require Export Zstd.proof.dec.B.huf.HufX1DSpecsBC.
Require Export Zstd.proof.dec.B.huf.HufX1D4X.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* ---------- model lemmas ---------- *)

(* one stream of the 4: well formed, decodes to exactly the k symbols q, ending at position 0 *)
Definition x1_stream_ok (ht: huf_table) (si: list Z) (k: Z) (q: list Z) : Prop :=
  bs_wf si = true /\ Zlength q = k /\ bytes_ok q /\
  huf_decode_syms ht si (Z.to_nat k) (bs_total si) = Some (q, 0).

Lemma huf4s_slice_sublist (b: list Z) (i k: Z) :
  0 <= i -> 0 <= k -> slice b i k = sublist i (i + k) b.
Proof.
  intros. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma huf4s_le_value_nonneg (l: list Z) : bytes_ok l -> 0 <= le_value l.
Proof.
  induction l as [|a l IH]; cbn [le_value]; intros H; [lia|].
  apply Forall_cons_iff in H as [Ha Hl]. unfold is_byte in Ha. specialize (IH Hl). lia.
Qed.

Lemma huf4s_le_field_nonneg (s: list Z) (i k: Z) : bytes_ok s -> 0 <= le_field s i k.
Proof.
  intros H. unfold le_field, slice. apply huf4s_le_value_nonneg.
  apply Forall_firstn, Forall_skipn, H.
Qed.

Lemma huf4s_syms (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) (p: Z) :
  huf_ok ht -> huf_decode_syms ht V k pos = Some (q, p) ->
  Zlength q = Z.of_nat k /\ bytes_ok q.
Proof.
  intros Hok. revert pos q p. induction k as [|k IH]; simpl; intros pos q p H.
  - inversion H; subst. split; [reflexivity | constructor].
  - destruct (nth (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0)) as [sy nb] eqn:E.
    destruct (pos - nb <? 0); [discriminate|].
    destruct (huf_decode_syms ht V k (pos - nb)) as [[l p']|] eqn:E2; [|discriminate].
    inversion H; subst. destruct (IH _ _ _ E2) as [IH1 IH2].
    split.
    + rewrite Zlength_cons, IH1. lia.
    + constructor; [|exact IH2].
      destruct Hok as [_ [_ HF]].
      destruct (nth_in_or_default (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0)) as [Hin|Hd].
      * rewrite E in Hin. rewrite Forall_forall in HF. specialize (HF _ Hin). simpl in HF.
        unfold is_byte. lia.
      * rewrite E in Hd. inversion Hd; subst. unfold is_byte. lia.
Qed.

Lemma huf4s_stream (ht: huf_table) (si: list Z) (k: Z) (q: list Z) :
  huf_ok ht -> 0 <= k -> huf_decode_stream ht si k = Some q -> x1_stream_ok ht si k q.
Proof.
  intros Hok Hk H. unfold huf_decode_stream in H.
  destruct (bs_okb si) eqn:Eb; simpl in H; [|discriminate].
  destruct (huf_decode_syms ht si (Z.to_nat k) (bs_total si)) as [[l p]|] eqn:E; [|discriminate].
  destruct p; try discriminate. inversion H; subst.
  destruct (huf4s_syms _ _ _ _ _ _ Hok E) as [H1 H2].
  split; [|split; [|split]]; auto; [| rewrite H1; lia].
  unfold bs_okb in Eb. apply andb_prop in Eb as [Eb1 Eb2]. apply andb_prop in Eb1 as [_ Eb1].
  unfold bs_wf. rewrite Eb2, Bool.andb_true_r. rewrite Zlength_correct.
  destruct (length si); simpl in *; [discriminate|]. reflexivity.
Qed.

(* the model's 4 streams, in the terms of the C: the jump table read by MEM_readLE16 (le_field), the
   windows as sublists, segment seg = (n+3)/4, the last stream n - 3 seg symbols *)
Lemma huf4_split (ht: huf_table) (s: list Z) (n: Z) (l: list Z) :
  huf_ok ht -> bytes_ok s -> 0 <= n -> huf_decode_4streams ht s n = Some l ->
  let l1 := le_field s 0 2 in let l2 := le_field s 2 2 in let l3 := le_field s 4 2 in
  let seg := (n + 3) / 4 in
  10 <= Zlength s /\ 6 + l1 + l2 + l3 + 1 <= Zlength s /\ 3 * seg <= n /\
  exists q1 q2 q3 q4, l = q1 ++ q2 ++ q3 ++ q4 /\
    x1_stream_ok ht (sublist 6 (6 + l1) s) seg q1 /\
    x1_stream_ok ht (sublist (6 + l1) (6 + l1 + l2) s) seg q2 /\
    x1_stream_ok ht (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) seg q3 /\
    x1_stream_ok ht (sublist (6 + l1 + l2 + l3) (Zlength s) s) (n - 3 * seg) q4.
Proof.
  intros Hok Hs Hn H l1 l2 l3 seg.
  pose proof (huf4s_le_field_nonneg s 0 2 Hs) as P1.
  pose proof (huf4s_le_field_nonneg s 2 2 Hs) as P2.
  pose proof (huf4s_le_field_nonneg s 4 2 Hs) as P3.
  fold l1 l2 l3 in P1, P2, P3.
  assert (Hseg: 0 <= seg) by (unfold seg; apply Z.div_pos; lia).
  unfold huf_decode_4streams in H. rewrite <- Zlength_correct in H.
  fold l1 l2 l3 seg in H.
  destruct (Zlength s <? 10) eqn:E1; [discriminate|].
  destruct (Zlength s - 6 - l1 - l2 - l3 <? 1) eqn:E2; [discriminate|].
  destruct (n - 3 * seg <? 0) eqn:E3; [discriminate|].
  apply Z.ltb_ge in E1, E2, E3.
  destruct (huf_decode_stream ht (slice s 6 l1) seg) as [q1|] eqn:D1; [|discriminate].
  destruct (huf_decode_stream ht (slice s (6 + l1) l2) seg) as [q2|] eqn:D2; [|discriminate].
  destruct (huf_decode_stream ht (slice s (6 + l1 + l2) l3) seg) as [q3|] eqn:D3; [|discriminate].
  destruct (huf_decode_stream ht (slice s (6 + l1 + l2 + l3) (Zlength s - 6 - l1 - l2 - l3)) (n - 3 * seg))
    as [q4|] eqn:D4; [|discriminate].
  inversion H; subst.
  rewrite huf4s_slice_sublist in D1, D2, D3, D4 by lia.
  replace (6 + l1 + l2 + l3 + (Zlength s - 6 - l1 - l2 - l3)) with (Zlength s) in D4 by lia.
  split; [lia|]. split; [lia|]. split; [lia|].
  exists q1, q2, q3, q4. split; [reflexivity|].
  split; [|split; [|split]]; apply huf4s_stream; auto; lia.
Qed.

(* the jump table fields are 16-bit *)
Lemma le_field2_range (s: list Z) (i: Z) :
  bytes_ok s -> 0 <= le_field s i 2 < 65536.
Proof.
  intros Hs. unfold le_field, slice.
  assert (Hk: bytes_ok (skipn (Z.to_nat i) s)).
  { unfold bytes_ok in *. revert Hs. generalize (Z.to_nat i). intros k. revert s.
    induction k as [|k IH]; intros s Hs; simpl; [auto|]. destruct s; [constructor|].
    apply IH. inversion Hs; auto. }
  destruct (skipn (Z.to_nat i) s) as [|a [|b r]]; simpl; [lia| |].
  - inversion Hk as [|? ? Ha _]; unfold is_byte in Ha; lia.
  - inversion Hk as [|? ? Ha Hr]; inversion Hr as [|? ? Hb _]; unfold is_byte in Ha, Hb; lia.
Qed.

(* a model run: k symbols (bytes), each of >= 1 bit, positions stay >= 0 *)
Section HX1B.
Local Open Scope Z.

(* the peek of L bits is an L-bit value (any stream, any position) *)
Lemma hx1b_peek_range (V: list Z) (pos L: Z) : 0 <= L -> 0 <= bs_peek_s V pos L < 2 ^ L.
Proof.
  intros HL. unfold bs_peek_s.
  assert (HP: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  destruct (pos <? 0) eqn:E; [lia|]. apply Z.ltb_ge in E.
  destruct (pos - L >=? 0) eqn:E2.
  - apply Z.mod_pos_bound; lia.
  - rewrite Z.geb_leb, Z.leb_gt in E2.
    assert (Hp: 0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (He: 0 < 2 ^ (- (pos - L))) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound (le_value (slice V 0 5)) (2 ^ pos) Hp) as Hm.
    split.
    + apply Z.mul_nonneg_nonneg; lia.
    + replace (2 ^ L) with (2 ^ pos * 2 ^ (- (pos - L))).
      * apply Z.mul_lt_mono_pos_r; lia.
      * rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* the cell a step reads is a real cell of the table *)
Lemma hx1b_cell (ht: huf_table) (V: list Z) (pos: Z) (s nb: Z) :
  huf_ok ht -> nth (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0) = (s, nb) ->
  0 <= s < 256 /\ 1 <= nb <= ht_log ht.
Proof.
  intros (Hlog & Hlen & Hall) Hc.
  pose proof (hx1b_peek_range V pos (ht_log ht) ltac:(lia)) as Hr.
  assert (Hin: In (s, nb) (huf_cells ht)).
  { rewrite <- Hc. apply nth_In. rewrite Zlength_correct in Hlen. lia. }
  rewrite Forall_forall in Hall. apply (Hall _ Hin).
Qed.

End HX1B.

Lemma huf_decode_syms_bounds (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) (p: Z) :
  huf_ok ht -> bytes_ok V -> huf_decode_syms ht V k pos = Some (q, p) ->
  Zlength q = Z.of_nat k /\ bytes_ok q /\ p + Z.of_nat k <= pos /\ ((k > 0)%nat -> 0 <= p).
Proof.
  intros Hht HV. revert pos q p.
  induction k as [|k IH]; intros pos q p H; simpl in H.
  - inversion H; subst. repeat split; try (constructor || lia).
  - destruct (nth (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0)) as [s nb] eqn:Hc.
    pose proof (hx1b_cell ht V pos s nb Hht Hc) as [Hs Hnb].
    destruct (pos - nb <? 0)%Z eqn:E; [discriminate|]. apply Z.ltb_ge in E.
    destruct (huf_decode_syms ht V k (pos - nb)) as [[l p']|] eqn:Hr; [|discriminate].
    inversion H; subst q p; clear H.
    destruct (IH _ _ _ Hr) as (H1 & H2 & H3 & H4).
    split; [rewrite Zlength_cons; lia|].
    split; [constructor; [unfold is_byte; lia | exact H2]|].
    split; [lia|].
    intros _. destruct k as [|k].
    + simpl in Hr. inversion Hr; subst. lia.
    + apply H4. lia.
Qed.

(* one step of a model run seen through the C's exact L-bit peek (HufMPeek.hsym_peek) *)
Lemma huf_decode_syms_step (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) (p L: Z) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok V -> 0 <= pos ->
  huf_decode_syms ht V (S k) pos = Some (q, p) ->
  let c := hsym ht L (bs_peek (bs_value V) pos L) in
  exists q', q = fst c :: q' /\ 0 <= pos - snd c /\ huf_decode_syms ht V k (pos - snd c) = Some (q', p).
Proof.
  intros Hok HL HV Hpos H c. subst c.
  rewrite hsym_peek; [| destruct Hok; lia | lia | auto | lia].
  simpl in H. destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb]. simpl.
  destruct (pos - nb <? 0) eqn:E; [discriminate|].
  destruct (huf_decode_syms ht V k (pos - nb)) as [[l' p']|]; [|discriminate].
  inversion H; subst. exists l'. split; [auto|]. split; [lia|auto].
Qed.

(* bs_wf is part of bs_okb: a stream the model accepts passed BIT_initDStream *)
Lemma bs_okb_wf (s: list Z) : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. rewrite Zlength_correct. intros H.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [_ H1].
  rewrite H2, andb_true_r. destruct s; simpl in *; [discriminate|].
  destruct (Z.of_nat (S (length s)) =? 0) eqn:E; [lia|reflexivity].
Qed.

Local Open Scope Z_scope.

(* ---------- the main loop: per-stream invariants (pure) ----------
   A stream after m iterations of the main loop: w the 4m bytes it wrote, (pos, lo) its state, es the
   endSignal.  bitsConsumed = lo + 64 - pos stays small; while es = 1 the state is not overflowed and
   either 4 decodes stay inside the container (lo + 56 <= pos) or the window is at the bottom (lo = 0).
   Model ghost: if the model decodes the stream into q, the C followed it so far. *)
Definition x4_sinv (ht: huf_table) (si: list Z) (k m: Z) (w: list Z) (pos lo es: Z) : Prop :=
  Zlength w = 4 * m /\ bytes_ok w /\ pos <= lo + 64 /\ lo + 64 - pos <= 112 /\
  (es = 1 -> lo <= pos /\ (lo + 56 <= pos \/ lo = 0)) /\
  (forall q, x1_stream_ok ht si k q -> lo <= pos /\ exists r, q = w ++ r /\
     huf_decode_syms ht si (Z.to_nat (k - 4 * m)) pos = Some (r, 0)).

(* inside an iteration (es = 1, 4m + 4 <= k): t of the 4 decodes done, wt the bytes written *)
Definition x4_mid (ht: huf_table) (si: list Z) (k m t: Z) (wt: list Z) (pos lo: Z) : Prop :=
  Zlength wt = 4 * m + t /\ bytes_ok wt /\ 4 * m + 4 <= k /\ 0 <= t <= 4 /\
  pos <= lo + 64 /\ lo + 64 - pos <= 64 + 12 * t /\ (lo + 56 - 12 * t <= pos \/ lo = 0) /\
  (forall q, x1_stream_ok ht si k q -> exists r, q = wt ++ r /\
     huf_decode_syms ht si (Z.to_nat (k - 4 * m - t)) pos = Some (r, 0)).

(* the last byte of a list of bytes is a byte *)
Lemma x4_last_byte (si: list Z) : bytes_ok si -> si <> [] -> 0 <= last si 0 < 256.
Proof.
  induction si as [|a l IH]; intros H Hne; [congruence|].
  unfold bytes_ok in H. inversion H as [|? ? Ha Hl]; subst.
  destruct l as [|b l']; [simpl; unfold is_byte in Ha; lia|].
  change (last (a :: b :: l') 0) with (last (b :: l') 0). apply IH; [exact Hl|discriminate].
Qed.

(* after BIT_initDStream *)
Lemma x4_sinv_init (ht: huf_table) (si: list Z) (k: Z) :
  bs_wf si = true -> bytes_ok si ->
  x4_sinv ht si k 0 [] (bs_total si) (8 * Z.max 0 (Zlength si - 8)) 1.
Proof.
  intros Hwf Hb.
  unfold bs_wf in Hwf. apply andb_prop in Hwf as [H1 H2].
  apply negb_true_iff, Z.eqb_neq in H1. apply negb_true_iff, Z.eqb_neq in H2.
  assert (Hne: si <> []) by (intro; subst; auto).
  pose proof (x4_last_byte si Hb Hne) as Hl.
  assert (Hh: 0 <= highbit (last si 0) <= 7).
  { unfold highbit. split; [apply Z.log2_nonneg|]. change 7 with (Z.log2 255). apply Z.log2_le_mono. lia. }
  assert (Ht: 8 * (Zlength si - 1) <= bs_total si <= 8 * (Zlength si - 1) + 7).
  { unfold bs_total. rewrite Zlength_correct in *. lia. }
  pose proof (Zlength_nonneg si).
  assert (Hlo: 8 * Z.max 0 (Zlength si - 8) = 0 /\ Zlength si <= 8 \/
               8 * Z.max 0 (Zlength si - 8) = 8 * (Zlength si - 8) /\ 8 < Zlength si).
  { destruct (Z.max_spec 0 (Zlength si - 8)) as [[Ha ->]|[Ha ->]]; lia. }
  unfold x4_sinv. split; [reflexivity|]. split; [unfold bytes_ok; constructor|].
  split; [lia|]. split; [lia|]. split; [intros _; lia|].
  intros q (Hw & Hk & Hq & Hd). split; [lia|]. exists q. split; [reflexivity|].
  replace (k - 4 * 0) with k by lia. exact Hd.
Qed.

(* local copies of proved model facts (HufMPeek.hsym_peek, huf_decode_syms_bounds/step above),
   so that the main-loop lemmas below do not depend on other files' results *)
Lemma x4h_le_value_range (s: list Z) : bytes_ok s -> 0 <= le_value s.
Proof.
  induction s as [|b s IH]; intros H; cbn [le_value]; [lia|].
  inversion H as [|? ? Hb Hs]; subst. unfold is_byte in Hb. specialize (IH Hs). lia.
Qed.

Lemma x4h_le_value_skipn (k: nat) (s: list Z) :
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

Lemma x4h_le_value_firstn (k: nat) (s: list Z) :
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

Lemma x4h_bytes_ok_skipn (k: nat) (s: list Z) : bytes_ok s -> bytes_ok (skipn k s).
Proof.
  revert s; induction k as [|k IH]; intros s H; [exact H|].
  destruct s as [|b s]; [exact H|]. cbn [skipn]. inversion H; subst. auto.
Qed.

(* (a mod (b c)) / b = (a / b) mod c *)
Lemma x4h_mod_div (a b c: Z) : 0 < b -> 0 < c -> (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros Hb Hc. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm b ((a / b) mod c)), Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma x4h_mod_mod_pow (a k n: Z) : 0 <= k <= n -> (a mod 2 ^ n) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros H. replace n with (k + (n - k)) by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (n - k)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r by lia. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

Lemma x4h_peek_scale (V pos nb L: Z) :
  0 <= pos -> 0 <= nb <= L -> bs_peek V pos L / 2 ^ (L - nb) = bs_peek V pos nb.
Proof.
  intros Hp Hn. unfold bs_peek.
  assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
  assert (0 < 2 ^ (L - nb)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.div_div by lia.
  replace L with (nb + (L - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc. apply Z.div_mul_cancel_r; lia.
Qed.

Lemma x4h_le_value_window (s: list Z) (q: Z) :
  bytes_ok s -> 0 <= q -> le_value (slice s q 5) = (le_value s / 2 ^ (8 * q)) mod 2 ^ 40.
Proof.
  intros H Hq. unfold slice.
  rewrite x4h_le_value_firstn by (apply x4h_bytes_ok_skipn; exact H).
  rewrite <- x4h_le_value_skipn by exact H.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma x4h_peek_eq (s: list Z) (pos nb: Z) :
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
    rewrite Z.div_mul_cancel_r by lia. rewrite x4h_mod_div by lia.
    rewrite x4h_le_value_window by (auto; apply Z.div_pos; lia).
    fold V.
    assert (Hr: 0 <= lo mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (0 < 2 ^ (lo mod 8)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq: 0 <= lo / 8) by (apply Z.div_pos; lia).
    assert (0 < 2 ^ (8 * (lo / 8))) by (apply Z.pow_pos_nonneg; lia).
    replace (2 ^ 40) with (2 ^ (lo mod 8) * 2 ^ (40 - lo mod 8))
      by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite x4h_mod_div by (try lia; apply Z.pow_pos_nonneg; lia).
    rewrite x4h_mod_mod_pow by lia.
    rewrite Z.div_div by lia. rewrite <- Z.pow_add_r by lia.
    rewrite <- (Z_div_mod_eq_full lo 8). reflexivity.
  - assert (0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 2 ^ (- (pos - nb))) by (apply Z.pow_pos_nonneg; lia).
    replace nb with (pos + - (pos - nb)) at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite Z.mul_assoc, (Z.mul_comm _ (2 ^ pos)), <- Z.mul_assoc, (Z.mul_comm (2 ^ pos)), Z.div_mul by lia.
    f_equal. unfold slice. replace (Z.to_nat 0) with O by reflexivity. cbn [skipn].
    rewrite x4h_le_value_firstn by exact Hs.
    replace (8 * Z.of_nat (Z.to_nat 5)) with 40 by reflexivity.
    rewrite x4h_mod_mod_pow by lia. reflexivity.
Qed.

Lemma x4h_bs_peek_div (s: list Z) (pos nb L: Z) :
  bytes_ok s -> 0 <= pos -> 0 <= nb <= L -> L <= 32 ->
  bs_peek (bs_value s) pos L / 2 ^ (L - nb) = bs_peek_s s pos nb.
Proof.
  intros Hs Hp Hn HL. rewrite x4h_peek_scale by lia. apply x4h_peek_eq; auto; lia.
Qed.

Lemma x4h_hsym_peek (ht: huf_table) (s: list Z) (L pos: Z) :
  0 <= ht_log ht <= L -> L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  hsym ht L (bs_peek (bs_value s) pos L) = nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0).
Proof.
  intros Hl HL Hs Hp. unfold hsym. unfold HUF_TABLELOG_MAX in HL.
  rewrite x4h_bs_peek_div by (auto; lia). reflexivity.
Qed.

Lemma x4h_peek_range (V: list Z) (pos L: Z) : 0 <= L -> 0 <= bs_peek_s V pos L < 2 ^ L.
Proof.
  intros HL. unfold bs_peek_s.
  assert (HP: 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  destruct (pos <? 0) eqn:E; [lia|]. apply Z.ltb_ge in E.
  destruct (pos - L >=? 0) eqn:E2.
  - apply Z.mod_pos_bound; lia.
  - rewrite Z.geb_leb, Z.leb_gt in E2.
    assert (Hp: 0 < 2 ^ pos) by (apply Z.pow_pos_nonneg; lia).
    assert (He: 0 < 2 ^ (- (pos - L))) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound (le_value (slice V 0 5)) (2 ^ pos) Hp) as Hm.
    split.
    + apply Z.mul_nonneg_nonneg; lia.
    + replace (2 ^ L) with (2 ^ pos * 2 ^ (- (pos - L))).
      * apply Z.mul_lt_mono_pos_r; lia.
      * rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* the cell a step reads is a real cell of the table *)
Lemma x4h_cell (ht: huf_table) (V: list Z) (pos: Z) (s nb: Z) :
  huf_ok ht -> nth (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0) = (s, nb) ->
  0 <= s < 256 /\ 1 <= nb <= ht_log ht.
Proof.
  intros (Hlog & Hlen & Hall) Hc.
  pose proof (x4h_peek_range V pos (ht_log ht) ltac:(lia)) as Hr.
  assert (Hin: In (s, nb) (huf_cells ht)).
  { rewrite <- Hc. apply nth_In. rewrite Zlength_correct in Hlen. lia. }
  rewrite Forall_forall in Hall. apply (Hall _ Hin).
Qed.

Lemma x4h_bounds (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) (p: Z) :
  huf_ok ht -> bytes_ok V -> huf_decode_syms ht V k pos = Some (q, p) ->
  Zlength q = Z.of_nat k /\ bytes_ok q /\ p + Z.of_nat k <= pos /\ ((k > 0)%nat -> 0 <= p).
Proof.
  intros Hht HV. revert pos q p.
  induction k as [|k IH]; intros pos q p H; simpl in H.
  - inversion H; subst. repeat split; try (constructor || lia).
  - destruct (nth (Z.to_nat (bs_peek_s V pos (ht_log ht))) (huf_cells ht) (0, 0)) as [s nb] eqn:Hc.
    pose proof (x4h_cell ht V pos s nb Hht Hc) as [Hs Hnb].
    destruct (pos - nb <? 0)%Z eqn:E; [discriminate|]. apply Z.ltb_ge in E.
    destruct (huf_decode_syms ht V k (pos - nb)) as [[l p']|] eqn:Hr; [|discriminate].
    inversion H; subst q p; clear H.
    destruct (IH _ _ _ Hr) as (H1 & H2 & H3 & H4).
    split; [rewrite Zlength_cons; lia|].
    split; [constructor; [unfold is_byte; lia | exact H2]|].
    split; [lia|].
    intros _. destruct k as [|k].
    + simpl in Hr. inversion Hr; subst. lia.
    + apply H4. lia.
Qed.

Lemma x4h_step (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) (p L: Z) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok V -> 0 <= pos ->
  huf_decode_syms ht V (S k) pos = Some (q, p) ->
  let c := hsym ht L (bs_peek (bs_value V) pos L) in
  exists q', q = fst c :: q' /\ 0 <= pos - snd c /\ huf_decode_syms ht V k (pos - snd c) = Some (q', p).
Proof.
  intros Hok HL HV Hpos H c. subst c.
  rewrite x4h_hsym_peek; [| destruct Hok; lia | lia | auto | lia].
  simpl in H. destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb]. simpl.
  destruct (pos - nb <? 0) eqn:E; [discriminate|].
  destruct (huf_decode_syms ht V k (pos - nb)) as [[l' p']|]; [|discriminate].
  inversion H; subst. exists l'. split; [auto|]. split; [lia|auto].
Qed.

Lemma x4_mid_start (ht: huf_table) (si: list Z) (k m: Z) (w: list Z) (pos lo: Z) :
  x4_sinv ht si k m w pos lo 1 -> 4 * m + 4 <= k -> x4_mid ht si k m 0 w pos lo.
Proof.
  intros (Hw & Hb & H1 & H2 & Hes & Hq) Hk.
  destruct (Hes eq_refl) as [Hlo Hc].
  unfold x4_mid. rewrite Z.sub_0_r, Z.add_0_r.
  split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|].
  intros q Hq'. destruct (Hq q Hq') as [_ Hr]. rewrite Z.sub_0_r. exact Hr.
Qed.

(* one HUF_decodeSymbolX1: the peek v is exact when it must be (decodeSymbolX1's post) *)
Lemma x4_mid_step (ht: huf_table) (si: list Z) (k m t: Z) (wt: list Z) (pos lo L v: Z) :
  x4_mid ht si k m t wt pos lo -> t < 4 -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok si ->
  0 <= v < 2 ^ L -> (lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value si) pos L) ->
  x4_mid ht si k m (t + 1) (wt ++ [fst (hsym ht L v)]) (pos - snd (hsym ht L v)) lo.
Proof.
  intros (Hw & Hb & Hk & Ht & H1 & H2 & Hc & Hq) Ht4 Hok HL Hsi Hv Hex.
  assert (Hlog: ht_log ht <= L) by lia.
  destruct (hsym_range ht L v Hok Hlog Hv) as [Hs Hn].
  unfold HUF_TABLELOG_MAX in HL.
  unfold x4_mid.
  split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [apply Forall_app; split; [auto|]; constructor; [unfold is_byte; lia|constructor]|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros q Hq'. destruct (Hq q Hq') as (r & Hr & Hd).
  assert (Hn4: Z.to_nat (k - 4 * m - t) = S (Z.to_nat (k - 4 * m - (t + 1)))) by lia.
  rewrite Hn4 in Hd.
  destruct (x4h_bounds ht si _ pos r 0 Hok Hsi Hd) as (_ & _ & Hp & _).
  assert (Hv': v = bs_peek (bs_value si) pos L) by (apply Hex; lia).
  subst v.
  destruct (x4h_step ht si _ pos r 0 L Hok HL Hsi ltac:(lia) Hd) as (q' & Hr' & _ & Hd').
  exists q'. split; [subst q r; rewrite <- app_assoc; reflexivity|].
  exact Hd'.
Qed.

(* BIT_reloadDStreamFast's precondition after the 4 decodes (lo = 0 needs the Spec_bits fix) *)
Lemma x4_mid_pre_reload (ht: huf_table) (si: list Z) (k m: Z) (wt: list Z) (pos lo: Z) :
  x4_mid ht si k m 4 wt pos lo -> lo <= pos \/ lo = 0.
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hc & _). lia.
Qed.

(* a model run ending at position 0 starts at a position >= 0 (code lengths are >= 0) *)
Lemma x4_cell_nb_nonneg (ht: huf_table) (n: nat) : huf_ok ht -> 0 <= snd (nth n (huf_cells ht) (0, 0)).
Proof.
  intros (_ & _ & HF). destruct (Nat.lt_ge_cases n (length (huf_cells ht))) as [Hn|Hn].
  - pose proof (nth_In _ (0, 0) Hn) as HI. rewrite Forall_forall in HF. specialize (HF _ HI). lia.
  - rewrite nth_overflow by exact Hn. simpl; lia.
Qed.

Lemma x4_decode_pos_nonneg (ht: huf_table) (V: list Z) (k: nat) (pos: Z) (q: list Z) :
  huf_ok ht -> huf_decode_syms ht V k pos = Some (q, 0) -> 0 <= pos.
Proof.
  intros Hok H. destruct k as [|k]; cbn [huf_decode_syms] in H.
  - inversion H; lia.
  - pose proof (x4_cell_nb_nonneg ht (Z.to_nat (bs_peek_s V pos (ht_log ht))) Hok) as Hnb.
    destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb]. simpl in Hnb.
    destruct (pos - nb <? 0) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2. lia.
Qed.

(* BIT_reloadDStreamFast: the next iteration's invariant; es' = 1 only if the reload was unfinished *)
Lemma x4_mid_reload (ht: huf_table) (si: list Z) (k m: Z) (wt: list Z) (pos lo es': Z) :
  x4_mid ht si k m 4 wt pos lo -> huf_ok ht -> bytes_ok si ->
  (es' = 1 -> fst (bs_reload_fast pos lo) = BIT_unfinished) ->
  x4_sinv ht si k (m + 1) wt pos (snd (bs_reload_fast pos lo)) es'.
Proof.
  intros (Hlen & Hwb & Hk & Ht & Hp1 & Hp2 & Hp3 & Hm) Hok Hsi Hes.
  unfold bs_reload_fast in *. unfold BIT_overflow, BIT_unfinished in *.
  destruct (lo / 8 <? 8) eqn:E; cbn [fst snd] in *.
  - unfold x4_sinv. split; [lia|]. split; [exact Hwb|]. split; [lia|]. split; [lia|].
    split; [intros Hes1; specialize (Hes Hes1); lia|].
    intros q Hq. destruct (Hm q Hq) as (r & Hr & Hd). split.
    + destruct Hp3 as [H|H]; [lia|].
      pose proof (x4_decode_pos_nonneg ht si _ pos r Hok Hd). lia.
    + exists r. split; [exact Hr|]. replace (k - 4 * (m + 1)) with (k - 4 * m - 4) by lia. exact Hd.
  - apply Z.ltb_ge in E.
    assert (H64: 64 <= lo).
    { pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)). lia. }
    pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)) as Hmb.
    unfold x4_sinv. split; [lia|]. split; [exact Hwb|]. split; [lia|]. split; [lia|].
    split; [intros _; split; [lia|left; lia]|].
    intros q Hq. destruct (Hm q Hq) as (r & Hr & Hd). split; [lia|].
    exists r. split; [exact Hr|]. replace (k - 4 * (m + 1)) with (k - 4 * m - 4) by lia. exact Hd.
Qed.

(* a stream finished by HUF_decodeStreamX1 (its post): the model's q is what the C wrote *)
Lemma x4_sinv_finish (ht: huf_table) (si: list Z) (k m: Z) (w: list Z) (pos lo es: Z) (l: list Z) (pos' lo': Z) :
  x4_sinv ht si k m w pos lo es ->
  (lo <= pos -> forall l', huf_decode_syms ht si (Z.to_nat (k - 4 * m)) pos = Some (l', 0) ->
     l = l' /\ pos' = 0 /\ lo' = 0) ->
  forall q, x1_stream_ok ht si k q -> q = w ++ l /\ pos' = 0 /\ lo' = 0.
Proof.
  intros (Hlen & Hwb & _ & _ & _ & Hm) H q Hq.
  destruct (Hm q Hq) as (Hlp & r & Hr & Hd).
  destruct (H Hlp r Hd) as (Hl & Hp & Hlo). subst. auto.
Qed.

(* ---------- the output array: segments (start, bytes written) ---------- *)
Definition x4_cell (oc: list val) (segs: list (Z * list Z)) (i: Z) : val :=
  fold_right (fun sw acc => if andb (fst sw <=? i) (i <? fst sw + Zlength (snd sw))
                            then Vint (Int.repr (Znth (i - fst sw) (snd sw))) else acc) (Znth i oc) segs.

Definition x4_out (oc oc': list val) (segs: list (Z * list Z)) : Prop :=
  Zlength oc' = Zlength oc /\ forall i, 0 <= i < Zlength oc -> Znth i oc' = x4_cell oc segs i.

Ltac x4zb := repeat match goal with
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  end; cbn [andb].

Lemma x4c_nil_cover (oc: list val) (segs: list (Z * list Z)) (i: Z) :
  Forall (fun sw => snd sw = []) segs -> x4_cell oc segs i = Znth i oc.
Proof.
  intros H; unfold x4_cell; induction H as [|sw segs Hsw H IH]; simpl; auto.
  rewrite Hsw, IH, Zlength_nil.
  destruct (fst sw <=? i) eqn:E1; destruct (i <? fst sw + 0) eqn:E2; simpl; auto.
  apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia.
Qed.

Lemma x4c_pre_nocover (i: Z) (pre: list (Z * list Z)) (acc: val) :
  (forall sw, In sw pre -> ~ (fst sw <= i < fst sw + Zlength (snd sw))) ->
  fold_right (fun sw acc => if andb (fst sw <=? i) (i <? fst sw + Zlength (snd sw))
                            then Vint (Int.repr (Znth (i - fst sw) (snd sw))) else acc) acc pre = acc.
Proof.
  induction pre as [|sw pre IH]; intros H; simpl; auto.
  rewrite IH by (intros; apply H; simpl; auto).
  destruct (fst sw <=? i) eqn:E1; destruct (i <? fst sw + Zlength (snd sw)) eqn:E2; simpl; auto.
  apply Z.leb_le in E1; apply Z.ltb_lt in E2. exfalso; apply (H sw); simpl; auto.
Qed.

Lemma x4_out_init (oc: list val) (segs: list (Z * list Z)) :
  Forall (fun sw => snd sw = []) segs -> x4_out oc oc segs.
Proof.
  intros H; split; auto. intros i Hi. rewrite x4c_nil_cover; auto.
Qed.

(* one byte stored right after segment (st, w), outside every other segment *)
Lemma x4_out_store (oc oc': list val) (pre post: list (Z * list Z)) (st: Z) (w: list Z) (b: Z) :
  x4_out oc oc' (pre ++ (st, w) :: post) -> 0 <= st -> st + Zlength w < Zlength oc ->
  (forall sw, In sw (pre ++ post) -> ~ (fst sw <= st + Zlength w < fst sw + Zlength (snd sw))) ->
  x4_out oc (upd_Znth (st + Zlength w) oc' (Vint (Int.repr b))) (pre ++ (st, w ++ [b]) :: post).
Proof.
  intros [Hl Hc] Hst Hlt Hdis. pose proof (Zlength_nonneg w). split.
  { rewrite upd_Znth_Zlength by lia. auto. }
  intros i Hi. unfold x4_cell in *. rewrite fold_right_app.
  destruct (Z.eq_dec i (st + Zlength w)).
  - subst i. rewrite upd_Znth_same by lia.
    rewrite x4c_pre_nocover by (intros sw Hin; apply Hdis; apply in_app_iff; auto).
    cbn [fold_right fst snd]. rewrite Zlength_app. change (Zlength [b]) with 1. x4zb.
    replace (st + Zlength w - st) with (Zlength w) by lia.
    rewrite app_Znth2 by lia. rewrite Z.sub_diag. reflexivity.
  - rewrite upd_Znth_diff by lia. rewrite Hc by lia. rewrite fold_right_app. f_equal.
    cbn [fold_right fst snd]. rewrite Zlength_app. change (Zlength [b]) with 1.
    assert (i < st \/ st <= i < st + Zlength w \/ st + Zlength w < i) as [?|[?|?]] by lia; x4zb; auto.
    rewrite app_Znth1 by lia. auto.
Qed.

(* the epilogue: the 4 HUF_decodeStreamX1 calls fill [d + 4m, end of segment) of each segment *)
Definition x4_fill (oc': list val) (a k: Z) (l: list Z) : list val :=
  sublist 0 a oc' ++ zbytes l ++ sublist (a + k) (Zlength oc') oc'.

Lemma x4f_len (oc': list val) (a k: Z) (l: list Z) :
  0 <= a -> 0 <= k -> a + k <= Zlength oc' -> Zlength l = k -> Zlength (x4_fill oc' a k l) = Zlength oc'.
Proof. intros. unfold x4_fill. list_solve. Qed.

Lemma x4f_in (oc': list val) (a k: Z) (l: list Z) (i: Z) :
  0 <= a -> 0 <= k -> a + k <= Zlength oc' -> Zlength l = k -> a <= i < a + k ->
  Znth i (x4_fill oc' a k l) = Vint (Int.repr (Znth (i - a) l)).
Proof. intros. unfold x4_fill. list_solve. Qed.

Lemma x4f_out (oc': list val) (a k: Z) (l: list Z) (i: Z) :
  0 <= a -> 0 <= k -> a + k <= Zlength oc' -> Zlength l = k -> 0 <= i < Zlength oc' -> ~ (a <= i < a + k) ->
  Znth i (x4_fill oc' a k l) = Znth i oc'.
Proof. intros. unfold x4_fill. list_solve. Qed.

Lemma x4_out_final (oc oc': list val) (d seg n m: Z) (w1 w2 w3 w4 l1 l2 l3 l4: list Z) :
  0 <= d -> d + n <= Zlength oc -> 0 <= m -> 3 * seg + 4 * m <= n -> n <= 4 * seg ->
  Zlength w1 = 4 * m -> Zlength w2 = 4 * m -> Zlength w3 = 4 * m -> Zlength w4 = 4 * m ->
  Zlength l1 = seg - 4 * m -> Zlength l2 = seg - 4 * m -> Zlength l3 = seg - 4 * m ->
  Zlength l4 = n - 3 * seg - 4 * m ->
  x4_out oc oc' [(d, w1); (d + seg, w2); (d + seg + seg, w3); (d + seg + seg + seg, w4)] ->
  let oc4 := x4_fill (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) l1)
                 (d + seg + 4 * m) (seg - 4 * m) l2) (d + seg + seg + 4 * m) (seg - 4 * m) l3)
                 (d + seg + seg + seg + 4 * m) (n - 3 * seg - 4 * m) l4 in
  out_after oc oc4 d n /\
  sublist d (d + n) oc4 = zbytes (w1 ++ l1 ++ w2 ++ l2 ++ w3 ++ l3 ++ w4 ++ l4).
Proof.
  intros Hd Hn Hm H3 H4 Hw1 Hw2 Hw3 Hw4 Hl1 Hl2 Hl3 Hl4 [Hl Hc] oc4.
  remember (x4_fill oc' (d + 4 * m) (seg - 4 * m) l1) as oc1 eqn:E1.
  remember (x4_fill oc1 (d + seg + 4 * m) (seg - 4 * m) l2) as oc2 eqn:E2.
  remember (x4_fill oc2 (d + seg + seg + 4 * m) (seg - 4 * m) l3) as oc3 eqn:E3.
  assert (L1: Zlength oc1 = Zlength oc) by (subst oc1; rewrite x4f_len; lia).
  assert (L2: Zlength oc2 = Zlength oc) by (subst oc2; rewrite x4f_len; lia).
  assert (L3: Zlength oc3 = Zlength oc) by (subst oc3; rewrite x4f_len; lia).
  assert (L4: Zlength oc4 = Zlength oc) by (subst oc4; rewrite x4f_len; lia).
  assert (K: forall i, 0 <= i < Zlength oc -> Znth i oc4 =
            if andb (d <=? i) (i <? d + n)
            then Vint (Int.repr (Znth (i - d) (w1 ++ l1 ++ w2 ++ l2 ++ w3 ++ l3 ++ w4 ++ l4)))
            else Znth i oc).
  { intros i Hi. subst oc4.
    assert (i < d \/ d <= i < d + 4 * m \/ d + 4 * m <= i < d + seg \/
            d + seg <= i < d + seg + 4 * m \/ d + seg + 4 * m <= i < d + seg + seg \/
            d + seg + seg <= i < d + seg + seg + 4 * m \/ d + seg + seg + 4 * m <= i < d + seg + seg + seg \/
            d + seg + seg + seg <= i < d + seg + seg + seg + 4 * m \/
            d + seg + seg + seg + 4 * m <= i < d + n \/ d + n <= i) as HC by lia.
    decompose [or] HC; clear HC.
    all: repeat first [ rewrite x4f_in by lia | rewrite x4f_out by lia | rewrite E3 | rewrite E2 | rewrite E1 ].
    all: try (rewrite Hc by lia; unfold x4_cell; cbn [fold_right fst snd]; rewrite ?Hw1, ?Hw2, ?Hw3, ?Hw4).
    all: x4zb.
    all: repeat first [rewrite app_Znth1 by (rewrite ?Zlength_app; lia) | rewrite app_Znth2 by (rewrite ?Zlength_app; lia)].
    all: rewrite ?Zlength_app, ?Hw1, ?Hw2, ?Hw3, ?Hw4, ?Hl1, ?Hl2, ?Hl3.
    all: try reflexivity.
    all: match goal with |- Vint (Int.repr (Znth ?a ?l)) = Vint (Int.repr (Znth ?b ?l)) =>
           replace a with b by lia; reflexivity end. }
  split.
  - split; [exact L4 |]. intros i Hi Hout. rewrite K by lia.
    destruct ((d <=? i) && (i <? d + n))%bool eqn:EB; auto.
    apply andb_true_iff in EB as [EB1 EB2]. apply Z.leb_le in EB1. apply Z.ltb_lt in EB2. lia.
  - apply Znth_eq_ext.
    + rewrite Zlength_sublist by lia. rewrite Zlength_map, !Zlength_app. lia.
    + intros j Hj. rewrite Zlength_sublist in Hj by lia.
      rewrite Znth_sublist by lia. rewrite K by lia. x4zb.
      rewrite Znth_map by (rewrite !Zlength_app; lia).
      replace (j + d - d) with j by lia. reflexivity.
Qed.

(* the 4 segments of the output *)
Definition x4_segs (d seg: Z) (w1 w2 w3 w4: list Z) : list (Z * list Z) :=
  [(d, w1); (d + seg, w2); (d + seg + seg, w3); (d + seg + seg + seg, w4)].

Lemma x4_fill_len (oc': list val) (a k: Z) (l: list Z) :
  0 <= a -> 0 <= k -> a + k <= Zlength oc' -> Zlength l = k -> Zlength (x4_fill oc' a k l) = Zlength oc'.
Proof. intros. unfold x4_fill. rewrite !Zlength_app, Zlength_map, !Zlength_sublist by lia. lia. Qed.

(* the end: if the model decodes the 4 streams, the C's 4 HUF_decodeStreamX1 finished them exactly *)
Lemma x4_final_model (ht: huf_table) (s: list Z) (n m: Z) (w1 w2 w3 w4 r1 r2 r3 r4: list Z)
    (p1 o1 p2 o2 p3 o3 p4 o4 e p1' o1' p2' o2' p3' o3' p4' o4': Z) :
  huf_ok ht -> bytes_ok s -> 0 <= n ->
  let l1 := le_field s 0 2 in let l2 := le_field s 2 2 in let l3 := le_field s 4 2 in
  let seg := (n + 3) / 4 in
  x4_sinv ht (sublist 6 (6 + l1) s) seg m w1 p1 o1 e ->
  x4_sinv ht (sublist (6 + l1) (6 + l1 + l2) s) seg m w2 p2 o2 e ->
  x4_sinv ht (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) seg m w3 p3 o3 e ->
  x4_sinv ht (sublist (6 + l1 + l2 + l3) (Zlength s) s) (n - 3 * seg) m w4 p4 o4 e ->
  (o1 <= p1 -> forall l', huf_decode_syms ht (sublist 6 (6 + l1) s) (Z.to_nat (seg - 4 * m)) p1 = Some (l', 0) ->
     r1 = l' /\ p1' = 0 /\ o1' = 0) ->
  (o2 <= p2 -> forall l', huf_decode_syms ht (sublist (6 + l1) (6 + l1 + l2) s) (Z.to_nat (seg - 4 * m)) p2 = Some (l', 0) ->
     r2 = l' /\ p2' = 0 /\ o2' = 0) ->
  (o3 <= p3 -> forall l', huf_decode_syms ht (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) (Z.to_nat (seg - 4 * m)) p3 = Some (l', 0) ->
     r3 = l' /\ p3' = 0 /\ o3' = 0) ->
  (o4 <= p4 -> forall l', huf_decode_syms ht (sublist (6 + l1 + l2 + l3) (Zlength s) s) (Z.to_nat (n - 3 * seg - 4 * m)) p4 = Some (l', 0) ->
     r4 = l' /\ p4' = 0 /\ o4' = 0) ->
  forall l, huf_lits_with true ht s n = Some l ->
  l = w1 ++ r1 ++ w2 ++ r2 ++ w3 ++ r3 ++ w4 ++ r4 /\
  p1' = 0 /\ o1' = 0 /\ p2' = 0 /\ o2' = 0 /\ p3' = 0 /\ o3' = 0 /\ p4' = 0 /\ o4' = 0.
Proof.
  intros Hok Hs Hn l1 l2 l3 seg S1 S2 S3 S4 F1 F2 F3 F4 l E. unfold huf_lits_with in E.
  destruct (huf4_split ht s n l Hok Hs Hn E) as (_ & _ & _ & q1 & q2 & q3 & q4 & -> & Q1 & Q2 & Q3 & Q4).
  destruct (x4_sinv_finish _ _ _ _ _ _ _ _ _ _ _ S1 F1 q1 Q1) as (-> & ? & ?).
  destruct (x4_sinv_finish _ _ _ _ _ _ _ _ _ _ _ S2 F2 q2 Q2) as (-> & ? & ?).
  destruct (x4_sinv_finish _ _ _ _ _ _ _ _ _ _ _ S3 F3 q3 Q3) as (-> & ? & ?).
  destruct (x4_sinv_finish _ _ _ _ _ _ _ _ _ _ _ S4 F4 q4 Q4) as (-> & ? & ?).
  split; [rewrite !app_assoc; reflexivity | repeat split; auto].
Qed.

Local Open Scope logic.

(* ---------- VST helpers ---------- *)

(* the input window, cut out of the caller's array *)
Lemma win_split (sh: share) (N: Z) (c: list val) (off: Z) (s: list Z) (base: val) :
  0 <= off -> off + Zlength s <= N -> Zlength c = N -> sublist off (off + Zlength s) c = zbytes s ->
  field_compatible (tarray tuchar N) [] base ->
  data_at sh (tarray tuchar N) c base =
  data_at sh (tarray tuchar off) (sublist 0 off c) base *
  data_at sh (tarray tuchar (Zlength s)) (zbytes s) (offset_val off base) *
  data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c)
    (offset_val (off + Zlength s) base).
Proof.
  intros Hoff HN Hc Hsub Hfc. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh N off (off + Zlength s)) by (try rep_lia; list_solve).
  pose proof (Zlength_nonneg s).
  rewrite !field_address0_offset by (apply field_compatible0_cons; split; [simpl; lia | auto with field_compatible]).
  simpl. rewrite !Z.mul_1_l, Hsub. replace (off + Zlength s - off) with (Zlength s) by lia. reflexivity.
Qed.

Lemma mem_read_pre_ok (sh: share) (p: val) (s: list Z) (i k: Z) :
  readable_share sh -> bytes_ok s -> 0 <= i -> 0 <= k -> i + k <= Zlength s -> mem_read_pre sh p s i k.
Proof. intros. unfold mem_read_pre. split3; auto. split; [lia|]. apply Forall_sublist; auto. Qed.

(* pointer arithmetic of the prologue, as offset_val *)
Lemma oadd_uchar_long (p: val) (n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong p (Vlong (Int64.repr n))) = offset_val n p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sym. unfold Ptrofs.eqm. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma oadd_uchar_int (p: val) (j: Z) : isptr p -> Int.min_signed <= j <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tint p (Vint (Int.repr j))) = offset_val j p.
Proof.
  intros Hp Hj. destruct p; try contradiction. simpl. f_equal. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold ptrofs_of_int, Ptrofs.of_ints.
  rewrite Int.signed_repr by rep_lia. reflexivity.
Qed.

Lemma osub_uchar_int (p: val) (j: Z) : isptr p -> Int.min_signed <= j <= Int.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint p (Vint (Int.repr j))) = offset_val (- j) p.
Proof.
  intros Hp Hj. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold ptrofs_of_int, Ptrofs.of_ints.
  rewrite Int.signed_repr by rep_lia. rewrite Ptrofs.sub_add_opp. f_equal.
  rewrite <- Ptrofs.neg_repr. reflexivity.
Qed.

Lemma oadd_uint_one (p: val) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuint) tint p (Vint (Int.repr 1))) = offset_val 4 p.
Proof. intros Hp. destruct p; try contradiction. reflexivity. Qed.

(* comparing two pointers into one byte array (the array and any frame R) *)
Lemma arr_test_order (sh: share) (len: Z) (oc: list val) (ob: val) (i j: Z) (R: mpred) :
  readable_share sh -> 0 < len -> 0 <= i <= len -> 0 <= j <= len ->
  data_at sh (tarray tuchar len) oc ob * R |-- denote_tc_test_order (offset_val i ob) (offset_val j ob).
Proof.
  intros Hsh Hlen Hi Hj. saturate_local.
  assert (Hp: isptr ob) by (destruct H as [? _]; auto).
  rewrite isptr_denote_tc_test_order by (destruct ob; try contradiction; auto).
  unfold test_order_ptrs. rewrite sameblock_offset_val by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1; (eapply derives_trans; [apply data_at_memory_block|]);
    simpl sizeof; apply memory_block_weak_valid_pointer; try rep_lia; apply readable_nonidentity; auto.
Qed.

(* the order of two pointers into one byte array *)
Lemma sem_cmp_gt_offsets (len a c: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= c <= len ->
  sem_cmp_pp Cgt (offset_val a ob) (offset_val c ob) = Some (bool2val (c <? a)).
Proof.
  intros Hfc Ha Hc. destruct Hfc as (Hp & _ & Hsz & _). destruct ob; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold sem_cmp_pp; simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr c) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (c <? a) eqn:E; simpl; auto; rewrite ?Z.ltb_lt, ?Z.ltb_ge in E; lia.
Qed.

Lemma sem_cmp_lt_offsets (len a c: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= c <= len ->
  sem_cmp_pp Clt (offset_val a ob) (offset_val c ob) = Some (bool2val (a <? c)).
Proof.
  intros Hfc Ha Hc. destruct Hfc as (Hp & _ & Hsz & _). destruct ob; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold sem_cmp_pp; simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr c) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (a <? c) eqn:E; simpl; auto; rewrite ?Z.ltb_lt, ?Z.ltb_ge in E; lia.
Qed.

(* the main loop's condition endSignal & (op4 < olimit) *)
Lemma x4_loop_cond (len a b es: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= b <= len -> (es = 0 \/ es = 1) ->
  typed_true tint (match sem_and tuint tint (Vint (Int.repr es)) (compare_pp Clt (offset_val a ob) (offset_val b ob))
                   with Some v' => v' | None => Vundef end) ->
  es = 1 /\ a < b.
Proof.
  intros Hfc Ha Hb Hes Ht. destruct Hfc as (Hp & _ & Hsz & _). destruct ob; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i).
  unfold compare_pp in Ht. simpl in Ht. destruct (eq_block b0 b0); [|congruence]. simpl in Ht.
  unfold Ptrofs.ltu in Ht. rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) in Ht by rep_lia.
  rewrite !Ptrofs.unsigned_repr in Ht by rep_lia.
  destruct (zlt _ _); destruct Hes; subst; simpl in Ht; unfold typed_true in Ht; simpl in Ht;
    try discriminate; split; auto; lia.
Qed.

(* the main loop's exit: endSignal = 0 or op4 >= olimit *)
Lemma x4_loop_cond_false (len a b es: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= b <= len -> (es = 0 \/ es = 1) ->
  typed_false tint (match sem_and tuint tint (Vint (Int.repr es)) (compare_pp Clt (offset_val a ob) (offset_val b ob))
                    with Some v' => v' | None => Vundef end) ->
  es = 0 \/ b <= a.
Proof.
  intros Hfc Ha Hb Hes Ht. destruct Hfc as (Hp & _ & Hsz & _). destruct ob; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i).
  unfold compare_pp in Ht. simpl in Ht. destruct (eq_block b0 b0); [|congruence]. simpl in Ht.
  unfold Ptrofs.ltu in Ht. rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b) in Ht by rep_lia.
  rewrite !Ptrofs.unsigned_repr in Ht by rep_lia.
  destruct (zlt _ _); destruct Hes; subst; simpl in Ht; unfold typed_false in Ht; simpl in Ht;
    first [discriminate | left; reflexivity | right; lia].
Qed.

(* endCheck = the four BIT_endOfDStream results, and-ed *)
Lemma x4_endcheck (b1 b2 b3 b4: bool) :
  Int.and (Int.and (Int.and (Int.repr (if b1 then 1 else 0)) (Int.repr (if b2 then 1 else 0)))
     (Int.repr (if b3 then 1 else 0))) (Int.repr (if b4 then 1 else 0)) =
  Int.repr (if andb (andb b1 b2) (andb b3 b4) then 1 else 0).
Proof. destruct b1, b2, b3, b4; reflexivity. Qed.

(* one HUF_decodeSymbolX1 of the main loop, in the model: x4_mxw_step with x4_mid's bounds; the exact peek
   v = xb_look_fast .. is consumed (cleared), so that later entailments keep v abstract *)
Ltac x4_mx_pre v :=
  match goal with Hv: v = xb_look_fast (xb_of ?si ?q ?o) ?L, Hm: x4_mxw ?ht ?si ?P ?o ?w ?wt ?q |- _ =>
    match goal with Hd: x4_mid ht si _ _ _ wt q o |- _ =>
      let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
      pose proof Hd as (H1 & _ & _ & H2 & H3 & H4 & _ & _);
      let HM := fresh "HMX" in
      assert (HM := x4_mxw_step ht si P o w wt q L v Hm ltac:(assumption) ltac:(assumption) Hv ltac:(lia) ltac:(lia));
      clear Hv H1 H2 H3 H4 end end.

(* zstd's do { .. } while (0): the body, its normal end and its break both leave the loop *)
Lemma semax_dw0 {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred)
  (s: statement) (R: ret_assert) :
  semax Delta P s (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop s Sbreak) R.
Proof.
  intros H. eapply semax_loop; [exact H|].
  eapply semax_pre; [|apply semax_break]. destruct R; simpl. intros rho; apply andp_left2, derives_refl.
Qed.

(* the same, for a body that only ends normally (no break/continue/return inside at its level) *)
Lemma semax_dw0_n {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred)
  (s: statement) (R: ret_assert) :
  semax Delta P s (normal_ret_assert (RA_normal R)) -> semax Delta P (Sloop s Sbreak) R.
Proof.
  intros H. apply semax_dw0. eapply semax_post; [ | | | | exact H]; destruct R; simpl.
  - intros rho; apply andp_left2, derives_refl.
  - intros rho; apply andp_left2. simpl. apply FF_left.
  - intros rho; apply andp_left2. simpl. apply FF_left.
  - intros vl rho; apply andp_left2. simpl. apply FF_left.
Qed.

Ltac dw0 := repeat match goal with M := @abbreviate statement _ |- _ => unfold M; clear M end;
  try match goal with |- semax _ _ (@abbreviate statement _) _ => unfold abbreviate end;
  match goal with |- semax _ _ (Ssequence (Sloop _ Sbreak) _) _ =>
  eapply semax_seq; [apply semax_dw0; abbreviate_semax | ] end.

(* ---------- the returns ---------- *)

Lemma out_after_refl (oc: list val) (d n: Z) : out_after oc oc d n.
Proof. split; auto. intros i _ _. reflexivity. Qed.

Lemma err_20 : is_error_code (Int64.max_unsigned - 19) = true.
Proof. reflexivity. Qed.

Lemma vlong_err_20 : Vlong (Int64.repr (- (20))) = Vlong (Int64.repr (Int64.max_unsigned - 19)).
Proof. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. Qed.

Lemma hufdt_fold (sht: share) (ht: huf_table) (dt: val) (L: Z) (res: val) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> align_compatible tuint dt -> byte_val res ->
  L = hufdt_log false ht ->
  data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) dt *
  data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 dt) *
  memory_block sht (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) dt)
  |-- hufdt_x_at false sht ht dt.
Proof. intros. unfold hufdt_x_at. Exists L res. entailer!. Qed.

Lemma rep_data_at_ (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep sh gv s start pos lo p |-- data_at_ sh t_bitD p.
Proof. unfold BIT_DStream_rep. Intros ptr lim. apply data_at_data_at_. Qed.

(* the model accepts only inputs that pass the C's checks *)
Lemma x4_model_facts (ht: huf_table) (s: list Z) (n: Z) (l: list Z) :
  huf_ok ht -> bytes_ok s -> 0 <= n -> huf_lits_with true ht s n = Some l ->
  10 <= Zlength s /\ le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 7 <= Zlength s /\
  bs_wf (sublist 6 (6 + le_field s 0 2) s) = true /\
  bs_wf (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) = true /\
  bs_wf (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s) = true /\
  bs_wf (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) = true.
Proof.
  intros Hok Hs Hn E. unfold huf_lits_with in E.
  destruct (huf4_split ht s n l Hok Hs Hn E) as (H1 & H2 & _ & q1 & q2 & q3 & q4 & _ & S1 & S2 & S3 & S4).
  destruct S1 as [? _], S2 as [? _], S3 as [? _], S4 as [? _]. repeat split; auto; lia.
Qed.

Ltac x4_err_props := rewrite err_20; split3; [apply out_after_refl | discriminate |]; split; [|apply vlong_err_20];
  match goal with |- context [huf_lits_with true ?ht ?s ?n] =>
    let E := fresh "E" in destruct (huf_lits_with true ht s n) eqn:E; auto;
    apply x4_model_facts in E; auto; [|lia]; exfalso end.

(* the CHECK_F(BIT_initDStream(..)) blocks: after the call, the ERR_isError loop *)
Ltac x4_chk_err :=
  let r := fresh "r" in Intros r; forward;
  let Hr := fresh "Hr" in assert (Hr: 0 <= r <= Int64.max_unsigned) by lia;
  apply semax_dw0; abbreviate_semax; forward_call r;
  match goal with H: is_error_code r = true |- _ => rewrite H end;
  forward_if; [ | exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end].

Ltac x4_chk_ok li :=
  let r := fresh "r" in Intros r; subst r; forward;
  apply semax_dw0; abbreviate_semax; forward_call li;
  assert (is_error_code li = false) as -> by (unfold is_error_code; apply Z.ltb_ge; rep_lia);
  forward_if; [ match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end
              | forward; apply ENTAIL_refl ].

Ltac dw0q QQ := repeat match goal with M := @abbreviate statement _ |- _ => unfold M; clear M end;
  try match goal with |- semax _ _ (@abbreviate statement _) _ => unfold abbreviate end;
  match goal with |- semax _ _ (Ssequence (Sloop _ Sbreak) _) _ =>
    apply semax_seq with (Q := QQ); [apply semax_dw0_n; abbreviate_semax | abbreviate_semax] end.

(* a byte of the output array, as an array cell (for VST's store) *)
Lemma off_fa (len i: Z) (p: val) :
  field_compatible (tarray tuchar len) [] p -> 0 <= i < len ->
  offset_val i p = field_address (tarray tuchar len) [ArraySubsc i] p.
Proof.
  intros Hfc Hi. rewrite field_address_offset.
  - simpl. f_equal. lia.
  - apply field_compatible_cons. split; auto.
Qed.

Lemma zext_byte (b: Z) : 0 <= b < 256 -> Int.zero_ext 8 (Int.repr b) = Int.repr b.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

(* endSignal after the 4 reloads: 1 iff the 4 reloads were unfinished *)
Lemma fst_reload_range (p o: Z) : 0 <= fst (bs_reload_fast p o) <= 3.
Proof. unfold bs_reload_fast, BIT_overflow, BIT_unfinished. destruct (o / 8 <? 8); simpl; lia. Qed.

Lemma x4_es_and (e1 e2 e3 e4: Z) :
  0 <= e1 <= 3 -> 0 <= e2 <= 3 -> 0 <= e3 <= 3 -> 0 <= e4 <= 3 ->
  Int.and (Int.and (Int.and (Int.and (Int.repr 1) (Int.repr (Z.b2z (Int.eq (Int.repr e1) (Int.repr 0)))))
     (Int.repr (Z.b2z (Int.eq (Int.repr e2) (Int.repr 0))))) (Int.repr (Z.b2z (Int.eq (Int.repr e3) (Int.repr 0)))))
     (Int.repr (Z.b2z (Int.eq (Int.repr e4) (Int.repr 0)))) = Int.repr (x4_es e1 e2 e3 e4).
Proof.
  intros H1 H2 H3 H4. unfold x4_es.
  assert (E: forall e, 0 <= e <= 3 -> Int.eq (Int.repr e) (Int.repr 0) = (e =? 0)).
  { intros e He. assert (e = 0 \/ e = 1 \/ e = 2 \/ e = 3) as [ -> | [ -> | [ -> | -> ] ] ] by lia; reflexivity. }
  rewrite !E by auto.
  destruct (e1 =? 0), (e2 =? 0), (e3 =? 0), (e4 =? 0); reflexivity.
Qed.

Lemma x4_es_01 (e1 e2 e3 e4: Z) : x4_es e1 e2 e3 e4 = 0 \/ x4_es e1 e2 e3 e4 = 1.
Proof. unfold x4_es. destruct (andb (andb (andb (e1 =? 0) (e2 =? 0)) (e3 =? 0)) (e4 =? 0)); simpl; auto. Qed.

Lemma x4_es_1 (e1 e2 e3 e4: Z) :
  x4_es e1 e2 e3 e4 = 1 -> e1 = 0 /\ e2 = 0 /\ e3 = 0 /\ e4 = 0.
Proof.
  unfold x4_es. intros H. destruct (e1 =? 0) eqn:E1, (e2 =? 0) eqn:E2, (e3 =? 0) eqn:E3, (e4 =? 0) eqn:E4;
    simpl in H; try discriminate. rewrite !Z.eqb_eq in *. auto.
Qed.

(* a stream BIT_initDStream rejects is one the model's xb_init rejects *)
Lemma x4_init_none_of (s: list Z) : bytes_ok s -> bs_wf s = false -> xb_init s = None.
Proof. intros Hb Hw. rewrite xb_init_eq by exact Hb. rewrite Hw. reflexivity. Qed.

(* a stream BIT_initDStream accepts: the model's initial state is the C's (pos, lo) of Spec_bits *)
Lemma x4_init_some (si: list Z) (len: Z) :
  bytes_ok si -> bs_wf si = true -> Zlength si = len ->
  xb_init si = Some (xb_of si (bs_total si) (8 * Z.max 0 (len - 8))).
Proof. intros Hb Hw <-. rewrite xb_init_eq by exact Hb. rewrite Hw. reflexivity. Qed.

(* the exact clause after a failed BIT_initDStream (sel picks the stream in x4_exact_init's disjunction) *)
Ltac x4_init_none Hfit sel := change (negb true) with false;
  match goal with |- match x_huf_decode ?t false ?s ?n with _ => _ end =>
    let E := fresh in assert (E: x_huf_decode t false s n = None);
    [ apply x4_exact_init; [lia | lia | exact Hfit |
        sel; apply x4_init_none_of; [apply Forall_sublist; auto | assumption]]
    | rewrite E; assumption ] end.

Lemma rep_g_true (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep_g true sh gv s start pos lo p = BIT_DStream_rep_np sh gv s start pos lo p.
Proof. reflexivity. Qed.

Ltac urepr := repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
  rewrite (Int64.unsigned_repr x) in H by rep_lia end.

(* the test (size_t)(oend - op4) >= sizeof(size_t) *)
Lemma x4_size_cmp (len a b: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= b -> b <= len -> b - a <= 131072 ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.ltu n1 n2)))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val b ob) (offset_val a ob))) (Vptrofs (Ptrofs.repr 8))
  with Some v' => v' | None => Vundef end = bool2val (8 <=? b - a).
Proof.
  intros Hfc Hab Hb Hd. destruct Hfc as (Hp & _ & Hsz & _). destruct ob; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i).
  unfold sem_sub_pp. simpl. destruct (eq_block b0 b0); [|congruence]. simpl.
  rewrite (Ptrofs.add_commut i (Ptrofs.repr b)), (Ptrofs.add_commut i (Ptrofs.repr a)), Ptrofs.sub_shifted.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia.
  unfold Ptrofs.divs. rewrite !Ptrofs.signed_repr by rep_lia. rewrite Z.quot_1_r.
  unfold Ptrofs.to_int64. rewrite !Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt _ _), (8 <=? b - a) eqn:E; simpl; auto; rewrite ?Z.leb_le, ?Z.leb_gt in E; lia.
Qed.

Lemma body_HUF_decompress4X1_usingDTable_internal_body :
  semax_body Vprog G_4X1 f_HUF_decompress4X1_usingDTable_internal_body
    HUF_decompress4X1_usingDTable_internal_body_bc_spec.
Proof.
  start_function.
  unfold hufdt_x_at. Intros L res. rename H8 into Hres.
  rename H9 into HLd.
  assert (HLx: L = xh_x1_log ht) by (rewrite HLd; reflexivity).
  destruct H4 as (Hsh & Hoff & HoffN & HN & HlenC & _ & Hbs & Hsub).
  assert_PROP (field_compatible (tarray tuchar N) [] base /\ field_compatible (tarray tuchar (Zlength oc)) [] ob /\
               isptr dt) as Hfc by entailer!.
  destruct Hfc as (Hfcb & Hfco & Hdt).
  assert (Hpb: isptr base) by (destruct Hfcb; auto).
  assert (Hpo: isptr ob) by (destruct Hfco; auto).
  assert (Hs0: 0 <= Zlength s) by apply Zlength_nonneg.
  assert (HL: 1 <= L <= 12) by (destruct H5 as [? _]; unfold HUF_TABLELOG_MAX in *; lia).
  unfold ZSTD_BLOCKSIZE_MAX in H1, H3.
  forward_if.
  { forward. Exists (Int64.max_unsigned - 19) oc. entailer!.
    - urepr. rewrite err_20. split3; [apply out_after_refl | discriminate | ].
      split; [|split; [change (negb true) with false; rewrite x4_exact_short by lia; reflexivity | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; lia.
    - apply hufdt_fold; auto. }
  forward_if. { urepr. lia. }
  urepr.
  forward. forward. forward. forward. forward. forward.
  rewrite (win_split sh N c off s base) by auto.
  Intros.
  rewrite !oadd_uchar_long by auto. rewrite osub_uchar_int by (auto; rep_lia).
  rewrite oadd_uint_one by auto. rewrite !offset_offset_val.
  set (l1 := le_field s 0 2). set (l2 := le_field s 2 2). set (l3 := le_field s 4 2).
  assert (Hl1: 0 <= l1 < 65536) by (apply le_field2_range; auto).
  assert (Hl2: 0 <= l2 < 65536) by (apply le_field2_range; auto).
  assert (Hl3: 0 <= l3 < 65536) by (apply le_field2_range; auto).
  apply -> seq_assoc; forward_call (sh, offset_val off base, s, 0). { apply mem_read_pre_ok; auto; lia. }
  forward.
  apply -> seq_assoc; forward_call (sh, offset_val off base, s, 2). { apply mem_read_pre_ok; auto; lia. }
  forward.
  apply -> seq_assoc; forward_call (sh, offset_val off base, s, 4). { apply mem_read_pre_ok; auto; lia. }
  forward.
  rewrite !Int.unsigned_repr by rep_lia. fold l1 l2 l3.
  forward.
  forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward.
  assert (Hseg: Int64.divu (Int64.add (Int64.repr n) (Int64.repr (Int.signed (Int.repr 3))))
                  (Int64.repr (Int.signed (Int.repr 4))) = Int64.repr ((n + 3) / 4)).
  { rewrite !Int.signed_repr by rep_lia. unfold Int64.divu, Int64.add.
    rewrite (Int64.unsigned_repr n), (Int64.unsigned_repr 3), (Int64.unsigned_repr 4),
      (Int64.unsigned_repr (n + 3)) by rep_lia. reflexivity. }
  assert (Hl4: Int64.sub (Int64.repr (Zlength s)) (Int64.add (Int64.add (Int64.add (Int64.repr l1)
                 (Int64.repr l2)) (Int64.repr l3)) (Int64.repr (Int.signed (Int.repr 6)))) =
               Int64.repr (Zlength s - (l1 + l2 + l3 + 6))).
  { rewrite Int.signed_repr by rep_lia. unfold Int64.sub, Int64.add.
    rewrite (Int64.unsigned_repr l1), (Int64.unsigned_repr l2), (Int64.unsigned_repr (l1 + l2)),
      (Int64.unsigned_repr l3), (Int64.unsigned_repr (l1 + l2 + l3)), (Int64.unsigned_repr 6),
      (Int64.unsigned_repr (l1 + l2 + l3 + 6)), (Int64.unsigned_repr (Zlength s)) by rep_lia.
    f_equal; lia. }
  rewrite Hseg, Hl4. clear Hseg Hl4.
  set (seg := (n + 3) / 4).
  assert (Hsegb: 3 * seg <= n /\ n <= 4 * seg /\ 2 <= seg).
  { subst seg. pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)). lia. }
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward. rewrite oadd_uchar_long by auto. rewrite offset_offset_val.
  forward. forward. forward. forward.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res)))).
  { memcpy_ok_B. }
  forward. { entailer!. simpl; rep_lia. }
  forward.
  forward_if.
  { forward. Exists (Int64.max_unsigned - 19) oc. entailer!.
    - assert (Hnf: Zlength s < l1 + l2 + l3 + 6).
      { destruct (Z_lt_le_dec (Zlength s) (l1 + l2 + l3 + 6)) as [?|Hge]; auto.
        unfold Int64.ltu in H9. rewrite !Int64.unsigned_repr in H9 by rep_lia. destruct zlt in H9; [lia|discriminate]. }
      rewrite err_20. split3; [apply out_after_refl | discriminate |].
      split; [|split; [change (negb true) with false; rewrite x4_exact_split by (auto; lia); reflexivity | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. lia.
    - rewrite (win_split sh (Zlength c) c off s base) by auto.
      first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel. }
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc ob _ _ TT)]; [cancel | | lia | lia | lia].
    auto with share. }
  { rewrite (sem_cmp_gt_offsets (Zlength oc)) in H10 by (auto; lia). simpl in H10.
    destruct (d + n <? d + seg + seg + seg) eqn:E; [rewrite Z.ltb_lt in E; lia | inv H10]. }
  assert (Hfit: l1 + l2 + l3 + 6 <= Zlength s).
  { unfold Int64.ltu in H9. destruct zlt as [|Hge]; [discriminate|].
    rewrite (Int64.unsigned_repr (Zlength s)) in Hge by rep_lia.
    destruct (Z_le_gt_dec (l1 + l2 + l3 + 6) (Zlength s)) as [|Hgt]; auto.
    rewrite Int64.unsigned_repr_eq in Hge.
    rewrite <- (Z.mod_unique (Zlength s - (l1 + l2 + l3 + 6)) Int64.modulus (-1)
               (Zlength s - (l1 + l2 + l3 + 6) + Int64.modulus)) in Hge by rep_lia.
    rep_lia. }
  clear H9 H10.
  set (s1 := sublist 6 (6 + l1) s). set (s2 := sublist (6 + l1) (6 + l1 + l2) s).
  set (s3 := sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s). set (s4 := sublist (6 + l1 + l2 + l3) (Zlength s) s).
  destruct (bs_wf s1) eqn:Hw1.
  2:{ dw0. 2: apply semax_ff.
    apply -> seq_assoc. forward_call (Tsh, v_bitD1, sh, offset_val off base, s, 6, l1, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s1; rewrite Hw1. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; congruence).
      all: try solve [x4_init_none Hfit ltac:(left)].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel. }
  dw0.
  { apply -> seq_assoc. forward_call (Tsh, v_bitD1, sh, offset_val off base, s, 6, l1, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s1; rewrite Hw1. x4_chk_ok l1. }
  destruct (bs_wf s2) eqn:Hw2.
  2:{ dw0. 2: apply semax_ff.
    apply -> seq_assoc. forward_call (Tsh, v_bitD2, sh, offset_val off base, s, (6 + l1), l2, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s2; rewrite Hw2. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; congruence).
      all: try solve [x4_init_none Hfit ltac:(right; left)].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel. }
  dw0.
  { apply -> seq_assoc. forward_call (Tsh, v_bitD2, sh, offset_val off base, s, (6 + l1), l2, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s2; rewrite Hw2. x4_chk_ok l2. }
  destruct (bs_wf s3) eqn:Hw3.
  2:{ dw0. 2: apply semax_ff.
    apply -> seq_assoc. forward_call (Tsh, v_bitD3, sh, offset_val off base, s, (6 + l1 + l2), l3, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s3; rewrite Hw3. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; congruence).
      all: try solve [x4_init_none Hfit ltac:(right; right; left)].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel. }
  dw0.
  { apply -> seq_assoc. forward_call (Tsh, v_bitD3, sh, offset_val off base, s, (6 + l1 + l2), l3, gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    fold s3; rewrite Hw3. x4_chk_ok l3. }
  destruct (bs_wf s4) eqn:Hw4.
  2:{ dw0. 2: apply semax_ff.
    apply -> seq_assoc. forward_call (Tsh, v_bitD4, sh, offset_val off base, s, (6 + l1 + l2 + l3), (Zlength s - (l1 + l2 + l3 + 6)), gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    replace (6 + l1 + l2 + l3 + (Zlength s - (l1 + l2 + l3 + 6))) with (Zlength s) by lia. fold s4; rewrite Hw4. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; congruence).
      all: try solve [x4_init_none Hfit ltac:(right; right; right)].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel. }
  dw0.
  { apply -> seq_assoc. forward_call (Tsh, v_bitD4, sh, offset_val off base, s, (6 + l1 + l2 + l3), (Zlength s - (l1 + l2 + l3 + 6)), gv).
    all: try solve [entailer!; rewrite !Z.add_assoc; reflexivity]. all: try solve [apply Forall_sublist; auto].
    replace (6 + l1 + l2 + l3 + (Zlength s - (l1 + l2 + l3 + 6))) with (Zlength s) by lia. fold s4; rewrite Hw4. x4_chk_ok (Zlength s - (l1 + l2 + l3 + 6)). }
  deadvars!.
  assert (Hb1: bytes_ok s1) by (apply Forall_sublist; auto).
  assert (Hb2: bytes_ok s2) by (apply Forall_sublist; auto).
  assert (Hb3: bytes_ok s3) by (apply Forall_sublist; auto).
  assert (Hb4: bytes_ok s4) by (apply Forall_sublist; auto).
  assert (I1 := x4_sinv_init ht s1 seg Hw1 Hb1).
  assert (I2 := x4_sinv_init ht s2 seg Hw2 Hb2).
  assert (I3 := x4_sinv_init ht s3 seg Hw3 Hb3).
  assert (I4 := x4_sinv_init ht s4 (n - 3 * seg) Hw4 Hb4).
  replace (Zlength s1) with l1 in I1 by (unfold s1; rewrite Zlength_sublist; lia).
  replace (Zlength s2) with l2 in I2 by (unfold s2; rewrite Zlength_sublist; lia).
  replace (Zlength s3) with l3 in I3 by (unfold s3; rewrite Zlength_sublist; lia).
  replace (Zlength s4) with (Zlength s - (l1 + l2 + l3 + 6)) in I4 by (unfold s4; rewrite Zlength_sublist; lia).
  set (st1 := offset_val 6 (offset_val off base)).
  set (st2 := offset_val (6 + l1) (offset_val off base)).
  set (st3 := offset_val (6 + l1 + l2) (offset_val off base)).
  set (st4 := offset_val (6 + l1 + l2 + l3) (offset_val off base)).
  subst N.
  assert (LP1: (8 * Z.max 0 (l1 - 8)) <= bs_total s1) by (destruct I1 as (_ & _ & _ & _ & He & _); destruct (He eq_refl); assumption).
  sep_apply (BIT_DStream_rep_rep_np Tsh gv s1 st1 (bs_total s1) (8 * Z.max 0 (l1 - 8)) v_bitD1 LP1).
  assert (LP2: (8 * Z.max 0 (l2 - 8)) <= bs_total s2) by (destruct I2 as (_ & _ & _ & _ & He & _); destruct (He eq_refl); assumption).
  sep_apply (BIT_DStream_rep_rep_np Tsh gv s2 st2 (bs_total s2) (8 * Z.max 0 (l2 - 8)) v_bitD2 LP2).
  assert (LP3: (8 * Z.max 0 (l3 - 8)) <= bs_total s3) by (destruct I3 as (_ & _ & _ & _ & He & _); destruct (He eq_refl); assumption).
  sep_apply (BIT_DStream_rep_rep_np Tsh gv s3 st3 (bs_total s3) (8 * Z.max 0 (l3 - 8)) v_bitD3 LP3).
  assert (LP4: (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8)) <= bs_total s4) by (destruct I4 as (_ & _ & _ & _ & He & _); destruct (He eq_refl); assumption).
  sep_apply (BIT_DStream_rep_rep_np Tsh gv s4 st4 (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8)) v_bitD4 LP4).
  set (D1 := xb_of s1 (bs_total s1) (8 * Z.max 0 (l1 - 8))).
  set (D2 := xb_of s2 (bs_total s2) (8 * Z.max 0 (l2 - 8))).
  set (D3 := xb_of s3 (bs_total s3) (8 * Z.max 0 (l3 - 8))).
  set (D4 := xb_of s4 (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8))).
  assert (I1x: xb_init s1 = Some D1) by (apply x4_init_some; auto; unfold s1; rewrite Zlength_sublist; lia).
  assert (I2x: xb_init s2 = Some D2) by (apply x4_init_some; auto; unfold s2; rewrite Zlength_sublist; lia).
  assert (I3x: xb_init s3 = Some D3) by (apply x4_init_some; auto; unfold s3; rewrite Zlength_sublist; lia).
  assert (I4x: xb_init s4 = Some D4) by (apply x4_init_some; auto; unfold s4; rewrite Zlength_sublist; lia).
  set (RL := xh_loop4s (Z.to_nat n + 1) (x4_dec4 ht) (n - 3 - 3 * seg) s1 s2 s3 s4 D1 D2 D3 D4 [] [] [] []).
  set (R0 := x4_run ht n seg s1 s2 s3 s4 D1 D2 D3 D4).
  forward_if (EX m: Z, EX w1: list Z, EX w2: list Z, EX w3: list Z, EX w4: list Z,
     EX p1: Z, EX o1: Z, EX p2: Z, EX o2: Z, EX p3: Z, EX o3: Z, EX p4: Z, EX o4: Z, EX es: Z, EX oc': list val,
     PROP (0 <= m; 3 * seg + 4 * m <= n; es = 0 \/ es = 1;
           x4_sinv ht s1 seg m w1 p1 o1 es; x4_sinv ht s2 seg m w2 p2 o2 es;
           x4_sinv ht s3 seg m w3 p3 o3 es; x4_sinv ht s4 (n - 3 * seg) m w4 p4 o4 es;
           x4_out oc oc' (x4_segs d seg w1 w2 w3 w4);
           R0 = ((xb_of s1 p1 o1, xb_of s2 p2 o2, xb_of s3 p3 o3, xb_of s4 p4 o4), (w1, w2, w3, w4)))
     LOCAL (temp _endSignal (Vint (Int.repr es)); temp _dtLog (Vint (Int.repr L));
       temp _op4 (offset_val (d + seg + seg + seg + 4 * m) ob); temp _op3 (offset_val (d + seg + seg + 4 * m) ob);
       temp _op2 (offset_val (d + seg + 4 * m) ob); temp _op1 (offset_val (d + 4 * m) ob);
       temp _opStart4 (offset_val (d + seg + seg + seg) ob); temp _opStart3 (offset_val (d + seg + seg) ob);
       temp _opStart2 (offset_val (d + seg) ob); temp _dt (offset_val 4 dt);
       temp _olimit (offset_val (d + (n + - (3))) ob); temp _oend (offset_val (d + n) ob);
       lvar _dtd (Tstruct ___gp_DTableDesc noattr) v_dtd; lvar _bitD4 t_bitD v_bitD4;
       lvar _bitD3 t_bitD v_bitD3; lvar _bitD2 t_bitD v_bitD2; lvar _bitD1 t_bitD v_bitD1;
       gvars gv; temp _dstSize (Vlong (Int64.repr n)))
     SEP (BIT_DStream_rep_g true Tsh gv s4 st4 p4 o4 v_bitD4; bit_src sh (offset_val off base) s; zstd_globals gv;
       BIT_DStream_rep_g true Tsh gv s3 st3 p3 o3 v_bitD3; BIT_DStream_rep_g true Tsh gv s2 st2 p2 o2 v_bitD2;
       BIT_DStream_rep_g true Tsh gv s1 st1 p1 o1 v_bitD1;
       data_at Tsh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) v_dtd;
       data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) dt;
       data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 dt);
       memory_block sht (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) dt);
       data_at sho (tarray tuchar (Zlength oc)) oc' ob;
       data_at sh (tarray tuchar off) (sublist 0 off c) base;
       data_at sh (tarray tuchar (Zlength c - (off + Zlength s))) (sublist (off + Zlength s) (Zlength c) c) (offset_val (off + Zlength s) base)))%assert.
  { entailer!. rewrite sameblock_offset_val by auto. reflexivity. }
  { assert (H8s: 8 <= n - 3 * seg).
    { rewrite (x4_size_cmp (Zlength oc)) in H9 by (auto; lia).
      destruct (8 <=? d + n - (d + seg + seg + seg)) eqn:E; [apply Z.leb_le in E; lia | inv H9]. }
    forward_while (EX m: Z, EX w1: list Z, EX w2: list Z, EX w3: list Z, EX w4: list Z,
     EX p1: Z, EX o1: Z, EX p2: Z, EX o2: Z, EX p3: Z, EX o3: Z, EX p4: Z, EX o4: Z, EX es: Z, EX oc': list val,
     PROP (0 <= m; 3 * seg + 4 * m <= n; es = 0 \/ es = 1;
           x4_sinv ht s1 seg m w1 p1 o1 es; x4_sinv ht s2 seg m w2 p2 o2 es;
           x4_sinv ht s3 seg m w3 p3 o3 es; x4_sinv ht s4 (n - 3 * seg) m w4 p4 o4 es;
           x4_out oc oc' (x4_segs d seg w1 w2 w3 w4);
           x4_lp ht (n - 3 - 3 * seg) s1 s2 s3 s4 RL (Z.to_nat (n + 1 - m)) p1 o1 p2 o2 p3 o3 p4 o4 w1 w2 w3 w4 es)
     LOCAL (temp _endSignal (Vint (Int.repr es)); temp _dtLog (Vint (Int.repr L));
       temp _op4 (offset_val (d + seg + seg + seg + 4 * m) ob); temp _op3 (offset_val (d + seg + seg + 4 * m) ob);
       temp _op2 (offset_val (d + seg + 4 * m) ob); temp _op1 (offset_val (d + 4 * m) ob);
       temp _opStart4 (offset_val (d + seg + seg + seg) ob); temp _opStart3 (offset_val (d + seg + seg) ob);
       temp _opStart2 (offset_val (d + seg) ob); temp _dt (offset_val 4 dt);
       temp _olimit (offset_val (d + (n + - (3))) ob); temp _oend (offset_val (d + n) ob);
       lvar _dtd (Tstruct ___gp_DTableDesc noattr) v_dtd; lvar _bitD4 t_bitD v_bitD4;
       lvar _bitD3 t_bitD v_bitD3; lvar _bitD2 t_bitD v_bitD2; lvar _bitD1 t_bitD v_bitD1;
       gvars gv; temp _dstSize (Vlong (Int64.repr n)))
     SEP (BIT_DStream_rep_g true Tsh gv s4 st4 p4 o4 v_bitD4; bit_src sh (offset_val off base) s; zstd_globals gv;
       BIT_DStream_rep_g true Tsh gv s3 st3 p3 o3 v_bitD3; BIT_DStream_rep_g true Tsh gv s2 st2 p2 o2 v_bitD2;
       BIT_DStream_rep_g true Tsh gv s1 st1 p1 o1 v_bitD1;
       data_at Tsh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) v_dtd;
       data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) dt;
       data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 dt);
       memory_block sht (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) dt);
       data_at sho (tarray tuchar (Zlength oc)) oc' ob;
       data_at sh (tarray tuchar off) (sublist 0 off c) base;
       data_at sh (tarray tuchar (Zlength c - (off + Zlength s))) (sublist (off + Zlength s) (Zlength c) c) (offset_val (off + Zlength s) base)))%assert.
    - Exists 0 (@nil Z) (@nil Z) (@nil Z) (@nil Z). Exists (bs_total s1) (8 * Z.max 0 (l1 - 8))%Z (bs_total s2) (8 * Z.max 0 (l2 - 8))%Z.
      Exists (bs_total s3) (8 * Z.max 0 (l3 - 8))%Z (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8))%Z 1 oc.
    rewrite !Z.mul_0_r, !Z.add_0_r. entailer!.
    all: try (split; [apply x4_out_init; repeat constructor|]).
    all: try (match goal with |- x4_lp _ _ _ _ _ _ _ (Z.to_nat ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                replace e with (n + 1 - 0) by lia end; apply x4_lp_init; lia).
    all: cbv beta iota delta [BIT_DStream_rep_g]; cancel.
    - entailer!.
      eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob _ _ TT)]; [cancel | | lia | lia | lia].
      auto with share.
    - (* the loop body *)
      apply x4_loop_cond with (len := Zlength oc) in HRE; [| auto | lia | lia | auto].
      destruct HRE as [-> Hlt].
      assert (M1 := x4_mid_start _ _ _ _ _ _ _ H13 ltac:(lia)).
      assert (M2 := x4_mid_start _ _ _ _ _ _ _ H14 ltac:(lia)).
      assert (M3 := x4_mid_start _ _ _ _ _ _ _ H15 ltac:(lia)).
      assert (M4 := x4_mid_start _ _ _ _ _ _ _ H16 ltac:(lia)).
      assert (Z1: (Zlength w1 = 4 * m)%Z) by (destruct H13; lia).
      assert (Z2: (Zlength w2 = 4 * m)%Z) by (destruct H14; lia).
      assert (Z3: (Zlength w3 = 4 * m)%Z) by (destruct H15; lia).
      assert (Z4: (Zlength w4 = 4 * m)%Z) by (destruct H16; lia).
      set (BS := fun (wt1 wt2 wt3 wt4: list Z) (q1 q2 q3 q4: Z) (oc2: list val) =>
       (PROP (x4_mid ht s1 seg m (Zlength wt1 - 4 * m) wt1 q1 o1; x4_mid ht s2 seg m (Zlength wt2 - 4 * m) wt2 q2 o2;
              x4_mid ht s3 seg m (Zlength wt3 - 4 * m) wt3 q3 o3;
              x4_mid ht s4 (n - 3 * seg) m (Zlength wt4 - 4 * m) wt4 q4 o4;
              x4_out oc oc2 (x4_segs d seg wt1 wt2 wt3 wt4);
              x4_mxw ht s1 p1 o1 w1 wt1 q1; x4_mxw ht s2 p2 o2 w2 wt2 q2;
              x4_mxw ht s3 p3 o3 w3 wt3 q3; x4_mxw ht s4 p4 o4 w4 wt4 q4)
        LOCAL (temp _endSignal (Vint (Int.repr 1)); temp _dtLog (Vint (Int.repr L));
          temp _op4 (offset_val (d + seg + seg + seg + Zlength wt4) ob); temp _op3 (offset_val (d + seg + seg + Zlength wt3) ob);
          temp _op2 (offset_val (d + seg + Zlength wt2) ob); temp _op1 (offset_val (d + Zlength wt1) ob);
          temp _opStart4 (offset_val (d + seg + seg + seg) ob); temp _opStart3 (offset_val (d + seg + seg) ob);
          temp _opStart2 (offset_val (d + seg) ob); temp _dt (offset_val 4 dt);
          temp _olimit (offset_val (d + (n + - (3))) ob); temp _oend (offset_val (d + n) ob);
          lvar _dtd (Tstruct ___gp_DTableDesc noattr) v_dtd; lvar _bitD4 t_bitD v_bitD4;
          lvar _bitD3 t_bitD v_bitD3; lvar _bitD2 t_bitD v_bitD2; lvar _bitD1 t_bitD v_bitD1;
          gvars gv; temp _dstSize (Vlong (Int64.repr n)))
        SEP (BIT_DStream_rep_g true Tsh gv s4 st4 q4 o4 v_bitD4; bit_src sh (offset_val off base) s; zstd_globals gv;
          BIT_DStream_rep_g true Tsh gv s3 st3 q3 o3 v_bitD3; BIT_DStream_rep_g true Tsh gv s2 st2 q2 o2 v_bitD2;
          BIT_DStream_rep_g true Tsh gv s1 st1 q1 o1 v_bitD1;
          @data_at CompSpecs Tsh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) v_dtd;
          @data_at CompSpecs sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 0), (Vint (Int.repr L), res))) dt;
          @data_at CompSpecs sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 dt);
          memory_block sht (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) dt);
          @data_at CompSpecs sho (tarray tuchar (Zlength oc)) oc2 ob;
          @data_at CompSpecs sh (tarray tuchar off) (sublist 0 off c) base;
          @data_at CompSpecs sh (tarray tuchar (Zlength c - (off + Zlength s))) (sublist (off + Zlength s) (Zlength c) c)
            (offset_val (off + Zlength s) base)))%assert).
      apply semax_pre with (BS w1 w2 w3 w4 p1 p2 p3 p4 oc').
      { unfold BS. rewrite Z1, Z2, Z3, Z4, Z.sub_diag. entailer!. all: repeat split; first [apply x4_mxw_start | assumption]. }
      (* decode 1: stream 1, symbol 0 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w1 + 1) && BS w w2 w3 w4 q p2 p3 p4 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD1, gv, s1, st1, p1, o1, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s1 _ _ _ w1 p1 o1 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + Zlength w1) ob)
            by (auto; match goal with Hm: x4_mid ht s1 _ _ _ w1 p1 o1 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w1 ++ [fst (hsym ht L v)]) (p1 - snd (hsym ht L v))
            (upd_Znth (d + Zlength w1) oc' (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w1 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc' [] [(d + seg, w2); (d + seg + seg, w3); (d + seg + seg + seg, w4)] (d) w1 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w1_1 p1_1 oc_1. apply semax_extract_prop; intro.
      assert (Z1_1: (Zlength w1_1 = 4 * m + 1)%Z) by lia.
      (* decode 2: stream 2, symbol 0 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w2 + 1) && BS w1_1 w w3 w4 p1_1 q p3 p4 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD2, gv, s2, st2, p2, o2, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s2 _ _ _ w2 p2 o2 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + Zlength w2) ob)
            by (auto; match goal with Hm: x4_mid ht s2 _ _ _ w2 p2 o2 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w2 ++ [fst (hsym ht L v)]) (p2 - snd (hsym ht L v))
            (upd_Znth (d + seg + Zlength w2) oc_1 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w2 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_1 [(d, w1_1)] [(d + seg + seg, w3); (d + seg + seg + seg, w4)] (d + seg) w2 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w2_1 p2_1 oc_2. apply semax_extract_prop; intro.
      assert (Z2_1: (Zlength w2_1 = 4 * m + 1)%Z) by lia.
      (* decode 3: stream 3, symbol 0 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w3 + 1) && BS w1_1 w2_1 w w4 p1_1 p2_1 q p4 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD3, gv, s3, st3, p3, o3, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s3 _ _ _ w3 p3 o3 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + Zlength w3) ob)
            by (auto; match goal with Hm: x4_mid ht s3 _ _ _ w3 p3 o3 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w3 ++ [fst (hsym ht L v)]) (p3 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + Zlength w3) oc_2 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w3 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_2 [(d, w1_1); (d + seg, w2_1)] [(d + seg + seg + seg, w4)] (d + seg + seg) w3 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w3_1 p3_1 oc_3. apply semax_extract_prop; intro.
      assert (Z3_1: (Zlength w3_1 = 4 * m + 1)%Z) by lia.
      (* decode 4: stream 4, symbol 0 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w4 + 1) && BS w1_1 w2_1 w3_1 w p1_1 p2_1 p3_1 q oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD4, gv, s4, st4, p4, o4, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s4 _ _ _ w4 p4 o4 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + seg + Zlength w4) ob)
            by (auto; match goal with Hm: x4_mid ht s4 _ _ _ w4 p4 o4 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w4 ++ [fst (hsym ht L v)]) (p4 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + seg + Zlength w4) oc_3 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w4 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_3 [(d, w1_1); (d + seg, w2_1); (d + seg + seg, w3_1)] [] (d + seg + seg + seg) w4 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w4_1 p4_1 oc_4. apply semax_extract_prop; intro.
      assert (Z4_1: (Zlength w4_1 = 4 * m + 1)%Z) by lia.
      (* decode 5: stream 1, symbol 1 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w1_1 + 1) && BS w w2_1 w3_1 w4_1 q p2_1 p3_1 p4_1 oc3).
      { unfold BS. Intros. forward_call tt. apply semax_if_seq. forward_if.
        - forward. forward_if.
          2: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
          apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD1, gv, s1, st1, p1_1, o1, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s1 _ _ _ w1_1 p1_1 o1 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + Zlength w1_1) ob)
            by (auto; match goal with Hm: x4_mid ht s1 _ _ _ w1_1 p1_1 o1 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w1_1 ++ [fst (hsym ht L v)]) (p1_1 - snd (hsym ht L v))
            (upd_Znth (d + Zlength w1_1) oc_4 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w1_1 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_4 [] [(d + seg, w2_1); (d + seg + seg, w3_1); (d + seg + seg + seg, w4_1)] (d) w1_1 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w1_2 p1_2 oc_5. apply semax_extract_prop; intro.
      assert (Z1_2: (Zlength w1_2 = 4 * m + 2)%Z) by lia.
      (* decode 6: stream 2, symbol 1 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w2_1 + 1) && BS w1_2 w w3_1 w4_1 p1_2 q p3_1 p4_1 oc3).
      { unfold BS. Intros. forward_call tt. apply semax_if_seq. forward_if.
        - forward. forward_if.
          2: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
          apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD2, gv, s2, st2, p2_1, o2, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s2 _ _ _ w2_1 p2_1 o2 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + Zlength w2_1) ob)
            by (auto; match goal with Hm: x4_mid ht s2 _ _ _ w2_1 p2_1 o2 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w2_1 ++ [fst (hsym ht L v)]) (p2_1 - snd (hsym ht L v))
            (upd_Znth (d + seg + Zlength w2_1) oc_5 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w2_1 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_5 [(d, w1_2)] [(d + seg + seg, w3_1); (d + seg + seg + seg, w4_1)] (d + seg) w2_1 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w2_2 p2_2 oc_6. apply semax_extract_prop; intro.
      assert (Z2_2: (Zlength w2_2 = 4 * m + 2)%Z) by lia.
      (* decode 7: stream 3, symbol 1 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w3_1 + 1) && BS w1_2 w2_2 w w4_1 p1_2 p2_2 q p4_1 oc3).
      { unfold BS. Intros. forward_call tt. apply semax_if_seq. forward_if.
        - forward. forward_if.
          2: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
          apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD3, gv, s3, st3, p3_1, o3, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s3 _ _ _ w3_1 p3_1 o3 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + Zlength w3_1) ob)
            by (auto; match goal with Hm: x4_mid ht s3 _ _ _ w3_1 p3_1 o3 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w3_1 ++ [fst (hsym ht L v)]) (p3_1 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + Zlength w3_1) oc_6 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w3_1 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_6 [(d, w1_2); (d + seg, w2_2)] [(d + seg + seg + seg, w4_1)] (d + seg + seg) w3_1 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w3_2 p3_2 oc_7. apply semax_extract_prop; intro.
      assert (Z3_2: (Zlength w3_2 = 4 * m + 2)%Z) by lia.
      (* decode 8: stream 4, symbol 1 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w4_1 + 1) && BS w1_2 w2_2 w3_2 w p1_2 p2_2 p3_2 q oc3).
      { unfold BS. Intros. forward_call tt. apply semax_if_seq. forward_if.
        - forward. forward_if.
          2: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
          apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD4, gv, s4, st4, p4_1, o4, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s4 _ _ _ w4_1 p4_1 o4 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + seg + Zlength w4_1) ob)
            by (auto; match goal with Hm: x4_mid ht s4 _ _ _ w4_1 p4_1 o4 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w4_1 ++ [fst (hsym ht L v)]) (p4_1 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + seg + Zlength w4_1) oc_7 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w4_1 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_7 [(d, w1_2); (d + seg, w2_2); (d + seg + seg, w3_2)] [] (d + seg + seg + seg) w4_1 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w4_2 p4_2 oc_8. apply semax_extract_prop; intro.
      assert (Z4_2: (Zlength w4_2 = 4 * m + 2)%Z) by lia.
      (* decode 9: stream 1, symbol 2 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w1_2 + 1) && BS w w2_2 w3_2 w4_2 q p2_2 p3_2 p4_2 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD1, gv, s1, st1, p1_2, o1, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s1 _ _ _ w1_2 p1_2 o1 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + Zlength w1_2) ob)
            by (auto; match goal with Hm: x4_mid ht s1 _ _ _ w1_2 p1_2 o1 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w1_2 ++ [fst (hsym ht L v)]) (p1_2 - snd (hsym ht L v))
            (upd_Znth (d + Zlength w1_2) oc_8 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w1_2 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_8 [] [(d + seg, w2_2); (d + seg + seg, w3_2); (d + seg + seg + seg, w4_2)] (d) w1_2 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w1_3 p1_3 oc_9. apply semax_extract_prop; intro.
      assert (Z1_3: (Zlength w1_3 = 4 * m + 3)%Z) by lia.
      (* decode 10: stream 2, symbol 2 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w2_2 + 1) && BS w1_3 w w3_2 w4_2 p1_3 q p3_2 p4_2 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD2, gv, s2, st2, p2_2, o2, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s2 _ _ _ w2_2 p2_2 o2 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + Zlength w2_2) ob)
            by (auto; match goal with Hm: x4_mid ht s2 _ _ _ w2_2 p2_2 o2 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w2_2 ++ [fst (hsym ht L v)]) (p2_2 - snd (hsym ht L v))
            (upd_Znth (d + seg + Zlength w2_2) oc_9 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w2_2 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_9 [(d, w1_3)] [(d + seg + seg, w3_2); (d + seg + seg + seg, w4_2)] (d + seg) w2_2 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w2_3 p2_3 oc_10. apply semax_extract_prop; intro.
      assert (Z2_3: (Zlength w2_3 = 4 * m + 3)%Z) by lia.
      (* decode 11: stream 3, symbol 2 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w3_2 + 1) && BS w1_3 w2_3 w w4_2 p1_3 p2_3 q p4_2 oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD3, gv, s3, st3, p3_2, o3, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s3 _ _ _ w3_2 p3_2 o3 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + Zlength w3_2) ob)
            by (auto; match goal with Hm: x4_mid ht s3 _ _ _ w3_2 p3_2 o3 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w3_2 ++ [fst (hsym ht L v)]) (p3_2 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + Zlength w3_2) oc_10 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w3_2 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_10 [(d, w1_3); (d + seg, w2_3)] [(d + seg + seg + seg, w4_2)] (d + seg + seg) w3_2 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w3_3 p3_3 oc_11. apply semax_extract_prop; intro.
      assert (Z3_3: (Zlength w3_3 = 4 * m + 3)%Z) by lia.
      (* decode 12: stream 4, symbol 2 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w4_2 + 1) && BS w1_3 w2_3 w3_3 w p1_3 p2_3 p3_3 q oc3).
      { unfold BS. Intros. forward_call tt. forward_if.
        - apply semax_dw0_n. abbreviate_semax.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD4, gv, s4, st4, p4_2, o4, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s4 _ _ _ w4_2 p4_2 o4 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + seg + Zlength w4_2) ob)
            by (auto; match goal with Hm: x4_mid ht s4 _ _ _ w4_2 p4_2 o4 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w4_2 ++ [fst (hsym ht L v)]) (p4_2 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + seg + Zlength w4_2) oc_11 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w4_2 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_11 [(d, w1_3); (d + seg, w2_3); (d + seg + seg, w3_3)] [] (d + seg + seg + seg) w4_2 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia).
        - exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end. }
      Intros w4_3 p4_3 oc_12. apply semax_extract_prop; intro.
      assert (Z4_3: (Zlength w4_3 = 4 * m + 3)%Z) by lia.
      (* decode 13: stream 1, symbol 3 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w1_3 + 1) && BS w w2_3 w3_3 w4_3 q p2_3 p3_3 p4_3 oc3).
      { unfold BS. Intros.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD1, gv, s1, st1, p1_3, o1, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s1 _ _ _ w1_3 p1_3 o1 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + Zlength w1_3) ob)
            by (auto; match goal with Hm: x4_mid ht s1 _ _ _ w1_3 p1_3 o1 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w1_3 ++ [fst (hsym ht L v)]) (p1_3 - snd (hsym ht L v))
            (upd_Znth (d + Zlength w1_3) oc_12 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w1_3 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_12 [] [(d + seg, w2_3); (d + seg + seg, w3_3); (d + seg + seg + seg, w4_3)] (d) w1_3 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia). }
      Intros w1_4 p1_4 oc_13. apply semax_extract_prop; intro.
      assert (Z1_4: (Zlength w1_4 = 4 * m + 4)%Z) by lia.
      (* decode 14: stream 2, symbol 3 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w2_3 + 1) && BS w1_4 w w3_3 w4_3 p1_4 q p3_3 p4_3 oc3).
      { unfold BS. Intros.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD2, gv, s2, st2, p2_3, o2, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s2 _ _ _ w2_3 p2_3 o2 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + Zlength w2_3) ob)
            by (auto; match goal with Hm: x4_mid ht s2 _ _ _ w2_3 p2_3 o2 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w2_3 ++ [fst (hsym ht L v)]) (p2_3 - snd (hsym ht L v))
            (upd_Znth (d + seg + Zlength w2_3) oc_13 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w2_3 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_13 [(d, w1_4)] [(d + seg + seg, w3_3); (d + seg + seg + seg, w4_3)] (d + seg) w2_3 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia). }
      Intros w2_4 p2_4 oc_14. apply semax_extract_prop; intro.
      assert (Z2_4: (Zlength w2_4 = 4 * m + 4)%Z) by lia.
      (* decode 15: stream 3, symbol 3 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w3_3 + 1) && BS w1_4 w2_4 w w4_3 p1_4 p2_4 q p4_3 oc3).
      { unfold BS. Intros.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD3, gv, s3, st3, p3_3, o3, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s3 _ _ _ w3_3 p3_3 o3 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + Zlength w3_3) ob)
            by (auto; match goal with Hm: x4_mid ht s3 _ _ _ w3_3 p3_3 o3 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w3_3 ++ [fst (hsym ht L v)]) (p3_3 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + Zlength w3_3) oc_14 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w3_3 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_14 [(d, w1_4); (d + seg, w2_4)] [(d + seg + seg + seg, w4_3)] (d + seg + seg) w3_3 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia). }
      Intros w3_4 p3_4 oc_15. apply semax_extract_prop; intro.
      assert (Z3_4: (Zlength w3_4 = 4 * m + 4)%Z) by lia.
      (* decode 16: stream 4, symbol 3 of the iteration *)
      dw0q (EX w: list Z, EX q: Z, EX oc3: list val, !!(Zlength w = Zlength w4_3 + 1) && BS w1_4 w2_4 w3_4 w p1_4 p2_4 p3_4 q oc3).
      { unfold BS. Intros.
          forward. forward. rewrite oadd_uchar_int by (auto; rep_lia). rewrite offset_offset_val.
          forward_call (Tsh, v_bitD4, gv, s4, st4, p4_3, o4, sht, offset_val 4 dt, ht, L, true).
          { match goal with Hm: x4_mid ht s4 _ _ _ w4_3 p4_3 o4 |- _ => destruct Hm as (_&_&_&?&_&?&_&_) end. rep_lia. }
          Intros v.
          rewrite (off_fa (Zlength oc) (d + seg + seg + seg + Zlength w4_3) ob)
            by (auto; match goal with Hm: x4_mid ht s4 _ _ _ w4_3 p4_3 o4 |- _ => destruct Hm as (?&_&?&?&_) end; lia).
          forward.
          destruct (hsym_range ht L v H5 ltac:(lia) ltac:(assumption)) as [Hb Hn].
          rewrite (zext_byte (fst (hsym ht L v))) by lia.
          x4_mx_pre v.
          Exists (w4_3 ++ [fst (hsym ht L v)]) (p4_3 - snd (hsym ht L v))
            (upd_Znth (d + seg + seg + seg + Zlength w4_3) oc_15 (Vint (Int.repr (fst (hsym ht L v))))).
          unfold BS. rewrite Zlength_app, Zlength_cons, Zlength_nil. entailer!.
          repeat match goal with |- _ /\ _ => split end; try lia.
          all: try (match goal with |- x4_mid _ _ _ _ ?t _ _ _ => replace t with (Zlength w4_3 - 4 * m + 1) by lia end;
                    apply x4_mid_step; auto; lia).
          all: try (apply (x4_out_store oc oc_15 [(d, w1_4); (d + seg, w2_4); (d + seg + seg, w3_4)] [] (d + seg + seg + seg) w4_3 _); [assumption | lia | lia |];
                    intros sw Hin; simpl in Hin; repeat destruct Hin as [<-|Hin]; simpl; try lia; contradiction).
          all: try (f_equal; lia). }
      Intros w4_4 p4_4 oc_16. apply semax_extract_prop; intro.
      assert (Z4_4: (Zlength w4_4 = 4 * m + 4)%Z) by lia.
      (* the 4 reloads *)
      unfold BS. Intros.
      change (BIT_DStream_rep_g true) with BIT_DStream_rep_np.
      assert_PROP (bit_inv s1 p1_4 o1 /\ bit_inv s2 p2_4 o2 /\ bit_inv s3 p3_4 o3 /\ bit_inv s4 p4_4 o4) as Hbi.
      { unfold BIT_DStream_rep_np. Intros lm1 lm2 lm3 lm4. entailer!. }
      destruct Hbi as (Bi1 & Bi2 & Bi3 & Bi4).
      match goal with Hl: x4_lp _ _ _ _ _ _ _ (Z.to_nat _) _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        rewrite (x4_fuel n m) in Hl by lia; rename Hl into HLP end.
      assert (R1: x4_mid ht s1 seg m 4 w1_4 p1_4 o1) by (replace 4 with (Zlength w1_4 - 4 * m) by lia; assumption).
      assert (R2: x4_mid ht s2 seg m 4 w2_4 p2_4 o2) by (replace 4 with (Zlength w2_4 - 4 * m) by lia; assumption).
      assert (R3: x4_mid ht s3 seg m 4 w3_4 p3_4 o3) by (replace 4 with (Zlength w3_4 - 4 * m) by lia; assumption).
      assert (R4: x4_mid ht s4 (n - 3 * seg) m 4 w4_4 p4_4 o4) by (replace 4 with (Zlength w4_4 - 4 * m) by lia; assumption).
      forward_call (Tsh, v_bitD1, gv, s1, st1, p1_4, o1, sh, offset_val off base, s, 6).
      { split.
        - unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s1; rewrite Zlength_sublist by lia.
          split; [lia|]. f_equal; lia.
        - destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R1) as [? | ->]; [left; assumption | right; lia]. }
      forward.
      forward_call (Tsh, v_bitD2, gv, s2, st2, p2_4, o2, sh, offset_val off base, s, (6 + l1)).
      { split.
        - unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s2; rewrite Zlength_sublist by lia.
          split; [lia|]. f_equal; lia.
        - destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R2) as [? | ->]; [left; assumption | right; lia]. }
      forward.
      forward_call (Tsh, v_bitD3, gv, s3, st3, p3_4, o3, sh, offset_val off base, s, (6 + l1 + l2)).
      { split.
        - unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s3; rewrite Zlength_sublist by lia.
          split; [lia|]. f_equal; lia.
        - destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R3) as [? | ->]; [left; assumption | right; lia]. }
      forward.
      forward_call (Tsh, v_bitD4, gv, s4, st4, p4_4, o4, sh, offset_val off base, s, (6 + l1 + l2 + l3)).
      { split.
        - unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s4; rewrite Zlength_sublist by lia.
          split; [lia|]. f_equal; lia.
        - destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R4) as [? | ->]; [left; assumption | right; lia]. }
      forward.
      rewrite (x4_es_and _ _ _ _ (fst_reload_range _ _) (fst_reload_range _ _) (fst_reload_range _ _) (fst_reload_range _ _)).
      set (ES := x4_es (fst (bs_reload_fast p1_4 o1)) (fst (bs_reload_fast p2_4 o2))
                   (fst (bs_reload_fast p3_4 o3)) (fst (bs_reload_fast p4_4 o4))).
      assert (HES: ES = 1 -> fst (bs_reload_fast p1_4 o1) = BIT_unfinished /\ fst (bs_reload_fast p2_4 o2) = BIT_unfinished /\
                      fst (bs_reload_fast p3_4 o3) = BIT_unfinished /\ fst (bs_reload_fast p4_4 o4) = BIT_unfinished)
        by (intros HE; apply x4_es_1 in HE; unfold BIT_unfinished; exact HE).
      Exists ((m + 1)%Z, w1_4, w2_4, w3_4, w4_4, p1_4, snd (bs_reload_fast p1_4 o1), p2_4, snd (bs_reload_fast p2_4 o2),
              p3_4, snd (bs_reload_fast p3_4 o3), p4_4, snd (bs_reload_fast p4_4 o4), ES, oc_16).
      cbn [fst snd]. rewrite Z1_4, Z2_4, Z3_4, Z4_4. change (BIT_DStream_rep_g true) with BIT_DStream_rep_np. replace (4 * (m + 1))%Z with (4 * m + 4)%Z by lia.
      entailer!.
      repeat match goal with |- _ /\ _ => split end; try lia.
      all: try apply x4_es_01.
      all: try (apply x4_mid_reload; auto; intros HE; apply HES in HE; tauto).
      all: try (eapply x4_lp_step; [exact HLP | lia | eassumption | lia | eassumption | lia | eassumption | lia
                  | eassumption | lia | exact Bi1 | destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R1); lia
                  | exact Bi2 | destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R2); lia
                  | exact Bi3 | destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R3); lia
                  | exact Bi4 | destruct (x4_mid_pre_reload _ _ _ _ _ _ _ R4); lia]).
      all: try (f_equal; lia).
    - assert (Zw4e: (Zlength w4 = 4 * m)%Z) by (match goal with Hs: x4_sinv ht s4 _ _ w4 _ _ _ |- _ => destruct Hs; lia end).
      assert (Hex: (es = 1 -> n - 3 - 3 * seg <= Zlength w4)%Z).
      { intros Hes1. apply x4_loop_cond_false with (len := Zlength oc) in HRE; [| auto | lia | lia | auto]. lia. }
      match goal with Hl: x4_lp _ _ _ _ _ _ _ (Z.to_nat _) _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        rewrite (x4_fuel n m) in Hl by lia; apply x4_lp_exit in Hl; [rename Hl into HLe | exact Hex] end.
      forward. Exists m w1 w2 w3 w4. Exists p1 o1 p2 o2. Exists p3 o3 p4 o4. Exists es oc'. entailer!.
      all: unfold R0, x4_run; rewrite (proj2 (Z.leb_le 8 (n - 3 * seg))) by lia; exact HLe. }
  { assert (H8s: n - 3 * seg < 8).
    { rewrite (x4_size_cmp (Zlength oc)) in H9 by (auto; lia).
      destruct (8 <=? d + n - (d + seg + seg + seg)) eqn:E; [inv H9 | apply Z.leb_gt in E; lia]. }
    forward. Exists 0 (@nil Z) (@nil Z) (@nil Z) (@nil Z). Exists (bs_total s1) (8 * Z.max 0 (l1 - 8))%Z (bs_total s2) (8 * Z.max 0 (l2 - 8))%Z.
      Exists (bs_total s3) (8 * Z.max 0 (l3 - 8))%Z (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8))%Z 1 oc.
    rewrite !Z.mul_0_r, !Z.add_0_r. entailer!.
    all: try (split; [apply x4_out_init; repeat constructor|]).
    all: try (apply x4_out_init; repeat constructor).
    all: try (unfold R0, x4_run; rewrite (proj2 (Z.leb_gt 8 (n - 3 * seg))) by lia; reflexivity).
    all: cbv beta iota delta [BIT_DStream_rep_g]; cancel. }
  Intros m w1 w2 w3 w4. Intros p1 o1 p2 o2. Intros p3 o3 p4 o4. Intros es oc'.
  (* ---------- the epilogue ---------- *)
  Intros.
  change (BIT_DStream_rep_g true) with BIT_DStream_rep_np.
  sep_apply (BIT_DStream_rep_np_rep Tsh gv s1 st1 p1 o1 v_bitD1).
  sep_apply (BIT_DStream_rep_np_rep Tsh gv s2 st2 p2 o2 v_bitD2).
  sep_apply (BIT_DStream_rep_np_rep Tsh gv s3 st3 p3 o3 v_bitD3).
  sep_apply (BIT_DStream_rep_np_rep Tsh gv s4 st4 p4 o4 v_bitD4).
  assert (Zw1: (Zlength w1 = 4 * m)%Z) by (match goal with Hs: x4_sinv ht s1 _ _ w1 _ _ _ |- _ => destruct Hs; lia end).
  assert (Zw2: (Zlength w2 = 4 * m)%Z) by (match goal with Hs: x4_sinv ht s2 _ _ w2 _ _ _ |- _ => destruct Hs; lia end).
  assert (Zw3: (Zlength w3 = 4 * m)%Z) by (match goal with Hs: x4_sinv ht s3 _ _ w3 _ _ _ |- _ => destruct Hs; lia end).
  assert (Zw4: (Zlength w4 = 4 * m)%Z) by (match goal with Hs: x4_sinv ht s4 _ _ w4 _ _ _ |- _ => destruct Hs; lia end).
  assert (Hoc': Zlength oc' = Zlength oc) by (match goal with Ho: x4_out oc oc' _ |- _ => destruct Ho; auto end).
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob _ _ TT)]; [cancel | | lia | lia | lia].
    auto with share. }
  { match goal with Ht: typed_true _ (match sem_cmp_pp _ _ _ with _ => _ end) |- _ =>
      rewrite (sem_cmp_gt_offsets (Zlength oc)) in Ht by (auto; lia); simpl in Ht;
      destruct (d + seg <? d + 4 * m) eqn:E; [rewrite Z.ltb_lt in E; lia | inv Ht] end. }
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob _ _ TT)]; [cancel | | lia | lia | lia].
    auto with share. }
  { match goal with Ht: typed_true _ (match sem_cmp_pp _ _ _ with _ => _ end) |- _ =>
      rewrite (sem_cmp_gt_offsets (Zlength oc)) in Ht by (auto; lia); simpl in Ht;
      destruct (d + seg + seg <? d + seg + 4 * m) eqn:E; [rewrite Z.ltb_lt in E; lia | inv Ht] end. }
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob _ _ TT)]; [cancel | | lia | lia | lia].
    auto with share. }
  { match goal with Ht: typed_true _ (match sem_cmp_pp _ _ _ with _ => _ end) |- _ =>
      rewrite (sem_cmp_gt_offsets (Zlength oc)) in Ht by (auto; lia); simpl in Ht;
      destruct (d + seg + seg + seg <? d + seg + seg + 4 * m) eqn:E; [rewrite Z.ltb_lt in E; lia | inv Ht] end. }
  rewrite <- Hoc'.
  forward_call (Tsh, v_bitD1, gv, s1, st1, p1, o1, sh, offset_val off base, s, 6, sht, offset_val 4 dt, ht, L,
                sho, ob, oc', (d + 4 * m)%Z, (seg - 4 * m)%Z).
  { replace (d + 4 * m + (seg - 4 * m)) with (d + seg) by lia. entailer!. }
  { match goal with Hs: x4_sinv ht s1 _ _ w1 p1 o1 _ |- _ => destruct Hs as (_ & _ & _ & ? & _) end.
    split; [| try split; rep_lia].
    unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s1; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  Intros r1. destruct r1 as [[pa1 la1] L1]. cbn [fst snd] in *.
  match goal with Hx: forall dx, xb_rel s1 _ _ dx -> _ |- _ =>
    destruct (Hx _ (xb_rel_of _ _ _)) as [X1a X1b]; clear Hx end.
  change (sublist 0 (d + 4 * m) oc' ++ zbytes L1 ++ sublist (d + 4 * m + (seg - 4 * m)) (Zlength oc') oc')
    with (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1).
  match goal with Hf: o1 <= p1 -> _ |- _ => rename Hf into F1 end.
  match goal with Hz: Zlength L1 = _ |- _ => rename Hz into ZL1 end.
  match goal with Hz: bytes_ok L1 |- _ => rename Hz into BL1 end.
  assert (ZO1: Zlength (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) = Zlength oc') by (apply x4_fill_len; lia).
  forward_call (Tsh, v_bitD2, gv, s2, st2, p2, o2, sh, offset_val off base, s, (6 + l1), sht, offset_val 4 dt, ht, L,
                sho, ob, (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1), (d + seg + 4 * m)%Z, (seg - 4 * m)%Z).
  { replace (d + seg + 4 * m + (seg - 4 * m)) with (d + seg + seg) by lia. entailer!. }
  { rewrite ZO1. cancel. }
  { match goal with Hs: x4_sinv ht s2 _ _ w2 p2 o2 _ |- _ => destruct Hs as (_ & _ & _ & ? & _) end.
    split; [| try split; rep_lia].
    unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s2; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  Intros r2. destruct r2 as [[pa2 la2] L2]. cbn [fst snd] in *.
  match goal with Hx: forall dx, xb_rel s2 _ _ dx -> _ |- _ =>
    destruct (Hx _ (xb_rel_of _ _ _)) as [X2a X2b]; clear Hx end.
  change (sublist 0 (d + seg + 4 * m) (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) ++ zbytes L2 ++ sublist (d + seg + 4 * m + (seg - 4 * m)) (Zlength (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1)) (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1))
    with (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2).
  match goal with Hf: o2 <= p2 -> _ |- _ => rename Hf into F2 end.
  match goal with Hz: Zlength L2 = _ |- _ => rename Hz into ZL2 end.
  match goal with Hz: bytes_ok L2 |- _ => rename Hz into BL2 end.
  assert (ZO2: Zlength (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) = Zlength (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1)) by (apply x4_fill_len; lia).
  forward_call (Tsh, v_bitD3, gv, s3, st3, p3, o3, sh, offset_val off base, s, (6 + l1 + l2), sht, offset_val 4 dt, ht, L,
                sho, ob, (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2), (d + seg + seg + 4 * m)%Z, (seg - 4 * m)%Z).
  { replace (d + seg + seg + 4 * m + (seg - 4 * m)) with (d + seg + seg + seg) by lia. entailer!. }
  { rewrite ZO2. cancel. }
  { match goal with Hs: x4_sinv ht s3 _ _ w3 p3 o3 _ |- _ => destruct Hs as (_ & _ & _ & ? & _) end.
    split; [| try split; rep_lia].
    unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s3; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  Intros r3. destruct r3 as [[pa3 la3] L3]. cbn [fst snd] in *.
  match goal with Hx: forall dx, xb_rel s3 _ _ dx -> _ |- _ =>
    destruct (Hx _ (xb_rel_of _ _ _)) as [X3a X3b]; clear Hx end.
  change (sublist 0 (d + seg + seg + 4 * m) (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) ++ zbytes L3 ++ sublist (d + seg + seg + 4 * m + (seg - 4 * m)) (Zlength (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2)) (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2))
    with (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3).
  match goal with Hf: o3 <= p3 -> _ |- _ => rename Hf into F3 end.
  match goal with Hz: Zlength L3 = _ |- _ => rename Hz into ZL3 end.
  match goal with Hz: bytes_ok L3 |- _ => rename Hz into BL3 end.
  assert (ZO3: Zlength (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3) = Zlength (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2)) by (apply x4_fill_len; lia).
  forward_call (Tsh, v_bitD4, gv, s4, st4, p4, o4, sh, offset_val off base, s, (6 + l1 + l2 + l3), sht, offset_val 4 dt, ht, L,
                sho, ob, (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3), (d + seg + seg + seg + 4 * m)%Z, (n - 3 * seg - 4 * m)%Z).
  { replace (d + seg + seg + seg + 4 * m + (n - 3 * seg - 4 * m)) with (d + n) by lia. entailer!. }
  { rewrite ZO3. cancel. }
  { match goal with Hs: x4_sinv ht s4 _ _ w4 p4 o4 _ |- _ => destruct Hs as (_ & _ & _ & ? & _) end.
    split; [| try split; rep_lia].
    unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s4; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  Intros r4. destruct r4 as [[pa4 la4] L4]. cbn [fst snd] in *.
  match goal with Hx: forall dx, xb_rel s4 _ _ dx -> _ |- _ =>
    destruct (Hx _ (xb_rel_of _ _ _)) as [X4a X4b]; clear Hx end.
  change (sublist 0 (d + seg + seg + seg + 4 * m) (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3) ++ zbytes L4 ++ sublist (d + seg + seg + seg + 4 * m + (n - 3 * seg - 4 * m)) (Zlength (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3)) (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3))
    with (x4_fill (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3) (d + seg + seg + seg + 4 * m) (n - 3 * seg - 4 * m) L4).
  match goal with Hf: o4 <= p4 -> _ |- _ => rename Hf into F4 end.
  match goal with Hz: Zlength L4 = _ |- _ => rename Hz into ZL4 end.
  match goal with Hz: bytes_ok L4 |- _ => rename Hz into BL4 end.
  assert (ZO4: Zlength (x4_fill (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3) (d + seg + seg + seg + 4 * m) (n - 3 * seg - 4 * m) L4) = Zlength (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1) (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3)) by (apply x4_fill_len; lia).
  assert_PROP (bit_inv s1 pa1 la1 /\ bit_inv s2 pa2 la2 /\ bit_inv s3 pa3 la3 /\ bit_inv s4 pa4 la4) as Hbe.
  { unfold BIT_DStream_rep. Intros q1 m1 q2 m2. Intros q3 m3 q4 m4. entailer!. }
  forward_call (Tsh, v_bitD1, gv, s1, st1, pa1, la1, sh, offset_val off base, s, 6).
  { unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s1; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  forward_call (Tsh, v_bitD2, gv, s2, st2, pa2, la2, sh, offset_val off base, s, (6 + l1)).
  { unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s2; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  forward_call (Tsh, v_bitD3, gv, s3, st3, pa3, la3, sh, offset_val off base, s, (6 + l1 + l2)).
  { unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s3; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  forward_call (Tsh, v_bitD4, gv, s4, st4, pa4, la4, sh, offset_val off base, s, (6 + l1 + l2 + l3)).
  { unfold bit_src_ok. split; [reflexivity|]. split; [lia|]. unfold s4; rewrite Zlength_sublist by lia.
    split; [lia|]. f_equal; lia. }
  forward.
  set (O4 := x4_fill (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1)
                 (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3)
                 (d + seg + seg + seg + 4 * m) (n - 3 * seg - 4 * m) L4).
  assert (ZO: Zlength (x4_fill (x4_fill (x4_fill oc' (d + 4 * m) (seg - 4 * m) L1)
                 (d + seg + 4 * m) (seg - 4 * m) L2) (d + seg + seg + 4 * m) (seg - 4 * m) L3) = Zlength oc) by lia.
  rewrite ZO.
  assert (Hfin: out_after oc O4 d n /\ sublist d (d + n) O4 = zbytes (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4)).
  { match goal with Ho: x4_out oc oc' _ |- _ =>
      exact (x4_out_final oc oc' d seg n m w1 w2 w3 w4 L1 L2 L3 L4 H0 H2 ltac:(lia) ltac:(lia) ltac:(lia)
               Zw1 Zw2 Zw3 Zw4 ZL1 ZL2 ZL3 ZL4 Ho) end. }
  assert (Hmod: forall l, huf_lits_with true ht s n = Some l ->
            l = w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4 /\
            pa1 = 0 /\ la1 = 0 /\ pa2 = 0 /\ la2 = 0 /\ pa3 = 0 /\ la3 = 0 /\ pa4 = 0 /\ la4 = 0).
  { match goal with S1: x4_sinv ht s1 _ _ w1 _ _ _, S2: x4_sinv ht s2 _ _ w2 _ _ _,
                    S3: x4_sinv ht s3 _ _ w3 _ _ _, S4: x4_sinv ht s4 _ _ w4 _ _ _ |- _ =>
      exact (x4_final_model ht s n m w1 w2 w3 w4 L1 L2 L3 L4 p1 o1 p2 o2 p3 o3 p4 o4 es pa1 la1 pa2 la2 pa3 la3 pa4 la4
               H5 Hbs ltac:(lia) S1 S2 S3 S4 F1 F2 F3 F4) end. }
  assert (Hbl: bytes_ok (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4)).
  { match goal with S1: x4_sinv ht s1 _ _ w1 _ _ _, S2: x4_sinv ht s2 _ _ w2 _ _ _,
                    S3: x4_sinv ht s3 _ _ w3 _ _ _, S4: x4_sinv ht s4 _ _ w4 _ _ _ |- _ =>
      destruct S1 as (_ & ? & _), S2 as (_ & ? & _), S3 as (_ & ? & _), S4 as (_ & ? & _) end.
    unfold bytes_ok in *. rewrite !Forall_app. tauto. }
  (* the model: x4_exact *)
  assert (Hx: x_huf_decode (xhuf_of false ht) false s n =
     if andb (andb (andb (la1 =? 0) (pa1 =? 0)) (andb (la2 =? 0) (pa2 =? 0)))
             (andb (andb (la3 =? 0) (pa3 =? 0)) (andb (la4 =? 0) (pa4 =? 0)))
     then Some (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4) else None).
  { destruct Hbe as (Be1 & Be2 & Be3 & Be4).
    apply (x4_exact ht s n m D1 D2 D3 D4 p1 o1 p2 o2 p3 o3 p4 o4 pa1 la1 pa2 la2 pa3 la3 pa4 la4
             w1 w2 w3 w4 L1 L2 L3 L4); first [assumption | lia]. }
  clear X1a X1b X2a X2b X3a X3b X4a X4b.
  forward_if.
  - (* endCheck = 0: an error *)
    match goal with Hb: Int.and _ _ = Int.zero |- _ => rewrite x4_endcheck in Hb;
      match type of Hb with Int.repr (if ?B then 1 else 0) = _ =>
        assert (EB: B = false) by (destruct B; [vm_compute in Hb; discriminate | reflexivity]) end end.
    rewrite EB in Hx.
    forward. Exists (Int64.max_unsigned - 19) O4. entailer!.
    + split; [intros Hbc; apply (byte_cells_out oc O4 d n (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4)); [exact (proj1 Hfin) | lia | lia | lia | exact (proj2 Hfin) | exact Hbl | exact Hbc] |].
      rewrite err_20. repeat match goal with |- _ /\ _ => split end; try apply vlong_err_20; try tauto;
        try (intros Hc; discriminate).
      all: try (change (negb true) with false; rewrite Hx; reflexivity).
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      destruct (Hmod _ eq_refl) as (_ & -> & -> & -> & -> & -> & -> & -> & ->).
      exfalso. vm_compute in EB. discriminate.
    + unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel.
  - (* endCheck <> 0: success *)
    match goal with Hb: Int.and _ _ <> Int.zero |- _ => rewrite x4_endcheck in Hb;
      match type of Hb with Int.repr (if ?B then 1 else 0) <> _ =>
        assert (EB: B = true) by (destruct B; [reflexivity | exfalso; apply Hb; reflexivity]) end end.
    rewrite EB in Hx.
    forward. Exists n O4. entailer!.
    + split; [intros Hbc; apply (byte_cells_out oc O4 d n (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4)); [exact (proj1 Hfin) | lia | lia | lia | exact (proj2 Hfin) | exact Hbl | exact Hbc] |].
      repeat match goal with |- _ /\ _ => split end; try tauto; try rep_lia.
      all: try (change (negb true) with false; rewrite Hx; hnf; split; [reflexivity | exact (proj2 Hfin)]).
      * intros _. split; auto. exists (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4). split; [tauto | auto].
      * destruct (huf_lits_with true ht s n) eqn:E; auto.
        destruct (Hmod _ eq_refl) as (-> & _). split; [auto | tauto].
    + unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. first [sep_apply (hufdt_fold sht ht dt (hufdt_log false ht) res) | sep_apply (hufdt_fold sht ht dt L res)]; auto. cancel.
Qed.
