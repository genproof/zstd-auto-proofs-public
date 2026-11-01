(* X1D: the exact model run of HUF_decompress4X1_usingDTable_internal_body (ExHuf.xh_4streams with the X1
   symbol decoder), in the terms the body's proof (HufX1D4BC.v) follows the C with.

   Inside the main loop every stream's state is a window-pointer state (BIT_DStream_rep_np), whose model
   state is exactly HufXBit.xb_of s pos lo.  The proof carries, as a forward invariant, that the model's loop
   run from the four initial states (xh_loop4s) is the continuation of its run from the current states and
   outputs (x4_lp); inside an iteration, that each stream's bytes since the iteration's start are the model's
   symbols (x4_mxw).  After the loop the model's run has ended in the C's states (x4_run), and the epilogue's
   four HUF_decodeStreamX1 and BIT_endOfDStream are the model's fin and xb_end (x4_exact).  The early
   returns are the model's early None (x4_exact_short, x4_exact_split, x4_exact_init). *)
Require Export Zstd.proof.dec.B.huf.HufXBit.
Local Open Scope Z_scope.

(* the four-symbol step of each stream in the main loop *)
Definition x4_dec4 (ht: huf_table) : xbit -> list Z * xbit := fun d => xh_x1_n (xhuf_of false ht) d 4.

(* the result of the main loop: the four states and the four outputs *)
Definition x4_res : Type := ((xbit * xbit * xbit * xbit) * (list Z * list Z * list Z * list Z))%type.

(* endSignal after the four BIT_reloadDStreamFast: 1 iff all four returned unfinished *)
Definition x4_es (e1 e2 e3 e4: Z) : Z := Z.b2z (andb (andb (andb (e1 =? 0) (e2 =? 0)) (e3 =? 0)) (e4 =? 0)).

(* ---------- one symbol, inside an iteration ---------- *)

(* the X1 cell of v in the model's table is the cell hsym ht L v of the parsed description *)
Lemma x4_cells_nth (ht: huf_table) (L v: Z) :
  0 <= v < 2 ^ L ->
  nth (Z.to_nat v) (xh_cells_x1 ht L) (0, 0, 0) = (fst (hsym ht L v), snd (hsym ht L v), 1).
Proof.
  intros Hv. unfold xh_cells_x1.
  assert (Hl: (Z.to_nat v < length (seq 0 (Z.to_nat (2 ^ L))))%nat).
  { rewrite seq_length. apply Z2Nat.inj_lt; lia. }
  rewrite (nth_indep _ (0, 0, 0) (let '(s, nb) := hsym ht L (Z.of_nat 0) in (s, nb, 1)))
    by (rewrite map_length; exact Hl).
  rewrite (map_nth (fun n => let '(s, nb) := hsym ht L (Z.of_nat n) in (s, nb, 1))).
  rewrite seq_nth by (rewrite seq_length in Hl; exact Hl).
  rewrite Nat.add_0_l, Z2Nat.id by lia.
  destruct (hsym ht L v). reflexivity.
Qed.

(* HUF_decodeSymbolX1 on a window-pointer state: the peek v (decodeSymbolX1's exact PROP) selects the cell
   (fst (hsym ht L v), snd (hsym ht L v)); the model emits its byte and skips its code length *)
Lemma x4x_sym (ht: huf_table) (si: list Z) (L p o v: Z) :
  L = xh_x1_log ht -> 0 <= v < 2 ^ L -> v = xb_look_fast (xb_of si p o) L ->
  0 <= o + 64 - (p - snd (hsym ht L v)) < 2 ^ 32 ->
  xh_x1_sym (xhuf_of false ht) (xb_of si p o) = (fst (hsym ht L v), xb_of si (p - snd (hsym ht L v)) o).
Proof.
  intros HL Hv Hlk Hb. subst L. unfold xh_x1_sym, xh_cell.
  change (xh_log (xhuf_of false ht)) with (xh_x1_log ht). rewrite <- Hlk.
  change (xh_cells (xhuf_of false ht)) with (xh_cells_x1 ht (xh_x1_log ht)).
  rewrite x4_cells_nth by exact Hv.
  unfold xb_skip, xb_of; cbn [xb_c xb_bc xb_ptr]. f_equal. f_equal.
  rewrite Z.mod_small; lia.
Qed.

(* the bytes wt the C wrote into a stream's segment since the iteration's start (w at state (P, o)) are the
   model's symbols from xb_of si P o, and the C's state (q, o) is the model's *)
Definition x4_mxw (ht: huf_table) (si: list Z) (P o: Z) (w wt: list Z) (q: Z) : Prop :=
  exists a, wt = w ++ a /\ xh_x1_n (xhuf_of false ht) (xb_of si P o) (length a) = (a, xb_of si q o).

(* k + 1 symbols: k symbols, then one more *)
Lemma x4_n_snoc (t: xhuf) (k: nat) (d d1 d2: xbit) (a: list Z) (c: Z) :
  xh_x1_n t d k = (a, d1) -> xh_x1_sym t d1 = (c, d2) -> xh_x1_n t d (S k) = (a ++ [c], d2).
Proof.
  revert d a. induction k as [|k IH]; intros d a H1 H2.
  - simpl in H1. inversion H1; subst. simpl. rewrite H2. reflexivity.
  - change (xh_x1_n t d (S (S k))) with
      (let '(c', d') := xh_x1_sym t d in let '(l, d'') := xh_x1_n t d' (S k) in (c' :: l, d'')).
    simpl in H1. destruct (xh_x1_sym t d) as [c0 e0].
    destruct (xh_x1_n t e0 k) as [l0 e1] eqn:E. inversion H1; subst.
    rewrite (IH e0 l0 E H2). reflexivity.
Qed.

Lemma x4_mxw_start (ht: huf_table) (si: list Z) (P o: Z) (w: list Z) : x4_mxw ht si P o w w P.
Proof.
  exists []. split; [rewrite app_nil_r; reflexivity | reflexivity].
Qed.

(* one more HUF_decodeSymbolX1 (bitsConsumed stays a small U32: o + 64 - q in [0, 100], code length in
   [0, 12]) *)
Lemma x4_mxw_step (ht: huf_table) (si: list Z) (P o: Z) (w wt: list Z) (q L v: Z) :
  x4_mxw ht si P o w wt q -> L = xh_x1_log ht -> 0 <= v < 2 ^ L -> v = xb_look_fast (xb_of si q o) L ->
  0 <= o + 64 - q <= 100 -> 0 <= snd (hsym ht L v) <= 12 ->
  x4_mxw ht si P o w (wt ++ [fst (hsym ht L v)]) (q - snd (hsym ht L v)).
Proof.
  intros (a & Hw & Ha) HL Hv Hlk Hq Hn.
  exists (a ++ [fst (hsym ht L v)]). split.
  - rewrite Hw, app_assoc. reflexivity.
  - rewrite app_length, Nat.add_1_r. simpl length.
    apply (x4_n_snoc _ _ _ (xb_of si q o)); [exact Ha|].
    apply x4x_sym; auto. lia.
Qed.

(* ---------- the main loop ---------- *)

(* the forward invariant of the main loop (fuel f, lim4 = olimit - opStart4): while endSignal = 1 the model's
   run R is the run from the current states and outputs; once endSignal = 0 the run has ended there *)
Definition x4_lp (ht: huf_table) (lim4: Z) (s1 s2 s3 s4: list Z) (R: x4_res) (f: nat)
    (p1 o1 p2 o2 p3 o3 p4 o4: Z) (w1 w2 w3 w4: list Z) (es: Z) : Prop :=
  (es = 1 -> xh_loop4s f (x4_dec4 ht) lim4 s1 s2 s3 s4
               (xb_of s1 p1 o1) (xb_of s2 p2 o2) (xb_of s3 p3 o3) (xb_of s4 p4 o4) w1 w2 w3 w4 = R) /\
  (es <> 1 -> R = ((xb_of s1 p1 o1, xb_of s2 p2 o2, xb_of s3 p3 o3, xb_of s4 p4 o4), (w1, w2, w3, w4))).

Lemma x4_lp_init (ht: huf_table) (lim4 n: Z) (s1 s2 s3 s4: list Z) (p1 o1 p2 o2 p3 o3 p4 o4: Z) :
  0 <= n ->
  x4_lp ht lim4 s1 s2 s3 s4
    (xh_loop4s (Z.to_nat n + 1) (x4_dec4 ht) lim4 s1 s2 s3 s4
       (xb_of s1 p1 o1) (xb_of s2 p2 o2) (xb_of s3 p3 o3) (xb_of s4 p4 o4) [] [] [] [])
    (Z.to_nat (n + 1 - 0)) p1 o1 p2 o2 p3 o3 p4 o4 [] [] [] [] 1.
Proof.
  intros Hn. split.
  - intros _. replace (Z.to_nat (n + 1 - 0)) with (Z.to_nat n + 1)%nat by lia. reflexivity.
  - intros H. contradiction H. reflexivity.
Qed.

(* the fuel left after m iterations, n + 1 - m, is positive while 4 m < n *)
Lemma x4_fuel (n m: Z) : 0 <= m -> m < n + 1 -> Z.to_nat (n + 1 - m) = S (Z.to_nat (n + 1 - (m + 1))).
Proof.
  intros H0 H1. lia.
Qed.

(* four symbols written since the iteration's start are the model's x4_dec4 *)
Lemma x4_mxw_dec4 (ht: huf_table) (si: list Z) (P o: Z) (w wt: list Z) (q: Z) :
  x4_mxw ht si P o w wt q -> Zlength wt = Zlength w + 4 ->
  exists a, wt = w ++ a /\ x4_dec4 ht (xb_of si P o) = (a, xb_of si q o).
Proof.
  intros (a & Hw & Ha) Hl. exists a. split; [exact Hw|].
  subst wt. rewrite Zlength_app in Hl.
  assert (length a = 4%nat) by (rewrite !Zlength_correct in Hl; lia).
  unfold x4_dec4. rewrite <- H. exact Ha.
Qed.

(* one iteration: 4 symbols per stream (x4_mxw from the iteration's start states (p_i, o_i) to (q_i, o_i)),
   then the four BIT_reloadDStreamFast (Spec_bits.bs_reload_fast, on states with bit_inv) *)
Lemma x4_lp_step (ht: huf_table) (lim4: Z) (s1 s2 s3 s4: list Z) (R: x4_res) (f: nat)
    (p1 o1 p2 o2 p3 o3 p4 o4 q1 q2 q3 q4: Z) (w1 w2 w3 w4 wt1 wt2 wt3 wt4: list Z) :
  x4_lp ht lim4 s1 s2 s3 s4 R (S f) p1 o1 p2 o2 p3 o3 p4 o4 w1 w2 w3 w4 1 ->
  Zlength w4 < lim4 ->
  x4_mxw ht s1 p1 o1 w1 wt1 q1 -> Zlength wt1 = Zlength w1 + 4 ->
  x4_mxw ht s2 p2 o2 w2 wt2 q2 -> Zlength wt2 = Zlength w2 + 4 ->
  x4_mxw ht s3 p3 o3 w3 wt3 q3 -> Zlength wt3 = Zlength w3 + 4 ->
  x4_mxw ht s4 p4 o4 w4 wt4 q4 -> Zlength wt4 = Zlength w4 + 4 ->
  bit_inv s1 q1 o1 -> (o1 <= q1 \/ o1 < 64) -> bit_inv s2 q2 o2 -> (o2 <= q2 \/ o2 < 64) ->
  bit_inv s3 q3 o3 -> (o3 <= q3 \/ o3 < 64) -> bit_inv s4 q4 o4 -> (o4 <= q4 \/ o4 < 64) ->
  x4_lp ht lim4 s1 s2 s3 s4 R f
    q1 (snd (bs_reload_fast q1 o1)) q2 (snd (bs_reload_fast q2 o2))
    q3 (snd (bs_reload_fast q3 o3)) q4 (snd (bs_reload_fast q4 o4)) wt1 wt2 wt3 wt4
    (x4_es (fst (bs_reload_fast q1 o1)) (fst (bs_reload_fast q2 o2))
           (fst (bs_reload_fast q3 o3)) (fst (bs_reload_fast q4 o4))).
Proof.
  intros [Hr _] Hlt M1 Z1 M2 Z2 M3 Z3 M4 Z4 I1 C1 I2 C2 I3 C3 I4 C4.
  specialize (Hr eq_refl).
  destruct (x4_mxw_dec4 _ _ _ _ _ _ _ M1 Z1) as (a1 & E1 & D1).
  destruct (x4_mxw_dec4 _ _ _ _ _ _ _ M2 Z2) as (a2 & E2 & D2).
  destruct (x4_mxw_dec4 _ _ _ _ _ _ _ M3 Z3) as (a3 & E3 & D3).
  destruct (x4_mxw_dec4 _ _ _ _ _ _ _ M4 Z4) as (a4 & E4 & D4).
  cbn [xh_loop4s] in Hr. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hr. cbn [negb] in Hr.
  rewrite D1, D2, D3, D4 in Hr.
  rewrite (xb_reload_fast_of s1 q1 o1 I1 C1), (xb_reload_fast_of s2 q2 o2 I2 C2),
    (xb_reload_fast_of s3 q3 o3 I3 C3), (xb_reload_fast_of s4 q4 o4 I4 C4) in Hr.
  rewrite <- E1, <- E2, <- E3, <- E4 in Hr. unfold XB_unfinished in Hr.
  unfold x4_lp, x4_es.
  destruct (fst (bs_reload_fast q1 o1) =? 0), (fst (bs_reload_fast q2 o2) =? 0),
    (fst (bs_reload_fast q3 o3) =? 0), (fst (bs_reload_fast q4 o4) =? 0);
    cbn [andb Z.b2z] in Hr |- *; split; intros H;
    solve [exact Hr | symmetry; exact Hr | contradiction H; reflexivity | discriminate H].
Qed.

(* the loop's exit (endSignal = 0, or op4 >= olimit): the run has ended in the current states *)
Lemma x4_lp_exit (ht: huf_table) (lim4: Z) (s1 s2 s3 s4: list Z) (R: x4_res) (f: nat)
    (p1 o1 p2 o2 p3 o3 p4 o4: Z) (w1 w2 w3 w4: list Z) (es: Z) :
  x4_lp ht lim4 s1 s2 s3 s4 R (S f) p1 o1 p2 o2 p3 o3 p4 o4 w1 w2 w3 w4 es ->
  (es = 1 -> lim4 <= Zlength w4) ->
  R = ((xb_of s1 p1 o1, xb_of s2 p2 o2, xb_of s3 p3 o3, xb_of s4 p4 o4), (w1, w2, w3, w4)).
Proof.
  intros [Hr Hn] Hl. destruct (Z.eq_dec es 1) as [E|E].
  - rewrite <- (Hr E). specialize (Hl E). cbn [xh_loop4s].
    rewrite (proj2 (Z.ltb_ge _ _) Hl). reflexivity.
  - exact (Hn E).
Qed.

(* ---------- the whole decoder ---------- *)

(* the main loop as xh_4streams runs it (X1: slack 3, olimit = oend - 3), only when oend - op4 >= 8 *)
Definition x4_run (ht: huf_table) (n seg: Z) (s1 s2 s3 s4: list Z) (D1 D2 D3 D4: xbit) : x4_res :=
  if 8 <=? n - 3 * seg
  then xh_loop4s (Z.to_nat n + 1) (x4_dec4 ht) (n - 3 - 3 * seg) s1 s2 s3 s4 D1 D2 D3 D4 [] [] [] []
  else ((D1, D2, D3, D4), ([], [], [], [])).

(* the X1 table's four-stream decoder is xh_4streams with xh_x1_n, slack 3 and xh_x1_stream *)
Lemma x4_decode_x1 (ht: huf_table) (s: list Z) (n: Z) :
  x_huf_decode (xhuf_of false ht) false s n =
  xh_4streams (fun d => xh_x1_n (xhuf_of false ht) d 4) 3 (xh_x1_stream (xhuf_of false ht)) s n.
Proof. reflexivity. Qed.

Lemma x4_slice (l: list Z) (i k: Z) : 0 <= i -> slice l i k = sublist i (i + k) l.
Proof.
  intros Hi. unfold slice, sublist. rewrite skipn_firstn_comm. f_equal. lia.
Qed.

Lemma x4_slice_nil (l: list Z) (i k: Z) : k <= 0 -> slice l i k = [].
Proof. intros Hk. unfold slice. replace (Z.to_nat k) with 0%nat by lia. reflexivity. Qed.

Lemma x4_init_nil : xb_init [] = None.
Proof. reflexivity. Qed.

(* the jump table, when the sizes fit *)
Lemma x4_split4_slice (s: list Z) :
  le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  xh_split4 s =
  Some (slice s 6 (le_field s 0 2), slice s (6 + le_field s 0 2) (le_field s 2 2),
        slice s (6 + le_field s 0 2 + le_field s 2 2) (le_field s 4 2),
        slice s (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)
          (Zlength s - 6 - le_field s 0 2 - le_field s 2 2 - le_field s 4 2)).
Proof. intros H. unfold xh_split4. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. Qed.

(* with three positive sizes the streams are the sublists of the statements *)
Lemma x4_split4 (s: list Z) :
  1 <= le_field s 0 2 -> 1 <= le_field s 2 2 -> 1 <= le_field s 4 2 ->
  le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  xh_split4 s =
  Some (sublist 6 (6 + le_field s 0 2) s,
        sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s,
        sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s,
        sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s).
Proof.
  intros H1 H2 H3 H. rewrite (x4_split4_slice s H). rewrite !x4_slice by lia. repeat f_equal. lia.
Qed.

(* a stream that BIT_initDStream accepts is not empty *)
Lemma x4_init_pos (s: list Z) (a b: Z) (d: xbit) : xb_init (sublist a b s) = Some d -> 1 <= b - a.
Proof.
  intros H. destruct (Z_le_gt_dec b a) as [E|E]; [|lia].
  rewrite sublist_nil_gen in H by exact E. discriminate H.
Qed.

(* three segments of (n + 3) / 4 fit in n >= 6 *)
Lemma x4_seg3 (n: Z) : 6 <= n -> (n <? 3 * ((n + 3) / 4)) = false.
Proof.
  intros H. apply Z.ltb_ge.
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)). lia.
Qed.

(* BIT_endOfDStream on a C state (directly from xb_rel and bit_inv) *)
Lemma x4_end_rel (s: list Z) (pos lo: Z) (d: xbit) :
  bit_inv s pos lo -> xb_rel s pos lo d -> xb_end d = andb (lo =? 0) (pos =? 0).
Proof.
  intros (_ & _ & H0 & H8 & _ & Hp & _) (_ & Hb & [Hs | [Hl Hs]]); unfold xb_end; rewrite Hs.
  - rewrite Hb. destruct (Z.eqb_spec lo 0) as [E|E].
    + subst lo. cbn [andb]. destruct (Z.eqb_spec pos 0), (Z.eqb_spec (0 + 64 - pos) 64); try lia;
        rewrite Zdiv_0_l; reflexivity.
    + replace (lo / 8 =? 0) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. intros E8. apply E.
      pose proof (Z.div_mod lo 8 ltac:(lia)). lia.
  - destruct (Z.eqb_spec lo 0), (Z.eqb_spec pos 0); try reflexivity; lia.
Qed.

(* cSrcSize < 10 *)
Lemma x4_exact_short (ht: huf_table) (s: list Z) (n: Z) :
  Zlength s < 10 -> x_huf_decode (xhuf_of false ht) false s n = None.
Proof.
  intros H. rewrite x4_decode_x1. unfold xh_4streams.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

(* the jump table's three sizes and the table exceed the input (length4 > cSrcSize) *)
Lemma x4_exact_split (ht: huf_table) (s: list Z) (n: Z) :
  10 <= Zlength s -> 6 <= n -> Zlength s < le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 ->
  x_huf_decode (xhuf_of false ht) false s n = None.
Proof.
  intros H10 H6 Hl. rewrite x4_decode_x1. unfold xh_4streams.
  rewrite (proj2 (Z.ltb_ge _ _) H10), (proj2 (Z.ltb_ge _ _) H6).
  unfold xh_split4. rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
Qed.

(* the four-stream decoder's result once a BIT_initDStream has failed: case on the others *)
Ltac x4_inits :=
  repeat match goal with |- context [xb_init ?l] => destruct (xb_init l) end; reflexivity.

(* a BIT_initDStream fails *)
Lemma x4_exact_init (ht: huf_table) (s: list Z) (n: Z) :
  10 <= Zlength s -> 6 <= n ->
  let l1 := le_field s 0 2 in let l2 := le_field s 2 2 in let l3 := le_field s 4 2 in
  l1 + l2 + l3 + 6 <= Zlength s ->
  xb_init (sublist 6 (6 + l1) s) = None \/ xb_init (sublist (6 + l1) (6 + l1 + l2) s) = None \/
  xb_init (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) = None \/
  xb_init (sublist (6 + l1 + l2 + l3) (Zlength s) s) = None ->
  x_huf_decode (xhuf_of false ht) false s n = None.
Proof.
  intros H10 H6. cbv zeta. intros Hl Hi. rewrite x4_decode_x1. unfold xh_4streams.
  rewrite (proj2 (Z.ltb_ge _ _) H10), (proj2 (Z.ltb_ge _ _) H6), (x4_seg3 n H6).
  destruct (Z_le_gt_dec (le_field s 0 2) 0) as [E1|E1];
    [|destruct (Z_le_gt_dec (le_field s 2 2) 0) as [E2|E2];
      [|destruct (Z_le_gt_dec (le_field s 4 2) 0) as [E3|E3]]].
  4: { rewrite (x4_split4 s) by lia. cbv zeta.
       destruct Hi as [E | [E | [E | E]]]; rewrite E; x4_inits. }
  all: rewrite (x4_split4_slice s Hl); cbv zeta.
  - rewrite (x4_slice_nil _ _ _ E1), x4_init_nil. x4_inits.
  - rewrite (x4_slice_nil _ (6 + _) _ E2), x4_init_nil. x4_inits.
  - rewrite (x4_slice_nil _ (6 + _ + _) _ E3), x4_init_nil. x4_inits.
Qed.

(* the end: the four streams initialized to D_i, the main loop ended in the window-pointer states (p_i, o_i)
   with outputs w_i (4 m bytes each), each stream finished by xh_x1_stream into the C state (pa_i, la_i);
   the model returns the C's bytes iff the four BIT_endOfDStream return 1 *)
Lemma x4_exact (ht: huf_table) (s: list Z) (n m: Z) (D1 D2 D3 D4: xbit)
    (p1 o1 p2 o2 p3 o3 p4 o4 pa1 la1 pa2 la2 pa3 la3 pa4 la4: Z) (w1 w2 w3 w4 L1 L2 L3 L4: list Z) :
  10 <= Zlength s -> 6 <= n ->
  let l1 := le_field s 0 2 in let l2 := le_field s 2 2 in let l3 := le_field s 4 2 in
  let seg := (n + 3) / 4 in
  let s1 := sublist 6 (6 + l1) s in let s2 := sublist (6 + l1) (6 + l1 + l2) s in
  let s3 := sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s in let s4 := sublist (6 + l1 + l2 + l3) (Zlength s) s in
  let t := xhuf_of false ht in
  l1 + l2 + l3 + 6 <= Zlength s ->
  xb_init s1 = Some D1 -> xb_init s2 = Some D2 -> xb_init s3 = Some D3 -> xb_init s4 = Some D4 ->
  x4_run ht n seg s1 s2 s3 s4 D1 D2 D3 D4 =
    ((xb_of s1 p1 o1, xb_of s2 p2 o2, xb_of s3 p3 o3, xb_of s4 p4 o4), (w1, w2, w3, w4)) ->
  0 <= m -> 3 * seg + 4 * m <= n ->
  Zlength w1 = 4 * m -> Zlength w2 = 4 * m -> Zlength w3 = 4 * m -> Zlength w4 = 4 * m ->
  fst (xh_x1_stream t s1 (xb_of s1 p1 o1) (seg - 4 * m)) = L1 ->
  xb_rel s1 pa1 la1 (snd (xh_x1_stream t s1 (xb_of s1 p1 o1) (seg - 4 * m))) -> bit_inv s1 pa1 la1 ->
  fst (xh_x1_stream t s2 (xb_of s2 p2 o2) (seg - 4 * m)) = L2 ->
  xb_rel s2 pa2 la2 (snd (xh_x1_stream t s2 (xb_of s2 p2 o2) (seg - 4 * m))) -> bit_inv s2 pa2 la2 ->
  fst (xh_x1_stream t s3 (xb_of s3 p3 o3) (seg - 4 * m)) = L3 ->
  xb_rel s3 pa3 la3 (snd (xh_x1_stream t s3 (xb_of s3 p3 o3) (seg - 4 * m))) -> bit_inv s3 pa3 la3 ->
  fst (xh_x1_stream t s4 (xb_of s4 p4 o4) (n - 3 * seg - 4 * m)) = L4 ->
  xb_rel s4 pa4 la4 (snd (xh_x1_stream t s4 (xb_of s4 p4 o4) (n - 3 * seg - 4 * m))) -> bit_inv s4 pa4 la4 ->
  x_huf_decode t false s n =
  if andb (andb (andb (la1 =? 0) (pa1 =? 0)) (andb (la2 =? 0) (pa2 =? 0)))
          (andb (andb (la3 =? 0) (pa3 =? 0)) (andb (la4 =? 0) (pa4 =? 0)))
  then Some (w1 ++ L1 ++ w2 ++ L2 ++ w3 ++ L3 ++ w4 ++ L4) else None.
Proof.
  intros H10 H6. cbv zeta.
  intros Hl HD1 HD2 HD3 HD4 Hrun Hm Hseg Hw1 Hw2 Hw3 Hw4
    HL1 HR1 HI1 HL2 HR2 HI2 HL3 HR3 HI3 HL4 HR4 HI4.
  pose proof (x4_init_pos _ _ _ _ HD1). pose proof (x4_init_pos _ _ _ _ HD2).
  pose proof (x4_init_pos _ _ _ _ HD3).
  rewrite x4_decode_x1. unfold xh_4streams.
  rewrite (proj2 (Z.ltb_ge _ _) H10), (proj2 (Z.ltb_ge _ _) H6), (x4_split4 s) by lia.
  rewrite (x4_seg3 n H6).
  cbv zeta. rewrite HD1, HD2, HD3, HD4.
  lazymatch goal with |- context [if 8 <=? ?x then ?a else ?b] =>
    lazymatch type of Hrun with _ = ?R =>
      let E := fresh in assert (E: (if 8 <=? x then a else b) = R) by exact Hrun; rewrite E
    end
  end.
  rewrite Hw1, Hw2, Hw3, Hw4.
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
  rewrite !(proj2 (Z.ltb_ge _ _)) by lia.
  destruct (xh_x1_stream _ _ (xb_of _ p1 o1) _) as [t1 e1]. cbn [fst snd] in HL1, HR1. subst t1.
  destruct (xh_x1_stream _ _ (xb_of _ p2 o2) _) as [t2 e2]. cbn [fst snd] in HL2, HR2. subst t2.
  destruct (xh_x1_stream _ _ (xb_of _ p3 o3) _) as [t3 e3]. cbn [fst snd] in HL3, HR3. subst t3.
  destruct (xh_x1_stream _ _ (xb_of _ p4 o4) _) as [t4 e4]. cbn [fst snd] in HL4, HR4. subst t4.
  rewrite (x4_end_rel _ _ _ _ HI1 HR1), (x4_end_rel _ _ _ _ HI2 HR2),
    (x4_end_rel _ _ _ _ HI3 HR3), (x4_end_rel _ _ _ _ HI4 HR4).
  reflexivity.
Qed.
