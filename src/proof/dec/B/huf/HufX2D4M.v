(* X2D: the exact model (model/ExHuf.v) of HUF_decompress4X2_usingDTable_internal_body, cut into the steps of
   the C's body (HufX2D4.v): the four streams of the jump table, the main loop xh_loop4s one iteration at a
   time, the code after it (x4_after), and the output array written by the four streams.

   The output array.  Each stream i (segment start x_i = d + (i - 1) seg) has emitted the bytes q_i, which the
   array holds at x_i, unless that region has been overwritten by a neighbour: HUF_decodeSymbolX2 writes 2
   bytes at op_i, so a stream that decodes at op_i = opStart_{i+1} - 1 (or beyond) writes into the next
   segment.  Such a stream is "doomed" (x4_doom): it has run past its segment (the check op_i > opStart_{i+1}
   rejects it), or it stands exactly at the segment's end with fewer than 64 bits consumed, so that
   BIT_endOfDStream fails after its HUF_decodeStreamX2 of 0 bytes.  x4_mem: each region holds its bytes unless
   that stream or the previous one is doomed.  On success no stream is doomed, so the array holds all four. *)
Require Export Zstd.proof.dec.B.huf.HufX2DSpecs.
Local Open Scope logic.

(* ---------- the output array ---------- *)

(* the 2-byte write of HUF_decodeSymbolX2 at a *)
Definition wr2 (oc: list val) (a b1 b2: Z) : list val :=
  sublist 0 a oc ++ zbytes [b1; b2] ++ sublist (a + 2) (Zlength oc) oc.

Lemma wr2_len (oc: list val) (a b1 b2: Z) : 0 <= a -> a + 2 <= Zlength oc -> Zlength (wr2 oc a b1 b2) = Zlength oc.
Proof. intros. unfold wr2. list_solve. Qed.

Lemma wr2_out (oc: list val) (a b1 b2 j: Z) : 0 <= a -> a + 2 <= Zlength oc -> 0 <= j < Zlength oc ->
  ~ (a <= j < a + 2) -> Znth j (wr2 oc a b1 b2) = Znth j oc.
Proof. intros. unfold wr2. list_solve. Qed.

Lemma wr2_in (oc: list val) (a b1 b2 j: Z) : 0 <= a -> a + 2 <= Zlength oc -> 0 <= j < 2 ->
  Znth (a + j) (wr2 oc a b1 b2) = Vint (Int.repr (Znth j [b1; b2])).
Proof. intros. unfold wr2. destruct (zeq j 0); [subst; list_solve|]. assert (j = 1) by lia. subst. list_solve. Qed.

(* the cells [x, x + |w|) hold the bytes w *)
Definition region_is (oc: list val) (x: Z) (w: list Z) : Prop :=
  forall j, 0 <= j < Zlength w -> Znth (x + j) oc = Vint (Int.repr (Znth j w)).

Lemma region_is_wr2_out (oc: list val) (x: Z) (w: list Z) (a b1 b2: Z) :
  0 <= a -> a + 2 <= Zlength oc -> 0 <= x -> x + Zlength w <= Zlength oc ->
  (a + 2 <= x \/ x + Zlength w <= a) -> region_is oc x w -> region_is (wr2 oc a b1 b2) x w.
Proof. intros ? ? ? ? Hd H j Hj. rewrite wr2_out by lia. apply H; auto. Qed.

(* ---------- the four streams and the code after the main loop ---------- *)

(* the four streams of the jump table, as the C reads them (MEM_readLE16 = le_field) *)
Definition x4s1 (s: list Z) : list Z := sublist 6 (6 + le_field s 0 2) s.
Definition x4s2 (s: list Z) : list Z := sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s.
Definition x4s3 (s: list Z) : list Z :=
  sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s.
Definition x4s4 (s: list Z) : list Z :=
  sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s.

(* the reader state BIT_initDStream sets on a well-formed stream w (HufXBit.xb_init_eq) *)
Definition x4_d0 (w: list Z) : xbit := xb_of w (bs_total w) (8 * Z.max 0 (Zlength w - 8)).

(* xh_4streams after its main loop, from the loop's final states and outputs: the checks op_i <= opStart_{i+1},
   the four HUF_decodeStreamX2 and the four BIT_endOfDStream *)
Definition x4_after (ht: huf_table) (s: list Z) (n: Z)
    (st: (xbit * xbit * xbit * xbit) * (list Z * list Z * list Z * list Z)) : option (list Z) :=
  let seg := (n + 3) / 4 in
  let '((d1, d2, d3, d4), (o1, o2, o3, o4)) := st in
  if seg <? Zlength o1 then None else
  if seg <? Zlength o2 then None else
  if seg <? Zlength o3 then None else
  let '(t1, d1) := xh_x2_stream (xhuf_of true ht) (x4s1 s) d1 (seg - Zlength o1) in
  let '(t2, d2) := xh_x2_stream (xhuf_of true ht) (x4s2 s) d2 (seg - Zlength o2) in
  let '(t3, d3) := xh_x2_stream (xhuf_of true ht) (x4s3 s) d3 (seg - Zlength o3) in
  let '(t4, d4) := xh_x2_stream (xhuf_of true ht) (x4s4 s) d4 (n - 3 * seg - Zlength o4) in
  if andb (andb (xb_end d1) (xb_end d2)) (andb (xb_end d3) (xb_end d4))
  then Some (o1 ++ t1 ++ o2 ++ t2 ++ o3 ++ t3 ++ o4 ++ t4) else None.

(* the main loop of xh_4streams (olimit = oend - 7) with fuel f *)
Definition x4_loop (ht: huf_table) (s: list Z) (n: Z) (f: nat) (d1 d2 d3 d4: xbit) (o1 o2 o3 o4: list Z) :=
  xh_loop4s f (fun d => xh_x2_n (xhuf_of true ht) d 4) (n - 7 - 3 * ((n + 3) / 4))
    (x4s1 s) (x4s2 s) (x4s3 s) (x4s4 s) d1 d2 d3 d4 o1 o2 o3 o4.

(* endSignal after the four BIT_reloadDStreamFast (status 0 = unfinished) *)
Definition x4_es (r1 r2 r3 r4: Z) : bool := ((r1 =? 0) && (r2 =? 0) && (r3 =? 0) && (r4 =? 0))%bool.

(* ---------- x_huf_decode on four streams, as the C's body runs it ---------- *)

(* the jump table's fields are 16-bit *)
Lemma x4m_le_field2 (s: list Z) (i: Z) : bytes_ok s -> 0 <= le_field s i 2 < 65536.
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

Lemma x4m_slice (l: list Z) (i k: Z) : 0 <= i -> 0 <= k -> slice l i k = sublist i (i + k) l.
Proof. intros Hi Hk. unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia. Qed.

(* the four streams of xh_split4 are x4s1 .. x4s4 *)
Lemma x4m_split (s: list Z) :
  bytes_ok s -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  xh_split4 s = Some (x4s1 s, x4s2 s, x4s3 s, x4s4 s).
Proof.
  intros Hs Hfit. unfold xh_split4.
  pose proof (x4m_le_field2 s 0 Hs). pose proof (x4m_le_field2 s 2 Hs). pose proof (x4m_le_field2 s 4 Hs).
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite !x4m_slice by lia. unfold x4s1, x4s2, x4s3, x4s4. repeat f_equal; lia.
Qed.

(* BIT_initDStream on stream w of the jump table *)
Lemma x4m_init (s w: list Z) (x y: Z) :
  bytes_ok s -> 0 <= x <= y -> y <= Zlength s -> w = sublist x y s ->
  xb_init w = if bs_wf w then Some (x4_d0 w) else None.
Proof. intros Hs Hx Hy ->. rewrite xb_init_eq by (apply Forall_sublist; auto). reflexivity. Qed.

(* cSrcSize < 10 *)
Lemma x4_dec_short (ht: huf_table) (s: list Z) (n: Z) :
  Zlength s < 10 -> x_huf_decode (xhuf_of true ht) false s n = None.
Proof.
  intros H. unfold x_huf_decode, xhuf_of, xh_4streams. simpl xh_x2. cbv beta iota.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

(* length4 > cSrcSize: the jump table's three sizes exceed the input *)
Lemma x4_dec_fit (ht: huf_table) (s: list Z) (n: Z) :
  10 <= Zlength s -> Zlength s < le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 ->
  x_huf_decode (xhuf_of true ht) false s n = None.
Proof.
  intros H10 Hlt. unfold x_huf_decode, xhuf_of, xh_4streams. simpl xh_x2. cbv beta iota.
  rewrite (proj2 (Z.ltb_ge _ _) H10). destruct (n <? 6); [reflexivity|].
  unfold xh_split4. rewrite (proj2 (Z.ltb_lt _ _) Hlt). reflexivity.
Qed.

(* one of the four BIT_initDStream fails *)
Lemma x4_dec_wf (ht: huf_table) (s: list Z) (n: Z) :
  bytes_ok s -> 10 <= Zlength s -> 6 <= n -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  (bs_wf (x4s1 s) && bs_wf (x4s2 s) && bs_wf (x4s3 s) && bs_wf (x4s4 s))%bool = false ->
  x_huf_decode (xhuf_of true ht) false s n = None.
Proof.
  intros Hs H10 Hn Hfit Hw. unfold x_huf_decode, xhuf_of, xh_4streams. simpl xh_x2. cbv beta iota.
  rewrite (proj2 (Z.ltb_ge _ _) H10), (proj2 (Z.ltb_ge n 6)) by lia. rewrite x4m_split by auto.
  pose proof (x4m_le_field2 s 0 Hs). pose proof (x4m_le_field2 s 2 Hs). pose proof (x4m_le_field2 s 4 Hs).
  rewrite (proj2 (Z.ltb_ge n (3 * ((n + 3) / 4)))) by (pose proof (Z.div_mod (n + 3) 4 ltac:(lia));
    pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)); lia).
  rewrite (x4m_init s (x4s1 s) 6 (6 + le_field s 0 2)) by (auto; lia).
  rewrite (x4m_init s (x4s2 s) (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2)) by (auto; lia).
  rewrite (x4m_init s (x4s3 s) (6 + le_field s 0 2 + le_field s 2 2)
             (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)) by (auto; lia).
  rewrite (x4m_init s (x4s4 s) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s)) by (auto; lia).
  destruct (bs_wf (x4s1 s)), (bs_wf (x4s2 s)), (bs_wf (x4s3 s)), (bs_wf (x4s4 s)); try reflexivity.
  discriminate.
Qed.

(* all checks before the main loop pass: the loop (when oend - op4 >= 8) and the code after it *)
Lemma x4_dec_eq (ht: huf_table) (s: list Z) (n: Z) :
  bytes_ok s -> 10 <= Zlength s -> 6 <= n -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  bs_wf (x4s1 s) = true -> bs_wf (x4s2 s) = true -> bs_wf (x4s3 s) = true -> bs_wf (x4s4 s) = true ->
  x_huf_decode (xhuf_of true ht) false s n =
  x4_after ht s n
    (if 8 <=? n - 3 * ((n + 3) / 4)
     then x4_loop ht s n (Z.to_nat n + 1) (x4_d0 (x4s1 s)) (x4_d0 (x4s2 s)) (x4_d0 (x4s3 s)) (x4_d0 (x4s4 s))
            nil nil nil nil
     else ((x4_d0 (x4s1 s), x4_d0 (x4s2 s), x4_d0 (x4s3 s), x4_d0 (x4s4 s)), (nil, nil, nil, nil))).
Proof.
  intros Hs H10 Hn Hfit W1 W2 W3 W4. unfold x_huf_decode, xhuf_of, xh_4streams. simpl xh_x2. cbv beta iota.
  rewrite (proj2 (Z.ltb_ge _ _) H10), (proj2 (Z.ltb_ge n 6)) by lia. rewrite x4m_split by auto.
  pose proof (x4m_le_field2 s 0 Hs). pose proof (x4m_le_field2 s 2 Hs). pose proof (x4m_le_field2 s 4 Hs).
  rewrite (proj2 (Z.ltb_ge n (3 * ((n + 3) / 4)))) by (pose proof (Z.div_mod (n + 3) 4 ltac:(lia));
    pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)); lia).
  rewrite (x4m_init s (x4s1 s) 6 (6 + le_field s 0 2)) by (auto; lia).
  rewrite (x4m_init s (x4s2 s) (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2)) by (auto; lia).
  rewrite (x4m_init s (x4s3 s) (6 + le_field s 0 2 + le_field s 2 2)
             (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)) by (auto; lia).
  rewrite (x4m_init s (x4s4 s) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s)) by (auto; lia).
  rewrite W1, W2, W3, W4. cbv zeta. unfold x4_after, x4_loop.
  destruct (8 <=? n - 3 * ((n + 3) / 4)); reflexivity.
Qed.

(* the loop's test fails (op4 >= olimit): the loop stops *)
Lemma x4_loop_stop (ht: huf_table) (s: list Z) (n: Z) (f: nat) (d1 d2 d3 d4: xbit) (o1 o2 o3 o4: list Z) :
  n - 7 - 3 * ((n + 3) / 4) <= Zlength o4 ->
  x4_loop ht s n (S f) d1 d2 d3 d4 o1 o2 o3 o4 = ((d1, d2, d3, d4), (o1, o2, o3, o4)).
Proof.
  intros H. unfold x4_loop. cbn [xh_loop4s]. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

(* one iteration of the loop on window-pointer states: stream i went from P_i to p_i emitting a_i, then
   BIT_reloadDStreamFast (Spec_bits.bs_reload_fast) *)
Lemma x4_loop_iter (ht: huf_table) (s: list Z) (n: Z) (f: nat)
    (P1 P2 P3 P4 p1 lo1 p2 lo2 p3 lo3 p4 lo4: Z) (o1 o2 o3 o4 a1 a2 a3 a4: list Z) :
  Zlength o4 < n - 7 - 3 * ((n + 3) / 4) ->
  xh_x2_n (xhuf_of true ht) (xb_of (x4s1 s) P1 lo1) 4 = (a1, xb_of (x4s1 s) p1 lo1) ->
  xh_x2_n (xhuf_of true ht) (xb_of (x4s2 s) P2 lo2) 4 = (a2, xb_of (x4s2 s) p2 lo2) ->
  xh_x2_n (xhuf_of true ht) (xb_of (x4s3 s) P3 lo3) 4 = (a3, xb_of (x4s3 s) p3 lo3) ->
  xh_x2_n (xhuf_of true ht) (xb_of (x4s4 s) P4 lo4) 4 = (a4, xb_of (x4s4 s) p4 lo4) ->
  bit_inv (x4s1 s) p1 lo1 -> bit_inv (x4s2 s) p2 lo2 -> bit_inv (x4s3 s) p3 lo3 -> bit_inv (x4s4 s) p4 lo4 ->
  lo1 <= p1 \/ lo1 < 64 -> lo2 <= p2 \/ lo2 < 64 -> lo3 <= p3 \/ lo3 < 64 -> lo4 <= p4 \/ lo4 < 64 ->
  x4_loop ht s n (S f) (xb_of (x4s1 s) P1 lo1) (xb_of (x4s2 s) P2 lo2) (xb_of (x4s3 s) P3 lo3)
    (xb_of (x4s4 s) P4 lo4) o1 o2 o3 o4 =
  if x4_es (fst (bs_reload_fast p1 lo1)) (fst (bs_reload_fast p2 lo2)) (fst (bs_reload_fast p3 lo3))
       (fst (bs_reload_fast p4 lo4))
  then x4_loop ht s n f (xb_of (x4s1 s) p1 (snd (bs_reload_fast p1 lo1))) (xb_of (x4s2 s) p2 (snd (bs_reload_fast p2 lo2)))
         (xb_of (x4s3 s) p3 (snd (bs_reload_fast p3 lo3))) (xb_of (x4s4 s) p4 (snd (bs_reload_fast p4 lo4)))
         (o1 ++ a1) (o2 ++ a2) (o3 ++ a3) (o4 ++ a4)
  else ((xb_of (x4s1 s) p1 (snd (bs_reload_fast p1 lo1)), xb_of (x4s2 s) p2 (snd (bs_reload_fast p2 lo2)),
         xb_of (x4s3 s) p3 (snd (bs_reload_fast p3 lo3)), xb_of (x4s4 s) p4 (snd (bs_reload_fast p4 lo4))),
        (o1 ++ a1, o2 ++ a2, o3 ++ a3, o4 ++ a4)).
Proof.
  intros Hlim E1 E2 E3 E4 I1 I2 I3 I4 L1 L2 L3 L4.
  unfold x4_loop. cbn [xh_loop4s]. rewrite (proj2 (Z.ltb_lt _ _) Hlim). cbn [negb].
  rewrite E1, E2, E3, E4.
  rewrite (xb_reload_fast_of (x4s1 s) p1 lo1 I1 L1), (xb_reload_fast_of (x4s2 s) p2 lo2 I2 L2),
    (xb_reload_fast_of (x4s3 s) p3 lo3 I3 L3), (xb_reload_fast_of (x4s4 s) p4 lo4 I4 L4).
  unfold x4_es, XB_unfinished.
  destruct (fst (bs_reload_fast p1 lo1) =? 0), (fst (bs_reload_fast p2 lo2) =? 0),
    (fst (bs_reload_fast p3 lo3) =? 0), (fst (bs_reload_fast p4 lo4) =? 0); reflexivity.
Qed.

(* one HUF_decodeSymbolX2 (its exact post: the peeked value v and the cell (first symbol + 256 b2, nb, kk))
   is one xh_x2_sym on the window-pointer state *)
Lemma x4_sym_step (ht: huf_table) (L: Z) (w: list Z) (p lo v kk b2 nb: Z) :
  L = xh_x2_log ht -> 0 <= v < 2 ^ L -> v = xb_look_fast (xb_of w p lo) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  0 <= fst (hsym ht L v) < 256 -> 0 <= b2 < 256 -> 1 <= kk <= 2 -> 0 <= nb ->
  0 <= lo + 64 - (p - nb) < 2 ^ 32 ->
  xh_x2_sym (xhuf_of true ht) (xb_of w p lo) = (firstn (Z.to_nat kk) [fst (hsym ht L v); b2], xb_of w (p - nb) lo).
Proof.
  intros HL Hv Hvx Hc Hs Hb2 Hkk Hnb Hr. subst L. unfold xh_x2_sym, xhuf_of. cbv zeta. cbn [xh_log].
  rewrite <- Hvx. unfold xh_cell. cbn [xh_cells]. rewrite Hc.
  f_equal.
  - f_equal. f_equal.
    + rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
    + rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. reflexivity.
  - unfold xb_skip, xb_of. cbn [xb_c xb_bc xb_ptr]. rewrite Z.mod_small by lia. f_equal. lia.
Qed.

(* xh_x2_n: j + 1 decodes are j decodes, then one *)
Lemma xh_x2_n_snoc (t: xhuf) (d: xbit) (j: nat) :
  xh_x2_n t d (S j) = let '(a, e) := xh_x2_n t d j in let '(b, g) := xh_x2_sym t e in (a ++ b, g).
Proof.
  revert d. induction j as [|j IH]; intros d.
  - cbn. destruct (xh_x2_sym t d) as [c e]. rewrite app_nil_r. reflexivity.
  - change (xh_x2_n t d (S (S j))) with
      (let '(c, d1) := xh_x2_sym t d in let '(l, d2) := xh_x2_n t d1 (S j) in (c ++ l, d2)).
    change (xh_x2_n t d (S j)) with
      (let '(c, d1) := xh_x2_sym t d in let '(l, d2) := xh_x2_n t d1 j in (c ++ l, d2)).
    destruct (xh_x2_sym t d) as [c d1]. rewrite IH.
    destruct (xh_x2_n t d1 j) as [a e]. destruct (xh_x2_sym t e) as [b g]. rewrite app_assoc. reflexivity.
Qed.

(* j + 1 decodes = j decodes, then one *)
Lemma x4_n_step (ht: huf_table) (L: Z) (w: list Z) (P p lo j v kk b2 nb: Z) :
  0 <= j -> snd (xh_x2_n (xhuf_of true ht) (xb_of w P lo) (Z.to_nat j)) = xb_of w p lo ->
  L = xh_x2_log ht -> 0 <= v < 2 ^ L -> v = xb_look_fast (xb_of w p lo) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  0 <= fst (hsym ht L v) < 256 -> 0 <= b2 < 256 -> 1 <= kk <= 2 -> 0 <= nb ->
  0 <= lo + 64 - (p - nb) < 2 ^ 32 ->
  xh_x2_n (xhuf_of true ht) (xb_of w P lo) (Z.to_nat (j + 1)) =
  (fst (xh_x2_n (xhuf_of true ht) (xb_of w P lo) (Z.to_nat j)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2],
   xb_of w (p - nb) lo).
Proof.
  intros Hj Hr HL Hv Hvx Hc Hs Hb2 Hkk Hnb Hrange.
  rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r, xh_x2_n_snoc.
  destruct (xh_x2_n (xhuf_of true ht) (xb_of w P lo) (Z.to_nat j)) as [a e]. simpl in Hr. subst e.
  rewrite (x4_sym_step ht L w p lo v kk b2 nb HL Hv Hvx Hc Hs Hb2 Hkk Hnb Hrange). reflexivity.
Qed.

(* the end of the loop: the states and outputs after the main loop (endSignal = 0, or op4 >= olimit) *)
Lemma x4_after_ovf (ht: huf_table) (s: list Z) (n: Z) (d1 d2 d3 d4: xbit) (o1 o2 o3 o4: list Z) :
  (n + 3) / 4 < Zlength o1 \/ (n + 3) / 4 < Zlength o2 \/ (n + 3) / 4 < Zlength o3 ->
  x4_after ht s n ((d1, d2, d3, d4), (o1, o2, o3, o4)) = None.
Proof.
  intros H. unfold x4_after.
  destruct ((n + 3) / 4 <? Zlength o1) eqn:E1; [reflexivity|].
  destruct ((n + 3) / 4 <? Zlength o2) eqn:E2; [reflexivity|].
  destruct ((n + 3) / 4 <? Zlength o3) eqn:E3; [reflexivity|].
  rewrite Z.ltb_ge in E1, E2, E3. lia.
Qed.

Lemma x4_after_eq (ht: huf_table) (s: list Z) (n: Z) (d1 d2 d3 d4: xbit) (o1 o2 o3 o4: list Z) :
  Zlength o1 <= (n + 3) / 4 -> Zlength o2 <= (n + 3) / 4 -> Zlength o3 <= (n + 3) / 4 ->
  x4_after ht s n ((d1, d2, d3, d4), (o1, o2, o3, o4)) =
  let r1 := xh_x2_stream (xhuf_of true ht) (x4s1 s) d1 ((n + 3) / 4 - Zlength o1) in
  let r2 := xh_x2_stream (xhuf_of true ht) (x4s2 s) d2 ((n + 3) / 4 - Zlength o2) in
  let r3 := xh_x2_stream (xhuf_of true ht) (x4s3 s) d3 ((n + 3) / 4 - Zlength o3) in
  let r4 := xh_x2_stream (xhuf_of true ht) (x4s4 s) d4 (n - 3 * ((n + 3) / 4) - Zlength o4) in
  if andb (andb (xb_end (snd r1)) (xb_end (snd r2))) (andb (xb_end (snd r3)) (xb_end (snd r4)))
  then Some (o1 ++ fst r1 ++ o2 ++ fst r2 ++ o3 ++ fst r3 ++ o4 ++ fst r4) else None.
Proof.
  intros H1 H2 H3. unfold x4_after.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), (proj2 (Z.ltb_ge _ _) H3).
  cbv zeta.
  destruct (xh_x2_stream (xhuf_of true ht) (x4s1 s) d1 ((n + 3) / 4 - Zlength o1)) as [t1 e1].
  destruct (xh_x2_stream (xhuf_of true ht) (x4s2 s) d2 ((n + 3) / 4 - Zlength o2)) as [t2 e2].
  destruct (xh_x2_stream (xhuf_of true ht) (x4s3 s) d3 ((n + 3) / 4 - Zlength o3)) as [t3 e3].
  destruct (xh_x2_stream (xhuf_of true ht) (x4s4 s) d4 (n - 3 * ((n + 3) / 4) - Zlength o4)) as [t4 e4].
  reflexivity.
Qed.

(* a stream standing exactly at its segment's end with fewer than 64 bits consumed: its HUF_decodeStreamX2
   of 0 bytes (one reload) leaves it unfinished, BIT_endOfDStream fails *)
Lemma x4_doom_end (ht: huf_table) (w: list Z) (p lo: Z) :
  0 <= lo -> 0 <= lo + 64 - p < 64 -> xb_end (snd (xh_x2_stream (xhuf_of true ht) w (xb_of w p lo) 0)) = false.
Proof.
  intros Hlo Hb.
  assert (E: forall d, xh_x2_stream (xhuf_of true ht) w d 0 = (nil, snd (xb_reload w d))).
  { intros d. unfold xh_x2_stream. destruct (xb_reload w d). reflexivity. }
  rewrite E. cbn [snd]. clear E.
  unfold xb_reload, xb_of. cbn [xb_bc xb_ptr xb_c].
  rewrite (proj2 (Z.ltb_ge 64 (lo + 64 - p))) by lia.
  assert (Hk: 0 <= lo / 8) by (apply Z.div_pos; lia).
  destruct (8 <=? lo / 8) eqn:E8.
  - unfold xb_reload_internal, xb_end. cbn [snd xb_ptr xb_bc].
    assert (Z.land (lo + 64 - p) 7 <= 7).
    { change (Z.land (lo + 64 - p) 7) with (Z.land (lo + 64 - p) (Z.ones 3)). rewrite Z.land_ones by lia.
      pose proof (Z.mod_pos_bound (lo + 64 - p) (2 ^ 3) ltac:(lia)). change (2 ^ 3) with 8 in *. lia. }
    rewrite (proj2 (Z.eqb_neq (Z.land (lo + 64 - p) 7) 64)) by lia. apply andb_false_r.
  - destruct (lo / 8 =? 0) eqn:E0.
    + unfold xb_end. cbn [snd xb_ptr xb_bc]. rewrite (proj2 (Z.eqb_neq (lo + 64 - p) 64)) by lia.
      apply andb_false_r.
    + assert (Hs: 0 <= Z.shiftr (lo + 64 - p) 3) by (apply Z.shiftr_nonneg; lia).
      destruct (lo / 8 <? Z.shiftr (lo + 64 - p) 3) eqn:Ek; unfold xb_end; cbn [snd xb_ptr xb_bc];
        match goal with |- (_ && (?x =? 64))%bool = false =>
          rewrite (proj2 (Z.eqb_neq x 64)) by lia; apply andb_false_r end.
Qed.

(* ---------- the output array of the four streams ---------- *)

(* stream (bytes q, reader (p, lo)) is doomed: past its segment, or exactly at its end with bits left *)
Definition x4_doom (n: Z) (q: list Z) (p lo: Z) : Prop :=
  (n + 3) / 4 < Zlength q \/ (Zlength q = (n + 3) / 4 /\ lo + 64 - p < 64).

(* the array oc holds each stream's bytes q_i at its segment start, unless that stream or the previous one is
   doomed (stream 4 never runs past the output) *)
Definition x4_mem (oc: list val) (d n: Z) (p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) : Prop :=
  (x4_doom n q1 p1 lo1 \/ region_is oc d q1) /\
  (x4_doom n q1 p1 lo1 \/ x4_doom n q2 p2 lo2 \/ region_is oc (d + (n + 3) / 4) q2) /\
  (x4_doom n q2 p2 lo2 \/ x4_doom n q3 p3 lo3 \/ region_is oc (d + (n + 3) / 4 + (n + 3) / 4) q3) /\
  (x4_doom n q3 p3 lo3 \/ region_is oc (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) q4).

Lemma x4_mem_init (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) :
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 nil nil nil nil.
Proof.
  unfold x4_mem, region_is. rewrite Zlength_nil.
  repeat split; right; try right; intros j Hj; lia.
Qed.

(* The bounds of the steps below (seg = (n + 3) / 4): the output [d, d + n) inside oc, 3 seg <= n, the three
   first streams within 2 seg - 8 bytes of their start, the fourth within its segment; a decode of stream i at
   x_i + |q_i| either stays 2 bytes before the next segment or leaves the stream with fewer than 64 bits
   consumed (so that reaching the segment's end exactly dooms it). *)

(* the bytes a decode emits: 1 or 2 *)
Lemma x4m_firstn_len (b1 b2 kk: Z) : 1 <= kk <= 2 -> Zlength (firstn (Z.to_nat kk) [b1; b2]) = kk.
Proof. intros H. destruct (zeq kk 1) as [->|]; [reflexivity|]. replace kk with 2 by lia. reflexivity. Qed.

(* a doomed stream stays doomed when it emits more bytes *)
Lemma x4m_doom_grow (n: Z) (q w: list Z) (p lo p': Z) :
  1 <= Zlength w -> x4_doom n q p lo -> x4_doom n (q ++ w) p' lo.
Proof. intros Hw Hd. left. unfold x4_doom in Hd. rewrite Zlength_app. lia. Qed.

(* a stream's own write extends its region *)
Lemma x4m_region_app (oc: list val) (x: Z) (q: list Z) (b1 b2 kk: Z) :
  0 <= x -> x + Zlength q + 2 <= Zlength oc -> 1 <= kk <= 2 -> region_is oc x q ->
  region_is (wr2 oc (x + Zlength q) b1 b2) x (q ++ firstn (Z.to_nat kk) [b1; b2]).
Proof.
  intros Hx Hoc Hk H j Hj. pose proof (x4m_firstn_len b1 b2 kk Hk) as Lw.
  rewrite Zlength_app, Lw in Hj. pose proof (Zlength_nonneg q).
  destruct (zlt j (Zlength q)).
  - rewrite wr2_out by lia. rewrite app_Znth1 by lia. apply H. lia.
  - replace (x + j) with (x + Zlength q + (j - Zlength q)) by lia. rewrite wr2_in by lia.
    rewrite app_Znth2 by lia. f_equal. f_equal.
    destruct (zeq kk 1) as [->|]; [replace (j - Zlength q) with 0 by lia; reflexivity|].
    replace kk with 2 in * by lia. reflexivity.
Qed.

Lemma x4_mem_step1 (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) (b1 b2 kk nb: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n ->
  Zlength q1 + 2 <= 2 * ((n + 3) / 4) - 6 -> Zlength q2 <= 2 * ((n + 3) / 4) - 8 ->
  Zlength q3 <= 2 * ((n + 3) / 4) - 8 -> Zlength q4 <= n - 3 * ((n + 3) / 4) ->
  1 <= kk <= 2 -> 0 <= nb ->
  (Zlength q1 + 2 <= (n + 3) / 4 \/ lo1 + 64 - (p1 - nb) < 64) ->
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 ->
  x4_mem (wr2 oc (d + Zlength q1) b1 b2) d n (p1 - nb) lo1 p2 lo2 p3 lo3
    (q1 ++ firstn (Z.to_nat kk) [b1; b2]) q2 q3 q4.
Proof.
  intros Hd Hoc Hn3 Hq1 Hq2 Hq3 Hq4 Hkk Hnb Hc (M1 & M2 & M3 & M4).
  pose proof (x4m_firstn_len b1 b2 kk Hkk) as Lw.
  pose proof (Zlength_nonneg q1). pose proof (Zlength_nonneg q2).
  pose proof (Zlength_nonneg q3). pose proof (Zlength_nonneg q4).
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
  assert (Hg: forall p', x4_doom n q1 p1 lo1 -> x4_doom n (q1 ++ firstn (Z.to_nat kk) [b1; b2]) p' lo1)
    by (intros p' Hd0; eapply x4m_doom_grow; [rewrite Lw; lia | exact Hd0]).
  assert (Hnew: Zlength q1 + 2 <= (n + 3) / 4 \/ x4_doom n (q1 ++ firstn (Z.to_nat kk) [b1; b2]) (p1 - nb) lo1).
  { destruct Hc as [Hc|Hc]; [left; auto|].
    destruct (Z_le_gt_dec (Zlength q1 + 2) ((n + 3) / 4)); [left; auto|right].
    unfold x4_doom. rewrite Zlength_app, Lw. lia. }
  unfold x4_mem. split; [|split; [|split]].
  - destruct M1 as [M1|M1]; [left; auto | right; apply x4m_region_app; auto; lia].
  - destruct M2 as [M2|[M2|M2]]; [left; auto | right; left; auto |].
    destruct Hnew as [Hnew|Hnew]; [right; right | left; auto].
    apply region_is_wr2_out; auto; lia.
  - destruct M3 as [M3|[M3|M3]]; [left; auto | right; left; auto | right; right].
    apply region_is_wr2_out; auto; lia.
  - destruct M4 as [M4|M4]; [left; auto | right].
    apply region_is_wr2_out; auto; lia.
Qed.

Lemma x4_mem_step2 (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) (b1 b2 kk nb: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n ->
  Zlength q1 <= 2 * ((n + 3) / 4) - 8 -> Zlength q2 + 2 <= 2 * ((n + 3) / 4) - 6 ->
  Zlength q3 <= 2 * ((n + 3) / 4) - 8 -> Zlength q4 <= n - 3 * ((n + 3) / 4) ->
  1 <= kk <= 2 -> 0 <= nb ->
  (Zlength q2 + 2 <= (n + 3) / 4 \/ lo2 + 64 - (p2 - nb) < 64) ->
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 ->
  x4_mem (wr2 oc (d + (n + 3) / 4 + Zlength q2) b1 b2) d n p1 lo1 (p2 - nb) lo2 p3 lo3
    q1 (q2 ++ firstn (Z.to_nat kk) [b1; b2]) q3 q4.
Proof.
  intros Hd Hoc Hn3 Hq1 Hq2 Hq3 Hq4 Hkk Hnb Hc (M1 & M2 & M3 & M4).
  pose proof (x4m_firstn_len b1 b2 kk Hkk) as Lw.
  pose proof (Zlength_nonneg q1). pose proof (Zlength_nonneg q2).
  pose proof (Zlength_nonneg q3). pose proof (Zlength_nonneg q4).
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
  assert (Hg: forall p', x4_doom n q2 p2 lo2 -> x4_doom n (q2 ++ firstn (Z.to_nat kk) [b1; b2]) p' lo2)
    by (intros p' Hd0; eapply x4m_doom_grow; [rewrite Lw; lia | exact Hd0]).
  assert (Hnew: Zlength q2 + 2 <= (n + 3) / 4 \/ x4_doom n (q2 ++ firstn (Z.to_nat kk) [b1; b2]) (p2 - nb) lo2).
  { destruct Hc as [Hc|Hc]; [left; auto|].
    destruct (Z_le_gt_dec (Zlength q2 + 2) ((n + 3) / 4)); [left; auto|right].
    unfold x4_doom. rewrite Zlength_app, Lw. lia. }
  unfold x4_mem. split; [|split; [|split]].
  - destruct M1 as [M1|M1]; [left; auto|].
    destruct (Z_lt_le_dec ((n + 3) / 4) (Zlength q1)); [left; left; auto | right].
    apply region_is_wr2_out; auto; lia.
  - destruct M2 as [M2|[M2|M2]]; [left; auto | right; left; auto |].
    right; right. replace (d + (n + 3) / 4 + Zlength q2) with ((d + (n + 3) / 4) + Zlength q2) by lia.
    apply x4m_region_app; auto; lia.
  - destruct M3 as [M3|[M3|M3]]; [left; auto | right; left; auto |].
    destruct Hnew as [Hnew|Hnew]; [right; right | left; auto].
    apply region_is_wr2_out; auto; lia.
  - destruct M4 as [M4|M4]; [left; auto | right].
    apply region_is_wr2_out; auto; lia.
Qed.

Lemma x4_mem_step3 (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) (b1 b2 kk nb: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n ->
  Zlength q1 <= 2 * ((n + 3) / 4) - 8 -> Zlength q2 <= 2 * ((n + 3) / 4) - 8 ->
  Zlength q3 + 2 <= 2 * ((n + 3) / 4) - 6 -> Zlength q4 <= n - 3 * ((n + 3) / 4) ->
  1 <= kk <= 2 -> 0 <= nb ->
  (Zlength q3 + 2 <= (n + 3) / 4 \/ lo3 + 64 - (p3 - nb) < 64) ->
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 ->
  x4_mem (wr2 oc (d + (n + 3) / 4 + (n + 3) / 4 + Zlength q3) b1 b2) d n p1 lo1 p2 lo2 (p3 - nb) lo3
    q1 q2 (q3 ++ firstn (Z.to_nat kk) [b1; b2]) q4.
Proof.
  intros Hd Hoc Hn3 Hq1 Hq2 Hq3 Hq4 Hkk Hnb Hc (M1 & M2 & M3 & M4).
  pose proof (x4m_firstn_len b1 b2 kk Hkk) as Lw.
  pose proof (Zlength_nonneg q1). pose proof (Zlength_nonneg q2).
  pose proof (Zlength_nonneg q3). pose proof (Zlength_nonneg q4).
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
  assert (Hg: forall p', x4_doom n q3 p3 lo3 -> x4_doom n (q3 ++ firstn (Z.to_nat kk) [b1; b2]) p' lo3)
    by (intros p' Hd0; eapply x4m_doom_grow; [rewrite Lw; lia | exact Hd0]).
  assert (Hnew: Zlength q3 + 2 <= (n + 3) / 4 \/ x4_doom n (q3 ++ firstn (Z.to_nat kk) [b1; b2]) (p3 - nb) lo3).
  { destruct Hc as [Hc|Hc]; [left; auto|].
    destruct (Z_le_gt_dec (Zlength q3 + 2) ((n + 3) / 4)); [left; auto|right].
    unfold x4_doom. rewrite Zlength_app, Lw. lia. }
  unfold x4_mem. split; [|split; [|split]].
  - destruct M1 as [M1|M1]; [left; auto | right]. apply region_is_wr2_out; auto; lia.
  - destruct M2 as [M2|[M2|M2]]; [left; auto | right; left; auto |].
    destruct (Z_lt_le_dec ((n + 3) / 4) (Zlength q2)); [right; left; left; auto | right; right].
    apply region_is_wr2_out; auto; lia.
  - destruct M3 as [M3|[M3|M3]]; [left; auto | right; left; auto |].
    right; right. replace (d + (n + 3) / 4 + (n + 3) / 4 + Zlength q3)
      with ((d + (n + 3) / 4 + (n + 3) / 4) + Zlength q3) by lia.
    apply x4m_region_app; auto; lia.
  - destruct M4 as [M4|M4]; [left; auto|].
    destruct Hnew as [Hnew|Hnew]; [right | left; auto].
    apply region_is_wr2_out; auto; lia.
Qed.

Lemma x4_mem_step4 (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) (b1 b2 kk: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n ->
  Zlength q1 <= 2 * ((n + 3) / 4) - 8 -> Zlength q2 <= 2 * ((n + 3) / 4) - 8 ->
  Zlength q3 <= 2 * ((n + 3) / 4) - 8 -> Zlength q4 + 2 <= n - 3 * ((n + 3) / 4) ->
  1 <= kk <= 2 ->
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 ->
  x4_mem (wr2 oc (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + Zlength q4) b1 b2) d n p1 lo1 p2 lo2 p3 lo3
    q1 q2 q3 (q4 ++ firstn (Z.to_nat kk) [b1; b2]).
Proof.
  intros Hd Hoc Hn3 Hq1 Hq2 Hq3 Hq4 Hkk (M1 & M2 & M3 & M4).
  pose proof (Zlength_nonneg q1). pose proof (Zlength_nonneg q2).
  pose proof (Zlength_nonneg q3). pose proof (Zlength_nonneg q4).
  pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
  unfold x4_mem. split; [|split; [|split]].
  - destruct M1 as [M1|M1]; [left; auto | right]. apply region_is_wr2_out; auto; lia.
  - destruct M2 as [M2|[M2|M2]]; [left; auto | right; left; auto | right; right].
    apply region_is_wr2_out; auto; lia.
  - destruct M3 as [M3|[M3|M3]]; [left; auto | right; left; auto |].
    destruct (Z_lt_le_dec ((n + 3) / 4) (Zlength q3)); [right; left; left; auto | right; right].
    apply region_is_wr2_out; auto; lia.
  - destruct M4 as [M4|M4]; [left; auto | right].
    replace (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + Zlength q4)
      with ((d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) + Zlength q4) by lia.
    apply x4m_region_app; auto; lia.
Qed.

(* BIT_reloadDStreamFast: bitsConsumed drops to at most 7, or does not change *)
Lemma x4_mem_reload (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3 lo1' lo2' lo3': Z) (q1 q2 q3 q4: list Z) :
  (lo1' + 64 - p1 <= 7 \/ lo1' = lo1) -> (lo2' + 64 - p2 <= 7 \/ lo2' = lo2) -> (lo3' + 64 - p3 <= 7 \/ lo3' = lo3) ->
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 -> x4_mem oc d n p1 lo1' p2 lo2' p3 lo3' q1 q2 q3 q4.
Proof.
  intros R1 R2 R3 (M1 & M2 & M3 & M4).
  assert (D: forall q p lo lo', (lo' + 64 - p <= 7 \/ lo' = lo) -> x4_doom n q p lo -> x4_doom n q p lo').
  { intros q p lo lo' R [Hd | [Hd Hb]]; [left; auto | right; split; auto; destruct R; subst; lia]. }
  unfold x4_mem. split; [|split; [|split]].
  - destruct M1 as [M1|M1]; [left; eapply D; eauto | right; auto].
  - destruct M2 as [M2|[M2|M2]]; [left; eapply D; eauto | right; left; eapply D; eauto | right; right; auto].
  - destruct M3 as [M3|[M3|M3]]; [left; eapply D; eauto | right; left; eapply D; eauto | right; right; auto].
  - destruct M4 as [M4|M4]; [left; eapply D; eauto | right; auto].
Qed.

(* no stream doomed: the array holds all four *)
Lemma x4_mem_ok (oc: list val) (d n p1 lo1 p2 lo2 p3 lo3: Z) (q1 q2 q3 q4: list Z) :
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 q1 q2 q3 q4 ->
  ~ x4_doom n q1 p1 lo1 -> ~ x4_doom n q2 p2 lo2 -> ~ x4_doom n q3 p3 lo3 ->
  region_is oc d q1 /\ region_is oc (d + (n + 3) / 4) q2 /\ region_is oc (d + (n + 3) / 4 + (n + 3) / 4) q3 /\
  region_is oc (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) q4.
Proof.
  intros (M1 & M2 & M3 & M4) N1 N2 N3. tauto.
Qed.

(* all the lemmas above (a check that none of them rests on an admitted lemma) *)
Lemma x4m_all : True.
Proof.
  pose proof @x4_dec_short. pose proof @x4_dec_fit. pose proof @x4_dec_wf. pose proof @x4_dec_eq.
  pose proof @x4_loop_stop. pose proof @x4_loop_iter. pose proof @x4_sym_step. pose proof @x4_n_step.
  pose proof @x4_after_ovf. pose proof @x4_after_eq. pose proof @x4_doom_end. pose proof @x4_mem_init.
  pose proof @x4_mem_step1. pose proof @x4_mem_step2. pose proof @x4_mem_step3. pose proof @x4_mem_step4.
  pose proof @x4_mem_reload. pose proof @x4_mem_ok.
  exact I.
Qed.
