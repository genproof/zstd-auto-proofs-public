(* X2D: the body of HUF_decompress4X2_usingDTable_internal_body (spec in HufX2DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX2D4M.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* ---------- model: the four streams ---------- *)

(* one stream of the 4: well formed, decodes to exactly the k symbols q, ending at position 0 *)
Definition stream_ok (ht: huf_table) (si: list Z) (k: Z) (q: list Z) : Prop :=
  bs_wf si = true /\ Zlength q = k /\ bytes_ok q /\
  huf_decode_syms ht si (Z.to_nat k) (bs_total si) = Some (q, 0).


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

(* the model's 4 streams, in the terms of the C: the jump table read by MEM_readLE16 (le_field), the
   windows as sublists, segment seg = (n+3)/4, the last stream n - 3 seg symbols *)
Lemma huf4_split (ht: huf_table) (s: list Z) (n: Z) (l: list Z) :
  huf_ok ht -> bytes_ok s -> 0 <= n -> huf_decode_4streams ht s n = Some l ->
  let l1 := le_field s 0 2 in let l2 := le_field s 2 2 in let l3 := le_field s 4 2 in
  let seg := (n + 3) / 4 in
  10 <= Zlength s /\ 6 + l1 + l2 + l3 + 1 <= Zlength s /\ 3 * seg <= n /\
  exists q1 q2 q3 q4, l = q1 ++ q2 ++ q3 ++ q4 /\
    stream_ok ht (sublist 6 (6 + l1) s) seg q1 /\
    stream_ok ht (sublist (6 + l1) (6 + l1 + l2) s) seg q2 /\
    stream_ok ht (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) seg q3 /\
    stream_ok ht (sublist (6 + l1 + l2 + l3) (Zlength s) s) (n - 3 * seg) q4.
Proof.
  intros Hok Hs Hn E. unfold huf_decode_4streams in E.
  rewrite <- Zlength_correct in E.
  destruct (Zlength s <? 10) eqn:E10; [discriminate|]. apply Z.ltb_ge in E10.
  set (l1 := le_field s 0 2) in *. set (l2 := le_field s 2 2) in *. set (l3 := le_field s 4 2) in *.
  assert (H1: 0 <= l1 < 65536) by (apply le_field2_range; auto).
  assert (H2: 0 <= l2 < 65536) by (apply le_field2_range; auto).
  assert (H3: 0 <= l3 < 65536) by (apply le_field2_range; auto).
  destruct (Zlength s - 6 - l1 - l2 - l3 <? 1) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4.
  set (seg := (n + 3) / 4) in *.
  assert (Hseg0: 0 <= seg) by (apply Z.div_pos; lia).
  destruct (n - 3 * seg <? 0) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
  assert (Sl: forall i k, 0 <= i -> 0 <= k -> slice s i k = sublist i (i + k) s).
  { intros i k Hi Hk. unfold slice, sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia. }
  rewrite !Sl in E by lia.
  replace (6 + l1 + l2 + l3 + (Zlength s - 6 - l1 - l2 - l3)) with (Zlength s) in E by lia.
  replace (6 + l1 + l2 + (6 + l1 + l2 + l3 - (6 + l1 + l2))) with (6 + l1 + l2 + l3) in E by lia.
  assert (St: forall w k q, 0 <= k -> huf_decode_stream ht w k = Some q -> stream_ok ht w k q).
  { intros w k q Hk Hd. unfold huf_decode_stream in Hd.
    destruct (bs_okb w) eqn:Ew; [|discriminate]. simpl in Hd.
    destruct (huf_decode_syms ht w (Z.to_nat k) (bs_total w)) as [[q' p']|] eqn:Ed; [|discriminate].
    destruct p' as [|pp|pp]; try discriminate. inv Hd.
    assert (Hwf: bs_wf w = true).
    { unfold bs_okb, bs_wf in *. rewrite Zlength_correct. apply andb_prop in Ew as [Ew1 Ew2].
      apply andb_prop in Ew1 as [_ Ew1]. rewrite Ew2, andb_true_r.
      destruct w; simpl in *; [discriminate|]. reflexivity. }
    assert (Hpos: 0 <= bs_total w).
    { unfold bs_total. unfold bs_wf in Hwf. apply andb_prop in Hwf as [Hw1 _].
      apply negb_true_iff, Z.eqb_neq in Hw1. rewrite Zlength_correct in Hw1.
      pose proof (Z.log2_nonneg (last w 0)). unfold highbit. lia. }
    destruct (huf_decode_syms_bounds ht w (Z.to_nat k) (bs_total w) 0 q Hok Hpos Ed) as (Hl & Hb & _).
    rewrite Z2Nat.id in Hl by lia.
    split; [auto|]. split; [auto|]. split; [|auto].
    unfold bytes_ok. eapply Forall_impl; [|exact Hb]. intros x Hx. cbv beta in Hx. unfold is_byte. lia. }
  destruct (huf_decode_stream ht (sublist 6 (6 + l1) s) seg) as [q1|] eqn:D1; [|discriminate].
  destruct (huf_decode_stream ht (sublist (6 + l1) (6 + l1 + l2) s) seg) as [q2|] eqn:D2; [|discriminate].
  destruct (huf_decode_stream ht (sublist (6 + l1 + l2) (6 + l1 + l2 + l3) s) seg) as [q3|] eqn:D3; [|discriminate].
  destruct (huf_decode_stream ht (sublist (6 + l1 + l2 + l3) (Zlength s) s) (n - 3 * seg)) as [q4|] eqn:D4;
    [|discriminate].
  inv E. split; [lia|]. split; [lia|]. split; [lia|].
  exists q1, q2, q3, q4. split; [auto|].
  split; [apply St; auto|]. split; [apply St; auto|]. split; apply St; auto; lia.
Qed.

(* ---------- model: one stream in the main loop (valid runs) ---------- *)

(* c of the M symbols q decoded, the rest decodes from pos to the end of the stream *)
Definition vs_head (ht: huf_table) (si q: list Z) (M pos lo c: Z) : Prop :=
  0 <= c <= M /\ 0 <= lo <= pos /\
  huf_decode_syms ht si (Z.to_nat (M - c)) pos = Some (sublist c M q, 0).

(* after j decodes of an iteration: the bits consumed in the container, and enough symbols left (the first
   iteration: >= 8 symbols in the stream; later ones: pos >= 72 at the reload) *)
Definition vs_mid (ht: huf_table) (si q: list Z) (M j pos lo c: Z) : Prop :=
  vs_head ht si q M pos lo c /\
  (lo + 64 - pos <= 8 + 12 * j \/ lo = 0) /\
  ((8 <= M /\ c <= 2 * j) \/ 72 - 12 * j <= pos).

Lemma vs_head_mid (ht: huf_table) (si q: list Z) (M pos lo c: Z) :
  vs_head ht si q M pos lo c -> (lo + 64 - pos <= 8 \/ lo = 0) -> (c = 0 /\ 8 <= M \/ 72 <= pos) ->
  vs_mid ht si q M 0 pos lo c.
Proof. intros H1 H2 H3. split; [auto|]. split; [lia|]. lia. Qed.

(* a run ending at a position >= 0 starts at a position >= 0 *)
Lemma huf_decode_syms_pos (ht: huf_table) (V: list Z) (m: nat) (p pe: Z) (l: list Z) :
  huf_ok ht -> 0 <= pe -> huf_decode_syms ht V m p = Some (l, pe) -> 0 <= p.
Proof.
  intros Hok Hpe H. destruct m as [|m]; simpl in H; [inv H; lia|].
  pose proof (bs_peek_s_range V p (ht_log ht) ltac:(destruct Hok; lia)) as Hr.
  destruct Hok as (Hlog & Hlen & Hall).
  assert (Hin: In (nth (Z.to_nat (bs_peek_s V p (ht_log ht))) (huf_cells ht) (0, 0)) (huf_cells ht)).
  { apply nth_In. rewrite Zlength_correct in Hlen. lia. }
  rewrite Forall_forall in Hall. specialize (Hall _ Hin).
  destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb] eqn:Hc. simpl in Hall.
  destruct (p - nb <? 0) eqn:Hneg; [discriminate|]. apply Z.ltb_ge in Hneg. lia.
Qed.

Lemma vs_step (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (si q: list Z)
    (M j pos lo c v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok si -> Zlength q = M -> 0 <= j <= 3 ->
  vs_mid ht si q M j pos lo c ->
  (lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value si) pos L) ->
  x2_step ht L v k b2 nb ->
  vs_mid ht si q M (j + 1) (pos - nb) lo (c + k) /\ c + 2 <= M /\ 1 <= k <= 2 /\
  sublist 0 k [fst (hsym ht L v); b2] = sublist c (c + k) q.
Proof.
  intros Htab Hsi Hq Hj ((Hc & Hlo & Hr) & Hbc & Hfirst) Hv Hst.
  destruct Htab as (Hok & HL & _).
  assert (Hlog: ht_log ht <= 12 /\ L <= 12) by (unfold HUF_TABLELOG_MAX in HL; lia).
  assert (Hk: 1 <= k <= 2 /\ 1 <= nb <= L).
  { destruct Hst as (_ & Hnb & Hcase). destruct (hsym ht L v) as [s1 n1].
    destruct Hcase as [[-> _]|Hc2]; [lia|].
    destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2]. destruct Hc2 as [-> _]. lia. }
  destruct (huf_decode_syms_bounds ht si (Z.to_nat (M - c)) pos 0 (sublist c M q) Hok ltac:(lia) Hr)
    as (_ & _ & Hpb & _).
  rewrite Z2Nat.id in Hpb by lia.
  assert (H12: ht_log ht * (M - c) <= 12 * (M - c)) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hm: 2 <= M - c /\ (72 - 12 * j <= pos -> 3 <= M - c)) by lia.
  assert (Hex: v = bs_peek (bs_value si) pos L).
  { apply Hv. destruct Hbc as [Hbc|Hbc]; [left; unfold HUF_TABLELOG_MAX in HL; lia | right; lia]. }
  destruct (x2_step_syms Hf ht si L pos v k b2 nb (Z.to_nat (M - c)) (sublist c M q) 0 Hok HL Hsi
              ltac:(lia) Hex Hst ltac:(lia) Hr) as (Hs & Hr').
  replace (Z.to_nat (M - c) - Z.to_nat k)%nat with (Z.to_nat (M - (c + k))) in Hr' by lia.
  rewrite Zlength_sublist, sublist_sublist in Hr' by lia.
  replace (k + c) with (c + k) in Hr' by lia. replace (M - c + c) with M in Hr' by lia.
  pose proof (huf_decode_syms_pos ht si _ _ _ _ Hok (Z.le_refl 0) Hr') as Hp0.
  destruct (huf_decode_syms_bounds ht si (Z.to_nat (M - (c + k))) (pos - nb) 0 (sublist (c + k) M q) Hok
              Hp0 Hr') as (_ & _ & Hpb' & _).
  rewrite Z2Nat.id in Hpb' by lia.
  split; [|split; [lia | split; [lia|]]].
  - unfold vs_mid, vs_head. split; [split; [lia | split; [lia | exact Hr']]|].
    split; [unfold HUF_TABLELOG_MAX in HL; lia | lia].
  - rewrite <- Hs. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma vs_reload (ht: huf_table) (si q: list Z) (M pos lo c: Z) :
  vs_mid ht si q M 4 pos lo c ->
  lo <= pos /\ vs_head ht si q M pos (snd (bs_reload_fast pos lo)) c /\
  (fst (bs_reload_fast pos lo) = BIT_unfinished ->
   snd (bs_reload_fast pos lo) + 64 - pos <= 8 /\ 72 <= pos).
Proof.
  intros ((Hc & Hlo & Hr) & Hbc & _). unfold bs_reload_fast.
  destruct (lo / 8 <? 8) eqn:E; cbn [fst snd].
  - split; [lia|]. split; [split; auto|]. unfold BIT_overflow, BIT_unfinished. lia.
  - apply Z.ltb_ge in E.
    assert (H64: 64 <= lo) by (pose proof (Z.mul_div_le lo 8 ltac:(lia)); lia).
    assert (Hb: lo + 64 - pos <= 56) by lia.
    pose proof (Z.mul_div_le (lo + 64 - pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)).
    pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)).
    split; [lia|]. split; [split; [auto | split; [lia | exact Hr]]|]. intros _. lia.
Qed.

(* ---------- the output array ---------- *)

(* the k-byte fill of HUF_decodeStreamX2 at a *)
Definition wrk (oc: list val) (a: Z) (l: list Z) : list val :=
  sublist 0 a oc ++ zbytes l ++ sublist (a + Zlength l) (Zlength oc) oc.

Lemma wrk_len (oc: list val) (a: Z) (l: list Z) : 0 <= a -> a + Zlength l <= Zlength oc ->
  Zlength (wrk oc a l) = Zlength oc.
Proof. intros. unfold wrk. list_solve. Qed.

Lemma wrk_out (oc: list val) (a: Z) (l: list Z) (j: Z) : 0 <= a -> a + Zlength l <= Zlength oc ->
  0 <= j < Zlength oc -> ~ (a <= j < a + Zlength l) -> Znth j (wrk oc a l) = Znth j oc.
Proof. intros. unfold wrk. list_solve. Qed.

Lemma wrk_in (oc: list val) (a: Z) (l: list Z) (j: Z) : 0 <= a -> a + Zlength l <= Zlength oc ->
  0 <= j < Zlength l -> Znth (a + j) (wrk oc a l) = Vint (Int.repr (Znth j l)).
Proof. intros. unfold wrk. list_solve. Qed.

(* the cells [x, x+len) hold bytes *)
Definition region_bytes (oc: list val) (x len: Z) : Prop :=
  forall j, x <= j < x + len -> exists b, 0 <= b < 256 /\ Znth j oc = Vint (Int.repr b).

Lemma region_is_sublist (oc: list val) (x: Z) (w: list Z) :
  0 <= x -> x + Zlength w <= Zlength oc -> region_is oc x w -> sublist x (x + Zlength w) oc = zbytes w.
Proof.
  intros Hx Hw H. apply Znth_eq_ext; [list_solve|].
  intros i Hi. rewrite Zlength_sublist in Hi by list_solve.
  rewrite Znth_sublist by lia. rewrite Znth_map by lia. rewrite Z.add_comm. apply H. lia.
Qed.

Definition val_byte (x: val) : Z := match x with Vint i => Int.unsigned i | _ => 0 end.

Lemma region_bytes_zbytes (oc: list val) (x len: Z) :
  0 <= x -> 0 <= len -> x + len <= Zlength oc -> region_bytes oc x len ->
  exists l, sublist x (x + len) oc = zbytes l /\ bytes_ok l.
Proof.
  intros Hx Hlen Hoc H. exists (map val_byte (sublist x (x + len) oc)). split.
  - apply Znth_eq_ext; [list_solve|]. intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite Znth_map by list_solve. rewrite Znth_map by list_solve. rewrite Znth_sublist by lia.
    destruct (H (i + x) ltac:(lia)) as (b & Hb & ->). simpl. rewrite Int.repr_unsigned. reflexivity.
  - unfold bytes_ok. rewrite Forall_forall. intros y Hy. apply in_map_iff in Hy as (z & <- & Hz).
    apply In_Znth in Hz as (i & Hi & <-). rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia.
    destruct (H (i + x) ltac:(lia)) as (b & Hb & ->). simpl. unfold is_byte.
    rewrite Int.unsigned_repr by rep_lia. lia.
Qed.

(* ---------- the main loop: invariants ---------- *)

Lemma region_is_wr2_ext (oc: list val) (x c k: Z) (q: list Z) (b1 b2: Z) :
  0 <= x -> 0 <= c -> 1 <= k <= 2 -> c + 2 <= Zlength q -> x + c + 2 <= Zlength oc ->
  sublist 0 k [b1; b2] = sublist c (c + k) q ->
  region_is oc x (sublist 0 c q) -> region_is (wr2 oc (x + c) b1 b2) x (sublist 0 (c + k) q).
Proof.
  intros Hx Hc Hk Hq Hoc Hs H j Hj. rewrite Zlength_sublist in Hj by lia.
  destruct (zlt j c).
  - rewrite wr2_out by lia. rewrite H by (rewrite Zlength_sublist; lia). rewrite !Znth_sublist by lia. reflexivity.
  - replace (x + j) with (x + c + (j - c)) by lia. rewrite wr2_in by lia.
    rewrite Znth_sublist by lia.
    assert (E: Znth (j - c) (sublist 0 k [b1; b2]) = Znth (j - c) (sublist c (c + k) q)) by (rewrite Hs; auto).
    rewrite !Znth_sublist in E by (simpl; lia). replace (j - c + 0) with (j - c) in E by lia.
    rewrite E. f_equal. f_equal. f_equal. lia.
Qed.

Lemma region_bytes_wr2 (oc: list val) (x len a b1 b2: Z) :
  0 <= a -> a + 2 <= Zlength oc -> 0 <= x -> x + len <= Zlength oc -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  region_bytes oc x len -> region_bytes (wr2 oc a b1 b2) x len.
Proof.
  intros ? ? ? ? Hb1 Hb2 H j Hj. destruct (zlt j a); [|destruct (zlt j (a + 2))].
  - rewrite wr2_out by lia. auto.
  - replace j with (a + (j - a)) by lia. rewrite wr2_in by lia.
    destruct (zeq (j - a) 0) as [->|]; [exists b1; auto|]. replace (j - a) with 1 by lia. exists b2; auto.
  - rewrite wr2_out by lia. auto.
Qed.

Lemma region_bytes_wr2_ext (oc: list val) (x c k b1 b2: Z) :
  0 <= x -> 0 <= c -> 0 <= k <= 2 -> x + c + 2 <= Zlength oc -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  region_bytes oc x c -> region_bytes (wr2 oc (x + c) b1 b2) x (c + k).
Proof.
  intros ? ? ? ? Hb1 Hb2 H j Hj. destruct (zlt j (x + c)).
  - rewrite wr2_out by lia. apply H. lia.
  - replace j with (x + c + (j - (x + c))) by lia. rewrite wr2_in by lia.
    destruct (zeq (j - (x + c)) 0) as [->|]; [exists b1; auto|]. replace (j - (x + c)) with 1 by lia. exists b2; auto.
Qed.

Lemma out_after_wr2 (oc oc': list val) (d n a b1 b2: Z) :
  out_after oc oc' d n -> d <= a -> a + 2 <= d + n -> 0 <= a -> a + 2 <= Zlength oc ->
  out_after oc (wr2 oc' a b1 b2) d n.
Proof.
  intros [Hl Hu] ? ? ? ?. split; [rewrite wr2_len; lia|].
  intros i Hi Hn. rewrite wr2_out by lia. apply Hu; auto.
Qed.

Lemma byte_cells_wr2 (oc: list val) (a b1 b2: Z) :
  byte_cells oc -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> byte_cells (wr2 oc a b1 b2).
Proof.
  intros Ho Hb1 Hb2. unfold wr2. apply byte_cells_splice; auto.
  unfold bytes_ok. repeat constructor; unfold is_byte; lia.
Qed.

Lemma byte_cells_wrk (oc: list val) (a: Z) (l: list Z) :
  byte_cells oc -> bytes_ok l -> byte_cells (wrk oc a l).
Proof. intros Ho Hl. unfold wrk. apply byte_cells_splice; auto. Qed.

(* one stream, valid runs: its M symbols q, c of them written at x *)
Definition vs_full (ht: huf_table) (si q: list Z) (M x: Z) (oc: list val) (es pos lo c: Z) : Prop :=
  Zlength q = M /\ vs_head ht si q M pos lo c /\ region_is oc x (sublist 0 c q) /\
  (es = 1 -> (lo + 64 - pos <= 8 \/ lo = 0) /\ (c = 0 \/ 72 <= pos)).

Definition vs_fullm (ht: huf_table) (si q: list Z) (M x: Z) (oc: list val) (j pos lo c: Z) : Prop :=
  Zlength q = M /\ vs_mid ht si q M j pos lo c /\ region_is oc x (sublist 0 c q).

Lemma vsf_mid (ht: huf_table) (si q: list Z) (M x: Z) (oc: list val) (pos lo c: Z) :
  vs_full ht si q M x oc 1 pos lo c -> 8 <= M -> vs_fullm ht si q M x oc 0 pos lo c.
Proof.
  intros (Hq & Hh & Hr & He) HM. destruct (He eq_refl) as [H1 H2].
  split; [auto|split; [|auto]]. apply vs_head_mid; auto. lia.
Qed.

Lemma vsf_step (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (si q: list Z)
    (M x: Z) (oc: list val) (j pos lo c v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok si -> 0 <= j <= 3 -> 0 <= x -> x + M <= Zlength oc ->
  vs_fullm ht si q M x oc j pos lo c ->
  (lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value si) pos L) ->
  x2_step ht L v k b2 nb ->
  vs_fullm ht si q M x (wr2 oc (x + c) (fst (hsym ht L v)) b2) (j + 1) (pos - nb) lo (c + k) /\
  c + 2 <= M /\ 1 <= k <= 2.
Proof.
  intros Htab Hsi Hj Hx HxM (Hq & Hm & Hr) Hv Hst.
  destruct (vs_step Hf ht L c2 si q M j pos lo c v k b2 nb Htab Hsi Hq Hj Hm Hv Hst) as (Hm' & Hc2 & Hk & Hs).
  pose proof (proj1 (proj1 Hm)) as Hc.
  split; [|split; auto]. split; [auto|]. split; [auto|].
  apply region_is_wr2_ext; auto; lia.
Qed.

Lemma vsf_frame (ht: huf_table) (si q: list Z) (M x: Z) (oc: list val) (j pos lo c a b1 b2: Z) :
  0 <= x -> x + M <= Zlength oc -> 0 <= a -> a + 2 <= Zlength oc -> (a + 2 <= x \/ x + M <= a) ->
  vs_fullm ht si q M x oc j pos lo c -> vs_fullm ht si q M x (wr2 oc a b1 b2) j pos lo c.
Proof.
  intros ? ? ? ? Hd (Hq & Hm & Hr). pose proof (proj1 (proj1 Hm)) as Hc.
  split; [auto|split; [auto|]]. apply region_is_wr2_out; auto; rewrite Zlength_sublist; lia.
Qed.

(* the initial state of a stream after BIT_initDStream *)
Lemma last_byte (w: list Z) : bytes_ok w -> w <> [] -> 0 <= last w 0 < 256.
Proof.
  intros H Hne. induction w as [|a w IH]; [congruence|]. inversion H as [|? ? Ha Hw]; subst.
  destruct w as [|b w']; [simpl; unfold is_byte in Ha; lia|]. simpl last. apply IH; auto; congruence.
Qed.

Lemma bs_init_bounds (w: list Z) : bs_wf w = true -> bytes_ok w ->
  (0 <= 8 * Z.max 0 (Zlength w - 8) <= bs_total w /\
   8 * Z.max 0 (Zlength w - 8) + 64 - bs_total w <= 64 /\
   (8 * Z.max 0 (Zlength w - 8) + 64 - bs_total w <= 8 \/ 8 * Z.max 0 (Zlength w - 8) = 0))%Z.
Proof.
  intros Hwf Hb. unfold bs_wf in Hwf. apply andb_prop in Hwf as [H1 H2].
  apply negb_true_iff, Z.eqb_neq in H1. apply negb_true_iff, Z.eqb_neq in H2.
  assert (Hne: w <> []) by (intros ->; apply H1; reflexivity).
  pose proof (last_byte w Hb Hne) as Hl.
  assert (Hh: 0 <= highbit (last w 0) <= 7).
  { unfold highbit. split; [apply Z.log2_nonneg|].
    change 7 with (Z.log2 255). apply Z.log2_le_mono. lia. }
  unfold bs_total. rewrite Zlength_correct in *. pose proof (Zlength_nonneg w).
  destruct (Z.max_spec 0 (Z.of_nat (length w) - 8)) as [[? ->]|[? ->]]; lia.
Qed.

(* the four streams' facts at the loop head *)
Definition x4_valid (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (es p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) : Prop :=
  forall l, huf_lits_with true ht s n = Some l ->
  exists q1 q2 q3 q4, l = q1 ++ q2 ++ q3 ++ q4 /\
    vs_full ht (sublist 6 (6 + le_field s 0 2) s) q1 ((n + 3) / 4) d oc es p1 lo1 k1 /\
    vs_full ht (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) q2 ((n + 3) / 4)
      (d + (n + 3) / 4) oc es p2 lo2 k2 /\
    vs_full ht (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
      q3 ((n + 3) / 4) (d + (n + 3) / 4 + (n + 3) / 4) oc es p3 lo3 k3 /\
    vs_full ht (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) q4 (n - 3 * ((n + 3) / 4))
      (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) oc es p4 lo4 k4.

Definition x4_vmid (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) : Prop :=
  forall l, huf_lits_with true ht s n = Some l ->
  exists q1 q2 q3 q4, l = q1 ++ q2 ++ q3 ++ q4 /\
    vs_fullm ht (sublist 6 (6 + le_field s 0 2) s) q1 ((n + 3) / 4) d oc j1 p1 lo1 k1 /\
    vs_fullm ht (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) q2 ((n + 3) / 4)
      (d + (n + 3) / 4) oc j2 p2 lo2 k2 /\
    vs_fullm ht (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
      q3 ((n + 3) / 4) (d + (n + 3) / 4 + (n + 3) / 4) oc j3 p3 lo3 k3 /\
    vs_fullm ht (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) q4 (n - 3 * ((n + 3) / 4))
      (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) oc j4 p4 lo4 k4.

Lemma x4_head_mid (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) :
  8 <= n - 3 * ((n + 3) / 4) -> n <= 4 * ((n + 3) / 4) ->
  x4_valid ht s n d oc 1 p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 ->
  x4_vmid ht s n d oc 0 p1 lo1 k1 0 p2 lo2 k2 0 p3 lo3 k3 0 p4 lo4 k4.
Proof.
  intros HM Hn H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  exists q1, q2, q3, q4. split; [auto|]. do 3 (split; [apply vsf_mid; auto; lia|]). apply vsf_mid; auto; lia.
Qed.

Lemma x4v_step1 (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (s: list Z) (n d: Z) (oc: list val)
    (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok s -> 0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  0 <= j1 <= 3 ->
  (lo1 <= p1 - L \/ (lo1 = 0 /\ 0 < p1) -> v = bs_peek (bs_value (sublist 6 (6 + le_field s 0 2) s)) p1 L) ->
  x2_step ht L v k b2 nb ->
  x4_vmid ht s n d oc j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_vmid ht s n d (wr2 oc (d + k1) (fst (hsym ht L v)) b2) (j1 + 1) (p1 - nb) lo1 (k1 + k) j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4.
Proof.
  intros Htab Hs Hd Hdn Hs3 Hs4 Hs2 Hj Hv Hst H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  assert (Hw: bytes_ok (sublist 6 (6 + le_field s 0 2) s)) by (apply Forall_sublist; auto).
  assert (Hx: 0 <= d) by lia. assert (HxM: d + ((n + 3) / 4) <= Zlength oc) by lia.
  destruct (vsf_step Hf ht L c2 _ _ _ _ _ _ _ _ _ _ _ _ _ Htab Hw Hj Hx HxM V1 Hv Hst) as (V' & Hc & Hk).
  pose proof (proj1 (proj1 (proj1 (proj2 V1)))) as Hci.
  exists q1, q2, q3, q4. split; [auto|].
  do 3 (split; [first [ exact V' | apply vsf_frame; auto; lia ]|]). first [ exact V' | apply vsf_frame; auto; lia ].
Qed.

Lemma x4v_step2 (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (s: list Z) (n d: Z) (oc: list val)
    (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok s -> 0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  0 <= j2 <= 3 ->
  (lo2 <= p2 - L \/ (lo2 = 0 /\ 0 < p2) -> v = bs_peek (bs_value (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)) p2 L) ->
  x2_step ht L v k b2 nb ->
  x4_vmid ht s n d oc j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_vmid ht s n d (wr2 oc ((d + (n + 3) / 4) + k2) (fst (hsym ht L v)) b2) j1 p1 lo1 k1 (j2 + 1) (p2 - nb) lo2 (k2 + k) j3 p3 lo3 k3 j4 p4 lo4 k4.
Proof.
  intros Htab Hs Hd Hdn Hs3 Hs4 Hs2 Hj Hv Hst H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  assert (Hw: bytes_ok (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)) by (apply Forall_sublist; auto).
  assert (Hx: 0 <= (d + (n + 3) / 4)) by lia. assert (HxM: (d + (n + 3) / 4) + ((n + 3) / 4) <= Zlength oc) by lia.
  destruct (vsf_step Hf ht L c2 _ _ _ _ _ _ _ _ _ _ _ _ _ Htab Hw Hj Hx HxM V2 Hv Hst) as (V' & Hc & Hk).
  pose proof (proj1 (proj1 (proj1 (proj2 V2)))) as Hci.
  exists q1, q2, q3, q4. split; [auto|].
  do 3 (split; [first [ exact V' | apply vsf_frame; auto; lia ]|]). first [ exact V' | apply vsf_frame; auto; lia ].
Qed.

Lemma x4v_step3 (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (s: list Z) (n d: Z) (oc: list val)
    (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok s -> 0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  0 <= j3 <= 3 ->
  (lo3 <= p3 - L \/ (lo3 = 0 /\ 0 < p3) -> v = bs_peek (bs_value (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)) p3 L) ->
  x2_step ht L v k b2 nb ->
  x4_vmid ht s n d oc j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_vmid ht s n d (wr2 oc ((d + (n + 3) / 4 + (n + 3) / 4) + k3) (fst (hsym ht L v)) b2) j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) (p3 - nb) lo3 (k3 + k) j4 p4 lo4 k4.
Proof.
  intros Htab Hs Hd Hdn Hs3 Hs4 Hs2 Hj Hv Hst H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  assert (Hw: bytes_ok (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)) by (apply Forall_sublist; auto).
  assert (Hx: 0 <= (d + (n + 3) / 4 + (n + 3) / 4)) by lia. assert (HxM: (d + (n + 3) / 4 + (n + 3) / 4) + ((n + 3) / 4) <= Zlength oc) by lia.
  destruct (vsf_step Hf ht L c2 _ _ _ _ _ _ _ _ _ _ _ _ _ Htab Hw Hj Hx HxM V3 Hv Hst) as (V' & Hc & Hk).
  pose proof (proj1 (proj1 (proj1 (proj2 V3)))) as Hci.
  exists q1, q2, q3, q4. split; [auto|].
  do 3 (split; [first [ exact V' | apply vsf_frame; auto; lia ]|]). first [ exact V' | apply vsf_frame; auto; lia ].
Qed.

Lemma x4v_step4 (Hf: hsym_facts) (ht: huf_table) (L: Z) (c2: list (val * (val * val))) (s: list Z) (n d: Z) (oc: list val)
    (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v k b2 nb: Z) :
  x2_tab_ok ht L c2 -> bytes_ok s -> 0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  0 <= j4 <= 3 ->
  (lo4 <= p4 - L \/ (lo4 = 0 /\ 0 < p4) -> v = bs_peek (bs_value (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)) p4 L) ->
  x2_step ht L v k b2 nb ->
  x4_vmid ht s n d oc j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_vmid ht s n d (wr2 oc ((d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) + k4) (fst (hsym ht L v)) b2) j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) (p4 - nb) lo4 (k4 + k).
Proof.
  intros Htab Hs Hd Hdn Hs3 Hs4 Hs2 Hj Hv Hst H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  assert (Hw: bytes_ok (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)) by (apply Forall_sublist; auto).
  assert (Hx: 0 <= (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4)) by lia. assert (HxM: (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) + (n - 3 * ((n + 3) / 4)) <= Zlength oc) by lia.
  destruct (vsf_step Hf ht L c2 _ _ _ _ _ _ _ _ _ _ _ _ _ Htab Hw Hj Hx HxM V4 Hv Hst) as (V' & Hc & Hk).
  pose proof (proj1 (proj1 (proj1 (proj2 V4)))) as Hci.
  exists q1, q2, q3, q4. split; [auto|].
  do 3 (split; [first [ exact V' | apply vsf_frame; auto; lia ]|]). first [ exact V' | apply vsf_frame; auto; lia ].
Qed.

Lemma vsf_reload (ht: huf_table) (si q: list Z) (M x: Z) (oc: list val) (pos lo c: Z) (b: bool) :
  vs_fullm ht si q M x oc 4 pos lo c -> (b = true -> fst (bs_reload_fast pos lo) = BIT_unfinished) ->
  vs_full ht si q M x oc (if b then 1 else 0) pos (snd (bs_reload_fast pos lo)) c.
Proof.
  intros (Hq & Hm & Hr) Hb. destruct (vs_reload ht si q M pos lo c Hm) as (Hle & Hh & Hu).
  split; [auto|split; [auto|split; [auto|]]].
  intros Hes. destruct b; [|discriminate]. destruct (Hu (Hb eq_refl)) as [H1 H2]. split; lia.
Qed.

Lemma x4_reload (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) :
  x4_vmid ht s n d oc 4 p1 lo1 k1 4 p2 lo2 k2 4 p3 lo3 k3 4 p4 lo4 k4 ->
  x4_valid ht s n d oc
    (if x4_es (fst (bs_reload_fast p1 lo1)) (fst (bs_reload_fast p2 lo2)) (fst (bs_reload_fast p3 lo3))
          (fst (bs_reload_fast p4 lo4)) then 1 else 0)
    p1 (snd (bs_reload_fast p1 lo1)) k1 p2 (snd (bs_reload_fast p2 lo2)) k2
    p3 (snd (bs_reload_fast p3 lo3)) k3 p4 (snd (bs_reload_fast p4 lo4)) k4.
Proof.
  intros H l Hl. destruct (H l Hl) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
  exists q1, q2, q3, q4. split; [auto|]. unfold x4_es.
  do 3 (split; [apply vsf_reload; auto; intros Hb; rewrite !andb_true_iff, !Z.eqb_eq in Hb; unfold BIT_unfinished; tauto|]).
  apply vsf_reload; auto; intros Hb; rewrite !andb_true_iff, !Z.eqb_eq in Hb; unfold BIT_unfinished; tauto.
Qed.

Lemma vsf_init (ht: huf_table) (w q: list Z) (M x: Z) (oc: list val) :
  bs_wf w = true -> bytes_ok w -> Zlength q = M -> 0 <= M ->
  huf_decode_syms ht w (Z.to_nat M) (bs_total w) = Some (q, 0) ->
  vs_full ht w q M x oc 1 (bs_total w) (8 * Z.max 0 (Zlength w - 8)) 0.
Proof.
  intros Hwf Hw Hq HM Hd. destruct (bs_init_bounds w Hwf Hw) as (H1 & H2 & H3).
  split; [auto|]. split; [|split].
  - split; [lia|]. split; [lia|]. rewrite Z.sub_0_r, sublist_same by lia. auto.
  - intros j Hj. rewrite Zlength_sublist in Hj by lia. lia.
  - intros _. split; [lia | auto].
Qed.

Lemma x4_init (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) :
  huf_ok ht -> bytes_ok s -> 6 <= n -> 6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2 <= Zlength s ->
  0 <= le_field s 0 2 -> 0 <= le_field s 2 2 -> 0 <= le_field s 4 2 ->
  x4_valid ht s n d oc 1
    (bs_total (sublist 6 (6 + le_field s 0 2) s)) (8 * Z.max 0 (le_field s 0 2 - 8)) 0
    (bs_total (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)) (8 * Z.max 0 (le_field s 2 2 - 8)) 0
    (bs_total (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s))
      (8 * Z.max 0 (le_field s 4 2 - 8)) 0
    (bs_total (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s))
      (8 * Z.max 0 (Zlength s - (le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6) - 8)) 0.
Proof.
  intros Hok Hs Hn Hfit H1 H2 H3 l Hl. unfold huf_lits_with in Hl.
  destruct (huf4_split ht s n l Hok Hs ltac:(lia) Hl) as (_ & _ & Hseg & q1 & q2 & q3 & q4 & -> & S1 & S2 & S3 & S4).
  assert (Hseg0: 0 <= (n + 3) / 4) by (apply Z.div_pos; lia).
  exists q1, q2, q3, q4. split; [auto|].
  destruct S1 as (W1 & Q1 & _ & D1), S2 as (W2 & Q2 & _ & D2), S3 as (W3 & Q3 & _ & D3), S4 as (W4 & Q4 & _ & D4).
  assert (Hx: forall x y w (q: list Z) M lo X, 0 <= x <= y -> y <= Zlength s -> w = sublist x y s ->
     Zlength q = M -> 0 <= M -> bs_wf w = true ->
     huf_decode_syms ht w (Z.to_nat M) (bs_total w) = Some (q, 0) -> (lo = 8 * Z.max 0 (y - x - 8))%Z ->
     vs_full ht w q M X oc 1 (bs_total w) lo 0).
  { intros x y w q M lo X Hxy Hy -> HqM HM Hwf Hd ->.
    replace (y - x) with (Zlength (sublist x y s)) by (rewrite Zlength_sublist; lia).
    apply vsf_init; auto. apply Forall_sublist; auto. }
  split; [|split; [|split]].
  - apply (Hx 6 (6 + le_field s 0 2)); auto; try lia; f_equal; f_equal; lia.
  - apply (Hx (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2)); auto; try lia; f_equal; f_equal; lia.
  - apply (Hx (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)); auto; try lia; f_equal; f_equal; lia.

  - apply (Hx (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s)); auto; try lia; f_equal; f_equal; lia.
Qed.

(* ---------- after the loop: HUF_decodeStreamX2's writes and the whole output ---------- *)

Lemma region_is_wrk_out (oc: list val) (x: Z) (w: list Z) (a: Z) (l: list Z) :
  0 <= a -> a + Zlength l <= Zlength oc -> 0 <= x -> x + Zlength w <= Zlength oc ->
  (a + Zlength l <= x \/ x + Zlength w <= a) -> region_is oc x w -> region_is (wrk oc a l) x w.
Proof. intros ? ? ? ? Hd H j Hj. rewrite wrk_out by lia. apply H; auto. Qed.

Lemma region_is_wrk_in (oc: list val) (a: Z) (l: list Z) :
  0 <= a -> a + Zlength l <= Zlength oc -> region_is (wrk oc a l) a l.
Proof. intros ? ? j Hj. apply wrk_in; auto. Qed.

Lemma region_is_app (oc: list val) (x: Z) (w1 w2: list Z) :
  region_is oc x w1 -> region_is oc (x + Zlength w1) w2 -> region_is oc x (w1 ++ w2).
Proof.
  intros H1 H2 j Hj. rewrite Zlength_app in Hj. destruct (zlt j (Zlength w1)).
  - rewrite app_Znth1 by lia. apply H1. pose proof (Zlength_nonneg w2). lia.
  - rewrite app_Znth2 by lia. replace (x + j) with (x + Zlength w1 + (j - Zlength w1)) by lia. apply H2. lia.
Qed.

Lemma region_is_split (oc: list val) (x k: Z) (q: list Z) :
  0 <= k <= Zlength q -> region_is oc x (sublist 0 k q) -> region_is oc (x + k) (sublist k (Zlength q) q) ->
  region_is oc x q.
Proof.
  intros Hk H1 H2. assert (E: q = sublist 0 k q ++ sublist k (Zlength q) q) by list_solve.
  rewrite E at 1. apply region_is_app; auto. rewrite Zlength_sublist by lia. replace (k - 0) with k by lia. auto.
Qed.

Lemma region_bytes_wrk (oc: list val) (x len a: Z) (l: list Z) :
  0 <= a -> a + Zlength l <= Zlength oc -> 0 <= x -> x + len <= Zlength oc -> bytes_ok l ->
  region_bytes oc x len -> region_bytes (wrk oc a l) x len.
Proof.
  intros ? ? ? ? Hl H j Hj. destruct (zlt j a); [|destruct (zlt j (a + Zlength l))].
  - rewrite wrk_out by lia. auto.
  - replace j with (a + (j - a)) by lia. rewrite wrk_in by lia. exists (Znth (j - a) l). split; [|auto].
    unfold bytes_ok in Hl. rewrite Forall_forall in Hl. apply Hl. apply Znth_In. lia.
  - rewrite wrk_out by lia. auto.
Qed.

Lemma region_bytes_wrk_in (oc: list val) (a: Z) (l: list Z) :
  0 <= a -> a + Zlength l <= Zlength oc -> bytes_ok l -> region_bytes (wrk oc a l) a (Zlength l).
Proof.
  intros ? ? Hl j Hj. replace j with (a + (j - a)) by lia. rewrite wrk_in by lia. exists (Znth (j - a) l).
  split; [|auto]. unfold bytes_ok in Hl. rewrite Forall_forall in Hl. apply Hl. apply Znth_In. lia.
Qed.

Lemma region_bytes_app (oc: list val) (x a b: Z) :
  region_bytes oc x a -> region_bytes oc (x + a) b -> region_bytes oc x (a + b).
Proof. intros H1 H2 j Hj. destruct (zlt j (x + a)); [apply H1 | apply H2]; lia. Qed.

Lemma out_after_wrk (oc oc': list val) (d n a: Z) (l: list Z) :
  out_after oc oc' d n -> d <= a -> a + Zlength l <= d + n -> 0 <= a -> a + Zlength l <= Zlength oc ->
  out_after oc (wrk oc' a l) d n.
Proof.
  intros [Hl Hu] ? ? ? ?. split; [rewrite wrk_len; lia|].
  intros i Hi Hn. rewrite wrk_out by lia. apply Hu; auto.
Qed.

(* ---------- VST helpers ---------- *)

(* from HufX2DStream.v *)
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

Lemma sub_pp_gen (ob: val) (x y: Z) :
  isptr ob -> 0 <= x - y <= Ptrofs.max_unsigned ->
  sem_sub_pp tuchar (offset_val x ob) (offset_val y ob) = Some (Vlong (Int64.repr (x - y))).
Proof. intros. replace x with (y + (x - y)) at 1 by lia. apply sub_pp_uchar; auto. Qed.

Lemma ltu_tt (x: Z) (y: int64) :
  0 <= x <= Int64.max_unsigned ->
  typed_true tint (bool2val (negb (Int64.ltu (Int64.repr x) y))) -> Int64.unsigned y <= x.
Proof.
  intros Hx H. unfold Int64.ltu in H. rewrite Int64.unsigned_repr in H by lia.
  destruct (zlt x (Int64.unsigned y)); [|lia]. compute in H. discriminate.
Qed.

Lemma ltu_tf (x: Z) (y: int64) :
  0 <= x <= Int64.max_unsigned ->
  typed_false tint (bool2val (negb (Int64.ltu (Int64.repr x) y))) -> x < Int64.unsigned y.
Proof.
  intros Hx H. unfold Int64.ltu in H. rewrite Int64.unsigned_repr in H by lia.
  destruct (zlt x (Int64.unsigned y)); [lia|]. compute in H. discriminate.
Qed.

Lemma sameblock_off (ob: val) (x y: Z) : isptr ob -> is_true (sameblock (offset_val x ob) (offset_val y ob)).
Proof. destruct ob; try contradiction; intros _. simpl. destruct (peq b b); [reflexivity|congruence]. Qed.

Lemma x_wvp_off (sh: share) (n: Z) (c: list val) (p: val) (i: Z) :
  readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite data_at__memory_block. Intros. simpl sizeof.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma x_test_order (R: mpred) (a b: Z) (p: val) : isptr p ->
  (R |-- weak_valid_pointer (offset_val a p)) -> (R |-- weak_valid_pointer (offset_val b p)) ->
  R |-- denote_tc_test_order (offset_val a p) (offset_val b p).
Proof.
  intros. destruct p; try contradiction.
  apply derives_trans with (weak_valid_pointer (offset_val a (Vptr b0 i)) && weak_valid_pointer (offset_val b (Vptr b0 i))).
  { apply andp_right; auto. }
  Transparent denote_tc_test_order. unfold denote_tc_test_order. Opaque denote_tc_test_order.
  simpl. unfold test_order_ptrs. simpl. destruct (peq b0 b0); [|contradiction]. simpl. apply derives_refl.
Qed.

Ltac wvp_find := first [ eapply x_wvp_off; [eassumption | lia | lia]
  | apply sepcon_weak_valid_pointer2; wvp_find | apply sepcon_weak_valid_pointer1; wvp_find ].

Lemma x_ofs (b: block) (i: ptrofs) (n a: Z) : field_compatible (tarray tuchar n) [] (Vptr b i) -> 0 <= a <= n ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr a)) = Ptrofs.unsigned i + a.
Proof.
  intros. destruct H as [_ [_ [Hs _]]]. simpl in Hs. rewrite Z.max_r in Hs by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr a) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma x_cmp (p: val) (n a c: Z) : field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= c <= n ->
  sem_cmp_pp Cle (offset_val a p) (offset_val c p) = Some (bool2val (a <=? c)) /\
  sem_cmp_pp Clt (offset_val a p) (offset_val c p) = Some (bool2val (a <? c)).
Proof.
  intros. destruct p; try (destruct H; contradiction).
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !(x_ofs b i n) by auto.
  split; f_equal; f_equal.
  - destruct (zlt _ _), (a <=? c) eqn:E; simpl; auto; try (apply Z.leb_le in E; lia); try (apply Z.leb_gt in E; lia).
  - destruct (zlt _ _), (a <? c) eqn:E; simpl; auto; try (apply Z.ltb_lt in E; lia); try (apply Z.ltb_ge in E; lia).
Qed.

Lemma int_eq_small (x: Z) : 0 <= x <= 3 -> Int.eq (Int.repr x) (Int.repr 0) = (x =? 0).
Proof.
  intros Hx. destruct (Z.eq_dec x 0) as [->|Hn]; [reflexivity|].
  rewrite Int.eq_false; [symmetry; apply Z.eqb_neq; auto|].
  intros C. apply (f_equal Int.unsigned) in C. rewrite !Int.unsigned_repr in C by rep_lia. lia.
Qed.

Lemma ltu64_repr (n x: Z) :
  0 <= n <= Int64.max_unsigned -> 0 <= x <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr n) (Int64.repr x) = (n <? x).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt n x); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma and_b2z_tt (b1 b2: bool) :
  typed_true tint (Vint (Int.and (Int.repr (Z.b2z b1)) (Int.repr (Z.b2z b2)))) -> b1 = true /\ b2 = true.
Proof. destruct b1, b2; compute; intros H; first [split; reflexivity | discriminate H]. Qed.

Lemma and_b2z_tf (b1 b2: bool) :
  typed_false tint (Vint (Int.and (Int.repr (Z.b2z b1)) (Int.repr (Z.b2z b2)))) -> b1 = false \/ b2 = false.
Proof. destruct b1, b2; compute; intros H; first [left; reflexivity | right; reflexivity | discriminate H]. Qed.



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

Lemma osub_olimit {cs: compspecs} (p: val) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tulong p
    (eval_binop Osub tulong tint (if complete_type cenv_cs tulong then Vptrofs (Ptrofs.repr (sizeof tulong)) else Vundef)
       (Vint (Int.repr 1)))) = offset_val (-7) p.
Proof. intros Hp. destruct p; try contradiction. simpl. rewrite Ptrofs.sub_add_opp. reflexivity. Qed.

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

(* zstd's do { .. } while (0): the body, its normal end and its break both leave the loop *)
Lemma semax_dw0 {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred)
  (s: statement) (R: ret_assert) :
  semax Delta P s (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop s Sbreak) R.
Proof.
  intros H. eapply semax_loop; [exact H|].
  eapply semax_pre; [|apply semax_break]. destruct R; simpl. intros rho; apply andp_left2, derives_refl.
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

(* the table is ExHuf's (BRep.hufdt_x_at true); kept folded: VST's entailer would substitute L and c2 *)
Definition x4_tabx (ht: huf_table) (L: Z) (c2: list (val * (val * val))) : Prop :=
  L = xh_x2_log ht /\ c2 = map x2v (xh_cells_x2 ht L).

Lemma hufdt_fold (sht: share) (ht: huf_table) (dt: val) (L: Z) (res: val) (c2: list (val * (val * val))) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> align_compatible tuint dt -> byte_val res ->
  Zlength c2 = 2 ^ L -> (forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2)) ->
  x4_tabx ht L c2 ->
  data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res))) dt *
  data_at sht (tarray t_deltx2 (2 ^ L)) c2 (offset_val 4 dt) *
  memory_block sht (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) dt)
  |-- hufdt_x_at true sht ht dt.
Proof. intros ? ? ? ? ? ? [? ?]. unfold hufdt_x_at. Exists L res. Exists c2. entailer!. Qed.

Lemma rep_data_at_ (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep sh gv s start pos lo p |-- data_at_ sh t_bitD2 p.
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
  let r := fresh "r" in Intros r;
  let Hr := fresh "Hr" in assert (Hr: 0 <= r <= Int64.max_unsigned) by lia;
  apply semax_dw0; abbreviate_semax; forward_call r;
  match goal with H: is_error_code r = true |- _ => rewrite H end;
  forward_if; [ | exfalso; match goal with H: Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact H end].

Ltac x4_chk_ok li :=
  let r := fresh "r" in Intros r; subst r;
  apply semax_dw0; abbreviate_semax; forward_call li;
  assert (is_error_code li = false) as -> by (unfold is_error_code; apply Z.ltb_ge; rep_lia);
  forward_if; [ match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end
              | forward; apply ENTAIL_refl ].

Ltac urepr := repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
  rewrite (Int64.unsigned_repr x) in H by rep_lia end.

Lemma tt_b2v (b: bool) : typed_true tint (bool2val b) -> b = true.
Proof. destruct b; intros H; [reflexivity | inv H]. Qed.

Lemma tf_b2v (b: bool) : typed_false tint (bool2val b) -> b = false.
Proof. destruct b; intros H; [inv H | reflexivity]. Qed.

(* the exact model at the loop head: x_huf_decode is x4_after of the rest of the main loop (es = 1, with
   fuel f) or of the current state (es = 0); the states are the window-pointer states xb_of; after a reload
   that kept the loop going, at most 7 bits are consumed (all four reloads were unfinished) *)
Definition x4_mx (ht: huf_table) (s: list Z) (n es: Z) (f: nat) (p1 lo1 p2 lo2 p3 lo3 p4 lo4: Z)
    (o1 o2 o3 o4: list Z) : Prop :=
  x_huf_decode (xhuf_of true ht) false s n =
    x4_after ht s n
      (if es =? 1
       then x4_loop ht s n f (xb_of (x4s1 s) p1 lo1) (xb_of (x4s2 s) p2 lo2) (xb_of (x4s3 s) p3 lo3)
              (xb_of (x4s4 s) p4 lo4) o1 o2 o3 o4
       else ((xb_of (x4s1 s) p1 lo1, xb_of (x4s2 s) p2 lo2, xb_of (x4s3 s) p3 lo3, xb_of (x4s4 s) p4 lo4),
             (o1, o2, o3, o4))) /\
  (es = 1 -> Z.max 0 (n - 7 - 3 * ((n + 3) / 4) - Zlength o4) < Z.of_nat f) /\
  (es = 1 -> 0 < Zlength o4 ->
   lo1 + 64 - p1 <= 7 /\ lo2 + 64 - p2 <= 7 /\ lo3 + 64 - p3 <= 7 /\ lo4 + 64 - p4 <= 7).

(* the C's positions are the lengths of the model's outputs (kept folded: VST's entailer would substitute) *)
Definition x4_lens (o1 o2 o3 o4: list Z) (k1 k2 k3 k4: Z) : Prop :=
  Zlength o1 = k1 /\ Zlength o2 = k2 /\ Zlength o3 = k3 /\ Zlength o4 = k4.

(* the exact facts at the loop head: the model, the bytes o_i emitted by each stream (k_i of them), the output
   array (HufX2D4M.x4_mem) *)
Definition x4_ex (ht: huf_table) (s: list Z) (n: Z) (oc: list val) (d es: Z) (f: nat)
    (p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) (o1 o2 o3 o4: list Z) : Prop :=
  x4_mx ht s n es f p1 lo1 p2 lo2 p3 lo3 p4 lo4 o1 o2 o3 o4 /\ x4_lens o1 o2 o3 o4 k1 k2 k3 k4 /\
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 o1 o2 o3 o4.

(* the loop has stopped: x_huf_decode is x4_after of the current state *)
Lemma x4_mx_exit (ht: huf_table) (s: list Z) (n es: Z) (f: nat) (p1 lo1 p2 lo2 p3 lo3 p4 lo4: Z)
    (o1 o2 o3 o4: list Z) :
  x4_mx ht s n es f p1 lo1 p2 lo2 p3 lo3 p4 lo4 o1 o2 o3 o4 -> (es = 0 \/ es = 1) ->
  (es = 0 \/ n - 3 * ((n + 3) / 4) - 7 <= Zlength o4) ->
  x_huf_decode (xhuf_of true ht) false s n =
    x4_after ht s n ((xb_of (x4s1 s) p1 lo1, xb_of (x4s2 s) p2 lo2, xb_of (x4s3 s) p3 lo3, xb_of (x4s4 s) p4 lo4),
                     (o1, o2, o3, o4)).
Proof.
  intros (E & Hf & _) Hes Hx. destruct Hes as [-> | ->]; [exact E|].
  rewrite Z.eqb_refl in E. destruct Hx as [Hx|Hx]; [discriminate|].
  specialize (Hf eq_refl). destruct f as [|f]; [simpl in Hf; lia|].
  rewrite E. rewrite x4_loop_stop by lia. reflexivity.
Qed.

(* the any-input facts at the loop head: positions in the 4 segments (streams 1-3 may overrun, bounded by
   twice stream 4's), bits consumed, the bytes written *)
Definition x4_any (oc oc': list val) (d n: Z) (es p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) : Prop :=
  (es = 0 \/ es = 1) /\
  0 <= k1 <= 2 * k4 /\ 0 <= k2 <= 2 * k4 /\ 0 <= k3 <= 2 * k4 /\ 0 <= k4 <= n - 3 * ((n + 3) / 4) /\
  ((es = 0 \/ 1 <= k4) -> 4 <= k1) /\
  lo1 + 64 - p1 <= 112 /\ lo2 + 64 - p2 <= 112 /\ lo3 + 64 - p3 <= 112 /\ lo4 + 64 - p4 <= 112 /\
  (es = 1 -> (lo1 + 64 - p1 <= 64 /\ (lo1 < 64 \/ lo1 + 64 - p1 <= 8)) /\ (lo2 + 64 - p2 <= 64 /\ (lo2 < 64 \/ lo2 + 64 - p2 <= 8)) /\
    (lo3 + 64 - p3 <= 64 /\ (lo3 < 64 \/ lo3 + 64 - p3 <= 8)) /\ (lo4 + 64 - p4 <= 64 /\ (lo4 < 64 \/ lo4 + 64 - p4 <= 8))) /\
  out_after oc oc' d n /\ region_bytes oc' d k1 /\ region_bytes oc' (d + (n + 3) / 4) k2 /\
  region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4) k3 /\ region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) k4 /\
  (byte_cells oc -> byte_cells oc').

Definition x4_state (gv: globals) (ht: huf_table) (sht: share) (dt: val) (L: Z) (res: val) (c2: list (val * (val * val)))
  (sho: share) (ob: val) (oc: list val) (d n: Z) (sh: share) (base: val) (N: Z) (c: list val) (off: Z) (s: list Z)
  (v1 v2 v3 v4 vd: val) (X: Z -> Z -> Prop) : environ -> mpred :=
  @exp (environ -> mpred) _ (Z) (fun es => @exp (environ -> mpred) _ (Z) (fun p1 => @exp (environ -> mpred) _ (Z) (fun lo1 => @exp (environ -> mpred) _ (Z) (fun k1 => @exp (environ -> mpred) _ (Z) (fun p2 => @exp (environ -> mpred) _ (Z) (fun lo2 => @exp (environ -> mpred) _ (Z) (fun k2 => @exp (environ -> mpred) _ (Z) (fun p3 => @exp (environ -> mpred) _ (Z) (fun lo3 => @exp (environ -> mpred) _ (Z) (fun k3 => @exp (environ -> mpred) _ (Z) (fun p4 => @exp (environ -> mpred) _ (Z) (fun lo4 => @exp (environ -> mpred) _ (Z) (fun k4 => @exp (environ -> mpred) _ (list val) (fun oc' =>
  @exp (environ -> mpred) _ nat (fun f => @exp (environ -> mpred) _ (list Z) (fun o1 =>
  @exp (environ -> mpred) _ (list Z) (fun o2 => @exp (environ -> mpred) _ (list Z) (fun o3 =>
  @exp (environ -> mpred) _ (list Z) (fun o4 =>
  PROP (x4_any oc oc' d n es p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4;
        x4_valid ht s n d oc' es p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4; X es k4;
        x4_ex ht s n oc' d es f p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 o1 o2 o3 o4)
  LOCAL (temp _endSignal (Vint (Int.repr es));
         temp _op4 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) ob);
         temp _op3 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + k3) ob);
         temp _op2 (offset_val (d + (n + 3) / 4 + k2) ob); temp _op1 (offset_val (d + k1) ob);
         temp _opStart4 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) ob);
         temp _opStart3 (offset_val (d + (n + 3) / 4 + (n + 3) / 4) ob);
         temp _opStart2 (offset_val (d + (n + 3) / 4) ob);
         temp _dt (offset_val 4 dt); temp _dtLog (Vint (Int.repr L));
         temp _olimit (offset_val (d + (n + -7)) ob); temp _oend (offset_val (d + n) ob);
         lvar _dtd (Tstruct ___gp_DTableDesc noattr) vd;
         lvar _bitD4 (Tstruct ___gp_BIT_DStream_t noattr) v4; lvar _bitD3 (Tstruct ___gp_BIT_DStream_t noattr) v3;
         lvar _bitD2 (Tstruct ___gp_BIT_DStream_t noattr) v2; lvar _bitD1 (Tstruct ___gp_BIT_DStream_t noattr) v1;
         gvars gv; temp _dstSize (Vlong (Int64.repr n)))
  SEP (BIT_DStream_rep Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)
         (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4;
       bit_src sh (offset_val off base) s; zstd_globals gv;
       BIT_DStream_rep Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
         (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3;
       BIT_DStream_rep Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)
         (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2;
       BIT_DStream_rep Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1;
       data_at Tsh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res))) vd;
       data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res))) dt;
       data_at sht (tarray t_deltx2 (2 ^ L)) c2 (offset_val 4 dt);
       memory_block sht (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) dt);
       data_at sho (tarray tuchar (Zlength oc)) oc' ob;
       data_at sh (tarray tuchar off) (sublist 0 off c) base;
       data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c) (offset_val (off + Zlength s) base))))))))))))))))))))).

Lemma cmp_gt_tt (len a c: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= c <= len ->
  typed_true tint (match sem_cmp_pp Cgt (offset_val a ob) (offset_val c ob) with Some v' => v' | None => Vundef end) ->
  c < a.
Proof. intros Hf Ha Hc H. rewrite (sem_cmp_gt_offsets len) in H by auto. apply tt_b2v, Z.ltb_lt in H. auto. Qed.

Lemma cmp_gt_tf (len a c: Z) (ob: val) :
  field_compatible (tarray tuchar len) [] ob -> 0 <= a <= len -> 0 <= c <= len ->
  typed_false tint (match sem_cmp_pp Cgt (offset_val a ob) (offset_val c ob) with Some v' => v' | None => Vundef end) ->
  a <= c.
Proof. intros Hf Ha Hc H. rewrite (sem_cmp_gt_offsets len) in H by auto. apply tf_b2v, Z.ltb_ge in H. auto. Qed.

Lemma bit_src_ok_win (s: list Z) (bp: val) (x y: Z) :
  0 <= x <= y -> y <= Zlength s -> bit_src_ok (sublist x y s) (offset_val x bp) bp s x.
Proof.
  intros Hxy Hy. unfold bit_src_ok. rewrite Zlength_sublist by lia.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. f_equal. lia.
Qed.

(* ---------- the output after the four HUF_decodeStreamX2 ---------- *)

Section Final.
Variables (oc oc': list val) (d n k1 k2 k3 k4: Z) (m1 m2 m3 m4: list Z).
Hypotheses (Hd: 0 <= d) (Hdn: d + n <= Zlength oc) (Hn3: 3 * ((n + 3) / 4) <= n) (Hn4: n <= 4 * ((n + 3) / 4))
  (HS: 2 <= (n + 3) / 4)
  (Hk1: 0 <= k1 <= (n + 3) / 4) (Hk2: 0 <= k2 <= (n + 3) / 4) (Hk3: 0 <= k3 <= (n + 3) / 4)
  (Hk4: 0 <= k4 <= n - 3 * ((n + 3) / 4))
  (Hm1: Zlength m1 = (n + 3) / 4 - k1) (Hm2: Zlength m2 = (n + 3) / 4 - k2) (Hm3: Zlength m3 = (n + 3) / 4 - k3)
  (Hm4: Zlength m4 = n - 3 * ((n + 3) / 4) - k4) (Hlen: Zlength oc' = Zlength oc).

Definition fo1 := wrk oc' (d + k1) m1.
Definition fo2 := wrk fo1 (d + (n + 3) / 4 + k2) m2.
Definition fo3 := wrk fo2 (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3.
Definition fo4 := wrk fo3 (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) m4.

Lemma fin_len : Zlength fo1 = Zlength oc /\ Zlength fo2 = Zlength oc /\ Zlength fo3 = Zlength oc /\
  Zlength fo4 = Zlength oc.
Proof.
  assert (L1: Zlength fo1 = Zlength oc) by (unfold fo1; rewrite wrk_len; lia).
  assert (L2: Zlength fo2 = Zlength oc) by (unfold fo2; rewrite wrk_len; lia).
  assert (L3: Zlength fo3 = Zlength oc) by (unfold fo3; rewrite wrk_len; lia).
  assert (L4: Zlength fo4 = Zlength oc) by (unfold fo4; rewrite wrk_len; lia).
  auto.
Qed.

Lemma fin_out : out_after oc oc' d n -> out_after oc fo4 d n.
Proof.
  destruct fin_len as (L1 & L2 & L3 & L4). intros H.
  unfold fo4; apply out_after_wrk; [| lia | lia | lia | lia].
  unfold fo3; apply out_after_wrk; [| lia | lia | lia | lia].
  unfold fo2; apply out_after_wrk; [| lia | lia | lia | lia].
  unfold fo1; apply out_after_wrk; [auto | lia | lia | lia | lia].
Qed.

Lemma fin_bytes : bytes_ok m1 -> bytes_ok m2 -> bytes_ok m3 -> bytes_ok m4 ->
  region_bytes oc' d k1 -> region_bytes oc' (d + (n + 3) / 4) k2 ->
  region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4) k3 ->
  region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) k4 -> region_bytes fo4 d n.
Proof.
  intros B1 B2 B3 B4 R1 R2 R3 R4. destruct fin_len as (L1 & L2 & L3 & L4).
  assert (Q1: forall x len, 0 <= x -> x + len <= Zlength oc -> region_bytes oc' x len -> region_bytes fo1 x len).
  { intros. unfold fo1. apply region_bytes_wrk; auto; lia. }
  assert (Q2: forall x len, 0 <= x -> x + len <= Zlength oc -> region_bytes fo1 x len -> region_bytes fo2 x len).
  { intros. unfold fo2. apply region_bytes_wrk; auto; rewrite ?L1; lia. }
  assert (Q3: forall x len, 0 <= x -> x + len <= Zlength oc -> region_bytes fo2 x len -> region_bytes fo3 x len).
  { intros. unfold fo3. apply region_bytes_wrk; auto; rewrite ?L2; lia. }
  assert (Q4: forall x len, 0 <= x -> x + len <= Zlength oc -> region_bytes fo3 x len -> region_bytes fo4 x len).
  { intros. unfold fo4. apply region_bytes_wrk; auto; rewrite ?L3; lia. }
  assert (P1: region_bytes fo1 (d + k1) ((n + 3) / 4 - k1)).
  { rewrite <- Hm1. unfold fo1. apply region_bytes_wrk_in; auto; lia. }
  assert (P2: region_bytes fo2 (d + (n + 3) / 4 + k2) ((n + 3) / 4 - k2)).
  { rewrite <- Hm2. unfold fo2. apply region_bytes_wrk_in; auto; rewrite ?L1; lia. }
  assert (P3: region_bytes fo3 (d + (n + 3) / 4 + (n + 3) / 4 + k3) ((n + 3) / 4 - k3)).
  { rewrite <- Hm3. unfold fo3. apply region_bytes_wrk_in; auto; rewrite ?L2; lia. }
  assert (P4: region_bytes fo4 (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (n - 3 * ((n + 3) / 4) - k4)).
  { rewrite <- Hm4. unfold fo4. apply region_bytes_wrk_in; auto; rewrite ?L3; lia. }
  set (S := (n + 3) / 4) in *.
  assert (G: forall x k M, region_bytes fo4 x k -> region_bytes fo4 (x + k) (M - k) -> region_bytes fo4 x M).
  { intros x k M HA HB. replace M with (k + (M - k)) by lia. apply region_bytes_app; auto. }
  assert (G1: region_bytes fo4 d S) by (apply (G d k1 S); repeat (first [assumption | apply Q4; [lia|lia|] | apply Q3; [lia|lia|] | apply Q2; [lia|lia|] | apply Q1; [lia|lia|]])).
  assert (G2: region_bytes fo4 (d + S) S) by (apply (G (d + S) k2 S); repeat (first [assumption | apply Q4; [lia|lia|] | apply Q3; [lia|lia|] | apply Q2; [lia|lia|] | apply Q1; [lia|lia|]])).
  assert (G3: region_bytes fo4 (d + S + S) S) by (apply (G (d + S + S) k3 S); repeat (first [assumption | apply Q4; [lia|lia|] | apply Q3; [lia|lia|] | apply Q2; [lia|lia|] | apply Q1; [lia|lia|]])).
  assert (G4: region_bytes fo4 (d + S + S + S) (n - 3 * S)) by (apply (G (d + S + S + S) k4 (n - 3 * S)); repeat (first [assumption | apply Q4; [lia|lia|] | apply Q3; [lia|lia|] | apply Q2; [lia|lia|] | apply Q1; [lia|lia|]])).
  replace n with (S + S + S + (n - 3 * S)) at 1 by lia.
  apply region_bytes_app; [apply region_bytes_app; [apply region_bytes_app|]|]; auto.
  - replace (d + (S + S)) with (d + S + S) by lia. auto.
  - replace (d + (S + S + S)) with (d + S + S + S) by lia. auto.
Qed.

Lemma fin_valid (q1 q2 q3 q4: list Z) :
  Zlength q1 = (n + 3) / 4 -> Zlength q2 = (n + 3) / 4 -> Zlength q3 = (n + 3) / 4 ->
  Zlength q4 = n - 3 * ((n + 3) / 4) ->
  region_is oc' d (sublist 0 k1 q1) -> region_is oc' (d + (n + 3) / 4) (sublist 0 k2 q2) ->
  region_is oc' (d + (n + 3) / 4 + (n + 3) / 4) (sublist 0 k3 q3) ->
  region_is oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) (sublist 0 k4 q4) ->
  m1 = sublist k1 (Zlength q1) q1 -> m2 = sublist k2 (Zlength q2) q2 -> m3 = sublist k3 (Zlength q3) q3 ->
  m4 = sublist k4 (Zlength q4) q4 ->
  region_is fo4 d (q1 ++ q2 ++ q3 ++ q4).
Proof.
  intros Z1 Z2 Z3 Z4 R1 R2 R3 R4 E1 E2 E3 E4. destruct fin_len as (L1 & L2 & L3 & L4).
  set (S := (n + 3) / 4) in *.
  assert (Q1: forall x w, 0 <= x -> x + Zlength w <= Zlength oc ->
            (d + k1 + Zlength m1 <= x \/ x + Zlength w <= d + k1) -> region_is oc' x w -> region_is fo1 x w).
  { intros. unfold fo1. apply region_is_wrk_out; auto; lia. }
  assert (Q2: forall x w, 0 <= x -> x + Zlength w <= Zlength oc ->
            (d + S + k2 + Zlength m2 <= x \/ x + Zlength w <= d + S + k2) -> region_is fo1 x w -> region_is fo2 x w).
  { intros. unfold fo2. apply region_is_wrk_out; auto; rewrite ?L1; lia. }
  assert (Q3: forall x w, 0 <= x -> x + Zlength w <= Zlength oc ->
            (d + S + S + k3 + Zlength m3 <= x \/ x + Zlength w <= d + S + S + k3) -> region_is fo2 x w -> region_is fo3 x w).
  { intros. unfold fo3. apply region_is_wrk_out; auto; rewrite ?L2; lia. }
  assert (Q4: forall x w, 0 <= x -> x + Zlength w <= Zlength oc ->
            (d + S + S + S + k4 + Zlength m4 <= x \/ x + Zlength w <= d + S + S + S + k4) -> region_is fo3 x w ->
            region_is fo4 x w).
  { intros. unfold fo4. apply region_is_wrk_out; auto; rewrite ?L3; lia. }
  assert (P1: region_is fo1 (d + k1) m1) by (unfold fo1; apply region_is_wrk_in; lia).
  assert (P2: region_is fo2 (d + S + k2) m2) by (unfold fo2; apply region_is_wrk_in; rewrite ?L1; lia).
  assert (P3: region_is fo3 (d + S + S + k3) m3) by (unfold fo3; apply region_is_wrk_in; rewrite ?L2; lia).
  assert (P4: region_is fo4 (d + S + S + S + k4) m4) by (unfold fo4; apply region_is_wrk_in; rewrite ?L3; lia).
  assert (W1: Zlength (sublist 0 k1 q1) = k1) by (rewrite Zlength_sublist; lia).
  assert (W2: Zlength (sublist 0 k2 q2) = k2) by (rewrite Zlength_sublist; lia).
  assert (W3: Zlength (sublist 0 k3 q3) = k3) by (rewrite Zlength_sublist; lia).
  assert (W4: Zlength (sublist 0 k4 q4) = k4) by (rewrite Zlength_sublist; lia).
  apply region_is_app; [|rewrite Z1; apply region_is_app; [|rewrite Z2; apply region_is_app; [|rewrite Z3]]].
  - apply (region_is_split _ _ k1); [lia | repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]) |].
    rewrite <- E1. replace (d + k1) with (d + k1) by lia. repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]).
  - apply (region_is_split _ _ k2); [lia | repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]) |].
    rewrite <- E2. repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]).
  - apply (region_is_split _ _ k3); [lia | repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]) |].
    rewrite <- E3. repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]).
  - apply (region_is_split _ _ k4); [lia | repeat (first [assumption | apply Q4; [lia|lia|lia|] | apply Q3; [lia|lia|lia|] | apply Q2; [lia|lia|lia|] | apply Q1; [lia|lia|lia|]]) |].
    rewrite <- E4. auto.
Qed.

End Final.

Lemma fin_bc (oc': list val) (d n k1 k2 k3 k4: Z) (m1 m2 m3 m4: list Z) :
  byte_cells oc' -> bytes_ok m1 -> bytes_ok m2 -> bytes_ok m3 -> bytes_ok m4 ->
  byte_cells (fo4 oc' d n k1 k2 k3 k4 m1 m2 m3 m4).
Proof. intros. unfold fo4, fo3, fo2, fo1. repeat apply byte_cells_wrk; auto. Qed.

Lemma and01 (b1 b2: bool) :
  Int.and (Int.repr (if b1 then 1 else 0)) (Int.repr (if b2 then 1 else 0)) = Int.repr (if andb b1 b2 then 1 else 0).
Proof. destruct b1, b2; reflexivity. Qed.

Ltac fa13 X := specialize (X ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).

Ltac zl := repeat match goal with H: Zlength (wrk _ _ _) = _ |- context [Zlength (wrk _ _ _)] => rewrite H end; lia.

(* ---------- the code after the main loop, as its own lemma ---------- *)

Fixpoint seq_drop (k: nat) (s: statement) : statement :=
  match k with O => s | S k' => match s with Ssequence _ s2 => seq_drop k' s2 | _ => Sskip end end.

Definition x4_tail : statement := seq_drop 34 (fn_body f_HUF_decompress4X2_usingDTable_internal_body).
Definition Delta4 : tycontext := func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil.

Definition x4_post (gv: globals) (sht: share) (dt: val) (ht: huf_table) (sho: share) (ob: val) (oc: list val)
    (d n: Z) (sh: share) (base: val) (N: Z) (c: list val) (s: list Z) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong
    (EX (r : Z) (oc' : list val),
     PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n; (byte_cells oc -> byte_cells oc');
           is_error_code r = false -> r = n /\ (exists l : list Z, sublist d (d + n) oc' = zbytes l /\ bytes_ok l);
           match huf_lits_with true ht s n with
           | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
           | None => True
           end;
           match x_huf_decode (xhuf_of true ht) (negb true) s n with
           | None => is_error_code r = true
           | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
           end)
     RETURN (Vlong (Int64.repr r))
     SEP (zstd_globals gv; hufdt_x_at true sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
          data_at sh (tarray tuchar N) c base))%argsassert)
    (stackframe_of f_HUF_decompress4X2_usingDTable_internal_body).

(* After the checks op_i <= opStart_{i+1}, the four HUF_decodeStreamX2 (bytes m_i, new states (e_i, f_i)) and
   the four BIT_endOfDStream (eb, as the C combines them): x_huf_decode returns the bytes when eb holds, else
   None; and when eb holds, no stream is doomed, so the array holds each stream's loop bytes o_i. *)
Lemma x4_tail_model (ht: huf_table) (s: list Z) (n d: Z) (oc: list val)
    (p1 lo1 p2 lo2 p3 lo3 p4 lo4 e1 f1 e2 f2 e3 f3 e4 f4 k1 k2 k3 k4: Z) (o1 o2 o3 o4 m1 m2 m3 m4: list Z) :
  x_huf_decode (xhuf_of true ht) false s n =
    x4_after ht s n ((xb_of (x4s1 s) p1 lo1, xb_of (x4s2 s) p2 lo2, xb_of (x4s3 s) p3 lo3, xb_of (x4s4 s) p4 lo4),
                     (o1, o2, o3, o4)) ->
  x4_lens o1 o2 o3 o4 k1 k2 k3 k4 -> x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 o1 o2 o3 o4 ->
  k1 <= (n + 3) / 4 -> k2 <= (n + 3) / 4 -> k3 <= (n + 3) / 4 ->
  bit_inv (x4s1 s) p1 lo1 -> bit_inv (x4s2 s) p2 lo2 -> bit_inv (x4s3 s) p3 lo3 ->
  bit_inv (x4s1 s) e1 f1 -> bit_inv (x4s2 s) e2 f2 -> bit_inv (x4s3 s) e3 f3 -> bit_inv (x4s4 s) e4 f4 ->
  fst (xh_x2_stream (xhuf_of true ht) (x4s1 s) (xb_of (x4s1 s) p1 lo1) ((n + 3) / 4 - k1)) = m1 /\
    xb_rel (x4s1 s) e1 f1 (snd (xh_x2_stream (xhuf_of true ht) (x4s1 s) (xb_of (x4s1 s) p1 lo1) ((n + 3) / 4 - k1))) ->
  fst (xh_x2_stream (xhuf_of true ht) (x4s2 s) (xb_of (x4s2 s) p2 lo2) ((n + 3) / 4 - k2)) = m2 /\
    xb_rel (x4s2 s) e2 f2 (snd (xh_x2_stream (xhuf_of true ht) (x4s2 s) (xb_of (x4s2 s) p2 lo2) ((n + 3) / 4 - k2))) ->
  fst (xh_x2_stream (xhuf_of true ht) (x4s3 s) (xb_of (x4s3 s) p3 lo3) ((n + 3) / 4 - k3)) = m3 /\
    xb_rel (x4s3 s) e3 f3 (snd (xh_x2_stream (xhuf_of true ht) (x4s3 s) (xb_of (x4s3 s) p3 lo3) ((n + 3) / 4 - k3))) ->
  fst (xh_x2_stream (xhuf_of true ht) (x4s4 s) (xb_of (x4s4 s) p4 lo4) (n - 3 * ((n + 3) / 4) - k4)) = m4 /\
    xb_rel (x4s4 s) e4 f4
      (snd (xh_x2_stream (xhuf_of true ht) (x4s4 s) (xb_of (x4s4 s) p4 lo4) (n - 3 * ((n + 3) / 4) - k4))) ->
  let eb := andb (andb (andb (andb (f1 =? 0) (e1 =? 0)) (andb (f2 =? 0) (e2 =? 0))) (andb (f3 =? 0) (e3 =? 0)))
              (andb (f4 =? 0) (e4 =? 0)) in
  x_huf_decode (xhuf_of true ht) false s n = (if eb then Some (o1 ++ m1 ++ o2 ++ m2 ++ o3 ++ m3 ++ o4 ++ m4) else None) /\
  (eb = true -> region_is oc d o1 /\ region_is oc (d + (n + 3) / 4) o2 /\
     region_is oc (d + (n + 3) / 4 + (n + 3) / 4) o3 /\ region_is oc (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) o4).
Proof.
  intros HR Hl Hm Hk1 Hk2 Hk3 I1 I2 I3 J1 J2 J3 J4 [M1 X1] [M2 X2] [M3 X3] [M4 X4] eb.
  destruct Hl as (Ho1 & Ho2 & Ho3 & Ho4).
  rewrite x4_after_eq in HR by lia. cbv zeta in HR.
  rewrite Ho1, Ho2, Ho3, Ho4 in HR.
  rewrite (xb_end_rel _ _ _ _ J1 X1), (xb_end_rel _ _ _ _ J2 X2), (xb_end_rel _ _ _ _ J3 X3),
    (xb_end_rel _ _ _ _ J4 X4), M1, M2, M3, M4 in HR.
  assert (Heb: forall b1 b2 b3 b4: bool, andb (andb b1 b2) (andb b3 b4) = andb (andb (andb b1 b2) b3) b4)
    by (intros [] [] [] []; reflexivity).
  rewrite Heb in HR. split; [exact HR|].
  intros E. unfold eb in E. rewrite !andb_true_iff in E. destruct E as (((B1 & B2) & B3) & B4).
  assert (Hnd: forall (w: list Z) (p lo e f k: Z) (o: list Z), bit_inv w p lo -> bit_inv w e f -> Zlength o = k ->
            k <= (n + 3) / 4 ->
            xb_rel w e f (snd (xh_x2_stream (xhuf_of true ht) w (xb_of w p lo) ((n + 3) / 4 - k))) ->
            (f =? 0) = true /\ (e =? 0) = true -> ~ x4_doom n o p lo).
  { intros w p lo e f k o Hi Hj Ho Hk X B [Hd | [Hd Hb]]; [lia|].
    replace ((n + 3) / 4 - k) with 0 in X by lia.
    destruct Hi as (_ & _ & Hlo & _ & _ & Hp & _).
    assert (B': andb (f =? 0) (e =? 0) = true) by (apply andb_true_iff; exact B).
    rewrite <- (xb_end_rel _ _ _ _ Hj X), x4_doom_end in B' by lia. discriminate. }
  apply (x4_mem_ok oc d n p1 lo1 p2 lo2 p3 lo3 o1 o2 o3 o4 Hm).
  - apply (Hnd (x4s1 s) p1 lo1 e1 f1 k1 o1); auto.
  - apply (Hnd (x4s2 s) p2 lo2 e2 f2 k2 o2); auto.
  - apply (Hnd (x4s3 s) p3 lo3 e3 f3 k3 o3); auto.
Qed.

(* an error return where x_huf_decode is None by one of the checks op_i > opStart_{i+1} *)
Ltac x4_none HR Hlens :=
  change (negb true) with false; rewrite HR;
  let A := fresh in let B := fresh in let C := fresh in let D := fresh in
  destruct Hlens as (A & B & C & D); rewrite x4_after_ovf by lia; reflexivity.

Lemma bit_rep_inv_t sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

Lemma x4_tail_ok {Espec: OracleKind} (gv: globals) (ht: huf_table) (sht: share) (dt: val) (L: Z) (res: val)
    (c2: list (val * (val * val))) (sho: share) (ob: val) (oc: list val) (d n: Z) (sh: share) (base: val)
    (N: Z) (c: list val) (off: Z) (s: list Z) (v1 v2 v3 v4 vd: val) :
  readable_share sht -> writable_share sho -> readable_share sh ->
  1 <= Zlength oc -> 0 <= d -> 6 <= n <= ZSTD_BLOCKSIZE_MAX -> d + n <= Zlength oc ->
  Zlength s <= ZSTD_BLOCKSIZE_MAX -> 0 <= off -> off + Zlength s <= N -> N <= 2 ^ 63 - 1 -> Zlength c = N ->
  bytes_ok s -> sublist off (off + Zlength s) c = zbytes s ->
  field_compatible (tarray tuchar N) [] base -> field_compatible (tarray tuchar (Zlength oc)) [] ob -> isptr dt ->
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> align_compatible tuint dt -> byte_val res ->
  Zlength c2 = 2 ^ L -> (forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2)) ->
  10 <= Zlength s -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  x4_tabx ht L c2 ->
  semax Delta4
    (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd
       (fun es k4 => es = 0 \/ n - 3 * ((n + 3) / 4) - 7 <= k4))
    x4_tail (x4_post gv sht dt ht sho ob oc d n sh base N c s).
Proof.
  intros SH SH0 Hsh H H0 H1 H2 H3 Hoff HoffN HN HlenC Hbs Hsub Hfcb Hfco Hdt H5 H6 H7 Hres Hc2len Hc2ok H4 Hfit HT.
  unfold x4_tail, Delta4, x4_post. cbv [seq_drop fn_body f_HUF_decompress4X2_usingDTable_internal_body].
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  unfold x4_state. Intros es p1 lo1 k1 p2 lo2 k2.
  Intros p3 lo3 k3 p4 lo4 k4 oc'. Intros f o1 o2 o3 o4.
  match goal with H: x4_ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (Hmx & Hlens & Hmem) end.
  assert (Ho4: Zlength o4 = k4) by apply Hlens.
  match goal with H: x4_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (Hes & Hk1 & Hk2 & Hk3 & Hk4 & Hk1b & Hb1 & Hb2 & Hb3 & Hb4 & Hb64 & Hout & R1 & R2 & R3 & R4 & Hbcs) end.
  clear Hb64.
  match goal with H: x4_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hval end.
  match goal with H: es = 0 \/ _ |- _ => rename H into Hexit end.
  assert (Hlen': Zlength oc' = Zlength oc) by (destruct Hout; auto).
  assert (Hsegb: 3 * ((n + 3) / 4) <= n /\ n <= 4 * ((n + 3) / 4) /\ 2 <= (n + 3) / 4).
  { pose proof (Z.div_mod (n + 3) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 3) 4 ltac:(lia)).
    unfold ZSTD_BLOCKSIZE_MAX in *. lia. }
  assert (Hl1: 0 <= le_field s 0 2 < 65536) by (apply le_field2_range; auto).
  assert (Hl2: 0 <= le_field s 2 2 < 65536) by (apply le_field2_range; auto).
  assert (Hl3: 0 <= le_field s 4 2 < 65536) by (apply le_field2_range; auto).
  assert (Hpo: isptr ob) by (destruct Hfco; auto).
  pose proof (x4_mx_exit ht s n es f p1 lo1 p2 lo2 p3 lo3 p4 lo4 o1 o2 o3 o4 Hmx Hes
                ltac:(rewrite Ho4; exact Hexit)) as HR.
  clear Hmx Ho4.
  assert_PROP (bit_inv (x4s1 s) p1 lo1 /\ bit_inv (x4s2 s) p2 lo2 /\ bit_inv (x4s3 s) p3 lo3 /\
               bit_inv (x4s4 s) p4 lo4) as Hinv0.
  { unfold x4s1, x4s2, x4s3, x4s4.
    sep_apply (bit_rep_inv_t Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)
                 (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4).
    entailer!. }
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob (d + k1) (d + (n + 3) / 4) TT)];
      [cancel | auto with share | lia | lia | lia]. }
  { match goal with H: typed_true _ _ |- _ =>
      apply (cmp_gt_tt (Zlength oc) (d + k1) (d + (n + 3) / 4) ob) in H; [|auto|lia|lia] end.
    forward. Exists (Int64.max_unsigned - 19) oc'. entailer!.
    - rewrite err_20. split; [intros C; inv C|]. split; [|split; [x4_none HR Hlens | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto. exfalso.
      destruct (Hval _ E) as (q1 & q2 & q3 & q4 & _ & V1 & V2 & V3 & V4).
      destruct V1 as (_ & (? & _) & _). lia.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  match goal with H: typed_false _ _ |- _ =>
    apply (cmp_gt_tf (Zlength oc) (d + k1) (d + (n + 3) / 4) ob) in H; [rename H into Hc1|auto|lia|lia] end.
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob (d + (n + 3) / 4 + k2) (d + (n + 3) / 4 + (n + 3) / 4) TT)];
      [cancel | auto with share | lia | lia | lia]. }
  { match goal with H: typed_true _ _ |- _ =>
      apply (cmp_gt_tt (Zlength oc) (d + (n + 3) / 4 + k2) (d + (n + 3) / 4 + (n + 3) / 4) ob) in H; [|auto|lia|lia] end.
    forward. Exists (Int64.max_unsigned - 19) oc'. entailer!.
    - rewrite err_20. split; [intros C; inv C|]. split; [|split; [x4_none HR Hlens | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto. exfalso.
      destruct (Hval _ E) as (q1 & q2 & q3 & q4 & _ & V1 & V2 & V3 & V4).
      destruct V2 as (_ & (? & _) & _). lia.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  match goal with H: typed_false _ _ |- _ =>
    apply (cmp_gt_tf (Zlength oc) (d + (n + 3) / 4 + k2) (d + (n + 3) / 4 + (n + 3) / 4) ob) in H; [rename H into Hc2|auto|lia|lia] end.
  forward_if.
  { eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob (d + (n + 3) / 4 + (n + 3) / 4 + k3) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) TT)];
      [cancel | auto with share | lia | lia | lia]. }
  { match goal with H: typed_true _ _ |- _ =>
      apply (cmp_gt_tt (Zlength oc) (d + (n + 3) / 4 + (n + 3) / 4 + k3) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) ob) in H; [|auto|lia|lia] end.
    forward. Exists (Int64.max_unsigned - 19) oc'. entailer!.
    - rewrite err_20. split; [intros C; inv C|]. split; [|split; [x4_none HR Hlens | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto. exfalso.
      destruct (Hval _ E) as (q1 & q2 & q3 & q4 & _ & V1 & V2 & V3 & V4).
      destruct V3 as (_ & (? & _) & _). lia.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  match goal with H: typed_false _ _ |- _ =>
    apply (cmp_gt_tf (Zlength oc) (d + (n + 3) / 4 + (n + 3) / 4 + k3) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) ob) in H; [rename H into Hc3|auto|lia|lia] end.
  assert (Htab: x2_tab_ok ht L c2) by (split; [auto | split; [auto | split; auto]]).
  replace (Zlength oc) with (Zlength oc') by zl.
  replace (offset_val (d + (n + 3) / 4) ob) with (offset_val (d + k1 + ((n + 3) / 4 - k1)) ob) by (f_equal; lia).
  forward_call (Tsh, v1, gv, sublist 6 (6 + le_field s 0 2) s, offset_val 6 (offset_val off base), p1, lo1,
                sh, offset_val off base, s, 6, sht, offset_val 4 dt, ht, L, c2, sho, ob, oc', d + k1, (n + 3) / 4 - k1).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [apply (proj1 HT) | apply (proj2 HT) | rewrite <- offset_offset_val; apply bit_src_ok_win; lia | zl | unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia]. }
  Intros vret. destruct vret as [[e1 f1] m1]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength m1 = _ |- _ => rename H into Hm1L end.
  match goal with H: forall dx, xb_rel _ _ _ dx -> _ |- _ => rename H into Y1 end.
  replace (sublist 0 (d + k1) oc' ++ zbytes m1 ++ sublist (d + k1 + ((n + 3) / 4 - k1)) (Zlength oc') oc')
    with (wrk oc' (d + k1) m1) by (unfold wrk; rewrite Hm1L; reflexivity).
  match goal with |- context [wrk ?o ?a m1] => assert (HL1: Zlength (wrk o a m1) = Zlength oc') by (rewrite wrk_len by zl; zl) end.
  replace (Zlength oc') with (Zlength (wrk oc' (d + k1) m1)) by zl.
  replace (offset_val (d + (n + 3) / 4 + (n + 3) / 4) ob) with (offset_val (d + (n + 3) / 4 + k2 + ((n + 3) / 4 - k2)) ob) by (f_equal; lia).
  forward_call (Tsh, v2, gv, sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s, offset_val (6 + le_field s 0 2) (offset_val off base), p2, lo2,
                sh, offset_val off base, s, (6 + le_field s 0 2), sht, offset_val 4 dt, ht, L, c2, sho, ob, (wrk oc' (d + k1) m1), d + (n + 3) / 4 + k2, (n + 3) / 4 - k2).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [apply (proj1 HT) | apply (proj2 HT) | rewrite <- offset_offset_val; apply bit_src_ok_win; lia | zl | unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia]. }
  Intros vret. destruct vret as [[e2 f2] m2]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength m2 = _ |- _ => rename H into Hm2L end.
  match goal with H: forall dx, xb_rel _ _ _ dx -> _ |- _ => rename H into Y2 end.
  replace (sublist 0 (d + (n + 3) / 4 + k2) (wrk oc' (d + k1) m1) ++ zbytes m2 ++ sublist (d + (n + 3) / 4 + k2 + ((n + 3) / 4 - k2)) (Zlength (wrk oc' (d + k1) m1)) (wrk oc' (d + k1) m1))
    with (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) by (unfold wrk; rewrite Hm2L; reflexivity).
  match goal with |- context [wrk ?o ?a m2] => assert (HL2: Zlength (wrk o a m2) = Zlength oc') by (rewrite wrk_len by zl; zl) end.
  replace (Zlength (wrk oc' (d + k1) m1)) with (Zlength (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2)) by zl.
  replace (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) ob) with (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + k3 + ((n + 3) / 4 - k3)) ob) by (f_equal; lia).
  forward_call (Tsh, v3, gv, sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s, offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base), p3, lo3,
                sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2), sht, offset_val 4 dt, ht, L, c2, sho, ob, (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2), d + (n + 3) / 4 + (n + 3) / 4 + k3, (n + 3) / 4 - k3).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [apply (proj1 HT) | apply (proj2 HT) | rewrite <- offset_offset_val; apply bit_src_ok_win; lia | zl | unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia]. }
  Intros vret. destruct vret as [[e3 f3] m3]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength m3 = _ |- _ => rename H into Hm3L end.
  match goal with H: forall dx, xb_rel _ _ _ dx -> _ |- _ => rename H into Y3 end.
  replace (sublist 0 (d + (n + 3) / 4 + (n + 3) / 4 + k3) (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) ++ zbytes m3 ++ sublist (d + (n + 3) / 4 + (n + 3) / 4 + k3 + ((n + 3) / 4 - k3)) (Zlength (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2)) (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2))
    with (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3) by (unfold wrk; rewrite Hm3L; reflexivity).
  match goal with |- context [wrk ?o ?a m3] => assert (HL3: Zlength (wrk o a m3) = Zlength oc') by (rewrite wrk_len by zl; zl) end.
  replace (Zlength (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2)) with (Zlength (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3)) by zl.
  replace (offset_val (d + n) ob) with (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 + (n - 3 * ((n + 3) / 4) - k4)) ob) by (f_equal; lia).
  forward_call (Tsh, v4, gv, sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s, offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base), p4, lo4,
                sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2), sht, offset_val 4 dt, ht, L, c2, sho, ob, (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3), d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4, n - 3 * ((n + 3) / 4) - k4).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [apply (proj1 HT) | apply (proj2 HT) | rewrite <- offset_offset_val; apply bit_src_ok_win; lia | zl | unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia]. }
  Intros vret. destruct vret as [[e4 f4] m4]. simpl fst in *; simpl snd in *.
  match goal with H: Zlength m4 = _ |- _ => rename H into Hm4L end.
  match goal with H: forall dx, xb_rel _ _ _ dx -> _ |- _ => rename H into Y4 end.
  replace (sublist 0 (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3) ++ zbytes m4 ++ sublist (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 + (n - 3 * ((n + 3) / 4) - k4)) (Zlength (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3)) (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3))
    with (wrk (wrk (wrk (wrk oc' (d + k1) m1) (d + (n + 3) / 4 + k2) m2) (d + (n + 3) / 4 + (n + 3) / 4 + k3) m3) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) m4) by (unfold wrk; rewrite Hm4L; reflexivity).
  match goal with |- context [wrk ?o ?a m4] => assert (HL4: Zlength (wrk o a m4) = Zlength oc') by (rewrite wrk_len by zl; zl) end.
  match goal with |- context [data_at sho (tarray tuchar ?z) (wrk (wrk (wrk (wrk _ _ _) _ _) _ _) _ _) ob] =>
    replace z with (Zlength oc) by zl end.
  assert_PROP (bit_inv (x4s1 s) e1 f1 /\ bit_inv (x4s2 s) e2 f2 /\ bit_inv (x4s3 s) e3 f3 /\
               bit_inv (x4s4 s) e4 f4) as Hinv1.
  { unfold x4s1, x4s2, x4s3, x4s4.
    sep_apply (bit_rep_inv_t Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) e1 f1 v1).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)
                 (offset_val (6 + le_field s 0 2) (offset_val off base)) e2 f2 v2).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) e3 f3 v3).
    sep_apply (bit_rep_inv_t Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) e4 f4 v4).
    entailer!. }
  destruct Hinv0 as (I1 & I2 & I3 & I4). destruct Hinv1 as (J1 & J2 & J3 & J4).
  pose proof (x4_tail_model ht s n d oc' p1 lo1 p2 lo2 p3 lo3 p4 lo4 e1 f1 e2 f2 e3 f3 e4 f4 k1 k2 k3 k4
                o1 o2 o3 o4 m1 m2 m3 m4 HR Hlens Hmem ltac:(lia) ltac:(lia) ltac:(lia) I1 I2 I3 J1 J2 J3 J4
                (Y1 _ (xb_rel_of _ _ _)) (Y2 _ (xb_rel_of _ _ _)) (Y3 _ (xb_rel_of _ _ _)) (Y4 _ (xb_rel_of _ _ _)))
    as HTM.
  cbv zeta in HTM. destruct HTM as [HM HG]. clear Y1 Y2 Y3 Y4 HR.
  repeat apply -> seq_assoc.
  forward_call (Tsh, v1, gv, sublist 6 (6 + le_field s 0 2) s, offset_val 6 (offset_val off base), e1, f1, sh, offset_val off base, s, 6).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v2, gv, sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s, offset_val (6 + le_field s 0 2) (offset_val off base), e2, f2, sh, offset_val off base, s, (6 + le_field s 0 2)).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v3, gv, sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s, offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base), e3, f3, sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2)).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v4, gv, sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s, offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base), e4, f4, sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)).
  1: { repeat match goal with |- _ /\ _ => split end;
         first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward.
  rewrite !and01.
  match goal with |- context [if andb (andb (andb ?a ?b) ?c) ?e then 1 else 0] =>
    destruct (andb (andb (andb a b) c) e) eqn:EB end.
  - forward_if.
    { match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; apply Int.one_not_zero; exact H end. }
    forward.
    Exists n (fo4 oc' d n k1 k2 k3 k4 m1 m2 m3 m4). entailer!.
    + pose proof (fin_len oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FL; fa13 FL; destruct FL as (_ & _ & _ & FL4).
      pose proof (fin_out oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FO; fa13 FO.
      pose proof (fin_bytes oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FB; fa13 FB.
      split; [unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia|]. split; [auto|].
      split; [intros Hx; apply fin_bc; auto|]. split; [|split].
      * intros _. split; [auto|]. apply region_bytes_zbytes; [lia | lia | lia | apply FB; auto].
      * destruct (huf_lits_with true ht s n) eqn:E; [|auto].
        destruct (Hval _ E) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
        destruct V1 as (Q1 & (C1 & O1 & D1) & G1 & _). destruct V2 as (Q2 & (C2 & O2 & D2) & G2 & _).
        destruct V3 as (Q3 & (C3 & O3 & D3) & G3 & _). destruct V4 as (Q4 & (C4 & O4 & D4) & G4 & _).
        match goal with H: lo1 <= p1 -> _ |- _ => destruct (H ltac:(lia) _ D1) as (E1 & Ee1 & Ef1) end.
        match goal with H: lo2 <= p2 -> _ |- _ => destruct (H ltac:(lia) _ D2) as (E2 & Ee2 & Ef2) end.
        match goal with H: lo3 <= p3 -> _ |- _ => destruct (H ltac:(lia) _ D3) as (E3 & Ee3 & Ef3) end.
        match goal with H: lo4 <= p4 -> _ |- _ => destruct (H ltac:(lia) _ D4) as (E4 & Ee4 & Ef4) end.
        split; [auto|].
        pose proof (fin_valid oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FV; fa13 FV.
        replace (d + n) with (d + Zlength (q1 ++ q2 ++ q3 ++ q4)) by (rewrite !Zlength_app; lia).
        apply region_is_sublist; [lia | rewrite !Zlength_app; lia |].
        apply FV; auto; [rewrite Q1 | rewrite Q2 | rewrite Q3 | rewrite Q4]; auto.
      * change (negb true) with false. first [rewrite HM, EB | rewrite HM]. split; [reflexivity|].
        destruct (HG ltac:(first [exact EB | reflexivity])) as (G1 & G2 & G3 & G4).
        destruct Hlens as (Ho1 & Ho2 & Ho3 & Ho4).
        pose proof (fin_valid oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FV; fa13 FV.
        replace (o1 ++ m1 ++ o2 ++ m2 ++ o3 ++ m3 ++ o4 ++ m4)
          with ((o1 ++ m1) ++ (o2 ++ m2) ++ (o3 ++ m3) ++ (o4 ++ m4)) by (rewrite <- !app_assoc; reflexivity).
        replace (d + n) with (d + Zlength ((o1 ++ m1) ++ (o2 ++ m2) ++ (o3 ++ m3) ++ (o4 ++ m4)))
          by (rewrite !Zlength_app; lia).
        apply region_is_sublist; [lia | rewrite !Zlength_app; lia |].
        apply FV; try (rewrite Zlength_app; lia);
          first [ rewrite <- Ho1; rewrite sublist_app1, sublist_same by lia; auto
                | rewrite <- Ho2; rewrite sublist_app1, sublist_same by lia; auto
                | rewrite <- Ho3; rewrite sublist_app1, sublist_same by lia; auto
                | rewrite <- Ho4; rewrite sublist_app1, sublist_same by lia; auto
                | rewrite <- Ho1; rewrite sublist_app2 by lia; rewrite Z.sub_diag, Zlength_app;
                  replace (Zlength o1 + Zlength m1 - Zlength o1) with (Zlength m1) by lia; rewrite sublist_same by lia; auto
                | rewrite <- Ho2; rewrite sublist_app2 by lia; rewrite Z.sub_diag, Zlength_app;
                  replace (Zlength o2 + Zlength m2 - Zlength o2) with (Zlength m2) by lia; rewrite sublist_same by lia; auto
                | rewrite <- Ho3; rewrite sublist_app2 by lia; rewrite Z.sub_diag, Zlength_app;
                  replace (Zlength o3 + Zlength m3 - Zlength o3) with (Zlength m3) by lia; rewrite sublist_same by lia; auto
                | rewrite <- Ho4; rewrite sublist_app2 by lia; rewrite Z.sub_diag, Zlength_app;
                  replace (Zlength o4 + Zlength m4 - Zlength o4) with (Zlength m4) by lia; rewrite sublist_same by lia; auto ].
    + unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel.
  - forward_if.
    { forward. Exists (Int64.max_unsigned - 19) (fo4 oc' d n k1 k2 k3 k4 m1 m2 m3 m4). entailer!.
      + pose proof (fin_len oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FL; fa13 FL; destruct FL as (_ & _ & _ & FL4).
      pose proof (fin_out oc oc' d n k1 k2 k3 k4 m1 m2 m3 m4) as FO; fa13 FO.
        rewrite err_20. split; [auto|]. split; [intros Hx; apply fin_bc; auto|]. split; [intros C; inv C|].
        split; [|split; [change (negb true) with false; first [rewrite HM, EB | rewrite HM]; reflexivity | apply vlong_err_20]].
        destruct (huf_lits_with true ht s n) eqn:E; [exfalso|auto].
        destruct (Hval _ E) as (q1 & q2 & q3 & q4 & -> & V1 & V2 & V3 & V4).
        destruct V1 as (Q1 & (C1 & O1 & D1) & G1 & _). destruct V2 as (Q2 & (C2 & O2 & D2) & G2 & _).
        destruct V3 as (Q3 & (C3 & O3 & D3) & G3 & _). destruct V4 as (Q4 & (C4 & O4 & D4) & G4 & _).
        match goal with H: lo1 <= p1 -> _ |- _ => destruct (H ltac:(lia) _ D1) as (E1 & Ee1 & Ef1) end.
        match goal with H: lo2 <= p2 -> _ |- _ => destruct (H ltac:(lia) _ D2) as (E2 & Ee2 & Ef2) end.
        match goal with H: lo3 <= p3 -> _ |- _ => destruct (H ltac:(lia) _ D3) as (E3 & Ee3 & Ef3) end.
        match goal with H: lo4 <= p4 -> _ |- _ => destruct (H ltac:(lia) _ D4) as (E4 & Ee4 & Ef4) end.
        subst e1 f1 e2 f2 e3 f3 e4 f4. simpl in EB. discriminate EB.
      + unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
    match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end.
Qed.

(* ---------- the main loop's body ---------- *)

(* the facts of any input during an iteration: k4h = stream 4's position at its start, j_i decodes done *)
Definition x4_bfacts (oc oc': list val) (d n k4h: Z) (j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) : Prop :=
  k4h + 8 <= n - 3 * ((n + 3) / 4) /\ 0 <= k4h /\
  0 <= j1 <= 4 /\ 0 <= j2 <= 4 /\ 0 <= j3 <= 4 /\ 0 <= j4 <= 4 /\
  j1 <= k1 <= 2 * k4h + 2 * j1 /\ j2 <= k2 <= 2 * k4h + 2 * j2 /\ j3 <= k3 <= 2 * k4h + 2 * j3 /\
  k4h + j4 <= k4 <= k4h + 2 * j4 /\
  (lo1 + 64 - p1 <= 64 + 12 * j1 /\ (lo1 < 64 \/ lo1 + 64 - p1 <= 8 + 12 * j1)) /\
  (lo2 + 64 - p2 <= 64 + 12 * j2 /\ (lo2 < 64 \/ lo2 + 64 - p2 <= 8 + 12 * j2)) /\
  (lo3 + 64 - p3 <= 64 + 12 * j3 /\ (lo3 < 64 \/ lo3 + 64 - p3 <= 8 + 12 * j3)) /\
  (lo4 + 64 - p4 <= 64 + 12 * j4 /\ (lo4 < 64 \/ lo4 + 64 - p4 <= 8 + 12 * j4)) /\
  out_after oc oc' d n /\ region_bytes oc' (d) k1 /\ region_bytes oc' (d + (n + 3) / 4) k2 /\
  region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4) k3 /\ region_bytes oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) k4 /\
  (byte_cells oc -> byte_cells oc').
Lemma bf_step1 (oc oc': list val) (d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb b1 b2: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  x4_bfacts oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 -> j1 <= 3 -> 1 <= kk <= 2 -> 1 <= nb <= 12 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  x4_bfacts oc (wr2 oc' (d + k1) b1 b2) d n k4h (j1 + 1) (p1 - nb) lo1 (k1 + kk) j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 /\ 0 <= d + k1 /\
  d + k1 + 2 <= Zlength oc' /\ Zlength (wr2 oc' (d + k1) b1 b2) = Zlength oc.
Proof.
  intros Hd Hdn Hs3 Hs4 Hs2 (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & R1 & R2 & R3 & R4 & Hbc) Hj Hkk Hnb Hb1' Hb2'.
  assert (Hl: Zlength oc' = Zlength oc) by (destruct Hout; auto).
  assert (Ha: 0 <= d + k1 /\ d + k1 + 2 <= Zlength oc') by lia.
  split; [|split; [lia | split; [lia | rewrite wr2_len; lia]]].
  unfold x4_bfacts. repeat match goal with |- _ /\ _ => split end; try lia.
  - apply out_after_wr2; auto; lia.
  - apply region_bytes_wr2_ext; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - intros Hx. apply byte_cells_wr2; auto.
Qed.

Lemma bf_step2 (oc oc': list val) (d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb b1 b2: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  x4_bfacts oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 -> j2 <= 3 -> 1 <= kk <= 2 -> 1 <= nb <= 12 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  x4_bfacts oc (wr2 oc' (d + (n + 3) / 4 + k2) b1 b2) d n k4h j1 p1 lo1 k1 (j2 + 1) (p2 - nb) lo2 (k2 + kk) j3 p3 lo3 k3 j4 p4 lo4 k4 /\ 0 <= d + (n + 3) / 4 + k2 /\
  d + (n + 3) / 4 + k2 + 2 <= Zlength oc' /\ Zlength (wr2 oc' (d + (n + 3) / 4 + k2) b1 b2) = Zlength oc.
Proof.
  intros Hd Hdn Hs3 Hs4 Hs2 (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & R1 & R2 & R3 & R4 & Hbc) Hj Hkk Hnb Hb1' Hb2'.
  assert (Hl: Zlength oc' = Zlength oc) by (destruct Hout; auto).
  assert (Ha: 0 <= d + (n + 3) / 4 + k2 /\ d + (n + 3) / 4 + k2 + 2 <= Zlength oc') by lia.
  split; [|split; [lia | split; [lia | rewrite wr2_len; lia]]].
  unfold x4_bfacts. repeat match goal with |- _ /\ _ => split end; try lia.
  - apply out_after_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2_ext; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - intros Hx. apply byte_cells_wr2; auto.
Qed.

Lemma bf_step3 (oc oc': list val) (d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb b1 b2: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  x4_bfacts oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 -> j3 <= 3 -> 1 <= kk <= 2 -> 1 <= nb <= 12 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  x4_bfacts oc (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + k3) b1 b2) d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) (p3 - nb) lo3 (k3 + kk) j4 p4 lo4 k4 /\ 0 <= d + (n + 3) / 4 + (n + 3) / 4 + k3 /\
  d + (n + 3) / 4 + (n + 3) / 4 + k3 + 2 <= Zlength oc' /\ Zlength (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + k3) b1 b2) = Zlength oc.
Proof.
  intros Hd Hdn Hs3 Hs4 Hs2 (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & R1 & R2 & R3 & R4 & Hbc) Hj Hkk Hnb Hb1' Hb2'.
  assert (Hl: Zlength oc' = Zlength oc) by (destruct Hout; auto).
  assert (Ha: 0 <= d + (n + 3) / 4 + (n + 3) / 4 + k3 /\ d + (n + 3) / 4 + (n + 3) / 4 + k3 + 2 <= Zlength oc') by lia.
  split; [|split; [lia | split; [lia | rewrite wr2_len; lia]]].
  unfold x4_bfacts. repeat match goal with |- _ /\ _ => split end; try lia.
  - apply out_after_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2_ext; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - intros Hx. apply byte_cells_wr2; auto.
Qed.

Lemma bf_step4 (oc oc': list val) (d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb b1 b2: Z) :
  0 <= d -> d + n <= Zlength oc -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) -> 2 <= (n + 3) / 4 ->
  x4_bfacts oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 -> j4 <= 3 -> 1 <= kk <= 2 -> 1 <= nb <= 12 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  x4_bfacts oc (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) b1 b2) d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) (p4 - nb) lo4 (k4 + kk) /\ 0 <= d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 /\
  d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 + 2 <= Zlength oc' /\ Zlength (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) b1 b2) = Zlength oc.
Proof.
  intros Hd Hdn Hs3 Hs4 Hs2 (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & R1 & R2 & R3 & R4 & Hbc) Hj Hkk Hnb Hb1' Hb2'.
  assert (Hl: Zlength oc' = Zlength oc) by (destruct Hout; auto).
  assert (Ha: 0 <= d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 /\ d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 + 2 <= Zlength oc') by lia.
  split; [|split; [lia | split; [lia | rewrite wr2_len; lia]]].
  unfold x4_bfacts. repeat match goal with |- _ /\ _ => split end; try lia.
  - apply out_after_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2; auto; lia.
  - apply region_bytes_wr2_ext; auto; lia.
  - intros Hx. apply byte_cells_wr2; auto.
Qed.

Lemma x2_step_bnd (ht: huf_table) (L v k b2 nb: Z) :
  x2_step ht L v k b2 nb -> 1 <= k <= 2 /\ 1 <= nb <= L /\ 0 <= b2 < 256.
Proof.
  intros (Hb2 & Hnb & Hcase). destruct (hsym ht L v) as [s1 n1].
  destruct Hcase as [[-> _]|Hc2]; [lia|].
  destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2]. destruct Hc2 as [-> _]. lia.
Qed.

Definition tX2c : type :=
  Tfunction ((tptr tvoid) :: (tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
             (tptr (Tstruct ___gp_HUF_DEltX2 noattr)) :: tuint :: nil) tuint cc_default.

(* op += HUF_decodeSymbolX2(op, &bitD, dt, dtLog) *)
Definition dcall4 (op bd t: ident) : statement :=
  Ssequence
    (Scall (Some t) (Evar _HUF_decodeSymbolX2 tX2c)
       ((Etempvar op (tptr tuchar)) ::
        (Eaddrof (Evar bd (Tstruct ___gp_BIT_DStream_t noattr)) (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
        (Etempvar _dt (tptr (Tstruct ___gp_HUF_DEltX2 noattr))) :: (Etempvar _dtLog tuint) :: nil))
    (Sset op (Ebinop Oadd (Etempvar op (tptr tuchar)) (Etempvar t tuint) (tptr tuchar))).

Definition mcall4 (t: ident) : statement := Scall (Some t) (Evar _MEM_64bits (Tfunction nil tuint cc_default)) nil.

(* do { c } while (0), normal exit *)
Lemma semax_dw0n {cs: compspecs} {Esp: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c: statement) :
  semax Delta P c (normal_ret_assert Q) -> semax Delta P (Sloop c Sbreak) (normal_ret_assert Q).
Proof.
  intros H. apply semax_loop with (Q' := Q).
  - eapply semax_post; [.. | exact H]; simpl; intros;
      first [apply andp_left2; apply derives_refl | apply andp_left2; apply prop_left; intros []].
  - eapply semax_pre; [| apply semax_break]. simpl. intros x. apply andp_left2. apply derives_refl.
Qed.

Lemma semax_normal_post {cs: compspecs} {Esp: OracleKind} (Delta: tycontext) (P Q: environ -> mpred)
    (c: statement) (R: ret_assert) :
  semax Delta P c (normal_ret_assert Q) -> ENTAIL Delta, Q |-- RA_normal R -> semax Delta P c R.
Proof.
  intros H HQ. eapply semax_post; [.. | exact H]; simpl; intros;
    first [exact (HQ x) | apply andp_left2; apply prop_left; intros []].
Qed.

Lemma bit_rep_inv4 sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

Lemma reload_fast_facts (pos lo: Z) : 0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 -> lo <= pos \/ lo < 64 ->
  snd (bs_reload_fast pos lo) <= lo /\ 0 <= snd (bs_reload_fast pos lo) /\
  ((fst (bs_reload_fast pos lo) = BIT_unfinished /\ snd (bs_reload_fast pos lo) + 64 - pos <= 7) \/
   (fst (bs_reload_fast pos lo) = BIT_overflow /\ snd (bs_reload_fast pos lo) = lo)).
Proof.
  intros H0 H8 H64 Hle. unfold bs_reload_fast.
  pose proof (Z.div_mod lo 8 ltac:(lia)).
  destruct (lo / 8 <? 8) eqn:E; cbn [fst snd].
  - split; [lia|]. split; [lia|]. right. auto.
  - apply Z.ltb_ge in E. assert (Hle': lo <= pos) by lia.
    pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)).
    assert (0 <= (lo + 64 - pos) / 8) by (apply Z.div_pos; lia).
    split; [lia|]. split; [lia|]. left. split; [reflexivity | lia].
Qed.

Lemma rep_g_true : BIT_DStream_rep_g true = BIT_DStream_rep_np.
Proof. reflexivity. Qed.

Lemma bit_rep_np_inv4 sh gv s start pos lo p :
  BIT_DStream_rep_np sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep_np. Intros lim. entailer!. Qed.

Definition x4_if : statement :=
  match seq_drop 33 (fn_body f_HUF_decompress4X2_usingDTable_internal_body) with Ssequence s _ => s | _ => Sskip end.
Definition x4_while : statement := match x4_if with Sifthenelse _ w _ => w | _ => Sskip end.
Definition x4_wbody : statement := match x4_while with Sloop (Ssequence _ b) _ => b | _ => Sskip end.
Definition x4_reloads : statement := seq_drop 16 x4_wbody.

(* ---------- the exact model during an iteration ---------- *)

(* stream w's decodes of this iteration so far: j decodes from the iteration's start (P, lo) *)
Definition x4_r (ht: huf_table) (w: list Z) (P lo j: Z) : list Z * xbit :=
  xh_x2_n (xhuf_of true ht) (xb_of w P lo) (Z.to_nat j).

(* the exact facts during an iteration (start: positions P_i, outputs O_i, fuel S f, stream 4 at k4h): the
   model's rest of the loop from the iteration's start; each stream's state after its j_i decodes is the C's;
   its bytes are O_i and those decodes'; bits consumed bounded after the first iteration; the output array *)
Definition x4_bx (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) : Prop :=
  x_huf_decode (xhuf_of true ht) false s n =
    x4_after ht s n (x4_loop ht s n (S f) (xb_of (x4s1 s) P1 lo1) (xb_of (x4s2 s) P2 lo2) (xb_of (x4s3 s) P3 lo3)
                       (xb_of (x4s4 s) P4 lo4) O1 O2 O3 O4) /\
  Zlength O4 = k4h /\ Z.max 0 (n - 7 - 3 * ((n + 3) / 4) - k4h) < Z.of_nat (S f) /\
  snd (x4_r ht (x4s1 s) P1 lo1 j1) = xb_of (x4s1 s) p1 lo1 /\ snd (x4_r ht (x4s2 s) P2 lo2 j2) = xb_of (x4s2 s) p2 lo2 /\
  snd (x4_r ht (x4s3 s) P3 lo3 j3) = xb_of (x4s3 s) p3 lo3 /\ snd (x4_r ht (x4s4 s) P4 lo4 j4) = xb_of (x4s4 s) p4 lo4 /\
  Zlength (O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 j1)) = k1 /\ Zlength (O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 j2)) = k2 /\
  Zlength (O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 j3)) = k3 /\ Zlength (O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 j4)) = k4 /\
  (0 < k4h -> lo1 + 64 - p1 <= 7 + 12 * j1 /\ lo2 + 64 - p2 <= 7 + 12 * j2 /\ lo3 + 64 - p3 <= 7 + 12 * j3 /\
              lo4 + 64 - p4 <= 7 + 12 * j4) /\
  x4_mem oc d n p1 lo1 p2 lo2 p3 lo3 (O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 j1)) (O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 j2))
    (O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 j3)) (O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 j4)).

(* one decode of stream w: its state and bytes after j + 1 decodes *)
Lemma x4_r_step (ht: huf_table) (L: Z) (w: list Z) (P p lo j v kk b2 nb: Z) (O: list Z) :
  0 <= j -> snd (x4_r ht w P lo j) = xb_of w p lo -> L = xh_x2_log ht -> huf_ok ht -> ht_log ht <= L ->
  0 <= v < 2 ^ L -> v = xb_look_fast (xb_of w p lo) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  x2_step ht L v kk b2 nb -> 0 <= lo + 64 - (p - nb) < 2 ^ 32 ->
  snd (x4_r ht w P lo (j + 1)) = xb_of w (p - nb) lo /\
  O ++ fst (x4_r ht w P lo (j + 1)) = (O ++ fst (x4_r ht w P lo j)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2] /\
  Zlength (firstn (Z.to_nat kk) [fst (hsym ht L v); b2]) = kk /\ 1 <= kk <= 2 /\ 1 <= nb <= L /\
  0 <= fst (hsym ht L v) < 256 /\ 0 <= b2 < 256.
Proof.
  intros Hj Hr HL Hok Hlog Hv Hvx Hc Hst Hrange.
  destruct (x2_step_bnd _ _ _ _ _ _ Hst) as (Hkk & Hnb & Hb2).
  pose proof (hsym_range ht L v Hok Hlog Hv) as (Hs & _).
  unfold x4_r in *.
  rewrite (x4_n_step ht L w P p lo j v kk b2 nb Hj Hr HL Hv Hvx Hc Hs Hb2 Hkk ltac:(lia) Hrange).
  simpl fst; simpl snd. split; [reflexivity|]. split; [rewrite app_assoc; reflexivity|].
  split; [|auto].
  destruct (zeq kk 1) as [->|]; [reflexivity|]. replace kk with 2 by lia. reflexivity.
Qed.

Lemma bx_step1 (ht: huf_table) (L: Z) (s: list Z) (n d: Z) (oc0 oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb: Z) :
  x4_bfacts oc0 oc d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_bx ht s n d oc f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  j1 <= 3 -> 0 <= d -> d + n <= Zlength oc0 -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) ->
  bit_inv (x4s1 s) p1 lo1 -> L = xh_x2_log ht -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  0 <= v < 2 ^ L -> v = xb_look_fast (xb_of (x4s1 s) p1 lo1) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  x2_step ht L v kk b2 nb ->
  x4_bx ht s n d (wr2 oc (d + k1) (fst (hsym ht L v)) b2) f P1 P2 P3 P4 O1 O2 O3 O4 k4h (j1 + 1) (p1 - nb) lo1 (k1 + kk) j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4.
Proof.
  intros HB HX Hj Hd Hdn Hs3 Hs4 Hi HL Hok Hlog Hv Hvx Hc Hst.
  destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & _ & _ & _ & _ & _).
  destruct HX as (E & HO4 & Hf & R1 & R2 & R3 & R4 & K1 & K2 & K3 & K4 & Hbc & Hm).
  destruct Hi as (_ & _ & Hlo & _ & _ & Hp & Hmax).
  assert (Hlen: Zlength oc = Zlength oc0) by (destruct Hout; auto).
  unfold HUF_TABLELOG_MAX in Hlog.
  destruct (x4_r_step ht L (x4s1 s) P1 p1 lo1 j1 v kk b2 nb O1 ltac:(lia) R1 HL Hok ltac:(lia) Hv Hvx Hc Hst
              ltac:(destruct (x2_step_bnd _ _ _ _ _ _ Hst); rep_lia)) as (R1' & A1 & L1 & Hkk & Hnb & Hs1 & Hsb2).
  assert (Z1: Zlength ((O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 j1)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2]) = k1 + kk)
    by (rewrite Zlength_app, L1; lia).
  unfold x4_bx. rewrite R1', A1.
  split; [exact E|]. split; [exact HO4|]. split; [exact Hf|].
  repeat (split; [first [reflexivity | assumption | lia | intros Hk; specialize (Hbc Hk); lia] |]).
  replace (d + k1) with (d + Zlength (O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 j1))) by lia.
  apply x4_mem_step1; auto; try lia.
  all: try (destruct (Z_lt_le_dec 0 k4h) as [Hk|Hk]; [specialize (Hbc Hk); right; lia | left; lia]).
Qed.

Lemma bx_step2 (ht: huf_table) (L: Z) (s: list Z) (n d: Z) (oc0 oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb: Z) :
  x4_bfacts oc0 oc d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_bx ht s n d oc f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  j2 <= 3 -> 0 <= d -> d + n <= Zlength oc0 -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) ->
  bit_inv (x4s2 s) p2 lo2 -> L = xh_x2_log ht -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  0 <= v < 2 ^ L -> v = xb_look_fast (xb_of (x4s2 s) p2 lo2) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  x2_step ht L v kk b2 nb ->
  x4_bx ht s n d (wr2 oc (d + (n + 3) / 4 + k2) (fst (hsym ht L v)) b2) f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 (j2 + 1) (p2 - nb) lo2 (k2 + kk) j3 p3 lo3 k3 j4 p4 lo4 k4.
Proof.
  intros HB HX Hj Hd Hdn Hs3 Hs4 Hi HL Hok Hlog Hv Hvx Hc Hst.
  destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & _ & _ & _ & _ & _).
  destruct HX as (E & HO4 & Hf & R1 & R2 & R3 & R4 & K1 & K2 & K3 & K4 & Hbc & Hm).
  destruct Hi as (_ & _ & Hlo & _ & _ & Hp & Hmax).
  assert (Hlen: Zlength oc = Zlength oc0) by (destruct Hout; auto).
  unfold HUF_TABLELOG_MAX in Hlog.
  destruct (x4_r_step ht L (x4s2 s) P2 p2 lo2 j2 v kk b2 nb O2 ltac:(lia) R2 HL Hok ltac:(lia) Hv Hvx Hc Hst
              ltac:(destruct (x2_step_bnd _ _ _ _ _ _ Hst); rep_lia)) as (R2' & A2 & L2 & Hkk & Hnb & Hs1 & Hsb2).
  assert (Z2: Zlength ((O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 j2)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2]) = k2 + kk)
    by (rewrite Zlength_app, L2; lia).
  unfold x4_bx. rewrite R2', A2.
  split; [exact E|]. split; [exact HO4|]. split; [exact Hf|].
  repeat (split; [first [reflexivity | assumption | lia | intros Hk; specialize (Hbc Hk); lia] |]).
  replace (d + (n + 3) / 4 + k2) with (d + (n + 3) / 4 + Zlength (O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 j2))) by lia.
  apply x4_mem_step2; auto; try lia.
  all: try (destruct (Z_lt_le_dec 0 k4h) as [Hk|Hk]; [specialize (Hbc Hk); right; lia | left; lia]).
Qed.

Lemma bx_step3 (ht: huf_table) (L: Z) (s: list Z) (n d: Z) (oc0 oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb: Z) :
  x4_bfacts oc0 oc d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_bx ht s n d oc f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  j3 <= 3 -> 0 <= d -> d + n <= Zlength oc0 -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) ->
  bit_inv (x4s3 s) p3 lo3 -> L = xh_x2_log ht -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  0 <= v < 2 ^ L -> v = xb_look_fast (xb_of (x4s3 s) p3 lo3) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  x2_step ht L v kk b2 nb ->
  x4_bx ht s n d (wr2 oc (d + (n + 3) / 4 + (n + 3) / 4 + k3) (fst (hsym ht L v)) b2) f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) (p3 - nb) lo3 (k3 + kk) j4 p4 lo4 k4.
Proof.
  intros HB HX Hj Hd Hdn Hs3 Hs4 Hi HL Hok Hlog Hv Hvx Hc Hst.
  destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & _ & _ & _ & _ & _).
  destruct HX as (E & HO4 & Hf & R1 & R2 & R3 & R4 & K1 & K2 & K3 & K4 & Hbc & Hm).
  destruct Hi as (_ & _ & Hlo & _ & _ & Hp & Hmax).
  assert (Hlen: Zlength oc = Zlength oc0) by (destruct Hout; auto).
  unfold HUF_TABLELOG_MAX in Hlog.
  destruct (x4_r_step ht L (x4s3 s) P3 p3 lo3 j3 v kk b2 nb O3 ltac:(lia) R3 HL Hok ltac:(lia) Hv Hvx Hc Hst
              ltac:(destruct (x2_step_bnd _ _ _ _ _ _ Hst); rep_lia)) as (R3' & A3 & L3 & Hkk & Hnb & Hs1 & Hsb2).
  assert (Z3: Zlength ((O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 j3)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2]) = k3 + kk)
    by (rewrite Zlength_app, L3; lia).
  unfold x4_bx. rewrite R3', A3.
  split; [exact E|]. split; [exact HO4|]. split; [exact Hf|].
  repeat (split; [first [reflexivity | assumption | lia | intros Hk; specialize (Hbc Hk); lia] |]).
  replace (d + (n + 3) / 4 + (n + 3) / 4 + k3) with (d + (n + 3) / 4 + (n + 3) / 4 + Zlength (O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 j3))) by lia.
  apply x4_mem_step3; auto; try lia.
  all: try (destruct (Z_lt_le_dec 0 k4h) as [Hk|Hk]; [specialize (Hbc Hk); right; lia | left; lia]).
Qed.

Lemma bx_step4 (ht: huf_table) (L: Z) (s: list Z) (n d: Z) (oc0 oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb: Z) :
  x4_bfacts oc0 oc d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  x4_bx ht s n d oc f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 ->
  j4 <= 3 -> 0 <= d -> d + n <= Zlength oc0 -> 3 * ((n + 3) / 4) <= n -> n <= 4 * ((n + 3) / 4) ->
  bit_inv (x4s4 s) p4 lo4 -> L = xh_x2_log ht -> huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  0 <= v < 2 ^ L -> v = xb_look_fast (xb_of (x4s4 s) p4 lo4) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  x2_step ht L v kk b2 nb ->
  x4_bx ht s n d (wr2 oc (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (fst (hsym ht L v)) b2) f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) (p4 - nb) lo4 (k4 + kk).
Proof.
  intros HB HX Hj Hd Hdn Hs3 Hs4 Hi HL Hok Hlog Hv Hvx Hc Hst.
  destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & _ & _ & _ & _ & _).
  destruct HX as (E & HO4 & Hf & R1 & R2 & R3 & R4 & K1 & K2 & K3 & K4 & Hbc & Hm).
  destruct Hi as (_ & _ & Hlo & _ & _ & Hp & Hmax).
  assert (Hlen: Zlength oc = Zlength oc0) by (destruct Hout; auto).
  unfold HUF_TABLELOG_MAX in Hlog.
  destruct (x4_r_step ht L (x4s4 s) P4 p4 lo4 j4 v kk b2 nb O4 ltac:(lia) R4 HL Hok ltac:(lia) Hv Hvx Hc Hst
              ltac:(destruct (x2_step_bnd _ _ _ _ _ _ Hst); rep_lia)) as (R4' & A4 & L4 & Hkk & Hnb & Hs1 & Hsb2).
  assert (Z4: Zlength ((O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 j4)) ++ firstn (Z.to_nat kk) [fst (hsym ht L v); b2]) = k4 + kk)
    by (rewrite Zlength_app, L4; lia).
  unfold x4_bx. rewrite R4', A4.
  split; [exact E|]. split; [exact HO4|]. split; [exact Hf|].
  repeat (split; [first [reflexivity | assumption | lia | intros Hk; specialize (Hbc Hk); lia] |]).
  replace (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) with (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + Zlength (O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 j4))) by lia.
  apply x4_mem_step4; auto; try lia.
  all: try (destruct (Z_lt_le_dec 0 k4h) as [Hk|Hk]; [specialize (Hbc Hk); right; lia | left; lia]).
Qed.

(* the end of an iteration: the four BIT_reloadDStreamFast; the loop head's exact facts with the new endSignal *)
Lemma bx_reload (ht: huf_table) (s: list Z) (n d: Z) (oc0 oc: list val) (f: nat) (P1 P2 P3 P4: Z)
    (O1 O2 O3 O4: list Z) (k4h p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) :
  x4_bfacts oc0 oc d n k4h 4 p1 lo1 k1 4 p2 lo2 k2 4 p3 lo3 k3 4 p4 lo4 k4 ->
  x4_bx ht s n d oc f P1 P2 P3 P4 O1 O2 O3 O4 k4h 4 p1 lo1 k1 4 p2 lo2 k2 4 p3 lo3 k3 4 p4 lo4 k4 ->
  bit_inv (x4s1 s) p1 lo1 -> bit_inv (x4s2 s) p2 lo2 -> bit_inv (x4s3 s) p3 lo3 -> bit_inv (x4s4 s) p4 lo4 ->
  lo1 <= p1 \/ lo1 < 64 -> lo2 <= p2 \/ lo2 < 64 -> lo3 <= p3 \/ lo3 < 64 -> lo4 <= p4 \/ lo4 < 64 ->
  x4_ex ht s n oc d
    (if x4_es (fst (bs_reload_fast p1 lo1)) (fst (bs_reload_fast p2 lo2)) (fst (bs_reload_fast p3 lo3))
          (fst (bs_reload_fast p4 lo4)) then 1 else 0) f
    p1 (snd (bs_reload_fast p1 lo1)) k1 p2 (snd (bs_reload_fast p2 lo2)) k2
    p3 (snd (bs_reload_fast p3 lo3)) k3 p4 (snd (bs_reload_fast p4 lo4)) k4
    (O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 4)) (O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 4))
    (O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 4)) (O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 4)).
Proof.
  intros HB HX I1 I2 I3 I4 Hle1 Hle2 Hle3 Hle4.
  destruct HB as (HM & Hk4h & _ & _ & _ & _ & _ & _ & _ & Hk4 & _).
  destruct HX as (E & HO4 & Hf & R1 & R2 & R3 & R4 & K1 & K2 & K3 & K4 & Hbc & Hm).
  assert (Fx: forall w p lo, bit_inv w p lo -> lo <= p \/ lo < 64 ->
            (fst (bs_reload_fast p lo) = 0 /\ snd (bs_reload_fast p lo) + 64 - p <= 7) \/
            (fst (bs_reload_fast p lo) = 3 /\ snd (bs_reload_fast p lo) = lo)).
  { intros w p lo (_ & _ & H0 & H8 & _ & H64 & _) Hle.
    destruct (reload_fast_facts p lo H0 H8 H64 Hle) as (_ & _ & [F|F]); [left|right]; exact F. }
  pose proof (Fx _ _ _ I1 Hle1) as F1. pose proof (Fx _ _ _ I2 Hle2) as F2.
  pose proof (Fx _ _ _ I3 Hle3) as F3. pose proof (Fx _ _ _ I4 Hle4) as F4.
  assert (Ex: forall w P p lo, snd (x4_r ht w P lo 4) = xb_of w p lo ->
            xh_x2_n (xhuf_of true ht) (xb_of w P lo) 4 = (fst (x4_r ht w P lo 4), xb_of w p lo)).
  { intros w P p lo H. unfold x4_r in H |- *. change (Z.to_nat 4) with 4%nat in H |- *. rewrite <- H.
    apply surjective_pairing. }
  rewrite (x4_loop_iter ht s n f P1 P2 P3 P4 p1 lo1 p2 lo2 p3 lo3 p4 lo4 O1 O2 O3 O4 _ _ _ _ ltac:(lia)
             (Ex _ _ _ _ R1) (Ex _ _ _ _ R2) (Ex _ _ _ _ R3) (Ex _ _ _ _ R4) I1 I2 I3 I4 Hle1 Hle2 Hle3 Hle4) in E.
  unfold x4_ex, x4_mx, x4_lens.
  split; [split; [|split]|split; [auto|]].
  - destruct (x4_es _ _ _ _); exact E.
  - destruct (x4_es _ _ _ _) eqn:Es; [|intros C; discriminate]. intros _.
    rewrite Nat2Z.inj_succ in Hf. rewrite Z.max_lub_lt_iff in Hf |- *. lia.
  - destruct (x4_es _ _ _ _) eqn:Es; [|intros C; discriminate]. intros _ _.
    unfold x4_es in Es. rewrite !andb_true_iff, !Z.eqb_eq in Es. destruct Es as (((E1 & E2) & E3) & E4).
    destruct F1 as [F1|F1]; [|lia]. destruct F2 as [F2|F2]; [|lia].
    destruct F3 as [F3|F3]; [|lia]. destruct F4 as [F4|F4]; [|lia]. lia.
  - apply (x4_mem_reload oc d n p1 lo1 p2 lo2 p3 lo3); auto; [destruct F1 | destruct F2 | destruct F3]; tauto.
Qed.

(* the loop head with endSignal = 1 and op4 < olimit: the start of an iteration *)
Lemma bx_init (ht: huf_table) (s: list Z) (n d: Z) (oc: list val) (fh: nat)
    (p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) (o1 o2 o3 o4: list Z) :
  x4_ex ht s n oc d 1 fh p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 o1 o2 o3 o4 ->
  x4_bx ht s n d oc (Nat.pred fh) p1 p2 p3 p4 o1 o2 o3 o4 k4 0 p1 lo1 k1 0 p2 lo2 k2 0 p3 lo3 k3 0 p4 lo4 k4.
Proof.
  intros ((E & Hf & Hbc) & (L1 & L2 & L3 & L4) & Hm).
  specialize (Hf eq_refl). rewrite Z.eqb_refl in E.
  destruct fh as [|f]; [rewrite Z.max_lub_lt_iff in Hf; simpl in Hf; lia|]. simpl Nat.pred.
  unfold x4_bx, x4_r. simpl Z.to_nat. cbn [xh_x2_n fst snd]. rewrite !app_nil_r.
  split; [exact E|]. split; [exact L4|]. split; [rewrite <- L4; exact Hf|].
  repeat (split; [first [reflexivity | assumption] |]).
  split; [|exact Hm].
  intros Hk. rewrite <- L4 in Hk. specialize (Hbc eq_refl Hk). lia.
Qed.

(* before the loop: the four streams initialized, nothing emitted *)
Lemma x4_ex_init (ht: huf_table) (s: list Z) (n: Z) (oc: list val) (d: Z) :
  bytes_ok s -> 10 <= Zlength s -> 6 <= n -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  bs_wf (x4s1 s) = true -> bs_wf (x4s2 s) = true -> bs_wf (x4s3 s) = true -> bs_wf (x4s4 s) = true ->
  x4_ex ht s n oc d 1 (Z.to_nat n + 1)
    (bs_total (x4s1 s)) (8 * Z.max 0 (le_field s 0 2 - 8)) 0
    (bs_total (x4s2 s)) (8 * Z.max 0 (le_field s 2 2 - 8)) 0
    (bs_total (x4s3 s)) (8 * Z.max 0 (le_field s 4 2 - 8)) 0
    (bs_total (x4s4 s)) (8 * Z.max 0 (Zlength s - (le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6) - 8)) 0
    nil nil nil nil.
Proof.
  intros Hs H10 Hn Hfit W1 W2 W3 W4.
  assert (Hl1: 0 <= le_field s 0 2 < 65536) by (apply le_field2_range; auto).
  assert (Hl2: 0 <= le_field s 2 2 < 65536) by (apply le_field2_range; auto).
  assert (Hl3: 0 <= le_field s 4 2 < 65536) by (apply le_field2_range; auto).
  assert (Z1: Zlength (x4s1 s) = le_field s 0 2) by (unfold x4s1; rewrite Zlength_sublist; lia).
  assert (Z2: Zlength (x4s2 s) = le_field s 2 2) by (unfold x4s2; rewrite Zlength_sublist; lia).
  assert (Z3: Zlength (x4s3 s) = le_field s 4 2) by (unfold x4s3; rewrite Zlength_sublist; lia).
  assert (Z4: Zlength (x4s4 s) = Zlength s - (le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6))
    by (unfold x4s4; rewrite Zlength_sublist; lia).
  pose proof (x4_dec_eq ht s n Hs H10 Hn Hfit W1 W2 W3 W4) as E.
  unfold x4_d0 in E. rewrite Z1, Z2, Z3, Z4 in E.
  unfold x4_ex, x4_mx, x4_lens. rewrite Z.eqb_refl.
  split; [split; [|split]|split; [repeat split; reflexivity | apply x4_mem_init]].
  - rewrite E. destruct (8 <=? n - 3 * ((n + 3) / 4)) eqn:E8; [reflexivity|].
    apply Z.leb_gt in E8. rewrite Nat.add_1_r, x4_loop_stop by (rewrite Zlength_nil; lia). reflexivity.
  - intros _. rewrite Nat2Z.inj_add, Z2Nat.id, Zlength_nil by lia. rewrite Z.max_lub_lt_iff. change (Z.of_nat 1) with 1.
    pose proof (Z.div_pos (n + 3) 4). split; lia.
  - intros _ C. rewrite Zlength_nil in C. lia.
Qed.

Section Loop.
Context {Espec: OracleKind}.
Variables (gv: globals) (ht: huf_table) (sht: share) (dt: val) (L: Z) (res: val) (c2: list (val * (val * val)))
  (sho: share) (ob: val) (oc: list val) (d n: Z) (sh: share) (base: val) (N: Z) (c: list val) (off: Z) (s: list Z)
  (v1 v2 v3 v4 vd: val).
Hypotheses (Hf: hsym_facts) (SH: readable_share sht) (SH0: writable_share sho) (Hsh: readable_share sh)
  (Hd: 0 <= d) (Hn: 6 <= n <= ZSTD_BLOCKSIZE_MAX) (Hdn: d + n <= Zlength oc)
  (Hs3: 3 * ((n + 3) / 4) <= n) (Hs4: n <= 4 * ((n + 3) / 4)) (Hs2: 2 <= (n + 3) / 4)
  (Hbs: bytes_ok s) (Hfit: le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s)
  (Hl1: 0 <= le_field s 0 2) (Hl2: 0 <= le_field s 2 2) (Hl3: 0 <= le_field s 4 2)
  (Htab: x2_tab_ok ht L c2) (HT: x4_tabx ht L c2).

(* one iteration: its start (positions P_i, outputs O_i, fuel S f) is fixed *)
Section Body.
Variables (P1 P2 P3 P4: Z) (O1 O2 O3 O4: list Z) (f: nat).

Definition bst (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) : environ -> mpred :=
  PROP (x4_bfacts oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4; x4_vmid ht s n d oc' j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4;
        x4_bx ht s n d oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4)
  LOCAL (temp _endSignal (Vint (Int.repr 1));
         temp _op4 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) ob);
         temp _op3 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + k3) ob);
         temp _op2 (offset_val (d + (n + 3) / 4 + k2) ob); temp _op1 (offset_val (d + k1) ob);
         temp _opStart4 (offset_val (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4) ob);
         temp _opStart3 (offset_val (d + (n + 3) / 4 + (n + 3) / 4) ob);
         temp _opStart2 (offset_val (d + (n + 3) / 4) ob);
         temp _dt (offset_val 4 dt); temp _dtLog (Vint (Int.repr L));
         temp _olimit (offset_val (d + (n + -7)) ob); temp _oend (offset_val (d + n) ob);
         lvar _dtd (Tstruct ___gp_DTableDesc noattr) vd;
         lvar _bitD4 (Tstruct ___gp_BIT_DStream_t noattr) v4; lvar _bitD3 (Tstruct ___gp_BIT_DStream_t noattr) v3;
         lvar _bitD2 (Tstruct ___gp_BIT_DStream_t noattr) v2; lvar _bitD1 (Tstruct ___gp_BIT_DStream_t noattr) v1;
         gvars gv; temp _dstSize (Vlong (Int64.repr n)))
  SEP (BIT_DStream_rep_g true Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4;
       bit_src sh (offset_val off base) s; zstd_globals gv;
       BIT_DStream_rep_g true Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s) (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3;
       BIT_DStream_rep_g true Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2;
       BIT_DStream_rep_g true Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1;
       data_at Tsh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res))) vd;
       data_at sht t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res))) dt;
       data_at sht (tarray t_deltx2 (2 ^ L)) c2 (offset_val 4 dt);
       memory_block sht (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) dt);
       data_at sho (tarray tuchar (Zlength oc)) oc' ob;
       data_at sh (tarray tuchar off) (sublist 0 off c) base;
       data_at sh (tarray tuchar (N - (off + Zlength s))) (sublist (off + Zlength s) N c) (offset_val (off + Zlength s) base)).

Lemma dec_s1 (t: ident) (Ht: In t [_t'12; _t'20; _t'32; _t'40]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j1 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (dcall4 _op1 _bitD1 t)
    (normal_ret_assert (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. simpl in Ht. repeat destruct Ht as [<- | Ht]; [(unfold bst, dcall4, tX2c, Delta4; Intros;
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
  match goal with H: x4_bfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HB end;
  match goal with H: x4_vmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HV end;
  let Hl := fresh "Hl" in
  assert (Hl: Zlength oc' = Zlength oc) by
    (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&[? _]&_); auto);
  destruct (proj1 Htab) as [Hlog _]; destruct (proj1 (proj2 Htab)) as [HL1 HL2];
  replace (Zlength oc) with (Zlength oc') by auto;
  match goal with H: x4_bx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HX end;
  assert_PROP (bit_inv (sublist 6 (6 + le_field s 0 2) s) p1 lo1) as HI
    by (rewrite rep_g_true; sep_apply (bit_rep_np_inv4 Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1); entailer!);
  let HA := fresh "HA" in
  assert (HA: 0 <= d + k1 /\ d + k1 + 2 <= Zlength oc' /\ lo1 + 64 - (p1 - L) <= Int.max_unsigned)
    by (destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 & _);
        unfold HUF_TABLELOG_MAX in *; rep_lia);
  pose proof (proj2 HT) as Hc2x;
  forward_call (Tsh, v1, gv, (sublist 6 (6 + le_field s 0 2) s), offset_val 6 (offset_val off base), p1, lo1, sht, offset_val 4 dt,
                ht, L, c2, sho, ob, oc', d + k1, true)); Intros vret; destruct vret as [[[v kk] b2] nb]; simpl fst in *; simpl snd in *; forward;
  match goal with Hst: x2_step _ _ _ _ _ _, Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _ |- _ =>
    destruct (x2_step_bnd _ _ _ _ _ _ Hst) as (Hkk & Hnb & Hb2');
    pose proof (hsym_range ht L v (proj1 Htab) ltac:(lia) Hv) as Hr;
    destruct (bf_step1 oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb (fst (hsym ht L v)) b2 Hd Hdn Hs3 Hs4 Hs2 HB Hj Hkk
                ltac:(unfold HUF_TABLELOG_MAX in *; lia) ltac:(lia) Hb2') as (HB' & Ha0 & Ha2 & HlW);
    pose proof (x4v_step1 Hf ht L c2 s n d oc' j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb Htab Hbs Hd ltac:(lia) Hs3 Hs4 Hs2
                  ltac:(destruct HB as (_&_&?&?&?&?&_); lia) Hx Hst HV) as HV';
    first [ match goal with Hxa: v = xb_look_fast _ _ /\ _ |- _ => pose proof (bx_step1 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv (proj1 Hxa) (proj2 Hxa) Hst) as HX' end
          | match goal with Hvx: v = xb_look_fast _ _, Hc: nth (Z.to_nat v) _ _ = _ |- _ =>
              pose proof (bx_step1 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv Hvx Hc Hst) as HX' end ]
  end;
  Exists (p1 - nb) (k1 + kk) (wr2 oc' (d + k1) (fst (hsym ht L v)) b2);
  unfold wr2 in *; entailer!; try (f_equal; lia); try (f_equal; unfold Z.div; lia); try (rewrite <- Hl in HlW; rewrite HlW; cancel) .. | contradiction].
Qed.

Lemma dec_s2 (t: ident) (Ht: In t [_t'14; _t'23; _t'34; _t'41]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j2 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (dcall4 _op2 _bitD2 t)
    (normal_ret_assert (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. simpl in Ht. repeat destruct Ht as [<- | Ht]; [(unfold bst, dcall4, tX2c, Delta4; Intros;
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
  match goal with H: x4_bfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HB end;
  match goal with H: x4_vmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HV end;
  let Hl := fresh "Hl" in
  assert (Hl: Zlength oc' = Zlength oc) by
    (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&[? _]&_); auto);
  destruct (proj1 Htab) as [Hlog _]; destruct (proj1 (proj2 Htab)) as [HL1 HL2];
  replace (Zlength oc) with (Zlength oc') by auto;
  match goal with H: x4_bx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HX end;
  assert_PROP (bit_inv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) p2 lo2) as HI
    by (rewrite rep_g_true; sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2); entailer!);
  let HA := fresh "HA" in
  assert (HA: 0 <= d + (n + 3) / 4 + k2 /\ d + (n + 3) / 4 + k2 + 2 <= Zlength oc' /\ lo2 + 64 - (p2 - L) <= Int.max_unsigned)
    by (destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 & _);
        unfold HUF_TABLELOG_MAX in *; rep_lia);
  pose proof (proj2 HT) as Hc2x;
  forward_call (Tsh, v2, gv, (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s), offset_val (6 + le_field s 0 2) (offset_val off base), p2, lo2, sht, offset_val 4 dt,
                ht, L, c2, sho, ob, oc', d + (n + 3) / 4 + k2, true)); Intros vret; destruct vret as [[[v kk] b2] nb]; simpl fst in *; simpl snd in *; forward;
  match goal with Hst: x2_step _ _ _ _ _ _, Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _ |- _ =>
    destruct (x2_step_bnd _ _ _ _ _ _ Hst) as (Hkk & Hnb & Hb2');
    pose proof (hsym_range ht L v (proj1 Htab) ltac:(lia) Hv) as Hr;
    destruct (bf_step2 oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb (fst (hsym ht L v)) b2 Hd Hdn Hs3 Hs4 Hs2 HB Hj Hkk
                ltac:(unfold HUF_TABLELOG_MAX in *; lia) ltac:(lia) Hb2') as (HB' & Ha0 & Ha2 & HlW);
    pose proof (x4v_step2 Hf ht L c2 s n d oc' j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb Htab Hbs Hd ltac:(lia) Hs3 Hs4 Hs2
                  ltac:(destruct HB as (_&_&?&?&?&?&_); lia) Hx Hst HV) as HV';
    first [ match goal with Hxa: v = xb_look_fast _ _ /\ _ |- _ => pose proof (bx_step2 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv (proj1 Hxa) (proj2 Hxa) Hst) as HX' end
          | match goal with Hvx: v = xb_look_fast _ _, Hc: nth (Z.to_nat v) _ _ = _ |- _ =>
              pose proof (bx_step2 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv Hvx Hc Hst) as HX' end ]
  end;
  Exists (p2 - nb) (k2 + kk) (wr2 oc' (d + (n + 3) / 4 + k2) (fst (hsym ht L v)) b2);
  unfold wr2 in *; entailer!; try (f_equal; lia); try (f_equal; unfold Z.div; lia); try (rewrite <- Hl in HlW; rewrite HlW; cancel) .. | contradiction].
Qed.

Lemma dec_s3 (t: ident) (Ht: In t [_t'16; _t'26; _t'36; _t'42]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j3 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (dcall4 _op3 _bitD3 t)
    (normal_ret_assert (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. simpl in Ht. repeat destruct Ht as [<- | Ht]; [(unfold bst, dcall4, tX2c, Delta4; Intros;
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
  match goal with H: x4_bfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HB end;
  match goal with H: x4_vmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HV end;
  let Hl := fresh "Hl" in
  assert (Hl: Zlength oc' = Zlength oc) by
    (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&[? _]&_); auto);
  destruct (proj1 Htab) as [Hlog _]; destruct (proj1 (proj2 Htab)) as [HL1 HL2];
  replace (Zlength oc) with (Zlength oc') by auto;
  match goal with H: x4_bx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HX end;
  assert_PROP (bit_inv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s) p3 lo3) as HI
    by (rewrite rep_g_true; sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s) (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3); entailer!);
  let HA := fresh "HA" in
  assert (HA: 0 <= d + (n + 3) / 4 + (n + 3) / 4 + k3 /\ d + (n + 3) / 4 + (n + 3) / 4 + k3 + 2 <= Zlength oc' /\ lo3 + 64 - (p3 - L) <= Int.max_unsigned)
    by (destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 & _);
        unfold HUF_TABLELOG_MAX in *; rep_lia);
  pose proof (proj2 HT) as Hc2x;
  forward_call (Tsh, v3, gv, (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s), offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base), p3, lo3, sht, offset_val 4 dt,
                ht, L, c2, sho, ob, oc', d + (n + 3) / 4 + (n + 3) / 4 + k3, true)); Intros vret; destruct vret as [[[v kk] b2] nb]; simpl fst in *; simpl snd in *; forward;
  match goal with Hst: x2_step _ _ _ _ _ _, Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _ |- _ =>
    destruct (x2_step_bnd _ _ _ _ _ _ Hst) as (Hkk & Hnb & Hb2');
    pose proof (hsym_range ht L v (proj1 Htab) ltac:(lia) Hv) as Hr;
    destruct (bf_step3 oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb (fst (hsym ht L v)) b2 Hd Hdn Hs3 Hs4 Hs2 HB Hj Hkk
                ltac:(unfold HUF_TABLELOG_MAX in *; lia) ltac:(lia) Hb2') as (HB' & Ha0 & Ha2 & HlW);
    pose proof (x4v_step3 Hf ht L c2 s n d oc' j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb Htab Hbs Hd ltac:(lia) Hs3 Hs4 Hs2
                  ltac:(destruct HB as (_&_&?&?&?&?&_); lia) Hx Hst HV) as HV';
    first [ match goal with Hxa: v = xb_look_fast _ _ /\ _ |- _ => pose proof (bx_step3 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv (proj1 Hxa) (proj2 Hxa) Hst) as HX' end
          | match goal with Hvx: v = xb_look_fast _ _, Hc: nth (Z.to_nat v) _ _ = _ |- _ =>
              pose proof (bx_step3 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv Hvx Hc Hst) as HX' end ]
  end;
  Exists (p3 - nb) (k3 + kk) (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + k3) (fst (hsym ht L v)) b2);
  unfold wr2 in *; entailer!; try (f_equal; lia); try (f_equal; unfold Z.div; lia); try (rewrite <- Hl in HlW; rewrite HlW; cancel) .. | contradiction].
Qed.

Lemma dec_s4 (t: ident) (Ht: In t [_t'18; _t'29; _t'38; _t'43]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j4 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (dcall4 _op4 _bitD4 t)
    (normal_ret_assert (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'')).
Proof.
  intros Hj. simpl in Ht. repeat destruct Ht as [<- | Ht]; [(unfold bst, dcall4, tX2c, Delta4; Intros;
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
  match goal with H: x4_bfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HB end;
  match goal with H: x4_vmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HV end;
  let Hl := fresh "Hl" in
  assert (Hl: Zlength oc' = Zlength oc) by
    (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&[? _]&_); auto);
  destruct (proj1 Htab) as [Hlog _]; destruct (proj1 (proj2 Htab)) as [HL1 HL2];
  replace (Zlength oc) with (Zlength oc') by auto;
  match goal with H: x4_bx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HX end;
  assert_PROP (bit_inv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) p4 lo4) as HI
    by (rewrite rep_g_true; sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4); entailer!);
  let HA := fresh "HA" in
  assert (HA: 0 <= d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 /\ d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4 + 2 <= Zlength oc' /\ lo4 + 64 - (p4 - L) <= Int.max_unsigned)
    by (destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 & _);
        unfold HUF_TABLELOG_MAX in *; rep_lia);
  pose proof (proj2 HT) as Hc2x;
  forward_call (Tsh, v4, gv, (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s), offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base), p4, lo4, sht, offset_val 4 dt,
                ht, L, c2, sho, ob, oc', d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4, true)); Intros vret; destruct vret as [[[v kk] b2] nb]; simpl fst in *; simpl snd in *; forward;
  match goal with Hst: x2_step _ _ _ _ _ _, Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _ |- _ =>
    destruct (x2_step_bnd _ _ _ _ _ _ Hst) as (Hkk & Hnb & Hb2');
    pose proof (hsym_range ht L v (proj1 Htab) ltac:(lia) Hv) as Hr;
    destruct (bf_step4 oc oc' d n k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 kk nb (fst (hsym ht L v)) b2 Hd Hdn Hs3 Hs4 Hs2 HB Hj Hkk
                ltac:(unfold HUF_TABLELOG_MAX in *; lia) ltac:(lia) Hb2') as (HB' & Ha0 & Ha2 & HlW);
    pose proof (x4v_step4 Hf ht L c2 s n d oc' j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb Htab Hbs Hd ltac:(lia) Hs3 Hs4 Hs2
                  ltac:(destruct HB as (_&_&?&?&?&?&_); lia) Hx Hst HV) as HV';
    first [ match goal with Hxa: v = xb_look_fast _ _ /\ _ |- _ => pose proof (bx_step4 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv (proj1 Hxa) (proj2 Hxa) Hst) as HX' end
          | match goal with Hvx: v = xb_look_fast _ _, Hc: nth (Z.to_nat v) _ _ = _ |- _ =>
              pose proof (bx_step4 ht L s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 v kk b2 nb HB HX Hj Hd Hdn Hs3 Hs4 HI (proj1 HT) (proj1 Htab) (proj1 (proj2 Htab)) Hv Hvx Hc Hst) as HX' end ]
  end;
  Exists (p4 - nb) (k4 + kk) (wr2 oc' (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (fst (hsym ht L v)) b2);
  unfold wr2 in *; entailer!; try (f_equal; lia); try (f_equal; unfold Z.div; lia); try (rewrite <- Hl in HlW; rewrite HlW; cancel) .. | contradiction].
Qed.

Lemma decA_s1 (t tm: ident) (Ht: In (t, tm) [(_t'12, _t'13); (_t'32, _t'33)]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j1 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence (mcall4 tm) (Sifthenelse (Etempvar tm tuint) (dcall4 _op1 _bitD1 t) Sskip)) Sbreak)
    (normal_ret_assert (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. assert (Ht1: In t [_t'12; _t'20; _t'32; _t'40]) by (simpl in Ht; destruct Ht as [E|[E|[]]]; inv E; simpl; tauto).
  simpl in Ht.
  repeat destruct Ht as [Ht | Ht]; [inv Ht;
    (apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros;
     abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
     forward_call tt;
     forward_if (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'');
     [ eapply semax_normal_post;
       [ eapply semax_pre; [| apply (dec_s1 _ Ht1 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]; unfold bst; entailer!
       | simpl; intros rho; apply andp_left2; apply derives_refl ]
     | exfalso; discriminate ]) .. | contradiction].
Qed.

Lemma decB_s1 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j1 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence
       (Ssequence (mcall4 _t'21)
          (Sifthenelse (Etempvar _t'21 tuint) (Sset _t'22 (Econst_int (Int.repr 1) tint))
             (Sset _t'22 (Ecast (Ebinop Ole (Econst_int (Int.repr 12) tint) (Econst_int (Int.repr 12) tint) tint) tbool))))
       (Sifthenelse (Etempvar _t'22 tint) (dcall4 _op1 _bitD1 _t'20) Sskip)) Sbreak)
    (normal_ret_assert (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  forward_call tt.
  forward_if (temp _t'22 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. discriminate. }
  forward_if (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'').
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dec_s1 _t'20 ltac:(simpl; tauto) k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]. unfold bst. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma decC_s1 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j1 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (Sloop (dcall4 _op1 _bitD1 _t'40) Sbreak) (normal_ret_assert (EX p1': Z, EX k1': Z, EX oc'': list val, bst k4h (j1 + 1) p1' lo1 k1' j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof. intros Hj. apply semax_dw0n. apply (dec_s1 _t'40 ltac:(simpl; tauto)); auto. Qed.

Lemma decA_s2 (t tm: ident) (Ht: In (t, tm) [(_t'14, _t'15); (_t'34, _t'35)]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j2 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence (mcall4 tm) (Sifthenelse (Etempvar tm tuint) (dcall4 _op2 _bitD2 t) Sskip)) Sbreak)
    (normal_ret_assert (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. assert (Ht1: In t [_t'14; _t'23; _t'34; _t'41]) by (simpl in Ht; destruct Ht as [E|[E|[]]]; inv E; simpl; tauto).
  simpl in Ht.
  repeat destruct Ht as [Ht | Ht]; [inv Ht;
    (apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros;
     abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
     forward_call tt;
     forward_if (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'');
     [ eapply semax_normal_post;
       [ eapply semax_pre; [| apply (dec_s2 _ Ht1 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]; unfold bst; entailer!
       | simpl; intros rho; apply andp_left2; apply derives_refl ]
     | exfalso; discriminate ]) .. | contradiction].
Qed.

Lemma decB_s2 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j2 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence
       (Ssequence (mcall4 _t'24)
          (Sifthenelse (Etempvar _t'24 tuint) (Sset _t'25 (Econst_int (Int.repr 1) tint))
             (Sset _t'25 (Ecast (Ebinop Ole (Econst_int (Int.repr 12) tint) (Econst_int (Int.repr 12) tint) tint) tbool))))
       (Sifthenelse (Etempvar _t'25 tint) (dcall4 _op2 _bitD2 _t'23) Sskip)) Sbreak)
    (normal_ret_assert (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  forward_call tt.
  forward_if (temp _t'25 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. discriminate. }
  forward_if (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'').
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dec_s2 _t'23 ltac:(simpl; tauto) k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]. unfold bst. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma decC_s2 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j2 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (Sloop (dcall4 _op2 _bitD2 _t'41) Sbreak) (normal_ret_assert (EX p2': Z, EX k2': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 (j2 + 1) p2' lo2 k2' j3 p3 lo3 k3 j4 p4 lo4 k4 oc'')).
Proof. intros Hj. apply semax_dw0n. apply (dec_s2 _t'41 ltac:(simpl; tauto)); auto. Qed.

Lemma decA_s3 (t tm: ident) (Ht: In (t, tm) [(_t'16, _t'17); (_t'36, _t'37)]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j3 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence (mcall4 tm) (Sifthenelse (Etempvar tm tuint) (dcall4 _op3 _bitD3 t) Sskip)) Sbreak)
    (normal_ret_assert (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. assert (Ht1: In t [_t'16; _t'26; _t'36; _t'42]) by (simpl in Ht; destruct Ht as [E|[E|[]]]; inv E; simpl; tauto).
  simpl in Ht.
  repeat destruct Ht as [Ht | Ht]; [inv Ht;
    (apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros;
     abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
     forward_call tt;
     forward_if (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'');
     [ eapply semax_normal_post;
       [ eapply semax_pre; [| apply (dec_s3 _ Ht1 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]; unfold bst; entailer!
       | simpl; intros rho; apply andp_left2; apply derives_refl ]
     | exfalso; discriminate ]) .. | contradiction].
Qed.

Lemma decB_s3 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j3 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence
       (Ssequence (mcall4 _t'27)
          (Sifthenelse (Etempvar _t'27 tuint) (Sset _t'28 (Econst_int (Int.repr 1) tint))
             (Sset _t'28 (Ecast (Ebinop Ole (Econst_int (Int.repr 12) tint) (Econst_int (Int.repr 12) tint) tint) tbool))))
       (Sifthenelse (Etempvar _t'28 tint) (dcall4 _op3 _bitD3 _t'26) Sskip)) Sbreak)
    (normal_ret_assert (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'')).
Proof.
  intros Hj. apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  forward_call tt.
  forward_if (temp _t'28 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. discriminate. }
  forward_if (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'').
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dec_s3 _t'26 ltac:(simpl; tauto) k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]. unfold bst. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma decC_s3 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j3 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (Sloop (dcall4 _op3 _bitD3 _t'42) Sbreak) (normal_ret_assert (EX p3': Z, EX k3': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 (j3 + 1) p3' lo3 k3' j4 p4 lo4 k4 oc'')).
Proof. intros Hj. apply semax_dw0n. apply (dec_s3 _t'42 ltac:(simpl; tauto)); auto. Qed.

Lemma decA_s4 (t tm: ident) (Ht: In (t, tm) [(_t'18, _t'19); (_t'38, _t'39)]) (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j4 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence (mcall4 tm) (Sifthenelse (Etempvar tm tuint) (dcall4 _op4 _bitD4 t) Sskip)) Sbreak)
    (normal_ret_assert (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'')).
Proof.
  intros Hj. assert (Ht1: In t [_t'18; _t'29; _t'38; _t'43]) by (simpl in Ht; destruct Ht as [E|[E|[]]]; inv E; simpl; tauto).
  simpl in Ht.
  repeat destruct Ht as [Ht | Ht]; [inv Ht;
    (apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros;
     abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta;
     forward_call tt;
     forward_if (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'');
     [ eapply semax_normal_post;
       [ eapply semax_pre; [| apply (dec_s4 _ Ht1 k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]; unfold bst; entailer!
       | simpl; intros rho; apply andp_left2; apply derives_refl ]
     | exfalso; discriminate ]) .. | contradiction].
Qed.

Lemma decB_s4 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j4 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc')
    (Sloop (Ssequence
       (Ssequence (mcall4 _t'30)
          (Sifthenelse (Etempvar _t'30 tuint) (Sset _t'31 (Econst_int (Int.repr 1) tint))
             (Sset _t'31 (Ecast (Ebinop Ole (Econst_int (Int.repr 12) tint) (Econst_int (Int.repr 12) tint) tint) tbool))))
       (Sifthenelse (Etempvar _t'31 tint) (dcall4 _op4 _bitD4 _t'29) Sskip)) Sbreak)
    (normal_ret_assert (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'')).
Proof.
  intros Hj. apply semax_dw0n; unfold mcall4; unfold bst at 1; unfold Delta4; Intros.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  forward_call tt.
  forward_if (temp _t'31 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. discriminate. }
  forward_if (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'').
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dec_s4 _t'29 ltac:(simpl; tauto) k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc' Hj)]. unfold bst. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma decC_s4 (k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4: Z) (oc': list val) :
  j4 <= 3 ->
  semax Delta4 (bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 j4 p4 lo4 k4 oc') (Sloop (dcall4 _op4 _bitD4 _t'43) Sbreak) (normal_ret_assert (EX p4': Z, EX k4': Z, EX oc'': list val, bst k4h j1 p1 lo1 k1 j2 p2 lo2 k2 j3 p3 lo3 k3 (j4 + 1) p4' lo4 k4' oc'')).
Proof. intros Hj. apply semax_dw0n. apply (dec_s4 _t'43 ltac:(simpl; tauto)); auto. Qed.

Lemma es_val (r1 r2 r3 r4: Z) : 0 <= r1 <= 3 -> 0 <= r2 <= 3 -> 0 <= r3 <= 3 -> 0 <= r4 <= 3 ->
  Int.and (Int.and (Int.and (Int.repr (Z.b2z (Int.eq (Int.repr r1) (Int.repr 0))))
    (Int.repr (Z.b2z (Int.eq (Int.repr r2) (Int.repr 0))))) (Int.repr (Z.b2z (Int.eq (Int.repr r3) (Int.repr 0)))))
    (Int.repr (Z.b2z (Int.eq (Int.repr r4) (Int.repr 0)))) = Int.repr (if x4_es r1 r2 r3 r4 then 1 else 0).
Proof.
  intros. rewrite !int_eq_small by lia. unfold x4_es.
  destruct (r1 =? 0), (r2 =? 0), (r3 =? 0), (r4 =? 0); reflexivity.
Qed.

Lemma x4_es_true (r1 r2 r3 r4: Z) : x4_es r1 r2 r3 r4 = true -> r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0.
Proof. unfold x4_es. rewrite !andb_true_iff, !Z.eqb_eq. tauto. Qed.

Lemma reload_ok (k4h p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) (oc': list val) :
  semax Delta4 (bst k4h 4 p1 lo1 k1 4 p2 lo2 k2 4 p3 lo3 k3 4 p4 lo4 k4 oc') x4_reloads
    (normal_ret_assert (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd
       (fun _ _ => True))).
Proof.
  unfold x4_reloads, x4_wbody, x4_while, x4_if, Delta4.
  cbv [seq_drop fn_body f_HUF_decompress4X2_usingDTable_internal_body].
  unfold bst. Intros. rewrite !rep_g_true.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  match goal with H: x4_bfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HB end.
  match goal with H: x4_vmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HV end.
  assert_PROP (bit_inv (sublist 6 (6 + le_field s 0 2) s) p1 lo1 /\
               bit_inv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s) p2 lo2 /\
               bit_inv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s) p3 lo3 /\
               bit_inv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s) p4 lo4) as Hinv.
  { sep_apply (bit_rep_np_inv4 Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1).
    sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)
                 (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2).
    sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3).
    sep_apply (bit_rep_np_inv4 Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)
                 (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4).
    entailer!. }
  pose proof Hinv as Hinv'.
  destruct Hinv as ((_ & _ & I1a & I1b & _ & I1c & _) & (_ & _ & I2a & I2b & _ & I2c & _) &
                    (_ & _ & I3a & I3b & _ & I3c & _) & (_ & _ & I4a & I4b & _ & I4c & _)).
  assert (Hle1: lo1 <= p1 \/ lo1 < 64) by (destruct HB as (_&_&_&_&_&_&_&_&_&_&Hb1&_); lia).
  assert (Hle2: lo2 <= p2 \/ lo2 < 64) by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&Hb2&_); lia).
  assert (Hle3: lo3 <= p3 \/ lo3 < 64) by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&Hb3&_); lia).
  assert (Hle4: lo4 <= p4 \/ lo4 < 64) by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hb4&_); lia).
  match goal with H: x4_bx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HX end.
  destruct Hinv' as (J1 & J2 & J3 & J4).
  pose proof (bx_reload ht s n d oc oc' f P1 P2 P3 P4 O1 O2 O3 O4 k4h p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4
                HB HX J1 J2 J3 J4 Hle1 Hle2 Hle3 Hle4) as HEX.
  destruct (reload_fast_facts p1 lo1 I1a I1b I1c Hle1) as (F1a & F1b & F1d).
  destruct (reload_fast_facts p2 lo2 I2a I2b I2c Hle2) as (F2a & F2b & F2d).
  destruct (reload_fast_facts p3 lo3 I3a I3b I3c Hle3) as (F3a & F3b & F3d).
  destruct (reload_fast_facts p4 lo4 I4a I4b I4c Hle4) as (F4a & F4b & F4d).
  repeat apply -> seq_assoc.
  forward_call (Tsh, v1, gv, sublist 6 (6 + le_field s 0 2) s, offset_val 6 (offset_val off base), p1, lo1,
                sh, offset_val off base, s, 6).
  { repeat match goal with |- _ /\ _ => split end;
      first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v2, gv, (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s), offset_val (6 + le_field s 0 2) (offset_val off base), p2, lo2,
                sh, offset_val off base, s, (6 + le_field s 0 2)).
  { repeat match goal with |- _ /\ _ => split end;
      first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v3, gv, (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s), offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base), p3, lo3,
                sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2)).
  { repeat match goal with |- _ /\ _ => split end;
      first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward_call (Tsh, v4, gv, (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s), offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base), p4, lo4,
                sh, offset_val off base, s, (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2)).
  { repeat match goal with |- _ /\ _ => split end;
      first [rewrite <- offset_offset_val; apply bit_src_ok_win; lia | auto]. }
  forward.
  assert (Q1: 0 <= fst (bs_reload_fast p1 lo1) <= 3) by
    (destruct F1d as [[E _]|[E _]]; rewrite E; unfold BIT_unfinished, BIT_overflow; lia).
  assert (Q2: 0 <= fst (bs_reload_fast p2 lo2) <= 3) by
    (destruct F2d as [[E _]|[E _]]; rewrite E; unfold BIT_unfinished, BIT_overflow; lia).
  assert (Q3: 0 <= fst (bs_reload_fast p3 lo3) <= 3) by
    (destruct F3d as [[E _]|[E _]]; rewrite E; unfold BIT_unfinished, BIT_overflow; lia).
  assert (Q4: 0 <= fst (bs_reload_fast p4 lo4) <= 3) by
    (destruct F4d as [[E _]|[E _]]; rewrite E; unfold BIT_unfinished, BIT_overflow; lia).
  rewrite es_val by auto.
  pose proof (x4_reload ht s n d oc' p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 HV) as HV'.
  destruct HB as (HM & Hk4h & Hj1 & Hj2 & Hj3 & Hj4 & Hk1 & Hk2 & Hk3 & Hk4 & Hb1 & Hb2 & Hb3 & Hb4 &
    Hout & R1 & R2 & R3 & R4 & Hbcs).
  assert (Hany: x4_any oc oc' d n
    (if x4_es (fst (bs_reload_fast p1 lo1)) (fst (bs_reload_fast p2 lo2)) (fst (bs_reload_fast p3 lo3))
          (fst (bs_reload_fast p4 lo4)) then 1 else 0)
    p1 (snd (bs_reload_fast p1 lo1)) k1 p2 (snd (bs_reload_fast p2 lo2)) k2
    p3 (snd (bs_reload_fast p3 lo3)) k3 p4 (snd (bs_reload_fast p4 lo4)) k4).
  { unfold x4_any. split; [destruct (x4_es _ _ _ _); auto|].
    repeat match goal with |- _ /\ _ => split end; auto; try lia.
    all: (destruct (x4_es _ _ _ _) eqn:Ees; [|intros C; discriminate C]; intros _;
      destruct (x4_es_true _ _ _ _ Ees) as (E1 & E2 & E3 & E4);
      destruct F1d as [[_ ?]|[E _]]; [|rewrite E in E1; unfold BIT_overflow in E1; lia];
      destruct F2d as [[_ ?]|[E _]]; [|rewrite E in E2; unfold BIT_overflow in E2; lia];
      destruct F3d as [[_ ?]|[E _]]; [|rewrite E in E3; unfold BIT_overflow in E3; lia];
      destruct F4d as [[_ ?]|[E _]]; [|rewrite E in E4; unfold BIT_overflow in E4; lia];
      lia). }
  repeat sep_apply BIT_DStream_rep_np_rep.
  unfold x4_state.
  Exists (if x4_es (fst (bs_reload_fast p1 lo1)) (fst (bs_reload_fast p2 lo2)) (fst (bs_reload_fast p3 lo3))
            (fst (bs_reload_fast p4 lo4)) then 1 else 0)
    p1 (snd (bs_reload_fast p1 lo1)) k1 p2 (snd (bs_reload_fast p2 lo2)) k2.
  Exists p3 (snd (bs_reload_fast p3 lo3)) k3 p4 (snd (bs_reload_fast p4 lo4)) k4 oc'.
  Exists f (O1 ++ fst (x4_r ht (x4s1 s) P1 lo1 4)) (O2 ++ fst (x4_r ht (x4s2 s) P2 lo2 4))
    (O3 ++ fst (x4_r ht (x4s3 s) P3 lo3 4)) (O4 ++ fst (x4_r ht (x4s4 s) P4 lo4 4)).
  entailer!.
Qed.

Lemma body_ok (k4h p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4: Z) (oc': list val) :
  semax Delta4 (bst k4h 0 p1 lo1 k1 0 p2 lo2 k2 0 p3 lo3 k3 0 p4 lo4 k4 oc') x4_wbody
    (normal_ret_assert (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd
       (fun _ _ => True))).
Proof.
  unfold x4_wbody, x4_while, x4_if.
  cbv [seq_drop fn_body f_HUF_decompress4X2_usingDTable_internal_body].
  eapply semax_seq'; [apply (decA_s1 _t'12 _t'13 ltac:(simpl; tauto)); lia |]. Intros p1a0 k1a0 oc0.
  eapply semax_seq'; [apply (decA_s2 _t'14 _t'15 ltac:(simpl; tauto)); lia |]. Intros p2a1 k2a1 oc1.
  eapply semax_seq'; [apply (decA_s3 _t'16 _t'17 ltac:(simpl; tauto)); lia |]. Intros p3a2 k3a2 oc2.
  eapply semax_seq'; [apply (decA_s4 _t'18 _t'19 ltac:(simpl; tauto)); lia |]. Intros p4a3 k4a3 oc3.
  eapply semax_seq'; [apply decB_s1; lia |]. Intros p1a4 k1a4 oc4.
  eapply semax_seq'; [apply decB_s2; lia |]. Intros p2a5 k2a5 oc5.
  eapply semax_seq'; [apply decB_s3; lia |]. Intros p3a6 k3a6 oc6.
  eapply semax_seq'; [apply decB_s4; lia |]. Intros p4a7 k4a7 oc7.
  eapply semax_seq'; [apply (decA_s1 _t'32 _t'33 ltac:(simpl; tauto)); lia |]. Intros p1a8 k1a8 oc8.
  eapply semax_seq'; [apply (decA_s2 _t'34 _t'35 ltac:(simpl; tauto)); lia |]. Intros p2a9 k2a9 oc9.
  eapply semax_seq'; [apply (decA_s3 _t'36 _t'37 ltac:(simpl; tauto)); lia |]. Intros p3a10 k3a10 oc10.
  eapply semax_seq'; [apply (decA_s4 _t'38 _t'39 ltac:(simpl; tauto)); lia |]. Intros p4a11 k4a11 oc11.
  eapply semax_seq'; [apply decC_s1; lia |]. Intros p1a12 k1a12 oc12.
  eapply semax_seq'; [apply decC_s2; lia |]. Intros p2a13 k2a13 oc13.
  eapply semax_seq'; [apply decC_s3; lia |]. Intros p3a14 k3a14 oc14.
  eapply semax_seq'; [apply decC_s4; lia |]. Intros p4a15 k4a15 oc15.
  apply reload_ok.
Qed.

End Body.

Lemma cmp_lt_pp (len a b0: Z) (q0: val) :
  field_compatible (tarray tuchar len) [] q0 -> 0 <= a <= len -> 0 <= b0 <= len ->
  compare_pp Clt (offset_val a q0) (offset_val b0 q0) = bool2val (a <? b0).
Proof.
  intros Hfc Ha Hc. destruct Hfc as (Hp & _ & Hsz & _). destruct q0; try contradiction.
  simpl in Hsz. rewrite Z.max_r in Hsz by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold compare_pp; simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !Ptrofs.add_unsigned, (Ptrofs.unsigned_repr a), (Ptrofs.unsigned_repr b0) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt _ _), (a <? b0) eqn:E; simpl; auto; rewrite ?Z.ltb_lt, ?Z.ltb_ge in E; lia.
Qed.

Lemma ent_exp {A: Type} (D: tycontext) (P: environ -> mpred) (F: A -> environ -> mpred) (x: A) :
  ENTAIL D, P |-- F x -> ENTAIL D, P |-- (fun rho => @exp mpred _ A (fun y => F y rho)).
Proof. intros H rho. specialize (H rho). eapply derives_trans; [apply H|]. simpl. apply exp_right with x. auto. Qed.

Lemma loop_cond_tt (len a b es: Z) (q0: val) :
  es = 0 \/ es = 1 -> field_compatible (tarray tuchar len) [] q0 -> 0 <= a <= len -> 0 <= b <= len ->
  typed_true tint (match sem_and tuint tint (Vint (Int.repr es))
    (compare_pp Clt (offset_val a q0) (offset_val b q0)) with Some v' => v' | None => Vundef end) ->
  es = 1 /\ a < b.
Proof.
  intros Hes Hfq Ha Hb H. rewrite (cmp_lt_pp len) in H by auto.
  destruct (a <? b) eqn:E; destruct Hes as [-> | ->]; compute in H;
    first [split; [reflexivity | apply Z.ltb_lt; exact E] | discriminate H | inv H].
Qed.

Lemma loop_cond_tf (len a b es: Z) (q0: val) :
  es = 0 \/ es = 1 -> field_compatible (tarray tuchar len) [] q0 -> 0 <= a <= len -> 0 <= b <= len ->
  typed_false tint (match sem_and tuint tint (Vint (Int.repr es))
    (compare_pp Clt (offset_val a q0) (offset_val b q0)) with Some v' => v' | None => Vundef end) ->
  es = 0 \/ b <= a.
Proof.
  intros Hes Hfq Ha Hb H. rewrite (cmp_lt_pp len) in H by auto.
  destruct (a <? b) eqn:E; destruct Hes as [-> | ->];
    first [left; reflexivity | right; apply Z.ltb_ge; exact E | compute in H; first [discriminate H | inv H]].
Qed.

Lemma loop_ok :
  8 <= n - 3 * ((n + 3) / 4) -> field_compatible (tarray tuchar (Zlength oc)) [] ob ->
  semax Delta4 (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd (fun _ _ => True))
    x4_while
    (normal_ret_assert (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd
       (fun es k4 => es = 0 \/ n - 3 * ((n + 3) / 4) - 7 <= k4))).
Proof.
  intros HM8 Hfco.
  unfold Delta4.
  abbreviate (func_tycontext f_HUF_decompress4X2_usingDTable_internal_body Vprog G_4X2 nil) as Delta.
  unfold x4_while, x4_if.
  cbv [seq_drop fn_body f_HUF_decompress4X2_usingDTable_internal_body].
  forward_while (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v1 v2 v3 v4 vd (fun _ _ => True)).
  - apply ENTAIL_refl.
  - entailer!.
    match goal with H: x4_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H as (_ & _ & _ & _ & Hk4 & _) end.
    eapply derives_trans; [| apply (arr_test_order sho (Zlength oc) oc' ob
        (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (d + (n + -7)) TT)];
      [cancel | auto with share | lia | lia | lia].
  - match goal with H: x4_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as (Hes & Hk1 & Hk2 & Hk3 & Hk4 & Hk1b & Hb1 & Hb2 & Hb3 & Hb4 & Hb64 & Hout & R1 & R2 & R3 & R4 & Hbcs) end.
    match goal with H: x4_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HVa end.
    apply (loop_cond_tt (Zlength oc) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (d + (n + -7)) es ob Hes Hfco)
      in HRE; [|lia|lia]. destruct HRE as [-> Hlt].
    eapply semax_normal_post.
    + match goal with H: x4_ex _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        pose proof (bx_init ht s n d oc' f p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 o1 o2 o3 o4 H) as HXi end.
      eapply semax_pre; [| apply (body_ok p1 p2 p3 p4 o1 o2 o3 o4 (Nat.pred f) k4 p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 oc')].
      pose proof (x4_head_mid ht s n d oc' p1 lo1 k1 p2 lo2 k2 p3 lo3 k3 p4 lo4 k4 ltac:(lia) Hs4 HVa) as HVm.
      destruct (Hb64 eq_refl) as (B1 & B2 & B3 & B4).
      unfold bst. rewrite !rep_g_true.
      sep_apply (BIT_DStream_rep_rep_np Tsh gv (sublist 6 (6 + le_field s 0 2) s) (offset_val 6 (offset_val off base)) p1 lo1 v1 ltac:(lia)).
      sep_apply (BIT_DStream_rep_rep_np Tsh gv (sublist (6 + le_field s 0 2) (6 + le_field s 0 2 + le_field s 2 2) s)
                   (offset_val (6 + le_field s 0 2) (offset_val off base)) p2 lo2 v2 ltac:(lia)).
      sep_apply (BIT_DStream_rep_rep_np Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2) (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) s)
                   (offset_val (6 + le_field s 0 2 + le_field s 2 2) (offset_val off base)) p3 lo3 v3 ltac:(lia)).
      sep_apply (BIT_DStream_rep_rep_np Tsh gv (sublist (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (Zlength s) s)
                   (offset_val (6 + le_field s 0 2 + le_field s 2 2 + le_field s 4 2) (offset_val off base)) p4 lo4 v4 ltac:(lia)).
      entailer!.
      unfold x4_bfacts. repeat match goal with |- _ /\ _ => split end; auto; lia.
    + unfold POSTCONDITION, abbreviate. simpl RA_normal. unfold x4_state at 1.
      Intros es' p1' lo1' k1' p2' lo2' k2'. Intros p3' lo3' k3' p4' lo4' k4' oc''. Intros f' o1' o2' o3' o4'.
      apply (ent_exp _ _ _ (es', p1', lo1', k1', p2', lo2', k2', p3', lo3', k3', p4', lo4', k4', oc'', f', o1', o2', o3', o4')).
      simpl fst; simpl snd. entailer!.
  - match goal with H: x4_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof H as Hany; destruct H as (Hes & _ & _ & _ & Hk4 & _) end.
    apply (loop_cond_tf (Zlength oc) (d + (n + 3) / 4 + (n + 3) / 4 + (n + 3) / 4 + k4) (d + (n + -7)) es ob Hes Hfco)
      in HRE; [|lia|lia].
    forward. unfold x4_state. Exists es p1 lo1 k1 p2 lo2 k2. Exists p3 lo3 k3 p4 lo4 k4 oc'. Exists f o1 o2 o3 o4.
    entailer!.
Qed.

End Loop.

(* one of the four BIT_initDStream fails *)
Lemma x4_dec_wfk (ht: huf_table) (s: list Z) (n: Z) :
  bytes_ok s -> 10 <= Zlength s -> 6 <= n -> le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6 <= Zlength s ->
  bs_wf (x4s1 s) = false \/ bs_wf (x4s2 s) = false \/ bs_wf (x4s3 s) = false \/ bs_wf (x4s4 s) = false ->
  x_huf_decode (xhuf_of true ht) false s n = None.
Proof.
  intros Hs H10 Hn Hfit Hw. apply x4_dec_wf; auto.
  destruct Hw as [E|[E|[E|E]]]; rewrite E; rewrite ?andb_false_r; reflexivity.
Qed.

Lemma body_HUF_decompress4X2_usingDTable_internal_body :
  hsym_facts -> semax_body Vprog G_4X2 f_HUF_decompress4X2_usingDTable_internal_body
    HUF_decompress4X2_usingDTable_internal_body_spec.
Proof.
  intros Hf.
  start_function.
  unfold hufdt_x_at. Intros L res c2.
  match goal with H: byte_val res |- _ => rename H into Hres end.
  match goal with H: Zlength c2 = 2 ^ L |- _ => rename H into Hc2len end.
  match goal with H: forall v, 0 <= v < 2 ^ L -> _ |- _ => rename H into Hc2ok end.
  assert (HT: x4_tabx ht L c2).
  { split; [match goal with H: L = _ |- _ => exact H end | match goal with H: c2 = _ |- _ => exact H end]. }
  match goal with H: L = _ |- _ => clear H end. match goal with H: c2 = _ |- _ => clear H end.
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
    - urepr. rewrite err_20. split3; [apply out_after_refl | discriminate |].
      split; [|split; [change (negb true) with false; rewrite x4_dec_short by lia; reflexivity | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; lia.
    - apply (hufdt_fold sht ht dt L res c2); auto. }
  forward_if. { urepr. lia. }
  urepr.
  assert (H10s: 10 <= Zlength s) by lia.
  forward. forward. forward. forward. forward. forward.
  rewrite (win_split sh N c off s base) by auto.
  Intros.
  rewrite !oadd_uchar_long by auto. rewrite osub_olimit by auto.
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
  forward. forward. forward. forward. forward.
  forward_call (Tsh, v_dtd, sht, dt, (Vint (Int.repr 12), (Vint (Int.repr 1), (Vint (Int.repr L), res)))).
  { memcpy_ok_B. }
  forward. { entailer!. simpl; rep_lia. }
  forward_if.
  { forward. Exists (Int64.max_unsigned - 19) oc. entailer!.
    - assert (Hlt: Zlength s < le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6).
      { destruct (Z_lt_le_dec (Zlength s) (le_field s 0 2 + le_field s 2 2 + le_field s 4 2 + 6)) as [?|Hge];
          [auto|exfalso]. fold l1 l2 l3 in Hge. unfold Int64.ltu in H9.
        rewrite !Int64.unsigned_repr in H9 by rep_lia. destruct zlt in H9; [lia|discriminate]. }
      rewrite err_20. split3; [apply out_after_refl | discriminate |].
      split; [|split; [change (negb true) with false; rewrite x4_dec_fit by lia; reflexivity | apply vlong_err_20]].
      destruct (huf_lits_with true ht s n) eqn:E; auto. exfalso.
      apply x4_model_facts in E; auto; [|lia]. lia.
    - rewrite (win_split sh (Zlength c) c off s base) by auto.
      sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
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
    forward_call (Tsh, v_bitD1, sh, offset_val off base, s, 6, l1, gv). { apply Forall_sublist; auto. }
    fold s1; rewrite Hw1. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; exact Hc); try (intros Hc; congruence).
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
      all: change (negb true) with false;
        rewrite (x4_dec_wfk ht s n Hbs H10s ltac:(lia) Hfit
                   (or_introl Hw1)); assumption.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  dw0.
  { forward_call (Tsh, v_bitD1, sh, offset_val off base, s, 6, l1, gv). { apply Forall_sublist; auto. }
    fold s1; rewrite Hw1. x4_chk_ok l1. }
  drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  destruct (bs_wf s2) eqn:Hw2.
  2:{ dw0. 2: apply semax_ff.
    forward_call (Tsh, v_bitD2, sh, offset_val off base, s, (6 + l1), l2, gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1) with (off + (6 + l1)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    fold s2; rewrite Hw2. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; exact Hc); try (intros Hc; congruence).
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
      all: change (negb true) with false;
        rewrite (x4_dec_wfk ht s n Hbs H10s ltac:(lia) Hfit
                   (or_intror (or_introl Hw2))); assumption.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  dw0.
  { forward_call (Tsh, v_bitD2, sh, offset_val off base, s, (6 + l1), l2, gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1) with (off + (6 + l1)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    fold s2; rewrite Hw2. x4_chk_ok l2. }
  drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  destruct (bs_wf s3) eqn:Hw3.
  2:{ dw0. 2: apply semax_ff.
    forward_call (Tsh, v_bitD3, sh, offset_val off base, s, (6 + l1 + l2), l3, gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1 + l2) with (off + (6 + l1 + l2)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    fold s3; rewrite Hw3. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; exact Hc); try (intros Hc; congruence).
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
      all: change (negb true) with false;
        rewrite (x4_dec_wfk ht s n Hbs H10s ltac:(lia) Hfit
                   (or_intror (or_intror (or_introl Hw3)))); assumption.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  dw0.
  { forward_call (Tsh, v_bitD3, sh, offset_val off base, s, (6 + l1 + l2), l3, gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1 + l2) with (off + (6 + l1 + l2)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    fold s3; rewrite Hw3. x4_chk_ok l3. }
  drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  destruct (bs_wf s4) eqn:Hw4.
  2:{ dw0. 2: apply semax_ff.
    forward_call (Tsh, v_bitD4, sh, offset_val off base, s, (6 + l1 + l2 + l3), (Zlength s - (l1 + l2 + l3 + 6)), gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1 + l2 + l3) with (off + (6 + l1 + l2 + l3)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    replace (6 + l1 + l2 + l3 + (Zlength s - (l1 + l2 + l3 + 6))) with (Zlength s) by lia. fold s4; rewrite Hw4. x4_chk_err.
    forward. Exists r oc. entailer!.
    - repeat split; try apply out_after_refl; try (intros Hc; exact Hc); try (intros Hc; congruence).
      destruct (huf_lits_with true ht s n) eqn:E; auto.
      apply x4_model_facts in E; auto; [|lia]. fold l1 l2 l3 s1 s2 s3 s4 in E. exfalso; intuition congruence.
      all: change (negb true) with false;
        rewrite (x4_dec_wfk ht s n Hbs H10s ltac:(lia) Hfit
                   (or_intror (or_intror (or_intror Hw4)))); assumption.
    - unfold bit_src. rewrite (win_split sh (Zlength c) c off s base) by auto.
      repeat sep_apply rep_data_at_. sep_apply (hufdt_fold sht ht dt L res c2); auto. cancel. }
  dw0.
  { forward_call (Tsh, v_bitD4, sh, offset_val off base, s, (6 + l1 + l2 + l3), (Zlength s - (l1 + l2 + l3 + 6)), gv). 1: (entailer!; rewrite ?offset_offset_val; replace (off + 6 + l1 + l2 + l3) with (off + (6 + l1 + l2 + l3)) by lia; reflexivity). 1: (apply Forall_sublist; auto).
    replace (6 + l1 + l2 + l3 + (Zlength s - (l1 + l2 + l3 + 6))) with (Zlength s) by lia. fold s4; rewrite Hw4. x4_chk_ok (Zlength s - (l1 + l2 + l3 + 6)). }
  drop_LOCAL 0%nat. drop_LOCAL 0%nat.
  assert (Hz1: Zlength s1 = l1) by (unfold s1; rewrite Zlength_sublist; lia).
  assert (Hz2: Zlength s2 = l2) by (unfold s2; rewrite Zlength_sublist; lia).
  assert (Hz3: Zlength s3 = l3) by (unfold s3; rewrite Zlength_sublist; lia).
  assert (Hz4: Zlength s4 = Zlength s - (l1 + l2 + l3 + 6)) by (unfold s4; rewrite Zlength_sublist; lia).
  assert (B1 := bs_init_bounds s1 Hw1 ltac:(apply Forall_sublist; auto)). rewrite Hz1 in B1.
  assert (B2 := bs_init_bounds s2 Hw2 ltac:(apply Forall_sublist; auto)). rewrite Hz2 in B2.
  assert (B3 := bs_init_bounds s3 Hw3 ltac:(apply Forall_sublist; auto)). rewrite Hz3 in B3.
  assert (B4 := bs_init_bounds s4 Hw4 ltac:(apply Forall_sublist; auto)). rewrite Hz4 in B4.
  assert (Hinit := x4_init ht s n d oc H5 Hbs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (x4_ex_init ht s n oc d Hbs H10s ltac:(lia) Hfit Hw1 Hw2 Hw3 Hw4) as HEX0.
  forward_if (x4_state gv ht sht dt L res c2 sho ob oc d n sh base N c off s v_bitD1 v_bitD2 v_bitD3 v_bitD4 v_dtd
                (fun es k4 => es = 0 \/ n - 3 * seg - 7 <= k4)).
  { apply prop_right; rewrite sameblock_offset_val by auto; reflexivity. }
  { match goal with H: context [sem_sub_pp] |- _ =>
      rewrite sub_pp_gen in H by (auto; rep_lia); simpl in H; apply ltu_tt in H; [|rep_lia];
      change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H; rename H into HM8 end.
    eapply semax_normal_post.
    - assert (Htab: x2_tab_ok ht L c2) by (split; [auto | split; [auto | split; auto]]).
      eapply semax_pre; [| apply (loop_ok gv ht sht dt L res c2 sho ob oc d n sh base N c off s
                                   v_bitD1 v_bitD2 v_bitD3 v_bitD4 v_dtd Hf)];
        [ | auto; try (unfold ZSTD_BLOCKSIZE_MAX in *; lia) .. ].
      + unfold x4_state.
        Exists 1 (bs_total s1) (8 * Z.max 0 (l1 - 8))%Z 0 (bs_total s2) (8 * Z.max 0 (l2 - 8))%Z 0.
        Exists (bs_total s3) (8 * Z.max 0 (l3 - 8))%Z 0 (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8))%Z 0 oc.
        Exists (Z.to_nat n + 1)%nat (@nil Z) (@nil Z) (@nil Z) (@nil Z).
        entailer!.
        all: try exact HEX0.
        { unfold x4_any. repeat match goal with |- _ /\ _ => split end; auto; try lia;
            try apply out_after_refl; try (unfold region_bytes; intros; lia). }
        unfold s1, s2, s3, s4. cancel.
    - simpl. intros rho. apply andp_left2. apply derives_refl. }
  { forward. unfold x4_state.
    Exists 1 (bs_total s1) (8 * Z.max 0 (l1 - 8))%Z 0 (bs_total s2) (8 * Z.max 0 (l2 - 8))%Z 0.
    Exists (bs_total s3) (8 * Z.max 0 (l3 - 8))%Z 0 (bs_total s4) (8 * Z.max 0 (Zlength s - (l1 + l2 + l3 + 6) - 8))%Z 0 oc.
    Exists (Z.to_nat n + 1)%nat (@nil Z) (@nil Z) (@nil Z) (@nil Z).
    entailer!.
    all: try exact HEX0.
    { match goal with H: typed_false _ _ |- _ =>
        rewrite sub_pp_gen in H by (auto; rep_lia); simpl in H; apply ltu_tf in H; [|rep_lia];
        rewrite Int64.unsigned_repr in H by rep_lia end.
      split; [|right; lia]. unfold x4_any.
      split; [right; reflexivity|].
      repeat split; try lia; try apply out_after_refl; try (intros Hbx; exact Hbx); unfold region_bytes; intros; lia. }
    unfold s1, s2, s3, s4. cancel. }
  (* ---------- after the loop ---------- *)
  apply (x4_tail_ok gv ht sht dt L res c2 sho ob oc d n sh base N c off s v_bitD1 v_bitD2 v_bitD3 v_bitD4 v_dtd);
    auto; try lia.
Qed.
