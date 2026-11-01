(* ZSTD_decodeLiteralsBlock exactly (BlkIface.lits_exact): the outcome of each arm of its switch, as the C computes it,
   is model/ExBlock.v's x_lits (the section) and x_lits_store (its stores, in the C's order).  Pure lemmas, one per
   arm and literal place, stated with the C's results as the VST proofs of the arms (BlkLIT3Raw, BlkLIT3Rle,
   BlkLIT3Comp) obtain them:
   - the output array after ZSTD_allocateLiteralsBuffer is alloc_out (the zeroed slack, patch item 19), then the
     copies of the arm (cwr: a memcpy / memset / Huffman output / memmove into the array);
   - litExtraBuffer (lxb, LITEXTRA_N bytes) gets the literals from its start (LExtra) or the last 65536 of them
     (LSplit);
   - the model's closed forms (xl_* lemmas) are the C's checks in their order. *)
Require Export Zstd.proof.dec.v3.B.BlkLIT3Base.
Local Open Scope bool_scope.
Local Open Scope Z_scope.

(* the facts of the precondition the exact outcome depends on *)
Definition lx_hyps (o: outarr) (i: inwin) (bsm streaming: Z) (lxb: list Z) : Prop :=
  outarr_ok o /\ inwin_ok i /\ (streaming = 0 \/ streaming = 1) /\ 0 <= bsm <= ZSTD_BLOCKSIZE_MAX /\
  Zlength (iw_s i) <= bsm /\ Zlength lxb = LITEXTRA_N.

(* the compressed header's sizes lhSize and litCSize are not negative *)
Lemma lx_hdr_nonneg (s: list Z) (lh n cs: Z) (single: bool) :
  bytes_ok s -> 5 <= Zlength s -> lit_hdr s = (lh, n, cs, single) -> 0 <= lh /\ 0 <= cs.
Proof.
  intros Hb H5 Hh. destruct (lit_le_field s 4 Hb ltac:(lia)) as [Hc0 _].
  pose proof (lit_byte_range s 4 Hb) as B4.
  assert (Ht: forall (a b c: Z) (d: bool), (a, b, c, d) = (lh, n, cs, single) -> a = lh /\ c = cs)
    by (intros a b c d E; inversion E; auto).
  unfold lit_hdr in Hh. cbv zeta in Hh.
  destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 2); [| destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 3)];
    apply Ht in Hh; destruct Hh as [<- <-]; clear Ht.
  - split; [lia |]. apply Z.shiftr_nonneg. exact Hc0.
  - split; [lia |]. apply Z.add_nonneg_nonneg; [apply Z.shiftr_nonneg; exact Hc0 | lia].
  - split; [lia |]. apply Z.land_nonneg. right. lia.
Qed.

(* HUF_readStats on no bytes fails (four streams with litCSize = 0 are an error) *)
Lemma lx_readstats_nil : x_readstats [] = None.
Proof. vm_compute. reflexivity. Qed.

Lemma lx_pair {A B} (a c: A) (b d: B) : (a, b) = (c, d) -> a = c /\ b = d.
Proof. intros E. inversion E. auto. Qed.

(* ===================== the model's literals section, by the type of the block ===================== *)

Lemma xl_short (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) :
  Zlength s < 2 -> xb_lits hx s bsm w st = None.
Proof.
  intros H. unfold xb_lits, x_lits. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

(* set_basic *)
Lemma xl_raw (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) (lh ls: Z) :
  Z.land (byte_at s 0) 3 = 0 -> 2 <= Zlength s ->
  (Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> 3 <= Zlength s) -> lit_rawhdr s = (lh, ls) ->
  xb_lits hx s bsm w st =
  if ls >? bsm then None else if w <? ls then None else if lh + ls >? Zlength s then None
  else Some (slice s lh ls, lh + ls, hx).
Proof.
  intros Ht H2 H3 Hh. unfold lit_rawhdr in Hh. cbv zeta in Hh. unfold xb_lits, x_lits. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) H2), Ht. cbn [Z.eqb].
  destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 1) eqn:E1;
    [| destruct (Z.land (Z.shiftr (byte_at s 0) 2) 3 =? 3) eqn:E3];
    apply lx_pair in Hh; destruct Hh as [<- <-].
  - apply Z.eqb_eq in E1. rewrite E1. reflexivity.
  - apply Z.eqb_eq in E3. rewrite (proj2 (Z.ltb_ge _ _) (H3 E3)). reflexivity.
  - reflexivity.
Qed.

Lemma xl_raw3 (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) :
  Z.land (byte_at s 0) 3 = 0 -> Z.land (Z.shiftr (byte_at s 0) 2) 3 = 3 -> Zlength s < 3 ->
  xb_lits hx s bsm w st = None.
Proof.
  intros Ht H3 Hn. unfold xb_lits, x_lits. cbv zeta. rewrite Ht, H3. cbn [Z.eqb].
  destruct (Zlength s <? 2); [reflexivity |]. rewrite (proj2 (Z.ltb_lt _ _) Hn). reflexivity.
Qed.

(* set_rle *)
Lemma xl_rle (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) :
  2 <= Zlength s -> Z.land (byte_at s 0) 3 = 1 ->
  xb_lits hx s bsm w st =
    if andb (rle_lhl s =? 1) (Zlength s <? 3) then None else
    if andb (rle_lhl s =? 3) (Zlength s <? 4) then None else
    if rle_ls s >? bsm then None else
    if w <? rle_ls s then None else
    Some (repeat (byte_at s (rle_lh s)) (Z.to_nat (rle_ls s)), rle_lh s + 1, hx).
Proof.
  intros Hn Hk. unfold xb_lits, x_lits. cbv zeta. rewrite (proj2 (Z.ltb_ge _ _) Hn), Hk. cbn [Z.eqb].
  unfold rle_lh, rle_ls. fold (rle_lhl s).
  destruct (rle_lhl s =? 1); [reflexivity |]. destruct (rle_lhl s =? 3); reflexivity.
Qed.

(* set_compressed / set_repeat *)
Lemma xl_rep_none (s: list Z) (bsm w: Z) (st: bool) :
  Z.land (byte_at s 0) 3 = 3 -> xb_lits None s bsm w st = None.
Proof.
  intros Ht. unfold xb_lits, x_lits. cbv zeta. rewrite Ht. cbn [Z.eqb andb].
  destruct (Zlength s <? 2); reflexivity.
Qed.

Lemma xl_comp_short (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) :
  (Z.land (byte_at s 0) 3 = 2 \/ Z.land (byte_at s 0) 3 = 3) -> Zlength s < 5 -> xb_lits hx s bsm w st = None.
Proof.
  intros Ht Hn. unfold xb_lits, x_lits. cbv zeta.
  destruct (Zlength s <? 2); [reflexivity |]. rewrite (proj2 (Z.ltb_lt _ _) Hn).
  destruct Ht as [Ht | Ht]; rewrite Ht; cbn [Z.eqb andb]; [reflexivity | destruct hx; reflexivity].
Qed.

Lemma xl_comp (hx: option xhuf) (s: list Z) (bsm w: Z) (st: bool) (e lh n cs: Z) (single: bool) :
  bytes_ok s -> 5 <= Zlength s -> Z.land (byte_at s 0) 3 = e -> (e = 2 \/ e = 3) -> (e = 3 -> hx <> None) ->
  lit_hdr s = (lh, n, cs, single) ->
  xb_lits hx s bsm w st =
  if n >? bsm then None else if andb (negb single) (n <? 6) then None else
  if cs + lh >? Zlength s then None else if w <? n then None else
  match x_lits_huf hx e single (sublist lh (lh + cs) s) n with
  | Some (l, t) => Some (l, lh + cs, Some t)
  | None => None
  end.
Proof.
  intros Hb H5 Ht He Hx Hh.
  destruct (lx_hdr_nonneg s lh n cs single Hb H5 Hh) as [Hlh Hcs].
  unfold xb_lits, x_lits. cbv zeta. rewrite Ht.
  replace (Zlength s <? 2) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength s <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  assert (E0: (e =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (E1: (e =? 1) = false) by (apply Z.eqb_neq; lia).
  assert (E3: (e =? 3) && match hx with None => true | Some _ => false end = false).
  { destruct (Z.eqb_spec e 3) as [H3 | H3]; [| reflexivity]. destruct hx; [reflexivity |]. exfalso; apply (Hx H3); reflexivity. }
  rewrite E0, E1, E3. unfold lit_hdr in Hh. cbv zeta in Hh. rewrite Hh. unfold MIN_LITERALS_FOR_4_STREAMS.
  destruct (n >? bsm); [reflexivity |]. destruct (negb single && (n <? 6)); [reflexivity |].
  destruct (cs + lh >? Zlength s) eqn:Ec; [reflexivity |]. rewrite Z.gtb_ltb, Z.ltb_ge in Ec.
  destruct (w <? n); [reflexivity |]. rewrite lit_slice by lia. reflexivity.
Qed.

(* ===================== the Huffman part against the decoders' specifications ===================== *)

(* set_compressed: HUF_decompress1X1_DCtx_wksp (single) / HUF_decompress4X_hufOnly_wksp, as huf_dctx_spec states
   them (four = negb single) *)
Lemma xl_huf2 (hx: option xhuf) (single: bool) (cb: list Z) (n: Z) :
  (single = false -> 6 <= n) ->
  x_lits_huf hx 2 single cb n = xh_dctx (huf_dctx_x2 (negb single) n cb) (negb (negb single)) cb n.
Proof.
  intros H6. unfold x_lits_huf, huf_dctx_x2. cbn [Z.eqb Pos.eqb]. rewrite Bool.negb_involutive.
  destruct single; [reflexivity |]. cbn [negb].
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; specialize (H6 eq_refl); lia).
  destruct (Zlength cb =? 0) eqn:E; [| reflexivity].
  apply Z.eqb_eq, Zlength_nil_inv in E. subst cb. unfold xh_dctx, x_huf_read. rewrite lx_readstats_nil. reflexivity.
Qed.

(* set_repeat: HUF_decompress1X_usingDTable / 4X with the table t *)
Lemma xl_huf3 (t: xhuf) (single: bool) (cb: list Z) (n: Z) :
  x_lits_huf (Some t) 3 single cb n =
  match x_huf_decode t single cb n with Some l => Some (l, t) | None => None end.
Proof.
  reflexivity.
Qed.

(* the table xh_dctx keeps is the one HUF_readStats parses (huf_built's ht) *)
Lemma xl_dctx_tab (x2 single: bool) (cb: list Z) (n: Z) (l: list Z) (t: xhuf) (ht: huf_table) (h: Z) :
  xh_dctx x2 single cb n = Some (l, t) -> x_readstats cb = Some (ht, h) -> t = xhuf_of x2 ht.
Proof.
  intros H1 H2. unfold xh_dctx, x_huf_read in H1. rewrite H2 in H1.
  destruct (Zlength cb <=? h); [discriminate |].
  destruct (x_huf_decode _ _ _ _); [| discriminate]. inversion H1; reflexivity.
Qed.

(* ---------- the Huffman decoders emit bytes ---------- *)

(* X1 emits the cells' symbols (bytes when the cells hold bytes); X2 emits the two bytes of the cells' 16-bit
   sequences (bytes when the sequences are below 65536) *)
Definition lxh_x1_ok (t: xhuf) : Prop := forall v, is_byte (fst (fst (xh_cell t v))).
Definition lxh_x2_ok (t: xhuf) : Prop := forall v, 0 <= fst (fst (xh_cell t v)) < 65536.

Lemma lxh_app (a b: list Z) : bytes_ok a -> bytes_ok b -> bytes_ok (a ++ b).
Proof. intros. apply Forall_app. auto. Qed.

Lemma lxh_x1_n (t: xhuf) : lxh_x1_ok t -> forall k d, bytes_ok (fst (xh_x1_n t d k)).
Proof.
  intros H1. induction k as [|k IH]; intros d; [constructor|].
  cbn [xh_x1_n]. unfold xh_x1_sym.
  pose proof (H1 (xb_look_fast d (xh_log t))) as Hc.
  destruct (xh_cell t (xb_look_fast d (xh_log t))) as [[sq nb] len].
  specialize (IH (xb_skip d nb)).
  destruct (xh_x1_n t (xb_skip d nb) k) as [l d']. constructor; assumption.
Qed.

Lemma lxh_x1_loop4 (t: xhuf) : lxh_x1_ok t -> forall fuel s d rem acc,
  bytes_ok acc -> bytes_ok (fst (fst (xh_x1_loop4 fuel s t d rem acc))).
Proof.
  intros H1. induction fuel as [|fuel IH]; intros s d rem acc Ha; cbn [xh_x1_loop4]; [assumption |].
  destruct (xb_reload s d) as [st d1]. destruct (_ && _); [| assumption].
  pose proof (lxh_x1_n t H1 4 d1) as Hn. destruct (xh_x1_n t d1 4) as [l d2].
  apply IH. apply lxh_app; assumption.
Qed.

Lemma lxh_x1_stream (t: xhuf) : lxh_x1_ok t -> forall s d rem, bytes_ok (fst (xh_x1_stream t s d rem)).
Proof.
  intros H1 s d rem. unfold xh_x1_stream. destruct (3 <? rem).
  - pose proof (lxh_x1_loop4 t H1 (Z.to_nat rem + 1) s d rem nil (Forall_nil _)) as Ha.
    destruct (xh_x1_loop4 _ _ _ _ _ _) as [[a d1] r1]. cbn [fst] in Ha.
    pose proof (lxh_x1_n t H1 (Z.to_nat r1) d1) as Hb. destruct (xh_x1_n t d1 (Z.to_nat r1)) as [b d2].
    apply lxh_app; assumption.
  - destruct (xb_reload s d) as [st d1].
    pose proof (lxh_x1_n t H1 (Z.to_nat rem) d1) as Hb. destruct (xh_x1_n t d1 (Z.to_nat rem)) as [b d2].
    apply lxh_app; [constructor | assumption].
Qed.

Lemma lxh_x2_sym (t: xhuf) : lxh_x2_ok t -> forall d, bytes_ok (fst (xh_x2_sym t d)).
Proof.
  intros H2 d. unfold xh_x2_sym. pose proof (H2 (xb_look_fast d (xh_log t))) as Hc.
  destruct (xh_cell t (xb_look_fast d (xh_log t))) as [[sq nb] len]. cbn [fst] in *.
  apply Forall_firstn. constructor; [| constructor; [| constructor]]; unfold is_byte.
  - apply Z.mod_pos_bound. lia.
  - split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma lxh_x2_n (t: xhuf) : lxh_x2_ok t -> forall k d, bytes_ok (fst (xh_x2_n t d k)).
Proof.
  intros H2. induction k as [|k IH]; intros d; [constructor|].
  cbn [xh_x2_n]. pose proof (lxh_x2_sym t H2 d) as Hs. destruct (xh_x2_sym t d) as [c d1].
  specialize (IH d1). destruct (xh_x2_n t d1 k) as [l d2]. apply lxh_app; assumption.
Qed.

Lemma lxh_x2_last (t: xhuf) : lxh_x2_ok t -> forall d, bytes_ok (fst (xh_x2_last t d)).
Proof.
  intros H2 d. unfold xh_x2_last.
  destruct (xh_cell t (xb_look_fast d (xh_log t))) as [[sq nb] len]. cbn [fst].
  constructor; [| constructor]. unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma lxh_x2_loopr (t: xhuf) : lxh_x2_ok t -> forall fuel s k cond d rem acc,
  bytes_ok acc -> bytes_ok (fst (fst (xh_x2_loopr fuel s t k cond d rem acc))).
Proof.
  intros H2. induction fuel as [|fuel IH]; intros s k cond d rem acc Ha; cbn [xh_x2_loopr]; [assumption |].
  destruct (xb_reload s d) as [st d1]. destruct (_ && _); [| assumption].
  pose proof (lxh_x2_n t H2 k d1) as Hn. destruct (xh_x2_n t d1 k) as [l d2].
  apply IH. apply lxh_app; assumption.
Qed.

Lemma lxh_x2_loop1 (t: xhuf) : lxh_x2_ok t -> forall fuel d rem acc,
  bytes_ok acc -> bytes_ok (fst (fst (xh_x2_loop1 fuel t d rem acc))).
Proof.
  intros H2. induction fuel as [|fuel IH]; intros d rem acc Ha; cbn [xh_x2_loop1]; [assumption |].
  destruct (2 <=? rem); [| assumption].
  pose proof (lxh_x2_sym t H2 d) as Hn. destruct (xh_x2_sym t d) as [l d2].
  apply IH. apply lxh_app; assumption.
Qed.

Lemma lxh_x2_stream (t: xhuf) : lxh_x2_ok t -> forall s d rem, bytes_ok (fst (xh_x2_stream t s d rem)).
Proof.
  intros H2 s d rem. unfold xh_x2_stream.
  assert (Ha: forall k c d0 r0, bytes_ok (fst (fst (xh_x2_loopr (Z.to_nat rem + 1) s t k c d0 r0 nil))))
    by (intros; apply lxh_x2_loopr; auto; constructor).
  assert (Hb: forall d0 r0, bytes_ok (fst (fst (xh_x2_loop1 (Z.to_nat rem + 1) t d0 r0 nil))))
    by (intros; apply lxh_x2_loop1; auto; constructor).
  pose proof (lxh_x2_last t H2) as Hc.
  repeat (match goal with
   | |- context [xh_x2_loopr ?f ?s ?t ?k ?c ?d ?r nil] =>
       let E := fresh "E" in pose proof (Ha k c d r) as E;
       destruct (xh_x2_loopr f s t k c d r nil) as [[? ?] ?]; cbn [fst] in E
   | |- context [xh_x2_loop1 ?f ?t ?d ?r nil] =>
       let E := fresh "E" in pose proof (Hb d r) as E;
       destruct (xh_x2_loop1 f t d r nil) as [[? ?] ?]; cbn [fst] in E
   | |- context [xh_x2_last ?t ?d] =>
       let E := fresh "E" in pose proof (Hc d) as E; destruct (xh_x2_last t d) as [? ?]; cbn [fst] in E
   | |- context [xb_reload ?s ?d] => destruct (xb_reload s d) as [? ?]
   | |- context [if ?b then _ else _] => destruct b
   end; cbv beta iota).
  all: cbn [fst]; repeat (first [apply lxh_app | assumption | constructor]).
Qed.

Lemma lxh_1stream (fin: list Z -> xbit -> Z -> list Z * xbit) (src: list Z) (n: Z) (l: list Z) :
  (forall s d r, bytes_ok (fst (fin s d r))) -> xh_1stream fin src n = Some l -> bytes_ok l.
Proof.
  intros Hf H. unfold xh_1stream in H. destruct (xb_init src) as [d |]; [| discriminate].
  pose proof (Hf src d n) as Hl. destruct (fin src d n) as [l' d'].
  destruct (xb_end d'); [| discriminate]. inversion H; subst. exact Hl.
Qed.

Lemma lxh_loop4s (dec4: xbit -> list Z * xbit) : (forall d, bytes_ok (fst (dec4 d))) ->
  forall fuel lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4,
  bytes_ok o1 -> bytes_ok o2 -> bytes_ok o3 -> bytes_ok o4 ->
  let '(_, (a1, a2, a3, a4)) := xh_loop4s fuel dec4 lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4 in
  bytes_ok a1 /\ bytes_ok a2 /\ bytes_ok a3 /\ bytes_ok a4.
Proof.
  intros Hd. induction fuel as [|fuel IH]; intros lim4 s1 s2 s3 s4 d1 d2 d3 d4 o1 o2 o3 o4 B1 B2 B3 B4;
    cbn [xh_loop4s]; [auto |].
  destruct (negb _); [auto |].
  pose proof (Hd d1) as C1. destruct (dec4 d1) as [a1 e1].
  pose proof (Hd d2) as C2. destruct (dec4 d2) as [a2 e2].
  pose proof (Hd d3) as C3. destruct (dec4 d3) as [a3 e3].
  pose proof (Hd d4) as C4. destruct (dec4 d4) as [a4 e4]. cbn [fst] in *.
  destruct (xb_reload_fast s1 e1) as [r1 f1]. destruct (xb_reload_fast s2 e2) as [r2 f2].
  destruct (xb_reload_fast s3 e3) as [r3 f3]. destruct (xb_reload_fast s4 e4) as [r4 f4].
  destruct (_ && _); [apply IH | repeat split]; apply lxh_app; assumption.
Qed.

Lemma lxh_4streams (dec4: xbit -> list Z * xbit) (slack: Z) (fin: list Z -> xbit -> Z -> list Z * xbit)
    (src: list Z) (n: Z) (l: list Z) :
  (forall d, bytes_ok (fst (dec4 d))) -> (forall s d r, bytes_ok (fst (fin s d r))) ->
  xh_4streams dec4 slack fin src n = Some l -> bytes_ok l.
Proof.
  intros Hd Hf H. unfold xh_4streams in H.
  destruct (Zlength src <? 10); [discriminate |]. destruct (n <? 6); [discriminate |].
  destruct (xh_split4 src) as [[[[s1 s2] s3] s4] |]; [| discriminate].
  destruct (n <? 3 * ((n + 3) / 4)); [discriminate |].
  destruct (xb_init s1) as [d1 |]; [| discriminate]. destruct (xb_init s2) as [d2 |]; [| discriminate].
  destruct (xb_init s3) as [d3 |]; [| discriminate]. destruct (xb_init s4) as [d4 |]; [| discriminate].
  match type of H with context [let '(_, _) := ?e in _] =>
    assert (Ho: let '(_, (a1, a2, a3, a4)) := e in bytes_ok a1 /\ bytes_ok a2 /\ bytes_ok a3 /\ bytes_ok a4);
    [| destruct e as [[[[e1 e2] e3] e4] [[[o1 o2] o3] o4]]; destruct Ho as (B1 & B2 & B3 & B4)] end.
  { destruct (8 <=? _); [apply lxh_loop4s; auto; constructor | repeat split; constructor]. }
  destruct (_ <? Zlength o1); [discriminate |]. destruct (_ <? Zlength o2); [discriminate |].
  destruct (_ <? Zlength o3); [discriminate |].
  pose proof (Hf s1 e1 ((n + 3) / 4 - Zlength o1)) as T1. destruct (fin s1 e1 _) as [t1 f1].
  pose proof (Hf s2 e2 ((n + 3) / 4 - Zlength o2)) as T2. destruct (fin s2 e2 _) as [t2 f2].
  pose proof (Hf s3 e3 ((n + 3) / 4 - Zlength o3)) as T3. destruct (fin s3 e3 _) as [t3 f3].
  pose proof (Hf s4 e4 (n - 3 * ((n + 3) / 4) - Zlength o4)) as T4. destruct (fin s4 e4 _) as [t4 f4].
  cbn [fst] in *. destruct (_ && _); [| discriminate]. inversion H; subst.
  repeat apply lxh_app; assumption.
Qed.

Lemma lxh_decode (t: xhuf) (single: bool) (cb: list Z) (n: Z) (l: list Z) :
  (xh_x2 t = true -> lxh_x2_ok t) -> (xh_x2 t = false -> lxh_x1_ok t) ->
  x_huf_decode t single cb n = Some l -> bytes_ok l.
Proof.
  intros H2 H1 H. unfold x_huf_decode in H. destruct (xh_x2 t).
  - specialize (H2 eq_refl). destruct single.
    + eapply lxh_1stream; [| exact H]. intros. apply lxh_x2_stream; auto.
    + eapply lxh_4streams; [| | exact H]; intros; [apply lxh_x2_n | apply lxh_x2_stream]; auto.
  - specialize (H1 eq_refl). destruct single.
    + eapply lxh_1stream; [| exact H]. intros. apply lxh_x1_stream; auto.
    + eapply lxh_4streams; [| | exact H]; intros; [apply lxh_x1_n | apply lxh_x1_stream]; auto.
Qed.

Lemma lxh_nth {A} (P: A -> Prop) (l: list A) (d: A) (k: nat) : Forall P l -> P d -> P (nth k l d).
Proof.
  intros Hl Hd. revert k. induction Hl as [| x l Hx Hl IH]; intros k; destruct k; simpl; auto.
Qed.

Lemma lxh_nth_map {A B} (P: A -> Prop) (f: B -> A) (l: list B) (d: A) (k: nat) :
  (forall x, P (f x)) -> P d -> P (nth k (map f l) d).
Proof.
  intros Hf Hd. apply lxh_nth; [| exact Hd]. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [y [<- _]]. apply Hf.
Qed.

(* Huffman-decoded literals are bytes (litExtraBuffer holds bytes) *)
Lemma xl_dec_bytes (x2 single: bool) (ht: huf_table) (cb: list Z) (n: Z) (l: list Z) :
  huf_ok ht -> x_huf_decode (xhuf_of x2 ht) single cb n = Some l -> bytes_ok l.
Proof.
  intros Hok H. eapply lxh_decode; [| | exact H]; intros Hx v;
    unfold xh_cell; destruct x2; cbn [xhuf_of xh_x2 xh_cells] in *; try discriminate.
  - apply (lxh_nth_map (fun c => 0 <= fst (fst c) < 65536)); [| cbn; lia].
    intros k. unfold xh_x2_fields. cbn [fst]. apply Z.mod_pos_bound. lia.
  - apply (lxh_nth_map (fun c => is_byte (fst (fst c)))); [| unfold is_byte; cbn; lia].
    intros k. destruct (hsym ht (xh_x1_log ht) (Z.of_nat k)) as [sy nb] eqn:E. cbn [fst].
    assert (Hs: 0 <= fst (hsym ht (xh_x1_log ht) (Z.of_nat k)) < 256).
    { unfold hsym. apply (lxh_nth (fun c => 0 <= fst c < 256)); [| cbn; lia].
      destruct Hok as (_ & _ & Hf). eapply Forall_impl; [| exact Hf]. intros c Hc. cbn beta in Hc. lia. }
    rewrite E in Hs. exact Hs.
Qed.

(* ===================== ExBlock's memory: stores and copies ===================== *)

(* The cells of the model's memory after a run of stores, read back with xm_rd (as in the proof that
   x_lits_store establishes the sequence loop's invariant, model/ExAgreeBlkStore.v): one store changes one
   cell; a run of stores the run's cells; a copy whose source the copy does not overwrite is the run of
   stores of the bytes it reads. *)

Lemma lxm_nth_upd_eq {A} (l: list A) i x d : (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  revert i. induction l as [|y l IH]; intros i H; simpl in H; [lia|].
  destruct i; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma lxm_nth_upd_neq {A} (l: list A) i n x d : n <> i -> nth n (upd l i x) d = nth n l d.
Proof.
  revert i n. induction l as [|y l IH]; intros i n H; simpl; [reflexivity|].
  destruct i, n; simpl; try reflexivity; [lia|]. apply IH. lia.
Qed.

Lemma lxm_length_upd {A} (l: list A) i x : length (upd l i x) = length l.
Proof. revert i. induction l as [|y l IH]; intros i; simpl; [reflexivity|]. destruct i; simpl; auto. Qed.

Lemma lxm_Zlength_upd {A} (l: list A) i x : Zlength (upd l i x) = Zlength l.
Proof. rewrite !Zlength_correct, lxm_length_upd. reflexivity. Qed.

Lemma lxm_byte_at_Znth (l: list Z) (p: Z) : 0 <= p -> byte_at l p = Znth p l.
Proof. intros H. unfold byte_at, Znth. destruct (Z_lt_dec p 0); [lia | reflexivity]. Qed.

Definition lxm_reqb (a b: xreg) : bool :=
  match a, b with R_dst, R_dst | R_lxb, R_lxb | R_src, R_src => true | _, _ => false end.

Lemma lxm_wr_rd (m: xmem) (r: xreg) (i v: Z) (m': xmem) : xm_wr m r i v = Some m' -> forall src r' p,
  xm_rd src m' r' p = if lxm_reqb r r' && (p =? i) then Some v else xm_rd src m r' p.
Proof.
  intros H src r' p. unfold xm_wr in H.
  destruct (Z.ltb_spec i 0) as [Hi|Hi]; [discriminate|].
  destruct r.
  - inversion H; subst; clear H.
    destruct r'; simpl; [|reflexivity|reflexivity].
    unfold xm_rd. simpl.
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.ltb_spec i 0); [lia|].
      destruct (Z.ltb_spec i (Zlength (xm_dst m))).
      * apply lxm_nth_upd_eq. rewrite Zlength_correct in *. lia.
      * rewrite app_nth2 by (rewrite Zlength_correct in *; lia).
        rewrite app_nth2 by (rewrite repeat_length, Zlength_correct in *; lia).
        rewrite repeat_length. rewrite Zlength_correct in *.
        replace (Z.to_nat i - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat with O by lia.
        reflexivity.
    + destruct (Z.ltb_spec p 0); [reflexivity|].
      destruct (Z.ltb_spec i (Zlength (xm_dst m))).
      * apply lxm_nth_upd_neq. lia.
      * rewrite Zlength_correct in *.
        destruct (Nat.ltb_spec (Z.to_nat p) (length (xm_dst m))).
        -- rewrite app_nth1 by lia. reflexivity.
        -- rewrite app_nth2 by lia. rewrite (nth_overflow (xm_dst m)) by lia.
           destruct (Nat.ltb_spec (Z.to_nat p - length (xm_dst m)) (Z.to_nat (i - Z.of_nat (length (xm_dst m))))).
           ++ rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
           ++ rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
              destruct (Z.to_nat p - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat eqn:E; [lia|].
              simpl. destruct n; reflexivity.
  - destruct (Z.ltb_spec i (Zlength (xm_lxb m))) as [Hl|Hl]; [|discriminate].
    inversion H; subst; clear H.
    destruct r'; simpl; [reflexivity| |reflexivity].
    unfold xm_rd. cbn [xm_lxb]. rewrite lxm_Zlength_upd.
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec i (Zlength (xm_lxb m))); [|lia].
      unfold byte_at. rewrite lxm_nth_upd_eq; [reflexivity|]. rewrite Zlength_correct in *. lia.
    + destruct (Z.ltb_spec p 0); [reflexivity|]. destruct (p <? Zlength (xm_lxb m)); [|reflexivity].
      unfold byte_at. rewrite lxm_nth_upd_neq; [reflexivity|]. lia.
  - discriminate.
Qed.

Lemma lxm_wr_lxb_len (m: xmem) (r: xreg) (i v: Z) (m': xmem) :
  xm_wr m r i v = Some m' -> Zlength (xm_lxb m') = Zlength (xm_lxb m).
Proof.
  intros H. unfold xm_wr in H. destruct (i <? 0); [discriminate|].
  destruct r; [inversion H; reflexivity| |discriminate].
  destruct (i <? Zlength (xm_lxb m)); [|discriminate]. inversion H; subst. cbn [xm_lxb].
  apply lxm_Zlength_upd.
Qed.

(* where a run of stores may go: dst at any index >= 0, litExtraBuffer within its length *)
Definition lxm_wr_ok (m: xmem) (r: xreg) (i n: Z) : Prop :=
  0 <= i /\ r <> R_src /\ (r = R_lxb -> i + n <= Zlength (xm_lxb m)).

Lemma lxm_wrn_spec (vs: list Z) : forall (m: xmem) (r: xreg) (i: Z), lxm_wr_ok m r i (Zlength vs) ->
  exists m', xm_wrn vs m r i = Some m' /\ Zlength (xm_lxb m') = Zlength (xm_lxb m) /\
  forall src r' p, xm_rd src m' r' p =
    if lxm_reqb r r' && ((i <=? p) && (p <? i + Zlength vs)) then Some (byte_at vs (p - i)) else xm_rd src m r' p.
Proof.
  induction vs as [|v vs IH]; intros m r i Hok.
  - exists m. split; [reflexivity|]. split; [reflexivity|]. intros src r' p.
    rewrite Zlength_nil. destruct (lxm_reqb r r'); simpl; [|reflexivity].
    destruct (Z.leb_spec i p); destruct (Z.ltb_spec p (i + 0)); simpl; try reflexivity; lia.
  - destruct Hok as [Hi [Hs Hl]]. rewrite Zlength_cons in Hl.
    assert (Hw: exists m1, xm_wr m r i v = Some m1).
    { unfold xm_wr. destruct (Z.ltb_spec i 0); [lia|].
      destruct r; [eauto| |congruence].
      destruct (Z.ltb_spec i (Zlength (xm_lxb m))); [eauto|]. specialize (Hl eq_refl).
      pose proof (Zlength_nonneg vs). lia. }
    destruct Hw as [m1 Hw].
    pose proof (lxm_wr_rd _ _ _ _ _ Hw) as Hr1. pose proof (lxm_wr_lxb_len _ _ _ _ _ Hw) as Hl1.
    destruct (IH m1 r (i + 1)) as [m' [Hm' [Hl' Hr']]].
    { split; [lia|]. split; [exact Hs|]. intros ->. rewrite Hl1. specialize (Hl eq_refl). lia. }
    exists m'. simpl. rewrite Hw. split; [exact Hm'|]. split; [congruence|].
    intros src r' p. rewrite Hr', Hr1. rewrite Zlength_cons.
    destruct (lxm_reqb r r'); simpl; [|reflexivity].
    destruct (Z.eqb_spec p i) as [->|Hne].
    + destruct (Z.leb_spec (i + 1) i); [lia|]. simpl.
      destruct (Z.leb_spec i i); [|lia].
      destruct (Z.ltb_spec i (i + Z.succ (Zlength vs))); [|pose proof (Zlength_nonneg vs); lia].
      simpl. replace (i - i) with 0 by lia. reflexivity.
    + destruct (Z.leb_spec (i + 1) p); destruct (Z.ltb_spec p (i + 1 + Zlength vs));
      destruct (Z.leb_spec i p); destruct (Z.ltb_spec p (i + Z.succ (Zlength vs))); simpl; try lia; try reflexivity.
      unfold byte_at. replace (Z.to_nat (p - i)) with (S (Z.to_nat (p - (i + 1)))) by lia. reflexivity.
Qed.

(* reading k defined cells *)
Lemma lxm_rdn_eq (src l: list Z) : forall (m: xmem) (r: xreg) (s: Z),
  (forall j, 0 <= j < Zlength l -> xm_rd src m r (s + j) = Some (byte_at l j)) ->
  xm_rdn src (length l) m r s = Some l.
Proof.
  induction l as [|v l IH]; intros m r s H; [reflexivity|].
  simpl. rewrite (IH m r (s + 1)).
  - specialize (H 0). rewrite Z.add_0_r in H.
    rewrite H by (rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia). reflexivity.
  - intros j Hj. specialize (H (j + 1)). rewrite Zlength_cons in H.
    replace (s + 1 + j) with (s + (j + 1)) by lia. rewrite H by lia.
    unfold byte_at. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

(* a move is the stores of the bytes it reads *)
Lemma lxm_move_eq (src l: list Z) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z) :
  (forall j, 0 <= j < Zlength l -> xm_rd src m rs (s + j) = Some (byte_at l j)) ->
  xm_move src (length l) m rd d rs s = xm_wrn l m rd d.
Proof. intros. unfold xm_move. rewrite lxm_rdn_eq by assumption. reflexivity. Qed.

(* a forward copy between two regions is the stores of the bytes it reads *)
Lemma lxm_fwd_eq (src l: list Z) : forall (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (s: Z), rd <> rs ->
  (forall j, 0 <= j < Zlength l -> xm_rd src m rs (s + j) = Some (byte_at l j)) ->
  xm_fwd src (length l) m rd d rs s = xm_wrn l m rd d.
Proof.
  induction l as [|v l IH]; intros m rd d rs s Hne H; [reflexivity|].
  simpl. pose proof (H 0) as H0. rewrite Z.add_0_r in H0.
  rewrite H0 by (rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia).
  unfold byte_at at 1. simpl.
  destruct (xm_wr m rd d v) as [m1|] eqn:Hw; [|reflexivity].
  apply IH; [exact Hne|]. intros j Hj.
  rewrite (lxm_wr_rd _ _ _ _ _ Hw). replace (lxm_reqb rd rs) with false by (destruct rd, rs; cbn; congruence). simpl.
  specialize (H (j + 1)). rewrite Zlength_cons in H.
  replace (s + 1 + j) with (s + (j + 1)) by lia. rewrite H by lia.
  unfold byte_at. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. reflexivity.
Qed.

(* stores into dst leave litExtraBuffer as it is, stores into litExtraBuffer leave dst *)
Lemma lxm_wrn_dst_lxb (vs: list Z) : forall (m m': xmem) (i: Z),
  xm_wrn vs m R_dst i = Some m' -> xm_lxb m' = xm_lxb m.
Proof.
  induction vs as [|v vs IH]; intros m m' i H; simpl in H; [inversion H; reflexivity|].
  unfold xm_wr in H. destruct (i <? 0); [discriminate|]. apply IH in H. exact H.
Qed.

Lemma lxm_wrn_lxb_dst (vs: list Z) : forall (m m': xmem) (i: Z),
  xm_wrn vs m R_lxb i = Some m' -> xm_dst m' = xm_dst m.
Proof.
  induction vs as [|v vs IH]; intros m m' i H; simpl in H; [inversion H; reflexivity|].
  unfold xm_wr in H. destruct (i <? 0); [discriminate|]. destruct (i <? Zlength (xm_lxb m)); [|discriminate].
  apply IH in H. exact H.
Qed.

(* the cells of dst, read *)
Lemma lxm_rd_dst (src: list Z) (m: xmem) (p: Z) : 0 <= p -> xm_rd src m R_dst p = nth (Z.to_nat p) (xm_dst m) None.
Proof. intros H. unfold xm_rd. destruct (Z.ltb_spec p 0); [lia | reflexivity]. Qed.

(* the array c with v stored from k *)
Lemma lxm_cwr_len (c v: list val) (k: Z) : 0 <= k -> k + Zlength v <= Zlength c -> Zlength (cwr c k v) = Zlength c.
Proof. intros. unfold cwr. list_solve. Qed.

Lemma lxm_cwr_in (c v: list val) (k x: Z) :
  0 <= k -> k + Zlength v <= Zlength c -> k <= x < k + Zlength v -> Znth x (cwr c k v) = Znth (x - k) v.
Proof. intros. unfold cwr. list_solve. Qed.

Lemma lxm_cwr_out (c v: list val) (k x: Z) :
  0 <= k -> k + Zlength v <= Zlength c -> 0 <= x < Zlength c -> ~ (k <= x < k + Zlength v) ->
  Znth x (cwr c k v) = Znth x c.
Proof. intros. unfold cwr. list_solve. Qed.

(* the model's region on the output array at rb *)
Lemma lxm_rel_init (oc: list val) (rb: Z) (mem: list Z) :
  0 <= rb -> rb + Zlength mem <= Zlength oc -> sublist rb (rb + Zlength mem) oc = zbytes mem ->
  dst_rel oc rb (map Some mem).
Proof.
  intros H0 H1 H2 j z Hj Hn.
  destruct (Nat.ltb_spec (Z.to_nat j) (length mem)) as [Hl | Hl];
    [| rewrite nth_overflow in Hn by (rewrite length_map; lia); discriminate].
  rewrite (nth_indep _ None (Some 0)) in Hn by (rewrite length_map; lia).
  rewrite map_nth in Hn. inversion Hn; subst z.
  rewrite Zlength_correct in H1, H2.
  assert (E: Znth j (sublist rb (rb + Z.of_nat (length mem)) oc) = Znth (j + rb) oc) by (apply Znth_sublist; lia).
  rewrite H2, Znth_map in E by (rewrite Zlength_correct; lia). rewrite Z.add_comm, <- E.
  rewrite <- lxm_byte_at_Znth by lia. unfold byte_at. reflexivity.
Qed.

(* stores into the model's region from K are the C's stores into the array from rb + K *)
Lemma lxm_rel_wrn (oc: list val) (rb K: Z) (vs: list Z) (m m': xmem) :
  dst_rel oc rb (xm_dst m) -> 0 <= rb -> 0 <= K -> rb + K + Zlength vs <= Zlength oc ->
  (forall p, 0 <= p -> nth (Z.to_nat p) (xm_dst m') None =
     if (K <=? p) && (p <? K + Zlength vs) then Some (byte_at vs (p - K)) else nth (Z.to_nat p) (xm_dst m) None) ->
  dst_rel (cwr oc (rb + K) (zbytes vs)) rb (xm_dst m').
Proof.
  intros Hr H0 HK Hn Hc j z Hj Hz. rewrite Hc in Hz by lia.
  destruct (Z.leb_spec K j); destruct (Z.ltb_spec j (K + Zlength vs)); simpl in Hz.
  - inversion Hz; subst z. rewrite lxm_cwr_in by (rewrite ?Zlength_map; lia).
    rewrite Znth_map by lia. rewrite lxm_byte_at_Znth by lia. f_equal. f_equal. f_equal. lia.
  - apply Hr in Hz; [| lia].
    assert (rb + j < Zlength oc).
    { destruct (Z_lt_le_dec (rb + j) (Zlength oc)); [auto |]. rewrite Znth_overflow in Hz by lia. discriminate. }
    rewrite lxm_cwr_out by (rewrite ?Zlength_map; lia). exact Hz.
  - apply Hr in Hz; [| lia].
    assert (rb + j < Zlength oc).
    { destruct (Z_lt_le_dec (rb + j) (Zlength oc)); [auto |]. rewrite Znth_overflow in Hz by lia. discriminate. }
    rewrite lxm_cwr_out by (rewrite ?Zlength_map; lia). exact Hz.
  - apply Hr in Hz; [| lia].
    assert (rb + j < Zlength oc).
    { destruct (Z_lt_le_dec (rb + j) (Zlength oc)); [auto |]. rewrite Znth_overflow in Hz by lia. discriminate. }
    rewrite lxm_cwr_out by (rewrite ?Zlength_map; lia). exact Hz.
Qed.

(* a run of stores into dst: defined, litExtraBuffer unchanged, the array's cells follow *)
Lemma lxm_dst_wrn (oc: list val) (rb K K': Z) (vs: list Z) (m: xmem) :
  K' = rb + K -> dst_rel oc rb (xm_dst m) -> 0 <= rb -> 0 <= K -> rb + K + Zlength vs <= Zlength oc ->
  exists m', xm_wrn vs m R_dst K = Some m' /\ xm_lxb m' = xm_lxb m /\
    dst_rel (cwr oc K' (zbytes vs)) rb (xm_dst m') /\
    forall src p, xm_rd src m' R_dst p =
      if (K <=? p) && (p <? K + Zlength vs) then Some (byte_at vs (p - K)) else xm_rd src m R_dst p.
Proof.
  intros -> Hr H0 HK Hn.
  destruct (lxm_wrn_spec vs m R_dst K) as [m' [Hw [_ Hc]]].
  { split; [lia | split; [discriminate | discriminate]]. }
  exists m'. split; [exact Hw |]. split; [eapply lxm_wrn_dst_lxb; eauto |]. split.
  - apply (lxm_rel_wrn oc rb K vs m m'); auto. intros p Hp.
    specialize (Hc nil R_dst p). rewrite !lxm_rd_dst in Hc by lia. exact Hc.
  - intros src p. apply Hc.
Qed.

(* two lists of bytes are equal when their cells are *)
Lemma lxm_list_ext (a b: list Z) :
  Zlength a = Zlength b -> (forall p, 0 <= p < Zlength a -> byte_at a p = byte_at b p) -> a = b.
Proof.
  intros Hl Hc. apply Znth_eq_ext; [exact Hl |]. intros p Hp.
  rewrite <- !lxm_byte_at_Znth by lia. apply Hc. exact Hp.
Qed.

(* a run of stores into litExtraBuffer within its length: dst unchanged, the bytes replaced *)
Lemma lxm_lxb_wrn (vs: list Z) (m: xmem) (i: Z) :
  0 <= i -> i + Zlength vs <= Zlength (xm_lxb m) ->
  exists m', xm_wrn vs m R_lxb i = Some m' /\ xm_dst m' = xm_dst m /\
    xm_lxb m' = sublist 0 i (xm_lxb m) ++ vs ++ sublist (i + Zlength vs) (Zlength (xm_lxb m)) (xm_lxb m).
Proof.
  intros H0 Hn.
  destruct (lxm_wrn_spec vs m R_lxb i) as [m' [Hw [Hl Hc]]].
  { split; [lia | split; [discriminate | intros _; lia]]. }
  exists m'. split; [exact Hw |]. split; [eapply lxm_wrn_lxb_dst; eauto |].
  pose proof (Zlength_nonneg vs).
  apply lxm_list_ext; [rewrite Hl; list_solve |]. intros p Hp.
  specialize (Hc nil R_lxb p). unfold xm_rd in Hc. rewrite Hl in Hc.
  destruct (Z.ltb_spec p 0); [lia |]. destruct (Z.ltb_spec p (Zlength (xm_lxb m))); [| lia].
  cbn [lxm_reqb andb] in Hc.
  destruct (Z.leb_spec i p); destruct (Z.ltb_spec p (i + Zlength vs)); simpl in Hc; inversion Hc as [Hc'];
    rewrite Hc'; rewrite !lxm_byte_at_Znth by lia; list_solve.
Qed.

(* ===================== the stores of each arm ===================== *)

(* ---------- ZSTD_allocateLiteralsBuffer's choice in the model and in the C ---------- *)

Lemma lx_zrep {A} (x: A) (n: nat) : Zlength (repeat x n) = Z.of_nat n.
Proof. rewrite Zlength_correct, repeat_length. reflexivity. Qed.

Lemma lx_gtb_f (a b: Z) : a <= b -> (a >? b) = false.
Proof. intros. rewrite Z.gtb_ltb. apply Z.ltb_ge. lia. Qed.

Lemma lx_ltb_f (a b: Z) : b <= a -> (a <? b) = false.
Proof. intros. apply Z.ltb_ge. lia. Qed.

Lemma lx_loc_dst (streaming cap bsm n: Z) : (streaming = 0 \/ streaming = 1) ->
  alloc_loc streaming cap bsm n = LOC_IN_DST -> x_alloc_loc cap n bsm (streaming =? 1) = XL_in_dst.
Proof.
  intros Hs H. destruct (lit_alloc_cases streaming cap bsm n) as [(_ & -> & Hc) | [(Hl & _) | (Hl & _)]];
    [| rewrite Hl in H; discriminate | rewrite Hl in H; discriminate].
  unfold x_alloc_loc, XWILDCOPY. cbn [Z.eqb negb andb]. rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _) Hc). reflexivity.
Qed.

Lemma lx_loc_extra (streaming cap bsm n: Z) : (streaming = 0 \/ streaming = 1) ->
  alloc_loc streaming cap bsm n = LOC_NOT_IN_DST -> x_alloc_loc cap n bsm (streaming =? 1) = XL_extra.
Proof.
  intros Hs H. unfold alloc_loc in H. unfold x_alloc_loc, XWILDCOPY, XLITEXTRA.
  unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE, LOC_IN_DST, LOC_NOT_IN_DST in *.
  destruct Hs as [-> | ->]; cbn [Z.eqb negb andb Pos.eqb] in *; rewrite ?Z.gtb_ltb.
  - destruct (bsm + 32 + n + 32 <? cap); [discriminate |].
    destruct (n <=? 65536); [reflexivity | discriminate].
  - destruct (n <=? 65536); [reflexivity | discriminate].
Qed.

Lemma lx_loc_split (streaming cap bsm n: Z) : (streaming = 0 \/ streaming = 1) ->
  alloc_loc streaming cap bsm n = LOC_SPLIT -> x_alloc_loc cap n bsm (streaming =? 1) = XL_split.
Proof.
  intros Hs H. unfold alloc_loc in H. unfold x_alloc_loc, XWILDCOPY, XLITEXTRA.
  unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE, LOC_IN_DST, LOC_NOT_IN_DST, LOC_SPLIT in *.
  destruct Hs as [-> | ->]; cbn [Z.eqb negb andb Pos.eqb] in *; rewrite ?Z.gtb_ltb.
  - destruct (bsm + 32 + n + 32 <? cap); [discriminate |].
    destruct (n <=? 65536); [discriminate | reflexivity].
  - destruct (n <=? 65536); [discriminate | reflexivity].
Qed.

Lemma lx_out_dst (oc: list val) (streaming cap bsm n d ews split: Z) :
  alloc_loc streaming cap bsm n = LOC_IN_DST ->
  alloc_out oc streaming cap bsm n d ews split = cwr oc (d + bsm + WILDCOPY_OVERLENGTH + n) (zbytes (repeat 0 32)).
Proof. intros H. unfold alloc_out, alloc_slack. rewrite H. reflexivity. Qed.

Lemma lx_out_extra (oc: list val) (streaming cap bsm n d ews split: Z) :
  alloc_loc streaming cap bsm n = LOC_NOT_IN_DST -> alloc_out oc streaming cap bsm n d ews split = oc.
Proof. intros H. unfold alloc_out, alloc_slack. rewrite H. reflexivity. Qed.

Lemma lx_out_split1 (oc: list val) (streaming cap bsm n d ews: Z) :
  alloc_loc streaming cap bsm n = LOC_SPLIT ->
  alloc_out oc streaming cap bsm n d ews 1 = cwr oc (d + ews - WILDCOPY_OVERLENGTH) (zbytes (repeat 0 32)).
Proof. intros H. unfold alloc_out, alloc_slack. rewrite H. reflexivity. Qed.

Lemma lx_out_split0 (oc: list val) (streaming cap bsm n d ews: Z) :
  alloc_loc streaming cap bsm n = LOC_SPLIT -> alloc_out oc streaming cap bsm n d ews 0 = oc.
Proof. intros H. unfold alloc_out, alloc_slack. rewrite H. reflexivity. Qed.

(* the model reads the block's bytes [a, a + |l|) as l *)
Lemma lx_rd_src (s l: list Z) (m: xmem) (a: Z) :
  0 <= a -> a + Zlength l <= Zlength s -> (forall j, 0 <= j < Zlength l -> Znth (a + j) s = Znth j l) ->
  forall j, 0 <= j < Zlength l -> xm_rd s m R_src (a + j) = Some (byte_at l j).
Proof.
  intros Ha Hl Hc j Hj. unfold xm_rd.
  destruct (Z.ltb_spec (a + j) 0); [lia |]. destruct (Z.ltb_spec (a + j) (Zlength s)); [| lia].
  rewrite !lxm_byte_at_Znth by lia. rewrite Hc by lia. reflexivity.
Qed.

(* a copy of the bytes l from the block into a region *)
Lemma lx_fwd_src (s l: list Z) (m: xmem) (rd: xreg) (d a: Z) (k: Z) :
  rd <> R_src -> k = Zlength l -> 0 <= a -> a + Zlength l <= Zlength s ->
  (forall j, 0 <= j < Zlength l -> Znth (a + j) s = Znth j l) ->
  xm_fwd s (Z.to_nat k) m rd d R_src a = xm_wrn l m rd d.
Proof.
  intros Hr Hk Ha Hl Hc. subst k. rewrite Zlength_correct, Nat2Z.id.
  apply lxm_fwd_eq; [exact Hr |]. apply lx_rd_src; assumption.
Qed.

(* a copy / a move whose source cells hold l are the stores of l *)
Lemma lx_fwd_gen (s l: list Z) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (a k: Z) :
  rd <> rs -> k = Zlength l ->
  (forall j, 0 <= j < Zlength l -> xm_rd s m rs (a + j) = Some (byte_at l j)) ->
  xm_fwd s (Z.to_nat k) m rd d rs a = xm_wrn l m rd d.
Proof. intros Hr -> Hc. rewrite Zlength_correct, Nat2Z.id. apply lxm_fwd_eq; assumption. Qed.

Lemma lx_move_gen (s l: list Z) (m: xmem) (rd: xreg) (d: Z) (rs: xreg) (a k: Z) :
  k = Zlength l ->
  (forall j, 0 <= j < Zlength l -> xm_rd s m rs (a + j) = Some (byte_at l j)) ->
  xm_move s (Z.to_nat k) m rd d rs a = xm_wrn l m rd d.
Proof. intros -> Hc. rewrite Zlength_correct, Nat2Z.id. apply lxm_move_eq; assumption. Qed.

(* reads of dst depend only on dst *)
Lemma lx_rd_dst_eq (s: list Z) (m m': xmem) (p: Z) : xm_dst m = xm_dst m' -> xm_rd s m R_dst p = xm_rd s m' R_dst p.
Proof. intros E. unfold xm_rd. rewrite E. reflexivity. Qed.

Lemma lx_le_field_nonneg (s: list Z) (k: Z) : bytes_ok s -> 0 <= le_field s 0 k.
Proof.
  intros Hb. unfold le_field, slice. simpl skipn.
  apply lit_le_value_range. unfold bytes_ok in *. apply Forall_firstn. exact Hb.
Qed.

Lemma lx_rle_range (s: list Z) : bytes_ok s -> 1 <= rle_lh s <= 3 /\ 0 <= rle_ls s.
Proof.
  intros Hb. pose proof (lit_byte_range s 0 Hb).
  unfold rle_lh, rle_ls. destruct (rle_lhl s =? 1); [| destruct (rle_lhl s =? 3)]; split; try lia;
    apply Z.shiftr_nonneg; try apply lx_le_field_nonneg; auto; lia.
Qed.

(* ---------- tactics for the stores of the arms ---------- *)

Ltac lxl := unfold x_split_L0, LITEXTRA_N, XWILDCOPY, WILDCOPY_OVERLENGTH, XLITEXTRA, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; lia.

(* the lengths of the lists the arms store *)
Ltac lx_len :=
  repeat (rewrite lxm_cwr_len by (rewrite ?Zlength_map, ?lx_zrep, ?Zlength_sublist by lxl; lxl));
  rewrite ?Zlength_map, ?lx_zrep, ?Zlength_sublist by lxl; lxl.

(* the first run of stores into dst in the goal, the C's stores into the array OC from K' *)
Ltac lx_dst RB OC K' m1 Hl1 Hr1 Hc1 :=
  match goal with |- context [xm_wrn ?vs ?m R_dst ?K] =>
    let Hw := fresh "Hw" in
    destruct (lxm_dst_wrn OC RB K K' vs m) as (m1 & Hw & Hl1 & Hr1 & Hc1);
    [lxl | assumption | lxl | lxl | lx_len | rewrite Hw; clear Hw]
  end.

(* the first run of stores into litExtraBuffer in the goal *)
Ltac lx_lxb m1 Hd1 Hx1 :=
  match goal with |- context [xm_wrn ?vs ?m R_lxb ?i] =>
    let Hw := fresh "Hw" in
    destruct (lxm_lxb_wrn vs m i) as (m1 & Hw & Hd1 & Hx1); [lxl | | rewrite Hw; clear Hw]
  end.

(* the first copy from the block in the goal, as the stores of l *)
Ltac lx_src l :=
  match goal with |- context [xm_fwd ?s (Z.to_nat ?k) ?m ?rd ?d R_src ?a] =>
    rewrite (lx_fwd_src s l m rd d a k); [| discriminate | | lxl | | ]
  end.

(* set_basic, the literals referenced in place (lhSize + litSize + 32 <= srcSize): only the slack zeroed by
   ZSTD_allocateLiteralsBuffer changes *)
Lemma lx_raw_ref (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming lh ls: Z) :
  lx_hyps o i bsm streaming lxb ->
  Z.land (byte_at (iw_s i) 0) 3 = 0 -> 2 <= Zlength (iw_s i) ->
  (Z.land (Z.shiftr (byte_at (iw_s i) 0) 2) 3 = 3 -> 3 <= Zlength (iw_s i)) -> lit_rawhdr (iw_s i) = (lh, ls) ->
  ls <= bsm -> ls <= Z.min bsm (oa_cap o) -> lh + ls + WILDCOPY_OVERLENGTH <= Zlength (iw_s i) ->
  lits_exact hx lxb o i bsm streaming (lh + ls)
    (alloc_out (oa_c o) streaming (oa_cap o) bsm ls (oa_d o) (Z.min bsm (oa_cap o)) 1)
    (LIn (iw_off i + lh)) (slice (iw_s i) lh ls) hx lxb.
Proof.
  intros (Ho & Hi & Hs & Hbsm & Hbl & Hxl) Ht H2 H3 Hh Hls Hlse Hin rb mem Hrb Hm Hsub. cbv zeta.
  destruct Ho as (_ & HN & _ & Hd & Hcap & Hdc). destruct Hi as (_ & _ & _ & _ & _ & _ & Hb & _).
  pose proof (lit_rawhdr_range _ _ _ Hb H2 H3 Hh) as (Hlh1 & Hlh2 & Hls0).
  rewrite (xl_raw hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) lh ls Ht H2 H3 Hh).
  rewrite (lx_gtb_f ls bsm), (lx_ltb_f (Z.min bsm (oa_cap o)) ls), (lx_gtb_f (lh + ls) (Zlength (iw_s i))) by lxl.
  assert (R0: dst_rel (oa_c o) rb (map Some mem)) by (apply lxm_rel_init; auto; lxl).
  unfold x_lits_store. cbv zeta. rewrite (lit_slice_len (iw_s i) lh ls) by lxl. rewrite Ht.
  replace (lh + ls - ls) with lh by lia.
  rewrite (proj2 (Z.leb_le (lh + ls + XWILDCOPY) (Zlength (iw_s i)))) by lxl.
  destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(Hl & _ & Hc) | [(Hl & Hsm) | (Hl & Hbig)]].
  - rewrite (lx_loc_dst _ _ _ _ Hs Hl). rewrite lx_out_dst by exact Hl.
    cbn - [repeat xm_wrn Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + ls) m1 Hl1 Hr1 Hc1.
    cbn [litloc_rel xm_lxb] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr1 _))))));
      [apply lit_not_err; lxl | congruence | repeat split; lxl].
  - rewrite (lx_loc_extra _ _ _ _ Hs Hl). rewrite lx_out_extra by exact Hl.
    cbn - [repeat xm_wrn Z.to_nat cwr]. cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj R0 _))))));
      [apply lit_not_err; lxl | repeat split; lxl].
  - rewrite (lx_loc_split _ _ _ _ Hs Hl). rewrite lx_out_split1 by exact Hl.
    cbn - [repeat xm_wrn Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - WILDCOPY_OVERLENGTH) m1 Hl1 Hr1 Hc1.
    cbn [litloc_rel xm_lxb] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr1 _))))));
      [apply lit_not_err; lxl | congruence | repeat split; lxl].
Qed.

(* set_basic, the literals copied (srcSize < lhSize + litSize + 32), by the place ZSTD_allocateLiteralsBuffer
   chose: in dst after the block's room, in litExtraBuffer, split (the last 65536 in litExtraBuffer) *)
Lemma lx_raw_copy (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming lh ls: Z) :
  lx_hyps o i bsm streaming lxb ->
  Z.land (byte_at (iw_s i) 0) 3 = 0 -> 2 <= Zlength (iw_s i) ->
  (Z.land (Z.shiftr (byte_at (iw_s i) 0) 2) 3 = 3 -> 3 <= Zlength (iw_s i)) -> lit_rawhdr (iw_s i) = (lh, ls) ->
  ls <= bsm -> ls <= Z.min bsm (oa_cap o) -> lh + ls <= Zlength (iw_s i) ->
  Zlength (iw_s i) < lh + ls + WILDCOPY_OVERLENGTH ->
  (alloc_loc streaming (oa_cap o) bsm ls = LOC_IN_DST ->
   lits_exact hx lxb o i bsm streaming (lh + ls)
     (cwr (alloc_out (oa_c o) streaming (oa_cap o) bsm ls (oa_d o) (Z.min bsm (oa_cap o)) 1)
          (oa_d o + bsm + WILDCOPY_OVERLENGTH) (zbytes (slice (iw_s i) lh ls)))
     (LDst (oa_d o + bsm + WILDCOPY_OVERLENGTH)) (slice (iw_s i) lh ls) hx lxb) /\
  (alloc_loc streaming (oa_cap o) bsm ls = LOC_NOT_IN_DST ->
   lits_exact hx lxb o i bsm streaming (lh + ls) (oa_c o) LExtra (slice (iw_s i) lh ls) hx
     (slice (iw_s i) lh ls ++ sublist ls LITEXTRA_N lxb)) /\
  (alloc_loc streaming (oa_cap o) bsm ls = LOC_SPLIT ->
   lits_exact hx lxb o i bsm streaming (lh + ls)
     (cwr (alloc_out (oa_c o) streaming (oa_cap o) bsm ls (oa_d o) (Z.min bsm (oa_cap o)) 1)
          (oa_d o + Z.min bsm (oa_cap o) - ls + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH)
          (zbytes (sublist 0 (ls - LITBUFFEREXTRASIZE) (slice (iw_s i) lh ls))))
     (LSplit (oa_d o + Z.min bsm (oa_cap o) - ls + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH))
     (slice (iw_s i) lh ls) hx
     (sublist (ls - LITBUFFEREXTRASIZE) ls (slice (iw_s i) lh ls) ++ sublist LITBUFFEREXTRASIZE LITEXTRA_N lxb)).
Proof.
  intros (Ho & Hi & Hs & Hbsm & Hbl & Hxl) Ht H2 H3 Hh Hls Hlse Hin Hout.
  destruct Ho as (_ & HN & _ & Hd & Hcap & Hdc). destruct Hi as (_ & _ & _ & _ & _ & _ & Hb & _).
  pose proof (lit_rawhdr_range _ _ _ Hb H2 H3 Hh) as (Hlh1 & Hlh2 & Hls0).
  assert (Hsl: Zlength (slice (iw_s i) lh ls) = ls) by (apply lit_slice_len; lxl).
  assert (Hsc: forall j, 0 <= j < ls -> Znth (lh + j) (iw_s i) = Znth j (slice (iw_s i) lh ls))
    by (intros j Hj; rewrite lit_slice by lxl; list_solve).
  assert (Pre: forall rb mem, 0 <= rb <= oa_d o -> rb + Zlength mem <= oa_N o ->
    sublist rb (rb + Zlength mem) (oa_c o) = zbytes mem ->
    dst_rel (oa_c o) rb (map Some mem) /\
    xb_lits hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) = Some (slice (iw_s i) lh ls, lh + ls, hx)).
  { intros rb mem Hrb Hm Hsub. split; [apply lxm_rel_init; auto; lxl |].
    rewrite (xl_raw hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) lh ls Ht H2 H3 Hh).
    rewrite (lx_gtb_f ls bsm), (lx_ltb_f (Z.min bsm (oa_cap o)) ls), (lx_gtb_f (lh + ls) (Zlength (iw_s i))) by lxl.
    reflexivity. }
  split; [| split]; intros Hl rb mem Hrb Hm Hsub; cbv zeta;
    destruct (Pre rb mem Hrb Hm Hsub) as [R0 ->];
    unfold x_lits_store; cbv zeta; rewrite Hsl, Ht; replace (lh + ls - ls) with lh by lia;
    rewrite (proj2 (Z.leb_gt (lh + ls + XWILDCOPY) (Zlength (iw_s i)))) by lxl.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(_ & _ & Hc) | [(Hl' & _) | (Hl' & _)]];
      [| rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate].
    rewrite (lx_loc_dst _ _ _ _ Hs Hl). rewrite lx_out_dst by exact Hl.
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + ls) m1 Hl1 Hr1 Hc1.
    lx_src (slice (iw_s i) lh ls); [| lxl | lxl | intros j Hj; apply Hsc; lxl].
    lx_dst rb (cwr (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + ls) (zbytes (repeat 0 32)))
      (oa_d o + bsm + WILDCOPY_OVERLENGTH) m2 Hl2 Hr2 Hc2.
    cbn [litloc_rel xm_lxb] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr2 _))))));
      [apply lit_not_err; lxl | congruence | repeat split; try reflexivity; lxl].
  - rewrite (lx_loc_extra _ _ _ _ Hs Hl).
    destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(Hl' & _) | [(_ & Hsm) | (Hl' & _)]];
      [rewrite Hl' in Hl; discriminate | | rewrite Hl' in Hl; discriminate].
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_src (slice (iw_s i) lh ls); [| lxl | lxl | intros j Hj; apply Hsc; lxl].
    lx_lxb m1 Hd1 Hx1; [cbn [xm_lxb]; lxl |].
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ _))))));
      [apply lit_not_err; lxl | | rewrite Hd1; exact R0 | repeat split; try reflexivity; lxl].
    rewrite Hx1, Hsl, Hxl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(Hl' & _) | [(Hl' & _) | (_ & Hbig)]];
      [rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate |].
    rewrite (lx_loc_split _ _ _ _ Hs Hl). rewrite lx_out_split1 by exact Hl.
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - WILDCOPY_OVERLENGTH) m1 Hl1 Hr1 Hc1.
    lx_src (sublist 0 (ls - LITBUFFEREXTRASIZE) (slice (iw_s i) lh ls));
      [| lx_len | lx_len | intros j Hj; rewrite Zlength_sublist in Hj by lxl; rewrite lit_slice by lxl;
                         unfold LITBUFFEREXTRASIZE in *; list_solve].
    lx_dst rb (cwr (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - WILDCOPY_OVERLENGTH) (zbytes (repeat 0 32)))
      (oa_d o + Z.min bsm (oa_cap o) - ls + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) m2 Hl2 Hr2 Hc2.
    lx_src (sublist (ls - LITBUFFEREXTRASIZE) ls (slice (iw_s i) lh ls));
      [| lx_len | lx_len | intros j Hj; rewrite Zlength_sublist in Hj by lxl; rewrite lit_slice by lxl;
                         unfold LITBUFFEREXTRASIZE, XLITEXTRA in *; list_solve].
    lx_lxb m3 Hd3 Hx3; [rewrite Hl2, Hl1; cbn [xm_lxb]; lx_len |].
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ _))))));
      [apply lit_not_err; lxl | | rewrite Hd3; exact Hr2 | repeat split; try reflexivity; lxl].
    rewrite Hx3, Hl2, Hl1. cbn [xm_lxb]. rewrite Zlength_sublist by lxl. rewrite Hxl.
    unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
Qed.

(* set_rle: the byte v = istart[lhSize] repeated litSize times, by the place *)
Lemma lx_rle (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming: Z) :
  lx_hyps o i bsm streaming lxb ->
  2 <= Zlength (iw_s i) -> Z.land (byte_at (iw_s i) 0) 3 = 1 ->
  ~ (rle_lhl (iw_s i) = 1 /\ Zlength (iw_s i) < 3) -> ~ (rle_lhl (iw_s i) = 3 /\ Zlength (iw_s i) < 4) ->
  rle_ls (iw_s i) <= bsm -> rle_ls (iw_s i) <= Z.min bsm (oa_cap o) ->
  (alloc_loc streaming (oa_cap o) bsm (rle_ls (iw_s i)) = LOC_IN_DST ->
   lits_exact hx lxb o i bsm streaming (rle_lh (iw_s i) + 1)
     (cwr (alloc_out (oa_c o) streaming (oa_cap o) bsm (rle_ls (iw_s i)) (oa_d o) (Z.min bsm (oa_cap o)) 1)
          (oa_d o + bsm + WILDCOPY_OVERLENGTH) (zbytes (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat (rle_ls (iw_s i))))))
     (LDst (oa_d o + bsm + WILDCOPY_OVERLENGTH)) (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat (rle_ls (iw_s i)))) hx lxb) /\
  (alloc_loc streaming (oa_cap o) bsm (rle_ls (iw_s i)) = LOC_NOT_IN_DST ->
   lits_exact hx lxb o i bsm streaming (rle_lh (iw_s i) + 1) (oa_c o) LExtra (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat (rle_ls (iw_s i)))) hx
     (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat (rle_ls (iw_s i))) ++ sublist (rle_ls (iw_s i)) LITEXTRA_N lxb)) /\
  (alloc_loc streaming (oa_cap o) bsm (rle_ls (iw_s i)) = LOC_SPLIT ->
   lits_exact hx lxb o i bsm streaming (rle_lh (iw_s i) + 1)
     (cwr (alloc_out (oa_c o) streaming (oa_cap o) bsm (rle_ls (iw_s i)) (oa_d o) (Z.min bsm (oa_cap o)) 1)
          (oa_d o + Z.min bsm (oa_cap o) - (rle_ls (iw_s i)) + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH)
          (zbytes (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat ((rle_ls (iw_s i)) - LITBUFFEREXTRASIZE)))))
     (LSplit (oa_d o + Z.min bsm (oa_cap o) - (rle_ls (iw_s i)) + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH))
     (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat (rle_ls (iw_s i)))) hx
     (repeat (byte_at (iw_s i) (rle_lh (iw_s i))) (Z.to_nat LITBUFFEREXTRASIZE) ++ sublist LITBUFFEREXTRASIZE LITEXTRA_N lxb)).
Proof.
  intros (Ho & Hi & Hs & Hbsm & Hbl & Hxl) H2 Ht N1 N3 Hls Hlse.
  destruct Ho as (_ & HN & _ & Hd & Hcap & Hdc). destruct Hi as (_ & _ & _ & _ & _ & _ & Hb & _).
  destruct (lx_rle_range (iw_s i) Hb) as [Hlh Hls0].
  set (v := byte_at (iw_s i) (rle_lh (iw_s i))) in *. set (ls := rle_ls (iw_s i)) in *.
  assert (Hrl: forall k, 0 <= k -> Zlength (repeat v (Z.to_nat k)) = k) by (intros k Hk; rewrite lx_zrep; lia).
  assert (Pre: forall rb mem, 0 <= rb <= oa_d o -> rb + Zlength mem <= oa_N o ->
    sublist rb (rb + Zlength mem) (oa_c o) = zbytes mem ->
    dst_rel (oa_c o) rb (map Some mem) /\
    xb_lits hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) =
      Some (repeat v (Z.to_nat ls), rle_lh (iw_s i) + 1, hx)).
  { intros rb mem Hrb Hm Hsub. split; [apply lxm_rel_init; auto; lxl |].
    rewrite (xl_rle hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) H2 Ht). fold ls v.
    replace ((rle_lhl (iw_s i) =? 1) && (Zlength (iw_s i) <? 3)) with false
      by (destruct (Z.eqb_spec (rle_lhl (iw_s i)) 1); destruct (Z.ltb_spec (Zlength (iw_s i)) 3); auto; tauto).
    replace ((rle_lhl (iw_s i) =? 3) && (Zlength (iw_s i) <? 4)) with false
      by (destruct (Z.eqb_spec (rle_lhl (iw_s i)) 3); destruct (Z.ltb_spec (Zlength (iw_s i)) 4); auto; tauto).
    rewrite (lx_gtb_f ls bsm), (lx_ltb_f (Z.min bsm (oa_cap o)) ls) by lxl. reflexivity. }
  split; [| split]; intros Hl rb mem Hrb Hm Hsub; cbv zeta;
    destruct (Pre rb mem Hrb Hm Hsub) as [R0 ->];
    unfold x_lits_store; cbv zeta; rewrite (Hrl ls Hls0), Ht;
    replace (rle_lh (iw_s i) + 1 - 1) with (rle_lh (iw_s i)) by lia; fold v.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(_ & _ & Hc) | [(Hl' & _) | (Hl' & _)]];
      [| rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate].
    rewrite (lx_loc_dst _ _ _ _ Hs Hl). rewrite lx_out_dst by exact Hl.
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + ls) m1 Hl1 Hr1 Hc1.
    lx_dst rb (cwr (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + ls) (zbytes (repeat 0 32)))
      (oa_d o + bsm + WILDCOPY_OVERLENGTH) m2 Hl2 Hr2 Hc2.
    cbn [litloc_rel xm_lxb] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr2 _))))));
      [apply lit_not_err; lxl | congruence | rewrite ?Hrl by lia; repeat split; try reflexivity; lxl].
  - rewrite (lx_loc_extra _ _ _ _ Hs Hl).
    destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(Hl' & _) | [(_ & Hsm) | (Hl' & _)]];
      [rewrite Hl' in Hl; discriminate | | rewrite Hl' in Hl; discriminate].
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_lxb m1 Hd1 Hx1; [cbn [xm_lxb]; rewrite Hrl by lia; lxl |].
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ _))))));
      [apply lit_not_err; lxl | | rewrite Hd1; exact R0 | rewrite ?Hrl by lia; repeat split; try reflexivity; lxl].
    rewrite Hx1, Hrl, Hxl by lia. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm ls) as [(Hl' & _) | [(Hl' & _) | (_ & Hbig)]];
      [rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate |].
    rewrite (lx_loc_split _ _ _ _ Hs Hl). rewrite lx_out_split1 by exact Hl.
    cbn - [repeat xm_wrn xm_fwd Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - WILDCOPY_OVERLENGTH) m1 Hl1 Hr1 Hc1.
    lx_dst rb (cwr (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - WILDCOPY_OVERLENGTH) (zbytes (repeat 0 32)))
      (oa_d o + Z.min bsm (oa_cap o) - ls + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) m2 Hl2 Hr2 Hc2.
    replace (Z.to_nat XLITEXTRA) with (Z.to_nat LITBUFFEREXTRASIZE) by reflexivity.
    set (R := repeat v (Z.to_nat LITBUFFEREXTRASIZE)) in *.
    assert (HR: Zlength R = 65536) by (unfold R; rewrite lx_zrep, Z2Nat.id; reflexivity || lxl).
    lx_lxb m3 Hd3 Hx3; [rewrite Hl2, Hl1; cbn [xm_lxb]; lxl |].
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ _))))));
      [apply lit_not_err; lxl | | rewrite Hd3; exact Hr2 | repeat split; try reflexivity; lxl].
    rewrite Hx3, Hl2, Hl1. cbn [xm_lxb]. rewrite HR, Hxl.
    unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
Qed.

(* set_compressed (e = 2) / set_repeat (e = 3): the n Huffman-decoded literals lits (the model's x_lits_huf)
   written at litBuffer; split: decoded at dst + ews - n, the last 65536 copied to litExtraBuffer, the first
   n - 65536 moved up by 65536 - 32 (patch items 18 and 20: only after a successful decode) *)
Lemma lx_huf (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming e lh n cs: Z) (single: bool)
    (lits: list Z) (t: xhuf) :
  lx_hyps o i bsm streaming lxb ->
  5 <= Zlength (iw_s i) -> Z.land (byte_at (iw_s i) 0) 3 = e -> (e = 2 \/ e = 3) -> (e = 3 -> hx <> None) ->
  lit_hdr (iw_s i) = (lh, n, cs, single) ->
  n <= bsm -> (single = false -> 6 <= n) -> cs + lh <= Zlength (iw_s i) -> n <= Z.min bsm (oa_cap o) ->
  x_lits_huf hx e single (sublist lh (lh + cs) (iw_s i)) n = Some (lits, t) -> Zlength lits = n ->
  (alloc_loc streaming (oa_cap o) bsm n = LOC_IN_DST ->
   lits_exact hx lxb o i bsm streaming (lh + cs)
     (cwr (alloc_out (oa_c o) streaming (oa_cap o) bsm n (oa_d o) (Z.min bsm (oa_cap o)) 0)
          (oa_d o + bsm + WILDCOPY_OVERLENGTH) (zbytes lits))
     (LDst (oa_d o + bsm + WILDCOPY_OVERLENGTH)) lits (Some t) lxb) /\
  (alloc_loc streaming (oa_cap o) bsm n = LOC_NOT_IN_DST ->
   lits_exact hx lxb o i bsm streaming (lh + cs) (oa_c o) LExtra lits (Some t) (lits ++ sublist n LITEXTRA_N lxb)) /\
  (alloc_loc streaming (oa_cap o) bsm n = LOC_SPLIT ->
   lits_exact hx lxb o i bsm streaming (lh + cs)
     (cwr (cwr (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - n) (zbytes lits))
          (oa_d o + Z.min bsm (oa_cap o) - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH)
          (zbytes (sublist 0 (n - LITBUFFEREXTRASIZE) lits)))
     (LSplit (oa_d o + Z.min bsm (oa_cap o) - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH)) lits (Some t)
     (sublist (n - LITBUFFEREXTRASIZE) n lits ++ sublist LITBUFFEREXTRASIZE LITEXTRA_N lxb)).
Proof.
  intros (Ho & Hi & Hs & Hbsm & Hbl & Hxl) H5 Ht He Hx Hh Hn H6 Hcs Hne Hhuf Hln.
  destruct Ho as (_ & HN & _ & Hd & Hcap & Hdc). destruct Hi as (_ & _ & _ & _ & _ & _ & Hb & _).
  destruct (lx_hdr_nonneg _ _ _ _ _ Hb H5 Hh) as [Hlh Hcs0].
  pose proof (Zlength_nonneg lits) as Hn0.
  assert (Pre: forall rb mem, 0 <= rb <= oa_d o -> rb + Zlength mem <= oa_N o ->
    sublist rb (rb + Zlength mem) (oa_c o) = zbytes mem ->
    dst_rel (oa_c o) rb (map Some mem) /\
    xb_lits hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) = Some (lits, lh + cs, Some t)).
  { intros rb mem Hrb Hm Hsub. split; [apply lxm_rel_init; auto; lxl |].
    rewrite (xl_comp hx (iw_s i) bsm (Z.min bsm (oa_cap o)) (streaming =? 1) e lh n cs single Hb H5 Ht He Hx Hh).
    rewrite (lx_gtb_f n bsm), (lx_gtb_f (cs + lh) (Zlength (iw_s i))), (lx_ltb_f (Z.min bsm (oa_cap o)) n) by lxl.
    replace (negb single && (n <? 6)) with false
      by (destruct single; [reflexivity |]; specialize (H6 eq_refl); cbn [negb andb]; symmetry; apply Z.ltb_ge; lia).
    rewrite Hhuf. reflexivity. }
  assert (Ht0: (e =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Ht1: (e =? 1) = false) by (apply Z.eqb_neq; lia).
  assert (Ht2: (e <=? 1) = false) by (apply Z.leb_gt; lia).
  split; [| split]; intros Hl rb mem Hrb Hm Hsub; cbv zeta;
    destruct (Pre rb mem Hrb Hm Hsub) as [R0 ->];
    unfold x_lits_store; cbv zeta; rewrite Hln, Ht, Ht0, Ht1, Ht2.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm n) as [(_ & _ & Hc) | [(Hl' & _) | (Hl' & _)]];
      [| rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate].
    rewrite (lx_loc_dst _ _ _ _ Hs Hl). rewrite lx_out_dst by exact Hl.
    cbn - [repeat xm_wrn xm_fwd xm_move Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + n) m1 Hl1 Hr1 Hc1.
    lx_dst rb (cwr (oa_c o) (oa_d o + bsm + WILDCOPY_OVERLENGTH + n) (zbytes (repeat 0 32)))
      (oa_d o + bsm + WILDCOPY_OVERLENGTH) m2 Hl2 Hr2 Hc2.
    cbn [litloc_rel xm_lxb] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr2 _))))));
      [apply lit_not_err; lxl | congruence | repeat split; try reflexivity; lxl].
  - rewrite (lx_loc_extra _ _ _ _ Hs Hl).
    destruct (lit_alloc_cases streaming (oa_cap o) bsm n) as [(Hl' & _) | [(_ & Hsm) | (Hl' & _)]];
      [rewrite Hl' in Hl; discriminate | | rewrite Hl' in Hl; discriminate].
    cbn - [repeat xm_wrn xm_fwd xm_move Z.to_nat cwr].
    lx_lxb m1 Hd1 Hx1; [cbn [xm_lxb]; lxl |].
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj _ _))))));
      [apply lit_not_err; lxl | | rewrite Hd1; exact R0 | repeat split; try reflexivity; lxl].
    rewrite Hx1, Hln, Hxl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
  - destruct (lit_alloc_cases streaming (oa_cap o) bsm n) as [(Hl' & _) | [(Hl' & _) | (_ & Hbig)]];
      [rewrite Hl' in Hl; discriminate | rewrite Hl' in Hl; discriminate |].
    rewrite (lx_loc_split _ _ _ _ Hs Hl).
    cbn - [repeat xm_wrn xm_fwd xm_move Z.to_nat cwr].
    lx_dst rb (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - n) m1 Hl1 Hr1 Hc1.
    (* the last 65536 literals copied to litExtraBuffer *)
    match goal with |- context [xm_fwd ?s (Z.to_nat ?k) ?m R_lxb 0 R_dst ?a] =>
      rewrite (lx_fwd_gen s (sublist (n - LITBUFFEREXTRASIZE) n lits) m R_lxb 0 R_dst a k);
      [| discriminate | rewrite Zlength_sublist by lxl; lxl |]
    end.
    2:{ intros j Hj. rewrite Zlength_sublist in Hj by lxl. rewrite Hc1.
        match goal with |- context [if ?a && ?b then _ else _] =>
          replace (a && b) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lxl) end.
        f_equal. rewrite !lxm_byte_at_Znth by lxl. rewrite Znth_sublist by lxl. f_equal. lxl. }
    lx_lxb m2 Hd2 Hx2; [rewrite Hl1; cbn [xm_lxb]; rewrite Zlength_sublist by lxl; lxl |].
    (* the first n - 65536 moved up by 65536 - 32 *)
    match goal with |- context [xm_move ?s (Z.to_nat ?k) ?m R_dst ?d R_dst ?a] =>
      rewrite (lx_move_gen s (sublist 0 (n - LITBUFFEREXTRASIZE) lits) m R_dst d R_dst a k);
      [| rewrite Zlength_sublist by lxl; lxl |]
    end.
    2:{ intros j Hj. rewrite Zlength_sublist in Hj by lxl. rewrite (lx_rd_dst_eq _ m2 m1) by exact Hd2. rewrite Hc1.
        match goal with |- context [if ?a && ?b then _ else _] =>
          replace (a && b) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lxl) end.
        f_equal. rewrite !lxm_byte_at_Znth by lxl. rewrite Znth_sublist by lxl. f_equal. lxl. }
    rewrite <- Hd2 in Hr1.
    lx_dst rb (cwr (oa_c o) (oa_d o + Z.min bsm (oa_cap o) - n) (zbytes lits))
      (oa_d o + Z.min bsm (oa_cap o) - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH) m3 Hl3 Hr3 Hc3.
    cbn [litloc_rel xm_lxb xm_dst] in *.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hr3 _))))));
      [apply lit_not_err; lxl | | repeat split; try reflexivity; lxl].
    rewrite Hl3, Hx2, Hl1. cbn [xm_lxb]. rewrite Zlength_sublist by lxl. rewrite Hxl.
    unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. list_solve.
Qed.
