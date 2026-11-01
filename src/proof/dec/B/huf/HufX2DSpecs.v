(* Sub-group X2D (HufX2D.v): the internal specifications of the X2 decoders, the model facts they use, and
   the small contexts their body lemmas are proved in (lifted to G_HUF ++ X2D_imports ++ X2D_specs by
   Layer.body_ok_mono).  Fixed: the X2D body lemmas are proved against these specifications.

   The body lemmas that need the model take `hsym_facts` (the statements of HufMPeek.hsym_peek and
   HufMAlign.hsym_pair) as a hypothesis, so that no body depends on those model proofs; HufX2D.X2D_ok_from
   discharges it with the two lemmas. *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMAlign.
Require Export Zstd.proof.dec.B.huf.HufXBit.
Local Open Scope logic.

Definition t_bitD2 : type := Tstruct ___gp_BIT_DStream_t noattr.

(* ---------- the model facts (statements of HufMPeek.hsym_peek, HufMAlign.hsym_pair) ---------- *)

Definition hsym_peek_stmt : Prop :=
  forall (ht: huf_table) (s: list Z) (L pos: Z),
  0 <= ht_log ht <= L -> L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  hsym ht L (bs_peek (bs_value s) pos L) = nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0).

Definition hsym_pair_stmt : Prop :=
  forall (ht: huf_table) (s: list Z) (L pos v n1: Z),
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok s ->
  v = bs_peek (bs_value s) pos L -> n1 = snd (hsym ht L v) -> 0 <= pos - n1 ->
  n1 + snd (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) <= L ->
  hsym ht L ((v * 2 ^ n1) mod 2 ^ L) = nth (Z.to_nat (bs_peek_s s (pos - n1) (ht_log ht))) (huf_cells ht) (0, 0).

Definition hsym_facts : Prop := hsym_peek_stmt /\ hsym_pair_stmt.

(* ---------- the table ---------- *)

(* the X2 cells c2 of ht at log L (hufdt_x_at true) *)
Definition x2_tab_ok (ht: huf_table) (L: Z) (c2: list (val * (val * val))) : Prop :=
  huf_ok ht /\ ht_log ht <= L <= HUF_TABLELOG_MAX /\ Zlength c2 = 2 ^ L /\
  forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2).

(* One decode with the cell of the L-bit value v: k symbols (1 or 2), the second byte the C writes b2 (the
   second symbol when k = 2, any byte otherwise), nb bits consumed (in [1, L]). *)
Definition x2_step (ht: huf_table) (L v k b2 nb: Z) : Prop :=
  0 <= b2 < 256 /\ 1 <= nb <= L /\
  (let '(s1, n1) := hsym ht L v in
   (k = 1 /\ nb = n1) \/
   (let '(s2, n2) := hsym ht L ((v * 2 ^ n1) mod 2 ^ L) in k = 2 /\ b2 = s2 /\ nb = n1 + n2)).

(* HUF_decodeLastSymbolX2's new position: a 2-symbol cell is skipped only when bitsConsumed < 64 (pos > lo),
   and then clamped to bitsConsumed = 64 (pos = lo) *)
Definition x2_last_pos (pos lo k nb: Z) : Z :=
  if k =? 1 then pos - nb else if pos <=? lo then pos else Z.max lo (pos - nb).

(* ---------- model lemmas ---------- *)

(* the cell of any L-bit value: a symbol (byte) and a code length in [1, ht_log] *)
Lemma hsym_range (ht: huf_table) (L v: Z) :
  huf_ok ht -> ht_log ht <= L -> 0 <= v < 2 ^ L ->
  0 <= fst (hsym ht L v) < 256 /\ 1 <= snd (hsym ht L v) <= ht_log ht.
Proof.
  intros (Hlog & Hlen & Hall) HL Hv. unfold hsym.
  set (i := v / 2 ^ (L - ht_log ht)).
  assert (Hi: 0 <= i < 2 ^ ht_log ht).
  { subst i. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
    apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (L - ht_log ht + ht_log ht) with L by lia. lia. }
  rewrite Forall_forall in Hall. apply Hall. apply nth_In.
  rewrite Zlength_correct in Hlen. lia.
Qed.

(* decoding a + b symbols = a symbols, then b *)
Lemma huf_decode_syms_app (t: huf_table) (V: list Z) (a b: nat) (pos: Z) :
  huf_decode_syms t V (a + b) pos =
  match huf_decode_syms t V a pos with
  | Some (l1, p1) =>
      match huf_decode_syms t V b p1 with Some (l2, p2) => Some (l1 ++ l2, p2) | None => None end
  | None => None
  end.
Proof.
  revert pos. induction a as [|a IH]; intros pos; simpl.
  - destruct (huf_decode_syms t V b pos) as [[l2 p2]|]; reflexivity.
  - destruct (nth _ (huf_cells t) (0, 0)) as [s nb].
    destruct (pos - nb <? 0); [reflexivity|].
    rewrite IH. destruct (huf_decode_syms t V a (pos - nb)) as [[l1 p1]|]; [|reflexivity].
    destruct (huf_decode_syms t V b p1) as [[l2 p2]|]; reflexivity.
Qed.

(* the model's peek of nb bits is an nb-bit value *)
Lemma bs_peek_s_range (s: list Z) (pos nb: Z) : 0 <= nb -> 0 <= bs_peek_s s pos nb < 2 ^ nb.
Proof.
  intros Hnb. unfold bs_peek_s.
  destruct (pos <? 0) eqn:H0; [split; [lia | apply Z.pow_pos_nonneg; lia]|]. apply Z.ltb_ge in H0.
  destruct (pos - nb >=? 0) eqn:H1.
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - rewrite Z.geb_leb, Z.leb_gt in H1.
    pose proof (Z.mod_pos_bound (le_value (slice s 0 5)) (2 ^ pos) ltac:(apply Z.pow_pos_nonneg; lia)).
    assert (E: (2 ^ nb = 2 ^ pos * 2 ^ (- (pos - nb)))%Z) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    rewrite E. pose proof (Z.pow_pos_nonneg 2 (- (pos - nb)) ltac:(lia) ltac:(lia)). nia.
Qed.

(* a model run of m symbols from pos to pe: m symbols, each of 1..ht_log bits *)
Lemma huf_decode_syms_bounds (ht: huf_table) (s: list Z) (m: nat) (pos pe: Z) (l: list Z) :
  huf_ok ht -> 0 <= pos -> huf_decode_syms ht s m pos = Some (l, pe) ->
  Zlength l = Z.of_nat m /\ Forall (fun x => 0 <= x < 256) l /\
  pe + Z.of_nat m <= pos <= pe + ht_log ht * Z.of_nat m /\ 0 <= pe.
Proof.
  intros Hok. revert pos l. induction m as [|m IH]; intros pos l Hpos H.
  - simpl in H. inv H. split; [reflexivity|]. split; [constructor|]. lia.
  - simpl in H.
    pose proof (bs_peek_s_range s pos (ht_log ht) ltac:(destruct Hok; lia)) as Hr.
    destruct Hok as (Hlog & Hlen & Hall).
    assert (Hin: In (nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0)) (huf_cells ht)).
    { apply nth_In. rewrite Zlength_correct in Hlen. lia. }
    rewrite Forall_forall in Hall. specialize (Hall _ Hin).
    destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb] eqn:Hc. simpl in Hall.
    destruct (pos - nb <? 0) eqn:Hneg; [discriminate|]. apply Z.ltb_ge in Hneg.
    destruct (huf_decode_syms ht s m (pos - nb)) as [[l1 p1]|] eqn:Hm; [|discriminate].
    inv H. destruct (IH (pos - nb) l1 ltac:(lia) Hm) as (H1 & H2 & H3 & H4).
    split; [rewrite Zlength_cons; lia|]. split; [constructor; [lia | exact H2]|]. lia.
Qed.

(* the first model symbol is the C cell's first symbol (exact peek) *)
Lemma x2_first (Hf: hsym_facts) (ht: huf_table) (s: list Z) (L pos v: Z) (m: nat) (l: list Z) (pe: Z) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  v = bs_peek (bs_value s) pos L -> huf_decode_syms ht s (S m) pos = Some (l, pe) ->
  exists l', l = fst (hsym ht L v) :: l' /\ 0 <= pos - snd (hsym ht L v) /\
             huf_decode_syms ht s m (pos - snd (hsym ht L v)) = Some (l', pe).
Proof.
  intros Hok HL Hs Hpos Hv H. destruct Hf as [Hpeek _].
  assert (Hc: nth (Z.to_nat (bs_peek_s s pos (ht_log ht))) (huf_cells ht) (0, 0) = hsym ht L v).
  { subst v. symmetry. apply Hpeek; auto; try lia. destruct Hok; lia. }
  simpl in H. rewrite Hc in H.
  destruct (hsym ht L v) as [s1 n1] eqn:Hh. simpl.
  destruct (pos - n1 <? 0) eqn:Hneg; [discriminate|]. apply Z.ltb_ge in Hneg.
  destruct (huf_decode_syms ht s m (pos - n1)) as [[l1 p1]|] eqn:Hm; [|discriminate].
  inv H. exists l1. auto.
Qed.

(* one C decode (x2_step) with an exact peek, k <= m: the k model symbols, and the rest of the run *)
Lemma x2_step_syms (Hf: hsym_facts) (ht: huf_table) (s: list Z) (L pos v k b2 nb: Z) (m: nat)
    (l: list Z) (pe: Z) :
  huf_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> bytes_ok s -> 0 <= pos ->
  v = bs_peek (bs_value s) pos L -> x2_step ht L v k b2 nb -> k <= Z.of_nat m ->
  huf_decode_syms ht s m pos = Some (l, pe) ->
  sublist 0 k l = sublist 0 k [fst (hsym ht L v); b2] /\
  huf_decode_syms ht s (m - Z.to_nat k) (pos - nb) = Some (sublist k (Zlength l) l, pe).
Proof.
  intros Hok HL Hs Hpos Hv Hst Hkm H.
  destruct Hst as (Hb2 & Hnb & Hcase).
  destruct (hsym ht L v) as [s1 n1] eqn:Hh.
  destruct m as [|m].
  { exfalso. simpl in Hkm. destruct Hcase as [[-> _]|Hc2]; [lia|].
    destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)%Z) as [s2 n2]. destruct Hc2 as [-> _]. lia. }
  destruct (x2_first Hf ht s L pos v m l pe Hok HL Hs Hpos Hv H) as (l1 & -> & Hp1 & H1).
  rewrite Hh in Hp1, H1. simpl fst in *; simpl snd in *.
  destruct Hcase as [[-> ->]|Hc2].
  - simpl. rewrite Nat.sub_0_r. rewrite Zlength_cons, sublist_1_cons.
    rewrite Z.sub_1_r, Z.pred_succ. rewrite (sublist_same 0 (Zlength l1) l1) by lia. rewrite Hh.
    split; [|exact H1]. unfold sublist. simpl. reflexivity.
  - destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)%Z) as [s2 n2] eqn:Hh2.
    destruct Hc2 as (-> & -> & ->).
    destruct m as [|m]; [lia|].
    destruct Hf as [Hpeek Hpair].
    assert (Hc: hsym ht L ((v * 2 ^ n1) mod 2 ^ L) =
                nth (Z.to_nat (bs_peek_s s (pos - n1) (ht_log ht))) (huf_cells ht) (0, 0)).
    { apply (Hpair ht s L pos v n1); auto; [rewrite Hh; reflexivity | rewrite Hh2; simpl; lia]. }
    rewrite Hh2 in Hc.
    simpl in H1. rewrite <- Hc in H1.
    destruct (pos - n1 - n2 <? 0) eqn:Hneg; [discriminate|].
    destruct (huf_decode_syms ht s m (pos - n1 - n2)) as [[l2 p2]|] eqn:Hm; [|discriminate].
    inv H1. simpl. replace (m - 0)%nat with m by lia.
    replace (pos - (n1 + n2)) with (pos - n1 - n2) by lia. rewrite Hm.
    rewrite !Zlength_cons. split.
    + rewrite Hh. unfold sublist. simpl. reflexivity.
    + f_equal. f_equal. list_solve.
Qed.

(* the output stays made of bytes when bytes are written into it *)
Lemma byte_cells_splice (oc: list val) (a b: Z) (l: list Z) :
  byte_cells oc -> bytes_ok l -> byte_cells (sublist 0 a oc ++ zbytes l ++ sublist b (Zlength oc) oc).
Proof.
  intros Ho Hl. unfold byte_cells in *. apply Forall_app; split; [|apply Forall_app; split].
  - apply Forall_sublist; exact Ho.
  - unfold bytes_ok in Hl. rewrite Forall_map. eapply Forall_impl; [|exact Hl].
    intros z Hz. exists z. unfold is_byte in Hz. split; [lia | reflexivity].
  - apply Forall_sublist; exact Ho.
Qed.

(* ---------- HUF_decodeSymbolX2(op, D, dt, L) ----------
   On BIT_DStream_rep_g np (np = true: the window-pointer state rep_np of the 4-stream loop).  Peeks L bits (BIT_lookBitsFast: v, exact when the bits are in the container or lo = 0 < pos), copies the
   2 bytes of the cell's sequence to op (the first symbol and b2), skips nb bits, returns k (x2_step).
   Exactly (last PROP; the cells are ExHuf's, c2 = map x2v (xh_cells_x2 ht L)): v is the C's peek on every
   state (ExHuf.xb_look_fast, HufXBit), and (sequence, nbBits, length) of its cell are (first symbol + 256 b2,
   nb, k). *)
Definition HUF_decodeSymbolX2_spec : ident * funspec :=
  DECLARE _HUF_decodeSymbolX2
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       sht: share, dt: val, ht: huf_table, L: Z, c2: list (val * (val * val)),
       sho: share, ob: val, oc: list val, a: Z, np: bool
  PRE [ tptr tvoid, tptr t_bitD2, tptr t_deltx2, tuint ]
    PROP (writable_share sh; readable_share sht; x2_tab_ok ht L c2;
          writable_share sho; 0 <= a; a + 2 <= Zlength oc;
          lo + 64 - (pos - L) <= Int.max_unsigned; c2 = map x2v (xh_cells_x2 ht L))
    PARAMS (offset_val a ob; p; dt; Vint (Int.repr L))
    SEP (BIT_DStream_rep_g np sh gv s start pos lo p; data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc)) oc ob)
  POST [ tuint ]
    EX v: Z, EX k: Z, EX b2: Z, EX nb: Z,
    PROP (0 <= v < 2 ^ L; lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value s) pos L;
          x2_step ht L v k b2 nb;
          v = xb_look_fast (xb_of s pos lo) L /\
          nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, k))
    RETURN (Vint (Int.repr k))
    SEP (BIT_DStream_rep_g np sh gv s start (pos - nb) lo p; data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc))
           (sublist 0 a oc ++ zbytes [fst (hsym ht L v); b2] ++ sublist (a + 2) (Zlength oc) oc) ob).

(* ---------- HUF_decodeLastSymbolX2(op, D, dt, L) ----------
   Copies the first symbol only; returns 1; the new position is x2_last_pos (reads and writes
   D->bitsConsumed directly).  Exactly (last PROP): as HUF_decodeSymbolX2. *)
Definition HUF_decodeLastSymbolX2_spec : ident * funspec :=
  DECLARE _HUF_decodeLastSymbolX2
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       sht: share, dt: val, ht: huf_table, L: Z, c2: list (val * (val * val)),
       sho: share, ob: val, oc: list val, a: Z
  PRE [ tptr tvoid, tptr t_bitD2, tptr t_deltx2, tuint ]
    PROP (writable_share sh; readable_share sht; x2_tab_ok ht L c2;
          writable_share sho; 0 <= a; a + 1 <= Zlength oc;
          lo + 64 - (pos - L) <= Int.max_unsigned; c2 = map x2v (xh_cells_x2 ht L))
    PARAMS (offset_val a ob; p; dt; Vint (Int.repr L))
    SEP (BIT_DStream_rep sh gv s start pos lo p; data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc)) oc ob)
  POST [ tuint ]
    EX v: Z, EX k: Z, EX b2: Z, EX nb: Z,
    PROP (0 <= v < 2 ^ L; lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value s) pos L;
          x2_step ht L v k b2 nb;
          v = xb_look_fast (xb_of s pos lo) L /\
          nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, k))
    RETURN (Vint (Int.repr 1))
    SEP (BIT_DStream_rep sh gv s start (x2_last_pos pos lo k nb) lo p;
         data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc))
           (sublist 0 a oc ++ zbytes [fst (hsym ht L v)] ++ sublist (a + 1) (Zlength oc) oc) ob).

(* ---------- HUF_decodeStreamX2(p, D, pEnd, dt, L) ----------
   Fills the k = pEnd - p bytes at offset a of the output array (any stream state, any bytes: k defined
   bytes l, returns k); bitsConsumed grows by at most 12 per byte.  Model: from a non-overflowed state
   (lo <= pos), if the model decodes exactly k symbols from pos ending at 0, then l are those symbols and
   the stream ends consumed (pos' = 0, window at the bottom: BIT_endOfDStream returns 1).
   Exactly (last PROP; the table is the reader's, L = xh_x2_log ht with ExHuf's cells): from any state, the
   bytes and the new state are ExHuf.xh_x2_stream's, for either C description d of the state
   (HufXBit.xb_rel). *)
Definition HUF_decodeStreamX2_spec : ident * funspec :=
  DECLARE _HUF_decodeStreamX2
  WITH sh: share, bD: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z,
       sht: share, dt: val, ht: huf_table, L: Z, c2: list (val * (val * val)),
       sho: share, ob: val, oc: list val, a: Z, k: Z
  PRE [ tptr tuchar, tptr t_bitD2, tptr tuchar, tptr t_deltx2, tuint ]
    PROP (writable_share sh; readable_share shs; bit_src_ok s start bp buf off;
          readable_share sht; x2_tab_ok ht L c2;
          writable_share sho; 1 <= Zlength oc; 0 <= a; 0 <= k; a + k <= Zlength oc;
          lo + 64 - pos + 12 * k <= Int.max_unsigned; L = xh_x2_log ht; c2 = map x2v (xh_cells_x2 ht L))
    PARAMS (offset_val a ob; bD; offset_val (a + k) ob; dt; Vint (Int.repr L)) GLOBALS (gv)
    SEP (BIT_DStream_rep sh gv s start pos lo bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc)) oc ob)
  POST [ tulong ]
    EX pos': Z, EX lo': Z, EX l: list Z,
    PROP (Zlength l = k; bytes_ok l; lo' + 64 - pos' <= lo + 64 - pos + 12 * k;
          lo <= pos -> forall l', huf_decode_syms ht s (Z.to_nat k) pos = Some (l', 0) ->
            l = l' /\ pos' = 0 /\ lo' = 0;
          forall dx, xb_rel s pos lo dx ->
            fst (xh_x2_stream (xhuf_of true ht) s dx k) = l /\
            xb_rel s pos' lo' (snd (xh_x2_stream (xhuf_of true ht) s dx k)))
    RETURN (Vlong (Int64.repr k))
    SEP (BIT_DStream_rep sh gv s start pos' lo' bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc)) (sublist 0 a oc ++ zbytes l ++ sublist (a + k) (Zlength oc) oc) ob).

(* ---------- the bodies (dst, dstSize, cSrc, cSrcSize, DTable) ----------
   huf_x_using_spec four true without the flags; exactly (last PROP): ExHuf.x_huf_decode's outcome. *)
Definition huf_x2_body_spec (four: bool) : funspec :=
  WITH gv: globals, sht: share, dt: val, ht: huf_table, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint ]
    PROP (readable_share sht; writable_share sho; 1 <= Zlength oc;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s)); dt)
    GLOBALS (gv)
    SEP (zstd_globals gv; hufdt_x_at true sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n; (byte_cells oc -> byte_cells oc');
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits_with four ht s n with
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end;
          match x_huf_decode (xhuf_of true ht) (negb four) s n with
          | None => is_error_code r = true
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; hufdt_x_at true sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base).

Definition HUF_decompress1X2_usingDTable_internal_body_spec : ident * funspec :=
  DECLARE _HUF_decompress1X2_usingDTable_internal_body huf_x2_body_spec false.
Definition HUF_decompress4X2_usingDTable_internal_body_spec : ident * funspec :=
  DECLARE _HUF_decompress4X2_usingDTable_internal_body huf_x2_body_spec true.
Definition HUF_decompress4X2_usingDTable_internal_default_spec : ident * funspec :=
  DECLARE _HUF_decompress4X2_usingDTable_internal_default huf_x2_body_spec true.

(* ---------- the specifications of ids_X2D, in its order ---------- *)
Definition X2D_specs : funspecs :=
  [ HUF_decodeSymbolX2_spec; HUF_decodeLastSymbolX2_spec; HUF_decodeStreamX2_spec;
    HUF_decompress1X2_usingDTable_internal_body_spec; HUF_decompress4X2_usingDTable_internal_body_spec;
    HUF_decompress4X2_usingDTable_internal_default_spec; HUF_decompress4X2_usingDTable_internal_spec;
    HUF_decompress1X2_usingDTable_internal_spec ].

(* ---------- the contexts of the body lemmas ---------- *)
Definition G_sym2 : funspecs := [ BIT_lookBitsFast_spec; memcpy_spec; BIT_skipBits_spec ].
Definition G_stream2 : funspecs :=
  [ BIT_reloadDStream_spec; MEM_64bits_spec; HUF_decodeSymbolX2_spec; HUF_decodeLastSymbolX2_spec ].
Definition G_1X2 : funspecs :=
  [ BIT_initDStream_spec; ERR_isError_spec; ZSTD_maybeNullPtrAdd_spec; HUF_getDTableDesc_spec;
    HUF_decodeStreamX2_spec; BIT_endOfDStream_spec ].
Definition G_4X2 : funspecs :=
  [ MEM_readLE16_spec; HUF_getDTableDesc_spec; BIT_initDStream_spec; ERR_isError_spec; MEM_64bits_spec;
    HUF_decodeSymbolX2_spec; BIT_reloadDStreamFast_spec; HUF_decodeStreamX2_spec; BIT_endOfDStream_spec ].
