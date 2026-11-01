(* Sub-group X1D (HufX1D.v): the internal specifications of the X1 decoders and the small contexts their
   body lemmas are proved in (lifted to G_HUF ++ X1D_imports ++ X1D_specs by Layer.body_ok_mono).
   Fixed: the X1D body lemmas are proved against these specifications.

   Files: HufX1DSym.v (decodeSymbolX1), HufX1DStream.v (decodeStreamX1), HufX1D1.v (1X1 body),
   HufX1D4.v (4X1 body), HufX1D.v (the wrappers and X1D_ok). *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMPeek.
Require Export Zstd.proof.dec.B.huf.HufXBit.
Local Open Scope logic.

Definition t_bitD : type := Tstruct ___gp_BIT_DStream_t noattr.

(* ---------- model facts ---------- *)

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

(* ---------- HUF_decodeSymbolX1(D, dt, L) ----------
   Peeks L bits (BIT_lookBitsFast: v, exact when the bits are in the container or lo = 0 < pos), returns
   the byte of cell v and skips its code length.  np: the state is BIT_DStream_rep_np (window pointer, the
   4-stream loop) or BIT_DStream_rep (Spec_bits.BIT_DStream_rep_g).  The table: the 2^L X1 cells of ht (hufdt_x_at false).
   Exactly (last PROP): v is the C's peek on every state, ExHuf.xb_look_fast of the reader (HufXBit). *)
Definition HUF_decodeSymbolX1_spec : ident * funspec :=
  DECLARE _HUF_decodeSymbolX1
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       sht: share, dt: val, ht: huf_table, L: Z, np: bool
  PRE [ tptr t_bitD, tptr t_deltx1, tuint ]
    PROP (writable_share sh; readable_share sht; huf_ok ht; ht_log ht <= L <= HUF_TABLELOG_MAX;
          lo + 64 - (pos - L) <= Int.max_unsigned)
    PARAMS (p; dt; Vint (Int.repr L))
    SEP (BIT_DStream_rep_g np sh gv s start pos lo p; data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) dt)
  POST [ tuchar ]
    EX v: Z,
    PROP (0 <= v < 2 ^ L; lo <= pos - L \/ (lo = 0 /\ 0 < pos) -> v = bs_peek (bs_value s) pos L;
          v = xb_look_fast (xb_of s pos lo) L)
    RETURN (Vint (Int.repr (fst (hsym ht L v))))
    SEP (BIT_DStream_rep_g np sh gv s start (pos - snd (hsym ht L v)) lo p;
         data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) dt).

(* ---------- HUF_decodeStreamX1(p, D, pEnd, dt, L) ----------
   Fills the k = pEnd - p bytes at offset a of the output array (any stream state, any bytes: k defined
   bytes l, returns k); bitsConsumed grows by at most 12 per byte.  Model: from a non-overflowed state
   (lo <= pos), if the model decodes exactly k symbols from pos ending at 0, then l are those symbols and
   the stream ends consumed (pos' = 0, window at the bottom: BIT_endOfDStream returns 1).
   Exactly (last PROP; the table's log is the reader's, L = xh_x1_log ht): from any state, the bytes and the
   new state are ExHuf.xh_x1_stream's, for either C description d of the state (HufXBit.xb_rel). *)
Definition HUF_decodeStreamX1_spec : ident * funspec :=
  DECLARE _HUF_decodeStreamX1
  WITH sh: share, bD: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z,
       sht: share, dt: val, ht: huf_table, L: Z,
       sho: share, ob: val, oc: list val, a: Z, k: Z
  PRE [ tptr tuchar, tptr t_bitD, tptr tuchar, tptr t_deltx1, tuint ]
    PROP (writable_share sh; readable_share shs; bit_src_ok s start bp buf off;
          readable_share sht; huf_ok ht; ht_log ht <= L <= HUF_TABLELOG_MAX;
          writable_share sho; 1 <= Zlength oc; 0 <= a; 0 <= k; a + k <= Zlength oc;
          lo + 64 - pos + 12 * k <= Int.max_unsigned; L = xh_x1_log ht)
    PARAMS (offset_val a ob; bD; offset_val (a + k) ob; dt; Vint (Int.repr L)) GLOBALS (gv)
    SEP (BIT_DStream_rep sh gv s start pos lo bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) dt;
         data_at sho (tarray tuchar (Zlength oc)) oc ob)
  POST [ tulong ]
    EX pos': Z, EX lo': Z, EX l: list Z,
    PROP (Zlength l = k; bytes_ok l; lo' + 64 - pos' <= lo + 64 - pos + 12 * k;
          lo <= pos -> forall l', huf_decode_syms ht s (Z.to_nat k) pos = Some (l', 0) ->
            l = l' /\ pos' = 0 /\ lo' = 0;
          forall dx, xb_rel s pos lo dx ->
            fst (xh_x1_stream (xhuf_of false ht) s dx k) = l /\
            xb_rel s pos' lo' (snd (xh_x1_stream (xhuf_of false ht) s dx k)))
    RETURN (Vlong (Int64.repr k))
    SEP (BIT_DStream_rep sh gv s start pos' lo' bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) dt;
         data_at sho (tarray tuchar (Zlength oc)) (sublist 0 a oc ++ zbytes l ++ sublist (a + k) (Zlength oc) oc) ob).

(* ---------- the bodies (dst, dstSize, cSrc, cSrcSize, DTable) ----------
   huf_x_using_spec four false without the flags, and with a nonempty output array (a pointer comparison
   needs a valid pointer). *)
Definition huf_x1_body_spec (four: bool) : funspec :=
  WITH gv: globals, sht: share, dt: val, ht: huf_table, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint ]
    PROP (readable_share sht; writable_share sho; 1 <= Zlength oc;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s)); dt)
    GLOBALS (gv)
    SEP (zstd_globals gv; hufdt_x_at false sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n;
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits_with four ht s n with
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; hufdt_x_at false sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base).

Definition HUF_decompress1X1_usingDTable_internal_body_spec : ident * funspec :=
  DECLARE _HUF_decompress1X1_usingDTable_internal_body huf_x1_body_spec false.
Definition HUF_decompress4X1_usingDTable_internal_body_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_usingDTable_internal_body huf_x1_body_spec true.
Definition HUF_decompress4X1_usingDTable_internal_default_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_usingDTable_internal_default huf_x1_body_spec true.

(* ---------- the specifications of ids_X1D, in its order ---------- *)
Definition X1D_specs : funspecs :=
  [ HUF_decodeSymbolX1_spec; HUF_decodeStreamX1_spec; HUF_decompress1X1_usingDTable_internal_body_spec;
    HUF_decompress4X1_usingDTable_internal_body_spec; HUF_decompress4X1_usingDTable_internal_default_spec;
    HUF_decompress1X1_usingDTable_internal_spec; HUF_decompress4X1_usingDTable_internal_spec ].

(* ---------- the contexts of the body lemmas ---------- *)
Definition G_sym : funspecs := [ BIT_lookBitsFast_spec; BIT_skipBits_spec ].
Definition G_stream : funspecs :=
  [ BIT_reloadDStream_spec; MEM_64bits_spec; MEM_32bits_spec; HUF_decodeSymbolX1_spec ].
Definition G_1X1 : funspecs :=
  [ ZSTD_maybeNullPtrAdd_spec; HUF_getDTableDesc_spec; BIT_initDStream_spec; ERR_isError_spec;
    HUF_decodeStreamX1_spec; BIT_endOfDStream_spec ].
Definition G_4X1 : funspecs :=
  [ MEM_readLE16_spec; HUF_getDTableDesc_spec; BIT_initDStream_spec; ERR_isError_spec; MEM_64bits_spec;
    HUF_decodeSymbolX1_spec; BIT_reloadDStreamFast_spec; HUF_decodeStreamX1_spec; BIT_endOfDStream_spec ].
