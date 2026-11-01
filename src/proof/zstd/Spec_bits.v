(* Specifications of the decoder, group `bits`: the backward bitstream reader BIT_* (lib/common/bitstream.h).
   One specification per function, shared by every harness.
   A function still specified by `vacuous_funspec` has precondition FF: a placeholder until its
   specification is written (for group `dead`: final). *)
Require Export Zstd.proof.zstd.Spec_util.

(* ---------- The state of a BIT_DStream_t, against the model (model/Bitstream.v) ----------

   The reader reads the stream s (bytes at `start`, n = Zlength s >= 1) backward.  Its model state
   is pos: the number of bits of V = bs_value s not yet read (bs_total s after BIT_initDStream; may
   become negative when a reader reads past the end).  The C state also has a window: ptr = start + k,
   and bitContainer holds the 8 bytes s[k, k+8) (s itself, zero-extended, when n < 8), i.e. the bits
   [lo, lo + 64) of V with lo = 8 k; bitsConsumed = lo + 64 - pos.  The window base lo is part of the
   abstract state: bits below lo are not in the container (a read below lo returns an unspecified
   value).  After a reload that returns BIT_DStream_unfinished, pos - lo >= 57.
   The overflow state (bitsConsumed > 64, i.e. pos < lo): BIT_reloadDStream then sets ptr to
   &zeroFilled (a global), and returns BIT_DStream_overflow forever. *)

Definition bit_C (s: list Z) (lo: Z) : Z := (bs_value s / 2 ^ lo) mod 2 ^ 64.

Definition bit_inv (s: list Z) (pos lo: Z) : Prop :=
  bytes_ok s /\ 1 <= Zlength s /\
  0 <= lo /\ lo mod 8 = 0 /\ lo / 8 <= Z.max 0 (Zlength s - 8) /\
  pos <= lo + 64 /\ lo + 64 - pos <= Int.max_unsigned.

Definition BIT_DStream_rep (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) : mpred :=
  EX ptr: val, EX lim: val,
  !! (bit_inv s pos lo /\
      (ptr = offset_val (lo / 8) start \/ (pos < lo /\ ptr = gv _zeroFilled))) &&
  data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
    (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (ptr, (start, lim)))) p.

(* The same state with ptr the window pointer for sure, also past the end (pos < lo): the state between
   the fast operations of the 4-stream Huffman loops, which never move ptr to &zeroFilled. *)
Definition BIT_DStream_rep_np (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) : mpred :=
  EX lim: val,
  !! (bit_inv s pos lo) &&
  data_at sh (Tstruct ___gp_BIT_DStream_t noattr)
    (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (offset_val (lo / 8) start, (start, lim)))) p.

Lemma BIT_DStream_rep_np_rep: forall sh gv s start pos lo p,
  BIT_DStream_rep_np sh gv s start pos lo p |-- BIT_DStream_rep sh gv s start pos lo p.
Proof.
  intros. unfold BIT_DStream_rep_np, BIT_DStream_rep. Intros lim.
  Exists (offset_val (lo / 8) start) lim. entailer!.
Qed.

Lemma BIT_DStream_rep_rep_np: forall sh gv s start pos lo p, lo <= pos ->
  BIT_DStream_rep sh gv s start pos lo p |-- BIT_DStream_rep_np sh gv s start pos lo p.
Proof.
  intros. unfold BIT_DStream_rep_np, BIT_DStream_rep. Intros ptr lim.
  destruct H1 as [-> | [? _]]; [| lia].
  Exists lim. entailer!.
Qed.

(* rep or rep_np *)
Definition BIT_DStream_rep_g (np: bool) (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) : mpred :=
  if np then BIT_DStream_rep_np sh gv s start pos lo p else BIT_DStream_rep sh gv s start pos lo p.

(* Where the stream bytes are: s = buf[off, off + n), buf a byte array the caller holds (any
   readable share), start = bp + off.  (Since patch item 12, BIT_reloadDStream compares distances
   inside the stream: no slack below start is needed.) *)
Definition bit_src_ok (s: list Z) (start bp: val) (buf: list Z) (off: Z) : Prop :=
  start = offset_val off bp /\ 0 <= off /\ off + Zlength s <= Zlength buf /\
  sublist off (off + Zlength s) buf = s.

Definition bit_src (shs: share) (bp: val) (buf: list Z) : mpred :=
  data_at shs (tarray tuchar (Zlength buf)) (zbytes buf) bp.

(* A well-formed stream (bs_ok of the model, for a byte string): nonempty, last byte not 0. *)
Definition bs_wf (s: list Z) : bool := negb (Zlength s =? 0) && negb (last s 0 =? 0).

(* BIT_DStream_status *)
Definition BIT_unfinished := 0.
Definition BIT_endOfBuffer := 1.
Definition BIT_completed := 2.
Definition BIT_overflow := 3.

(* BIT_reloadDStream: (status, new lo); pos does not change *)
Definition bs_reload (pos lo: Z) : Z * Z :=
  if pos <? lo then (BIT_overflow, lo) else
  let k := lo / 8 in
  let nb := (lo + 64 - pos) / 8 in
  if 8 <=? k then (BIT_unfinished, lo - 8 * nb)
  else if k =? 0 then ((if 0 <? pos then BIT_endOfBuffer else BIT_completed), lo)
  else if k <? nb then (BIT_endOfBuffer, 0)
  else (BIT_unfinished, lo - 8 * nb).

(* BIT_reloadDStreamFast (requires lo <= pos) *)
Definition bs_reload_fast (pos lo: Z) : Z * Z :=
  if lo / 8 <? 8 then (BIT_overflow, lo) else (BIT_unfinished, lo - 8 * ((lo + 64 - pos) / 8)).

(* ---------- specifications ---------- *)

(* Success (srcSize >= 1, last byte not 0: bs_wf, i.e. bs_ok): returns srcSize, state
   pos = bs_total s with the window at the top.  Otherwise an error code, struct contents unspecified.
   Reads the De Bruijn table (ZSTD_highbit32): zstd_globals. *)
Definition BIT_initDStream_spec : ident * funspec :=
  DECLARE _BIT_initDStream
  WITH sh: share, p: val, shs: share, bp: val, buf: list Z, off: Z, n: Z, gv: globals
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tptr tvoid, tulong ]
    PROP (writable_share sh; readable_share shs; 0 <= off; 0 <= n; off + n <= Zlength buf;
          bytes_ok (sublist off (off + n) buf))
    PARAMS (p; offset_val off bp; Vlong (Int64.repr n)) GLOBALS (gv)
    SEP (data_at_ sh (Tstruct ___gp_BIT_DStream_t noattr) p; bit_src shs bp buf; zstd_globals gv)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r <= Int64.max_unsigned;
          if bs_wf (sublist off (off + n) buf) then r = n else is_error_code r = true)
    RETURN (Vlong (Int64.repr r))
    SEP (if bs_wf (sublist off (off + n) buf)
         then BIT_DStream_rep sh gv (sublist off (off + n) buf) (offset_val off bp)
                (bs_total (sublist off (off + n) buf)) (8 * Z.max 0 (n - 8)) p
         else data_at_ sh (Tstruct ___gp_BIT_DStream_t noattr) p;
         bit_src shs bp buf; zstd_globals gv).

(* (bitContainer >> (start & 63)) & ((1 << nbBits) - 1), for nbBits < 64 *)
Definition BIT_getMiddleBits_spec : ident * funspec :=
  DECLARE _BIT_getMiddleBits
  WITH c: Z, st: Z, nb: Z
  PRE [ tulong, tuint, tuint ]
    PROP (0 <= c <= Int64.max_unsigned; 0 <= st <= Int.max_unsigned; 0 <= nb < 64)
    PARAMS (Vlong (Int64.repr c); Vint (Int.repr st); Vint (Int.repr nb)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Z.land (Z.shiftr c (st mod 64)) (Z.ones nb)))) SEP ().

(* Peek nb bits (nb < 64): the model's bs_peek when the bits are in the container (lo <= pos - nb);
   otherwise some value below 2^nb.  The state is unchanged. *)
Definition BIT_lookBits_spec : ident * funspec :=
  DECLARE _BIT_lookBits
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z, nb: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tuint ]
    PROP (readable_share sh; 0 <= nb < 64)
    PARAMS (p; Vint (Int.repr nb))
    SEP (BIT_DStream_rep sh gv s start pos lo p)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r < 2 ^ nb; lo <= pos - nb -> r = bs_peek (bs_value s) pos nb)
    RETURN (Vlong (Int64.repr r))
    SEP (BIT_DStream_rep sh gv s start pos lo p).

(* The fast peek (1 <= nb < 64): also exact past the end of the stream (zero bits below 0) as long
   as the window is at the bottom and some bit is left (lo = 0 < pos).  On every state (last PROP): the
   value the C computes, (bitContainer << (bitsConsumed & 63)) >> (64 - nb), also when the bits are not in
   the container (the Huffman decoders' exact outcome depends on it: model/ExHuf.v, xb_look_fast). *)
Definition BIT_lookBitsFast_spec : ident * funspec :=
  DECLARE _BIT_lookBitsFast
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z, nb: Z, np: bool
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tuint ]
    PROP (readable_share sh; 1 <= nb < 64)
    PARAMS (p; Vint (Int.repr nb))
    SEP (BIT_DStream_rep_g np sh gv s start pos lo p)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r < 2 ^ nb; lo <= pos - nb \/ (lo = 0 /\ 0 < pos) -> r = bs_peek (bs_value s) pos nb;
          r = Z.shiftr ((Z.shiftl (bit_C s lo) ((lo + 64 - pos) mod 64)) mod 2 ^ 64) (64 - nb))
    RETURN (Vlong (Int64.repr r))
    SEP (BIT_DStream_rep_g np sh gv s start pos lo p).

(* pos -= nb.  bitsConsumed must not wrap around (lo + 64 - (pos - nb) <= Int.max_unsigned). *)
Definition BIT_skipBits_spec : ident * funspec :=
  DECLARE _BIT_skipBits
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z, nb: Z, np: bool
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tuint ]
    PROP (writable_share sh; 0 <= nb; lo + 64 - (pos - nb) <= Int.max_unsigned)
    PARAMS (p; Vint (Int.repr nb))
    SEP (BIT_DStream_rep_g np sh gv s start pos lo p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (BIT_DStream_rep_g np sh gv s start (pos - nb) lo p).

Definition BIT_readBits_spec : ident * funspec :=
  DECLARE _BIT_readBits
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z, nb: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tuint ]
    PROP (writable_share sh; 0 <= nb < 64; lo + 64 - (pos - nb) <= Int.max_unsigned)
    PARAMS (p; Vint (Int.repr nb))
    SEP (BIT_DStream_rep sh gv s start pos lo p)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r < 2 ^ nb; lo <= pos - nb -> r = bs_peek (bs_value s) pos nb)
    RETURN (Vlong (Int64.repr r))
    SEP (BIT_DStream_rep sh gv s start (pos - nb) lo p).

Definition BIT_readBitsFast_spec : ident * funspec :=
  DECLARE _BIT_readBitsFast
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z, nb: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr), tuint ]
    PROP (writable_share sh; 1 <= nb < 64; lo + 64 - (pos - nb) <= Int.max_unsigned)
    PARAMS (p; Vint (Int.repr nb))
    SEP (BIT_DStream_rep sh gv s start pos lo p)
  POST [ tulong ]
    EX r: Z,
    PROP (0 <= r < 2 ^ nb; lo <= pos - nb \/ (lo = 0 /\ 0 < pos) -> r = bs_peek (bs_value s) pos nb)
    RETURN (Vlong (Int64.repr r))
    SEP (BIT_DStream_rep sh gv s start (pos - nb) lo p).

(* Called by BIT_reloadDStream(Fast) with ptr - start >= 8 and bitsConsumed <= 64. *)
Definition BIT_reloadDStream_internal_spec : ident * funspec :=
  DECLARE _BIT_reloadDStream_internal
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr) ]
    PROP (writable_share sh; readable_share shs; bit_src_ok s start bp buf off; lo <= pos; 64 <= lo)
    PARAMS (p)
    SEP (BIT_DStream_rep sh gv s start pos lo p; bit_src shs bp buf)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr BIT_unfinished))
    SEP (BIT_DStream_rep sh gv s start pos (lo - 8 * ((lo + 64 - pos) / 8)) p; bit_src shs bp buf).

(* With ptr the window pointer (rep_np; rep_rep_np gives it when lo <= pos): compares ptr with start + 8,
   then, when lo >= 64, reloads (bitsConsumed <= 64 needed: lo <= pos). *)
Definition BIT_reloadDStreamFast_spec : ident * funspec :=
  DECLARE _BIT_reloadDStreamFast
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr) ]
    PROP (writable_share sh; readable_share shs; bit_src_ok s start bp buf off; lo <= pos \/ lo < 64)
    PARAMS (p)
    SEP (BIT_DStream_rep_np sh gv s start pos lo p; bit_src shs bp buf)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (fst (bs_reload_fast pos lo))))
    SEP (BIT_DStream_rep_np sh gv s start pos (snd (bs_reload_fast pos lo)) p; bit_src shs bp buf).

(* Any state.  Status and new window by bs_reload; pos unchanged. *)
Definition BIT_reloadDStream_spec : ident * funspec :=
  DECLARE _BIT_reloadDStream
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr) ]
    PROP (writable_share sh; readable_share shs; bit_src_ok s start bp buf off)
    PARAMS (p) GLOBALS (gv)
    SEP (BIT_DStream_rep sh gv s start pos lo p; bit_src shs bp buf)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (fst (bs_reload pos lo))))
    SEP (BIT_DStream_rep sh gv s start pos (snd (bs_reload pos lo)) p; bit_src shs bp buf).

(* 1 iff the stream is consumed exactly (pos = 0 with the window at the bottom).  Compares ptr with
   start: needs both valid (the source bytes, and &zeroFilled of zstd_globals in the overflow state). *)
Definition BIT_endOfDStream_spec : ident * funspec :=
  DECLARE _BIT_endOfDStream
  WITH sh: share, p: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z
  PRE [ tptr (Tstruct ___gp_BIT_DStream_t noattr) ]
    PROP (readable_share sh; readable_share shs; bit_src_ok s start bp buf off)
    PARAMS (p)
    SEP (BIT_DStream_rep sh gv s start pos lo p; bit_src shs bp buf; zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if andb (lo =? 0) (pos =? 0) then 1 else 0)))
    SEP (BIT_DStream_rep sh gv s start pos lo p; bit_src shs bp buf; zstd_globals gv).

Definition Specs_bits : funspecs := [
  BIT_initDStream_spec;
  BIT_getMiddleBits_spec;
  BIT_lookBits_spec;
  BIT_lookBitsFast_spec;
  BIT_skipBits_spec;
  BIT_readBits_spec;
  BIT_readBitsFast_spec;
  BIT_reloadDStream_internal_spec;
  BIT_reloadDStreamFast_spec;
  BIT_reloadDStream_spec;
  BIT_endOfDStream_spec
].
