(* Specifications of the decoder, group `xxh`: XXH64 (the frame checksum; ZSTD_XXH64 is also called by the constructive harnesses).
   One specification per function, shared by every harness.
   A function still specified by `vacuous_funspec` has precondition FF: a placeholder until its
   specification is written (for group `dead`: final). *)
Require Export Zstd.proof.zstd.Spec_bits.

(* ---------- the state of the streaming hash (struct XXH64_state_s) ---------- *)

Definition t_xxh64_state : type := Tstruct _XXH64_state_s noattr.

(* the bytes l as C values *)
Definition xxh_bytes (l: list Z) : list val := map (fun b => Vint (Int.repr b)) l.

(* the four lanes before the first stripe *)
Definition xxh_init (seed: Z) : Z * Z * Z * Z :=
  (m64 (seed + XXH_P1 + XXH_P2), m64 (seed + XXH_P2), m64 seed, m64 (seed - XXH_P1)).

(* after consuming l: the lanes (every whole 32-byte stripe of l) and the buffered rest (< 32 bytes) *)
Definition xxh_lanes (seed: Z) (l: list Z) : Z * Z * Z * Z := fst (xxh_stripes (length l) (xxh_init seed) l).
Definition xxh_rest (seed: Z) (l: list Z) : list Z := snd (xxh_stripes (length l) (xxh_init seed) l).

Definition xxh_lane1 (v: Z * Z * Z * Z) : Z := match v with (a, _, _, _) => a end.
Definition xxh_lane2 (v: Z * Z * Z * Z) : Z := match v with (_, a, _, _) => a end.
Definition xxh_lane3 (v: Z * Z * Z * Z) : Z := match v with (_, _, a, _) => a end.
Definition xxh_lane4 (v: Z * Z * Z * Z) : Z := match v with (_, _, _, a) => a end.

(* what XXH64_digest computes from the state of l (total_len is kept mod 2^64);
   = xxh64 l seed when Zlength l <= Int64.max_unsigned (lemma xxh64_digest_model_eq, XxhLemmas.v) *)
Definition xxh64_digest_model (seed: Z) (l: list Z) : Z :=
  let v := xxh_lanes seed l in
  let tl := m64 (Zlength l) in
  let h :=
    if tl >=? 32 then
      let h := m64 (rotl64 (xxh_lane1 v) 1 + rotl64 (xxh_lane2 v) 7 + rotl64 (xxh_lane3 v) 12 + rotl64 (xxh_lane4 v) 18) in
      xxh_merge (xxh_merge (xxh_merge (xxh_merge h (xxh_lane1 v)) (xxh_lane2 v)) (xxh_lane3 v)) (xxh_lane4 v)
    else m64 (xxh_lane3 v + XXH_P5) in
  xxh_finalize (m64 (h + tl)) (xxh_rest seed l).

(* xxh64_state sh seed l p: the XXH64_state_s at p (any address: a variable, a field) has been reset
   with seed and has consumed the bytes l.  mem64 is held as 32 bytes: the buffered rest, then junk. *)
Definition xxh64_state (sh: share) (seed: Z) (l: list Z) (p: val) : mpred :=
  EX junk: list val,
  !! (bytes_ok l /\ Zlength junk = 32 - Zlength (xxh_rest seed l)) &&
  (field_at sh t_xxh64_state (DOT _total_len) (Vlong (Int64.repr (Zlength l))) p *
   field_at sh t_xxh64_state (DOT _v)
     (map Vlong (map Int64.repr [xxh_lane1 (xxh_lanes seed l); xxh_lane2 (xxh_lanes seed l);
                                 xxh_lane3 (xxh_lanes seed l); xxh_lane4 (xxh_lanes seed l)])) p *
   data_at sh (tarray tuchar 32) (xxh_bytes (xxh_rest seed l) ++ junk)
     (field_address t_xxh64_state (DOT _mem64) p) *
   field_at sh t_xxh64_state (DOT _memsize) (Vint (Int.repr (Zlength (xxh_rest seed l)))) p *
   field_at_ sh t_xxh64_state (DOT _reserved32) p *
   field_at_ sh t_xxh64_state (DOT _reserved64) p).

(* ---------- specifications ---------- *)

(* Byte inputs: data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p.  The code compares p with
   NULL, which CompCert defines only for a (weakly) valid pointer.  For an EMPTY input the caller
   names a resource it holds, w: ptr_witness (returned unchanged), with pw_pred w |-- weak_valid_pointer p:
   the buffer around p (pw_bytes: e.g. the whole output buffer, the rest of an array), or the
   malloc_token of a zero-sized block (pw_token).  For a non-empty input w can be pw_none.
   p = NULL is not supported.  (A WITH of type mpred is a universe inconsistency in VST, hence the
   first-order witness.) *)
Inductive ptr_witness : Type :=
| pw_none
| pw_bytes (sh: share) (n: Z) (c: list val) (base: val)
| pw_token (sh: share) (t: type) (q: val).

Definition pw_pred (w: ptr_witness) : mpred :=
  match w with
  | pw_none => emp
  | pw_bytes sh n c base => data_at sh (tarray tuchar n) c base
  | pw_token sh t q => malloc_token sh t q
  end.

(* a list of witnesses (the API's buffers lend theirs as a list) *)
Definition pws_pred (ws: list ptr_witness) : mpred := fold_right sepcon emp (map pw_pred ws).

Definition XXH_memcpy_spec :=
  DECLARE _XXH_memcpy
  WITH shs: share, shd: share, src: val, dst: val, tv: {t: type & reptype t}
  PRE  [ tptr tvoid, tptr tvoid, tulong ]
       PROP (readable_share shs; writable_share shd; 0 <= sizeof (projT1 tv) <= Int64.max_unsigned;
             memcpy_ok (projT1 tv) (projT2 tv))
       PARAMS (dst; src; Vlong (Int64.repr (sizeof (projT1 tv))))
       SEP (data_at shs (projT1 tv) (projT2 tv) src; data_at_ shd (projT1 tv) dst)
  POST [ tptr tvoid ]
       PROP () RETURN (dst)
       SEP (data_at shs (projT1 tv) (projT2 tv) src; data_at shd (projT1 tv) (projT2 tv) dst).

(* the n bytes bs at p read as a little-endian scalar *)
Definition XXH_read32_spec :=
  DECLARE _XXH_read32
  WITH sh: share, p: val, bs: list Z
  PRE  [ tptr tvoid ]
       PROP (readable_share sh; Zlength bs = 4; bytes_ok bs)
       PARAMS (p)
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p)
  POST [ tuint ]
       PROP () RETURN (Vint (Int.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p).

Definition XXH_readLE32_spec :=
  DECLARE _XXH_readLE32
  WITH sh: share, p: val, bs: list Z
  PRE  [ tptr tvoid ]
       PROP (readable_share sh; Zlength bs = 4; bytes_ok bs)
       PARAMS (p)
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p)
  POST [ tuint ]
       PROP () RETURN (Vint (Int.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p).

(* align: 1 = XXH_unaligned (memcpy), 0 = XXH_aligned (a direct load: p aligned for the scalar) *)
Definition XXH_readLE32_align_spec :=
  DECLARE _XXH_readLE32_align
  WITH sh: share, p: val, bs: list Z, align: Z
  PRE  [ tptr tvoid, tint ]
       PROP (readable_share sh; Zlength bs = 4; bytes_ok bs;
             align = 1 \/ (align = 0 /\ field_compatible tuint [] p))
       PARAMS (p; Vint (Int.repr align))
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p)
  POST [ tuint ]
       PROP () RETURN (Vint (Int.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 4) (xxh_bytes bs) p).

Definition XXH_read64_spec :=
  DECLARE _XXH_read64
  WITH sh: share, p: val, bs: list Z
  PRE  [ tptr tvoid ]
       PROP (readable_share sh; Zlength bs = 8; bytes_ok bs)
       PARAMS (p)
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p).

Definition XXH_readLE64_spec :=
  DECLARE _XXH_readLE64
  WITH sh: share, p: val, bs: list Z
  PRE  [ tptr tvoid ]
       PROP (readable_share sh; Zlength bs = 8; bytes_ok bs)
       PARAMS (p)
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p).

Definition XXH_readLE64_align_spec :=
  DECLARE _XXH_readLE64_align
  WITH sh: share, p: val, bs: list Z, align: Z
  PRE  [ tptr tvoid, tint ]
       PROP (readable_share sh; Zlength bs = 8; bytes_ok bs;
             align = 1 \/ (align = 0 /\ field_compatible tulong [] p))
       PARAMS (p; Vint (Int.repr align))
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (le_value bs)))
       SEP (data_at sh (tarray tuchar 8) (xxh_bytes bs) p).

Definition XXH64_round_spec :=
  DECLARE _XXH64_round
  WITH acc: Z, input: Z
  PRE  [ tulong, tulong ]
       PROP (0 <= acc <= Int64.max_unsigned; 0 <= input <= Int64.max_unsigned)
       PARAMS (Vlong (Int64.repr acc); Vlong (Int64.repr input)) SEP ()
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh_round acc input))) SEP ().

Definition XXH64_mergeRound_spec :=
  DECLARE _XXH64_mergeRound
  WITH acc: Z, v: Z
  PRE  [ tulong, tulong ]
       PROP (0 <= acc <= Int64.max_unsigned; 0 <= v <= Int64.max_unsigned)
       PARAMS (Vlong (Int64.repr acc); Vlong (Int64.repr v)) SEP ()
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh_merge acc v))) SEP ().

Definition XXH64_avalanche_spec :=
  DECLARE _XXH64_avalanche
  WITH h: Z
  PRE  [ tulong ]
       PROP (0 <= h <= Int64.max_unsigned)
       PARAMS (Vlong (Int64.repr h)) SEP ()
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh_avalanche h))) SEP ().

(* the last len mod 32 bytes bs at p; aligned (align = 0): p 8-aligned *)
Definition XXH64_finalize_spec :=
  DECLARE _XXH64_finalize
  WITH sh: share, h: Z, p: val, bs: list Z, len: Z, align: Z, w: ptr_witness
  PRE  [ tulong, tptr tuchar, tulong, tint ]
       PROP (readable_share sh; 0 <= h <= Int64.max_unsigned; 0 <= len <= Int64.max_unsigned;
             Zlength bs = len mod 32; bytes_ok bs;
             align = 1 \/ (align = 0 /\ exists b o, p = Vptr b o /\ (8 | Ptrofs.unsigned o));
             Zlength bs = 0 -> (pw_pred w |-- weak_valid_pointer p))
       PARAMS (Vlong (Int64.repr h); p; Vlong (Int64.repr len); Vint (Int.repr align))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh_finalize h bs)))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w).

(* only XXH_unaligned (1) is reachable: ZSTD_XXH64's aligned call is under XXH_FORCE_ALIGN_CHECK = 0 *)
Definition XXH64_endian_align_spec :=
  DECLARE _XXH64_endian_align
  WITH sh: share, p: val, bs: list Z, seed: Z, w: ptr_witness
  PRE  [ tptr tuchar, tulong, tulong, tint ]
       PROP (readable_share sh; bytes_ok bs; 0 <= seed <= Int64.max_unsigned;
             Zlength bs = 0 -> (pw_pred w |-- weak_valid_pointer p))
       PARAMS (p; Vlong (Int64.repr (Zlength bs)); Vlong (Int64.repr seed); Vint (Int.repr 1))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh64 bs seed)))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w).

(* one-shot: XXH64(p, n, seed) on the n bytes bs at p *)
Definition ZSTD_XXH64_spec :=
  DECLARE _ZSTD_XXH64
  WITH sh: share, p: val, bs: list Z, seed: Z, w: ptr_witness
  PRE  [ tptr tvoid, tulong, tulong ]
       PROP (readable_share sh; bytes_ok bs; 0 <= seed <= Int64.max_unsigned;
             Zlength bs = 0 -> (pw_pred w |-- weak_valid_pointer p))
       PARAMS (p; Vlong (Int64.repr (Zlength bs)); Vlong (Int64.repr seed))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh64 bs seed)))
       SEP (data_at sh (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pw_pred w).

Definition ZSTD_XXH64_reset_spec :=
  DECLARE _ZSTD_XXH64_reset
  WITH sh: share, st: val, seed: Z
  PRE  [ tptr t_xxh64_state, tulong ]
       PROP (writable_share sh; 0 <= seed <= Int64.max_unsigned)
       PARAMS (st; Vlong (Int64.repr seed))
       SEP (data_at_ sh t_xxh64_state st)
  POST [ tint ]
       PROP () RETURN (Vint (Int.repr 0))
       SEP (xxh64_state sh seed [] st).

(* len <= 2^64 - 1 - 32: the code tests memsize + len < 32 in size_t, which wraps for a larger len *)
Definition ZSTD_XXH64_update_spec :=
  DECLARE _ZSTD_XXH64_update
  WITH sh: share, st: val, seed: Z, l: list Z, shi: share, p: val, bs: list Z, ws: list ptr_witness
  PRE  [ tptr t_xxh64_state, tptr tvoid, tulong ]
       PROP (writable_share sh; readable_share shi; bytes_ok bs; Zlength bs <= Int64.max_unsigned - 32;
             Zlength bs = 0 -> (pws_pred ws |-- weak_valid_pointer p))
       PARAMS (st; p; Vlong (Int64.repr (Zlength bs)))
       SEP (xxh64_state sh seed l st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws)
  POST [ tint ]
       PROP () RETURN (Vint (Int.repr 0))
       SEP (xxh64_state sh seed (l ++ bs) st; data_at shi (tarray tuchar (Zlength bs)) (xxh_bytes bs) p; pws_pred ws).

Definition ZSTD_XXH64_digest_spec :=
  DECLARE _ZSTD_XXH64_digest
  WITH sh: share, st: val, seed: Z, l: list Z
  PRE  [ tptr t_xxh64_state ]
       PROP (readable_share sh)
       PARAMS (st)
       SEP (xxh64_state sh seed l st)
  POST [ tulong ]
       PROP () RETURN (Vlong (Int64.repr (xxh64_digest_model seed l)))
       SEP (xxh64_state sh seed l st).

Definition Specs_xxh : funspecs := [
  XXH_memcpy_spec;
  XXH_read32_spec;
  XXH_readLE32_spec;
  XXH_readLE32_align_spec;
  XXH_read64_spec;
  XXH_readLE64_spec;
  XXH_readLE64_align_spec;
  XXH64_round_spec;
  XXH64_mergeRound_spec;
  XXH64_avalanche_spec;
  XXH64_finalize_spec;
  XXH64_endian_align_spec;
  ZSTD_XXH64_spec;
  ZSTD_XXH64_reset_spec;
  ZSTD_XXH64_update_spec;
  ZSTD_XXH64_digest_spec
].
