(* Specifications of the decoder, group `util`: MEM_*, bit counting, error codes, small copies.
   One specification per function, shared by every harness.
   A function still specified by `vacuous_funspec` has precondition FF: a placeholder until its
   specification is written (for group `dead`: final). *)
Require Export Zstd.proof.zstd.Globals.

(* A byte string of the model as C values (the form nondet_bytes produces). *)
Notation zbytes l := (map (fun b : Z => Vint (Int.repr b)) l).

(* Bit counting (ZSTD_NO_INTRINSICS: the De Bruijn fallbacks).  Both are total: ctz 0 = 0 and
   Z.log2 0 = 0 are what the fallbacks compute on 0. *)
Definition ctz (v: Z) : Z := Z.log2 (Z.land v (- v)).

(* The error code `ERROR(e)` = (size_t)-e, and the value ERR_getErrorCode extracts from a result. *)
Definition err_code (e: Z) : Z := 2 ^ 64 - e.
Definition error_of (c: Z) : Z := if is_error_code c then 2 ^ 64 - c else 0.

(* ---------- compiler.h: pointer arithmetic helpers ---------- *)

Definition ZSTD_wrappedPtrAdd_spec : ident * funspec :=
  DECLARE _ZSTD_wrappedPtrAdd
  WITH p: val, a: Z
  PRE [ tptr tvoid, tlong ]
    PROP (isptr p; Int64.min_signed <= a <= Int64.max_signed)
    PARAMS (p; Vlong (Int64.repr a)) SEP ()
  POST [ tptr tvoid ]
    PROP () RETURN (offset_val a p) SEP ().

Definition ZSTD_wrappedPtrSub_spec : ident * funspec :=
  DECLARE _ZSTD_wrappedPtrSub
  WITH p: val, a: Z
  PRE [ tptr tvoid, tlong ]
    PROP (isptr p; Int64.min_signed <= a <= Int64.max_signed)
    PARAMS (p; Vlong (Int64.repr a)) SEP ()
  POST [ tptr tvoid ]
    PROP () RETURN (offset_val (- a) p) SEP ().

(* ptr + add if add > 0 (ptr must then be a pointer), else ptr itself (may be NULL) *)
Definition ZSTD_maybeNullPtrAdd_spec : ident * funspec :=
  DECLARE _ZSTD_maybeNullPtrAdd
  WITH p: val, a: Z
  PRE [ tptr tvoid, tlong ]
    PROP (is_pointer_or_null p; 0 < a -> isptr p; Int64.min_signed <= a <= Int64.max_signed)
    PARAMS (p; Vlong (Int64.repr a)) SEP ()
  POST [ tptr tvoid ]
    PROP () RETURN (if 0 <? a then offset_val a p else p) SEP ().

(* ---------- mem.h ---------- *)

Definition MEM_32bits_spec : ident * funspec :=
  DECLARE _MEM_32bits
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tuint ] PROP () RETURN (Vint (Int.repr 0)) SEP ().

Definition MEM_64bits_spec : ident * funspec :=
  DECLARE _MEM_64bits
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tuint ] PROP () RETURN (Vint (Int.repr 1)) SEP ().

Definition MEM_isLittleEndian_spec : ident * funspec :=
  DECLARE _MEM_isLittleEndian
  WITH u: unit
  PRE [ ] PROP () PARAMS () SEP ()
  POST [ tuint ] PROP () RETURN (Vint (Int.repr 1)) SEP ().

(* Reads: the k-byte little-endian field at offset i of a byte array bs held by the caller
   (any readable share; the array is given back unchanged).  The bytes read must be defined. *)
Definition mem_read_pre (sh: share) (p: val) (bs: list Z) (i k: Z) : Prop :=
  readable_share sh /\ 0 <= i /\ i + k <= Zlength bs /\ bytes_ok (sublist i (i + k) bs).

Definition MEM_read16_spec : ident * funspec :=
  DECLARE _MEM_read16
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 2)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tushort ]
    PROP () RETURN (Vint (Int.repr (le_field bs i 2)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_read32_spec : ident * funspec :=
  DECLARE _MEM_read32
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 4)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (le_field bs i 4)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_read64_spec : ident * funspec :=
  DECLARE _MEM_read64
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 8)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le_field bs i 8)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

(* Writes: the k-byte little-endian encoding of v at offset i of a byte array with ANY contents
   (list val: may hold undefined bytes); the rest of the array is unchanged. *)
Definition mem_write_pre (sh: share) (p: val) (c: list val) (i k: Z) : Prop :=
  writable_share sh /\ 0 <= i /\ i + k <= Zlength c.

Definition mem_written (c: list val) (i k v: Z) : list val :=
  sublist 0 i c ++ zbytes (le_bytes (Z.to_nat k) v) ++ sublist (i + k) (Zlength c) c.

Definition MEM_write16_spec : ident * funspec :=
  DECLARE _MEM_write16
  WITH sh: share, p: val, c: list val, i: Z, v: Z
  PRE [ tptr tvoid, tushort ]
    PROP (mem_write_pre sh p c i 2; 0 <= v < 2 ^ 16)
    PARAMS (offset_val i p; Vint (Int.repr v)) SEP (data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh (tarray tuchar (Zlength c)) (mem_written c i 2 v) p).

Definition MEM_write32_spec : ident * funspec :=
  DECLARE _MEM_write32
  WITH sh: share, p: val, c: list val, i: Z, v: Z
  PRE [ tptr tvoid, tuint ]
    PROP (mem_write_pre sh p c i 4; 0 <= v < 2 ^ 32)
    PARAMS (offset_val i p; Vint (Int.repr v)) SEP (data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh (tarray tuchar (Zlength c)) (mem_written c i 4 v) p).

Definition MEM_write64_spec : ident * funspec :=
  DECLARE _MEM_write64
  WITH sh: share, p: val, c: list val, i: Z, v: Z
  PRE [ tptr tvoid, tulong ]
    PROP (mem_write_pre sh p c i 8; 0 <= v < 2 ^ 64)
    PARAMS (offset_val i p; Vlong (Int64.repr v)) SEP (data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh (tarray tuchar (Zlength c)) (mem_written c i 8 v) p).

(* The byte swaps run only on big-endian targets (dead here): any result. *)
Definition MEM_swap32_fallback_spec : ident * funspec :=
  DECLARE _MEM_swap32_fallback
  WITH v: int
  PRE [ tuint ] PROP () PARAMS (Vint v) SEP ()
  POST [ tuint ] EX r: int, PROP () RETURN (Vint r) SEP ().

Definition MEM_swap32_spec : ident * funspec :=
  DECLARE _MEM_swap32
  WITH v: int
  PRE [ tuint ] PROP () PARAMS (Vint v) SEP ()
  POST [ tuint ] EX r: int, PROP () RETURN (Vint r) SEP ().

Definition MEM_swap64_fallback_spec : ident * funspec :=
  DECLARE _MEM_swap64_fallback
  WITH v: int64
  PRE [ tulong ] PROP () PARAMS (Vlong v) SEP ()
  POST [ tulong ] EX r: int64, PROP () RETURN (Vlong r) SEP ().

Definition MEM_swap64_spec : ident * funspec :=
  DECLARE _MEM_swap64
  WITH v: int64
  PRE [ tulong ] PROP () PARAMS (Vlong v) SEP ()
  POST [ tulong ] EX r: int64, PROP () RETURN (Vlong r) SEP ().

Definition MEM_readLE16_spec : ident * funspec :=
  DECLARE _MEM_readLE16
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 2)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tushort ]
    PROP () RETURN (Vint (Int.repr (le_field bs i 2)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_readLE24_spec : ident * funspec :=
  DECLARE _MEM_readLE24
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 3)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (le_field bs i 3)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_readLE32_spec : ident * funspec :=
  DECLARE _MEM_readLE32
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 4)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (le_field bs i 4)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_writeLE32_spec : ident * funspec :=
  DECLARE _MEM_writeLE32
  WITH sh: share, p: val, c: list val, i: Z, v: Z
  PRE [ tptr tvoid, tuint ]
    PROP (mem_write_pre sh p c i 4; 0 <= v < 2 ^ 32)
    PARAMS (offset_val i p; Vint (Int.repr v)) SEP (data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at sh (tarray tuchar (Zlength c)) (mem_written c i 4 v) p).

Definition MEM_readLE64_spec : ident * funspec :=
  DECLARE _MEM_readLE64
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 8)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le_field bs i 8)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

Definition MEM_readLEST_spec : ident * funspec :=
  DECLARE _MEM_readLEST
  WITH sh: share, p: val, bs: list Z, i: Z
  PRE [ tptr tvoid ]
    PROP (mem_read_pre sh p bs i 8)
    PARAMS (offset_val i p) SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le_field bs i 8)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

(* ---------- error_private.h, zstd_common.c, fse ---------- *)

Definition ERR_isError_spec : ident * funspec :=
  DECLARE _ERR_isError
  WITH c: Z
  PRE [ tulong ]
    PROP (0 <= c <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr c)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if is_error_code c then 1 else 0))) SEP ().

Definition ERR_getErrorCode_spec : ident * funspec :=
  DECLARE _ERR_getErrorCode
  WITH c: Z
  PRE [ tulong ]
    PROP (0 <= c <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr c)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (error_of c))) SEP ().

(* called only under `if (0)` (error_private.h): never executed *)
Definition _force_has_format_string_spec : ident * funspec := (__force_has_format_string, vacuous_funspec (Internal f__force_has_format_string)).

Definition FSE_isError_spec : ident * funspec :=
  DECLARE _FSE_isError
  WITH c: Z
  PRE [ tulong ]
    PROP (0 <= c <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr c)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if is_error_code c then 1 else 0))) SEP ().

Definition ZSTD_isError_spec : ident * funspec :=
  DECLARE _ZSTD_isError
  WITH c: Z
  PRE [ tulong ]
    PROP (0 <= c <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr c)) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if is_error_code c then 1 else 0))) SEP ().

Definition ZSTD_getErrorCode_spec : ident * funspec :=
  DECLARE _ZSTD_getErrorCode
  WITH c: Z
  PRE [ tulong ]
    PROP (0 <= c <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr c)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (error_of c))) SEP ().

(* ---------- bits.h: software bit counting over the De Bruijn tables (zstd_globals) ---------- *)

Definition ZSTD_countTrailingZeros32_fallback_spec : ident * funspec :=
  DECLARE _ZSTD_countTrailingZeros32_fallback
  WITH v: Z, gv: globals
  PRE [ tuint ]
    PROP (0 <= v <= Int.max_unsigned) PARAMS (Vint (Int.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (ctz v))) SEP (zstd_globals gv).

Definition ZSTD_countTrailingZeros32_spec : ident * funspec :=
  DECLARE _ZSTD_countTrailingZeros32
  WITH v: Z, gv: globals
  PRE [ tuint ]
    PROP (0 <= v <= Int.max_unsigned) PARAMS (Vint (Int.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (ctz v))) SEP (zstd_globals gv).

(* 31 - floor(log2 v); 31 for v = 0 *)
Definition ZSTD_countLeadingZeros32_fallback_spec : ident * funspec :=
  DECLARE _ZSTD_countLeadingZeros32_fallback
  WITH v: Z, gv: globals
  PRE [ tuint ]
    PROP (0 <= v <= Int.max_unsigned) PARAMS (Vint (Int.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (31 - Z.log2 v))) SEP (zstd_globals gv).

Definition ZSTD_countLeadingZeros32_spec : ident * funspec :=
  DECLARE _ZSTD_countLeadingZeros32
  WITH v: Z, gv: globals
  PRE [ tuint ]
    PROP (0 <= v <= Int.max_unsigned) PARAMS (Vint (Int.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (31 - Z.log2 v))) SEP (zstd_globals gv).

(* 32 for v = 0 *)
Definition ZSTD_countTrailingZeros64_spec : ident * funspec :=
  DECLARE _ZSTD_countTrailingZeros64
  WITH v: Z, gv: globals
  PRE [ tulong ]
    PROP (0 <= v <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (if v =? 0 then 32 else ctz v))) SEP (zstd_globals gv).

(* highbit v = floor(log2 v); 0 for v = 0 *)
Definition ZSTD_highbit32_spec : ident * funspec :=
  DECLARE _ZSTD_highbit32
  WITH v: Z, gv: globals
  PRE [ tuint ]
    PROP (0 <= v <= Int.max_unsigned) PARAMS (Vint (Int.repr v)) GLOBALS (gv) SEP (zstd_globals gv)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (highbit v))) SEP (zstd_globals gv).

(* ---------- small copies (zstd_internal.h, zstd_decompress_block.c) ----------
   k bytes from offset is of the array cs (held with share shs; ANY contents, undefined bytes
   included: the literal buffer's slack is over-copied) to offset id of the array cd, a separately
   held array (two objects, or two disjoint pieces the caller holds separately). *)
(* the k copied bytes are defined: the copy is libc.c's memcpy, a byte loop (LibcSpec.memcpy_bytes_spec) *)
Definition copy_pre (shs shd: share) (cs cd: list val) (is id k: Z) : Prop :=
  readable_share shs /\ writable_share shd /\ 0 <= is /\ is + k <= Zlength cs /\
  0 <= id /\ id + k <= Zlength cd /\ Forall byte_val (sublist is (is + k) cs).

Definition copied (cs cd: list val) (is id k: Z) : list val :=
  sublist 0 id cd ++ sublist is (is + k) cs ++ sublist (id + k) (Zlength cd) cd.

Definition ZSTD_copy4_spec : ident * funspec :=
  DECLARE _ZSTD_copy4
  WITH shs: share, ps: val, cs: list val, is: Z, shd: share, pd: val, cd: list val, id: Z
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (copy_pre shs shd cs cd is id 4)
    PARAMS (offset_val id pd; offset_val is ps)
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps; data_at shd (tarray tuchar (Zlength cd)) cd pd)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps;
         data_at shd (tarray tuchar (Zlength cd)) (copied cs cd is id 4) pd).

Definition ZSTD_copy8_spec : ident * funspec :=
  DECLARE _ZSTD_copy8
  WITH shs: share, ps: val, cs: list val, is: Z, shd: share, pd: val, cd: list val, id: Z
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (copy_pre shs shd cs cd is id 8)
    PARAMS (offset_val id pd; offset_val is ps)
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps; data_at shd (tarray tuchar (Zlength cd)) cd pd)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps;
         data_at shd (tarray tuchar (Zlength cd)) (copied cs cd is id 8) pd).

Definition ZSTD_copy16_spec : ident * funspec :=
  DECLARE _ZSTD_copy16
  WITH shs: share, ps: val, cs: list val, is: Z, shd: share, pd: val, cd: list val, id: Z
  PRE [ tptr tvoid, tptr tvoid ]
    PROP (copy_pre shs shd cs cd is id 16)
    PARAMS (offset_val id pd; offset_val is ps)
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps; data_at shd (tarray tuchar (Zlength cd)) cd pd)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs (tarray tuchar (Zlength cs)) cs ps;
         data_at shd (tarray tuchar (Zlength cd)) (copied cs cd is id 16) pd).

(* DYNAMIC_BMI2 = 0: the constant 0, for any argument *)
Definition ZSTD_DCtx_get_bmi2_spec : ident * funspec :=
  DECLARE _ZSTD_DCtx_get_bmi2
  WITH d: val
  PRE [ tptr (Tstruct _ZSTD_DCtx_s noattr) ]
    PROP (is_pointer_or_null d) PARAMS (d) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr 0)) SEP ().

Definition Specs_util : funspecs := [
  ZSTD_wrappedPtrAdd_spec;
  ZSTD_wrappedPtrSub_spec;
  ZSTD_maybeNullPtrAdd_spec;
  MEM_32bits_spec;
  MEM_64bits_spec;
  MEM_isLittleEndian_spec;
  MEM_read16_spec;
  MEM_read32_spec;
  MEM_read64_spec;
  MEM_write16_spec;
  MEM_write32_spec;
  MEM_write64_spec;
  MEM_swap32_fallback_spec;
  MEM_swap32_spec;
  MEM_swap64_fallback_spec;
  MEM_swap64_spec;
  MEM_readLE16_spec;
  MEM_readLE24_spec;
  MEM_readLE32_spec;
  MEM_writeLE32_spec;
  MEM_readLE64_spec;
  MEM_readLEST_spec;
  ERR_isError_spec;
  ERR_getErrorCode_spec;
  _force_has_format_string_spec;
  ZSTD_countTrailingZeros32_fallback_spec;
  ZSTD_countTrailingZeros32_spec;
  ZSTD_countLeadingZeros32_fallback_spec;
  ZSTD_countLeadingZeros32_spec;
  ZSTD_countTrailingZeros64_spec;
  ZSTD_highbit32_spec;
  FSE_isError_spec;
  ZSTD_copy8_spec;
  ZSTD_copy16_spec;
  ZSTD_isError_spec;
  ZSTD_getErrorCode_spec;
  ZSTD_DCtx_get_bmi2_spec;
  ZSTD_copy4_spec
].
