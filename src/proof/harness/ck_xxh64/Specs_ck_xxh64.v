(* Specifications of the functions of harness/ck_xxh64.c besides main (and of the helpers upto and any_bytes of
   harness/laws_common.h it includes), and the context their bodies are proved in.  The API the harness imports
   is ZSTD_XXH64 alone (Spec_xxh.ZSTD_XXH64_spec).  The harness's own XXH64 (xxh64 and its pieces rotl, le,
   round64, merge) is specified against the model's XXH64 (src/proof/model/Xxh64.v), which the decoder's
   specification of ZSTD_XXH64 also returns: the law's gp_assert holds by the two specifications. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_xxh.
Require Export Zstd.proof.harness.ck_xxh64.HOK_ck_xxh64.

(* the API of the law: zstd's XXH64 *)
Definition API : funspecs := [ZSTD_XXH64_spec].

(* upto(max): any value from 0 to max *)
Definition upto_spec : ident * funspec :=
  DECLARE _upto
  WITH max: Z
  PRE [ tulong ]
    PROP (0 <= max <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr max)) SEP ()
  POST [ tulong ] EX v: Z,
    PROP (0 <= v <= max) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_bytes(n): NULL, or a new object of n arbitrary bytes *)
Definition any_bytes_spec : ident * funspec :=
  DECLARE _any_bytes
  WITH n: Z, gv: globals
  PRE [ tulong ]
    PROP (0 <= n <= Ptrofs.max_unsigned) PARAMS (Vlong (Int64.repr n)) GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tptr tuchar ] EX p: val, EX bs: list Z,
    PROP (Zlength bs = n; bytes_ok bs)
    RETURN (p)
    SEP (mem_mgr gv;
         if eq_dec p nullval then emp
         else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (zbytes bs) p).

(* rotl(x, r) = x <<< r *)
Definition rotl_spec : ident * funspec :=
  DECLARE _rotl
  WITH x: Z, r: Z
  PRE [ tulong, tint ]
    PROP (0 <= x <= Int64.max_unsigned; 1 <= r <= 63)
    PARAMS (Vlong (Int64.repr x); Vint (Int.repr r)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (rotl64 x r))) SEP ().

(* le(p, size): the little-endian value of the size bytes at p = base + i, of the array all at base *)
Definition le_spec : ident * funspec :=
  DECLARE _le
  WITH sh: share, base: val, all: list Z, i: Z, k: Z
  PRE [ tptr tuchar, tint ]
    PROP (readable_share sh; bytes_ok all; 0 <= i; 0 <= k <= 8; i + k <= Zlength all)
    PARAMS (offset_val i base; Vint (Int.repr k))
    SEP (data_at sh (tarray tuchar (Zlength all)) (zbytes all) base)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le_field all i k)))
    SEP (data_at sh (tarray tuchar (Zlength all)) (zbytes all) base).

(* round64(acc, lane): the model's XXH64 round *)
Definition round64_spec : ident * funspec :=
  DECLARE _round64
  WITH acc: Z, lane: Z
  PRE [ tulong, tulong ]
    PROP (0 <= acc <= Int64.max_unsigned; 0 <= lane <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr acc); Vlong (Int64.repr lane)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (xxh_round acc lane))) SEP ().

(* merge(acc, accn): the model's merge of an accumulator *)
Definition merge_spec : ident * funspec :=
  DECLARE _merge
  WITH acc: Z, accn: Z
  PRE [ tulong, tulong ]
    PROP (0 <= acc <= Int64.max_unsigned; 0 <= accn <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr acc); Vlong (Int64.repr accn)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (xxh_merge acc accn))) SEP ().

(* xxh64(p, len, seed): the model's XXH64 of the len bytes at p *)
Definition xxh64_spec : ident * funspec :=
  DECLARE _xxh64
  WITH sh: share, p: val, bs: list Z, seed: Z
  PRE [ tptr tuchar, tulong, tulong ]
    PROP (readable_share sh; bytes_ok bs; Zlength bs <= Int64.max_unsigned; 0 <= seed <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr (Zlength bs)); Vlong (Int64.repr seed))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (xxh64 bs seed)))
    SEP (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) p).

(* in the order of helper_ids *)
Definition Hs : funspecs :=
  [ any_bytes_spec; merge_spec; upto_spec; xxh64_spec; le_spec; round64_spec; rotl_spec ].

Lemma Hs_ids : map fst Hs = helper_ids.
Proof. vm_compute. reflexivity. Qed.

(* the context of the bodies *)
Definition G : funspecs := Gprog API Hs.
