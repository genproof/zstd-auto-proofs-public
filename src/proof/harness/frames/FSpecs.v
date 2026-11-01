(* Specifications of the harness helpers of harness/laws_common.h (upto, any_bytes, copy_of, bytes_eq,
   out_of_memory) and of the frame writer of harness/frames.h (put_le, new_frame, new_skippable, join), once
   for all the laws that include them.

   The helpers are static functions of every harness, with the same Clight body in each (the identifiers of
   QuickProof's Clight are computed from their names); the bodies named here are those of the harness
   api_split_invariant, which has all of them; a law checks that its own body is the same term
   (`vm_compute; reflexivity`, FTransfer.v).  Every specification is stated for ANY compspecs cs (no
   composite is involved): FBodies*.v prove the bodies at any cs, and FTransfer.v moves a body into a law's
   context (the law's compspecs, varspecs and funspecs).

   Byte arrays hold `zbytes l` (l: list Z of bytes), as in the decoder's specifications.  ZSTD_XXH64 and
   ZSTD_getErrorCode are called with the decoder's specifications (Spec_xxh, Spec_util), stated at the
   decoder's compspecs; for byte arrays the two compspecs mean the same (HCsConv.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export Zstd.proof.top.HarnessDefs.
Require Zstd.proof.zstd.Spec_xxh.
Require Export Zstd.proof.harness.frames.FModel.
Require Zstd.harness.api_split_invariant.code.

Local Open Scope logic.

Notation zbytes l := (map (fun b : Z => Vint (Int.repr b)) l).

(* the identifiers (the same in every harness) *)
Definition _upto : ident := Zstd.harness.api_split_invariant.code._upto.
Definition _any_bytes : ident := Zstd.harness.api_split_invariant.code._any_bytes.
Definition _copy_of : ident := Zstd.harness.api_split_invariant.code._copy_of.
Definition _bytes_eq : ident := Zstd.harness.api_split_invariant.code._bytes_eq.
Definition _out_of_memory : ident := Zstd.harness.api_split_invariant.code._out_of_memory.
Definition _put_le : ident := Zstd.harness.api_split_invariant.code._put_le.
Definition _new_frame : ident := Zstd.harness.api_split_invariant.code._new_frame.
Definition _new_skippable : ident := Zstd.harness.api_split_invariant.code._new_skippable.
Definition _join : ident := Zstd.harness.api_split_invariant.code._join.
Definition _ZSTD_XXH64 : ident := Zstd.harness.api_split_invariant.code._ZSTD_XXH64.
Definition _ZSTD_getErrorCode : ident := Zstd.harness.api_split_invariant.code._ZSTD_getErrorCode.

(* the bodies *)
Definition f_upto := Zstd.harness.api_split_invariant.code.f_upto.
Definition f_any_bytes := Zstd.harness.api_split_invariant.code.f_any_bytes.
Definition f_copy_of := Zstd.harness.api_split_invariant.code.f_copy_of.
Definition f_bytes_eq := Zstd.harness.api_split_invariant.code.f_bytes_eq.
Definition f_out_of_memory := Zstd.harness.api_split_invariant.code.f_out_of_memory.
Definition f_put_le := Zstd.harness.api_split_invariant.code.f_put_le.
Definition f_new_frame := Zstd.harness.api_split_invariant.code.f_new_frame.
Definition f_new_skippable := Zstd.harness.api_split_invariant.code.f_new_skippable.
Definition f_join := Zstd.harness.api_split_invariant.code.f_join.

(* PTRDIFF_MAX *)
Definition PTRDIFF_MAX : Z := 2 ^ 63 - 1.

(* the object of n bytes at p that malloc returned (NULL: nothing) *)
Definition mbytes {cs: compspecs} (n: Z) (l: list Z) (p: val) : mpred :=
  if eq_dec p nullval then emp
  else malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (zbytes l) p.

Section Specs.
Context {cs: compspecs}.

(* ---------- laws_common.h ---------- *)

(* upto(max): any value from 0 to max *)
Definition upto_spec : ident * funspec :=
  DECLARE _upto
  WITH max: Z
  PRE [ tulong ]
    PROP (0 <= max <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr max)) SEP ()
  POST [ tulong ]
    EX v: Z, PROP (0 <= v <= max) RETURN (Vlong (Int64.repr v)) SEP ().

(* any_bytes(n): NULL, or a new object of n bytes, any bytes *)
Definition any_bytes_spec : ident * funspec :=
  DECLARE _any_bytes
  WITH gv: globals, n: Z
  PRE [ tulong ]
    PROP (0 <= n <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr n)) GLOBALS (gv) SEP (mem_mgr gv)
  POST [ tptr tuchar ]
    EX p: val, EX l: list Z,
    PROP (Zlength l = n; bytes_ok l) RETURN (p) SEP (mem_mgr gv; mbytes n l p).

(* copy_of(source, n): NULL, or a new object holding the n bytes l at source *)
Definition copy_of_spec : ident * funspec :=
  DECLARE _copy_of
  WITH gv: globals, sh: share, p: val, l: list Z
  PRE [ tptr tuchar, tulong ]
    PROP (readable_share sh; bytes_ok l)
    PARAMS (p; Vlong (Int64.repr (Zlength l))) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p)
  POST [ tptr tuchar ]
    EX q: val,
    PROP () RETURN (q)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength l)) (zbytes l) p; mbytes (Zlength l) l q).

(* bytes_eq(a, b, n): 1 if the n bytes la at a equal the n bytes lb at b, else 0 *)
Definition bytes_eq_spec : ident * funspec :=
  DECLARE _bytes_eq
  WITH sha: share, a: val, la: list Z, shb: share, b: val, lb: list Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; bytes_ok la; bytes_ok lb; Zlength la = Zlength lb)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (data_at sha (tarray tuchar (Zlength la)) (zbytes la) a;
         data_at shb (tarray tuchar (Zlength lb)) (zbytes lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (if list_eq_dec Z.eq_dec la lb then Int.one else Int.zero))
    SEP (data_at sha (tarray tuchar (Zlength la)) (zbytes la) a;
         data_at shb (tarray tuchar (Zlength lb)) (zbytes lb) b).

(* out_of_memory(result): 1 iff result is the error code memory_allocation (64) *)
Definition out_of_memory_spec : ident * funspec :=
  DECLARE _out_of_memory
  WITH r: Z
  PRE [ tulong ]
    PROP (0 <= r <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr r)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (if Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r) 64 then Int.one else Int.zero))
    SEP ().

(* ---------- frames.h ---------- *)

(* put_le(p + i, v, k): the k-byte little-endian encoding of v at offset i of an array with any contents *)
Definition put_le_spec : ident * funspec :=
  DECLARE _put_le
  WITH sh: share, p: val, c: list val, i: Z, v: Z, k: Z
  PRE [ tptr tuchar, tulong, tulong ]
    PROP (writable_share sh; 0 <= i; 0 <= k <= 8; i + k <= Zlength c; 0 <= v <= Int64.max_unsigned)
    PARAMS (offset_val i p; Vlong (Int64.repr v); Vlong (Int64.repr k))
    SEP (data_at sh (tarray tuchar (Zlength c)) c p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar (Zlength c)) (Zstd.proof.zstd.Spec_util.mem_written c i k v) p).

(* new_frame(data, n, fcs, max_window, dict_id, len), d the n bytes at data.  NULL (out of memory: the
   data then holds some n bytes d', *len anything), or a new object of *len bytes holding the frame
   nf_bytes d fcs dict_id c for some choices c with nf_ok, the data then being nf_data d c (RLE blocks).
   A frame comes only for n <= (PTRDIFF_MAX - 26) / 4 (the test before new_frame's malloc), so it has at most
   26 + 4 n <= PTRDIFF_MAX bytes (FFacts.nf_bytes_length).
   A run where the chosen window is above max_window is not continued (gp_assume).  For n = 0 the caller
   lends a resource w that makes data a weakly valid pointer (ZSTD_XXH64 compares it with NULL). *)
Definition new_frame_spec : ident * funspec :=
  DECLARE _new_frame
  WITH gv: globals, sh: share, p: val, d: list Z, fcs: Z, maxw: Z, did: Z, shl: share, lp: val,
       w: Zstd.proof.zstd.Spec_xxh.ptr_witness
  PRE [ tptr tuchar, tulong, tulong, tulong, tuint, tptr tulong ]
    PROP (writable_share sh; writable_share shl; bytes_ok d; Zlength d <= Int64.max_unsigned;
          0 <= fcs <= Int64.max_unsigned; 0 <= maxw <= Int64.max_unsigned; 0 <= did <= Int.max_unsigned;
          Zlength d = 0 -> (Zstd.proof.zstd.Spec_xxh.pw_pred w |-- weak_valid_pointer p))
    PARAMS (p; Vlong (Int64.repr (Zlength d)); Vlong (Int64.repr fcs); Vlong (Int64.repr maxw);
            Vint (Int.repr did); lp)
    GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength d)) (zbytes d) p;
         Zstd.proof.zstd.Spec_xxh.pw_pred w; data_at_ shl tulong lp)
  POST [ tptr tuchar ]
    EX q: val, EX d': list Z,
    PROP (Zlength d' = Zlength d; bytes_ok d')
    RETURN (q)
    SEP (mem_mgr gv; data_at sh (tarray tuchar (Zlength d)) (zbytes d') p;
         Zstd.proof.zstd.Spec_xxh.pw_pred w;
         if eq_dec q nullval then data_at_ shl tulong lp
         else EX c: nf_choice,
              !! (nf_ok (Zlength d) fcs maxw did c /\ d' = nf_data d c /\ Zlength d <= (PTRDIFF_MAX - 26) / 4) &&
              (data_at shl tulong (Vlong (Int64.repr (Zlength (nf_bytes d fcs did c)))) lp *
               mbytes (Zlength (nf_bytes d fcs did c)) (nf_bytes d fcs did c) q)).

(* new_skippable(len): NULL (out of memory; *len untouched), or a new object of *len bytes holding a skippable
   frame with any of the 16 magic numbers and any user data of any length up to 2^32 - 1 *)
Definition new_skippable_spec : ident * funspec :=
  DECLARE _new_skippable
  WITH gv: globals, shl: share, lp: val
  PRE [ tptr tulong ]
    PROP (writable_share shl) PARAMS (lp) GLOBALS (gv) SEP (mem_mgr gv; data_at_ shl tulong lp)
  POST [ tptr tuchar ]
    EX q: val,
    PROP () RETURN (q)
    SEP (mem_mgr gv;
         if eq_dec q nullval then data_at_ shl tulong lp
         else EX k: Z, EX u: list Z,
              !! (0 <= k < 16 /\ Zlength u <= 4294967295 /\ bytes_ok u) &&
              (data_at shl tulong (Vlong (Int64.repr (Zlength (sk_bytes k u)))) lp *
               mbytes (Zlength (sk_bytes k u)) (sk_bytes k u) q)).

(* join(a, a_len, b, b_len): frees a and b (objects of malloc, or NULL) and returns NULL or a new object
   holding la ++ lb; NULL also when a is NULL with a_len > 0 (same for b).  The two lengths must add up to
   less than 2^64: the test a_len <= PTRDIFF_MAX - b_len is computed in size_t and wraps, so it does not
   exclude a sum a_len + b_len that wraps to a small size given to malloc.  A new object also means
   a_len + b_len <= PTRDIFF_MAX when b_len is (what keeps a series that grows by join within PTRDIFF_MAX) *)
Definition join_spec : ident * funspec :=
  DECLARE _join
  WITH gv: globals, a: val, la: list Z, b: val, lb: list Z
  PRE [ tptr tuchar, tulong, tptr tuchar, tulong ]
    PROP (bytes_ok la; bytes_ok lb; Zlength la <= Int64.max_unsigned; Zlength lb <= Int64.max_unsigned;
          Zlength la + Zlength lb <= Int64.max_unsigned)
    PARAMS (a; Vlong (Int64.repr (Zlength la)); b; Vlong (Int64.repr (Zlength lb))) GLOBALS (gv)
    SEP (mem_mgr gv; mbytes (Zlength la) la a; mbytes (Zlength lb) lb b)
  POST [ tptr tuchar ]
    EX q: val,
    PROP (q <> nullval -> Zlength lb <= PTRDIFF_MAX -> Zlength la + Zlength lb <= PTRDIFF_MAX)
    RETURN (q) SEP (mem_mgr gv; mbytes (Zlength la + Zlength lb) (la ++ lb) q).

(* ---------- the functions each body calls, at cs ---------- *)

Definition malloc_e : ident * funspec := (_quickproof_malloc, malloc_spec').
Definition free_e : ident * funspec := (_quickproof_free, free_spec').

Definition G_upto : funspecs := [nondet_size_spec].
Definition G_any_bytes : funspecs := [malloc_e; nondet_bytes_nn_spec].
Definition G_copy_of : funspecs := [malloc_e].
Definition G_bytes_eq : funspecs := [].
Definition G_out_of_memory : funspecs := [Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec].
Definition G_put_le : funspecs := [].
Definition G_new_frame : funspecs :=
  [malloc_e; free_e; nondet_u8_spec; gp_assume_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec;
   upto_spec; copy_of_spec; put_le_spec].
Definition G_new_skippable : funspecs := [malloc_e; nondet_u8_spec; nondet_bytes_nn_spec; upto_spec; put_le_spec].
Definition G_join : funspecs := [malloc_e; free_e].

End Specs.
