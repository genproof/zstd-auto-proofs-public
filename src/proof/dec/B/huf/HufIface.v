(* Group HUF of subtree B: the specifications its sub-groups export to each other.
   Fixed: each sub-group is proved against these specifications.

   Sub-groups (HufGroups.v): X1T (X1 table), X2T (X2 table), X1D (X1 decoders), X2D (X2 decoders), TOP
   (descriptor, selectors, DCtx/usingDTable entry points, dead fast loops). *)
Require Export Zstd.proof.dec.B.BGroups.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* ---------- the table, by type ---------- *)

(* BRep.hufdt_x_at: hufdt_at with the table type fixed *)
Lemma hufdt_at_x (sh: share) (ht: huf_table) (p: val) :
  hufdt_at sh ht p = EX x2: bool, hufdt_x_at x2 sh ht p.
Proof. reflexivity. Qed.

(* ---------- the descriptor ---------- *)

(* HUF_getDTableDesc(dtd, table): copies the 4-byte descriptor (any contents) *)
Definition HUF_getDTableDesc_spec : ident * funspec :=
  DECLARE _HUF_getDTableDesc
  WITH shd: share, q: val, sh: share, p: val, v: reptype t_dtdesc
  PRE [ tptr t_dtdesc, tptr tuint ]
    PROP (writable_share shd; readable_share sh;
          (* the descriptor's bytes are defined: the copy is libc.c's memcpy *)
          memcpy_ok t_dtdesc v)
    PARAMS (q; p)
    SEP (data_at_ shd t_dtdesc q; data_at sh t_dtdesc v p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shd t_dtdesc v q; data_at sh t_dtdesc v p).

(* ---------- building an X1 table (exported by X1T) ---------- *)

(* HUF_readDTableX1_wksp(DTable, src, srcSize, workSpace, wkspSize, flags = 0): as
   HUF_readDTableX2_wksp_spec (C-result form), an X1 table; exactly: res is ExHuf.x_readstats s *)
Definition HUF_readDTableX1_wksp_spec : ident * funspec :=
  DECLARE _HUF_readDTableX1_wksp
  WITH gv: globals, shd: share, dt: val, sh: share, base: val, N: Z, c: list val, off: Z, s: list Z,
       shk: share, pk: val, nk: Z
  PRE [ tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (writable_share shd; writable_share shk; 640 <= nk <= 4096; win_ok sh N c off (Zlength s) s)
    PARAMS (dt; offset_val off base; Vlong (Int64.repr (Zlength s)); pk; Vlong (Int64.repr (4 * nk));
            Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; hufhdr_at shd dt; data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX res: option (huf_table * Z),
    PROP (0 <= r <= Int64.max_unsigned;
          forall x, huf_parse_desc s = Some x -> res = Some x;
          match res with Some (ht, size) => r = size /\ 1 <= size <= Zlength s | None => is_error_code r = true end;
          res = x_readstats s)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv;
         match res with Some (ht, size) => hufdt_x_at false shd ht dt | None => hufhdr_at shd dt end;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

(* ---------- decoding with a table of a known type (exported by X1D, X2D) ---------- *)

(* the internal decoders (dst, dstSize, cSrc, cSrcSize, DTable, flags = 0): huf_using_spec with the
   table type fixed, and a nonempty output array (the decoders compare p < pEnd: weak_valid_pointer); exactly
   (last PROP): the outcome of ExHuf.x_huf_decode on xhuf_of x2 ht *)
Definition huf_x_using_spec (four x2: bool) : funspec :=
  WITH gv: globals, sht: share, dt: val, ht: huf_table, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint, tint ]
    PROP (readable_share sht; writable_share sho; 1 <= Zlength oc;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s)); dt;
            Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; hufdt_x_at x2 sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n; (byte_cells oc -> byte_cells oc');
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits_with four ht s n with
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end;
          match x_huf_decode (xhuf_of x2 ht) (negb four) s n with
          | None => is_error_code r = true
          | Some l => r = n /\ sublist d (d + n) oc' = zbytes l
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; hufdt_x_at x2 sht ht dt; data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base).

Definition HUF_decompress1X1_usingDTable_internal_spec : ident * funspec :=
  DECLARE _HUF_decompress1X1_usingDTable_internal huf_x_using_spec false false.
Definition HUF_decompress4X1_usingDTable_internal_spec : ident * funspec :=
  DECLARE _HUF_decompress4X1_usingDTable_internal huf_x_using_spec true false.
Definition HUF_decompress1X2_usingDTable_internal_spec : ident * funspec :=
  DECLARE _HUF_decompress1X2_usingDTable_internal huf_x_using_spec false true.
Definition HUF_decompress4X2_usingDTable_internal_spec : ident * funspec :=
  DECLARE _HUF_decompress4X2_usingDTable_internal huf_x_using_spec true true.

(* ---------- the dead fast loops (HUF_DISABLE_FAST_DECODE: only in `if (0)` branches) ---------- *)

Definition HUF_getDTableLog_spec : ident * funspec :=
  (_HUF_getDTableLog, vacuous_funspec (Internal f_HUF_getDTableLog)).
Definition HUF_initFastDStream_spec : ident * funspec :=
  (_HUF_initFastDStream, vacuous_funspec (Internal f_HUF_initFastDStream)).
Definition HUF_DecompressFastArgs_init_spec : ident * funspec :=
  (_HUF_DecompressFastArgs_init, vacuous_funspec (Internal f_HUF_DecompressFastArgs_init)).
Definition HUF_initRemainingDStream_spec : ident * funspec :=
  (_HUF_initRemainingDStream, vacuous_funspec (Internal f_HUF_initRemainingDStream)).
Definition HUF_decompress4X1_usingDTable_internal_fast_c_loop_spec : ident * funspec :=
  (_HUF_decompress4X1_usingDTable_internal_fast_c_loop,
   vacuous_funspec (Internal f_HUF_decompress4X1_usingDTable_internal_fast_c_loop)).
Definition HUF_decompress4X1_usingDTable_internal_fast_spec : ident * funspec :=
  (_HUF_decompress4X1_usingDTable_internal_fast,
   vacuous_funspec (Internal f_HUF_decompress4X1_usingDTable_internal_fast)).
Definition HUF_decompress4X2_usingDTable_internal_fast_c_loop_spec : ident * funspec :=
  (_HUF_decompress4X2_usingDTable_internal_fast_c_loop,
   vacuous_funspec (Internal f_HUF_decompress4X2_usingDTable_internal_fast_c_loop)).
Definition HUF_decompress4X2_usingDTable_internal_fast_spec : ident * funspec :=
  (_HUF_decompress4X2_usingDTable_internal_fast,
   vacuous_funspec (Internal f_HUF_decompress4X2_usingDTable_internal_fast)).
