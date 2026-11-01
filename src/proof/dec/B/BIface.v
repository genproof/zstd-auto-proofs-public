(* Subtree B: the specifications its groups export to each other.  Fixed: each group is proved against
   these specifications.

   Groups (BGroups.v):
   - ENT  (FSE + Huffman weights): FSE_readNCount, ZSTD_buildFSETable, HUF_readStats_wksp;
   - HUF  (Huffman tables and decoders): HUF_readDTableX2_wksp, HUF_decompress1X1_DCtx_wksp,
          HUF_decompress4X_hufOnly_wksp, HUF_decompress1X_usingDTable, HUF_decompress4X_usingDTable;
   - BLK  (literals, sequence headers, sequences, ZSTD_decompressBlock_internal): DecIface's block spec;
   - DICT (ZSTD_decompressBegin*, dictionaries' entropy, DDicts): DecIface's begin / DDict specs.

   Input bytes are windows of a byte array (DecIface.win_ok): n bytes s at offset off of an array of N cells
   c at base.  Output byte regions: n bytes at offset d of an array of N cells oc at ob (any contents). *)
Require Export Zstd.proof.dec.B.BRep.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* ---------- model side ---------- *)

(* a normalized distribution zstd's FSE_readNCount accepts (model read_ncount): accuracy log, at most max+1
   counts, each >= -1, the probabilities (a -1 counts 1) summing to 2^log *)
Definition ncount_ok (norm: list Z) (log max: Z) : Prop :=
  5 <= log <= 15 /\ 1 <= Zlength norm <= max + 1 /\ Forall (fun c => -1 <= c <= 2 ^ log) norm /\
  fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) norm) = 2 ^ log.

(* the literals of a Huffman-compressed literals section cb (tree description, then 1 or 4 streams) that
   regenerates n bytes (model Block.decode_literals, set_compressed) *)
Definition huf_lits (four: bool) (cb: list Z) (n: Z) : option (huf_table * list Z) :=
  match huf_parse_desc cb with
  | None => None
  | Some (t, h) =>
      if h >=? Zlength cb then None else
      match (if four then huf_decode_4streams t (skipn (Z.to_nat h) cb) n
             else huf_decode_stream t (skipn (Z.to_nat h) cb) n) with
      | Some l => Some (t, l)
      | None => None
      end
  end.

(* the same with an existing table (set_repeat) *)
Definition huf_lits_with (four: bool) (t: huf_table) (cb: list Z) (n: Z) : option (list Z) :=
  if four then huf_decode_4streams t cb n else huf_decode_stream t cb n.

(* rankStats of HUF_readStats: the number of symbols of each weight 0..12 *)
Definition rank_stats (ws: list Z) : list val :=
  map (fun w => Vint (Int.repr (Zlength (filter (fun x => x =? Z.of_nat w) ws)))) (seq 0 13).

(* an output region after a call: changed only in [d, d+n) *)
Definition out_after (oc oc': list val) (d n: Z) : Prop :=
  Zlength oc' = Zlength oc /\ unchanged_outside oc oc' d (d + n).

(* ---------- ENT ---------- *)

(* FSE_readNCount(normalizedCounter, maxSVPtr, tableLogPtr, headerBuffer, hbSize): the description at the
   start of the window s, read with largest symbol maxsv.  zstd's result res: the model's read_ncount when it
   reads the description (C is more lenient than the model on truncated descriptions); on success a valid distribution
   within s, the counts in front of the counter array
   (for log <= 9: C stores a count 2^15 as a negative short), *maxSVPtr = last symbol, *tableLogPtr = log.
   Windows of any length (code fix F11: the zero-repeat scan stops once charnum reaches maxSV1, so C's unsigned
   charnum cannot wrap).  Exactly: res is ExHuf.x_ncount s maxsv, zstd's own reading on every window
   (FSE_readNCount_body, on a zero-padded 8-byte copy below 8 bytes). *)
Definition FSE_readNCount_spec : ident * funspec :=
  DECLARE _FSE_readNCount
  WITH gv: globals, shn: share, pn: val, nn: Z, shm: share, pm: val, sht: share, pt: val, maxsv: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tshort, tptr tuint, tptr tuint, tptr tvoid, tulong ]
    PROP (writable_share shn; writable_share shm; writable_share sht; 0 <= maxsv <= 255; maxsv + 1 <= nn <= 256;
          Zlength s <= 2 ^ 63 - 1; win_ok sh N c off (Zlength s) s)
    PARAMS (pn; pm; pt; offset_val off base; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shn (tarray tshort nn) pn; data_at shm tuint (Vint (Int.repr maxsv)) pm;
         data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX nc: list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength nc = nn;
          forall x, read_ncount s maxsv = Some x -> res = Some x;
          match res with
          | Some (norm, log, size) =>
              r = size /\ size <= Zlength s /\ ncount_ok norm log maxsv /\
              (log <= 9 -> sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm)
          | None => is_error_code r = true
          end;
          res = ExHuf.x_ncount s maxsv)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shn (tarray tshort nn) nc pn;
         match res with
         | Some (norm, log, size) =>
             data_at shm tuint (Vint (Int.repr (Zlength norm - 1))) pm * data_at sht tuint (Vint (Int.repr log)) pt
         | None => data_at_ shm tuint pm * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base).

(* ZSTD_buildFSETable(dt, normalizedCounter, maxSymbolValue, baseValue, nbAdditionalBits, tableLog, wksp,
   wkspSize, bmi2): the decoding table of kind k (base and extra-bits tables of the globals) of a valid
   distribution, in the table field dt. *)
Definition ZSTD_buildFSETable_spec : ident * funspec :=
  DECLARE _ZSTD_buildFSETable
  WITH gv: globals, k: seqkind, shd: share, dt: val, shn: share, pn: val, nc: list val, norm: list Z, log: Z,
       shw: share, pw: val, nw: Z
  PRE [ tptr t_seqSymbol, tptr tshort, tuint, tptr tuint, tptr tuchar, tuint, tptr tvoid, tulong, tint ]
    PROP (writable_share shd; readable_share shn; writable_share shw;
          ncount_ok norm log (sk_max k); log <= sk_maxlog k;
          Zlength norm <= Zlength nc; sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm;
          157 <= nw <= 640)
    PARAMS (dt; pn; Vint (Int.repr (Zlength norm - 1)); gv (sk_gbase k); gv (sk_gbits k); Vint (Int.repr log);
            pw; Vlong (Int64.repr (4 * nw)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shd (tarray t_seqSymbol (sk_size k)) dt;
         data_at shn (tarray tshort (Zlength nc)) nc pn; data_at_ shw (tarray tuint nw) pw)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (zstd_globals gv; seqspace_at shd k (Some (fse_build norm log)) dt;
         data_at shn (tarray tshort (Zlength nc)) nc pn; data_at_ shw (tarray tuint nw) pw).

(* HUF_readStats_wksp(huffWeight, 256, rankStats, nbSymbolsPtr, tableLogPtr, src, srcSize, workSpace,
   wkspSize = 876, flags = 0) (both callers pass the 219 U32 statsWksp; C's result depends on it): the tree
   description at the start of the window s.  zstd's result res: the model's huf_parse_desc when it parses
   the description; on success the weights (the implied last one included) in front of huffWeight, their
   counts per weight 0..12 in rankStats, their number, the table log.  Exactly: res is ExHuf.x_readstats s. *)
Definition HUF_readStats_wksp_spec : ident * funspec :=
  DECLARE _HUF_readStats_wksp
  WITH gv: globals, shw: share, pw: val, shr: share, pr: val, shs: share, ps: val, sht: share, pt: val,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, shk: share, pk: val
  PRE [ tptr tuchar, tulong, tptr tuint, tptr tuint, tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (writable_share shw; writable_share shr; writable_share shs; writable_share sht; writable_share shk;
          win_ok sh N c off (Zlength s) s)
    PARAMS (pw; Vlong (Int64.repr 256); pr; ps; pt; offset_val off base; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (4 * 219)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shw (tarray tuchar 256) pw; data_at_ shr (tarray tuint 13) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint 219) pk)
  POST [ tulong ]
    EX r: Z, EX wc: list val, EX res: option (huf_table * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength wc = 256;
          forall x, huf_parse_desc s = Some x -> res = Some x;
          match res with
          | Some (ht, size) =>
              r = size /\ 1 <= size <= Zlength s /\ huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\
              Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht) /\
              sublist 0 (Zlength (ht_weights ht)) wc = map (fun x => Vint (Int.repr x)) (ht_weights ht)
          | None => is_error_code r = true
          end;
          res = x_readstats s)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         match res with
         | Some (ht, size) =>
             data_at shr (tarray tuint 13) (rank_stats (ht_weights ht)) pr *
             data_at shs tuint (Vint (Int.repr (Zlength (ht_weights ht)))) ps *
             data_at sht tuint (Vint (Int.repr (ht_log ht))) pt
         | None => data_at_ shr (tarray tuint 13) pr * data_at_ shs tuint ps * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint 219) pk).

Definition ENT_exports : funspecs := [ FSE_readNCount_spec; ZSTD_buildFSETable_spec; HUF_readStats_wksp_spec ].

(* ---------- HUF ---------- *)

(* the Huffman table field after a call that builds a table of type x2 from the description at the start of
   s: on success the table zstd parses (ExHuf.x_readstats; the model's when it decodes), on an error anything *)
Definition huf_built (shd: share) (r: Z) (om: option huf_table) (x2: bool) (s: list Z) (dt: val) : mpred :=
  if is_error_code r then memory_block shd (4 + HUF_CELLBYTES) dt
  else EX ht: huf_table,
       !! (match om with Some t => ht = t | None => True end /\ exists h, x_readstats s = Some (ht, h)) &&
       hufdt_x_at x2 shd ht dt.

(* HUF_readDTableX2_wksp(DTable, src, srcSize, workSpace, wkspSize, flags = 0) (ZSTD_loadDEntropy: the
   workspace is the three sequence tables): zstd's result res is huf_parse_desc's when the model parses the
   description (readStats); an X2 table (hufdt_x_at true).  Exactly: res is ExHuf.x_readstats s (so the table
   is ExHuf.x_huf_read true s's). *)
Definition HUF_readDTableX2_wksp_spec : ident * funspec :=
  DECLARE _HUF_readDTableX2_wksp
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
         match res with Some (ht, size) => hufdt_x_at true shd ht dt | None => hufhdr_at shd dt end;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

(* HUF_decompress1X1_DCtx_wksp / HUF_decompress4X_hufOnly_wksp(DTable, dst, dstSize, cSrc, cSrcSize,
   workSpace, wkspSize, flags = 0): build a table from the description in front of the window s, decode n
   bytes (1 stream / 4 streams) into ob[d, d+n).  Any bytes: an error, or n defined bytes and a table; when
   the model decodes: success with exactly its literals and its table.  Exactly (last PROP): the table type is
   huf_dctx_x2 (X1 for one stream, HUF_selectDecoder's choice for four), and the outcome is ExHuf.xh_dctx's:
   an error iff it fails, else its n bytes; the table is the one zstd parses (huf_built). *)
Definition huf_dctx_x2 (four: bool) (n: Z) (s: list Z) : bool :=
  if four then x_huf_select n (Zlength s) else false.

Definition huf_dctx_spec (four: bool) : funspec :=
  WITH gv: globals, shd: share, dt: val, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (writable_share shd; writable_share sho; writable_share shk; 640 <= nk <= 4096;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc; 1 <= Zlength oc;
          Zlength s <= ZSTD_BLOCKSIZE_MAX; win_ok sh N c off (Zlength s) s)
    PARAMS (dt; offset_val d ob; Vlong (Int64.repr n); offset_val off base; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (4 * nk)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; hufhdr_at shd dt; data_at sho (tarray tuchar (Zlength oc)) oc ob;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; out_after oc oc' d n; (byte_cells oc -> byte_cells oc');
          is_error_code r = false -> r = n /\ exists l, sublist d (d + n) oc' = zbytes l /\ bytes_ok l;
          match huf_lits four s n with
          | Some (t, l) => r = n /\ sublist d (d + n) oc' = zbytes l
          | None => True
          end;
          match xh_dctx (huf_dctx_x2 four n s) (negb four) s n with
          | None => is_error_code r = true
          | Some (l, _) => r = n /\ sublist d (d + n) oc' = zbytes l
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; huf_built shd r (option_map fst (huf_lits four s n)) (huf_dctx_x2 four n s) s dt;
         data_at sho (tarray tuchar (Zlength oc)) oc' ob;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

Definition HUF_decompress1X1_DCtx_wksp_spec : ident * funspec :=
  DECLARE _HUF_decompress1X1_DCtx_wksp huf_dctx_spec false.
Definition HUF_decompress4X_hufOnly_wksp_spec : ident * funspec :=
  DECLARE _HUF_decompress4X_hufOnly_wksp huf_dctx_spec true.

(* HUF_decompress1X_usingDTable / HUF_decompress4X_usingDTable(dst, maxDstSize, cSrc, cSrcSize, DTable,
   flags = 0): decode n bytes with the existing table ht of type x2 (the context's or a DDict's, X1 or X2).
   Exactly (last PROP): the outcome of ExHuf.x_huf_decode on the table xhuf_of x2 ht. *)
Definition huf_using_spec (four: bool) : funspec :=
  WITH gv: globals, sht: share, dt: val, ht: huf_table, x2: bool, sho: share, ob: val, oc: list val, d: Z, n: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint, tint ]
    PROP (readable_share sht; writable_share sho;
          0 <= d; (if four then 6 else 0) <= n <= ZSTD_BLOCKSIZE_MAX; d + n <= Zlength oc; 1 <= Zlength oc;
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

Definition HUF_decompress1X_usingDTable_spec : ident * funspec :=
  DECLARE _HUF_decompress1X_usingDTable huf_using_spec false.
Definition HUF_decompress4X_usingDTable_spec : ident * funspec :=
  DECLARE _HUF_decompress4X_usingDTable huf_using_spec true.

Definition HUF_exports : funspecs :=
  [ HUF_readDTableX2_wksp_spec; HUF_decompress1X1_DCtx_wksp_spec; HUF_decompress4X_hufOnly_wksp_spec;
    HUF_decompress1X_usingDTable_spec; HUF_decompress4X_usingDTable_spec ].

(* ---------- BLK, DICT: the exports of DecIface with B's predicates ---------- *)

Definition BLK_exports : funspecs := [ ZSTD_decompressBlock_internal_spec dent_def tabs_def ].

Definition DICT_exports : funspecs :=
  [ ZSTD_decompressBegin_usingDict_spec tabs_def; ZSTD_decompressBegin_usingDDict_spec dent_def tabs_def;
    ZSTD_initDDict_internal_spec dent_def; ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec ].
