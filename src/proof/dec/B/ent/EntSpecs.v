(* Group ENT of subtree B: the specifications of its functions.  Exports
   (BIface.v): FSE_readNCount_spec, ZSTD_buildFSETable_spec, HUF_readStats_wksp_spec. *)
Require Export Zstd.proof.dec.B.BGroups Zstd.proof.dec.B.ent.EntModel.
Require Export Zstd.proof.model.ExHuf.
Local Open Scope logic.

(* on >= 8 bytes the specifications' ncount_res is zstd's exact reading *)
Lemma ncount_res_x (s: list Z) (maxsv: Z) : 8 <= Zlength s -> ncount_res s maxsv = x_ncount s maxsv.
Proof.
  intros H. rewrite x_ncount_ge8 by exact H. unfold ncount_res.
  destruct (Zlength s <? 8) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity].
Qed.

(* the exact reading on >= 8 bytes is the one nc_rel fixes *)
Lemma nc_rel_x (s: list Z) (maxsv: Z) res : 8 <= Zlength s -> nc_rel s maxsv res -> res = x_ncount s maxsv.
Proof.
  intros H Hr. unfold nc_rel in Hr. destruct (Zlength s <? 8) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite Hr. apply ncount_res_x; exact H.
Qed.

Definition t_fdec : type := Tstruct ___gp_FSE_decode_t noattr.
Definition t_fhdr : type := Tstruct ___gp_FSE_DTableHeader noattr.
Definition t_dstate : type := Tstruct ___gp_FSE_DState_t noattr.
Definition t_bitd : type := Tstruct ___gp_BIT_DStream_t noattr.

#[export] Instance Inhabitant_fse_entry : Inhabitant fse_entry := {| fe_sym := 0; fe_nb := 0; fe_base := 0 |}.

(* ---------- the FSE decoding table of FSE_buildDTable_internal (an FSE_DTable: U32s) ---------- *)

(* FSE_decode_t {newState; symbol; nbBits} of a model cell *)
Definition fdcell (e: fse_entry) : val * (val * val) :=
  (Vint (Int.repr (fe_base e)), (Vint (Int.repr (fe_sym e)), Vint (Int.repr (fe_nb e)))).

Definition fse_dt_ok (t: fse_table) : Prop :=
  1 <= ft_log t <= 12 /\ Zlength (ft_cells t) = 2 ^ ft_log t /\
  Forall (fun e => 0 <= fe_sym e < 256 /\ 0 <= fe_nb e <= ft_log t /\
                   0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ ft_log t) (ft_cells t).

(* the table at dt: header {tableLog; fastMode = fm} in the first U32, then the 2^log cells *)
Definition fsedt_at (sh: share) (t: fse_table) (fm: Z) (dt: val) : mpred :=
  !! (fse_dt_ok t /\ (fm = 0 \/ fm = 1)) &&
  (data_at sh t_fhdr (Vint (Int.repr (ft_log t)), Vint (Int.repr fm)) dt *
   data_at sh (tarray t_fdec (2 ^ ft_log t)) (map fdcell (ft_cells t)) (offset_val 4 dt)).

(* ---------- FSE decoding ---------- *)

(* FSE_decode_copy(dst, &table[i]) *)
Definition FSE_decode_copy_spec : ident * funspec :=
  DECLARE _FSE_decode_copy
  WITH shs: share, tb: val, es: list fse_entry, i: Z, shd: share, dst: val
  PRE [ tptr t_fdec, tptr t_fdec ]
    PROP (readable_share shs; writable_share shd; 0 <= i < Zlength es)
    PARAMS (dst; offset_val (4 * i) tb)
    SEP (data_at shs (tarray t_fdec (Zlength es)) (map fdcell es) tb; data_at_ shd t_fdec dst)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs (tarray t_fdec (Zlength es)) (map fdcell es) tb; data_at shd t_fdec (fdcell (Znth i es)) dst).

(* FSE_initDState(DStatePtr, bitD, dt): state = the next log bits, then a reload *)
Definition FSE_initDState_spec : ident * funspec :=
  DECLARE _FSE_initDState
  WITH shs: share, sp: val, shb: share, bp: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       sht: share, dt: val, t: fse_table, fm: Z, shsrc: share, srcp: val, buf: list Z, off: Z
  PRE [ tptr t_dstate, tptr t_bitd, tptr tuint ]
    PROP (writable_share shs; writable_share shb; readable_share sht; readable_share shsrc;
          bit_src_ok s start srcp buf off; lo + 64 - (pos - ft_log t) <= Int.max_unsigned)
    PARAMS (sp; bp; dt) GLOBALS (gv)
    SEP (data_at_ shs t_dstate sp; BIT_DStream_rep shb gv s start pos lo bp; fsedt_at sht t fm dt;
         bit_src shsrc srcp buf)
  POST [ tvoid ]
    EX st: Z,
    PROP (0 <= st < 2 ^ ft_log t; lo <= pos - ft_log t -> st = bs_peek (bs_value s) pos (ft_log t))
    RETURN ()
    SEP (data_at shs t_dstate (Vlong (Int64.repr st), offset_val 4 dt) sp;
         BIT_DStream_rep shb gv s start (pos - ft_log t) (snd (bs_reload (pos - ft_log t) lo)) bp;
         fsedt_at sht t fm dt; bit_src shsrc srcp buf).

(* FSE_decodeSymbol(DStatePtr, bitD) / FSE_decodeSymbolFast: the symbol of the state's cell; the new state
   is the cell's base + the next nbBits bits *)
Definition decsym_spec (fast: bool) : funspec :=
  WITH shs: share, sp: val, st: Z, sht: share, dt: val, t: fse_table, fm: Z,
       shb: share, bp: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z
  PRE [ tptr t_dstate, tptr t_bitd ]
    PROP (writable_share shs; readable_share sht; writable_share shb; 0 <= st < 2 ^ ft_log t;
          lo + 64 - (pos - fe_nb (fse_cell t st)) <= Int.max_unsigned;
          fast = true -> 1 <= fe_nb (fse_cell t st))
    PARAMS (sp; bp)
    SEP (data_at shs t_dstate (Vlong (Int64.repr st), offset_val 4 dt) sp; fsedt_at sht t fm dt;
         BIT_DStream_rep shb gv s start pos lo bp)
  POST [ tuchar ]
    EX r: Z,
    PROP (0 <= r < 2 ^ fe_nb (fse_cell t st);
          lo <= pos - fe_nb (fse_cell t st) \/ (fast = true /\ lo = 0 /\ 0 < pos) ->
            r = bs_peek (bs_value s) pos (fe_nb (fse_cell t st)))
    RETURN (Vint (Int.repr (fe_sym (fse_cell t st))))
    SEP (data_at shs t_dstate (Vlong (Int64.repr (fe_base (fse_cell t st) + r)), offset_val 4 dt) sp;
         fsedt_at sht t fm dt;
         BIT_DStream_rep shb gv s start (pos - fe_nb (fse_cell t st)) lo bp).

Definition FSE_decodeSymbol_spec : ident * funspec := DECLARE _FSE_decodeSymbol decsym_spec false.
Definition FSE_decodeSymbolFast_spec : ident * funspec := DECLARE _FSE_decodeSymbolFast decsym_spec true.

(* FSE_decompress_usingDTable_generic(huffWeight, 255, cSrc, cSrcSize, dt, fast): the weights the two
   states decode from the window s (fse_weights_dec); fast = the table's fastMode *)
Definition FSE_decompress_usingDTable_generic_spec : ident * funspec :=
  DECLARE _FSE_decompress_usingDTable_generic
  WITH gv: globals, shw: share, pw: val, oc: list val, sh: share, base: val, N: Z, c: list val, off: Z,
       s: list Z, sht: share, dt: val, t: fse_table, fm: Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tptr tuint, tuint ]
    PROP (writable_share shw; Zlength oc = 256; readable_share sht; win_ok sh N c off (Zlength s) s;
          fm = 1 -> Forall (fun e => 1 <= fe_nb e) (ft_cells t))
    PARAMS (pw; Vlong (Int64.repr 255); offset_val off base; Vlong (Int64.repr (Zlength s)); dt;
            Vint (Int.repr fm)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc pw; data_at sh (tarray tuchar N) c base;
         fsedt_at sht t fm dt)
  POST [ tulong ]
    EX r: Z, EX oc': list val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = 256;
          match fse_weights_dec t s with
          | Some ws => r = Zlength ws /\ sublist 0 (Zlength ws) oc' = zbytes ws
          | None => is_error_code r = true
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc' pw; data_at sh (tarray tuchar N) c base;
         fsedt_at sht t fm dt).

(* ---------- building decoding tables ---------- *)

(* FSE_buildDTable_internal(dt, normalizedCounter, maxSymbolValue, tableLog, workSpace, wkspSize): the
   table of a valid distribution (Huffman weights: symbols <= 255, log <= 12) *)
Definition FSE_buildDTable_internal_spec : ident * funspec :=
  DECLARE _FSE_buildDTable_internal
  WITH gv: globals, shd: share, dt: val, shn: share, pn: val, nc: list val, norm: list Z, log: Z,
       shw: share, pw: val, nw: Z
  PRE [ tptr tuint, tptr tshort, tuint, tuint, tptr tvoid, tulong ]
    PROP (writable_share shd; readable_share shn; writable_share shw;
          ncount_ok norm log 255; log <= 12;
          Zlength norm <= Zlength nc; sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm;
          2 * Zlength norm + 2 ^ log + 8 <= 4 * nw <= Int.max_unsigned)
    PARAMS (dt; pn; Vint (Int.repr (Zlength norm - 1)); Vint (Int.repr log); pw; Vlong (Int64.repr (4 * nw)))
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shd (tarray tuint (1 + 2 ^ log)) dt; data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at_ shw (tarray tuint nw) pw)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr 0))
    SEP (zstd_globals gv; fsedt_at shd (fse_build norm log) (fse_fm norm log) dt; data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at_ shw (tarray tuint nw) pw).

(* ZSTD_buildFSETable_body / _body_default(dt, normalizedCounter, maxSymbolValue, baseValue,
   nbAdditionalBits, tableLog, wksp, wkspSize): as ZSTD_buildFSETable (BIface), without bmi2 *)
Definition buildfse_body_spec : funspec :=
  WITH gv: globals, k: seqkind, shd: share, dt: val, shn: share, pn: val, nc: list val, norm: list Z, log: Z,
       shw: share, pw: val, nw: Z
  PRE [ tptr t_seqSymbol, tptr tshort, tuint, tptr tuint, tptr tuchar, tuint, tptr tvoid, tulong ]
    PROP (writable_share shd; readable_share shn; writable_share shw;
          ncount_ok norm log (sk_max k); log <= sk_maxlog k;
          Zlength norm <= Zlength nc; sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm;
          157 <= nw <= 640)
    PARAMS (dt; pn; Vint (Int.repr (Zlength norm - 1)); gv (sk_gbase k); gv (sk_gbits k); Vint (Int.repr log);
            pw; Vlong (Int64.repr (4 * nw))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shd (tarray t_seqSymbol (sk_size k)) dt;
         data_at shn (tarray tshort (Zlength nc)) nc pn; data_at_ shw (tarray tuint nw) pw)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (zstd_globals gv; seqspace_at shd k (Some (fse_build norm log)) dt;
         data_at shn (tarray tshort (Zlength nc)) nc pn; data_at_ shw (tarray tuint nw) pw).

Definition ZSTD_buildFSETable_body_spec : ident * funspec :=
  DECLARE _ZSTD_buildFSETable_body buildfse_body_spec.
Definition ZSTD_buildFSETable_body_default_spec : ident * funspec :=
  DECLARE _ZSTD_buildFSETable_body_default buildfse_body_spec.

(* ---------- FSE_readNCount_body / _body_default / _bmi2 (bmi2 = 0) ---------- *)

(* FSE_readNCount_body on the window s: C's result res (nc_rel: exactly ncount_res on >= 8 bytes; on fewer, the
   exported FSE_readNCount on a zero-padded copy, in its C-result form); the counts as C stores them (short_val),
   known on >= 8 bytes and for log <= 9.  Exactly (last PROP): res is ExHuf.x_ncount s maxsv on every window *)
Definition ncount_body_spec : funspec :=
  WITH gv: globals, shn: share, pn: val, nn: Z, shm: share, pm: val, sht: share, pt: val, maxsv: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tshort, tptr tuint, tptr tuint, tptr tvoid, tulong ]
    PROP (writable_share shn; writable_share shm; writable_share sht; 0 <= maxsv <= 255; maxsv + 1 <= nn <= 256;
          win_ok sh N c off (Zlength s) s; Zlength s <= 2 ^ 63 - 1)
    PARAMS (pn; pm; pt; offset_val off base; Vlong (Int64.repr (Zlength s))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shn (tarray tshort nn) pn; data_at shm tuint (Vint (Int.repr maxsv)) pm;
         data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX nc: list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength nc = nn; nc_rel s maxsv res;
          match res with
          | Some (norm, log, size) =>
              r = size /\ (8 <= Zlength s \/ log <= 9 -> sublist 0 (Zlength norm) nc = map short_val norm)
          | None => is_error_code r = true
          end;
          res = x_ncount s maxsv)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shn (tarray tshort nn) nc pn;
         match res with
         | Some (norm, log, size) =>
             data_at shm tuint (Vint (Int.repr (Zlength norm - 1))) pm * data_at sht tuint (Vint (Int.repr log)) pt
         | None => data_at_ shm tuint pm * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base).

Definition FSE_readNCount_body_spec : ident * funspec := DECLARE _FSE_readNCount_body ncount_body_spec.
Definition FSE_readNCount_body_default_spec : ident * funspec :=
  DECLARE _FSE_readNCount_body_default ncount_body_spec.

Definition FSE_readNCount_bmi2_spec : ident * funspec :=
  DECLARE _FSE_readNCount_bmi2
  WITH gv: globals, shn: share, pn: val, nn: Z, shm: share, pm: val, sht: share, pt: val, maxsv: Z,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z
  PRE [ tptr tshort, tptr tuint, tptr tuint, tptr tvoid, tulong, tint ]
    PROP (writable_share shn; writable_share shm; writable_share sht; 0 <= maxsv <= 255; maxsv + 1 <= nn <= 256;
          win_ok sh N c off (Zlength s) s; Zlength s <= 2 ^ 63 - 1)
    PARAMS (pn; pm; pt; offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shn (tarray tshort nn) pn; data_at shm tuint (Vint (Int.repr maxsv)) pm;
         data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base)
  POST [ tulong ]
    EX r: Z, EX nc: list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength nc = nn; nc_rel s maxsv res;
          match res with
          | Some (norm, log, size) =>
              r = size /\ (8 <= Zlength s \/ log <= 9 -> sublist 0 (Zlength norm) nc = map short_val norm)
          | None => is_error_code r = true
          end;
          res = x_ncount s maxsv)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shn (tarray tshort nn) nc pn;
         match res with
         | Some (norm, log, size) =>
             data_at shm tuint (Vint (Int.repr (Zlength norm - 1))) pm * data_at sht tuint (Vint (Int.repr log)) pt
         | None => data_at_ shm tuint pm * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base).

(* ---------- FSE_decompress_wksp_body / _body_default / _bmi2: the Huffman weights ---------- *)

(* FSE_decompress_wksp_*(huffWeight[256], 255, window s, 6, workSpace (nk U32), 4 nk[, bmi2 = 0]):
   weights_of res nk s, res = its FSE_readNCount_bmi2's result (nc_rel; exactly ExHuf.x_ncount s 255) *)
Definition weights_spec : funspec :=
  WITH gv: globals, shw: share, pw: val, oc: list val, sh: share, base: val, N: Z, c: list val, off: Z,
       s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tuint, tptr tvoid, tulong, tint ]
    PROP (writable_share shw; Zlength oc = 256; win_ok sh N c off (Zlength s) s; writable_share shk;
          219 <= nk <= 4096; Zlength s <= 2 ^ 63 - 1)
    PARAMS (pw; Vlong (Int64.repr 255); offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 6);
            pk; Vlong (Int64.repr (4 * nk)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc pw; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = 256; nc_rel s 255 res;
          match weights_of res nk s with
          | Some ws => r = Zlength ws /\ sublist 0 (Zlength ws) oc' = zbytes ws
          | None => is_error_code r = true
          end;
          res = x_ncount s 255)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc' pw; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk).

Definition FSE_decompress_wksp_body_spec : ident * funspec := DECLARE _FSE_decompress_wksp_body weights_spec.
Definition FSE_decompress_wksp_bmi2_spec : ident * funspec := DECLARE _FSE_decompress_wksp_bmi2 weights_spec.

Definition FSE_decompress_wksp_body_default_spec : ident * funspec :=
  DECLARE _FSE_decompress_wksp_body_default
  WITH gv: globals, shw: share, pw: val, oc: list val, sh: share, base: val, N: Z, c: list val, off: Z,
       s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tvoid, tulong, tptr tvoid, tulong, tuint, tptr tvoid, tulong ]
    PROP (writable_share shw; Zlength oc = 256; win_ok sh N c off (Zlength s) s; writable_share shk;
          219 <= nk <= 4096; Zlength s <= 2 ^ 63 - 1)
    PARAMS (pw; Vlong (Int64.repr 255); offset_val off base; Vlong (Int64.repr (Zlength s)); Vint (Int.repr 6);
            pk; Vlong (Int64.repr (4 * nk))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc pw; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = 256; nc_rel s 255 res;
          match weights_of res nk s with
          | Some ws => r = Zlength ws /\ sublist 0 (Zlength ws) oc' = zbytes ws
          | None => is_error_code r = true
          end;
          res = x_ncount s 255)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) oc' pw; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk).

(* ---------- HUF_readStats_body / _body_default (bmi2 = 0) ---------- *)

(* as HUF_readStats_wksp_spec (BIface), with huf_parse_res res nk (C's weights; res = the weights' readNCount
   result, nc_rel and exactly ExHuf.x_ncount on rs_window s) and without huf_ok *)
Definition HUF_readStats_body_spec : ident * funspec :=
  DECLARE _HUF_readStats_body
  WITH gv: globals, shw: share, pw: val, shr: share, pr: val, shs: share, ps: val, sht: share, pt: val,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tuchar, tulong, tptr tuint, tptr tuint, tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (writable_share shw; writable_share shr; writable_share shs; writable_share sht; writable_share shk;
          219 <= nk <= 4096; win_ok sh N c off (Zlength s) s)
    PARAMS (pw; Vlong (Int64.repr 256); pr; ps; pt; offset_val off base; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (4 * nk)); Vint (Int.repr 0)) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shw (tarray tuchar 256) pw; data_at_ shr (tarray tuint 13) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX wc: list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength wc = 256;
          match rs_window s with Some w => nc_rel w 255 res | None => True end;
          match huf_parse_res res nk s with
          | Some (ht, size) =>
              r = size /\ sublist 0 (Zlength (ht_weights ht)) wc = map (fun x => Vint (Int.repr x)) (ht_weights ht)
          | None => is_error_code r = true
          end;
          match rs_window s with Some w => res = x_ncount w 255 | None => True end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         match huf_parse_res res nk s with
         | Some (ht, size) =>
             data_at shr (tarray tuint 13) (rank_stats (ht_weights ht)) pr *
             data_at shs tuint (Vint (Int.repr (Zlength (ht_weights ht)))) ps *
             data_at sht tuint (Vint (Int.repr (ht_log ht))) pt
         | None => data_at_ shr (tarray tuint 13) pr * data_at_ shs tuint ps * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

Definition HUF_readStats_body_default_spec : ident * funspec :=
  DECLARE _HUF_readStats_body_default
  WITH gv: globals, shw: share, pw: val, shr: share, pr: val, shs: share, ps: val, sht: share, pt: val,
       sh: share, base: val, N: Z, c: list val, off: Z, s: list Z, shk: share, pk: val, nk: Z
  PRE [ tptr tuchar, tulong, tptr tuint, tptr tuint, tptr tuint, tptr tvoid, tulong, tptr tvoid, tulong ]
    PROP (writable_share shw; writable_share shr; writable_share shs; writable_share sht; writable_share shk;
          219 <= nk <= 4096; win_ok sh N c off (Zlength s) s)
    PARAMS (pw; Vlong (Int64.repr 256); pr; ps; pt; offset_val off base; Vlong (Int64.repr (Zlength s));
            pk; Vlong (Int64.repr (4 * nk))) GLOBALS (gv)
    SEP (zstd_globals gv; data_at_ shw (tarray tuchar 256) pw; data_at_ shr (tarray tuint 13) pr;
         data_at_ shs tuint ps; data_at_ sht tuint pt; data_at sh (tarray tuchar N) c base;
         data_at_ shk (tarray tuint nk) pk)
  POST [ tulong ]
    EX r: Z, EX wc: list val, EX res: option (list Z * Z * Z),
    PROP (0 <= r <= Int64.max_unsigned; Zlength wc = 256;
          match rs_window s with Some w => nc_rel w 255 res | None => True end;
          match huf_parse_res res nk s with
          | Some (ht, size) =>
              r = size /\ sublist 0 (Zlength (ht_weights ht)) wc = map (fun x => Vint (Int.repr x)) (ht_weights ht)
          | None => is_error_code r = true
          end;
          match rs_window s with Some w => res = x_ncount w 255 | None => True end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at shw (tarray tuchar 256) wc pw;
         match huf_parse_res res nk s with
         | Some (ht, size) =>
             data_at shr (tarray tuint 13) (rank_stats (ht_weights ht)) pr *
             data_at shs tuint (Vint (Int.repr (Zlength (ht_weights ht)))) ps *
             data_at sht tuint (Vint (Int.repr (ht_log ht))) pt
         | None => data_at_ shr (tarray tuint 13) pr * data_at_ shs tuint ps * data_at_ sht tuint pt
         end;
         data_at sh (tarray tuchar N) c base; data_at_ shk (tarray tuint nk) pk).

(* ---------- ZSTD_buildFSETable (the export) wrapper specs are BIface's ---------- *)
