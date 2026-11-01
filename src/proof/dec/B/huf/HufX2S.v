(* Sub-group X2T: the specifications of the six functions that build
   an X2 table, and the context the bodies are proved against.  Model: HufX2M.v.

   The fill functions see the cells as U32s (`tarray tuint`): the C writes each cell by a 4-byte memcpy of a
   U32 local (HUF_buildDEltX2U32).  HUF_readDTableX2_wksp turns the 2^L U32s into HUF_DEltX2 cells at the end
   (x2_u32s_cells). *)
Require Export Zstd.proof.dec.B.huf.HufX2M.
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

Definition t_ssym : type := Tstruct ___gp_sortedSymbol_t noattr.

(* HUF_buildDEltX2U32(symbol, nbBits, baseSeq, level) *)
Definition HUF_buildDEltX2U32_spec : ident * funspec :=
  DECLARE _HUF_buildDEltX2U32
  WITH sym: Z, nb: Z, bs: Z, lv: Z
  PRE [ tuint, tuint, tuint, tint ]
    PROP (0 <= sym <= Int.max_unsigned; 0 <= nb <= Int.max_unsigned; 0 <= bs <= Int.max_unsigned;
          lv = 1 \/ lv = 2)
    PARAMS (Vint (Int.repr sym); Vint (Int.repr nb); Vint (Int.repr bs); Vint (Int.repr lv))
    SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (deltu sym nb bs lv))) SEP ().

(* HUF_buildDEltX2(DElt, symbol, nbBits, baseSeq, level): one U32 cell *)
Definition HUF_buildDEltX2_spec : ident * funspec :=
  DECLARE _HUF_buildDEltX2
  WITH sh: share, p: val, sym: Z, nb: Z, bs: Z, lv: Z
  PRE [ tptr t_deltx2, tuint, tuint, tuint, tint ]
    PROP (writable_share sh; 0 <= sym <= Int.max_unsigned; 0 <= nb <= Int.max_unsigned;
          0 <= bs <= Int.max_unsigned; lv = 1 \/ lv = 2)
    PARAMS (p; Vint (Int.repr sym); Vint (Int.repr nb); Vint (Int.repr bs); Vint (Int.repr lv))
    SEP (data_at_ sh tuint p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh tuint (Vint (Int.repr (deltu sym nb bs lv))) p).

(* HUF_fillDTableX2ForWeight(DTableRank, begin, end, nbBits, tableLog, baseSeq, level): the symbols syms at
   sortedSymbol[b..e) get 2^(L - nb) cells each. *)
Definition HUF_fillDTableX2ForWeight_spec : ident * funspec :=
  DECLARE _HUF_fillDTableX2ForWeight
  WITH sh: share, p: val, shs: share, ps: val, ss: list val, b: Z, e: Z, syms: list Z, nb: Z, L: Z,
       bs: Z, lv: Z
  PRE [ tptr t_deltx2, tptr t_ssym, tptr t_ssym, tuint, tuint, tushort, tint ]
    PROP (writable_share sh; readable_share shs; 0 <= b <= e; e <= 256; Zlength ss = 256;
          sublist b e ss = map (fun s => Vint (Int.repr s)) syms; Forall (fun s => 0 <= s < 256) syms;
          1 <= nb <= L; L <= HUF_TABLELOG_MAX; 0 <= bs < 256; lv = 1 \/ lv = 2)
    PARAMS (p; offset_val b ps; offset_val e ps; Vint (Int.repr nb); Vint (Int.repr L); Vint (Int.repr bs);
            Vint (Int.repr lv))
    SEP (data_at_ sh (tarray tuint ((e - b) * 2 ^ (L - nb))) p; data_at shs (tarray t_ssym 256) ss ps)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint ((e - b) * 2 ^ (L - nb))) (fw_u32s syms nb bs lv (2 ^ (L - nb))) p;
         data_at shs (tarray t_ssym 256) ss ps).

(* the workspace arrays as HUF_readDTableX2_wksp leaves them for the fill (ht's sorted symbols, the start
   index of each weight in them, rankVal) *)
Definition x2_ss_ok (ht: huf_table) (ss: list val) : Prop :=
  Zlength ss = 256 /\
  forall i, 0 <= i < rstart ht (maxw ht + 1) -> Znth i ss = Vint (Int.repr (Znth i (sorted_syms ht))).
Definition x2_rs_ok (ht: huf_table) (rs: list val) : Prop :=
  Zlength rs = 15 /\ forall w, 1 <= w <= maxw ht + 1 -> Znth w rs = Vint (Int.repr (rstart ht w)).
(* a row rankVal[c]: the first cell of each weight in a table of L - c bits *)
Definition x2_row_ok (ht: huf_table) (L c: Z) (row: list val) : Prop :=
  Zlength row = 13 /\ forall w, 1 <= w <= maxw ht -> Znth w row = Vint (Int.repr (rv0 ht L w / 2 ^ c)).
Definition x2_rv_ok (ht: huf_table) (L: Z) (rv: list (list val)) : Prop :=
  Zlength rv = 12 /\ Forall (fun r => Zlength r = 13) rv /\
  forall c, c = 0 \/ minbits ht <= c <= L - minbits ht -> x2_row_ok ht L c (Znth c rv).

(* HUF_fillDTableX2Level2(DTable, targetLog, consumedBits, rankVal, minWeight, maxWeight1, sortedSymbols,
   rankStart, nbBitsBaseline, baseSeq): the sub-table of the first symbol s1 of code length n1 *)
Definition HUF_fillDTableX2Level2_spec : ident * funspec :=
  DECLARE _HUF_fillDTableX2Level2
  WITH sh: share, p: val, shw: share, ht: huf_table, L: Z, n1: Z, s1: Z, prow: val, row: list val,
       ps: val, ss: list val, prs: val, rs: list val
  PRE [ tptr t_deltx2, tuint, tuint, tptr tuint, tint, tint, tptr t_ssym, tptr tuint, tuint, tushort ]
    PROP (writable_share sh; readable_share shw; x2_ht_ok ht; ht_log ht <= L <= HUF_TABLELOG_MAX;
          minbits ht <= n1 <= L - minbits ht; 0 <= s1 < 256;
          x2_row_ok ht L n1 row; x2_ss_ok ht ss; x2_rs_ok ht rs)
    PARAMS (p; Vint (Int.repr L); Vint (Int.repr n1); prow; Vint (Int.repr (Z.max 1 (n1 + ht_log ht + 1 - L)));
            Vint (Int.repr (maxw ht + 1)); ps; prs; Vint (Int.repr (ht_log ht + 1)); Vint (Int.repr s1))
    SEP (data_at_ sh (tarray tuint (2 ^ (L - n1))) p; data_at shw (tarray tuint 13) row prow;
         data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint (2 ^ (L - n1))) (lvl2_u32s ht L s1 n1) p; data_at shw (tarray tuint 13) row prow;
         data_at shw (tarray t_ssym 256) ss ps; data_at shw (tarray tuint 15) rs prs).

(* HUF_fillDTableX2(DTable, targetLog, sortedList, rankStart, rankValOrigin, maxWeight, nbBitsBaseline):
   the whole table *)
Definition HUF_fillDTableX2_spec : ident * funspec :=
  DECLARE _HUF_fillDTableX2
  WITH sh: share, p: val, shw: share, ht: huf_table, L: Z, ps: val, ss: list val, prs: val, rs: list val,
       prv: val, rv: list (list val)
  PRE [ tptr t_deltx2, tuint, tptr t_ssym, tptr tuint, tptr (tarray tuint 13), tuint, tuint ]
    PROP (writable_share sh; readable_share shw; x2_ht_ok ht; ht_log ht <= L <= HUF_TABLELOG_MAX;
          x2_ss_ok ht ss; x2_rs_ok ht rs; x2_rv_ok ht L rv)
    PARAMS (p; Vint (Int.repr L); ps; prs; prv; Vint (Int.repr (maxw ht)); Vint (Int.repr (ht_log ht + 1)))
    SEP (data_at_ sh (tarray tuint (2 ^ L)) p; data_at shw (tarray t_ssym 256) ss ps;
         data_at shw (tarray tuint 15) rs prs; data_at shw (tarray (tarray tuint 13) 12) rv prv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuint (2 ^ L)) (x2_u32s ht L) p; data_at shw (tarray t_ssym 256) ss ps;
         data_at shw (tarray tuint 15) rs prs; data_at shw (tarray (tarray tuint 13) 12) rv prv).

(* the specifications of X2T (ids_X2T order); the export is BIface's *)
Definition X2T_specs : funspecs :=
  [ HUF_buildDEltX2U32_spec; HUF_buildDEltX2_spec; HUF_fillDTableX2ForWeight_spec; HUF_fillDTableX2Level2_spec;
    HUF_fillDTableX2_spec; HUF_readDTableX2_wksp_spec ].

(* the context of every body *)
Definition G_X2 : funspecs := (G_HUF ++ X2T_imports) ++ X2T_specs.

(* ---------- the final conversion: U32 cells -> HUF_DEltX2 cells ---------- *)

(* the cells are x2_cell_ok (what they decode) and exactly ExHuf's xh_cells_x2 *)
Definition x2_cells_stmt : Prop :=
  forall (sh: share) (ht: huf_table) (L: Z) (p: val),
  x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
  data_at sh (tarray tuint (2 ^ L)) (x2_u32s ht L) p |--
  EX c2: list (val * (val * val)),
    !! (Zlength c2 = 2 ^ L /\ (forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2)) /\
        c2 = map x2v (xh_cells_x2 ht L)) &&
    data_at sh (tarray t_deltx2 (2 ^ L)) c2 p.

(* what a parsed description gives (HufMDesc.huf_parse_desc_facts) *)
Definition x2_desc_facts : Prop :=
  forall s ht h, huf_parse_desc s = Some (ht, h) -> x2_ht_ok ht /\ 1 <= h <= Zlength s.
