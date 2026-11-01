(* Sub-group X1T of group HUF: the specifications of the two internal
   functions (HUF_DEltX1_set4, HUF_rescaleStats) and the two loop segments of HUF_readDTableX1_wksp proved
   separately (statement 9: rankStart + the symbols sorted by weight; statement 10: the fill of the cells). *)
Require Export Zstd.proof.dec.B.huf.HufGroups.
Require Export Zstd.proof.dec.B.huf.HufMRescale Zstd.proof.dec.B.huf.HufMDesc.
Local Open Scope logic.

Definition t_x1wksp : type := Tstruct ___gp_HUF_ReadDTableX1_Workspace noattr.

(* ---------- HUF_DEltX1_set4(symbol, nbBits): the U64 of 4 cells {nbBits; symbol} (little-endian) ---------- *)

Definition set4_val (sym nb: Z) : Z := (sym * 256 + nb) * 281479271743489.   (* 0x0001000100010001 *)

Definition HUF_DEltX1_set4_spec : ident * funspec :=
  DECLARE _HUF_DEltX1_set4
  WITH sym: Z, nb: Z
  PRE [ tuchar, tuchar ]
    PROP (0 <= sym < 256; 0 <= nb < 256)
    PARAMS (Vint (Int.repr sym); Vint (Int.repr nb)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (set4_val sym nb))) SEP ().

(* ---------- HUF_rescaleStats(huffWeight, rankVal, nbSymbols, tableLog, targetTableLog) ---------- *)

(* the weights raised to log L (= ht_weights (huf_rescale ht L) when tl = ht_log ht) *)
Definition x1_rescale_ws (ws: list Z) (tl L: Z) : list Z :=
  map (fun w => if w =? 0 then 0 else w + (L - tl)) ws.

Lemma x1_rescale_ws_eq (ht: huf_table) (L: Z) :
  huf_rescale ht L = {| ht_log := L; ht_weights := x1_rescale_ws (ht_weights ht) (ht_log ht) L |}.
Proof. reflexivity. Qed.

Definition HUF_rescaleStats_spec : ident * funspec :=
  DECLARE _HUF_rescaleStats
  WITH shw: share, pw: val, ws: list Z, wr: list val, shr: share, pr: val, tl: Z, tg: Z
  PRE [ tptr tuchar, tptr tuint, tuint, tuint, tuint ]
    PROP (writable_share shw; writable_share shr; 1 <= tl <= HUF_TABLELOG_MAX; 1 <= tg <= HUF_TABLELOG_MAX;
          (Zlength ws + Zlength wr = 256)%Z; Forall (fun w => 0 <= w <= tl) ws)
    PARAMS (pw; pr; Vint (Int.repr (Zlength ws)); Vint (Int.repr tl); Vint (Int.repr tg))
    SEP (data_at shw (tarray tuchar 256) (map (fun w => Vint (Int.repr w)) ws ++ wr) pw;
         data_at shr (tarray tuint 13) (rank_stats ws) pr)
  POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (Z.max tl tg)))
    SEP (data_at shw (tarray tuchar 256)
           (map (fun w => Vint (Int.repr w)) (x1_rescale_ws ws tl (Z.max tl tg)) ++ wr) pw;
         data_at shr (tarray tuint 13) (rank_stats (x1_rescale_ws ws tl (Z.max tl tg))) pr).

(* the specifications of ids_X1T, in order *)
Definition X1T_specs : funspecs :=
  [ HUF_DEltX1_set4_spec; HUF_rescaleStats_spec; HUF_readDTableX1_wksp_spec ].

(* ---------- the statements of HUF_readDTableX1_wksp ---------- *)

Fixpoint sq_drop (k: nat) (s: statement) : statement :=
  match k, s with
  | O, _ => s
  | S k', Ssequence _ s2 => sq_drop k' s2
  | S _, _ => Sskip
  end.
Definition sq_head (s: statement) : statement := match s with Ssequence s1 _ => s1 | _ => s end.

(* top-level statements 0..11 of the body: 9 = rankStart and symbols (three loops), 10 = the fill *)
Definition x1_sort_stmt : statement :=
  Eval cbv [sq_head sq_drop fn_body f_HUF_readDTableX1_wksp] in sq_head (sq_drop 9 (fn_body f_HUF_readDTableX1_wksp)).
Definition x1_fill_stmt : statement :=
  Eval cbv [sq_head sq_drop fn_body f_HUF_readDTableX1_wksp] in sq_head (sq_drop 10 (fn_body f_HUF_readDTableX1_wksp)).

Definition x1_Delta (G: funspecs) : tycontext := func_tycontext f_HUF_readDTableX1_wksp Vprog G nil.

(* ---------- the model of the two segments ---------- *)

Notation vint z := (Vint (Int.repr z)).

(* symbols ordered by weight (0..12), then by symbol: wksp->symbols after statement 9 *)
Definition x1_sorted (ws: list Z) : list Z :=
  flat_map (fun w => map Z.of_nat (filter (fun s => nth s ws 0 =? w) (seq 0 (length ws))))
           (map Z.of_nat (seq 0 13)).

(* Segment 9: from the rescaled statistics (log L, weights rws in huffWeight[0..n), rank_stats rws in rankVal)
   to the sorted symbols.  F: the rest of the state. *)
Definition x1_sort_ok : Prop :=
  forall (Espec: OracleKind) (F: mpred) (sz: Z) (cells pk vtl vnb vdtd vD vD1: val) (shk: share)
         (rws: list Z) (wr: list val) (L: Z),
  writable_share shk -> 1 <= L <= HUF_TABLELOG_MAX -> 1 <= Zlength rws <= 256 ->
  Zlength wr = 256 - Zlength rws -> Forall (fun w => 0 <= w <= L) rws ->
  semax (x1_Delta nil)
    (PROP ()
     LOCAL (temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at_ shk t_x1wksp (DOT _rankStart) pk;
          field_at_ shk t_x1wksp (DOT _symbols) pk;
          field_at shk t_x1wksp (DOT _huffWeight) (map (fun w => vint w) rws ++ wr) pk;
          F))
    x1_sort_stmt
    (normal_ret_assert
      (PROP ()
       LOCAL (temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at Tsh tuint (vint L) vtl; data_at Tsh tuint (vint (Zlength rws)) vnb;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at_ shk t_x1wksp (DOT _rankStart) pk;
            field_at shk t_x1wksp (DOT _symbols)
              (map (fun s => vint s) (x1_sorted rws) ++ Zrepeat Vundef (256 - Zlength rws)) pk;
            field_at shk t_x1wksp (DOT _huffWeight) (map (fun w => vint w) rws ++ wr) pk;
            F))).

(* Segment 10: the fill.  The cells of the table {L; rws} (each symbol of weight w > 0 in 2^(w-1) cells of
   L + 1 - w bits), written as HUF_DEltX1 cells; Kraft: they are exactly 2^L. *)
Definition x1_fill_ok : Prop :=
  forall (Espec: OracleKind) (F: mpred) (sz: Z) (cells pk vtl vnb vdtd vD vD1: val) (shk shd: share)
         (rws: list Z) (sr: list val) (L: Z),
  writable_share shk -> writable_share shd -> 1 <= L <= HUF_TABLELOG_MAX -> 1 <= Zlength rws <= 256 ->
  Zlength sr = 256 - Zlength rws -> Forall (fun w => 0 <= w <= L) rws ->
  Zlength (huf_cells {| ht_log := L; ht_weights := rws |}) = 2 ^ L ->
  semax (x1_Delta [HUF_DEltX1_set4_spec; MEM_write64_spec])
    (PROP ()
     LOCAL (temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
            lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
            lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
     SEP (data_at Tsh tuint (vint L) vtl;
          field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
          field_at shk t_x1wksp (DOT _symbols) (map (fun s => vint s) (x1_sorted rws) ++ sr) pk;
          data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1;
          memory_block shd HUF_CELLBYTES cells;
          F))
    x1_fill_stmt
    (normal_ret_assert
      (PROP ()
       LOCAL (temp _iSize (Vlong (Int64.repr sz)); temp _dt cells; temp _wksp pk;
              lvar _tableLog tuint vtl; lvar _nbSymbols tuint vnb; lvar _dtd t_dtdesc vdtd;
              lvar _D t_deltx1 vD; lvar _D__1 t_deltx1 vD1)
       SEP (data_at Tsh tuint (vint L) vtl;
            field_at shk t_x1wksp (DOT _rankVal) (rank_stats rws) pk;
            field_at shk t_x1wksp (DOT _symbols) (map (fun s => vint s) (x1_sorted rws) ++ sr) pk;
            data_at_ Tsh t_deltx1 vD; data_at_ Tsh t_deltx1 vD1;
            data_at shd (tarray t_deltx1 (2 ^ L)) (map x1cell (huf_cells {| ht_log := L; ht_weights := rws |})) cells;
            memory_block shd (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (2 * 2 ^ L) cells);
            F))).
