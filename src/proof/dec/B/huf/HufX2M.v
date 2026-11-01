(* Model of the X2 table fill of HUF_readDTableX2_wksp (sub-group X2T).

   The C fills a table of 2^L U32 cells (HUF_DEltX2 {sequence; nbBits; length} as one little-endian U32:
   `deltu`).  Cell v (the L peeked bits) gets the symbol s1 (code length n1) of v, and, when the code of the
   symbol s2 at the remaining bits (v * 2^n1 mod 2^L, zeros below) also fits in the L bits, s2 as well:
   `x2_elt`.  Such a cell is x2_cell_ok (BRep).

   The C walks the canonical code by weight (HUF_fillDTableX2: weights 1..maxW; for a weight with room for
   a second symbol, one sub-table of 2^(L-n1) cells per symbol: HUF_fillDTableX2Level2), with
   - sortedSymbol: the symbols sorted by weight then symbol (`sorted_syms`), the symbols of weight w at
     [rstart w, rstart (w+1));
   - rankVal[0][w] = rv0 w: the first cell of weight w in the L-table; rankVal[c][w] = rv0 w / 2^c. *)
Require Export Zstd.proof.dec.B.BIface.
Require Export Zstd.proof.model.HufC.
Local Open Scope Z_scope.

(* ---------- weights ---------- *)

(* what huf_parse_desc guarantees (HufMDesc.huf_parse_desc_facts) *)
Definition x2_ht_ok (ht: huf_table) : Prop :=
  huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\ Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht).

Definition hw (ht: huf_table) (s: Z) : Z := nth (Z.to_nat s) (ht_weights ht) 0.
(* the code length of weight w *)
Definition nbw (ht: huf_table) (w: Z) : Z := ht_log ht + 1 - w.
(* the symbols, the symbols of weight w (increasing), their number (= the C's rankStats[w], rank_stats) *)
Definition hsyms (ht: huf_table) : list Z := map Z.of_nat (seq 0 (length (ht_weights ht))).
Definition symsw (ht: huf_table) (w: Z) : list Z := filter (fun s => hw ht s =? w) (hsyms ht).
Definition cntw (ht: huf_table) (w: Z) : Z := Zlength (filter (fun x => x =? w) (ht_weights ht)).
(* the largest weight (the C's maxW) *)
Definition maxw (ht: huf_table) : Z := fold_right Z.max 0 (ht_weights ht).
(* the weights 1 .. w-1 *)
Definition wbelow (w: Z) : list Z := map Z.of_nat (seq 1 (Z.to_nat (w - 1))).
(* index in sorted_syms of the first symbol of weight w (w >= 1) *)
Definition rstart (ht: huf_table) (w: Z) : Z := fold_right Z.add 0 (map (cntw ht) (wbelow w)).
(* the symbols of weight >= 1, by weight then symbol *)
Definition sorted_syms (ht: huf_table) : list Z := flat_map (symsw ht) (wbelow (maxw ht + 1)).
(* the first cell of weight w in the L-table (a symbol of weight w has 2^(L - nbw w) cells) *)
Definition rv0 (ht: huf_table) (L w: Z) : Z :=
  fold_right Z.add 0 (map (fun w' => cntw ht w' * 2 ^ (L - nbw ht w')) (wbelow w)).
(* the shortest code length (the C's minBits) *)
Definition minbits (ht: huf_table) : Z := ht_log ht + 1 - maxw ht.

(* ---------- cells ---------- *)

(* the cells, deltu (HUF_buildDEltX2U32), x2_cellu and x2_elt, are model/HufC.v's *)

(* the whole table *)
Definition x2_u32s (ht: huf_table) (L: Z) : list val :=
  map (fun n => Vint (Int.repr (x2_elt ht L (Z.of_nat n)))) (seq 0 (Z.to_nat (2 ^ L))).

(* the sub-table of the first symbol s1 of code length n1 (HUF_fillDTableX2Level2) *)
Definition lvl2_u32s (ht: huf_table) (L s1 n1: Z) : list val :=
  map (fun j => Vint (Int.repr (x2_cellu ht L s1 n1 (Z.of_nat j * 2 ^ n1)))) (seq 0 (Z.to_nat (2 ^ (L - n1)))).

(* HUF_fillDTableX2ForWeight: len cells per symbol of syms *)
Definition fw_u32s (syms: list Z) (nb bs lv len: Z) : list val :=
  flat_map (fun s => repeat (Vint (Int.repr (deltu s nb bs lv))) (Z.to_nat len)) syms.

(* ---------- the C's sort (HUF_readDTableX2_wksp) ---------- *)

(* where the C puts symbol s: weight-0 symbols after all others *)
Definition sort_pos (ht: huf_table) (s: Z) : Z :=
  (if hw ht s =? 0 then rstart ht (maxw ht + 1) else rstart ht (hw ht s)) +
  Zlength (filter (fun s' => hw ht s' =? hw ht s) (map Z.of_nat (seq 0 (Z.to_nat s)))).

(* the sortedSymbol array after the symbols 0..n-1 (sortedSymbol_t is one byte: its reptype is val) *)
Definition sort_arr (ht: huf_table) (n: nat) (a0: list val) : list val :=
  fold_left (fun a s => upd_Znth (sort_pos ht (Z.of_nat s)) a (Vint (Int.repr (Z.of_nat s)))) (seq 0 n) a0.

(* ===================== facts =====================
   Grouped in records (Prop) so that the body lemmas can take them as hypotheses. *)

Definition x2_cell (ht: huf_table) (L v: Z) : val * (val * val) :=
  let e := x2_elt ht L v in
  (Vint (Int.repr (e mod 65536)), (Vint (Int.repr ((e / 65536) mod 256)), Vint (Int.repr (e / 16777216)))).

(* ---------- counting and sorting (proved in HufX2Mc.v: x2_count_ok) ---------- *)
Record x2_count : Prop := {
  xc_maxw : forall ht, x2_ht_ok ht ->
    1 <= maxw ht <= ht_log ht /\ 0 < cntw ht (maxw ht) /\ (forall w, maxw ht < w -> cntw ht w = 0) /\
    (forall w, 0 <= w <= 12 -> Znth w (rank_stats (ht_weights ht)) = Vint (Int.repr (cntw ht w)));
  xc_symsw : forall ht w, x2_ht_ok ht -> 1 <= w <= maxw ht ->
    Zlength (symsw ht w) = cntw ht w /\ Forall (fun s => 0 <= s < 256) (symsw ht w) /\
    sublist (rstart ht w) (rstart ht (w + 1)) (sorted_syms ht) = symsw ht w;
  xc_rstart : forall ht w, x2_ht_ok ht -> 1 <= w ->
    rstart ht 1 = 0 /\ rstart ht (w + 1) = rstart ht w + cntw ht w /\
    Zlength (sorted_syms ht) = rstart ht (maxw ht + 1) /\
    rstart ht (maxw ht + 1) + cntw ht 0 = Zlength (ht_weights ht);
  (* the C's counting sort *)
  xc_sort_pos : forall ht s, x2_ht_ok ht -> 0 <= s < Zlength (ht_weights ht) ->
    0 <= sort_pos ht s < Zlength (ht_weights ht);
  xc_sort_arr : forall ht (a0: list val) i, x2_ht_ok ht -> Zlength a0 = 256 -> 0 <= i < rstart ht (maxw ht + 1) ->
    Znth i (sort_arr ht (length (ht_weights ht)) a0) = Vint (Int.repr (Znth i (sorted_syms ht)))
}.

(* ---------- the canonical layout in an L-table (proved in HufX2Ml.v: x2_layout_ok) ---------- *)
Record x2_layout : Prop := {
  xl_rv0 : forall ht L w, x2_ht_ok ht -> ht_log ht <= L -> 1 <= w ->
    rv0 ht L 1 = 0 /\ rv0 ht L (w + 1) = rv0 ht L w + cntw ht w * 2 ^ (L - nbw ht w) /\
    rv0 ht L (maxw ht + 1) = 2 ^ L;
  (* the first cell of weight w <= maxw is aligned to the size of its symbols' cells *)
  xl_aligned : forall ht L w, x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= maxw ht ->
    rv0 ht L w mod 2 ^ (L - nbw ht w) = 0;
  (* the k-th symbol of weight w has the cells [rv0 w + k 2^(L - nbw w), + 2^(L - nbw w)) *)
  xl_layout : forall ht L w k i, x2_ht_ok ht -> ht_log ht <= L -> 1 <= w <= maxw ht -> 0 <= k < cntw ht w ->
    0 <= i < 2 ^ (L - nbw ht w) ->
    hsym ht L (rv0 ht L w + k * 2 ^ (L - nbw ht w) + i) = (Znth k (symsw ht w), nbw ht w)
}.

(* ---------- the fill, region by region, and the cells (proved in HufX2Mf.v: x2_fill_ok) ---------- *)
Record x2_fill : Prop := {
  (* a weight without room for a second symbol *)
  xf_single : forall ht L w, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> 1 <= w <= maxw ht ->
    L - nbw ht w < minbits ht ->
    sublist (rv0 ht L w) (rv0 ht L (w + 1)) (x2_u32s ht L) = fw_u32s (symsw ht w) (nbw ht w) 0 1 (2 ^ (L - nbw ht w));
  (* a weight with room: the k-th symbol's sub-table *)
  xf_double : forall ht L w k, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> 1 <= w <= maxw ht ->
    minbits ht <= L - nbw ht w -> 0 <= k < cntw ht w ->
    sublist (rv0 ht L w + k * 2 ^ (L - nbw ht w)) (rv0 ht L w + (k + 1) * 2 ^ (L - nbw ht w)) (x2_u32s ht L) =
    lvl2_u32s ht L (Znth k (symsw ht w)) (nbw ht w);
  (* the sub-table of a first symbol of code length n1; Z.max 1 (..) = the C's minWeight *)
  xf_skip : forall ht L s1 n1, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
    minbits ht <= n1 <= L - minbits ht -> 1 < Z.max 1 (n1 + ht_log ht + 1 - L) ->
    0 <= rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1 < 2 ^ (L - n1) /\
    sublist 0 (rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1) (lvl2_u32s ht L s1 n1) =
    repeat (Vint (Int.repr (deltu s1 n1 0 1))) (Z.to_nat (rv0 ht L (Z.max 1 (n1 + ht_log ht + 1 - L)) / 2 ^ n1));
  xf_weight : forall ht L s1 n1 w, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX ->
    minbits ht <= n1 <= L - minbits ht -> Z.max 1 (n1 + ht_log ht + 1 - L) <= w <= maxw ht ->
    0 <= L - n1 - nbw ht w /\
    rv0 ht L (w + 1) / 2 ^ n1 = rv0 ht L w / 2 ^ n1 + cntw ht w * 2 ^ (L - n1 - nbw ht w) /\
    sublist (rv0 ht L w / 2 ^ n1) (rv0 ht L (w + 1) / 2 ^ n1) (lvl2_u32s ht L s1 n1) =
    fw_u32s (symsw ht w) (n1 + nbw ht w) s1 2 (2 ^ (L - n1 - nbw ht w));
  (* the U32 of a cell, and its fields (HUF_DEltX2 {sequence; nbBits; length}) *)
  xf_range : forall ht L v, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> 0 <= v < 2 ^ L ->
    0 <= x2_elt ht L v < 16777216 * 3;
  xf_cell_ok : forall ht L v, x2_ht_ok ht -> ht_log ht <= L <= HUF_TABLELOG_MAX -> 0 <= v < 2 ^ L ->
    x2_cell_ok ht L v (x2_cell ht L v)
}.
