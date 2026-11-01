(* Subtree B of the decoder: the representations of the entropy tables, and B's choice of the
   abstract predicates TABS (a context's tables group) and DENT (a DDict's entropy field) of DecRep.v.
   Fixed: every group of B uses these representations.

   - FSE tables of the sequences (ZSTD_seqSymbol arrays): seqtab_at, against model/Fse.v fse_table;
   - Huffman tables (HUF_DTable, X1 or X2 cells): hufdt_x_at, against model/Huffman.v huf_table: the cells are
     exactly those of model/ExHuf.v's xhuf_of (the log zstd's reader picks, the X1 and X2 cells it writes);
   - tabs_def / dent_def: TABS and DENT, and their facts TABS_OK / DENT_OK (BLemmas.v). *)
Require Export Zstd.proof.dec.DecSubtrees.
Require Export Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block Zstd.proof.model.Series.
Require Export Zstd.proof.model.HufC.
Require Import Zstd.proof.model.ExHuf.
Local Open Scope logic.

Definition t_seqhdr : type := Tstruct ___gp_ZSTD_seqSymbol_header noattr.
Definition t_dtdesc : type := Tstruct ___gp_DTableDesc noattr.
Definition t_deltx1 : type := Tstruct ___gp_HUF_DEltX1 noattr.
Definition t_deltx2 : type := Tstruct ___gp_HUF_DEltX2 noattr.
Definition t_entropy_dd : type := Tstruct _ZSTD_DDict_s noattr.

(* ZSTD_LITBUFFEREXTRASIZE *)
Definition LITBUFFEREXTRASIZE : Z := 65536.

(* ===================== sequence code tables (FSE) ===================== *)

(* the three kinds of sequence codes: literal lengths, offsets, match lengths *)
Inductive seqkind := KLL | KOF | KML.

(* OF_base of zstd_decompress_internal.h: 0, 1, 1, 5, 0xD, ..., 2^s - 3 *)
Definition OF_base_tab : list Z :=
  map (fun n => let s := Z.of_nat n in if s <? 2 then s else 2 ^ s - 3) (seq 0 32).
Definition OF_bits_tab : list Z := map Z.of_nat (seq 0 32).

Definition sk_base (k: seqkind) (s: Z) : Z :=
  match k with
  | KLL => nth (Z.to_nat s) LL_base_tab 0
  | KOF => nth (Z.to_nat s) OF_base_tab 0
  | KML => nth (Z.to_nat s) ML_base_tab 0
  end.
Definition sk_bits (k: seqkind) (s: Z) : Z :=
  match k with
  | KLL => nth (Z.to_nat s) LL_bits_tab 0
  | KOF => nth (Z.to_nat s) OF_bits_tab 0
  | KML => nth (Z.to_nat s) ML_bits_tab 0
  end.
(* largest code, largest accuracy log, cells of the table field (SEQSYMBOL_TABLE_SIZE(maxLog)) *)
Definition sk_max (k: seqkind) : Z := match k with KLL => MaxLL | KOF => MaxOff | KML => MaxML end.
Definition sk_maxlog (k: seqkind) : Z := match k with KLL => LLFSELog | KOF => OffFSELog | KML => MLFSELog end.
Definition sk_size (k: seqkind) : Z := 1 + 2 ^ sk_maxlog k.
Definition sk_predef (k: seqkind) : fse_table :=
  match k with KLL => LL_predef | KOF => OF_predef | KML => ML_predef end.
(* the globals: the predefined table, the base and extra-bits tables *)
Definition sk_gdefault (k: seqkind) : ident :=
  match k with KLL => _LL_defaultDTable | KOF => _OF_defaultDTable | KML => _ML_defaultDTable end.
Definition sk_gbase (k: seqkind) : ident :=
  match k with KLL => _LL_base | KOF => _OF_base | KML => _ML_base end.
Definition sk_gbits (k: seqkind) : ident :=
  match k with KLL => _LL_bits | KOF => _OF_bits | KML => _ML_bits end.
(* the fields: of struct ZSTD_entropyDTables_t, and the table pointer of the context *)
Definition sk_tfield (k: seqkind) : ident :=
  match k with KLL => _LLTable | KOF => _OFTable | KML => _MLTable end.
Definition sk_pfield (k: seqkind) : ident :=
  match k with KLL => _LLTptr | KOF => _OFTptr | KML => _MLTptr end.

(* a well-formed decoding table of kind k: 2^log cells, symbols <= max, a state's next states inside the
   table *)
Definition fse_ok (k: seqkind) (t: fse_table) : Prop :=
  0 <= ft_log t <= sk_maxlog k /\ Zlength (ft_cells t) = 2 ^ ft_log t /\
  Forall (fun e => 0 <= fe_sym e <= sk_max k /\ 0 <= fe_nb e <= ft_log t /\
                   0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ ft_log t) (ft_cells t).

(* the C cell of a model cell: nextState, nbAdditionalBits, nbBits, baseValue *)
Definition seqcell (k: seqkind) (e: fse_entry) : val * (val * (val * val)) :=
  (Vint (Int.repr (fe_base e)),
   (Vint (Int.repr (sk_bits k (fe_sym e))),
    (Vint (Int.repr (fe_nb e)), Vint (Int.repr (sk_base k (fe_sym e)))))).

(* A table at p: the header (fastMode = fm, unused by the sequence decoder; tableLog) in cell 0, then the
   2^log cells.  The predefined tables (globals) have a fixed fm. *)
Definition seqtab_at_fm (sh: share) (k: seqkind) (t: fse_table) (fm: Z) (p: val) : mpred :=
  !! (fse_ok k t /\ 0 <= fm <= Int.max_unsigned) &&
  (data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) p *
   data_at sh (tarray t_seqSymbol (2 ^ ft_log t)) (map (seqcell k) (ft_cells t)) (offset_val 8 p)).

Definition seqtab_at (sh: share) (k: seqkind) (t: fse_table) (p: val) : mpred :=
  EX fm: Z, seqtab_at_fm sh k t fm p.

(* A table field (sk_size k cells at p, in a context or a DDict): no table, or the table t in front *)
Definition seqspace_at (sh: share) (k: seqkind) (ot: option fse_table) (p: val) : mpred :=
  match ot with
  | None => data_at_ sh (tarray t_seqSymbol (sk_size k)) p
  | Some t =>
      seqtab_at sh k t p *
      data_at_ sh (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t)) (offset_val (8 * (1 + 2 ^ ft_log t)) p)
  end.

(* the fastMode field the globals hold in cell 0 ({1, 1, 1, log} read as {fastMode, tableLog}) *)
Definition predef_fm : Z := 16842753.   (* 0x01010001 *)

(* ===================== Huffman tables ===================== *)

(* a well-formed Huffman table: its canonical cells (model huf_cells) *)
Definition huf_ok (ht: huf_table) : Prop :=
  1 <= ht_log ht <= HUF_TABLELOG_MAX /\ Zlength (huf_cells ht) = 2 ^ ht_log ht /\
  Forall (fun c => 0 <= fst c < 256 /\ 1 <= snd c <= ht_log ht) (huf_cells ht).

(* hsym ht L x, the symbol and code length of the L-bit value x (L >= ht_log), is model/HufC.v's *)

(* X1 cells (HUF_DEltX1 {nbBits; byte}): determined by the table *)
Definition x1cell (c: Z * Z) : val * val := (Vint (Int.repr (snd c)), Vint (Int.repr (fst c))).
Definition x1_cells (ht: huf_table) (L: Z) : list (val * val) :=
  map (fun n => x1cell (hsym ht L (Z.of_nat n))) (seq 0 (Z.to_nat (2 ^ L))).

(* An X2 cell (HUF_DEltX2 {sequence; nbBits; length}) at the L-bit value v: one symbol (the first one, its
   code length; the high byte of sequence is any byte) or two symbols whose codes both fit in the L bits *)
Definition x2_cell_ok (ht: huf_table) (L v: Z) (c: val * (val * val)) : Prop :=
  let '(s1, n1) := hsym ht L v in
  (exists hi, 0 <= hi < 256 /\ c = (Vint (Int.repr (s1 + 256 * hi)), (Vint (Int.repr n1), Vint (Int.repr 1)))) \/
  (let '(s2, n2) := hsym ht L ((v * 2 ^ n1) mod 2 ^ L) in
   n1 + n2 <= L /\ c = (Vint (Int.repr (s1 + 256 * s2)), (Vint (Int.repr (n1 + n2)), Vint (Int.repr 2)))).

(* The 4097 U32s of a HUF_DTable at p (hufTable[HUF_DTABLE_SIZE(12)]): the descriptor DTableDesc
   {maxTableLog = 12; tableType; tableLog; reserved} in front, then 16384 bytes of cells. *)
Definition HUF_CELLBYTES : Z := 16384.

(* only the descriptor's maxTableLog (ZSTD_decompressBegin, ZSTD_initDDict_internal: hufTable[0] =
   12 * 0x1000001): a table to be built.  The other three descriptor bytes are defined bytes: HUF_getDTableDesc
   copies the descriptor with memcpy, libc.c's byte loop (QuickProof v0.1.0-beta.1). *)
Definition hufhdr_at (sh: share) (p: val) : mpred :=
  EX ty: val, EX lg: val, EX res: val,
  !! (align_compatible tuint p /\ byte_val ty /\ byte_val lg /\ byte_val res) &&
  data_at sh t_dtdesc (Vint (Int.repr 12), (ty, (lg, res))) p *
  memory_block sh HUF_CELLBYTES (offset_val 4 p).

(* the log of the table zstd's reader of type x2 builds from ht (ExHuf.xhuf_of): X1 max(tableLog, 11), X2 11 or 12 *)
Definition hufdt_log (x2: bool) (ht: huf_table) : Z := if x2 then xh_x2_log ht else xh_x1_log ht.

(* an X2 cell (sequence, nbBits, length) of ExHuf.xh_cells_x2 as the HUF_DEltX2 struct's fields *)
Definition x2v (c: Z * Z * Z) : val * (val * val) :=
  let '(sq, nb, len) := c in (Vint (Int.repr sq), (Vint (Int.repr nb), Vint (Int.repr len))).

(* the table ht, as X1 (x2 = false, tableType 0) or X2 (tableType 1) cells of log L; the reserved
   descriptor byte is whatever byte it was (the builders copy the descriptor back).  The log and the cells are
   exactly those of ExHuf.xhuf_of x2 ht (L = hufdt_log x2 ht; the X2 cells are xh_cells_x2 ht L, which also
   satisfy x2_cell_ok, the description by what they decode). *)
Definition hufdt_x_at (x2: bool) (sh: share) (ht: huf_table) (p: val) : mpred :=
  EX L: Z, EX res: val,
  !! (huf_ok ht /\ ht_log ht <= L <= HUF_TABLELOG_MAX /\ align_compatible tuint p /\ byte_val res /\
      L = hufdt_log x2 ht) &&
  data_at sh t_dtdesc (Vint (Int.repr 12), (Vint (Int.repr (if x2 then 1 else 0)),
                                             (Vint (Int.repr L), res))) p *
  (if x2 then
     EX c2: list (val * (val * val)),
     !! (Zlength c2 = 2 ^ L /\ (forall v, 0 <= v < 2 ^ L -> x2_cell_ok ht L v (Znth v c2)) /\
         c2 = map x2v (xh_cells_x2 ht L)) &&
     (data_at sh (tarray t_deltx2 (2 ^ L)) c2 (offset_val 4 p) *
      memory_block sh (HUF_CELLBYTES - 4 * 2 ^ L) (offset_val (4 + 4 * 2 ^ L) p))
   else
     data_at sh (tarray t_deltx1 (2 ^ L)) (x1_cells ht L) (offset_val 4 p) *
     memory_block sh (HUF_CELLBYTES - 2 * 2 ^ L) (offset_val (4 + 2 * 2 ^ L) p)).

Definition hufdt_at (sh: share) (ht: huf_table) (p: val) : mpred :=
  EX x2: bool, hufdt_x_at x2 sh ht p.

(* ===================== the entropy state ===================== *)

Definition rep_ok (r: Z * Z * Z) : Prop :=
  let '(r1, r2, r3) := r in 1 <= r1 < 2 ^ 32 /\ 1 <= r2 < 2 ^ 32 /\ 1 <= r3 < 2 ^ 32.

Definition rep_vals (r: Z * Z * Z) : list val :=
  let '(r1, r2, r3) := r in [Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3)].

Definition seqs_ok (o: option (fse_table * fse_table * fse_table)) : Prop :=
  match o with Some (a, b, c) => fse_ok KLL a /\ fse_ok KOF b /\ fse_ok KML c | None => True end.

Definition dstate_ok (st: dstate) : Prop :=
  match st_huf st with Some ht => huf_ok ht | None => True end /\ seqs_ok (st_seq st) /\ rep_ok (st_rep st).

Definition seq_of (k: seqkind) (o: option (fse_table * fse_table * fse_table)) : option fse_table :=
  match o with
  | Some (a, b, c) => Some (match k with KLL => a | KOF => b | KML => c end)
  | None => None
  end.

(* ---------- DENT: a DDict's entropy field ---------- *)

Definition dd_huf (q: val) : val := field_address t_entropy_dd (DOT _entropy DOT _hufTable) q.
Definition dd_seq (k: seqkind) (q: val) : val := field_address t_entropy_dd (DOT _entropy DOT sk_tfield k) q.

(* None: anything.  Some st (a formatted dictionary's tables, ZSTD_loadDEntropy): the Huffman table, the
   three sequence tables, the repeat offsets. *)
Definition dent_def (gv: globals) (q: val) (oe: option dstate) : mpred :=
  match oe with
  | None => field_at_ Ews t_entropy_dd (DOT _entropy) q
  | Some st =>
      match st_huf st, st_seq st with
      | Some ht, Some (a, b, c) =>
          !! (dstate_ok st) &&
          (hufdt_at Ews ht (dd_huf q) *
           seqspace_at Ews KLL (Some a) (dd_seq KLL q) *
           seqspace_at Ews KOF (Some b) (dd_seq KOF q) *
           seqspace_at Ews KML (Some c) (dd_seq KML q) *
           field_at Ews t_entropy_dd (DOT _entropy DOT _rep) (rep_vals (st_rep st)) q *
           field_at_ Ews t_entropy_dd (DOT _entropy DOT _workspace) q)
      | _, _ => FF
      end
  end.

(* the tables of the DDict ox the context may use *)
Definition ox_ent (ox: option ddx) : option dstate :=
  match ox with Some x => ddx_ent x | None => None end.
Definition ox_huf (ox: option ddx) : option huf_table :=
  match ox_ent ox with Some st => st_huf st | None => None end.
Definition ox_seq (k: seqkind) (ox: option ddx) : option fse_table :=
  match ox_ent ox with Some st => seq_of k (st_seq st) | None => None end.
Definition ox_q (ox: option ddx) : val := match ox with Some x => dx_q x | None => nullval end.

(* ---------- TABS: the tables group of a context ---------- *)

Definition ctx_huf (p: val) : val := field_address t_dctx (DOT _entropy DOT _hufTable) p.
Definition ctx_seq (k: seqkind) (p: val) : val := field_address t_dctx (DOT _entropy DOT sk_tfield k) p.

(* where a table the context uses lives *)
Inductive tloc := TCtx | TDict | TGlob.

(* the Huffman part: HUFptr, litEntropy (1 iff there is a table), the context's hufTable; x2: the type of the
   context's table (X1 / X2, irrelevant without a table or with a DDict's table) *)
Definition tabs_huf (gv: globals) (p: val) (ox: option ddx) (oh: option huf_table) (x2: bool) : mpred :=
  EX hp: val,
  field_at Ews t_dctx (DOT _HUFptr) hp p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr (match oh with Some _ => 1 | None => 0 end))) p *
  match oh with
  | None => !! (hp = ctx_huf p) && hufhdr_at Ews (ctx_huf p)
  | Some ht =>
      EX w: bool,
      if w then !! (hp = ctx_huf p) && hufdt_x_at x2 Ews ht (ctx_huf p)
      else !! (ox_huf ox = Some ht /\ hp = dd_huf (ox_q ox)) && hufhdr_at Ews (ctx_huf p)
  end.

(* the context's pointer to its table of kind k *)
Definition seq_ptr_at (p: val) (k: seqkind) (tp: val) : mpred :=
  match k with
  | KLL => field_at Ews t_dctx (DOT _LLTptr) tp p
  | KOF => field_at Ews t_dctx (DOT _OFTptr) tp p
  | KML => field_at Ews t_dctx (DOT _MLTptr) tp p
  end.

(* one sequence table of kind k: its pointer and the context's table field *)
Definition seq_where (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) : mpred :=
  EX tp: val, EX w: tloc,
  seq_ptr_at p k tp *
  match w with
  | TCtx => !! (tp = ctx_seq k p) && seqspace_at Ews k (Some t) (ctx_seq k p)
  | TDict => !! (ox_seq k ox = Some t /\ tp = dd_seq k (ox_q ox)) && seqspace_at Ews k None (ctx_seq k p)
  | TGlob => !! (t = sk_predef k /\ tp = gv (sk_gdefault k)) && seqspace_at Ews k None (ctx_seq k p)
  end.

(* the sequence part: fseEntropy = fe (TABS: 1 iff there are tables), the three tables *)
Definition tabs_seq (gv: globals) (p: val) (ox: option ddx) (os: option (fse_table * fse_table * fse_table))
    (fe: Z) : mpred :=
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p *
  match os with
  | None =>
      field_at_ Ews t_dctx (DOT _LLTptr) p * field_at_ Ews t_dctx (DOT _OFTptr) p *
      field_at_ Ews t_dctx (DOT _MLTptr) p *
      seqspace_at Ews KLL None (ctx_seq KLL p) * seqspace_at Ews KOF None (ctx_seq KOF p) *
      seqspace_at Ews KML None (ctx_seq KML p)
  | Some (a, b, c) => seq_where gv p ox KLL a * seq_where gv p ox KOF b * seq_where gv p ox KML c
  end.

(* the fields of the group B uses as scratch between calls (litExtraBuffer, whose bytes are part of the state,
   apart) *)
Definition tabs_scratch (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p.

(* the tables of ts: the Huffman table of type ts_x2, the sequence tables, the repeat offsets, litExtraBuffer
   holding ts_lxb *)
Definition tabs_def (gv: globals) (p: val) (ox: option ddx) (ts: tstate) : mpred :=
  !! (dstate_ok ts) &&
  (tabs_huf gv p ox (st_huf ts) (ts_x2 ts) *
   tabs_seq gv p ox (st_seq ts) (match st_seq ts with Some _ => 1 | None => 0 end) *
   field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (st_rep ts)) p *
   tabs_scratch p * lit_extra_at p (ts_lxb ts)).

(* ===================== sanity checks of the representation ===================== *)

(* the predefined tables are well formed *)
Example predef_ok : fse_ok KLL LL_predef /\ fse_ok KOF OF_predef /\ fse_ok KML ML_predef.
Proof.
  unfold fse_ok; vm_compute; repeat split; try discriminate; repeat constructor; discriminate.
Qed.

(* the predefined tables of the globals are the model's (cells 1..), with tableLog in cell 0 *)
Example predef_cells :
  tl LL_defaultDTable_val = map (seqcell KLL) (ft_cells LL_predef) /\
  tl OF_defaultDTable_val = map (seqcell KOF) (ft_cells OF_predef) /\
  tl ML_defaultDTable_val = map (seqcell KML) (ft_cells ML_predef).
Proof. vm_compute. repeat split; reflexivity. Qed.
