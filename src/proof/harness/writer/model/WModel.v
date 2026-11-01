(* The writer's model (plain Coq, unit-independent): the objects the
   writer's internal functions (harness/writer.h) build, and what they append to an output, in terms
   that the specifications of the v2 template WSpecs use.

   Two styles:
   - ENCODERS (deterministic functions: what the C code appends, bit for bit): the bit writer
     (fields_wl, bw_full/bw_pad/bw_mark), FSE table descriptions (fse_desc_bytes), Huffman streams
     (huf_stream_bytes), the FSE-compressed Huffman weights given their choices (hfw_bytes);
   - SEMANTIC predicates (what the format model's decoder makes of the bytes): Huffman tree
     descriptions (huf_desc_ok), literals sections (lit_ok), compressed blocks (decode_block), frames
     (zframe_ok).
   The lemmas connecting encoders to the decoder model are in WM_*.v. *)
Require Export Zstd.proof.harness.writer.WTop.
Require Export Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast
  Zstd.proof.model.NCount Zstd.proof.model.Fse Zstd.proof.model.Huffman Zstd.proof.model.Block
  Zstd.proof.model.Frame Zstd.proof.model.Info Zstd.proof.model.Xxh64 Zstd.proof.model.Series
  Zstd.proof.model.WriterFacts.
Local Open Scope bool_scope.

(* element i of a list of Z (0 out of range) *)
Definition zn (l: list Z) (i: Z) : Z := nth (Z.to_nat i) l 0.

(* sum of a list *)
Definition zsum (l: list Z) : Z := fold_right Z.add 0 l.

(* ---------------------------------------------------------------------------------------------- *)
(* the bit writer (bits_t): fields put least significant bit first *)

(* the bits written by bits_put calls with the fields fs = [(value, width); ...] (in writing order),
   after W (value) / L (number) bits already written *)
Fixpoint fields_wl (fs: list (Z * Z)) (W L: Z) : Z * Z :=
  match fs with
  | nil => (W, L)
  | (v, nb) :: fs' => fields_wl fs' (W + v * 2 ^ L) (L + nb)
  end.

Definition fields_W (fs: list (Z * Z)) : Z := fst (fields_wl fs 0 0).
Definition fields_L (fs: list (Z * Z)) : Z := snd (fields_wl fs 0 0).

(* the fields bits_put accepts: nb <= 32, v < 2^nb *)
Definition fields_ok (fs: list (Z * Z)) : Prop :=
  Forall (fun f => 0 <= snd f <= 32 /\ 0 <= fst f < 2 ^ snd f) fs.

(* bits_t holding W / L (0 <= W < 2^L): the bytes it has put (the full bytes), its acc and bits *)
Definition bw_full (W L: Z) : list Z := le_bytes (Z.to_nat (L / 8)) W.
Definition bw_acc (W L: Z) : Z := W / 2 ^ (8 * (L / 8)).
Definition bw_bits (L: Z) : Z := L mod 8.

(* all the bytes after bits_pad (a forward bitstream: FSE table descriptions) *)
Definition bw_pad (W L: Z) : list Z := le_bytes (Z.to_nat ((L + 7) / 8)) W.

(* all the bytes after bits_end_mark (a backward bitstream: the end mark at bit L) *)
Definition bw_mark (W L: Z) : list Z := le_bytes (Z.to_nat (L / 8 + 1)) (W + 2 ^ L).

Definition fields_pad (fs: list (Z * Z)) : list Z := bw_pad (fields_W fs) (fields_L fs).
Definition fields_mark (fs: list (Z * Z)) : list Z := bw_mark (fields_W fs) (fields_L fs).

(* ---------------------------------------------------------------------------------------------- *)
(* FSE tables (fse_t) *)

(* a normalized distribution as fse_pick draws it: accuracy log 5..9, counts >= -1 summing (with -1
   as 1) to 2^log, at least two non-zero, the last one non-zero *)
Definition ncount_of (p: Z) : Z := if p =? -1 then 1 else p.

Definition ndist_ok (log: Z) (norm: list Z) : Prop :=
  5 <= log <= 9 /\ 1 <= Zlength norm <= 53 /\
  Forall (fun p => -1 <= p <= 2 ^ log) norm /\
  zsum (map ncount_of norm) = 2 ^ log /\
  2 <= Zlength (filter (fun p => negb (p =? 0)) norm) /\
  last norm 0 <> 0.

(* ... over symbols 0..maxsym, every needed symbol (need[s] <> 0) with a non-zero count *)
Definition ndist_need (maxsym: Z) (need: list Z) (norm: list Z) : Prop :=
  Zlength norm <= maxsym + 1 /\
  forall s, 0 <= s <= maxsym -> zn need s <> 0 -> s < Zlength norm /\ zn norm s <> 0.

(* the table of a fse_t: log = 0 is an RLE table of the symbol nsym - 1 (fse_rle); else the table
   built from norm (fse_build; predefined tables are built the same way) *)
Record wfse := { wf_log : Z; wf_nsym : Z; wf_norm : list Z }.

Definition wf_table (F: wfse) : fse_table :=
  if wf_log F =? 0 then Fse.fse_rle (wf_nsym F - 1) else fse_build (wf_norm F) (wf_log F).

(* the distributions the writer builds tables from: drawn ones and the predefined ones *)
Definition ndist_base (log: Z) (norm: list Z) : Prop :=
  5 <= log <= 9 /\ 1 <= Zlength norm <= 53 /\
  Forall (fun p => -1 <= p <= 2 ^ log) norm /\
  zsum (map ncount_of norm) = 2 ^ log.

Definition wf_ok (F: wfse) : Prop :=
  if wf_log F =? 0 then 1 <= wf_nsym F <= 53
  else ndist_base (wf_log F) (wf_norm F) /\ wf_nsym F = Zlength (wf_norm F).

Definition rle_wfse (sym: Z) : wfse := {| wf_log := 0; wf_nsym := sym + 1; wf_norm := nil |}.

(* fse_predefined(t, type): 0 literals lengths, 1 offsets, 2 match lengths *)
Definition pre_wfse (ty: Z) : wfse :=
  if ty =? 0 then {| wf_log := 6; wf_nsym := 36; wf_norm := LL_norm |}
  else if ty =? 1 then {| wf_log := 5; wf_nsym := 29; wf_norm := OF_norm |}
  else {| wf_log := 6; wf_nsym := 53; wf_norm := ML_norm |}.

(* fse_has(t, s) *)
Definition fse_has_b (F: wfse) (s: Z) : bool :=
  if wf_log F =? 0 then (wf_nsym F - 1 =? s)
  else (s <? wf_nsym F) && negb (zn (wf_norm F) s =? 0).

(* fse_states: states sts of the codes cs, read in this order by one FSE state of table tab: each
   state has its code's symbol, and the next state is in the range [base, base + 2^nb) of the
   current one *)
Definition fse_chain (tab: fse_table) (cs sts: list Z) : Prop :=
  Zlength sts = Zlength cs /\
  (forall i, 0 <= i < Zlength cs ->
     0 <= zn sts i < 2 ^ ft_log tab /\ fe_sym (fse_cell tab (zn sts i)) = zn cs i) /\
  (forall i, 0 <= i < Zlength cs - 1 ->
     fe_base (fse_cell tab (zn sts i)) <= zn sts (i + 1) <
       fe_base (fse_cell tab (zn sts i)) + 2 ^ fe_nb (fse_cell tab (zn sts i))).

(* fse_put_description: Accuracy_Log - 5 in 4 bits, then each count (value p + 1) in a variable-size
   field, a count 0 followed by 2-bit repeat flags for the zeros after it *)
Fixpoint zrun (l: list Z) : nat :=
  match l with
  | p :: l' => if p =? 0 then S (zrun l') else O
  | nil => O
  end.

Definition ncount_field (p remaining: Z) : Z * Z :=
  let bits := highbit (remaining + 1) + 1 in
  let threshold := 2 ^ bits - 1 - (remaining + 1) in
  let lower_mask := 2 ^ (bits - 1) - 1 in
  let val := p + 1 in
  if val <? threshold then (val, bits - 1)
  else if val <=? lower_mask then (val, bits)
  else (val + threshold, bits).

Fixpoint ncount_fields (fuel: nat) (norm: list Z) (remaining: Z) : list (Z * Z) :=
  match fuel with
  | O => nil
  | S f =>
      match norm with
      | nil => nil
      | p :: rest =>
          let fld := ncount_field p remaining in
          let remaining := remaining - ncount_of p in
          if p =? 0 then
            let z := zrun rest in
            fld :: repeat (3, 2) (z / 3) ++ [(Z.of_nat (z mod 3), 2)] ++
              ncount_fields f (skipn z rest) remaining
          else fld :: ncount_fields f rest remaining
      end
  end.

Definition fse_desc_fields (norm: list Z) (log: Z) : list (Z * Z) :=
  (log - 5, 4) :: ncount_fields (length norm) norm (2 ^ log).

Definition fse_desc_bytes (norm: list Z) (log: Z) : list Z := fields_pad (fse_desc_fields norm log).

(* ---------------------------------------------------------------------------------------------- *)
(* Huffman codes (huf_t) *)

(* w: the weights of symbols 0..255 (0 = absent); log: Max_Number_of_Bits; last: the highest present
   symbol; used: the present symbols, increasing *)
Record whuf := { wh_w : list Z; wh_log : Z; wh_last : Z; wh_used : list Z }.

Definition wh_weight (H: whuf) (s: Z) : Z := zn (wh_w H) s.

Definition syms256 : list Z := map Z.of_nat (seq 0 256).

(* the canonical code (Huffman.huf_cells' order: by weight, then symbol; 2^(w-1) cells each) *)
Definition huf_nb_of (H: whuf) (s: Z) : Z := wh_log H + 1 - wh_weight H s.

Definition huf_start (H: whuf) (s: Z) : Z :=
  let w := wh_weight H s in
  zsum (map (fun s' => let w' := wh_weight H s' in
                       if (0 <? w') && ((w' <? w) || ((w' =? w) && (s' <? s))) then 2 ^ (w' - 1) else 0)
            syms256).

Definition huf_code_of (H: whuf) (s: Z) : Z := huf_start H s / 2 ^ (wh_weight H s - 1).

(* the decoder's table *)
Definition huf_model (H: whuf) : huf_table :=
  {| ht_log := wh_log H; ht_weights := firstn (Z.to_nat (wh_last H + 1)) (wh_w H) |}.

(* what huf_pick draws: a complete prefix code (Kraft sum 2^log) of 2 to 256 symbols, codes of at
   most 11 bits *)
Definition huf_ok (H: whuf) : Prop :=
  Zlength (wh_w H) = 256 /\ 1 <= wh_log H <= 11 /\
  Forall (fun w => 0 <= w <= wh_log H) (wh_w H) /\
  zsum (map (fun w => if w =? 0 then 0 else 2 ^ (w - 1)) (wh_w H)) = 2 ^ wh_log H /\
  wh_used H = filter (fun s => negb (wh_weight H s =? 0)) syms256 /\
  2 <= Zlength (wh_used H) /\
  wh_last H = last (wh_used H) 0 /\
  In 1 (wh_w H).

Definition huf_present (H: whuf) (s: Z) : Prop := 0 <= s < 256 /\ wh_weight H s <> 0.

(* huf_put_stream: the codes of lit[k-1], ..., lit[0] (lit[0] is read first), then the end mark *)
Definition huf_stream_fields (H: whuf) (lits: list Z) : list (Z * Z) :=
  map (fun c => (huf_code_of H c, huf_nb_of H c)) (rev lits).

Definition huf_stream_bytes (H: whuf) (lits: list Z) : list Z := fields_mark (huf_stream_fields H lits).

(* huf_put_description's direct form: 127 + last, then the weights of 0..last-1, two per byte *)
Definition huf_direct_bytes (H: whuf) : list Z :=
  (127 + wh_last H) ::
    map (fun j => wh_weight H (2 * Z.of_nat j) * 16 +
                  (if 2 * Z.of_nat j + 1 <? wh_last H then wh_weight H (2 * Z.of_nat j + 1) else 0))
        (seq 0 (Z.to_nat ((wh_last H + 1) / 2))).

(* huf_put_fse_weights: the weights ws = w[0..last) FSE-compressed with a table of log 5 or 6 drawn by
   fse_pick (need: the weights that occur) and the states sts (one per weight): two interleaved chains
   (sts[i] leads to sts[i+2]), the state of weight last-2 reads at least one bit *)
Definition hfw_weights (H: whuf) : list Z := firstn (Z.to_nat (wh_last H)) (wh_w H).

Definition need_of (ws: list Z) : list Z :=
  map (fun s => if existsb (Z.eqb (Z.of_nat s)) ws then 1 else 0) (seq 0 53).

Definition hfw_ok (H: whuf) (norm: list Z) (log: Z) (sts: list Z) : Prop :=
  let n := wh_last H in
  let ws := hfw_weights H in
  let tab := fse_build norm log in
  2 <= n <= 255 /\ 5 <= log <= 6 /\
  ndist_ok log norm /\ ndist_need 11 (need_of ws) norm /\
  Zlength sts = n /\
  (forall i, 0 <= i < n -> 0 <= zn sts i < 2 ^ log /\ fe_sym (fse_cell tab (zn sts i)) = zn ws i) /\
  (forall i, 0 <= i < n - 2 ->
     fe_base (fse_cell tab (zn sts i)) <= zn sts (i + 2) <
       fe_base (fse_cell tab (zn sts i)) + 2 ^ fe_nb (fse_cell tab (zn sts i))) /\
  0 < fe_nb (fse_cell tab (zn sts (n - 2))).

(* the bitstream: written: for i = n-3 downto 0 the update from sts[i] to sts[i+2], then sts[1],
   sts[0] in log bits; then the end mark *)
Definition hfw_fields (H: whuf) (norm: list Z) (log: Z) (sts: list Z) : list (Z * Z) :=
  let n := wh_last H in
  let tab := fse_build norm log in
  map (fun j => let i := n - 3 - Z.of_nat j in
                (zn sts (i + 2) - fe_base (fse_cell tab (zn sts i)), fe_nb (fse_cell tab (zn sts i))))
      (seq 0 (Z.to_nat (n - 2))) ++
  [(zn sts 1, log); (zn sts 0, log)].

Definition hfw_bytes (H: whuf) (norm: list Z) (log: Z) (sts: list Z) : list Z :=
  fse_desc_bytes norm log ++ fields_mark (hfw_fields H norm log sts).

(* a Huffman tree description of H (huf_put_description), followed by anything *)
Definition huf_desc_ok (H: whuf) (bs: list Z) : Prop :=
  bytes_ok bs /\ 2 <= Zlength bs <= 128 /\
  forall rest, huf_parse_desc (bs ++ rest) = Some (huf_model H, Zlength bs).

(* ---------------------------------------------------------------------------------------------- *)
(* literals sections *)

(* bs is a literals section that decodes, with the previous Huffman table hprev and Block_Maximum_Size
   bsm, to lits and leaves the Huffman table hnew; the sequences section (at least one byte) follows *)
Definition lit_ok (hprev: option huf_table) (bsm: Z) (lits: list Z) (hnew: option huf_table) (bs: list Z)
    : Prop :=
  bytes_ok bs /\
  forall rest, 1 <= Zlength rest -> decode_literals hprev (bs ++ rest) bsm = Some (lits, Zlength bs, hnew).

(* the literal-length and match-length codes (ll_code, ml_code): the largest code whose baseline is
   <= x *)
Fixpoint lcode (base: list Z) (c: nat) (x: Z) : Z :=
  match c with
  | O => 0
  | S c' => if nth c base 0 <=? x then Z.of_nat c else lcode base c' x
  end.

Definition ll_code_of (ll: Z) : Z := lcode LL_base_tab 35 ll.
Definition ml_code_of (ml: Z) : Z := lcode ML_base_tab 52 ml.

(* ---------------------------------------------------------------------------------------------- *)
(* the state of a frame's decoding that later blocks depend on (wstate_t) *)

Record wst := { wt_rep : Z * Z * Z; wt_huf : option whuf; wt_tabs : option (wfse * wfse * wfse) }.

Definition wt_dstate (S: wst) : dstate :=
  {| st_huf := option_map huf_model (wt_huf S);
     st_seq := option_map (fun '(a, b, c) => (wf_table a, wf_table b, wf_table c)) (wt_tabs S);
     st_rep := wt_rep S |}.

Definition wt_ok (S: wst) : Prop :=
  (let '(r1, r2, r3) := wt_rep S in 1 <= r1 < 2 ^ 32 /\ 1 <= r2 < 2 ^ 32 /\ 1 <= r3 < 2 ^ 32) /\
  (forall H, wt_huf S = Some H -> huf_ok H) /\
  (forall a b c, wt_tabs S = Some (a, b, c) -> wf_ok a /\ wf_ok b /\ wf_ok c).

Definition wst_init : wst := {| wt_rep := (1, 4, 8); wt_huf := None; wt_tabs := None |}.

(* ---------------------------------------------------------------------------------------------- *)
(* frames *)

(* the facts of one Zstandard frame written as the bytes fb, with content c and frame record f (whose
   start/cstart/size/csize are the series' business), followed by anything; see WriterFacts.frame_facts *)
Definition zframe_bound (f: winfo) : Z :=
  if wi_fcs_present f then wi_fcs f else wi_blocks f * Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX.

Definition zframe_ok (dm: dict_model) (f: winfo) (fb c: list Z) : Prop :=
  bytes_ok fb /\ bytes_ok c /\ wi_skippable f = false /\
  wi_fcs f = Zlength c /\
  wi_hsize f + 3 + (if wi_checksum f then 4 else 0) <= Zlength fb /\
  (forall t,
     is_frame (fb ++ t) = 1 /\
     is_skippable_frame (fb ++ t) = 0 /\
     frame_compressed_size (fb ++ t) = (if wi_big f then None else Some (Zlength fb)) /\
     get_frame_header (fb ++ t) = (if wi_big f then FH_err else FH_ok (wi_header f)) /\
     frame_content_size (fb ++ t) = (if wi_big f then ZSTD_CONTENTSIZE_ERROR
                                     else if wi_fcs_present f then wi_fcs f else ZSTD_CONTENTSIZE_UNKNOWN) /\
     dict_id_from_frame (fb ++ t) = (if wi_big f then 0 else wi_did f) /\
     frame_header_size (fb ++ t) = Some (wi_hsize f) /\
     frame_size_info (fb ++ t) = (if wi_big f then None else Some (Zlength fb, zframe_bound f)) /\
     (forall wl, decode_frame dm wl (fb ++ t) = if wi_rejected wl f then FDetHdr else FOk c (Zlength fb)) /\
     (forall wl, decode_frame dm wl (set_bit3 fb 4 ++ t) = FDetHdr) /\
     (wi_checksum f = true -> forall wl x, 0 < x < 2 ^ 32 -> wi_rejected wl f = false ->
        decode_frame dm wl (xor4 fb (Zlength fb - 4) x ++ t) = FDetCk)).
