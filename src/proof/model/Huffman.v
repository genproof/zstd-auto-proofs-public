(* The format model: Huffman coding of literals (RFC 8878, 4.2).

   A table is given by its weights: symbol s has weight w(s) in 0..tableLog (0 = absent) and a code
   of tableLog + 1 - w(s) bits.  The decoding table has 2^tableLog cells, filled by weight
   increasing, then symbol increasing, each symbol taking 2^(w-1) consecutive cells; decoding peeks
   tableLog bits (zeros past the end of the stream), and the cell gives the symbol and how many bits
   it consumes.  This is the canonical code of the specification (harness/build.h's huf_pick
   computes the same codes).

   The weights are described directly (header byte >= 128: two per byte) or FSE-compressed (header
   byte < 128 = the size of the compressed weights: an FSE table description (NCount.v) then one
   backward bitstream decoded with two interleaved states, as zstd's FSE_decompress_usingDTable_generic
   does).  The checks are those of zstd's HUF_readStats_body (lib/common/entropy_common.c). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse Zstd.proof.model.NCount.

Record huf_table := { ht_log : Z; ht_weights : list Z  (* weight of symbol s, s < length *) }.

Definition HUF_TABLELOG_MAX : Z := 12.

Definition huf_cells (t: huf_table) : list (Z * Z) :=
  let ws := ht_weights t in
  let log := ht_log t in
  flat_map (fun w =>
    flat_map (fun s =>
      if nth s ws 0 =? w then repeat (Z.of_nat s, log + 1 - w) (Z.to_nat (2 ^ (w - 1))) else nil)
      (seq 0 (length ws)))
    (map Z.of_nat (seq 1 (Z.to_nat log))).

(* the weights of the direct representation: oSize weights, two per byte, high nibble first *)
Definition huf_direct_weights (b: list Z) (oSize: Z) : list Z :=
  map (fun n => let byte := byte_at b (1 + Z.of_nat n / 2) in
                if Nat.even n then Z.shiftr byte 4 else Z.land byte 15)
      (seq 0 (Z.to_nat oSize)).

(* FSE-compressed weights: two states over one backward bitstream of value V (pos = payload bits
   not yet read).  Emit the symbol of state 1 and update it (read its nbBits); if that read went past
   the payload (pos < 0), emit the symbol of state 2 and stop; then the same with the states swapped.
   (zstd: the tail loop of FSE_decompress_usingDTable_generic; its 4-symbol fast loop cannot run past
   the payload.)  acc = the symbols so far. *)
Fixpoint fse2_loop (fuel: nat) (t: fse_table) (V: list Z) (pos s1 s2: Z) (acc: list Z) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
      let e1 := fse_cell t s1 in
      let acc := acc ++ [fe_sym e1] in
      let pos := pos - fe_nb e1 in
      if pos <? 0 then Some (acc ++ [fe_sym (fse_cell t s2)]) else
      let s1 := fe_base e1 + bs_peek_s V (pos + fe_nb e1) (fe_nb e1) in
      let e2 := fse_cell t s2 in
      let acc := acc ++ [fe_sym e2] in
      let pos := pos - fe_nb e2 in
      if pos <? 0 then Some (acc ++ [fe_sym (fse_cell t s1)]) else
      let s2 := fe_base e2 + bs_peek_s V (pos + fe_nb e2) (fe_nb e2) in
      fse2_loop f t V pos s1 s2 acc
  end.

(* FSE_decompress_wksp(dst, 255, b, length b, maxLog 6): the weights, at most 255; zstd's workspace
   (HUF_READ_STATS_WORKSPACE_SIZE, 876 bytes) must hold FSE_DECOMPRESS_WKSP_SIZE(log, last symbol) (it
   rejects e.g. log 6 with symbols above 11: weights the format does not allow) *)
Definition huf_fse_weights (b: list Z) : option (list Z) :=
  match read_ncount b 255 with
  | None => None
  | Some (norm, log, nsize) =>
      if log >? 6 then None else
      if 4 * ((2 ^ log + 1) + 1 + (2 * Zlength norm + 2 ^ log + 8 + 3) / 4 + 129) >? 876 then None else
      let t := fse_build norm log in
      let st := skipn (Z.to_nat nsize) b in
      if negb (bs_okb st) then None else
      let T := bs_total st in
      if T - 2 * log <? 0 then None else
      let s1 := bs_peek_s st T log in
      let s2 := bs_peek_s st (T - log) log in
      match fse2_loop 256 t st (T - 2 * log) s1 s2 nil with
      | Some ws => if Zlength ws >? 255 then None else Some ws
      | None => None
      end
  end.

(* The weights of a tree description at the start of b (all but the last, implied one) and the
   bytes the description takes. *)
Definition huf_desc_weights (b: list Z) : option (list Z * Z) :=
  if Zlength b <? 1 then None else
  let hb := byte_at b 0 in
  if hb >=? 128 then
    let oSize := hb - 127 in
    let iSize := (oSize + 1) / 2 in
    if Zlength b <? iSize + 1 then None else
    Some (huf_direct_weights b oSize, iSize + 1)
  else
    let iSize := hb in
    if Zlength b <? iSize + 1 then None else
    match huf_fse_weights (slice b 1 iSize) with
    | Some ws => Some (ws, iSize + 1)
    | None => None
    end.

(* Parse a tree description at the start of b (HUF_readStats): the table and the bytes it takes. *)
Definition huf_parse_desc (b: list Z) : option (huf_table * Z) :=
  match huf_desc_weights b with
  | None => None
  | Some (ws, size) =>
  if existsb (fun w => w >? HUF_TABLELOG_MAX) ws then None else
  let total := fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 ws in
  if total =? 0 then None else
  let tableLog := highbit total + 1 in
  if tableLog >? HUF_TABLELOG_MAX then None else
  let rest := 2 ^ tableLog - total in
  if negb (2 ^ highbit rest =? rest) then None else
  let ws := ws ++ [highbit rest + 1] in
  let rank1 := Z.of_nat (length (filter (fun w => w =? 1) ws)) in
  if orb (rank1 <? 2) (Z.odd rank1) then None else
  Some ({| ht_log := tableLog; ht_weights := ws |}, size)
  end.

(* Decode k symbols from position pos of a stream of value V; each step must stay in the stream. *)
Fixpoint huf_decode_syms (t: huf_table) (V: list Z) (k: nat) (pos: Z) : option (list Z * Z) :=
  match k with
  | O => Some (nil, pos)
  | S k' =>
      let '(s, nb) := nth (Z.to_nat (bs_peek_s V pos (ht_log t))) (huf_cells t) (0, 0) in
      if pos - nb <? 0 then None else
      match huf_decode_syms t V k' (pos - nb) with
      | Some (l, p) => Some (s :: l, p)
      | None => None
      end
  end.

(* One stream: the bytes s decode to exactly k symbols, consuming the whole stream. *)
Definition huf_decode_stream (t: huf_table) (s: list Z) (k: Z) : option (list Z) :=
  if negb (bs_okb s) then None else
  match huf_decode_syms t s (Z.to_nat k) (bs_total s) with
  | Some (l, 0) => Some l
  | _ => None
  end.

(* Four streams with a 6-byte jump table: segments of ceil(k/4) symbols, the last one the rest. *)
Definition huf_decode_4streams (t: huf_table) (b: list Z) (k: Z) : option (list Z) :=
  if Z.of_nat (length b) <? 10 then None else
  let s1 := le_field b 0 2 in
  let s2 := le_field b 2 2 in
  let s3 := le_field b 4 2 in
  let s4 := Z.of_nat (length b) - 6 - s1 - s2 - s3 in
  if s4 <? 1 then None else
  let seg := (k + 3) / 4 in
  if k - 3 * seg <? 0 then None else
  match huf_decode_stream t (slice b 6 s1) seg,
        huf_decode_stream t (slice b (6 + s1) s2) seg,
        huf_decode_stream t (slice b (6 + s1 + s2) s3) seg,
        huf_decode_stream t (slice b (6 + s1 + s2 + s3) s4) (k - 3 * seg) with
  | Some l1, Some l2, Some l3, Some l4 => Some (l1 ++ l2 ++ l3 ++ l4)
  | _, _, _, _ => None
  end.
