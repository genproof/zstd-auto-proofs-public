(* The format model: compressed blocks (RFC 8878, 3.1.1.3 - 3.1.1.5), as zstd decodes them
   (lib/decompress/zstd_decompress_block.c).  Plain Coq, no VST.

   `decode_block st hist out b bsm wsize` decodes the body b of a compressed block: st = the entropy state
   the block may repeat (previous Huffman table, previous sequence tables, repeat offsets), hist = the
   dictionary content in front of the frame, out = the frame's output so far, bsm = the frame's
   Block_Maximum_Size, wsize = its Window_Size (a match reaches back at most wsize bytes into the frame's
   output, or into hist: offset <= wsize + |hist|; zstd's streaming decoder keeps no more history).
   It returns the new state and the block's content, or None.

   The model is exact where it returns Some: zstd's decoder (any of its paths: Huffman X1/X2 tables,
   single/4 streams, split literal buffer, short/long sequence decoders) produces this content and
   this state.  Where it returns None nothing is claimed: it may be stricter than zstd (e.g. matches
   are checked against the dictionary CONTENT only, never its header bytes; every block's content and
   size are bounded by Block_Maximum_Size), never more lenient.  The capacity of the output buffer
   plays no role: a one-shot decoder with too small a buffer fails, which the specifications allow. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Fse Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.BitsFast.
Local Open Scope bool_scope.

Definition MIN_LITERALS_FOR_4_STREAMS : Z := 6.
Definition LONGNBSEQ : Z := 32512.   (* 0x7F00 *)
Definition LLFSELog : Z := 9.
Definition MLFSELog : Z := 9.
Definition OffFSELog : Z := 8.

(* ---------- the entropy state between blocks (and from a dictionary) ---------- *)

(* st_huf: the Huffman table of the last compressed literals (dctx->HUFptr, litEntropy);
   st_seq: the three sequence tables LL, OF, ML of the last block with sequences (dctx->LLTptr,
   OFTptr, MLTptr, fseEntropy); st_rep: the repeat offsets (dctx->entropy.rep). *)
Record dstate := {
  st_huf : option huf_table;
  st_seq : option (fse_table * fse_table * fse_table);
  st_rep : Z * Z * Z
}.

(* ZSTD_decompressBegin without a dictionary *)
Definition dstate_init : dstate := {| st_huf := None; st_seq := None; st_rep := (1, 4, 8) |}.

(* ---------- literals section (ZSTD_decodeLiteralsBlock) ---------- *)

(* The literals of block body b, the bytes they take, and the new Huffman table. *)
Definition decode_literals (hprev: option huf_table) (b: list Z) (bsm: Z)
    : option (list Z * Z * option huf_table) :=
  let n := Zlength b in
  if n <? 2 then None else
  let b0 := byte_at b 0 in
  let ty := Z.land b0 3 in
  let lhl := Z.land (Z.shiftr b0 2) 3 in
  if ty =? 0 then
    (* raw *)
    let '(lh, litSize) :=
      if lhl =? 1 then (2, Z.shiftr (le_field b 0 2) 4)
      else if lhl =? 3 then (3, Z.shiftr (le_field b 0 3) 4)
      else (1, Z.shiftr b0 3) in
    if (lhl =? 3) && (n <? 3) then None else
    if litSize >? bsm then None else
    if lh + litSize >? n then None else
    Some (slice b lh litSize, lh + litSize, hprev)
  else if ty =? 1 then
    (* RLE *)
    let '(lh, litSize) :=
      if lhl =? 1 then (2, Z.shiftr (le_field b 0 2) 4)
      else if lhl =? 3 then (3, Z.shiftr (le_field b 0 3) 4)
      else (1, Z.shiftr b0 3) in
    if (lhl =? 1) && (n <? 3) then None else
    if (lhl =? 3) && (n <? 4) then None else
    if litSize >? bsm then None else
    Some (repeat (byte_at b lh) (Z.to_nat litSize), lh + 1, hprev)
  else
    (* compressed (2) or treeless (3) *)
    if (ty =? 3) && (match hprev with None => true | Some _ => false end) then None else
    if n <? 5 then None else
    let lhc := le_field b 0 4 in
    let '(lh, litSize, litCSize, single) :=
      if lhl =? 2 then (4, Z.land (Z.shiftr lhc 4) 16383, Z.shiftr lhc 18, false)
      else if lhl =? 3 then (5, Z.land (Z.shiftr lhc 4) 262143, Z.shiftr lhc 22 + byte_at b 4 * 1024, false)
      else (3, Z.land (Z.shiftr lhc 4) 1023, Z.land (Z.shiftr lhc 14) 1023, lhl =? 0) in
    if litSize >? bsm then None else
    if negb single && (litSize <? MIN_LITERALS_FOR_4_STREAMS) then None else
    if litCSize + lh >? n then None else
    let cb := slice b lh litCSize in
    let tbl :=
      if ty =? 2 then
        match huf_parse_desc cb with
        | Some (t, hsize) => if hsize >=? litCSize then None else Some (t, hsize)
        | None => None
        end
      else match hprev with Some t => Some (t, 0) | None => None end in
    match tbl with
    | None => None
    | Some (t, hsize) =>
        let streams := skipn (Z.to_nat hsize) cb in
        let lits := if single then huf_decode_stream t streams litSize
                    else huf_decode_4streams t streams litSize in
        match lits with
        | Some l => Some (l, lh + litCSize, Some t)
        | None => None
        end
    end.

(* ---------- sequences section header (ZSTD_decodeSeqHeaders, ZSTD_buildSeqTable) ---------- *)

(* The table of a code type from its mode (0 predefined, 1 RLE, 2 FSE-compressed, 3 repeat) and the
   bytes it takes; max = the largest code (MaxLL / MaxOff / MaxML), maxLog = LLFSELog / OffFSELog /
   MLFSELog. *)
Definition seq_table (mode: Z) (predef: fse_table) (prev: option fse_table) (max maxLog: Z) (b: list Z)
    : option (fse_table * Z) :=
  if mode =? 0 then Some (predef, 0)
  else if mode =? 1 then
    (if Zlength b <? 1 then None
     else if byte_at b 0 >? max then None
     else Some (fse_rle (byte_at b 0), 1))
  else if mode =? 3 then
    match prev with Some t => Some (t, 0) | None => None end
  else
    match read_ncount b max with
    | None => None
    | Some (norm, log, size) =>
        if log >? maxLog then None else Some (fse_build norm log, size)
    end.

(* The header of the sequences section: nbSeq, the tables (unchanged when nbSeq = 0), the bytes it
   takes. *)
Definition decode_seq_header (prev: option (fse_table * fse_table * fse_table)) (b: list Z)
    : option (Z * option (fse_table * fse_table * fse_table) * Z) :=
  let n := Zlength b in
  if n <? 1 then None else
  let b0 := byte_at b 0 in
  let '(nbSeq, pos, ok) :=
    if b0 <=? 127 then (b0, 1, true)
    else if b0 =? 255 then (le_field b 1 2 + LONGNBSEQ, 3, 3 <=? n)
    else ((b0 - 128) * 256 + byte_at b 1, 2, 2 <=? n) in
  if negb ok then None else
  if nbSeq =? 0 then (if pos =? n then Some (0, prev, pos) else None) else
  if pos + 1 >? n then None else
  let modes := byte_at b pos in
  if negb (Z.land modes 3 =? 0) then None else
  let pos := pos + 1 in
  let pLL := option_map (fun '(l, _, _) => l) prev in
  let pOF := option_map (fun '(_, o, _) => o) prev in
  let pML := option_map (fun '(_, _, m) => m) prev in
  match seq_table (Z.shiftr modes 6) LL_predef pLL MaxLL LLFSELog (skipn (Z.to_nat pos) b) with
  | None => None
  | Some (tLL, k1) =>
    let pos := pos + k1 in
    match seq_table (Z.land (Z.shiftr modes 4) 3) OF_predef pOF MaxOff OffFSELog (skipn (Z.to_nat pos) b) with
    | None => None
    | Some (tOF, k2) =>
      let pos := pos + k2 in
      match seq_table (Z.land (Z.shiftr modes 2) 3) ML_predef pML MaxML MLFSELog (skipn (Z.to_nat pos) b) with
      | None => None
      | Some (tML, k3) => Some (nbSeq, Some (tLL, tOF, tML), pos + k3)
      end
    end
  end.

(* ---------- sequences bitstream (ZSTD_decodeSequence) ---------- *)

(* A sequence: literal length, match length, offset value (RFC 3.1.1.3.2.1.1: 1..3 = repeat codes,
   > 3 = a new offset + 3) *)
Record sequence := { sq_ll : Z; sq_ml : Z; sq_ov : Z }.

(* read nb bits at pos from the stream s, if they are all in the stream *)
Definition rd (s: list Z) (pos nb: Z) : option (Z * Z) :=
  if pos - nb <? 0 then None else Some (bs_peek_s s pos nb, pos - nb).

(* Decode k sequences: for each: offset, match length, literal length extra bits; then (not after
   the last one) the states LL, ML, OF. *)
Fixpoint decode_seqs (tLL tOF tML: fse_table) (V: list Z) (k: nat) (sLL sOF sML pos: Z)
    : option (list sequence * Z) :=
  match k with
  | O => Some (nil, pos)
  | S k' =>
      let cLL := fe_sym (fse_cell tLL sLL) in
      let cOF := fe_sym (fse_cell tOF sOF) in
      let cML := fe_sym (fse_cell tML sML) in
      match rd V pos cOF with None => None | Some (eOF, pos) =>
      match rd V pos (nth (Z.to_nat cML) ML_bits_tab 0) with None => None | Some (eML, pos) =>
      match rd V pos (nth (Z.to_nat cLL) LL_bits_tab 0) with None => None | Some (eLL, pos) =>
      let sq := {| sq_ll := nth (Z.to_nat cLL) LL_base_tab 0 + eLL;
                   sq_ml := nth (Z.to_nat cML) ML_base_tab 0 + eML;
                   sq_ov := 2 ^ cOF + eOF |} in
      match k' with
      | O => Some ([sq], pos)
      | _ =>
        let eLL := fse_cell tLL sLL in
        match rd V pos (fe_nb eLL) with None => None | Some (uLL, pos) =>
        let eML := fse_cell tML sML in
        match rd V pos (fe_nb eML) with None => None | Some (uML, pos) =>
        let eOF := fse_cell tOF sOF in
        match rd V pos (fe_nb eOF) with None => None | Some (uOF, pos) =>
        match decode_seqs tLL tOF tML V k' (fe_base eLL + uLL) (fe_base eOF + uOF) (fe_base eML + uML) pos with
        | Some (l, p) => Some (sq :: l, p)
        | None => None
        end end end end
      end
      end end end
  end.

(* The sequences bitstream s: initial states LL, OF, ML, then exactly nbSeq sequences, consuming the
   whole stream. *)
Definition decode_seq_stream (tLL tOF tML: fse_table) (s: list Z) (nbSeq: Z) : option (list sequence) :=
  if negb (bs_okb s) then None else
  let V := s in
  match rd V (bs_total s) (ft_log tLL) with None => None | Some (sLL, pos) =>
  match rd V pos (ft_log tOF) with None => None | Some (sOF, pos) =>
  match rd V pos (ft_log tML) with None => None | Some (sML, pos) =>
  match decode_seqs tLL tOF tML V (Z.to_nat nbSeq) sLL sOF sML pos with
  | Some (l, 0) => Some l
  | _ => None
  end end end end.

(* ---------- executing sequences (ZSTD_execSequence) ---------- *)

(* The offset of a sequence and the new repeat offsets (RFC 3.1.1.5); None when it is 0. *)
Definition resolve_offset (rep: Z * Z * Z) (ll ov: Z) : option (Z * (Z * Z * Z)) :=
  let '(r1, r2, r3) := rep in
  if ov >? 3 then Some (ov - 3, (ov - 3, r1, r2)) else
  let idx := if ll =? 0 then ov + 1 else ov in
  if idx =? 1 then Some (r1, rep)
  else if idx =? 2 then Some (r2, (r2, r1, r3))
  else if idx =? 3 then Some (r3, (r3, r1, r2))
  else if r1 - 1 <=? 0 then None
  else Some (r1 - 1, (r1 - 1, r1, r2)).

(* copy ml bytes from `offset` back in hist ++ out, byte by byte (the copy may overlap what it
   writes); returns the new out *)
Fixpoint lz_copy (hist out: list Z) (offset: Z) (ml: nat) : list Z :=
  match ml with
  | O => out
  | S m => lz_copy hist (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - offset)]) offset m
  end.

(* Execute the sequences after the frame's output so far `out`, behind the dictionary content hist,
   with literals lits: the new output, the literals left, the repeat offsets.  A match may reach into
   hist (zstd: offset <= oLitEnd - virtualStart). *)
Fixpoint exec_seqs (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    : option (list Z * list Z * (Z * Z * Z)) :=
  match seqs with
  | nil => Some (out, lits, rep)
  | sq :: rest =>
      if sq_ll sq >? Zlength lits then None else
      let out := out ++ firstn (Z.to_nat (sq_ll sq)) lits in
      let lits := skipn (Z.to_nat (sq_ll sq)) lits in
      match resolve_offset rep (sq_ll sq) (sq_ov sq) with
      | None => None
      | Some (offset, rep) =>
          if offset >? Zlength hist + Zlength out then None else
          if offset >? wsize + Zlength hist then None else
          exec_seqs wsize rep hist lits (lz_copy hist out offset (Z.to_nat (sq_ml sq))) rest
      end
  end.

(* ---------- a compressed block (ZSTD_decompressBlock_internal) ---------- *)

(* The body b of a compressed block after the frame's output `out` (behind hist): the new state and
   the block's content. *)
Definition decode_block (st: dstate) (hist out: list Z) (b: list Z) (bsm wsize: Z)
    : option (dstate * list Z) :=
  if Zlength b >? bsm then None else
  match decode_literals (st_huf st) b bsm with
  | None => None
  | Some (lits, lused, huf) =>
    let rest := skipn (Z.to_nat lused) b in
    match decode_seq_header (st_seq st) rest with
    | None => None
    | Some (nbSeq, tabs, hused) =>
      let bits := skipn (Z.to_nat hused) rest in
      let seqs :=
        if nbSeq =? 0 then Some nil else
        match tabs with
        | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML bits nbSeq
        | None => None
        end in
      match seqs with
      | None => None
      | Some seqs =>
        match exec_seqs wsize (st_rep st) hist lits out seqs with
        | None => None
        | Some (out', lits', rep') =>
            let content := skipn (length out) (out' ++ lits') in
            if Zlength content >? bsm then None else
            Some ({| st_huf := huf; st_seq := tabs; st_rep := rep' |}, content)
        end
      end
    end
  end.
