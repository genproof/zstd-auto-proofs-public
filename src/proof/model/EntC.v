(* FSE_readNCount_body, FSE_decompress_wksp and HUF_readStats_body (lib/common/entropy_common.c,
   lib/common/fse_decompress.c) as the C computes them, on every input: None exactly when the C returns an
   error code.  Plain Coq over the format model.  The decoder's specifications (dec/B/ent/EntModel.v, which
   exports this file) and the exact model (ExHuf.v) state their results with these functions. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast.
Require Import Zstd.proof.model.Fse Zstd.proof.model.NCount Zstd.proof.model.Huffman.
Local Open Scope Z_scope.

(* ---------- FSE decoding of the Huffman weights (FSE_decompress_usingDTable_generic) ---------- *)

(* the symbols the two interleaved states decode from the backward bitstream st with table t, into a
   255-byte buffer (Huffman.huf_fse_weights after the description); None = C's error *)
Definition fse_weights_dec (t: fse_table) (st: list Z) : option (list Z) :=
  if negb (bs_okb st) then None else
  let T := bs_total st in
  let log := ft_log t in
  if T - 2 * log <? 0 then None else
  match fse2_loop 256 t st (T - 2 * log) (bs_peek_s st T log) (bs_peek_s st (T - log) log) nil with
  | Some ws => if Zlength ws >? 255 then None else Some ws
  | None => None
  end.

(* ---------- FSE_readNCount as C computes it, with its window re-reads ---------- *)

(* C re-reads its 32-bit window at ip <= iend - 4 with bitCount &= 31: a position at or past the end of the
   n-byte buffer (n >= 8) wraps back into its last 4 bytes *)
Definition wrapP (n p: Z) : Z := if p <? 8 * n then p else 8 * (n - 4) + (p - 8 * (n - 4)) mod 32.

(* up to k leading 2-bit repeat flags 0b11 at bit position p *)
Fixpoint reps (k: nat) (b: list Z) (p: Z) : Z :=
  match k with
  | O => 0
  | S k' => if fbits b p 2 =? 3 then 1 + reps k' b (p + 2) else 0
  end.

(* the zero-repeat scan: groups of 12 repeats (36 zeros, 24 bits, then a re-read), then the last group and
   the final 2-bit count; returns (zeros, new position) *)
Fixpoint zeros_c (fuel: nat) (b: list Z) (n p z: Z) : Z * Z :=
  match fuel with
  | O => (z, p)
  | S f =>
      let p := wrapP n p in
      let k := reps 12 b p in
      if k =? 12 then zeros_c f b n (p + 24) (z + 36)
      else (z + 3 * k + fbits b (p + 2 * k) 2, p + 2 * k + 2)
  end.

(* the main loop of FSE_readNCount_body (n = hbSize >= 8): Ncount.ncount_loop with C's re-reads *)
Fixpoint ncount_loop_c (fuel: nat) (b: list Z) (n maxsv1: Z) (p remaining threshold nbBits: Z)
    (prev0: bool) (acc: list Z) : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S f =>
      let '(acc, p, stop) :=
        if prev0 then
          let '(z, p') := zeros_c (Z.to_nat (8 * n + 8)) b n p 0 in
          let acc := acc ++ repeat 0 (Z.to_nat z) in
          (acc, p', Zlength acc >=? maxsv1)
        else (acc, p, false) in
      if stop then Some (acc, remaining, p) else
      let p := wrapP n p in
      let max := (2 * threshold - 1) - remaining in
      let low := fbits b p (nbBits - 1) in
      let '(count, p) :=
        if low <? max then (low, p + nbBits - 1)
        else let c := fbits b p nbBits in
             ((if c >=? threshold then c - max else c), p + nbBits) in
      let count := count - 1 in
      let remaining := if count >=? 0 then remaining - count else remaining + count in
      let acc := acc ++ [count] in
      let prev0 := count =? 0 in
      if andb (remaining <? threshold) (remaining <=? 1) then Some (acc, remaining, p) else
      let '(nbBits, threshold) :=
        if remaining <? threshold then (highbit remaining + 1, 2 ^ highbit remaining)
        else (nbBits, threshold) in
      if Zlength acc >=? maxsv1 then Some (acc, remaining, p) else
      ncount_loop_c f b n maxsv1 p remaining threshold nbBits prev0 acc
  end.

(* FSE_readNCount_body on hbSize >= 8 bytes b *)
Definition ncount_c (b: list Z) (maxsv: Z) : option (list Z * Z * Z) :=
  let n := Zlength b in
  let log := fbits b 0 4 + FSE_MIN_TABLELOG in
  if log >? FSE_TABLELOG_ABSOLUTE_MAX then None else
  match ncount_loop_c (Z.to_nat (maxsv + 2)) b n (maxsv + 1) 4 (2 ^ log + 1) (2 ^ log) (log + 1) false nil with
  | None => None
  | Some (norm, remaining, p) =>
      if negb (remaining =? 1) then None else
      if Zlength norm >? maxsv + 1 then None else
      let size := (p + 7) / 8 in
      if size >? n then None else
      Some (norm, log, size)
  end.

(* ---------- FSE_decompress_wksp (Huffman weights) and HUF_readStats as C computes them ---------- *)

(* FSE_DECOMPRESS_WKSP_SIZE(tableLog, maxSymbolValue) in bytes *)
Definition fse_dwksp (log msv: Z) : Z := 4 * ((2 ^ log + 1) + 1 + (2 * (msv + 1) + 2 ^ log + 8 + 3) / 4 + 129).

(* FSE_decompress_wksp_bmi2(huffWeight, 255, s, |s|, 6, workSpace, 4 nk, 0) after its FSE_readNCount_bmi2
   returned res *)
Definition weights_of (res: option (list Z * Z * Z)) (nk: Z) (s: list Z) : option (list Z) :=
  match res with
  | None => None
  | Some (norm, log, nsize) =>
      if log >? 6 then None else
      if fse_dwksp log (Zlength norm - 1) >? 4 * nk then None else
      fse_weights_dec (fse_build norm log) (skipn (Z.to_nat nsize) s)
  end.

(* Huffman.huf_desc_weights / huf_parse_desc with the FSE weights decoder fw as a parameter *)
Definition huf_desc_weights_w (fw: list Z -> option (list Z)) (b: list Z) : option (list Z * Z) :=
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
    match fw (slice b 1 iSize) with
    | Some ws => Some (ws, iSize + 1)
    | None => None
    end.

(* HUF_readStats_body's checks and the implied last weight, with the FSE weights decoder fw *)
Definition huf_parse_w (fw: list Z -> option (list Z)) (b: list Z) : option (huf_table * Z) :=
  match huf_desc_weights_w fw b with
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

(* HUF_readStats_body(huffWeight, 256, ..., s, |s|, workSpace, 4 nk, 0) when its FSE_decompress_wksp's
   readNCount returned res *)
Definition huf_parse_res (res: option (list Z * Z * Z)) (nk: Z) (b: list Z) : option (huf_table * Z) :=
  huf_parse_w (weights_of res nk) b.

(* the window HUF_readStats_body passes to FSE_decompress_wksp, when it calls it *)
Definition rs_window (b: list Z) : option (list Z) :=
  if andb (andb (1 <=? Zlength b) (byte_at b 0 <? 128)) (byte_at b 0 + 1 <=? Zlength b)
  then Some (slice b 1 (byte_at b 0)) else None.

