(* The format model: FSE table descriptions (RFC 8878, 4.1.1), as zstd reads them (FSE_readNCount,
   lib/common/entropy_common.c).  Plain Coq, no VST.

   The description is a FORWARD bitstream: bit k of the description is bit (k mod 8) of byte k / 8
   (least significant first); bits past the end read as 0.  `read_ncount b maxsv` returns
   (norm, log, size): the normalized counts of symbols 0 .. length norm - 1 (-1 = "less than 1"), the
   accuracy log, and the bytes the description takes (ceil (bits / 8) <= length b); None when zstd
   returns an error.  maxsv is the largest symbol allowed (zstd's *maxSVPtr on entry). *)
Require Import Zstd.proof.model.Bytes.
Local Open Scope bool_scope.

(* n <= 32 bits at bit position p of the forward bitstream b (zeros past the end): bits p .. p+n-1 of
   le_value b, read from a window of 5 bytes *)
Definition fbits (b: list Z) (p n: Z) : Z := (le_value (slice b (p / 8) 5) / 2 ^ (p mod 8)) mod 2 ^ n.

Definition FSE_MIN_TABLELOG : Z := 5.
Definition FSE_TABLELOG_ABSOLUTE_MAX : Z := 15.

(* the 2-bit repeat flags after a zero count: zeros added and the new bit position *)
Fixpoint ncount_zeros (fuel: nat) (b: list Z) (p: Z) : Z * Z :=
  match fuel with
  | O => (0, p)
  | S f =>
      let r := fbits b p 2 in
      if r =? 3 then let '(z, p') := ncount_zeros f b (p + 2) in (3 + z, p')
      else (r, p + 2)
  end.

(* The loop of FSE_readNCount: acc = the counts read so far (in order), charnum = length acc.
   Returns (acc, remaining, p) at the loop's exit. *)
Fixpoint ncount_loop (fuel: nat) (b: list Z) (maxsv1: Z) (p remaining threshold nbBits: Z)
    (prev0: bool) (acc: list Z) : option (list Z * Z * Z) :=
  match fuel with
  | O => None
  | S f =>
      (* zero repeats *)
      let '(acc, p, stop) :=
        if prev0 then
          let '(z, p') := ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p in
          let acc := acc ++ repeat 0 (Z.to_nat z) in
          (acc, p', Zlength acc >=? maxsv1)
        else (acc, p, false) in
      if stop then Some (acc, remaining, p) else
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
      if (remaining <? threshold) && (remaining <=? 1) then Some (acc, remaining, p) else
      let '(nbBits, threshold) :=
        if remaining <? threshold then
          (highbit remaining + 1, 2 ^ highbit remaining)
        else (nbBits, threshold) in
      if Zlength acc >=? maxsv1 then Some (acc, remaining, p) else
      ncount_loop f b maxsv1 p remaining threshold nbBits prev0 acc
  end.

Definition read_ncount (b: list Z) (maxsv: Z) : option (list Z * Z * Z) :=
  if Zlength b =? 0 then None else
  let log := fbits b 0 4 + FSE_MIN_TABLELOG in
  if log >? FSE_TABLELOG_ABSOLUTE_MAX then None else
  match ncount_loop (Z.to_nat (maxsv + 2)) b (maxsv + 1) 4 (2 ^ log + 1) (2 ^ log) (log + 1) false nil with
  | None => None
  | Some (norm, remaining, p) =>
      if negb (remaining =? 1) then None else
      if Zlength norm >? maxsv + 1 then None else
      let size := (p + 7) / 8 in
      if size >? Zlength b then None else
      Some (norm, log, size)
  end.

