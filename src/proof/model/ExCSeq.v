(* The C-exact steps of ZSTD_decodeSequence (lib/decompress/zstd_decompress_block.c) that the exact block model
   (ExBlock.v) is instantiated with: one sequence decoded from the FSE states and the bit stream, and the C's
   resolution of the offset (repeat offsets as size_t values).  The decoder's proofs (dec/B/blk/BlkSeqDecModel.v,
   which exports this file) use the same functions.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Fse Zstd.proof.model.Block.
Local Open Scope Z_scope.

(* one step of Block.decode_seqs: the sequence, the next states (sLL, sOF, sML), the position; `last` = no
   state update (C: isLastSeq) *)
Definition dseq_one (tLL tOF tML: fse_table) (V: list Z) (last: bool) (sLL sOF sML pos: Z)
    : option (sequence * (Z * Z * Z) * Z) :=
  let cLL := fe_sym (fse_cell tLL sLL) in
  let cOF := fe_sym (fse_cell tOF sOF) in
  let cML := fe_sym (fse_cell tML sML) in
  match rd V pos cOF with None => None | Some (eOF, pos) =>
  match rd V pos (nth (Z.to_nat cML) ML_bits_tab 0) with None => None | Some (eML, pos) =>
  match rd V pos (nth (Z.to_nat cLL) LL_bits_tab 0) with None => None | Some (eLL, pos) =>
  let sq := {| sq_ll := nth (Z.to_nat cLL) LL_base_tab 0 + eLL;
               sq_ml := nth (Z.to_nat cML) ML_base_tab 0 + eML;
               sq_ov := 2 ^ cOF + eOF |} in
  if last then Some (sq, (sLL, sOF, sML), pos) else
  let eLL := fse_cell tLL sLL in
  match rd V pos (fe_nb eLL) with None => None | Some (uLL, pos) =>
  let eML := fse_cell tML sML in
  match rd V pos (fe_nb eML) with None => None | Some (uML, pos) =>
  let eOF := fse_cell tOF sOF in
  match rd V pos (fe_nb eOF) with None => None | Some (uOF, pos) =>
  Some (sq, (fe_base eLL + uLL, fe_base eOF + uOF, fe_base eML + uML), pos)
  end end end
  end end end.

(* SIZE_MAX on the 64-bit target *)
Definition SIZE_MAX : Z := 2 ^ 64 - 1.

(* the C offset resolution (non-aarch64), total (an invalid repeat gives (size_t)-1): ofBits > 1: offset =
   OF_base + bits = ov - 3, shift; ofBits = 0 (ov = 1): offset = prevOffset[ll0]; ofBits = 1 (ov = 2 + bit):
   index ov + ll0 - 1 into {r2, r3, r1 - 1}, with `temp -= !temp` (0 -> (size_t)-1).  ll0 = (LL baseValue == 0)
   iff ll = 0. *)

Definition c_offset (rep: Z * Z * Z) (ll ov: Z) : Z * (Z * Z * Z) :=
  let '(r1, r2, r3) := rep in
  if ov >? 3 then (ov - 3, (ov - 3, r1, r2)) else
  let idx := if ll =? 0 then ov + 1 else ov in
  if idx =? 1 then (r1, rep)
  else if idx =? 2 then (r2, (r2, r1, r3))
  else if idx =? 3 then (r3, (r3, r1, r2))
  else let t := (r1 - 1) mod 2 ^ 64 in
       let t := if t =? 0 then SIZE_MAX else t in (t, (t, r1, r2)).
