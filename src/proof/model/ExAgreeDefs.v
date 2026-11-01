(* The layers of the agreement between the exact one-shot model (Exact.os_res) and the format model
   (Series.decode_series, Block.decode_block, Huffman.v, NCount.v), as statements.  Plain Coq.

   ExAgree.os_res_agrees is assembled from four facts, each proved in its own file from the ones below it:
   - ncount_agree (ExAgreeNCount.v): zstd's FSE_readNCount (ExHuf.x_ncount, on a window of any length)
     returns the format model's result wherever the model reads the description;
   - huf_agree (ExAgreeHuf.v): the Huffman literals as zstd decodes them (ExHuf.x_lits_huf: X1 / X2 tables,
     one or four streams) are the format model's wherever the model decodes them;
   - block_agree (ExAgreeBlock.v): ZSTD_decompressBlock_internal on the one-shot destination
     (Exact.xblock: mem = the frame's output so far, prefix from 0, no extDict, not streaming) gives the
     content of Block.decode_block when that content fits the capacity, and an error otherwise;
   - the frame and series layer (ExAgreeFrame.v): Exact.os_res against Series.decode_series.
   The relation between the two models' entropy states (xst_rel) is the invariant the frame layer carries
   from block to block. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Fse Zstd.proof.model.NCount.
Require Import Zstd.proof.model.Huffman Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock Zstd.proof.model.ExFrame.
Require Import Zstd.proof.model.Exact.
Local Open Scope Z_scope.

(* ---------- FSE table descriptions ---------- *)

(* every symbol bound the decoder uses (MaxLL, MaxOff, MaxML, 255 for the Huffman weights) is at most 255 *)
Definition ncount_agree : Prop :=
  forall (s: list Z) (maxsv: Z) x, 0 <= maxsv <= 255 ->
  read_ncount s maxsv = Some x -> ExHuf.x_ncount s maxsv = Some x.

(* ---------- Huffman literals ---------- *)

(* a Huffman table of the format model that a tree description (of bytes: so its symbols are bytes) parses to *)
Definition huf_ok (t: huf_table) : Prop :=
  exists (b: list Z) (h: Z), bytes_ok b /\ huf_parse_desc b = Some (t, h).

(* zstd's decoding table (of either type, X1 or X2) built from the parsed table t *)
Definition xhuf_rel (xt: xhuf) (t: huf_table) : Prop := huf_ok t /\ exists x2, xt = xhuf_of x2 t.

Definition opt_rel {A B: Type} (R: A -> B -> Prop) (a: option A) (b: option B) : Prop :=
  match a, b with
  | None, None => True
  | Some x, Some y => R x y
  | _, _ => False
  end.

(* The Huffman part of Block.decode_literals (literals block type ty = 2 compressed, 3 treeless) on the
   compressed bytes cb of litSize literals: the literals and the table kept. *)
Definition huf_lits_model (hprev: option huf_table) (ty: Z) (single: bool) (cb: list Z) (litSize: Z)
    : option (list Z * huf_table) :=
  let tbl :=
    if ty =? 2 then
      match huf_parse_desc cb with
      | Some (t, hsize) => if hsize >=? Zlength cb then None else Some (t, hsize)
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
      | Some l => Some (l, t)
      | None => None
      end
  end.

Definition huf_agree : Prop :=
  forall (xprev: option xhuf) (hprev: option huf_table) (ty: Z) (single: bool) (cb: list Z) (litSize: Z)
         (l: list Z) (t: huf_table),
  opt_rel xhuf_rel xprev hprev -> (ty = 2 \/ ty = 3) -> 0 <= litSize ->
  (single = false -> MIN_LITERALS_FOR_4_STREAMS <= litSize) -> bytes_ok cb ->
  huf_lits_model hprev ty single cb litSize = Some (l, t) ->
  exists xt, x_lits_huf xprev ty single cb litSize = Some (l, xt) /\ xhuf_rel xt t.

(* ---------- compressed blocks ---------- *)

(* the repeat offsets are positive (as every offset the format model makes is; at 0 the two models differ:
   the format model reads past its output, zstd the cells after op) and fit zstd's U32 storage between blocks *)
Definition reps_ok (r: Z * Z * Z) : Prop :=
  let '(r1, r2, r3) := r in 1 <= r1 < 2 ^ 32 /\ 1 <= r2 < 2 ^ 32 /\ 1 <= r3 < 2 ^ 32.

(* the codes of the current sequence tables are those of the format (at most MaxLL, MaxOff, MaxML): every new
   offset fits 32 bits, and every match length is at least 3 (an ML code beyond MaxML would give length 0, and a
   block of sequences with no content, which zstd refuses on a capacity of 0) *)
Definition of_ok (sq: option (fse_table * fse_table * fse_table)) : Prop :=
  match sq with
  | Some (tLL, tOF, tML) =>
      Forall (fun e => 0 <= fe_sym e <= MaxLL) (ft_cells tLL) /\
      Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells tOF) /\
      Forall (fun e => 0 <= fe_sym e <= MaxML) (ft_cells tML)
  | None => True
  end.

(* The exact model's decoding state xs is the format model's ds: the same Huffman table (zstd's of either
   type), the same sequence tables and repeat offsets, and a litExtraBuffer of its full size. *)
Definition xst_rel (xs: xstate) (ds: dstate) : Prop :=
  opt_rel xhuf_rel (x_huf xhuf xs) (st_huf ds) /\ x_seq xhuf xs = st_seq ds /\ x_rep xhuf xs = st_rep ds /\
  Zlength (x_lxb xhuf xs) = XLITEXTRA + XWILDCOPY /\ reps_ok (st_rep ds) /\ of_ok (st_seq ds).

(* One compressed block of a frame decoded one-shot without a dictionary: the destination is the frame's
   output so far (all of it prefix), the block starts at its end, room bytes of capacity are left.  Where
   the format model decodes the block to c: zstd decodes it to c when c fits (the cells from |out| on are c,
   the size returned is |c|, the new states are related) and fails otherwise. *)
Definition block_agree : Prop :=
  forall (xs: xstate) (ds: dstate) (out body: list Z) (bsm wsize: Z) (ds': dstate) (c: list Z) (room: Z),
  xst_rel xs ds -> bytes_ok body -> 0 <= bsm <= ZSTD_BLOCKSIZE_MAX -> 0 <= room ->
  decode_block ds nil out body bsm wsize = Some (ds', c) ->
  match xblock xs out 0 (Zlength out) 0 0 body bsm room false with
  | Some (xs', mem, d) => d = Zlength c /\ Zlength c <= room /\ slice mem (Zlength out) d = c /\ xst_rel xs' ds'
  | None => room < Zlength c
  end.

(* ---------- frames and series ---------- *)

Definition series_agree : Prop :=
  forall (s: list Z) (cap: Z), bytes_ok s -> 0 <= cap ->
  match decode_series no_dict no_wlim s with
  | SOk c => os_res s cap = (if Zlength c <=? cap then Some c else None)
  | SDet => os_res s cap = None
  | SUnk => True
  end.
