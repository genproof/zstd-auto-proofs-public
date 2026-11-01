(* The sequence executors' stores as functions on the C arrays, store by store: the mirror, on lists of
   values (the output array and the arrays the literals are read from), of model/ExBlock.v's memory
   functions (xm_fwd, xm_move, xm_chunks16, xm_wild, xm_ov8, xm_safecopy, xm_sdbs, xm_match, x_exec,
   x_exec_split).  The specifications of SEQ's copies and executors (BlkSeqCOPY, BlkSeqEXEC) state their
   result exactly as these functions; BlkSeqXKit relates them to the model's functions on a region of
   cells (BlkIface.dst_rel), which the sequence loops use to state their outcome as ExBlock's x_seqs.

   Positions are offsets in the arrays (the model's are indices in its region, from its base rb).  A
   source is the output array itself (LW: a match, literals in dst) or a separate array (LS cs: the input
   array for literals read in place, litExtraBuffer).  Out-of-range reads and stores have no meaning here:
   the C's are in range (the safety proofs), and the bridge lemmas say so in their hypotheses. *)
Require Export Zstd.proof.dec.B.blk.BlkGroups.
Require Import Zstd.proof.model.ExBlock.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Inductive lsrc : Type := LW | LS (cs: list val).

Definition lrd (c: list val) (s: lsrc) (i: Z) : val :=
  match s with LW => Znth i c | LS cs => Znth i cs end.

(* k bytes forward, each read after the previous store (memcpy, ZSTD_copy4/8, one-byte memmove loops) *)
Fixpoint lfwd (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : list val :=
  match k with
  | O => c
  | S k' => lfwd k' (upd_Znth d c (lrd c s i)) (d + 1) s (i + 1)
  end.

Fixpoint lrdn (k: nat) (c: list val) (s: lsrc) (i: Z) : list val :=
  match k with
  | O => nil
  | S k' => lrd c s i :: lrdn k' c s (i + 1)
  end.

Fixpoint lwrn (vs: list val) (c: list val) (d: Z) : list val :=
  match vs with
  | nil => c
  | v :: vs' => lwrn vs' (upd_Znth d c v) (d + 1)
  end.

(* k bytes moved: all read, then all stored (memmove, ZSTD_copy16) *)
Definition lmove (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : list val := lwrn (lrdn k c s i) c d.

(* k ZSTD_copy16 at stride 16 *)
Fixpoint lchunks16 (k: nat) (c: list val) (d: Z) (s: lsrc) (i: Z) : list val :=
  match k with
  | O => c
  | S k' => lchunks16 k' (lmove 16 c d s i) (d + 16) s (i + 16)
  end.

(* ZSTD_wildcopy(d, i, len, srcb4 ? ZSTD_overlap_src_before_dst : ZSTD_no_overlap) (xm_wild) *)
Definition lwild (c: list val) (d: Z) (s: lsrc) (i len: Z) (srcb4: bool) : list val :=
  if srcb4 && (d - i <? 16) then lfwd (Z.to_nat (8 * Z.max 1 ((len + 7) / 8))) c d s i
  else
    let nch := if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32) in
    lchunks16 (Z.to_nat nch) c d s i.

(* ZSTD_overlapCopy8(&op, &ip, off), ip in the output array (xm_ov8): the array, the new op and ip *)
Definition lov8 (c: list val) (op ip off: Z) : list val * Z * Z :=
  if off <? 8 then
    let c1 := lfwd 4 c op LW ip in
    let ip1 := ip + xdec32 off in
    (lfwd 4 c1 (op + 4) LW ip1, op + 8, ip1 - xdec64 off + 8)
  else (lfwd 8 c op LW ip, op + 8, ip + 8).

(* ZSTD_safecopy(op, oend_w, ip, len, srcb4 ? ZSTD_overlap_src_before_dst : ZSTD_no_overlap) (xm_safecopy);
   srcb4 only with the source in the output array *)
Definition lsafecopy (c: list val) (op oend_w: Z) (s: lsrc) (ip len: Z) (srcb4: bool) : list val :=
  let oend := op + len in
  if len <? 8 then lfwd (Z.to_nat len) c op s ip else
  let '(c1, op1, ip1) := if srcb4 then lov8 c op ip (op - ip) else (c, op, ip) in
  let len1 := if srcb4 then len - 8 else len in
  if oend_w - oend >=? 0 then lwild c1 op1 s ip1 len1 srcb4 else
  let '(c2, op2, ip2) :=
    if oend_w - op1 >=? 0 then (lwild c1 op1 s ip1 (oend_w - op1) srcb4, oend_w, ip1 + (oend_w - op1))
    else (c1, op1, ip1) in
  lfwd (Z.to_nat (oend - op2)) c2 op2 s ip2.

(* ZSTD_safecopyDstBeforeSrc(op, ip, len), both in the output array (xm_sdbs) *)
Definition lsdbs (c: list val) (op ip len: Z) : list val :=
  let diff := op - ip in
  if (len <? 8) || (diff >? -8) then lfwd (Z.to_nat len) c op LW ip else
  let '(c1, op1, ip1) :=
    if (len >=? 32) && (diff <? -16) then (lwild c op LW ip (len - 32) false, op + len - 32, ip + len - 32)
    else (c, op, ip) in
  lfwd (Z.to_nat (op + len - op1)) c1 op1 LW ip1.

(* The match of a sequence at oLitEnd (xm_match), the history in the output array: prefixStart ps,
   virtualStart vs, dictEnd de (offsets in the output array).  An offset beyond oLitEnd - vs is an error
   (the C stops before any store); the function's value there is meaningless. *)
Definition lprefix (c: list val) (op mt ml off: Z) (wo: option Z) : list val :=
  match wo with
  | Some w => lsafecopy c op w LW mt ml true
  | None =>
      if off >=? 16 then lwild c op LW mt ml false else
      let '(c1, op1, mt1) := lov8 c op mt off in
      if ml >? 8 then lwild c1 op1 LW mt1 (ml - 8) true else c1
  end.

Definition lmatch (ps vs de: Z) (c: list val) (oLitEnd ml off: Z) (wo: option Z) : list val :=
  if off >? oLitEnd - ps then
    let mt := de + (oLitEnd - off - ps) in
    if de - mt >=? ml then lmove (Z.to_nat ml) c oLitEnd LW mt else
    let l1 := de - mt in
    lprefix (lmove (Z.to_nat l1) c oLitEnd LW mt) (oLitEnd + l1) ps (ml - l1) off wo
  else lprefix c oLitEnd (oLitEnd - off) ml off wo.

(* ZSTD_execSequence / ZSTD_execSequenceEnd (x_exec): the output array after a successful execution of the
   sequence (ll, ml, off) at op, literals at li of the source s, limit llim, output end oend *)
Definition lexec (ps vs de oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) : list val :=
  let oLitEnd := op + ll in
  let oend_w := oend - WILDCOPY_OVERLENGTH in
  if (llim - li <? ll) || (oend_w - op <? ll + ml) then
    lmatch ps vs de (lsafecopy c op oend_w s li ll false) oLitEnd ml off (Some oend_w)
  else
    let c1 := lmove 16 c op s li in
    let c2 := if ll >? 16 then lwild c1 (op + 16) s (li + 16) (ll - 16) false else c1 in
    lmatch ps vs de c2 oLitEnd ml off None.

(* ZSTD_execSequenceSplitLitBuffer / ZSTD_execSequenceEndSplitLitBuffer (x_exec_split): literals in the
   output array at li, oend_w = li + ll - 32 *)
Definition lexec_split (ps vs de oend: Z) (c: list val) (op li llim ll ml off: Z) : list val :=
  let oLitEnd := op + ll in
  let oend_w := li + ll - WILDCOPY_OVERLENGTH in
  if (llim - li <? ll) || (oend_w - op <? ll + ml) then
    lmatch ps vs de (lsdbs c op li ll) oLitEnd ml off (Some oend_w)
  else
    let c1 := lmove 16 c op LW li in
    let c2 := if ll >? 16 then lwild c1 (op + 16) LW (li + 16) (ll - 16) false else c1 in
    lmatch ps vs de c2 oLitEnd ml off None.

(* ---------- from the model's region to the arrays ----------
   The model's regions: R_dst = the output array from rb; R_src = the input array ci from bo (the block's
   body); R_lxb = litExtraBuffer's array cl from its start. *)
Definition reg_l (lr: xreg) (ci cl: list val) : lsrc :=
  match lr with R_dst => LW | R_src => LS ci | R_lxb => LS cl end.
Definition reg_o (lr: xreg) (rb bo: Z) : Z :=
  match lr with R_dst => rb | R_src => bo | R_lxb => 0 end.

(* the block's body at bo of the input array ci, litExtraBuffer's array cl holding lxb *)
Definition src_rel (body lxb: list Z) (ci: list val) (bo: Z) (cl: list val) : Prop :=
  0 <= bo /\ bo + Zlength body <= Zlength ci /\ sublist bo (bo + Zlength body) ci = zbytes body /\
  cl = zbytes lxb.

(* a written cell of the model's region *)
Definition xwr (m: xmem) (j: Z) : Prop := 0 <= j /\ nth (Z.to_nat j) (xm_dst m) None <> None.
Definition xwr_rng (m: xmem) (a b: Z) : Prop := forall j, a <= j < b -> xwr m j.
(* m' extends m: written cells stay written (their values may change), litExtraBuffer unchanged *)
Definition xm_le (m m': xmem) : Prop := (forall j, xwr m j -> xwr m' j) /\ xm_lxb m' = xm_lxb m.
