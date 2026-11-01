(* w_compressed_block (harness/writer.h) in plain Coq: the objects its proof talks about.  Definitions only; the lemmas
   are in
   WM_BlkGen.v (drawing the sequences: repeat offsets, matches, exec_seqs), WM_BlkCodes.v (codes and
   extra bits), WM_BlkHdr.v (the sequences section header), WM_BlkStream.v (the sequences bitstream),
   WM_BlkAsm.v (decode_block of the whole body). *)
Require Export Zstd.proof.harness.writer.model.WModel.
Local Open Scope bool_scope.

(* ---------- sequences ---------- *)

(* the repeat offsets of a wst (wt_ok's first part) *)
Definition rep_ok (rep: Z * Z * Z) : Prop :=
  let '(r1, r2, r3) := rep in 1 <= r1 < 2 ^ 32 /\ 1 <= r2 < 2 ^ 32 /\ 1 <= r3 < 2 ^ 32.

Definition set_rep (S: wst) (rep: Z * Z * Z) : wst :=
  {| wt_rep := rep; wt_huf := wt_huf S; wt_tabs := wt_tabs S |}.
Definition set_huf (S: wst) (H: whuf) : wst :=
  {| wt_rep := wt_rep S; wt_huf := Some H; wt_tabs := wt_tabs S |}.
Definition set_tabs (S: wst) (T: wfse * wfse * wfse) : wst :=
  {| wt_rep := wt_rep S; wt_huf := wt_huf S; wt_tabs := Some T |}.

(* a sequence as the writer draws it: ll in 0..rem-3, ml in 3..rem-ll (rem <= 2^17), Offset_Value below
   2^32 (gp_assume(ov < 2ULL << OF_CODE_MAX), OF_CODE_MAX = 31) *)
Definition seq_ok (sq: sequence) : Prop :=
  0 <= sq_ll sq /\ 3 <= sq_ml sq /\ sq_ll sq + sq_ml sq <= 2 ^ 17 /\ 1 <= sq_ov sq < 2 ^ 32.

Definition seq0 : sequence := {| sq_ll := 0; sq_ml := 0; sq_ov := 0 |}.
Definition sqn (seqs: list sequence) (i: Z) : sequence := nth (Z.to_nat i) seqs seq0.

(* the code tables: 0 literals lengths, 1 offsets, 2 match lengths (w_code[ty], w_extra[ty]) *)
Definition sq_code (ty: Z) (sq: sequence) : Z :=
  if ty =? 0 then ll_code_of (sq_ll sq) else if ty =? 1 then Z.log2 (sq_ov sq) else ml_code_of (sq_ml sq).

(* the number of extra bits of the code (W_LL_bits / the offset code / W_ML_bits) *)
Definition sq_nbits (ty: Z) (sq: sequence) : Z :=
  if ty =? 0 then zn LL_bits_tab (sq_code 0 sq) else if ty =? 1 then sq_code 1 sq
  else zn ML_bits_tab (sq_code 2 sq).

(* the extra bits: ll - W_LL_base[code], ov - 2^code, ml - W_ML_base[code] *)
Definition sq_extra (ty: Z) (sq: sequence) : Z :=
  if ty =? 0 then sq_ll sq - zn LL_base_tab (sq_code 0 sq)
  else if ty =? 1 then sq_ov sq - 2 ^ sq_code 1 sq
  else sq_ml sq - zn ML_base_tab (sq_code 2 sq).

(* maxsym[ty] (= MaxLL, MaxOff, MaxML) and maxlog[ty] (= LLFSELog, OffFSELog, MLFSELog) *)
Definition ty_max (ty: Z) : Z := if ty =? 0 then 35 else if ty =? 1 then 31 else 52.
Definition ty_maxlog (ty: Z) : Z := if ty =? 0 then 9 else if ty =? 1 then 8 else 9.

(* the Offset_Value ov the writer may choose for the offset off after ll literals, with the repeat
   offsets rep: a new offset (off + 3), or a repeat code that gives off *)
Definition ov_valid (rep: Z * Z * Z) (ll off ov: Z) : Prop :=
  let '(r1, r2, r3) := rep in
  ov = off + 3 \/
  (0 < ll /\ ((ov = 1 /\ r1 = off) \/ (ov = 2 /\ r2 = off) \/ (ov = 3 /\ r3 = off))) \/
  (ll = 0 /\ ((ov = 1 /\ r2 = off) \/ (ov = 2 /\ r3 = off) \/ (ov = 3 /\ 1 < r1 /\ r1 - 1 = off))).

(* the C's update of the repeat offsets (st->rep[]) *)
Definition c_rep_upd (rep: Z * Z * Z) (ll ov off: Z) : Z * Z * Z :=
  let '(r1, r2, r3) := rep in
  if (ov >? 3) || ((ov =? 3) && (ll =? 0)) then (off, r1, r2)
  else
    let idx := ov - 1 + (if ll =? 0 then 1 else 0) in
    if idx =? 0 then (r1, r2, r3) else if idx =? 1 then (r2, r1, r3) else (r3, r1, r2).

(* the bytes lz_copy appends *)
Definition lz_tail (hist cur: list Z) (off: Z) (ml: nat) : list Z :=
  skipn (length cur) (lz_copy hist cur off ml).

(* the sequences drawn so far: with any literals Y after their literals lits, they execute
   (behind the dictionary content hist, after the frame's output out, from the repeat offsets
   rep0) to out ++ cont, leaving Y, with the repeat offsets rep *)
Definition gen_ok (wsize: Z) (rep0: Z * Z * Z) (hist out lits: list Z) (seqs: list sequence) (cont: list Z)
    (rep: Z * Z * Z) : Prop :=
  forall Y, exec_seqs wsize rep0 hist (lits ++ Y) out seqs = Some (out ++ cont, Y, rep).

(* the literal bytes of the literals mode lm (0 raw: any byte, 1 RLE: rleb, 2/3 Huffman: a symbol of
   the code Hl) *)
Definition lit_in (lm rleb: Z) (Hl: whuf) (c: Z) : Prop :=
  if lm =? 0 then 0 <= c < 256 else if lm =? 1 then c = rleb else huf_present Hl c.

(* the literals mode drawn for the state S (Hl: the Huffman code of modes 2 (new) and 3 (S's)) *)
Definition lm_ok (S: wst) (lm rleb: Z) (Hl: whuf) : Prop :=
  0 <= lm <= 3 /\ 0 <= rleb < 256 /\ (2 <= lm -> huf_ok Hl) /\ (lm = 3 -> wt_huf S = Some Hl).

(* the state after the literals section *)
Definition lm_state (S: wst) (lm: Z) (Hl: whuf) : wst := if lm =? 2 then set_huf S Hl else S.

(* ---------- the sequences section header ---------- *)

(* Number_of_Sequences in the form f (0: 1 byte, 1: 2 bytes, 2: 3 bytes) *)
Definition nseq_bytes (f n: Z) : list Z :=
  if f =? 0 then [n] else if f =? 1 then [128 + n / 256; n mod 256] else 255 :: le_bytes 2 (n - 32512).

Definition nseq_form_ok (f n: Z) : Prop :=
  (f = 0 /\ 0 <= n < 128) \/ (f = 1 /\ 0 <= n < 32512) \/ (f = 2 /\ 32512 <= n < 65536 + 32512).

(* the table of type ty in mode m (0 predefined, 1 RLE, 2 FSE-compressed, 3 repeat), prev: the
   table of the previous block *)
Definition mode_ok (ty m: Z) (prev: option wfse) (F: wfse) : Prop :=
  (m = 0 /\ F = pre_wfse ty) \/
  (m = 1 /\ exists c, 0 <= c <= ty_max ty /\ F = rle_wfse c) \/
  (m = 2 /\ ndist_ok (wf_log F) (wf_norm F) /\ wf_nsym F = Zlength (wf_norm F) /\
     wf_log F <= ty_maxlog ty /\ Zlength (wf_norm F) <= ty_max ty + 1) \/
  (m = 3 /\ prev = Some F).

(* the description that follows the modes byte *)
Definition wtab_desc (m: Z) (F: wfse) : list Z :=
  if m =? 1 then [wf_nsym F - 1] else if m =? 2 then fse_desc_bytes (wf_norm F) (wf_log F) else [].

Definition seq_hdr_bytes (f n m0 m1 m2: Z) (F0 F1 F2: wfse) : list Z :=
  nseq_bytes f n ++ [m0 * 64 + m1 * 16 + m2 * 4] ++ wtab_desc m0 F0 ++ wtab_desc m1 F1 ++ wtab_desc m2 F2.

Definition wtabs_ll (T: wfse * wfse * wfse) : wfse := let '(a, _, _) := T in a.
Definition wtabs_of (T: wfse * wfse * wfse) : wfse := let '(_, b, _) := T in b.
Definition wtabs_ml (T: wfse * wfse * wfse) : wfse := let '(_, _, c) := T in c.

(* ---------- the sequences bitstream ---------- *)

(* the update from state sts[q] to sts[q+1] in the table T *)
Definition fse_upd_field (T: fse_table) (sts: list Z) (q: Z) : Z * Z :=
  (zn sts (q + 1) - fe_base (fse_cell T (zn sts q)), fe_nb (fse_cell T (zn sts q))).

(* the extra bits of a sequence, in writing order LL, ML, OF *)
Definition seq_ex_fields (sq: sequence) : list (Z * Z) :=
  [(sq_extra 0 sq, sq_nbits 0 sq); (sq_extra 2 sq, sq_nbits 2 sq); (sq_extra 1 sq, sq_nbits 1 sq)].

(* what the C writes for sequence q: (not after the last) the state updates OF, ML, LL, then the extra
   bits *)
Definition seq_fields_at (T0 T1 T2: fse_table) (s0 s1 s2: list Z) (seqs: list sequence) (q: Z)
    : list (Z * Z) :=
  (if q + 1 <? Zlength seqs then [fse_upd_field T1 s1 q; fse_upd_field T2 s2 q; fse_upd_field T0 s0 q]
   else []) ++ seq_ex_fields (sqn seqs q).

(* the whole bitstream's fields (before the end mark): sequences n-1 down to 0, then the initial
   states ML, OF, LL *)
Definition seq_fields (T0 T1 T2: fse_table) (s0 s1 s2: list Z) (seqs: list sequence) : list (Z * Z) :=
  flat_map (fun j => seq_fields_at T0 T1 T2 s0 s1 s2 seqs (Zlength seqs - 1 - Z.of_nat j))
    (seq 0 (length seqs)) ++
  [(zn s2 0, ft_log T2); (zn s1 0, ft_log T1); (zn s0 0, ft_log T0)].

(* ---------- the sequences section ---------- *)

(* sb is a sequences section (the end of the block body) that, after the tables prev, decodes to
   seqs and leaves the tables tabs *)
Definition seqsec_ok (prev: option (fse_table * fse_table * fse_table)) (seqs: list sequence)
    (tabs: option (fse_table * fse_table * fse_table)) (sb: list Z) : Prop :=
  bytes_ok sb /\ 1 <= Zlength sb /\
  exists hused, decode_seq_header prev sb = Some (Zlength seqs, tabs, hused) /\
    (seqs = [] \/
     exists tLL tOF tML, tabs = Some (tLL, tOF, tML) /\
       decode_seq_stream tLL tOF tML (skipn (Z.to_nat hused) sb) (Zlength seqs) = Some seqs).
