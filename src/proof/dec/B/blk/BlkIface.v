(* Group BLK of subtree B: the interfaces between its four sub-groups.  Fixed: each sub-group is proved
   against these interfaces.

   Sub-groups (BlkGroups.v):
   - LIT  ZSTD_blockSizeMax, ZSTD_allocateLiteralsBuffer, ZSTD_decodeLiteralsBlock
          exports blockSizeMax_spec, decodeLiteralsBlock_spec (the literals view below);
   - HDR  ZSTD_buildSeqTable_rle, ZSTD_buildSeqTable, ZSTD_decodeSeqHeaders
          exports decodeSeqHeaders_spec (exactly the model's decode_seq_header);
   - SEQ  the 22 functions of the sequence decoders (copies, execSequence*, decodeSequence, the three loops,
          their dispatchers); exports the three dispatchers' specs (seqs_spec);
   - TOP  ZSTD_totalHistorySize, ZSTD_getOffsetInfo, ZSTD_maxShortOffset, ZSTD_decompressBlock_internal
          exports DecIface's block spec (BLK_exports).

   The literals after ZSTD_decodeLiteralsBlock (C: ZSTD_allocateLiteralsBuffer and set_basic's direct
   reference) are at one of four places (litloc); `litfields` owns the six literal fields of the context
   (litPtr, litSize, litBuffer, litBufferEnd, litBufferLocation, litExtraBuffer) and says where they point;
   `lits_at` says where the literal bytes are in the input / output arrays (pure). *)
Require Export Zstd.proof.dec.B.BGroups.
Require Export Zstd.proof.dec.B.blk.BlkModel Zstd.proof.dec.B.blk.BlkSeqModel.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Local Open Scope logic.

(* ZSTD_litLocation_e *)
Definition LOC_NOT_IN_DST : Z := 0.
Definition LOC_IN_DST : Z := 1.
Definition LOC_SPLIT : Z := 2.

(* the cells of litExtraBuffer: DecRep.LITEXTRA_N = ZSTD_LITBUFFEREXTRASIZE + WILDCOPY_OVERLENGTH *)

Definition lit_extra (p: val) : val := field_address t_dctx (DOT _litExtraBuffer) p.

(* where the literals are:
   - LIn off:    in the input array, at offset off (set_basic, referenced in place); not_in_dst;
   - LExtra:     in litExtraBuffer, from its start (litSize <= 65536); not_in_dst;
   - LDst lb:    in the output array at offset lb (not streaming, large capacity; lb = d + bsm + 32); in_dst;
   - LSplit lb:  the first litSize - 65536 bytes in the output array at offset lb (ending 32 bytes before
                 d + min(bsm, cap)), the last 65536 in litExtraBuffer; split. *)
Inductive litloc := LIn (off: Z) | LExtra | LDst (lb: Z) | LSplit (lb: Z).

Definition loc_code (l: litloc) : Z :=
  match l with LIn _ | LExtra => LOC_NOT_IN_DST | LDst _ => LOC_IN_DST | LSplit _ => LOC_SPLIT end.

(* litExtraBuffer holding the bytes lxb: DecRep.lit_extra_at *)

(* The literal fields of the context for the literals lits at l (ob: the output array's base, ib: the input
   array's base), litExtraBuffer holding lxb (exactly: its first n bytes are the literals for LExtra, its first
   65536 bytes their last 65536 for LSplit; its other cells are what earlier blocks left).  litBuffer is only
   meaningful in dst. *)
Definition litfields (p ob ib: val) (l: litloc) (lits lxb: list Z) : mpred :=
  let n := Zlength lits in
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr n)) p *
  field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (loc_code l))) p *
  lit_extra_at p lxb *
  match l with
  | LIn off =>
      field_at Ews t_dctx (DOT _litPtr) (offset_val off ib) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (off + n) ib) p *
      field_at_ Ews t_dctx (DOT _litBuffer) p
  | LExtra =>
      !! (sublist 0 n lxb = lits) &&
      (field_at Ews t_dctx (DOT _litPtr) (lit_extra p) p *
       field_at Ews t_dctx (DOT _litBufferEnd) (offset_val n (lit_extra p)) p *
       field_at Ews t_dctx (DOT _litBuffer) (lit_extra p) p)
  | LDst lb =>
      field_at Ews t_dctx (DOT _litPtr) (offset_val lb ob) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + n) ob) p *
      field_at Ews t_dctx (DOT _litBuffer) (offset_val lb ob) p
  | LSplit lb =>
      !! (sublist 0 LITBUFFEREXTRASIZE lxb = sublist (n - LITBUFFEREXTRASIZE) n lits) &&
      (field_at Ews t_dctx (DOT _litPtr) (offset_val lb ob) p *
       field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + (n - LITBUFFEREXTRASIZE)) ob) p *
       field_at Ews t_dctx (DOT _litBuffer) (offset_val lb ob) p)
  end.

(* the literal fields with any contents, litExtraBuffer holding bytes (B's scratch, as in tabs_scratch;
   bytes in, bytes out: DecRep.lit_extra_bytes) *)
Definition lit_scratch (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_bytes p.

(* the same with litExtraBuffer holding exactly lxb *)
Definition lit_scratch_x (p: val) (lxb: list Z) : mpred :=
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_at p lxb.

(* Where the literal bytes are, for a block written at d with capacity cap into the output array oc, read
   from the input window i (pure).  The 32 bytes after the literals are readable (zstd's wildcopy). *)
Definition lits_at (l: litloc) (oc: list val) (d cap: Z) (i: inwin) (lits: list Z) : Prop :=
  let n := Zlength lits in
  bytes_ok lits /\ 0 <= n <= ZSTD_BLOCKSIZE_MAX /\
  match l with
  | LIn off =>   (* in the input array (the windows of LIT and SEQ differ, the array is the same); the 32 cells
                    after them are defined bytes (the copies over-read them; the C reads in place only when they are
                    still inside the block) *)
      0 <= off /\ off + n + WILDCOPY_OVERLENGTH <= iw_N i /\ sublist off (off + n) (iw_c i) = zbytes lits /\
      Forall is_byte_val (sublist (off + n) (off + n + WILDCOPY_OVERLENGTH) (iw_c i))
  | LExtra => n <= LITBUFFEREXTRASIZE
  | LDst lb =>
      d <= lb /\ lb + n + WILDCOPY_OVERLENGTH <= d + cap /\ sublist lb (lb + n) oc = zbytes lits
  | LSplit lb =>
      LITBUFFEREXTRASIZE < n /\ d <= lb /\ lb + (n - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH <= d + cap /\
      sublist lb (lb + (n - LITBUFFEREXTRASIZE)) oc = zbytes (sublist 0 (n - LITBUFFEREXTRASIZE) lits)
  end.

(* where ZSTD_allocateLiteralsBuffer puts literals in dst (n = their number): LDst at
   dst + blockSizeMax + WILDCOPY_OVERLENGTH; LSplit's head at dst + expectedWriteSize - n + LITBUFFEREXTRASIZE -
   WILDCOPY_OVERLENGTH with expectedWriteSize = min(blockSizeMax, dstCapacity).  The sequence loops rely on it: the
   output never catches up with unread literals when the content fits (k + 32 <= litPtr). *)
Definition lit_pos (l: litloc) (d cap bsm n: Z) : Prop :=
  match l with
  | LDst lb => lb = d + bsm + WILDCOPY_OVERLENGTH
  | LSplit lb => lb = d + Z.min bsm cap - n + LITBUFFEREXTRASIZE - WILDCOPY_OVERLENGTH
  | _ => True
  end.

(* the Huffman part after an error: HUFptr, litEntropy, the context's table are anything *)
Definition huf_junk (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _HUFptr) p *
  field_at_ Ews t_dctx (DOT _litEntropy) p *
  memory_block Ews (4 + HUF_CELLBYTES) (ctx_huf p).

(* the sequence part after an error: the pointers, fseEntropy, the context's tables are anything *)
Definition seq_junk (p: val) : mpred :=
  field_at_ Ews t_dctx (DOT _fseEntropy) p *
  field_at_ Ews t_dctx (DOT _LLTptr) p * field_at_ Ews t_dctx (DOT _OFTptr) p *
  field_at_ Ews t_dctx (DOT _MLTptr) p *
  seqspace_at Ews KLL None (ctx_seq KLL p) * seqspace_at Ews KOF None (ctx_seq KOF p) *
  seqspace_at Ews KML None (ctx_seq KML p).

(* is_byte_val, hist_def (the history zstd may read is defined bytes), ext_clean (an extDict in the output
   array lies outside what the block may write), dictend_ok, hist_ptrs_ok: DecIface.v *)

(* ===================== exactness: the model of model/ExBlock.v =====================

   Each specification below ends with a clause stating its outcome EXACTLY as the plain-Coq model
   model/ExBlock.v computes it, on every input (an error iff the model returns None), instantiated with the
   C-exact pieces as model/Exact.v does.  The model addresses the destination as a region of cells (Some byte:
   written, None: never written) from its base, which is at offset rb of the output array. *)

(* the instances of ExBlock's parameters (model/Exact.v's xblock) *)
Definition xb_lits := x_lits xhuf x_lits_huf.
Definition xb_seq_header := x_seq_header ncount_c.
Definition xb_seqs := x_seqs dseq_one c_offset.

(* every written cell of the model's region m is the output array's byte at rb + its index *)
Definition dst_rel (oc: list val) (rb: Z) (m: list (option Z)) : Prop :=
  forall j z, 0 <= j -> nth (Z.to_nat j) m None = Some z -> Znth (rb + j) oc = Vint (Int.repr z).

(* the C's literal place l (litfields) for n literals, and the model's literal pointer: region lr, index li,
   limit lim (litBufferEnd), split flag sp; rb: the region's base in the output array, bo: the block body's
   offset in the input array (literals read in place are body bytes) *)
Definition litloc_rel (l: litloc) (rb bo n: Z) (lr: xreg) (li lim: Z) (sp: bool) : Prop :=
  match l with
  | LIn off => lr = R_src /\ off = bo + li /\ lim = li + n /\ sp = false
  | LExtra => lr = R_lxb /\ li = 0 /\ lim = n /\ sp = false
  | LDst lb => lr = R_dst /\ lb = rb + li /\ lim = li + n /\ sp = false
  | LSplit lb => lr = R_dst /\ lb = rb + li /\ lim = li + (n - LITBUFFEREXTRASIZE) /\ sp = true
  end.

(* ZSTD_decodeLiteralsBlock exactly: ExBlock.x_lits (the section) and x_lits_store (its stores, in the C's order).
   hx: the Huffman table zstd holds (None while litEntropy = 0), lxb: litExtraBuffer's bytes.  For any region
   mem at offset rb (the cells [rb, rb + |mem|) of the output array hold mem; the block is written at
   op = d - rb): an error iff the model fails, else the bytes taken, the literals, the table kept (hx'),
   litExtraBuffer's new bytes, the written cells and the literals' place. *)
Definition lits_exact (hx: option xhuf) (lxb: list Z) (o: outarr) (i: inwin) (bsm streaming: Z)
    (r: Z) (oc': list val) (l: litloc) (lits: list Z) (hx': option xhuf) (lxb': list Z) : Prop :=
  forall rb mem,
    0 <= rb <= oa_d o -> rb + Zlength mem <= oa_N o -> sublist rb (rb + Zlength mem) (oa_c o) = zbytes mem ->
    let b := iw_s i in
    let ews := Z.min bsm (oa_cap o) in
    match xb_lits hx b bsm ews (streaming =? 1) with
    | None => is_error_code r = true
    | Some (lits0, lused, hx0) =>
        match x_lits_store b lits0 lused {| xm_dst := map Some mem; xm_lxb := lxb |} (oa_d o - rb) ews bsm
                (oa_cap o) (streaming =? 1) with
        | None => is_error_code r = true
        | Some (m, lr, li, lim, sp) =>
            is_error_code r = false /\ r = lused /\ lits = lits0 /\ hx' = hx0 /\ lxb' = xm_lxb m /\
            dst_rel oc' rb (xm_dst m) /\ litloc_rel l rb (iw_off i) (Zlength lits0) lr li lim sp
        end
    end.

(* the sequences section as ZSTD_decompressBlock_internal's callee runs it (ExBlock.x_block): without
   sequences only the last literals (no bitstream), else ExBlock.x_seqs; the memory, the final op, the
   repeat offsets *)
Definition x_seq_section (e: xenv) (tabs: option seq_tabs) (rep: Z * Z * Z) (bits: list Z) (nbSeq: Z) (s0: xex)
    : option (xmem * Z * (Z * Z * Z)) :=
  if nbSeq =? 0 then match x_last e s0 with Some (m, op') => Some (m, op', rep) | None => None end
  else match tabs with Some t => xb_seqs e t rep bits nbSeq s0 | None => None end.

(* the history of h in region coordinates: DecIface.hc_region *)

(* the sequences' output end (oend) in region coordinates: litBuffer for literals in dst after the block's room,
   else dst + dstCapacity *)
Definition seq_oend (l: litloc) (rb: Z) (o: outarr) : Z :=
  match l with LDst lb => lb - rb | _ => oa_d o + oa_cap o - rb end.

(* ZSTD_decompressSequences* exactly: x_seq_section from the state after the literals section.  For any region m
   at offset rb whose written cells are the output array's (dst_rel), in which the history the matches read
   ([prefixStart, op) and the extDict) and the literals in dst with the 32 cells after them are written, and
   for the block body at offset bo of the input array (the literals read in place, with 32 bytes after them,
   are inside it): an error iff the model fails, else the size, the written cells, the repeat offsets. *)
Definition seqs_exact (os: option seq_tabs) (rep: Z * Z * Z) (l: litloc) (lits lxb: list Z) (nbSeq: Z)
    (o: outarr) (i: inwin) (h: hctx) (r: Z) (oc': list val) (rep': Z * Z * Z) : Prop :=
  forall rb (m: list (option Z)) (body: list Z) bo lr li lim sp ps ds de,
    hc_region h rb = Some (ps, ds, de) -> 0 <= rb <= oa_d o ->
    dst_rel (oa_c o) rb m ->
    (forall j, ps <= j < oa_d o - rb \/ ds <= j < de -> nth (Z.to_nat j) m None <> None) ->
    0 <= bo -> bo + Zlength body <= iw_N i -> sublist bo (bo + Zlength body) (iw_c i) = zbytes body ->
    litloc_rel l rb bo (Zlength lits) lr li lim sp ->
    (* the region starts at or before prefixStart and dictStart, the body at or before in-place literals *)
    0 <= ps -> 0 <= ds -> 0 <= li ->
    (lr = R_dst -> forall j, li <= j < lim + WILDCOPY_OVERLENGTH -> nth (Z.to_nat j) m None <> None) ->
    (lr = R_src -> lim + WILDCOPY_OVERLENGTH <= Zlength body) ->
    let e := {| xe_src := body; xe_ps := ps; xe_vs := ps - (de - ds); xe_de := de; xe_oend := seq_oend l rb o |} in
    let s0 := {| xmm := {| xm_dst := m; xm_lxb := lxb |}; xop := oa_d o - rb; xlr := lr; xli := li; xlim := lim;
                 xsp := sp |} in
    match x_seq_section e os rep (iw_s i) nbSeq s0 with
    | None => is_error_code r = true
    | Some (mm, op', rep2) =>
        is_error_code r = false /\ r = op' - (oa_d o - rb) /\ dst_rel oc' rb (xm_dst mm) /\ rep' = rep2
    end.

(* ===================== LIT ===================== *)

(* ZSTD_blockSizeMax(dctx): fParams.blockSizeMax in a frame *)
Definition ZSTD_blockSizeMax_spec : ident * funspec :=
  DECLARE _ZSTD_blockSizeMax
  WITH p: val, fs: fstate, bsm: Z
  PRE [ tptr t_dctx ]
    PROP (0 <= bsm <= ZSTD_BLOCKSIZE_MAX; fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1))
    PARAMS (p) SEP (frame_fields p fs)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr bsm)) SEP (frame_fields p fs).

(* The 32 cells after the literals in the output array (LDst; for LSplit after its part in the output array) hold
   defined bytes: the sequence executors over-read them (ZSTD_copy16, the wild copies), and memcpy and memmove are
   libc.c's byte loops (QuickProof v0.1.0-beta.1).  ZSTD_allocateLiteralsBuffer zeroes them (patch item 19), or
   they are Huffman-decoded literals (a split buffer after its shift).  The other places need nothing:
   litExtraBuffer holds bytes (litfields), literals read in place have the rest of the block after them. *)
Definition lit_slack_def (l: litloc) (oc: list val) (n: Z) : Prop :=
  match l with
  | LDst lb => Forall is_byte_val (sublist (lb + n) (lb + n + WILDCOPY_OVERLENGTH) oc)
  | LSplit lb =>
      Forall is_byte_val (sublist (lb + (n - LITBUFFEREXTRASIZE)) (lb + (n - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) oc)
  | _ => True
  end.

(* the literals section's outcome (success): its place and bytes, the new Huffman state *)
Definition lits_ok (oh: option huf_table) (o: outarr) (i: inwin) (bsm streaming r: Z) (oc': list val)
    (l: litloc) (lits: list Z) (oh': option huf_table) : Prop :=
  1 <= r <= Zlength (iw_s i) /\ lits_at l oc' (oa_d o) (oa_cap o) i lits /\
  Zlength lits <= Z.min (oa_cap o) bsm /\
  (match l with LDst _ => streaming = 0 | _ => True end) /\
  (match oh' with Some ht => huf_ok ht | None => oh = None end) /\
  (match decode_literals oh (iw_s i) bsm with
   | Some (lits0, used, huf') => r = used /\ lits = lits0 /\ oh' = huf'
   | None => True
   end) /\
  lit_pos l (oa_d o) (oa_cap o) bsm (Zlength lits) /\
  lit_slack_def l oc' (Zlength lits).

(* ZSTD_decodeLiteralsBlock(dctx, src, srcSize, dst, dstCapacity, streaming): the literals section at the
   start of the block body s (|s| <= bsm).  Any s: an error, or the bytes it takes, the literals (litfields,
   lits_at) and the new Huffman state; the output array changes only in [d, d+cap) (streaming: in
   [d, d + min(cap, bsm))).  When the model decodes the section: exactly its literals, bytes and table, or
   a capacity error (min(cap, bsm) < |lits|). *)
Definition ZSTD_decodeLiteralsBlock_spec : ident * funspec :=
  DECLARE _ZSTD_decodeLiteralsBlock
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, oh: option huf_table, x2: bool, lxb: list Z, bsm: Z,
       streaming: Z, W: list ptr_witness, o: outarr, i: inwin
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tint ]
    PROP (outarr_ok o; inwin_ok i; streaming = 0 \/ streaming = 1; 0 <= bsm <= ZSTD_BLOCKSIZE_MAX;
          Zlength (iw_s i) <= bsm;
          fp_blockSizeMax (fs_fParams fs) = Vint (Int.repr bsm);
          fs_isFrameDecompression fs = Vint (Int.repr 1);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          match oh with Some ht => huf_ok ht | None => True end)
    PARAMS (p; offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i)));
            offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o)); Vint (Int.repr streaming))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p fs; tabs_huf gv p ox oh x2; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; lit_scratch_x p lxb;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i))
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX l: litloc, EX lits: list Z, EX oh': option huf_table, EX x2': bool,
    EX lxb': list Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o;
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          streaming = 1 -> unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) bsm);
          is_error_code r = false -> lits_ok oh o i bsm streaming r oc' l lits oh';
          match decode_literals oh (iw_s i) bsm with
          | Some (lits0, _, _) => is_error_code r = false \/ Z.min (oa_cap o) bsm < Zlength lits0
          | None => True
          end;
          is_error_code r = true -> dec_err r;
          byte_cells (oa_c o) -> byte_cells (iw_c i) -> byte_cells oc';
          ox = None ->
          lits_exact (option_map (xhuf_of x2) oh) lxb o i bsm streaming r oc' l lits
            (option_map (xhuf_of x2') oh') lxb')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p fs; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i);
         if is_error_code r then huf_junk p * lit_scratch p
         else tabs_huf gv p ox oh' x2' * litfields p (oa_base o) (iw_base i) l lits lxb').

(* ===================== HDR ===================== *)

(* zstd's outcome of the sequences section's header (C-result form, as ENT's FSE_readNCount_spec: zstd may
   accept a table description the model rejects): the number of sequences, the tables, the bytes taken *)
Definition shdr_ok (os: option (fse_table * fse_table * fse_table)) (s: list Z)
    (res: option (Z * option (fse_table * fse_table * fse_table) * Z)) : Prop :=
  (forall x, decode_seq_header os s = Some x -> res = Some x) /\
  match res with
  | Some (nb, os', used) =>
      1 <= used <= Zlength s /\ 0 <= nb <= LONGNBSEQ + 65535 /\ seqs_ok os' /\
      (nb = 0 -> os' = os) /\ (0 < nb -> os' <> None)
  | None => True
  end.

(* ZSTD_decodeSeqHeaders(dctx, &nbSeq, src, srcSize): the sequences section's header at the start of the
   window s, any bytes: an error, or zstd's outcome res (shdr_ok: the model's whenever the model decodes it);
   the number of sequences in *nbSeqPtr, the tables os' (unchanged when nbSeq = 0; fseEntropy untouched);
   seq_junk after an error. *)
Definition ZSTD_decodeSeqHeaders_spec : ident * funspec :=
  DECLARE _ZSTD_decodeSeqHeaders
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, os: option (fse_table * fse_table * fse_table),
       fe: Z, shn: share, pn: val, i: inwin
  PRE [ tptr t_dctx, tptr tint, tptr tvoid, tulong ]
    PROP (inwin_ok i; writable_share shn; seqs_ok os;
          fe = (match os with Some _ => 1 | None => 0 end);
          fs_ddictIsCold fs = Vint (Int.repr 0) \/ fs_ddictIsCold fs = Vint (Int.repr 1);
          Zlength (iw_s i) <= ZSTD_BLOCKSIZE_MAX)
    PARAMS (p; pn; offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i))))
    GLOBALS (gv)
    SEP (zstd_globals gv; frame_fields p fs; tabs_seq gv p ox os fe; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p; data_at_ shn tint pn;
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i))
  POST [ tulong ]
    EX r: Z, EX res: option (Z * option (fse_table * fse_table * fse_table) * Z),
    PROP (0 <= r <= Int64.max_unsigned; shdr_ok os (iw_s i) res;
          match res with
          | Some (_, _, used) => r = used
          | None => is_error_code r = true
          end;
          is_error_code r = true -> dec_err r;
          (* exactly: zstd's own outcome on every header (ExBlock.x_seq_header) *)
          res = xb_seq_header os (iw_s i))
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; frame_fields p fs; dent_of dent_def gv ox;
         field_at_ Ews t_dctx (DOT _workspace) p;
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i);
         match res with
         | Some (nb, os', _) => data_at shn tint (Vint (Int.repr nb)) pn * tabs_seq gv p ox os' fe
         | None => data_at_ shn tint pn * seq_junk p
         end).

(* ===================== SEQ ===================== *)

(* the content and repeat offsets the model gives the sequences section: nbSeq sequences decoded from
   the bitstream with the tables os, executed after the frame output out (behind hist) *)
Definition seqs_model (os: option (fse_table * fse_table * fse_table)) (bits: list Z) (nbSeq: Z)
    (rep: Z * Z * Z) (hist out lits: list Z) (wsize: Z) : option (list Z * (Z * Z * Z)) :=
  let seqs :=
    if nbSeq =? 0 then Some nil else
    match os with
    | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML bits nbSeq
    | None => None
    end in
  match seqs with
  | None => None
  | Some seqs =>
      match exec_seqs wsize rep hist lits out seqs with
      | None => None
      | Some (out', lits', rep') => Some (skipn (length out) (out' ++ lits'), rep')
      end
  end.

(* ZSTD_decompressSequences / ...SplitLitBuffer / ...Long (dctx, dst, maxDstSize, seqStart, seqSize, nbSeq,
   isLongOffset = 0): execute the sequences section (bitstream = the window i) after the literals (l, lits)
   into the output array o.  Any bitstream: no undefined behaviour, the output changes only in [d, d+cap);
   success = r <= cap bytes, written only in [d, d + min(cap, r + 32)), defined bytes when the history is
   (hist_def) and an extDict in the output array is out of the way (ext_clean), or beyond what a section of
   r <= bsm bytes writes (ext_far: op only grows, so all writes stay in [d, d + min(cap, bsm + 32))); the
   literal fields become scratch, fseEntropy 1 when there are sequences, the repeat offsets rep' (any value
   after an error: the C saves them before its last capacity check).  When the
   history is the model's (hist_view, ext_clear, or cap = 0) and the model executes the section: exactly
   its content and repeat offsets, or a capacity error (cap < |content|). *)
Definition seqs_spec (allowed: litloc -> Prop) : funspec :=
  WITH gv: globals, p: val, fs: fstate, ox: option ddx, os: option (fse_table * fse_table * fse_table),
       fe: Z, rep: Z * Z * Z, l: litloc, lits: list Z, lxb: list Z, nbSeq: Z, bsm: Z,
       W: list ptr_witness, o: outarr, i: inwin, h: hctx
  PRE [ tptr t_dctx, tptr tvoid, tulong, tptr tvoid, tulong, tint, tint ]
    PROP (outarr_ok o; inwin_ok i; allowed l; lits_at l (oa_c o) (oa_d o) (oa_cap o) i lits;
          0 <= bsm <= ZSTD_BLOCKSIZE_MAX; Zlength lits <= bsm;
          0 <= nbSeq <= LONGNBSEQ + 65535; nbSeq > 0 -> os <> None /\ 0 < oa_cap o;
          seqs_ok os; rep_ok rep; fe = 0 \/ fe = 1;
          oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)));
          0 < oa_cap o -> layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h);
          hist_ptrs_ok fs o (hc_ext h);
          lit_pos l (oa_d o) (oa_cap o) bsm (Zlength lits); ext0_ok W fs (hc_ext h);
          (* what the copies read is defined (memcpy and memmove are libc.c's byte loops): the history, the
             32 cells after the literals in the output array *)
          hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h); lit_slack_def l (oa_c o) (Zlength lits))
    PARAMS (p; offset_val (oa_d o) (oa_base o); Vlong (Int64.repr (oa_cap o));
            offset_val (iw_off i) (iw_base i); Vlong (Int64.repr (Zlength (iw_s i)));
            Vint (Int.repr nbSeq); Vint (Int.repr 0))
    GLOBALS (gv)
    SEP (zstd_globals gv; pws_pred W; frame_fields p fs; tabs_seq gv p ox os fe; dent_of dent_def gv ox;
         field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p;
         litfields p (oa_base o) (iw_base i) l lits lxb;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h))
  POST [ tulong ]
    EX r: Z, EX oc': list val, EX rep': Z * Z * Z,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o; rep_ok rep';
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
          is_error_code r = false ->
            r <= oa_cap o /\
            unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
            (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
             (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
               exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
          oa_cap o = 0 \/
          (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
           ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
          match seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h) with
          | Some (cnt, rep2) =>
              Zlength cnt <= bsm ->
              (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
               rep' = rep2) \/
              (is_error_code r = true /\ oa_cap o < Zlength cnt)
          | None => True
          end;
          is_error_code r = true -> dec_err r;
          byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc';
          seqs_exact os rep l lits lxb nbSeq o i h r oc' rep')
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; pws_pred W; frame_fields p fs;
         tabs_seq gv p ox os (if nbSeq =? 0 then fe else 1); dent_of dent_def gv ox;
         field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p; lit_scratch_x p lxb;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
         data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)).

Definition not_split (l: litloc) : Prop := match l with LSplit _ => False | _ => True end.
Definition is_split (l: litloc) : Prop := match l with LSplit _ => True | _ => False end.

Definition ZSTD_decompressSequences_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequences seqs_spec not_split.
Definition ZSTD_decompressSequencesSplitLitBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequencesSplitLitBuffer seqs_spec is_split.
Definition ZSTD_decompressSequencesLong_spec : ident * funspec :=
  DECLARE _ZSTD_decompressSequencesLong seqs_spec (fun _ => True).
