(* Sub-group EXEC of CORE: the sequence executors.

     ZSTD_execSequenceEnd, ZSTD_execSequenceEndSplitLitBuffer, ZSTD_execSequence,
     ZSTD_execSequenceSplitLitBuffer

   The bodies are proved (EXEC_ok) against the COPY helpers (BlkSeqCOPY) and memmove / ZSTD_copy16 of G_BLK.

   One call executes one sequence (ll, ml, off) at op = ob + k of the output array c (N = |c| cells at ob),
   oend = ob + e; the literals are at litPtr = base + li (in a separate array: LitSep, the input array or
   litExtraBuffer; or in the output array itself: LitIn), litLimit = base + lim; the history is the
   prefix from prefixStart = ob + ps and the extDict x (DecIface.ext_seg), virtualStart = ob + ps - elen.
   The result: an error exactly under the C's conditions (exec_err / exec_split_err: capacity, literals,
   offset beyond the history; split: the output caught up with the literals); otherwise ll + ml, litPtr
   advanced by ll, the bytes [k, k + ll + ml) are exec_c (BlkSeqExecModel: literals, then the match
   from the array / the extDict) unless the extDict part reads bytes the literal copy's slack just
   overwrote (ext_read_ok), and nothing is written outside [k, min(e, k + ll + ml + 32)).  The byte copies
   are memmoves (contract VST edit): any bytes may be copied; the written
   bytes are defined when everything read is (the prefix [ps, k), the literals, the extDict); and, success or
   error, every cell of the output array is a byte if every cell of the arrays read is (byte_cells: bytes in,
   bytes out, slack included). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqExecModel.
Local Open Scope logic.

(* where the literals are *)
Inductive litsrc := LitSep (shl: share) (lb: val) (cl: list val) | LitIn.

Definition lit_base (ls: litsrc) (ob: val) : val := match ls with LitSep _ lb _ => lb | LitIn => ob end.
Definition lit_arr (ls: litsrc) (c: list val) : list val := match ls with LitSep _ _ cl => cl | LitIn => c end.
Definition lit_res (ls: litsrc) : mpred :=
  match ls with LitSep shl lb cl => data_at shl (tarray tuchar (Zlength cl)) cl lb | LitIn => emp end.

(* the dictEnd argument: the end of the extDict; anything (dE) without one *)
Definition dict_end (x: ext_seg) (ob dE: val) : val :=
  match x with ExtNone => dE | ExtIn e1 _ => offset_val e1 ob | ExtSep _ eb _ _ e1 _ => offset_val e1 eb end.

(* the extDict lies inside its array (for ExtIn it may overlap anything, e.g. a ring buffer) *)
Definition exec_ext_ok (x: ext_seg) (c: list val) : Prop :=
  0 <= ext_len x <= 2 ^ 63 - 1 /\
  match x with
  | ExtNone => True
  | ExtIn e1 elen => 0 <= e1 - elen /\ e1 <= Zlength c
  | ExtSep sh eb en ec e1 elen =>
      readable_share sh /\ Zlength ec = en /\ en <= 2 ^ 63 - 1 /\ 0 <= e1 - elen /\ e1 <= en
  end.

(* its bytes are defined *)
Definition ext_def (x: ext_seg) (c: list val) : Prop :=
  match x with
  | ExtNone => True
  | ExtIn e1 elen => Forall is_byte_val (sublist (e1 - elen) e1 c)
  | ExtSep _ _ _ ec e1 elen => Forall is_byte_val (sublist (e1 - elen) e1 ec)
  end.

(* the bytes an ExtIn extDict part of the match reads ([e1 - dl, e1 - dl + min(ml, dl)), dl = off - (x0 - ps),
   x0 = k + ll) are not in the literal copy's slack [x0, min(e, x0 + 32)), which the C writes before it *)
Definition ext_read_ok (x: ext_seg) (k e ll ml off ps: Z) : Prop :=
  match x with
  | ExtIn e1 _ =>
      let x0 := k + ll in let dl := off - (x0 - ps) in
      off <= x0 - ps \/ Z.min e (x0 + WILDCOPY_OVERLENGTH) <= e1 - dl \/ e1 - dl + Z.min ml dl <= x0
  | _ => True
  end.

(* the literals' array as a source of BlkSeqXMem's copies *)
Definition ls_l (ls: litsrc) : lsrc := match ls with LitSep _ _ cl => LS cl | LitIn => LW end.

(* the C's error conditions *)
Definition exec_err (k e li lim ll ml off ps elen: Z) : bool :=
  (e - k <? ll + ml) || (lim - li <? ll) || (k + ll - ps + elen <? off).
Definition exec_split_err (k e li ll ml off ps elen: Z) : bool :=
  (e - k <? ll + ml) || ((li <? k) && (k <? li + ll)) || (k + ll - ps + elen <? off).

(* the literals of the split variants are copied exactly unless 16 < li - k < 32 (safecopyDstBeforeSrc's
   wild part then overwrites its source; unreachable when the literals are far ahead of op) *)
Definition lit_exact_split (k li ll: Z) : Prop := ll < 32 \/ li <= k + 16 \/ k + 32 <= li.

(* ZSTD_execSequence / ZSTD_execSequenceEnd (op, oend, &seq, &litPtr, litLimit, prefixStart,
   virtualStart, dictEnd): literals not split.  Literals in the output array lie at or after oend
   (litBuffer in dst). *)
Definition exec_spec : funspec :=
  WITH gv: globals, sh: share, ob: val, c: list val, k: Z, e: Z,
       shq: share, sp: val, ll: Z, ml: Z, off: Z, shp: share, plp: val,
       ls: litsrc, li: Z, lim: Z, ps: Z, x: ext_seg, dE: val
  PRE [ tptr tuchar, tptr tuchar, tptr t_seq, tptr (tptr tuchar), tptr tuchar, tptr tuchar, tptr tuchar,
        tptr tuchar ]
    PROP (writable_share sh; readable_share shq; writable_share shp;
          Zlength c <= 2 ^ 63 - 1; 0 <= ps <= k; k <= e <= Zlength c;
          0 <= ll <= 2 ^ 24; 1 <= ml <= 2 ^ 24; 1 <= off <= Int64.max_unsigned;
          match ls with
          | LitSep shl _ cl => readable_share shl /\ 0 <= li <= lim /\ lim + WILDCOPY_OVERLENGTH <= Zlength cl
          | LitIn => e <= li <= lim /\ lim + WILDCOPY_OVERLENGTH <= Zlength c
          end;
          exec_ext_ok x c; is_pointer_or_null dE;
          (* what the copies read is defined (memcpy and memmove are libc.c's byte loops): the history, the
             literals with the 32 bytes after them, the extDict *)
          Forall is_byte_val (sublist ps k c);
          Forall is_byte_val (sublist li (lim + WILDCOPY_OVERLENGTH) (lit_arr ls c));
          ext_def x c;
          (* litLimit - litPtr is a ptrdiff_t the C compares with litLength: it does not wrap (for literals
             in the output array this follows from Zlength c <= 2 ^ 63 - 1) *)
          lim - li <= Int64.max_signed)
    PARAMS (offset_val k ob; offset_val e ob; sp; plp; offset_val lim (lit_base ls ob); offset_val ps ob;
            offset_val (ps - ext_len x) ob; dict_end x ob dE)
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) (offset_val li (lit_base ls ob)) plp; lit_res ls; ext_res x)
  POST [ tulong ]
    EX r: Z, EX c': list val, EX lp: val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength c' = Zlength c;
          byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes x -> byte_cells c';
          is_error_code r = exec_err k e li lim ll ml off ps (ext_len x);
          is_error_code r = true -> unchanged_outside c c' k e /\ dec_err r;
          is_error_code r = false ->
            r = (ll + ml)%Z /\ lp = offset_val (li + ll) (lit_base ls ob) /\
            unchanged_outside c c' k (Z.min e (k + r + WILDCOPY_OVERLENGTH)) /\
            (ext_read_ok x k e ll ml off ps ->
               sublist k (k + r) c' = sublist k (k + r) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps x) /\
               (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
                ext_def x c -> Forall is_byte_val (sublist k (k + r) c')));
          (* every cell is unchanged or a defined byte (the copies read only defined bytes, slack included) *)
          forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c');
          (* the bytes written are defined *)
          is_error_code r = false -> Forall is_byte_val (sublist k (k + r) c');
          (* exactly its stores, store by store, slack included (BlkSeqXMem.lexec, the model's x_exec), the
             history in the output array *)
          match x with
          | ExtSep _ _ _ _ _ _ => True
          | _ => is_error_code r = false ->
                 c' = lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c' ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) lp plp; lit_res ls; ext_res x).

(* ZSTD_execSequenceSplitLitBuffer / ZSTD_execSequenceEndSplitLitBuffer (op, oend, oend_w, &seq, &litPtr,
   litLimit, prefixStart, virtualStart, dictEnd): the literals are the head of a split literal buffer in
   the output array, oend_w = litPtr + ll - WILDCOPY_OVERLENGTH (the call sites), li + ll <= lim (the
   loops checked it), and 32 readable bytes after lim before oend. *)
Definition exec_split_spec : funspec :=
  WITH gv: globals, sh: share, ob: val, c: list val, k: Z, e: Z,
       shq: share, sp: val, ll: Z, ml: Z, off: Z, shp: share, plp: val,
       li: Z, lim: Z, ps: Z, x: ext_seg, dE: val
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr t_seq, tptr (tptr tuchar), tptr tuchar, tptr tuchar,
        tptr tuchar, tptr tuchar ]
    PROP (writable_share sh; readable_share shq; writable_share shp;
          Zlength c <= 2 ^ 63 - 1; 0 <= ps <= k; k <= e <= Zlength c;
          0 <= ll <= 2 ^ 24; 1 <= ml <= 2 ^ 24; 1 <= off <= Int64.max_unsigned;
          0 <= li; li + ll <= lim; lim + WILDCOPY_OVERLENGTH <= e;
          exec_ext_ok x c; is_pointer_or_null dE;
          (* what the copies read is defined (memcpy and memmove are libc.c's byte loops) *)
          Forall is_byte_val (sublist ps k c);
          Forall is_byte_val (sublist li (lim + WILDCOPY_OVERLENGTH) c);
          ext_def x c;
          (* ZSTD_safecopy compares oend_w = litPtr + ll - 32 with the end of the match copy (a ptrdiff_t
             difference, which must not wrap): once the size check has passed (k + ll + ml <= e) this bound
             gives it; the split literal buffer lies near the end of dst *)
          e - li + WILDCOPY_OVERLENGTH <= 2 ^ 63)
    PARAMS (offset_val k ob; offset_val e ob; offset_val (li + ll - WILDCOPY_OVERLENGTH) ob; sp; plp;
            offset_val lim ob; offset_val ps ob; offset_val (ps - ext_len x) ob; dict_end x ob dE)
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) (offset_val li ob) plp; ext_res x)
  POST [ tulong ]
    EX r: Z, EX c': list val, EX lp: val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength c' = Zlength c;
          byte_cells c -> ext_bytes x -> byte_cells c';
          is_error_code r = exec_split_err k e li ll ml off ps (ext_len x);
          is_error_code r = true -> unchanged_outside c c' k e /\ dec_err r;
          is_error_code r = false ->
            r = (ll + ml)%Z /\ lp = offset_val (li + ll) ob /\
            unchanged_outside c c' k (Z.min (Z.min e (k + r + WILDCOPY_OVERLENGTH)) (Z.max (k + r) (li + ll))) /\
            (ext_read_ok x k e ll ml off ps ->
               (lit_exact_split k li ll ->
                  sublist k (k + r) c' = sublist k (k + r) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
               (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
                ext_def x c -> Forall is_byte_val (sublist k (k + r) c')));
          (* every cell is unchanged or a defined byte *)
          forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c');
          (* the bytes written are defined *)
          is_error_code r = false -> Forall is_byte_val (sublist k (k + r) c');
          (* exactly its stores (BlkSeqXMem.lexec_split, the model's x_exec_split) *)
          match x with
          | ExtSep _ _ _ _ _ _ => True
          | _ => is_error_code r = false ->
                 c' = lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c' ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) lp plp; ext_res x).

(* ZSTD_execSequenceEnd / ZSTD_execSequenceEndSplitLitBuffer: called only on their callers' slow path
   (ZSTD_execSequence, ZSTD_execSequenceSplitLitBuffer), whose condition they take as a precondition: they
   always copy as the slow path does (ZSTD_safecopy / ZSTD_safecopyDstBeforeSrc), which lexec / lexec_split
   mirror only under that condition.  Otherwise the same specifications. *)
Definition exec_end_spec : funspec :=
  WITH gv: globals, sh: share, ob: val, c: list val, k: Z, e: Z,
       shq: share, sp: val, ll: Z, ml: Z, off: Z, shp: share, plp: val,
       ls: litsrc, li: Z, lim: Z, ps: Z, x: ext_seg, dE: val
  PRE [ tptr tuchar, tptr tuchar, tptr t_seq, tptr (tptr tuchar), tptr tuchar, tptr tuchar, tptr tuchar,
        tptr tuchar ]
    PROP (writable_share sh; readable_share shq; writable_share shp;
          Zlength c <= 2 ^ 63 - 1; 0 <= ps <= k; k <= e <= Zlength c;
          0 <= ll <= 2 ^ 24; 1 <= ml <= 2 ^ 24; 1 <= off <= Int64.max_unsigned;
          match ls with
          | LitSep shl _ cl => readable_share shl /\ 0 <= li <= lim /\ lim + WILDCOPY_OVERLENGTH <= Zlength cl
          | LitIn => e <= li <= lim /\ lim + WILDCOPY_OVERLENGTH <= Zlength c
          end;
          exec_ext_ok x c; is_pointer_or_null dE;
          (* what the copies read is defined (memcpy and memmove are libc.c's byte loops): the history, the
             literals with the 32 bytes after them, the extDict *)
          Forall is_byte_val (sublist ps k c);
          Forall is_byte_val (sublist li (lim + WILDCOPY_OVERLENGTH) (lit_arr ls c));
          ext_def x c;
          (* the caller's slow path: the literals reach litLimit or the sequence reaches oend_w *)
          orb (lim - li <? ll) (e - WILDCOPY_OVERLENGTH - k <? ll + ml) = true)
    PARAMS (offset_val k ob; offset_val e ob; sp; plp; offset_val lim (lit_base ls ob); offset_val ps ob;
            offset_val (ps - ext_len x) ob; dict_end x ob dE)
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) (offset_val li (lit_base ls ob)) plp; lit_res ls; ext_res x)
  POST [ tulong ]
    EX r: Z, EX c': list val, EX lp: val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength c' = Zlength c;
          byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes x -> byte_cells c';
          is_error_code r = exec_err k e li lim ll ml off ps (ext_len x);
          is_error_code r = true -> unchanged_outside c c' k e /\ dec_err r;
          is_error_code r = false ->
            r = (ll + ml)%Z /\ lp = offset_val (li + ll) (lit_base ls ob) /\
            unchanged_outside c c' k (Z.min e (k + r + WILDCOPY_OVERLENGTH)) /\
            (ext_read_ok x k e ll ml off ps ->
               sublist k (k + r) c' = sublist k (k + r) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps x) /\
               (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
                ext_def x c -> Forall is_byte_val (sublist k (k + r) c')));
          (* every cell is unchanged or a defined byte (the copies read only defined bytes, slack included) *)
          forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c');
          (* the bytes written are defined *)
          is_error_code r = false -> Forall is_byte_val (sublist k (k + r) c');
          (* exactly its stores, store by store, slack included (BlkSeqXMem.lexec, the model's x_exec), the
             history in the output array *)
          match x with
          | ExtSep _ _ _ _ _ _ => True
          | _ => is_error_code r = false ->
                 c' = lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c' ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) lp plp; lit_res ls; ext_res x).

Definition exec_end_split_spec : funspec :=
  WITH gv: globals, sh: share, ob: val, c: list val, k: Z, e: Z,
       shq: share, sp: val, ll: Z, ml: Z, off: Z, shp: share, plp: val,
       li: Z, lim: Z, ps: Z, x: ext_seg, dE: val
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr t_seq, tptr (tptr tuchar), tptr tuchar, tptr tuchar,
        tptr tuchar, tptr tuchar ]
    PROP (writable_share sh; readable_share shq; writable_share shp;
          Zlength c <= 2 ^ 63 - 1; 0 <= ps <= k; k <= e <= Zlength c;
          0 <= ll <= 2 ^ 24; 1 <= ml <= 2 ^ 24; 1 <= off <= Int64.max_unsigned;
          0 <= li; li + ll <= lim; lim + WILDCOPY_OVERLENGTH <= e;
          exec_ext_ok x c; is_pointer_or_null dE;
          (* what the copies read is defined (memcpy and memmove are libc.c's byte loops) *)
          Forall is_byte_val (sublist ps k c);
          Forall is_byte_val (sublist li (lim + WILDCOPY_OVERLENGTH) c);
          ext_def x c;
          (* ZSTD_safecopy compares oend_w = litPtr + ll - 32 with the end of the match copy (a ptrdiff_t
             difference, which must not wrap): once the size check has passed (k + ll + ml <= e) this bound
             gives it; the split literal buffer lies near the end of dst *)
          e - li + WILDCOPY_OVERLENGTH <= 2 ^ 63;
          (* the caller's slow path *)
          orb (lim - li <? ll) (li + ll - WILDCOPY_OVERLENGTH - k <? ll + ml) = true)
    PARAMS (offset_val k ob; offset_val e ob; offset_val (li + ll - WILDCOPY_OVERLENGTH) ob; sp; plp;
            offset_val lim ob; offset_val ps ob; offset_val (ps - ext_len x) ob; dict_end x ob dE)
    GLOBALS (gv)
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) (offset_val li ob) plp; ext_res x)
  POST [ tulong ]
    EX r: Z, EX c': list val, EX lp: val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength c' = Zlength c;
          byte_cells c -> ext_bytes x -> byte_cells c';
          is_error_code r = exec_split_err k e li ll ml off ps (ext_len x);
          is_error_code r = true -> unchanged_outside c c' k e /\ dec_err r;
          is_error_code r = false ->
            r = (ll + ml)%Z /\ lp = offset_val (li + ll) ob /\
            unchanged_outside c c' k (Z.min (Z.min e (k + r + WILDCOPY_OVERLENGTH)) (Z.max (k + r) (li + ll))) /\
            (ext_read_ok x k e ll ml off ps ->
               (lit_exact_split k li ll ->
                  sublist k (k + r) c' = sublist k (k + r) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
               (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
                ext_def x c -> Forall is_byte_val (sublist k (k + r) c')));
          (* every cell is unchanged or a defined byte *)
          forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c');
          (* the bytes written are defined *)
          is_error_code r = false -> Forall is_byte_val (sublist k (k + r) c');
          (* exactly its stores (BlkSeqXMem.lexec_split, the model's x_exec_split) *)
          match x with
          | ExtSep _ _ _ _ _ _ => True
          | _ => is_error_code r = false ->
                 c' = lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
          end)
    RETURN (Vlong (Int64.repr r))
    SEP (zstd_globals gv; data_at sh (tarray tuchar (Zlength c)) c' ob; data_at shq t_seq (seqrep ll ml off) sp;
         data_at shp (tptr tuchar) lp plp; ext_res x).

Definition ZSTD_execSequenceEnd_spec : ident * funspec := DECLARE _ZSTD_execSequenceEnd exec_end_spec.
Definition ZSTD_execSequence_spec : ident * funspec := DECLARE _ZSTD_execSequence exec_spec.
Definition ZSTD_execSequenceEndSplitLitBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_execSequenceEndSplitLitBuffer exec_end_split_spec.
Definition ZSTD_execSequenceSplitLitBuffer_spec : ident * funspec :=
  DECLARE _ZSTD_execSequenceSplitLitBuffer exec_split_spec.

(* ================= sub-group EXEC ================= *)
Definition EXEC_ids : list ident :=
  [ _ZSTD_execSequenceEnd; _ZSTD_execSequenceEndSplitLitBuffer; _ZSTD_execSequence;
    _ZSTD_execSequenceSplitLitBuffer ].
Definition EXEC_exports : funspecs :=
  [ ZSTD_execSequenceEnd_spec; ZSTD_execSequenceEndSplitLitBuffer_spec; ZSTD_execSequence_spec;
    ZSTD_execSequenceSplitLitBuffer_spec ].
Definition EXEC_imports : funspecs := COPY_exports.
Definition EXEC_obligation : Prop := subtree_ok EXEC_ids EXEC_exports (G_BLK ++ EXEC_imports).

(* ================= the proofs ================= *)
Definition EXEC_G : funspecs := G_BLK ++ EXEC_imports ++ EXEC_exports.

(* ---------- glue: the bytes the C leaves in [k, x + ml) are exec_c ----------
   cA: the array after the literal copy (= put c k Lv below x = k + |Lv|, maybe slack after x);
   c2: after the extDict memmove; c': the final array. *)

(* the match lies in the prefix (off <= x - ps): a forward copy behind x *)
Lemma exec_glue_prefix (c cA c': list val) (k ps ml off x: Z) (Lv: list val) (xs: ext_seg) :
  x = k + Zlength Lv -> 0 <= ps <= k -> 1 <= off <= x - ps -> 1 <= ml -> x + ml <= Zlength c ->
  Zlength cA = Zlength c -> Zlength c' = Zlength c ->
  (forall p, ps <= p < x -> Znth p cA = Znth p (put c k Lv)) ->
  (forall p, k <= p < x -> Znth p c' = Znth p cA) ->
  sublist x (x + ml) c' = sublist x (x + ml) (listcopy cA (x - off) x (Z.to_nat ml)) ->
  sublist k (x + ml) c' = sublist k (x + ml) (exec_c c k Lv ml off ps xs).
Proof.
  intros Hx Hps Hoff Hml HN HcA Hc' HA Hc'A Hcp.
  pose proof (Zlength_nonneg Lv) as HLv.
  assert (HP: Zlength (put c k Lv) = Zlength c) by (apply ecl_Zlength_put; lia).
  unfold exec_c. rewrite <- Hx. replace (off <=? x - ps) with true by (symmetry; apply Z.leb_le; lia).
  assert (HL1: Zlength (listcopy (put c k Lv) (x - off) x (Z.to_nat ml)) = Zlength c)
    by (rewrite Zlength_listcopy; lia).
  apply Znth_eq_ext.
  { rewrite !Zlength_sublist; lia. }
  rewrite Zlength_sublist by lia. intros i Hi.
  rewrite !Znth_sublist by lia.
  destruct (Z_lt_le_dec (i + k) x) as [Hlt | Hge].
  - rewrite Hc'A by lia. rewrite HA by lia.
    rewrite listcopy_suffix by lia. reflexivity.
  - assert (Hq: Znth (i + k - x) (sublist x (x + ml) c') =
                Znth (i + k - x) (sublist x (x + ml) (listcopy cA (x - off) x (Z.to_nat ml))))
      by (rewrite Hcp; reflexivity).
    rewrite !Znth_sublist in Hq by lia.
    replace (i + k - x + x) with (i + k) in Hq by lia. rewrite Hq.
    rewrite !lc_char by lia.
    replace (andb (x <=? i + k) (i + k <? x + ml)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    apply HA.
    pose proof (Z.mod_pos_bound (i + k - (x - off)) (x - (x - off))). lia.
Qed.

(* the match starts dl bytes before the end of the extDict: l1 = min(ml, dl) bytes from there, then
   (l1 < ml) a forward copy from ps to x + l1 *)
Lemma exec_glue_ext (c cA c2 c': list val) (k ps ml off x dl l1: Z) (Lv: list val) (xs: ext_seg) :
  x = k + Zlength Lv -> dl = off - (x - ps) -> l1 = Z.min ml dl ->
  0 <= ps <= k -> 0 < dl <= ext_len xs -> 1 <= ml -> x + ml <= Zlength c -> exec_ext_ok xs c ->
  Zlength cA = Zlength c -> Zlength c2 = Zlength c -> Zlength c' = Zlength c ->
  (forall p, ps <= p < x -> Znth p cA = Znth p (put c k Lv)) ->
  sublist (ext_end xs - dl) (ext_end xs - dl + l1) (ext_src cA xs) =
    sublist (ext_end xs - dl) (ext_end xs - dl + l1) (ext_src (put c k Lv) xs) ->
  (forall p, ps <= p < x -> Znth p c2 = Znth p cA) ->
  sublist x (x + l1) c2 = sublist (ext_end xs - dl) (ext_end xs - dl + l1) (ext_src cA xs) ->
  (forall p, k <= p < x + l1 -> Znth p c' = Znth p c2) ->
  (l1 < ml -> sublist (x + l1) (x + ml) c' = sublist (x + l1) (x + ml) (listcopy c2 ps (x + l1) (Z.to_nat (ml - l1)))) ->
  sublist k (x + ml) c' = sublist k (x + ml) (exec_c c k Lv ml off ps xs).
Proof.
  intros Hx Hdl Hl1 Hps Hdl0 Hml Hxml Hxok HlA Hl2 Hl' HA Hext H2 HS2 H' Hcp.
  pose proof (Zlength_nonneg Lv) as HLv.
  set (E := ext_end xs) in *.
  set (c1 := put c k Lv) in *.
  assert (Hc1l: Zlength c1 = Zlength c) by (unfold c1; apply ecl_Zlength_put; lia).
  assert (HE: 0 <= E - dl /\ E <= Zlength (ext_src c1 xs)).
  { destruct Hxok as [_ Hxk]. unfold E.
    destruct xs as [|e1 elen|sh eb en ec e1 elen]; simpl in *; lia. }
  assert (Hl1b: 0 <= l1 <= ml /\ l1 <= dl) by lia.
  set (S := sublist (E - dl) (E - dl + l1) (ext_src c1 xs)) in *.
  assert (HSl: Zlength S = l1) by (unfold S; rewrite Zlength_sublist; lia).
  set (C2 := put c1 x S).
  assert (HC2l: Zlength C2 = Zlength c) by (unfold C2; rewrite ecl_Zlength_put; lia).
  assert (Hag: forall q, ps <= q < x + l1 -> Znth q c2 = Znth q C2).
  { intros q Hq. unfold C2. destruct (Z_lt_le_dec q x).
    - rewrite ecl_Znth_put_out by lia. rewrite H2 by lia. apply HA. lia.
    - rewrite ecl_Znth_put_in by lia.
      assert (E1: Znth (q - x) (sublist x (x + l1) c2) = Znth q c2).
      { rewrite Znth_sublist by lia. f_equal. lia. }
      rewrite <- E1, HS2, Hext. reflexivity. }
  assert (Hrhs: exec_c c k Lv ml off ps xs = listcopy C2 ps (x + l1) (Z.to_nat (ml - l1))).
  { unfold exec_c. cbv zeta. rewrite <- Hx, <- Hdl. fold c1.
    destruct (off <=? x - ps) eqn:Ho; [apply Z.leb_le in Ho; lia|].
    rewrite <- Hl1. reflexivity. }
  rewrite Hrhs.
  apply Znth_eq_ext.
  - rewrite !Zlength_sublist; try lia.
    all: rewrite listcopy_Zlength; rewrite ?Z2Nat.id; lia.
  - intros i Hi. rewrite Zlength_sublist in Hi by lia.
    rewrite !Znth_sublist by lia.
    destruct (Z_lt_le_dec (i + k) (x + l1)).
    + rewrite H' by lia.
      rewrite listcopy_outside by (rewrite ?Z2Nat.id; lia).
      apply Hag. lia.
    + assert (Hlt: l1 < ml) by lia.
      assert (El1: l1 = dl) by lia.
      specialize (Hcp Hlt).
      assert (E1: Znth (i + k - (x + l1)) (sublist (x + l1) (x + ml) c') = Znth (i + k) c').
      { rewrite Znth_sublist by lia. f_equal. lia. }
      rewrite <- E1, Hcp, Znth_sublist by lia.
      replace (i + k - (x + l1) + (x + l1)) with (i + k) by lia.
      rewrite !lc_char by lia.
      replace (andb (x + l1 <=? i + k) (i + k <? x + l1 + (ml - l1))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Hag.
      pose proof (Z.mod_pos_bound (i + k - ps) (x + l1 - ps) ltac:(lia)). lia.
Qed.

(* ext_read_ok: what the extDict memmove reads after a literal copy with slack [x, W) is put c k Lv *)
Lemma exec_ext_read (c cA: list val) (k e ll ml off ps W dl: Z) (Lv: list val) (xs: ext_seg) :
  Zlength Lv = ll -> dl = off - (k + ll - ps) -> 0 <= ps <= k -> 0 < dl <= ext_len xs ->
  k + ll <= W <= Z.min e (k + ll + WILDCOPY_OVERLENGTH) -> k + ll + ml <= e -> e <= Zlength c -> 1 <= ml ->
  exec_ext_ok xs c -> Zlength cA = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < W) -> Znth p cA = Znth p (put c k Lv)) ->
  ext_read_ok xs k e ll ml off ps ->
  sublist (ext_end xs - dl) (ext_end xs - dl + Z.min ml dl) (ext_src cA xs) =
    sublist (ext_end xs - dl) (ext_end xs - dl + Z.min ml dl) (ext_src (put c k Lv) xs).
Proof.
  intros HL Hdl Hps Hdl2 HW Hml He Hml1 Hok HcA Hag Hrd.
  pose proof (Zlength_nonneg Lv).
  destruct xs as [ | e1 elen | sh eb en ec e1 elen]; simpl in *.
  - lia.
  - destruct Hok as [_ [Ho1 Ho2]].
    assert (Hput: Zlength (put c k Lv) = Zlength c) by (apply ecl_Zlength_put; lia).
    assert (Hmin: 0 <= Z.min ml dl <= dl) by lia.
    apply Znth_eq_ext.
    { rewrite !Zlength_sublist; lia. }
    rewrite Zlength_sublist by lia. intros i Hi.
    rewrite !Znth_sublist by lia.
    apply Hag; [lia |].
    unfold WILDCOPY_OVERLENGTH in *. lia.
  - reflexivity.
Qed.

(* the bytes exec_c writes are defined when everything it reads is *)
Lemma ecb_Forall_Znth (l: list val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= Zlength l -> (forall p, lo <= p < hi -> is_byte_val (Znth p l)) ->
  Forall is_byte_val (sublist lo hi l).
Proof.
  intros H1 H2 H. apply Forall_forall. intros v Hv.
  apply In_Znth in Hv. destruct Hv as [i [Hi Hv]]. subst v.
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist by lia. apply H. lia.
Qed.

Lemma ecb_Znth_Forall (l: list val) (lo hi p: Z) :
  0 <= lo -> hi <= Zlength l -> Forall is_byte_val (sublist lo hi l) -> lo <= p < hi ->
  is_byte_val (Znth p l).
Proof.
  intros H1 H2 H Hp. rewrite Forall_forall in H. apply H.
  replace (Znth p l) with (Znth (p - lo) (sublist lo hi l)) by (rewrite Znth_sublist by lia; f_equal; lia).
  apply Znth_In. rewrite Zlength_sublist by lia. lia.
Qed.

Lemma ecb_listcopy (a: list val) (si di lo: Z) (n: nat) :
  0 <= lo <= si -> si < di -> di + Z.of_nat n <= Zlength a ->
  (forall p, lo <= p < di -> is_byte_val (Znth p a)) ->
  forall p, lo <= p < di + Z.of_nat n -> is_byte_val (Znth p (listcopy a si di n)).
Proof.
  revert a si di. induction n as [|m IH]; intros a si di Hlo Hsd Hn Ha p Hp.
  - simpl. apply Ha. lia.
  - simpl. rewrite Nat2Z.inj_succ in *.
    assert (Hu: Zlength (upd_Znth di a (Znth si a)) = Zlength a) by apply Zlength_upd_Znth.
    apply IH; try lia.
    intros q Hq. destruct (Z.eq_dec q di) as [->|Hne].
    + rewrite upd_Znth_same by lia. apply Ha. lia.
    + rewrite upd_Znth_diff by lia. apply Ha. lia.
Qed.

Lemma exec_c_bytes (c: list val) (k ml off ps: Z) (Lv: list val) (xs: ext_seg) :
  0 <= ps <= k -> 1 <= ml -> k + Zlength Lv + ml <= Zlength c ->
  1 <= off <= k + Zlength Lv - ps + ext_len xs -> exec_ext_ok xs c ->
  Forall is_byte_val (sublist ps k c) -> Forall is_byte_val Lv -> ext_def xs c ->
  Forall is_byte_val (sublist k (k + Zlength Lv + ml) (exec_c c k Lv ml off ps xs)).
Proof.
  intros Hps Hml HL Hoff Hok Hpre HLv Hdef.
  pose proof (Zlength_nonneg Lv) as HLv0.
  set (x := k + Zlength Lv) in *.
  assert (Hc1l: Zlength (put c k Lv) = Zlength c) by (apply ecl_Zlength_put; lia).
  assert (Hc1: forall p, ps <= p < x -> is_byte_val (Znth p (put c k Lv))).
  { intros p Hp. destruct (Z_lt_le_dec p k).
    - rewrite ecl_Znth_put_out by lia. apply (ecb_Znth_Forall c ps k); auto; lia.
    - rewrite ecl_Znth_put_in by lia. apply (ecb_Znth_Forall Lv 0 (Zlength Lv)); try lia.
      rewrite sublist_same by lia. auto. }
  unfold exec_c. cbv zeta. fold x.
  destruct (off <=? x - ps) eqn:Hc.
  - apply Z.leb_le in Hc.
    assert (HL1: Zlength (listcopy (put c k Lv) (x - off) x (Z.to_nat ml)) = Zlength c)
      by (rewrite listcopy_Zlength; lia).
    apply ecb_Forall_Znth; try lia. intros p Hp.
    apply (ecb_listcopy _ (x - off) x ps); try (rewrite ?Z2Nat.id; lia).
    intros q Hq. apply Hc1. lia.
  - apply Z.leb_gt in Hc.
    set (dl := off - (x - ps)) in *.
    set (l1 := Z.min ml dl) in *.
    assert (Hl1: 1 <= l1 <= ml /\ l1 <= dl) by (unfold l1, dl; lia).
    assert (Hdl: dl <= ext_len xs) by (unfold dl; lia).
    set (S := sublist (ext_end xs - dl) (ext_end xs - dl + l1) (ext_src (put c k Lv) xs)).
    assert (HS: Zlength S = l1 /\ forall j, 0 <= j < l1 -> is_byte_val (Znth j S)).
    { unfold S. destruct xs as [|e1 elen|sh eb en ec e1 elen]; simpl in *.
      - lia.
      - destruct Hok as [_ [He0 He1]].
        split; [rewrite Zlength_sublist; lia|].
        intros j Hj. rewrite Znth_sublist by lia.
        destruct (Z_lt_le_dec (j + (e1 - dl)) k) as [L|L];
          [|destruct (Z_lt_le_dec (j + (e1 - dl)) x) as [L2|L2]].
        + rewrite ecl_Znth_put_out by lia. apply (ecb_Znth_Forall c (e1 - elen) e1); auto; lia.
        + apply Hc1. lia.
        + rewrite ecl_Znth_put_out by lia. apply (ecb_Znth_Forall c (e1 - elen) e1); auto; lia.
      - destruct Hok as [_ [_ [Hen [_ [He0 He1]]]]].
        split; [rewrite Zlength_sublist; lia|].
        intros j Hj. rewrite Znth_sublist by lia.
        apply (ecb_Znth_Forall ec (e1 - elen) e1); auto; lia. }
    destruct HS as [HSl HSb].
    assert (Hc2l: Zlength (put (put c k Lv) x S) = Zlength c) by (rewrite ecl_Zlength_put; lia).
    assert (HL1: Zlength (listcopy (put (put c k Lv) x S) ps (x + l1) (Z.to_nat (ml - l1))) = Zlength c)
      by (rewrite listcopy_Zlength; rewrite ?Z2Nat.id; lia).
    apply ecb_Forall_Znth; try lia. intros p Hp.
    apply (ecb_listcopy _ ps (x + l1) ps); try (rewrite ?Z2Nat.id; lia).
    intros q Hq. destruct (Z_lt_le_dec q x).
    + rewrite ecl_Znth_put_out by lia. apply Hc1. lia.
    + rewrite ecl_Znth_put_in by lia. apply HSb. lia.
Qed.

(* ---------- the definedness of what the executors write ----------
   memcpy and memmove are libc.c's byte loops, so every copy must read defined bytes.  xd_rng l lo hi: the
   cells [lo, hi) of l are defined bytes; xd_ub c c': every cell of c' is the cell of c or a defined byte (what
   a sequence of copies that read only defined bytes leaves behind, slack included).  A defined cell stays
   defined under xd_ub, so the history, the extDict and the literals stay readable. *)
Definition xd_rng (l: list val) (lo hi: Z) : Prop := forall q, lo <= q < hi -> is_byte_val (Znth q l).

Definition xd_ub (c c': list val) : Prop :=
  forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c').

Lemma xd_ub_refl (c: list val) : xd_ub c c.
Proof. intros q _. left. reflexivity. Qed.

Lemma xd_ub_trans (c c1 c2: list val) : Zlength c1 = Zlength c -> xd_ub c c1 -> xd_ub c1 c2 -> xd_ub c c2.
Proof.
  intros HL H1 H2 q Hq. destruct (H2 q ltac:(lia)) as [E|E]; [| right; exact E].
  rewrite E. exact (H1 q Hq).
Qed.

Lemma xd_rng_ub (c c': list val) (lo hi: Z) :
  0 <= lo -> hi <= Zlength c -> xd_ub c c' -> xd_rng c lo hi -> xd_rng c' lo hi.
Proof.
  intros H1 H2 Hu Hr q Hq. destruct (Hu q ltac:(lia)) as [E|E]; [rewrite E; apply Hr; lia | exact E].
Qed.

Lemma xd_rng_Forall (l: list val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= Zlength l -> xd_rng l lo hi -> Forall is_byte_val (sublist lo hi l).
Proof. intros. apply ecb_Forall_Znth; auto; lia. Qed.

Lemma xd_Forall_rng (l: list val) (lo hi: Z) :
  0 <= lo -> hi <= Zlength l -> Forall is_byte_val (sublist lo hi l) -> xd_rng l lo hi.
Proof. intros H1 H2 H q Hq. apply (ecb_Znth_Forall l lo hi); auto. Qed.

Lemma xd_rng_sub (l: list val) (lo hi lo' hi': Z) : lo <= lo' -> hi' <= hi -> xd_rng l lo hi -> xd_rng l lo' hi'.
Proof. intros H1 H2 H q Hq. apply H. lia. Qed.

Lemma xd_rng_app (l: list val) (a b d: Z) : xd_rng l a b -> xd_rng l b d -> xd_rng l a d.
Proof. intros H1 H2 q Hq. destruct (Z_lt_le_dec q b); [apply H1 | apply H2]; lia. Qed.

(* a sub-range of a defined range *)
Lemma xd_sub (l: list val) (a b a' b': Z) :
  0 <= a <= a' -> a' <= b' <= b -> b <= Zlength l ->
  Forall is_byte_val (sublist a b l) -> Forall is_byte_val (sublist a' b' l).
Proof.
  intros H1 H2 H3 H. replace (sublist a' b' l) with (sublist (a' - a) (b' - a) (sublist a b l)).
  - apply Forall_sublist; auto.
  - rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* LibcSpec.byte_val and DecIface.is_byte_val are the same predicate *)
Lemma xd_bv (l: list val) : Forall is_byte_val l -> Forall byte_val l.
Proof. intros H. exact H. Qed.

(* unchanged outside [lo, hi), defined inside *)
Lemma xd_ub_frame (c c': list val) (lo hi: Z) :
  (forall q, 0 <= q < Zlength c -> ~ (lo <= q < hi) -> Znth q c' = Znth q c) -> xd_rng c' lo hi -> xd_ub c c'.
Proof.
  intros Hf Hr q Hq. destruct (Z_lt_le_dec q lo); [left; apply Hf; lia|].
  destruct (Z_lt_le_dec q hi); [right; apply Hr; lia | left; apply Hf; lia].
Qed.

(* a forward copy of E cells from si to di reads only [si, min(di, si + E)) (source before destination: the
   cells from di on are written before they are read) or [si, si + E) (destination before source) *)
Lemma xd_listcopy (c: list val) (si di E: Z) :
  0 <= si -> 0 <= di -> si <> di -> 0 <= E -> di + E <= Zlength c -> si + E <= Zlength c ->
  xd_rng c si (if si <? di then Z.min di (si + E) else si + E) ->
  xd_rng (listcopy c si di (Z.to_nat E)) di (di + E).
Proof.
  intros Hs Hd Hne HE HdE HsE Hr q Hq. revert Hr.
  destruct (Z.ltb_spec si di) as [Hlt|Hge]; intros Hr.
  - rewrite lc_char by lia.
    replace (andb (di <=? q) (q <? di + E)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    apply Hr.
    pose proof (Z.mod_pos_bound (q - si) (di - si) ltac:(lia)).
    assert ((q - si) mod (di - si) < E).
    { destruct (Z_lt_le_dec (q - si) (2 * (di - si))).
      - assert (Ht: (q - si) mod (di - si) = q - si - (di - si)).
        { symmetry. apply (Z.mod_unique (q - si) (di - si) 1); [left; lia | lia]. }
        lia.
      - lia. }
    lia.
  - replace q with (di + (q - di)) by lia. rewrite listcopy_dbs by lia. apply Hr. lia.
Qed.

Lemma xd_ub_listcopy (c: list val) (si di E: Z) :
  0 <= si -> 0 <= di -> si <> di -> 0 <= E -> di + E <= Zlength c -> si + E <= Zlength c ->
  xd_rng c si (if si <? di then Z.min di (si + E) else si + E) ->
  xd_ub c (listcopy c si di (Z.to_nat E)).
Proof.
  intros. apply (xd_ub_frame c _ di (di + E)).
  - intros q Hq Hn. apply listcopy_outside; rewrite ?Z2Nat.id; lia.
  - apply xd_listcopy; auto.
Qed.

(* ZSTD_wildcopy in one array: the result is the forward copy of wc_ext bytes (at most n + 31) *)
Lemma xd_wc_within (c g: list val) (si di n: Z) (b: bool) :
  0 <= si -> 0 <= di -> si <> di -> 0 <= n -> di + n + WILDCOPY_OVERLENGTH <= Zlength c ->
  si + n + WILDCOPY_OVERLENGTH <= Zlength c -> copy_src_def c si di n ->
  g = sublist (di + n) (di + n + WILDCOPY_OVERLENGTH) (listcopy c si di (Z.to_nat (wc_ext b n))) ->
  xd_ub c (wc_within_post c si di n g) /\ xd_rng (wc_within_post c si di n g) di (di + n).
Proof.
  intros Hs Hd Hne Hn HdN HsN Hcd Hg. unfold WILDCOPY_OVERLENGTH in *.
  pose proof (wc_ext_bounds b n Hn) as HE.
  set (E := wc_ext b n) in *.
  assert (Hw: wc_within_post c si di n g = listcopy c si di (Z.to_nat E))
    by (rewrite Hg; apply wc_post_listcopy; lia).
  rewrite Hw.
  assert (Hr: xd_rng c si (if si <? di then Z.min di (si + E) else si + E)).
  { unfold copy_src_def, WILDCOPY_OVERLENGTH in Hcd.
    destruct (si <? di) eqn:Ed; apply xd_Forall_rng in Hcd; try lia;
      (eapply xd_rng_sub; [| | exact Hcd]); lia. }
  split.
  - apply xd_ub_listcopy; auto; lia.
  - apply (xd_rng_sub _ di (di + E)); try lia. apply xd_listcopy; auto; lia.
Qed.

(* ZSTD_wildcopy from a separate array: n source bytes, then the slack (source bytes up to wc_ext, the rest
   unchanged) *)
Lemma xd_wc_dj (cs cd g: list val) (n: Z) :
  0 <= n -> n + WILDCOPY_OVERLENGTH <= Zlength cs -> n + WILDCOPY_OVERLENGTH <= Zlength cd ->
  Forall is_byte_val (sublist 0 (n + WILDCOPY_OVERLENGTH) cs) ->
  g = sublist n (n + WILDCOPY_OVERLENGTH) (sublist 0 (wc_ext false n) cs ++ sublist (wc_ext false n) (Zlength cd) cd) ->
  xd_ub cd (sublist 0 n cs ++ g ++ sublist (n + WILDCOPY_OVERLENGTH) (Zlength cd) cd).
Proof.
  intros Hn Hs Hd Hb Hg. unfold WILDCOPY_OVERLENGTH in *.
  pose proof (wc_ext_bounds false n Hn) as HE.
  set (E := wc_ext false n) in *.
  apply xd_Forall_rng in Hb; [| lia | lia].
  subst g. intros q Hq.
  destruct (Z_lt_le_dec q E) as [L|L].
  - right. replace (Znth q (sublist 0 n cs ++ sublist n (n + 32) (sublist 0 E cs ++ sublist E (Zlength cd) cd) ++
                       sublist (n + 32) (Zlength cd) cd)) with (Znth q cs) by list_solve.
    apply Hb. lia.
  - left. list_solve.
Qed.

(* ZSTD_copy4/8/16 *)
Lemma xd_copied (cs cd: list val) (is id k: Z) :
  0 <= is -> is + k <= Zlength cs -> 0 <= id -> id + k <= Zlength cd -> 0 <= k ->
  Forall is_byte_val (sublist is (is + k) cs) ->
  xd_ub cd (copied cs cd is id k) /\ xd_rng (copied cs cd is id k) id (id + k).
Proof.
  intros H1 H2 H3 H4 H5 Hb. apply xd_Forall_rng in Hb; [| lia | lia].
  assert (Hr: xd_rng (copied cs cd is id k) id (id + k)).
  { intros q Hq. replace (Znth q (copied cs cd is id k)) with (Znth (is + (q - id)) cs)
      by (unfold copied; list_solve).
    apply Hb. lia. }
  split; [| exact Hr].
  apply (xd_ub_frame cd _ id (id + k)); [| exact Hr].
  intros q Hq Hn. unfold copied. list_solve.
Qed.

(* defined bytes put at i *)
Lemma xd_put (c bs: list val) (i: Z) :
  0 <= i -> i + Zlength bs <= Zlength c -> Forall is_byte_val bs ->
  xd_ub c (put c i bs) /\ xd_rng (put c i bs) i (i + Zlength bs).
Proof.
  intros H1 H2 Hb.
  assert (Hr: xd_rng (put c i bs) i (i + Zlength bs)).
  { intros q Hq. rewrite ecl_Znth_put_in by lia. rewrite Forall_forall in Hb. apply Hb, Znth_In. lia. }
  split; [| exact Hr].
  apply (xd_ub_frame c _ i (i + Zlength bs)); [| exact Hr].
  intros q Hq Hn. rewrite ecl_Znth_put_out by lia. reflexivity.
Qed.

(* the in-array memmove of n bytes from si to di *)
Lemma xd_mm_put (c: list val) (si di n: Z) :
  0 <= si -> 0 <= n -> si + n <= Zlength c ->
  mm_result c (Zlength c) si di n = put c di (sublist si (si + n) c).
Proof. intros. unfold mm_result, put. rewrite Zlength_sublist by lia. f_equal. f_equal. f_equal. lia. Qed.

(* the destination pieces of the literal copies, joined back *)
Lemma xd_ub_join_r (c d': list val) (m: Z) :
  0 <= m <= Zlength c -> Zlength d' = Zlength c - m -> xd_ub (sublist m (Zlength c) c) d' ->
  xd_ub c (sublist 0 m c ++ d').
Proof.
  intros Hm Hd H q Hq. destruct (Z_lt_le_dec q m) as [L|L].
  - left. list_solve.
  - rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
    destruct (H (q - (m - 0)) ltac:(rewrite Zlength_sublist; lia)) as [E|E]; [left | right; exact E].
    rewrite E. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

Lemma xd_ub_join_r' (c d': list val) (N m: Z) :
  Zlength c = N -> 0 <= m <= N -> Zlength d' = N - m -> xd_ub (sublist m N c) d' -> xd_ub c (sublist 0 m c ++ d').
Proof. intros <-. apply xd_ub_join_r. Qed.

Lemma xd_ub_join_l (c a': list val) (m: Z) :
  0 <= m <= Zlength c -> Zlength a' = m -> xd_ub (sublist 0 m c) a' ->
  xd_ub c (a' ++ sublist m (Zlength c) c).
Proof.
  intros Hm Ha H q Hq. destruct (Z_lt_le_dec q m) as [L|L].
  - rewrite Znth_app1 by lia.
    destruct (H q ltac:(rewrite Zlength_sublist; lia)) as [E|E]; [left | right; exact E].
    rewrite E. rewrite Znth_sublist by lia. f_equal. lia.
  - left. rewrite Znth_app2 by lia. rewrite Znth_sublist by lia. f_equal. lia.
Qed.

(* after the literal copy: the history and the literals are defined *)
Lemma xd_after_lit (c cA Lv: list val) (k ps ll: Z) :
  0 <= ps <= k -> Zlength Lv = ll -> 0 <= ll -> k + ll <= Zlength c -> Zlength cA = Zlength c ->
  xd_rng c ps k -> Forall is_byte_val Lv ->
  (forall p, ps <= p < k + ll -> Znth p cA = Znth p (put c k Lv)) ->
  xd_rng cA ps (k + ll).
Proof.
  intros Hps HL Hll Hk HA Hh Hb Heq q Hq. rewrite Heq by lia.
  destruct (Z_lt_le_dec q k).
  - rewrite ecl_Znth_put_out by lia. apply Hh. lia.
  - rewrite ecl_Znth_put_in by lia. rewrite Forall_forall in Hb. apply Hb, Znth_In. lia.
Qed.

(* the extDict's bytes, read from the array as it is now *)
Lemma xd_ext_in (c cA: list val) (e1 elen a b: Z) :
  Zlength cA = Zlength c -> xd_ub c cA -> Forall is_byte_val (sublist (e1 - elen) e1 c) ->
  0 <= e1 - elen <= a -> a <= b <= e1 -> e1 <= Zlength c ->
  Forall is_byte_val (sublist a b cA).
Proof.
  intros HA Hu Hd H1 H2 H3. apply xd_rng_Forall; [lia | lia |].
  apply (xd_rng_sub _ (e1 - elen) e1); try lia.
  apply (xd_rng_ub c); try lia; auto. apply xd_Forall_rng; auto; lia.
Qed.

(* the error code is not a success *)
Lemma xd_nf (r: Z) (P: Prop) : is_error_code r = true -> is_error_code r = false -> P.
Proof. congruence. Qed.

(* the cells a forward copy reads, inside a defined range below the destination *)
Lemma xd_csd (c: list val) (lo si di n: Z) :
  0 <= lo <= si -> si < di -> di <= Zlength c -> 0 <= n -> xd_rng c lo di -> copy_src_def c si di n.
Proof.
  intros H1 H2 H3 H4 Hr. unfold copy_src_def, WILDCOPY_OVERLENGTH. rewrite (proj2 (Z.ltb_lt si di)) by lia.
  apply xd_rng_Forall; [lia | lia |]. apply (xd_rng_sub _ lo di); auto; lia.
Qed.

(* equal ranges are defined together *)
Lemma xd_rng_eq (l1 l2: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l1 -> b <= Zlength l2 -> sublist a b l1 = sublist a b l2 -> xd_rng l2 a b -> xd_rng l1 a b.
Proof.
  intros H1 H2 H3 E Hr q Hq.
  assert (Eq: Znth (q - a) (sublist a b l1) = Znth (q - a) (sublist a b l2)) by (rewrite E; reflexivity).
  rewrite !Znth_sublist in Eq by lia. replace (q - a + a) with q in Eq by lia. rewrite Eq. apply Hr. lia.
Qed.

(* the destination, split around [i, i + n) and joined with n new cells, is a put *)
Lemma xd_put_eq (c v: list val) (i n: Z) :
  Zlength v = n -> sublist 0 i c ++ v ++ sublist (i + n) (Zlength c) c = put c i v.
Proof. intros <-. reflexivity. Qed.

(* the success post's definedness from the defined range [k, k + r) *)
Lemma xd_post_F (c': list val) (k r: Z) :
  0 <= k -> 0 <= r -> k + r <= Zlength c' -> xd_rng c' k (k + r) -> Forall is_byte_val (sublist k (k + r) c').
Proof. intros. apply xd_rng_Forall; auto; lia. Qed.

(* the in-array memmove of defined bytes *)
Lemma xd_mm (c: list val) (N si di n: Z) :
  Zlength c = N -> 0 <= si -> 0 <= n -> si + n <= N -> 0 <= di -> di + n <= N ->
  Forall is_byte_val (sublist si (si + n) c) ->
  xd_ub c (mm_result c N si di n) /\ xd_rng (mm_result c N si di n) di (di + n).
Proof.
  intros <- H1 H2 H3 H4 H5 Hb. rewrite xd_mm_put by lia.
  destruct (xd_put c (sublist si (si + n) c) di) as [A B]; [lia | rewrite Zlength_sublist; lia | exact Hb |].
  rewrite Zlength_sublist in B by lia. replace (di + (si + n - si)) with (di + n) in B by lia. auto.
Qed.

(* the memmove from a separate array, as the three pieces of the destination *)
Lemma xd_put3 (c v: list val) (N i n: Z) :
  Zlength c = N -> 0 <= i -> i + n <= N -> Zlength v = n -> Forall is_byte_val v ->
  xd_ub c (sublist 0 i c ++ v ++ sublist (i + n) N c) /\ xd_rng (sublist 0 i c ++ v ++ sublist (i + n) N c) i (i + n).
Proof. intros <- H1 H2 <- Hb. rewrite xd_put_eq by reflexivity. apply xd_put; auto. Qed.

(* the final array: unchanged or defined everywhere, defined on [k, b) (the history and the first copies
   [ps, a) carried through the last copy, which defines [a, b)) *)
Lemma xd_fin (c cA c': list val) (k ps a b: Z) :
  0 <= ps <= k -> k <= a <= b -> b <= Zlength c -> Zlength cA = Zlength c ->
  xd_ub c cA -> xd_ub cA c' -> xd_rng cA ps a -> xd_rng c' a b ->
  (forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c')) /\
  (Zlength c' = Zlength c -> Forall is_byte_val (sublist k b c')).
Proof.
  intros Hps Hab Hb HA Hu1 Hu2 Hr1 Hr2. split; [apply (xd_ub_trans c cA c'); auto |].
  intros Hc'. apply xd_rng_Forall; [lia | lia |]. apply (xd_rng_app _ _ a); auto.
  apply (xd_rng_ub cA); try lia; auto. apply (xd_rng_sub _ ps a); auto; lia.
Qed.

(* ---------- ZSTD_execSequenceEnd ---------- *)
Lemma xe_add_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a + n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_int64. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite ptrofs_add_repr. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|].
  unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus.
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

(* for (;;break) { c } rest (RETURN_ERROR_IF, DEBUGLOG): c, then rest from Q *)
Lemma xe_loop_seq {Espec: OracleKind} {cs: compspecs} Delta (P Q: environ -> mpred) c rest R :
  semax Delta P c (loop1_ret_assert Q (overridePost Q R)) -> semax Delta Q rest R ->
  semax Delta P (Ssequence (Sloop c Sbreak) rest) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [|exact H2].
  apply semax_loop with Q; [exact H1|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

(* for (;;break) {} : a no-op *)
Lemma xe_skipbreak_seq {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H. apply xe_loop_seq with P; [|exact H].
  eapply semax_post; [| | | | apply semax_skip].
  all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
  - intros rho; simpl; apply andp_left2, derives_refl.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

(* (ptr_a - ptr_b) cast to size_t, compared with a size_t n by > (RETURN_ERROR_IF) *)
Lemma xe_gt_diff (p: val) (a b n: Z) : isptr p -> 0 <= a - b <= Int64.max_unsigned -> 0 <= n <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1))) sem_cast_pointer sem_cast_pointer
      (Vlong (Int64.repr n)) (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) with
  | Some v' => v' | None => Vundef end = Vint (if zlt (a - b) n then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. rewrite cp_sub_pp by auto. simpl. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia. destruct (zlt (a - b) n); reflexivity.
Qed.

(* the statements before RETURN_ERROR_IF's return: for(;;break){} ; for(;;break){if (0) ...} ; twice for(;;break){} *)
Ltac xe_if0_loop :=
  match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P); [forward_if; [exfalso; auto | forward; apply ENTAIL_refl] | ] end.
Ltac xe_err_prefix := apply xe_skipbreak_seq; xe_if0_loop; apply xe_skipbreak_seq; apply xe_skipbreak_seq.

(* the PROP part of an error return (-n cast to size_t) *)
Lemma xe_err_ret (n: Z) (b: bool) (P: Prop) : 0 < n < 120 -> b = true ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = false -> P) /\ Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn ->. unfold err_code, is_error_code.
  split; [rep_lia|]. split; [apply Z.ltb_lt; lia|]. split; [intros E; apply Z.ltb_ge in E; lia|].
  f_equal. apply cp_repr_eqm. replace (2 ^ 64 - n) with (- n + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma xe_fa (N: Z) (p: val) (i: Z) :
  field_compatible (tarray tuchar N) [] p -> 0 <= i < N ->
  field_address (tarray tuchar N) (SUB i) p = offset_val i p.
Proof.
  intros Hfc Hi. rewrite arr_field_address by (auto; lia). simpl sizeof. rewrite Z.mul_1_l. reflexivity.
Qed.

(* after the literal copy: the literals at [k, k + ll), nothing written outside [k, min(k + ll + 32, max(k + ll, e))) *)
Definition xe_litc (c cA: list val) (k e ll: Z) (Lv: list val) : Prop :=
  Zlength cA = Zlength c /\ sublist k (k + ll) cA = Lv /\
  forall p, 0 <= p < Zlength c -> ~ (k <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) e)) ->
    Znth p cA = Znth p c.

Lemma xe_litc_intro (c cA: list val) (k e ll: Z) (Lv: list val) :
  Zlength cA = Zlength c -> sublist k (k + ll) cA = Lv ->
  (forall p, 0 <= p < Zlength c ->
     ~ (k <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) (e - 32 + WILDCOPY_OVERLENGTH))) ->
     Znth p cA = Znth p c) ->
  xe_litc c cA k e ll Lv.
Proof.
  unfold xe_litc, WILDCOPY_OVERLENGTH. intros H1 H2 H3. split; [auto | split; [auto |]].
  intros p Hp Hn. apply H3; auto. replace (e - 32 + 32) with e by lia. auto.
Qed.

Lemma xe_lc_dbs (c: list val) (li k ll: Z) :
  0 <= k <= li -> 0 <= ll -> li + ll <= Zlength c ->
  sublist k (k + ll) (listcopy c li k (Z.to_nat ll)) = sublist li (li + ll) c.
Proof.
  intros. assert (HL: Zlength (listcopy c li k (Z.to_nat ll)) = Zlength c) by (apply Zlength_listcopy; lia).
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia |].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia.
  replace (i + k) with (k + i) by lia. rewrite listcopy_dbs by lia. f_equal; lia.
Qed.

(* the array after the literal copy agrees with put c k Lv outside the slack [k + ll, W) *)
Lemma xe_cA_put (c cA Lv: list val) (k ll e: Z) :
  Zlength Lv = ll -> 0 <= k -> 0 <= ll -> k + ll <= e <= Zlength c -> Zlength cA = Zlength c ->
  sublist k (k + ll) cA = Lv ->
  (forall p, 0 <= p < Zlength c -> ~ (k <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) e)) ->
     Znth p cA = Znth p c) ->
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) e)) ->
    Znth p cA = Znth p (put c k Lv).
Proof.
  intros HL Hk Hll He HcA Hs Ho p Hp Hn.
  destruct (Z_lt_le_dec p k) as [Hlt|Hge].
  - rewrite ecl_Znth_put_out by lia. apply Ho; lia.
  - destruct (Z_lt_le_dec p (k + ll)) as [Hlt2|Hge2].
    + rewrite ecl_Znth_put_in by lia. rewrite <- Hs. rewrite Znth_sublist by lia. f_equal; lia.
    + rewrite ecl_Znth_put_out by lia. apply Ho; lia.
Qed.

(* the PROP part of a successful return *)
Lemma xe_ok_post (c c': list val) (k e li lim ll ml off ps: Z) (Lvs: list val) (x: ext_seg) (lp: val) :
  0 <= ps <= k -> 0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> k + ll + ml <= e -> e <= Zlength c ->
  ll <= lim - li -> 1 <= off <= k + ll - ps + ext_len x -> exec_ext_ok x c -> Zlength Lvs = ll ->
  unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok x k e ll ml off ps ->
     sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lvs ml off ps x)) ->
  is_error_code (ll + ml) = exec_err k e li lim ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false -> ll + ml = ll + ml /\ lp = lp /\
    unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) /\
    (ext_read_ok x k e ll ml off ps ->
      sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lvs ml off ps x) /\
      (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val Lvs -> ext_def x c ->
       Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros Hps Hll Hml Hke He Hli Hoff Hx HL Hu Hex.
  assert (E: is_error_code (ll + ml) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  rewrite E. split.
  { unfold exec_err. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge (lim - li) ll)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity. }
  split; [discriminate|]. intros _. split; [auto | split; [auto | split; [auto |]]].
  intros Hr. split; [auto|]. intros B1 B2 B3. rewrite (Hex Hr).
  replace (k + (ll + ml)) with (k + Zlength Lvs + ml) by lia.
  apply exec_c_bytes; auto; lia.
Qed.

(* the match in the prefix: one forward copy behind x = k + ll *)
Lemma xe_prefix_case (c cA c' Lv: list val) (k e ll ml off ps: Z) (x: ext_seg) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml <= e <= Zlength c ->
  1 <= off <= k + ll - ps ->
  Zlength cA = Zlength c -> sublist k (k + ll) cA = Lv ->
  (forall p, 0 <= p < Zlength c -> ~ (k <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) e)) ->
     Znth p cA = Znth p c) ->
  Zlength c' = Zlength cA ->
  sublist (k + ll) (k + ll + ml) c' = sublist (k + ll) (k + ll + ml) (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml)) ->
  (forall p, 0 <= p < Zlength cA ->
     ~ (k + ll <= p < Z.min (k + ll + ml + WILDCOPY_OVERLENGTH) (Z.max (k + ll + ml) (e - 32 + WILDCOPY_OVERLENGTH))) ->
     Znth p c' = Znth p cA) ->
  unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) /\
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x).
Proof.
  unfold WILDCOPY_OVERLENGTH. intros HL Hps Hll Hml He Hoff HcA Hs Ho Hc' Hx Ho'.
  split.
  - intros p Hp Hn. rewrite Ho' by lia. apply Ho; lia.
  - replace (k + (ll + ml)) with (k + ll + ml) by lia.
    apply (exec_glue_prefix c cA c' k ps ml off (k + ll) Lv x); try lia.
    + intros p Hp. apply (xe_cA_put c cA Lv k ll e); unfold WILDCOPY_OVERLENGTH; auto; lia.
    + intros p Hp. apply Ho'; lia.
    + exact Hx.
Qed.

Lemma xe_sub_pi {cs: compspecs} (p: val) (a k: Z) : isptr p -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val a p) (Vint (Int.repr k))) =
  offset_val (a - k) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_sub_repr. f_equal. lia.
Qed.

Lemma xe_sub_pl_g {cs: compspecs} (p: val) (a n: Z) (sg: signedness) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (Tlong sg noattr) (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof.
  intros Hp. destruct p; try contradiction. destruct sg; simpl; f_equal.
  all: unfold Ptrofs.of_int64. all: rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  all: rewrite <- (Ptrofs.repr_unsigned i). all: rewrite ptrofs_add_repr, ptrofs_add_repr, Ptrofs.sub_add_opp.
  all: unfold Ptrofs.neg. all: rewrite ptrofs_add_repr.
  all: apply Ptrofs.eqm_samerepr. all: replace (Ptrofs.unsigned i + (a - n)) with (Ptrofs.unsigned i + a + - n) by lia.
  all: apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|]. all: apply Ptrofs.eqm_neg.
  all: eapply Ptrofs.eqm_trans; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
  all: unfold Ptrofs.eqm; change Ptrofs.modulus with Int64.modulus; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

(* the same with the error clause unchanged_outside /\ dec_err (RETURN_ERROR constants are never 80, 82) *)
Lemma xe_err_ret2 (n: Z) (b: bool) (U P Q: Prop) : 0 < n < 120 -> n <> 80 -> n <> 82 -> b = true -> U ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = true -> U /\ dec_err (err_code n)) /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn H80 H82 Hb HU. destruct (xe_err_ret n b P Hn Hb) as (A & B & C & D).
  split; [auto | split; [auto | split; [| split; [auto | split; [intros E; congruence | auto]]]]].
  intros _. split; [auto|].
  unfold dec_err, is_error_code, err_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

(* (ptr_a - ptr_b) >= (long) n *)
Lemma xe_ge_diff (p: val) (a b n: Z) : isptr p -> Int64.min_signed <= a - b <= Int64.max_signed ->
  0 <= n <= Int64.max_signed ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n1 n2)))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vlong (Int64.repr n)) with
  | Some v' => v' | None => Vundef end = Vint (if zle n (a - b) then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. rewrite cp_sub_pp by auto. simpl. unfold Int64.lt.
  rewrite (Int64.signed_repr (a - b)), (Int64.signed_repr n) by rep_lia. destruct (zlt (a - b) n), (zle n (a - b)); try lia; reflexivity.
Qed.

(* the extDict memmove of n bytes from [e1 - dl, e1 - dl + n) of the extDict's array to [x0, x0 + n) *)
Definition xe_mm (cA c2: list val) (x: ext_seg) (x0 dl n: Z) : Prop :=
  Zlength c2 = Zlength cA /\
  sublist x0 (x0 + n) c2 = sublist (ext_end x - dl) (ext_end x - dl + n) (ext_src cA x) /\
  forall p, 0 <= p < Zlength cA -> ~ (x0 <= p < x0 + n) -> Znth p c2 = Znth p cA.

Lemma xe_mm_within (cA: list val) (N e1 elen dl x0 n: Z) :
  Zlength cA = N -> 0 <= e1 - dl -> e1 - dl + n <= N -> 0 <= x0 -> x0 + n <= N -> 0 <= n ->
  xe_mm cA (mm_result cA N (e1 - dl) x0 n) (ExtIn e1 elen) x0 dl n.
Proof.
  intros. unfold xe_mm, mm_result; simpl ext_end; simpl ext_src.
  split; [list_solve | split; [list_solve |]]. intros p Hp Hn. list_solve.
Qed.

Lemma xe_mm_sep (cA ec: list val) (shx: share) (eb: val) (N en e1 elen dl x0 n: Z) :
  Zlength cA = N -> Zlength ec = en -> 0 <= e1 - dl -> e1 - dl + n <= en -> 0 <= x0 -> x0 + n <= N -> 0 <= n ->
  xe_mm cA (sublist 0 x0 cA ++ sublist (e1 - dl) (e1 - dl + n) ec ++ sublist (x0 + n) N cA)
    (ExtSep shx eb en ec e1 elen) x0 dl n.
Proof.
  intros. unfold xe_mm; simpl ext_end; simpl ext_src.
  split; [list_solve | split; [list_solve |]]. intros p Hp Hn. list_solve.
Qed.

(* the match starts in the extDict: l1 = min(ml, dl) bytes by memmove (c2), then (l1 < ml) the forward copy
   from ps (c') *)
Lemma xe_ext_case (c cA c2 c' Lv: list val) (k e ll ml off ps: Z) (x: ext_seg) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml <= e <= Zlength c ->
  k + ll - ps < off <= k + ll - ps + ext_len x -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> sublist k (k + ll) cA = Lv ->
  (forall p, 0 <= p < Zlength c -> ~ (k <= p < Z.min (k + ll + WILDCOPY_OVERLENGTH) (Z.max (k + ll) e)) ->
     Znth p cA = Znth p c) ->
  xe_mm cA c2 x (k + ll) (off - (k + ll - ps)) (Z.min ml (off - (k + ll - ps))) ->
  Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c ->
     ~ (k + ll + Z.min ml (off - (k + ll - ps)) <= p < Z.min (k + ll + ml + WILDCOPY_OVERLENGTH) e) ->
     Znth p c' = Znth p c2) ->
  (Z.min ml (off - (k + ll - ps)) < ml ->
     sublist (k + ll + Z.min ml (off - (k + ll - ps))) (k + ll + ml) c' =
     sublist (k + ll + Z.min ml (off - (k + ll - ps))) (k + ll + ml)
       (listcopy c2 ps (k + ll + Z.min ml (off - (k + ll - ps))) (Z.to_nat (ml - Z.min ml (off - (k + ll - ps)))))) ->
  unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) /\
  (ext_read_ok x k e ll ml off ps ->
     sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x)).
Proof.
  unfold WILDCOPY_OVERLENGTH. intros HL Hps Hll Hml He Hoff Hx HcA Hs Ho [Hc2 [Hm Hc2o]] Hc' Ho' Hcp.
  set (dl := off - (k + ll - ps)) in *. set (l1 := Z.min ml dl) in *.
  assert (Hl1: 0 < l1 <= ml /\ l1 <= dl) by (unfold l1, dl in *; lia).
  pose proof (proj1 Hx) as Hel.
  split.
  - intros p Hp Hn. rewrite Ho' by lia. rewrite Hc2o by lia. apply Ho; lia.
  - intros Hr. replace (k + (ll + ml)) with (k + ll + ml) by lia.
    assert (HP: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < Z.min (k + ll + 32) (Z.max (k + ll) e)) ->
                Znth p cA = Znth p (put c k Lv))
      by (apply (xe_cA_put c cA Lv k ll e); unfold WILDCOPY_OVERLENGTH; auto; lia).
    apply (exec_glue_ext c cA c2 c' k ps ml off (k + ll) dl l1 Lv x); auto; try lia.
    + intros p Hp. apply HP; lia.
    + apply (exec_ext_read c cA k e ll ml off ps (Z.min (k + ll + 32) (Z.max (k + ll) e)) dl Lv x); auto; try lia.
      unfold WILDCOPY_OVERLENGTH. lia.
    + intros p Hp. rewrite Hc2o by lia. reflexivity.
    + intros p Hp. apply Ho'; lia.
Qed.

Lemma xe_sub_pp {cs: compspecs} (p: val) (a b: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p)) =
  Vlong (Int64.repr (a - b)).
Proof. intros Hp. rewrite <- (cp_sub_pp p a b Hp). destruct p; try contradiction; reflexivity. Qed.

(* the array holding the extDict *)
Definition xe_xb (x: ext_seg) (ob: val) : val := match x with ExtSep _ eb _ _ _ _ => eb | _ => ob end.

Lemma xe_dict_end (x: ext_seg) (ob dE: val) :
  x <> ExtNone -> dict_end x ob dE = offset_val (ext_end x) (xe_xb x ob).
Proof. destruct x; simpl; auto; congruence. Qed.

(* one piece [a, a + n) of a byte array, held separately *)
Lemma xe_mid (sh: share) (p: val) (l: list val) (N a n: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p -> 0 <= a -> 0 <= n -> a + n <= N ->
  data_at sh (tarray tuchar N) l p =
  data_at sh (tarray tuchar n) (sublist a (a + n) l) (offset_val a p) *
  (data_at sh (tarray tuchar a) (sublist 0 a l) p *
   data_at sh (tarray tuchar (N - (a + n))) (sublist (a + n) N l) (offset_val (a + n) p)).
Proof.
  intros HN Hfc Ha Hn Han. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh N a (a + n) l p) by lia.
  change (Tarray tuchar N noattr) with (tarray tuchar N).
  rewrite !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
  replace (a + n - a) with n by lia.
  apply pred_ext; cancel.
Qed.

Lemma xe_mid_join (sh: share) (p: val) (l bs: list val) (N a n: Z) :
  Zlength l = N -> field_compatible (tarray tuchar N) [] p -> 0 <= a -> 0 <= n -> a + n <= N -> Zlength bs = n ->
  data_at sh (tarray tuchar n) bs (offset_val a p) *
  (data_at sh (tarray tuchar a) (sublist 0 a l) p *
   data_at sh (tarray tuchar (N - (a + n))) (sublist (a + n) N l) (offset_val (a + n) p)) =
  data_at sh (tarray tuchar N) (sublist 0 a l ++ bs ++ sublist (a + n) N l) p.
Proof.
  intros HN Hfc Ha Hn Han Hbs.
  rewrite (xe_mid sh p (sublist 0 a l ++ bs ++ sublist (a + n) N l) N a n) by (auto; list_solve).
  f_equal; [f_equal; list_solve | f_equal; f_equal; list_solve].
Qed.

Lemma xe_sub_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof. apply xe_sub_pl_g. Qed.

Lemma xe_sub_pl_l {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tlong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof. apply xe_sub_pl_g. Qed.

(* bytes in, bytes out: the byte_cells clause of exec_spec *)
Lemma xeb_sub (l: list val) (a b: Z) : byte_cells l -> byte_cells (sublist a b l).
Proof. apply Forall_sublist. Qed.

Lemma xeb_lit_sep (c cl cA: list val) (li: Z) (X: Prop) :
  (byte_cells c /\ byte_cells (sublist li (Zlength cl) cl) -> byte_cells cA) ->
  byte_cells c -> byte_cells cl -> X -> byte_cells cA.
Proof. intros H Hc Hl _. apply H. split; [auto | apply xeb_sub; auto]. Qed.

Lemma xeb_lit_in (c cA: list val) (X: Prop) :
  (byte_cells c -> byte_cells cA) -> byte_cells c -> byte_cells c -> X -> byte_cells cA.
Proof. auto. Qed.

Lemma xeb_app3 (a b d: list val) : byte_cells a -> byte_cells b -> byte_cells d -> byte_cells (a ++ b ++ d).
Proof. intros. unfold byte_cells in *. rewrite !Forall_app. auto. Qed.

Lemma xeb_mm_within (cA: list val) (N si di n: Z) (X: Prop) : byte_cells cA -> X -> byte_cells (mm_result cA N si di n).
Proof. intros. unfold mm_result. apply xeb_app3; apply xeb_sub; auto. Qed.

Lemma xeb_mm_sep (cA ec: list val) (a b d f g h: Z) : byte_cells cA -> byte_cells ec ->
  byte_cells (sublist a b cA ++ sublist d f ec ++ sublist g h cA).
Proof. intros. apply xeb_app3; apply xeb_sub; auto. Qed.

(* ---------- exact glue: the callees' results as BlkSeqXMem's mirrors ----------
   The callees' exact posts (memmove: mm_result; ZSTD_copy16: copied, on two separately held pieces;
   ZSTD_wildcopy on two separate arrays: a piece of the destination; ZSTD_safecopy from a separate array:
   lsafecopy from the start of the piece after litPtr) put together as the mirrors on the whole output
   array; the branches of lexec / lexec_split / lmatch as the C takes them. *)

(* stores of read values at d: a put *)
Lemma xg_lwrn_put (vs c: list val) (d: Z) :
  0 <= d -> d + Zlength vs <= Zlength c -> lwrn vs c d = put c d vs.
Proof.
  revert c d. induction vs as [|v vs IH]; intros c d Hd Hl; simpl.
  - unfold put. simpl. list_solve.
  - rewrite Zlength_cons in Hl. rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    unfold put. rewrite Zlength_cons. list_solve.
Qed.

Lemma xg_lrdn_LS (k: nat) (c cs: list val) (i: Z) :
  0 <= i -> i + Z.of_nat k <= Zlength cs -> lrdn k c (LS cs) i = sublist i (i + Z.of_nat k) cs.
Proof.
  revert i. induction k as [|k IH]; intros i Hi Hl; simpl.
  - rewrite sublist_nil_gen by lia. reflexivity.
  - rewrite IH by lia. rewrite (sublist_split i (i + 1) (i + Z.pos (Pos.of_succ_nat k))) by lia.
    rewrite sublist_len_1 by lia. simpl. f_equal. f_equal. lia.
Qed.

Lemma xg_lrdn_LW (k: nat) (c: list val) (i: Z) :
  0 <= i -> i + Z.of_nat k <= Zlength c -> lrdn k c LW i = sublist i (i + Z.of_nat k) c.
Proof.
  revert i. induction k as [|k IH]; intros i Hi Hl; simpl.
  - rewrite sublist_nil_gen by lia. reflexivity.
  - rewrite IH by lia. rewrite (sublist_split i (i + 1) (i + Z.pos (Pos.of_succ_nat k))) by lia.
    rewrite sublist_len_1 by lia. simpl. f_equal. f_equal. lia.
Qed.

Lemma xg_lmove_LS (k: nat) (c cs: list val) (d i: Z) :
  0 <= d -> d + Z.of_nat k <= Zlength c -> 0 <= i -> i + Z.of_nat k <= Zlength cs ->
  lmove k c d (LS cs) i = put c d (sublist i (i + Z.of_nat k) cs).
Proof.
  intros. unfold lmove. rewrite xg_lrdn_LS by lia. apply xg_lwrn_put; [lia | rewrite Zlength_sublist; lia].
Qed.

Lemma xg_lmove_LW (k: nat) (c: list val) (d i: Z) :
  0 <= d -> d + Z.of_nat k <= Zlength c -> 0 <= i -> i + Z.of_nat k <= Zlength c ->
  lmove k c d LW i = put c d (sublist i (i + Z.of_nat k) c).
Proof.
  intros. unfold lmove. rewrite xg_lrdn_LW by lia. apply xg_lwrn_put; [lia | rewrite Zlength_sublist; lia].
Qed.

(* memmove within the array *)
Lemma xg_mm (c: list val) (si di n: Z) :
  0 <= n -> 0 <= si -> si + n <= Zlength c -> 0 <= di -> di + n <= Zlength c ->
  mm_result c (Zlength c) si di n = lmove (Z.to_nat n) c di LW si.
Proof.
  intros. rewrite xg_lmove_LW by lia. rewrite Z2Nat.id by lia. unfold mm_result, put. list_solve.
Qed.

(* ZSTD_copy16 from a separate array *)
Lemma xg_copied (cs cd: list val) (is id: Z) :
  0 <= is -> is + 16 <= Zlength cs -> 0 <= id -> id + 16 <= Zlength cd ->
  copied cs cd is id 16 = lmove 16 cd id (LS cs) is.
Proof.
  intros. rewrite xg_lmove_LS by (simpl; lia). unfold copied, put. simpl. list_solve.
Qed.

(* ZSTD_copy16 from a later piece of the same array *)
Lemma xg_copied_in (c: list val) (k li: Z) :
  0 <= k -> k + 16 <= li -> li + 16 <= Zlength c ->
  copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c = lmove 16 c k LW li.
Proof.
  intros. rewrite xg_lmove_LW by (simpl; lia). unfold copied, put. simpl. list_solve.
Qed.

(* chunks of 16 from a separate array / from a part of the array they do not write *)
Lemma xg_chunks_LS (k: nat) (c cs: list val) (d i: Z) :
  0 <= d -> d + Z.mul 16 (Z.of_nat k) <= Zlength c -> 0 <= i -> i + Z.mul 16 (Z.of_nat k) <= Zlength cs ->
  lchunks16 k c d (LS cs) i = put c d (sublist i (i + Z.mul 16 (Z.of_nat k)) cs).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hd Hc Hi Hs; simpl lchunks16.
  - unfold put. simpl. list_solve.
  - rewrite Nat2Z.inj_succ in *. rewrite xg_lmove_LS by (simpl; lia).
    assert (Hp: Zlength (put c d (sublist i (i + Z.of_nat 16) cs)) = Zlength c)
      by (unfold put; simpl; list_solve).
    rewrite IH by (rewrite ?Hp; lia). unfold put. simpl. list_solve.
Qed.

Lemma xg_chunks_LW (k: nat) (c: list val) (d i: Z) :
  0 <= d -> d + Z.mul 16 (Z.of_nat k) <= Zlength c -> 0 <= i -> i + Z.mul 16 (Z.of_nat k) <= Zlength c ->
  (d + Z.mul 16 (Z.of_nat k) <= i \/ i + Z.mul 16 (Z.of_nat k) <= d) ->
  lchunks16 k c d LW i = put c d (sublist i (i + Z.mul 16 (Z.of_nat k)) c).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Hd Hc Hi Hs Hdj; simpl lchunks16.
  - unfold put. simpl. list_solve.
  - rewrite Nat2Z.inj_succ in *. rewrite xg_lmove_LW by (simpl; lia).
    assert (Hp: Zlength (put c d (sublist i (i + Z.of_nat 16) c)) = Zlength c)
      by (unfold put; simpl; list_solve).
    rewrite IH by (rewrite ?Hp; lia). unfold put. simpl. list_solve.
Qed.

(* the number of bytes a no-overlap wild copy moves *)
Lemma xg_wc_ext (n: Z) : 0 <= n ->
  Z.mul 16 (Z.of_nat (Z.to_nat (if n <=? 16 then 1 else 1 + Z.mul 2 ((n - 16 + 31) / 32)))) = wc_ext false n /\
  n <= wc_ext false n <= n + 31.
Proof.
  intros Hn. unfold wc_ext, WILDCOPY_VECLEN.
  destruct (n <=? 16) eqn:E; [apply Z.leb_le in E | apply Z.leb_gt in E].
  - simpl. lia.
  - assert (0 <= (n - 16 + 31) / 32) by (apply Z.div_pos; lia).
    rewrite Z2Nat.id by lia.
    pose proof (Z.div_mod (n - 16 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (n - 16 + 31) 32 ltac:(lia)).
    lia.
Qed.

Lemma xg_wild_LS (c cs: list val) (d i n: Z) :
  0 <= n -> 0 <= d -> d + wc_ext false n <= Zlength c -> 0 <= i -> i + wc_ext false n <= Zlength cs ->
  lwild c d (LS cs) i n false = put c d (sublist i (i + wc_ext false n) cs).
Proof.
  intros. destruct (xg_wc_ext n) as [E _]; auto.
  unfold lwild. simpl andb. cbv iota. rewrite xg_chunks_LS by lia. rewrite E. reflexivity.
Qed.

Lemma xg_wild_LW (c: list val) (d i n: Z) :
  0 <= n -> 0 <= d -> d + wc_ext false n <= Zlength c -> 0 <= i -> i + wc_ext false n <= Zlength c ->
  (d + wc_ext false n <= i \/ i + wc_ext false n <= d) ->
  lwild c d LW i n false = put c d (sublist i (i + wc_ext false n) c).
Proof.
  intros. destruct (xg_wc_ext n) as [E _]; auto.
  unfold lwild. simpl andb. cbv iota. rewrite xg_chunks_LW by lia. rewrite E. reflexivity.
Qed.

(* ZSTD_wildcopy on two separate arrays: its post-state of the destination piece *)
Lemma xg_wild_dj (cs cd g: list val) (n: Z) :
  0 <= n -> n + WILDCOPY_OVERLENGTH <= Zlength cs -> n + WILDCOPY_OVERLENGTH <= Zlength cd ->
  sublist 0 n cs ++ g ++ sublist (n + WILDCOPY_OVERLENGTH) (Zlength cd) cd = lwild cd 0 (LS cs) 0 n false ->
  sublist 0 n cs ++ g ++ sublist (n + WILDCOPY_OVERLENGTH) (Zlength cd) cd = put cd 0 (sublist 0 (wc_ext false n) cs).
Proof.
  intros H0 H1 H2 ->. destruct (xg_wc_ext n) as [_ E]; auto. unfold WILDCOPY_OVERLENGTH in *.
  apply xg_wild_LS; lia.
Qed.

(* reading a separate array from a later start *)
Lemma xg_lrd_shift (c cs: list val) (a i: Z) :
  0 <= a <= Zlength cs -> 0 <= i -> lrd c (LS (sublist a (Zlength cs) cs)) i = lrd c (LS cs) (a + i).
Proof.
  intros. simpl. destruct (Z_lt_le_dec i (Zlength cs - a)).
  - rewrite Znth_sublist by lia. f_equal. lia.
  - rewrite !Znth_overflow; auto; rewrite ?Zlength_sublist; lia.
Qed.

Lemma xg_fwd_shift (k: nat) (c cs: list val) (d a i: Z) :
  0 <= a <= Zlength cs -> 0 <= i ->
  lfwd k c d (LS (sublist a (Zlength cs) cs)) i = lfwd k c d (LS cs) (a + i).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Ha Hi; cbn [lfwd]; auto.
  rewrite xg_lrd_shift by lia. rewrite IH by lia. f_equal. lia.
Qed.

Lemma xg_lrdn_shift (k: nat) (c cs: list val) (a i: Z) :
  0 <= a <= Zlength cs -> 0 <= i ->
  lrdn k c (LS (sublist a (Zlength cs) cs)) i = lrdn k c (LS cs) (a + i).
Proof.
  revert i. induction k as [|k IH]; intros i Ha Hi; cbn [lrdn]; auto.
  rewrite xg_lrd_shift by lia. rewrite IH by lia. do 2 f_equal. lia.
Qed.

Lemma xg_move_shift (k: nat) (c cs: list val) (d a i: Z) :
  0 <= a <= Zlength cs -> 0 <= i ->
  lmove k c d (LS (sublist a (Zlength cs) cs)) i = lmove k c d (LS cs) (a + i).
Proof. intros. unfold lmove. rewrite xg_lrdn_shift by lia. reflexivity. Qed.

Lemma xg_chunks_shift (k: nat) (c cs: list val) (d a i: Z) :
  0 <= a <= Zlength cs -> 0 <= i ->
  lchunks16 k c d (LS (sublist a (Zlength cs) cs)) i = lchunks16 k c d (LS cs) (a + i).
Proof.
  revert c d i. induction k as [|k IH]; intros c d i Ha Hi; cbn [lchunks16]; [reflexivity|].
  rewrite xg_move_shift by lia. rewrite IH by lia.
  replace (a + (i + 16)) with (a + i + 16) by lia. reflexivity.
Qed.

Lemma xg_wild_shift (c cs: list val) (d a i n: Z) :
  0 <= a <= Zlength cs -> 0 <= i ->
  lwild c d (LS (sublist a (Zlength cs) cs)) i n false = lwild c d (LS cs) (a + i) n false.
Proof. intros. unfold lwild. simpl andb. cbv iota. apply xg_chunks_shift; auto. Qed.

Lemma xg_safecopy_shift (c cs: list val) (op w a len: Z) :
  0 <= a <= Zlength cs ->
  lsafecopy c op w (LS (sublist a (Zlength cs) cs)) 0 len false = lsafecopy c op w (LS cs) a len false.
Proof.
  intros Ha. unfold lsafecopy. cbv iota.
  destruct (len <? 8). { rewrite xg_fwd_shift by lia. rewrite ?Z.add_0_l, ?Z.add_0_r. reflexivity. }
  destruct (w - (op + len) >=? 0). { rewrite xg_wild_shift by lia. rewrite ?Z.add_0_l, ?Z.add_0_r. reflexivity. }
  destruct (w - op >=? 0) eqn:E.
  - assert (0 <= w - op) by (rewrite Z.geb_le in E; lia).
    rewrite xg_wild_shift by lia. rewrite xg_fwd_shift by lia. rewrite ?Z.add_0_l, ?Z.add_0_r. reflexivity.
  - rewrite xg_fwd_shift by lia. rewrite ?Z.add_0_l, ?Z.add_0_r. reflexivity.
Qed.

(* the branches of the mirrors *)
Lemma xg_lexec_slow (ps vs de oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) :
  orb (llim - li <? ll) (oend - WILDCOPY_OVERLENGTH - op <? ll + ml) = true ->
  lexec ps vs de oend c op s li llim ll ml off =
  lmatch ps vs de (lsafecopy c op (oend - WILDCOPY_OVERLENGTH) s li ll false) (op + ll) ml off
    (Some (oend - WILDCOPY_OVERLENGTH)).
Proof. intros H. unfold lexec. rewrite H. reflexivity. Qed.

Lemma xg_lexec_fast (ps vs de oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) :
  ll <= llim - li -> ll + ml <= oend - WILDCOPY_OVERLENGTH - op ->
  lexec ps vs de oend c op s li llim ll ml off =
  lmatch ps vs de (if ll >? 16 then lwild (lmove 16 c op s li) (op + 16) s (li + 16) (ll - 16) false
                   else lmove 16 c op s li) (op + ll) ml off None.
Proof.
  intros H1 H2. unfold lexec.
  replace (orb (llim - li <? ll) (oend - WILDCOPY_OVERLENGTH - op <? ll + ml)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma xg_lexec_split_slow (ps vs de oend: Z) (c: list val) (op li llim ll ml off: Z) :
  orb (llim - li <? ll) (li + ll - WILDCOPY_OVERLENGTH - op <? ll + ml) = true ->
  lexec_split ps vs de oend c op li llim ll ml off =
  lmatch ps vs de (lsdbs c op li ll) (op + ll) ml off (Some (li + ll - WILDCOPY_OVERLENGTH)).
Proof. intros H. unfold lexec_split. rewrite H. reflexivity. Qed.

Lemma xg_lexec_split_fast (ps vs de oend: Z) (c: list val) (op li llim ll ml off: Z) :
  ll <= llim - li -> ll + ml <= li + ll - WILDCOPY_OVERLENGTH - op ->
  lexec_split ps vs de oend c op li llim ll ml off =
  lmatch ps vs de (if ll >? 16 then lwild (lmove 16 c op LW li) (op + 16) LW (li + 16) (ll - 16) false
                   else lmove 16 c op LW li) (op + ll) ml off None.
Proof.
  intros H1 H2. unfold lexec_split.
  replace (orb (llim - li <? ll) (li + ll - WILDCOPY_OVERLENGTH - op <? ll + ml)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* the match: from the prefix (d = 0) or, past the extDict part of length d, from prefixStart *)
Lemma xg_lmatch_prefix (ps vs de: Z) (c: list val) (x ml off: Z) (wo: option Z) :
  off <= x - ps -> lmatch ps vs de c x ml off wo = lprefix c x (x - off) ml off wo.
Proof.
  intros H. unfold lmatch. replace (off >? x - ps) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma xg_lmatch_ext (ps vs de: Z) (c: list val) (x ml off: Z) (wo: option Z) :
  x - ps < off -> ml <= off - (x - ps) ->
  lmatch ps vs de c x ml off wo = lmove (Z.to_nat ml) c x LW (de - (off - (x - ps))).
Proof.
  intros H1 H2. unfold lmatch. replace (off >? x - ps) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
  replace (de + (x - off - ps)) with (de - (off - (x - ps))) by lia.
  replace (de - (de - (off - (x - ps))) >=? ml) with true by (symmetry; apply Z.geb_le; lia).
  reflexivity.
Qed.

Lemma xg_lmatch_span (ps vs de: Z) (c: list val) (x ml off: Z) (wo: option Z) :
  x - ps < off -> off - (x - ps) < ml ->
  lmatch ps vs de c x ml off wo =
  lprefix (lmove (Z.to_nat (off - (x - ps))) c x LW (de - (off - (x - ps))))
    (x + (off - (x - ps))) (x + (off - (x - ps)) - off) (ml - (off - (x - ps))) off wo.
Proof.
  intros H1 H2. unfold lmatch. replace (off >? x - ps) with true by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
  replace (de + (x - off - ps)) with (de - (off - (x - ps))) by lia.
  replace (de - (de - (off - (x - ps))) >=? ml) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  replace (de - (de - (off - (x - ps)))) with (off - (x - ps)) by lia.
  replace (x + (off - (x - ps)) - off) with ps by lia. reflexivity.
Qed.

(* the output array after the literal copy is the mirror's first store (ZSTD_safecopy of the literals) *)
Definition xe_lit_mirror (c cA: list val) (k e: Z) (ls: litsrc) (li ll: Z) : Prop :=
  cA = lsafecopy c k (e - WILDCOPY_OVERLENGTH) (ls_l ls) li ll false.

(* the memmove from an ExtIn extDict (inside the output array) is the mirror's lmove *)
Lemma xe_mm_lmove (cA c2: list val) (e1 elen x0 dl n: Z) :
  xe_mm cA c2 (ExtIn e1 elen) x0 dl n -> 0 <= n -> 0 <= e1 - dl -> e1 - dl + n <= Zlength cA ->
  0 <= x0 -> x0 + n <= Zlength cA ->
  c2 = lmove (Z.to_nat n) cA x0 LW (e1 - dl).
Proof.
  intros (HL & Hs & Ho) Hn H1 H2 H3 H4. cbn [ext_end ext_src] in Hs.
  rewrite xg_lmove_LW by (rewrite ?Z2Nat.id; lia). rewrite Z2Nat.id by lia.
  apply Znth_eq_ext; [unfold put; list_solve |].
  intros q Hq. rewrite HL in Hq. unfold put.
  destruct (Z_lt_le_dec q x0); [| destruct (Z_lt_le_dec q (x0 + n))].
  - rewrite Ho by lia. list_solve.
  - assert (E: Znth (q - x0) (sublist x0 (x0 + n) c2) = Znth (q - x0) (sublist (e1 - dl) (e1 - dl + n) cA))
      by (rewrite Hs; reflexivity).
    rewrite !Znth_sublist in E by lia. replace (q - x0 + x0) with q in E by lia. rewrite E. list_solve.
  - rewrite Ho by lia. list_solve.
Qed.

(* the exact clause, match in the prefix: ZSTD_safecopy from k + ll - off after the literal copy *)
Lemma xe_exact_prefix (c cA c': list val) (k e li lim ll ml off ps: Z) (ls: litsrc) (x: ext_seg) (P: Prop) :
  xe_lit_mirror c cA k e ls li ll ->
  orb (lim - li <? ll) (e - WILDCOPY_OVERLENGTH - k <? ll + ml) = true ->
  off <= k + ll - ps ->
  c' = lsafecopy cA (k + ll) (e - 32) LW (k + ll - off) ml (1 =? OV_SRC_BEFORE_DST) ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => P -> c' = lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off
  end.
Proof.
  intros HA Hs Hp ->.
  assert (E: lsafecopy cA (k + ll) (e - 32) LW (k + ll - off) ml (1 =? OV_SRC_BEFORE_DST) =
             lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off).
  { rewrite xg_lexec_slow by exact Hs. rewrite xg_lmatch_prefix by lia. unfold lprefix.
    unfold xe_lit_mirror in HA. rewrite <- HA. reflexivity. }
  destruct x; auto.
Qed.

(* the exact clause, match wholly in an ExtIn extDict: one memmove after the literal copy *)
Lemma xe_exact_ext (c cA c2: list val) (k e li lim ll ml off ps: Z) (ls: litsrc) (x: ext_seg) (P: Prop) :
  xe_lit_mirror c cA k e ls li ll ->
  orb (lim - li <? ll) (e - WILDCOPY_OVERLENGTH - k <? ll + ml) = true ->
  exec_ext_ok x c -> Zlength cA = Zlength c ->
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml <= e <= Zlength c ->
  k + ll - ps < off <= k + ll - ps + ext_len x -> ml <= off - (k + ll - ps) ->
  xe_mm cA c2 x (k + ll) (off - (k + ll - ps)) ml ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => P -> c2 = lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off
  end.
Proof.
  intros HA Hs Hx HL Hps Hll Hml He Hoff Hin Hm.
  destruct x as [|e1 elen|]; auto.
  - simpl ext_len in Hoff. lia.
  - intros _. destruct Hx as [_ [Hx1 Hx2]]. cbn [ext_len ext_end] in *.
    rewrite xg_lexec_slow by exact Hs. unfold xe_lit_mirror in HA. rewrite <- HA.
    rewrite xg_lmatch_ext by lia.
    apply (xe_mm_lmove cA c2 e1 elen); auto; lia.
Qed.

(* the exact clause, match from an ExtIn extDict into the prefix: memmove of the extDict part, then
   ZSTD_safecopy from prefixStart *)
Lemma xe_exact_span (c cA c2 c': list val) (k e li lim ll ml off ps: Z) (ls: litsrc) (x: ext_seg) (P: Prop) :
  xe_lit_mirror c cA k e ls li ll ->
  orb (lim - li <? ll) (e - WILDCOPY_OVERLENGTH - k <? ll + ml) = true ->
  exec_ext_ok x c -> Zlength cA = Zlength c ->
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml <= e <= Zlength c ->
  k + ll - ps < off <= k + ll - ps + ext_len x -> off - (k + ll - ps) < ml ->
  xe_mm cA c2 x (k + ll) (off - (k + ll - ps)) (off - (k + ll - ps)) ->
  c' = lsafecopy c2 (k + ll + (off - (k + ll - ps))) (e - 32) LW ps (ml - (off - (k + ll - ps)))
         (1 =? OV_SRC_BEFORE_DST) ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => P -> c' = lexec ps (ps - ext_len x) (ext_end x) e c k (ls_l ls) li lim ll ml off
  end.
Proof.
  intros HA Hs Hx HL Hps Hll Hml He Hoff Hsp Hm ->.
  destruct x as [|e1 elen|]; auto.
  - simpl ext_len in Hoff. lia.
  - intros _. destruct Hx as [_ [Hx1 Hx2]]. cbn [ext_len ext_end] in *.
    rewrite xg_lexec_slow by exact Hs. unfold xe_lit_mirror in HA. rewrite <- HA.
    rewrite xg_lmatch_span by lia. unfold lprefix.
    rewrite <- (xe_mm_lmove cA c2 e1 elen (k + ll) (off - (k + ll - ps)) (off - (k + ll - ps))) by (auto; lia).
    replace (k + ll + (off - (k + ll - ps)) - off) with ps by lia. reflexivity.
Qed.

(* an equation kept as a hypothesis (VST's forward and entailer! would substitute a variable equation away) *)
Definition xe_is (a b: list val) : Prop := a = b.

(* a successful return: xe_ok_post's PROPs and the exact clause *)
Lemma xe_ok_post_x (A B C M: Prop) : A /\ B /\ C -> M -> A /\ B /\ C /\ M.
Proof. tauto. Qed.

(* an error return: xe_err_ret2 with the exact clause, vacuous on an error *)
Lemma xe_err_ret3 (n: Z) (b: bool) (U P Q R: Prop) (x: ext_seg) : 0 < n < 120 -> n <> 80 -> n <> 82 -> b = true -> U ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = true -> U /\ dec_err (err_code n)) /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  match x with ExtSep _ _ _ _ _ _ => True | _ => is_error_code (err_code n) = false -> R end /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn H80 H82 Hb HU.
  destruct (xe_err_ret2 n b U P Q Hn H80 H82 Hb HU) as (A & B & C & D & E & G).
  assert (Hb': is_error_code (err_code n) = true) by congruence.
  split; [auto | split; [auto | split; [auto | split; [auto | split; [auto | split; [| auto]]]]]].
  destruct x; auto; intros Hf; congruence.
Qed.

Lemma body_ZSTD_execSequenceEnd :
  semax_body Vprog EXEC_G f_ZSTD_execSequenceEnd ZSTD_execSequenceEnd_spec.
Proof.
  start_function.
  rename H8 into Xdh, H9 into Xdl, H10 into Xde, H11 into Hslow.
  assert (Hoff1: 1 <= off) by lia.
  forward_call (shq, sp, ll, ml, off, Tsh, v_sequence).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] ob) as FCc by entailer!.
  assert_PROP (isptr (lit_base ls ob)) as Plb by (destruct ls; simpl lit_base; simpl lit_res; entailer!).
  assert (Pob: isptr ob) by (destruct FCc; auto).
  assert_PROP (Zlength (lit_arr ls c) <= Ptrofs.max_unsigned) as Hla.
  { destruct ls; simpl lit_res; simpl lit_arr.
    - entailer!. match goal with Hf: field_compatible (Tarray tuchar (Zlength cl) _) _ lb |- _ =>
        destruct Hf as (Hp & _ & Hs & _) end.
      destruct lb; try contradiction. simpl in Hs. pose proof (Ptrofs.unsigned_range i). rep_lia.
    - entailer!. }
  assert (Hlim: 0 <= li <= lim /\ lim + 32 <= Zlength (lit_arr ls c))
    by (unfold WILDCOPY_OVERLENGTH in H5; destruct ls; simpl; [tauto | lia]).
  assert (Hel: 0 <= ext_len x <= 2 ^ 63 - 1) by apply H6.
  unfold seqrep. forward. forward. rewrite xe_add_pl by auto.
  forward. forward. forward. forward. forward. forward. rewrite xe_add_pl by auto.
  forward. forward. rewrite xe_sub_pl by auto.
  forward. rewrite xe_sub_pi by (auto; rep_lia).
  replace (Int64.add (Int64.repr ll) (Int64.repr ml)) with (Int64.repr (ll + ml))
    by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
  destruct (Z_lt_ge_dec (e - k) (ll + ml)) as [Herr1|Hok1].
  { apply xe_loop_seq with (Q := FF); [|apply semax_ff].
    forward_if.
    { apply prop_right, cp_sameblock; auto. }
    { xe_err_prefix. forward.
      Exists (err_code 70) c (offset_val li (lit_base ls ob)).
      entailer!. apply xe_err_ret3; [lia | lia | lia | | intros i _ _; reflexivity].
      unfold exec_err. rewrite (proj2 (Z.ltb_lt _ _) Herr1). reflexivity. }
    { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt (e - k) (ll + ml)); [|lia]. inv H8. }
  }
  match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P) end.
  { forward_if.
    { apply prop_right, cp_sameblock; auto. }
    { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt (e - k) (ll + ml)); [lia|]. inv H8. }
    { forward. apply ENTAIL_refl. } }
  destruct (Z_lt_ge_dec (lim - li) ll) as [Herr2|Hok2].
  { apply xe_loop_seq with (Q := FF); [|apply semax_ff].
    forward. forward.
    forward_if.
    { apply prop_right, cp_sameblock; auto. }
    { xe_err_prefix. forward.
      Exists (err_code 20) c (offset_val li (lit_base ls ob)).
      entailer!. apply xe_err_ret3; [lia | lia | lia | | intros i _ _; reflexivity]. unfold exec_err.
      rewrite (proj2 (Z.ltb_lt _ _) Herr2), orb_true_r. reflexivity. }
    { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt (lim - li) ll); [|lia]. inv H8. }
  }
  match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P) end.
  { forward. forward. forward_if.
    { apply prop_right, cp_sameblock; auto. }
    { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt (lim - li) ll); [lia|]. inv H8. }
    { forward. entailer!. } }
  set (Lv := sublist li (li + ll) (lit_arr ls c)).
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx [?A; ?B; ?C; _; ?D; ?E; ?F]))) _ _ =>
    apply semax_seq with (EX cA: list val, PROPx [xe_litc c cA k e ll Lv;
        byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes x -> byte_cells cA; xd_ub c cA;
        xe_lit_mirror c cA k e ls li ll]
      (LOCALx (temp _t'8 (Vlong (Int64.repr ll)) :: temp _t'7 (offset_val li (lit_base ls ob)) :: L)
      (SEPx [A; B; C; data_at sh (tarray tuchar (Zlength c)) cA ob; D; E; F]))) end.
  { destruct ls as [shl lb cl|]; simpl lit_base in *; simpl lit_res; simpl lit_arr in *.
    - (* separate literals *)
      destruct H5 as (SHl & _ & Hcl). unfold WILDCOPY_OVERLENGTH in Hcl.
      assert_PROP (field_compatible (tarray tuchar (Zlength cl)) [] lb) as FCl by entailer!.
      forward. forward.
      rewrite (tuchar_split shl lb cl li) by (auto; lia). flatten_sepcon_in_SEP.
      forward_call (gv, false, sh, ob, c, e - 32, 0, k, shl, offset_val li lb, sublist li (Zlength cl) cl, ll, 0).
      { rewrite (xe_fa _ ob k) by (auto; lia). entailer!. }
      { unfold WILDCOPY_OVERLENGTH, OV_NO_OVERLAP in *. rewrite Zlength_sublist by lia.
        split; [rep_lia|]. split; [rep_lia|]. split; [intros _; repeat split; auto; lia|].
        intros _. rewrite sublist_sublist by lia. apply (xd_sub cl li (lim + 32)); auto; lia. }
      Intros cA. Exists cA. entailer!.
      { split; [| split; [apply (xeb_lit_sep c cl _ li); auto |]].
        - apply xe_litc_intro; auto. rewrite H8. unfold Lv. rewrite sublist_sublist by lia. f_equal; lia.
        - unfold xe_lit_mirror. cbn [ls_l]. rewrite xg_safecopy_shift by lia. reflexivity. }
      rewrite (tuchar_split shl lb cl li) by (auto; lia). cancel.
    - (* literals in the output array *)
      forward. forward.
      forward_call (gv, true, sh, ob, c, e - 32, li, k, sh, ob, c, ll, 0).
      { rewrite (xe_fa _ ob k), (xe_fa _ ob li) by (auto; lia). entailer!. }
      { unfold WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN, OV_SRC_BEFORE_DST, OV_NO_OVERLAP in *.
        split; [lia|]. split; [intros _; split; [lia|]; split; [intros; discriminate|]; intros _; lia|].
        intros _. unfold copy_src_def. rewrite (proj2 (Z.ltb_ge li k)) by lia.
        apply (xd_sub c li (lim + 32)); auto; unfold WILDCOPY_OVERLENGTH; lia. }
      Intros cA. Exists cA. entailer!.
      try match goal with |- _ /\ _ => split; [| apply xeb_lit_in; auto] end.
      apply xe_litc_intro; auto. unfold Lv. rewrite <- (xe_lc_dbs c li k ll) by lia. auto. }
  Intros cA. match goal with H: xe_litc _ _ _ _ _ _ |- _ => destruct H as (HcA & HcAk & HcAo) end.
  match goal with H: xe_lit_mirror _ _ _ _ _ _ _ |- _ => rename H into HxA end.
  match goal with H: byte_cells c -> _ -> _ -> byte_cells cA |- _ => rename H into HbA end.
  match goal with H: xd_ub c cA |- _ => rename H into HuA end.
  assert (HLv0: Zlength Lv = ll) by (unfold Lv; rewrite Zlength_sublist; lia).
  assert (HLvb: Forall is_byte_val Lv)
    by (unfold Lv; apply (xd_sub (lit_arr ls c) li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia).
  assert (HdA: xd_rng cA ps (k + ll)).
  { apply (xd_after_lit c cA Lv k ps ll); auto; try lia.
    - apply xd_Forall_rng; auto; lia.
    - intros p Hp. apply (xe_cA_put c cA Lv k ll e); auto; try lia. }
  forward. forward. forward.
  apply semax_if_seq. forward_if.
  { apply prop_right, cp_sameblock; auto. }
  { (* the match starts in the extDict *)
    rewrite xe_gt_diff in H8 by (auto; rep_lia).
    destruct (zlt (k + ll - ps) off) as [Hext|Hc]; [clear H8 | inv H8].
    apply (proj1 (seq_assoc _ _ _ _ _ _)).
    destruct (Z_lt_ge_dec (k + ll - (ps - ext_len x)) off) as [Herr3|Hok3].
    { apply xe_loop_seq with (Q := FF); [|apply semax_ff].
      forward.
      forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { xe_err_prefix. forward.
        assert (HuA': forall q, 0 <= q < Zlength c -> Znth q cA = Znth q c \/ is_byte_val (Znth q cA)) by exact HuA.
        Exists (err_code 20) cA (offset_val (li + ll) (lit_base ls ob)).
        entailer!. apply xe_err_ret3; [lia | lia | lia | |].
        - unfold exec_err. rewrite (proj2 (Z.ltb_lt (k + ll - ps + ext_len x) off)) by lia.
          rewrite !orb_true_r. reflexivity.
        - intros p Hp Hn. apply HcAo; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt _ off); [|lia]. inv H8. }
    }
    match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P) end.
    { forward. forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { rewrite xe_gt_diff in H8 by (auto; rep_lia). destruct (zlt _ off); [lia|]. inv H8. }
      { forward. entailer!. } }
    assert (HxN: x <> ExtNone) by (intro; subst x; simpl in *; lia).
    rewrite (xe_dict_end x ob dE HxN).
    assert_PROP (isptr (xe_xb x ob)) as Pxb by (destruct x; simpl xe_xb; simpl ext_res; entailer!).
    set (dl := off - (k + ll - ps)).
    assert (Hdl: 0 < dl <= ext_len x) by (unfold dl; lia).
    assert (Hx: match x with ExtIn e1 elen => 0 <= e1 - elen /\ e1 <= Zlength c
                | ExtSep shx eb en ec e1 elen => readable_share shx /\ Zlength ec = en /\ en <= 2 ^ 63 - 1 /\
                    0 <= e1 - elen /\ e1 <= en | ExtNone => False end)
      by (destruct H6 as [_ H6]; destruct x; auto).
    forward.
    { entailer!. apply prop_right, cp_sameblock; auto. }
    rewrite cp_eval_sub by auto. rewrite xe_sub_pl_l by auto.
    replace (ext_end x - (ps - (k + ll - off))) with (ext_end x - dl) by (unfold dl; lia).
    forward. forward_if.
    { apply prop_right, cp_sameblock; auto. }
    { (* the match lies in the extDict *)
      rewrite xe_ge_diff in H8 by (auto; rep_lia).
      replace (ext_end x - (ext_end x - dl)) with dl in H8 by lia.
      destruct (zle ml dl) as [Hin|Hc]; [clear H8 | inv H8].
      forward.
      match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx [?A; ?B; ?C; _; ?D; ?E; _]))) _ _ =>
        apply semax_seq with (EX c2: list val, PROPx [xe_mm cA c2 x (k + ll) dl ml; byte_cells cA -> ext_bytes x -> byte_cells c2;
          xd_ub cA c2; xd_rng c2 (k + ll) (k + ll + ml)]
          (LOCALx L (SEPx [A; B; C; data_at sh (tarray tuchar (Zlength c)) c2 ob; D; E; ext_res x]))) end.
      { destruct x as [|e1 elen|shx eb en ec e1 elen]; [congruence | |]; simpl xe_xb in *; simpl ext_end in *;
          simpl ext_res; simpl ext_len in *.
        - forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) ml).
          { simpl. split; [auto|]. repeat split; try rep_lia.
            apply xd_bv. apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]. }
          destruct (xd_mm cA (Zlength c) (e1 - dl) (k + ll) ml) as [Hm1 Hm2]; auto; try lia.
          { apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]. }
          Exists (mm_result cA (Zlength c) (e1 - dl) (k + ll) ml). simpl mm_post. entailer!.
          split; [apply xe_mm_within; lia | intros B _; unfold mm_result; apply xeb_app3; apply xeb_sub; exact B].
        - destruct Hx as (SHx & Hen & Hen2 & Hx1 & Hx2).
          assert_PROP (field_compatible (tarray tuchar en) [] eb) as FCe by entailer!.
          rewrite (xe_mid shx eb ec en (e1 - dl) ml) by (auto; lia).
          rewrite (xe_mid sh ob cA (Zlength c) (k + ll) ml) by (auto; lia).
          flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
          sep_apply (data_at_data_at_ sh (tarray tuchar ml) (sublist (k + ll) (k + ll + ml) cA) (offset_val (k + ll) ob)).
          forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) ml
                          (sublist (e1 - dl) (e1 - dl + ml) ec)).
          { simpl mm_pre. cancel. }
          { simpl. split; [auto|]. split; [auto|]. split; [list_solve | split; [rep_lia |]].
            apply xd_bv. apply (xd_sub ec (e1 - elen) e1); auto; lia. }
          destruct (xd_put3 cA (sublist (e1 - dl) (e1 - dl + ml) ec) (Zlength c) (k + ll) ml) as [Hm1 Hm2]; auto; try lia.
          { rewrite Zlength_sublist; lia. }
          { apply (xd_sub ec (e1 - elen) e1); auto; lia. }
          Exists (sublist 0 (k + ll) cA ++ sublist (e1 - dl) (e1 - dl + ml) ec ++ sublist (k + ll + ml) (Zlength c) cA).
          simpl mm_post. entailer!.
          { split; [apply xe_mm_sep; lia | intros B E; apply xeb_mm_sep; [exact B | exact E]]. }
          rewrite <- (xe_mid_join sh ob cA (sublist (e1 - dl) (e1 - dl + ml) ec) (Zlength c) (k + ll) ml) by (auto; list_solve).
          cancel. }
      Intros c2. match goal with H: xe_mm _ _ _ _ _ _ |- _ => destruct H as (Hc2 & Hc2m & Hc2o) end.
      match goal with H: byte_cells cA -> _ -> byte_cells c2 |- _ => rename H into Hb2 end.
      match goal with H: xd_ub cA c2 |- _ => rename H into Hu2 end.
      match goal with H: xd_rng c2 (k + ll) _ |- _ => rename H into Hd2 end.
      assert (HU: forall q, 0 <= q < Zlength c -> Znth q c2 = Znth q c \/ is_byte_val (Znth q c2))
        by (apply (xd_ub_trans c cA c2); auto).
      assert (HF: Forall is_byte_val (sublist k (k + (ll + ml)) c2)).
      { apply xd_post_F; try lia. apply (xd_rng_app _ _ (k + ll)).
        - apply (xd_rng_ub cA); try lia; auto. apply (xd_rng_sub _ ps (k + ll)); auto; lia.
        - replace (k + (ll + ml)) with (k + ll + ml) by lia. exact Hd2. }
      unfold MORE_COMMANDS, abbreviate. forward.
      Exists (ll + ml) c2 (offset_val (li + ll) (lit_base ls ob)).
      entailer!.
      assert (HLv: Zlength (sublist li (li + ll) (lit_arr ls c)) = ll) by (rewrite Zlength_sublist; lia).
      destruct (xe_ext_case c cA c2 c2 (sublist li (li + ll) (lit_arr ls c)) k e ll ml off ps x) as [U X];
        auto; try lia.
      { rewrite Z.min_l by lia. split; [|split]; auto. }
      assert (Edl: dl = off - (k + ll - ps)) by reflexivity.
      apply xe_ok_post_x; [apply xe_ok_post; auto; try lia |].
      apply (xe_exact_ext c cA c2 k e li lim ll ml off ps ls x);
        [exact HxA | exact Hslow | exact H6 | lia .. | exact (conj Hc2 (conj Hc2m Hc2o))]. }
    (* the match runs from the extDict into the prefix *)
    rewrite xe_ge_diff in H8 by (auto; rep_lia).
    replace (ext_end x - (ext_end x - dl)) with dl in H8 by lia.
    destruct (zle ml dl) as [Hc|Hspan]; [inv H8 | clear H8].
    forward.
    { entailer!. apply prop_right, cp_sameblock; auto. }
    rewrite xe_sub_pp by auto. replace (ext_end x - (ext_end x - dl)) with dl by lia.
    apply (proj1 (seq_assoc _ _ _ _ _ _)).
    match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx [?A; ?B; ?C; _; ?D; ?E; _]))) _ _ =>
      apply semax_seq with (EX c2: list val, PROPx [xe_mm cA c2 x (k + ll) dl dl; byte_cells cA -> ext_bytes x -> byte_cells c2;
          xd_ub cA c2; xd_rng c2 (k + ll) (k + ll + dl)]
        (LOCALx L (SEPx [A; B; C; data_at sh (tarray tuchar (Zlength c)) c2 ob; D; E; ext_res x]))) end.
    { destruct x as [|e1 elen|shx eb en ec e1 elen]; [congruence | |]; simpl xe_xb in *; simpl ext_end in *;
        simpl ext_res; simpl ext_len in *.
      - forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) dl).
        { simpl. split; [auto|]. repeat split; try rep_lia.
          apply xd_bv. apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]. }
        destruct (xd_mm cA (Zlength c) (e1 - dl) (k + ll) dl) as [Hm1 Hm2]; auto; try lia.
        { apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]. }
        Exists (mm_result cA (Zlength c) (e1 - dl) (k + ll) dl). simpl mm_post. entailer!.
        split; [apply xe_mm_within; lia | intros B _; unfold mm_result; apply xeb_app3; apply xeb_sub; exact B].
      - destruct Hx as (SHx & Hen & Hen2 & Hx1 & Hx2).
        assert_PROP (field_compatible (tarray tuchar en) [] eb) as FCe by entailer!.
        rewrite (xe_mid shx eb ec en (e1 - dl) dl) by (auto; lia).
        rewrite (xe_mid sh ob cA (Zlength c) (k + ll) dl) by (auto; lia).
        flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
        sep_apply (data_at_data_at_ sh (tarray tuchar dl) (sublist (k + ll) (k + ll + dl) cA) (offset_val (k + ll) ob)).
        forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) dl
                        (sublist (e1 - dl) (e1 - dl + dl) ec)).
        { simpl mm_pre. cancel. }
        { simpl. split; [auto|]. split; [auto|]. split; [list_solve | split; [rep_lia |]].
          apply xd_bv. apply (xd_sub ec (e1 - elen) e1); auto; lia. }
        destruct (xd_put3 cA (sublist (e1 - dl) (e1 - dl + dl) ec) (Zlength c) (k + ll) dl) as [Hm1 Hm2]; auto; try lia.
        { rewrite Zlength_sublist; lia. }
        { apply (xd_sub ec (e1 - elen) e1); auto; lia. }
        Exists (sublist 0 (k + ll) cA ++ sublist (e1 - dl) (e1 - dl + dl) ec ++ sublist (k + ll + dl) (Zlength c) cA).
        simpl mm_post. entailer!.
        { split; [apply xe_mm_sep; lia | intros B E; apply xeb_mm_sep; [exact B | exact E]]. }
        rewrite <- (xe_mid_join sh ob cA (sublist (e1 - (off - (k + ll - ps))) (e1 - (off - (k + ll - ps)) + (off - (k + ll - ps))) ec)
                      (Zlength c) (k + ll) (off - (k + ll - ps))) by (auto; list_solve).
        cancel. }
    Intros c2. match goal with H: xe_mm _ _ _ _ _ _ |- _ => destruct H as (Hc2 & Hc2m & Hc2o) end.
    match goal with H: byte_cells cA -> _ -> byte_cells c2 |- _ => rename H into Hb2 end.
    match goal with H: xd_ub cA c2 |- _ => rename H into Hu2 end.
    match goal with H: xd_rng c2 (k + ll) _ |- _ => rename H into Hd2 end.
    assert (Hd2p: xd_rng c2 ps (k + ll + dl)).
    { apply (xd_rng_app _ _ (k + ll)); [| exact Hd2].
      apply (xd_rng_ub cA); try lia; auto. }
    assert (HC: copy_src_def c2 ps (k + ll + dl) (ml - dl)) by (apply (xd_csd c2 ps); auto; lia).
    forward. rewrite xe_add_pl by auto.
    forward. forward. forward.
    forward.
    replace (Int64.sub (Int64.repr ml) (Int64.repr dl)) with (Int64.repr (ml - dl))
      by (unfold Int64.sub; rewrite !Int64.unsigned_repr by rep_lia; reflexivity).
    forward_call (gv, true, sh, ob, c2, e - 32, ps, k + ll + dl, sh, ob, c2, ml - dl, 1).
    { rewrite (xe_fa _ ob (k + ll + dl)), (xe_fa _ ob ps) by (rewrite ?Hc2, ?HcA; auto; lia). entailer!. }
    { rewrite Hc2, HcA. cancel. }
    { unfold WILDCOPY_OVERLENGTH, OV_SRC_BEFORE_DST, OV_NO_OVERLAP in *. rewrite Hc2, HcA.
      repeat split; try rep_lia; intros; try lia; try discriminate; assumption. }
    Intros c'. match goal with H: c' = ?v |- _ => change (xe_is c' v) in H; rename H into Hsc end.
    match goal with H: forall q, 0 <= q < Zlength c2 -> Znth q c' = Znth q c2 \/ _ |- _ => rename H into Hu3 end.
    assert (HU: forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c')).
    { apply (xd_ub_trans c c2 c'); [lia | apply (xd_ub_trans c cA c2); auto; lia | exact Hu3]. }
    assert (HF: Forall is_byte_val (sublist k (k + (ll + ml)) c')).
    { apply xd_post_F; try lia. apply (xd_rng_app _ _ (k + ll + dl)).
      - apply (xd_rng_ub c2); try lia; [exact Hu3 |]. apply (xd_rng_sub _ ps (k + ll + dl)); auto; lia.
      - replace (k + (ll + ml)) with (k + ll + dl + (ml - dl)) by lia.
        apply (xd_rng_eq c' (listcopy c2 ps (k + ll + dl) (Z.to_nat (ml - dl)))); try lia;
          [rewrite Zlength_listcopy; lia | match goal with H: sublist (k + ll + dl) _ c' = _ |- _ => exact H end |].
        apply xd_listcopy; try lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        apply (xd_rng_sub _ ps (k + ll + dl)); auto; lia. }
    forward.
    Exists (ll + ml) c' (offset_val (li + ll) (lit_base ls ob)).
    entailer!.
    2: { rewrite Hc2, HcA. apply derives_refl. }
    assert (HLv: Zlength (sublist li (li + ll) (lit_arr ls c)) = ll) by (rewrite Zlength_sublist; lia).
    destruct (xe_ext_case c cA c2 c' (sublist li (li + ll) (lit_arr ls c)) k e ll ml off ps x) as [U X];
      auto; try lia.
    { rewrite Z.min_r by lia. split; [|split]; auto. }
    { rewrite Z.min_r by lia. intros p Hp Hn.
      match goal with Hq: forall k0, _ -> _ -> Znth k0 c' = Znth k0 c2 |- _ => apply Hq end; [lia|].
      unfold WILDCOPY_OVERLENGTH in *. lia. }
    { rewrite Z.min_r by lia. intros _. replace (k + ll + ml) with (k + ll + dl + (ml - dl)) by lia.
      match goal with Hq: sublist _ _ c' = _ |- _ => exact Hq end. }
    assert (Edl: dl = off - (k + ll - ps)) by reflexivity.
    apply xe_ok_post_x; [apply xe_ok_post; auto; try lia |].
    apply (xe_exact_span c cA c2 _ k e li lim ll ml off ps ls x);
      [exact HxA | exact Hslow | exact H6 | lia .. | exact (conj Hc2 (conj Hc2m Hc2o)) | exact Hsc]. }
  (* the match lies in the prefix *)
  rewrite xe_gt_diff in H8 by (auto; rep_lia).
  destruct (zlt (k + ll - ps) off) as [Hc|Hpre]; [inv H8|]. clear H8.
  assert (HC: copy_src_def cA (k + ll - off) (k + ll) ml) by (apply (xd_csd cA ps); auto; lia).
  forward.
  forward_call (gv, true, sh, ob, cA, e - 32, k + ll - off, k + ll, sh, ob, cA, ml, 1).
  { rewrite (xe_fa _ ob (k + ll)), (xe_fa _ ob (k + ll - off)) by (rewrite ?HcA; auto; lia). entailer!. }
  { rewrite HcA. cancel. }
  { unfold WILDCOPY_OVERLENGTH, OV_SRC_BEFORE_DST, OV_NO_OVERLAP in *. rewrite HcA.
    repeat split; try rep_lia; intros; try lia; try discriminate; assumption. }
  Intros c'. match goal with H: c' = ?v |- _ => change (xe_is c' v) in H; rename H into Hsc end.
  match goal with H: forall q, 0 <= q < Zlength cA -> Znth q c' = Znth q cA \/ _ |- _ => rename H into Hu3 end.
  assert (HU: forall q, 0 <= q < Zlength c -> Znth q c' = Znth q c \/ is_byte_val (Znth q c')).
  { apply (xd_ub_trans c cA c'); [lia | auto | exact Hu3]. }
  assert (HF: Forall is_byte_val (sublist k (k + (ll + ml)) c')).
  { apply xd_post_F; try lia. apply (xd_rng_app _ _ (k + ll)).
    - apply (xd_rng_ub cA); try lia; [exact Hu3 |]. apply (xd_rng_sub _ ps (k + ll)); auto; lia.
    - replace (k + (ll + ml)) with (k + ll + ml) by lia.
      apply (xd_rng_eq c' (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml))); try lia;
        [rewrite Zlength_listcopy; lia | match goal with H: sublist (k + ll) _ c' = _ |- _ => exact H end |].
      apply xd_listcopy; try lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      apply (xd_rng_sub _ ps (k + ll)); auto; lia. }
  forward.
  Exists (ll + ml) c' (offset_val (li + ll) (lit_base ls ob)).
  entailer!.
  2: { rewrite HcA. apply derives_refl. }
  assert (HLv: Zlength (sublist li (li + ll) (lit_arr ls c)) = ll) by (rewrite Zlength_sublist; lia).
  destruct (xe_prefix_case c cA c' (sublist li (li + ll) (lit_arr ls c)) k e ll ml off ps x) as [U X];
    auto; try lia.
  apply xe_ok_post_x; [apply xe_ok_post; auto; try lia |].
  apply (xe_exact_prefix c cA _ k e li lim ll ml off ps ls x); [exact HxA | exact Hslow | lia | exact Hsc].
Qed.

(* ---------- ZSTD_execSequenceEndSplitLitBuffer ---------- *)
Lemma es_add (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a + n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  unfold Ptrofs.of_int64. rewrite !Ptrofs.unsigned_repr_eq. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with Ptrofs.modulus. unfold Ptrofs.eqm. rewrite Zmod_mod.
  apply Zbits.eqmod_add; apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity.
Qed.

(* do { body } while (0); c  -- the body ends normally with F *)
Lemma es_dw : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) (F: Prop) body c R,
  semax Delta P body (loop1_ret_assert (!! F && P) (overridePost (!! F && P) R)) ->
  (F -> semax Delta P c R) ->
  semax Delta P (Ssequence (Sloop body Sbreak) c) R.
Proof.
  intros Espec cs Delta P F body c R H1 H2.
  apply semax_seq with (!! F && P).
  - apply semax_loop with (!! F && P); [exact H1 |].
    eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
    apply andp_left2, derives_refl.
  - apply semax_extract_prop. exact H2.
Qed.

(* for (;;break) {}: a no-op *)
Lemma es_skipbreak : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros Espec cs Delta P c R H. apply (es_dw Delta P True); [| intros _; exact H].
  eapply semax_post; [| | | | apply semax_skip].
  all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
  - intros rho; simpl. apply andp_left2. apply andp_right; [apply prop_right; auto | apply derives_refl].
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

Lemma es_ltu (a b: Z) : 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma es_neg (n: Z) : 0 < n < 120 -> n <> 80 -> n <> 82 -> Vlong (Int64.repr (- n)) = Vlong (Int64.repr (2 ^ 64 - n)) /\
  0 <= 2 ^ 64 - n <= Int64.max_unsigned /\ is_error_code (2 ^ 64 - n) = true /\ dec_err (2 ^ 64 - n).
Proof.
  intros. split; [| split; [| split]].
  - f_equal. apply cp_repr_eqm. replace (2 ^ 64 - n) with (- n + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. reflexivity.
  - unfold Int64.max_unsigned. change Int64.modulus with (2 ^ 64). lia.
  - unfold is_error_code. apply Z.ltb_lt. lia.
  - unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
    split; [apply Z.ltb_lt; lia | lia].
Qed.

Lemma es_bf (b: bool) : typed_false tint (bool2val b) -> b = false.
Proof. destruct b; [intros Hf; inversion Hf | auto]. Qed.

Lemma es_bt (b: bool) : typed_true tint (bool2val b) -> b = true.
Proof. destruct b; [auto | intros Hf; inversion Hf]. Qed.

Ltac es_cmp H := rewrite cp_sub_pp in H by auto; simpl in H; rewrite es_ltu in H by rep_lia;
  first [apply es_bt in H | apply es_bf in H | idtac].

Lemma es_cmp_gt (n: Z) (p: val) (i j: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i <= n -> 0 <= j <= n ->
  sem_cmp_pp Cgt (offset_val i p) (offset_val j p) = Some (Vint (if zlt j i then Int.one else Int.zero)).
Proof.
  intros FC Hi Hj. destruct FC as [Pp [_ [Hs _]]]. destruct p; try contradiction.
  simpl in Hs. rewrite Z.max_r in Hs by lia. pose proof (Ptrofs.unsigned_range i0).
  unfold sem_cmp_pp. simpl.
  rewrite if_true by auto. simpl. f_equal. unfold Ptrofs.ltu, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr i), (Ptrofs.unsigned_repr j) by rep_lia.
  rewrite !Ptrofs.unsigned_repr by rep_lia.
  destruct (zlt (Ptrofs.unsigned i0 + j) (Ptrofs.unsigned i0 + i)), (zlt j i); try reflexivity; lia.
Qed.

Lemma es_fa (n: Z) (p: val) (i: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i < n ->
  field_address (tarray tuchar n) (SUB i) p = offset_val i p.
Proof.
  intros. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

(* the literal copy is exact (no overlap with the source, or dst before src) *)
Lemma es_litput (c cA: list val) (k li ll: Z) :
  0 <= k -> 0 <= li -> 0 <= ll -> k + ll <= Zlength c -> li + ll <= Zlength c -> ~ (li < k < li + ll) ->
  Zlength cA = Zlength c ->
  sublist k (k + ll) cA = sublist k (k + ll) (listcopy c li k (Z.to_nat ll)) ->
  (forall p, 0 <= p < Zlength c -> ~ (k <= p < k + ll) -> Znth p cA = Znth p c) ->
  cA = put c k (sublist li (li + ll) c).
Proof.
  intros Hk Hli Hll Hkl Hlil Hov HA Hsub Hfr.
  assert (HLv: Zlength (sublist li (li + ll) c) = ll) by (rewrite Zlength_sublist; lia).
  apply Znth_eq_ext. { rewrite ecl_Zlength_put; lia. }
  intros p Hp. rewrite HA in Hp.
  destruct (Z_lt_le_dec p k) as [Lp | Lp]; [| destruct (Z_lt_le_dec p (k + ll)) as [Lq | Lq]].
  - rewrite ecl_Znth_put_out by lia. apply Hfr; lia.
  - rewrite ecl_Znth_put_in by lia. rewrite Znth_sublist by lia.
    assert (E: Znth p cA = Znth p (listcopy c li k (Z.to_nat ll))).
    { assert (E1: Znth (p - k) (sublist k (k + ll) cA) = Znth (p - k) (sublist k (k + ll) (listcopy c li k (Z.to_nat ll))))
        by (rewrite Hsub; reflexivity).
      rewrite !Znth_sublist in E1 by (try rewrite Zlength_listcopy; lia).
      replace (p - k + k) with p in E1 by lia. exact E1. }
    rewrite E.
    destruct (Z_le_gt_dec k li) as [Kl | Kl].
    + replace p with (k + (p - k)) at 1 by lia. rewrite listcopy_dbs by lia. f_equal; lia.
    + rewrite listcopy_disj by lia.
      rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. f_equal; lia.
  - rewrite ecl_Znth_put_out by lia. apply Hfr; lia.
Qed.

Lemma es_unch2 (c cA c': list val) (k ll a b hi: Z) :
  Zlength cA = Zlength c -> k <= a -> b <= hi -> k + ll <= hi ->
  (forall p, 0 <= p < Zlength c -> ~ (k <= p < k + ll) -> Znth p cA = Znth p c) ->
  (forall p, 0 <= p < Zlength c -> ~ (a <= p < b) -> Znth p c' = Znth p cA) ->
  unchanged_outside c c' k hi.
Proof.
  intros HA Ha Hb Hh Hf1 Hf2 i Hi Hn. rewrite Hf2 by lia. apply Hf1; lia.
Qed.

Lemma es_bytes (c c': list val) (k li ll ml off ps: Z) (x: ext_seg) :
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> 0 <= li -> li + ll <= Zlength c -> k + ll + ml <= Zlength c ->
  1 <= off <= k + ll - ps + ext_len x -> exec_ext_ok x c ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x) ->
  Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) -> ext_def x c ->
  Forall is_byte_val (sublist k (k + (ll + ml)) c').
Proof.
  intros. rewrite H7.
  assert (HLv: Zlength (sublist li (li + ll) c) = ll) by (rewrite Zlength_sublist; lia).
  pose proof (exec_c_bytes c k ml off ps (sublist li (li + ll) c) x) as B.
  rewrite HLv in B. replace (k + (ll + ml)) with (k + ll + ml) by lia. apply B; auto; lia.
Qed.

(* the match inside the prefix *)
Lemma es_exactP (c cA c': list val) (k li ll ml off ps: Z) (x: ext_seg) :
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> 1 <= off <= k + ll - ps -> k + ll + ml <= Zlength c ->
  0 <= li -> li + ll <= Zlength c ->
  cA = put c k (sublist li (li + ll) c) -> Zlength c' = Zlength c ->
  (forall p, k <= p < k + ll -> Znth p c' = Znth p cA) ->
  sublist (k + ll) (k + ll + ml) c' = sublist (k + ll) (k + ll + ml) (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml)) ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x).
Proof.
  intros. assert (HLv: Zlength (sublist li (li + ll) c) = ll) by (rewrite Zlength_sublist; lia).
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_prefix c cA c' k ps ml off (k + ll)); auto; try lia.
  - subst cA. rewrite ecl_Zlength_put; lia.
  - intros p Hp. subst cA. reflexivity.
Qed.

(* the match in the extDict: n = min ml dl bytes by memmove, then (dl < ml) the rest from the prefix *)
Lemma es_exactE (c cA c' : list val) (k li ll ml off ps: Z) (x: ext_seg) (n: Z) :
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll - ps < off <= k + ll - ps + ext_len x -> k + ll + ml <= Zlength c ->
  0 <= li -> li + ll <= Zlength c -> exec_ext_ok x c ->
  n = Z.min ml (off - (k + ll - ps)) ->
  cA = put c k (sublist li (li + ll) c) -> Zlength c' = Zlength c ->
  (forall p, k <= p < k + ll + n -> Znth p c' =
     Znth p (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + n) (ext_src cA x)))) ->
  (n < ml -> sublist (k + ll + n) (k + ll + ml) c' =
     sublist (k + ll + n) (k + ll + ml)
       (listcopy (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + n) (ext_src cA x)))
          ps (k + ll + n) (Z.to_nat (ml - n)))) ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x).
Proof.
  intros Hps Hll Hml Hoff Hc Hli Hlil Hx Hn HcA Hc' Hfr Hrest.
  assert (HLv: Zlength (sublist li (li + ll) c) = ll) by (rewrite Zlength_sublist; lia).
  set (dl := off - (k + ll - ps)) in *.
  assert (Hdl: 0 < dl <= ext_len x) by lia.
  assert (HB: 0 <= ext_end x - dl /\ ext_end x - dl + n <= Zlength (ext_src cA x)).
  { subst cA. unfold exec_ext_ok in Hx. destruct x as [| e1 elen | shx eb en ec e1 elen]; simpl in *;
      [lia | rewrite ecl_Zlength_put by lia; lia | lia]. }
  set (bs := sublist (ext_end x - dl) (ext_end x - dl + n) (ext_src cA x)) in *.
  assert (Hbs: Zlength bs = n) by (subst bs; rewrite Zlength_sublist; lia).
  assert (HA: Zlength cA = Zlength c) by (subst cA; rewrite ecl_Zlength_put; lia).
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_ext c cA (put cA (k + ll) bs) c' k ps ml off (k + ll) dl n); auto; try lia.
  - rewrite ecl_Zlength_put; lia.
  - intros p Hp. subst cA. reflexivity.
  - subst cA. reflexivity.
  - intros p Hp. rewrite ecl_Znth_put_out; [reflexivity | rewrite ?Hbs, ?HA; lia ..].
  - change (sublist (ext_end x - dl) (ext_end x - dl + n) (ext_src cA x)) with bs.
    assert (0 <= n <= ml) by lia. clearbody bs. unfold put. rewrite Hbs. list_solve.
Qed.

Lemma es_code (k e li ll ml off ps elen: Z) :
  0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> ll + ml <= e - k -> ~ (li < k < li + ll) ->
  off <= k + ll - ps + elen ->
  is_error_code (ll + ml) = false /\ exec_split_err k e li ll ml off ps elen = false.
Proof.
  intros. split.
  - unfold is_error_code. apply Z.ltb_ge. lia.
  - unfold exec_split_err.
    rewrite (proj2 (Z.ltb_ge (e - k) (ll + ml))) by lia.
    rewrite (proj2 (Z.ltb_ge (k + ll - ps + elen) off)) by lia.
    destruct (Z.ltb_spec li k), (Z.ltb_spec k (li + ll)); simpl; auto; lia.
Qed.

Lemma es_lit_exact (k li ll: Z) : lit_exact_split k li ll ->
  ll < WILDCOPY_OVERLENGTH \/ li - k <= WILDCOPY_VECLEN \/ WILDCOPY_OVERLENGTH <= li - k.
Proof. unfold lit_exact_split, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN. lia. Qed.

Lemma es_sub_l (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tlong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. unfold sem_sub_pl. simpl. f_equal.
  change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.add, Ptrofs.neg, Ptrofs.of_int64. apply Ptrofs.eqm_samerepr.
  rewrite !Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq. change Int64.modulus with Ptrofs.modulus.
  unfold Ptrofs.eqm. rewrite Zmod_mod. replace (a - n) with (a + - n) by lia.
  apply Zbits.eqmod_add. { apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity. }
  apply Zbits.eqmod_trans with (- (n mod Ptrofs.modulus)).
  { apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity. }
  apply Zbits.eqmod_neg. apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity.
Qed.

Lemma es_lt (a b: Z) : Int64.min_signed <= a <= Int64.max_signed -> Int64.min_signed <= b <= Int64.max_signed ->
  Int64.lt (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.lt. rewrite !Int64.signed_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma es_split3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + m)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + m - i) with m by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma es_mm_put (c: list val) (si di n: Z) :
  0 <= si -> 0 <= n -> si + n <= Zlength c ->
  mm_result c (Zlength c) si di n = put c di (sublist si (si + n) c).
Proof. intros. unfold mm_result, put. rewrite Zlength_sublist by lia. f_equal. f_equal. f_equal. lia. Qed.

(* the success post of the split executor, from the final array's frame and exactness *)
Lemma es_post (c cA c': list val) (k e li lim ll ml off ps: Z) (x: ext_seg) (lp: val) :
  0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> ll + ml <= e - k -> ~ (li < k < li + ll) ->
  1 <= off <= k + ll - ps + ext_len x -> 0 <= ps <= k -> k <= e <= Zlength c -> 0 <= li ->
  li + ll <= lim -> lim + 32 <= e -> exec_ext_ok x c ->
  Zlength cA = Zlength c ->
  (ll < WILDCOPY_OVERLENGTH \/ li - k <= WILDCOPY_VECLEN \/ WILDCOPY_OVERLENGTH <= li - k ->
   sublist k (k + ll) cA = sublist k (k + ll) (listcopy c li k (Z.to_nat ll))) ->
  (forall k0, 0 <= k0 < Zlength c -> ~ (k <= k0 < k + ll) -> Znth k0 cA = Znth k0 c) ->
  (Forall is_byte_val (sublist li (li + ll) c) -> Forall is_byte_val (sublist k (k + ll) cA)) ->
  Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < Z.min (k + ll + ml + 32) (Z.max (k + ll + ml) (li + ll))) ->
     Znth p c' = Znth p cA) ->
  (cA = put c k (sublist li (li + ll) c) ->
   sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) ->
  ((forall p, ps <= p < k + ll -> is_byte_val (Znth p cA)) -> ext_def x c ->
   Forall is_byte_val (sublist k (k + (ll + ml)) c')) ->
  is_error_code (ll + ml) = exec_split_err k e li ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false ->
     ll + ml = ll + ml /\ lp = lp /\
     unchanged_outside c c' k (Z.min (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) /\
     (ext_read_ok x k e ll ml off ps ->
        (lit_exact_split k li ll ->
           sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
        (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
         ext_def x c -> Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros Hll Hml Hcap Hov Hoff Hps Hke Hli Hlil Hlim Hx HA HAx HAf HAb Hc' Hfr Hex Hby.
  assert (Hel: 0 <= ext_len x) by (destruct Hx; lia).
  destruct (es_code k e li ll ml off ps (ext_len x)) as [Ec1 Ec2]; try lia.
  rewrite Ec1, Ec2. split; [reflexivity|]. split; [discriminate|]. intros _.
  split; [reflexivity|]. split; [reflexivity|]. split.
  { apply (es_unch2 c cA c' k ll (k + ll) (Z.min (k + ll + ml + 32) (Z.max (k + ll + ml) (li + ll)))); auto;
      unfold WILDCOPY_OVERLENGTH; lia. }
  intros Hrd. split.
  { intros Hle.
    assert (HcA: cA = put c k (sublist li (li + ll) c)).
    { apply es_litput; auto; try lia. apply HAx, es_lit_exact; auto. }
    exact (Hex HcA). }
  intros Hb1 Hb2 Hdef. apply Hby; auto.
  intros p Hp. destruct (Z_lt_le_dec p k) as [L|L].
  - rewrite HAf by lia. apply (ecb_Znth_Forall c ps k); auto; lia.
  - apply (ecb_Znth_Forall cA k (k + ll)); auto; lia.
Qed.

(* the bytes of the final array, match in the prefix *)
Lemma es_bytesP (cA c': list val) (k ll ml off ps: Z) :
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> 1 <= off <= k + ll - ps -> k + ll + ml <= Zlength cA ->
  Zlength c' = Zlength cA ->
  (forall p, k <= p < k + ll -> Znth p c' = Znth p cA) ->
  sublist (k + ll) (k + ll + ml) c' = sublist (k + ll) (k + ll + ml) (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml)) ->
  (forall p, ps <= p < k + ll -> is_byte_val (Znth p cA)) ->
  Forall is_byte_val (sublist k (k + (ll + ml)) c').
Proof.
  intros Hps Hll Hml Hoff HL Hc' Hfr Hsub Hb.
  apply ecb_Forall_Znth; try lia. intros p Hp.
  destruct (Z_lt_le_dec p (k + ll)) as [L|L].
  - rewrite Hfr by lia. apply Hb. lia.
  - assert (E: Znth (p - (k + ll)) (sublist (k + ll) (k + ll + ml) c') =
               Znth (p - (k + ll)) (sublist (k + ll) (k + ll + ml) (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml))))
      by (rewrite Hsub; reflexivity).
    rewrite !Znth_sublist in E by (try rewrite listcopy_Zlength; rewrite ?Z2Nat.id; lia).
    replace (p - (k + ll) + (k + ll)) with p in E by lia. rewrite E.
    apply (ecb_listcopy _ (k + ll - off) (k + ll) ps); try (rewrite ?Z2Nat.id; lia).
    intros q Hq. apply Hb. lia.
Qed.

(* the bytes of the final array, match from the extDict (then the prefix) *)
Lemma es_bytesE (c cA c': list val) (k ll ml off ps: Z) (x: ext_seg) (n: Z) :
  0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll - ps < off <= k + ll - ps + ext_len x -> k + ll + ml <= Zlength c ->
  exec_ext_ok x c -> n = Z.min ml (off - (k + ll - ps)) ->
  Zlength cA = Zlength c -> Zlength c' = Zlength c ->
  (forall k0, 0 <= k0 < Zlength c -> ~ (k <= k0 < k + ll) -> Znth k0 cA = Znth k0 c) ->
  (forall p, ps <= p < k + ll -> is_byte_val (Znth p cA)) -> ext_def x c ->
  (forall p, k <= p < k + ll + n -> Znth p c' =
     Znth p (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + n) (ext_src cA x)))) ->
  (n < ml -> sublist (k + ll + n) (k + ll + ml) c' =
     sublist (k + ll + n) (k + ll + ml)
       (listcopy (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + n) (ext_src cA x)))
          ps (k + ll + n) (Z.to_nat (ml - n)))) ->
  Forall is_byte_val (sublist k (k + (ll + ml)) c').
Proof.
  intros Hps Hll Hml Hoff Hc Hx Hn HA Hc' HAf HAb Hdef Hfr Hrest.
  set (dl := off - (k + ll - ps)) in *.
  assert (Hdl: 0 < dl <= ext_len x) by lia.
  set (S := sublist (ext_end x - dl) (ext_end x - dl + n) (ext_src cA x)) in *.
  assert (HS: Zlength S = n /\ forall j, 0 <= j < n -> is_byte_val (Znth j S)).
  { unfold S. unfold exec_ext_ok in Hx. destruct x as [|e1 elen|shx eb en ec e1 elen]; simpl in *.
    - lia.
    - destruct Hx as [_ [He0 He1]].
      split; [rewrite Zlength_sublist; lia|].
      intros j Hj. rewrite Znth_sublist by lia.
      destruct (Z_lt_le_dec (j + (e1 - dl)) k) as [L|L];
        [|destruct (Z_lt_le_dec (j + (e1 - dl)) (k + ll)) as [L2|L2]].
      + rewrite HAf by lia. apply (ecb_Znth_Forall c (e1 - elen) e1); auto; lia.
      + apply HAb. lia.
      + rewrite HAf by lia. apply (ecb_Znth_Forall c (e1 - elen) e1); auto; lia.
    - destruct Hx as [_ [_ [Hen [_ [He0 He1]]]]].
      split; [rewrite Zlength_sublist; lia|].
      intros j Hj. rewrite Znth_sublist by lia.
      apply (ecb_Znth_Forall ec (e1 - elen) e1); auto; lia. }
  destruct HS as [HSl HSb].
  assert (Hc2l: Zlength (put cA (k + ll) S) = Zlength c) by (rewrite ecl_Zlength_put; lia).
  assert (Hc2b: forall q, ps <= q < k + ll + n -> is_byte_val (Znth q (put cA (k + ll) S))).
  { intros q Hq. destruct (Z_lt_le_dec q (k + ll)).
    + rewrite ecl_Znth_put_out by lia. apply HAb. lia.
    + rewrite ecl_Znth_put_in by lia. apply HSb. lia. }
  apply ecb_Forall_Znth; try lia. intros p Hp.
  destruct (Z_lt_le_dec p (k + ll + n)) as [L|L].
  - rewrite Hfr by lia. apply Hc2b. lia.
  - assert (Hlt: n < ml) by lia. specialize (Hrest Hlt).
    assert (E: Znth (p - (k + ll + n)) (sublist (k + ll + n) (k + ll + ml) c') =
               Znth (p - (k + ll + n)) (sublist (k + ll + n) (k + ll + ml)
                 (listcopy (put cA (k + ll) S) ps (k + ll + n) (Z.to_nat (ml - n)))))
      by (rewrite Hrest; reflexivity).
    rewrite !Znth_sublist in E by (try rewrite listcopy_Zlength; rewrite ?Z2Nat.id; lia).
    replace (p - (k + ll + n) + (k + ll + n)) with p in E by lia. rewrite E.
    apply (ecb_listcopy _ ps (k + ll + n) ps); try (rewrite ?Z2Nat.id; lia).
    intros q Hq. apply Hc2b. lia.
Qed.

Lemma es_join_put (sh: share) (n i m: Z) (l v: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n -> Zlength v = m ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) v (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) (put l i v) p.
Proof.
  intros. rewrite (es_split3 sh n i m (put l i v) p) by (auto; unfold put; list_solve).
  unfold put. subst m.
  replace (sublist 0 i (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with (sublist 0 i l) by list_solve.
  replace (sublist i (i + Zlength v) (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with v by list_solve.
  replace (sublist (i + Zlength v) n (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l))
    with (sublist (i + Zlength v) n l) by list_solve.
  apply derives_refl.
Qed.

Lemma es_join3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) l p.
Proof. intros. rewrite (es_split3 sh n i m l p) by auto. apply derives_refl. Qed.

Lemma es_fa0 (n: Z) (p: val) (i: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i <= n ->
  field_address0 (tarray tuchar n) (SUB i) p = offset_val i p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Lemma es_unch (c: list val) (lo hi: Z) : unchanged_outside c c lo hi.
Proof. intros i _ _. reflexivity. Qed.

Lemma es_sub (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. unfold sem_sub_pl. simpl. f_equal.
  change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.add, Ptrofs.neg, Ptrofs.of_int64. apply Ptrofs.eqm_samerepr.
  rewrite !Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq. change Int64.modulus with Ptrofs.modulus.
  unfold Ptrofs.eqm. rewrite Zmod_mod. replace (a - n) with (a + - n) by lia.
  apply Zbits.eqmod_add. { apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity. }
  apply Zbits.eqmod_trans with (- (n mod Ptrofs.modulus)).
  { apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity. }
  apply Zbits.eqmod_neg. apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; reflexivity.
Qed.

(* bytes in, bytes out: the split executor's arrays stay byte_cells *)
Lemma esb_cells (c c': list val) (di n: Z) :
  Zlength c' = Zlength c -> 0 <= di -> 0 <= n -> di + n <= Zlength c -> byte_cells c ->
  (Forall is_byte_val (sublist di (di + n) c')) ->
  (forall i, 0 <= i < Zlength c -> ~ (di <= i < di + n) -> Znth i c' = Znth i c) ->
  byte_cells c'.
Proof.
  intros HL H1 H2 H3 Hc Hs Hu. unfold byte_cells in *.
  pose proof (proj1 (Forall_Znth c _) Hc) as Hc'.
  apply Forall_Znth. intros i Hi.
  destruct (Z_lt_le_dec i di) as [L|L]; [|destruct (Z_lt_le_dec i (di + n)) as [L2|L2]].
  - rewrite Hu by lia. apply Hc'; lia.
  - apply (ecb_Znth_Forall c' di (di + n)); auto; lia.
  - rewrite Hu by lia. apply Hc'; lia.
Qed.

Lemma esb_put (c v: list val) (i: Z) :
  byte_cells c -> byte_cells v -> byte_cells (put c i v).
Proof.
  intros Hc Hv. unfold byte_cells, put in *.
  apply Forall_app; split; [apply Forall_sublist; auto|].
  apply Forall_app; split; [auto | apply Forall_sublist; auto].
Qed.

Lemma esb_put_sub (c d: list val) (i lo hi: Z) :
  byte_cells c -> byte_cells d -> byte_cells (put c i (sublist lo hi d)).
Proof. intros Hc Hd. apply esb_put; auto. unfold byte_cells in *. apply Forall_sublist; auto. Qed.

Lemma esb_cA (c cA: list val) (li k ll: Z) :
  Zlength cA = Zlength c -> 0 <= k -> 0 <= ll -> k + ll <= Zlength c ->
  (Forall is_byte_val (sublist li (li + ll) c) -> Forall is_byte_val (sublist k (k + ll) cA)) ->
  (forall i, 0 <= i < Zlength c -> ~ (k <= i < k + ll) -> Znth i cA = Znth i c) ->
  byte_cells c -> byte_cells cA.
Proof.
  intros HL H1 H2 H3 Hs Hu Hc. apply (esb_cells c cA k ll); auto.
  apply Hs. apply Forall_sublist. exact Hc.
Qed.

(* an error return: the exact clause (about successful returns) holds vacuously *)
Ltac es_xerr x := solve [ exact I | (intros ?HF; congruence) | (destruct x; try exact I; intros ?HF; congruence) ].

(* the exact equations of the callees' posts, once used: the return's forward would substitute them *)
Ltac es_clr := repeat match goal with
  | H: _ = lsafecopy _ _ _ _ _ _ _ |- _ => clear H
  | H: _ = lsdbs _ _ _ _ |- _ => clear H
  end.

Lemma body_ZSTD_execSequenceEndSplitLitBuffer :
  semax_body Vprog EXEC_G f_ZSTD_execSequenceEndSplitLitBuffer ZSTD_execSequenceEndSplitLitBuffer_spec.
Proof.
  start_function.
  rename H10 into Xdh, H11 into Xdl, H12 into Xde, H13 into Xov, H14 into Xslow.
  assert (Hoff1: 1 <= off) by lia.
  forward_call (shq, sp, ll, ml, off, Tsh, v_sequence).
  unfold seqrep.
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] ob) as FC by entailer!.
  assert (Pob: isptr ob) by (destruct FC; auto).
  assert (Hlim: lim + 32 <= e) by exact H7.
  assert (Hel: 0 <= ext_len x <= 2 ^ 63 - 1) by (destruct H8; lia).
  forward. forward. rewrite es_add by auto.
  forward. forward. forward. rewrite add64_repr.
  forward. forward. forward. rewrite es_add by auto.
  forward. forward. rewrite es_sub by auto.
  apply (es_dw _ _ (ll + ml <= e - k)).
  forward_if.
  { entailer!. apply cp_sameblock; auto. }
  { rewrite cp_sub_pp in H10 by auto. simpl in H10. rewrite es_ltu in H10 by rep_lia.
    apply es_skipbreak. apply (es_dw _ _ True). forward_if. { contradiction. } { forward. entailer!. }
    intros _. apply es_skipbreak. apply es_skipbreak.
    destruct (es_neg 70) as [E1 [E2 [E3 E4]]]; try lia.
    forward. Exists (2 ^ 64 - 70) c (offset_val li ob). unfold seqrep. entailer!.
    split; [| split; [intros _; split; [apply es_unch | exact E4] | es_xerr x]].
    rewrite E3. unfold exec_split_err. rewrite H10. reflexivity. }
  forward.
  entailer!.
  { rewrite cp_sub_pp in H10 by auto. simpl in H10. rewrite es_ltu in H10 by rep_lia.
    apply es_bf, Z.ltb_ge in H10. lia. }
  intros Hcap.
  apply (es_dw _ _ True). forward. forward. forward_if.
  { entailer!. apply cp_sameblock; auto. }
  { es_cmp H10. apply Z.ltb_lt in H10. lia. }
  { forward. entailer!. }
  intros _.
  apply (es_dw _ _ (~ (li < k /\ k < li + ll))). forward.
  forward_if (temp _t'1 (Val.of_bool ((li <? k) && (k <? li + ll)))).
  { apply (cp_test_order_TT sh (Zlength c) c); auto; try lia. cancel. }
  { rewrite (es_cmp_gt (Zlength c)) in H10 by (auto; lia).
    forward. forward. forward.
    entailer!. { apply (cp_test_order_TT sh (Zlength c) c); auto; try lia. cancel. }
    change (eval_binop Oadd (tptr tuchar) tulong (offset_val li ob) (Vlong (Int64.repr ll))) with
      (force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val li ob) (Vlong (Int64.repr ll)))).
    rewrite es_add by auto. unfold eval_binop. simpl force_val2.
    destruct (zlt li k) as [Hlk|Hlk]; [|inversion H10].
    change (sem_binary_operation' Olt (tptr tuchar) (tptr tuchar)) with (sem_cmp_pp Clt).
    rewrite (cp_cmp (Zlength c)) by (auto; lia).
    assert (Hb: (li <? k) = true) by (apply Z.ltb_lt; lia). rewrite Hb. simpl andb.
    destruct (zlt k (li + ll)) as [Hk|Hk];
      [rewrite (proj2 (Z.ltb_lt k (li+ll))) by lia | rewrite (proj2 (Z.ltb_ge k (li+ll))) by lia]; entailer!. }
  { rewrite (es_cmp_gt (Zlength c)) in H10 by (auto; lia).
    destruct (zlt li k) as [Hlk|Hlk]; [inversion H10|].
    forward. rewrite (proj2 (Z.ltb_ge li k)) by lia. entailer!. }
  forward_if.
  { destruct (es_neg 70) as [E1 [E2 [E3 E4]]]; try lia.
    apply es_skipbreak. apply (es_dw _ _ True). forward_if. { contradiction. } { forward. entailer!. }
    intros _. apply es_skipbreak. apply es_skipbreak.
    forward. Exists (2 ^ 64 - 70) c (offset_val li ob). unfold seqrep. entailer!.
    split; [| split; [intros _; split; [apply es_unch | exact E4] | es_xerr x]].
    rewrite E3. unfold exec_split_err. destruct (andb (li <? k) (k <? li + ll)); [|inversion H10].
    rewrite orb_true_r. reflexivity. }
  { forward. entailer!. destruct (andb (li <? k) (k <? li + ll)) eqn:Eb; [inversion H10|].
    rewrite (proj2 (Z.ltb_lt li k)), (proj2 (Z.ltb_lt k (li + ll))) in Eb by lia. discriminate. }
  intros Hov.
  assert (HlB: Forall is_byte_val (sublist li (li + ll) c))
    by (apply (xd_sub c li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia).
  forward. forward. forward_call (gv, sh, ob, c, li, k, ll).
  { entailer!. simpl. rewrite !(es_fa0 (Zlength c)) by (auto; lia). reflexivity. }
  Intros cA.
  match goal with H: cA = lsdbs _ _ _ _ |- _ => rename H into HxA end.
  assert (HbA: byte_cells c -> byte_cells cA) by (apply (esb_cA c cA li k ll); auto; lia).
  assert (HuA: xd_ub c cA)
    by (apply (xd_ub_frame c cA k (k + ll)); [exact H13 | apply xd_Forall_rng; [lia | lia | apply H12; exact HlB]]).
  assert (HdA: xd_rng cA ps (k + ll)).
  { apply (xd_rng_app _ _ k).
    - apply (xd_rng_ub c); try lia; [exact HuA | apply xd_Forall_rng; auto; lia].
    - apply xd_Forall_rng; [lia | lia | apply H12; exact HlB]. }
  forward. forward. forward.
  apply semax_if_seq. forward_if.
  { entailer!. apply cp_sameblock; auto. }
  2: {
    es_cmp H14. apply Z.ltb_ge in H14.
    assert (HC: copy_src_def cA (k + ll - off) (k + ll) ml) by (apply (xd_csd cA ps); auto; lia).
    forward.
    forward_call (gv, true, sh, ob, cA, li + ll - WILDCOPY_OVERLENGTH, k + ll - off, k + ll, Tsh, nullval, @nil val, ml, 1).
    { entailer!. simpl. rewrite H10, !(es_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite H10. cancel. }
    { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH in *.
      repeat split; first [lia | rep_lia | (intros; lia) | (intros Hc; discriminate) | exact HC]. }
    Intros c'.
    match goal with H: c' = lsafecopy _ _ _ _ _ _ _ |- _ => rename H into Hx3 end. cbv beta iota in Hx3.
    match goal with H: forall q, 0 <= q < Zlength cA -> Znth q c' = Znth q cA \/ _ |- _ => rename H into Hu3 end.
    destruct (xd_fin c cA c' k ps (k + ll) (k + (ll + ml))) as [HU HF]; auto; try lia.
    { replace (k + (ll + ml)) with (k + ll + ml) by lia.
      apply (xd_rng_eq c' (listcopy cA (k + ll - off) (k + ll) (Z.to_nat ml))); try lia;
        [rewrite Zlength_listcopy; lia | exact H16 |].
      apply xd_listcopy; try lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      apply (xd_rng_sub _ ps (k + ll)); auto; lia. }
    rewrite H10 in *. specialize (HF H15).
    assert (HX: match x with ExtSep _ _ _ _ _ _ => True | _ => is_error_code (ll + ml) = false ->
                  c' = lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off end).
    { destruct x; try exact I; intros _;
        rewrite xg_lexec_split_slow by exact Xslow; rewrite <- HxA; rewrite xg_lmatch_prefix by lia;
        unfold lprefix; exact Hx3. }
    es_clr.
    forward.
    Exists (ll + ml) c' (offset_val (li + ll) ob). entailer!.
    try (split; [solve [intros Hb _; apply H18, HbA, Hb]|]).
    apply (es_post c cA c' k e li lim ll ml off ps x); auto; try lia.
    - intros p Hp Hn. apply H17; unfold WILDCOPY_OVERLENGTH in *; lia.
    - intros HcA. apply (es_exactP c cA c'); auto; try lia.
      intros p Hp. apply H17; unfold WILDCOPY_OVERLENGTH in *; lia.
    }
  (* the match starts in the extDict *)
  es_cmp H14. apply Z.ltb_lt in H14.
  apply -> seq_assoc. apply (es_dw _ _ (off <= k + ll - ps + ext_len x)).
  forward. forward_if.
  { entailer!. apply cp_sameblock; auto. }
  { es_cmp H15. apply Z.ltb_lt in H15.
    destruct (es_neg 20) as [E1 [E2 [E3 E4]]]; try lia.
    apply es_skipbreak. apply (es_dw _ _ True). forward_if. { contradiction. } { forward. entailer!. }
    intros _. apply es_skipbreak. apply es_skipbreak.
    assert (HuA': forall q, 0 <= q < Zlength c -> Znth q cA = Znth q c \/ is_byte_val (Znth q cA)) by exact HuA.
    es_clr. forward. Exists (2 ^ 64 - 20) cA (offset_val (li + ll) ob). unfold seqrep. entailer!.
    try (split; [solve [intros Hb _; apply HbA, Hb]|]).
    split.
    { rewrite E3. unfold exec_split_err. rewrite (proj2 (Z.ltb_lt (k + ll - ps + ext_len x) off)) by lia.
      rewrite !orb_true_r. reflexivity. }
    split; [intros _; split; [intros i Hi Hn; apply H13; lia | exact E4] | es_xerr x]. }
  { forward. entailer!. es_cmp H15. apply Z.ltb_ge in H15. lia. }
  intros Hoffx.
  destruct x as [| e1 elen | shx eb en ec e1 elen]; simpl ext_len in *; [lia | |].
  - (* ExtIn *)
    simpl dict_end. assert (He1: 0 <= e1 - elen /\ e1 <= Zlength c) by (destruct H8 as [_ ?]; auto).
    destruct He1 as [He1 He2].
    forward.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    replace (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val ps ob) (offset_val (k + ll - off) ob))
      with (Vlong (Int64.repr (ps - (k + ll - off)))) by (symmetry; apply (cp_sub_pp ob ps (k + ll - off)); auto).
    rewrite es_sub_l by auto.
    replace (e1 - (ps - (k + ll - off))) with (e1 - (off - (k + ll - ps))) by lia.
    assert (Hdl: 0 < off - (k + ll - ps) <= elen) by lia.
    set (dl := off - (k + ll - ps)) in *.
    forward. forward_if.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    { match goal with Ht: typed_true _ _ |- _ => rename Ht into Hge end.
      rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
      rewrite es_lt in Hge by rep_lia. apply es_bt, negb_true_iff, Z.ltb_ge in Hge.
      forward.
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) cA))
        by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
      forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) ml).
      { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
      unfold mm_post.
      replace (mm_result cA (Zlength c) (e1 - dl) (k + ll) ml) with (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA))
        by (rewrite <- H10; symmetry; apply es_mm_put; lia).
      destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + ml) cA) (k + ll)) as [Hm1 Hm2];
        [lia | rewrite Zlength_sublist; lia | exact HmB |].
      rewrite Zlength_sublist in Hm2 by lia.
      destruct (xd_fin c cA (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA)) k ps (k + ll) (k + (ll + ml)))
        as [HU HF]; auto; try lia.
      { replace (k + (ll + ml)) with (k + ll + (e1 - dl + ml - (e1 - dl))) by lia. exact Hm2. }
      specialize (HF ltac:(rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia)).
      assert (HX: is_error_code (ll + ml) = false ->
                  put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA) =
                  lexec_split ps (ps - elen) e1 e c k li lim ll ml off).
      { intros _. rewrite xg_lexec_split_slow by exact Xslow; rewrite <- HxA.
        rewrite xg_lmatch_ext by (unfold dl in *; lia). change (off - (k + ll - ps)) with dl.
        rewrite <- xg_mm by (unfold dl in *; lia). rewrite es_mm_put by (unfold dl in *; lia). reflexivity. }
      es_clr.
      forward.
      Exists (ll + ml) (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA)) (offset_val (li + ll) ob).
      entailer!.
      try (split; [solve [intros Hb _; apply esb_put_sub; apply HbA, Hb]|]).
      apply (es_post c cA _ k e li lim ll ml off ps (ExtIn e1 elen)); auto; try (simpl; lia).
      - intros p Hp Hn. rewrite ecl_Znth_put_out; [reflexivity | rewrite ?Zlength_sublist; lia ..].
      - intros HcA. apply (es_exactE c cA _ k li ll ml off ps (ExtIn e1 elen) ml); auto; try (simpl; lia). }
    match goal with Ht: typed_false _ _ |- _ => rename Ht into Hge end.
    rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
    rewrite es_lt in Hge by rep_lia. apply es_bf, negb_false_iff, Z.ltb_lt in Hge.
    forward.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    replace (force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val e1 ob) (offset_val (e1 - dl) ob)))
      with (Vlong (Int64.repr dl))
      by (symmetry; etransitivity; [apply (cp_sub_pp ob e1 (e1 - dl)); auto | do 2 f_equal; lia]).
    assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) cA))
      by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
    forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) dl).
    { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
    unfold mm_post.
    replace (mm_result cA (Zlength c) (e1 - dl) (k + ll) dl) with (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA))
      by (rewrite <- H10; symmetry; apply es_mm_put; lia).
    forward. rewrite es_add by auto.
    forward. forward. rewrite sub64_repr.
    forward. forward.
    destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + dl) cA) (k + ll)) as [Hm1 Hm2];
      [lia | rewrite Zlength_sublist; lia | exact HmB |].
    rewrite Zlength_sublist in Hm2 by lia. replace (k + ll + (e1 - dl + dl - (e1 - dl))) with (k + ll + dl) in Hm2 by lia.
    remember (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)) as c2 eqn:Hc2e.
    assert (Hc2: Zlength c2 = Zlength c) by (subst c2; rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia).
    assert (Hc2f: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA).
    { intros p Hp Hn. subst c2. rewrite ecl_Znth_put_out; [reflexivity | rewrite ?Zlength_sublist; lia ..]. }
    assert (Hu2: xd_ub c c2) by (apply (xd_ub_trans c cA c2); auto).
    assert (Hd2p: xd_rng c2 ps (k + ll + dl)).
    { apply (xd_rng_app _ _ (k + ll)); [| exact Hm2]. apply (xd_rng_ub cA); try lia; auto. }
    assert (HC: copy_src_def c2 ps (k + ll + dl) (ml - dl)) by (apply (xd_csd c2 ps); auto; lia).
    forward_call (gv, true, sh, ob, c2, li + ll - WILDCOPY_OVERLENGTH, ps, k + ll + dl, Tsh, nullval, @nil val, ml - dl, 1).
    { entailer!. simpl. rewrite Hc2, !(es_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc2. cancel. }
    { rewrite Hc2. unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH in *.
      repeat split; first [lia | rep_lia | (intros; lia) | (intros Hc; discriminate) | exact HC]. }
    Intros c'.
    match goal with H: c' = lsafecopy _ _ _ _ _ _ _ |- _ => rename H into Hx3 end. cbv beta iota in Hx3.
    match goal with H: forall q, 0 <= q < Zlength c2 -> Znth q c' = Znth q c2 \/ _ |- _ => rename H into Hu3 end.
    destruct (xd_fin c c2 c' k ps (k + ll + dl) (k + (ll + ml))) as [HU HF]; auto; try lia.
    { replace (k + (ll + ml)) with (k + ll + dl + (ml - dl)) by lia.
      apply (xd_rng_eq c' (listcopy c2 ps (k + ll + dl) (Z.to_nat (ml - dl)))); try lia;
        [rewrite Zlength_listcopy; lia | exact H16 |].
      apply xd_listcopy; try lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      apply (xd_rng_sub _ ps (k + ll + dl)); auto; lia. }
    rewrite Hc2 in *. specialize (HF H15).
    assert (HX: is_error_code (ll + ml) = false ->
                c' = lexec_split ps (ps - elen) e1 e c k li lim ll ml off).
    { intros _. rewrite xg_lexec_split_slow by exact Xslow; rewrite <- HxA.
      rewrite xg_lmatch_span by (unfold dl in *; lia). change (off - (k + ll - ps)) with dl.
      unfold lprefix. replace (k + ll + dl - off) with ps by (unfold dl in *; lia).
      rewrite <- xg_mm by (unfold dl in *; lia). rewrite es_mm_put by (unfold dl in *; lia).
      rewrite <- Hc2e. exact Hx3. }
    es_clr.
    forward.
    Exists (ll + ml) c' (offset_val (li + ll) ob). entailer!.
    try (split; [solve [intros Hb _; apply H18; try rewrite Hc2e; apply esb_put_sub; apply HbA, Hb]|]).
    apply (es_post c cA c' k e li lim ll ml off ps (ExtIn e1 elen)); auto; try (simpl; lia).
    + intros p Hp Hn. rewrite H17 by (unfold WILDCOPY_OVERLENGTH in *; lia). apply Hc2f; lia.
    + intros HcA. apply (es_exactE c cA c' k li ll ml off ps (ExtIn e1 elen) dl); auto; try (simpl; lia).
      * intros p Hp. simpl ext_end; simpl ext_src. rewrite H17 by (unfold WILDCOPY_OVERLENGTH in *; lia).
        try rewrite Hc2e; reflexivity.
      * intros _. replace (k + ll + ml) with (k + ll + dl + (ml - dl)) by lia. rewrite H16. try rewrite Hc2e; reflexivity.
  - (* ExtSep *)
    simpl dict_end. unfold ext_res.
    assert (Hx: readable_share shx /\ Zlength ec = en /\ en <= 2 ^ 63 - 1 /\ 0 <= e1 - elen /\ e1 <= en)
      by (destruct H8 as [_ ?]; auto).
    destruct Hx as [Hshx [Hen [Hen2 [He1 He2]]]].
    assert_PROP (field_compatible (tarray tuchar en) [] eb) as FCe by entailer!.
    assert (Peb: isptr eb) by (destruct FCe; auto).
    forward.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    replace (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val ps ob) (offset_val (k + ll - off) ob))
      with (Vlong (Int64.repr (ps - (k + ll - off)))) by (symmetry; apply (cp_sub_pp ob ps (k + ll - off)); auto).
    rewrite es_sub_l by auto.
    replace (e1 - (ps - (k + ll - off))) with (e1 - (off - (k + ll - ps))) by lia.
    assert (Hdl: 0 < off - (k + ll - ps) <= elen) by lia.
    set (dl := off - (k + ll - ps)) in *.
    forward. forward_if.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    { match goal with Ht: typed_true _ _ |- _ => rename Ht into Hge end.
      rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
      rewrite es_lt in Hge by rep_lia. apply es_bt, negb_true_iff, Z.ltb_ge in Hge.
      forward.
      rewrite (es_split3 shx en (e1 - dl) ml ec eb) by (auto; lia).
      rewrite (es_split3 sh (Zlength c) (k + ll) ml cA ob) by (auto; lia).
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
      forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) ml (sublist (e1 - dl) (e1 - dl + ml) ec)).
      { unfold mm_pre. cancel. }
      { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
      unfold mm_post. Intros.
      sep_apply (es_join3 shx en (e1 - dl) ml ec eb); auto; try lia.
      sep_apply (es_join_put sh (Zlength c) (k + ll) ml cA (sublist (e1 - dl) (e1 - dl + ml) ec) ob); auto; try lia.
      { rewrite Zlength_sublist; lia. }
      destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + ml) ec) (k + ll)) as [Hm1 Hm2];
        [lia | rewrite Zlength_sublist; lia | exact HmB |].
      rewrite Zlength_sublist in Hm2 by lia.
      destruct (xd_fin c cA (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)) k ps (k + ll) (k + (ll + ml)))
        as [HU HF]; auto; try lia.
      { replace (k + (ll + ml)) with (k + ll + (e1 - dl + ml - (e1 - dl))) by lia. exact Hm2. }
      specialize (HF ltac:(rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia)).
      es_clr.
      forward.
      Exists (ll + ml) (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)) (offset_val (li + ll) ob).
      entailer!.
      try (split; [solve [intros Hb Hx; apply esb_put_sub; [apply HbA, Hb | exact Hx]]|]).
      apply (es_post c cA _ k e li lim ll ml off ps (ExtSep shx eb _ ec e1 elen)); auto; try (simpl; lia).
      - intros p Hp Hn. rewrite ecl_Znth_put_out; [reflexivity | rewrite ?Zlength_sublist; lia ..].
      - intros HcA. apply (es_exactE c cA _ k li ll ml off ps (ExtSep shx eb _ ec e1 elen) ml); auto; try (simpl; lia). }
    match goal with Ht: typed_false _ _ |- _ => rename Ht into Hge end.
    rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
    rewrite es_lt in Hge by rep_lia. apply es_bf, negb_false_iff, Z.ltb_lt in Hge.
    forward.
    { entailer!. try apply prop_right. apply cp_sameblock; auto. }
    replace (force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val e1 eb) (offset_val (e1 - dl) eb)))
      with (Vlong (Int64.repr dl))
      by (symmetry; etransitivity; [apply (cp_sub_pp eb e1 (e1 - dl)); auto | do 2 f_equal; lia]).
    rewrite (es_split3 shx en (e1 - dl) dl ec eb) by (auto; lia).
    rewrite (es_split3 sh (Zlength c) (k + ll) dl cA ob) by (auto; lia).
    assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
    forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) dl (sublist (e1 - dl) (e1 - dl + dl) ec)).
    { unfold mm_pre. cancel. }
    { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
    unfold mm_post. Intros.
    sep_apply (es_join3 shx en (e1 - dl) dl ec eb); auto; try lia.
    sep_apply (es_join_put sh (Zlength c) (k + ll) dl cA (sublist (e1 - dl) (e1 - dl + dl) ec) ob); auto; try lia.
    { rewrite Zlength_sublist; lia. }
    forward. rewrite es_add by auto.
    forward. forward. rewrite sub64_repr.
    forward. forward.
    destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + dl) ec) (k + ll)) as [Hm1 Hm2];
      [lia | rewrite Zlength_sublist; lia | exact HmB |].
    rewrite Zlength_sublist in Hm2 by lia. replace (k + ll + (e1 - dl + dl - (e1 - dl))) with (k + ll + dl) in Hm2 by lia.
    remember (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)) as c2 eqn:Hc2e.
    assert (Hc2: Zlength c2 = Zlength c) by (subst c2; rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia).
    assert (Hc2f: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA).
    { intros p Hp Hn. subst c2. rewrite ecl_Znth_put_out; [reflexivity | rewrite ?Zlength_sublist; lia ..]. }
    assert (Hu2: xd_ub c c2) by (apply (xd_ub_trans c cA c2); auto).
    assert (Hd2p: xd_rng c2 ps (k + ll + dl)).
    { apply (xd_rng_app _ _ (k + ll)); [| exact Hm2]. apply (xd_rng_ub cA); try lia; auto. }
    assert (HC: copy_src_def c2 ps (k + ll + dl) (ml - dl)) by (apply (xd_csd c2 ps); auto; lia).
    forward_call (gv, true, sh, ob, c2, li + ll - WILDCOPY_OVERLENGTH, ps, k + ll + dl, Tsh, nullval, @nil val, ml - dl, 1).
    { entailer!. simpl. rewrite Hc2, !(es_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc2. cancel. }
    { rewrite Hc2. unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH in *.
      repeat split; first [lia | rep_lia | (intros; lia) | (intros Hc; discriminate) | exact HC]. }
    Intros c'.
    match goal with H: forall q, 0 <= q < Zlength c2 -> Znth q c' = Znth q c2 \/ _ |- _ => rename H into Hu3 end.
    destruct (xd_fin c c2 c' k ps (k + ll + dl) (k + (ll + ml))) as [HU HF]; auto; try lia.
    { replace (k + (ll + ml)) with (k + ll + dl + (ml - dl)) by lia.
      apply (xd_rng_eq c' (listcopy c2 ps (k + ll + dl) (Z.to_nat (ml - dl)))); try lia;
        [rewrite Zlength_listcopy; lia | exact H16 |].
      apply xd_listcopy; try lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      apply (xd_rng_sub _ ps (k + ll + dl)); auto; lia. }
    rewrite Hc2 in *. specialize (HF H15).
    es_clr.
    forward.
    Exists (ll + ml) c' (offset_val (li + ll) ob). entailer!.
    try (split; [solve [intros Hb Hx; apply H18; try rewrite Hc2e; apply esb_put_sub; [apply HbA, Hb | exact Hx]]|]).
    apply (es_post c cA c' k e li lim ll ml off ps (ExtSep shx eb _ ec e1 elen)); auto; try (simpl; lia).
    + intros p Hp Hn. rewrite H17 by (unfold WILDCOPY_OVERLENGTH in *; lia). apply Hc2f; lia.
    + intros HcA. apply (es_exactE c cA c' k li ll ml off ps (ExtSep shx eb _ ec e1 elen) dl); auto; try (simpl; lia).
      * intros p Hp. simpl ext_end; simpl ext_src. rewrite H17 by (unfold WILDCOPY_OVERLENGTH in *; lia).
        try rewrite Hc2e; reflexivity.
      * intros _. replace (k + ll + ml) with (k + ll + dl + (ml - dl)) by lia. rewrite H16. try rewrite Hc2e; reflexivity.
Qed.

(* ---------- ZSTD_execSequence ---------- *)
Lemma xf_add_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a + n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_int64. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite ptrofs_add_repr. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|].
  unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus.
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma xf_sub_pi {cs: compspecs} (p: val) (a k: Z) : isptr p -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val a p) (Vint (Int.repr k))) =
  offset_val (a - k) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_sub_repr. f_equal. lia.
Qed.

Lemma xf_sub_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  unfold Ptrofs.of_int64. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite ptrofs_add_repr, ptrofs_add_repr, Ptrofs.sub_add_opp.
  unfold Ptrofs.neg. rewrite ptrofs_add_repr.
  apply Ptrofs.eqm_samerepr. replace (Ptrofs.unsigned i + (a - n)) with (Ptrofs.unsigned i + a + - n) by lia.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|]. apply Ptrofs.eqm_neg.
  eapply Ptrofs.eqm_trans; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
  unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus. apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma xf_sub_pl' {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_sub_pl tuchar (offset_val a p) (Vlong (Int64.repr n))) = offset_val (a - n) p.
Proof. intros Hp. exact (xf_sub_pl p a n Hp). Qed.

Lemma xf_lt_diff (p: val) (a b n: Z) : isptr p ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.lt n1 n2))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vlong (Int64.repr n)) with
  | Some v' => v' | None => Vundef end =
  Vint (if Int64.lt (Int64.repr (a - b)) (Int64.repr n) then Int.one else Int.zero).
Proof.
  intros Hp. rewrite cp_sub_pp by auto. simpl. destruct (Int64.lt _ _); reflexivity.
Qed.

(* the C's "litLimit - litPtr < ll": false gives ll <= lim - li also when lim - li is beyond the signed range *)
Lemma xf_lt_false (d n: Z) : 0 <= d <= Int64.max_unsigned -> 0 <= n <= Int64.max_signed ->
  Int64.lt (Int64.repr d) (Int64.repr n) = false -> n <= d.
Proof.
  intros Hd Hn E. unfold Int64.lt in E. rewrite (Int64.signed_repr n) in E by rep_lia.
  destruct (zlt (Int64.signed (Int64.repr d)) n); [discriminate|].
  destruct (zle d Int64.max_signed).
  - rewrite Int64.signed_repr in g by rep_lia. lia.
  - lia.
Qed.

Lemma xf_cast_lt (p: val) (a b n: Z) : isptr p ->
  Int64.min_signed <= a - b <= Int64.max_signed -> 0 <= n <= Int64.max_signed ->
  force_val (sem_cast tint tbool
    (eval_binop Olt tlong tlong
       (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p))
       (eval_cast tulong tlong (Vlong (Int64.repr n))))) =
  Vint (if zlt (a - b) n then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. destruct p; try contradiction.
  unfold eval_binop.
  replace (force_val2 (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar))
             (offset_val a (Vptr b0 i)) (offset_val b (Vptr b0 i)))
    with (Vlong (Int64.repr (a - b))) by (rewrite <- (cp_sub_pp (Vptr b0 i) a b I); reflexivity).
  simpl. unfold Int64.lt. rewrite !Int64.signed_repr by rep_lia.
  destruct (zlt (a - b) n); reflexivity.
Qed.

Lemma xf_Zlength_copied (cs cd: list val) (is id n: Z) :
  0 <= n -> 0 <= is -> is + n <= Zlength cs -> 0 <= id -> id + n <= Zlength cd ->
  Zlength (copied cs cd is id n) = Zlength cd.
Proof. intros. unfold copied. rewrite !Zlength_app, !Zlength_sublist by lia. lia. Qed.

Lemma xf_rejoin (sh: share) (p: val) (l: list val) (d: Z) :
  field_compatible (tarray tuchar (Zlength l)) [] p -> 0 <= d <= Zlength l ->
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l))) (sublist d (Zlength l) l) (offset_val d p) |--
  data_at sh (tarray tuchar (Zlength l)) l p.
Proof. intros. rewrite <- tuchar_split by auto. apply derives_refl. Qed.

Lemma xf_join (sh: share) (p: val) (N i: Z) (a b b': list val) :
  field_compatible (tarray tuchar N) [] p -> Zlength a = i -> Zlength b' = Zlength b -> Zlength a + Zlength b = N ->
  data_at sh (tarray tuchar (Zlength a)) a p * data_at sh (tarray tuchar (Zlength b)) b' (offset_val i p) |--
  data_at sh (tarray tuchar N) (a ++ b') p.
Proof. intros. subst i. rewrite <- H1. rewrite (tuchar_join sh p N a b') by (auto; lia). apply derives_refl. Qed.

Lemma xf_join2 (sh: share) (p: val) (N i j: Z) (a b: list val) :
  field_compatible (tarray tuchar N) [] p -> Zlength a = i -> Zlength b = j -> i + j = N ->
  data_at sh (tarray tuchar i) a p * data_at sh (tarray tuchar j) b (offset_val i p) |--
  data_at sh (tarray tuchar N) (a ++ b) p.
Proof. intros. subst i j. rewrite (tuchar_join sh p N a b) by (auto; lia). apply derives_refl. Qed.

Lemma xf_lit16 (c cl: list val) (k li ll: Z) :
  0 <= k -> 0 <= li -> 0 <= ll <= 16 -> k + 16 <= Zlength c -> li + 16 <= Zlength cl ->
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) ->
    Znth p (copied cl c li k 16) = Znth p (put c k (sublist li (li + ll) cl)).
Proof.
  intros. unfold copied, put. rewrite Zlength_sublist by lia.
  list_solve.
Qed.

Lemma xf_lit32 (c cl g: list val) (k li ll: Z) :
  0 <= k -> 0 <= li -> 16 < ll -> k + ll + 32 <= Zlength c -> li + ll + 32 <= Zlength cl -> Zlength g = 32 ->
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) ->
    Znth p (sublist 0 (k + 16) (copied cl c li k 16) ++
            (sublist 0 (ll - 16) (sublist (li + 16) (Zlength cl) cl) ++ g ++
             sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength c) (copied cl c li k 16)))
               (sublist (k + 16) (Zlength c) (copied cl c li k 16))))
    = Znth p (put c k (sublist li (li + ll) cl)).
Proof.
  intros. unfold WILDCOPY_OVERLENGTH. unfold copied, put. list_solve.
Qed.

(* the array after the literal copy: put c k Lv, except the slack [k + ll, k + ll + 32) *)
Definition xf_lit_ok (c cA: list val) (k ll: Z) (Lv: list val) : Prop :=
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) -> Znth p cA = Znth p (put c k Lv).

Lemma xf_litin (c A': list val) (k li ll: Z) :
  0 <= k -> 0 <= ll -> k + ll + 32 <= li -> li + ll <= Zlength c -> Zlength A' = li ->
  xf_lit_ok (sublist 0 li c) A' k ll (sublist 0 ll (sublist li (Zlength c) c)) ->
  xf_lit_ok c (A' ++ sublist li (Zlength c) c) k ll (sublist li (li + ll) c).
Proof.
  unfold xf_lit_ok. intros Hk Hll Hli Hli2 HA H p Hp Hq.
  destruct (zlt p li).
  - rewrite Znth_app1 by lia. rewrite H by (try rewrite Zlength_sublist; lia). unfold put.
    rewrite !Zlength_sublist by (try rewrite Zlength_sublist; lia). list_solve.
  - rewrite Znth_app2 by lia. unfold put. rewrite !Zlength_sublist by lia. list_solve.
Qed.

(* ---- the match copy (pure parts) ----
   x0 = k + ll; the match continues at di = x0 + d (d = 0, or d = dl after the extDict part) from
   si = di - off; xf_J: any final array that keeps c2 below di and holds the forward copy on [di, x0 + ml)
   is exec_c there *)
Definition xf_J (c c2: list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) (d: Z) : Prop :=
  forall c', Zlength c' = Zlength c ->
    (forall p, k <= p < k + ll + d -> Znth p c' = Znth p c2) ->
    sublist (k + ll + d) (k + ll + ml) c' =
      sublist (k + ll + d) (k + ll + ml) (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat (ml - d))) ->
    ext_read_ok x k e ll ml off ps ->
    sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x).

(* the match lies in the prefix *)
Lemma xf_J_prefix (c cA: list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= off <= k + ll - ps -> 1 <= ml ->
  k + ll + ml + 32 <= Zlength c -> Zlength cA = Zlength c -> xf_lit_ok c cA k ll Lv ->
  xf_J c cA k e ll ml off ps x Lv 0.
Proof.
  intros HL Hps Hll Hoff Hml HN HcA Hlit c' Hc' Hag Hsub _.
  rewrite Z.add_0_r in Hag, Hsub. replace (Z.to_nat (ml - 0)) with (Z.to_nat ml) in Hsub by (f_equal; lia).
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_prefix c cA c' k ps ml off (k + ll) Lv x); try lia; auto.
  intros p Hp. apply Hlit; lia.
Qed.

(* dl < ml bytes from the extDict were moved to [x0, x0 + dl) (c2), the rest follows from the prefix *)
Lemma xf_J_ext (c cA c2: list val) (k e ll ml off ps dl: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml + 32 <= e -> e <= Zlength c ->
  dl = off - (k + ll - ps) -> 0 < dl < ml -> dl <= ext_len x -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> xf_lit_ok c cA k ll Lv -> Zlength c2 = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA) ->
  sublist (k + ll) (k + ll + dl) c2 = sublist (ext_end x - dl) (ext_end x) (ext_src cA x) ->
  xf_J c c2 k e ll ml off ps x Lv dl.
Proof.
  intros HL Hps Hll Hml He HeN Hdl Hdl1 Hdl2 Hx HcA Hlit Hc2 Hc2o Hc2s c' Hc' Hag Hsub Hrd.
  assert (Hrd2 := exec_ext_read c cA k e ll ml off ps (k + ll + 32) dl Lv x HL Hdl ltac:(lia) ltac:(lia)
                    ltac:(unfold WILDCOPY_OVERLENGTH; lia) ltac:(lia) HeN Hml Hx HcA Hlit Hrd).
  replace (Z.min ml dl) with dl in Hrd2 by lia.
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_ext c cA c2 c' k ps ml off (k + ll) dl dl Lv x).
  all: first [ lia | assumption
             | (intros p Hp; first [apply Hlit | apply Hc2o | apply Hag]; lia)
             | (replace (ext_end x - dl + dl) with (ext_end x) by lia; assumption)
             | (intros _; replace ps with (k + ll + dl - off) by lia; exact Hsub) ].
Qed.

(* the whole match comes from the extDict (ml <= dl): one memmove *)
Lemma xf_full_ext (c cA c': list val) (k e ll ml off ps dl: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml + 32 <= e -> e <= Zlength c ->
  dl = off - (k + ll - ps) -> 0 < dl -> ml <= dl -> dl <= ext_len x -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> xf_lit_ok c cA k ll Lv -> Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + ml) -> Znth p c' = Znth p cA) ->
  sublist (k + ll) (k + ll + ml) c' = sublist (ext_end x - dl) (ext_end x - dl + ml) (ext_src cA x) ->
  ext_read_ok x k e ll ml off ps ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x).
Proof.
  intros HL Hps Hll Hml He HeN Hdl Hdl1 Hdl2 Hdl3 Hx HcA Hlit Hc' Hc'o Hc's Hrd.
  assert (Hrd2 := exec_ext_read c cA k e ll ml off ps (k + ll + 32) dl Lv x HL Hdl ltac:(lia) ltac:(lia)
                    ltac:(unfold WILDCOPY_OVERLENGTH; lia) ltac:(lia) HeN Hml Hx HcA Hlit Hrd).
  replace (Z.min ml dl) with ml in Hrd2 by lia.
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_ext c cA c' c' k ps ml off (k + ll) dl ml Lv x).
  all: first [ lia | assumption | (intros; lia)
             | (intros p Hp; first [apply Hlit | apply Hc'o]; lia) | (intros; reflexivity) ].
Qed.

(* the wild copy of the match (off >= 16) *)
Lemma xf_wc_facts (c2 g: list val) (si di n: Z) :
  0 <= si < di -> 0 <= n -> di + n + 32 <= Zlength c2 -> Zlength g = 32 ->
  Zlength (wc_within_post c2 si di n g) = Zlength c2 /\
  (forall p, 0 <= p < Zlength c2 -> ~ (di <= p < di + n + 32) -> Znth p (wc_within_post c2 si di n g) = Znth p c2) /\
  sublist di (di + n) (wc_within_post c2 si di n g) = sublist di (di + n) (listcopy c2 si di (Z.to_nat n)).
Proof.
  intros Hs Hn Hd Hg.
  assert (HL: Zlength (listcopy c2 si di (Z.to_nat n)) = Zlength c2) by (apply Zlength_listcopy; lia).
  unfold wc_within_post, WILDCOPY_OVERLENGTH.
  split; [|split].
  - list_solve.
  - intros p Hp Hq. destruct (zlt p di).
    + rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
      rewrite Z.add_0_r. apply listcopy_suffix; lia.
    + rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      rewrite Znth_app2 by lia. rewrite Znth_sublist by lia. f_equal. lia.
  - list_solve.
Qed.

Lemma xf_oc8_K (off: Z) : 1 <= off < 16 ->
  8 <= oc8_off off /\ oc8_off off mod off = 0 /\ off <= oc8_off off <= 8 + off.
Proof.
  intros H.
  assert (off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7 \/ off = 8 \/
          off = 9 \/ off = 10 \/ off = 11 \/ off = 12 \/ off = 13 \/ off = 14 \/ off = 15) as E by lia.
  repeat destruct E as [E|E]; subst; compute; repeat split; congruence.
Qed.

Lemma xf_sub_sub (l: list val) (a b c: Z) : 0 <= a <= b -> b <= c -> c <= Zlength l ->
  sublist a b l = sublist a b (sublist 0 c l).
Proof. intros. rewrite sublist_sublist by lia. f_equal; lia. Qed.

(* overlapCopy8, then (n > 8) the wild copy at distance oc8_off off (off < 16) *)
Lemma xf_oc8_facts (c2 g: list val) (off di n: Z) :
  1 <= off < 16 -> 0 <= di - off -> 1 <= n -> di + n + 32 <= Zlength c2 -> Zlength g = 32 ->
  let c3 := listcopy c2 (di - off) di 8 in
  let c' := if n >? 8 then wc_within_post c3 (di + 8 - oc8_off off) (di + 8) (n - 8) g else c3 in
  Zlength c' = Zlength c2 /\
  (forall p, 0 <= p < Zlength c2 -> ~ (di <= p < di + n + 32) -> Znth p c' = Znth p c2) /\
  sublist di (di + n) c' = sublist di (di + n) (listcopy c2 (di - off) di (Z.to_nat n)).
Proof.
  intros Hoff Hdi Hn HN Hg c3 c'.
  destruct (xf_oc8_K off Hoff) as (HK1 & HK2 & HK3).
  assert (Ec3: c3 = listcopy c2 (di - off) di (Z.to_nat 8)) by reflexivity.
  assert (H3: Zlength c3 = Zlength c2) by (rewrite Ec3; apply Zlength_listcopy; lia).
  assert (Hpre: forall n0 E, 0 <= n0 <= E -> di + E <= Zlength c2 ->
            sublist di (di + n0) (listcopy c2 (di - off) di (Z.to_nat E)) =
            sublist di (di + n0) (listcopy c2 (di - off) di (Z.to_nat n0))).
  { intros n0 E ? ?. rewrite (xf_sub_sub (listcopy c2 (di - off) di (Z.to_nat E)) di (di + n0) (di + n0))
      by (rewrite ?Zlength_listcopy; lia).
    rewrite (xf_sub_sub (listcopy c2 (di - off) di (Z.to_nat n0)) di (di + n0) (di + n0))
      by (rewrite ?Zlength_listcopy; lia).
    rewrite listcopy_prefix by lia. reflexivity. }
  unfold c'. destruct (n >? 8) eqn:En.
  - apply Z.gtb_lt in En.
    destruct (xf_wc_facts c3 g (di + 8 - oc8_off off) (di + 8) (n - 8)) as (W1 & W2 & W3); try lia.
    assert (HR: listcopy c3 (di + 8 - oc8_off off) (di + 8) (Z.to_nat (n - 8)) =
                listcopy c2 (di - off) di (Z.to_nat (8 + (n - 8)))).
    { rewrite Ec3.
      rewrite <- lc_reoff with (si := di - off) (di := di) (a := 8) (K := oc8_off off) (m := n - 8); try lia.
      - reflexivity.
      - replace (di - (di - off)) with off by lia. auto. }
    replace (8 + (n - 8)) with n in HR by lia.
    split; [lia | split].
    + intros p Hp Hq. rewrite W2 by lia. rewrite Ec3. apply listcopy_suffix; lia.
    + apply Znth_eq_ext.
      { rewrite !Zlength_sublist; rewrite ?W1, ?H3, ?Zlength_listcopy; lia. }
      intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?W1, ?H3; lia).
      rewrite !Znth_sublist by (rewrite ?W1, ?H3, ?Zlength_listcopy; lia).
      destruct (zlt i 8).
      * rewrite W2 by lia. rewrite Ec3.
        assert (E1 := Hpre 8 n ltac:(lia) ltac:(lia)).
        assert (E2: Znth i (sublist di (di + 8) (listcopy c2 (di - off) di (Z.to_nat n))) =
                    Znth i (sublist di (di + 8) (listcopy c2 (di - off) di (Z.to_nat 8)))) by (rewrite E1; auto).
        rewrite !Znth_sublist in E2 by (rewrite ?Zlength_listcopy; lia). auto.
      * assert (E3: Znth (i - 8) (sublist (di + 8) (di + 8 + (n - 8)) (wc_within_post c3 (di + 8 - oc8_off off) (di + 8) (n - 8) g)) =
                    Znth (i - 8) (sublist (di + 8) (di + 8 + (n - 8)) (listcopy c3 (di + 8 - oc8_off off) (di + 8) (Z.to_nat (n - 8)))))
          by (rewrite W3; auto).
        rewrite HR in E3. rewrite !Znth_sublist in E3 by (rewrite ?W1, ?H3, ?Zlength_listcopy; lia).
        replace (i - 8 + (di + 8)) with (i + di) in E3 by lia. auto.
  - rewrite Z.gtb_ltb in En. apply Z.ltb_ge in En. split; [auto | split].
    + intros p Hp Hq. rewrite Ec3. apply listcopy_suffix; lia.
    + rewrite Ec3. apply Hpre; lia.
Qed.

(* the success post from exactness: the bytes are defined when everything read is *)
Lemma xf_post (c c': list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 1 <= ml -> 1 <= off <= k + ll - ps + ext_len x ->
  k + ll + ml <= Zlength c -> exec_ext_ok x c -> Zlength c' = Zlength c ->
  (ext_read_ok x k e ll ml off ps ->
     sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x)) ->
  ext_read_ok x k e ll ml off ps ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x) /\
  (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val Lv -> ext_def x c ->
   Forall is_byte_val (sublist k (k + (ll + ml)) c')).
Proof.
  intros HL Hps Hml Hoff HN Hx Hc' Heq Hrd. specialize (Heq Hrd). split; [exact Heq|].
  intros B1 B2 B3. rewrite Heq. subst ll.
  replace (k + (Zlength Lv + ml)) with (k + Zlength Lv + ml) by lia.
  apply exec_c_bytes; auto; lia.
Qed.

(* for (;;break) { c } rest (RETURN_ERROR_IF, DEBUGLOG): c, then rest from Q *)
Lemma xf_loop_seq {Espec: OracleKind} {cs: compspecs} Delta (P Q: environ -> mpred) c rest R :
  semax Delta P c (loop1_ret_assert Q (overridePost Q R)) -> semax Delta Q rest R ->
  semax Delta P (Ssequence (Sloop c Sbreak) rest) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [|exact H2].
  apply semax_loop with Q; [exact H1|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

(* for (;;break) {} : a no-op *)
Lemma xf_skipbreak_seq {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H. apply xf_loop_seq with P; [|exact H].
  eapply semax_post; [| | | | apply semax_skip].
  all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
  - intros rho; simpl; apply andp_left2, derives_refl.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

(* (ptr_a - ptr_b) cast to size_t, compared with a size_t n by > (RETURN_ERROR_IF) *)
Lemma xf_gt_diff (p: val) (a b n: Z) : isptr p -> 0 <= a - b <= Int64.max_unsigned -> 0 <= n <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1))) sem_cast_pointer sem_cast_pointer
      (Vlong (Int64.repr n)) (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) with
  | Some v' => v' | None => Vundef end = Vint (if zlt (a - b) n then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. rewrite cp_sub_pp by auto. simpl. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia. destruct (zlt (a - b) n); reflexivity.
Qed.

(* the statements before RETURN_ERROR_IF's return *)
Ltac xf_if0_loop :=
  match goal with |- semax _ ?P _ _ => apply (xf_loop_seq _ P P); [forward_if; [exfalso; auto | forward; apply ENTAIL_refl] | ] end.
Ltac xf_err_prefix := apply xf_skipbreak_seq; xf_if0_loop; apply xf_skipbreak_seq; apply xf_skipbreak_seq.

(* the PROP part of an error return (-n cast to size_t) *)
Lemma xf_err_ret (n: Z) (b: bool) (P: Prop) : 0 < n < 120 -> b = true ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = false -> P) /\ Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn ->. unfold err_code, is_error_code.
  split; [rep_lia|]. split; [apply Z.ltb_lt; lia|]. split; [intros E; apply Z.ltb_ge in E; lia|].
  f_equal. apply cp_repr_eqm. replace (2 ^ 64 - n) with (- n + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* the same with the error clause unchanged_outside /\ dec_err (RETURN_ERROR constants are never 80, 82) *)
Lemma xf_err_ret2 (n: Z) (b: bool) (U P Q: Prop) : 0 < n < 120 -> n <> 80 -> n <> 82 -> b = true -> U ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = true -> U /\ dec_err (err_code n)) /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn H80 H82 Hb HU. destruct (xf_err_ret n b P Hn Hb) as (A & B & C & D).
  split; [auto | split; [auto | split; [| split; [auto | split; [intros E; congruence | auto]]]]].
  intros _. split; [auto|].
  unfold dec_err, is_error_code, err_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

(* after the literal copy nothing outside [k, hi) changed *)
Lemma xf_lit_unch (c cA: list val) (k ll hi: Z) (Lv: list val) :
  Zlength Lv = ll -> 0 <= k -> 0 <= ll -> k + ll + 32 <= hi -> k + ll <= Zlength c ->
  xf_lit_ok c cA k ll Lv -> unchanged_outside c cA k hi.
Proof.
  intros HL Hk Hll Hhi Hc H i Hi Hout. rewrite H by lia.
  unfold put. rewrite HL. list_solve.
Qed.

Lemma xf_add_ptr_long {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_add_ptr_long tuchar (offset_val a p) (Vlong (Int64.repr n))) = offset_val (a + n) p.
Proof. intros Hp. exact (xf_add_pl p a n Hp). Qed.

Lemma xf_ge_diff (p: val) (a b n: Z) : isptr p ->
  Int64.min_signed <= a - b <= Int64.max_signed -> Int64.min_signed <= n <= Int64.max_signed ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n1 n2)))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vlong (Int64.repr n)) with
  | Some v' => v' | None => Vundef end = Vint (if zlt (a - b) n then Int.zero else Int.one).
Proof.
  intros Hp Hab Hn. rewrite cp_sub_pp by auto. simpl. unfold Int64.lt.
  rewrite !Int64.signed_repr by lia. destruct (zlt (a - b) n); reflexivity.
Qed.

(* the success post *)
Lemma xf_noerr (ll ml: Z) : 0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> is_error_code (ll + ml) = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma xf_exec_err_false (k e li lim ll ml off ps elen: Z) :
  ll <= lim - li -> ll + ml <= e - k -> off <= k + ll - ps + elen -> exec_err k e li lim ll ml off ps elen = false.
Proof.
  intros. unfold exec_err. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Lemma xf_unch_trans (c c2 c': list val) (lo hi a b: Z) :
  unchanged_outside c c2 lo hi -> Zlength c2 = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (a <= p < b) -> Znth p c' = Znth p c2) -> lo <= a -> b <= hi ->
  unchanged_outside c c' lo hi.
Proof. intros H Hl H' ? ? i Hi Hout. rewrite H' by lia. apply H; lia. Qed.

Lemma xf_unch_min (c c': list val) (k e ll ml: Z) :
  unchanged_outside c c' k (k + ll + ml + 32) -> k + ll + ml + 32 <= e ->
  unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)).
Proof. intros. unfold WILDCOPY_OVERLENGTH. rewrite Z.min_r by lia. replace (k + (ll + ml) + 32) with (k + ll + ml + 32) by lia. auto. Qed.

Lemma xf_split3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + m)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + m - i) with m by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma xf_join_put (sh: share) (n i m: Z) (l v: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n -> Zlength v = m ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) v (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) (put l i v) p.
Proof.
  intros. rewrite (xf_split3 sh n i m (put l i v) p) by (auto; unfold put; list_solve).
  unfold put. subst m.
  replace (sublist 0 i (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with (sublist 0 i l) by list_solve.
  replace (sublist i (i + Zlength v) (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with v by list_solve.
  replace (sublist (i + Zlength v) n (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l))
    with (sublist (i + Zlength v) n l) by list_solve.
  apply derives_refl.
Qed.

Lemma xf_join3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) l p.
Proof. intros. rewrite (xf_split3 sh n i m l p) by auto. apply derives_refl. Qed.

Lemma xf_fa (n: Z) (p: val) (i: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i < n ->
  field_address (tarray tuchar n) (SUB i) p = offset_val i p.
Proof.
  intros. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

(* the success post from the array before the final copy (c2, xf_J) and the copy's frame and bytes *)
Lemma xf_final (c c2 c': list val) (k e li lim ll ml off ps d: Z) (x: ext_seg) (Lv: list val) (lp: val) :
  Zlength Lv = ll -> 0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> 0 <= ps <= k -> k + ll + ml + 32 <= e ->
  e <= Zlength c -> ll <= lim - li -> 1 <= off <= k + ll - ps + ext_len x -> exec_ext_ok x c ->
  0 <= d < ml -> Zlength c2 = Zlength c -> unchanged_outside c c2 k (k + ll + ml + 32) ->
  xf_J c c2 k e ll ml off ps x Lv d -> Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll + d <= p < k + ll + ml + 32) -> Znth p c' = Znth p c2) ->
  sublist (k + ll + d) (k + ll + ml) c' =
    sublist (k + ll + d) (k + ll + ml) (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat (ml - d))) ->
  is_error_code (ll + ml) = exec_err k e li lim ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false ->
     ll + ml = ll + ml /\ lp = lp /\
     unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) /\
     (ext_read_ok x k e ll ml off ps ->
        sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x) /\
        (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val Lv ->
         ext_def x c -> Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros HL Hll Hml Hps He HeN Hli Hoff Hx Hd Hc2 Hun2 HJ Hc' Hfr Hsub.
  rewrite (xf_noerr ll ml Hll Hml), (xf_exec_err_false k e li lim ll ml off ps (ext_len x)) by lia.
  split; [reflexivity|]. split; [discriminate|]. intros _.
  split; [reflexivity|]. split; [reflexivity|]. split.
  { apply xf_unch_min; [|lia]. intros i Hi Hn. rewrite Hfr by lia. apply Hun2; auto. }
  intros Hrd. apply (xf_post c c' k e ll ml off ps x Lv); auto; try lia.
  intros _. apply HJ; auto. intros p Hp. apply Hfr; lia.
Qed.

Ltac xf_sb := entailer!; try apply prop_right; try (apply cp_sameblock; auto).

Ltac xf_ur := match goal with H: context [Int64.unsigned (Int64.repr _)] |- _ =>
  rewrite !Int64.unsigned_repr in H by rep_lia end.

Ltac xf_tf := match goal with
  | H: typed_true _ _ |- _ => solve [inv H]
  | H: typed_false _ _ |- _ => solve [inv H]
  | H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity]
  | H: Int.one = _ |- _ => solve [inv H]
  | H: Int.repr 1 = _ |- _ => solve [inv H] end.

Ltac xf_fw := forward; repeat (first [rewrite xf_add_pl by auto | rewrite xf_sub_pl by auto |
                                      rewrite xf_sub_pl' by auto |
                                      rewrite xf_sub_pi by (auto; rep_lia)]).

(* ---------- bytes in, bytes out (ZSTD_execSequence) ---------- *)
Definition xfb_ok (c la: list val) (x: ext_seg) (c': list val) : Prop :=
  byte_cells c -> byte_cells la -> ext_bytes x -> byte_cells c'.

Lemma xfb_sublist (l: list val) (a b: Z) : byte_cells l -> byte_cells (sublist a b l).
Proof. apply Forall_sublist. Qed.

Lemma xfb_app (a b: list val) : byte_cells a -> byte_cells b -> byte_cells (a ++ b).
Proof. intros Ha Hb. apply Forall_app. split; auto. Qed.

Lemma xfb_copied (cs cd: list val) (is id k: Z) :
  byte_cells cs -> byte_cells cd -> byte_cells (copied cs cd is id k).
Proof. intros. unfold copied. repeat apply xfb_app; apply xfb_sublist; auto. Qed.

Lemma xfb_mm (c: list val) (N si di n: Z) : byte_cells c -> byte_cells (mm_result c N si di n).
Proof. intros. unfold mm_result. repeat apply xfb_app; apply xfb_sublist; auto. Qed.

Lemma xfb_put (c v: list val) (i: Z) : byte_cells c -> byte_cells v -> byte_cells (put c i v).
Proof. intros. unfold put. repeat apply xfb_app; try apply xfb_sublist; auto. Qed.

Lemma xfb_listcopy (c: list val) (si di: Z) (n: nat) :
  byte_cells c -> 0 <= si -> si + Z.of_nat n <= Zlength c -> byte_cells (listcopy c si di n).
Proof.
  revert c si di. induction n as [|m IH]; intros c si di Hc H1 H2; simpl; auto.
  rewrite Nat2Z.inj_succ in H2.
  apply IH; [| lia | rewrite Zlength_upd_Znth; lia].
  apply Forall_upd_Znth; auto. apply Forall_Znth; auto. lia.
Qed.

Lemma xfb_wc_g (c g: list val) (si di n: Z) (b: bool) :
  0 <= si -> 0 <= n -> si + n + WILDCOPY_OVERLENGTH <= Zlength c ->
  g = sublist (di + n) (di + n + WILDCOPY_OVERLENGTH) (listcopy c si di (Z.to_nat (wc_ext b n))) ->
  byte_cells c -> byte_cells g.
Proof.
  intros H1 H2 H3 Hg Hc. subst g. apply xfb_sublist, xfb_listcopy; auto.
  pose proof (wc_ext_bounds b n H2). rewrite Z2Nat.id by lia. unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

Lemma xfb_wc_dj (cs cd g: list val) (n: Z) :
  g = sublist n (n + WILDCOPY_OVERLENGTH) (sublist 0 (wc_ext false n) cs ++ sublist (wc_ext false n) (Zlength cd) cd) ->
  byte_cells cs -> byte_cells cd -> byte_cells g.
Proof. intros Hg Hs Hd. subst g. apply xfb_sublist, xfb_app; apply xfb_sublist; auto. Qed.

Lemma xfb_wc_within (c g: list val) (si di n: Z) :
  byte_cells c -> byte_cells g -> 0 <= si -> 0 <= n -> si + n <= Zlength c ->
  byte_cells (wc_within_post c si di n g).
Proof.
  intros. unfold wc_within_post. apply xfb_app; [| apply xfb_app; auto; apply xfb_sublist; auto].
  apply xfb_sublist, xfb_listcopy; auto. rewrite Z2Nat.id; lia.
Qed.

Ltac xfb_t := repeat first [ assumption | apply xfb_app | apply xfb_sublist | apply xfb_copied ].

(* ---------- exact stores (ZSTD_execSequence) ----------
   The fast path's stores as BlkSeqXMem's mirrors, carried through the proof: after the literals the array is
   xq_lit (ZSTD_copy16, then the disjoint wild copy of the rest when ll > 16); after the extDict part of the
   match (length d) the rest of the match is lprefix .. None from op = k + ll + d (xq_M). *)
Definition xq_lit (c cA: list val) (k: Z) (s: lsrc) (li ll: Z) : Prop :=
  cA = if ll >? 16 then lwild (lmove 16 c k s li) (k + 16) s (li + 16) (ll - 16) false else lmove 16 c k s li.

Lemma xq_lit_gt (c cA: list val) (k: Z) (s: lsrc) (li ll: Z) :
  16 < ll -> cA = lwild (lmove 16 c k s li) (k + 16) s (li + 16) (ll - 16) false -> xq_lit c cA k s li ll.
Proof. intros H ->. unfold xq_lit. replace (ll >? 16) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity. Qed.

Lemma xq_lit_le (c cA: list val) (k: Z) (s: lsrc) (li ll: Z) :
  ll <= 16 -> cA = lmove 16 c k s li -> xq_lit c cA k s li ll.
Proof.
  intros H ->. unfold xq_lit. replace (ll >? 16) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* the disjoint wild copy of the literals after the first 16, on the pieces after k + 16 / after li + 16 *)
Lemma xq_wild_dj_join (c1 cl R: list val) (N d a n: Z) :
  Zlength c1 = N -> 0 <= d -> 0 <= a -> 0 <= n -> d + n + 32 <= N -> a + n + 32 <= Zlength cl ->
  R = lwild (sublist d N c1) 0 (LS (sublist a (Zlength cl) cl)) 0 n false ->
  sublist 0 d c1 ++ R = lwild c1 d (LS cl) a n false.
Proof.
  intros HN Hd Ha Hn H1 H2 ->. destruct (xg_wc_ext n) as [_ W]; auto.
  rewrite !xg_wild_LS by (rewrite ?Zlength_sublist; lia).
  set (w := wc_ext false n) in *. unfold put. list_solve.
Qed.

(* the same with the literals in the output array after the piece [0, N) *)
Lemma xq_litin_join (c1 B R: list val) (N d n: Z) :
  Zlength c1 = N -> 0 <= d -> 0 <= n -> d + n + 32 <= N -> 16 + n + 32 <= Zlength B ->
  R = lwild (sublist d N c1) 0 (LS (sublist 16 (Zlength B) B)) 0 n false ->
  (sublist 0 d c1 ++ R) ++ B = lwild (c1 ++ B) d LW (N + 16) n false.
Proof.
  intros HN Hd Hn H1 H2 HR. rewrite (xq_wild_dj_join c1 B R N d 16 n) by (auto; lia).
  destruct (xg_wc_ext n) as [_ W]; auto.
  rewrite xg_wild_LS by lia. rewrite xg_wild_LW by (rewrite ?Zlength_app; lia).
  set (w := wc_ext false n) in *. unfold put. list_solve.
Qed.

Definition xq_M (x: ext_seg) (cA c2: list val) (k ll ml off ps d: Z) : Prop :=
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => lmatch ps (ps - ext_len x) (ext_end x) cA (k + ll) ml off None =
         lprefix c2 (k + ll + d) (k + ll + d - off) (ml - d) off None
  end.

Lemma xq_M_prefix (x: ext_seg) (cA: list val) (k ll ml off ps: Z) :
  off <= k + ll - ps -> xq_M x cA cA k ll ml off ps 0.
Proof.
  intros H. unfold xq_M. destruct x; auto; rewrite xg_lmatch_prefix by lia; rewrite !Z.add_0_r, !Z.sub_0_r; reflexivity.
Qed.

Lemma xq_M_span (cA: list val) (N e1 elen k ll ml off ps dl: Z) :
  Zlength cA = N -> dl = off - (k + ll - ps) -> 0 < dl < ml -> dl <= elen -> 0 <= e1 - elen -> e1 <= N ->
  0 <= k + ll -> k + ll + ml <= N ->
  xq_M (ExtIn e1 elen) cA (mm_result cA N (e1 - dl) (k + ll) dl) k ll ml off ps dl.
Proof.
  intros HN Hdl H1 H2 H3 H4 H5 H6. unfold xq_M. cbn [ext_len ext_end].
  rewrite xg_lmatch_span by lia. subst N. rewrite xg_mm by lia. subst dl. reflexivity.
Qed.

(* the whole match from the extDict *)
Lemma xq_full_ext (c cA: list val) (N e1 elen k e li lim ll ml off ps dl: Z) (s: lsrc) :
  xq_lit c cA k s li ll -> ll <= lim - li -> ll + ml <= e - 32 - k -> Zlength cA = N ->
  dl = off - (k + ll - ps) -> 0 < dl -> ml <= dl -> dl <= elen -> 0 <= e1 - elen -> e1 <= N ->
  0 <= k + ll -> k + ll + ml <= N -> 0 <= ml ->
  mm_result cA N (e1 - dl) (k + ll) ml = lexec ps (ps - elen) e1 e c k s li lim ll ml off.
Proof.
  intros XL H1 H2 HN Hdl. intros.
  rewrite xg_lexec_fast by (unfold WILDCOPY_OVERLENGTH; lia). unfold xq_lit in XL. rewrite <- XL.
  rewrite xg_lmatch_ext by lia. subst N. rewrite xg_mm by lia. subst dl. reflexivity.
Qed.

(* the end: the rest of the match as lprefix .. None *)
Lemma xq_final (c cA c2 c': list val) (x: ext_seg) (k e li lim ll ml off ps d: Z) (s: lsrc) :
  xq_lit c cA k s li ll -> ll <= lim - li -> ll + ml <= e - 32 - k -> xq_M x cA c2 k ll ml off ps d ->
  c' = lprefix c2 (k + ll + d) (k + ll + d - off) (ml - d) off None ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code (ll + ml) = false -> c' = lexec ps (ps - ext_len x) (ext_end x) e c k s li lim ll ml off
  end.
Proof.
  intros XL H1 H2 XM ->. unfold xq_M in XM. unfold xq_lit in XL.
  destruct x; auto; intros _; rewrite xg_lexec_fast by (unfold WILDCOPY_OVERLENGTH; lia);
    rewrite <- XL; symmetry; exact XM.
Qed.

(* an error return: the exact clause holds vacuously *)
Lemma xq_err_ret (n: Z) (b: bool) (U P Q R: Prop) (x: ext_seg) :
  0 < n < 120 -> n <> 80 -> n <> 82 -> b = true -> U ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = true -> U /\ dec_err (err_code n)) /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  match x with ExtSep _ _ _ _ _ _ => True | _ => is_error_code (err_code n) = false -> R end /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn H80 H82 Hb HU. destruct (xf_err_ret2 n b U P Q Hn H80 H82 Hb HU) as (A & B & C & D & E & F).
  refine (conj A (conj B (conj C (conj D (conj E (conj _ F)))))).
  destruct x; auto; intros Hf; congruence.
Qed.

Lemma xq_pre16 (c2 c': list val) (di si ml off: Z) :
  16 <= off -> c' = lwild c2 di LW si ml (0 =? OV_SRC_BEFORE_DST) -> c' = lprefix c2 di si ml off None.
Proof.
  intros H ->. unfold lprefix. replace (off >=? 16) with true by (symmetry; apply Z.geb_le; lia). reflexivity.
Qed.

Lemma xq_pre8 (c2 c3 c': list val) (di ml off: Z) :
  off < 16 -> 8 < ml -> lov8 c2 di (di - off) off = pair (pair c3 (di + 8)) (di + 8 - oc8_off off) ->
  c' = lwild c3 (di + 8) LW (di + 8 - oc8_off off) (ml - 8) (1 =? OV_SRC_BEFORE_DST) ->
  c' = lprefix c2 di (di - off) ml off None.
Proof.
  intros H1 H2 Hov ->. unfold lprefix.
  replace (off >=? 16) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  rewrite Hov. replace (ml >? 8) with true by (symmetry; apply Z.gtb_lt; lia). reflexivity.
Qed.

Lemma xq_pre8s (c2 c3: list val) (di ml off: Z) :
  off < 16 -> ml <= 8 -> lov8 c2 di (di - off) off = pair (pair c3 (di + 8)) (di + 8 - oc8_off off) ->
  c3 = lprefix c2 di (di - off) ml off None.
Proof.
  intros H1 H2 Hov. unfold lprefix.
  replace (off >=? 16) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  rewrite Hov. replace (ml >? 8) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma body_ZSTD_execSequence :
  semax_body Vprog EXEC_G f_ZSTD_execSequence ZSTD_execSequence_spec.
Proof.
  start_function.
  rename H8 into Xdh, H9 into Xdl, H10 into Xde.
  assert (Hoff1: 1 <= off) by lia.
  forward.
  forward_call (shq, sp, ll, ml, off, Tsh, v_sequence).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] ob) as FCc by entailer!.
  assert_PROP (isptr (lit_base ls ob)) as Plb by (destruct ls; simpl lit_base; simpl lit_res; entailer!).
  assert (Pob: isptr ob) by (destruct FCc; auto).
  unfold seqrep. 
  forward. forward. forward. rewrite xf_add_pl by auto.
  assert_PROP (Zlength (lit_arr ls c) <= Ptrofs.max_unsigned) as Hla.
  { destruct ls; simpl lit_res; simpl lit_arr.
    - entailer!. match goal with Hf: field_compatible (Tarray tuchar (Zlength cl) _) _ lb |- _ =>
        destruct Hf as (Hp & _ & Hs & _) end.
      destruct lb; try contradiction. simpl in Hs. pose proof (Ptrofs.unsigned_range i). rep_lia.
    - entailer!. }
  assert (Hlim: 0 <= li <= lim /\ lim + 32 <= Zlength (lit_arr ls c))
    by (unfold WILDCOPY_OVERLENGTH in H5; destruct ls; simpl; [tauto | lia]).
  forward. forward. forward.
  replace (Int64.add (Int64.repr ll) (Int64.repr ml)) with (Int64.repr (ll + ml))
    by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
  do 8 xf_fw.
  forward. forward.
  set (slow1 := Int64.lt (Int64.repr (lim - li)) (Int64.repr ll)).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'2 (Vint (if orb slow1 (e - 32 - k <? ll + ml)%Z
                                                   then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { apply prop_right, cp_sameblock; auto. }
  { rewrite xf_lt_diff in H8 by auto. forward. entailer!.
    fold slow1 in H8. destruct slow1; [reflexivity | inv H8]. }
  { rewrite xf_lt_diff in H8 by auto. fold slow1 in H8. destruct slow1 eqn:Es1; [inv H8|].
    forward. forward.
    { entailer!. all: apply prop_right, cp_sameblock; auto. }
    entailer!. rewrite cp_sub_pp by auto. simpl.
    unfold Int64.lt. rewrite !Int64.signed_repr by rep_lia.
    destruct (zlt (e - 32 - k) (ll + ml)) as [Hz|Hz].
    - rewrite (proj2 (Z.ltb_lt _ _) Hz). reflexivity.
    - replace (e - 32 - k <? ll + ml) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  set (slow := orb slow1 (e - 32 - k <? ll + ml)%Z).
  forward_if (temp _t'3 (Vint (if slow then Int.one else Int.zero))).
  { destruct slow; [| xf_tf]. forward. entailer!. }
  { destruct slow; [xf_tf |]. forward_call tt.
    forward_if.
    { xf_tf. }
    forward. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((slow = false) :: P) (LOCALx Q (SEPx R))) end.
  { (* the slow path: ZSTD_execSequenceEnd, under its precondition (the slow condition) *)
    assert (Hs: slow = true) by (destruct slow; [reflexivity | xf_tf]).
    assert (Hlimb: lim - li <= Int64.max_signed) by lia.
    assert (Hslow: orb (lim - li <? ll) (e - WILDCOPY_OVERLENGTH - k <? ll + ml) = true).
    { unfold slow, slow1 in Hs. unfold Int64.lt in Hs. rewrite !Int64.signed_repr in Hs by rep_lia.
      unfold WILDCOPY_OVERLENGTH. destruct (zlt (lim - li) ll) as [Hz|Hz].
      - rewrite (proj2 (Z.ltb_lt _ _) Hz). reflexivity.
      - rewrite (proj2 (Z.ltb_ge _ _)) by lia. exact Hs. }
    forward.
    forward_call (gv, sh, ob, c, k, e, Tsh, v_sequence, ll, ml, off, shp, plp, ls, li, lim, ps, x, dE).
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
    forward. Exists r c' lp. entailer!. }
  { destruct slow eqn:Es; [xf_tf|]. forward. entailer!. }
  Intros. rename H8 into Eslow.
  assert (Hfast1: ll <= lim - li /\ ll + ml <= e - 32 - k).
  { unfold slow, slow1 in Eslow. apply orb_false_iff in Eslow. destruct Eslow as [E1 E2].
    apply xf_lt_false in E1; [| rep_lia | rep_lia]. apply Z.ltb_ge in E2. lia. }
  rewrite Eslow. clear Eslow. clear slow slow1.
  (* the literals: [k, k + ll) := Lv, slack [k + ll, k + ll + 32) *)
  set (Lv := sublist li (li + ll) (lit_arr ls c)).
  unfold MORE_COMMANDS, abbreviate. apply <- seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx _))) _ _ =>
    apply semax_seq' with (P' := EX cA: list val,
      PROPx ((Zlength cA = Zlength c) ::
             xf_lit_ok c cA k ll Lv :: xfb_ok c (lit_arr ls c) x cA :: xd_ub c cA ::
             xq_lit c cA k (ls_l ls) li ll :: P)
      (LOCALx L
      (SEPx [data_at shq t_seq (seqrep ll ml off) sp; data_at Tsh t_seq (seqrep ll ml off) v_sequence;
             data_at Tsh (tptr tuchar) (offset_val (k + ll - off) ob) v_match;
             data_at Tsh (tptr tuchar) (offset_val k ob) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) cA ob;
             data_at shp (tptr tuchar) (offset_val li (lit_base ls ob)) plp; lit_res ls; ext_res x])))
  end.
  { destruct ls as [shl lb cl|]; simpl lit_base in *; simpl lit_res; simpl lit_arr in *.
    - (* LitSep *)
      destruct H5 as (Hshl & Hli & Hlimcl). unfold WILDCOPY_OVERLENGTH in Hlimcl.
      forward. forward.
      assert (HL16: Forall is_byte_val (sublist li (li + 16) cl))
        by (apply (xd_sub cl li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia).
      forward_call (shl, lb, cl, li, sh, ob, c, k).
      { unfold copy_pre. refine (conj _ (conj _ _)); [auto | auto |]. repeat split; try lia. apply xd_bv. exact HL16. }
      assert (Hc1: Zlength (copied cl c li k 16) = Zlength c) by (apply xf_Zlength_copied; lia).
      destruct (xd_copied cl c li k 16) as [Hc1u Hc1r]; try lia; [exact HL16 |].
      forward. forward_if.
      + rewrite !Int64.unsigned_repr in H5 by rep_lia.
        forward. forward. forward.
        assert_PROP (field_compatible (tarray tuchar (Zlength cl)) [] lb) as FCl by entailer!.
        rewrite (tuchar_split shl lb cl (li + 16)) by (auto; lia).
        sep_apply (tuchar_split_N sh ob (Zlength c) (copied cl c li k 16) (k + 16) Hc1 FCc ltac:(lia)).
        assert (HFs: Forall is_byte_val (sublist 0 (ll - 16 + WILDCOPY_OVERLENGTH) (sublist (li + 16) (Zlength cl) cl))).
        { rewrite sublist_sublist by (unfold WILDCOPY_OVERLENGTH in *; lia).
          apply (xd_sub cl li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia. }
        forward_call (gv, false, sh, ob, c, 0, 0, shl, offset_val (li + 16) lb, sublist (li + 16) (Zlength cl) cl,
                      sh, offset_val (k + 16) ob,
                      sublist (k + 16) (Zlength (copied cl c li k 16)) (copied cl c li k 16), ll - 16, 0).
        { cancel. }
        { split; [auto | split; [auto | split; [reflexivity |]]].
          rewrite Hc1, !Zlength_sublist by lia. unfold WILDCOPY_OVERLENGTH; lia. }
        Intros g.
        match goal with H: _ = lwild _ _ _ _ _ _ |- _ => rename H into Hx end.
        match goal with H: g = _ |- _ =>
          assert (Hgu := xd_wc_dj (sublist (li + 16) (Zlength cl) cl)
                           (sublist (k + 16) (Zlength (copied cl c li k 16)) (copied cl c li k 16)) g (ll - 16)
                           ltac:(lia) ltac:(rewrite Zlength_sublist by lia; unfold WILDCOPY_OVERLENGTH; lia)
                           ltac:(rewrite Zlength_sublist by (rewrite Hc1; lia); rewrite Hc1; unfold WILDCOPY_OVERLENGTH; lia)
                           HFs H) end.
        match goal with H: g = _ |- _ => pose proof (xfb_wc_dj _ _ _ _ H) as Hgb; clear H end. rewrite Hc1 in *.
        sep_apply (xf_rejoin shl lb cl (li + 16) FCl ltac:(lia)).
        sep_apply (xf_join sh ob (Zlength c) (k + 16) (sublist 0 (k + 16) (copied cl c li k 16))
                     (sublist (k + 16) (Zlength c) (copied cl c li k 16))
                     (sublist 0 (ll - 16) (sublist (li + 16) (Zlength cl) cl) ++ g ++
                      sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength c) (copied cl c li k 16)))
                        (sublist (k + 16) (Zlength c) (copied cl c li k 16))) FCc).
        { list_solve. }
        { unfold WILDCOPY_OVERLENGTH in *. list_solve. }
        { list_solve. }
        set (cA := sublist 0 (k + 16) (copied cl c li k 16) ++
                (sublist 0 (ll - 16) (sublist (li + 16) (Zlength cl) cl) ++ g ++
                 sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength c) (copied cl c li k 16)))
                   (sublist (k + 16) (Zlength c) (copied cl c li k 16)))).
        assert (HA1: Zlength cA = Zlength c) by (unfold cA, WILDCOPY_OVERLENGTH in *; list_solve).
        assert (XL: xq_lit c cA k (LS cl) li ll).
        { apply xq_lit_gt; [lia|]. rewrite <- xg_copied by lia. unfold cA.
          apply (xq_wild_dj_join _ _ _ (Zlength c)); auto; lia. }
        assert (HA2: xf_lit_ok c cA k ll Lv) by (intros p ? ?; apply xf_lit32; unfold WILDCOPY_OVERLENGTH in *; lia).
        assert (HB: xfb_ok c cl x cA)
          by (intros Hc Hl _; assert (byte_cells g) by (apply Hgb; xfb_t); unfold cA; xfb_t).
        assert (HuA: xd_ub c cA).
        { apply (xd_ub_trans c (copied cl c li k 16)); [exact Hc1 | exact Hc1u |].
          unfold cA. apply (xd_ub_join_r' _ _ (Zlength c)); [exact Hc1 | lia | | exact Hgu].
          unfold WILDCOPY_OVERLENGTH in *. list_solve. }
        clearbody cA. Exists cA. unfold seqrep. entailer!.
      + rewrite !Int64.unsigned_repr in H5 by rep_lia. forward.
        assert (HA2: xf_lit_ok c (copied cl c li k 16) k ll Lv) by (intros p ? ?; apply xf_lit16; lia).
        assert (HB: xfb_ok c cl x (copied cl c li k 16)) by (intros ? ? _; xfb_t).
        assert (HuA: xd_ub c (copied cl c li k 16)) by exact Hc1u.
        assert (XL: xq_lit c (copied cl c li k 16) k (LS cl) li ll)
          by (apply xq_lit_le; [lia | apply xg_copied; lia]).
        Exists (copied cl c li k 16). unfold seqrep. entailer!.
    - (* LitIn: the literals lie in c after oend; split c at li *)
      destruct H5 as (Hli & Hlimc). unfold WILDCOPY_OVERLENGTH in Hlimc.
      forward. forward.
      sep_apply (tuchar_split_N sh ob (Zlength c) c li eq_refl FCc ltac:(lia)).
      assert (HL16: Forall is_byte_val (sublist 0 16 (sublist li (Zlength c) c))).
      { rewrite sublist_sublist by lia. apply (xd_sub c li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia. }
      forward_call (sh, offset_val li ob, sublist li (Zlength c) c, 0, sh, ob, sublist 0 li c, k).
      { cancel. }
      { unfold copy_pre. refine (conj _ (conj _ _)); [apply writable_readable_share; auto | auto |].
        rewrite !Zlength_sublist by lia. repeat split; try lia. apply xd_bv. exact HL16. }
      assert (HAl: Zlength (sublist 0 li c) = li) by (rewrite Zlength_sublist; lia).
      assert (HBl: Zlength (sublist li (Zlength c) c) = Zlength c - li) by (rewrite Zlength_sublist; lia).
      set (A := sublist 0 li c) in *. set (B := sublist li (Zlength c) c) in *.
      assert (Hc1: Zlength (copied B A 0 k 16) = Zlength A) by (apply xf_Zlength_copied; lia).
      destruct (xd_copied B A 0 k 16) as [Hc1u Hc1r]; try lia; [exact HL16 |].
      assert_PROP (field_compatible (tarray tuchar (Zlength B)) [] (offset_val li ob)) as FCB by entailer!.
      assert_PROP (field_compatible (tarray tuchar (Zlength A)) [] ob) as FCA by entailer!.
      forward. forward_if.
      + rewrite !Int64.unsigned_repr in H5 by rep_lia.
        forward. forward. forward.
        rewrite (tuchar_split sh (offset_val li ob) B 16) by (auto; lia).
        sep_apply (tuchar_split_N sh ob (Zlength A) (copied B A 0 k 16) (k + 16) Hc1 FCA ltac:(lia)).
        assert (HFs: Forall is_byte_val (sublist 0 (ll - 16 + WILDCOPY_OVERLENGTH) (sublist 16 (Zlength B) B))).
        { unfold B. rewrite !sublist_sublist by (rewrite ?Zlength_sublist; unfold WILDCOPY_OVERLENGTH in *; lia).
          apply (xd_sub c li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia. }
        forward_call (gv, false, sh, ob, c, 0, 0, sh, offset_val 16 (offset_val li ob), sublist 16 (Zlength B) B,
                      sh, offset_val (k + 16) ob,
                      sublist (k + 16) (Zlength (copied B A 0 k 16)) (copied B A 0 k 16), ll - 16, 0).
        { cancel. }
        { split; [apply writable_readable_share; auto | split; [auto | split; [reflexivity |]]].
          rewrite Hc1, !Zlength_sublist by lia. unfold WILDCOPY_OVERLENGTH; lia. }
        Intros g.
        match goal with H: _ = lwild _ _ _ _ _ _ |- _ => rename H into Hx end.
        match goal with H: g = _ |- _ =>
          assert (Hgu := xd_wc_dj (sublist 16 (Zlength B) B)
                           (sublist (k + 16) (Zlength (copied B A 0 k 16)) (copied B A 0 k 16)) g (ll - 16)
                           ltac:(lia) ltac:(rewrite Zlength_sublist by lia; unfold WILDCOPY_OVERLENGTH; lia)
                           ltac:(rewrite Zlength_sublist by (rewrite Hc1; lia); rewrite Hc1; unfold WILDCOPY_OVERLENGTH; lia)
                           HFs H) end.
        match goal with H: g = _ |- _ => pose proof (xfb_wc_dj _ _ _ _ H) as Hgb; clear H end. rewrite Hc1 in *.
        sep_apply (xf_rejoin sh (offset_val li ob) B 16 FCB ltac:(lia)).
        sep_apply (xf_join sh ob (Zlength A) (k + 16) (sublist 0 (k + 16) (copied B A 0 k 16))
                     (sublist (k + 16) (Zlength A) (copied B A 0 k 16))
                     (sublist 0 (ll - 16) (sublist 16 (Zlength B) B) ++ g ++
                      sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength A) (copied B A 0 k 16)))
                        (sublist (k + 16) (Zlength A) (copied B A 0 k 16))) FCA).
        { list_solve. }
        { unfold WILDCOPY_OVERLENGTH in *. list_solve. }
        { list_solve. }
        set (A' := sublist 0 (k + 16) (copied B A 0 k 16) ++
                (sublist 0 (ll - 16) (sublist 16 (Zlength B) B) ++ g ++
                 sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength A) (copied B A 0 k 16)))
                   (sublist (k + 16) (Zlength A) (copied B A 0 k 16)))).
        assert (HA1: Zlength A' = li) by (unfold A', WILDCOPY_OVERLENGTH in *; list_solve).
        assert (XL: xq_lit c (A' ++ B) k LW li ll).
        { apply xq_lit_gt; [lia|].
          assert (E1: copied B A 0 k 16 ++ B = lmove 16 c k LW li) by (unfold A, B; apply xg_copied_in; lia).
          rewrite <- E1. rewrite <- HAl. unfold A'.
          apply (xq_litin_join _ _ _ (Zlength A)); auto; lia. }
        assert (HA2: xf_lit_ok A A' k ll (sublist 0 ll B))
          by (intros p ? ?; apply (xf_lit32 A B g k 0 ll); unfold WILDCOPY_OVERLENGTH in *; lia).
        assert (HB: xfb_ok c c x (A' ++ B))
          by (intros Hc _ _; assert (byte_cells A) by (unfold A; xfb_t); assert (byte_cells B) by (unfold B; xfb_t);
              assert (byte_cells g) by (apply Hgb; xfb_t); unfold A'; xfb_t).
        assert (HuA: xd_ub c (A' ++ B)).
        { change (A' ++ B) with (A' ++ sublist li (Zlength c) c). apply xd_ub_join_l; [lia | exact HA1 |].
          apply (xd_ub_trans A (copied B A 0 k 16)); [exact Hc1 | exact Hc1u |].
          unfold A'. apply (xd_ub_join_r' _ _ (Zlength A)); [exact Hc1 | lia | | exact Hgu].
          unfold WILDCOPY_OVERLENGTH in *. list_solve. }
        clearbody A'. rewrite HAl, HBl.
        sep_apply (xf_join2 sh ob (Zlength c) li (Zlength c - li) A' B FCc HA1 HBl ltac:(lia)).
        assert (HA3: xf_lit_ok c (A' ++ B) k ll Lv) by (apply xf_litin; lia || auto).
        Exists (A' ++ B). unfold seqrep. entailer!; try list_solve.
      + rewrite !Int64.unsigned_repr in H5 by rep_lia. forward.
        assert (HA2: xf_lit_ok A (copied B A 0 k 16) k ll (sublist 0 ll B))
          by (intros p ? ?; apply (xf_lit16 A B k 0 ll); lia).
        rewrite HAl, HBl.
        sep_apply (xf_join2 sh ob (Zlength c) li (Zlength c - li) (copied B A 0 k 16) B FCc ltac:(lia) HBl ltac:(lia)).
        assert (HA3: xf_lit_ok c (copied B A 0 k 16 ++ B) k ll Lv) by (apply xf_litin; lia || auto).
        assert (XL: xq_lit c (copied B A 0 k 16 ++ B) k LW li ll)
          by (apply xq_lit_le; [lia | unfold A, B; apply xg_copied_in; lia]).
        assert (HuA: xd_ub c (copied B A 0 k 16 ++ B))
          by (change (copied B A 0 k 16 ++ B) with (copied B A 0 k 16 ++ sublist li (Zlength c) c);
              apply xd_ub_join_l; [lia | rewrite Hc1; exact HAl | exact Hc1u]).
        assert (HB: xfb_ok c c x (copied B A 0 k 16 ++ B))
          by (intros Hc _ _; assert (byte_cells A) by (unfold A; xfb_t); assert (byte_cells B) by (unfold B; xfb_t); xfb_t).
        Exists (copied B A 0 k 16 ++ B). unfold seqrep. entailer!; try list_solve. }
  (* the match *)
  Intros cA.
  match goal with H: Zlength cA = Zlength c |- _ => rename H into HcA end.
  match goal with H: xf_lit_ok _ _ _ _ _ |- _ => rename H into HlA end.
  match goal with H: xfb_ok _ _ _ cA |- _ => rename H into HbA end.
  assert (HLv: Zlength Lv = ll) by (unfold Lv; rewrite Zlength_sublist; lia).
  match goal with H: xd_ub c cA |- _ => rename H into HuA end.
  match goal with H: xq_lit c cA _ _ _ _ |- _ => rename H into XL end.
  assert (HLvb: Forall is_byte_val Lv)
    by (unfold Lv; apply (xd_sub (lit_arr ls c) li (lim + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia).
  assert (HdA: xd_rng cA ps (k + ll)).
  { apply (xd_after_lit c cA Lv k ps ll); auto; try lia.
    - apply xd_Forall_rng; auto; lia.
    - intros p Hp. apply HlA; lia. }
  assert (Hext: 0 <= ext_len x <= 2 ^ 63 - 1) by (destruct H6; auto).
  unfold seqrep. forward. forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?L _)) _ _ =>
    forward_if (EX d: Z, EX c2: list val,
      PROPx [0 <= d < ml; ps <= k + ll + d - off; off <= k + ll - ps + ext_len x;
             Zlength c2 = Zlength c; unchanged_outside c c2 k (k + ll + ml + 32);
             xf_J c c2 k e ll ml off ps x Lv d; xfb_ok c (lit_arr ls c) x c2; xd_ub c c2; xd_rng c2 ps (k + ll + d);
             xq_M x cA c2 k ll ml off ps d]
      (LOCALx L
      (SEPx [data_at shq t_seq (seqrep ll ml off) sp; data_at Tsh t_seq (seqrep ll (ml - d) off) v_sequence;
             data_at Tsh (tptr tuchar) (offset_val (k + ll + d - off) ob) v_match;
             data_at Tsh (tptr tuchar) (offset_val (k + ll + d) ob) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) c2 ob;
             data_at shp (tptr tuchar) (offset_val (li + ll) (lit_base ls ob)) plp; lit_res ls; ext_res x])))
  end.
  { apply prop_right, cp_sameblock; auto. }
  { (* offset beyond the prefix: the extDict *)
    rewrite xf_gt_diff in H8 by (auto; rep_lia).
    assert (Hoff2: k + ll - ps < off) by (destruct (zlt (k + ll - ps) off); [lia | xf_tf]). clear H8.
    destruct (Z_lt_ge_dec (k + ll - ps + ext_len x) off) as [Herr|Hok].
    { apply xf_loop_seq with (Q := FF); [|apply semax_ff].
      forward. forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { xf_err_prefix. forward.
        assert (Hun: unchanged_outside c cA k e) by (apply (xf_lit_unch c cA k ll e Lv); auto; lia).
        assert (HuA': forall q, 0 <= q < Zlength c -> Znth q cA = Znth q c \/ is_byte_val (Znth q cA)) by exact HuA.
        Exists (err_code 20) cA (offset_val (li + ll) (lit_base ls ob)).
        entailer!. apply xq_err_ret; [lia | lia | lia | | exact Hun].
        unfold exec_err. rewrite (proj2 (Z.ltb_lt _ _) Herr). rewrite !orb_true_r. reflexivity. }
      { rewrite xf_gt_diff in H8 by (auto; rep_lia). destruct (zlt _ _); [xf_tf | lia]. } }
    match goal with |- semax _ ?P _ _ => apply (xf_loop_seq _ P P) end.
    { forward. forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { rewrite xf_gt_diff in H8 by (auto; rep_lia). destruct (zlt _ _); [lia | xf_tf]. }
      { forward. entailer!. } }
    destruct x as [|e1 elen|shx eb en ec e1 elen]; simpl dict_end in *; simpl ext_len in *.
    { lia. }
    - (* ExtIn *)
      unfold MORE_COMMANDS, abbreviate. abbreviate_semax. forward. forward.
      { xf_sb. }
      rewrite cp_sub_pp, xf_add_ptr_long by auto.
      set (dl := off - (k + ll - ps)).
      assert (Hdl: dl = off - (k + ll - ps)) by reflexivity. clearbody dl.
      replace (e1 + (k + ll - off - ps)) with (e1 - dl) by lia.
      forward. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx ((dl < ml) :: P) (LOCALx Q (SEPx R))) end.
      { xf_sb. }
      { (* the whole match from the extDict *)
        rewrite xf_ge_diff in H8 by (auto; rep_lia).
        assert (Hfull: ml <= dl) by (destruct (zlt _ _); [xf_tf | lia]). clear H8.
        assert (He12 := H6). destruct He12 as (_ & He1 & He2).
        forward. forward.
        assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) cA))
          by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
        forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) ml).
        { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
        simpl mm_post.
        destruct (xd_mm cA (Zlength c) (e1 - dl) (k + ll) ml) as [Hm1 Hm2]; auto; try lia.
        set (c' := mm_result cA (Zlength c) (e1 - dl) (k + ll) ml).
        assert (Hc'1: Zlength c' = Zlength c) by (unfold c', mm_result; list_solve).
        assert (Hc'2: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + ml) -> Znth p c' = Znth p cA)
          by (intros p ? ?; unfold c', mm_result; list_solve).
        assert (Hc'3: sublist (k + ll) (k + ll + ml) c' =
                      sublist (ext_end (ExtIn e1 elen) - dl) (ext_end (ExtIn e1 elen) - dl + ml) (ext_src cA (ExtIn e1 elen)))
          by (simpl; unfold c', mm_result; list_solve).
        assert (HU: unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH))).
        { apply xf_unch_min; [|lia]. apply (xf_unch_trans c cA c' k (k + ll + ml + 32) (k + ll) (k + ll + ml)); auto; try lia.
          apply (xf_lit_unch c cA k ll _ Lv); auto; lia. }
        assert (HR := xf_post c c' k e ll ml off ps (ExtIn e1 elen) Lv HLv H0 ltac:(lia) ltac:(simpl; lia) ltac:(lia)
                        ltac:(split; [simpl; lia | split; lia]) Hc'1
                        (xf_full_ext c cA c' k e ll ml off ps dl (ExtIn e1 elen) Lv HLv H0 ltac:(lia) ltac:(lia) ltac:(lia)
                           ltac:(lia) Hdl ltac:(lia) Hfull ltac:(simpl; lia) ltac:(split; [simpl; lia | split; lia])
                           HcA HlA Hc'1 Hc'2 Hc'3)).
        assert (HB: xfb_ok c (lit_arr ls c) (ExtIn e1 elen) c') by (intros ? ? ?; unfold c'; apply xfb_mm; apply HbA; auto).
        destruct (xd_fin c cA c' k ps (k + ll) (k + (ll + ml))) as [XU XF]; try lia; [exact HuA | exact Hm1 | exact HdA | |].
        { replace (k + (ll + ml)) with (k + ll + ml) by lia. exact Hm2. }
        specialize (XF Hc'1).
        assert (HE := xf_noerr ll ml H2 H3).
        assert (HX: exec_err k e li lim ll ml off ps (ext_len (ExtIn e1 elen)) = false)
          by (apply xf_exec_err_false; simpl; lia).
        assert (Xex: is_error_code (ll + ml) = false -> c' = lexec ps (ps - elen) e1 e c k (ls_l ls) li lim ll ml off).
        { intros _. subst c'. apply (xq_full_ext c cA (Zlength c) e1 elen k e li lim ll ml off ps dl); auto; lia. }
        forward.
        Exists (ll + ml) c' (offset_val (li + ll) (lit_base ls ob)).
        entailer!. rewrite HE; symmetry; exact HX. }
      { rewrite xf_ge_diff in H8 by (auto; rep_lia).
        assert (dl < ml) by (destruct (zlt _ _); [lia | xf_tf]). forward. entailer!. }
      Intros. rename H8 into Hpart.
      assert (He12 := H6). destruct He12 as (_ & He1 & He2).
      forward. forward.
      { xf_sb. }
      rewrite cp_sub_pp' by auto. replace (e1 - (e1 - dl)) with dl by lia.
      forward.
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) cA))
        by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
      forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) dl).
      { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
      simpl mm_post.
      destruct (xd_mm cA (Zlength c) (e1 - dl) (k + ll) dl) as [Hm1 Hm2]; auto; try lia.
      xf_fw. xf_fw. xf_fw. xf_fw.
      set (c2 := mm_result cA (Zlength c) (e1 - dl) (k + ll) dl).
      assert (Hu2: xd_ub c c2) by (apply (xd_ub_trans c cA c2); [lia | exact HuA | exact Hm1]).
      assert (Hd2: xd_rng c2 ps (k + ll + dl))
        by (apply (xd_rng_app _ _ (k + ll)); [apply (xd_rng_ub cA); try lia; [exact Hm1 | exact HdA] | exact Hm2]).
      assert (Hc21: Zlength c2 = Zlength c) by (unfold c2, mm_result; list_solve).
      assert (Hc22: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA)
        by (intros p ? ?; unfold c2, mm_result; list_solve).
      assert (Hc23: sublist (k + ll) (k + ll + dl) c2 =
                    sublist (ext_end (ExtIn e1 elen) - dl) (ext_end (ExtIn e1 elen)) (ext_src cA (ExtIn e1 elen)))
        by (simpl; unfold c2, mm_result; list_solve).
      assert (HJ := xf_J_ext c cA c2 k e ll ml off ps dl (ExtIn e1 elen) Lv HLv H0 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) Hdl ltac:(lia) ltac:(simpl; lia) H6 HcA HlA Hc21 Hc22 Hc23).
      assert (HU2: unchanged_outside c c2 k (k + ll + ml + 32)).
      { apply (xf_unch_trans c cA c2 k (k + ll + ml + 32) (k + ll) (k + ll + dl)); auto; try lia.
        apply (xf_lit_unch c cA k ll _ Lv); auto; lia. }
      assert (HB2: xfb_ok c (lit_arr ls c) (ExtIn e1 elen) c2) by (intros ? ? ?; unfold c2; apply xfb_mm; apply HbA; auto).
      assert (XM: xq_M (ExtIn e1 elen) cA c2 k ll ml off ps dl) by (unfold c2; apply xq_M_span; auto; lia).
      clearbody c2.
      Exists dl c2. replace (k + ll + dl - off) with ps by lia. unfold seqrep. entailer!.
      apply derives_refl'. f_equal.
    - (* ExtSep *)
      unfold MORE_COMMANDS, abbreviate. abbreviate_semax. simpl ext_res.
      assert (Hx: readable_share shx /\ Zlength ec = en /\ en <= 2 ^ 63 - 1 /\ 0 <= e1 - elen /\ e1 <= en)
        by (destruct H6 as [_ ?]; auto).
      destruct Hx as [Hshx [Hen [Hen2 [He1 He2]]]].
      assert_PROP (field_compatible (tarray tuchar en) [] eb) as FCe by entailer!.
      assert (Peb: isptr eb) by (destruct FCe; auto).
      forward. forward.
      { xf_sb. }
      rewrite cp_sub_pp, xf_add_ptr_long by auto.
      set (dl := off - (k + ll - ps)).
      assert (Hdl: dl = off - (k + ll - ps)) by reflexivity. clearbody dl.
      replace (e1 + (k + ll - off - ps)) with (e1 - dl) by lia.
      forward. forward.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx ((dl < ml) :: P) (LOCALx Q (SEPx R))) end.
      { xf_sb. }
      { (* the whole match from the extDict *)
        rewrite xf_ge_diff in H8 by (auto; rep_lia).
        assert (Hfull: ml <= dl) by (destruct (zlt _ _); [xf_tf | lia]). clear H8.
        forward. forward.
        rewrite (xf_split3 shx en (e1 - dl) ml ec eb) by (auto; lia).
        rewrite (xf_split3 sh (Zlength c) (k + ll) ml cA ob) by (auto; lia).
        assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
        forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) ml
                        (sublist (e1 - dl) (e1 - dl + ml) ec)).
        { unfold mm_pre. cancel. }
        { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
        unfold mm_post. Intros.
        sep_apply (xf_join3 shx en (e1 - dl) ml ec eb); auto; try lia.
        sep_apply (xf_join_put sh (Zlength c) (k + ll) ml cA (sublist (e1 - dl) (e1 - dl + ml) ec) ob); auto; try lia.
        { rewrite Zlength_sublist; lia. }
        destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + ml) ec) (k + ll)) as [Hm1 Hm2];
          [lia | rewrite Zlength_sublist; lia | exact HmB |].
        rewrite Zlength_sublist in Hm2 by lia.
        set (c' := put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)).
        assert (Hc'1: Zlength c' = Zlength c) by (unfold c', put; list_solve).
        assert (Hc'2: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + ml) -> Znth p c' = Znth p cA)
          by (intros p ? ?; unfold c', put; list_solve).
        assert (Hc'3: sublist (k + ll) (k + ll + ml) c' =
                      sublist (ext_end (ExtSep shx eb en ec e1 elen) - dl) (ext_end (ExtSep shx eb en ec e1 elen) - dl + ml)
                        (ext_src cA (ExtSep shx eb en ec e1 elen)))
          by (simpl; unfold c', put; list_solve).
        assert (HU: unchanged_outside c c' k (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH))).
        { apply xf_unch_min; [|lia]. apply (xf_unch_trans c cA c' k (k + ll + ml + 32) (k + ll) (k + ll + ml)); auto; try lia.
          apply (xf_lit_unch c cA k ll _ Lv); auto; lia. }
        assert (HR := xf_post c c' k e ll ml off ps (ExtSep shx eb en ec e1 elen) Lv HLv H0 ltac:(lia) ltac:(simpl; lia)
                        ltac:(lia) H6 Hc'1
                        (xf_full_ext c cA c' k e ll ml off ps dl (ExtSep shx eb en ec e1 elen) Lv HLv H0 ltac:(lia)
                           ltac:(lia) ltac:(lia) ltac:(lia) Hdl ltac:(lia) Hfull ltac:(simpl; lia) H6
                           HcA HlA Hc'1 Hc'2 Hc'3)).
        assert (HB: xfb_ok c (lit_arr ls c) (ExtSep shx eb en ec e1 elen) c')
          by (intros Hc Hl He; unfold c'; apply xfb_put; [apply HbA; auto | apply xfb_sublist; exact He]).
        destruct (xd_fin c cA c' k ps (k + ll) (k + (ll + ml))) as [XU XF]; try lia; [exact HuA | exact Hm1 | exact HdA | |].
        { replace (k + (ll + ml)) with (k + ll + (e1 - dl + ml - (e1 - dl))) by lia. exact Hm2. }
        specialize (XF Hc'1).
        assert (HE := xf_noerr ll ml H2 H3).
        assert (HX: exec_err k e li lim ll ml off ps (ext_len (ExtSep shx eb en ec e1 elen)) = false)
          by (apply xf_exec_err_false; simpl; lia).
        forward.
        Exists (ll + ml) c' (offset_val (li + ll) (lit_base ls ob)).
        entailer!. rewrite HE; symmetry; exact HX. }
      { rewrite xf_ge_diff in H8 by (auto; rep_lia).
        assert (dl < ml) by (destruct (zlt _ _); [lia | xf_tf]). forward. entailer!. }
      Intros. rename H8 into Hpart.
      forward. forward.
      { xf_sb. }
      rewrite cp_sub_pp' by auto. replace (e1 - (e1 - dl)) with dl by lia.
      forward.
      rewrite (xf_split3 shx en (e1 - dl) dl ec eb) by (auto; lia).
      rewrite (xf_split3 sh (Zlength c) (k + ll) dl cA ob) by (auto; lia).
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
      forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) dl
                      (sublist (e1 - dl) (e1 - dl + dl) ec)).
      { unfold mm_pre. cancel. }
      { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
      unfold mm_post. Intros.
      sep_apply (xf_join3 shx en (e1 - dl) dl ec eb); auto; try lia.
      sep_apply (xf_join_put sh (Zlength c) (k + ll) dl cA (sublist (e1 - dl) (e1 - dl + dl) ec) ob); auto; try lia.
      { rewrite Zlength_sublist; lia. }
      xf_fw. xf_fw. xf_fw. xf_fw.
      destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + dl) ec) (k + ll)) as [Hm1 Hm2];
        [lia | rewrite Zlength_sublist; lia | exact HmB |].
      rewrite Zlength_sublist in Hm2 by lia. replace (k + ll + (e1 - dl + dl - (e1 - dl))) with (k + ll + dl) in Hm2 by lia.
      set (c2 := put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)).
      assert (Hu2: xd_ub c c2) by (apply (xd_ub_trans c cA c2); [lia | exact HuA | exact Hm1]).
      assert (Hd2: xd_rng c2 ps (k + ll + dl))
        by (apply (xd_rng_app _ _ (k + ll)); [apply (xd_rng_ub cA); try lia; [exact Hm1 | exact HdA] | exact Hm2]).
      assert (Hc21: Zlength c2 = Zlength c) by (unfold c2, put; list_solve).
      assert (Hc22: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA)
        by (intros p ? ?; unfold c2, put; list_solve).
      assert (Hc23: sublist (k + ll) (k + ll + dl) c2 =
                    sublist (ext_end (ExtSep shx eb en ec e1 elen) - dl) (ext_end (ExtSep shx eb en ec e1 elen))
                      (ext_src cA (ExtSep shx eb en ec e1 elen)))
        by (simpl; unfold c2, put; list_solve).
      assert (HJ := xf_J_ext c cA c2 k e ll ml off ps dl (ExtSep shx eb en ec e1 elen) Lv HLv H0 ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia) Hdl ltac:(lia) ltac:(simpl; lia) H6 HcA HlA Hc21 Hc22 Hc23).
      assert (HU2: unchanged_outside c c2 k (k + ll + ml + 32)).
      { apply (xf_unch_trans c cA c2 k (k + ll + ml + 32) (k + ll) (k + ll + dl)); auto; try lia.
        apply (xf_lit_unch c cA k ll _ Lv); auto; lia. }
      assert (HB2: xfb_ok c (lit_arr ls c) (ExtSep shx eb en ec e1 elen) c2)
        by (intros Hc Hl He; unfold c2; apply xfb_put; [apply HbA; auto | apply xfb_sublist; exact He]).
      assert (XM: xq_M (ExtSep shx eb en ec e1 elen) cA c2 k ll ml off ps dl) by exact I.
      clearbody c2.
      Exists dl c2. replace (k + ll + dl - off) with ps by lia. unfold seqrep. entailer!.
      apply derives_refl'. f_equal. }
  { (* inside the prefix *)
    forward.
    match goal with H: typed_false _ _ |- _ => rename H into Hf end.
    rewrite xf_gt_diff in Hf by (auto; rep_lia).
    assert (Hoff2: off <= k + ll - ps) by (destruct (zlt (k + ll - ps) off); [xf_tf | lia]).
    Exists 0 cA. unfold seqrep. rewrite !Z.sub_0_r, !Z.add_0_r. entailer!.
    split; [apply (xf_lit_unch c cA k ll _ Lv); auto; lia|].
    split; [apply (xf_J_prefix c cA k e ll ml off ps x Lv); auto; lia | apply xq_M_prefix; lia]. }
  (* the match from the prefix, at di = k + ll + d, si = di - off *)
  Intros d c2.
  match goal with H: 0 <= d < ml |- _ => rename H into Hd end.
  match goal with H: ps <= k + ll + d - off |- _ => rename H into Hsi end.
  match goal with H: off <= k + ll - ps + ext_len x |- _ => rename H into Hoffx end.
  match goal with H: Zlength c2 = Zlength c |- _ => rename H into Hc2L end.
  match goal with H: unchanged_outside c c2 _ _ |- _ => rename H into Hc2u end.
  match goal with H: xf_J _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: xfb_ok _ _ _ c2 |- _ => rename H into Hc2b end.
  match goal with H: xd_ub c c2 |- _ => rename H into Hu2 end.
  match goal with H: xd_rng c2 ps _ |- _ => rename H into Hd2 end.
  match goal with H: xq_M _ _ c2 _ _ _ _ _ _ |- _ => rename H into XM end.
  unfold seqrep.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((off < 16) :: P) (LOCALx Q (SEPx R))) end.
  { (* off >= 16: one wild copy *)
    xf_ur.
    forward. forward. forward.
    assert (HC: copy_src_def c2 (k + ll + d - off) (k + ll + d) (ml - d)) by (apply (xd_csd c2 ps); auto; lia).
    forward_call (gv, true, sh, ob, c2, k + ll + d - off, k + ll + d, sh, nullval, @nil val, sh, nullval, @nil val,
                  ml - d, 0).
    { entailer!. simpl. rewrite Hc2L, !(xf_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc2L. cancel. }
    { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN.
      rewrite Hc2L. split; [exact SH|]. repeat split; try rep_lia; intros; try discriminate; first [exact HC | lia]. }
    Intros g.
    match goal with H: wc_within_post _ _ _ _ g = _ |- _ => rename H into Hw end.
    match goal with H: g = _ |- _ =>
      destruct (xd_wc_within c2 g (k + ll + d - off) (k + ll + d) (ml - d) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite Hc2L; unfold WILDCOPY_OVERLENGTH; lia) ltac:(rewrite Hc2L; unfold WILDCOPY_OVERLENGTH; lia) HC H)
        as [Hwu Hwr] end.
    match goal with H: g = _ |- _ =>
      assert (Hgb: byte_cells c2 -> byte_cells g)
        by (intro; refine (xfb_wc_g _ _ _ _ _ _ _ _ _ H _); [lia | lia | rewrite Hc2L; unfold WILDCOPY_OVERLENGTH; lia | assumption]);
      clear H end.
    assert (HB: xfb_ok c (lit_arr ls c) x (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g))
      by (intros Hc Hl He; apply xfb_wc_within; [apply Hc2b; auto | apply Hgb, Hc2b; auto | lia | lia | rewrite Hc2L; lia]).
    destruct (xf_wc_facts c2 g (k + ll + d - off) (k + ll + d) (ml - d)) as (W1 & W2 & W3); try (unfold WILDCOPY_OVERLENGTH in *; lia).
    destruct (xd_fin c c2 (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g) k ps (k + ll + d) (k + (ll + ml)))
      as [XU XF]; auto; try lia.
    { replace (k + (ll + ml)) with (k + ll + d + (ml - d)) by lia. exact Hwr. }
    specialize (XF ltac:(lia)).
    try rewrite Hc2L; try rewrite Hc3L.
    assert (Xfin := xq_final c cA c2 _ x k e li lim ll ml off ps d (ls_l ls) XL ltac:(lia) ltac:(lia) XM
                      (xq_pre16 c2 _ (k + ll + d) (k + ll + d - off) (ml - d) off ltac:(lia) Hw)).
    forward.
    Exists (ll + ml) (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g) (offset_val (li + ll) (lit_base ls ob)).
    unfold seqrep. entailer!.
    apply (xf_final c c2 _ k e li lim ll ml off ps d x Lv); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia. exact W3. }
  { forward. entailer!. xf_ur. lia. }
  Intros. match goal with H: off < 16 |- _ => rename H into Hoff16 end.
  forward.
  forward_call (gv, sh, ob, c2, v_op, v_match, k + ll + d, off).
  { rewrite Hc2L, !(xf_fa (Zlength c)) by (auto; lia). replace (k + ll + d - off) with (k + ll + d - off) by lia.
    cancel. }
  { apply xd_rng_Forall; try lia. apply (xd_rng_sub _ ps (k + ll + d)); auto; lia. }
  match goal with H: lov8 _ _ _ _ = _ |- _ => rename H into Hov end.
  destruct (xf_oc8_K off) as (K1 & K2 & K3); [lia|].
  rewrite Hc2L, !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
  assert (Hr8: xd_rng c2 (k + ll + d - off) (if k + ll + d - off <? k + ll + d then Z.min (k + ll + d) (k + ll + d - off + 8)
                                             else k + ll + d - off + 8)).
  { rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply (xd_rng_sub _ ps (k + ll + d)); auto; lia. }
  assert (Hu3: xd_ub c2 (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat 8))) by (apply xd_ub_listcopy; auto; lia).
  assert (Hd3: xd_rng (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat 8)) (k + ll + d) (k + ll + d + 8))
    by (apply xd_listcopy; auto; lia).
  change (Z.to_nat 8) with 8%nat in Hu3, Hd3.
  set (c3 := listcopy c2 (k + ll + d - off) (k + ll + d) 8).
  assert (Hu23: xd_ub c c3) by (apply (xd_ub_trans c c2 c3); auto).
  assert (Hd23: xd_rng c3 ps (k + ll + d + 8)) by (apply (xd_rng_app _ _ (k + ll + d)); [apply (xd_rng_ub c2); try lia; auto | exact Hd3]).
  assert (Hc3b: xfb_ok c (lit_arr ls c) x c3)
    by (intros Hc Hl He; unfold c3; apply xfb_listcopy; [apply Hc2b; auto | lia | rewrite Hc2L; change (Z.of_nat 8) with 8; lia]).
  forward.
  apply semax_if_seq. forward_if.
  { (* ml - d > 8: the wild copy at distance oc8_off off *)
    xf_ur.
    forward. forward. forward.
    assert (Hc3L: Zlength c3 = Zlength c) by (unfold c3; rewrite listcopy_Zlength; lia).
    assert (HC: copy_src_def c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8))
      by (apply (xd_csd c3 ps); auto; lia).
    forward_call (gv, true, sh, ob, c3, k + ll + d + 8 - oc8_off off, k + ll + d + 8, sh, nullval, @nil val,
                  sh, nullval, @nil val, ml - d - 8, 1).
    { entailer!. simpl. rewrite Hc3L, !(xf_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc3L. cancel. }
    { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN.
      rewrite Hc3L. split; [exact SH|]. repeat split; try rep_lia; intros; try discriminate; first [exact HC | lia]. }
    Intros g.
    match goal with H: wc_within_post _ _ _ _ g = _ |- _ => rename H into Hw end.
    match goal with H: g = _ |- _ =>
      destruct (xd_wc_within c3 g (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) _ ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(rewrite Hc3L; unfold WILDCOPY_OVERLENGTH; lia)
                  ltac:(rewrite Hc3L; unfold WILDCOPY_OVERLENGTH; lia) HC H)
        as [Hwu Hwr] end.
    match goal with H: g = _ |- _ =>
      assert (Hgb: byte_cells c3 -> byte_cells g)
        by (intro; refine (xfb_wc_g _ _ _ _ _ _ _ _ _ H _); [lia | lia | rewrite Hc3L; unfold WILDCOPY_OVERLENGTH; lia | assumption]);
      clear H end.
    assert (HB: xfb_ok c (lit_arr ls c) x
                  (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g))
      by (intros Hc Hl He; apply xfb_wc_within; [apply Hc3b; auto | apply Hgb, Hc3b; auto | lia | lia | rewrite Hc3L; lia]).
    destruct (xf_oc8_facts c2 g off (k + ll + d) (ml - d)) as (W1 & W2 & W3); try (unfold WILDCOPY_OVERLENGTH in *; lia).
    cbv zeta in W1, W2, W3.
    assert (Eg: (ml - d >? 8) = true) by (apply Z.gtb_lt; lia).
    rewrite Eg in W1, W2, W3. fold c3 in W1, W2, W3.
    destruct (xd_fin c c3 (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g) k ps
                (k + ll + d + 8) (k + (ll + ml))) as [XU XF]; auto; try lia.
    { replace (k + (ll + ml)) with (k + ll + d + 8 + (ml - d - 8)) by lia. exact Hwr. }
    specialize (XF ltac:(lia)).
    try rewrite Hc2L; try rewrite Hc3L.
    assert (Xfin := xq_final c cA c2 _ x k e li lim ll ml off ps d (ls_l ls) XL ltac:(lia) ltac:(lia) XM
                      (xq_pre8 c2 c3 _ (k + ll + d) (ml - d) off ltac:(lia) ltac:(lia) Hov Hw)).
    forward.
    Exists (ll + ml) (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g)
      (offset_val (li + ll) (lit_base ls ob)).
    unfold seqrep. entailer!.
    apply (xf_final c c2 _ k e li lim ll ml off ps d x Lv); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia.
      replace (k + ll + d - off) with (k + ll + d - off) by lia. exact W3. }
  { xf_ur.
    destruct (xf_oc8_facts c2 (Zrepeat Vundef 32) off (k + ll + d) (ml - d)) as (W1 & W2 & W3); try (unfold WILDCOPY_OVERLENGTH in *; lia).
    { rewrite Zlength_Zrepeat; lia. }
    cbv zeta in W1, W2, W3.
    assert (Eg: (ml - d >? 8) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite Eg in W1, W2, W3. fold c3 in W1, W2, W3. try rewrite Hc2L.
    destruct (xd_fin c c2 c3 k ps (k + ll + d) (k + (ll + ml))) as [XU XF]; auto; try lia.
    { apply (xd_rng_sub _ (k + ll + d) (k + ll + d + 8)); auto; lia. }
    specialize (XF ltac:(lia)).
    assert (Xfin := xq_final c cA c2 _ x k e li lim ll ml off ps d (ls_l ls) XL ltac:(lia) ltac:(lia) XM
                      (xq_pre8s c2 c3 (k + ll + d) (ml - d) off ltac:(lia) ltac:(lia) Hov)).
    forward.
    Exists (ll + ml) c3 (offset_val (li + ll) (lit_base ls ob)).
    unfold seqrep. entailer!.
    apply (xf_final c c2 _ k e li lim ll ml off ps d x Lv); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia. exact W3. }
Qed.

(* ---------- ZSTD_execSequenceSplitLitBuffer ---------- *)
Lemma fs_add_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a + n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  unfold Ptrofs.of_int64. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite ptrofs_add_repr. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|].
  unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus.
  apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma fs_sub_pi {cs: compspecs} (p: val) (a k: Z) : isptr p -> Int.min_signed <= k <= Int.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tint (offset_val a p) (Vint (Int.repr k))) =
  offset_val (a - k) p.
Proof.
  intros. destruct p; try contradiction. simpl. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite !ptrofs_add_repr.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite ptrofs_sub_repr. f_equal. lia.
Qed.

Lemma fs_sub_pl {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_binary_operation' Osub (tptr tuchar) tulong (offset_val a p) (Vlong (Int64.repr n))) =
  offset_val (a - n) p.
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
  unfold Ptrofs.of_int64. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite ptrofs_add_repr, ptrofs_add_repr, Ptrofs.sub_add_opp.
  unfold Ptrofs.neg. rewrite ptrofs_add_repr.
  apply Ptrofs.eqm_samerepr. replace (Ptrofs.unsigned i + (a - n)) with (Ptrofs.unsigned i + a + - n) by lia.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|]. apply Ptrofs.eqm_neg.
  eapply Ptrofs.eqm_trans; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
  unfold Ptrofs.eqm. change Ptrofs.modulus with Int64.modulus. apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Lemma fs_sub_pl' {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_sub_pl tuchar (offset_val a p) (Vlong (Int64.repr n))) = offset_val (a - n) p.
Proof. intros Hp. exact (fs_sub_pl p a n Hp). Qed.

Lemma fs_lt_diff (p: val) (a b n: Z) : isptr p ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.lt n1 n2))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) (Vlong (Int64.repr n)) with
  | Some v' => v' | None => Vundef end =
  Vint (if Int64.lt (Int64.repr (a - b)) (Int64.repr n) then Int.one else Int.zero).
Proof.
  intros Hp. rewrite cp_sub_pp by auto. simpl. destruct (Int64.lt _ _); reflexivity.
Qed.

(* the C's "litLimit - litPtr < ll": false gives ll <= lim - li also when lim - li is beyond the signed range *)
Lemma fs_lt_false (d n: Z) : 0 <= d <= Int64.max_unsigned -> 0 <= n <= Int64.max_signed ->
  Int64.lt (Int64.repr d) (Int64.repr n) = false -> n <= d.
Proof.
  intros Hd Hn E. unfold Int64.lt in E. rewrite (Int64.signed_repr n) in E by rep_lia.
  destruct (zlt (Int64.signed (Int64.repr d)) n); [discriminate|].
  destruct (zle d Int64.max_signed).
  - rewrite Int64.signed_repr in g by rep_lia. lia.
  - lia.
Qed.

Lemma fs_cast_lt (p: val) (a b n: Z) : isptr p ->
  Int64.min_signed <= a - b <= Int64.max_signed -> 0 <= n <= Int64.max_signed ->
  force_val (sem_cast tint tbool
    (eval_binop Olt tlong tlong
       (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val a p) (offset_val b p))
       (eval_cast tulong tlong (Vlong (Int64.repr n))))) =
  Vint (if zlt (a - b) n then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. destruct p; try contradiction.
  unfold eval_binop.
  replace (force_val2 (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar))
             (offset_val a (Vptr b0 i)) (offset_val b (Vptr b0 i)))
    with (Vlong (Int64.repr (a - b))) by (rewrite <- (cp_sub_pp (Vptr b0 i) a b I); reflexivity).
  simpl. unfold Int64.lt. rewrite !Int64.signed_repr by rep_lia.
  destruct (zlt (a - b) n); reflexivity.
Qed.

Lemma fs_Zlength_copied (cs cd: list val) (is id n: Z) :
  0 <= n -> 0 <= is -> is + n <= Zlength cs -> 0 <= id -> id + n <= Zlength cd ->
  Zlength (copied cs cd is id n) = Zlength cd.
Proof. intros. unfold copied. rewrite !Zlength_app, !Zlength_sublist by lia. lia. Qed.

Lemma fs_rejoin (sh: share) (p: val) (l: list val) (d: Z) :
  field_compatible (tarray tuchar (Zlength l)) [] p -> 0 <= d <= Zlength l ->
  data_at sh (tarray tuchar (Zlength (sublist 0 d l))) (sublist 0 d l) p *
  data_at sh (tarray tuchar (Zlength (sublist d (Zlength l) l))) (sublist d (Zlength l) l) (offset_val d p) |--
  data_at sh (tarray tuchar (Zlength l)) l p.
Proof. intros. rewrite <- tuchar_split by auto. apply derives_refl. Qed.

Lemma fs_join (sh: share) (p: val) (N i: Z) (a b b': list val) :
  field_compatible (tarray tuchar N) [] p -> Zlength a = i -> Zlength b' = Zlength b -> Zlength a + Zlength b = N ->
  data_at sh (tarray tuchar (Zlength a)) a p * data_at sh (tarray tuchar (Zlength b)) b' (offset_val i p) |--
  data_at sh (tarray tuchar N) (a ++ b') p.
Proof. intros. subst i. rewrite <- H1. rewrite (tuchar_join sh p N a b') by (auto; lia). apply derives_refl. Qed.

Lemma fs_join2 (sh: share) (p: val) (N i j: Z) (a b: list val) :
  field_compatible (tarray tuchar N) [] p -> Zlength a = i -> Zlength b = j -> i + j = N ->
  data_at sh (tarray tuchar i) a p * data_at sh (tarray tuchar j) b (offset_val i p) |--
  data_at sh (tarray tuchar N) (a ++ b) p.
Proof. intros. subst i j. rewrite (tuchar_join sh p N a b) by (auto; lia). apply derives_refl. Qed.

Lemma fs_lit16 (c cl: list val) (k li ll: Z) :
  0 <= k -> 0 <= li -> 0 <= ll <= 16 -> k + 16 <= Zlength c -> li + 16 <= Zlength cl ->
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) ->
    Znth p (copied cl c li k 16) = Znth p (put c k (sublist li (li + ll) cl)).
Proof.
  intros. unfold copied, put. rewrite Zlength_sublist by lia.
  list_solve.
Qed.

Lemma fs_lit32 (c cl g: list val) (k li ll: Z) :
  0 <= k -> 0 <= li -> 16 < ll -> k + ll + 32 <= Zlength c -> li + ll + 32 <= Zlength cl -> Zlength g = 32 ->
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) ->
    Znth p (sublist 0 (k + 16) (copied cl c li k 16) ++
            (sublist 0 (ll - 16) (sublist (li + 16) (Zlength cl) cl) ++ g ++
             sublist (ll - 16 + WILDCOPY_OVERLENGTH) (Zlength (sublist (k + 16) (Zlength c) (copied cl c li k 16)))
               (sublist (k + 16) (Zlength c) (copied cl c li k 16))))
    = Znth p (put c k (sublist li (li + ll) cl)).
Proof.
  intros. unfold WILDCOPY_OVERLENGTH. unfold copied, put. list_solve.
Qed.

(* the array after the literal copy: put c k Lv, except the slack [k + ll, k + ll + 32) *)
Definition fs_lit_ok (c cA: list val) (k ll: Z) (Lv: list val) : Prop :=
  forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + 32) -> Znth p cA = Znth p (put c k Lv).

Lemma fs_litin (c A': list val) (k li ll: Z) :
  0 <= k -> 0 <= ll -> k + ll + 32 <= li -> li + ll <= Zlength c -> Zlength A' = li ->
  fs_lit_ok (sublist 0 li c) A' k ll (sublist 0 ll (sublist li (Zlength c) c)) ->
  fs_lit_ok c (A' ++ sublist li (Zlength c) c) k ll (sublist li (li + ll) c).
Proof.
  unfold fs_lit_ok. intros Hk Hll Hli Hli2 HA H p Hp Hq.
  destruct (zlt p li).
  - rewrite Znth_app1 by lia. rewrite H by (try rewrite Zlength_sublist; lia). unfold put.
    rewrite !Zlength_sublist by (try rewrite Zlength_sublist; lia). list_solve.
  - rewrite Znth_app2 by lia. unfold put. rewrite !Zlength_sublist by lia. list_solve.
Qed.

(* ---- the match copy (pure parts) ----
   x0 = k + ll; the match continues at di = x0 + d (d = 0, or d = dl after the extDict part) from
   si = di - off; fs_J: any final array that keeps c2 below di and holds the forward copy on [di, x0 + ml)
   is exec_c there *)
Definition fs_J (c c2: list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) (d: Z) : Prop :=
  forall c', Zlength c' = Zlength c ->
    (forall p, k <= p < k + ll + d -> Znth p c' = Znth p c2) ->
    sublist (k + ll + d) (k + ll + ml) c' =
      sublist (k + ll + d) (k + ll + ml) (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat (ml - d))) ->
    ext_read_ok x k e ll ml off ps ->
    sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x).

(* the match lies in the prefix *)
Lemma fs_J_prefix (c cA: list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= off <= k + ll - ps -> 1 <= ml ->
  k + ll + ml + 32 <= Zlength c -> Zlength cA = Zlength c -> fs_lit_ok c cA k ll Lv ->
  fs_J c cA k e ll ml off ps x Lv 0.
Proof.
  intros HL Hps Hll Hoff Hml HN HcA Hlit c' Hc' Hag Hsub _.
  rewrite Z.add_0_r in Hag, Hsub. replace (Z.to_nat (ml - 0)) with (Z.to_nat ml) in Hsub by (f_equal; lia).
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_prefix c cA c' k ps ml off (k + ll) Lv x); try lia; auto.
  intros p Hp. apply Hlit; lia.
Qed.

(* dl < ml bytes from the extDict were moved to [x0, x0 + dl) (c2), the rest follows from the prefix *)
Lemma fs_J_ext (c cA c2: list val) (k e ll ml off ps dl: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml + 32 <= e -> e <= Zlength c ->
  dl = off - (k + ll - ps) -> 0 < dl < ml -> dl <= ext_len x -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> fs_lit_ok c cA k ll Lv -> Zlength c2 = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p c2 = Znth p cA) ->
  sublist (k + ll) (k + ll + dl) c2 = sublist (ext_end x - dl) (ext_end x) (ext_src cA x) ->
  fs_J c c2 k e ll ml off ps x Lv dl.
Proof.
  intros HL Hps Hll Hml He HeN Hdl Hdl1 Hdl2 Hx HcA Hlit Hc2 Hc2o Hc2s c' Hc' Hag Hsub Hrd.
  assert (Hrd2 := exec_ext_read c cA k e ll ml off ps (k + ll + 32) dl Lv x HL Hdl ltac:(lia) ltac:(lia)
                    ltac:(unfold WILDCOPY_OVERLENGTH; lia) ltac:(lia) HeN Hml Hx HcA Hlit Hrd).
  replace (Z.min ml dl) with dl in Hrd2 by lia.
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_ext c cA c2 c' k ps ml off (k + ll) dl dl Lv x).
  all: first [ lia | assumption
             | (intros p Hp; first [apply Hlit | apply Hc2o | apply Hag]; lia)
             | (replace (ext_end x - dl + dl) with (ext_end x) by lia; assumption)
             | (intros _; replace ps with (k + ll + dl - off) by lia; exact Hsub) ].
Qed.

(* the whole match comes from the extDict (ml <= dl): one memmove *)
Lemma fs_full_ext (c cA c': list val) (k e ll ml off ps dl: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 0 <= ll -> 1 <= ml -> k + ll + ml + 32 <= e -> e <= Zlength c ->
  dl = off - (k + ll - ps) -> 0 < dl -> ml <= dl -> dl <= ext_len x -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> fs_lit_ok c cA k ll Lv -> Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + ml) -> Znth p c' = Znth p cA) ->
  sublist (k + ll) (k + ll + ml) c' = sublist (ext_end x - dl) (ext_end x - dl + ml) (ext_src cA x) ->
  ext_read_ok x k e ll ml off ps ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x).
Proof.
  intros HL Hps Hll Hml He HeN Hdl Hdl1 Hdl2 Hdl3 Hx HcA Hlit Hc' Hc'o Hc's Hrd.
  assert (Hrd2 := exec_ext_read c cA k e ll ml off ps (k + ll + 32) dl Lv x HL Hdl ltac:(lia) ltac:(lia)
                    ltac:(unfold WILDCOPY_OVERLENGTH; lia) ltac:(lia) HeN Hml Hx HcA Hlit Hrd).
  replace (Z.min ml dl) with ml in Hrd2 by lia.
  replace (k + (ll + ml)) with (k + ll + ml) by lia.
  apply (exec_glue_ext c cA c' c' k ps ml off (k + ll) dl ml Lv x).
  all: first [ lia | assumption | (intros; lia)
             | (intros p Hp; first [apply Hlit | apply Hc'o]; lia) | (intros; reflexivity) ].
Qed.

(* the wild copy of the match (off >= 16) *)
Lemma fs_wc_facts (c2 g: list val) (si di n: Z) :
  0 <= si < di -> 0 <= n -> di + n + 32 <= Zlength c2 -> Zlength g = 32 ->
  Zlength (wc_within_post c2 si di n g) = Zlength c2 /\
  (forall p, 0 <= p < Zlength c2 -> ~ (di <= p < di + n + 32) -> Znth p (wc_within_post c2 si di n g) = Znth p c2) /\
  sublist di (di + n) (wc_within_post c2 si di n g) = sublist di (di + n) (listcopy c2 si di (Z.to_nat n)).
Proof.
  intros Hs Hn Hd Hg.
  assert (HL: Zlength (listcopy c2 si di (Z.to_nat n)) = Zlength c2) by (apply Zlength_listcopy; lia).
  unfold wc_within_post, WILDCOPY_OVERLENGTH.
  split; [|split].
  - list_solve.
  - intros p Hp Hq. destruct (zlt p di).
    + rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
      rewrite Z.add_0_r. apply listcopy_suffix; lia.
    + rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
      rewrite Znth_app2 by lia. rewrite Znth_sublist by lia. f_equal. lia.
  - list_solve.
Qed.

Lemma fs_oc8_K (off: Z) : 1 <= off < 16 ->
  8 <= oc8_off off /\ oc8_off off mod off = 0 /\ off <= oc8_off off <= 8 + off.
Proof.
  intros H.
  assert (off = 1 \/ off = 2 \/ off = 3 \/ off = 4 \/ off = 5 \/ off = 6 \/ off = 7 \/ off = 8 \/
          off = 9 \/ off = 10 \/ off = 11 \/ off = 12 \/ off = 13 \/ off = 14 \/ off = 15) as E by lia.
  repeat destruct E as [E|E]; subst; compute; repeat split; congruence.
Qed.

Lemma fs_sub_sub (l: list val) (a b c: Z) : 0 <= a <= b -> b <= c -> c <= Zlength l ->
  sublist a b l = sublist a b (sublist 0 c l).
Proof. intros. rewrite sublist_sublist by lia. f_equal; lia. Qed.

(* overlapCopy8, then (n > 8) the wild copy at distance oc8_off off (off < 16) *)
Lemma fs_oc8_facts (c2 g: list val) (off di n: Z) :
  1 <= off < 16 -> 0 <= di - off -> 1 <= n -> di + n + 32 <= Zlength c2 -> Zlength g = 32 ->
  let c3 := listcopy c2 (di - off) di 8 in
  let c' := if n >? 8 then wc_within_post c3 (di + 8 - oc8_off off) (di + 8) (n - 8) g else c3 in
  Zlength c' = Zlength c2 /\
  (forall p, 0 <= p < Zlength c2 -> ~ (di <= p < di + n + 32) -> Znth p c' = Znth p c2) /\
  sublist di (di + n) c' = sublist di (di + n) (listcopy c2 (di - off) di (Z.to_nat n)).
Proof.
  intros Hoff Hdi Hn HN Hg c3 c'.
  destruct (fs_oc8_K off Hoff) as (HK1 & HK2 & HK3).
  assert (Ec3: c3 = listcopy c2 (di - off) di (Z.to_nat 8)) by reflexivity.
  assert (H3: Zlength c3 = Zlength c2) by (rewrite Ec3; apply Zlength_listcopy; lia).
  assert (Hpre: forall n0 E, 0 <= n0 <= E -> di + E <= Zlength c2 ->
            sublist di (di + n0) (listcopy c2 (di - off) di (Z.to_nat E)) =
            sublist di (di + n0) (listcopy c2 (di - off) di (Z.to_nat n0))).
  { intros n0 E ? ?. rewrite (fs_sub_sub (listcopy c2 (di - off) di (Z.to_nat E)) di (di + n0) (di + n0))
      by (rewrite ?Zlength_listcopy; lia).
    rewrite (fs_sub_sub (listcopy c2 (di - off) di (Z.to_nat n0)) di (di + n0) (di + n0))
      by (rewrite ?Zlength_listcopy; lia).
    rewrite listcopy_prefix by lia. reflexivity. }
  unfold c'. destruct (n >? 8) eqn:En.
  - apply Z.gtb_lt in En.
    destruct (fs_wc_facts c3 g (di + 8 - oc8_off off) (di + 8) (n - 8)) as (W1 & W2 & W3); try lia.
    assert (HR: listcopy c3 (di + 8 - oc8_off off) (di + 8) (Z.to_nat (n - 8)) =
                listcopy c2 (di - off) di (Z.to_nat (8 + (n - 8)))).
    { rewrite Ec3.
      rewrite <- lc_reoff with (si := di - off) (di := di) (a := 8) (K := oc8_off off) (m := n - 8); try lia.
      - reflexivity.
      - replace (di - (di - off)) with off by lia. auto. }
    replace (8 + (n - 8)) with n in HR by lia.
    split; [lia | split].
    + intros p Hp Hq. rewrite W2 by lia. rewrite Ec3. apply listcopy_suffix; lia.
    + apply Znth_eq_ext.
      { rewrite !Zlength_sublist; rewrite ?W1, ?H3, ?Zlength_listcopy; lia. }
      intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?W1, ?H3; lia).
      rewrite !Znth_sublist by (rewrite ?W1, ?H3, ?Zlength_listcopy; lia).
      destruct (zlt i 8).
      * rewrite W2 by lia. rewrite Ec3.
        assert (E1 := Hpre 8 n ltac:(lia) ltac:(lia)).
        assert (E2: Znth i (sublist di (di + 8) (listcopy c2 (di - off) di (Z.to_nat n))) =
                    Znth i (sublist di (di + 8) (listcopy c2 (di - off) di (Z.to_nat 8)))) by (rewrite E1; auto).
        rewrite !Znth_sublist in E2 by (rewrite ?Zlength_listcopy; lia). auto.
      * assert (E3: Znth (i - 8) (sublist (di + 8) (di + 8 + (n - 8)) (wc_within_post c3 (di + 8 - oc8_off off) (di + 8) (n - 8) g)) =
                    Znth (i - 8) (sublist (di + 8) (di + 8 + (n - 8)) (listcopy c3 (di + 8 - oc8_off off) (di + 8) (Z.to_nat (n - 8)))))
          by (rewrite W3; auto).
        rewrite HR in E3. rewrite !Znth_sublist in E3 by (rewrite ?W1, ?H3, ?Zlength_listcopy; lia).
        replace (i - 8 + (di + 8)) with (i + di) in E3 by lia. auto.
  - rewrite Z.gtb_ltb in En. apply Z.ltb_ge in En. split; [auto | split].
    + intros p Hp Hq. rewrite Ec3. apply listcopy_suffix; lia.
    + rewrite Ec3. apply Hpre; lia.
Qed.

(* the success post from exactness: the bytes are defined when everything read is *)
Lemma fs_post (c c': list val) (k e ll ml off ps: Z) (x: ext_seg) (Lv: list val) :
  Zlength Lv = ll -> 0 <= ps <= k -> 1 <= ml -> 1 <= off <= k + ll - ps + ext_len x ->
  k + ll + ml <= Zlength c -> exec_ext_ok x c -> Zlength c' = Zlength c ->
  (ext_read_ok x k e ll ml off ps ->
     sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x)) ->
  ext_read_ok x k e ll ml off ps ->
  sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k Lv ml off ps x) /\
  (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val Lv -> ext_def x c ->
   Forall is_byte_val (sublist k (k + (ll + ml)) c')).
Proof.
  intros HL Hps Hml Hoff HN Hx Hc' Heq Hrd. specialize (Heq Hrd). split; [exact Heq|].
  intros B1 B2 B3. rewrite Heq. subst ll.
  replace (k + (Zlength Lv + ml)) with (k + Zlength Lv + ml) by lia.
  apply exec_c_bytes; auto; lia.
Qed.

(* for (;;break) { c } rest (RETURN_ERROR_IF, DEBUGLOG): c, then rest from Q *)
Lemma fs_loop_seq {Espec: OracleKind} {cs: compspecs} Delta (P Q: environ -> mpred) c rest R :
  semax Delta P c (loop1_ret_assert Q (overridePost Q R)) -> semax Delta Q rest R ->
  semax Delta P (Ssequence (Sloop c Sbreak) rest) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [|exact H2].
  apply semax_loop with Q; [exact H1|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

(* for (;;break) {} : a no-op *)
Lemma fs_skipbreak_seq {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R :
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
  intros H. apply fs_loop_seq with P; [|exact H].
  eapply semax_post; [| | | | apply semax_skip].
  all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
  - intros rho; simpl; apply andp_left2, derives_refl.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros rho; simpl; apply andp_left2, FF_left.
  - intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

(* (ptr_a - ptr_b) cast to size_t, compared with a size_t n by > (RETURN_ERROR_IF) *)
Lemma fs_gt_diff (p: val) (a b n: Z) : isptr p -> 0 <= a - b <= Int64.max_unsigned -> 0 <= n <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1))) sem_cast_pointer sem_cast_pointer
      (Vlong (Int64.repr n)) (force_val (sem_sub_pp tuchar (offset_val a p) (offset_val b p))) with
  | Some v' => v' | None => Vundef end = Vint (if zlt (a - b) n then Int.one else Int.zero).
Proof.
  intros Hp Hab Hn. rewrite cp_sub_pp by auto. simpl. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia. destruct (zlt (a - b) n); reflexivity.
Qed.

(* the statements before RETURN_ERROR_IF's return *)
Ltac fs_if0_loop :=
  match goal with |- semax _ ?P _ _ => apply (fs_loop_seq _ P P); [forward_if; [exfalso; auto | forward; apply ENTAIL_refl] | ] end.
Ltac fs_err_prefix := apply fs_skipbreak_seq; fs_if0_loop; apply fs_skipbreak_seq; apply fs_skipbreak_seq.

(* the PROP part of an error return (-n cast to size_t) *)
Lemma fs_err_ret (n: Z) (b: bool) (P Q: Prop) : 0 < n < 120 -> b = true ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn ->. unfold err_code, is_error_code.
  split; [rep_lia|]. split; [apply Z.ltb_lt; lia|]. split; [intros E; apply Z.ltb_ge in E; lia|].
  split; [intros E; apply Z.ltb_ge in E; lia|].
  f_equal. apply cp_repr_eqm. replace (2 ^ 64 - n) with (- n + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma fs_dec_err (n: Z) : 0 < n < 120 -> n <> 80 -> n <> 82 -> dec_err (err_code n).
Proof.
  intros. unfold dec_err, err_code, is_error_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

(* after the literal copy nothing outside [k, hi) changed *)
Lemma fs_lit_unch (c cA: list val) (k ll hi: Z) (Lv: list val) :
  Zlength Lv = ll -> 0 <= k -> 0 <= ll -> k + ll + 32 <= hi -> k + ll <= Zlength c ->
  fs_lit_ok c cA k ll Lv -> unchanged_outside c cA k hi.
Proof.
  intros HL Hk Hll Hhi Hc H i Hi Hout. rewrite H by lia.
  unfold put. rewrite HL. list_solve.
Qed.

Ltac fs_tf := match goal with
  | H: typed_true _ _ |- _ => solve [inv H]
  | H: typed_false _ _ |- _ => solve [inv H]
  | H: _ <> _ |- _ => solve [exfalso; apply H; reflexivity]
  | H: Int.one = _ |- _ => solve [inv H]
  | H: Int.repr 1 = _ |- _ => solve [inv H] end.

Ltac fs_fw := forward; repeat (first [rewrite fs_add_pl by auto | rewrite fs_sub_pl by auto |
                                      rewrite fs_sub_pl' by auto |
                                      rewrite fs_sub_pi by (auto; rep_lia)]).

Lemma fs_add_ptr_long {cs: compspecs} (p: val) (a n: Z) : isptr p ->
  force_val (sem_add_ptr_long tuchar (offset_val a p) (Vlong (Int64.repr n))) = offset_val (a + n) p.
Proof. intros Hp. exact (fs_add_pl p a n Hp). Qed.

Ltac fs_sb := entailer!; try apply prop_right; try (apply cp_sameblock; auto).

Lemma fs_lt (a b: Z) : Int64.min_signed <= a <= Int64.max_signed -> Int64.min_signed <= b <= Int64.max_signed ->
  Int64.lt (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros. unfold Int64.lt. rewrite !Int64.signed_repr by lia.
  destruct (zlt a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma fs_fa (n: Z) (p: val) (i: Z) :
  field_compatible (tarray tuchar n) [] p -> 0 <= i < n ->
  field_address (tarray tuchar n) (SUB i) p = offset_val i p.
Proof.
  intros. rewrite field_address_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

(* the literals in the output array, at least 32 bytes after op: copy16 (two pieces), then [ll > 16] the
   wild copy in the array (dst before src) *)
Lemma fs_lit_c16 (c: list val) (k li ll: Z) :
  0 <= k -> 0 <= ll <= 16 -> k + 16 <= li -> li + 16 <= Zlength c ->
  fs_lit_ok c (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c) k ll
    (sublist li (li + ll) c).
Proof.
  intros Hk Hll Hkl Hlc p Hp Hq. unfold copied, put. list_solve.
Qed.

Lemma fs_lit_wc (c g: list val) (k li ll: Z) :
  0 <= k -> 16 < ll -> k + 32 <= li -> li + ll + 32 <= Zlength c -> Zlength g = 32 ->
  fs_lit_ok c (wc_within_post (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c)
                 (li + 16) (k + 16) (ll - 16) g) k ll (sublist li (li + ll) c).
Proof.
  intros Hk Hll Hkl Hlc Hg p Hp Hq.
  set (c1 := copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c).
  assert (H1: Zlength c1 = Zlength c) by (unfold c1, copied; list_solve).
  assert (H1a: forall q, 0 <= q < Zlength c -> ~ (k <= q < k + 16) -> Znth q c1 = Znth q c)
    by (intros; unfold c1, copied; list_solve).
  assert (H1b: forall q, k <= q < k + 16 -> Znth q c1 = Znth (li + q - k) c)
    by (intros; unfold c1, copied; list_solve).
  assert (HL: Zlength (listcopy c1 (li + 16) (k + 16) (Z.to_nat (ll - 16))) = Zlength c)
    by (rewrite Zlength_listcopy; lia).
  clearbody c1.
  unfold wc_within_post, WILDCOPY_OVERLENGTH.
  destruct (zlt p (k + ll)).
  - rewrite Znth_app1 by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. rewrite Z.add_0_r.
    destruct (zlt p k).
    + rewrite listcopy_suffix by lia. rewrite H1a by lia. rewrite ecl_Znth_put_out by (rewrite ?Zlength_sublist; lia).
      reflexivity.
    + rewrite ecl_Znth_put_in by (rewrite ?Zlength_sublist; lia). rewrite Znth_sublist by lia.
      destruct (zlt p (k + 16)).
      * rewrite listcopy_suffix by lia. rewrite H1b by lia. f_equal; lia.
      * replace p with (k + 16 + (p - k - 16)) at 1 by lia. rewrite listcopy_dbs by lia.
        rewrite H1a by lia. f_equal; lia.
  - rewrite Znth_app2 by (rewrite Zlength_sublist; lia). rewrite Zlength_sublist by lia.
    rewrite Znth_app2 by lia. rewrite Znth_sublist by lia.
    rewrite ecl_Znth_put_out by (rewrite ?Zlength_sublist; lia).
    rewrite <- H1a by lia. f_equal. lia.
Qed.

(* the success post of the fast split executor from the final array's frame and exactness *)
Lemma fs_post_gen (c c': list val) (k e li lim ll ml off ps: Z) (x: ext_seg) (lp: val) :
  0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> 0 <= ps <= k -> k <= e <= Zlength c -> 0 <= li ->
  li + ll <= lim -> lim + 32 <= e -> k + ml + 32 <= li ->
  1 <= off <= k + ll - ps + ext_len x -> exec_ext_ok x c -> Zlength c' = Zlength c ->
  unchanged_outside c c' k (k + ll + ml + 32) ->
  (ext_read_ok x k e ll ml off ps ->
     sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) ->
  is_error_code (ll + ml) = exec_split_err k e li ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false ->
     ll + ml = ll + ml /\ lp = lp /\
     unchanged_outside c c' k (Z.min (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) /\
     (ext_read_ok x k e ll ml off ps ->
        (lit_exact_split k li ll ->
           sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
        (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
         ext_def x c -> Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros Hll Hml Hps Hke Hli Hlil Hlim Hfast Hoff Hx Hc' Hun Hex.
  assert (E1: is_error_code (ll + ml) = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  assert (E2: exec_split_err k e li ll ml off ps (ext_len x) = false).
  { unfold exec_split_err.
    rewrite (proj2 (Z.ltb_ge (e - k) (ll + ml))) by lia.
    rewrite (proj2 (Z.ltb_ge li k)) by lia.
    rewrite (proj2 (Z.ltb_ge (k + ll - ps + ext_len x) off)) by lia. reflexivity. }
  rewrite E1, E2. split; [reflexivity|]. split; [discriminate|]. intros _.
  split; [reflexivity|]. split; [reflexivity|]. split.
  { replace (Z.min (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll)))
      with (k + ll + ml + 32) by (unfold WILDCOPY_OVERLENGTH; lia). exact Hun. }
  intros Hrd.
  destruct (fs_post c c' k e ll ml off ps x (sublist li (li + ll) c)) as [Ex By]; auto; try lia;
    try (rewrite Zlength_sublist; lia).
  all: try (split; [intros _; exact Ex | exact By]).
Qed.

Lemma fs_final (c c2 c': list val) (k e li lim ll ml off ps d: Z) (x: ext_seg) (lp: val) :
  0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> 0 <= ps <= k -> k <= e <= Zlength c -> 0 <= li ->
  li + ll <= lim -> lim + 32 <= e -> k + ml + 32 <= li ->
  1 <= off <= k + ll - ps + ext_len x -> exec_ext_ok x c ->
  0 <= d < ml -> Zlength c2 = Zlength c -> unchanged_outside c c2 k (k + ll + ml + 32) ->
  fs_J c c2 k e ll ml off ps x (sublist li (li + ll) c) d -> Zlength c' = Zlength c ->
  (forall p, 0 <= p < Zlength c -> ~ (k + ll + d <= p < k + ll + ml + 32) -> Znth p c' = Znth p c2) ->
  sublist (k + ll + d) (k + ll + ml) c' =
    sublist (k + ll + d) (k + ll + ml) (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat (ml - d))) ->
  is_error_code (ll + ml) = exec_split_err k e li ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false ->
     ll + ml = ll + ml /\ lp = lp /\
     unchanged_outside c c' k (Z.min (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) /\
     (ext_read_ok x k e ll ml off ps ->
        (lit_exact_split k li ll ->
           sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
        (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
         ext_def x c -> Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros Hll Hml Hps Hke Hli Hlil Hlim Hfast Hoff Hx Hd Hc2 Hun2 HJ Hc' Hfr Hsub.
  apply (fs_post_gen c c' k e li lim); auto.
  - intros i Hi Hn. rewrite Hfr by lia. apply Hun2; auto.
  - intros Hrd. apply HJ; auto.
    intros p Hp. apply Hfr; lia.
Qed.

Lemma fs_bf (b: bool) : typed_false tint (bool2val b) -> b = false.
Proof. destruct b; [intros Hf; inversion Hf | auto]. Qed.

Lemma fs_bt (b: bool) : typed_true tint (bool2val b) -> b = true.
Proof. destruct b; [auto | intros Hf; inversion Hf]. Qed.

Lemma fs_split3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + m)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + m - i) with m by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.

Lemma fs_mm_put (c: list val) (si di n: Z) :
  0 <= si -> 0 <= n -> si + n <= Zlength c ->
  mm_result c (Zlength c) si di n = put c di (sublist si (si + n) c).
Proof. intros. unfold mm_result, put. rewrite Zlength_sublist by lia. f_equal. f_equal. f_equal. lia. Qed.

Lemma fs_join_put (sh: share) (n i m: Z) (l v: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n -> Zlength v = m ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) v (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) (put l i v) p.
Proof.
  intros. rewrite (fs_split3 sh n i m (put l i v) p) by (auto; unfold put; list_solve).
  unfold put. subst m.
  replace (sublist 0 i (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with (sublist 0 i l) by list_solve.
  replace (sublist i (i + Zlength v) (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l)) with v by list_solve.
  replace (sublist (i + Zlength v) n (sublist 0 i l ++ v ++ sublist (i + Zlength v) (Zlength l) l))
    with (sublist (i + Zlength v) n l) by list_solve.
  apply derives_refl.
Qed.

Lemma fs_join3 (sh: share) (n i m: Z) (l: list val) (p: val) :
  0 <= i -> 0 <= m -> i + m <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar i) (sublist 0 i l) p *
  data_at sh (tarray tuchar m) (sublist i (i + m) l) (offset_val i p) *
  data_at sh (tarray tuchar (n - (i + m))) (sublist (i + m) n l) (offset_val (i + m) p) |--
  data_at sh (tarray tuchar n) l p.
Proof. intros. rewrite (fs_split3 sh n i m l p) by auto. apply derives_refl. Qed.

(* the extDict part of the match: dl bytes moved from the extDict (dl < ml), the rest follows from the prefix *)
Lemma fs_part (c cA: list val) (k e li ll ml off ps: Z) (x: ext_seg) :
  0 <= ll -> 1 <= ml -> 0 <= ps <= k -> k <= e <= Zlength c -> 0 <= li -> li + ll <= Zlength c ->
  k + ll + ml + 32 <= e ->
  k + ll - ps < off <= k + ll - ps + ext_len x -> off - (k + ll - ps) < ml -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> fs_lit_ok c cA k ll (sublist li (li + ll) c) ->
  Zlength (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + (off - (k + ll - ps)))
             (ext_src cA x))) = Zlength c /\
  unchanged_outside c (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps)))
             (ext_end x - (off - (k + ll - ps)) + (off - (k + ll - ps))) (ext_src cA x))) k (k + ll + ml + 32) /\
  fs_J c (put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps)))
             (ext_end x - (off - (k + ll - ps)) + (off - (k + ll - ps))) (ext_src cA x)))
    k e ll ml off ps x (sublist li (li + ll) c) (off - (k + ll - ps)).
Proof.
  intros Hll Hml Hps Hke Hli Hlil Hcap Hoff Hdl Hx HcA Hlit.
  set (dl := off - (k + ll - ps)) in *.
  assert (HB: 0 <= ext_end x - dl /\ ext_end x <= Zlength (ext_src cA x)).
  { unfold exec_ext_ok in Hx. destruct x as [| e1 elen | shx eb en ec e1 elen]; simpl in *; lia. }
  set (bs := sublist (ext_end x - dl) (ext_end x - dl + dl) (ext_src cA x)).
  assert (Hbs: Zlength bs = dl) by (unfold bs; rewrite Zlength_sublist; lia).
  assert (Hun: unchanged_outside c cA k (k + ll + ml + 32))
    by (apply (fs_lit_unch c cA k ll _ (sublist li (li + ll) c)); auto; try lia; rewrite Zlength_sublist; lia).
  assert (Hc2: Zlength (put cA (k + ll) bs) = Zlength c) by (rewrite ecl_Zlength_put; lia).
  assert (Hc2o: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + dl) -> Znth p (put cA (k + ll) bs) = Znth p cA).
  { intros p Hp Hq. rewrite ecl_Znth_put_out by (rewrite ?HcA, ?Hbs; lia). reflexivity. }
  split; [exact Hc2|]. split.
  - intros i Hi Hn. rewrite Hc2o by lia. apply Hun; auto.
  - apply (fs_J_ext c cA _ k e ll ml off ps dl x (sublist li (li + ll) c)); auto; try lia.
    + rewrite Zlength_sublist; lia.
    + replace (sublist (ext_end x - dl) (ext_end x) (ext_src cA x)) with bs by (unfold bs; f_equal; lia).
      clearbody bs. unfold put. rewrite Hbs. list_solve.
Qed.

(* the whole match from the extDict (ml <= dl): one memmove, then the post *)
Lemma fs_post_full (c cA: list val) (k e li lim ll ml off ps: Z) (x: ext_seg) (lp: val) :
  0 <= ll <= 2 ^ 24 -> 1 <= ml <= 2 ^ 24 -> 0 <= ps <= k -> k <= e <= Zlength c -> 0 <= li ->
  li + ll <= lim -> lim + 32 <= e -> k + ml + 32 <= li ->
  k + ll - ps < off <= k + ll - ps + ext_len x -> ml <= off - (k + ll - ps) -> exec_ext_ok x c ->
  Zlength cA = Zlength c -> fs_lit_ok c cA k ll (sublist li (li + ll) c) ->
  let c' := put cA (k + ll) (sublist (ext_end x - (off - (k + ll - ps))) (ext_end x - (off - (k + ll - ps)) + ml)
                               (ext_src cA x)) in
  Zlength c' = Zlength c /\
  is_error_code (ll + ml) = exec_split_err k e li ll ml off ps (ext_len x) /\
  (is_error_code (ll + ml) = true -> unchanged_outside c c' k e /\ dec_err (ll + ml)) /\
  (is_error_code (ll + ml) = false ->
     ll + ml = ll + ml /\ lp = lp /\
     unchanged_outside c c' k (Z.min (Z.min e (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) /\
     (ext_read_ok x k e ll ml off ps ->
        (lit_exact_split k li ll ->
           sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps x)) /\
        (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
         ext_def x c -> Forall is_byte_val (sublist k (k + (ll + ml)) c')))).
Proof.
  intros Hll Hml Hps Hke Hli Hlil Hlim Hfast Hoff Hdl Hx HcA Hlit c'.
  set (dl := off - (k + ll - ps)) in *.
  assert (HB: 0 <= ext_end x - dl /\ ext_end x <= Zlength (ext_src cA x)).
  { unfold exec_ext_ok in Hx. destruct x as [| e1 elen | shx eb en ec e1 elen]; simpl in *; lia. }
  set (bs := sublist (ext_end x - dl) (ext_end x - dl + ml) (ext_src cA x)) in *.
  assert (Hbs: Zlength bs = ml) by (unfold bs; rewrite Zlength_sublist; lia).
  assert (Hun: unchanged_outside c cA k (k + ll + ml + 32))
    by (apply (fs_lit_unch c cA k ll _ (sublist li (li + ll) c)); auto; try lia; rewrite Zlength_sublist; lia).
  assert (Hc': Zlength c' = Zlength c) by (unfold c'; rewrite ecl_Zlength_put; lia).
  assert (Hc'o: forall p, 0 <= p < Zlength c -> ~ (k + ll <= p < k + ll + ml) -> Znth p c' = Znth p cA).
  { intros p Hp Hq. unfold c'. rewrite ecl_Znth_put_out by (rewrite ?HcA, ?Hbs; lia). reflexivity. }
  split; [exact Hc'|].
  apply (fs_post_gen c c' k e li lim); auto; try lia.
  - intros i Hi Hn. rewrite Hc'o by lia. apply Hun; auto.
  - intros Hrd. apply (fs_full_ext c cA c' k e ll ml off ps dl x (sublist li (li + ll) c)); auto; try lia.
    + rewrite Zlength_sublist; lia.
    + unfold c'. transitivity bs; [| reflexivity]. clearbody bs. unfold put. rewrite Hbs. list_solve.
Qed.

(* ---------- bytes in, bytes out (the byte_cells clause of exec_split_spec) ---------- *)
Definition fsb_bc (c c': list val) (x: ext_seg) : Prop := byte_cells c -> ext_bytes x -> byte_cells c'.

Lemma fsb_refl (c: list val) (x: ext_seg) : fsb_bc c c x.
Proof. intros H _. exact H. Qed.

Lemma fsb_listcopy (l: list val) (si di: Z) (n: nat) :
  0 <= si -> si + Z.of_nat n <= Zlength l -> byte_cells l -> byte_cells (listcopy l si di n).
Proof.
  revert l si di. induction n as [|m IH]; intros l si di Hs Hn Hl; simpl; [exact Hl|].
  rewrite Nat2Z.inj_succ in Hn.
  apply IH; [lia | rewrite Zlength_upd_Znth; lia |].
  apply Forall_upd_Znth; [exact Hl|].
  unfold byte_cells in Hl. rewrite Forall_forall in Hl. apply Hl, Znth_In. lia.
Qed.

Lemma fsb_wc_ext (b: bool) (n: Z) : 0 <= n -> 0 <= wc_ext b n <= n + 32.
Proof.
  intros Hn. unfold wc_ext, WILDCOPY_VECLEN. destruct b.
  - pose proof (Z.mul_div_le (n + 7) 8 ltac:(lia)). pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)). lia.
  - destruct (n <=? 16) eqn:E; [lia|]. apply Z.leb_gt in E.
    pose proof (Z.mul_div_le (n - 16 + 31) 32 ltac:(lia)). pose proof (Z.div_pos (n - 16 + 31) 32 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma fsb_wc (c g: list val) (si di n: Z) (b: bool) :
  0 <= si -> 0 <= n -> si + n + 32 <= Zlength c ->
  g = sublist (di + n) (di + n + WILDCOPY_OVERLENGTH) (listcopy c si di (Z.to_nat (wc_ext b n))) ->
  byte_cells c -> byte_cells (wc_within_post c si di n g).
Proof.
  intros Hs Hn HN Hg Hc. pose proof (fsb_wc_ext b n Hn). subst g. unfold wc_within_post, byte_cells in *.
  apply Forall_app; split; [apply Forall_sublist, fsb_listcopy; auto; lia|].
  apply Forall_app; split; [apply Forall_sublist, fsb_listcopy; auto; lia|].
  apply Forall_sublist; auto.
Qed.

Lemma fsb_put (c v: list val) (i: Z) : byte_cells c -> byte_cells v -> byte_cells (put c i v).
Proof.
  intros Hc Hv. unfold put, byte_cells in *.
  apply Forall_app; split; [apply Forall_sublist; auto|].
  apply Forall_app; split; [auto | apply Forall_sublist; auto].
Qed.

Lemma fsb_sub (c: list val) (lo hi: Z) : byte_cells c -> byte_cells (sublist lo hi c).
Proof. intros Hc. unfold byte_cells in *. apply Forall_sublist; auto. Qed.

Lemma fsb_c1 (c: list val) (k li: Z) :
  byte_cells c -> byte_cells (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c).
Proof.
  intros Hc. unfold copied.
  repeat (first [apply Forall_app; split | apply fsb_sub]); auto.
Qed.

Lemma fsb_trans (c c2 c': list val) (x: ext_seg) :
  fsb_bc c c2 x -> (byte_cells c2 -> byte_cells c') -> fsb_bc c c' x.
Proof. intros H1 H2 Hc Hx. auto. Qed.

(* ---- the exact clause of ZSTD_execSequenceSplitLitBuffer's fast path (lexec_split's fast branch) ----
   fsx_lit: the output array after the literal copy (ZSTD_copy16 from litPtr, then, past 16 literals, the
   no-overlap wild copy of the rest); the match: lmatch at oLitEnd = k + ll is lprefix at di = k + ll + d after
   the extDict part (d = 0 without one), and lprefix is what the last copies (one wild copy for off >= 16,
   ZSTD_overlapCopy8 then a wild copy otherwise) store *)
Definition fsx_lit (c: list val) (k li ll: Z) : list val :=
  if ll >? 16 then lwild (lmove 16 c k LW li) (k + 16) LW (li + 16) (ll - 16) false else lmove 16 c k LW li.

(* the same as a proposition about the array (an equation VST's automation does not substitute away) *)
Definition fsx_eq (cA c: list val) (k li ll: Z) : Prop := cA = fsx_lit c k li ll.

Lemma fsx_fast (ps vs de oend: Z) (c: list val) (op li llim ll ml off: Z) :
  ll <= llim - li -> ll + ml <= li + ll - WILDCOPY_OVERLENGTH - op ->
  lexec_split ps vs de oend c op li llim ll ml off = lmatch ps vs de (fsx_lit c op li ll) (op + ll) ml off None.
Proof. intros H1 H2. rewrite xg_lexec_split_fast by lia. unfold fsx_lit. reflexivity. Qed.

(* the literals: at most 16 (ZSTD_copy16 only) *)
Lemma fsx_lit_short (c: list val) (k li ll: Z) :
  ll <= 16 -> 0 <= k -> k + 16 <= li -> li + 16 <= Zlength c ->
  copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c = fsx_lit c k li ll.
Proof.
  intros. unfold fsx_lit. replace (ll >? 16) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  apply xg_copied_in; lia.
Qed.

(* more than 16: ZSTD_copy16, then the wild copy of the rest within the array (no overlap) *)
Lemma fsx_lit_long (c c1 g: list val) (k li ll: Z) :
  16 < ll -> 0 <= k -> k + 16 <= li -> li + 16 <= Zlength c ->
  c1 = copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c ->
  wc_within_post c1 (li + 16) (k + 16) (ll - 16) g = lwild c1 (k + 16) LW (li + 16) (ll - 16) false ->
  wc_within_post c1 (li + 16) (k + 16) (ll - 16) g = fsx_lit c k li ll.
Proof.
  intros H1 H2 H3 H4 Hc1 Hw. unfold fsx_lit. replace (ll >? 16) with true by (symmetry; apply Z.gtb_lt; lia).
  rewrite Hw. rewrite Hc1. rewrite xg_copied_in by lia. reflexivity.
Qed.

(* the match lies in the prefix (d = 0) *)
Lemma fsx_prefix (x: ext_seg) (cA: list val) (k ll ml off ps: Z) :
  off <= k + ll - ps ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => lmatch ps (ps - ext_len x) (ext_end x) cA (k + ll) ml off None = lprefix cA (k + ll) (k + ll - off) ml off None
  end.
Proof. intros H. destruct x; try exact I; apply xg_lmatch_prefix; lia. Qed.

(* the match starts in the extDict (in the output array) and continues in the prefix: memmove of dl bytes *)
Lemma fsx_span (cA: list val) (ps elen e1 k ll ml off dl: Z) :
  dl = off - (k + ll - ps) -> 0 < dl < ml -> 0 <= e1 - dl -> e1 <= Zlength cA -> 0 <= k + ll ->
  k + ll + dl <= Zlength cA ->
  lmatch ps (ps - elen) e1 cA (k + ll) ml off None =
  lprefix (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)) (k + ll + dl) ps (ml - dl) off None.
Proof.
  intros Hdl H1 H2 H3 H4 H5. rewrite xg_lmatch_span by lia.
  replace (off - (k + ll - ps)) with dl by lia. replace (k + ll + dl - off) with ps by lia.
  rewrite <- (xg_mm cA (e1 - dl) (k + ll) dl) by lia. rewrite fs_mm_put by lia. reflexivity.
Qed.

(* the whole match in the extDict (in the output array): one memmove *)
Lemma fsx_ext_full (c cA: list val) (k e li lim ll ml off ps e1 elen dl: Z) :
  cA = fsx_lit c k li ll -> ll <= lim - li -> k + ml + 32 <= li -> dl = off - (k + ll - ps) -> 0 < dl ->
  ml <= dl -> 0 <= e1 - dl -> e1 <= Zlength cA -> 0 <= k + ll -> k + ll + ml <= Zlength cA -> 0 <= ml ->
  is_error_code (ll + ml) = false ->
  put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA) = lexec_split ps (ps - elen) e1 e c k li lim ll ml off.
Proof.
  intros HcA H1 H2 Hdl H3 H4 H5 H6 H7 H8 H9 _.
  rewrite fsx_fast by (unfold WILDCOPY_OVERLENGTH; lia). rewrite <- HcA.
  rewrite xg_lmatch_ext by lia. replace (e1 - (off - (k + ll - ps))) with (e1 - dl) by lia.
  rewrite <- (xg_mm cA (e1 - dl) (k + ll) ml) by lia. rewrite fs_mm_put by lia. reflexivity.
Qed.

(* the last copy of the match, off >= 16: one wild copy (no overlap) *)
Lemma fsx_pre16 (c2 c': list val) (op off n: Z) :
  16 <= off -> c' = lwild c2 op LW (op - off) n false -> lprefix c2 op (op - off) n off None = c'.
Proof.
  intros H Hc. unfold lprefix. replace (off >=? 16) with true by (symmetry; apply Z.geb_le; lia).
  exact (eq_sym Hc).
Qed.

(* off < 16: ZSTD_overlapCopy8, then (more than 8 bytes) the wild copy with overlap *)
Lemma fsx_ov8 (c2 c3 c': list val) (op off n: Z) :
  off < 16 -> lov8 c2 op (op - off) off = ((c3, op + 8), op + 8 - oc8_off off) ->
  (if n >? 8 then c' = lwild c3 (op + 8) LW (op + 8 - oc8_off off) (n - 8) true else c' = c3) ->
  lprefix c2 op (op - off) n off None = c'.
Proof.
  intros H Hov Hc. unfold lprefix. replace (off >=? 16) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  rewrite Hov. cbv beta iota. destruct (n >? 8); exact (eq_sym Hc).
Qed.

(* the PROP part of an error return, with the exact clause (vacuous on an error) *)
Lemma fsx_err_ret (n: Z) (b: bool) (P Q R: Prop) (x: ext_seg) : 0 < n < 120 -> b = true ->
  0 <= err_code n <= Int64.max_unsigned /\ is_error_code (err_code n) = b /\
  (is_error_code (err_code n) = false -> P) /\ (is_error_code (err_code n) = false -> Q) /\
  match x with ExtSep _ _ _ _ _ _ => True | _ => is_error_code (err_code n) = false -> R end /\
  Vlong (Int64.repr (- n)) = Vlong (Int64.repr (err_code n)).
Proof.
  intros Hn Hb. destruct (fs_err_ret n b P Q Hn Hb) as (A & B & C & D & E). subst b.
  refine (conj A (conj B (conj C (conj D (conj _ E))))).
  destruct x; try exact I; intros Hf; rewrite B in Hf; discriminate.
Qed.

(* the exact clause from the literals' array and the match's last copies *)
Lemma fsx_final (x: ext_seg) (c cA c2 c': list val) (k e li lim ll ml off ps d: Z) :
  ll <= lim - li -> k + ml + 32 <= li -> cA = fsx_lit c k li ll ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => lmatch ps (ps - ext_len x) (ext_end x) cA (k + ll) ml off None =
         lprefix c2 (k + ll + d) (k + ll + d - off) (ml - d) off None
  end ->
  lprefix c2 (k + ll + d) (k + ll + d - off) (ml - d) off None = c' ->
  match x with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code (ll + ml) = false -> c' = lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
  end.
Proof.
  intros H1 H2 HcA HJ Hc.
  destruct x; try exact I; intros _; rewrite fsx_fast by (unfold WILDCOPY_OVERLENGTH; lia);
    rewrite <- HcA, HJ, Hc; reflexivity.
Qed.

Lemma body_ZSTD_execSequenceSplitLitBuffer :
  semax_body Vprog EXEC_G f_ZSTD_execSequenceSplitLitBuffer ZSTD_execSequenceSplitLitBuffer_spec.
Proof.
  start_function.
  rename H10 into Xdh, H11 into Xdl, H12 into Xde, H13 into Xov.
  assert (Hoff1: 1 <= off) by lia.
  forward.
  forward_call (shq, sp, ll, ml, off, Tsh, v_sequence).
  assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] ob) as FCc by entailer!.
  assert (Pob: isptr ob) by (destruct FCc; auto).
  assert (Hel: 0 <= ext_len x <= 2 ^ 63 - 1) by (destruct H8; lia).
  unfold seqrep.
  forward. forward. forward. rewrite fs_add_pl by auto.
  forward. forward. forward.
  replace (Int64.add (Int64.repr ll) (Int64.repr ml)) with (Int64.repr (ll + ml))
    by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
  do 8 fs_fw.
  unfold WILDCOPY_OVERLENGTH in *.
  forward.
  forward_if (temp _t'2 (Vint (if (li + ll - 32 - k <? ll + ml) then Int.one else Int.zero))).
  { apply prop_right, cp_sameblock; auto. }
  { rewrite fs_lt_diff in H10 by auto. rewrite fs_lt in H10 by rep_lia.
    destruct (lim - li <? ll) eqn:E; [apply Z.ltb_lt in E; lia | inv H10]. }
  { forward. forward.
    { entailer!. all: apply prop_right, cp_sameblock; auto. }
    entailer!. rewrite cp_sub_pp by auto. simpl. rewrite fs_lt by rep_lia.
    destruct (li + ll - 32 - k <? ll + ml); reflexivity. }
  set (slow := (li + ll - 32 - k <? ll + ml)).
  forward_if (temp _t'3 (Vint (if slow then Int.one else Int.zero))).
  { destruct slow; [| fs_tf]. forward. entailer!. }
  { destruct slow; [fs_tf |]. forward_call tt.
    forward_if.
    { fs_tf. }
    forward. entailer!. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((slow = false) :: P) (LOCALx Q (SEPx R))) end.
  { (* the slow path: ZSTD_execSequenceEndSplitLitBuffer *)
    forward.
    assert (Hsl: orb (lim - li <? ll) (li + ll - WILDCOPY_OVERLENGTH - k <? ll + ml) = true).
    { apply orb_true_iff; right. destruct slow eqn:Es; [|fs_tf]. exact Es. }
    forward_call (gv, sh, ob, c, k, e, Tsh, v_sequence, ll, ml, off, shp, plp, li, lim, ps, x, dE).
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
    forward. Exists r c' lp. entailer!. }
  { destruct slow eqn:Es; [fs_tf|]. forward. entailer!. }
  Intros. rename H10 into Eslow.
  assert (Hfast: k + ml + 32 <= li) by (unfold slow in Eslow; apply Z.ltb_ge in Eslow; lia).
  rewrite Eslow. clear Eslow slow.
  (* the literals: [k, k + ll) := Lv, slack [k + ll, k + ll + 32) *)
  set (Lv := sublist li (li + ll) c).
  unfold MORE_COMMANDS, abbreviate. apply <- seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx _))) _ _ =>
    apply semax_seq' with (P' := EX cA: list val,
      PROPx ((Zlength cA = Zlength c) :: fsb_bc c cA x :: fs_lit_ok c cA k ll Lv :: xd_ub c cA :: fsx_eq cA c k li ll :: P)
      (LOCALx L
      (SEPx [data_at shq t_seq (seqrep ll ml off) sp; data_at Tsh t_seq (seqrep ll ml off) v_sequence;
             data_at Tsh (tptr tuchar) (offset_val (k + ll - off) ob) v_match;
             data_at Tsh (tptr tuchar) (offset_val k ob) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) cA ob;
             data_at shp (tptr tuchar) (offset_val li ob) plp; ext_res x])))
  end.
  { forward. forward.
    sep_apply (tuchar_split_N sh ob (Zlength c) c li eq_refl FCc ltac:(lia)).
    assert (HL16: Forall is_byte_val (sublist 0 16 (sublist li (Zlength c) c))).
    { rewrite sublist_sublist by lia. apply (xd_sub c li (lim + 32)); auto; lia. }
    forward_call (sh, offset_val li ob, sublist li (Zlength c) c, 0, sh, ob, sublist 0 li c, k).
    { cancel. }
    { unfold copy_pre. refine (conj _ (conj _ _)); [apply writable_readable_share; auto | auto |].
      rewrite !Zlength_sublist by lia. repeat split; try lia. apply xd_bv. exact HL16. }
    destruct (xd_copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16) as [Hc1u _];
      try (rewrite Zlength_sublist; lia); try lia; [exact HL16 |].
    assert (HAl: Zlength (sublist 0 li c) = li) by (rewrite Zlength_sublist; lia).
    assert (HBl: Zlength (sublist li (Zlength c) c) = Zlength c - li) by (rewrite Zlength_sublist; lia).
    assert (Hc1: Zlength (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16) = li)
      by (rewrite fs_Zlength_copied; lia).
    rewrite HAl, HBl.
    sep_apply (fs_join2 sh ob (Zlength c) li (Zlength c - li)
                 (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16) (sublist li (Zlength c) c)
                 FCc Hc1 HBl ltac:(lia)).
    set (c1 := copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c).
    assert (Hc1L: Zlength c1 = Zlength c) by (unfold c1; rewrite Zlength_app; lia).
    assert (Hu1: xd_ub c c1).
    { change c1 with (copied (sublist li (Zlength c) c) (sublist 0 li c) 0 k 16 ++ sublist li (Zlength c) c).
      apply xd_ub_join_l; [lia | exact Hc1 | exact Hc1u]. }
    forward. forward_if.
    + rewrite !Int64.unsigned_repr in H10 by rep_lia.
      forward. forward. forward.
      assert (HC1: copy_src_def c1 (li + 16) (k + 16) (ll - 16)).
      { unfold copy_src_def, WILDCOPY_OVERLENGTH. rewrite (proj2 (Z.ltb_ge (li + 16) (k + 16))) by lia.
        replace (sublist (li + 16) (li + 16 + (ll - 16) + 32) c1) with (sublist (li + 16) (li + ll + 32) c)
          by (unfold c1, copied; list_solve).
        apply (xd_sub c li (lim + 32)); auto; lia. }
      forward_call (gv, true, sh, ob, c1, li + 16, k + 16, sh, nullval, @nil val, sh, nullval, @nil val, ll - 16, 0).
      { entailer!. simpl. rewrite Hc1L, !(fs_fa (Zlength c)) by (auto; lia). reflexivity. }
      { rewrite Hc1L. cancel. }
      { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN.
        rewrite Hc1L. split; [exact SH|]. repeat split; try rep_lia; intros; try discriminate; first [exact HC1 | lia]. }
      Intros g. match goal with H: g = _ |- _ => rename H into Hg end.
      match goal with H: context [lwild] |- _ => rename H into Hwx end.
      destruct (xd_wc_within c1 g (li + 16) (k + 16) (ll - 16) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite Hc1L; unfold WILDCOPY_OVERLENGTH; lia) ltac:(rewrite Hc1L; unfold WILDCOPY_OVERLENGTH; lia) HC1 Hg)
        as [Hwu _].
      assert (HuA: xd_ub c (wc_within_post c1 (li + 16) (k + 16) (ll - 16) g)) by (apply (xd_ub_trans c c1); auto).
      assert (Hb1: fsb_bc c (wc_within_post c1 (li + 16) (k + 16) (ll - 16) g) x).
      { apply (fsb_trans c c1); [intros Hc _; unfold c1; apply fsb_c1; auto|].
        eapply fsb_wc; [..|exact Hg]; rewrite ?Hc1L; lia. }
      clear Hg.
      assert (HxA: fsx_eq (wc_within_post c1 (li + 16) (k + 16) (ll - 16) g) c k li ll).
      { unfold fsx_eq. apply (fsx_lit_long c c1 g k li ll); [lia | lia | lia | lia | reflexivity | exact Hwx]. }
      Exists (wc_within_post c1 (li + 16) (k + 16) (ll - 16) g).
      unfold seqrep. rewrite Hc1L. entailer!.
      unfold c1 in *. apply (fs_lit_wc c g k li ll); auto; lia.
    + rewrite !Int64.unsigned_repr in H10 by rep_lia.
      assert (Hb1: fsb_bc c c1 x) by (intros Hc _; unfold c1; apply fsb_c1; auto).
      assert (HxA: fsx_eq c1 c k li ll) by (unfold fsx_eq; apply fsx_lit_short; lia).
      forward. Exists c1. unfold seqrep. entailer!.
      try unfold c1. apply fs_lit_c16; auto; lia. }
  (* the match *)
  Intros cA.
  match goal with H: Zlength cA = Zlength c |- _ => rename H into HcA end.
  match goal with H: fs_lit_ok _ _ _ _ _ |- _ => rename H into HlA end.
  match goal with H: fsb_bc _ _ _ |- _ => rename H into HbA end.
  assert (HLv: Zlength Lv = ll) by (unfold Lv; rewrite Zlength_sublist; lia).
  match goal with H: xd_ub c cA |- _ => rename H into HuA end.
  match goal with H: fsx_eq cA _ _ _ _ |- _ => rename H into HxA end.
  assert (HLvb: Forall is_byte_val Lv) by (unfold Lv; apply (xd_sub c li (lim + 32)); auto; lia).
  assert (HdA: xd_rng cA ps (k + ll)).
  { apply (xd_after_lit c cA Lv k ps ll); auto; try lia.
    - apply xd_Forall_rng; auto; lia.
    - intros p Hp. apply HlA; lia. }
  unfold seqrep. forward. forward. forward.
  match goal with |- semax _ (PROPx _ (LOCALx ?L _)) _ _ =>
    forward_if (EX d: Z, EX c2: list val,
      PROPx [0 <= d < ml; ps <= k + ll + d - off; off <= k + ll - ps + ext_len x;
             Zlength c2 = Zlength c; unchanged_outside c c2 k (k + ll + ml + 32);
             fs_J c c2 k e ll ml off ps x Lv d; fsb_bc c c2 x; xd_ub c c2; xd_rng c2 ps (k + ll + d);
             match x with
             | ExtSep _ _ _ _ _ _ => True
             | _ => lmatch ps (ps - ext_len x) (ext_end x) cA (k + ll) ml off None =
                    lprefix c2 (k + ll + d) (k + ll + d - off) (ml - d) off None
             end]
      (LOCALx L
      (SEPx [data_at shq t_seq (seqrep ll ml off) sp; data_at Tsh t_seq (seqrep ll (ml - d) off) v_sequence;
             data_at Tsh (tptr tuchar) (offset_val (k + ll + d - off) ob) v_match;
             data_at Tsh (tptr tuchar) (offset_val (k + ll + d) ob) v_op; zstd_globals gv;
             data_at sh (tarray tuchar (Zlength c)) c2 ob;
             data_at shp (tptr tuchar) (offset_val (li + ll) ob) plp; ext_res x])))
  end.
  { apply prop_right, cp_sameblock; auto. }
  { (* offset beyond the prefix: the extDict *)
    match goal with H: typed_true _ _ |- _ => rename H into Ht end.
    rewrite fs_gt_diff in Ht by (auto; rep_lia).
    assert (Hoff2: k + ll - ps < off) by (destruct (zlt (k + ll - ps) off); [lia | fs_tf]). clear Ht.
    destruct (Z_lt_ge_dec (k + ll - ps + ext_len x) off) as [Herr|Hok].
    { apply fs_loop_seq with (Q := FF); [|apply semax_ff].
      forward. forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { fs_err_prefix. forward.
        assert (Hun: unchanged_outside c cA k e) by (apply (fs_lit_unch c cA k ll e Lv); auto; lia).
        assert (Hde: dec_err (err_code 20)) by (apply fs_dec_err; lia).
        assert (HuA': forall q, 0 <= q < Zlength c -> Znth q cA = Znth q c \/ is_byte_val (Znth q cA)) by exact HuA.
        Exists (err_code 20) cA (offset_val (li + ll) ob).
        entailer!. apply fsx_err_ret; [lia|]. unfold exec_split_err. rewrite (proj2 (Z.ltb_lt _ _) Herr).
        rewrite !orb_true_r. reflexivity. }
      { match goal with H: typed_false _ _ |- _ => rename H into Hf end.
        rewrite fs_gt_diff in Hf by (auto; rep_lia). destruct (zlt _ _); [fs_tf | lia]. } }
    match goal with |- semax _ ?P _ _ => apply (fs_loop_seq _ P P) end.
    { forward. forward_if.
      { apply prop_right, cp_sameblock; auto. }
      { match goal with H: typed_true _ _ |- _ => rename H into Ht end.
        rewrite fs_gt_diff in Ht by (auto; rep_lia). destruct (zlt _ _); [lia | fs_tf]. }
      { forward. entailer!. } }
    destruct x as [|e1 elen|shx eb en ec e1 elen]; simpl dict_end in *; simpl ext_len in *.
    { lia. }
    - (* ExtIn *)
      assert (He1: 0 <= e1 - elen /\ e1 <= Zlength c) by (destruct H8 as [_ ?]; auto).
      destruct He1 as [He1 He2].
      unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
      forward. forward.
      { fs_sb. }
      rewrite cp_sub_pp, fs_add_ptr_long by auto.
      set (dl := off - (k + ll - ps)).
      replace (e1 + (k + ll - off - ps)) with (e1 - dl) by (unfold dl; lia).
      forward. forward.
      forward_if.
      { fs_sb. }
      { match goal with Ht: typed_true _ _ |- _ => rename Ht into Hge end.
        rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
        rewrite fs_lt in Hge by rep_lia. apply fs_bt, negb_true_iff, Z.ltb_ge in Hge.
        forward. forward.
        assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) cA))
          by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
        forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) ml).
        { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
        unfold mm_post.
        replace (mm_result cA (Zlength c) (e1 - dl) (k + ll) ml) with (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA))
          by (rewrite <- HcA; symmetry; apply fs_mm_put; lia).
        destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + ml) cA) (k + ll)) as [Hm1 Hm2];
          [lia | rewrite Zlength_sublist; lia | exact HmB |].
        rewrite Zlength_sublist in Hm2 by lia.
        destruct (xd_fin c cA (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA)) k ps (k + ll) (k + (ll + ml)))
          as [XU XF]; try lia; [exact HuA | exact Hm1 | exact HdA | |].
        { replace (k + (ll + ml)) with (k + ll + (e1 - dl + ml - (e1 - dl))) by lia. exact Hm2. }
        specialize (XF ltac:(rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia)).
        forward.
        assert (Hb2: fsb_bc c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA)) (ExtIn e1 elen))
          by (apply (fsb_trans c cA); auto; intros; apply fsb_put; [|apply fsb_sub]; auto).
        assert (Hfx: is_error_code (ll + ml) = false ->
                     put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA) = lexec_split ps (ps - elen) e1 e c k li lim ll ml off)
          by (apply (fsx_ext_full c cA k e li lim ll ml off ps e1 elen dl); [exact HxA | try unfold dl in *; lia ..]).
        Exists (ll + ml) (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) cA)) (offset_val (li + ll) ob).
        entailer!.
        assert (HP := fs_post_full c cA k e li lim ll ml off ps (ExtIn e1 elen) (offset_val (li + ll) ob)).
        refine (proj2 (HP _ _ _ _ _ _ _ _ _ _ _ _ _)); auto; simpl; lia. }
      match goal with Ht: typed_false _ _ |- _ => rename Ht into Hge end.
      rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
      rewrite fs_lt in Hge by rep_lia. apply fs_bf, negb_false_iff, Z.ltb_lt in Hge.
      forward. forward.
      { fs_sb. }
      replace (force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val e1 ob) (offset_val (e1 - dl) ob)))
        with (Vlong (Int64.repr dl))
        by (symmetry; etransitivity; [apply (cp_sub_pp ob e1 (e1 - dl)); auto | do 2 f_equal; lia]).
      forward.
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) cA))
        by (apply (xd_ext_in c cA e1 elen); [auto | exact HuA | exact Xde | lia | lia | lia]).
      forward_call (mm_within sh ob (Zlength c) cA (e1 - dl) (k + ll) dl).
      { simpl. split; [auto|]. repeat split; try rep_lia. apply xd_bv. exact HmB. }
      unfold mm_post.
      replace (mm_result cA (Zlength c) (e1 - dl) (k + ll) dl) with (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA))
        by (rewrite <- HcA; symmetry; apply fs_mm_put; lia).
      destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + dl) cA) (k + ll)) as [Hm1 Hm2];
        [lia | rewrite Zlength_sublist; lia | exact HmB |].
      rewrite Zlength_sublist in Hm2 by lia. replace (k + ll + (e1 - dl + dl - (e1 - dl))) with (k + ll + dl) in Hm2 by lia.
      assert (Hu2: xd_ub c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)))
        by (apply (xd_ub_trans c cA); [lia | exact HuA | exact Hm1]).
      assert (Hd2: xd_rng (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)) ps (k + ll + dl))
        by (apply (xd_rng_app _ _ (k + ll)); [apply (xd_rng_ub cA); try lia; [exact Hm1 | exact HdA] | exact Hm2]).
      forward. rewrite fs_add_ptr_long by auto.
      forward. forward. try rewrite sub64_repr.
      forward.
      destruct (fs_part c cA k e li ll ml off ps (ExtIn e1 elen)) as (P1 & P2 & P3); auto; simpl ext_len; try lia.
      simpl ext_end in P1, P2, P3. simpl ext_src in P1, P2, P3. fold dl in P1, P2, P3.
      assert (Hb2: fsb_bc c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)) (ExtIn e1 elen))
        by (apply (fsb_trans c cA); auto; intros; apply fsb_put; [|apply fsb_sub]; auto).
      assert (HJx: lmatch ps (ps - elen) e1 cA (k + ll) ml off None =
                   lprefix (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)) (k + ll + dl) ps (ml - dl) off None)
        by (apply fsx_span; try unfold dl in *; lia).
      Exists dl (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) cA)).
      replace (k + ll + dl - off) with ps by (unfold dl; lia).
      unfold seqrep. entailer!.
    - (* ExtSep *)
      unfold ext_res.
      assert (Hx: readable_share shx /\ Zlength ec = en /\ en <= 2 ^ 63 - 1 /\ 0 <= e1 - elen /\ e1 <= en)
        by (destruct H8 as [_ ?]; auto).
      destruct Hx as [Hshx [Hen [Hen2 [He1 He2]]]].
      assert_PROP (field_compatible (tarray tuchar en) [] eb) as FCe by entailer!.
      assert (Peb: isptr eb) by (destruct FCe; auto).
      unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
      forward. forward.
      { fs_sb. }
      rewrite cp_sub_pp, fs_add_ptr_long by auto.
      set (dl := off - (k + ll - ps)).
      replace (e1 + (k + ll - off - ps)) with (e1 - dl) by (unfold dl; lia).
      forward. forward.
      forward_if.
      { fs_sb. }
      { match goal with Ht: typed_true _ _ |- _ => rename Ht into Hge end.
        rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
        rewrite fs_lt in Hge by rep_lia. apply fs_bt, negb_true_iff, Z.ltb_ge in Hge.
        forward. forward.
        rewrite (fs_split3 shx en (e1 - dl) ml ec eb) by (auto; lia).
        rewrite (fs_split3 sh (Zlength c) (k + ll) ml cA ob) by (auto; lia).
        assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + ml) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
        forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) ml (sublist (e1 - dl) (e1 - dl + ml) ec)).
        { unfold mm_pre. cancel. }
        { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
        unfold mm_post. Intros.
        sep_apply (fs_join3 shx en (e1 - dl) ml ec eb); auto; try lia.
        sep_apply (fs_join_put sh (Zlength c) (k + ll) ml cA (sublist (e1 - dl) (e1 - dl + ml) ec) ob); auto; try lia.
        { rewrite Zlength_sublist; lia. }
        assert (Hb2: fsb_bc c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)) (ExtSep shx eb en ec e1 elen))
          by (intros Hc Hx; apply fsb_put; [apply HbA; auto | apply fsb_sub; exact Hx]).
        destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + ml) ec) (k + ll)) as [Hm1 Hm2];
          [lia | rewrite Zlength_sublist; lia | exact HmB |].
        rewrite Zlength_sublist in Hm2 by lia.
        destruct (xd_fin c cA (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)) k ps (k + ll) (k + (ll + ml)))
          as [XU XF]; try lia; [exact HuA | exact Hm1 | exact HdA | |].
        { replace (k + (ll + ml)) with (k + ll + (e1 - dl + ml - (e1 - dl))) by lia. exact Hm2. }
        specialize (XF ltac:(rewrite ecl_Zlength_put; rewrite ?Zlength_sublist; lia)).
        forward.
        Exists (ll + ml) (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + ml) ec)) (offset_val (li + ll) ob).
        entailer!.
        assert (HP := fs_post_full c cA k e li lim ll ml off ps (ExtSep shx eb (Zlength ec) ec e1 elen) (offset_val (li + ll) ob)).
        refine (proj2 (HP _ _ _ _ _ _ _ _ _ _ _ _ _)); auto; simpl; lia. }
      match goal with Ht: typed_false _ _ |- _ => rename Ht into Hge end.
      rewrite cp_sub_pp in Hge by auto. replace (e1 - (e1 - dl)) with dl in Hge by lia. simpl in Hge.
      rewrite fs_lt in Hge by rep_lia. apply fs_bf, negb_false_iff, Z.ltb_lt in Hge.
      forward. forward.
      { fs_sb. }
      replace (force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val e1 eb) (offset_val (e1 - dl) eb)))
        with (Vlong (Int64.repr dl))
        by (symmetry; etransitivity; [apply (cp_sub_pp eb e1 (e1 - dl)); auto | do 2 f_equal; lia]).
      forward.
      rewrite (fs_split3 shx en (e1 - dl) dl ec eb) by (auto; lia).
      rewrite (fs_split3 sh (Zlength c) (k + ll) dl cA ob) by (auto; lia).
      assert (HmB: Forall is_byte_val (sublist (e1 - dl) (e1 - dl + dl) ec)) by (apply (xd_sub ec (e1 - elen) e1); auto; lia).
      forward_call (mm_disjoint shx sh (offset_val (e1 - dl) eb) (offset_val (k + ll) ob) dl (sublist (e1 - dl) (e1 - dl + dl) ec)).
      { unfold mm_pre. cancel. }
      { simpl. split; [auto|]. split; [auto|]. split; [rewrite Zlength_sublist; lia | split; [rep_lia | apply xd_bv; exact HmB]]. }
      unfold mm_post. Intros.
      sep_apply (fs_join3 shx en (e1 - dl) dl ec eb); auto; try lia.
      sep_apply (fs_join_put sh (Zlength c) (k + ll) dl cA (sublist (e1 - dl) (e1 - dl + dl) ec) ob); auto; try lia.
      { rewrite Zlength_sublist; lia. }
      forward. rewrite fs_add_ptr_long by auto.
      forward. forward. try rewrite sub64_repr.
      forward.
      destruct (fs_part c cA k e li ll ml off ps (ExtSep shx eb en ec e1 elen)) as (P1 & P2 & P3); auto; simpl ext_len; try lia.
      simpl ext_end in P1, P2, P3. simpl ext_src in P1, P2, P3. fold dl in P1, P2, P3.
      assert (Hb2: fsb_bc c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)) (ExtSep shx eb en ec e1 elen))
        by (intros Hc Hx; apply fsb_put; [apply HbA; auto | apply fsb_sub; exact Hx]).
      destruct (xd_put cA (sublist (e1 - dl) (e1 - dl + dl) ec) (k + ll)) as [Hm1 Hm2];
        [lia | rewrite Zlength_sublist; lia | exact HmB |].
      rewrite Zlength_sublist in Hm2 by lia. replace (k + ll + (e1 - dl + dl - (e1 - dl))) with (k + ll + dl) in Hm2 by lia.
      assert (Hu2: xd_ub c (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)))
        by (apply (xd_ub_trans c cA); [lia | exact HuA | exact Hm1]).
      assert (Hd2: xd_rng (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)) ps (k + ll + dl))
        by (apply (xd_rng_app _ _ (k + ll)); [apply (xd_rng_ub cA); try lia; [exact Hm1 | exact HdA] | exact Hm2]).
      Exists dl (put cA (k + ll) (sublist (e1 - dl) (e1 - dl + dl) ec)).
      replace (k + ll + dl - off) with ps by (unfold dl; lia).
      unfold seqrep. entailer!. }
  { (* inside the prefix *)
    forward.
    match goal with H: typed_false _ _ |- _ => rename H into Hf end.
    rewrite fs_gt_diff in Hf by (auto; rep_lia).
    assert (Hoff2: off <= k + ll - ps) by (destruct (zlt (k + ll - ps) off); [fs_tf | lia]).
    assert (HJx := fsx_prefix x cA k ll ml off ps Hoff2).
    Exists 0 cA. unfold seqrep. rewrite !Z.sub_0_r, !Z.add_0_r. entailer!.
    split; [apply (fs_lit_unch c cA k ll _ Lv); auto; lia|].
    apply (fs_J_prefix c cA k e ll ml off ps x Lv); auto; lia. }
  (* the match from the prefix, at di = k + ll + d, si = di - off *)
  Intros d c2.
  rename H10 into Hd. rename H11 into Hsi. rename H12 into Hoffx. rename H13 into Hc2L.
  rename H14 into Hc2u. rename H15 into HJ. rename H16 into Hb2. rename H17 into Hu2. rename H18 into Hd2.
  rename H19 into HJx.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx ((off < 16) :: P) (LOCALx Q (SEPx R))) end.
  { (* off >= 16: one wild copy *)
    rewrite !Int64.unsigned_repr in H10 by rep_lia.
    forward. forward. forward.
    assert (HC: copy_src_def c2 (k + ll + d - off) (k + ll + d) (ml - d)) by (apply (xd_csd c2 ps); auto; lia).
    forward_call (gv, true, sh, ob, c2, k + ll + d - off, k + ll + d, sh, nullval, @nil val, sh, nullval, @nil val,
                  ml - d, 0).
    { entailer!. simpl. rewrite Hc2L, !(fs_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc2L. cancel. }
    { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN.
      rewrite Hc2L. split; [exact SH|]. repeat split; try rep_lia; intros; try discriminate; first [exact HC | lia]. }
    Intros g. match goal with H: g = _ |- _ => rename H into Hg end.
    match goal with H: context [lwild] |- _ => rename H into Hwx end.
    destruct (xd_wc_within c2 g (k + ll + d - off) (k + ll + d) (ml - d) _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(rewrite Hc2L; unfold WILDCOPY_OVERLENGTH; lia) ltac:(rewrite Hc2L; unfold WILDCOPY_OVERLENGTH; lia) HC Hg)
      as [Hwu Hwr].
    assert (Hb3: fsb_bc c (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g) x).
    { apply (fsb_trans c c2); auto. eapply fsb_wc; [..|exact Hg]; rewrite ?Hc2L; lia. }
    clear Hg.
    destruct (fs_wc_facts c2 g (k + ll + d - off) (k + ll + d) (ml - d)) as (W1 & W2 & W3); try lia.
    destruct (xd_fin c c2 (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g) k ps (k + ll + d) (k + (ll + ml)))
      as [XU XF]; try lia; [exact Hu2 | exact Hwu | exact Hd2 | |].
    { replace (k + (ll + ml)) with (k + ll + d + (ml - d)) by lia. exact Hwr. }
    specialize (XF ltac:(lia)).
    rewrite Hc2L in *.
    forward.
    assert (Hfin: match x with
                  | ExtSep _ _ _ _ _ _ => True
                  | _ => is_error_code (ll + ml) = false ->
                         wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g =
                         lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
                  end).
    { apply (fsx_final x c cA c2 _ k e li lim ll ml off ps d); [lia | lia | exact HxA | exact HJx |].
      apply (fsx_pre16 c2 _ (k + ll + d) off (ml - d)); [lia | exact Hwx]. }
    Exists (ll + ml) (wc_within_post c2 (k + ll + d - off) (k + ll + d) (ml - d) g) (offset_val (li + ll) ob).
    unfold seqrep. entailer!.
    apply (fs_final c c2 _ k e li lim ll ml off ps d x); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia. exact W3. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H10 by rep_lia. lia. }
  Intros. rename H10 into Hoff16.
  forward.
  forward_call (gv, sh, ob, c2, v_op, v_match, k + ll + d, off).
  { rewrite Hc2L, !(fs_fa (Zlength c)) by (auto; lia). replace (k + ll + d - off) with (k + ll + d - off) by lia.
    cancel. }
  { apply xd_rng_Forall; try lia. apply (xd_rng_sub _ ps (k + ll + d)); auto; lia. }
  match goal with H: lov8 _ _ _ _ = _ |- _ => rename H into Hov end.
  destruct (fs_oc8_K off) as (K1 & K2 & K3); [lia|].
  rewrite Hc2L, !arr_field_address0 by (auto; lia). simpl sizeof. rewrite !Z.mul_1_l.
  assert (Hr8: xd_rng c2 (k + ll + d - off) (if k + ll + d - off <? k + ll + d then Z.min (k + ll + d) (k + ll + d - off + 8)
                                             else k + ll + d - off + 8)).
  { rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply (xd_rng_sub _ ps (k + ll + d)); auto; lia. }
  assert (Hu3: xd_ub c2 (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat 8))) by (apply xd_ub_listcopy; auto; lia).
  assert (Hd3: xd_rng (listcopy c2 (k + ll + d - off) (k + ll + d) (Z.to_nat 8)) (k + ll + d) (k + ll + d + 8))
    by (apply xd_listcopy; auto; lia).
  change (Z.to_nat 8) with 8%nat in Hu3, Hd3.
  set (c3 := listcopy c2 (k + ll + d - off) (k + ll + d) 8).
  assert (Hu23: xd_ub c c3) by (apply (xd_ub_trans c c2 c3); auto; lia).
  assert (Hd23: xd_rng c3 ps (k + ll + d + 8))
    by (apply (xd_rng_app _ _ (k + ll + d)); [apply (xd_rng_ub c2); try lia; auto | exact Hd3]).
  forward.
  apply semax_if_seq. forward_if.
  { (* ml - d > 8: the wild copy at distance oc8_off off *)
    rewrite !Int64.unsigned_repr in H10 by rep_lia.
    forward. forward. forward.
    assert (Hc3L: Zlength c3 = Zlength c) by (unfold c3; rewrite listcopy_Zlength; lia).
    assert (HC: copy_src_def c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8))
      by (apply (xd_csd c3 ps); auto; lia).
    forward_call (gv, true, sh, ob, c3, k + ll + d + 8 - oc8_off off, k + ll + d + 8, sh, nullval, @nil val,
                  sh, nullval, @nil val, ml - d - 8, 1).
    { entailer!. simpl. rewrite Hc3L, !(fs_fa (Zlength c)) by (auto; lia). reflexivity. }
    { rewrite Hc3L. cancel. }
    { unfold OV_SRC_BEFORE_DST, OV_NO_OVERLAP, WILDCOPY_OVERLENGTH, WILDCOPY_VECLEN.
      rewrite Hc3L. split; [exact SH|]. repeat split; try rep_lia; intros; try discriminate; first [exact HC | lia]. }
    Intros g. match goal with H: g = _ |- _ => rename H into Hg end.
    match goal with H: context [lwild] |- _ => rename H into Hwx end.
    destruct (xd_wc_within c3 g (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) _ ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(rewrite Hc3L; unfold WILDCOPY_OVERLENGTH; lia)
                ltac:(rewrite Hc3L; unfold WILDCOPY_OVERLENGTH; lia) HC Hg)
      as [Hwu Hwr].
    assert (Hb3: fsb_bc c (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g) x).
    { apply (fsb_trans c c2); auto. intros Hc. eapply fsb_wc; [..|exact Hg|]; rewrite ?Hc3L; try lia.
      unfold c3. apply fsb_listcopy; auto; lia. }
    clear Hg.
    destruct (fs_oc8_facts c2 g off (k + ll + d) (ml - d)) as (W1 & W2 & W3); try lia.
    cbv zeta in W1, W2, W3.
    assert (Eg: (ml - d >? 8) = true) by (apply Z.gtb_lt; lia).
    rewrite Eg in W1, W2, W3. fold c3 in W1, W2, W3.
    destruct (xd_fin c c3 (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g) k ps
                (k + ll + d + 8) (k + (ll + ml))) as [XU XF]; try lia; [exact Hu23 | exact Hwu | exact Hd23 | |].
    { replace (k + (ll + ml)) with (k + ll + d + 8 + (ml - d - 8)) by lia. exact Hwr. }
    specialize (XF ltac:(lia)).
    rewrite Hc3L, Hc2L in *.
    forward.
    assert (Hfin: match x with
                  | ExtSep _ _ _ _ _ _ => True
                  | _ => is_error_code (ll + ml) = false ->
                         wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g =
                         lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
                  end).
    { apply (fsx_final x c cA c2 _ k e li lim ll ml off ps d); [lia | lia | exact HxA | exact HJx |].
      apply (fsx_ov8 c2 c3 _ (k + ll + d) off (ml - d)); [lia | exact Hov |]. rewrite Eg. exact Hwx. }
    Exists (ll + ml) (wc_within_post c3 (k + ll + d + 8 - oc8_off off) (k + ll + d + 8) (ml - d - 8) g)
      (offset_val (li + ll) ob).
    unfold seqrep. entailer!.
    apply (fs_final c c2 _ k e li lim ll ml off ps d x); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia.
      replace (k + ll + d - off) with (k + ll + d - off) by lia. exact W3. }
  { rewrite !Int64.unsigned_repr in H10 by rep_lia.
    destruct (fs_oc8_facts c2 (Zrepeat Vundef 32) off (k + ll + d) (ml - d)) as (W1 & W2 & W3); try lia.
    { rewrite Zlength_Zrepeat; lia. }
    cbv zeta in W1, W2, W3.
    assert (Eg: (ml - d >? 8) = false) by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    rewrite Eg in W1, W2, W3. fold c3 in W1, W2, W3.
    destruct (xd_fin c c2 c3 k ps (k + ll + d) (k + (ll + ml))) as [XU XF]; try lia; [exact Hu2 | exact Hu3 | exact Hd2 | |].
    { apply (xd_rng_sub _ (k + ll + d) (k + ll + d + 8)); auto; lia. }
    specialize (XF ltac:(lia)).
    rewrite Hc2L in *.
    assert (Hb3: fsb_bc c c3 x) by (apply (fsb_trans c c2); auto; intros; unfold c3; apply fsb_listcopy; auto; lia).
    forward.
    assert (Hfin: match x with
                  | ExtSep _ _ _ _ _ _ => True
                  | _ => is_error_code (ll + ml) = false ->
                         c3 = lexec_split ps (ps - ext_len x) (ext_end x) e c k li lim ll ml off
                  end).
    { apply (fsx_final x c cA c2 _ k e li lim ll ml off ps d); [lia | lia | exact HxA | exact HJx |].
      apply (fsx_ov8 c2 c3 _ (k + ll + d) off (ml - d)); [lia | exact Hov |]. rewrite Eg. reflexivity. }
    Exists (ll + ml) c3 (offset_val (li + ll) ob).
    unfold seqrep. entailer!.
    apply (fs_final c c2 _ k e li lim ll ml off ps d x); auto; try lia.
    - intros p Hp Hq. apply W2; lia.
    - replace (k + ll + ml) with (k + ll + d + (ml - d)) by lia. exact W3. }
Qed.

(* ---------- assembly ---------- *)
Lemma EXEC_ok : EXEC_obligation.
Proof.
  unfold EXEC_obligation, subtree_ok.
  exists EXEC_exports. split; [reflexivity | split; [apply incl_refl | ]].
  rewrite <- app_assoc. fold EXEC_G.
  repeat constructor.
  - exists f_ZSTD_execSequenceEnd.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_execSequenceEnd]].
  - exists f_ZSTD_execSequenceEndSplitLitBuffer.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_execSequenceEndSplitLitBuffer]].
  - exists f_ZSTD_execSequence.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_execSequence]].
  - exists f_ZSTD_execSequenceSplitLitBuffer.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_execSequenceSplitLitBuffer]].
Qed.
