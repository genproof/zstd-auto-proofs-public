(* LOOP: the split-literal loop (LSplit: the head in the output array, then litExtraBuffer).
   ZSTD_decompressSequences_bodySplitLitBuffer gets the dispatchers' seqs_spec (BlkIface) itself, in the loop bodies' context LOOP_GB
   (BlkSeqLoopCommon); BlkSeqLOOP.LOOP_ok lifts it.  Shared steps: BlkSeqLoopModel (the model invariant),
   BlkSeqLoopCommon (tables, bitstream, litExtraBuffer).

   Proof structure: the arguments (sa), the ghosts fixed by the
   prologue (sg: tables, borrowed resources), the loop state (sw), one invariant for both phases (ph = true:
   literals still split, from the output array at lb; ph = false: from litExtraBuffer), the state after a decode
   (PEND), the state before the last literals (LASTPRE); one segment lemma per piece of the body:
     seg_init (prologue after the loads), seg_dec (decodeSequence, both phases), seg_x1 (phase-1 check and
     execSequenceSplitLitBuffer), seg_left (the leftover copy and the switch to litExtraBuffer), seg_x2 (phase-2
     execSequence), seg_end (endOfDStream, the repeat offsets, the tables back), seg_last (the last literals). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Coq.micromega.Lia.
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopSplitX.
Require Import Zstd.proof.model.ExBlock Zstd.proof.model.ExCSeq.
Local Open Scope logic.

(* ===================================================================== *)
(* the pieces of the body *)

Fixpoint stm_at (s: statement) (path: list nat) : statement :=
  match path with
  | nil => s
  | k :: rest =>
      match s, k with
      | Ssequence a _, O => stm_at a rest | Ssequence _ b, S O => stm_at b rest
      | Sifthenelse _ a _, O => stm_at a rest | Sifthenelse _ _ b, S O => stm_at b rest
      | Sloop a _, O => stm_at a rest | Sloop _ b, S O => stm_at b rest
      | _, _ => Sskip
      end
  end.

Ltac sp_stm path :=
  let x := eval cbv beta iota zeta delta [stm_at fn_body f_ZSTD_decompressSequences_bodySplitLitBuffer] in
    (stm_at (fn_body f_ZSTD_decompressSequences_bodySplitLitBuffer) path) in exact x.

(* after the loads: `if (nbSeq) BIG; LAST` *)
Definition sp_big : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0]%nat).
Definition sp_last : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;1]%nat).
(* BIG = s1; (s2; (s3; (s4; (s5; (s6; (BLOCK; REST)))))): fseEntropy, prevOffset, initDStream, 3 initFseState *)
Definition sp_s1 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;0]%nat).
Definition sp_s2 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;0]%nat).
Definition sp_s3 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;0]%nat).
Definition sp_s4 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;0]%nat).
Definition sp_s5 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0]%nat).
Definition sp_s6 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;0]%nat).
Definition sp_init (REST: statement) : statement :=
  Ssequence sp_s1 (Ssequence sp_s2 (Ssequence sp_s3 (Ssequence sp_s4 (Ssequence sp_s5 (Ssequence sp_s6 REST))))).
(* BLOCK = z1; (z2; (z3; (LOOP1; (skip; if (nbSeq > 0) LEFTOVER)))) *)
Definition sp_block : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;0]%nat).
Definition sp_loop1 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;0;1;1;1;0]%nat).
(* LOOP1 = Sloop (if (nbSeq) skip else break; (DEC1; (CHK1; EX1))) (nbSeq--) *)
Definition sp_dec1 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;0;1;1;1;0;0;1;0]%nat).
Definition sp_x1 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;0;1;1;1;0;0;1;1]%nat).
Definition sp_left : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;0;1;1;1;1;1;0]%nat).
(* REST = (if (nbSeq > 0) LOOP2); END *)
Definition sp_loop2 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;1;0;0]%nat).
Definition sp_dec2 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;1;0;0;0;1;0]%nat).
Definition sp_x2 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;1;0;0;0;1;1]%nat).
Definition sp_end : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;1;1]%nat).

(* the arguments (sa), ghosts (sg), loop state (sw), invariants and exact steps: BlkSeqLoopSplitX *)

(* the frame the loops do not touch *)
Definition sp_FR0 (a: sa) : mpred :=
  pws_pred (a_W a) * frame_fields (a_p a) (a_fs a) *
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (sp_n a))) (a_p a) *
  field_at Ews t_dctx (DOT _litPtr) (offset_val (a_lb a) (sp_ob a)) (a_p a) *
  field_at Ews t_dctx (DOT _litBuffer) (offset_val (a_lb a) (sp_ob a)) (a_p a).
Definition sp_FRL (a: sa) (g: sg) (Rin: mpred) : mpred :=
  sp_FR0 a * field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) (a_p a) * seq_ptrs (a_p a) (g_tp g) *
  data_at (g_sh1 g) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) * Rin.

(* the temps and local variables *)
Definition sp_lvars (a: sa) : list localdef :=
  [lvar _sequence__1 t_seq (a_vsq1 a); lvar _sequence t_seq (a_vsq a);
   lvar _seqState t_seqstate (a_vss a); lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a);
   temp _dctx (a_p a)].
Definition sp_ptrs (a: sa) : list localdef :=
  [temp _ostart (offset_val (sp_d a) (sp_ob a)); temp _oend (offset_val (sp_d a + sp_cap a) (sp_ob a));
   temp _prefixStart (offset_val (sp_ps a) (sp_ob a));
   temp _vBase (offset_val (sp_ps a - ext_len (sp_x a)) (sp_ob a));
   temp _dictEnd (dict_end (sp_x a) (sp_ob a) (fs_dictEnd (a_fs a)))].
Definition sp_L (a: sa) (ph: bool) (w: sw) (nbt: Z) : list localdef :=
  sp_lvars a ++
  [temp _nbSeq (Vint (Int.repr nbt)); temp _isLongOffset (Vint (Int.repr 0));
   temp _op (offset_val (sp_d a + w_K w) (sp_ob a)); temp _litBufferEnd (sp_lbe a ph)] ++ sp_ptrs a.

(* the resources of the loops; SQ, SQ1: the two seq_t variables, SS: the seqState variable *)
Definition sp_S (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) (SQ SQ1 SS: mpred) : list mpred :=
  [data_at Tsh (tptr tuchar) (sp_lp a ph (w_j w)) (a_vlp a); SS; SQ; SQ1; zstd_globals (a_gv a); Q;
   bit_src (g_sh2 g) (sp_sst a) (sp_s a);
   data_at (oa_sh (a_o a)) (tarray tuchar (sp_N a)) (w_c w) (sp_ob a);
   data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ g_xr g) (lit_extra (a_p a));
   field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (sp_loc ph))) (a_p a);
   field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (sp_lim a) (sp_ob a)) (a_p a);
   field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (a_rep a)) (a_p a);
   ext_res (sp_x a); sp_FRL a g Rin].

(* a loop head (nbt: the value of the temp nbSeq: nb - id at the head, nb - id + 1 at the end of a body) *)
Definition sp_INV (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) (nbt: Z) : environ -> mpred :=
  PROPx [sinv a (g_t g) ph w; xinv a (g_t g) (zbytes (sp_tail a) ++ g_xr g) ph w]
  (LOCALx (sp_L a ph w nbt)
  (SEPx (sp_S a g Q Rin ph w (data_at_ Tsh t_seq (a_vsq a)) (data_at_ Tsh t_seq (a_vsq1 a))
           (seqstate_at Tsh (a_gv a) (sp_s a) (sp_sst a) (w_pos w) (w_lo w) (w_st w) (g_tp g) (w_crep w) (a_vss a))))).

(* after a decode: the sequence (ll, ml, the C offset) in `sequence` (ph) / `sequence__1`, the new repeat
   offsets in seqState *)
Definition sp_PEND (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) (ll ml ov: Z) : environ -> mpred :=
  let sq := data_at Tsh t_seq (seqrep ll ml (fst (c_offset (w_crep w) ll ov))) in
  PROPx [spend a (g_t g) ph w ll ml ov; xpend a (g_t g) (zbytes (sp_tail a) ++ g_xr g) ph w ll ml ov]
  (LOCALx (sp_L a ph w (a_nb a - w_id w))
  (SEPx (sp_S a g Q Rin ph w (if ph then sq (a_vsq a) else data_at_ Tsh t_seq (a_vsq a))
           (if ph then data_at_ Tsh t_seq (a_vsq1 a) else sq (a_vsq1 a))
           (seqstate_at Tsh (a_gv a) (sp_s a) (sp_sst a) (w_pos w) (w_lo w) (w_st w) (g_tp g)
              (snd (c_offset (w_crep w) ll ov)) (a_vss a))))).

(* before the last literals (also nbSeq = 0: nothing borrowed) *)
Definition sp_LAST (a: sa) (ph: bool) (w: sw) (rep': Z * Z * Z) (xr: list val) : environ -> mpred :=
  let gv := a_gv a in let p := a_p a in
  PROPx [slast a ph w rep'; Zlength xr = WILDCOPY_OVERLENGTH /\ byte_cells xr; xlast a (zbytes (sp_tail a) ++ xr) ph w rep']
  (LOCALx (sp_lvars a ++
           [temp _op (offset_val (sp_d a + w_K w) (sp_ob a)); temp _litBufferEnd (sp_lbe a ph)] ++ sp_ptrs a)
  (SEPx [data_at Tsh (tptr tuchar) (sp_lp a ph (w_j w)) (a_vlp a); data_at_ Tsh t_seqstate (a_vss a);
         data_at_ Tsh t_seq (a_vsq a); data_at_ Tsh t_seq (a_vsq1 a); zstd_globals gv;
         tabs_seq gv p (a_ox a) (a_os a) (if a_nb a =? 0 then a_fe a else 1); dent_of dent_def gv (a_ox a);
         field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p;
         data_at (oa_sh (a_o a)) (tarray tuchar (sp_N a)) (w_c w) (sp_ob a);
         data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a));
         data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ xr) (lit_extra p);
         field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (sp_loc ph))) p;
         field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (sp_lim a) (sp_ob a)) p;
         ext_res (sp_x a); sp_FR0 a])).

(* after the loads, nbSeq > 0 *)
Definition sp_P0 (a: sa) (xr: list val) : environ -> mpred :=
  let gv := a_gv a in let p := a_p a in
  PROPx []
  (LOCALx (sp_lvars a ++
           [temp _nbSeq (Vint (Int.repr (a_nb a))); temp _isLongOffset (Vint (Int.repr 0));
            temp _seqStart (sp_sst a); temp _seqSize (Vlong (Int64.repr (Zlength (sp_s a))));
            temp _op (offset_val (sp_d a) (sp_ob a)); temp _litBufferEnd (offset_val (sp_lim a) (sp_ob a))] ++
           sp_ptrs a)
  (SEPx [data_at Tsh (tptr tuchar) (offset_val (a_lb a) (sp_ob a)) (a_vlp a); data_at_ Tsh t_seqstate (a_vss a);
         data_at_ Tsh t_seq (a_vsq a); data_at_ Tsh t_seq (a_vsq1 a); zstd_globals gv;
         tabs_seq gv p (a_ox a) (a_os a) (a_fe a); dent_of dent_def gv (a_ox a);
         field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (a_rep a)) p;
         data_at (oa_sh (a_o a)) (tarray tuchar (sp_N a)) (sp_c0 a) (sp_ob a);
         data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a));
         data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ xr) (lit_extra p);
         field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr LOC_SPLIT)) p;
         field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (sp_lim a) (sp_ob a)) p;
         ext_res (sp_x a); sp_FR0 a])).

(* the function's postcondition (seqs_spec's POST for the arguments a) and its ret_assert *)
Definition sp_post (a: sa) : environ -> mpred :=
  let gv := a_gv a in let p := a_p a in let o := a_o a in let h := a_h a in
  (EX r: Z, EX oc': list val, EX rep': Z * Z * Z,
   PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o; rep_ok rep';
         unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
         is_error_code r = false ->
           r <= oa_cap o /\
           unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
           (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
            (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= a_bsm a /\ ext_far (oa_d o) (oa_cap o) (a_bsm a) (hc_ext h))) ->
              exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
         oa_cap o = 0 \/
         (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
          ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
         match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
         | Some (cnt, rep2) =>
             Zlength cnt <= a_bsm a ->
             (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
              rep' = rep2) \/
             (is_error_code r = true /\ oa_cap o < Zlength cnt)
         | None => True
         end;
         is_error_code r = true -> dec_err r;
         byte_cells (oa_c o) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext h) -> byte_cells oc';
         xpost a r oc' rep')
   RETURN (Vlong (Int64.repr r))
   SEP (zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a);
        tabs_seq gv p (a_ox a) (a_os a) (if a_nb a =? 0 then a_fe a else 1); dent_of dent_def gv (a_ox a);
        field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p; lit_scratch_x p (a_lxb a);
        data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
        data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a));
        ext_res (hc_ext h)))%assert.

Definition sp_Delta : tycontext := func_tycontext f_ZSTD_decompressSequences_bodySplitLitBuffer Vprog LOOP_GB nil.
Definition sp_R (a: sa) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong (sp_post a))
    (stackframe_of f_ZSTD_decompressSequences_bodySplitLitBuffer).
Definition sp_rest2 : statement := ltac:(sp_stm [1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;1;1;1]%nat).

(* ===================================================================== *)
(* shared lemmas *)

(* the pool of sp_tabs_borrow (as in seqtabs_borrow): a DDict's sequence table of kind k, a predefined
   table of kind k *)
Definition tabs_ddslot (ox: option ddx) (k: seqkind) : mpred :=
  match ox_seq k ox with
  | Some t => seqspace_at Ews k (Some t) (dd_seq k (ox_q ox))
  | None => emp
  end.
Definition tabs_gslot (gv: globals) (k: seqkind) : mpred :=
  seqtab_at_fm Ers k (sk_predef k) predef_fm (gv (sk_gdefault k)).

Lemma tabs_dent_split (gv: globals) (ox: option ddx) :
  exists Rd: mpred, dent_of dent_def gv ox = tabs_ddslot ox KLL * tabs_ddslot ox KOF * tabs_ddslot ox KML * Rd.
Proof.
  unfold tabs_ddslot, ox_seq.
  destruct ox as [x|].
  2: { exists emp. simpl. rewrite !emp_sepcon. reflexivity. }
  simpl dent_of. simpl ox_ent. simpl ox_q.
  destruct (ddx_ent x) as [st|].
  2: { exists (dent_def gv (dx_q x) None). rewrite !emp_sepcon. reflexivity. }
  unfold dent_def.
  destruct (st_seq st) as [[[a b] c]|] eqn:Hs.
  2: { simpl seq_of. exists (match st_huf st with Some _ => FF | None => FF end).
       rewrite !emp_sepcon. destruct (st_huf st); reflexivity. }
  simpl seq_of.
  destruct (st_huf st) as [ht|].
  - match goal with |- exists Rd, (andp ?P (?H * _ * _ * _ * ?Rp * ?W)) = _ =>
      exists (andp P (H * Rp * W)) end.
    apply pred_ext; entailer!.
  - exists FF. rewrite sepcon_FF. reflexivity.
Qed.

(* one table, lent: Qk keeps everything but the pointer field; the table is in Qk or in the global slot *)
Lemma tabs_one (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) :
  seq_where gv p ox k t * tabs_ddslot ox k |--
  EX tp: val, EX sh: share, EX fm: Z, EX Qk: mpred,
    !! (readable_share sh /\
        (seq_ptr_at p k tp * Qk * tabs_gslot gv k
         |-- seq_where gv p ox k t * tabs_ddslot ox k * tabs_gslot gv k) /\
        (exists Rk: mpred,
           (Qk * tabs_gslot gv k |-- seqtab_at_fm sh k t fm tp * Rk) /\
           (seqtab_at_fm sh k t fm tp * Rk |-- Qk * tabs_gslot gv k))) &&
    (seq_ptr_at p k tp * Qk).
Proof.
  unfold seq_where. Intros tp w. destruct w.
  - Intros. subst tp. unfold seqspace_at at 1, seqtab_at. Intros fm.
    set (D := data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (ctx_seq k p))).
    Exists (ctx_seq k p) Ews fm (seqtab_at_fm Ews k t fm (ctx_seq k p) * D * tabs_ddslot ox k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + subst D. Exists (ctx_seq k p) TCtx. unfold seqspace_at, seqtab_at. Exists fm. entailer!.
    + exists (D * tabs_ddslot ox k * tabs_gslot gv k). split; cancel.
  - Intros. rename H into Ho. subst tp. unfold tabs_ddslot at 1. rewrite Ho.
    unfold seqspace_at at 2, seqtab_at. Intros fm.
    set (D := data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (dd_seq k (ox_q ox)))).
    Exists (dd_seq k (ox_q ox)) Ews fm
      (seqtab_at_fm Ews k t fm (dd_seq k (ox_q ox)) * seqspace_at Ews k None (ctx_seq k p) * D).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + subst D. Exists (dd_seq k (ox_q ox)) TDict. try (unfold tabs_ddslot; rewrite Ho).
      unfold seqspace_at, seqtab_at. Exists fm. entailer!.
    + exists (seqspace_at Ews k None (ctx_seq k p) * D * tabs_gslot gv k). split; cancel.
  - Intros. subst t tp.
    Exists (gv (sk_gdefault k)) Ers predef_fm (seqspace_at Ews k None (ctx_seq k p) * tabs_ddslot ox k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + Exists (gv (sk_gdefault k)) TGlob. entailer!.
    + exists (seqspace_at Ews k None (ctx_seq k p) * tabs_ddslot ox k). unfold tabs_gslot. split; cancel.
Qed.

(* the sequence tables out of tabs_seq for the whole loop: the context's pointers (seq_ptrs, fixed tp) and Q;
   Q with zstd_globals lends the tables (decodeSequence) and gives them back; tabs_seq comes back with any
   fseEntropy.  (= BlkSeqLoopCommon.seqtabs_borrow, with zstd_globals kept out: the executors and BIT_* need it
   while the states point into the tables.) *)
Lemma sp_tabs_borrow (HG: GLOBALS_obligation) (gv: globals) (p: val) (ox: option ddx)
    (t: fse_table * fse_table * fse_table) (fe: Z) :
  tabs_seq gv p ox (Some t) fe * dent_of dent_def gv ox * zstd_globals gv |--
  EX tp: val * val * val, EX sht: share * share * share, EX fm: Z * Z * Z, EX Q: mpred,
    !! (seqtabs_sh_ok sht /\
        (forall fe': Z,
           field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p tp * Q * zstd_globals gv
           |-- tabs_seq gv p ox (Some t) fe' * dent_of dent_def gv ox * zstd_globals gv) /\
        (exists R': mpred,
           (Q * zstd_globals gv |-- seqtabs_at sht t fm tp * R') /\
           (seqtabs_at sht t fm tp * R' |-- Q * zstd_globals gv))) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p * seq_ptrs p tp * Q * zstd_globals gv).
Proof.
  destruct t as [[a b] c].
  destruct (tabs_dent_split gv ox) as [Rd Hd]. destruct (HG gv) as [Rg Hg].
  rewrite Hd, Hg. unfold predef_tabs.
  change (seqtab_at_fm Ers KLL LL_predef predef_fm (gv _LL_defaultDTable)) with (tabs_gslot gv KLL).
  change (seqtab_at_fm Ers KOF OF_predef predef_fm (gv _OF_defaultDTable)) with (tabs_gslot gv KOF).
  change (seqtab_at_fm Ers KML ML_predef predef_fm (gv _ML_defaultDTable)) with (tabs_gslot gv KML).
  unfold tabs_seq.
  sep_apply (tabs_one gv p ox KLL a). Intros tpa sha fma Qa.
  sep_apply (tabs_one gv p ox KOF b). Intros tpb shb fmb Qb.
  sep_apply (tabs_one gv p ox KML c). Intros tpc shc fmc Qc.
  destruct H1 as [Ra [Ha1 Ha2]]. destruct H4 as [Rb [Hb1 Hb2]]. destruct H7 as [Rc [Hc1 Hc2]].
  Exists (tpa, tpb, tpc) (sha, shb, shc) (fma, fmb, fmc) (Qa * Qb * Qc * Rd).
  unfold seq_ptrs, seqtabs_at.
  unfold seq_ptr_at in *.
  apply andp_right; [apply prop_right | cancel].
  split; [simpl; auto |]. split.
  - intros fe'.
    sep_apply H0. sep_apply H3. sep_apply H6. cancel.
  - exists (Ra * Rb * Rc * Rd * Rg).
    split.
    + sep_apply Ha1. sep_apply Hb1. sep_apply Hc1. cancel.
    + sep_apply Ha2. sep_apply Hb2. sep_apply Hc2. cancel.
Qed.

Lemma spm_lz_copy (hist out: list Z) (off: Z) (n: nat) :
  exists mb, lz_copy hist out off n = out ++ mb /\ length mb = n.
Proof.
  revert out. induction n as [|n IH]; intros out; simpl.
  - exists nil. rewrite app_nil_r. auto.
  - destruct (IH (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - off)])) as (mb & E & L).
    rewrite E, <- app_assoc. eexists; split; [reflexivity|]. simpl. lia.
Qed.

(* the model's output only grows; content length *)
Lemma sp_exec_len (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep2) ->
  exists ext, out' = out ++ ext /\ Zlength lits' <= Zlength lits /\ Zlength lits <= Zlength ext + Zlength lits'.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H; simpl in H.
  - injection H as <- <- <-. exists nil. rewrite app_nil_r. split; [auto|]. rewrite Zlength_nil. lia.
  - destruct (sq_ll sq >? Zlength lits) eqn:E1; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[off rep']|]; [|discriminate].
    destruct (off >? _); [discriminate|]. destruct (off >? _); [discriminate|].
    destruct (spm_lz_copy hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) off (Z.to_nat (sq_ml sq))) as (mb & Em & _).
    rewrite Em in H. apply IH in H as (ext & -> & H1 & H2).
    exists (firstn (Z.to_nat (sq_ll sq)) lits ++ mb ++ ext). split; [rewrite !app_assoc; reflexivity|].
    assert (Hs: Zlength lits = Zlength (firstn (Z.to_nat (sq_ll sq)) lits) + Zlength (skipn (Z.to_nat (sq_ll sq)) lits)).
    { rewrite <- Zlength_app, firstn_skipn. reflexivity. }
    rewrite !Zlength_app. pose proof (Zlength_nonneg mb). pose proof (Zlength_nonneg (firstn (Z.to_nat (sq_ll sq)) lits)). lia.
Qed.

Lemma spm_resolve (rep: Z * Z * Z) (ll ov off: Z) (rep': Z * Z * Z) :
  rep_ok rep -> 1 <= ov < 2 ^ 32 -> resolve_offset rep ll ov = Some (off, rep') ->
  c_offset rep ll ov = (off, rep') /\ rep_ok rep' /\ 1 <= off < 2 ^ 32.
Proof.
  destruct rep as [[r1 r2] r3]. unfold rep_ok, resolve_offset, c_offset, SIZE_MAX. intros (H1 & H2 & H3) Hov H.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; inversion H; subst; split; [reflexivity|]; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [inversion H; subst; split; [reflexivity|]; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [inversion H; subst; split; [reflexivity|]; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [inversion H; subst; split; [reflexivity|]; lia|].
  destruct (r1 - 1 <=? 0) eqn:E2; [discriminate|]. apply Z.leb_gt in E2. inversion H; subst.
  rewrite Z.mod_small by lia. destruct (r1 - 1 =? 0) eqn:E3; [apply Z.eqb_eq in E3; lia|].
  split; [reflexivity|]. lia.
Qed.

(* one model sequence, without the bytes (when the content does not fit the capacity the C bytes may differ) *)
Lemma sp_exec_free (wsize: Z) (crep: Z * Z * Z) (hist lr ob: list Z) (sq: sequence) (rest: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  rep_ok crep -> 0 <= sq_ll sq -> 0 <= sq_ml sq -> 1 <= sq_ov sq < 2 ^ 32 ->
  exec_seqs wsize crep hist lr ob (sq :: rest) = Some (out', lits', rep2) ->
  exists off crep' mb,
    c_offset crep (sq_ll sq) (sq_ov sq) = (off, crep') /\ rep_ok crep' /\ 1 <= off < 2 ^ 32 /\
    0 <= sq_ll sq <= Zlength lr /\ Zlength mb = sq_ml sq /\
    exec_seqs wsize crep' hist (skipn (Z.to_nat (sq_ll sq)) lr) (ob ++ firstn (Z.to_nat (sq_ll sq)) lr ++ mb) rest =
      Some (out', lits', rep2).
Proof.
  intros Hr Hll Hml Hov H. simpl in H.
  destruct (sq_ll sq >? Zlength lr) eqn:E1; [discriminate|]. rewrite Z.gtb_ltb, Z.ltb_ge in E1.
  destruct (resolve_offset crep (sq_ll sq) (sq_ov sq)) as [[off rep']|] eqn:Er; [|discriminate].
  destruct (spm_resolve _ _ _ _ _ Hr Hov Er) as (Hc & Hr' & Ho).
  destruct (off >? _); [discriminate|]. destruct (off >? _); [discriminate|].
  destruct (spm_lz_copy hist (ob ++ firstn (Z.to_nat (sq_ll sq)) lr) off (Z.to_nat (sq_ml sq))) as (mb & Em & Lm).
  rewrite Em, <- app_assoc in H.
  exists off, rep', mb. split; [exact Hc|]. split; [exact Hr'|]. split; [exact Ho|]. split; [lia|].
  split; [rewrite Zlength_correct, Lm; lia | exact H].
Qed.

(* the C repeat offsets after a sequence the executor accepted (offset < SIZE_MAX) *)
Lemma sp_rep_step (crep: Z * Z * Z) (ll ov: Z) :
  rep_ok crep -> 1 <= ov < 2 ^ 32 -> fst (c_offset crep ll ov) < SIZE_MAX -> rep_ok (snd (c_offset crep ll ov)).
Proof.
  destruct crep as [[r1 r2] r3]. unfold rep_ok, c_offset, SIZE_MAX. intros (H1 & H2 & H3) Hov Hf.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [simpl; lia|].
  cbn [fst snd] in *. destruct ((r1 - 1) mod 2 ^ 64 =? 0) eqn:E0; [cbn [fst] in Hf; lia|].
  rewrite Z.mod_small in * by lia. lia.
Qed.

(* giving back what the prologue borrowed *)
Lemma sp_release (a: sa) (g: sg) (Q Rin: mpred) :
  bfacts a g Q Rin ->
  sp_FRL a g Rin * Q * zstd_globals (a_gv a) * bit_src (g_sh2 g) (sp_sst a) (sp_s a) |--
  tabs_seq (a_gv a) (a_p a) (a_ox a) (a_os a) 1 * dent_of dent_def (a_gv a) (a_ox a) * zstd_globals (a_gv a) *
  data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) * sp_FR0 a.
Proof.
  intros (Hos & Hsh & Hgb & Hlend & Hr1 & Hr2 & Hin & Hxr). unfold sp_FRL. rewrite Hin.
  eapply derives_trans; [| apply sepcon_derives; [apply sepcon_derives; [apply (Hgb 1) | apply derives_refl] | apply derives_refl]].
  cancel.
Qed.

(* litExtraBuffer (litfields, LSplit): its bytes lxb are the literals' last 65536, then the 32 cells xr *)
Definition sa_x (a: sa) (xr: list val) : Prop :=
  Zlength (a_lxb a) = LITEXTRA_N /\ bytes_ok (a_lxb a) /\ sublist 0 LITBUFFEREXTRASIZE (a_lxb a) = sp_tail a /\
  xr = zbytes (sublist LITBUFFEREXTRASIZE LITEXTRA_N (a_lxb a)).

Lemma sa_x_cl (a: sa) (xr: list val) : sa_x a xr -> zbytes (sp_tail a) ++ xr = zbytes (a_lxb a).
Proof.
  intros (Hl & _ & Ht & ->). rewrite <- Ht, <- map_app.
  rewrite <- sublist_split by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  rewrite sublist_same by lia. reflexivity.
Qed.

Lemma sa_x_bytes (a: sa) (xr: list val) : sa_x a xr -> byte_cells (zbytes (sp_tail a) ++ xr).
Proof.
  intros Hx. rewrite (sa_x_cl a xr Hx). destruct Hx as (_ & Hb & _).
  clear - Hb. induction Hb as [|b l Hb' Hl IH]; constructor; auto. exists b. split; [exact Hb' | reflexivity].
Qed.

(* the literal fields as scratch, litExtraBuffer still holding lxb (seqs_spec's lit_scratch_x) *)
Lemma lsx (a: sa) (xr: list val) (lp ls lb lbe loc: val) :
  sa_x a xr ->
  field_at Ews t_dctx (DOT _litPtr) lp (a_p a) * field_at Ews t_dctx (DOT _litSize) ls (a_p a) *
  field_at Ews t_dctx (DOT _litBuffer) lb (a_p a) * field_at Ews t_dctx (DOT _litBufferEnd) lbe (a_p a) *
  field_at Ews t_dctx (DOT _litBufferLocation) loc (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ xr) (lit_extra (a_p a)) |--
  lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros Hx. pose proof (sa_x_cl a xr Hx) as E. destruct Hx as (Hl & Hb & _).
  unfold lit_scratch_x, lit_extra_at. rewrite E, <- litextra_data_at.
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation)).
  entailer!.
Qed.

(* the executors' exact clause after the case split on the error flag *)
Lemma sx_exact (x: ext_seg) (b b': bool) (P: Prop) :
  b = false -> (match x with ExtSep _ _ _ _ _ _ => True | _ => b = false -> P end) ->
  match x with ExtSep _ _ _ _ _ _ => True | _ => b' = false -> P end.
Proof. intros Hb H. destruct x; auto. Qed.

(* ===================================================================== *)
(* the segments *)

(* helpers of seg_init *)
Lemma seg_init_repr_eqm: forall x y, x mod 2^64 = y mod 2^64 -> Int64.repr x = Int64.repr y.
Proof.
  intros x y H. apply Int64.eqm_samerepr. unfold Int64.eqm. change Int64.modulus with (2^64).
  apply Zbits.eqmod_trans with (x mod 2^64); [apply Zbits.eqmod_mod; lia|].
  rewrite H. apply Zbits.eqmod_sym, Zbits.eqmod_mod; lia.
Qed.

(* the seqState_t local, split into its fields *)
Lemma seg_init_ss_split (v: val) :
  data_at_ Tsh t_seqstate v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold t_seqstate. unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma seg_init_tab_isptr (sh: share) (k: seqkind) (t: fse_table) (fm: Z) (p: val) :
  seqtab_at_fm sh k t fm p |-- !! isptr p.
Proof.
  unfold seqtab_at_fm. Intros. rewrite (data_at_isptr sh t_seqhdr). Intros. apply prop_right. auto.
Qed.

(* the stream as its own bit source (offset 0) *)
Lemma seg_init_bsrc (s: list Z) (st: val) : isptr st -> bit_src_ok s st st s 0.
Proof.
  intros Hp. unfold bit_src_ok. rewrite isptr_offset_val_zero by exact Hp.
  pose proof (Zlength_nonneg s). split; [reflexivity|]. split; [lia|]. split; [lia|].
  rewrite Z.add_0_l. apply sublist_same; lia.
Qed.

(* bits consumed after BIT_initDStream: at most 64 *)
Lemma seg_init_bcons0 (s: list Z) :
  bytes_ok s -> bs_wf s = true -> 0 <= bcons (bs_total s) (8 * Z.max 0 (Zlength s - 8)) <= 64.
Proof.
  intros Hb Hwf. destruct (lim_init s Hb Hwf) as (H0 & H8 & H64 & Hr).
  assert (Ht: 0 <= bs_total s).
  { unfold bs_wf in Hwf. apply andb_prop in Hwf as [Hz _]. apply negb_true_iff, Z.eqb_neq in Hz.
    unfold bs_total. rewrite <- Zlength_correct. pose proof (Zlength_nonneg s).
    pose proof (Z.log2_nonneg (last s 0)). unfold highbit. lia. }
  unfold bcons. destruct Hr as [Hr | Hr]; lia.
Qed.

(* one read of nb bits and a reload consume at most nb more bits *)
Lemma seg_init_bcons_step (pos lo nb: Z) :
  0 <= lo -> pos - nb <= lo + 64 ->
  bcons (pos - nb) (snd (bs_reload (pos - nb) lo)) <= bcons pos lo + nb.
Proof.
  intros H0 H1. pose proof (bs_reload_lo (pos - nb) lo H0 H1). unfold bcons. lia.
Qed.

Lemma seg_init_rep_inv (sh: share) (gv: globals) (s: list Z) (st: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep sh gv s st pos lo p |-- !! (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64).
Proof.
  unfold BIT_DStream_rep, bit_inv. Intros ptr lim. apply prop_right. tauto.
Qed.

(* no well-formed stream: the model fails *)
Lemma seg_init_model_none (t: fse_table * fse_table * fse_table) (s: list Z) (nb: Z) (rep: Z * Z * Z)
    (hist out lits: list Z) (w: Z) :
  bs_wf s = false -> nb <> 0 -> seqs_model (Some t) s nb rep hist out lits w = None.
Proof.
  intros Hwf Hnb. destruct t as [[tLL tOF] tML]. unfold seqs_model.
  rewrite (proj2 (Z.eqb_neq nb 0) Hnb). unfold decode_seq_stream.
  assert (Hok: bs_okb s = false).
  { unfold bs_wf in Hwf. unfold bs_okb.
    apply andb_false_iff in Hwf as [Hz | Hl].
    - apply negb_false_iff, Z.eqb_eq in Hz. rewrite Zlength_correct in Hz.
      assert (length s = 0%nat) as -> by lia. rewrite andb_false_r. reflexivity.
    - rewrite Hl, andb_false_r. reflexivity. }
  rewrite Hok. reflexivity.
Qed.

Lemma seg_init_zbytes_cells (l: list Z) : bytes_ok l -> byte_cells (zbytes l).
Proof.
  intros H. induction H as [|b l Hb Hl IH]; constructor; auto. exists b. split; [exact Hb | reflexivity].
Qed.

(* do { } while (0) with an empty body *)
Ltac seg_init_dw0 :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

(* do { if (0) ...; } while (0) *)
Ltac seg_init_dw0if :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [ apply ENTAIL_refl
    | forward_if P;
      [ exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end
      | forward; try apply ENTAIL_refl
      | forward; try apply ENTAIL_refl ]
    | ]
  end.

(* the prologue after the loads (nbSeq > 0): fseEntropy, prevOffset, BIT_initDStream (error: return), the three
   initFseState; continues with the phase-1 loop invariant at id = 0 *)
(* the split loop always has a capacity: the head with its 32 cells lies in dst *)
Lemma sp_cap_pos (a: sa) : sa_ok a -> 0 < sp_cap a.
Proof.
  intros (_ & _ & Hl & _). destruct Hl as (_ & _ & Hgt & Hdlb & Hlbn & _).
  unfold sp_cap, sp_d, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia.
Qed.

(* at the start: the history, the extDict and the head with its 32 cells are defined *)
Lemma sp_dfd0 (a: sa) : sa_ok a -> sa_dok a -> sp_dfd a 0 (sp_c0 a).
Proof.
  intros Hsa [Hhd Hsl]. pose proof (sp_cap_pos a Hsa) as Hcap.
  destruct Hsa as (Ho & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _).
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  destruct Hlt as (Hlb & _ & Hgt & Hdlb & Hlbn & Hsub).
  unfold sp_dfd, sp_N, sp_d, sp_cap, sp_ps, sp_lim, sp_n, sp_x, sp_c0 in *.
  split; [rewrite Z.add_0_r, sublist_nil; constructor|].
  split; [apply (hist_def_prefix _ _ _ _ Hhd); lia|]. split.
  - apply (hist_def_ext _ (oa_d (a_o a)) (hc_ps (a_h a))); auto; try lia.
    unfold exec_ext_ok. split; [lia|]. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia.
  - simpl in Hsl. apply (Forall_def_join _ (a_lb a) (a_lb a + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)));
      try (unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia); [| exact Hsl].
    rewrite Hsub. apply seg_init_zbytes_cells. unfold bytes_ok in *. apply Forall_sublist. exact Hlb.
Qed.

(* a step keeps it: every cell unchanged or a defined byte, the r bytes written defined *)
Lemma sp_dfd_step (a: sa) (K r: Z) (c c': list val) :
  sa_ok a -> 0 <= K -> 0 <= r -> sp_d a + K + r <= sp_N a -> Zlength c = sp_N a -> Zlength c' = Zlength c ->
  sp_dfd a K c -> xd_ub c c' -> Forall is_byte_val (sublist (sp_d a + K) (sp_d a + K + r) c') ->
  sp_dfd a (K + r) c'.
Proof.
  intros Hsa HK Hr Hend Hc Hc' Hdef Hu Hnew. pose proof (sp_cap_pos a Hsa) as Hcap.
  destruct Hdef as (Hw & Hh & He & Hl).
  destruct Hsa as (Ho & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _).
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  destruct Hlt as (_ & _ & Hgt & Hdlb & Hlbn & _).
  unfold sp_dfd, sp_N, sp_d, sp_cap, sp_ps, sp_lim, sp_n, sp_x, sp_c0 in *.
  split; [| split; [| split]].
  - replace (oa_d (a_o a) + (K + r)) with (oa_d (a_o a) + K + r) by lia.
    apply (Forall_def_join _ (oa_d (a_o a)) (oa_d (a_o a) + K)); try lia; [| exact Hnew].
    apply (Forall_def_ub c); auto; lia.
  - apply (Forall_def_ub c); auto; lia.
  - apply (ext_def_ub _ c); auto. unfold exec_ext_ok. split; [lia|].
    destruct (hc_ext (a_h a)); simpl in *; try tauto; lia.
  - apply (Forall_def_ub c); auto; unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia.
Qed.

(* what an execution at op = d + K with the literals at lb + j reads *)
Lemma sp_dfd_exec (a: sa) (K j: Z) (c: list val) :
  sa_ok a -> Zlength c = sp_N a -> 0 <= K <= sp_cap a -> 0 <= j <= sp_n a - LITBUFFEREXTRASIZE -> sp_dfd a K c ->
  Forall is_byte_val (sublist (sp_ps a) (sp_d a + K) c) /\ ext_def (sp_x a) c /\
  Forall is_byte_val (sublist (a_lb a + j) (sp_lim a + WILDCOPY_OVERLENGTH) c).
Proof.
  intros Hsa Hc HK Hj (Hw & Hh & He & Hl). pose proof (sp_cap_pos a Hsa) as Hcap.
  destruct Hsa as (Ho & _ & Hlt & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _).
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  destruct Hlt as (_ & _ & Hgt & Hdlb & Hlbn & _).
  unfold sp_N, sp_d, sp_cap, sp_ps, sp_lim, sp_n, sp_x, sp_c0 in *.
  split; [| split; [exact He |]].
  - apply (Forall_def_join _ (hc_ps (a_h a)) (oa_d (a_o a))); auto; lia.
  - eapply xd_sub; [| | | exact Hl]; unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia.
Qed.

Lemma seg_init {Espec: OracleKind} (HG: GLOBALS_obligation) (a: sa) (xr: list val) (REST: statement) (R: ret_assert) :
  sa_ok a -> sa_dok a -> sp_pending a -> 0 < a_nb a -> Zlength xr = WILDCOPY_OVERLENGTH -> byte_cells xr ->
  sa_x a xr -> RA_return R = RA_return (sp_R a) ->
  (forall (g: sg) (Q Rin: mpred) (w: sw),
     bfacts a g Q Rin -> g_xr g = xr -> w_id w = 0 -> w_K w = 0 -> w_j w = 0 -> w_c w = sp_c0 a ->
     w_crep w = a_rep a ->
     semax sp_Delta (sp_INV a g Q Rin true w (a_nb a)) REST R) ->
  semax sp_Delta (sp_P0 a xr) (sp_init REST) R.
Proof.
  intros Hsa Hda Hpend Hnb Hxl Hxb Hxa HR HK.
  unfold sp_init, sp_s1, sp_s2, sp_s3, sp_s4, sp_s5, sp_s6, sp_P0, sp_lvars, sp_ptrs. cbn [app].
  destruct R as [Rn Rb Rc Rr].
  assert (HR': Rr = RA_return (sp_R a)) by exact HR. clear HR. rename HR' into HR.
  pose proof Hsa as (Hoa & Hiw & Hlits & Hbsm & Hn & Hnbr & Hnb' & Hso & Hrep & Hfe & _ & _ & _ & _ & _).
  destruct (Hnb' ltac:(lia)) as [Hosn Hcap]. clear Hnb'.
  destruct (a_os a) as [t|] eqn:Hos; [|congruence]. clear Hosn.
  destruct (inwin_bits (a_i a) Hiw) as (sh1 & sh2 & Rin & Hsh1 & Hsh2 & Hin).
  sep_apply (sp_tabs_borrow HG (a_gv a) (a_p a) (a_ox a) t (a_fe a)).
  Intros tp sht fm Q.
  rename H into Hsht, H0 into Hgive, H1 into Hlend.
  rewrite Hin. fold (sp_sst a) (sp_s a). Intros.
  forward.
  rewrite (seg_init_ss_split (a_vss a)). Intros.
  destruct (a_rep a) as [[r1 r2] r3] eqn:Erep.
  pose proof Hrep as (Hr1 & Hr2 & Hr3).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?S))) _ _ =>
    match S with context C [field_at_ Tsh t_seqstate (DOT _prevOffset) (a_vss a)] =>
      let Inv := constr:(fun k: Z => ltac:(
         let S' := context C [field_at Tsh t_seqstate (DOT _prevOffset)
             (map (fun r => Vlong (Int64.repr r)) (sublist 0 k [r1; r2; r3]) ++ Zrepeat Vundef (3 - k)) (a_vss a)] in
         exact (PROPx [] (LOCALx Q (SEPx S'))))) in
      forward_for_simple_bound 3 (EX k: Z, Inv k)%assert
    end end.
  - entailer!. unfold field_at_. apply derives_refl.
  - assert (Hz: forall d, @Znth val d i (rep_vals (r1, r2, r3)) = Vint (Int.repr (Znth i [r1; r2; r3]))).
    { intros d. assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity. }
    forward.
    { rewrite Hz. entailer!. }
    forward.
    assert (Hz2: forall d, @Znth val d i [Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3)] =
                           Vint (Int.repr (Znth i [r1; r2; r3]))) by exact Hz.
    rewrite ?Hz, ?Hz2.
    assert (Hl: upd_Znth i
       (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 i [r1; r2; r3]) ++ Zrepeat Vundef (3 - i))
       (force_val (sem_cast_i2l Unsigned (Vint (Int.repr (Znth i [r1; r2; r3]))))) =
       map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 (i + 1) [r1; r2; r3]) ++
       Zrepeat Vundef (3 - (i + 1))).
    { assert (i = 0 \/ i = 1 \/ i = 2) as [ -> | [ -> | -> ] ] by lia; cbn;
        rewrite Int.unsigned_repr by rep_lia; reflexivity. }
    rewrite Hl. entailer!.
  - change (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 3 [r1; r2; r3]) ++ Zrepeat Vundef (3 - 3))
      with (rep64_vals (r1, r2, r3)).
    pose proof Hiw as (Hiw1 & Hiw2 & Hiw3 & Hiw4 & Hiw5 & Hiw6 & Hiw7 & Hiw8).
    fold (sp_s a) in Hiw7.
    assert (Hn32: 0 <= Zlength (sp_s a) <= 2 ^ 63 - 1)
      by (unfold sp_s; pose proof (Zlength_nonneg (iw_s (a_i a))); lia).
    assert (Hsub: sublist 0 (0 + Zlength (sp_s a)) (sp_s a) = sp_s a)
      by (rewrite Z.add_0_l; apply sublist_same; lia).
    assert_PROP (isptr (sp_sst a)) as Hst by (unfold bit_src; entailer!).
    destruct (bs_wf (sp_s a)) eqn:Ewf.
    + match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?S))) _ _ =>
        match S with context C [data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) (a_vss a))] =>
          let S' := context C [BIT_DStream_rep Tsh (a_gv a) (sp_s a) (sp_sst a) (bs_total (sp_s a))
                  (8 * Z.max 0 (Zlength (sp_s a) - 8)) (field_address t_seqstate (DOT _DStream) (a_vss a))] in
          forward_loop (PROPx [] (LOCALx Q (SEPx S))) continue: (PROPx [] (LOCALx Q (SEPx S')))
            break: (PROPx [] (LOCALx Q (SEPx S')))
        end end.
      * entailer!.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), sh2, sp_sst a, sp_s a, 0,
          Zlength (sp_s a), a_gv a).
        { rewrite isptr_offset_val_zero by exact Hst. entailer!.
          unfold field_address. rewrite if_true by auto with field_compatible. reflexivity. }
        rewrite Hsub, Ewf. Intros r. subst r.
        forward_call (Zlength (sp_s a)).
        assert (Hne: is_error_code (Zlength (sp_s a)) = false)
          by (unfold is_error_code; apply Z.ltb_ge; lia).
        rewrite Hne.
        forward_if.
        { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
        { forward. rewrite isptr_offset_val_zero by exact Hst. entailer!. }
      * forward. entailer!.
      * destruct t as [[tLL tOF] tML], tp as [[pLL pOF] pML], sht as [[shLL shOF] shML], fm as [[fLL fOF] fML].
        pose proof Hso as (HfLL & HfOF & HfML).
        destruct Hlend as [R' [Hl1 Hl2]].
        sep_apply Hl1.
        pose proof Hsht as (HsLL & HsOF & HsML).
        unfold seq_ptrs, seqtabs_at. Intros.
        assert_PROP (isptr pLL) as HpLL by (sep_apply (seg_init_tab_isptr shLL KLL tLL fLL pLL); entailer!).
        assert_PROP (isptr pOF) as HpOF by (sep_apply (seg_init_tab_isptr shOF KOF tOF fOF pOF); entailer!).
        assert_PROP (isptr pML) as HpML by (sep_apply (seg_init_tab_isptr shML KML tML fML pML); entailer!).
        pose proof (seg_init_bcons0 _ Hiw7 Ewf) as Hb0.
        pose proof HfLL as (HlLL & _). pose proof HfOF as (HlOF & _). pose proof HfML as (HlML & _).
        cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
        pose proof (seg_init_bsrc (sp_s a) _ Hst) as Hbs.
        forward.
        forward_call (Tsh, field_address t_seqstate (DOT _stateLL) (a_vss a), Tsh,
          field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, sp_s a, sp_sst a,
          bs_total (sp_s a), (8 * Z.max 0 (Zlength (sp_s a) - 8))%Z, sh2, sp_sst a, sp_s a, 0,
          shLL, KLL, tLL, fLL, pLL).
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        Intros v1.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi1 by (sep_apply seg_init_rep_inv; entailer!);
          pose proof (seg_init_bcons_step (bs_total (sp_s a)) (8 * Z.max 0 (Zlength (sp_s a) - 8)) (ft_log tLL)
            ltac:(lia) ltac:(unfold bcons in Hb0; lia)) as Hb1;
          forward;
          forward_call (Tsh, field_address t_seqstate (DOT _stateOffb) (a_vss a), Tsh,
            field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, sp_s a, sp_sst a,
            pos, lo, sh2, sp_sst a, sp_s a, 0, shOF, KOF, tOF, fOF, pOF)
        end.
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        Intros v2.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi2 by (sep_apply seg_init_rep_inv; entailer!)
        end.
        pose proof (seg_init_bcons_step (bs_total (sp_s a) - ft_log tLL)
            (snd (bs_reload (bs_total (sp_s a) - ft_log tLL) (8 * Z.max 0 (Zlength (sp_s a) - 8))))
            (ft_log tOF) ltac:(lia) ltac:(lia)) as Hb2.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          forward;
          forward_call (Tsh, field_address t_seqstate (DOT _stateML) (a_vss a), Tsh,
            field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, sp_s a, sp_sst a,
            pos, lo, sh2, sp_sst a, sp_s a, 0, shML, KML, tML, fML, pML)
        end.
        { entailer!. unfold field_address. rewrite !if_true by auto with field_compatible. reflexivity. }
        Intros v3.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          assert_PROP (0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64) as Hi3 by (sep_apply seg_init_rep_inv; entailer!)
        end.
        pose proof (seg_init_bcons_step (bs_total (sp_s a) - ft_log tLL - ft_log tOF)
           (snd (bs_reload (bs_total (sp_s a) - ft_log tLL - ft_log tOF)
              (snd (bs_reload (bs_total (sp_s a) - ft_log tLL) (8 * Z.max 0 (Zlength (sp_s a) - 8))))))
           (ft_log tML) ltac:(lia) ltac:(lia)) as Hb3.
        unfold seqtabs_at in Hl2. sep_apply Hl2.
        match goal with |- context [BIT_DStream_rep Tsh _ _ _ ?pos ?lo _] =>
          eapply semax_pre; [| apply (HK {| g_t := (tLL, tOF, tML); g_tp := (pLL, pOF, pML);
            g_sht := (shLL, shOF, shML); g_fm := (fLL, fOF, fML); g_sh1 := sh1; g_sh2 := sh2; g_xr := xr |} Q Rin
            {| w_id := 0; w_pos := pos; w_lo := lo; w_st := (v1, v2, v3); w_crep := (r1, r2, r3); w_K := 0;
               w_j := 0; w_c := sp_c0 a |}) ]
        end.
        -- unfold sp_INV. match goal with |- context [sinv ?a ?t ?ph ?w] => assert (Hsinv: sinv a t ph w) end.
           { clear HK Hgive Hl1 Hl2 Hin.
             unfold sinv. cbn [g_t w_id w_pos w_lo w_st w_crep w_K w_j w_c].
             split; [lia|]. split; [discriminate|]. split; [lia|].
             split. { unfold LONGNBSEQ in Hnbr. unfold DSEQ_BITS. rep_lia. }
             split. { unfold states_ok. lia. }
             split; [exact Hrep|].
             split.
             { pose proof Hoa as (_ & HcN & _ & _ & _ & _).
               pose proof Hlits as (_ & _ & Hsp & _).
               unfold sp_outok. split; [lia|]. split; [exact HcN|].
               split. { split; [unfold sp_n; lia|]. intros k _ _. reflexivity. }
               split. { apply sp_dfd0; auto. }
               intros Hc _ _. exact Hc. }
             unfold sp_minv. intros seqs out' lits' rep2 Hm.
             unfold model_hyp in Hm. destruct Hm as (Hhv & Hec & Hdec & Hex & Hcnt).
             destruct (loop_init_model tLL tOF tML (sp_s a) (a_nb a) seqs v1 v2 v3 Hiw7 Ewf HfLL HfOF HfML
               H0 H2 H4 Hdec) as [Hrdy Hd].
             cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c]. rewrite Z.sub_0_r. change (Z.to_nat 0) with O.
             cbn [skipn].
             split; [exact Hd|]. split; [intros _; exact Hrdy|]. split; [intros; lia|].
             exists []. split; [reflexivity|]. split.
             { rewrite app_nil_r. rewrite Erep in Hex. exact Hex. }
             intros _. rewrite Z.add_0_r, sublist_nil. reflexivity. }
           match goal with |- context [xinv ?a ?t ?cl ?ph ?w] => assert (Hxinv: xinv a t cl ph w) end.
           { clear HK Hgive Hl1 Hl2 Hin. cbn [g_t g_xr].
             pose proof (xinit a (tLL, tOF, tML) (zbytes (sp_tail a) ++ xr) v1 v2 v3 Hsa Hos ltac:(lia) Ewf
                           (sa_x_cl a xr Hxa) (proj1 Hxa)) as HX.
             cbv zeta in HX. rewrite Erep in HX. exact (HX H0 H2 H4). }
           unfold sp_L, sp_S, sp_FRL, sp_lvars, sp_ptrs, seqstate_at, sp_lp, sp_lbe, sp_loc, seq_ptrs.
           cbn [g_t g_tp g_sht g_fm g_sh1 g_sh2 g_xr w_id w_pos w_lo w_st w_crep w_K w_j w_c app].
           rewrite !Z.add_0_r, Erep.
           entailer!.
        -- clear HK. unfold bfacts. cbn [g_t g_tp g_sht g_fm g_sh1 g_sh2 g_xr].
           rewrite Hos. split; [reflexivity|]. split; [exact Hsht|]. split; [exact Hgive|].
           split. { exists R'. split; [exact Hl1|]. unfold seqtabs_at. exact Hl2. }
           split; [exact Hsh1|]. split; [exact Hsh2|]. split; [exact Hin|]. split; [exact Hxl | exact Hxb].
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
    + clear HK.
      match goal with |- semax _ ?Pre _ _ =>
        forward_loop Pre continue: (PROP (False) LOCAL () SEP ()) break: (PROP (False) LOCAL () SEP ()) end.
      * entailer!.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), sh2, sp_sst a, sp_s a, 0,
          Zlength (sp_s a), a_gv a).
        { rewrite isptr_offset_val_zero by exact Hst. entailer!.
          unfold field_address. rewrite if_true by auto with field_compatible. reflexivity. }
        rewrite Hsub, Ewf. Intros r.
        match goal with H: is_error_code r = true |- _ => rename H into Hre end.
        forward_call r.
        rewrite Hre.
        forward_if.
        { seg_init_dw0. seg_init_dw0if. seg_init_dw0. seg_init_dw0.
          subst Rr. apply semax_post with (R' := sp_R a).
          1-3: unfold sp_R, frame_ret_assert, function_body_ret_assert; simpl RA_normal; simpl RA_break;
               simpl RA_continue; unfold bind_ret; apply andp_left2; intro rho; simpl; normalize; try contradiction.
          1: intros vl; apply andp_left2; apply derives_refl.
          assert (Hmn: seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a))
                         (a_lits a) (hc_wsize (a_h a)) = None)
            by (rewrite Hos; apply seg_init_model_none; [exact Ewf | lia]).
          assert (Hin': data_at sh1 (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
                        bit_src sh2 (sp_sst a) (sp_s a) * Rin |--
                        data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)))
            by (rewrite Hin; apply derives_refl).
          assert (Hxp: xpost a (2 ^ 64 - 20) (oa_c (a_o a)) (r1, r2, r3)).
          { apply xpost_err; [reflexivity|]. intros. eapply xinit_err; eauto; lia. }
          clear Hin Hlend.
          unfold sp_R, sp_post. forward.
          Exists (2 ^ 64 - 20) (oa_c (a_o a)) (r1, r2, r3).
          rewrite Hmn, (proj2 (Z.eqb_neq (a_nb a) 0) ltac:(lia)), Hos.
          sep_apply (Hgive 1). sep_apply Hin'.
          unfold sp_FR0.
          sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a)))
                       (offset_val (a_lb a) (sp_ob a)) (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr LOC_SPLIT)) Hxa).
          change (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) (a_vss a)) with (data_at_ Tsh t_seqstate (a_vss a)).
          rewrite (seg_init_ss_split (a_vss a)).
          unfold sp_ob, sp_c0, sp_N, sp_x in *.
          entailer!.
          repeat match goal with
            | |- _ /\ _ => split
            | |- Zlength _ = _ => pose proof Hoa as (_ & Hl & _); exact Hl
            | |- is_error_code _ = false -> _ => intros Hf; discriminate Hf
            | |- is_error_code _ = true -> dec_err _ =>
                intros _; exact (fs_dec_err 20 ltac:(lia) ltac:(lia) ltac:(lia))
            | |- Vlong _ = Vlong _ => f_equal; apply seg_init_repr_eqm; reflexivity
            | |- xpost _ _ _ _ => exact Hxp
            end. }
        { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end. }
Qed.

(* seg_dec's helpers (prefix sdec_): the skipn step, the model after one decode, the bitstream facts *)
Lemma sdec_skipn (A: Type) (n: Z) (xs rest: list A) (x: A) :
  0 <= n -> skipn (Z.to_nat n) xs = x :: rest -> rest = skipn (Z.to_nat (n + 1)) xs.
Proof.
  intros Hn H. replace (Z.to_nat (n + 1)) with (1 + Z.to_nat n)%nat by lia.
  rewrite <- skipn_skipn, H. reflexivity.
Qed.

Lemma sdec_spend (a: sa) (t: fse_table * fse_table * fse_table) (ph: bool) (w: sw) (pos' lo': Z)
    (st': Z * Z * Z) (ll ml ov: Z) :
  seqs_ok (Some t) -> sinv a t ph w -> w_id w < a_nb a ->
  w_lo w mod 8 = 0 -> w_pos w <= w_lo w + 64 ->
  0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= ov < 2 ^ 32 -> states_ok t st' ->
  w_pos w - DSEQ_BITS <= pos' <= w_pos w -> 0 <= lo' <= w_lo w ->
  ((a_nb a - w_id w =? 1) = true -> st' = w_st w) ->
  (bs_ready (w_pos w) (w_lo w) ->
   forall sq stn pn,
     (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := w_st w in
      dseq_one tLL tOF tML (sp_s a) (a_nb a - w_id w =? 1) sLL sOF sML (w_pos w)) = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     ((a_nb a - w_id w =? 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
  spend a t ph (Build_sw (w_id w) pos' lo' st' (w_crep w) (w_K w) (w_j w) (w_c w)) ll ml ov.
Proof.
  destruct w as [id pos lo st crep K j c]. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  intros Hso Hinv Hid H8 Hplo Hll Hml Hov Hst' Hpos' Hlo' Hlast Hspec.
  destruct Hinv as (Hid0 & Hph & H0lo & Hbc & Hst & Hrep & Hout & Hminv).
  cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in *.
  unfold spend. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  split; [lia|]. split; [exact Hph|]. split; [lia|].
  split; [unfold bcons, DSEQ_BITS in *; lia|].
  split; [exact Hst'|]. split; [exact Hrep|].
  split; [exact Hll|]. split; [exact Hml|]. split; [exact Hov|]. split; [exact Hout|].
  intros seqs out' lits' rep2 Hm.
  destruct (Hminv seqs out' lits' rep2 Hm) as (Hds & Hrdy & _ & Hex).
  cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in Hds, Hrdy, Hex.
  specialize (Hrdy Hid).
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML]; destruct st' as [[sLL' sOF'] sML'].
  destruct Hso as (HfLL & HfOF & HfML). destruct Hst as (HsLL & HsOF & HsML).
  cbv beta iota zeta in Hds, Hspec |- *.
  assert (Hk: Z.to_nat (a_nb a - id) = S (Z.to_nat (a_nb a - id - 1))) by lia.
  rewrite Hk in Hds.
  destruct (loop_dec_step _ _ _ _ _ _ _ _ _ _ Hds) as (sq & x & y & z & pn & rest & Hl & Hone & Hrest & Hk0).
  assert (Hle: Nat.eqb (Z.to_nat (a_nb a - id - 1)) 0 = (a_nb a - id =? 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (a_nb a - id - 1)) 0); destruct (Z.eqb_spec (a_nb a - id) 1); lia. }
  rewrite Hle in Hone.
  destruct (Hspec Hrdy sq (x, y, z) pn Hone) as (Ell & Eml & Eov & Hpn & Hnl).
  pose proof (sdec_skipn _ id seqs rest sq ltac:(lia) Hl) as Hrs.
  exists sq. split; [rewrite Hl, Hrs; reflexivity|].
  split; [auto|]. split; [auto|]. split; [auto|].
  destruct (a_nb a - id =? 1) eqn:EL.
  - apply Z.eqb_eq in EL. rewrite <- Hrs.
    destruct Hk0 as [Hr0 Hp0]; [lia|]. subst rest pn. subst pos'.
    specialize (Hlast eq_refl). injection Hlast as -> -> ->.
    assert (Hlo0: lo' = 0)
      by (eapply (loop_end_lo tLL tOF tML (sp_s a) sLL sOF sML pos lo lo' sq (x, y, z)); eauto).
    subst lo'.
    split; [replace (Z.to_nat (a_nb a - id - 1)) with O by lia; simpl; rewrite Hr0; reflexivity|].
    split; [intros; lia|]. split; [intros; reflexivity|].
    exact Hex.
  - apply Z.eqb_neq in EL. destruct (Hnl eq_refl) as [Hst'' Hrd]. injection Hst'' as -> -> ->. subst pos'.
    split; [rewrite Hrest, Hrs; reflexivity|].
    split; [intros; exact Hrd|]. split; [intros; lia|].
    exact Hex.
Qed.

Lemma sdec_bit (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z)
    (tp: val * val * val) (r: Z * Z * Z) (q: val) :
  seqstate_at sh gv s start pos lo st tp r q |-- !! bit_inv s pos lo.
Proof.
  unfold seqstate_at, BIT_DStream_rep. destruct st as [[x y] z]; destruct tp as [[x' y'] z'].
  Intros ptr lim. entailer!.
Qed.

(* ZSTD_decodeSequence in either loop (ph = true: into `sequence`, else `sequence__1`) *)
Lemma seg_dec {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> w_id w < a_nb a ->
  semax sp_Delta (sp_INV a g Q Rin ph w (a_nb a - w_id w)) (if ph then sp_dec1 else sp_dec2)
    (normal_ret_assert (EX w': sw, EX ll: Z, EX ml: Z, EX ov: Z, sp_PEND a g Q Rin ph w' ll ml ov)).
Proof.
  intros Hsa Hpend Hbf Hid.
  destruct Hbf as (Hos & Hsht & _ & (R' & HL1 & HL2) & _ & Hsh2 & _ & _).
  assert (Hso: seqs_ok (Some (g_t g))) by (rewrite <- Hos; apply Hsa).
  unfold sp_INV, sp_S, sp_L, sp_lvars, sp_ptrs. simpl app. Intros.
  rename H into Hinv, H0 into Hxinv.
  assert (Hinv' := Hinv). destruct Hinv' as (Hid0 & _ & H0lo & Hbc & Hst & Hrep & _ & _).
  assert_PROP (bit_inv (sp_s a) (w_pos w) (w_lo w)) as HBI.
  { sep_apply (sdec_bit Tsh (a_gv a) (sp_s a) (sp_sst a) (w_pos w) (w_lo w) (w_st w) (g_tp g) (w_crep w) (a_vss a)).
    entailer!. }
  assert_PROP (isptr (sp_sst a)) as Hsst.
  { unfold bit_src. entailer!. }
  sep_apply HL1. Intros.
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by apply Hsa.
  unfold sp_Delta; simplify_func_tycontext.
  destruct ph; unfold sp_dec1, sp_dec2.
  - forward_call (a_gv a, Tsh, a_vsq a, Tsh, a_vss a, sp_s a, sp_sst a, w_pos w, w_lo w, w_st w, g_t g, g_tp g,
                  g_sht g, g_fm g, w_crep w, g_sh2 g, sp_sst a, sp_s a, 0, 0, (a_nb a - w_id w =? 1)).
    { go_lower. apply prop_right. simpl. unfold Int.eq.
      rewrite !Int.unsigned_repr by (unfold LONGNBSEQ in *; rep_lia).
      destruct (Z.eqb_spec (a_nb a - w_id w) 1); destruct (zeq (a_nb a - w_id w) 1); try lia; reflexivity. }
    { split; [|split].
      - unfold bit_src_ok. rewrite isptr_offset_val_zero by exact Hsst.
        split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity].
      - apply les_rep64, Hrep.
      - unfold DSEQ_BITS in *. lia. }
    Intros vret. destruct vret as [[[[[ll ml] ov] st'] pos'] lo']. Intros. cbn [fst snd] in *.
    sep_apply HL2.
    destruct HBI as (_ & _ & _ & H8lo & _ & Hplo & _).
    assert (HS := sdec_spend a (g_t g) true w pos' lo' st' ll ml ov Hso Hinv Hid H8lo Hplo
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    assert (HX := xdec a (g_t g) (zbytes (sp_tail a) ++ g_xr g) true w pos' lo' st' ll ml ov Hso Hinv Hxinv Hid
                    H8lo Hplo ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption)).
    Exists (Build_sw (w_id w) pos' lo' st' (w_crep w) (w_K w) (w_j w) (w_c w)) ll ml ov.
    unfold sp_PEND, sp_S, sp_L, sp_lvars, sp_ptrs. simpl app. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
    entailer!.
  - forward_call (a_gv a, Tsh, a_vsq1 a, Tsh, a_vss a, sp_s a, sp_sst a, w_pos w, w_lo w, w_st w, g_t g, g_tp g,
                  g_sht g, g_fm g, w_crep w, g_sh2 g, sp_sst a, sp_s a, 0, 0, (a_nb a - w_id w =? 1)).
    { go_lower. apply prop_right. simpl. unfold Int.eq.
      rewrite !Int.unsigned_repr by (unfold LONGNBSEQ in *; rep_lia).
      destruct (Z.eqb_spec (a_nb a - w_id w) 1); destruct (zeq (a_nb a - w_id w) 1); try lia; reflexivity. }
    { split; [|split].
      - unfold bit_src_ok. rewrite isptr_offset_val_zero by exact Hsst.
        split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity].
      - apply les_rep64, Hrep.
      - unfold DSEQ_BITS in *. lia. }
    Intros vret. destruct vret as [[[[[ll ml] ov] st'] pos'] lo']. Intros. cbn [fst snd] in *.
    sep_apply HL2.
    destruct HBI as (_ & _ & _ & H8lo & _ & Hplo & _).
    assert (HS := sdec_spend a (g_t g) false w pos' lo' st' ll ml ov Hso Hinv Hid H8lo Hplo
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    assert (HX := xdec a (g_t g) (zbytes (sp_tail a) ++ g_xr g) false w pos' lo' st' ll ml ov Hso Hinv Hxinv Hid
                    H8lo Hplo ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption)).
    Exists (Build_sw (w_id w) pos' lo' st' (w_crep w) (w_K w) (w_j w) (w_c w)) ll ml ov.
    unfold sp_PEND, sp_S, sp_L, sp_lvars, sp_ptrs. simpl app. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
    entailer!.
Qed.

(* phase 1 after the decode: break when the head has fewer than ll literals left, else
   ZSTD_execSequenceSplitLitBuffer (an error is returned) *)
Definition sp_x1_R (a: sa) (g: sg) (Q Rin: mpred) : ret_assert :=
  {| RA_normal := EX w': sw, sp_INV a g Q Rin true w' (a_nb a - w_id w' + 1);
     RA_break := EX w': sw, EX ll: Z, EX ml: Z, EX ov: Z,
                   !! (sp_lim a - (a_lb a + w_j w') < ll) && sp_PEND a g Q Rin true w' ll ml ov;
     RA_continue := FF;
     RA_return := RA_return (sp_R a) |}.

(* the break test: (size_t)(litBufferEnd - litPtr) < litLength *)
Lemma sx1_sub32 (i: ptrofs) (n: Z) :
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 32))) =
  Ptrofs.add i (Ptrofs.repr (n - WILDCOPY_OVERLENGTH)).
Proof.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, <- Ptrofs.sub_add_opp. f_equal.
  unfold Ptrofs.sub, WILDCOPY_OVERLENGTH. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sub;
  apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma sx1_cmp (b: val) (x y ll: Z) :
  isptr b -> 0 <= x - y <= Int64.max_signed -> 0 <= ll <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n1 n2))) sem_cast_pointer sem_cast_pointer
      (force_val (sem_sub_pp tuchar (offset_val x b) (offset_val y b))) (Vlong (Int64.repr ll)) with
  | Some v' => v' | None => Vundef end = bool2val (x - y <? ll).
Proof.
  intros Hb Hxy Hll. destruct b; try contradiction. unfold sem_sub_pp. simpl.
  rewrite peq_true. simpl.
  replace (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr x)) (Ptrofs.add i (Ptrofs.repr y))) with (Ptrofs.repr (x - y)).
  2: { rewrite (Ptrofs.add_commut i), (Ptrofs.add_commut i), Ptrofs.sub_shifted.
       unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr.
       apply Ptrofs.eqm_sub; apply Ptrofs.eqm_unsigned_repr. }
  rewrite Ptrofs.divs_one by reflexivity. unfold Ptrofs.to_int64. unfold Int64.ltu.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned, Int64.max_signed in *; simpl in *; lia).
  rewrite !Int64.unsigned_repr by (unfold Int64.max_signed, Int64.max_unsigned in *; simpl in *; lia).
  destruct (zlt (x - y) ll); destruct (x - y <? ll) eqn:E; try reflexivity; lia.
Qed.

(* the call's preconditions *)
Lemma sx1_pre (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> ll <= sp_lim a - (a_lb a + w_j w) ->
  Zlength (w_c w) = sp_N a /\ 0 < sp_cap a /\
  writable_share (oa_sh (a_o a)) /\ Zlength (w_c w) <= 2 ^ 63 - 1 /\ 0 <= sp_ps a <= sp_d a + w_K w /\
  sp_d a + w_K w <= sp_d a + sp_cap a <= Zlength (w_c w) /\ 0 <= ll <= 2 ^ 24 /\ 1 <= ml <= 2 ^ 24 /\
  1 <= fst (c_offset (w_crep w) ll ov) <= Int64.max_unsigned /\ 0 <= a_lb a + w_j w /\
  sp_lim a + WILDCOPY_OVERLENGTH <= sp_d a + sp_cap a /\ exec_ext_ok (sp_x a) (w_c w) /\
  is_pointer_or_null (fs_dictEnd (a_fs a)) /\
  sp_d a + sp_cap a - (a_lb a + w_j w) + WILDCOPY_OVERLENGTH <= 2 ^ 63.
Proof.
  intros Hsa (_ & HdE) Hsp Hbrk.
  destruct Hsa as (Ho & _ & Hl & Hbsm & Hn & _ & Hnc & _ & _ & _ & _ & Hlay & _ & Hlp & _).
  destruct Hsp as (Hid & _ & _ & _ & _ & Hrep & Hll & Hml & Hov & (HK & HcN & (Hj & _) & _) & _).
  destruct (Hnc ltac:(lia)) as [_ Hcap]. specialize (Hlay Hcap).
  destruct Hlay as (Hps & _ & _ & Hel & Hx).
  destruct Ho as (Hsh & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hl as (_ & _ & _ & Hdlb & Hlbn & _).
  destruct (c_offset_ok (w_crep w) ll ov (les_rep64 _ Hrep) Hov) as [Hoff _].
  unfold sp_N, sp_cap, sp_d, sp_ps, sp_lim, sp_n, sp_x in *.
  unfold LL_VMAX, ML_VMAX, SIZE_MAX, LITBUFFEREXTRASIZE in *.
  split; [lia|]. split; [lia|]. split; [exact Hsh|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [rep_lia|]. split; [lia|]. split; [lia|].
  split; [|split; [exact HdE|]].
  - unfold exec_ext_ok. split; [lia|].
    destruct (hc_ext (a_h a)); simpl in *; try tauto; lia.
  - (* the split literal buffer lies at the end of the block's output (lit_pos) *)
    simpl in Hlp. unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *. lia.
Qed.

(* the model's success as seqs_model gives it *)
Lemma sx1_model (a: sa) (t: fse_table * fse_table * fse_table) (cnt: list Z) (rep2: Z * Z * Z) :
  0 < a_nb a -> a_os a = Some t ->
  hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  seqs_model (a_os a) (sp_s a) (a_nb a) (a_rep a) (sp_hist a) (sp_out a) (a_lits a) (sp_ws a) = Some (cnt, rep2) ->
  Zlength cnt <= a_bsm a ->
  exists seqs out' lits', model_hyp a t seqs out' lits' rep2 /\ cntlen a out' lits' = Zlength cnt.
Proof.
  intros Hnb Hos Hhv Hcl Hm Hcnt.
  unfold seqs_model in Hm. rewrite Hos in Hm. destruct t as [[tLL tOF] tML].
  replace (a_nb a =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; lia).
  destruct (decode_seq_stream tLL tOF tML (sp_s a) (a_nb a)) as [seqs|] eqn:Hd; [|discriminate].
  destruct (exec_seqs (sp_ws a) (a_rep a) (sp_hist a) (a_lits a) (sp_out a) seqs) as [[[out' lits'] rep']|] eqn:He;
    [|discriminate].
  injection Hm as Hc Hr. subst rep'.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ He) as [mid Hmid].
  assert (Hsk: cnt = mid ++ lits').
  { rewrite <- Hc, Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hl: cntlen a out' lits' = Zlength cnt).
  { unfold cntlen. rewrite Hsk, Hmid, !Zlength_app. lia. }
  exists seqs, out', lits'. split; [|exact Hl].
  unfold model_hyp. split; [exact Hhv|]. split; [exact Hcl|]. split; [exact Hd|]. split; [exact He|].
  fold (cntlen a out' lits'). lia.
Qed.

(* the head literals the call copies: untouched (at or after max(op, litPtr)), the model's next ones *)
Lemma sx1_lits (a: sa) (K j ll: Z) (c: list val) :
  sa_ok a -> sp_outok a true K j c -> sp_d a + K <= a_lb a + j -> 0 <= ll -> a_lb a + j + ll <= sp_lim a ->
  sublist (a_lb a + j) (a_lb a + j + ll) c = zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat j) (a_lits a))).
Proof.
  intros Hsa (HK & HcN & (Hj & Hun) & _) HKj Hll Hlim.
  destruct Hsa as (Ho & _ & Hl & _).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  destruct Hl as (_ & Hn0 & Hgt & Hdlb & Hlbn & Hsub).
  unfold sp_lim, sp_n, sp_N, sp_c0, sp_d, sp_cap, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  assert (E: sublist (a_lb a + j) (a_lb a + j + ll) c = sublist (a_lb a + j) (a_lb a + j + ll) (oa_c (a_o a))).
  { apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
    intros q Hq. rewrite Zlength_sublist in Hq by lia.
    rewrite !Znth_sublist by lia. apply Hun; [lia|]. intros Hq'. lia. }
  rewrite E.
  replace (a_lb a + j) with (j + a_lb a) by lia. replace (j + a_lb a + ll) with (j + ll + a_lb a) by lia.
  rewrite <- (sublist_sublist (j + ll) (a_lb a + (Zlength (a_lits a) - 65536)) j (a_lb a)) by lia.
  rewrite Hsub, sublist_map. f_equal.
  rewrite sublist_sublist by lia. rewrite !Z.add_0_r.
  unfold sublist. rewrite firstn_skipn_comm.
  replace (Z.to_nat (j + ll)) with (Z.to_nat j + Z.to_nat ll)%nat by lia.
  replace (Z.to_nat (j + ll - j)) with (Z.to_nat ll) by lia. reflexivity.
Qed.

(* the model's step for the pending sequence: the new block bytes blk ++ L ++ mb; when the content fits the
   capacity, the literals are far ahead of op and the call's result is the model's (loop_exec_step, lo = 0) *)
Lemma sx1_mstep (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> model_hyp a t seqs out' lits' rep2 ->
  exists blk mb,
    Zlength blk = w_K w /\ Zlength mb = ml /\ ll <= sp_n a - w_j w /\
    exec_seqs (sp_ws a) (snd (c_offset (w_crep w) ll ov)) (sp_hist a) (skipn (Z.to_nat (w_j w + ll)) (a_lits a))
      (sp_out a ++ blk ++ firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb)
      (skipn (Z.to_nat (w_id w + 1)) seqs) = Some (out', lits', rep2) /\
    (cntlen a out' lits' <= sp_cap a ->
       sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk /\
       sp_d a + w_K w + WILDCOPY_OVERLENGTH <= a_lb a + w_j w /\ w_K w <= a_bsm a /\
       sp_d a + w_K w + ll + ml <= sp_d a + cntlen a out' lits' /\
       fst (c_offset (w_crep w) ll ov) <= sp_d a + w_K w + ll - sp_ps a + ext_len (sp_x a) /\
       ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) /\
       sublist (sp_d a + w_K w) (sp_d a + w_K w + ll + ml)
         (exec_c (w_c w) (sp_d a + w_K w) (zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)))) ml
            (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (sp_x a)) =
       zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb)).
Proof.
  intros Hsa Hpend Hsp Hmh.
  destruct Hsa as (Ho & Hi & Hl & Hbsm & Hn & Hnb & Hnc & Hso & Hrep0 & Hfe & Hc0 & Hlay & Hhp & Hlp & He0).
  destruct Hsp as (Hid & _ & Hlo & Hbc & Hst & Hrep & Hll & Hml & Hov & Hok & Hm).
  destruct Hok as (HK & HcN & (Hj & Hun) & Hdef & Hbyt).
  destruct (Hm seqs out' lits' rep2 Hmh) as (sq & Hsq & Hsll & Hsml & Hsov & _ & _ & _ & blk & Hblen & Hex & Hbytes).
  clear Hm. rewrite Hsq in Hex.
  destruct t as [[tLL tOF] tML]. destruct Hmh as (Hhv & Hcl & _ & _ & Hcnt).
  fold (cntlen a out' lits') in Hcnt.
  destruct (sp_exec_len _ _ _ _ _ _ _ _ _ Hex) as (ext & Hout & Hl1 & Hl2).
  assert (Hsk: Zlength (skipn (Z.to_nat (w_j w)) (a_lits a)) = sp_n a - w_j w).
  { rewrite Zlength_skipn. unfold sp_n, LITBUFFEREXTRASIZE in *. lia. }
  assert (Hcl2: cntlen a out' lits' = w_K w + Zlength ext + Zlength lits').
  { unfold cntlen. rewrite Hout, !Zlength_app. lia. }
  destruct Hl as (Hlb & Hn0 & Hgt & Hdlb & Hlbn & Hsub).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct (Hnc ltac:(lia)) as [_ Hcap].
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hx).
  assert (Hlr: bytes_ok (skipn (Z.to_nat (w_j w)) (a_lits a))) by (unfold bytes_ok in *; apply Forall_skipn; exact Hlb).
  destruct (Z_le_gt_dec (cntlen a out' lits') (sp_cap a)) as [Hfit|Hnofit].
  - destruct Hpend as (Hpd & _).
    pose proof (Zlength_nonneg ext). pose proof (Zlength_nonneg lits').
    assert (HKb: w_K w <= a_bsm a) by lia.
    assert (Hfar: sp_d a + w_K w + WILDCOPY_OVERLENGTH <= a_lb a + w_j w).
    { unfold sp_n, sp_d, sp_cap in *.
      destruct (Z.min_spec (a_bsm a) (oa_cap (a_o a))) as [[_ E]|[_ E]]; rewrite E in Hpd; lia. }
    specialize (Hbytes Hfit).
    destruct (loop_exec_step (sp_c0 a) (w_c w) (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a)
                (sp_out a) (sp_ws a) blk (skipn (Z.to_nat (w_j w)) (a_lits a)) 0 sq (skipn (Z.to_nat (w_id w + 1)) seqs)
                (w_crep w) out' lits' rep2)
      as (off & crep' & mb & Hco & Hrep' & Hlrl & Hend & Hoff & Hmb & Hfitp & Hexr).
    + unfold sp_d, sp_ps in *. lia.
    + unfold sp_cap in *. lia.
    + unfold sp_d, sp_cap, sp_N in *. lia.
    + unfold sp_c0, sp_N in *. lia.
    + lia.
    + exact Hhv.
    + exact Hcl.
    + unfold ext_in_bounds. unfold sp_x, sp_N in *. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia.
    + lia.
    + intros q Hq Hnq. apply Hun; [exact Hq|]. intros Hq2. apply Hnq.
      unfold WILDCOPY_OVERLENGTH in *. lia.
    + exact Hlr.
    + exact Hrep.
    + exact Hex.
    + exact Hcnt.
    + lia.
    + lia.
    + rewrite Hsov. exact Hov.
    + rewrite Z.add_0_r, Hblen. simpl. rewrite app_nil_r. exact Hbytes.
    + cbv zeta in *. rewrite Hsll, Hsml, Hsov in *. rewrite Hblen in *.
      rewrite Hco. cbn [fst snd].
      exists blk, mb. split; [exact Hblen|]. split; [exact Hmb|]. split; [rewrite Hsk in Hlrl; lia|].
      split.
      { rewrite skipn_skipn in Hexr.
        replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hexr by lia. exact Hexr. }
      intros _. split; [exact Hbytes|]. split; [exact Hfar|]. split; [exact HKb|].
      split; [unfold cntlen; lia|]. split; [lia|].
      destruct Hfitp as (Hro & Hec); [unfold cntlen in *; lia|].
      split.
      * specialize (Hro (sp_d a + sp_cap a) ltac:(lia)). rewrite Z.add_0_r, Z.sub_0_r in Hro. exact Hro.
      * rewrite !Z.add_0_r in Hec. simpl skipn in Hec. exact Hec.
  - exists blk.
    destruct (sp_exec_free (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
                sq (skipn (Z.to_nat (w_id w + 1)) seqs) out' lits' rep2 Hrep ltac:(lia) ltac:(lia)
                ltac:(rewrite Hsov; exact Hov) Hex)
      as (off & crep' & mb & Hco & _ & _ & Hlr' & Hmb & Hexf).
    rewrite Hsll, Hsml, Hsov in *. rewrite Hco. cbn [snd].
    exists mb. split; [exact Hblen|]. split; [exact Hmb|]. split; [rewrite Hsk in Hlr'; lia|].
    split; [|intros; lia].
    rewrite skipn_skipn in Hexf. rewrite <- app_assoc in Hexf.
    replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hexf by lia. exact Hexf.
Qed.

(* an error of the call means the content does not fit the capacity *)
Lemma sx1_err (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (cnt: list Z) (rep2: Z * Z * Z) :
  sa_ok a -> sp_pending a -> a_os a = Some t -> spend a t true w ll ml ov ->
  exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml (fst (c_offset (w_crep w) ll ov))
    (sp_ps a) (ext_len (sp_x a)) = true ->
  hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  seqs_model (a_os a) (sp_s a) (a_nb a) (a_rep a) (sp_hist a) (sp_out a) (a_lits a) (sp_ws a) = Some (cnt, rep2) ->
  Zlength cnt <= a_bsm a -> sp_cap a < Zlength cnt.
Proof.
  intros Hsa Hpend Hos Hsp Herr Hhv Hcl Hm Hcnt.
  assert (Hnb: 0 < a_nb a) by (destruct Hsp as (Hid & _); lia).
  destruct (sx1_model a t cnt rep2 Hnb Hos Hhv Hcl Hm Hcnt) as (seqs & out' & lits' & Hmh & Hlen).
  destruct (Z_lt_le_dec (sp_cap a) (Zlength cnt)) as [Hlt|Hle]; [exact Hlt|exfalso].
  destruct (sx1_mstep a t w ll ml ov seqs out' lits' rep2 Hsa Hpend Hsp Hmh)
    as (blk & mb & _ & _ & _ & _ & Hfit).
  destruct (Hfit ltac:(lia)) as (_ & Hfar & _ & Hend & Hoff & _).
  unfold exec_split_err in Herr. rewrite !orb_true_iff, andb_true_iff, !Z.ltb_lt in Herr.
  unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

Lemma sx1_fsub (lst: list val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= Zlength lst ->
  (Forall is_byte_val (sublist lo hi lst) <-> forall q, lo <= q < hi -> is_byte_val (Znth q lst)).
Proof.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - lo) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - lo + lo) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma sx1_zbytes (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

Ltac sx1_zmin :=
  repeat match goal with
  | |- context [Z.min ?a ?b] =>
      let Hz := fresh "Hz" in destruct (Z.min_spec a b) as [[Hz ->]|[Hz ->]]
  | H0: context [Z.min ?a ?b] |- _ =>
      let Hz := fresh "Hz" in let Hm := fresh "Hm" in
      destruct (Z.min_spec a b) as [[Hz Hm]|[Hz Hm]]; rewrite Hm in H0; clear Hm
  end.

(* what the executors read stays defined, and the bytes the call wrote are defined (exec_split_spec) *)
Lemma sx1_def (a: sa) (K j r: Z) (c c': list val) :
  sa_ok a -> sp_outok a true K j c -> 0 <= r -> K + r <= sp_cap a -> Zlength c' = Zlength c ->
  xd_ub c c' -> Forall is_byte_val (sublist (sp_d a + K) (sp_d a + K + r) c') -> sp_dfd a (K + r) c'.
Proof.
  intros Hsa (HK & HcN & _ & Hdef & _) Hr HKr Hc' Hu Hnew.
  apply (sp_dfd_step a K r c c'); auto; try lia.
  destruct Hsa as ((_ & _ & _ & Hd & _ & Hdc) & _). unfold sp_N, sp_d, sp_cap in *. lia.
Qed.

(* the written region grows (sp_outok's unchanged_outside) *)
Lemma sx1_unch (c0 c c': list val) (d cap K j lb r ll: Z) :
  0 <= K -> 0 <= r -> 0 <= ll -> 0 <= d -> Zlength c = Zlength c0 ->
  unchanged_outside c0 c d (Z.min (d + Z.min cap (K + WILDCOPY_OVERLENGTH)) (Z.max (d + K) (lb + j))) ->
  unchanged_outside c c' (d + K)
    (Z.min (Z.min (d + cap) (d + K + r + WILDCOPY_OVERLENGTH)) (Z.max (d + K + r) (lb + j + ll))) ->
  unchanged_outside c0 c' d (Z.min (d + Z.min cap (K + r + WILDCOPY_OVERLENGTH)) (Z.max (d + (K + r)) (lb + (j + ll)))).
Proof.
  intros HK Hr Hll Hd Hc Hun Hun' q Hq Hnq. unfold WILDCOPY_OVERLENGTH in *.
  rewrite (Hun' q) by (try lia; intros ?; apply Hnq; sx1_zmin; lia).
  apply Hun; [exact Hq|]. intros ?. apply Hnq. sx1_zmin; lia.
Qed.

Lemma sx1_len (l: list Z) (j ll: Z) :
  0 <= j -> 0 <= ll -> ll <= Zlength l - j -> Zlength (firstn (Z.to_nat ll) (skipn (Z.to_nat j) l)) = ll.
Proof. intros. rewrite Zlength_firstn, Zlength_skipn. lia. Qed.

(* the loop invariant after a successful call *)
Lemma sx1_inv (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (c': list val) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> ll <= sp_lim a - (a_lb a + w_j w) ->
  Zlength c' = Zlength (w_c w) ->
  (byte_cells (w_c w) -> ext_bytes (sp_x a) -> byte_cells c') ->
  exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml (fst (c_offset (w_crep w) ll ov))
    (sp_ps a) (ext_len (sp_x a)) = false ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w)
    (Z.min (Z.min (sp_d a + sp_cap a) (sp_d a + w_K w + (ll + ml) + WILDCOPY_OVERLENGTH))
       (Z.max (sp_d a + w_K w + (ll + ml)) (a_lb a + w_j w + ll))) ->
  (ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) ->
     (lit_exact_split (sp_d a + w_K w) (a_lb a + w_j w) ll ->
        sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c' =
        sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml))
          (exec_c (w_c w) (sp_d a + w_K w) (sublist (a_lb a + w_j w) (a_lb a + w_j w + ll) (w_c w)) ml
             (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (sp_x a))) /\
     (Forall is_byte_val (sublist (sp_ps a) (sp_d a + w_K w) (w_c w)) ->
      Forall is_byte_val (sublist (a_lb a + w_j w) (a_lb a + w_j w + ll) (w_c w)) ->
      ext_def (sp_x a) (w_c w) ->
      Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c'))) ->
  xd_ub (w_c w) c' -> Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c') ->
  sinv a t true {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                   w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                   w_c := c' |}.
Proof.
  intros Hsa Hpend Hsp Hbrk Hc' Hbc Herr Hun' Hok Hxu Hxf.
  destruct (sx1_pre a t w ll ml ov Hsa Hpend Hsp Hbrk)
    as (HcN & Hcap & _ & Hc32 & Hps & HkE & Hll24 & Hml24 & Hoff1 & Hli0 & Hlim32 & _ & _).
  assert (Hd0: 0 <= sp_d a) by (destruct Hsa as ((_ & _ & _ & Hd & _) & _); exact Hd).
  unfold exec_split_err in Herr. rewrite !orb_false_iff in Herr. destruct Herr as ((Hcap' & Hov) & Hoff).
  apply Z.ltb_ge in Hcap', Hoff.
  assert (Hov': ~ (a_lb a + w_j w < sp_d a + w_K w /\ sp_d a + w_K w < a_lb a + w_j w + ll)).
  { intros (H1 & H2). apply Z.ltb_lt in H1, H2. rewrite H1, H2 in Hov. discriminate. }
  clear Hov.
  assert (Hsp' := Hsp).
  destruct Hsp' as (Hid & _ & Hlo & Hbc0 & Hst & Hrep & Hll & Hml & Hovr & Hok0 & Hm).
  assert (Hok0' := Hok0). destruct Hok0' as (HK & _ & (Hj & Hun) & _ & Hbyt).
  assert (Hel: 0 <= ext_len (sp_x a) <= 2 ^ 63 - 1).
  { destruct Hsa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _). apply (Hlay Hcap). }
  unfold sinv, sp_outok, sp_minv. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  split; [lia|]. split; [discriminate|]. split; [exact Hlo|].
  split; [replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia; exact Hbc0|].
  split; [exact Hst|].
  split; [apply sp_rep_step; [exact Hrep | exact Hovr | unfold SIZE_MAX; lia]|].
  split.
  { split; [lia|]. split; [lia|]. split.
    - split; [unfold sp_lim in Hbrk; lia|].
      assert (Hc0l: Zlength (w_c w) = Zlength (sp_c0 a))
        by (destruct Hsa as ((_ & Hoc & _) & _); unfold sp_c0, sp_N in *; lia).
      apply (sx1_unch (sp_c0 a) (w_c w) c' (sp_d a) (sp_cap a) (w_K w) (w_j w) (a_lb a) (ll + ml) ll);
        [lia | lia | lia | lia | exact Hc0l | exact Hun | exact Hun'].
    - split.
      + apply (sx1_def a (w_K w) (w_j w) (ll + ml) (w_c w) c'); auto; lia.
      + intros B1 B2 B3. apply Hbc; [apply Hbyt; assumption | exact B3]. }
  intros seqs out' lits' rep2 Hmh.
  destruct (Hm seqs out' lits' rep2 Hmh) as (sq & Hsq & Hsll & Hsml & Hsov & Hdec & Hrdy & Hlo0 & _).
  destruct (sx1_mstep a t w ll ml ov seqs out' lits' rep2 Hsa Hpend Hsp Hmh)
    as (blk & mb & Hblen & Hmb & Hlrl & Hexr & Hfit).
  split.
  { destruct t as [[tLL tOF] tML]. destruct (w_st w) as [[sLL sOF] sML].
    replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia. exact Hdec. }
  split; [exact Hrdy|]. split; [exact Hlo0|].
  set (L := firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a))) in *.
  assert (HL: Zlength L = ll).
  { unfold L. apply sx1_len; unfold sp_n in Hlrl; lia. }
  exists (blk ++ L ++ mb). split; [rewrite !Zlength_app; lia|]. split; [exact Hexr|].
  intros Hcf. destruct (Hfit Hcf) as (Hblk & Hfar & HKb & Hend & Hoffm & Hro & Hexc).
  rewrite (sublist_split (sp_d a) (sp_d a + w_K w) (sp_d a + (w_K w + (ll + ml)))) by lia.
  rewrite !map_app. f_equal.
  - rewrite <- Hblk. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
    intros q Hq. rewrite Zlength_sublist in Hq by lia.
    rewrite !Znth_sublist by lia.
    apply Hun'; lia.
  - replace (sp_d a + (w_K w + (ll + ml))) with (sp_d a + w_K w + (ll + ml)) by lia.
    destruct (Hok Hro) as (Hx & _).
    rewrite Hx by (right; right; exact Hfar).
    rewrite (sx1_lits a (w_K w) (w_j w) ll (w_c w) Hsa Hok0) by (unfold WILDCOPY_OVERLENGTH in *; lia).
    fold L. rewrite <- map_app, <- Hexc. f_equal. lia.
Qed.

(* the error return: the seqState_t local back to data_at_ (as BlkSeqLoopLongMainX2.x2_ss) *)
Lemma sx1_ss_split (v: val) :
  data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma sx1_ss (gv0: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv0 s start pos lo st tp r v |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite (sx1_ss_split v). unfold seqstate_at, BIT_DStream_rep.
  destruct st as [[x1 x2] x3]; destruct tp as [[y1 y2] y3]. Intros ptr lim.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at.
  repeat (sep_apply data_at_data_at_). cancel.
Qed.

(* the error return: the literal fields to lit_scratch *)
Lemma sx1_lit_release (a: sa) (xr: list val) (v1 v2: val) :
  sa_x a xr ->
  sp_FR0 a * field_at Ews t_dctx (DOT _litBufferLocation) v1 (a_p a) *
  field_at Ews t_dctx (DOT _litBufferEnd) v2 (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ xr) (lit_extra (a_p a)) |--
  pws_pred (a_W a) * frame_fields (a_p a) (a_fs a) * lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros Hx. unfold sp_FR0.
  sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
               v2 v1 Hx).
  cancel.
Qed.

(* op += oneSeqSize *)
Lemma sx1_add (b: val) (x n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val x b) (Vlong (Int64.repr n))) =
  offset_val (x + n) b.
Proof.
  intros Hb Hn. destruct b; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

(* litExtraBuffer holds bytes *)
Lemma sx1_xbytes (a: sa) (g: sg) (Q Rin: mpred) :
  sa_ok a -> bfacts a g Q Rin -> byte_cells (zbytes (sp_tail a) ++ g_xr g).
Proof.
  intros Hsa Hb. destruct Hb as (_ & _ & _ & _ & _ & _ & _ & _ & Hxr).
  destruct Hsa as (_ & _ & (Hlb & _) & _).
  apply Forall_app. split; [|exact Hxr].
  apply sx1_zbytes. unfold sp_tail, bytes_ok in *. apply Forall_sublist. exact Hlb.
Qed.

(* the error return's PROP (sp_post with r, c', rep' = a_rep a) *)
Lemma sx1_errpost (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (ll ml ov r: Z) (c': list val) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> spend a (g_t g) true w ll ml ov ->
  0 <= r <= Int64.max_unsigned -> Zlength c' = Zlength (w_c w) ->
  (byte_cells (w_c w) -> ext_bytes (sp_x a) -> byte_cells c') ->
  is_error_code r = true ->
  true = exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml (fst (c_offset (w_crep w) ll ov))
    (sp_ps a) (ext_len (sp_x a)) ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w) (sp_d a + sp_cap a) -> dec_err r ->
  0 <= r <= Int64.max_unsigned /\
  Zlength c' = oa_N (a_o a) /\
  rep_ok (a_rep a) /\
  unchanged_outside (oa_c (a_o a)) c' (oa_d (a_o a)) (oa_d (a_o a) + oa_cap (a_o a)) /\
  (is_error_code r = false ->
   r <= oa_cap (a_o a) /\
   unchanged_outside (oa_c (a_o a)) c' (oa_d (a_o a))
     (oa_d (a_o a) + Z.min (oa_cap (a_o a)) (r + WILDCOPY_OVERLENGTH)) /\
   (hist_def (oa_c (a_o a)) (oa_d (a_o a)) (hc_ps (a_h a)) (hc_ext (a_h a)) ->
    ext_clean (oa_d (a_o a)) (oa_cap (a_o a)) (hc_ext (a_h a)) \/
    r <= a_bsm a /\ ext_far (oa_d (a_o a)) (oa_cap (a_o a)) (a_bsm a) (hc_ext (a_h a)) ->
    exists cnt : list Z, sublist (oa_d (a_o a)) (oa_d (a_o a) + r) c' = zbytes cnt /\ bytes_ok cnt)) /\
  (oa_cap (a_o a) = 0 \/
   hist_view (oa_c (a_o a)) (oa_d (a_o a)) (hc_ps (a_h a)) (hc_ext (a_h a)) (hc_hist (a_h a)) (hc_out (a_h a))
     (hc_wsize (a_h a)) /\
   ext_clear (oa_d (a_o a)) (hc_ps (a_h a)) (oa_cap (a_o a)) (a_bsm a) (hc_ext (a_h a)) (hc_hist (a_h a))
     (hc_out (a_h a)) (hc_wsize (a_h a)) ->
   match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a)) (a_lits a)
           (hc_wsize (a_h a)) with
   | Some (cnt, rep2) =>
       Zlength cnt <= a_bsm a ->
       is_error_code r = false /\ r = Zlength cnt /\
       sublist (oa_d (a_o a)) (oa_d (a_o a) + r) c' = zbytes cnt /\ a_rep a = rep2 \/
       is_error_code r = true /\ oa_cap (a_o a) < Zlength cnt
   | None => True
   end) /\
  (is_error_code r = true -> dec_err r) /\
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext (a_h a)) -> byte_cells c').
Proof.
  intros Hsa Hpend Hb Hsp Hr Hlen Hbc Er Hee Hun Hde.
  assert (Hsp' := Hsp). destruct Hsp' as (Hid & _ & _ & _ & _ & _ & _ & _ & _ & (HK & HcN & (Hj & Hun0) & _ & Hbyt) & _).
  assert (Hcap: 0 < sp_cap a) by (destruct Hsa as (_ & _ & _ & _ & _ & _ & Hnc & _); apply Hnc; lia).
  assert (Hrep0: rep_ok (a_rep a)) by apply Hsa.
  assert (Hoc: Zlength (oa_c (a_o a)) = oa_N (a_o a)) by (destruct Hsa as ((_ & Hoc & _) & _); exact Hoc).
  split; [exact Hr|]. split; [unfold sp_N in HcN; lia|]. split; [exact Hrep0|].
  split.
  { intros q Hq Hnq. rewrite (Hun q) by (unfold sp_c0, sp_N, sp_d, sp_cap in *; try lia; intros ?; apply Hnq; lia).
    apply Hun0; [exact Hq|]. intros ?. apply Hnq. unfold sp_d, sp_cap in *. sx1_zmin; lia. }
  split; [rewrite Er; discriminate|].
  split.
  { intros Hv. destruct Hv as [Hc0|(Hhv & Hcl)]; [unfold sp_cap in Hcap; lia|].
    destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hm; [|exact I].
    intros Hcnt. right. split; [exact Er|].
    destruct Hb as (Hos & _).
    exact (sx1_err a (g_t g) w ll ml ov cnt rep2 Hsa Hpend Hos Hsp (eq_sym Hee) Hhv Hcl Hm Hcnt). }
  split; [intros _; exact Hde|].
  intros B1 B2 B3. apply Hbc; [apply Hbyt; assumption | exact B3].
Qed.

Lemma seg_x1 {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) ->
  semax sp_Delta (sp_PEND a g Q Rin true w ll ml ov) sp_x1 (sp_x1_R a g Q Rin).
Proof.
  intros Hsa Hpend Hb Hxa. unfold sp_PEND, sp_S, sp_L, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc. simpl app. Intros.
  rename H into Hsp, H0 into Hxp.
  assert_PROP (isptr (sp_ob a)) as Hob by entailer!.
  assert (Hj: 0 <= w_j w <= sp_n a - LITBUFFEREXTRASIZE)
    by (destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & (Hj & _) & _) & _); exact Hj).
  assert (Hn: sp_n a <= ZSTD_BLOCKSIZE_MAX) by (destruct Hsa as (_ & _ & _ & Hbsm & Hn & _); lia).
  assert (Hll: 0 <= ll <= LL_VMAX) by (destruct Hsp as (_ & _ & _ & _ & _ & _ & Hll & _); exact Hll).
  unfold sp_Delta, sp_x1; simplify_func_tycontext.
  forward. forward. forward. cbv [seqrep].
  forward_if.
  { entailer!. destruct (sp_ob a); try contradiction. simpl. destruct (peq b b); [reflexivity | congruence]. }
  - rewrite sx1_cmp in H by (auto; unfold sp_lim, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX, LL_VMAX in *; rep_lia).
    destruct (sp_lim a - (a_lb a + w_j w) <? ll) eqn:Ebrk; [|discriminate].
    forward. Exists w ll ml ov. unfold sp_PEND, sp_S, sp_L, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc. simpl app.
    entailer!.
  - rewrite sx1_cmp in H by (auto; unfold sp_lim, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX, LL_VMAX in *; rep_lia).
    destruct (sp_lim a - (a_lb a + w_j w) <? ll) eqn:Ebrk; [discriminate|]. apply Z.ltb_ge in Ebrk.
    forward. forward.
    pose proof (sx1_pre a (g_t g) w ll ml ov Hsa Hpend Hsp Ebrk) as Hpre.
    assert (HcN: Zlength (w_c w) = sp_N a) by apply Hpre.
    assert (Xok: sp_outok a true (w_K w) (w_j w) (w_c w))
      by (destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _); exact Hok).
    destruct (sp_dfd_exec a (w_K w) (w_j w) (w_c w) Hsa HcN ltac:(destruct Xok as (? & _); lia) Hj
                (proj1 (proj2 (proj2 (proj2 Xok))))) as (Xdh & Xde & Xdl).
    rewrite <- HcN.
    forward_call (a_gv a, oa_sh (a_o a), sp_ob a, w_c w, sp_d a + w_K w, sp_d a + sp_cap a, Tsh, a_vsq a, ll, ml,
                  fst (c_offset (w_crep w) ll ov), Tsh, a_vlp a, a_lb a + w_j w, sp_lim a, sp_ps a, sp_x a,
                  fs_dictEnd (a_fs a)).
    { entailer!. destruct (sp_ob a); try contradiction. simpl. rewrite sx1_sub32. reflexivity. }
    { destruct Hpre as (_ & _ & Hw & _ & _ & _ & _ & _ & _ & _ & _ & Hx & Hd & Hxo). auto. }
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *. Intros.
    rename H0 into Hr, H1 into Hlen, H2 into Hbyt, H3 into Hee, H4 into Herrc, H5 into Hsucc.
    rename H6 into Hxu, H7 into Hxf, H8 into Hxc.
    forward.
    forward_call r.
    destruct (is_error_code r) eqn:Er.
    + forward_if (PROP (False) LOCAL () SEP ()).
      * destruct (Herrc eq_refl) as [Hun Hde].
        unfold POSTCONDITION, abbreviate. apply semax_post with (R' := sp_R a).
        1-3: unfold sp_R, frame_ret_assert, function_body_ret_assert; simpl RA_normal; simpl RA_break;
             simpl RA_continue; unfold bind_ret; apply andp_left2; intro rho; simpl; normalize; try contradiction.
        1: intros vl; apply andp_left2; apply derives_refl.
        unfold sp_R, sp_post. forward.
        pose proof (sx1_errpost a g Q Rin w ll ml ov r c' Hsa Hpend Hb Hsp Hr Hlen Hbyt Er Hee Hun Hde) as HP.
        assert (Hxpost: xpost a r c' (a_rep a)).
        { apply xpost_err; [exact Er|].
          exact (xx1_err a (g_t g) _ w ll ml ov Hsa Hpend Hsp Hxp Ebrk (eq_sym Hee)). }
        Exists r c' (a_rep a).
        sep_apply (sp_release a g Q Rin Hb).
        sep_apply (sx1_lit_release a (g_xr g) (Vint (Int.repr LOC_SPLIT)) (offset_val (sp_lim a) (sp_ob a)) Hxa).
        sep_apply sx1_ss.
        sep_apply (data_at_data_at_ Tsh t_seq (seqrep ll ml (fst (c_offset (w_crep w) ll ov))) (a_vsq a)).
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) lp (a_vlp a)).
        replace (a_nb a =? 0) with false
          by (symmetry; apply Z.eqb_neq; destruct Hsp as (Hid & _); lia).
        rewrite HcN. unfold sp_ob, sp_N, sp_x in *.
        apply andp_right; [apply prop_right; repeat (split; [tauto|]); reflexivity |].
        unfold t_seq, t_seqstate. cancel.
      * exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
          rewrite Int.unsigned_zero in Hx; lia end.
    + destruct (Hsucc eq_refl) as (Hrr & Hlp & Hun & Hbytes). clear Hsucc Herrc. subst r lp.
      forward_if. { exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
      unfold MORE_COMMANDS, abbreviate. apply dec_skipbreak_seq. forward.
      pose proof (sx1_inv a (g_t g) w ll ml ov c' Hsa Hpend Hsp Ebrk Hlen Hbyt (eq_sym Hee) Hun Hbytes Hxu (Hxf eq_refl))
        as Hinv.
      pose proof (xx1 a (g_t g) (zbytes (sp_tail a) ++ g_xr g) w ll ml ov (ll + ml) c' Hsa Hpend Hsp Hxp Ebrk Hlen
                    (eq_sym Hee) Er (sx_exact (sp_x a) false (is_error_code (ll + ml)) _ eq_refl Hxc)) as Hxinv.
      rewrite sx1_add by (auto; lia).
      unfold sp_x1_R; cbn [RA_normal].
      Exists {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                w_c := c' |}.
      unfold sp_INV, sp_S, sp_L, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc. simpl app.
      cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
      rewrite HcN.
      sep_apply (data_at_data_at_ Tsh t_seq (seqrep ll ml (fst (c_offset (w_crep w) ll ov))) (a_vsq a)).
      replace (a_nb a - (w_id w + 1) + 1) with (a_nb a - w_id w) by lia.
      replace (sp_d a + (w_K w + (ll + ml))) with (sp_d a + w_K w + (ll + ml)) by lia.
      replace (a_lb a + (w_j w + ll)) with (a_lb a + w_j w + ll) by lia.
      entailer!.
Qed.

(* the break: copy the head's leftover literals (error when they do not fit), switch to litExtraBuffer,
   ZSTD_execSequence for the rest of the sequence (an error is returned), nbSeq-- *)
Definition sp_left_R (a: sa) (g: sg) (Q Rin: mpred) : ret_assert :=
  {| RA_normal := EX w': sw, sp_INV a g Q Rin false w' (a_nb a - w_id w');
     RA_break := FF; RA_continue := FF;
     RA_return := RA_return (sp_R a) |}.

(* ---------- seg_left helpers (the VST ones adapted from the long loop's BlkSeqLoopLongMainX1) ---------- *)

Lemma sleft_ss_split (v: val) :
  data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma sleft_ss (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv s start pos lo st tp r v |-- data_at_ Tsh t_seqstate v.
Proof.
  unfold seqstate_at. destruct st as [[sLL sOF] sML], tp as [[pLL pOF] pML].
  change t_seqstate with (Tstruct ___gp_seqState_t noattr).
  rewrite sleft_ss_split. unfold BIT_DStream_rep. Intros ptr lim.
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v).
  rewrite !field_at_data_at.
  sep_apply (data_at_data_at_ Tsh t_bitd
    (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (ptr, (start, lim))))
    (field_address t_seqstate (DOT _DStream) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sLL pLL) (field_address t_seqstate (DOT _stateLL) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sOF pOF) (field_address t_seqstate (DOT _stateOffb) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sML pML) (field_address t_seqstate (DOT _stateML) v)).
  cancel.
Qed.

(* (p + A) - (p + B) *)
Lemma sleft_sub (b: val) (A B: Z) :
  isptr b -> 0 <= B <= A -> A <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val A b) (offset_val B b)) =
  Vlong (Int64.repr (A - B)).
Proof.
  intros Hb HAB HA. destruct b; try contradiction.
  simpl. unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr A)) (Ptrofs.add i (Ptrofs.repr B)) = Ptrofs.repr (A - B)).
  { rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted. apply ptrofs_sub_repr. }
  rewrite E. rewrite Ptrofs.divs_one by (compute; congruence).
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* leftoverLit > (size_t)(oend - op) *)
Lemma sleft_gt (b: val) (E k lo: Z) :
  isptr b -> 0 <= k <= E -> E <= Ptrofs.max_unsigned -> 0 <= lo <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1)))
      sem_cast_pointer sem_cast_pointer (Vlong (Int64.repr lo))
      (force_val (sem_sub_pp tuchar (offset_val E b) (offset_val k b))) with
  | Some v' => v' | None => Vundef end = Val.of_bool (E - k <? lo).
Proof.
  intros Hb HkE HE Hlo. destruct b; try contradiction.
  unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  assert (Q: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr E)) (Ptrofs.add i (Ptrofs.repr k)) = Ptrofs.repr (E - k)).
  { rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted. apply ptrofs_sub_repr. }
  rewrite Q. rewrite Ptrofs.divs_one by (compute; congruence).
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (E - k) lo), (E - k <? lo) eqn:W; simpl; auto;
    try (apply Z.ltb_lt in W; lia); try (apply Z.ltb_ge in W; lia).
Qed.

(* op += n *)
Lemma sleft_add (b: val) (a n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a b) (Vlong (Int64.repr n))) =
  offset_val (a + n) b.
Proof.
  intros Hb Hn. destruct b; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma sleft_sub64 (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. intros. unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

(* the literal fields and litExtraBuffer back as scratch *)
Lemma sleft_lit_rel (p: val) (v1 v2 v3 v4 v5: val) (xc: list val) :
  byte_cells xc ->
  field_at Ews t_dctx (DOT _litSize) v1 p * field_at Ews t_dctx (DOT _litPtr) v2 p *
  field_at Ews t_dctx (DOT _litBufferEnd) v3 p * field_at Ews t_dctx (DOT _litBuffer) v4 p *
  field_at Ews t_dctx (DOT _litBufferLocation) v5 p * data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra p)
  |-- lit_scratch p.
Proof.
  intros Hxc. unfold lit_scratch, lit_extra_bytes, lit_extra.
  Exists xc. rewrite (field_at_data_at Ews t_dctx (DOT _litExtraBuffer)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize) v1 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr) v2 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd) v3 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer) v4 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation) v5 p).
  entailer!.
Qed.

(* do { body } while (0) *)
Lemma sleft_do0 {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P: environ -> mpred) (body: statement)
    (R: ret_assert) :
  semax Delta P body (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop body Sbreak) R.
Proof.
  intros H. apply semax_loop with (RA_normal R); [exact H|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

(* litExtraBuffer + 65536 *)
Lemma sleft_extra_end (p: val) :
  isptr p ->
  force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
    (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer p) (Vint (Int.repr 65536))) =
  offset_val 65536 (offset_val 30380 p).
Proof. intros Hp. destruct p; try contradiction. simpl. f_equal. Qed.

Lemma sleft_err70 : dec_err (Int64.unsigned (Int64.repr (-70))).
Proof.
  unfold dec_err. split; [reflexivity|].
  unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; compute; congruence.
Qed.

(* ---------- seg_left: the model ---------- *)

(* what the leftover copy did (lo = 0: nothing): c1 from c *)
Definition sleft_cp (a: sa) (K j: Z) (c c1: list val) : Prop :=
  let lo := sp_lim a - (a_lb a + j) in let di := sp_d a + K in let si := a_lb a + j in
  Zlength c1 = Zlength c /\ K + lo <= sp_cap a /\
  (lo < WILDCOPY_OVERLENGTH \/ si - di <= 16 \/ WILDCOPY_OVERLENGTH <= si - di ->
     sublist di (di + lo) c1 = sublist di (di + lo) (listcopy c si di (Z.to_nat lo))) /\
  (Forall is_byte_val (sublist si (si + lo) c) -> Forall is_byte_val (sublist di (di + lo) c1)) /\
  (forall k, 0 <= k < Zlength c -> ~ (di <= k < di + lo) -> Znth k c1 = Znth k c).

(* a forward copy to an earlier position reads only unwritten cells *)
Lemma sleft_listcopy_fwd (c: list val) (si di: Z) (n: nat) :
  0 <= di <= si -> si + Z.of_nat n <= Zlength c ->
  forall t, 0 <= t < Z.of_nat n -> Znth (di + t) (listcopy c si di n) = Znth (si + t) c.
Proof.
  induction n as [|n IH]; intros Hd Hs t Ht; [lia|].
  rewrite listcopy_snoc. rewrite Nat2Z.inj_succ in Hs, Ht.
  assert (HL: Zlength (listcopy c si di n) = Zlength c) by (apply listcopy_Zlength; lia).
  destruct (Z.eq_dec t (Z.of_nat n)) as [->|Hne].
  - rewrite upd_Znth_same by lia. apply listcopy_outside; lia.
  - rewrite upd_Znth_diff by lia. apply IH; lia.
Qed.

Lemma sleft_sublist_fwd (c: list val) (si di n: Z) :
  0 <= di <= si -> 0 <= n -> si + n <= Zlength c ->
  sublist di (di + n) (listcopy c si di (Z.to_nat n)) = sublist si (si + n) c.
Proof.
  intros Hd Hn Hs.
  assert (HL: Zlength (listcopy c si di (Z.to_nat n)) = Zlength c) by (apply listcopy_Zlength; lia).
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros t Ht. rewrite Zlength_sublist in Ht by lia. rewrite !Znth_sublist by lia.
  rewrite Z.add_comm, (Z.add_comm t si). apply sleft_listcopy_fwd; lia.
Qed.

(* when the content fits: the C bytes before the rest of the pending sequence are the model's, the
   history is untouched *)
Lemma sleft_blk (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (c1: list val)
    (seqs: list sequence) (out' lits': list Z) (rep2: Z * Z * Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov ->
  sleft_cp a (w_K w) (w_j w) (w_c w) c1 ->
  model_hyp a t seqs out' lits' rep2 -> cntlen a out' lits' <= sp_cap a ->
  exists sq blk,
    skipn (Z.to_nat (w_id w)) seqs = sq :: skipn (Z.to_nat (w_id w + 1)) seqs /\
    sq_ll sq = ll /\ sq_ml sq = ml /\ sq_ov sq = ov /\ Zlength blk = w_K w /\
    exec_seqs (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
      (sq :: skipn (Z.to_nat (w_id w + 1)) seqs) = Some (out', lits', rep2) /\
    sublist (sp_d a) (sp_d a + Zlength blk + (sp_lim a - (a_lb a + w_j w))) c1 =
      zbytes (blk ++ firstn (Z.to_nat (sp_lim a - (a_lb a + w_j w))) (skipn (Z.to_nat (w_j w)) (a_lits a))) /\
    unchanged_outside (sp_c0 a) c1 (sp_d a) (sp_d a + Z.min (sp_cap a) (a_bsm a + WILDCOPY_OVERLENGTH)) /\
    sp_d a + w_K w + WILDCOPY_OVERLENGTH <= a_lb a + w_j w /\
    w_K w + (sp_n a - w_j w) <= cntlen a out' lits' /\ cntlen a out' lits' <= a_bsm a.
Proof.
  intros Hsa Hpend Hsp Hcp Hm Hfit.
  destruct w as [id pos blo st crep K j c]; cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in *.
  destruct Hsp as (Hid & _ & _ & _ & _ & _ & Hll & Hml & Hov & Hout & Hmd).
  unfold sp_outok in Hout. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in *.
  destruct (Hmd seqs out' lits' rep2 Hm) as (sq & Hsq & Hsll & Hsml & Hsov & _ & _ & _ & blk & Hblk & Hex & Hbytes).
  specialize (Hbytes Hfit).
  assert (Hm' := Hm). destruct t as [[tLL tOF] tML]. destruct Hm' as (_ & _ & _ & _ & Hcb).
  rewrite Hsq in Hex.
  destruct (sp_exec_len _ _ _ _ _ _ _ _ _ Hex) as (ext & Hext & Hl1 & Hl2).
  assert (Hcnt: cntlen a out' lits' = K + Zlength ext + Zlength lits').
  { unfold cntlen. rewrite Hext, !Zlength_app, Hblk. lia. }
  destruct Hsa as (Ho & Hi & Hl & Hbsm & Hn & Hnb & Hnbp & Hso & Hrep & Hfe & Hc0 & Hlay & Hhp & Hlp & Hx0).
  destruct Hl as (Hlb & Hn0 & Hgt & Hdlb & Hend & Hsub).
  destruct Ho as (Hosh & HoN & HoN32 & Hod & Hocap & HodN).
  destruct Hout as (HK & Hc & (Hj & Hun) & _ & _).
  destruct Hpend as (Hpd & _).
  destruct Hcp as (Hc1 & HKlo & Hexact & _ & Hun1).
  unfold sp_lim, sp_n, sp_d, sp_cap, sp_c0, sp_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  rewrite Zlength_skipn in Hl2.
  assert (Hlen: K + (Zlength (a_lits a) - j) <= cntlen a out' lits').
  { rewrite Hcnt. lia. }
  unfold cntlen in Hcb. fold (cntlen a out' lits') in Hcb.
  assert (Hfar: oa_d (a_o a) + K + 32 <= a_lb a + j).
  { pose proof (Z.le_min_l (a_bsm a) (oa_cap (a_o a))). pose proof (Z.le_min_r (a_bsm a) (oa_cap (a_o a))).
    destruct (Z.min_spec (a_bsm a) (oa_cap (a_o a))) as [[_ E]|[_ E]]; rewrite E in Hpd; lia. }
  set (lo := a_lb a + (Zlength (a_lits a) - 65536) - (a_lb a + j)) in *.
  assert (Hlo: 0 <= lo) by (unfold lo; lia).
  exists sq, blk. do 5 (split; [assumption|]). split; [exact Hex|].
  split; [|split; [|split; [lia | split; lia]]].
  - rewrite (sublist_split (oa_d (a_o a)) (oa_d (a_o a) + Zlength blk) (oa_d (a_o a) + Zlength blk + lo)) by lia.
    rewrite map_app. f_equal.
    + rewrite <- Hbytes, Hblk. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
      intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia. apply Hun1; lia.
    + rewrite Hblk. rewrite Hexact by lia. rewrite sleft_sublist_fwd by lia.
      assert (E1: sublist (a_lb a + j) (a_lb a + j + lo) c = sublist (a_lb a + j) (a_lb a + j + lo) (oa_c (a_o a))).
      { apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
        intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia.
        apply Hun; [lia|]. intros Hq2.
        destruct (Z.max_spec (oa_d (a_o a) + K) (a_lb a + j)) as [[_ E]|[_ E]]; rewrite E in Hq2; lia. }
      rewrite E1.
      replace (a_lb a + j) with (j + a_lb a) by lia. replace (j + a_lb a + lo) with (j + lo + a_lb a) by lia.
      rewrite <- (sublist_sublist (j + lo) (a_lb a + (Zlength (a_lits a) - 65536)) j (a_lb a)) by lia.
      rewrite Hsub. rewrite sublist_map. f_equal. rewrite sublist_sublist by lia.
      unfold sublist. rewrite firstn_skipn_comm. f_equal; [lia | f_equal; lia].
  - intros q Hq Hnq. rewrite Hun1 by lia. apply Hun; [lia|]. intros Hq2. apply Hnq.
    destruct (Z.min_spec (oa_cap (a_o a)) (K + 32)) as [[_ E]|[_ E]]; rewrite E in Hq2;
    destruct (Z.max_spec (oa_d (a_o a) + K) (a_lb a + j)) as [[_ E2]|[_ E2]]; rewrite E2 in Hq2;
    destruct (Z.min_spec (oa_cap (a_o a)) (a_bsm a + 32)) as [[_ E3]|[_ E3]]; rewrite E3;
    try (destruct (Z.min_spec (oa_d (a_o a) + (oa_d (a_o a) + 0 - oa_d (a_o a))) 0); lia);
    repeat match type of Hq2 with context [Z.min ?x ?y] =>
      destruct (Z.min_spec x y) as [[_ E4]|[_ E4]]; rewrite E4 in Hq2 end; lia.
Qed.

(* the content is at least what was written plus the literals left *)
Lemma sleft_len (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z)
    (seqs: list sequence) (out' lits': list Z) (rep2: Z * Z * Z) :
  spend a t true w ll ml ov -> model_hyp a t seqs out' lits' rep2 ->
  w_K w + (sp_n a - w_j w) <= cntlen a out' lits' /\ cntlen a out' lits' <= a_bsm a.
Proof.
  intros Hsp Hm.
  destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hout & Hmd).
  destruct (Hmd seqs out' lits' rep2 Hm) as (sq & Hsq & _ & _ & _ & _ & _ & _ & blk & Hblk & Hex & _).
  assert (Hm' := Hm). destruct t as [[tLL tOF] tML]. destruct Hm' as (_ & _ & _ & _ & Hcb).
  destruct Hout as (_ & _ & (Hj & _) & _).
  rewrite Hsq in Hex.
  destruct (sp_exec_len _ _ _ _ _ _ _ _ _ Hex) as (ext & Hext & Hl1 & Hl2).
  subst out'. unfold cntlen in *. rewrite !Zlength_app, Hblk in *. rewrite Zlength_skipn in Hl2.
  unfold sp_n, LITBUFFEREXTRASIZE in *. split; lia.
Qed.

(* the model's step for the rest of the pending sequence (loop_exec_step with the leftover lo), when the
   content fits *)
Lemma sleft_les (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (c1: list val)
    (seqs: list sequence) (out' lits': list Z) (rep2: Z * Z * Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> sp_lim a - (a_lb a + w_j w) < ll ->
  sleft_cp a (w_K w) (w_j w) (w_c w) c1 ->
  model_hyp a t seqs out' lits' rep2 -> cntlen a out' lits' <= sp_cap a ->
  let lo := sp_lim a - (a_lb a + w_j w) in
  let lr := skipn (Z.to_nat (w_j w)) (a_lits a) in
  let L := firstn (Z.to_nat ll) lr in
  let k := sp_d a + w_K w in
  exists blk off crep' mb,
    Zlength blk = w_K w /\
    c_offset (w_crep w) ll ov = (off, crep') /\ rep_ok crep' /\
    ll <= Zlength lr /\ k + ll + ml <= sp_d a + cntlen a out' lits' /\
    1 <= off <= k + ll - sp_ps a + ext_len (sp_x a) /\ Zlength mb = ml /\
    (forall E, E <= sp_d a + sp_cap a -> ext_read_ok (sp_x a) (k + lo) E (ll - lo) ml off (sp_ps a)) /\
    sublist (k + lo) (k + ll + ml) (exec_c c1 (k + lo) (zbytes (skipn (Z.to_nat lo) L)) ml off (sp_ps a) (sp_x a)) =
      zbytes (skipn (Z.to_nat lo) L ++ mb) /\
    exec_seqs (sp_ws a) crep' (sp_hist a) (skipn (Z.to_nat ll) lr) (sp_out a ++ blk ++ L ++ mb)
      (skipn (Z.to_nat (w_id w + 1)) seqs) = Some (out', lits', rep2) /\
    sublist (sp_d a) (k + lo) c1 = zbytes (blk ++ firstn (Z.to_nat lo) lr).
Proof.
  intros Hsa Hpend Hsp Hbrk Hcp Hm Hfit.
  destruct (sleft_blk a t w ll ml ov c1 seqs out' lits' rep2 Hsa Hpend Hsp Hcp Hm Hfit)
    as (sq & blk & Hsq & Hsll & Hsml & Hsov & Hblk & Hex & Hbytes & Hun & Hfar & Hlen & Hcb).
  assert (Hm' := Hm). destruct t as [[tLL tOF] tML]. destruct Hm' as (Hhv & Hecl & _ & _ & _).
  assert (Hsp' := Hsp). destruct Hsp' as (Hid & _ & _ & _ & _ & Hcrep & Hll & Hml & Hov & Hout & _).
  destruct Hout as (HK & Hc & (Hj & _) & _).
  destruct Hcp as (Hc1 & HKlo & _).
  assert (Hcap: 0 < sp_cap a).
  { destruct Hsa as (_ & _ & _ & _ & _ & _ & Hnbp & _). apply Hnbp. lia. }
  assert (Hsa' := Hsa).
  destruct Hsa' as (Ho & _ & Hl & Hbsm & _ & _ & _ & _ & _ & _ & _ & Hlay & _).
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & HoN & _ & Hod & Hocap & HodN).
  destruct Hl as (Hlb & _).
  cbv zeta.
  destruct (loop_exec_step (sp_c0 a) c1 (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a)
              (sp_ws a) blk (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_lim a - (a_lb a + w_j w)) sq
              (skipn (Z.to_nat (w_id w + 1)) seqs) (w_crep w) out' lits' rep2)
    as (off & crep' & mb & Hco & Hrep' & Hlr & Hend & Hoff & Hmb & Hfit2 & Hexr).
  - unfold sp_d, sp_ps in *; lia.
  - unfold sp_cap in *; lia.
  - rewrite Hc1, Hc. unfold sp_d, sp_cap, sp_N in *; lia.
  - rewrite Hc1, Hc. unfold sp_c0, sp_N. exact HoN.
  - lia.
  - exact Hhv.
  - exact Hecl.
  - rewrite Hc1, Hc. unfold ext_in_bounds. unfold sp_N. destruct (sp_x a); simpl in *; try tauto; lia.
  - lia.
  - exact Hun.
  - unfold bytes_ok in *. apply Forall_skipn. exact Hlb.
  - exact Hcrep.
  - exact Hex.
  - exact Hcb.
  - unfold sp_lim, sp_n, LITBUFFEREXTRASIZE in *. lia.
  - lia.
  - lia.
  - exact Hbytes.
  - rewrite Hsll, Hsml, Hsov, Hblk in *.
    destruct Hfit2 as (Hro & Hexc); [unfold cntlen in *; lia|].
    exists blk, off, crep', mb.
    split; [exact Hblk|]. split; [exact Hco|]. split; [exact Hrep'|]. split; [exact Hlr|].
    split; [exact Hend|]. split; [exact Hoff|]. split; [exact Hmb|].
    split; [exact Hro|]. split; [exact Hexc|]. split; [exact Hexr|].
    exact Hbytes.
Qed.

(* an error after the leftover check: the content does not fit *)
Lemma sleft_err_mdl (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) :
  sa_ok a -> a_os a = Some t -> spend a t true w ll ml ov ->
  (forall seqs out' lits' rep2, model_hyp a t seqs out' lits' rep2 -> sp_cap a < cntlen a out' lits') ->
  oa_cap (a_o a) = 0 \/
  (hist_view (oa_c (a_o a)) (oa_d (a_o a)) (hc_ps (a_h a)) (hc_ext (a_h a)) (hc_hist (a_h a)) (hc_out (a_h a))
     (hc_wsize (a_h a)) /\
   ext_clear (oa_d (a_o a)) (hc_ps (a_h a)) (oa_cap (a_o a)) (a_bsm a) (hc_ext (a_h a)) (hc_hist (a_h a))
     (hc_out (a_h a)) (hc_wsize (a_h a))) ->
  match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a)) (a_lits a)
          (hc_wsize (a_h a)) with
  | Some (cnt, rep2) => Zlength cnt <= a_bsm a -> oa_cap (a_o a) < Zlength cnt
  | None => True
  end.
Proof.
  intros Hsa Hos Hsp Hcnt Hhv0.
  assert (Hid: 0 <= w_id w < a_nb a) by (destruct Hsp as (Hid & _); exact Hid).
  assert (Hcap: 0 < sp_cap a).
  { destruct Hsa as (_ & _ & _ & _ & _ & _ & Hnbp & _). apply Hnbp. lia. }
  unfold sp_cap in Hcap.
  assert (Hhv: hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
               ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a))
    by (destruct Hhv0; [lia | assumption]).
  rewrite Hos. unfold seqs_model. destruct t as [[tLL tOF] tML].
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)) as [seqs|] eqn:Hds; [|exact I].
  destruct (exec_seqs (hc_wsize (a_h a)) (a_rep a) (hc_hist (a_h a)) (a_lits a) (hc_out (a_h a)) seqs)
    as [[[out' lits'] rep2]|] eqn:Hex; [|exact I].
  intros Hcb.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid].
  assert (Hlen: Zlength (skipn (length (hc_out (a_h a))) (out' ++ lits')) = cntlen a out' lits').
  { unfold cntlen, sp_out. rewrite Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl.
    rewrite !Zlength_app. lia. }
  rewrite Hlen in *.
  apply (Hcnt seqs out' lits' rep2).
  unfold model_hyp. split; [apply Hhv|]. split; [apply Hhv|]. split; [exact Hds|]. split; [exact Hex|].
  exact Hcb.
Qed.

Lemma sleft_sub_eq (l: list Z) (j lo ll: Z) :
  0 <= j -> 0 <= lo <= ll ->
  skipn (Z.to_nat lo) (firstn (Z.to_nat ll) (skipn (Z.to_nat j) l)) = sublist (j + lo) (j + ll) l.
Proof.
  intros Hj Hl. unfold sublist. rewrite firstn_skipn_comm, skipn_skipn. f_equal; [lia | f_equal; lia].
Qed.

(* the model after the step *)
Lemma sleft_minv (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (xr c1 c': list val) :
  let lo := sp_lim a - (a_lb a + w_j w) in
  let off := fst (c_offset (w_crep w) ll ov) in
  let k' := sp_d a + w_K w + lo in
  let r := ll - lo + ml in
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> lo < ll ->
  sleft_cp a (w_K w) (w_j w) (w_c w) c1 ->
  Zlength c' = Zlength c1 ->
  unchanged_outside c1 c' k' (Z.min (sp_d a + sp_cap a) (k' + r + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (sp_x a) k' (sp_d a + sp_cap a) (ll - lo) ml off (sp_ps a) ->
     sublist k' (k' + r) c' =
     sublist k' (k' + r) (exec_c c1 k' (sublist 0 (ll - lo) (zbytes (sp_tail a) ++ xr)) ml off (sp_ps a) (sp_x a))) ->
  sp_minv a t {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                 w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + ll + ml; w_j := w_j w + ll; w_c := c' |}.
Proof.
  intros lo off k' r Hsa Hpend Hsp Hbrk Hcp Hc' Hun' Hexb.
  unfold sp_minv. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  intros seqs out' lits' rep2 Hm.
  assert (Hsp' := Hsp).
  destruct Hsp' as (Hid & _ & _ & _ & _ & Hcrep & Hll & Hml & Hov & Hout & Hmd).
  destruct (Hmd seqs out' lits' rep2 Hm)
    as (sq & Hsq & Hsll & Hsml & Hsov & Hdec & Hrdy & Hlo0 & blk & Hblk & Hex & _).
  assert (Hj: 0 <= w_j w <= sp_n a - LITBUFFEREXTRASIZE) by (destruct Hout as (_ & _ & (Hj & _) & _); exact Hj).
  assert (Hlo: 0 <= lo) by (unfold lo, sp_lim; lia).
  split.
  { destruct t as [[tLL tOF] tML]. destruct (w_st w) as [[sLL sOF] sML].
    replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia. exact Hdec. }
  split; [exact Hrdy|]. split; [exact Hlo0|].
  rewrite Hsq in Hex.
  destruct (Z_le_gt_dec (cntlen a out' lits') (sp_cap a)) as [Hfit|Hbig].
  - destruct (sleft_les a t w ll ml ov c1 seqs out' lits' rep2 Hsa Hpend Hsp Hbrk Hcp Hm Hfit)
      as (blk2 & off2 & crep' & mb & Hblk2 & Hco & Hrep' & Hlr & Hend & Hoff & Hmb & Hro & Hexc & Hexr & Hbytes).
    cbv zeta in *. fold lo in Hro, Hexc, Hbytes.
    set (lr := skipn (Z.to_nat (w_j w)) (a_lits a)) in *.
    set (L := firstn (Z.to_nat ll) lr) in *.
    assert (HL: Zlength L = ll) by (unfold L; rewrite Zlength_firstn; lia).
    assert (Hoff2: off = off2) by (unfold off; rewrite Hco; reflexivity).
    rewrite Hco. cbn [snd].
    exists (blk2 ++ L ++ mb). split; [rewrite !Zlength_app; lia|]. split.
    + unfold L, lr in Hexr. rewrite skipn_skipn in Hexr. replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hexr by lia.
      exact Hexr.
    + intros _.
      assert (Hcp' := Hcp). destruct Hcp' as (Hc1 & HKlo & _).
      assert (HN: Zlength (w_c w) = sp_N a) by (destruct Hout as (_ & HN & _); exact HN).
      assert (Hdcap: sp_d a + sp_cap a <= sp_N a).
      { destruct Hsa as ((_ & _ & _ & _ & _ & H) & _). exact H. }
      assert (Hd0: 0 <= sp_d a).
      { destruct Hsa as ((_ & _ & _ & H & _) & _). exact H. }
      assert (HK0: 0 <= w_K w) by (destruct Hout as ((HK0 & _) & _); exact HK0).
      rewrite (sublist_split (sp_d a) k' (sp_d a + (w_K w + ll + ml))) by (unfold k', r in *; lia).
      assert (E1: sublist (sp_d a) k' c' = zbytes (blk2 ++ firstn (Z.to_nat lo) lr)).
      { rewrite <- Hbytes. apply Znth_eq_ext; [rewrite !Zlength_sublist; unfold k'; lia|].
        intros q Hq. rewrite Zlength_sublist in Hq by (unfold k'; lia). rewrite !Znth_sublist by (unfold k'; lia).
        apply Hun'; unfold k'; lia. }
      assert (E2: sublist k' (sp_d a + (w_K w + ll + ml)) c' = zbytes (skipn (Z.to_nat lo) L ++ mb)).
      { rewrite <- Hexc.
        replace (sp_d a + (w_K w + ll + ml)) with (k' + r) by (unfold k', r; lia).
        replace (sp_d a + w_K w + ll + ml) with (k' + r) by (unfold k', r; lia).
        rewrite Hexb by (rewrite Hoff2; apply Hro; lia).
        rewrite Hoff2. f_equal. f_equal.
        assert (Hlrl: Zlength lr = sp_n a - w_j w) by (unfold lr; rewrite Zlength_skipn, ?Z2Nat.id by lia; unfold sp_n, LITBUFFEREXTRASIZE in *; lia).
        assert (Htl: Zlength (sp_tail a) = LITBUFFEREXTRASIZE)
          by (unfold sp_tail; rewrite Zlength_sublist; unfold sp_n, LITBUFFEREXTRASIZE in *; lia).
        assert (Hgt: LITBUFFEREXTRASIZE < sp_n a).
        { destruct Hsa as (_ & _ & (_ & _ & H & _) & _). exact H. }
        rewrite sublist_app1 by (rewrite ?Zlength_map, ?Htl; unfold lo, sp_lim, LITBUFFEREXTRASIZE in *; lia).
        unfold sp_tail. rewrite !sublist_map. f_equal.
        unfold L, lr. rewrite sublist_sublist by (unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE in *; lia).
        rewrite sleft_sub_eq by lia. f_equal; unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE in *; lia. }
      rewrite E1, E2. rewrite <- map_app. f_equal. rewrite <- !app_assoc. f_equal.
      rewrite app_assoc. f_equal.
      unfold L, lr. rewrite <- (firstn_skipn (Z.to_nat lo) (firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)))) at 2.
      rewrite firstn_firstn. rewrite Nat.min_l by lia. reflexivity.
  - destruct (sp_exec_free (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
                sq (skipn (Z.to_nat (w_id w + 1)) seqs) out' lits' rep2)
      as (off2 & crep' & mb & Hco & _ & _ & Hlr & Hmb & Hexr); [exact Hcrep | lia | lia | lia | exact Hex |].
    rewrite Hsll, Hsml, Hsov in *.
    rewrite Hco. cbn [snd].
    exists (blk ++ firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb).
    split; [rewrite !Zlength_app, Zlength_firstn; lia|]. split; [|intros; lia].
    rewrite skipn_skipn in Hexr. replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hexr by lia.
    rewrite <- !app_assoc in Hexr. exact Hexr.
Qed.

Lemma sleft_fb (lst: list val) (x y: Z) :
  0 <= x <= y -> y <= Zlength lst ->
  (Forall is_byte_val (sublist x y lst) <-> forall q, x <= q < y -> is_byte_val (Znth q lst)).
Proof.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - x) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - x + x) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma sleft_zbytes_byte (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

Ltac sleft_zmin :=
  repeat match goal with
  | |- context [Z.min ?a ?b] =>
      let Hz := fresh "Hz" in destruct (Z.min_spec a b) as [[Hz ->]|[Hz ->]]
  | H0: context [Z.min ?a ?b] |- _ =>
      let Hz := fresh "Hz" in let Hm := fresh "Hm" in
      destruct (Z.min_spec a b) as [[Hz Hm]|[Hz Hm]]; rewrite Hm in H0; clear Hm
  | H0: context [Z.max ?a ?b] |- _ =>
      let Hz := fresh "Hz" in let Hm := fresh "Hm" in
      destruct (Z.max_spec a b) as [[Hz Hm]|[Hz Hm]]; rewrite Hm in H0; clear Hm
  end.

(* the leftover copy: the cells it writes are the defined head bytes, the rest unchanged *)
Lemma sleft_cp_ub (a: sa) (K j: Z) (c c1: list val) :
  let lo := sp_lim a - (a_lb a + j) in
  0 <= sp_d a + K -> sp_d a + K + lo <= Zlength c -> sleft_cp a K j c c1 ->
  Forall is_byte_val (sublist (a_lb a + j) (a_lb a + j + lo) c) ->
  xd_ub c c1 /\ Forall is_byte_val (sublist (sp_d a + K) (sp_d a + K + lo) c1).
Proof.
  intros lo H0 Hb (Hc1 & _ & _ & Hcpb & Hun1) Hs.
  specialize (Hcpb Hs). split; [| exact Hcpb].
  apply (xd_ub_frame c c1 (sp_d a + K) (sp_d a + K + lo)); [exact Hun1 |].
  apply xd_Forall_rng; [lia | lia | exact Hcpb].
Qed.

(* the copy keeps bytes bytes *)
Lemma sleft_cp_bytes (a: sa) (K j: Z) (c c1: list val) :
  0 <= sp_d a -> 0 <= K -> a_lb a + j + (sp_lim a - (a_lb a + j)) <= Zlength c ->
  sp_d a + K + (sp_lim a - (a_lb a + j)) <= Zlength c -> 0 <= a_lb a + j <= sp_lim a ->
  sleft_cp a K j c c1 -> byte_cells c -> byte_cells c1.
Proof.
  intros Hd HK Hs Hdi Hj (Hc1 & _ & _ & Hcpb & Hun1) Hb.
  unfold byte_cells in *. fold is_byte_val in *.
  change (Forall is_byte_val c1). change (Forall is_byte_val c) in Hb.
  rewrite <- (sublist_same 0 (Zlength c1) c1) by reflexivity.
  rewrite sleft_fb by lia. intros q Hq.
  set (lo := sp_lim a - (a_lb a + j)) in *.
  destruct (Z_lt_ge_dec q (sp_d a + K)) as [H1|H1]; [rewrite Hun1 by lia; rewrite Forall_forall in Hb; apply Hb, Znth_In; lia|].
  destruct (Z_lt_ge_dec q (sp_d a + K + lo)) as [H2|H2]; [|rewrite Hun1 by lia; rewrite Forall_forall in Hb; apply Hb, Znth_In; lia].
  assert (Hs': Forall is_byte_val (sublist (a_lb a + j) (a_lb a + j + lo) c)) by (apply Forall_sublist; exact Hb).
  specialize (Hcpb Hs'). rewrite sleft_fb in Hcpb by lia. apply Hcpb. lia.
Qed.

(* the loop invariant after the step *)
Lemma sleft_sinv (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (xr c1 c': list val) :
  let lo := sp_lim a - (a_lb a + w_j w) in
  let off := fst (c_offset (w_crep w) ll ov) in
  let k' := sp_d a + w_K w + lo in
  let r := ll - lo + ml in
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> lo < ll ->
  sleft_cp a (w_K w) (w_j w) (w_c w) c1 -> Zlength c' = Zlength c1 -> byte_cells xr ->
  (byte_cells c1 -> byte_cells (zbytes (sp_tail a) ++ xr) -> ext_bytes (sp_x a) -> byte_cells c') ->
  exec_err k' (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml off (sp_ps a) (ext_len (sp_x a)) = false ->
  unchanged_outside c1 c' k' (Z.min (sp_d a + sp_cap a) (k' + r + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (sp_x a) k' (sp_d a + sp_cap a) (ll - lo) ml off (sp_ps a) ->
     sublist k' (k' + r) c' =
       sublist k' (k' + r) (exec_c c1 k' (sublist 0 (ll - lo) (zbytes (sp_tail a) ++ xr)) ml off (sp_ps a) (sp_x a)) /\
     (Forall is_byte_val (sublist (sp_ps a) k' c1) ->
      Forall is_byte_val (sublist 0 (ll - lo) (zbytes (sp_tail a) ++ xr)) ->
      ext_def (sp_x a) c1 -> Forall is_byte_val (sublist k' (k' + r) c'))) ->
  xd_ub (w_c w) c1 -> Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + lo) c1) ->
  xd_ub c1 c' -> Forall is_byte_val (sublist k' (k' + r) c') ->
  sinv a t false {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                    w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + ll + ml; w_j := w_j w + ll;
                    w_c := c' |}.
Proof.
  intros lo off k' r Hsa Hpend Hsp Hbrk Hcp Hc' Hxr Hbc Herr Hun' Hexb Xu1 Xd1 Xu2 Xd2.
  assert (Hmv := sleft_minv a t w ll ml ov xr c1 c' Hsa Hpend Hsp Hbrk Hcp Hc' Hun'
                   (fun H => proj1 (Hexb H))).
  unfold exec_err in Herr. apply orb_false_iff in Herr as [Herr Hoffe]. apply orb_false_iff in Herr as [Hcape Hlite].
  apply Z.ltb_ge in Hcape, Hlite, Hoffe.
  assert (Hsp' := Hsp).
  destruct Hsp' as (Hid & _ & Hlo0 & Hbc0 & Hst & Hcrep & Hll & Hml & Hov & Hout & _).
  assert (Hout' := Hout). destruct Hout' as (HK & Hc & (Hj & Hun) & Hdef & Hbyt).
  assert (Hcp' := Hcp). destruct Hcp' as (Hc1 & HKlo & _ & _ & Hun1).
  assert (Hsa' := Hsa).
  destruct Hsa' as (Ho & _ & Hl & Hbsm & Hn & _ & _ & _ & _ & _ & _ & Hlay & _).
  assert (Hcap: 0 < sp_cap a).
  { destruct Hsa as (_ & _ & _ & _ & _ & _ & Hnbp & _). apply Hnbp. lia. }
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & _).
  destruct Ho as (_ & HoN & HoN32 & Hod & Hocap & HodN).
  destruct Hl as (Hlb & Hn0 & Hgt & Hdlb & Hlend & _).
  assert (Hlo: 0 <= lo) by (unfold lo, sp_lim; lia).
  unfold sinv. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  split; [lia|]. split; [intros; lia|]. split; [exact Hlo0|].
  split; [replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia; exact Hbc0|].
  split; [exact Hst|].
  split.
  { apply sp_rep_step; [exact Hcrep | exact Hov |]. fold off. unfold SIZE_MAX.
    unfold k', lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, sp_ps, LITBUFFEREXTRASIZE in *.
    unfold ZSTD_BLOCKSIZE_MAX in *. lia. }
  split; [|exact Hmv].
  unfold sp_outok.
  split; [unfold k', r in *; lia|].
  split; [lia|].
  split.
  { split; [unfold lo, sp_lim, LITBUFFEREXTRASIZE in *; lia|].
    intros q Hq Hnq.
    unfold k', r, lo, sp_lim, sp_d, sp_cap, sp_c0, sp_N, WILDCOPY_OVERLENGTH in *.
    rewrite Hun' by (sleft_zmin; lia). rewrite Hun1 by (sleft_zmin; lia). apply Hun; [lia|].
    intros Hq2. apply Hnq. sleft_zmin; lia. }
  split.
  { assert (D1: sp_dfd a (w_K w + lo) c1).
    { apply (sp_dfd_step a (w_K w) lo (w_c w) c1); auto; try lia.
      unfold lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
    assert (Hn2: Forall is_byte_val (sublist (sp_d a + (w_K w + lo)) (sp_d a + (w_K w + lo) + r) c'))
      by (replace (sp_d a + (w_K w + lo)) with k' by (unfold k'; lia); exact Xd2).
    replace (w_K w + ll + ml) with (w_K w + lo + r) by (unfold r; lia).
    apply (sp_dfd_step a (w_K w + lo) r c1 c'); auto; try lia.
    unfold k', r, lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
  intros B1 B2 B3. apply Hbc; [| |exact B3].
  - unfold lo in *.
    apply (sleft_cp_bytes a (w_K w) (w_j w) (w_c w) c1);
      [unfold sp_d; lia | lia | | | | exact Hcp | exact (Hbyt B1 B2 B3)];
      unfold sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia.
  - unfold byte_cells in *. apply Forall_app. split; [|exact Hxr].
    fold is_byte_val. apply sleft_zbytes_byte. unfold sp_tail, bytes_ok in *. apply Forall_sublist. exact Hlb.
Qed.

(* the -70 of the leftover check: the content does not fit *)
Lemma sleft_lerr (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) :
  spend a t true w ll ml ov -> sp_cap a - w_K w < sp_lim a - (a_lb a + w_j w) ->
  forall seqs out' lits' rep2, model_hyp a t seqs out' lits' rep2 -> sp_cap a < cntlen a out' lits'.
Proof.
  intros Hsp Hlt seqs out' lits' rep2 Hm.
  destruct (sleft_len a t w ll ml ov seqs out' lits' rep2 Hsp Hm) as [H1 _].
  unfold sp_lim, LITBUFFEREXTRASIZE in *. lia.
Qed.

(* an error of execSequence: the content does not fit *)
Lemma sleft_xerr (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (c1: list val) :
  let lo := sp_lim a - (a_lb a + w_j w) in
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> lo < ll ->
  sleft_cp a (w_K w) (w_j w) (w_c w) c1 ->
  exec_err (sp_d a + w_K w + lo) (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = true ->
  forall seqs out' lits' rep2, model_hyp a t seqs out' lits' rep2 -> sp_cap a < cntlen a out' lits'.
Proof.
  intros lo Hsa Hpend Hsp Hbrk Hcp Herr seqs out' lits' rep2 Hm.
  destruct (Z_le_gt_dec (cntlen a out' lits') (sp_cap a)) as [Hfit|]; [|lia].
  exfalso.
  destruct (sleft_les a t w ll ml ov c1 seqs out' lits' rep2 Hsa Hpend Hsp Hbrk Hcp Hm Hfit)
    as (blk & off & crep' & mb & Hblk & Hco & _ & Hlr & Hend & Hoff & _).
  rewrite Hco in Herr. cbn [fst] in Herr.
  rewrite Zlength_skipn in Hlr.
  unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
  fold lo in Hend, Hoff.
  unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE in *.
  destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & (Hj & _) & _) & _).
  unfold sp_n, LITBUFFEREXTRASIZE in Hj.
  lia.
Qed.

(* the output after an error return changed only in [d, d + cap) *)
Lemma sleft_unch_err (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) (c1 c': list val) (k' e: Z) :
  sa_ok a -> spend a t true w ll ml ov -> sleft_cp a (w_K w) (w_j w) (w_c w) c1 ->
  sp_d a <= k' -> e <= sp_d a + sp_cap a ->
  unchanged_outside c1 c' k' e ->
  unchanged_outside (sp_c0 a) c' (sp_d a) (sp_d a + sp_cap a).
Proof.
  intros Hsa Hsp Hcp Hk He Hun' q Hq Hnq.
  destruct Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HK & Hc & (Hj & Hun) & _) & _).
  destruct Hcp as (Hc1 & HKlo & _ & _ & Hun1).
  destruct Hsa as ((_ & HoN & _ & Hod & Hocap & HodN) & _).
  unfold sp_c0, sp_N, sp_d, sp_cap, sp_lim in *.
  rewrite Hun' by lia. rewrite Hun1 by lia. apply Hun; [lia|].
  intros Hq2. apply Hnq. sleft_zmin; lia.
Qed.

(* an error return: the borrowed resources back, the literal fields scratch, the locals freed *)
Lemma sleft_rel (a: sa) (g: sg) (Q Rin: mpred) (lpv: val) (sq: reptype t_seq) (pos lo: Z) (st rp: Z * Z * Z)
    (v3 v5: val) (xr: list val) :
  bfacts a g Q Rin -> sa_x a xr ->
  data_at Tsh (tptr tuchar) lpv (a_vlp a) *
  seqstate_at Tsh (a_gv a) (sp_s a) (sp_sst a) pos lo st (g_tp g) rp (a_vss a) *
  data_at Tsh t_seq sq (a_vsq a) * data_at_ Tsh t_seq (a_vsq1 a) * zstd_globals (a_gv a) * Q *
  bit_src (g_sh2 g) (sp_sst a) (sp_s a) *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (sp_tail a) ++ xr) (lit_extra (a_p a)) *
  field_at Ews t_dctx (DOT _litBufferLocation) v5 (a_p a) *
  field_at Ews t_dctx (DOT _litBufferEnd) v3 (a_p a) * sp_FRL a g Rin
  |-- zstd_globals (a_gv a) * pws_pred (a_W a) * frame_fields (a_p a) (a_fs a) *
      tabs_seq (a_gv a) (a_p a) (a_ox a) (a_os a) 1 * dent_of dent_def (a_gv a) (a_ox a) *
      lit_scratch_x (a_p a) (a_lxb a) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
      data_at_ Tsh (tptr tuchar) (a_vlp a) * data_at_ Tsh (Tstruct ___gp_seqState_t noattr) (a_vss a) *
      data_at_ Tsh (Tstruct ___gp_seq_t noattr) (a_vsq a) * data_at_ Tsh (Tstruct ___gp_seq_t noattr) (a_vsq1 a).
Proof.
  intros Hb Hxa.
  sep_apply (sp_release a g Q Rin Hb). unfold sp_FR0.
  sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
               v3 v5 Hxa).
  sep_apply (sleft_ss (a_gv a) (sp_s a) (sp_sst a) pos lo st (g_tp g) rp (a_vss a)).
  sep_apply (data_at_data_at_ Tsh (tptr tuchar) lpv (a_vlp a)).
  sep_apply (data_at_data_at_ Tsh t_seq sq (a_vsq a)).
  cancel.
Qed.

(* do { } while (0) with an empty body (as seg_init_dw0) *)
Ltac sleft_dw0 :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

(* do { if (0) ...; } while (0) *)
Ltac sleft_dw0if :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [ apply ENTAIL_refl
    | forward_if P;
      [ exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end
      | forward; try apply ENTAIL_refl
      | forward; try apply ENTAIL_refl ]
    | ]
  end.

(* the array after the leftover copy (COPY's lsdbs; nothing when there is none); a definition, so that VST's
   automatic substitutions keep c1 *)
Definition sleft_c1 (a: sa) (w: sw) (c1: list val) : Prop :=
  let lo := sp_lim a - (a_lb a + w_j w) in
  c1 = (if lo =? 0 then w_c w else lsdbs (w_c w) (sp_d a + w_K w) (a_lb a + w_j w) lo).

Lemma seg_left {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) -> sp_lim a - (a_lb a + w_j w) < ll ->
  semax sp_Delta (sp_PEND a g Q Rin true w ll ml ov) sp_left (sp_left_R a g Q Rin).
Proof.
  intros Hsa Hpend Hb Hxa Hbrk.
  unfold sp_Delta, sp_left, sp_left_R. unfold sp_PEND, sp_L, sp_S, sp_lvars, sp_ptrs; cbn [app]. Intros.
  rename H into Hsp, H0 into Hxpd.
  assert (Hsp' := Hsp).
  destruct Hsp' as (Hid & _ & Hlo0 & Hbc0 & Hst & Hcrep & Hll & Hml & Hov & Hout & _).
  assert (Hout' := Hout). destruct Hout' as (HK & Hc & (Hj & Hun) & _ & Hbyt).
  assert (Hsa' := Hsa).
  destruct Hsa' as (Ho & Hi & Hl & Hbsm & Hn & Hnb & Hnbp & Hso & Hrep & Hfe & Hc0 & Hlay & Hhp & Hlp & Hx0).
  assert (Hcap: 0 < sp_cap a) by (apply Hnbp; lia).
  destruct (Hlay Hcap) as (Hps & Hfps & Hfvs & Hel & Hext).
  destruct Ho as (Hosh & HoN & HoN32 & Hod & Hocap & HodN).
  destruct Hl as (Hlb & Hn0 & Hgt & Hdlb & Hlend & Hsub).
  assert_PROP (isptr (sp_ob a)) as Hob by entailer!.
  unfold sp_lp, sp_lbe.
  forward. forward. forward.
  { entailer!. clear - Hob. destruct (sp_ob a); try contradiction. simpl.
    apply prop_right. destruct (peq b b); [reflexivity | congruence]. }
  rewrite sleft_sub by (auto; unfold sp_lim, sp_n, sp_d, sp_cap, sp_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia).
  set (lo := sp_lim a - (a_lb a + w_j w)) in *.
  assert (Hlo: 0 <= lo) by (unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE in *; lia).
  assert (Hlo2: w_K w + lo <= sp_cap a -> sp_d a + w_K w + lo <= sp_N a) by (unfold sp_d, sp_cap, sp_N in *; lia).
  assert (HlimN: sp_lim a + WILDCOPY_OVERLENGTH <= sp_d a + sp_cap a) by (unfold sp_lim, sp_n, sp_d, sp_cap, LITBUFFEREXTRASIZE in *; lia).
  set (off := fst (c_offset (w_crep w) ll ov)) in *.
  assert (Xdf: sp_dfd a (w_K w) (w_c w)) by (destruct Hout as (_ & _ & _ & Hd & _); exact Hd).
  destruct (sp_dfd_exec a (w_K w) (w_j w) (w_c w) Hsa Hc ltac:(lia) Hj Xdf) as (Xdh & Xde & Xdl).
  assert (Xsrc: Forall is_byte_val (sublist (a_lb a + w_j w) (a_lb a + w_j w + lo) (w_c w))).
  { apply (xd_sub _ (a_lb a + w_j w) (sp_lim a + WILDCOPY_OVERLENGTH)); auto;
      unfold lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
  freeze [1;3;5;6;8;9;10;11;12;13] FR.
  apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ _ (Ssequence ?S1 _) _ => apply semax_seq with
   (EX c1: list val,
    PROP (sleft_cp a (w_K w) (w_j w) (w_c w) c1;
          sleft_c1 a w c1)
    LOCAL (temp _leftoverLit (Vlong (Int64.repr lo));
     lvar _sequence__1 t_seq (a_vsq1 a); lvar _sequence t_seq (a_vsq a);
     lvar _seqState t_seqstate (a_vss a); lvar _litPtr (tptr tuchar) (a_vlp a);
     gvars (a_gv a); temp _dctx (a_p a);
     temp _nbSeq (Vint (Int.repr (a_nb a - w_id w)));
     temp _isLongOffset (Vint (Int.repr 0));
     temp _op (offset_val (sp_d a + w_K w + lo) (sp_ob a));
     temp _litBufferEnd (offset_val (sp_lim a) (sp_ob a));
     temp _ostart (offset_val (sp_d a) (sp_ob a));
     temp _oend (offset_val (sp_d a + sp_cap a) (sp_ob a));
     temp _prefixStart (offset_val (sp_ps a) (sp_ob a));
     temp _vBase (offset_val (sp_ps a - ext_len (sp_x a)) (sp_ob a));
     temp _dictEnd (dict_end (sp_x a) (sp_ob a) (fs_dictEnd (a_fs a))))
    SEP (FRZL FR; data_at Tsh (tptr tuchar) (offset_val (a_lb a + w_j w) (sp_ob a)) (a_vlp a);
     data_at Tsh t_seq (seqrep (ll - lo) ml off) (a_vsq a); zstd_globals (a_gv a);
     data_at (oa_sh (a_o a)) (tarray tuchar (sp_N a)) c1 (sp_ob a)))%assert end.
  { forward_if.
    - (* leftover literals *)
      assert (Hlp0: 0 < lo).
      { destruct (Z.eq_dec lo 0) as [Hz|]; [|lia]. exfalso.
        match goal with H: Int64.repr lo <> Int64.zero |- _ => rewrite Hz in H; apply H; reflexivity end. }
      assert (HlimN': sp_lim a <= sp_N a) by (unfold sp_d, sp_cap, sp_N, WILDCOPY_OVERLENGTH in *; lia).
      destruct (Z_lt_ge_dec (sp_cap a - w_K w) lo) as [Herr|Hok].
      + eapply semax_seq; [| apply semax_ff].
        apply sleft_do0. forward_if.
        { apply prop_right. clear - Hob. destruct (sp_ob a); try contradiction.
          simpl. destruct (peq b b); [reflexivity | congruence]. }
        { sleft_dw0. sleft_dw0if. sleft_dw0. sleft_dw0.
          apply semax_post with (R' := sp_R a).
          1-3: unfold sp_R, frame_ret_assert, function_body_ret_assert; simpl RA_normal; simpl RA_break;
               simpl RA_continue; unfold bind_ret; apply andp_left2; intro rho; simpl; normalize; try contradiction.
          1: intros vl; apply andp_left2; apply derives_refl.
          repeat match goal with H := @abbreviate ret_assert _ |- _ => clear H end.
          thaw FR.
          unfold sp_R, sp_post. forward.
          assert (Hb' := Hb). destruct Hb' as (Hos & _ & _ & _ & _ & _ & _ & Hxrl & Hxrb).
          assert (Hxc: byte_cells (zbytes (sp_tail a) ++ g_xr g)).
          { apply Forall_app. split; [|exact Hxrb]. apply sleft_zbytes_byte.
            unfold sp_tail, bytes_ok in *. apply Forall_sublist. exact Hlb. }
          assert (Hune: unchanged_outside (sp_c0 a) (w_c w) (sp_d a) (sp_d a + sp_cap a)).
          { intros q Hq Hnq. apply Hun; [exact Hq|]. intros Hq2. apply Hnq. sleft_zmin; lia. }
          assert (Hmdl := sleft_err_mdl a (g_t g) w ll ml ov Hsa Hos Hsp (sleft_lerr a (g_t g) w ll ml ov Hsp Herr)).
          assert (Hxpost: xpost a (Int64.unsigned (Int64.repr (-70))) (w_c w) (a_rep a)).
          { apply xpost_err; [reflexivity|]. exact (xleft_lerr a (g_t g) _ w ll ml ov Hsa Hpend Hsp Hxpd Hbrk Hlp0 Herr). }
          Exists (Int64.unsigned (Int64.repr (-70))) (w_c w) (a_rep a).
          rewrite Int64.repr_unsigned.
          sep_apply (sleft_rel a g Q Rin (offset_val (a_lb a + w_j w) (sp_ob a)) (seqrep ll ml off) (w_pos w) (w_lo w)
                       (w_st w) (snd (c_offset (w_crep w) ll ov)) (offset_val (sp_lim a) (sp_ob a))
                       (Vint (Int.repr (sp_loc true))) (g_xr g) Hb Hxa).
          replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          change (sp_ob a) with (oa_base (a_o a)). change (sp_x a) with (hc_ext (a_h a)).
          change (sp_N a) with (oa_N (a_o a)).
          assert (He70: is_error_code (Int64.unsigned (Int64.repr (-70))) = true) by reflexivity.
          entailer!.
          repeat match goal with
           | |- _ /\ _ => split
           | |- is_error_code _ = false -> _ => let Hf := fresh in intros Hf; rewrite He70 in Hf; discriminate Hf
           | |- is_error_code _ = true -> dec_err _ => intros _; exact sleft_err70
           end.
          all: try first [apply Int64.unsigned_range_2 | unfold sp_N in *; lia | exact Hrep | exact Hune | exact Hbyt |
                          exact Hxpost].
          all: try (let Hv := fresh "Hv" in intros Hv).
          all: match goal with Hv: _ = 0 \/ _ |- _ => specialize (Hmdl Hv) end.
          all: destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; [|exact I].
          all: intros Hcb; right; split; [exact He70 | apply Hmdl; exact Hcb]. }
        { exfalso. match goal with H: typed_false tint _ |- _ =>
            rewrite sleft_gt in H by (auto; unfold sp_d, sp_cap, sp_N in *; rep_lia);
            replace (sp_d a + sp_cap a - (sp_d a + w_K w) <? lo) with true in H by (symmetry; apply Z.ltb_lt; lia);
            discriminate H end. }
      + match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
        { apply sleft_do0. forward_if.
          { apply prop_right. clear - Hob. destruct (sp_ob a); try contradiction.
            simpl. destruct (peq b b); [reflexivity | congruence]. }
          { exfalso. match goal with H: typed_true tint _ |- _ =>
              rewrite sleft_gt in H by (auto; unfold sp_d, sp_cap, sp_N in *; rep_lia);
              replace (sp_d a + sp_cap a - (sp_d a + w_K w) <? lo) with false in H by (symmetry; apply Z.ltb_ge; lia);
              discriminate H end. }
          { forward. entailer!. } }
        abbreviate_semax. forward.
        replace (sp_N a) with (Zlength (w_c w)) by lia.
        assert_PROP (field_compatible (tarray tuchar (Zlength (w_c w))) [] (sp_ob a)) as Hfc by entailer!.
        assert (Hfa1: field_address0 (tarray tuchar (Zlength (w_c w))) (SUB (sp_d a + w_K w)) (sp_ob a) =
                      offset_val (sp_d a + w_K w) (sp_ob a)).
        { rewrite arr_field_address0 by (auto; unfold sp_d, sp_cap, sp_N in *; lia).
          change (sizeof tuchar) with 1. f_equal; lia. }
        assert (Hfa2: field_address0 (tarray tuchar (Zlength (w_c w))) (SUB (a_lb a + w_j w)) (sp_ob a) =
                      offset_val (a_lb a + w_j w) (sp_ob a)).
        { rewrite arr_field_address0 by (auto; unfold lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
          change (sizeof tuchar) with 1. f_equal; lia. }
        forward_call (a_gv a, oa_sh (a_o a), sp_ob a, w_c w, a_lb a + w_j w, sp_d a + w_K w, lo).
        { unfold lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. rep_lia. }
        Intros c1.
        assert (Hcp1: sleft_cp a (w_K w) (w_j w) (w_c w) c1).
        { unfold sleft_cp. fold lo. unfold WILDCOPY_VECLEN in *.
          split; [assumption|]. split; [lia|]. split; [assumption|]. split; assumption. }
        forward. forward. forward.
        rewrite sleft_add by (auto; unfold sp_lim, sp_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
        rewrite sleft_sub64 by (unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE, LL_VMAX, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
        change (Vlong (Int64.repr (ll - lo)), snd (seqrep ll ml off)) with (seqrep (ll - lo) ml off).
        assert (Hc1x: sleft_c1 a w c1)
          by (unfold sleft_c1; cbv zeta; fold lo; rewrite (proj2 (Z.eqb_neq lo 0)) by lia; assumption).
        Exists c1. replace (sp_N a) with (Zlength (w_c w)) by lia. entailer!.
    - (* none *)
      assert (Hz: lo = 0).
      { match goal with H: Int64.repr lo = Int64.zero |- _ =>
          apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by
            (unfold lo, sp_lim, sp_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia); exact H end. }
      assert (Hcp0: sleft_cp a (w_K w) (w_j w) (w_c w) (w_c w)).
      { unfold sleft_cp. fold lo. rewrite Hz, !Z.add_0_r. split; [reflexivity|]. split; [lia|].
        split; [intros _; reflexivity|]. split; [intros _; rewrite sublist_nil; constructor|]. intros; reflexivity. }
      assert (Hc1z: sleft_c1 a w (w_c w)).
      { unfold sleft_c1; cbv zeta; fold lo. rewrite Hz. reflexivity. }
      forward. Exists (w_c w). rewrite Hz, !Z.add_0_r, Z.sub_0_r. entailer!. }
  Intros c1.
  rename H into Hcp, H0 into Hc1x.
  assert (Hcp' := Hcp). destruct Hcp' as (Hc1 & HKlo & _).
  destruct (sleft_cp_ub a (w_K w) (w_j w) (w_c w) c1) as (Xu1 & Xd1);
    [unfold sp_d in *; lia | unfold lo, sp_d, sp_cap, sp_N in *; lia | exact Hcp | exact Xsrc |].
  thaw FR. abbreviate_semax.
  forward.
  assert_PROP (isptr (lit_extra (a_p a))) as Hxp by entailer!.
  assert (Hle: lit_extra (a_p a) = offset_val 30380 (a_p a)).
  { revert Hxp. unfold lit_extra, field_address. destruct (field_compatible_dec _ _ _); [reflexivity | intros []]. }
  rewrite <- Hle.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'6 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
  { forward. entailer!. }
  { exfalso. match goal with H: Int.lt _ _ = false |- _ => revert H; vm_compute; intros Hc'; discriminate Hc' end. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'7 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
  { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc'; discriminate Hc' end]. }
  { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'7 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
    { forward. forward. entailer!. }
    { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc'; discriminate Hc' end]. } }
  forward. forward.
  assert (Hpp: isptr (a_p a)) by (rewrite Hle in Hxp; destruct (a_p a); try contradiction; simpl; auto).
  rewrite (sleft_extra_end (a_p a) Hpp), <- Hle.
  assert (Hb' := Hb). destruct Hb' as (Hos & _ & _ & _ & _ & _ & _ & Hxrl & Hxrb).
  assert (Hxl: Zlength (zbytes (sp_tail a) ++ g_xr g) = LITEXTRA_N).
  { rewrite Zlength_app, Zlength_map, Hxrl. unfold sp_tail. rewrite Zlength_sublist by (unfold sp_n, LITBUFFEREXTRASIZE in *; lia).
    unfold LITEXTRA_N, WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE. lia. }
  rewrite <- Hxl.
  change (data_at Ews (tarray tuchar (Zlength (zbytes (sp_tail a) ++ g_xr g))) (zbytes (sp_tail a) ++ g_xr g) (lit_extra (a_p a)))
    with (BlkSeqEXEC.lit_res (LitSep Ews (lit_extra (a_p a)) (zbytes (sp_tail a) ++ g_xr g))).
  replace (sp_N a) with (Zlength c1) by lia.
  replace (data_at Tsh (tptr tuchar) (lit_extra (a_p a)) (a_vlp a))
    with (data_at Tsh (tptr tuchar) (offset_val 0 (lit_extra (a_p a))) (a_vlp a))
    by (rewrite isptr_offset_val_zero by exact Hxp; reflexivity).
  assert (Hoff: 1 <= off <= SIZE_MAX).
  { apply c_offset_ok; [apply les_rep64; exact Hcrep | exact Hov]. }
  assert (HdE: is_pointer_or_null (fs_dictEnd (a_fs a))) by apply Hpend.
  assert (Xxo: exec_ext_ok (sp_x a) (w_c w)).
  { unfold exec_ext_ok. split; [lia|].
    destruct (sp_x a) as [|e1 elen|sh eb en ec e1 elen];
      [exact I | destruct Hext as (_ & ? & ?); split; lia | destruct Hext as (_ & ? & ? & ? & ? & ?); repeat split; auto; lia]. }
  assert (Xdh1: Forall is_byte_val (sublist (sp_ps a) (sp_d a + w_K w + lo) c1)).
  { apply (Forall_def_join _ (sp_ps a) (sp_d a + w_K w)); try (unfold sp_d, sp_cap, sp_N in *; lia); [| exact Xd1].
    apply (Forall_def_ub (w_c w)); auto; unfold sp_d, sp_cap, sp_N in *; lia. }
  assert (Xde1: ext_def (sp_x a) c1) by (apply (ext_def_ub _ (w_c w)); auto).
  assert (Xdl1: Forall is_byte_val (sublist 0 (LITBUFFEREXTRASIZE + WILDCOPY_OVERLENGTH) (zbytes (sp_tail a) ++ g_xr g))).
  { apply Forall_sublist. apply Forall_app. split; [| exact Hxrb]. apply sleft_zbytes_byte.
    unfold sp_tail, bytes_ok in *. apply Forall_sublist. exact Hlb. }
  forward_call (a_gv a, oa_sh (a_o a), sp_ob a, c1, sp_d a + w_K w + lo, sp_d a + sp_cap a, Tsh, a_vsq a,
                ll - lo, ml, off, Tsh, a_vlp a, LitSep Ews (lit_extra (a_p a)) (zbytes (sp_tail a) ++ g_xr g),
                0, LITBUFFEREXTRASIZE, sp_ps a, sp_x a, fs_dictEnd (a_fs a)).
  { split; [unfold sp_N in *; lia|]. split; [unfold sp_d, sp_cap, sp_N in *; lia|].
    split; [unfold LL_VMAX in *; lia|]. split; [unfold ML_VMAX in *; lia|].
    split; [rewrite Hxl; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH; lia|].
    unfold exec_ext_ok. split; [lia|].
    destruct (sp_x a) as [|e1 elen|sh eb en ec e1 elen];
      [exact I | destruct Hext as (_ & ? & ?); split; lia | destruct Hext as (_ & ? & ? & ? & ? & ?); repeat split; auto; lia]. }
  Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
  rename H into Hr0, H0 into Hc'l, H1 into Hbc', H2 into Hee, H3 into Herrc, H4 into Hsucc.
  rename H5 into Hxu, H6 into Hxf, H7 into Hxex.
  forward_call r.
  destruct (is_error_code r) eqn:Er.
  - forward_if (PROP (False) LOCAL () SEP ()).
    + apply semax_post with (R' := sp_R a).
      1-3: unfold sp_R, frame_ret_assert, function_body_ret_assert; simpl RA_normal; simpl RA_break;
           simpl RA_continue; unfold bind_ret; apply andp_left2; intro rho; simpl; normalize; try contradiction.
      1: intros vl; apply andp_left2; apply derives_refl.
      unfold sp_R, sp_post. forward.
      assert (Hxc: byte_cells (zbytes (sp_tail a) ++ g_xr g)).
      { apply Forall_app. split; [|exact Hxrb]. apply sleft_zbytes_byte.
        unfold sp_tail, bytes_ok in *. apply Forall_sublist. exact Hlb. }
      destruct (Herrc eq_refl) as [Hunx Hderr].
      assert (Hune: unchanged_outside (sp_c0 a) c' (sp_d a) (sp_d a + sp_cap a))
        by (apply (sleft_unch_err a (g_t g) w ll ml ov c1 c' (sp_d a + w_K w + lo) (sp_d a + sp_cap a)); auto; lia).
      assert (Hmdl := sleft_err_mdl a (g_t g) w ll ml ov Hsa Hos Hsp
                        (sleft_xerr a (g_t g) w ll ml ov c1 Hsa Hpend Hsp Hbrk Hcp (eq_sym Hee))).
      assert (Hxpost: xpost a r c' (a_rep a)).
      { apply xpost_err; [exact Er|].
        exact (xleft_xerr a (g_t g) _ w ll ml ov c1 Hsa Hpend Hsp Hxpd Hbrk HKlo Hc1x (eq_sym Hee)). }
      assert (Hbc2: byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext (a_h a)) -> byte_cells c').
      { intros B1 B2 B3. apply Hbc'; [| exact Hxc | exact B3].
        apply (sleft_cp_bytes a (w_K w) (w_j w) (w_c w) c1);
          [unfold sp_d; lia | lia | | | | exact Hcp | exact (Hbyt B1 B2 B3)];
          unfold lo, sp_lim, sp_d, sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
      Exists r c' (a_rep a).
      unfold BlkSeqEXEC.lit_res. rewrite Hxl.
      sep_apply (sleft_rel a g Q Rin lp (seqrep (ll - lo) ml off) (w_pos w) (w_lo w) (w_st w)
                   (snd (c_offset (w_crep w) ll ov)) (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr 0))
                   (g_xr g) Hb Hxa).
      replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      change (sp_ob a) with (oa_base (a_o a)). change (sp_x a) with (hc_ext (a_h a)).
      replace (Zlength c1) with (oa_N (a_o a)) by (unfold sp_N in *; lia).
      entailer!.
      repeat match goal with
       | |- _ /\ _ => split
       | |- is_error_code _ = false -> _ => let Hf := fresh in intros Hf; rewrite Er in Hf; discriminate Hf
       | |- is_error_code _ = true -> dec_err _ => intros _; exact Hderr
       end.
      all: try first [unfold sp_N in *; lia | exact Hrep | exact Hune | exact Hbc2 | exact Hxpost].
      all: match goal with Hv: _ = 0 \/ _ |- _ => specialize (Hmdl Hv) end.
      all: destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; [|exact I].
      all: intros Hcb; right; split; [exact Er | apply Hmdl; exact Hcb].
    + exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
        rewrite Int.unsigned_zero in Hx; lia end.
  - destruct (Hsucc eq_refl) as (Hr & Hlpv & Hunx & Hbytes). clear Hsucc Herrc. subst r lp.
    forward_if.
    { exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
    unfold MORE_COMMANDS, abbreviate. apply -> seq_assoc. apply dec_skipbreak_seq.
    forward. forward.
    { entailer!. all: try (rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia); unfold LONGNBSEQ in *; rep_lia). }
    assert (Hsinv: sinv a (g_t g) false
              {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                 w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + ll + ml; w_j := w_j w + ll;
                 w_c := c' |}).
    { apply (sleft_sinv a (g_t g) w ll ml ov (g_xr g) c1 c' Hsa Hpend Hsp Hbrk Hcp Hc'l Hxrb); fold lo off.
      - intros B1 B2 B3. apply Hbc'; auto.
      - symmetry. exact Hee.
      - exact Hunx.
      - rewrite Z.add_0_l in Hbytes. exact Hbytes.
      - exact Xu1.
      - exact Xd1.
      - exact Hxu.
      - exact (Hxf eq_refl). }
    assert (Hxinv := xleft_ok a (g_t g) (zbytes (sp_tail a) ++ g_xr g) w ll ml ov (ll - lo + ml) c1 c' Hsa Hpend Hsp Hxpd
                       Hbrk HKlo Hc1x ltac:(lia) Hc'l (eq_sym Hee) Er
                       (sx_exact (sp_x a) false (is_error_code (ll - lo + ml)) _ eq_refl Hxex)).
    Exists {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
              w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + ll + ml; w_j := w_j w + ll;
              w_c := c' |}.
    unfold sp_INV, sp_L, sp_S, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc; cbn [app w_id w_pos w_lo w_st w_crep w_K w_j w_c].
    unfold BlkSeqEXEC.lit_res. rewrite Hxl. cbn [lit_base].
    rewrite sleft_add by (auto; unfold LL_VMAX, ML_VMAX in *; rep_lia).
    replace (Zlength c1) with (sp_N a) by lia.
    sep_apply (data_at_data_at_ Tsh t_seq (seqrep (ll - lo) ml off) (a_vsq a)).
    entailer!.
    + split; [f_equal; f_equal; lia | f_equal; lia].
    + replace (w_j w + ll - (sp_n a - LITBUFFEREXTRASIZE)) with (ll - lo)
        by (unfold lo, sp_lim; lia). apply derives_refl.
Qed.

(* phase 2 after the decode: ZSTD_execSequence from litExtraBuffer (an error is returned) *)
Definition sp_x2_R (a: sa) (g: sg) (Q Rin: mpred) : ret_assert :=
  {| RA_normal := EX w': sw, sp_INV a g Q Rin false w' (a_nb a - w_id w' + 1);
     RA_break := FF; RA_continue := FF;
     RA_return := RA_return (sp_R a) |}.

(* ---------- seg_x2's helpers ---------- *)

Lemma sx2_zb (l0: list Z) : bytes_ok l0 -> byte_cells (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

(* the facts of the precondition *)
Lemma sx2_pre (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) :
  sa_ok a -> bfacts a g Q Rin -> spend a t false w ll ml ov ->
  0 < sp_cap a /\ Zlength (zbytes (sp_tail a) ++ g_xr g) = LITEXTRA_N /\
  Zlength (w_c w) = sp_N a /\ Zlength (sp_c0 a) = sp_N a /\ sp_N a <= 2 ^ 63 - 1 /\
  writable_share (oa_sh (a_o a)) /\
  0 <= sp_d a /\ 0 <= w_K w /\ 0 <= sp_ps a <= sp_d a /\ sp_d a + w_K w <= sp_d a + sp_cap a <= sp_N a /\
  LITBUFFEREXTRASIZE < sp_n a /\ sp_n a - LITBUFFEREXTRASIZE <= w_j w <= sp_n a /\
  exec_ext_ok (sp_x a) (w_c w) /\ ext_in_bounds (sp_x a) (sp_N a) /\ 0 <= ext_len (sp_x a) <= 2 ^ 63 - 1 /\
  layout_ok (a_fs a) (sp_ob a) (sp_N a) (sp_d a) (sp_ps a) (sp_x a) /\
  bytes_ok (a_lits a) /\ sp_n a <= a_bsm a /\ 0 <= a_bsm a /\ rep_ok (a_rep a) /\
  byte_cells (g_xr g) /\ Zlength (g_xr g) = WILDCOPY_OVERLENGTH.
Proof.
  intros Hsa Hbf Hsp.
  destruct Hsa as (Ho & Hi & Hl & Hbsm & Hn & Hnb & Hnc & Hso & Hrep & Hfe & Hc0 & Hlay & Hhp & Hlp & He0).
  destruct Hsp as (Hid & _ & _ & _ & _ & _ & _ & _ & _ & Hout & _).
  destruct Hout as (HK & Hc & (Hj & _) & _ & _).
  destruct (Hnc ltac:(lia)) as [_ Hcap].
  specialize (Hlay Hcap).
  destruct Hbf as (_ & _ & _ & _ & _ & _ & _ & Hxr & Hxb).
  destruct Hl as (Hlb & Hn0 & Hgt & Hd & Hend & Hsub).
  destruct Ho as (Hsh & HcN & HN & Hd0 & Hc0' & HdN).
  pose proof Hlay as (Hps & _ & _ & Hel & Hx).
  unfold sp_tail, sp_cap, sp_N, sp_d, sp_n, sp_ps, sp_x, sp_ob, sp_c0 in *.
  split; [lia|].
  split. { rewrite Zlength_app, Zlength_map, Zlength_sublist, Hxr by lia. unfold LITEXTRA_N, LITBUFFEREXTRASIZE in *. lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [auto|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { unfold exec_ext_ok. destruct (hc_ext (a_h a)); simpl in *; intuition lia. }
  split. { unfold ext_in_bounds. destruct (hc_ext (a_h a)); simpl in *; intuition lia. }
  split; [lia|]. split; [auto|]. split; [auto|]. split; [lia|]. split; [lia|]. auto.
Qed.

(* the content length of a model run *)
Lemma sx2_cnt (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep2) ->
  Zlength (skipn (length out) (out' ++ lits')) = Zlength out' - Zlength out + Zlength lits'.
Proof.
  intros H. destruct (sp_exec_len _ _ _ _ _ _ _ _ _ H) as (ext & -> & _ & _).
  rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl.
  rewrite !Zlength_app. lia.
Qed.

Lemma sx2_blk (wsize: Z) (rep: Z * Z * Z) (hist lits out blk: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  exec_seqs wsize rep hist lits (out ++ blk) seqs = Some (out', lits', rep2) ->
  Zlength blk <= Zlength out' - Zlength out.
Proof.
  intros H. destruct (sp_exec_len _ _ _ _ _ _ _ _ _ H) as (ext & -> & _ & _).
  rewrite !Zlength_app. pose proof (Zlength_nonneg ext). lia.
Qed.

(* the literals execSequence reads from litExtraBuffer are the model's next ones *)
Lemma sx2_lits (a: sa) (xr: list val) (j ll: Z) :
  LITBUFFEREXTRASIZE < sp_n a -> sp_n a - LITBUFFEREXTRASIZE <= j -> 0 <= ll -> j + ll <= sp_n a ->
  sublist (j - (sp_n a - LITBUFFEREXTRASIZE)) (j - (sp_n a - LITBUFFEREXTRASIZE) + ll) (zbytes (sp_tail a) ++ xr) =
  zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat j) (a_lits a))).
Proof.
  intros Hn Hj Hll Hjl. unfold sp_tail, sp_n in *.
  rewrite sublist_app1 by (rewrite ?Zlength_map, ?Zlength_sublist by lia; lia).
  rewrite sublist_map. f_equal.
  rewrite sublist_sublist by lia.
  replace (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE) + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)) with j by lia.
  replace (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE) + ll + (Zlength (a_lits a) - LITBUFFEREXTRASIZE))
    with (j + ll) by lia.
  unfold sublist. rewrite firstn_skipn_comm. f_equal. f_equal. lia.
Qed.

(* the model step when the content fits: loop_exec_step at op = d + K *)
Lemma sx2_fit (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z)
    (seqs: list sequence) (out' lits': list Z) (rep2: Z * Z * Z) (sq: sequence) (blk: list Z) :
  sa_ok a -> bfacts a g Q Rin -> spend a t false w ll ml ov ->
  model_hyp a t seqs out' lits' rep2 ->
  skipn (Z.to_nat (w_id w)) seqs = sq :: skipn (Z.to_nat (w_id w + 1)) seqs ->
  sq_ll sq = ll -> sq_ml sq = ml -> sq_ov sq = ov ->
  Zlength blk = w_K w ->
  exec_seqs (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
    (skipn (Z.to_nat (w_id w)) seqs) = Some (out', lits', rep2) ->
  cntlen a out' lits' <= sp_cap a ->
  sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk ->
  exists mb,
    ll <= sp_n a - w_j w /\ sp_d a + w_K w + ll + ml <= sp_d a + sp_cap a /\
    fst (c_offset (w_crep w) ll ov) <= sp_d a + w_K w + ll - sp_ps a + ext_len (sp_x a) /\
    Zlength mb = ml /\
    ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) /\
    sublist (sp_d a + w_K w) (sp_d a + w_K w + ll + ml)
      (exec_c (w_c w) (sp_d a + w_K w) (zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)))) ml
         (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (sp_x a)) =
      zbytes (firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb) /\
    exec_seqs (sp_ws a) (snd (c_offset (w_crep w) ll ov)) (sp_hist a) (skipn (Z.to_nat (w_j w + ll)) (a_lits a))
      (sp_out a ++ blk ++ firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb)
      (skipn (Z.to_nat (w_id w + 1)) seqs) = Some (out', lits', rep2).
Proof.
  intros Hsa Hbf Hsp Hm Hsq Hsll Hsml Hsov Hbl Hex Hfit Hbytes.
  destruct (sx2_pre a g Q Rin t w ll ml ov Hsa Hbf Hsp)
    as (Hcap & _ & Hc & Hc0 & HN & _ & Hd0 & HK & Hps & HKc & Hn & Hj & _ & Hib & Hel & _ & Hlb & _ & Hbsm & _).
  assert (Hm': hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
               ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
               Zlength out' - Zlength (sp_out a) + Zlength lits' <= a_bsm a).
  { unfold model_hyp in Hm. destruct t as [[tLL tOF] tML]. tauto. }
  destruct Hm' as (Hhv & Hcl & Hcnt).
  destruct Hsp as (_ & _ & _ & _ & _ & Hrep & Hll & Hml & Hov & Hout & _).
  destruct Hout as (_ & _ & (_ & Hun) & _ & _).
  pose proof (sx2_blk _ _ _ _ _ _ _ _ _ _ Hex) as HKb.
  rewrite Hsq in Hex.
  assert (Hun2: unchanged_outside (sp_c0 a) (w_c w) (sp_d a)
                  (sp_d a + Z.min (sp_cap a) (a_bsm a + WILDCOPY_OVERLENGTH))).
  { intros q Hq Hnq. apply Hun; [exact Hq|]. intros Hq2. apply Hnq.
    pose proof (Zlength_nonneg lits'). unfold WILDCOPY_OVERLENGTH in *. lia. }
  assert (Hblk0: sublist (sp_d a) (sp_d a + Zlength blk + 0) (w_c w) =
                 zbytes (blk ++ firstn (Z.to_nat 0) (skipn (Z.to_nat (w_j w)) (a_lits a)))).
  { rewrite Z.add_0_r, Hbl. simpl. rewrite app_nil_r. exact Hbytes. }
  destruct (loop_exec_step (sp_c0 a) (w_c w) (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a)
              (sp_out a) (sp_ws a) blk (skipn (Z.to_nat (w_j w)) (a_lits a)) 0 sq
              (skipn (Z.to_nat (w_id w + 1)) seqs) (w_crep w) out' lits' rep2)
    as (off & crep' & mb & Hco & _ & Hlr & Hend & Hoff & Hmb & Hfit2 & Hrest);
    try lia; auto.
  - rewrite Hc. exact Hib.
  - apply Forall_skipn. exact Hlb.
  - cbv zeta in *. rewrite Hsll, Hsml, Hsov in *. rewrite Hbl in *.
    rewrite Hco. cbn [fst snd].
    rewrite Zlength_skipn in Hlr.
    unfold cntlen in Hfit.
    destruct Hfit2 as (Hro & Hx); [lia|].
    exists mb. unfold sp_n in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hmb|].
    split. { specialize (Hro (sp_d a + sp_cap a) ltac:(lia)). rewrite Z.add_0_r, Z.sub_0_r in Hro. exact Hro. }
    split. { rewrite Z.add_0_r in Hx. simpl skipn in Hx. exact Hx. }
    rewrite skipn_skipn in Hrest.
    replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hrest by lia.
    exact Hrest.
Qed.

(* the error: under the model it is a capacity error, which happens only when the content does not fit *)
Lemma sx2_err (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z) :
  sa_ok a -> bfacts a g Q Rin -> a_os a = Some t -> spend a t false w ll ml ov ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = true ->
  sp_cap a = 0 \/
  (hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
   ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a)) ->
  match seqs_model (a_os a) (sp_s a) (a_nb a) (a_rep a) (sp_hist a) (sp_out a) (a_lits a) (sp_ws a) with
  | Some (cnt, _) => Zlength cnt <= a_bsm a -> sp_cap a < Zlength cnt
  | None => True
  end.
Proof.
  intros Hsa Hbf Hos Hsp Herr Hv.
  pose proof (sx2_pre a g Q Rin t w ll ml ov Hsa Hbf Hsp) as (Hcap & _).
  assert (Hv': hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
               ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a))
    by (destruct Hv as [Hv|Hv]; [lia | exact Hv]).
  destruct Hv' as (Hhv & Hcl).
  pose proof Hsp as (Hid & _).
  rewrite Hos. unfold seqs_model.
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct t as [[tLL tOF] tML].
  destruct (decode_seq_stream tLL tOF tML (sp_s a) (a_nb a)) as [seqs|] eqn:Hds; [|exact I].
  destruct (exec_seqs (sp_ws a) (a_rep a) (sp_hist a) (a_lits a) (sp_out a) seqs) as [[[out' lits'] rep2]|] eqn:Hex;
    [|exact I].
  intros Hcnt. rewrite (sx2_cnt _ _ _ _ _ _ _ _ _ Hex) in Hcnt |- *.
  destruct (Z_le_gt_dec (cntlen a out' lits') (sp_cap a)) as [Hfit|Hno]; [|unfold cntlen in Hno; lia].
  exfalso.
  assert (Hm: model_hyp a (tLL, tOF, tML) seqs out' lits' rep2) by exact (conj Hhv (conj Hcl (conj Hds (conj Hex Hcnt)))).
  pose proof Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmod).
  destruct (Hmod seqs out' lits' rep2 Hm) as (sq & Hsq & Hsll & Hsml & Hsov & _ & _ & _ & blk & Hbl & Hexb & Hbytes).
  destruct (sx2_fit a g Q Rin (tLL, tOF, tML) w ll ml ov seqs out' lits' rep2 sq blk Hsa Hbf Hsp Hm Hsq Hsll Hsml
              Hsov Hbl Hexb Hfit (Hbytes Hfit)) as (mb & Hlr & Hend & Hoff & _).
  unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr. lia.
Qed.

Lemma sx2_def_sub (lst: list val) (lo hi: Z) :
  0 <= lo <= hi -> hi <= Zlength lst ->
  (Forall is_byte_val (sublist lo hi lst) <-> forall q, lo <= q < hi -> is_byte_val (Znth q lst)).
Proof.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - lo) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - lo + lo) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Ltac sx2_zmin :=
  repeat match goal with
  | |- context [Z.min ?a ?b] =>
      let Hz := fresh "Hz" in destruct (Z.min_spec a b) as [[Hz ->]|[Hz ->]]
  | H0: context [Z.min ?a ?b] |- _ =>
      let Hz := fresh "Hz" in let Hm := fresh "Hm" in
      destruct (Z.min_spec a b) as [[Hz Hm]|[Hz Hm]]; rewrite Hm in H0; clear Hm
  end.

(* sp_outok after the sequence *)
Lemma sx2_outok (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z)
    (c': list val) :
  sa_ok a -> bfacts a g Q Rin -> spend a t false w ll ml ov ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = false ->
  Zlength c' = Zlength (w_c w) ->
  (byte_cells (w_c w) -> byte_cells (zbytes (sp_tail a) ++ g_xr g) -> ext_bytes (sp_x a) -> byte_cells c') ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w)
    (Z.min (sp_d a + sp_cap a) (sp_d a + w_K w + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) ->
   Forall is_byte_val (sublist (sp_ps a) (sp_d a + w_K w) (w_c w)) ->
   Forall is_byte_val (sublist (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + ll)
                         (zbytes (sp_tail a) ++ g_xr g)) ->
   ext_def (sp_x a) (w_c w) ->
   Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c')) ->
  xd_ub (w_c w) c' -> Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c') ->
  sp_outok a false (w_K w + (ll + ml)) (w_j w + ll) c'.
Proof.
  intros Hsa Hbf Hsp Hno Hc' Hbc' Hun' Hbytes Hxu Hxf.
  destruct (sx2_pre a g Q Rin t w ll ml ov Hsa Hbf Hsp)
    as (Hcap & Hcl & Hc & Hc0 & HN & _ & Hd0 & HK & Hps & HKc & Hn & Hj & _ & _ & Hel & Hlay & Hlb & _ & Hbsm &
        _ & Hxb & Hxr).
  pose proof Hsp as (_ & _ & _ & _ & _ & _ & Hll & Hml & _ & Hout & _).
  destruct Hout as (_ & _ & (_ & Hun) & Hdef & Hbc).
  unfold exec_err in Hno. rewrite !orb_false_iff, !Z.ltb_ge in Hno. destruct Hno as ((Hno1 & Hno2) & Hno3).
  assert (Hlits: byte_cells (zbytes (sp_tail a) ++ g_xr g)).
  { apply Forall_app. split; [apply sx2_zb; unfold sp_tail; apply Forall_sublist; exact Hlb | exact Hxb]. }
  unfold sp_outok.
  split; [lia|]. split; [lia|]. split.
  { split; [lia|]. intros q Hq Hnq. rewrite Hun'.
    - apply Hun; [exact Hq|]. intros Hq2. apply Hnq. lia.
    - lia.
    - lia. }
  split.
  - apply (sp_dfd_step a (w_K w) (ll + ml) (w_c w) c'); auto; lia.
  - intros B0 Bi Be. apply Hbc'; [apply Hbc; auto | exact Hlits | exact Be].
Qed.

(* the model after the sequence: loop_exec_step when the content fits, else sp_exec_free *)
Lemma sx2_minv (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z)
    (c': list val) :
  sa_ok a -> bfacts a g Q Rin -> spend a t false w ll ml ov ->
  Zlength c' = Zlength (w_c w) ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w)
    (Z.min (sp_d a + sp_cap a) (sp_d a + w_K w + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) ->
   sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c' =
   sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml))
     (exec_c (w_c w) (sp_d a + w_K w)
        (sublist (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + ll)
           (zbytes (sp_tail a) ++ g_xr g)) ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (sp_x a))) ->
  sp_minv a t {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                 w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                 w_c := c' |}.
Proof.
  intros Hsa Hbf Hsp Hc' Hun' Hx.
  destruct (sx2_pre a g Q Rin t w ll ml ov Hsa Hbf Hsp)
    as (Hcap & Hcl & Hc & Hc0 & HN & _ & Hd0 & HK & Hps & HKc & Hn & Hj & _ & _ & Hel & Hlay & Hlb & _ & Hbsm & _).
  pose proof Hsp as (Hid & _ & _ & _ & _ & Hrep & Hll & Hml & Hov & _ & Hmod).
  unfold sp_minv. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  intros seqs out' lits' rep2 Hm.
  destruct (Hmod seqs out' lits' rep2 Hm)
    as (sq & Hsq & Hsll & Hsml & Hsov & Hds & Hrdy & Hlo & blk & Hbl & Hexb & Hbytes).
  split. { replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia. exact Hds. }
  split; [exact Hrdy|]. split; [exact Hlo|].
  destruct (Z_le_gt_dec (cntlen a out' lits') (sp_cap a)) as [Hfit|Hnf].
  - destruct (sx2_fit a g Q Rin t w ll ml ov seqs out' lits' rep2 sq blk Hsa Hbf Hsp Hm Hsq Hsll Hsml Hsov
                Hbl Hexb Hfit (Hbytes Hfit)) as (mb & Hlr & Hend & Hoff & Hmb & Hro & Hxc & Hrest).
    exists (blk ++ firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb).
    split. { rewrite !Zlength_app, Zlength_firstn, Zlength_skipn. unfold sp_n in *. lia. }
    split; [exact Hrest|].
    intros _.
    rewrite (sublist_split (sp_d a) (sp_d a + w_K w) (sp_d a + (w_K w + (ll + ml)))) by lia.
    rewrite map_app. f_equal.
    + rewrite <- (Hbytes Hfit).
      apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
      intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia.
      apply Hun'; lia.
    + replace (sp_d a + (w_K w + (ll + ml))) with (sp_d a + w_K w + (ll + ml)) by lia.
      rewrite (Hx Hro). rewrite sx2_lits by (unfold sp_n in *; lia).
      replace (sp_d a + w_K w + (ll + ml)) with (sp_d a + w_K w + ll + ml) by lia.
      exact Hxc.
  - rewrite Hsq in Hexb.
    destruct (sp_exec_free (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a))
                (sp_out a ++ blk) sq (skipn (Z.to_nat (w_id w + 1)) seqs) out' lits' rep2)
      as (off & crep' & mb & Hco & _ & _ & Hll' & Hmb & Hrest); try lia; auto.
    rewrite Hsll, Hsml, Hsov in *. rewrite Hco. cbn [snd].
    exists (blk ++ firstn (Z.to_nat ll) (skipn (Z.to_nat (w_j w)) (a_lits a)) ++ mb).
    split. { rewrite !Zlength_app, Zlength_firstn. lia. }
    split.
    + rewrite skipn_skipn in Hrest.
      replace (Z.to_nat ll + Z.to_nat (w_j w))%nat with (Z.to_nat (w_j w + ll)) in Hrest by lia.
      rewrite <- app_assoc in Hrest. exact Hrest.
    + intros Hf. lia.
Qed.

(* the invariant after the sequence *)
Lemma sx2_sinv (a: sa) (g: sg) (Q Rin: mpred) (t: fse_table * fse_table * fse_table) (w: sw) (ll ml ov: Z)
    (c': list val) :
  sa_ok a -> bfacts a g Q Rin -> spend a t false w ll ml ov ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = false ->
  Zlength c' = Zlength (w_c w) ->
  (byte_cells (w_c w) -> byte_cells (zbytes (sp_tail a) ++ g_xr g) -> ext_bytes (sp_x a) -> byte_cells c') ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w)
    (Z.min (sp_d a + sp_cap a) (sp_d a + w_K w + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (sp_x a) (sp_d a + w_K w) (sp_d a + sp_cap a) ll ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) ->
   sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c' =
   sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml))
     (exec_c (w_c w) (sp_d a + w_K w)
        (sublist (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + ll)
           (zbytes (sp_tail a) ++ g_xr g)) ml (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (sp_x a)) /\
   (Forall is_byte_val (sublist (sp_ps a) (sp_d a + w_K w) (w_c w)) ->
    Forall is_byte_val (sublist (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + ll)
                          (zbytes (sp_tail a) ++ g_xr g)) ->
    ext_def (sp_x a) (w_c w) ->
    Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c'))) ->
  xd_ub (w_c w) c' -> Forall is_byte_val (sublist (sp_d a + w_K w) (sp_d a + w_K w + (ll + ml)) c') ->
  sinv a t false {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                    w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                    w_c := c' |}.
Proof.
  intros Hsa Hbf Hsp Hno Hc' Hbc' Hun' Hbytes Hxu Hxf.
  destruct (sx2_pre a g Q Rin t w ll ml ov Hsa Hbf Hsp)
    as (Hcap & Hcl & Hc & Hc0 & HN & _ & Hd0 & HK & Hps & HKc & Hn & Hj & _ & _ & Hel & _).
  pose proof Hsp as (Hid & _ & Hlo & Hbc & Hst & Hrep & Hll & Hml & Hov & _).
  pose proof Hno as Hno'.
  unfold exec_err in Hno'. rewrite !orb_false_iff, !Z.ltb_ge in Hno'. destruct Hno' as ((Hno1 & Hno2) & Hno3).
  unfold sinv. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  split; [lia|]. split; [intros; lia|]. split; [lia|].
  split. { replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia. exact Hbc. }
  split; [exact Hst|].
  split. { apply sp_rep_step; [exact Hrep | exact Hov |]. unfold SIZE_MAX, LL_VMAX in *. lia. }
  split.
  - apply (sx2_outok a g Q Rin t w ll ml ov c'); auto; try (intros Hro; apply (Hbytes Hro)).
  - apply (sx2_minv a g Q Rin t w ll ml ov c'); auto.
    intros Hro. apply (Hbytes Hro).
Qed.


(* op += oneSeqSize *)
Lemma sx2_add (b: val) (x n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val x b) (Vlong (Int64.repr n))) =
  offset_val (x + n) b.
Proof.
  intros Hb Hn. destruct b; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

(* the error return: the facts of sp_post *)
Lemma sx2_err_post (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (ll ml ov r: Z) (c': list val) :
  sa_ok a -> bfacts a g Q Rin -> spend a (g_t g) false w ll ml ov ->
  0 <= r <= Int64.max_unsigned -> Zlength c' = Zlength (w_c w) ->
  (byte_cells (w_c w) -> byte_cells (zbytes (sp_tail a) ++ g_xr g) -> ext_bytes (sp_x a) -> byte_cells c') ->
  is_error_code r = true ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = true ->
  unchanged_outside (w_c w) c' (sp_d a + w_K w) (sp_d a + sp_cap a) -> dec_err r ->
  let o := a_o a in let h := a_h a in
  0 <= r <= Int64.max_unsigned /\ Zlength c' = oa_N o /\ rep_ok (a_rep a) /\
  unchanged_outside (oa_c o) c' (oa_d o) (oa_d o + oa_cap o) /\
  (is_error_code r = false ->
     r <= oa_cap o /\
     unchanged_outside (oa_c o) c' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
     (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
      (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= a_bsm a /\ ext_far (oa_d o) (oa_cap o) (a_bsm a) (hc_ext h))) ->
        exists cnt, sublist (oa_d o) (oa_d o + r) c' = zbytes cnt /\ bytes_ok cnt)) /\
  (oa_cap o = 0 \/
   (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
    ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
   match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
   | Some (cnt, rep2) =>
       Zlength cnt <= a_bsm a ->
       (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) c' = zbytes cnt /\
        a_rep a = rep2) \/
       (is_error_code r = true /\ oa_cap o < Zlength cnt)
   | None => True
   end) /\
  (is_error_code r = true -> dec_err r) /\
  (byte_cells (oa_c o) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext h) -> byte_cells c').
Proof.
  intros Hsa Hbf Hsp Hr Hc' Hbc' Er Herr Hun Hderr.
  pose proof Hbf as (Hos & _).
  pose proof (sx2_err a g Q Rin (g_t g) w ll ml ov Hsa Hbf Hos Hsp Herr) as Hmd.
  destruct (sx2_pre a g Q Rin (g_t g) w ll ml ov Hsa Hbf Hsp)
    as (Hcap & Hcl & Hc & Hc0 & HN & _ & Hd0 & HK & Hps & HKc & Hn & Hj & _ & _ & Hel & Hlay & Hlb & _ & Hbsm &
        Hrep0 & Hxb & Hxr).
  pose proof Hsp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hout & _).
  destruct Hout as (_ & _ & (_ & Hun0) & _ & Hbc0).
  assert (Hlits: byte_cells (zbytes (sp_tail a) ++ g_xr g)).
  { apply Forall_app. split; [apply sx2_zb; unfold sp_tail; apply Forall_sublist; exact Hlb | exact Hxb]. }
  cbv zeta.
  split; [exact Hr|]. split; [unfold sp_N in Hc; lia|]. split; [exact Hrep0|].
  split.
  { intros q Hq Hnq. transitivity (Znth q (w_c w)).
    - apply Hun; unfold sp_c0, sp_N, sp_d, sp_cap in *; lia.
    - apply Hun0; [exact Hq|]. unfold sp_c0, sp_N, sp_d, sp_cap in *. lia. }
  split; [rewrite Er; discriminate|].
  split.
  { intros Hv. specialize (Hmd Hv). unfold sp_s, sp_hist, sp_out, sp_ws in Hmd.
    destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; [|exact I].
    intros Hcnt. right. split; [exact Er | exact (Hmd Hcnt)]. }
  split; [intros _; exact Hderr|].
  intros B0 Bi Be. apply Hbc'; [apply Hbc0; auto | exact Hlits | exact Be].
Qed.

(* the literal fields back as scratch *)
Lemma sx2_scratch (a: sa) (v1 v2: val) (xr: list val) :
  sa_x a xr -> Zlength (zbytes (sp_tail a) ++ xr) = LITEXTRA_N ->
  field_at Ews t_dctx (DOT _litBufferLocation) v1 (a_p a) * field_at Ews t_dctx (DOT _litBufferEnd) v2 (a_p a) *
  data_at Ews (tarray tuchar (Zlength (zbytes (sp_tail a) ++ xr))) (zbytes (sp_tail a) ++ xr) (lit_extra (a_p a)) *
  sp_FR0 a |--
  lit_scratch_x (a_p a) (a_lxb a) * pws_pred (a_W a) * frame_fields (a_p a) (a_fs a).
Proof.
  intros Hx Hl. rewrite Hl. unfold sp_FR0.
  sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
               v2 v1 Hx).
  cancel.
Qed.

(* the seqState_t local, split into its fields (as BlkSeqLoopShort.sh_exec_ok_ss) *)
Lemma sx2_ss_split (v: val) :
  data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma sx2_ss (gv0: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv0 s start pos lo st tp r v |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite (sx2_ss_split v). unfold seqstate_at, BIT_DStream_rep.
  destruct st as [[a b] c]; destruct tp as [[x y] z]. Intros ptr lim.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at.
  repeat (sep_apply data_at_data_at_). cancel.
Qed.


Lemma seg_x2 {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) ->
  semax sp_Delta (sp_PEND a g Q Rin false w ll ml ov) sp_x2 (sp_x2_R a g Q Rin).
Proof.
  intros Hsa Hpend Hbf Hxa.
  apply (semax_post (overridePost (EX w': sw, sp_INV a g Q Rin false w' (a_nb a - w_id w' + 1)) (sp_R a))).
  { unfold sp_x2_R, overridePost; cbn [RA_normal]. apply andp_left2, derives_refl. }
  { unfold sp_x2_R, sp_R, overridePost, frame_ret_assert, function_body_ret_assert; cbn [RA_break].
    apply andp_left2. rewrite FF_sepcon. apply derives_refl. }
  { unfold sp_x2_R, sp_R, overridePost, frame_ret_assert, function_body_ret_assert; cbn [RA_continue].
    apply andp_left2. rewrite FF_sepcon. apply derives_refl. }
  { intros vl. unfold sp_x2_R, overridePost; cbn [RA_return]. apply andp_left2, derives_refl. }
  pose proof Hbf as (Hos & _).
  unfold sp_PEND, sp_S, sp_L, sp_lvars, sp_ptrs. simpl app. Intros.
  rename H into Hsp, H0 into Hxp.
  destruct (sx2_pre a g Q Rin (g_t g) w ll ml ov Hsa Hbf Hsp)
    as (Hcap & Hcl & Hc & Hc0 & HN & Hsh & Hd0 & HK & Hps & HKc & Hn & Hj & Hext & Hib & Hel & Hlay & Hlb &
        Hnbsm & Hbsm & Hrep0 & Hxb & Hxr).
  pose proof Hsp as (Hid & _ & Hlo & Hbc & Hst & Hrep & Hll & Hml & Hov & Hout & _).
  assert (Hoff: 1 <= fst (c_offset (w_crep w) ll ov) <= SIZE_MAX).
  { apply c_offset_ok; [apply les_rep64, Hrep | lia]. }
  assert_PROP (isptr (sp_ob a)) as Hob by entailer!.
  unfold sp_Delta; simplify_func_tycontext.
  unfold sp_x2.
  rewrite <- Hcl, <- Hc.
  unfold sp_lp, sp_lbe.
  assert (Xdf: sp_dfd a (w_K w) (w_c w)) by (destruct Hout as (_ & _ & _ & Hd & _); exact Hd).
  destruct (sp_dfd_exec a (w_K w) 0 (w_c w) Hsa Hc ltac:(lia) ltac:(unfold sp_n, LITBUFFEREXTRASIZE in *; lia) Xdf)
    as (Xdh & Xde & _).
  assert (Xdl: Forall is_byte_val (sublist (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (LITBUFFEREXTRASIZE + WILDCOPY_OVERLENGTH)
                                     (zbytes (sp_tail a) ++ g_xr g))).
  { apply Forall_sublist. apply Forall_app. split; [apply sx2_zb; unfold sp_tail; apply Forall_sublist; exact Hlb | exact Hxb]. }
  forward_call (a_gv a, oa_sh (a_o a), sp_ob a, w_c w, sp_d a + w_K w, sp_d a + sp_cap a, Tsh, a_vsq1 a, ll, ml,
                fst (c_offset (w_crep w) ll ov), Tsh, a_vlp a,
                LitSep Ews (lit_extra (a_p a)) (zbytes (sp_tail a) ++ g_xr g),
                w_j w - (sp_n a - LITBUFFEREXTRASIZE), LITBUFFEREXTRASIZE, sp_ps a, sp_x a, fs_dictEnd (a_fs a)).
  { rewrite Hcl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, LL_VMAX, ML_VMAX in *.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply Hpend | unfold LITBUFFEREXTRASIZE in *; rep_lia]. }
  Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd lit_arr lit_base lit_res] in *.
  forward_call r.
  unfold POSTCONDITION, abbreviate, sp_R, sp_post.
  destruct (is_error_code r) eqn:Er.
  - forward_if (PROP (False) LOCAL () SEP ()).
    + forward.
      destruct (H3 eq_refl) as [Hun Hderr].
      destruct (sx2_err_post a g Q Rin w ll ml ov r c' Hsa Hbf Hsp H H0 H1 Er (eq_sym H2) Hun Hderr)
        as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
      assert (Hxpost: xpost a r c' (a_rep a)).
      { apply xpost_err; [exact Er|]. exact (xx2_err a (g_t g) _ w ll ml ov Hsa Hpend Hsp Hxp (eq_sym H2)). }
      Exists r c' (a_rep a).
      sep_apply (sp_release a g Q Rin Hbf).
      sep_apply (sx2_scratch a (Vint (Int.repr (sp_loc false))) (offset_val (sp_lim a) (sp_ob a))
                   (g_xr g) Hxa Hcl).
      sep_apply sx2_ss.
      sep_apply (data_at_data_at_ Tsh t_seq (seqrep ll ml (fst (c_offset (w_crep w) ll ov))) (a_vsq1 a)).
      sep_apply (data_at_data_at_ Tsh (tptr tuchar) lp (a_vlp a)).
      replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite Hc.
      apply andp_right; [apply prop_right; repeat (split; [assumption|]); reflexivity |].
      cancel.
      apply derives_refl.
    + exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
        rewrite Int.unsigned_zero in Hx; lia end.
  - destruct (H4 eq_refl) as (Hr & Hlp & Hun & Hbytes). clear H3 H4. subst r lp.
    forward_if. { exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
    unfold MORE_COMMANDS, abbreviate. apply dec_skipbreak_seq. forward.
    assert (Hinv := sx2_sinv a g Q Rin (g_t g) w ll ml ov c' Hsa Hbf Hsp (eq_sym H2) H0 H1 Hun Hbytes H5 (H6 eq_refl)).
    assert (Hxinv := xx2 a (g_t g) (zbytes (sp_tail a) ++ g_xr g) w ll ml ov (ll + ml) c' Hsa Hpend Hsp Hxp H0
                       (eq_sym H2) Er (sx_exact (sp_x a) false (is_error_code (ll + ml)) _ eq_refl H7)).
    sep_apply (data_at_data_at_ Tsh t_seq (seqrep ll ml (fst (c_offset (w_crep w) ll ov))) (a_vsq1 a)).
    Exists {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
              w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
              w_c := c' |}.
    unfold sp_INV, sp_S, sp_L, sp_lvars, sp_ptrs, sp_lp, sp_lbe. simpl app.
    cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
    rewrite sx2_add by (auto; unfold LL_VMAX, ML_VMAX in *; rep_lia).
    rewrite <- Hc, <- Hcl, <- H0.
    replace (a_nb a - (w_id w + 1) + 1) with (a_nb a - w_id w) by lia.
    replace (sp_d a + (w_K w + (ll + ml))) with (sp_d a + w_K w + (ll + ml)) by lia.
    replace (w_j w + ll - (sp_n a - LITBUFFEREXTRASIZE)) with (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + ll) by lia.
    entailer!.
Qed.

(* after the loops (all nbSeq sequences): BIT_endOfDStream (error: return), the repeat offsets into the
   context, the tables and the input array given back *)
Definition sp_end_R (a: sa) (ph: bool) (w: sw) (xr: list val) : ret_assert :=
  {| RA_normal := EX rep': Z * Z * Z, sp_LAST a ph w rep' xr;
     RA_break := FF; RA_continue := FF;
     RA_return := RA_return (sp_R a) |}.

(* seg_end helpers: under the model, at id = nb the bitstream is exhausted (pos = 0, lo = 0) and the block is
   the executed bytes followed by the remaining literals *)
Lemma send_model (a: sa) (t: fse_table * fse_table * fse_table) (w: sw) (cnt: list Z) (rep2: Z * Z * Z) :
  a_os a = Some t -> 0 < a_nb a -> w_id w = a_nb a -> sp_minv a t w ->
  hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) ->
  seqs_model (a_os a) (sp_s a) (a_nb a) (a_rep a) (sp_hist a) (sp_out a) (a_lits a) (sp_ws a) = Some (cnt, rep2) ->
  Zlength cnt <= a_bsm a ->
  w_pos w = 0 /\ w_lo w = 0 /\
  exists blk, Zlength blk = w_K w /\ cnt = blk ++ skipn (Z.to_nat (w_j w)) (a_lits a) /\ rep2 = w_crep w /\
    (Zlength cnt <= sp_cap a -> sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk).
Proof.
  intros Hos Hnb Hid Hm Hhv Hec Hsm Hlen.
  unfold seqs_model in Hsm. rewrite Hos in Hsm. destruct t as [[tLL tOF] tML].
  replace (a_nb a =? 0) with false in Hsm by (symmetry; apply Z.eqb_neq; lia).
  destruct (decode_seq_stream tLL tOF tML (sp_s a) (a_nb a)) as [seqs|] eqn:Hd; [|discriminate].
  destruct (exec_seqs (sp_ws a) (a_rep a) (sp_hist a) (a_lits a) (sp_out a) seqs) as [[[out' lits'] r2]|] eqn:He;
    [|discriminate].
  injection Hsm as Hc Hr. subst cnt r2.
  destruct (sp_exec_len _ _ _ _ _ _ _ _ _ He) as (ext & Hout & _ & _).
  assert (Hcnt: skipn (length (sp_out a)) (out' ++ lits') = ext ++ lits').
  { rewrite Hout, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  rewrite Hcnt in Hlen |- *.
  assert (Hmh: model_hyp a (tLL, tOF, tML) seqs out' lits' rep2).
  { unfold model_hyp. split; [exact Hhv|]. split; [exact Hec|]. split; [exact Hd|]. split; [exact He|].
    rewrite Hout, Zlength_app in *. lia. }
  specialize (Hm _ _ _ _ Hmh). cbv beta iota in Hm.
  destruct (w_st w) as [[sLL sOF] sML].
  destruct Hm as (Hds & _ & Hlo & blk & Hbl & Hex & Hby).
  rewrite Hid, Z.sub_diag in Hds. cbn in Hds. injection Hds as Hsk Hpos.
  rewrite Hid, <- Hsk in Hex. cbn in Hex. injection Hex as Ho' Hl' Hr'.
  split; [lia|]. split; [apply Hlo; exact Hid|].
  exists blk. split; [exact Hbl|].
  assert (Hext: ext = blk) by (rewrite Hout in Ho'; apply app_inv_head in Ho'; symmetry; exact Ho').
  subst ext. split; [rewrite Hl'; reflexivity|]. split; [symmetry; exact Hr'|].
  intros Hc. apply Hby. unfold cntlen. rewrite Hout, !Zlength_app in *. lia.
Qed.

Lemma send_slast (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) :
  sa_ok a -> bfacts a g Q Rin -> w_id w = a_nb a -> 0 < a_nb a -> sinv a (g_t g) ph w -> slast a ph w (w_crep w).
Proof.
  intros Hsa Hb Hid Hnb H. destruct H as (_ & _ & _ & _ & _ & Hcrep & Hout & Hmin).
  destruct Hsa as (_ & _ & _ & _ & _ & _ & Hnbp & _). destruct Hb as (Hos & _).
  unfold slast. split; [exact Hcrep|]. split; [exact Hout|]. split; [intros; lia|].
  intros [Hc0 | [Hhv Hec]] cnt rep2 Hsm Hlen.
  - destruct (Hnbp ltac:(lia)) as (_ & Hc). lia.
  - destruct (send_model a (g_t g) w cnt rep2 Hos Hnb Hid Hmin Hhv Hec Hsm Hlen) as (_ & _ & Hx). exact Hx.
Qed.

Lemma send_unch (a: sa) (ph: bool) (K j: Z) (c: list val) :
  sp_outok a ph K j c -> unchanged_outside (sp_c0 a) c (sp_d a) (sp_d a + sp_cap a).
Proof.
  intros (HK & _ & Hu & _). unfold unchanged_outside in *.
  destruct ph; destruct Hu as (_ & Hu); intros i Hi Hn; apply Hu; try exact Hi; intro; apply Hn; lia.
Qed.

Lemma send_dec_err : dec_err (err_code 20).
Proof.
  unfold dec_err, err_code, is_error_code, ZSTD_error_noForwardProgress_destFull,
    ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | split; lia].
Qed.

Lemma send_lit_scratch (p lp lb lbe: val) (ls loc: val) (l: list Z) (xv: list val) :
  bytes_ok l -> byte_cells xv ->
  field_at Ews t_dctx (DOT _litPtr) lp p * field_at Ews t_dctx (DOT _litSize) ls p *
  field_at Ews t_dctx (DOT _litBuffer) lb p * field_at Ews t_dctx (DOT _litBufferEnd) lbe p *
  field_at Ews t_dctx (DOT _litBufferLocation) loc p *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes l ++ xv) (lit_extra p) |-- lit_scratch p.
Proof.
  intros Hl Hx. unfold lit_scratch, lit_extra_bytes. rewrite <- litextra_data_at.
  Exists (zbytes l ++ xv). entailer!.
  unfold byte_cells. apply Forall_app. split; [|exact Hx]. clear - Hl.
  unfold bytes_ok in Hl. induction Hl as [|z l Hz Hl IH]; simpl; [constructor|].
  constructor; [|exact IH]. exists z. split; [exact Hz | reflexivity].
Qed.

Lemma send_ss_free (gv: globals) (s: list Z) (start: val) (pos lo sLL sOF sML: Z) (pLL pOF pML: val)
    (rep: Z * Z * Z) (p: val) :
  BIT_DStream_rep Tsh gv s start pos lo (field_address t_seqstate (DOT _DStream) p) *
  field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) p *
  field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) p *
  field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) p *
  field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals rep) p |-- data_at_ Tsh t_seqstate p.
Proof.
  unfold BIT_DStream_rep. Intros ptr lim.
  sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_BIT_DStream_t noattr)).
  unfold_data_at (data_at_ Tsh t_seqstate p).
  change (data_at_ Tsh (Tstruct ___gp_BIT_DStream_t noattr) (field_address t_seqstate (DOT _DStream) p))
    with (data_at_ Tsh (nested_field_type t_seqstate (DOT _DStream)) (field_address t_seqstate (DOT _DStream) p)).
  rewrite <- field_at__data_at_.
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _stateLL)).
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _stateOffb)).
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _stateML)).
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _prevOffset)).
  unfold field_at_. cancel.
Qed.

(* a return under a ret_assert whose return part is the function's *)
Lemma send_ret {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred) (e: option expr) (R: ret_assert)
    (Pf: environ -> mpred) (f: function) :
  RA_return R = RA_return (frame_ret_assert (function_body_ret_assert tulong Pf) (stackframe_of f)) ->
  semax Delta P (Sreturn e)
    (overridePost (RA_normal R) (frame_ret_assert (function_body_ret_assert tulong Pf) (stackframe_of f))) ->
  semax Delta P (Sreturn e) R.
Proof.
  intros HR H. destruct R as [Rn Rb Rc Rr]. cbn in HR. subst Rr.
  eapply semax_post; [| | | | exact H].
  all: unfold overridePost, frame_ret_assert, function_body_ret_assert; cbn [RA_normal RA_break RA_continue RA_return].
  - apply andp_left2, derives_refl.
  - rewrite FF_sepcon. apply andp_left2, FF_left.
  - rewrite FF_sepcon. apply andp_left2, FF_left.
  - intros vl. apply andp_left2, derives_refl.
Qed.

Lemma seg_end {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) -> w_id w = a_nb a -> 0 < a_nb a ->
  semax sp_Delta (sp_INV a g Q Rin ph w 0) sp_end (sp_end_R a ph w (g_xr g)).
Proof.
  intros Hsa Hpend Hb Hxa Hid Hnb. unfold sp_Delta, sp_end, sp_INV, sp_L, sp_S, sp_lvars, sp_ptrs; cbn [app]. Intros.
  rename H0 into Hxinv.
  apply xe_skipbreak_seq.
  match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P); [forward_if; [exfalso; auto | forward; apply ENTAIL_refl] | ] end.
  apply xe_skipbreak_seq.
  apply (es_dw _ _ (w_lo w = 0 /\ w_pos w = 0)).
  - unfold seqstate_at. destruct (w_st w) as [[sLL sOF] sML] eqn:Hst. destruct (g_tp g) as [[pLL pOF] pML] eqn:Htp. Intros.
    forward_call (Tsh, field_address t_seqstate (DOT _DStream) (a_vss a), a_gv a, sp_s a, sp_sst a, w_pos w, w_lo w, g_sh2 g, sp_sst a, sp_s a, 0).
    { entailer!. simpl. f_equal. unfold field_address. rewrite if_true; [reflexivity|]. auto with field_compatible. }
    { split; [apply Hb|]. unfold bit_src_ok, sp_sst. rewrite offset_offset_val, Z.add_0_r, Z.add_0_l, sublist_same by lia.
      split; [reflexivity|]. split; [lia|]. split; [lia | reflexivity]. }
    forward_if.
    + apply xe_skipbreak_seq.
      match goal with |- semax _ ?P _ _ => apply (xe_loop_seq _ P P); [forward_if; [exfalso; auto | forward; apply ENTAIL_refl] | ] end.
      apply xe_skipbreak_seq. apply xe_skipbreak_seq.
      apply (send_ret _ _ _ _ (sp_post a) f_ZSTD_decompressSequences_bodySplitLitBuffer); [reflexivity|].
      unfold sp_post. forward.
      assert (Hne: ~ (w_lo w = 0 /\ w_pos w = 0)).
      { intros [E1 E2]. rewrite E1, E2 in H0. discriminate. }
      destruct (xe_err_ret 20 true True ltac:(lia) eq_refl) as (Hr1 & Hr2 & _ & Hr4).
      destruct (H) as (_ & _ & _ & _ & _ & _ & Hout & Hmin).
      destruct (Hsa) as (_ & _ & Hlits & _ & _ & _ & Hnbp & _ & Hrep0 & _).
      destruct (Hb) as (Hos & _ & _ & _ & _ & _ & _ & _ & Hxr).
      assert (Hxpost: xpost a (err_code 20) (w_c w) (a_rep a)).
      { apply xpost_err; [exact Hr2|]. exact (xend_err a (g_t g) _ ph w H Hxinv Hid Hne). }
      Exists (err_code 20) (w_c w) (a_rep a).
      apply andp_right; [apply prop_right |].
      { split; [exact Hr1|]. split; [apply Hout|]. split; [exact Hrep0|].
        split; [apply (send_unch a ph (w_K w) (w_j w) (w_c w) Hout)|].
        split; [intros E; rewrite Hr2 in E; discriminate|].
        split.
        { intros Hv. destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hsm; [|exact I].
          intros Hlen. exfalso. destruct Hv as [Hc0 | [Hhv Hec]].
          - destruct (Hnbp ltac:(lia)) as (_ & Hc). unfold sp_cap in Hc. lia.
          - apply Hne. destruct (send_model a (g_t g) w cnt rep2 Hos Hnb Hid Hmin Hhv Hec Hsm Hlen) as (Hp & Hl & _).
            split; assumption. }
        split; [intros _; exact send_dec_err|].
        split; [apply Hout|]. split; [exact Hxpost | exact Hr4]. }
      replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      assert (Hbt: bytes_ok (sp_tail a))
        by (destruct Hlits as (Hbl & _); unfold sp_tail; apply Forall_sublist; exact Hbl).
      sep_apply (send_ss_free (a_gv a) (sp_s a) (sp_sst a) (w_pos w) (w_lo w) sLL sOF sML pLL pOF pML (w_crep w) (a_vss a)).
      sep_apply (sp_release a g Q Rin Hb).
      unfold sp_FR0.
      sep_apply (lsx a (g_xr g) (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a)))
        (offset_val (a_lb a) (sp_ob a)) (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr (sp_loc ph))) Hxa).
      unfold sp_N, sp_ob, sp_x. cancel.
    + forward. entailer!. destruct ((w_lo w =? 0) && (w_pos w =? 0))%bool eqn:E; [|contradiction].
      apply andb_prop in E as [E1 E2]. split; apply Z.eqb_eq; assumption.
  - intros [Hlo0 Hpos0].
    unfold seqstate_at. destruct (w_st w) as [[sLL sOF] sML] eqn:Hst. destruct (g_tp g) as [[pLL pOF] pML] eqn:Htp.
    Intros.
    freeze [0;1;2;3;4;6;7;8;9;10;11;12;13;14;16;17] FR.
    match goal with |- semax _ (PROPx _ (LOCALx ?L _)) _ _ =>
      forward;
      forward_loop (EX i: Z, PROPx [0 <= i <= 3] (LOCALx (temp _i__1 (Vint (Int.repr i)) :: L)
          (SEPx [FRZL FR; field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals (w_crep w)) (a_vss a);
                field_at Ews t_dctx (DOT _entropy DOT _rep)
                  (sublist 0 i (rep_vals (w_crep w)) ++ sublist i 3 (rep_vals (a_rep a))) (a_p a)])))%assert
        break: (PROPx [] (LOCALx L
          (SEPx [FRZL FR; field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals (w_crep w)) (a_vss a);
                field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (w_crep w)) (a_p a)])))
    end.
    + Exists 0. entailer!. unfold rep_vals. destruct (a_rep a) as [[r1 r2] r3].
      rewrite sublist_nil, app_nil_l, sublist_same by reflexivity. cancel.
    + Intros i. destruct (H) as (_ & _ & _ & _ & _ & Hcrep & _). forward_if.
      * assert (Hi: i = 0 \/ i = 1 \/ i = 2) by lia.
        destruct (w_crep w) as [[c1 c2] c3] eqn:Hc.
        forward.
        { entailer!. destruct Hi as [-> | [-> | ->]]; simpl; auto. }
        forward.
        forward. Exists (i+1). entailer!.
        apply derives_refl'. f_equal. clear H18. unfold rep_ok in Hcrep. unfold rep_vals.
        destruct (a_rep a) as [[r1 r2] r3].
        destruct Hi as [-> | [-> | ->]]; cbn; rewrite ?Int64.Z_mod_modulus_eq, ?Z.mod_small by rep_lia; reflexivity.
      * forward. entailer!. assert (i = 3) by lia. subst i.
        unfold rep_vals. destruct (w_crep w) as [[c1 c2] c3]. destruct (a_rep a) as [[r1 r2] r3].
        rewrite sublist_nil, app_nil_r, sublist_same by reflexivity. cancel.
    + thaw FR. unfold sp_end_R; cbn [RA_normal]. Exists (w_crep w).
      unfold sp_LAST, sp_lvars, sp_ptrs; cbn [app].
      replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (send_slast a g Q Rin ph w Hsa Hb Hid Hnb H) as Hsl.
      pose proof (xend_ok a (g_t g) (zbytes (sp_tail a) ++ g_xr g) ph w H Hxinv Hid Hlo0 Hpos0) as Hxlst.
      destruct (Hb) as (_ & _ & _ & _ & _ & _ & _ & Hxl & Hxr).
      sep_apply (send_ss_free (a_gv a) (sp_s a) (sp_sst a) (w_pos w) (w_lo w) sLL sOF sML pLL pOF pML (w_crep w) (a_vss a)).
      sep_apply (sp_release a g Q Rin Hb).
      entailer!.
Qed.

(* seg_last helpers *)
Ltac slast_lia := unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia.

Lemma slast_ctx (a: sa) : sa_ok a ->
  writable_share (oa_sh (a_o a)) /\ Zlength (sp_c0 a) = sp_N a /\ sp_N a <= 2 ^ 63 - 1 /\ 0 <= sp_d a /\
  0 <= sp_cap a /\ sp_d a + sp_cap a <= sp_N a /\
  bytes_ok (a_lits a) /\ LITBUFFEREXTRASIZE < sp_n a /\ sp_n a <= a_bsm a /\ a_bsm a <= ZSTD_BLOCKSIZE_MAX /\
  sp_d a <= a_lb a /\ sp_lim a + WILDCOPY_OVERLENGTH <= sp_d a + sp_cap a /\
  sublist (a_lb a) (sp_lim a) (sp_c0 a) = zbytes (sublist 0 (sp_n a - LITBUFFEREXTRASIZE) (a_lits a)).
Proof.
  intros (Ho & _ & Hl & Hb & Hn & _).
  destruct Ho as (Hsh & HcN & HN & Hd & Hcap & HdN).
  destruct Hl as (Hbl & Hn0 & Hgt & Hlb & Hend & Hsub).
  unfold sp_c0, sp_N, sp_d, sp_cap, sp_lim, sp_n in *.
  repeat (split; [assumption || lia|]). exact Hsub.
Qed.

Lemma slast_zbytes_cells (l: list Z) : bytes_ok l -> byte_cells (zbytes l).
Proof.
  unfold bytes_ok, byte_cells. intros H. induction H as [|z l Hz Hl IH]; simpl; [constructor|].
  constructor; [|exact IH]. exists z. split; [exact Hz | reflexivity].
Qed.

Lemma slast_bytes_of (l0: list val) : Forall is_byte_val l0 -> exists x, l0 = zbytes x /\ bytes_ok x.
Proof.
  induction 1 as [|v l1 [z [Hz ->]] _ [x [-> Hx]]].
  - exists nil. split; [reflexivity | constructor].
  - exists (z :: x). split; [reflexivity | constructor; [unfold is_byte; lia | exact Hx]].
Qed.

Lemma slast_zbytes_byte_vals (l: list Z) : bytes_ok l -> Forall is_byte_val (zbytes l).
Proof.
  unfold bytes_ok. intros H. induction H as [|z l Hz Hl IH]; simpl; [constructor|].
  constructor; [|exact IH]. exists z. split; [exact Hz | reflexivity].
Qed.

Lemma slast_put_len (c: list val) (i: Z) (v: list val) :
  0 <= i -> i + Zlength v <= Zlength c -> Zlength (put c i v) = Zlength c.
Proof. intros. unfold put. list_solve. Qed.

Lemma slast_put_sub (c: list val) (lo i: Z) (v: list val) :
  0 <= lo <= i -> i + Zlength v <= Zlength c ->
  sublist lo (i + Zlength v) (put c i v) = sublist lo i c ++ v.
Proof. intros. unfold put. list_solve. Qed.

Lemma slast_put_cells (c: list val) (i: Z) (v: list val) :
  byte_cells c -> byte_cells v -> 0 <= i -> i + Zlength v <= Zlength c -> byte_cells (put c i v).
Proof.
  intros Hc Hv Hi Hl. unfold byte_cells, put in *.
  apply Forall_app; split; [apply Forall_sublist; exact Hc|].
  apply Forall_app; split; [exact Hv | apply Forall_sublist; exact Hc].
Qed.

Lemma slast_put_unch (oc c v: list val) (lo hi hi' i: Z) :
  unchanged_outside oc c lo hi -> Zlength c = Zlength oc -> 0 <= i -> i + Zlength v <= Zlength c ->
  lo <= i -> i + Zlength v <= hi' -> hi <= hi' -> unchanged_outside oc (put c i v) lo hi'.
Proof.
  intros Hun Hl H1 H2 H3 H4 H5 k Hk Hn.
  rewrite ecl_Znth_put_out by lia. apply Hun; lia.
Qed.

Lemma slast_unch_mono (oc c: list val) (lo hi hi': Z) :
  unchanged_outside oc c lo hi -> hi <= hi' -> unchanged_outside oc c lo hi'.
Proof. intros Hun Hh k Hk Hn. apply Hun; lia. Qed.

Lemma slast_outok_len (a: sa) (ph: bool) (K j: Z) (c: list val) :
  sp_outok a ph K j c -> 0 <= K <= sp_cap a /\ Zlength c = sp_N a /\
  (if ph then 0 <= j <= sp_n a - LITBUFFEREXTRASIZE else sp_n a - LITBUFFEREXTRASIZE <= j <= sp_n a).
Proof. intros (HK & HN & Hu & _). split; [exact HK|]. split; [exact HN|]. destruct ph; apply Hu. Qed.

Lemma slast_outok_unch (a: sa) (ph: bool) (K j: Z) (c: list val) :
  sp_outok a ph K j c -> unchanged_outside (sp_c0 a) c (sp_d a) (sp_d a + Z.min (sp_cap a) (K + WILDCOPY_OVERLENGTH)).
Proof.
  intros (HK & _ & Hu & _). destruct ph; destruct Hu as (_ & Hu); [|exact Hu].
  eapply slast_unch_mono; [exact Hu | lia].
Qed.

(* the PROP part of sp_post *)
Definition slast_P (a: sa) (r: Z) (oc': list val) (rep': Z * Z * Z) : Prop :=
  let o := a_o a in let h := a_h a in
  fold_right and True
   [0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o; rep_ok rep';
    unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
    is_error_code r = false ->
      r <= oa_cap o /\
      unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
      (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
       (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= a_bsm a /\ ext_far (oa_d o) (oa_cap o) (a_bsm a) (hc_ext h))) ->
         exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
    oa_cap o = 0 \/
    (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
     ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
    match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
    | Some (cnt, rep2) =>
        Zlength cnt <= a_bsm a ->
        (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
         rep' = rep2) \/
        (is_error_code r = true /\ oa_cap o < Zlength cnt)
    | None => True
    end;
    is_error_code r = true -> dec_err r;
    byte_cells (oa_c o) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext h) -> byte_cells oc'].

(* the capacity error (either check) *)
Lemma slast_err (a: sa) (ph: bool) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> slast a ph w rep' -> sp_cap a < w_K w + (sp_n a - w_j w) ->
  slast_P a (err_code 70) (w_c w) rep'.
Proof.
  intros Hsa (Hrep & Hout & _ & Hm) Hlt.
  destruct (xe_err_ret 70 true True ltac:(lia) eq_refl) as (Hr1 & Hr2 & _ & _).
  destruct (es_neg 70 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & _ & Hde).
  pose proof (slast_outok_len a ph _ _ _ Hout) as (HK & HN & Hj).
  destruct (slast_ctx a Hsa) as (_ & _ & _ & _ & _ & _ & _ & Hgt & _).
  assert (Hj': 0 <= w_j w <= sp_n a) by (destruct ph; unfold LITBUFFEREXTRASIZE in *; lia).
  unfold slast_P; cbn [fold_right].
  split; [exact Hr1|]. split; [exact HN|]. split; [exact Hrep|].
  split. { eapply slast_unch_mono; [apply (slast_outok_unch a ph _ _ _ Hout) | unfold sp_d, sp_cap; lia]. }
  split. { intros E. rewrite Hr2 in E. discriminate. }
  split.
  { intros Hv. destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hsm; [|exact I].
    intros Hlen. right. split; [exact Hr2|].
    destruct (Hm Hv cnt rep2 eq_refl Hlen) as (blk & Hbl & Hc & _).
    subst cnt. rewrite Zlength_app, Zlength_skipn. unfold sp_cap, sp_n in *.
    rewrite (Z.max_r 0 (w_j w)), Z.max_r by lia. lia. }
  split; [intros _; exact Hde|].
  split; [apply Hout | exact I].
Qed.


Lemma slast_bytes_skipn (l: list Z) (k: nat) : bytes_ok l -> bytes_ok (skipn k l).
Proof.
  unfold bytes_ok. intros H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. apply H.
Qed.

(* the last literals from litExtraBuffer: the success post *)
Lemma slast_ok (a: sa) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> slast a false w rep' -> w_K w + (sp_n a - w_j w) <= sp_cap a ->
  slast_P a (w_K w + (sp_n a - w_j w))
    (put (w_c w) (sp_d a + w_K w) (zbytes (skipn (Z.to_nat (w_j w)) (a_lits a)))) rep'.
Proof.
  intros Hsa (Hrep & Hout & _ & Hm) Hle.
  destruct (slast_ctx a Hsa) as (Hsh & Hc0 & HN32 & Hd & Hcap & HdN & Hbo & Hgt & Hnb & Hbm & Hlb & Hlim & Hsub).
  pose proof (slast_outok_len a false _ _ _ Hout) as (HK & HN & Hj). cbv iota in Hj.
  pose proof (slast_outok_unch a false _ _ _ Hout) as Hun.
  destruct Hout as (_ & _ & _ & Hdef & Hcells).
  set (bs := zbytes (skipn (Z.to_nat (w_j w)) (a_lits a))).
  assert (Hbs: Zlength bs = sp_n a - w_j w).
  { unfold bs. rewrite Zlength_map, Zlength_skipn. unfold sp_n in *. rewrite (Z.max_r 0 (w_j w)), Z.max_r by lia. lia. }
  set (r := w_K w + (sp_n a - w_j w)).
  assert (Er: r = w_K w + (sp_n a - w_j w)) by reflexivity.
  assert (Hne: is_error_code r = false).
  { unfold is_error_code. apply Z.ltb_ge. unfold r, sp_cap, sp_N in *. lia. }
  assert (Hpl: Zlength (put (w_c w) (sp_d a + w_K w) bs) = sp_N a) by (rewrite slast_put_len; lia).
  assert (Hsub2: sublist (sp_d a) (sp_d a + r) (put (w_c w) (sp_d a + w_K w) bs) =
                 sublist (sp_d a) (sp_d a + w_K w) (w_c w) ++ bs).
  { replace (sp_d a + r) with (sp_d a + w_K w + Zlength bs) by (unfold r; lia).
    apply slast_put_sub; lia. }
  unfold slast_P; cbn [fold_right]. fold (sp_d a) (sp_cap a) (sp_N a) (sp_c0 a).
  split; [unfold r, sp_cap, sp_N in *; rep_lia|].
  split; [exact Hpl|]. split; [exact Hrep|].
  split. { eapply slast_put_unch; [exact Hun | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia]. }
  split.
  { intros _. split; [lia|]. split.
    { eapply slast_put_unch; [exact Hun | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia]. }
    intros Hh He.
    assert (Hfb: Forall is_byte_val (sublist (sp_d a) (sp_d a + w_K w) (w_c w))) by exact (proj1 Hdef).
    destruct (slast_bytes_of _ Hfb) as (blk0 & Hb0 & Hbo0).
    exists (blk0 ++ skipn (Z.to_nat (w_j w)) (a_lits a)). rewrite Hsub2, Hb0, map_app. split; [reflexivity|].
    apply Forall_app; split; [exact Hbo0 | apply slast_bytes_skipn; exact Hbo]. }
  split.
  { intros Hv. destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hsm; [|exact I].
    intros Hlen. left.
    destruct (Hm Hv cnt rep2 eq_refl Hlen) as (blk & Hbl & Hc & Hr & Hby).
    assert (Hcl: Zlength cnt = r).
    { rewrite Hc, Zlength_app, Zlength_skipn. unfold r, sp_n in *. rewrite (Z.max_r 0 (w_j w)), Z.max_r by lia. lia. }
    split; [exact Hne|]. split; [lia|]. split; [|symmetry; exact Hr].
    rewrite Hsub2, Hby by lia. rewrite Hc, map_app. reflexivity. }
  split. { intros E. rewrite Hne in E. discriminate. }
  split; [|exact I].
  intros B1 B2 B3. apply slast_put_cells; [apply Hcells; assumption | | lia | lia].
  unfold bs. apply slast_zbytes_cells, slast_bytes_skipn. exact Hbo.
Qed.

(* the state after the split head's copy (memmove) and the switch to litExtraBuffer *)
Definition slast_w (a: sa) (w: sw) : sw :=
  {| w_id := w_id w; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w; w_crep := w_crep w;
     w_K := w_K w + (sp_lim a - (a_lb a + w_j w)); w_j := sp_n a - LITBUFFEREXTRASIZE;
     w_c := put (w_c w) (sp_d a + w_K w) (sublist (a_lb a + w_j w) (sp_lim a) (w_c w)) |}.

Lemma slast_switch (a: sa) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> sp_pending a -> slast a true w rep' ->
  w_K w + (sp_lim a - (a_lb a + w_j w)) <= sp_cap a ->
  slast a false (slast_w a w) rep'.
Proof.
  intros Hsa Hpend (Hrep & Hout & Hnb0 & Hm) Hle.
  destruct (slast_ctx a Hsa) as (Hsh & Hc0 & HN32 & Hd & Hcap & HdN & Hbo & Hgt & Hnb & Hbm & Hlb & Hlim & Hsub).
  pose proof (slast_outok_len a true _ _ _ Hout) as (HK & HN & Hj). cbv iota in Hj.
  pose proof (slast_outok_unch a true _ _ _ Hout) as Hun'.
  destruct Hout as (_ & _ & (_ & Hun) & Hdef & Hcells).
  assert (Elim: sp_lim a = a_lb a + (sp_n a - LITBUFFEREXTRASIZE)) by reflexivity.
  set (v := sublist (a_lb a + w_j w) (sp_lim a) (w_c w)).
  assert (Hv: Zlength v = sp_lim a - (a_lb a + w_j w)) by (unfold v; rewrite Zlength_sublist; slast_lia).
  (* the head bytes at or after max(op, litPtr) are the original ones *)
  assert (HU: forall i, Z.max (sp_d a + w_K w) (a_lb a + w_j w) <= i < sp_lim a -> Znth i (w_c w) = Znth i (sp_c0 a)).
  { intros i Hi. apply Hun; [slast_lia|]. slast_lia. }
  assert (HC0: Forall is_byte_val (sublist (a_lb a) (sp_lim a) (sp_c0 a))).
  { rewrite Hsub. apply slast_zbytes_byte_vals. apply Forall_sublist. exact Hbo. }
  unfold slast, slast_w; cbn [w_K w_j w_c]. fold v.
  split; [exact Hrep|].
  split.
  { unfold sp_outok. split; [slast_lia|]. split; [rewrite slast_put_len; slast_lia|]. split.
    { split; [slast_lia|]. eapply slast_put_unch; [exact Hun' | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia | slast_lia]. }
    split.
    { assert (Hv0: Forall is_byte_val v).
      { unfold v. apply (xd_sub _ (a_lb a) (sp_lim a + WILDCOPY_OVERLENGTH)); [slast_lia | slast_lia | slast_lia |].
        exact (proj2 (proj2 (proj2 Hdef))). }
      destruct (xd_put (w_c w) v (sp_d a + w_K w)) as [Hp1 Hp2]; [slast_lia | slast_lia | exact Hv0 |].
      rewrite Hv in Hp2.
      apply (sp_dfd_step a (w_K w) (sp_lim a - (a_lb a + w_j w)) (w_c w)); auto; try slast_lia.
      - rewrite slast_put_len; slast_lia.
      - apply xd_rng_Forall; [slast_lia | rewrite slast_put_len; slast_lia | exact Hp2]. }
    intros B1 B2 B3. apply slast_put_cells; [apply Hcells; assumption | | slast_lia | slast_lia].
    unfold v, byte_cells. apply Forall_sublist. apply Hcells; assumption. }
  split; [exact Hnb0|].
  intros Hvw cnt rep2 Hsm Hlen.
  destruct (Hm Hvw cnt rep2 Hsm Hlen) as (blk & Hbl & Hc & Hr & Hby).
  set (m := sp_n a - LITBUFFEREXTRASIZE).
  assert (Em: m = sp_n a - LITBUFFEREXTRASIZE) by reflexivity.
  exists (blk ++ sublist (w_j w) m (a_lits a)).
  assert (Hcl: Zlength cnt = w_K w + (sp_n a - w_j w)).
  { rewrite Hc, Zlength_app, Zlength_skipn. unfold sp_n in *. rewrite (Z.max_r 0 (w_j w)), Z.max_r by slast_lia. slast_lia. }
  split. { rewrite Zlength_app, Zlength_sublist by (unfold m, sp_n in *; slast_lia). unfold m. slast_lia. }
  split.
  { rewrite Hc, <- app_assoc. f_equal. unfold m, sp_n in *.
    rewrite <- !sublist_skip by slast_lia. rewrite <- sublist_split by slast_lia. reflexivity. }
  split; [exact Hr|].
  intros Hcap'.
  assert (Hfar: sp_d a + w_K w + WILDCOPY_OVERLENGTH <= a_lb a + w_j w).
  { destruct Hpend as (Hp & _). unfold sp_n in *. slast_lia. }
  assert (Hveq: v = zbytes (sublist (w_j w) m (a_lits a))).
  { assert (E1: v = sublist (a_lb a + w_j w) (sp_lim a) (sp_c0 a)).
    { unfold v. apply Znth_eq_ext; [rewrite !Zlength_sublist; slast_lia|].
      intros i Hi. rewrite Zlength_sublist in Hi by slast_lia. rewrite !Znth_sublist by slast_lia.
      apply HU. unfold WILDCOPY_OVERLENGTH in *. slast_lia. }
    rewrite E1. replace (sublist (a_lb a + w_j w) (sp_lim a) (sp_c0 a))
      with (sublist (w_j w) m (sublist (a_lb a) (sp_lim a) (sp_c0 a))) by (rewrite sublist_sublist by (unfold m; slast_lia); f_equal; slast_lia).
    rewrite Hsub, sublist_map, sublist_sublist by (unfold m; slast_lia).
    f_equal. f_equal; slast_lia. }
  replace (sp_d a + (w_K w + (sp_lim a - (a_lb a + w_j w)))) with (sp_d a + w_K w + Zlength v) by slast_lia.
  rewrite slast_put_sub by slast_lia. rewrite Hby by slast_lia. rewrite Hveq, map_app. reflexivity.
Qed.


(* a return under a ret_assert whose return part is the function's (as seg_end's send_ret) *)
Lemma slast_ret {Espec: OracleKind} (Delta: tycontext) (P: environ -> mpred) (e: option expr) (R: ret_assert)
    (Pf: environ -> mpred) (f: function) :
  RA_return R = RA_return (frame_ret_assert (function_body_ret_assert tulong Pf) (stackframe_of f)) ->
  semax Delta P (Sreturn e)
    (overridePost (RA_normal R) (frame_ret_assert (function_body_ret_assert tulong Pf) (stackframe_of f))) ->
  semax Delta P (Sreturn e) R.
Proof.
  intros HR H. destruct R as [Rn Rb Rc Rr]. cbn in HR. subst Rr.
  eapply semax_post; [| | | | exact H].
  all: unfold overridePost, frame_ret_assert, function_body_ret_assert; cbn [RA_normal RA_break RA_continue RA_return].
  - apply andp_left2, derives_refl.
  - rewrite FF_sepcon. apply andp_left2, FF_left.
  - rewrite FF_sepcon. apply andp_left2, FF_left.
  - intros vl. apply andp_left2, derives_refl.
Qed.

Lemma slast_lit_scratch (p lp lb lbe: val) (ls loc: val) (v: list val) :
  byte_cells v ->
  field_at Ews t_dctx (DOT _litPtr) lp p * field_at Ews t_dctx (DOT _litSize) ls p *
  field_at Ews t_dctx (DOT _litBuffer) lb p * field_at Ews t_dctx (DOT _litBufferEnd) lbe p *
  field_at Ews t_dctx (DOT _litBufferLocation) loc p *
  data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra p) |-- lit_scratch p.
Proof.
  intros Hx. unfold lit_scratch, lit_extra_bytes. rewrite <- litextra_data_at.
  Exists v. entailer!.
Qed.

Lemma slast_extra_cells (a: sa) (xr: list val) : sa_ok a -> byte_cells xr -> byte_cells (zbytes (sp_tail a) ++ xr).
Proof.
  intros Hsa Hx. destruct (slast_ctx a Hsa) as (_ & _ & _ & _ & _ & _ & Hbo & _).
  apply Forall_app. split; [|exact Hx]. apply slast_zbytes_cells. unfold sp_tail. apply Forall_sublist. exact Hbo.
Qed.

Ltac slast_fin HP :=
  cbv [slast_P fold_right] in HP; destruct HP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _);
  refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 _)))))))).

Lemma slast_wvp (sh: share) (N i: Z) (c: list val) (p: val) :
  readable_share sh -> 0 <= i <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros Hr Hi HN. sep_apply data_at_data_at_. rewrite data_at__memory_block. Intros. simpl sizeof.
  rewrite Z.mul_1_l, Z.max_r by lia.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma slast_teq (q: val) : isptr q -> weak_valid_pointer q |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros. destruct q; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq.
Qed.

Ltac slast_wvp_find tac := first [ tac
  | apply sepcon_weak_valid_pointer1; slast_wvp_find tac | apply sepcon_weak_valid_pointer2; slast_wvp_find tac ].

(* the memcpy: the source range of litExtraBuffer and the destination range of the output array, and back *)
Lemma slast_frame (sho: share) (N K L j0: Z) (c: list val) (ob: val) (v: list val) (ep: val) (bs: list val) :
  Zlength c = N -> Zlength v = LITEXTRA_N -> 0 <= K -> 0 <= L -> K + L <= N -> 0 <= j0 -> j0 + L <= LITEXTRA_N ->
  sublist j0 (j0 + L) v = bs ->
  exists F: mpred,
   (data_at sho (tarray tuchar N) c ob * data_at Ews (tarray tuchar LITEXTRA_N) v ep |--
     data_at Ews (tarray tuchar L) bs (offset_val j0 ep) * data_at_ sho (tarray tuchar L) (offset_val K ob) * F) /\
   (data_at Ews (tarray tuchar L) bs (offset_val j0 ep) * data_at sho (tarray tuchar L) bs (offset_val K ob) * F |--
     data_at sho (tarray tuchar N) (put c K bs) ob * data_at Ews (tarray tuchar LITEXTRA_N) v ep).
Proof.
  intros Hc Hv HK HL HKL Hj0 HjL Hbs.
  assert (Hbl: Zlength bs = L) by (subst bs; rewrite Zlength_sublist; lia).
  exists (!! (field_compatible (tarray tuchar N) [] ob /\ field_compatible (tarray tuchar LITEXTRA_N) [] ep) &&
    ((data_at sho (tarray tuchar K) (sublist 0 K c) ob *
      data_at sho (tarray tuchar (N - (K + L))) (sublist (K + L) N c) (offset_val (K + L) ob)) *
     (data_at Ews (tarray tuchar j0) (sublist 0 j0 v) ep *
      data_at Ews (tarray tuchar (LITEXTRA_N - (j0 + L))) (sublist (j0 + L) LITEXTRA_N v) (offset_val (j0 + L) ep)))).
  split.
  - assert_PROP (field_compatible (tarray tuchar N) [] ob /\ field_compatible (tarray tuchar LITEXTRA_N) [] ep)
      as HF by entailer!. destruct HF as [F1 F2].
    rewrite (xe_mid sho ob c N K L) by auto. rewrite (xe_mid Ews ep v LITEXTRA_N j0 L) by auto.
    rewrite Hbs. sep_apply (data_at_data_at_ sho (tarray tuchar L) (sublist K (K + L) c) (offset_val K ob)).
    entailer!.
  - Intros. rewrite (xe_mid Ews ep v LITEXTRA_N j0 L) by (auto; tauto). rewrite Hbs.
    unfold put. rewrite Hbl, Hc. rewrite <- (xe_mid_join sho ob c bs N K L) by (auto; tauto).
    cancel.
Qed.

Lemma slast_src_eq (a: sa) (xr: list val) (j: Z) :
  sa_ok a -> sp_n a - LITBUFFEREXTRASIZE <= j <= sp_n a ->
  sublist (j - (sp_n a - LITBUFFEREXTRASIZE)) (j - (sp_n a - LITBUFFEREXTRASIZE) + (sp_n a - j))
    (zbytes (sp_tail a) ++ xr) = zbytes (skipn (Z.to_nat j) (a_lits a)).
Proof.
  intros Hsa Hj. destruct (slast_ctx a Hsa) as (_ & _ & _ & _ & _ & _ & _ & Hgt & _).
  assert (Ht: Zlength (sp_tail a) = LITBUFFEREXTRASIZE) by (unfold sp_tail, sp_n in *; rewrite Zlength_sublist; slast_lia).
  rewrite sublist_app1 by (rewrite ?Zlength_map; slast_lia).
  rewrite sublist_map. unfold sp_tail, sp_n in *. rewrite sublist_sublist by slast_lia.
  rewrite <- sublist_skip by slast_lia. f_equal. f_equal; slast_lia.
Qed.

Lemma slast_le_eq (p: val) : isptr (lit_extra p) -> lit_extra p = offset_val 30380 p.
Proof.
  unfold lit_extra, field_address. intros H. destruct (field_compatible_dec _ _ _); [reflexivity | contradiction].
Qed.

Lemma slast_lbe_val (p: val) : isptr (lit_extra p) ->
  force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
    (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer p) (Vint (Int.shl (Int.repr 1) (Int.repr 16)))) =
  offset_val LITBUFFEREXTRASIZE (lit_extra p).
Proof.
  intros H. rewrite (slast_le_eq p H). rewrite (slast_le_eq p H) in H.
  destruct p; try contradiction. reflexivity.
Qed.

Definition slast_head : statement := match sp_last with Ssequence h _ => h | _ => Sskip end.
Definition slast_tail : statement := match sp_last with Ssequence _ t => t | _ => Sskip end.
Lemma slast_last_eq : sp_last = Ssequence slast_head slast_tail.
Proof. reflexivity. Qed.

Lemma slast_tail_ok {Espec: OracleKind} (a: sa) (w: sw) (rep': Z * Z * Z) (xr: list val) :
  sa_ok a -> sp_pending a -> sa_x a xr ->
  semax sp_Delta (sp_LAST a false w rep' xr) slast_tail (sp_R a).
Proof.
  intros Hsa Hpend Hxa.
  unfold sp_LAST, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc; cbn [app]. Intros.
  rename H2 into Hxl.
  unfold sp_Delta. cbv [slast_tail sp_last]. simplify_func_tycontext. abbreviate_semax.
  forward.
  assert_PROP (isptr (lit_extra (a_p a)) /\ isptr (sp_ob a)) as Hptrs by entailer!. destruct Hptrs as [Hle Hob].
  forward.
  { entailer!; try apply prop_right; apply cp_sameblock; auto. }
  rewrite xe_sub_pp by auto.
  replace (LITBUFFEREXTRASIZE - (w_j w - (sp_n a - LITBUFFEREXTRASIZE))) with (sp_n a - w_j w) by lia.
  pose proof H as (Hrep & Hout & Hnb0 & Hm).
  pose proof (slast_outok_len a false _ _ _ Hout) as (HK & HN & Hj). cbv iota in Hj.
  destruct (slast_ctx a Hsa) as (Hsh & Hc0 & HN32 & Hd & Hcap & HdN & Hbo & Hgt & Hnb & Hbm & Hlb & Hlim & Hsub).
  assert (HN0: 0 < sp_N a) by (unfold sp_lim in Hlim; slast_lia).
  apply -> seq_assoc. apply xe_skipbreak_seq. apply -> seq_assoc.
  apply (es_dw _ _ (sp_n a - w_j w <= sp_cap a - w_K w)).
  - forward_if.
    { entailer!; try apply prop_right; apply cp_sameblock; auto. }
    + rewrite xe_gt_diff in H2 by (auto; unfold sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE in *; rep_lia).
      destruct (zlt _ _) as [Hlt|_] in H2; [|inversion H2].
      xe_err_prefix.
      apply (slast_ret _ _ _ _ (sp_post a) f_ZSTD_decompressSequences_bodySplitLitBuffer); [reflexivity|].
      unfold sp_post. forward.
      Exists (err_code 70) (w_c w) rep'.
      apply andp_right.
      { apply prop_right. pose proof (slast_err a false w rep' Hsa H ltac:(lia)) as HP. slast_fin HP.
        split; [exact (xfin_terr a _ w rep' Hsa H Hxl ltac:(lia)) |].
        apply (xe_err_ret 70 true True ltac:(lia) eq_refl). }
      sep_apply (data_at_data_at_ Tsh (tptr tuchar)). unfold sp_FR0.
      sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
        (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr LOC_NOT_IN_DST)) Hxa).
      unfold sp_N, sp_ob, sp_x. cancel.
    + forward. entailer!.
      rewrite xe_gt_diff in H2 by (auto; unfold sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE in *; rep_lia).
      destruct (zlt _ _) as [Hlt|Hge] in H2; [inversion H2|]. lia.
  - intros Hfit.
    apply semax_if_seq. forward_if.
    { eapply derives_trans; [| apply slast_teq; rewrite isptr_offset_val; exact Hob].
      slast_wvp_find ltac:(apply (slast_wvp (oa_sh (a_o a)) (sp_N a)); [apply writable_readable; auto | slast_lia | slast_lia]). }
    2: { exfalso. revert H2. clear - Hob. destruct (sp_ob a); try contradiction. discriminate. }
    forward.
    assert (Hfr := slast_frame (oa_sh (a_o a)) (sp_N a) (sp_d a + w_K w) (sp_n a - w_j w)
      (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (w_c w) (sp_ob a) (zbytes (sp_tail a) ++ xr) (lit_extra (a_p a))
      (zbytes (skipn (Z.to_nat (w_j w)) (a_lits a)))).
    destruct Hfr as (F & Hsplit & Hjoin);
      [exact HN | rewrite Zlength_app, Zlength_map, H0; unfold sp_tail, LITEXTRA_N, LITBUFFEREXTRASIZE, sp_n in *; rewrite Zlength_sublist; slast_lia
      | lia | lia | lia | slast_lia | unfold LITEXTRA_N, LITBUFFEREXTRASIZE; slast_lia | apply slast_src_eq; auto |].
    sep_apply Hsplit.
    forward_call (Ews, oa_sh (a_o a), offset_val (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) (lit_extra (a_p a)),
      offset_val (sp_d a + w_K w) (sp_ob a),
      existT (fun t => reptype t) (tarray tuchar (sp_n a - w_j w)) (zbytes (skipn (Z.to_nat (w_j w)) (a_lits a)))).
    { simpl projT1. simpl projT2. cancel. }
    { cbn [projT1 projT2]. split; [simpl; rep_lia |]. apply memcpy_ok_zbytes; [| apply slast_bytes_skipn; exact Hbo].
      rewrite Zlength_skipn. unfold sp_n in *. rewrite (Z.max_r 0 (w_j w)), Z.max_r by lia. lia. }
    simpl projT1. simpl projT2.
    sep_apply Hjoin. Intros.
    forward. rewrite es_add by auto.
    apply xe_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
    apply (slast_ret _ _ _ _ (sp_post a) f_ZSTD_decompressSequences_bodySplitLitBuffer); [reflexivity|].
    unfold sp_post. forward.
    { entailer!; try apply prop_right; apply cp_sameblock; auto. }
    Exists (w_K w + (sp_n a - w_j w)) (put (w_c w) (sp_d a + w_K w) (zbytes (skipn (Z.to_nat (w_j w)) (a_lits a)))) rep'.
    apply andp_right.
    { apply prop_right. pose proof (slast_ok a w rep' Hsa H ltac:(lia)) as HP. slast_fin HP.
      split; [exact (xfin_ok a _ w rep' Hsa (proj1 (proj2 (proj2 Hxa))) H Hxl ltac:(lia)) |].
      rewrite cp_sub_pp by auto. f_equal. f_equal. lia. }
    sep_apply (data_at_data_at_ Tsh (tptr tuchar)). unfold sp_FR0.
    sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
      (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr LOC_NOT_IN_DST)) Hxa).
    unfold sp_N, sp_ob, sp_x. cancel.
Qed.

Lemma slast_head_ok {Espec: OracleKind} (a: sa) (ph: bool) (w: sw) (rep': Z * Z * Z) (xr: list val) :
  sa_ok a -> sp_pending a -> sa_x a xr ->
  semax sp_Delta (sp_LAST a ph w rep' xr) slast_head
    (overridePost (EX w': sw, sp_LAST a false w' rep' xr) (sp_R a)).
Proof.
  intros Hsa Hpend Hxa.
  unfold sp_LAST, sp_lvars, sp_ptrs, sp_lp, sp_lbe, sp_loc; cbn [app]. Intros.
  rename H2 into Hxl.
  unfold sp_Delta. cbv [slast_head sp_last]. simplify_func_tycontext. abbreviate_semax.
  forward.
  destruct ph.
  - forward_if.
    2: { exfalso. apply H2. reflexivity. }
    assert_PROP (isptr (lit_extra (a_p a)) /\ isptr (sp_ob a)) as Hptrs by entailer!. destruct Hptrs as [Hle Hob].
    forward. forward. { entailer!; try apply prop_right; apply cp_sameblock; auto. }
    rewrite xe_sub_pp by auto.
    pose proof H as (Hrep & Hout & Hnb0 & Hm).
    pose proof (slast_outok_len a true _ _ _ Hout) as (HK & HN & Hj). cbv iota in Hj.
    destruct (slast_ctx a Hsa) as (Hsh & Hc0 & HN32 & Hd & Hcap & HdN & Hbo & Hgt & Hnb & Hbm & Hlb & Hlim & Hsub).
    assert (Elim: sp_lim a = a_lb a + (sp_n a - LITBUFFEREXTRASIZE)) by reflexivity.
    assert (HN0: 0 < sp_N a) by slast_lia.
    apply xe_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
    apply (es_dw _ _ (sp_lim a - (a_lb a + w_j w) <= sp_cap a - w_K w)).
    + forward_if.
      { entailer!; try apply prop_right; apply cp_sameblock; auto. }
      * rewrite xe_gt_diff in H3 by (auto; unfold sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE in *; rep_lia).
        destruct (zlt _ _) as [Hlt|_] in H3; [|inversion H3].
        xe_err_prefix.
        apply (slast_ret _ _ _ _ (sp_post a) f_ZSTD_decompressSequences_bodySplitLitBuffer); [reflexivity|].
        unfold sp_post. forward.
        Exists (err_code 70) (w_c w) rep'.
        apply andp_right.
        { apply prop_right. pose proof (slast_err a true w rep' Hsa H ltac:(slast_lia)) as HP. slast_fin HP.
          split; [exact (xfin_herr a _ w rep' Hsa H Hxl ltac:(slast_lia)) |].
          apply (xe_err_ret 70 true True ltac:(lia) eq_refl). }
        sep_apply (data_at_data_at_ Tsh (tptr tuchar)). unfold sp_FR0.
        sep_apply (lsx a xr (offset_val (a_lb a) (sp_ob a)) (Vlong (Int64.repr (sp_n a))) (offset_val (a_lb a) (sp_ob a))
          (offset_val (sp_lim a) (sp_ob a)) (Vint (Int.repr LOC_SPLIT)) Hxa).
        unfold sp_N, sp_ob, sp_x. cancel.
      * forward. entailer!.
        rewrite xe_gt_diff in H3 by (auto; unfold sp_cap, sp_N, sp_n, LITBUFFEREXTRASIZE in *; rep_lia).
        destruct (zlt _ _) as [Hlt|Hge] in H3; [inversion H3|]. lia.
    + intros Hfit.
      apply semax_if_seq. forward_if.
      { eapply derives_trans; [| apply slast_teq; rewrite isptr_offset_val; exact Hob].
        slast_wvp_find ltac:(apply (slast_wvp (oa_sh (a_o a)) (sp_N a)); [apply writable_readable; auto | slast_lia | slast_lia]). }
      2: { exfalso. revert H3. clear - Hob. destruct (sp_ob a); try contradiction. discriminate. }
      forward.
      assert (Xmm: Forall byte_val (sublist (a_lb a + w_j w) (a_lb a + w_j w + (sp_lim a - (a_lb a + w_j w))) (w_c w))).
      { apply xd_bv. destruct Hout as (_ & _ & _ & Hdf & _).
        apply (xd_sub _ (a_lb a) (sp_lim a + WILDCOPY_OVERLENGTH)); [slast_lia | slast_lia | slast_lia |].
        exact (proj2 (proj2 (proj2 Hdf))). }
      forward_call (mm_within (oa_sh (a_o a)) (sp_ob a) (sp_N a) (w_c w) (a_lb a + w_j w) (sp_d a + w_K w)
        (sp_lim a - (a_lb a + w_j w))).
      { unfold mm_ok. split; [exact Hsh|]. repeat split; first [slast_lia | rep_lia | exact Xmm]. }
      cbn [mm_post]. rewrite <- HN. rewrite es_mm_put by slast_lia. rewrite HN.
      forward. rewrite es_add by auto.
      forward.
      apply -> seq_assoc. apply -> seq_assoc. apply semax_if_seq. forward_if.
      2: { exfalso. revert H4. vm_compute. discriminate. }
      forward. apply semax_if_seq. forward_if.
      { exfalso. revert H4. vm_compute. discriminate. }
      apply semax_if_seq. forward_if.
      2: { exfalso. revert H5. vm_compute. discriminate. }
      forward. forward. forward. forward.
      rewrite slast_lbe_val by auto.
      assert (Hsw := slast_switch a w rep' Hsa Hpend H ltac:(lia)).
      assert (Hxsw := xfin_switch a _ w rep' Hsa Hpend H Hxl ltac:(lia)).
      replace (a_lb a + w_j w + (sp_lim a - (a_lb a + w_j w))) with (sp_lim a) by lia.
      destruct (sp_R a). cbv iota beta.
      Exists (slast_w a w). unfold slast_w; cbn [w_K w_j w_c].
      entailer!.
      * f_equal. lia.
      * rewrite Z.sub_diag, isptr_offset_val_zero by auto. rewrite (slast_le_eq (a_p a) Hle). apply derives_refl.
  - forward_if.
    { exfalso. revert H2. vm_compute. discriminate. }
    forward. destruct (sp_R a). cbv iota beta.
    Exists w. entailer!.
Qed.

(* the last literals (still split: memmove the head's rest, switch; then memcpy from litExtraBuffer) and the
   return *)
Lemma seg_last {Espec: OracleKind} (a: sa) (ph: bool) (w: sw) (rep': Z * Z * Z) (xr: list val) :
  sa_ok a -> sp_pending a -> sa_x a xr ->
  semax sp_Delta (sp_LAST a ph w rep' xr) sp_last (sp_R a).
Proof.
  intros Hsa Hpend Hxa. rewrite slast_last_eq.
  eapply semax_seq; [apply (slast_head_ok a ph w rep' xr Hsa Hpend Hxa) |].
  apply semax_extract_exists; intro w'. apply slast_tail_ok; auto.
Qed.

(* ===================================================================== *)
(* the assembly *)

(* frame_fields without the three history pointers *)
Definition sp_ffr (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma sp_ff_split (p: val) (fs: fstate) :
  frame_fields p fs =
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p * sp_ffr p fs.
Proof. unfold frame_fields, sp_ffr. apply pred_ext; cancel. Qed.

Ltac sp_unf := unfold sp_INV, sp_PEND, sp_L, sp_S, sp_lvars, sp_ptrs; cbn [app].

(* the loop head `if (!nbSeq) break;` of both loops *)
Lemma sp_head {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) (R: ret_assert) :
  sa_ok a ->
  (!! (w_id w < a_nb a) && sp_INV a g Q Rin ph w (a_nb a - w_id w) |-- RA_normal R) ->
  (!! (w_id w = a_nb a) && sp_INV a g Q Rin ph w 0 |-- RA_break R) ->
  semax sp_Delta (sp_INV a g Q Rin ph w (a_nb a - w_id w))
    (Sifthenelse (Etempvar _nbSeq tint) Sskip Sbreak) R.
Proof.
  intros Hsa Hn Hb. unfold sp_Delta. sp_unf. Intros.
  rename H0 into Hxinv.
  assert (Hid: 0 <= w_id w <= a_nb a) by (destruct H as (Hid & _); exact Hid).
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by (destruct Hsa as (_ & _ & _ & _ & _ & Hnb & _); lia).
  forward_if.
  - forward. eapply derives_trans; [|apply Hn]. sp_unf. entailer!.
  - assert (Hz: a_nb a - w_id w = 0).
    { apply (f_equal Int.signed) in H0. rewrite Int.signed_repr in H0 by (unfold LONGNBSEQ in Hnb; rep_lia).
      exact H0. }
    eapply semax_pre; [|apply semax_break]. eapply derives_trans; [|apply andp_left2, Hb]. sp_unf.
    rewrite Hz. entailer!.
Qed.

(* the loops' `nbSeq--` *)
Lemma sp_decr {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) :
  sa_ok a ->
  semax sp_Delta (sp_INV a g Q Rin ph w (a_nb a - w_id w + 1))
    (Sset _nbSeq (Ebinop Osub (Etempvar _nbSeq tint) (Econst_int (Int.repr 1) tint) tint))
    (normal_ret_assert (sp_INV a g Q Rin ph w (a_nb a - w_id w))).
Proof.
  intros Hsa. unfold sp_Delta. sp_unf. Intros.
  assert (Hid: 0 <= w_id w <= a_nb a) by (destruct H as (Hid & _); exact Hid).
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by (destruct Hsa as (_ & _ & _ & _ & _ & Hnb & _); lia).
  unfold LONGNBSEQ in Hnb.
  forward. entailer!.
  do 2 f_equal. lia.
Qed.

(* ENTAIL with an empty frame of locals *)
Ltac sp_post_tac := intros; first [apply andp_left2; apply derives_refl | apply andp_left2; apply FF_left | idtac].

Definition sp_decr_stmt : statement :=
  Sset _nbSeq (Ebinop Osub (Etempvar _nbSeq tint) (Econst_int (Int.repr 1) tint) tint).
Definition sp_head_stmt : statement := Sifthenelse (Etempvar _nbSeq tint) Sskip Sbreak.

Ltac sp_ra R := repeat match goal with H := @abbreviate ret_assert _ |- _ => subst H end; destruct R;
  cbv [overridePost loop1_ret_assert loop2_ret_assert normal_ret_assert sp_x1_R sp_x2_R sp_left_R sp_end_R
       RA_normal RA_break RA_continue RA_return] in *.

(* `if (nbSeq > 0) LOOP2` *)
Lemma sp_part2 {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (ph: bool) (w: sw) (R: ret_assert) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) -> (ph = true -> w_id w = a_nb a) ->
  RA_return R = RA_return (sp_R a) ->
  semax sp_Delta (sp_INV a g Q Rin ph w (a_nb a - w_id w))
    (Sifthenelse (Ebinop Ogt (Etempvar _nbSeq tint) (Econst_int (Int.repr 0) tint) tint) sp_loop2 Sskip)
    (overridePost (EX ph': bool, EX w': sw, !! (w_id w' = a_nb a) && sp_INV a g Q Rin ph' w' 0) R).
Proof.
  intros Hsa Hpend Hb Hxa Hph HR.
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by (destruct Hsa as (_ & _ & _ & _ & _ & Hnb & _); lia).
  unfold LONGNBSEQ in Hnb.
  unfold sp_Delta. sp_unf. Intros.
  rename H0 into Hxinv.
  assert (Hid: 0 <= w_id w <= a_nb a) by (destruct H as (Hid & _); exact Hid).
  forward_if.
  - destruct ph; [rewrite (Hph eq_refl), Z.sub_diag in H0; discriminate|].
    sp_ra R.
    eapply semax_pre with (P' := EX w': sw, sp_INV a g Q Rin false w' (a_nb a - w_id w')).
    { Exists w. sp_unf. entailer!. }
    change sp_loop2 with (Sloop (Ssequence sp_head_stmt (Ssequence sp_dec2 sp_x2)) sp_decr_stmt).
    apply semax_loop with (Q' := EX w': sw, sp_INV a g Q Rin false w' (a_nb a - w_id w' + 1)).
    + apply semax_extract_exists; intro w1.
      eapply semax_seq with (Q := !! (w_id w1 < a_nb a) && sp_INV a g Q Rin false w1 (a_nb a - w_id w1)).
      { apply (sp_head a g Q Rin false w1); [exact Hsa | apply derives_refl |].
        Exists false w1. apply derives_refl. }
      apply semax_extract_prop; intro Hlt.
      eapply semax_seq with (Q := EX w2: sw, EX ll: Z, EX ml: Z, EX ov: Z, sp_PEND a g Q Rin false w2 ll ml ov).
      { eapply semax_post; [| | | | apply (seg_dec a g Q Rin false w1 Hsa Hpend Hb Hlt)].
        - apply andp_left2, derives_refl.
        - apply andp_left2, FF_left.
        - apply andp_left2, FF_left.
        - intros vl. apply andp_left2, FF_left. }
      Intros w2 ll ml ov.
      eapply semax_post; [| | | | apply (seg_x2 a g Q Rin w2 ll ml ov Hsa Hpend Hb Hxa)].
      * apply andp_left2, derives_refl.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros vl. rewrite HR. apply andp_left2, derives_refl.
    + apply semax_extract_exists; intro w1.
      eapply semax_post; [| | | | apply (sp_decr a g Q Rin false w1 Hsa)].
      * apply andp_left2. Exists w1. apply derives_refl.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros vl. apply andp_left2, FF_left.
  - forward. sp_ra R. Exists ph w. sp_unf. entailer!. do 2 f_equal. lia.
Qed.

Lemma sp_semax_orp {Espec: OracleKind} (Delta: tycontext) (P1 P2: environ -> mpred) (c: statement) (R: ret_assert) :
  semax Delta P1 c R -> semax Delta P2 c R -> semax Delta (P1 || P2) c R.
Proof.
  intros H1 H2. eapply semax_pre with (EX b: bool, if b then P1 else P2).
  - apply andp_left2. apply orp_left; [apply (exp_right true) | apply (exp_right false)]; apply derives_refl.
  - apply semax_extract_exists. intros []; assumption.
Qed.

(* the exit of loop 1: all sequences executed while split, or the break with a pending sequence *)
Definition sp_BRK1 (a: sa) (g: sg) (Q Rin: mpred) : environ -> mpred :=
  (EX w: sw, !! (w_id w = a_nb a) && sp_INV a g Q Rin true w 0) ||
  (EX w: sw, EX ll: Z, EX ml: Z, EX ov: Z,
     !! (sp_lim a - (a_lb a + w_j w) < ll) && sp_PEND a g Q Rin true w ll ml ov).

Definition sp_ifleft : statement :=
  Sifthenelse (Ebinop Ogt (Etempvar _nbSeq tint) (Econst_int (Int.repr 0) tint) tint) sp_left Sskip.

(* the block of loop 1: `sequence = {0}; LOOP1; if (nbSeq > 0) LEFTOVER` *)
Lemma sp_part1 {Espec: OracleKind} (a: sa) (g: sg) (Q Rin: mpred) (w: sw) (R: ret_assert) :
  sa_ok a -> sp_pending a -> bfacts a g Q Rin -> sa_x a (g_xr g) -> 0 < a_nb a -> w_id w = 0 ->
  RA_return R = RA_return (sp_R a) ->
  semax sp_Delta (sp_INV a g Q Rin true w (a_nb a)) sp_block
    (overridePost (EX ph: bool, EX w': sw, !! (ph = true -> w_id w' = a_nb a) &&
                     sp_INV a g Q Rin ph w' (a_nb a - w_id w')) R).
Proof.
  intros Hsa Hpend Hb Hxa Hnb Hw0 HR.
  assert (Hnbb: a_nb a <= LONGNBSEQ + 65535) by (destruct Hsa as (_ & _ & _ & _ & _ & Hnbb & _); lia).
  unfold LONGNBSEQ in Hnbb.
  unfold sp_Delta, sp_block. sp_unf. Intros.
  rename H0 into Hxinv0.
  forward. forward. forward.
  unfold MORE_COMMANDS, abbreviate.
  match goal with |- semax _ _ ?S _ =>
    change S with (Ssequence (Sloop (Ssequence sp_head_stmt (Ssequence sp_dec1 sp_x1)) sp_decr_stmt)
                    (Ssequence (Sloop Sskip Sbreak) sp_ifleft)) end.
  eapply semax_seq with (Q := sp_BRK1 a g Q Rin).
  - eapply semax_pre with (P' := EX w': sw, sp_INV a g Q Rin true w' (a_nb a - w_id w')).
    { Exists w. sp_unf. rewrite Hw0, Z.sub_0_r. entailer!. }
    apply semax_loop with (Q' := EX w': sw, sp_INV a g Q Rin true w' (a_nb a - w_id w' + 1)).
    + apply semax_extract_exists; intro w1.
      eapply semax_seq with (Q := !! (w_id w1 < a_nb a) && sp_INV a g Q Rin true w1 (a_nb a - w_id w1)).
      { apply (sp_head a g Q Rin true w1); [exact Hsa | sp_ra R; apply derives_refl |].
        sp_ra R. apply orp_right1. Exists w1. apply derives_refl. }
      apply semax_extract_prop; intro Hlt.
      eapply semax_seq with (Q := EX w2: sw, EX ll: Z, EX ml: Z, EX ov: Z, sp_PEND a g Q Rin true w2 ll ml ov).
      { eapply semax_post; [| | | | apply (seg_dec a g Q Rin true w1 Hsa Hpend Hb Hlt)].
        all: sp_ra R.
        - apply andp_left2, derives_refl.
        - apply andp_left2, FF_left.
        - apply andp_left2, FF_left.
        - intros vl. apply andp_left2, FF_left. }
      Intros w2 ll ml ov.
      eapply semax_post; [| | | | apply (seg_x1 a g Q Rin w2 ll ml ov Hsa Hpend Hb Hxa)].
      all: sp_ra R.
      * apply andp_left2, derives_refl.
      * apply andp_left2. apply orp_right2. apply derives_refl.
      * apply andp_left2, FF_left.
      * intros vl. rewrite HR. apply andp_left2, derives_refl.
    + apply semax_extract_exists; intro w1.
      eapply semax_post; [| | | | apply (sp_decr a g Q Rin true w1 Hsa)].
      all: sp_ra R.
      * apply andp_left2. Exists w1. apply derives_refl.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros vl. apply andp_left2, FF_left.
  - apply dec_skipbreak_seq. unfold sp_BRK1. apply sp_semax_orp.
    + Intros w1. apply semax_extract_prop; intro Hw1. sp_unf. Intros. unfold sp_ifleft. forward_if.
      * lia.
      * forward. sp_ra R. Exists true w1. sp_unf. rewrite Hw1, Z.sub_diag. entailer!.
    + Intros w1 ll ml ov. apply semax_extract_prop; intro Hbrk.
      sp_unf. Intros.
      rename H1 into Hxp1.
      assert (Hlt1: w_id w1 < a_nb a) by (destruct (H0) as ((_ & Hlt1) & _); exact Hlt1).
      unfold sp_ifleft. forward_if.
      * eapply semax_pre with (P' := sp_PEND a g Q Rin true w1 ll ml ov).
        { sp_unf. entailer!. }
        eapply semax_post; [| | | | apply (seg_left a g Q Rin w1 ll ml ov Hsa Hpend Hb Hxa Hbrk)].
        all: sp_ra R.
        -- apply andp_left2. Intros w'. Exists false w'.
           apply andp_right; [apply prop_right; intro; discriminate | apply derives_refl].
        -- apply andp_left2, FF_left.
        -- apply andp_left2, FF_left.
        -- intros vl. rewrite HR. apply andp_left2, derives_refl.
      * destruct (H0) as ((Hid0 & _) & _). rewrite Int.signed_repr in H1 by rep_lia. lia.
Qed.

(* the head is ahead of the output by 65504 - (content beyond min(bsm,cap)); dictEnd is a pointer or NULL *)
Lemma sp_pending_ok (a: sa) :
  sa_ok a -> isptr (sp_ob a) ->
  (match sp_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) -> sp_pending a.
Proof.
  intros Hsa Hob Heb. destruct Hsa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hde) & Hlp & _).
  unfold sp_pending. split.
  - unfold lit_pos in Hlp. rewrite Hlp. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. lia.
  - destruct Hde as [-> | [(k & _ & ->) | Hx]].
    + simpl; auto.
    + unfold sp_ob in Hob. destruct (oa_base (a_o a)); try contradiction. simpl; auto.
    + unfold sp_x in Heb, Hx. destruct (hc_ext (a_h a)); try contradiction.
      destruct Hx as (-> & _). destruct eb; try contradiction. simpl; auto.
Qed.

(* no sequences: nothing executed yet, the model's content is the literals *)
Lemma sp_slast0 (a: sa) (st: Z * Z * Z) :
  sa_ok a -> sa_dok a -> a_nb a = 0 ->
  slast a true {| w_id := 0; w_pos := 0; w_lo := 0; w_st := st; w_crep := a_rep a; w_K := 0; w_j := 0;
                  w_c := sp_c0 a |} (a_rep a).
Proof.
  intros Hsa Hda Hnb. pose proof (sp_dfd0 a Hsa Hda) as Hd0'.
  destruct Hsa as (Ho & Hi & Hl & Hb & Hn & _ & _ & _ & Hr & _).
  destruct Hl as (Hlb & Hn0 & Hgt & Hd & Hend & Hsub).
  destruct Ho as (_ & HcN & _ & Hd0 & Hc0 & HdN).
  unfold slast, sp_outok; cbn [w_K w_j w_c]. unfold sp_n, sp_cap, sp_c0, sp_N, sp_d in *.
  split; [exact Hr|]. split.
  { split; [lia|]. split; [exact HcN|]. split.
    - split; [unfold LITBUFFEREXTRASIZE in *; lia|]. intros k _ _. reflexivity.
    - split; [exact Hd0' | auto]. }
  split; [auto|].
  intros _ cnt rep2 Hm _. unfold seqs_model in Hm. rewrite Hnb in Hm. cbn in Hm.
  injection Hm as <- <-. exists []. split; [reflexivity|]. split.
  - rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
  - split; [reflexivity|]. intros _. rewrite Z.add_0_r, sublist_nil. reflexivity.
Qed.

Lemma body_ZSTD_decompressSequences_bodySplitLitBuffer :
  GLOBALS_obligation ->
  semax_body Vprog LOOP_GB f_ZSTD_decompressSequences_bodySplitLitBuffer (_ZSTD_decompressSequences_bodySplitLitBuffer, seqs_spec is_split).
Proof.
  intro HG. start_function.
  destruct l as [lo0 | | lo0 | lb]; try contradiction H1. clear H1.
  unfold litfields, lit_extra_at. Intros. rewrite litextra_data_at.
  match goal with Hq: sublist 0 LITBUFFEREXTRASIZE lxb = _ |- _ => rename Hq into Hlxt end.
  match goal with Hq: Zlength lxb = LITEXTRA_N |- _ => rename Hq into Hlxl end.
  match goal with Hq: bytes_ok lxb |- _ => rename Hq into Hlxb end.
  set (xr := zbytes (sublist LITBUFFEREXTRASIZE LITEXTRA_N lxb)).
  assert (Hxrl: Zlength xr = WILDCOPY_OVERLENGTH).
  { unfold xr. rewrite Zlength_map, Zlength_sublist; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
  assert (Hxrb: byte_cells xr).
  { unfold xr. apply seg_init_zbytes_cells. unfold bytes_ok in *. apply Forall_sublist. exact Hlxb. }
  assert (Hcap: 0 < oa_cap o).
  { destruct H2 as (_ & _ & H2a & H2b & H2c & _). unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia. }
  specialize (H11 Hcap).
  assert_PROP (isptr (oa_base o)) as Hob by entailer!.
  forward.
  forward_call (offset_val (oa_d o) (oa_base o), oa_cap o).
  { destruct (H) as (_ & _ & HN & Hd0 & Hc0 & HdN). rep_lia. }
  rewrite (proj2 (Z.ltb_lt 0 (oa_cap o)) Hcap), offset_offset_val.
  forward. forward. forward. forward.
  rewrite sp_ff_split. Intros.
  set (a := {| a_gv := gv; a_p := p; a_fs := fs; a_ox := ox; a_os := os; a_fe := fe; a_rep := rep; a_lb := lb;
               a_lits := lits; a_nb := nbSeq; a_bsm := bsm; a_W := W; a_o := o; a_i := i; a_h := h; a_lxb := lxb;
               a_vlp := v_litPtr; a_vss := v_seqState; a_vsq := v_sequence; a_vsq1 := v_sequence__1 |}).
  assert (Hxa: sa_x a xr).
  { unfold sa_x, sp_tail, sp_n. unfold a. cbn [a_lxb a_lits].
    split; [exact Hlxl|]. split; [exact Hlxb|]. split; [exact Hlxt | reflexivity]. }
  replace (zbytes lxb) with (zbytes (sp_tail a) ++ xr) by (first [exact (sa_x_cl a xr Hxa) | exact (eq_sym (sa_x_cl a xr Hxa))]).
  clearbody xr.
  assert (Hsa: sa_ok a).
  { unfold sa_ok. repeat match goal with |- _ /\ _ => split end;
      first [assumption | (intros; assumption) | (unfold a; cbn [a_bsm a_nb]; lia)]. }
  assert_PROP (match hc_ext h with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) as Heb.
  { destruct (hc_ext h); try (entailer!; fail). unfold ext_res. entailer!. }
  assert (Hpend: sp_pending a) by (apply sp_pending_ok; [exact Hsa | exact Hob | exact Heb]).
  assert (Hda: sa_dok a) by (split; assumption).
  destruct (H11) as (Hps & HpS & HvS & Hel & Hx).
  assert (HdE: fs_dictEnd fs = dict_end (hc_ext h) (oa_base o) (fs_dictEnd fs))
    by (destruct (hc_ext h); simpl in Hx |- *; tauto).
  assert (HdEp: is_pointer_or_null (fs_dictEnd fs)) by apply Hpend.
  rewrite HpS, HvS.
  forward. forward. forward. forward. forward. forward.
  apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
  eapply semax_seq with (Q := EX ph: bool, EX w: sw, EX rep': Z * Z * Z, sp_LAST a ph w rep' xr).
  2: { apply semax_extract_exists; intro ph. apply semax_extract_exists; intro w.
       apply semax_extract_exists; intro rep'. exact (seg_last a ph w rep' xr Hsa Hpend Hxa). }
  forward_if.
  - (* nbSeq > 0 *)
    assert (Hnb: 0 < nbSeq).
    { assert (nbSeq <> 0).
      { intro; subst nbSeq. match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
      lia. }
    eapply semax_pre with (P' := sp_P0 a xr).
    { unfold sp_P0, sp_lvars, sp_ptrs, sp_FR0, sp_ob, sp_d, sp_cap, sp_N, sp_n, sp_lim, sp_tail, sp_ps, sp_x,
        sp_c0, sp_s, sp_sst.
      unfold a. cbn [a_gv a_p a_fs a_ox a_os a_fe a_rep a_lb a_lits a_nb a_bsm a_W a_o a_i a_h
        a_vlp a_vss a_vsq a_vsq1 app]. rewrite sp_ff_split, HpS, HvS, <- HdE.
      entailer!. }
    match goal with |- semax _ _ ?S _ => change S with (sp_init (Ssequence sp_block sp_rest2)) end.
    eapply seg_init; [exact HG | exact Hsa | exact Hda | exact Hpend | exact Hnb | exact Hxrl | exact Hxrb | exact Hxa |
                      reflexivity |].
    intros g Q Rin w Hb Hxr Hid HK Hj Hc Hcr. subst xr.
    eapply semax_seq with
      (Q := EX ph: bool, EX w': sw, !! (ph = true -> w_id w' = nbSeq) && sp_INV a g Q Rin ph w' (nbSeq - w_id w')).
    2: {
      apply semax_extract_exists; intro ph. apply semax_extract_exists; intro w1.
      apply semax_extract_prop; intro Hph.
      change sp_rest2 with (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _nbSeq tint) (Econst_int (Int.repr 0) tint) tint) sp_loop2 Sskip) sp_end).
      eapply semax_seq with (Q := EX ph: bool, EX w': sw, !! (w_id w' = nbSeq) && sp_INV a g Q Rin ph w' 0).
      2: {
        apply semax_extract_exists; intro ph2. apply semax_extract_exists; intro w2.
        apply semax_extract_prop; intro Hw2.
        eapply semax_post; [| | | | apply (seg_end a g Q Rin ph2 w2 Hsa Hpend Hb Hxa Hw2 Hnb)].
        - unfold sp_end_R, overridePost; cbn [RA_normal]. apply andp_left2. Intros rep'.
          Exists ph2 w2 rep'. apply derives_refl.
        - apply andp_left2, FF_left.
        - apply andp_left2, FF_left.
        - intros vl. apply andp_left2, derives_refl. }
      apply (sp_part2 a g Q Rin ph w1); [exact Hsa | exact Hpend | exact Hb | exact Hxa | exact Hph | reflexivity]. }
    apply (sp_part1 a g Q Rin w); [exact Hsa | exact Hpend | exact Hb | exact Hxa | exact Hnb | exact Hid | reflexivity].
  - (* nbSeq = 0: the last literals only *)
    assert (Hnb0: nbSeq = 0).
    { match goal with Hz: Int.repr nbSeq = Int.zero |- _ =>
        apply (f_equal Int.signed) in Hz; rewrite Int.signed_repr in Hz by (unfold LONGNBSEQ in H5; rep_lia); exact Hz end. }
    subst nbSeq. forward.
    assert (Hxl0 := xlast0 a (zbytes (sp_tail a) ++ xr) (0, 0, 0) Hsa eq_refl (sa_x_cl a xr Hxa) (proj1 Hxa)).
    Exists true {| w_id := 0; w_pos := 0; w_lo := 0; w_st := (0, 0, 0); w_crep := rep; w_K := 0; w_j := 0;
                   w_c := oa_c o |} rep.
    unfold sp_LAST, sp_lvars, sp_ptrs, sp_FR0, sp_lp, sp_lbe, sp_loc, sp_ob, sp_d, sp_cap, sp_N, sp_n, sp_lim,
      sp_tail, sp_ps, sp_x. unfold a. cbn [a_gv a_p a_fs a_ox a_os a_fe a_rep a_lb a_lits a_nb a_bsm a_W a_o a_i a_h
      a_vlp a_vss a_vsq a_vsq1 w_K w_j w_c app]. rewrite sp_ff_split, HpS, HvS, <- HdE.
    entailer!.
    all: try exact Hxl0.
    + apply (sp_slast0 a (0, 0, 0) Hsa Hda eq_refl).
    + simpl. cancel.
Qed.
