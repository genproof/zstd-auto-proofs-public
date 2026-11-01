(* LOOP: the short loop (literals not split: LIn, LExtra, LDst).
   ZSTD_decompressSequences_body gets the dispatchers' seqs_spec (BlkIface) itself, in the loop bodies' context LOOP_GB
   (BlkSeqLoopCommon); BlkSeqLOOP.LOOP_ok lifts it.  Shared steps: BlkSeqLoopModel (the model invariant),
   BlkSeqLoopCommon (tables, bitstream, litExtraBuffer).

   The proof is cut into segments of the body
   (Section Short: the spec's variables, the context facts sh_ctx):
     sh_prologue_ok   statements 0..8 (oend, litPtr, litEnd, the history pointers), CPS to S_pre;
     sh_init_ok       if (nbSeq) { fseEntropy, prevOffset, BIT_initDStream, 3 initFseState }, CPS to the
                      loop invariant sh_inv at 0;
     sh_dec_ok        one ZSTD_decodeSequence (sh_inv_at -> sh_mid_at);
     sh_exec_ok       one ZSTD_execSequence, its error check, op += (sh_mid_at -> sh_inv_at (id+1));
     sh_end_ok        BIT_endOfDStream, saving the repeat offsets (sh_inv nbSeq -> sh_aft);
     sh_epi_ok        the last literals, the return (sh_aft -> the post);
   helpers sh_borrow (the tables, lending zstd_globals back for execSequence) and sh_release (the literal
   fields and the input array back). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopShortX.
Local Open Scope logic.

(* ---------- statements: the k-th / the rest after k of a right-nested Ssequence ---------- *)
Fixpoint sq_nth (n: nat) (s: statement) : statement :=
  match n, s with
  | O, Ssequence a _ => a
  | S n', Ssequence _ b => sq_nth n' b
  | _, _ => Sskip
  end.
Fixpoint sq_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => sq_drop n' b
  | _, _ => Sskip
  end.

Definition sh_body : statement := fn_body f_ZSTD_decompressSequences_body.
(* if (nbSeq) BIG; then EPI (the last literals, the return) *)
Definition sh_BIG : statement :=
  match sq_nth 9 sh_body with Sifthenelse _ s _ => s | _ => Sskip end.
Definition sh_EPI : statement := sq_drop 10 sh_body.
(* BIG = 6 statements of initialisation; the loop; END (endOfDStream check, saving the repeat offsets) *)
Definition sh_BREST : statement := sq_drop 6 sh_BIG.
Definition sh_LOOP : statement := sq_nth 6 sh_BIG.
Definition sh_END : statement := sq_drop 7 sh_BIG.
(* the loop body: if (nbSeq) skip else break; DEC (ZSTD_decodeSequence); EXEC *)
Definition sh_LB : statement := match sh_LOOP with Sloop b _ => b | _ => Sskip end.
Definition sh_DEC : statement := sq_nth 1 sh_LB.
Definition sh_EXEC : statement := sq_drop 2 sh_LB.

Definition sh_Delta : tycontext := func_tycontext f_ZSTD_decompressSequences_body Vprog LOOP_GB nil.

(* ---------- the tables, borrowed for the loop; zstd_globals can be lent back (execSequence) ---------- *)
Definition tabs_ok (gv: globals) (p: val) (ox: option ddx) (t: fse_table * fse_table * fse_table)
    (tp: val * val * val) (sht: share * share * share) (fm: Z * Z * Z) (Rt: mpred) : Prop :=
  seqtabs_sh_ok sht /\
  (forall fe': Z,
     field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p tp * seqtabs_at sht t fm tp * Rt
     |-- tabs_seq gv p ox (Some t) fe' * dent_of dent_def gv ox * zstd_globals gv) /\
  exists Y: mpred, seqtabs_at sht t fm tp * Rt = zstd_globals gv * Y.

(* sh_borrow's pool (as in BlkSeqLoopCommon.seqtabs_borrow): a DDict's sequence table of kind k, a
   predefined table of kind k *)
Definition sh_borrow_ddslot (ox: option ddx) (k: seqkind) : mpred :=
  match ox_seq k ox with
  | Some t => seqspace_at Ews k (Some t) (dd_seq k (ox_q ox))
  | None => emp
  end.
Definition sh_borrow_gslot (gv: globals) (k: seqkind) : mpred :=
  seqtab_at_fm Ers k (sk_predef k) predef_fm (gv (sk_gdefault k)).

Lemma sh_borrow_dent_split (gv: globals) (ox: option ddx) :
  exists Rd: mpred, dent_of dent_def gv ox =
    sh_borrow_ddslot ox KLL * sh_borrow_ddslot ox KOF * sh_borrow_ddslot ox KML * Rd.
Proof.
  unfold sh_borrow_ddslot, ox_seq.
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

Lemma sh_borrow_one (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) :
  seq_where gv p ox k t * sh_borrow_ddslot ox k * sh_borrow_gslot gv k |--
  EX tp: val, EX sh: share, EX fm: Z, EX Rk: mpred,
    !! (readable_share sh /\
        (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk
         |-- seq_where gv p ox k t * sh_borrow_ddslot ox k * sh_borrow_gslot gv k) /\
        exists Yk: mpred, seqtab_at_fm sh k t fm tp * Rk = sh_borrow_gslot gv k * Yk) &&
    (seq_ptr_at p k tp * seqtab_at_fm sh k t fm tp * Rk).
Proof.
  unfold seq_where. Intros tp w. destruct w.
  - Intros. subst tp. unfold seqspace_at at 1, seqtab_at. Intros fm.
    Exists (ctx_seq k p) Ews fm
      (data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (ctx_seq k p)) * sh_borrow_ddslot ox k * sh_borrow_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + Exists (ctx_seq k p) TCtx. unfold seqspace_at, seqtab_at. Exists fm. entailer!.
    + match goal with |- exists Yk, ?A * (?B * ?D) = ?D * _ => exists (A * B) end.
      apply pred_ext; cancel.
  - Intros. rename H into Ho. subst tp. unfold sh_borrow_ddslot at 1. rewrite Ho.
    unfold seqspace_at at 2, seqtab_at. Intros fm.
    Exists (dd_seq k (ox_q ox)) Ews fm
      (seqspace_at Ews k None (ctx_seq k p) *
       data_at_ Ews (tarray t_seqSymbol (sk_size k - 1 - 2 ^ ft_log t))
         (offset_val (8 * (1 + 2 ^ ft_log t)) (dd_seq k (ox_q ox))) * sh_borrow_gslot gv k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + Exists (dd_seq k (ox_q ox)) TDict. try (unfold sh_borrow_ddslot; rewrite Ho).
      unfold seqspace_at, seqtab_at. Exists fm. entailer!.
    + match goal with |- exists Yk, ?A * (?B * ?D) = ?D * _ => exists (A * B) end.
      apply pred_ext; cancel.
  - Intros. subst t tp. unfold sh_borrow_gslot at 1.
    Exists (gv (sk_gdefault k)) Ers predef_fm
      (seqspace_at Ews k None (ctx_seq k p) * sh_borrow_ddslot ox k).
    apply andp_right; [apply prop_right | cancel].
    split; [auto with share |]. split.
    + Exists (gv (sk_gdefault k)) TGlob. unfold sh_borrow_gslot. entailer!.
    + eexists. unfold sh_borrow_gslot. reflexivity.
Qed.

Lemma sh_borrow (HG: GLOBALS_obligation) (gv: globals) (p: val) (ox: option ddx)
    (t: fse_table * fse_table * fse_table) (fe: Z) :
  tabs_seq gv p ox (Some t) fe * dent_of dent_def gv ox * zstd_globals gv |--
  EX tp: val * val * val, EX sht: share * share * share, EX fm: Z * Z * Z, EX Rt: mpred,
    !! (tabs_ok gv p ox t tp sht fm Rt) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p * seq_ptrs p tp * seqtabs_at sht t fm tp * Rt).
Proof.
  destruct t as [[a b] c].
  destruct (sh_borrow_dent_split gv ox) as [Rd Hd]. destruct (HG gv) as [Rg Hg].
  assert (Hp: predef_tabs gv = sh_borrow_gslot gv KLL * sh_borrow_gslot gv KOF * sh_borrow_gslot gv KML)
    by reflexivity.
  rewrite Hd, Hg, Hp.
  unfold tabs_seq.
  sep_apply (sh_borrow_one gv p ox KLL a). Intros tpa sha fma Ra.
  sep_apply (sh_borrow_one gv p ox KOF b). Intros tpb shb fmb Rb.
  sep_apply (sh_borrow_one gv p ox KML c). Intros tpc shc fmc Rc.
  rename H0 into Hra, H3 into Hrb, H6 into Hrc.
  destruct H1 as [Ya Ea]. destruct H4 as [Yb Eb]. destruct H7 as [Yc Ec].
  Exists (tpa, tpb, tpc) (sha, shb, shc) (fma, fmb, fmc) (Ra * Rb * Rc * Rd * Rg).
  unfold seq_ptrs, seqtabs_at.
  unfold seq_ptr_at in *.
  apply andp_right; [apply prop_right | cancel].
  unfold tabs_ok. split; [simpl; auto |]. split.
  - intros fe'. unfold tabs_seq, seq_ptrs, seqtabs_at. rewrite Hd, Hg, Hp.
    sep_apply Hra. sep_apply Hrb. sep_apply Hrc. cancel.
  - exists (Ya * Yb * Yc * Rd). unfold seqtabs_at. rewrite Hg, Hp.
    transitivity ((seqtab_at_fm sha KLL a fma tpa * Ra) * (seqtab_at_fm shb KOF b fmb tpb * Rb) *
                  (seqtab_at_fm shc KML c fmc tpc * Rc) * Rd * Rg).
    { apply pred_ext; cancel. }
    rewrite Ea, Eb, Ec. apply pred_ext; cancel.
Qed.

Lemma sh_dec_err (k: Z) : 0 < k < 120 -> k <> 80 -> k <> 82 -> dec_err (Int64.unsigned (Int64.repr (- k))).
Proof.
  intros Hk H80 H82. rewrite Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64).
  rewrite <- (Z_mod_plus_full (- k) 1 (2 ^ 64)). rewrite Z.mod_small by lia.
  unfold dec_err, is_error_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [apply Z.ltb_lt; lia | lia].
Qed.

Section Short.
Context {Espec: OracleKind}.
Variables (gv: globals) (p: val) (fs: fstate) (ox: option ddx) (os: option (fse_table * fse_table * fse_table))
  (fe: Z) (rep: Z * Z * Z) (l: litloc) (lits: list Z) (nbSeq bsm: Z) (W: list ptr_witness)
  (o: outarr) (i: inwin) (h: hctx) (v_litPtr v_seqState v_sequence: val).
(* the input array split (BlkSeqLoopCommon.inwin_bits): a readable copy, the bitstream, the rest *)
Variables (sh1 sh2: share) (Ri: mpred).
(* the bytes after the literals in litExtraBuffer (LExtra); litExtraBuffer's bytes (all its cells) *)
Variable (xrest: list val).
Variable (lxb: list Z).

(* the facts of the precondition (seqs_spec), the facts the interfaces did not state at first (hist_ptrs_ok,
   in-dst literals after the content), and the facts of the split *)
Definition sh_ctx : Prop :=
  outarr_ok o /\ inwin_ok i /\ not_split l /\ lits_at l (oa_c o) (oa_d o) (oa_cap o) i lits /\
  0 <= bsm <= ZSTD_BLOCKSIZE_MAX /\ Zlength lits <= bsm /\ 0 <= nbSeq <= LONGNBSEQ + 65535 /\
  (nbSeq > 0 -> os <> None /\ 0 < oa_cap o) /\ seqs_ok os /\ rep_ok rep /\ (fe = 0 \/ fe = 1) /\
  (oa_cap o = 0 -> (pws_pred W |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)))) /\
  (0 < oa_cap o -> layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h)) /\
  (* pending *)
  is_pointer_or_null (fs_prefixStart fs) /\ is_pointer_or_null (fs_virtualStart fs) /\
  is_pointer_or_null (fs_dictEnd fs) /\
  (match l with LDst lb => oa_d o + bsm <= lb | _ => True end) /\
  (* the split *)
  readable_share sh1 /\ readable_share sh2 /\ isptr (oa_base o) /\ isptr (iw_base i) /\
  data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) =
    data_at sh1 (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) *
    bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i) * Ri /\
  (l = LExtra -> Zlength xrest = LITEXTRA_N - Zlength lits) /\
  (l = LExtra -> byte_cells xrest).

(* litExtraBuffer (litfields' lit_extra_at): all its LITEXTRA_N cells are the bytes lxb; for LExtra the
   literals followed by xrest *)
Definition sh_lx : Prop :=
  (l = LExtra -> zbytes lits ++ xrest = zbytes lxb) /\ Zlength lxb = LITEXTRA_N /\ bytes_ok lxb /\
  (l = LExtra -> sublist 0 (Zlength lits) lxb = lits).

(* where the literals are for execSequence, their first offset, oend *)
Definition sh_ls : litsrc :=
  match l with
  | LIn _ => LitSep sh1 (iw_base i) (iw_c i)
  | LExtra => LitSep Ews (lit_extra p) (zbytes lits ++ xrest)
  | _ => LitIn
  end.
Definition sh_li0 : Z := match l with LIn off => off | LExtra => 0 | LDst lb => lb | LSplit lb => lb end.
Definition sh_lb : val := lit_base sh_ls (oa_base o).
Definition sh_oend : Z := match l with LDst lb => lb | _ => oa_d o + oa_cap o end.

(* litfields with LExtra's tail fixed to xrest *)
Definition sh_lf : mpred :=
  match l with
  | LExtra =>
      field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (Zlength lits))) p *
      field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr LOC_NOT_IN_DST)) p *
      field_at Ews t_dctx (DOT _litPtr) (lit_extra p) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (Zlength lits) (lit_extra p)) p *
      field_at Ews t_dctx (DOT _litBuffer) (lit_extra p) p *
      field_at Ews t_dctx (DOT _litExtraBuffer) (zbytes lits ++ xrest) p
  | _ => litfields p (oa_base o) (iw_base i) l lits lxb
  end.

(* the literal fields during the loop (all but litExtraBuffer of LExtra, which is lit_res sh_ls), and the
   input array's readable copy when it is not lit_res *)
Definition sh_lrest : mpred :=
  field_at_ Ews t_dctx (DOT _litPtr) p * field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p * field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  match l with LExtra => emp | _ => lit_extra_at p lxb end *
  match l with LIn _ => emp | _ => data_at sh1 (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) end.

(* BlkSeqLoopCommon.litextra_data_at, proved here *)
Lemma sh_release_litextra (p0: val) (v: list val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) v p0 = data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra p0).
Proof.
  rewrite field_at_data_at. reflexivity.
Qed.

Lemma sh_release_zbytes (l0: list Z) : bytes_ok l0 -> byte_cells (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

Lemma sh_release (HC: sh_ctx) (HX: sh_lx) :
  sh_lrest * lit_res sh_ls * bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i) * Ri |--
  lit_scratch_x p lxb * data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i).
Proof using All.
  destruct HC as (_ & Hiw & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    Heq & Hx & Hxb).
  destruct HX as (Hxl & Hlxn & Hlxb & _).
  rewrite Heq. unfold sh_lrest, lit_scratch_x, sh_ls.
  destruct l; simpl in Hns; try contradiction; simpl lit_res.
  - destruct Hiw as (_ & _ & _ & _ & HN & _).
    rewrite HN. cancel.
  - rewrite (Hxl eq_refl).
    replace (Zlength (zbytes lxb)) with LITEXTRA_N by (rewrite Zlength_map; lia).
    rewrite <- sh_release_litextra.
    unfold lit_extra_at.
    rewrite prop_true_andp by (split; assumption).
    cancel.
  - cancel.
Qed.

(* the facts the exact steps (BlkSeqLoopShortX) use, and its names of the C's places *)
Lemma sh_xs_ctx (HC: sh_ctx) (HX: sh_lx) : xs_ctx fs os rep l lits lxb nbSeq o i h.
Proof using All.
  destruct HC as (Ho & Hi & Hns & Hla & _ & _ & Hnb & Hnbp & Hos & Hrep & _ & _ & Hlay & _).
  destruct HX as (_ & Hlxn & Hlxb & Hlxs).
  unfold xs_ctx. repeat (split; [assumption || lia|]). exact Hlxs.
Qed.

Lemma sh_xs_lsrc (HX: sh_lx) : ls_l sh_ls = xs_lsrc l lxb i.
Proof using All.
  destruct HX as (Hxl & _). unfold sh_ls, xs_lsrc, ls_l. destruct l; try reflexivity.
  rewrite (Hxl eq_refl). reflexivity.
Qed.

Lemma sh_xs_oend : sh_oend = xs_oend l o.
Proof. reflexivity. Qed.

Lemma sh_xs_li0 : sh_li0 = xs_li0 l.
Proof. reflexivity. Qed.

(* ---------- the function's postcondition (seqs_spec not_split) ---------- *)
Definition sh_POST : environ -> mpred := (
  EX r: Z, EX oc': list val, EX rep': Z * Z * Z,
  PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o; rep_ok rep';
        unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
        is_error_code r = false ->
          r <= oa_cap o /\
          unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
          (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
           (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= bsm /\ ext_far (oa_d o) (oa_cap o) bsm (hc_ext h))) ->
             exists cnt : list Z, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
        oa_cap o = 0 \/
        hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
        ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) ->
        match seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h) with
        | Some (cnt, rep2) =>
            Zlength cnt <= bsm ->
            is_error_code r = false /\ r = Zlength cnt /\
            sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ rep' = rep2 \/
            is_error_code r = true /\ oa_cap o < Zlength cnt
        | None => True
        end;
        is_error_code r = true -> dec_err r;
        byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc';
        seqs_exact os rep l lits lxb nbSeq o i h r oc' rep')
  RETURN (Vlong (Int64.repr r))
  SEP (zstd_globals gv; pws_pred W; frame_fields p fs; tabs_seq gv p ox os (if nbSeq =? 0 then fe else 1);
       dent_of dent_def gv ox; field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p; lit_scratch_x p lxb;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
       data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)))%argsassert.

Definition sh_SR : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong sh_POST) (stackframe_of f_ZSTD_decompressSequences_body).

(* ---------- the states ---------- *)

(* the precondition after start_function, litfields with xrest *)
Definition S_start : environ -> mpred :=
  PROP ()
  LOCAL (lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
         lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
         lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p;
         temp _dst (offset_val (oa_d o) (oa_base o)); temp _maxDstSize (Vlong (Int64.repr (oa_cap o)));
         temp _seqStart (offset_val (iw_off i) (iw_base i));
         temp _seqSize (Vlong (Int64.repr (Zlength (iw_s i))));
         temp _nbSeq (Vint (Int.repr nbSeq)); temp _isLongOffset (Vint (Int.repr 0)))
  SEP (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
       data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v_seqState;
       data_at_ Tsh (tptr tuchar) v_litPtr; zstd_globals gv; pws_pred W; frame_fields p fs;
       tabs_seq gv p ox os fe; dent_of dent_def gv ox;
       field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p; sh_lf;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
       data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)).

(* before `if (nbSeq)`: the temps set, the literal fields and the input array split *)
Definition S_pre : environ -> mpred :=
  PROP ()
  LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
         temp _op (offset_val (oa_d o) (oa_base o));
         temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
         temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
         temp _dictEnd (fs_dictEnd fs);
         lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
         lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
         lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p;
         temp _seqStart (offset_val (iw_off i) (iw_base i));
         temp _seqSize (Vlong (Int64.repr (Zlength (iw_s i))));
         temp _nbSeq (Vint (Int.repr nbSeq)); temp _isLongOffset (Vint (Int.repr 0)))
  SEP (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
       data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v_seqState;
       data_at Tsh (tptr tuchar) (offset_val sh_li0 sh_lb) v_litPtr;
       zstd_globals gv; tabs_seq gv p ox os fe; dent_of dent_def gv ox;
       field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p;
       pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
       bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)).

(* the model's history is what zstd sees *)
Definition sh_hv : Prop :=
  hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
  ext_clear (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h).
(* the length of the content the model gives (out' extends out) *)
Definition sh_cnt (out' lits': list Z) : Z := Zlength out' - Zlength (hc_out h) + Zlength lits'.
(* what the executors read is defined (memcpy and memmove are libc.c's byte loops): the history before dst,
   the extDict, the literals with the 32 cells after them *)
Definition sh_rd (c: list val) : Prop :=
  Forall is_byte_val (sublist (hc_ps h) (oa_d o) c) /\ ext_def (hc_ext h) c /\
  Forall is_byte_val (sublist sh_li0 (sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH) (lit_arr sh_ls c)).
(* the bytes written so far are defined, and (with a capacity, so with sequences to execute) what the
   executors read *)
Definition sh_def (K: Z) (c: list val) : Prop :=
  Forall is_byte_val (sublist (oa_d o) (oa_d o + K) c) /\ (0 < oa_cap o -> sh_rd c).
(* the definedness facts of seqs_spec's precondition *)
Definition sh_dctx : Prop :=
  hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) /\ lit_slack_def l (oa_c o) (Zlength lits).
(* bytes in, bytes out: the output array holds bytes when everything read does *)
Definition sh_bytes (c: list val) : Prop :=
  byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells c.

(* after `if (nbSeq) {...}`: K bytes written (op = d + K), j literals used, the repeat offsets crep *)
Definition sh_aft_mdl0 (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) : Prop :=
  (oa_cap o = 0 \/ sh_hv) ->
  match seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h) with
  | Some (cnt, rep2) =>
      Zlength cnt <= bsm ->
      exists blk, K = Zlength blk /\ sublist (oa_d o) (oa_d o + K) c = zbytes blk /\
        cnt = blk ++ skipn (Z.to_nat j) lits /\ crep = rep2
  | None => True
  end.
(* with the exact model's state (BlkSeqLoopShortX) *)
Definition sh_aft_mdl (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) : Prop :=
  sh_aft_mdl0 K c crep j /\ xs_aft os rep l lits lxb nbSeq o i h K c crep j.

Definition sh_aft_at (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) : environ -> mpred :=
  PROP (0 <= K; oa_d o + K <= sh_oend; 0 <= j <= Zlength lits; Zlength c = oa_N o;
        unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH));
        rep_ok crep; sh_def K c; sh_aft_mdl K c crep j; sh_bytes c)
  LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
         temp _op (offset_val (oa_d o + K) (oa_base o));
         temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
         lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
         lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
         lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p)
  SEP (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
       data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v_seqState;
       data_at Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr;
       zstd_globals gv; tabs_seq gv p ox os (if nbSeq =? 0 then fe else 1); dent_of dent_def gv ox;
       field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals crep) p;
       pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o);
       bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)).

Definition sh_aft : environ -> mpred :=
  EX K: Z, EX c: list val, EX crep: Z * Z * Z, EX j: Z, sh_aft_at K c crep j.

(* the loop invariant, model part: after id sequences decoded and executed (bitstream at (pos, lo), states
   st; K bytes written, j literals used, the C's repeat offsets crep), the rest of the model *)
Definition sh_inv_mdl0 (t: fse_table * fse_table * fse_table) (id K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) : Prop :=
  let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
  sh_hv ->
  forall seqs out' lits' rep2,
    decode_seq_stream tLL tOF tML (iw_s i) nbSeq = Some seqs ->
    exec_seqs (hc_wsize h) rep (hc_hist h) lits (hc_out h) seqs = Some (out', lits', rep2) ->
    sh_cnt out' lits' <= bsm ->
    bs_ready pos lo /\ (id = nbSeq -> lo = 0) /\
    decode_seqs tLL tOF tML (iw_s i) (Z.to_nat (nbSeq - id)) sLL sOF sML pos =
      Some (skipn (Z.to_nat id) seqs, 0) /\
    exists blk, K = Zlength blk /\ sublist (oa_d o) (oa_d o + K) c = zbytes blk /\
      exec_seqs (hc_wsize h) crep (hc_hist h) (skipn (Z.to_nat j) lits) (hc_out h ++ blk)
        (skipn (Z.to_nat id) seqs) = Some (out', lits', rep2).
(* with the exact model's continuation (BlkSeqLoopShortX) *)
Definition sh_inv_mdl (t: fse_table * fse_table * fse_table) (id K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) : Prop :=
  sh_inv_mdl0 t id K c crep j pos lo st /\ xs_inv os rep l lits lxb nbSeq o i h t id K c crep j pos lo st.

(* the loop invariant (the temp nbSeq is tn: nbSeq - id, or nbSeq - id + 1 before the decrement) *)
Definition sh_inv_at (t: fse_table * fse_table * fse_table) (tp: val * val * val) (sht: share * share * share)
    (fm: Z * Z * Z) (Rt: mpred) (id tn K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z)
    : environ -> mpred :=
  PROP (0 <= id <= nbSeq; 0 <= K; oa_d o + K <= sh_oend; 0 <= j <= Zlength lits; Zlength c = oa_N o;
        unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH));
        rep_ok crep; states_ok t st; bcons pos lo <= 100 + DSEQ_BITS * id;
        sh_def K c; sh_inv_mdl t id K c crep j pos lo st; sh_bytes c)
  LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
         temp _op (offset_val (oa_d o + K) (oa_base o));
         temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
         temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
         temp _dictEnd (fs_dictEnd fs); temp _nbSeq (Vint (Int.repr tn));
         temp _isLongOffset (Vint (Int.repr 0));
         lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
         lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
         lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p)
  SEP (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
       seqstate_at Tsh gv (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo st tp crep v_seqState;
       data_at Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr;
       field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p; seq_ptrs p tp; seqtabs_at sht t fm tp; Rt;
       field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p;
       pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o);
       bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)).

Definition sh_inv (t: fse_table * fse_table * fse_table) (tp: val * val * val) (sht: share * share * share)
    (fm: Z * Z * Z) (Rt: mpred) (id: Z) : environ -> mpred :=
  EX K: Z, EX c: list val, EX crep: Z * Z * Z, EX j: Z, EX pos: Z, EX lo: Z, EX st: Z * Z * Z,
    sh_inv_at t tp sht fm Rt id (nbSeq - id) K c crep j pos lo st.

(* after the id-th decode (before its execution): the sequence (ll, ml, ov) is the model's next one *)
Definition sh_mid_mdl0 (t: fse_table * fse_table * fse_table) (id K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) (ll ml ov: Z) : Prop :=
  let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
  sh_hv ->
  forall seqs out' lits' rep2,
    decode_seq_stream tLL tOF tML (iw_s i) nbSeq = Some seqs ->
    exec_seqs (hc_wsize h) rep (hc_hist h) lits (hc_out h) seqs = Some (out', lits', rep2) ->
    sh_cnt out' lits' <= bsm ->
    (exists sq, skipn (Z.to_nat id) seqs = sq :: skipn (Z.to_nat (id + 1)) seqs /\
       sq_ll sq = ll /\ sq_ml sq = ml /\ sq_ov sq = ov) /\
    bs_ready pos lo /\ (id + 1 = nbSeq -> lo = 0) /\
    decode_seqs tLL tOF tML (iw_s i) (Z.to_nat (nbSeq - (id + 1))) sLL sOF sML pos =
      Some (skipn (Z.to_nat (id + 1)) seqs, 0) /\
    exists blk, K = Zlength blk /\ sublist (oa_d o) (oa_d o + K) c = zbytes blk /\
      exec_seqs (hc_wsize h) crep (hc_hist h) (skipn (Z.to_nat j) lits) (hc_out h ++ blk)
        (skipn (Z.to_nat id) seqs) = Some (out', lits', rep2).
Definition sh_mid_mdl (t: fse_table * fse_table * fse_table) (id K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) (ll ml ov: Z) : Prop :=
  sh_mid_mdl0 t id K c crep j pos lo st ll ml ov /\
  xs_mid os rep l lits lxb nbSeq o i h t id K c crep j pos lo st ll ml ov.

Definition sh_mid_at (t: fse_table * fse_table * fse_table) (tp: val * val * val) (sht: share * share * share)
    (fm: Z * Z * Z) (Rt: mpred) (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z)
    (ll ml ov: Z) : environ -> mpred :=
  PROP (0 <= id < nbSeq; 0 <= K; oa_d o + K <= sh_oend; 0 <= j <= Zlength lits; Zlength c = oa_N o;
        unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH));
        rep_ok crep; states_ok t st; bcons pos lo <= 100 + DSEQ_BITS * (id + 1);
        0 <= ll <= LL_VMAX; 3 <= ml <= ML_VMAX; 1 <= ov < 2 ^ 32;
        sh_def K c; sh_mid_mdl t id K c crep j pos lo st ll ml ov; sh_bytes c)
  LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
         temp _op (offset_val (oa_d o + K) (oa_base o));
         temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
         temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
         temp _dictEnd (fs_dictEnd fs); temp _nbSeq (Vint (Int.repr (nbSeq - id)));
         temp _isLongOffset (Vint (Int.repr 0));
         lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
         lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
         lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p)
  SEP (data_at Tsh t_seq (seqrep ll ml (fst (c_offset crep ll ov))) v_sequence;
       seqstate_at Tsh gv (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo st tp
         (snd (c_offset crep ll ov)) v_seqState;
       data_at Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr;
       field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p; seq_ptrs p tp; seqtabs_at sht t fm tp; Rt;
       field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep) p;
       pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
       data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o);
       bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)).

(* ---------- the segments ---------- *)

(* statements 0..8: ostart, oend (maybeNullPtrAdd / litBuffer), op, litPtr, litEnd, prefixStart, vBase,
   dictEnd; the input array split (sh_ctx), the literal fields to sh_lrest + lit_res sh_ls *)
Lemma sh_prologue_ok_oend (b: val) (d c: Z) :
  0 <= c -> (if 0 <? c then offset_val c (offset_val d b) else offset_val d b) = offset_val (d + c) b.
Proof.
  intros Hc. destruct (Z.ltb_spec 0 c).
  - rewrite offset_offset_val; auto.
  - replace c with 0 by lia. rewrite Z.add_0_r; auto.
Qed.

Lemma sh_prologue_ok_add (b: val) (a n: Z) :
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

Lemma sh_prologue_ok_add0 (b: val) (n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong b (Vlong (Int64.repr n))) = offset_val n b.
Proof.
  intros Hb Hn. rewrite <- (isptr_offset_val_zero b) at 1 by auto.
  rewrite sh_prologue_ok_add by auto. rewrite Z.add_0_l; auto.
Qed.

Lemma sh_prologue_ok_litextra (q: val) (v: list val) :
  field_at Ews t_dctx (DOT _litExtraBuffer) v q = data_at Ews (tarray tuchar LITEXTRA_N) v (lit_extra q).
Proof.
  unfold lit_extra. rewrite field_at_data_at. reflexivity.
Qed.

Lemma sh_prologue_ok (HC: sh_ctx) :
  semax sh_Delta S_pre (sq_drop 9 sh_body) sh_SR ->
  semax sh_Delta S_start sh_body sh_SR.
Proof using All.
  intros HK.
  destruct HC as (Ho & Hi & Hns & Hla & Hbsm & Hlb & Hnb & Hnbp & Hos & Hrep & Hfe & Hcap0 & Hlay & Hps & Hvs
    & Hde & HlbD & Hsh1 & Hsh2 & Hob & Hib & Hsplit & Hxr & Hxb_ctx).
  assert (Hb: sh_body = Ssequence (sq_nth 0 sh_body) (Ssequence (sq_nth 1 sh_body) (Ssequence (sq_nth 2 sh_body)
    (Ssequence (sq_nth 3 sh_body) (Ssequence (sq_nth 4 sh_body) (Ssequence (sq_nth 5 sh_body)
    (Ssequence (sq_nth 6 sh_body) (Ssequence (sq_nth 7 sh_body) (Ssequence (sq_nth 8 sh_body)
    (sq_drop 9 sh_body)))))))))) by reflexivity.
  rewrite Hb; clear Hb.
  set (REST := sq_drop 9 sh_body) in *.
  cbv [sq_nth sh_body f_ZSTD_decompressSequences_body fn_body].
  unfold sh_Delta in *; simplify_func_tycontext.
  unfold S_pre, sh_oend, sh_li0, sh_lb, sh_ls, sh_lrest in HK.
  unfold S_start, sh_lf, litfields, frame_fields.
  assert (Hn: 0 <= Zlength lits <= Int64.max_unsigned)
    by (destruct Hla as (_ & ? & _); unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
  assert (HN: Zlength (iw_c i) = iw_N i) by (destruct Hi as (_ & _ & _ & _ & ? & _); auto).
  destruct l as [off| |lb|lb]; [ | | | contradiction Hns].
  - simpl loc_code. Intros.
    forward. forward. apply semax_if_seq. forward_if.
    + forward_call (offset_val (oa_d o) (oa_base o), oa_cap o).
      { destruct Ho as (_ & _ & ? & ? & ? & ?). rep_lia. }
      rewrite sh_prologue_ok_oend by (destruct Ho as (_ & _ & ? & ? & ? & ?); lia).
      forward. forward. forward. forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward. forward.
      apply dec_skipbreak_seq.
      rewrite sh_prologue_ok_add by auto.
      eapply semax_pre; [|exact HK].
      unfold lit_res, lit_base, frame_fields. rewrite HN, Hsplit.
      go_lower.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
      apply andp_right.
      { apply prop_right. rewrite !eqb_type_refl. repeat split; reflexivity. }
      cancel.
    + contradiction H; reflexivity.
  - Intros.
    assert_PROP (field_compatible t_dctx (DOT _litExtraBuffer) p) as Hfc by entailer!.
    pose proof (field_address_isptr _ _ _ Hfc) as Hle. fold (lit_extra p) in Hle.
    forward. forward. apply semax_if_seq. forward_if.
    + forward_call (offset_val (oa_d o) (oa_base o), oa_cap o).
      { destruct Ho as (_ & _ & ? & ? & ? & ?). rep_lia. }
      rewrite sh_prologue_ok_oend by (destruct Ho as (_ & _ & ? & ? & ? & ?); lia).
      forward. forward. forward. forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward. forward.
      apply dec_skipbreak_seq.
      rewrite sh_prologue_ok_add0 by auto.
      simpl lit_base in HK. rewrite Z.add_0_l, isptr_offset_val_zero in HK by auto.
      eapply semax_pre; [|exact HK].
      unfold lit_res, frame_fields.
      rewrite sh_prologue_ok_litextra, Hsplit.
      replace (Zlength (zbytes lits ++ xrest)) with LITEXTRA_N
        by (rewrite Zlength_app, Zlength_map, Hxr by auto; lia).
      go_lower.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)).
      apply andp_right.
      { apply prop_right. rewrite !eqb_type_refl. repeat split; reflexivity. }
      cancel.
    + contradiction H; reflexivity.
  - simpl loc_code. Intros.
    forward. forward. apply semax_if_seq. forward_if.
    + exfalso. unfold LOC_IN_DST in H. apply repr_inj_signed in H; rep_lia.
    + forward. forward.
      forward. forward. forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward. forward.
      apply dec_skipbreak_seq.
      rewrite sh_prologue_ok_add by auto.
      eapply semax_pre; [|exact HK].
      unfold lit_res, lit_base, frame_fields. rewrite Hsplit.
      go_lower.
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
      sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)).
      apply andp_right.
      { apply prop_right. rewrite !eqb_type_refl. repeat split; reflexivity. }
      cancel.
Qed.

(* do { } while (0) with an empty body *)
Ltac sh_init_ok_dw0 :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

(* do { if (0) ...; } while (0) *)
Ltac sh_init_ok_dw0if :=
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: P;
    [ apply ENTAIL_refl
    | forward_if P;
      [ exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end
      | forward; try apply ENTAIL_refl
      | forward; try apply ENTAIL_refl ]
    | ]
  end.

Lemma sh_init_ok_okb (s: list Z) : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. rewrite !andb_true_iff. intros [[_ H1] H2].
  rewrite Zlength_correct. split; [|exact H2].
  rewrite negb_true_iff in *. apply Z.eqb_neq. apply Nat.eqb_neq in H1. lia.
Qed.

(* a stream BIT_initDStream rejects is not a model stream *)
Lemma sh_init_ok_err_mdl (t: fse_table * fse_table * fse_table) (s: list Z) (n: Z) (r: Z * Z * Z)
    (hi out lt: list Z) (w: Z) :
  bs_wf s = false -> n <> 0 -> seqs_model (Some t) s n r hi out lt w = None.
Proof.
  intros Hw Hn. unfold seqs_model. destruct t as [[a b] c].
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn).
  unfold decode_seq_stream.
  destruct (bs_okb s) eqn:E; [rewrite (sh_init_ok_okb s E) in Hw; discriminate|]. reflexivity.
Qed.

(* one ZSTD_initFseState: nb bits read, then a reload; the window only goes down *)
Lemma sh_init_ok_reload (pos lo nb: Z) :
  0 <= lo -> pos <= lo + 64 -> 0 <= nb ->
  0 <= snd (bs_reload (pos - nb) lo) <= lo /\ pos - nb <= snd (bs_reload (pos - nb) lo) + 64.
Proof.
  intros H0 H1 Hn. split; [apply bs_reload_lo; lia|].
  unfold bs_reload.
  destruct (pos - nb <? lo) eqn:E; [apply Z.ltb_lt in E; cbn [snd]; lia|]. apply Z.ltb_ge in E.
  pose proof (Z.div_mod (lo + 64 - (pos - nb)) 8 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (lo + 64 - (pos - nb)) 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Hl.
  pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Hlm.
  destruct (8 <=? lo / 8); [cbn [snd]; lia|].
  destruct (lo / 8 =? 0); [cbn [snd]; lia|].
  destruct (lo / 8 <? (lo + 64 - (pos - nb)) / 8) eqn:E3; cbn [snd]; [apply Z.ltb_lt in E3; lia | lia].
Qed.

(* after BIT_initDStream: the window, at most 64 bits consumed *)
Lemma sh_init_ok_bc0 (s: list Z) :
  bytes_ok s -> bs_wf s = true ->
  0 <= 8 * Z.max 0 (Zlength s - 8) /\ bs_total s <= 8 * Z.max 0 (Zlength s - 8) + 64 /\
  bcons (bs_total s) (8 * Z.max 0 (Zlength s - 8)) <= 64.
Proof.
  intros Hb Hwf. unfold bcons, bs_total. rewrite <- Zlength_correct.
  assert (Hn: 1 <= Zlength s).
  { unfold bs_wf in Hwf. apply andb_true_iff in Hwf as [H1 _]. apply negb_true_iff, Z.eqb_neq in H1.
    pose proof (Zlength_nonneg s). lia. }
  assert (Hlast: 0 <= highbit (last s 0) <= 7).
  { assert (Hl: 0 <= last s 0 < 256).
    { destruct s as [|b r] using rev_ind; [cbn; lia|]. rewrite last_last.
      unfold bytes_ok in Hb. apply Forall_app in Hb as [_ Hb]. inversion Hb; subst. exact H1. }
    unfold highbit. split; [apply Z.log2_nonneg|].
    destruct (Z.eq_dec (last s 0) 0) as [->|Hz]; [cbn; lia|].
    assert (Z.log2 (last s 0) < 8); [|lia]. apply Z.log2_lt_pow2; [lia|]. cbn; lia. }
  lia.
Qed.

(* the tables of tabs_seq (fseEntropy = 1 already stored), borrowed *)
Lemma sh_init_ok_borrow (HG: GLOBALS_obligation) (tLL tOF tML: fse_table) :
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p * seq_where gv p ox KLL tLL *
  seq_where gv p ox KOF tOF * seq_where gv p ox KML tML * dent_of dent_def gv ox * zstd_globals gv |--
  EX tp: val * val * val, EX sht: share * share * share, EX fm: Z * Z * Z, EX Rt: mpred,
    !! (tabs_ok gv p ox (tLL, tOF, tML) tp sht fm Rt) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p * seq_ptrs p tp *
     seqtabs_at sht (tLL, tOF, tML) fm tp * Rt).
Proof.
  eapply derives_trans; [|apply (sh_borrow HG gv p ox (tLL, tOF, tML) 1)].
  unfold tabs_seq. cancel.
Qed.

Lemma sh_init_ok_fc (T t: type) (gfs: list gfield) (v: val) :
  field_compatible t [] (field_address T gfs v) -> field_compatible T gfs v.
Proof.
  unfold field_address. destruct (field_compatible_dec T gfs v); auto. intros [Hp _]. contradiction.
Qed.

Lemma sh_init_ok_fcf (v: val) :
  field_compatible t_seqstate [] v ->
  field_compatible t_seqstate (DOT _DStream) v /\ field_compatible t_seqstate (DOT _stateLL) v /\
  field_compatible t_seqstate (DOT _stateOffb) v /\ field_compatible t_seqstate (DOT _stateML) v.
Proof.
  intros Hc. split; [|split; [|split]]; apply field_compatible_cons; (split; [|exact Hc]); simpl;
    unfold in_members; simpl; auto 10.
Qed.

(* the seqState_t local, split into its fields *)
Lemma sh_init_ok_ss_split (v: val) :
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

(* the literals' place: inside their array, with the 32 cells after them *)
Lemma sh_li_ok (HC: sh_ctx) (c: list val) :
  Zlength c = oa_N o -> 0 <= sh_li0 /\ sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH <= Zlength (lit_arr sh_ls c).
Proof using All.
  intros Hc.
  destruct HC as (Ho & Hi & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & _).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc). destruct Hla as (_ & Hn & Hll).
  unfold sh_ls, sh_li0, lit_arr. destruct l; simpl in *.
  - destruct Hll as (? & ? & _). destruct Hi as (_ & _ & _ & _ & HiN & _). unfold WILDCOPY_OVERLENGTH in *; lia.
  - specialize (Hx eq_refl). rewrite Zlength_app, Zlength_map, Hx.
    unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia.
  - destruct Hll as (? & ? & _). unfold WILDCOPY_OVERLENGTH in *; lia.
  - contradiction.
Qed.

(* at the start: the history, the extDict and the literals are defined (seqs_spec's hist_def, lits_at,
   lit_slack_def; litExtraBuffer holds bytes) *)
Lemma sh_rd0 (HC: sh_ctx) (HD: sh_dctx) : 0 < oa_cap o -> sh_rd (oa_c o).
Proof using All.
  intros Hcap. destruct HD as [Hhd Hsl].
  destruct HC as (Ho & Hi & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & Hxb).
  specialize (Hlay Hcap). destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  destruct Hla as (Hlb & Hn & Hll).
  assert (Hxo: exec_ext_ok (hc_ext h) (oa_c o)).
  { unfold exec_ext_ok. destruct (hc_ext h); simpl in *; try tauto; lia. }
  split; [apply (hist_def_prefix _ _ _ _ Hhd); lia|]. split; [apply (hist_def_ext _ (oa_d o) (hc_ps h)); auto; lia|].
  unfold sh_ls, sh_li0, lit_arr. destruct l as [off| |lb|lb]; simpl in Hll, Hsl.
  - destruct Hll as (Hoff & HoN & Hsub & Hsl32). destruct Hi as (_ & _ & _ & _ & HiN & _).
    apply (Forall_def_join _ off (off + Zlength lits)); try (unfold WILDCOPY_OVERLENGTH in *; lia); [| exact Hsl32].
    rewrite Hsub. apply sh_release_zbytes. exact Hlb.
  - specialize (Hxb eq_refl). apply Forall_sublist. apply Forall_app.
    split; [apply sh_release_zbytes; exact Hlb | exact Hxb].
  - destruct Hll as (Hdlb & HlbN & Hsub).
    apply (Forall_def_join _ lb (lb + Zlength lits)); try (unfold WILDCOPY_OVERLENGTH in *; lia); [| exact Hsl].
    rewrite Hsub. apply sh_release_zbytes. exact Hlb.
  - contradiction.
Qed.

(* the 6 statements of initialisation of BIG (fseEntropy = 1; prevOffset = rep; BIT_initDStream and its
   error return; the tables borrowed (sh_borrow); 3 ZSTD_initFseState; the model: loop_init_model), CPS to
   the loop invariant at 0 *)
Lemma sh_init_ok (HG: GLOBALS_obligation) (HC: sh_ctx) (HX: sh_lx) (HD: sh_dctx) (t: fse_table * fse_table * fse_table)
    (Hos: os = Some t) (Hnb: 0 < nbSeq) :
  (forall tp sht fm Rt, tabs_ok gv p ox t tp sht fm Rt ->
     semax sh_Delta (sh_inv t tp sht fm Rt 0) sh_BREST (overridePost sh_aft sh_SR)) ->
  semax sh_Delta S_pre sh_BIG (overridePost sh_aft sh_SR).
Proof using All.
  intros HK.
  revert HK. unfold sh_Delta.
  simplify_func_tycontext' (func_tycontext f_ZSTD_decompressSequences_body Vprog LOOP_GB nil).
  intros HK.
  unfold sh_BIG, sh_body. cbn [sq_nth fn_body f_ZSTD_decompressSequences_body].
  unfold S_pre.
  unfold sh_SR, sh_POST.
  destruct t as [[tLL tOF] tML]. rewrite Hos. unfold tabs_seq at 1. Intros.
  forward.
  assert_PROP (field_compatible t_seqstate [] v_seqState) as Hfc. { entailer!. }
  destruct (sh_init_ok_fcf v_seqState Hfc) as (HfDS & HfLLs & HfOFs & HfMLs).
  rewrite (sh_init_ok_ss_split v_seqState).
  pose proof HC as HC'.
  destruct HC' as (Hoa & Hiw & Hns & Hla & Hbsm & Hll & Hnbr & Hpos & Hso & Hrep & Hfe & Hc0 & Hlay & Hp1 & Hp2
    & Hp3 & Hldst & Hr1 & Hr2 & Hib1 & Hib2 & Heq & Hxr & Hxb_ctx).
  destruct rep as [[r1 r2] r3] eqn:Erep.
  destruct Hrep as (Hr1b & Hr2b & Hr3b).
  forward_for_simple_bound 3 (EX k: Z,
    PROP ()
    LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
           temp _op (offset_val (oa_d o) (oa_base o));
           temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
           temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
           temp _dictEnd (fs_dictEnd fs);
           lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
           lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
           lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p;
           temp _seqStart (offset_val (iw_off i) (iw_base i));
           temp _seqSize (Vlong (Int64.repr (Zlength (iw_s i))));
           temp _nbSeq (Vint (Int.repr nbSeq)); temp _isLongOffset (Vint (Int.repr 0)))
    SEP (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
         data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v_seqState);
         data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v_seqState);
         data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v_seqState);
         data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v_seqState);
         field_at Tsh t_seqstate (DOT _prevOffset)
           (map (fun r => Vlong (Int64.repr r)) (sublist 0 k [r1; r2; r3]) ++ Zrepeat Vundef (3 - k))
           v_seqState;
         data_at Tsh (tptr tuchar) (offset_val sh_li0 sh_lb) v_litPtr;
         zstd_globals gv; field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p;
         seq_where gv p ox KLL tLL; seq_where gv p ox KOF tOF; seq_where gv p ox KML tML;
         dent_of dent_def gv ox;
         field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (r1, r2, r3)) p;
         pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
         data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
         bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)))%assert.
  - entailer!. unfold field_at_. apply derives_refl.
  - assert (Hz: forall d, @Znth val d i0 (rep_vals (r1, r2, r3)) = Vint (Int.repr (Znth i0 [r1; r2; r3]))).
    { intros d. assert (i0 = 0 \/ i0 = 1 \/ i0 = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity. }
    forward.
    { rewrite Hz. entailer!. }
    forward.
    assert (Hz2: forall d, @Znth val d i0 [Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3)] =
                           Vint (Int.repr (Znth i0 [r1; r2; r3]))) by exact Hz.
    rewrite !Hz2.
    assert (Hl: upd_Znth i0
       (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 i0 [r1; r2; r3]) ++ Zrepeat Vundef (3 - i0))
       (force_val (sem_cast_i2l Unsigned (Vint (Int.repr (Znth i0 [r1; r2; r3]))))) =
       map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 (i0 + 1) [r1; r2; r3]) ++
       Zrepeat Vundef (3 - (i0 + 1))).
    { assert (i0 = 0 \/ i0 = 1 \/ i0 = 2) as [ -> | [ -> | -> ] ] by lia; cbn;
        rewrite Int.unsigned_repr by rep_lia; reflexivity. }
    rewrite Hl. entailer!.
  - change (map (fun r : Z => Vlong (Int64.repr r)) (sublist 0 3 [r1; r2; r3]) ++ Zrepeat Vundef (3 - 3))
      with (rep64_vals (r1, r2, r3)).
    assert (Hsub: sublist 0 (0 + Zlength (iw_s i)) (iw_s i) = iw_s i)
      by (rewrite Z.add_0_l; apply sublist_same; lia).
    pose proof Hiw as (Hiw1 & Hiw2 & Hiw3 & Hiw4 & Hiw5 & Hiw6 & Hiw7 & Hiw8).
    destruct (bs_wf (iw_s i)) eqn:Ewf.
    + assert (Hst: offset_val 0 (offset_val (iw_off i) (iw_base i)) = offset_val (iw_off i) (iw_base i))
        by (destruct (iw_base i); try contradiction; simpl; rewrite Ptrofs.add_zero; reflexivity).
      match goal with |- semax _ ?P _ _ => forward_loop P break: (
        PROP ()
        LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
               temp _op (offset_val (oa_d o) (oa_base o));
               temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
               temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
               temp _dictEnd (fs_dictEnd fs);
               lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
               lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
               lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p;
               temp _seqStart (offset_val (iw_off i) (iw_base i));
               temp _seqSize (Vlong (Int64.repr (Zlength (iw_s i))));
               temp _nbSeq (Vint (Int.repr nbSeq)); temp _isLongOffset (Vint (Int.repr 0)))
        SEP (BIT_DStream_rep Tsh gv (iw_s i) (offset_val (iw_off i) (iw_base i)) (bs_total (iw_s i))
               (8 * Z.max 0 (Zlength (iw_s i) - 8)) (field_address t_seqstate (DOT _DStream) v_seqState);
             bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); zstd_globals gv;
             data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
             data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v_seqState);
             data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v_seqState);
             data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v_seqState);
             field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals (r1, r2, r3)) v_seqState;
             data_at Tsh (tptr tuchar) (offset_val sh_li0 sh_lb) v_litPtr;
             field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p;
             seq_where gv p ox KLL tLL; seq_where gv p ox KOF tOF; seq_where gv p ox KML tML;
             dent_of dent_def gv ox;
             field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (r1, r2, r3)) p;
             pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
             data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
             Ri; ext_res (hc_ext h)))%assert end.
      * apply ENTAIL_refl.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) v_seqState, sh2,
          offset_val (iw_off i) (iw_base i), iw_s i, 0, Zlength (iw_s i), gv).
        { entailer!. unfold field_address at 1. rewrite if_true by (eapply sh_init_ok_fc; eassumption).
          simpl. destruct (iw_base i); try contradiction. reflexivity. }
        rewrite Hsub, Ewf, Hst. Intros r. subst r.
        forward_call (Zlength (iw_s i)).
        replace (is_error_code (Zlength (iw_s i))) with false
          by (symmetry; unfold is_error_code; apply Z.ltb_ge; rep_lia).
        forward_if.
        { exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
        forward. entailer!.
      * sep_apply (sh_init_ok_borrow HG tLL tOF tML).
        Intros tp sht fm Rt.
        destruct tp as [[pLL pOF] pML]. destruct sht as [[sLL sOF] sML]. destruct fm as [[fLL fOF] fML].
        rename H into HT. pose proof HT as (HTsh & _ & _). destruct HTsh as (HsLL & HsOF & HsML).
        unfold seq_ptrs, seqtabs_at.
        pose proof (sh_init_ok_bc0 (iw_s i) Hiw7 Ewf) as (Hb0 & Hb1 & Hb2).
        rewrite Hos in Hso. destruct Hso as (HfLL & HfOF & HfML).
        pose proof HfLL as (HlLL & _). pose proof HfOF as (HlOF & _). pose proof HfML as (HlML & _).
        cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
        repeat flatten_sepcon_in_SEP.
        assert_PROP (isptr pLL /\ isptr pOF /\ isptr pML) as Hp.
        { unfold seqtab_at_fm. Intros. entailer!. }
        destruct Hp as (HpLL & HpOF & HpML).
        assert (Hbso: bit_src_ok (iw_s i) (offset_val (iw_off i) (iw_base i)) (offset_val (iw_off i) (iw_base i))
                  (iw_s i) 0).
        { split; [rewrite Hst; reflexivity|]. split; [lia|]. split; [lia|].
          rewrite Z.add_0_l; apply sublist_same; lia. }
        set (pos0 := bs_total (iw_s i)) in *. set (lo0 := (8 * Z.max 0 (Zlength (iw_s i) - 8))%Z) in *.
        unfold bcons in Hb2.
        forward.
        forward_call (Tsh, field_address t_seqstate (DOT _stateLL) v_seqState, Tsh,
          field_address t_seqstate (DOT _DStream) v_seqState, gv, iw_s i, offset_val (iw_off i) (iw_base i),
          pos0, lo0, sh2, offset_val (iw_off i) (iw_base i), iw_s i, 0, sLL, KLL, tLL, fLL, pLL).
        { entailer!. unfold field_address. rewrite !if_true by assumption. reflexivity. }
        { unfold bcons; rep_lia. }
        Intros v1.
        destruct (sh_init_ok_reload pos0 lo0 (ft_log tLL) Hb0 Hb1 ltac:(lia)) as (Hl1 & Hp1').
        set (pos1 := pos0 - ft_log tLL) in *. set (lo1 := snd (bs_reload pos1 lo0)) in *.
        forward.
        forward_call (Tsh, field_address t_seqstate (DOT _stateOffb) v_seqState, Tsh,
          field_address t_seqstate (DOT _DStream) v_seqState, gv, iw_s i, offset_val (iw_off i) (iw_base i),
          pos1, lo1, sh2, offset_val (iw_off i) (iw_base i), iw_s i, 0, sOF, KOF, tOF, fOF, pOF).
        { entailer!. unfold field_address. rewrite !if_true by assumption. reflexivity. }
        { unfold bcons; rep_lia. }
        Intros v2.
        destruct (sh_init_ok_reload pos1 lo1 (ft_log tOF) ltac:(lia) Hp1' ltac:(lia)) as (Hl2 & Hp2').
        set (pos2 := pos1 - ft_log tOF) in *. set (lo2 := snd (bs_reload pos2 lo1)) in *.
        forward.
        forward_call (Tsh, field_address t_seqstate (DOT _stateML) v_seqState, Tsh,
          field_address t_seqstate (DOT _DStream) v_seqState, gv, iw_s i, offset_val (iw_off i) (iw_base i),
          pos2, lo2, sh2, offset_val (iw_off i) (iw_base i), iw_s i, 0, sML, KML, tML, fML, pML).
        { entailer!. unfold field_address. rewrite !if_true by assumption. reflexivity. }
        { unfold bcons; rep_lia. }
        Intros v3.
        destruct (sh_init_ok_reload pos2 lo2 (ft_log tML) ltac:(lia) Hp2' ltac:(lia)) as (Hl3 & Hp3').
        set (pos3 := pos2 - ft_log tML) in *. set (lo3 := snd (bs_reload pos3 lo2)) in *.
        unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
        unfold sh_SR, sh_POST in HK. rewrite Hos, Erep in HK.
        eapply semax_pre; [| apply (HK (pLL, pOF, pML) (sLL, sOF, sML) (fLL, fOF, fML) Rt HT)].
        assert (HM0: sh_inv_mdl0 (tLL, tOF, tML) 0 0 (oa_c o) (r1, r2, r3) 0 pos3 lo3 (v1, v2, v3)).
        { unfold sh_inv_mdl0. intros _ seqs out' lits' rep2 Hd Hx _.
          destruct (loop_init_model tLL tOF tML (iw_s i) nbSeq seqs v1 v2 v3 Hiw7 Ewf HfLL HfOF HfML
            ltac:(assumption) ltac:(assumption) ltac:(assumption) Hd) as (Hrd & Hds).
          split; [exact Hrd|]. split; [lia|]. split; [rewrite Z.sub_0_r; exact Hds|].
          exists nil. split; [reflexivity|]. split; [rewrite Z.add_0_r, sublist_nil; reflexivity|].
          rewrite app_nil_r. rewrite Erep in Hx. exact Hx. }
        assert (HM: sh_inv_mdl (tLL, tOF, tML) 0 0 (oa_c o) (r1, r2, r3) 0 pos3 lo3 (v1, v2, v3)).
        { split; [exact HM0|]. rewrite <- Erep.
          apply (xs_init fs os rep l lits lxb nbSeq o i h tLL tOF tML v1 v2 v3 (sh_xs_ctx HC HX) Hos Hnb Ewf);
            assumption. }
        assert (Hoe: oa_d o + 0 <= sh_oend).
        { destruct Hoa as (_ & _ & _ & Hd0 & Hc0' & _). unfold sh_oend. destruct l; lia. }
        assert (Hdf: sh_def 0 (oa_c o)).
        { split; [rewrite Z.add_0_r, sublist_nil; constructor | intros Hcap; apply (sh_rd0 HC HD Hcap)]. }
        unfold sh_inv. Exists 0 (oa_c o) (r1, r2, r3) 0 pos3 lo3 (v1, v2, v3).
        unfold sh_inv_at, seqstate_at. rewrite Erep, Z.sub_0_r, !Z.add_0_r.
        rewrite (field_at_data_at _ t_seqstate (DOT _stateLL)), (field_at_data_at _ t_seqstate (DOT _stateOffb)),
          (field_at_data_at _ t_seqstate (DOT _stateML)).
        change (nested_field_type t_seqstate (DOT _stateLL)) with t_fsestate.
        change (nested_field_type t_seqstate (DOT _stateOffb)) with t_fsestate.
        change (nested_field_type t_seqstate (DOT _stateML)) with t_fsestate.
        assert (Hbc: bcons pos3 lo3 <= 100) by (unfold bcons, pos3, pos2, pos1 in *; lia).
        assert (Hso3: states_ok (tLL, tOF, tML) (v1, v2, v3)) by (unfold states_ok; lia).
        assert (Huo: unchanged_outside (oa_c o) (oa_c o) (oa_d o) (Z.min sh_oend (oa_d o + WILDCOPY_OVERLENGTH)))
          by (intros ? ? ?; reflexivity).
        assert (Hrok: rep_ok (r1, r2, r3)) by (unfold rep_ok; lia).
        assert (HN: Zlength (oa_c o) = oa_N o) by apply Hoa.
        unfold seq_ptrs, seqtabs_at.
        entailer!.
    + match goal with |- semax _ ?P _ _ =>
        forward_loop P continue: (PROP (False) LOCAL () SEP ()) break: (PROP (False) LOCAL () SEP ()) end.
      * entailer!.
      * forward_call (Tsh, field_address t_seqstate (DOT _DStream) v_seqState, sh2,
          offset_val (iw_off i) (iw_base i), iw_s i, 0, Zlength (iw_s i), gv).
        { entailer!. unfold field_address at 1. rewrite if_true by (eapply sh_init_ok_fc; eassumption).
          simpl. destruct (iw_base i); try contradiction. reflexivity. }
        rewrite Hsub, Ewf. Intros r.
        assert (Hrr: 0 <= r <= Int64.max_unsigned) by lia.
        forward_call r.
        match goal with He: is_error_code r = true |- _ => rewrite He end.
        forward_if.
        sh_init_ok_dw0. sh_init_ok_dw0if. sh_init_ok_dw0. sh_init_ok_dw0.
        forward.
        { Exists (Int64.unsigned (Int64.repr (-20))) (oa_c o) (r1, r2, r3).
          rewrite (sh_init_ok_ss_split v_seqState).
          sep_apply (sh_release HC HX).
          sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _prevOffset) (rep64_vals (r1, r2, r3)) v_seqState).
          sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val sh_li0 sh_lb) v_litPtr).
          replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          rewrite sh_init_ok_err_mdl by (first [exact Ewf | lia]).
          unfold tabs_seq. rewrite Int64.repr_unsigned.
          assert (Hderr: dec_err (Int64.unsigned (Int64.repr (-20)))) by exact (sh_dec_err 20 ltac:(lia) ltac:(lia) ltac:(lia)).
          assert (HXN: seqs_exact os (r1, r2, r3) l lits lxb nbSeq o i h (Int64.unsigned (Int64.repr (-20))) (oa_c o)
                         (r1, r2, r3)).
          { rewrite <- Erep. apply xs_exact_none; [reflexivity|].
            apply (xs_init_err fs os rep l lits lxb nbSeq o i h (tLL, tOF, tML) (sh_xs_ctx HC HX) Hos Hnb Ewf). }
          entailer!.
          split; [apply Hoa|]. split; [unfold rep_ok; lia|].
          split; [intros Hx; vm_compute in Hx; discriminate Hx | rewrite <- Hos; exact HXN]. }
        exfalso; apply Int.one_not_zero; assumption.
Qed.

(* sh_dec_ok's helpers: the model step after one decode, the bitstream facts of seqstate_at *)
Lemma sh_dec_ok_skipn (A: Type) (n: Z) (xs rest: list A) (x: A) :
  0 <= n -> skipn (Z.to_nat n) xs = x :: rest -> rest = skipn (Z.to_nat (n + 1)) xs.
Proof.
  intros Hn H. replace (Z.to_nat (n + 1)) with (1 + Z.to_nat n)%nat by lia.
  rewrite <- skipn_skipn, H. reflexivity.
Qed.

Lemma sh_dec_ok_mdl (t: fse_table * fse_table * fse_table) (id K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) (pos' lo': Z) (st': Z * Z * Z) (ll ml ov: Z) :
  seqs_ok (Some t) -> states_ok t st -> 0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
  0 <= id < nbSeq -> 0 <= lo' <= lo ->
  ((nbSeq - id =? 1) = true -> st' = st) ->
  (bs_ready pos lo ->
   forall sq stn pn,
     (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
      dseq_one tLL tOF tML (iw_s i) (nbSeq - id =? 1) sLL sOF sML pos) = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     ((nbSeq - id =? 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
  sh_inv_mdl0 t id K c crep j pos lo st ->
  sh_mid_mdl0 t id K c crep j pos' lo' st' ll ml ov.
Proof.
  intros Hso Hst H0lo H8 Hplo Hid Hlo' Hlast Hspec Hinv.
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML]; destruct st' as [[sLL' sOF'] sML'].
  destruct Hso as (HfLL & HfOF & HfML). destruct Hst as (HsLL & HsOF & HsML).
  unfold sh_inv_mdl0, sh_mid_mdl0 in *. cbv beta iota zeta in Hinv, Hspec |- *. intros Hhv seqs out' lits' rep2 Hd He Hc.
  destruct (Hinv Hhv seqs out' lits' rep2 Hd He Hc) as (Hr & _ & Hds & Hex).
  assert (Hk: Z.to_nat (nbSeq - id) = S (Z.to_nat (nbSeq - id - 1))) by lia.
  rewrite Hk in Hds.
  destruct (loop_dec_step _ _ _ _ _ _ _ _ _ _ Hds) as (sq & a & b & c0 & pn & rest & Hl & Hone & Hrest & Hk0).
  assert (Hle: Nat.eqb (Z.to_nat (nbSeq - id - 1)) 0 = (nbSeq - id =? 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (nbSeq - id - 1)) 0); destruct (Z.eqb_spec (nbSeq - id) 1); lia. }
  rewrite Hle in Hone.
  destruct (Hspec Hr sq (a, b, c0) pn Hone) as (Hll & Hml & Hov & Hpn & Hnl).
  pose proof (sh_dec_ok_skipn _ id seqs rest sq ltac:(lia) Hl) as Hrs.
  destruct (nbSeq - id =? 1) eqn:EL.
  - apply Z.eqb_eq in EL.
    destruct Hk0 as [Hr0 Hp0]; [lia|]. subst rest pn. subst pos'.
    specialize (Hlast eq_refl). injection Hlast as -> -> ->.
    assert (Hlo0: lo' = 0) by (eapply (loop_end_lo tLL tOF tML (iw_s i) sLL sOF sML pos lo lo' sq (a, b, c0)); eauto).
    subst lo'.
    split; [exists sq; repeat split; auto|].
    split; [left; reflexivity|]. split; [intros; reflexivity|].
    split; [replace (Z.to_nat (nbSeq - (id + 1))) with O by lia; simpl; rewrite Hr0; reflexivity|].
    exact Hex.
  - apply Z.eqb_neq in EL. destruct (Hnl eq_refl) as [Hst' Hrd]. injection Hst' as -> -> ->. subst pos' rest.
    split; [exists sq; repeat split; auto|].
    split; [exact Hrd|]. split; [intros; lia|].
    split; [replace (Z.to_nat (nbSeq - (id + 1))) with (Z.to_nat (nbSeq - id - 1)) by lia; exact Hrest|].
    exact Hex.
Qed.

Lemma sh_dec_ok_bit (sh: share) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (q: val) :
  seqstate_at sh gv s start pos lo st tp r q |-- !! bit_inv s pos lo.
Proof.
  unfold seqstate_at, BIT_DStream_rep. destruct st as [[a b] c0]; destruct tp as [[x y] z].
  Intros ptr lim. entailer!.
Qed.

(* one decode (the id-th sequence; isLast iff nbSeq - id = 1): DEC's spec, loop_dec_step, loop_end_lo *)
Lemma sh_dec_ok (HC: sh_ctx) (t: fse_table * fse_table * fse_table) (Hos: os = Some t)
    (tp: val * val * val) (sht: share * share * share) (fm: Z * Z * Z) (Rt: mpred)
    (HT: tabs_ok gv p ox t tp sht fm Rt)
    (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z) (Hid: id < nbSeq) :
  semax sh_Delta (sh_inv_at t tp sht fm Rt id (nbSeq - id) K c crep j pos lo st) sh_DEC
    (normal_ret_assert
       (EX pos': Z, EX lo': Z, EX st': Z * Z * Z, EX ll: Z, EX ml: Z, EX ov: Z,
          sh_mid_at t tp sht fm Rt id K c crep j pos' lo' st' ll ml ov)).
Proof using All.
  unfold sh_DEC, sh_LB, sh_LOOP, sh_BIG, sh_body. simpl fn_body. cbv [sq_nth sq_drop].
  assert (HC' := HC).
  destruct HC' as (_ & _ & _ & _ & _ & _ & Hnb & _ & Hso & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh2 & _ & Hib & _ & _).
  rewrite Hos in Hso. destruct HT as (Hsht & _ & _).
  unfold sh_inv_at. Intros. destruct H9 as [H9 H9x].
  assert_PROP (bit_inv (iw_s i) pos lo) as HBI.
  { sep_apply (sh_dec_ok_bit Tsh (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo st tp crep v_seqState).
    entailer!. }
  unfold sh_Delta; simplify_func_tycontext.
  forward_call (gv, Tsh, v_sequence, Tsh, v_seqState, iw_s i, offset_val (iw_off i) (iw_base i), pos, lo, st, t,
                tp, sht, fm, crep, sh2, offset_val (iw_off i) (iw_base i), iw_s i, 0, 0, (nbSeq - id =? 1)).
  { go_lower. apply prop_right. simpl. unfold Int.eq.
    rewrite !Int.unsigned_repr by (unfold LONGNBSEQ in *; rep_lia).
    destruct (Z.eqb_spec (nbSeq - id) 1); destruct (zeq (nbSeq - id) 1); try lia; reflexivity. }
  { split; [|split].
    - unfold bit_src_ok. rewrite isptr_offset_val_zero by (apply isptr_offset_val'; auto).
      split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity].
    - destruct crep as [[r1 r2] r3]. unfold rep_ok, rep64_ok, SIZE_MAX in *. lia.
    - unfold bcons, DSEQ_BITS, LONGNBSEQ in *. rep_lia. }
  Intros vret. destruct vret as [[[[[ll ml] ov] st'] pos'] lo']. Intros. cbn [fst snd] in *.
  assert (HM: sh_mid_mdl t id K c crep j pos' lo' st' ll ml ov).
  { destruct HBI as (_ & _ & H0lo & H8lo & _ & Hplo & _). split.
    - apply (sh_dec_ok_mdl t id K c crep j pos lo st pos' lo' st' ll ml ov); auto; lia.
    - apply (xs_dec_step os rep l lits lxb nbSeq o i h t id K c crep j pos lo st pos' lo' st' ll ml ov);
        auto; lia. }
  assert (HB: bcons pos' lo' <= 100 + DSEQ_BITS * (id + 1)) by (unfold bcons, DSEQ_BITS in *; lia).
  Exists pos' lo' st' ll ml ov. unfold sh_mid_at. entailer!.
Qed.

(* the facts of exec_spec's precondition and the history pointers *)
Lemma sh_exec_ok_pre (HC: sh_ctx) (c: list val) (K j: Z) :
  Zlength c = oa_N o -> 0 <= K -> oa_d o + K <= sh_oend -> 0 <= j <= Zlength lits -> 0 < oa_cap o ->
  Zlength c <= 2 ^ 63 - 1 /\ 0 <= hc_ps h <= oa_d o + K /\ sh_oend <= Zlength c /\
  sh_oend <= oa_d o + oa_cap o /\
  match sh_ls with
  | LitSep shl _ cl =>
      readable_share shl /\ 0 <= sh_li0 + j <= sh_li0 + Zlength lits /\
      sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH <= Zlength cl
  | LitIn => sh_oend <= sh_li0 + j <= sh_li0 + Zlength lits /\
      sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH <= Zlength c
  end /\
  exec_ext_ok (hc_ext h) c /\ is_pointer_or_null (fs_dictEnd fs) /\
  fs_prefixStart fs = offset_val (hc_ps h) (oa_base o) /\
  fs_virtualStart fs = offset_val (hc_ps h - ext_len (hc_ext h)) (oa_base o) /\
  dict_end (hc_ext h) (oa_base o) (fs_dictEnd fs) = fs_dictEnd fs.
Proof using All.
  intros Hc HK HKe Hj Hcap.
  destruct HC as (Ho & Hi & Hns & Hla & Hbsm & Hnl & Hnb & Hnc & Hso & Hrep & Hfe & Hc0 & Hlay & Hpps & Hpvs &
                  Hpde & Hldst & Hsh1 & Hsh2 & Hob & Hib & Hieq & Hx & Hxb_ctx).
  specialize (Hlay Hcap). destruct Hlay as (Hps & Hfps & Hfvs & Hel & Hext).
  destruct Ho as (Hosh & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hla as (Hlb & Hn & Hll). unfold WILDCOPY_OVERLENGTH in *.
  assert (Hoe: sh_oend <= oa_d o + oa_cap o /\ sh_oend <= Zlength c).
  { unfold sh_oend. pose proof (Zlength_nonneg lits). destruct l; try lia; try (destruct Hll as (? & ? & _); lia). }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { unfold sh_ls, sh_li0, sh_oend. destruct l.
    - destruct Hi as (? & ? & ? & ? & ? & _). destruct Hll as (? & ? & _). split; [auto|]. lia.
    - split; [auto|]. rewrite Zlength_app, Zlength_map, Hx by reflexivity.
      unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia.
    - destruct Hll as (? & ? & _). lia.
    - contradiction. }
  split.
  { unfold exec_ext_ok. destruct (hc_ext h); simpl in *; try tauto; lia. }
  split; [auto|]. split; [auto|]. split; [auto|].
  destruct (hc_ext h); simpl in *; try tauto; symmetry; tauto.
Qed.

(* the seqState_t local, split into its fields (as sh_init_ok_ss_split) *)
Lemma sh_exec_ok_ss_split (v: val) :
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

Lemma sh_exec_ok_ss (gv0: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv0 s start pos lo st tp r v |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite (sh_exec_ok_ss_split v). unfold seqstate_at, BIT_DStream_rep.
  destruct st as [[a b] c]; destruct tp as [[x y] z]. Intros ptr lim.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at.
  repeat (sep_apply data_at_data_at_). cancel.
Qed.

(* local copies of the proved BlkSeqLoopModel helpers of loop_exec_step *)
Lemma sh_exec_ok_mdl_rep_ok (crep: Z * Z * Z) (ll ov off: Z) (crep': Z * Z * Z) :
  rep_ok crep -> 1 <= ov < 2 ^ 32 -> resolve_offset crep ll ov = Some (off, crep') ->
  1 <= off /\ rep_ok crep'.
Proof using All.
  destruct crep as [[r1 r2] r3]. unfold rep_ok, resolve_offset. intros (H1 & H2 & H3) Hov H.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [inversion H; subst; lia|].
  destruct (r1 - 1 <=? 0) eqn:E4; [discriminate|]. apply Z.leb_gt in E4. inversion H; subst; lia.
Qed.

Lemma sh_exec_ok_mdl_rep64 (crep: Z * Z * Z) : rep_ok crep -> rep64_ok crep.
Proof using All. destruct crep as [[r1 r2] r3]. unfold rep_ok, rep64_ok, SIZE_MAX. lia. Qed.

(* the history the model sees is unchanged in the current array *)
Lemma sh_exec_ok_mdl_hist_view (c0 c: list val) (d ps cap bsm0: Z) (e: ext_seg) (hist out: list Z) (wsize: Z) :
  0 <= ps <= d -> 0 <= cap -> d + cap <= Zlength c -> Zlength c0 = Zlength c -> 0 <= bsm0 ->
  hist_view c0 d ps e hist out wsize -> ext_clear d ps cap bsm0 e hist out wsize ->
  ext_in_bounds e (Zlength c) ->
  unchanged_outside c0 c d (d + Z.min cap (bsm0 + WILDCOPY_OVERLENGTH)) ->
  hist_view c d ps e hist out wsize.
Proof using All.
  intros Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hu k Hk.
  destruct (Hhv k Hk) as [Hle Hch]. split; [exact Hle|]. rewrite <- Hch. unfold chist.
  assert (Hk1: 1 <= k) by lia.
  destruct (k <=? d - ps) eqn:E.
  - apply Z.leb_le in E. apply Hu; lia.
  - apply Z.leb_gt in E. destruct e as [|e1 elen|sh eb en ec e1 elen]; try reflexivity.
    simpl in Hcl, Hb. specialize (Hcl k ltac:(lia)).
    assert (0 <= Z.min cap (bsm0 + WILDCOPY_OVERLENGTH)) by (unfold WILDCOPY_OVERLENGTH; lia).
    apply Hu; lia.
Qed.

(* the offset is in the C's history *)
Lemma sh_exec_ok_mdl_off (c0: list val) (d ps: Z) (e: ext_seg) (hist out: list Z) (wsize off nb ll: Z) :
  0 <= ps <= d -> 0 <= ext_len e -> 0 <= nb -> 0 <= ll ->
  hist_view c0 d ps e hist out wsize ->
  1 <= off -> off <= Zlength hist + Zlength out + nb + ll -> off <= wsize + Zlength hist ->
  off <= d + nb + ll - ps + ext_len e.
Proof using All.
  intros Hps He Hnb Hll Hhv Ho1 Ho2 Ho3.
  assert (Hho: Zlength (hist ++ out) = Zlength hist + Zlength out) by apply Zlength_app.
  destruct (Z_le_gt_dec off (Zlength hist + Zlength out)) as [Hle|Hgt].
  - destruct (Hhv off) as [H _]; [rewrite Hho; lia|]. lia.
  - destruct (Z_le_gt_dec 1 (Zlength hist + Zlength out)) as [H1|H1]; [|lia].
    destruct (Hhv (Zlength hist + Zlength out)) as [H _]; [rewrite Hho; lia|]. lia.
Qed.

Lemma sh_exec_ok_mdl_ext_read (e: ext_seg) (d ps cap bsm0: Z) (hist out: list Z) (wsize off nb ll lo ml E: Z) :
  ext_clear d ps cap bsm0 e hist out wsize ->
  0 <= nb -> 0 <= ll -> nb + ll <= bsm0 -> E <= d + cap ->
  off <= Zlength hist + Zlength out + nb + ll -> off <= wsize + Zlength hist ->
  ext_read_ok e (d + nb + lo) E (ll - lo) ml off ps.
Proof using All.
  intros Hcl Hnb Hll Hb HE Ho1 Ho2.
  destruct e as [|e1 elen|sh eb en ec e1 elen]; try exact I. unfold ext_read_ok. simpl in Hcl.
  replace (d + nb + lo + (ll - lo)) with (d + nb + ll) by lia.
  destruct (Z_le_gt_dec off (d + nb + ll - ps)) as [H|H]; [left; exact H|right; left].
  rewrite Zlength_app in Hcl. specialize (Hcl (off - nb - ll) ltac:(lia)).
  unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

(* loop_exec_step without bytes_ok mb; mb is the match copy's tail *)
Lemma sh_exec_ok_mdl_core (c0 c: list val) (d ps cap bsm0: Z) (e: ext_seg) (hist out: list Z) (wsize: Z)
    (blk lr: list Z) (lo: Z) (sq: sequence) (rest: list sequence) (crep: Z * Z * Z)
    (out' lits0': list Z) (rep2: Z * Z * Z) :
  0 <= ps <= d -> 0 <= cap -> d + cap <= Zlength c -> Zlength c0 = Zlength c -> 0 <= bsm0 ->
  hist_view c0 d ps e hist out wsize -> ext_clear d ps cap bsm0 e hist out wsize ->
  ext_in_bounds e (Zlength c) -> 0 <= ext_len e ->
  unchanged_outside c0 c d (d + Z.min cap (bsm0 + WILDCOPY_OVERLENGTH)) ->
  bytes_ok lr -> rep_ok crep ->
  exec_seqs wsize crep hist lr (out ++ blk) (sq :: rest) = Some (out', lits0', rep2) ->
  Zlength out' - Zlength out + Zlength lits0' <= bsm0 ->
  0 <= lo <= sq_ll sq -> 0 <= sq_ml sq -> 1 <= sq_ov sq < 2 ^ 32 ->
  sublist d (d + Zlength blk + lo) c = zbytes (blk ++ firstn (Z.to_nat lo) lr) ->
  let ll := sq_ll sq in let ml := sq_ml sq in
  let k := d + Zlength blk in
  let L := firstn (Z.to_nat ll) lr in
  exists off crep' mb,
    c_offset crep ll (sq_ov sq) = (off, crep') /\ rep_ok crep' /\
    ll <= Zlength lr /\
    k + ll + ml <= d + (Zlength out' - Zlength out + Zlength lits0') /\
    1 <= off <= k + ll - ps + ext_len e /\
    Zlength mb = ml /\ lz_copy hist (out ++ blk ++ L) off (Z.to_nat ml) = out ++ blk ++ L ++ mb /\
    (k + ll + ml <= d + cap ->
     (forall E, E <= d + cap -> ext_read_ok e (k + lo) E (ll - lo) ml off ps) /\
     sublist (k + lo) (k + ll + ml) (exec_c c (k + lo) (zbytes (skipn (Z.to_nat lo) L)) ml off ps e) =
       zbytes (skipn (Z.to_nat lo) L ++ mb)) /\
    exec_seqs wsize crep' hist (skipn (Z.to_nat ll) lr) (out ++ blk ++ L ++ mb) rest =
      Some (out', lits0', rep2).
Proof using All.
  intros Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hel Hu Hlr Hrep Hex Hcnt Hlo Hml Hov Hblk.
  cbv zeta.
  cbn [exec_seqs] in Hex.
  destruct (sq_ll sq >? Zlength lr) eqn:Ell; [discriminate|]. rewrite Z.gtb_ltb in Ell; apply Z.ltb_ge in Ell.
  destruct (resolve_offset crep (sq_ll sq) (sq_ov sq)) as [[off crep']|] eqn:Er; [|discriminate].
  destruct (off >? _) eqn:Eo1 in Hex; [discriminate|]. rewrite Z.gtb_ltb in Eo1; apply Z.ltb_ge in Eo1.
  destruct (off >? _) eqn:Eo2 in Hex; [discriminate|]. rewrite Z.gtb_ltb in Eo2; apply Z.ltb_ge in Eo2.
  set (ll := sq_ll sq) in *. set (ml := sq_ml sq) in *.
  set (L := firstn (Z.to_nat ll) lr) in *.
  rewrite <- app_assoc in Eo1, Hex.
  destruct (sh_exec_ok_mdl_rep_ok crep ll (sq_ov sq) off crep' Hrep Hov Er) as [Hoff1 Hrep'].
  destruct (lz_copy_app hist (out ++ blk ++ L) off (Z.to_nat ml)) as [mb [Hmb Hmbl]].
  assert (HmbZ: Zlength mb = ml) by (rewrite Zlength_correct, Hmbl; lia).
  assert (HLZ: Zlength L = ll).
  { unfold L. rewrite Zlength_correct, length_firstn. rewrite Zlength_correct in Ell. lia. }
  rewrite Hmb, <- !app_assoc in Hex.
  pose proof (Zlength_nonneg blk) as Hb0. pose proof (Zlength_nonneg lits0') as Hl0.
  assert (Hend: d + Zlength blk + ll + ml <= d + (Zlength out' - Zlength out + Zlength lits0')).
  { destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid].
    assert (Zlength out' = Zlength out + Zlength blk + ll + ml + Zlength mid)
      by (rewrite Hmid, !Zlength_app; lia).
    pose proof (Zlength_nonneg mid). lia. }
  rewrite !Zlength_app in Eo1.
  exists off, crep', mb.
  split; [apply c_offset_resolve; [apply sh_exec_ok_mdl_rep64|]; assumption|].
  split; [exact Hrep'|]. split; [exact Ell|]. split; [exact Hend|].
  split; [split; [exact Hoff1|]; apply (sh_exec_ok_mdl_off c0 d ps e hist out wsize); auto; lia|].
  split; [exact HmbZ|]. split; [rewrite Hmb, <- !app_assoc; reflexivity|].
  split; [|exact Hex].
  intros Hfit. split.
  - intros E HE. apply (sh_exec_ok_mdl_ext_read e d ps cap bsm0 hist out wsize); auto; lia.
  - set (B := d + Z.min cap (bsm0 + WILDCOPY_OVERLENGTH)).
    assert (HLsplit: firstn (Z.to_nat lo) lr ++ skipn (Z.to_nat lo) L = L).
    { replace (firstn (Z.to_nat lo) lr) with (firstn (Z.to_nat lo) L) by
        (unfold L; rewrite firstn_firstn; f_equal; lia).
      apply firstn_skipn. }
    assert (HsZ: Zlength (skipn (Z.to_nat lo) L) = ll - lo).
    { rewrite Zlength_correct, length_skipn. rewrite Zlength_correct in HLZ. lia. }
    assert (Hfl: Zlength (firstn (Z.to_nat lo) lr) = lo).
    { rewrite Zlength_correct, length_firstn. rewrite Zlength_correct in Ell. lia. }
    destruct (exec_c_lz c d (d + Zlength blk + lo) ps B e hist out (blk ++ firstn (Z.to_nat lo) lr)
                (skipn (Z.to_nat lo) L) wsize ml off) as [_ Hx].
    + exact Hps.
    + rewrite Zlength_app, Hfl. lia.
    + exact Hml.
    + unfold B, WILDCOPY_OVERLENGTH. lia.
    + unfold B. lia.
    + unfold L. apply Forall_skipn, Forall_firstn, Hlr.
    + exact Hblk.
    + apply (sh_exec_ok_mdl_hist_view c0 c d ps cap bsm0); auto.
    + destruct e as [|e1 elen|sh eb en ec e1 elen]; simpl in Hb |- *; auto.
      split; [lia|]. split; [lia|]. exact Hcl.
    + exact Hel.
    + exact Hoff1.
    + rewrite <- !app_assoc, HLsplit, !Zlength_app. lia.
    + exact Eo2.
    + rewrite HsZ in Hx. replace (d + Zlength blk + lo + (ll - lo) + ml) with (d + Zlength blk + ll + ml) in Hx
        by lia.
      rewrite Hx. f_equal.
      rewrite <- !app_assoc, HLsplit, Hmb.
      replace ((out ++ blk ++ L) ++ mb) with ((out ++ blk ++ firstn (Z.to_nat lo) lr) ++ (skipn (Z.to_nat lo) L ++ mb)).
      * apply ecl_skipn_app.
      * rewrite (app_assoc (out ++ blk ++ firstn (Z.to_nat lo) lr) (skipn (Z.to_nat lo) L) mb). f_equal.
        rewrite <- !app_assoc, HLsplit. reflexivity.
Qed.

(* the error return: a capacity error, which the model allows only when the content does not fit *)
Lemma sh_exec_ok_err (HC: sh_ctx) (t: fse_table * fse_table * fse_table) (Hos: os = Some t)
    (id K: Z) (c c': list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z) (ll ml ov: Z) :
  0 <= id < nbSeq -> 0 <= K -> oa_d o + K <= sh_oend -> 0 <= j <= Zlength lits -> Zlength c = oa_N o ->
  unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH)) ->
  rep_ok crep -> 0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= ov < 2 ^ 32 ->
  sh_mid_mdl0 t id K c crep j pos lo st ll ml ov ->
  exec_err (oa_d o + K) sh_oend (sh_li0 + j) (sh_li0 + Zlength lits) ll ml (fst (c_offset crep ll ov))
    (hc_ps h) (ext_len (hc_ext h)) = true ->
  unchanged_outside c c' (oa_d o + K) sh_oend -> Zlength c' = Zlength c ->
  unchanged_outside (oa_c o) c' (oa_d o) (oa_d o + oa_cap o) /\
  (oa_cap o = 0 \/ sh_hv ->
   match seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h) with
   | Some (cnt, rep2) => Zlength cnt <= bsm -> oa_cap o < Zlength cnt
   | None => True
   end).
Proof using All.
  intros Hid HK HKe Hj Hc Hun Hrep Hll Hml Hov Hmid Herr Hun' Hc'.
  pose proof HC as HC0.
  destruct HC as (Ho & Hi & Hns & Hla & Hbsm & Hnl & Hnb & Hnc & Hso & Hrep0 & Hfe & Hc0 & Hlay & Hpps &
                  Hpvs & Hpde & Hldst & _).
  destruct (Hnc ltac:(lia)) as [_ Hcap].
  destruct (sh_exec_ok_pre HC0 c K j Hc HK HKe Hj Hcap) as (_ & _ & Hoe1 & Hoe2 & _).
  pose proof Ho as Ho'. destruct Ho' as (Hosh & Hoc & HoN & Hod & Hocap & Hodc).
  split.
  { intros q Hq Hnq. rewrite Hun' by lia. apply Hun; lia. }
  intros Hhv0. assert (Hhv: sh_hv) by (destruct Hhv0; [lia|auto]).
  rewrite Hos. unfold seqs_model. destruct t as [[tLL tOF] tML]. destruct st as [[sLL sOF] sML].
  replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (decode_seq_stream tLL tOF tML (iw_s i) nbSeq) as [seqs|] eqn:Hds; [|exact I].
  destruct (exec_seqs (hc_wsize h) rep (hc_hist h) lits (hc_out h) seqs) as [[[out' lits'] rep2]|] eqn:Hex;
    [|exact I].
  intros Hcnt.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid'].
  assert (Hlen: Zlength (skipn (length (hc_out h)) (out' ++ lits')) = sh_cnt out' lits').
  { unfold sh_cnt. rewrite Hmid', <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl.
    rewrite !Zlength_app. lia. }
  rewrite Hlen in *.
  unfold sh_mid_mdl0 in Hmid. specialize (Hmid Hhv seqs out' lits' rep2 Hds Hex Hcnt).
  destruct Hmid as ((sq & Hsq & Hsll & Hsml & Hsov) & _ & _ & _ & blk & HKb & Hsub & Hexb).
  rewrite Hsq in Hexb. subst ll ml ov.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hexb) as [mid2 Hmid2].
  assert (HKbsm: K <= bsm).
  { unfold sh_cnt in Hcnt. rewrite Hmid2, !Zlength_app in Hcnt.
    pose proof (Zlength_nonneg mid2). pose proof (Zlength_nonneg lits'). lia. }
  specialize (Hlay Hcap). destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Hla as (Hlb & _ & _).
  destruct (sh_exec_ok_mdl_core (oa_c o) c (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h)
              (hc_wsize h) blk (skipn (Z.to_nat j) lits) 0 sq (skipn (Z.to_nat (id + 1)) seqs) crep
              out' lits' rep2)
    as (off & crep' & mb & Hco & _ & Hlr & Hend & Hoff & _).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply Hhv.
  - apply Hhv.
  - unfold ext_in_bounds. destruct (hc_ext h); simpl in *; tauto || lia.
  - lia.
  - intros q Hq Hnq. apply Hun; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia.
  - apply Forall_skipn. exact Hlb.
  - exact Hrep.
  - exact Hexb.
  - exact Hcnt.
  - lia.
  - lia.
  - lia.
  - rewrite Z.add_0_r, <- HKb. simpl. rewrite app_nil_r. exact Hsub.
  - cbv zeta in *. rewrite Hco in Herr. simpl in Herr.
    unfold sh_cnt in Hend.
    rewrite Zlength_skipn in Hlr. rewrite <- HKb in Hend, Hoff.
    unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
    unfold sh_cnt in *. unfold sh_oend in Herr.
    destruct l; lia.
Qed.

(* op += oneSeqSize (as sh_prologue_ok_add) *)
Lemma sh_exec_ok_add (b: val) (a n: Z) :
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

(* the ll literals execSequence copies are the model's next ones *)
Lemma sh_exec_ok_lits (HC: sh_ctx) (c: list val) (K j ll: Z) :
  Zlength c = oa_N o -> 0 <= K -> oa_d o + K <= sh_oend -> 0 <= j -> 0 <= ll -> j + ll <= Zlength lits ->
  unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH)) ->
  sublist (sh_li0 + j) (sh_li0 + j + ll) (lit_arr sh_ls c) = zbytes (sublist j (j + ll) lits).
Proof using All.
  intros Hc HK HKe Hj Hll Hjl Hun.
  destruct HC as (Ho & Hi & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hx & Hxb_ctx).
  destruct Hla as (_ & Hn & Hll'). destruct Ho as (_ & Hoc & _ & Hod & _ & Hodc).
  unfold sh_ls, sh_li0, lit_arr. unfold sh_oend in HKe, Hun. destruct l.
  - destruct Hll' as (Hoff & Hon & Hsub & _).
    replace (off + j) with (j + off) by lia. replace (j + off + ll) with (j + ll + off) by lia.
    rewrite <- (sublist_sublist (j + ll) (off + Zlength lits) j off) by lia.
    rewrite Hsub, sublist_map. reflexivity.
  - rewrite !Z.add_0_l, sublist_app1 by (rewrite ?Zlength_map; lia). rewrite sublist_map. reflexivity.
  - destruct Hll' as (Hdlb & Hlbn & Hsub).
    assert (E: sublist (lb + j) (lb + j + ll) c = sublist (lb + j) (lb + j + ll) (oa_c o)).
    { apply Znth_eq_ext; [rewrite !Zlength_sublist; unfold WILDCOPY_OVERLENGTH in *; lia|].
      intros q Hq. rewrite Zlength_sublist in Hq by (unfold WILDCOPY_OVERLENGTH in *; lia).
      rewrite !Znth_sublist by lia. apply Hun; [unfold WILDCOPY_OVERLENGTH in *; lia|lia]. }
    rewrite E. replace (lb + j) with (j + lb) by lia. replace (j + lb + ll) with (j + ll + lb) by lia.
    rewrite <- (sublist_sublist (j + ll) (lb + Zlength lits) j lb) by lia.
    rewrite Hsub, sublist_map. reflexivity.
  - contradiction.
Qed.

Lemma sh_exec_ok_def_sub (lst: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength lst ->
  (Forall is_byte_val (sublist a b lst) <-> forall q, a <= q < b -> is_byte_val (Znth q lst)).
Proof using All.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - a) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - a + a) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma sh_exec_ok_def_zbytes (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof using All.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

(* the bytes written so far stay defined (exec_spec's byte clause; ext_read_ok from ext_clean) *)
Ltac sh_exec_ok_zmin :=
  repeat match goal with
  | |- context [Z.min ?a ?b] =>
      let Hz := fresh "Hz" in destruct (Z.min_spec a b) as [[Hz ->]|[Hz ->]]
  | H0: context [Z.min ?a ?b] |- _ =>
      let Hz := fresh "Hz" in let Hm := fresh "Hm" in
      destruct (Z.min_spec a b) as [[Hz Hm]|[Hz Hm]]; rewrite Hm in H0; clear Hm
  end.

Lemma sh_exec_ok_def (HC: sh_ctx) (c c': list val) (K j r: Z) :
  0 < oa_cap o -> Zlength c = oa_N o -> Zlength c' = Zlength c -> 0 <= K -> 0 <= r ->
  oa_d o + K + r <= sh_oend -> 0 <= j <= Zlength lits -> sh_def K c -> xd_ub c c' ->
  Forall is_byte_val (sublist (oa_d o + K) (oa_d o + K + r) c') -> sh_def (K + r) c'.
Proof using All.
  intros Hcap Hc Hc' HK Hr Hend Hj Hdef Hu Hnew.
  destruct (sh_exec_ok_pre HC c K j Hc HK ltac:(lia) Hj Hcap) as (_ & Hps & Hoe1 & _ & _ & Hext & _).
  destruct (sh_li_ok HC c Hc) as [Hl0 Hl1].
  assert (Hd0: 0 <= oa_d o) by (destruct HC as ((_ & _ & _ & Hd & _) & _); exact Hd).
  destruct Hdef as (Hw & Hrd). split.
  - replace (oa_d o + (K + r)) with (oa_d o + K + r) by lia.
    apply (Forall_def_join _ (oa_d o) (oa_d o + K)); [lia | lia | lia | | exact Hnew].
    apply (Forall_def_ub c); auto; lia.
  - intros _. destruct (Hrd Hcap) as (Hh & He & Hl). split; [| split].
    + apply (Forall_def_ub c); auto; lia.
    + apply (ext_def_ub _ c); auto.
    + apply (lit_def_ub _ c); auto.
Qed.

(* the new repeat offsets fit 32 bits when the offset is not (size_t)-1 *)
Lemma sh_exec_ok_rep (crep: Z * Z * Z) (ll ov: Z) :
  rep_ok crep -> 1 <= ov < 2 ^ 32 -> fst (c_offset crep ll ov) < SIZE_MAX ->
  rep_ok (snd (c_offset crep ll ov)).
Proof.
  destruct crep as [[r1 r2] r3]. unfold rep_ok, c_offset, SIZE_MAX. intros (H1 & H2 & H3) Hov Hoff.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [simpl; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [simpl; lia|].
  simpl in *. rewrite Z.mod_small in * by lia.
  destruct (r1 - 1 =? 0) eqn:E1; simpl in *; [lia|]. apply Z.eqb_neq in E1. lia.
Qed.


(* the model goes on after the sequence (loop_exec_step) *)
Lemma sh_exec_ok_mdl (HC: sh_ctx) (t: fse_table * fse_table * fse_table) (Hos: os = Some t)
    (id K: Z) (c c': list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z) (ll ml ov: Z) :
  0 <= id < nbSeq -> 0 <= K -> oa_d o + K + ll + ml <= sh_oend -> 0 <= j -> j + ll <= Zlength lits ->
  Zlength c = oa_N o -> Zlength c' = Zlength c ->
  unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH)) ->
  rep_ok crep -> 0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= ov < 2 ^ 32 ->
  sh_mid_mdl0 t id K c crep j pos lo st ll ml ov ->
  unchanged_outside c c' (oa_d o + K) (Z.min sh_oend (oa_d o + K + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
  (ext_read_ok (hc_ext h) (oa_d o + K) sh_oend ll ml (fst (c_offset crep ll ov)) (hc_ps h) ->
   sublist (oa_d o + K) (oa_d o + K + (ll + ml)) c' =
   sublist (oa_d o + K) (oa_d o + K + (ll + ml))
     (exec_c c (oa_d o + K) (sublist (sh_li0 + j) (sh_li0 + j + ll) (lit_arr sh_ls c)) ml
        (fst (c_offset crep ll ov)) (hc_ps h) (hc_ext h))) ->
  sh_inv_mdl0 t (id + 1) (K + (ll + ml)) c' (snd (c_offset crep ll ov)) (j + ll) pos lo st.
Proof using All.
  intros Hid HK HKe Hj Hjl Hc Hc' Hun Hrep Hll Hml Hov Hmid Hun' Hbytes.
  pose proof HC as HC0.
  destruct HC0 as (Ho & Hi & Hns & Hla & Hbsm & Hnl & Hnb & Hnc & Hso & Hrep0 & Hfe & Hc0 & Hlay & _).
  assert (Hcap: 0 < oa_cap o) by (apply Hnc; lia).
  destruct (sh_exec_ok_pre HC c K j Hc HK ltac:(lia) ltac:(lia) Hcap)
    as (Hc32 & Hps & Hoe & Hoed & _ & _ & _ & _ & _ & _).
  specialize (Hlay Hcap). destruct Hlay as (Hps0 & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hla as (Hlb & _ & _).
  destruct t as [[tLL tOF] tML]. destruct st as [[sLL sOF] sML].
  cbv beta iota zeta in Hmid |- *. unfold sh_inv_mdl0, sh_mid_mdl0 in *.
  intros Hhv seqs out' lits' rep2 Hdec Hex Hcnt.
  destruct (Hmid Hhv seqs out' lits' rep2 Hdec Hex Hcnt)
    as ((sq & Hsq & Hsll & Hsml & Hsov) & Hrdy & Hlo & Hds & blk & HKb & Hblk & Hexb).
  split; [exact Hrdy|]. split; [exact Hlo|]. split; [exact Hds|].
  rewrite Hsq in Hexb.
  destruct Hhv as (Hhv & Hecl).
  (* K <= bsm *)
  assert (HKbsm: K <= bsm).
  { destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hexb) as [mid Hmid'].
    unfold sh_cnt in Hcnt. rewrite Hmid', !Zlength_app in Hcnt.
    pose proof (Zlength_nonneg mid). pose proof (Zlength_nonneg lits'). lia. }
  assert (Hlr: bytes_ok (skipn (Z.to_nat j) lits)).
  { unfold bytes_ok in *. apply Forall_skipn. exact Hlb. }
  assert (Hib: ext_in_bounds (hc_ext h) (Zlength c)).
  { unfold ext_in_bounds. destruct (hc_ext h); simpl in *; try tauto; lia. }
  assert (Hun0: unchanged_outside (oa_c o) c (oa_d o) (oa_d o + Z.min (oa_cap o) (bsm + WILDCOPY_OVERLENGTH))).
  { intros q Hq Hnq. apply Hun; [exact Hq|]. intros Hq2. apply Hnq. lia. }
  assert (Hblk0: sublist (oa_d o) (oa_d o + Zlength blk + 0) c = zbytes (blk ++ firstn (Z.to_nat 0) (skipn (Z.to_nat j) lits))).
  { rewrite Z.add_0_r, <- HKb. simpl. rewrite app_nil_r. exact Hblk. }
  destruct (sh_exec_ok_mdl_core (oa_c o) c (oa_d o) (hc_ps h) (oa_cap o) bsm (hc_ext h) (hc_hist h) (hc_out h)
              (hc_wsize h) blk (skipn (Z.to_nat j) lits) 0 sq (skipn (Z.to_nat (id + 1)) seqs) crep
              out' lits' rep2) as (off & crep' & mb & Hco & _ & Hlrl & Hend & Hoff & Hmb & _ & Hfit & Hexr);
    try lia; auto.
  rewrite Hsll, Hsml, Hsov in *.
  rewrite Hco. cbn [fst snd] in *. rewrite Hco in Hbytes. cbn [fst] in Hbytes.
  set (L := firstn (Z.to_nat ll) (skipn (Z.to_nat j) lits)) in *.
  assert (HL: Zlength L = ll).
  { unfold L. rewrite Zlength_firstn. lia. }
  assert (HLs: sublist j (j + ll) lits = L).
  { unfold L, sublist. rewrite firstn_skipn_comm.
    replace (Z.to_nat (j + ll)) with (Z.to_nat j + Z.to_nat ll)%nat by lia. reflexivity. }
  destruct Hfit as (Hrok & Hexc); [rewrite <- HKb; lia|].
  exists (blk ++ L ++ mb). split; [rewrite !Zlength_app; lia|].
  split.
  - rewrite (sublist_split (oa_d o) (oa_d o + K) (oa_d o + (K + (ll + ml)))) by lia.
    rewrite map_app. f_equal.
    + rewrite <- Hblk. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
      intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia.
      apply Hun'; [lia|lia].
    + assert (Hro: ext_read_ok (hc_ext h) (oa_d o + K) sh_oend ll ml off (hc_ps h)).
      { specialize (Hrok sh_oend Hoed). rewrite <- HKb, Z.add_0_r, Z.sub_0_r in Hrok. exact Hrok. }
      rewrite Z.add_assoc. rewrite (Hbytes Hro).
      rewrite (sh_exec_ok_lits HC c K j ll Hc HK ltac:(lia) Hj ltac:(lia) Hjl Hun). rewrite HLs.
      rewrite <- HKb in Hexc. rewrite !Z.add_0_r in Hexc. simpl skipn in Hexc.
      rewrite <- Hexc. f_equal; lia.
  - rewrite skipn_skipn in Hexr. replace (Z.to_nat ll + Z.to_nat j)%nat with (Z.to_nat (j + ll)) in Hexr by lia.
    exact Hexr.
Qed.

(* one execution: ZSTD_execSequence (zstd_globals lent by tabs_ok), the error return (a capacity error under
   the model: loop_exec_step), op += oneSeqSize *)
(* the literals execSequence reads are bytes when the arrays read are *)
Lemma sh_exec_ok_litbytes (HC: sh_ctx) (c: list val) :
  byte_cells c -> byte_cells (iw_c i) -> byte_cells (lit_arr sh_ls c).
Proof using All.
  intros Bc Bi.
  destruct HC as (_ & _ & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & Hxb).
  unfold sh_ls, lit_arr. destruct l; auto.
  destruct Hla as (Hlb & _). apply Forall_app. split; [apply sh_release_zbytes; exact Hlb | apply Hxb; reflexivity].
Qed.

Lemma sh_exec_ok (HC: sh_ctx) (HX: sh_lx) (t: fse_table * fse_table * fse_table) (Hos: os = Some t)
    (tp: val * val * val) (sht: share * share * share) (fm: Z * Z * Z) (Rt: mpred)
    (HT: tabs_ok gv p ox t tp sht fm Rt)
    (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z) (ll ml ov: Z) :
  semax sh_Delta (sh_mid_at t tp sht fm Rt id K c crep j pos lo st ll ml ov) sh_EXEC
    (overridePost
       (EX K': Z, EX c': list val, EX crep': Z * Z * Z, EX j': Z,
          sh_inv_at t tp sht fm Rt (id + 1) (nbSeq - id) K' c' crep' j' pos lo st)
       sh_SR).
Proof using All.
  unfold sh_Delta.
  simplify_func_tycontext' (func_tycontext f_ZSTD_decompressSequences_body Vprog LOOP_GB nil).
  cbv [sh_EXEC sh_LB sh_LOOP sh_BIG sh_body sq_drop sq_nth]. cbn [fn_body f_ZSTD_decompressSequences_body].
  unfold sh_mid_at. Intros. destruct H12 as [H12 H12x].
  assert (Hcap: 0 < oa_cap o) by (destruct HC as (_&_&_&_&_&_&_&Hnc&_); apply Hnc; lia).
  destruct (sh_exec_ok_pre HC c K j H3 H0 H1 H2 Hcap)
    as (Hc32 & Hps & Hoe & Hoed & Hls & Hext & Hde & Hfps & Hfvs & Hfde).
  pose proof H11 as (Xw & Xrd). destruct (Xrd Hcap) as (Xh & Xe & Xl).
  destruct (sh_li_ok HC c H3) as [Xl0 Xl1].
  assert (Xps: hc_ps h <= oa_d o).
  { destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _). destruct (Hlay Hcap) as (? & _). lia. }
  assert (Xdh: Forall is_byte_val (sublist (hc_ps h) (oa_d o + K) c))
    by (apply (Forall_def_join c (hc_ps h) (oa_d o)); auto; lia).
  assert (Xdl: Forall is_byte_val (sublist (sh_li0 + j) (sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH) (lit_arr sh_ls c)))
    by (apply (xd_sub _ sh_li0 (sh_li0 + Zlength lits + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia).
  assert (Hoff: 1 <= fst (c_offset crep ll ov) <= SIZE_MAX).
  { apply c_offset_ok; [|lia]. destruct crep as [[r1 r2] r3]; unfold rep_ok, rep64_ok, SIZE_MAX in *; lia. }
  destruct HT as (Hsht & Hback & Y & HY).
  rewrite Hfps, Hfvs. unfold sh_lb.
  gather_SEP (seqtabs_at sht t fm tp) Rt. rewrite HY. flatten_sepcon_in_SEP.
  rewrite <- H3.
  forward_call (gv, oa_sh o, oa_base o, c, oa_d o + K, sh_oend, Tsh, v_sequence, ll, ml,
                fst (c_offset crep ll ov), Tsh, v_litPtr, sh_ls, sh_li0 + j, sh_li0 + Zlength lits, hc_ps h,
                hc_ext h, fs_dictEnd fs).
  { assert (Hlb: Zlength lits <= ZSTD_BLOCKSIZE_MAX) by (destruct HC as (_ & _ & _ & _ & (? & ?) & ? & _); lia).
    split; [destruct HC as ((? & _) & _); auto|]. unfold LL_VMAX, ML_VMAX, SIZE_MAX, ZSTD_BLOCKSIZE_MAX in *.
    repeat split; first [rep_lia | assumption]. }
  Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
  rename H14 into Hrr0, H15 into Hlen, H16 into Hbyt, H17 into Hee, H18 into Herrc, H19 into Hsucc.
  rename H20 into Hxu, H21 into Hxf, H22 into Hlx.
  rewrite (sh_xs_lsrc HX) in Hlx.
  (* the exact model's step (BlkSeqLoopShortX) *)
  destruct (xs_exec_step fs os rep l lits lxb nbSeq o i h t id K c c' crep j pos lo st ll ml ov r (sh_xs_ctx HC HX)
              H H0 H1 H2 H3 ltac:(lia) ltac:(lia) ltac:(lia) H12x Hee Hlx) as [XE XS].
  assert (Hbc': byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells c').
  { intros B1 B2 B3. apply Hbyt; [apply H13; auto | apply (sh_exec_ok_litbytes HC c); auto; apply H13; auto | auto]. }
  gather_SEP (zstd_globals gv) Y. rewrite <- HY. flatten_sepcon_in_SEP.
  forward_call r.
  unfold POSTCONDITION, abbreviate, sh_SR, sh_POST.
  destruct (is_error_code r) eqn:Er.
  - forward_if (PROP (False) LOCAL () SEP ()).
    + forward.
      destruct (sh_exec_ok_err HC t Hos id K c c' crep j pos lo st ll ml ov H H0 H1 H2 H3 H4 H5 H8 H9 H10 H12
                  (eq_sym Hee) (proj1 (Herrc eq_refl)) Hlen) as [Hun Hmd].
      assert (Hderr: dec_err r) by exact (proj2 (Herrc eq_refl)).
      assert (HXN: seqs_exact os rep l lits lxb nbSeq o i h r c' rep) by (apply xs_exact_none; auto).
      Exists r c' rep.
      sep_apply (Hback 1).
      sep_apply (sh_release HC HX).
      sep_apply sh_exec_ok_ss.
      rewrite Hos. replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite H3.
      entailer!.
      split; [destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); auto|].
      split; [|rewrite <- Hos; exact HXN].
      intros Hv. specialize (Hmd Hv). rewrite Hos in Hmd.
      destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; auto.
    + exfalso. match goal with Hx: Int.repr 1 = Int.zero |- _ =>
        apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia;
        rewrite Int.unsigned_zero in Hx; lia end.
  - destruct (Hsucc eq_refl) as (Hr & Hlp & Hun & Hbytes). clear Hsucc Herrc. subst r lp.
    forward_if. { exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
    unfold MORE_COMMANDS, abbreviate. apply dec_skipbreak_seq. forward.
    symmetry in Hee. unfold exec_err in Hee.
    apply orb_false_iff in Hee as [Hee Hoff2]. apply orb_false_iff in Hee as [Hcap2 Hlit2].
    apply Z.ltb_ge in Hcap2, Hlit2, Hoff2.
    assert (Hjl: j + ll <= Zlength lits) by lia.
    assert (Hel: 0 <= ext_len (hc_ext h) <= 2 ^ 63 - 1) by (destruct Hext; lia).
    assert (Hrep': rep_ok (snd (c_offset crep ll ov))).
    { apply sh_exec_ok_rep; auto. unfold LL_VMAX, SIZE_MAX in *. lia. }
    assert (Hdef': sh_def (K + (ll + ml)) c').
    { apply (sh_exec_ok_def HC c c' K j (ll + ml)); auto; try lia; apply Hxf; reflexivity. }
    assert (Hmdl': sh_inv_mdl t (id + 1) (K + (ll + ml)) c' (snd (c_offset crep ll ov)) (j + ll) pos lo st).
    { split; [|apply XS; reflexivity].
      apply (sh_exec_ok_mdl HC t Hos id K c c' crep j pos lo st ll ml ov); auto; try lia.
      intros Hro. apply (Hbytes Hro). }
    assert (Hun': unchanged_outside (oa_c o) c' (oa_d o)
                    (Z.min sh_oend (oa_d o + (K + (ll + ml)) + WILDCOPY_OVERLENGTH))).
    { intros iq Hq Hnq. destruct HC as ((_ & Hoc & _) & _).
      rewrite Hun by (rewrite ?H3; lia). apply H4; lia. }
    assert (Hsb': sh_bytes c') by exact Hbc'.
    Exists (K + (ll + ml)) c' (snd (c_offset crep ll ov)) (j + ll).
    unfold sh_inv_at. rewrite Hfps, Hfvs.
    rewrite sh_exec_ok_add by (destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                                               _ & _ & Hob & _); auto).
    rewrite H3. change (lit_base sh_ls (oa_base o)) with sh_lb.
    entailer!.
    + f_equal; lia.
    + rewrite Z.add_assoc. cancel.
Qed.

(* sh_end_ok's helpers: the model at the end (the stream consumed, the content), the loops *)
Lemma sh_end_ok_mdl (t: fse_table * fse_table * fse_table) (K: Z) (c: list val) (crep: Z * Z * Z)
    (j pos lo: Z) (st: Z * Z * Z) (cnt: list Z) (rep2: Z * Z * Z) :
  os = Some t -> 0 < nbSeq -> sh_hv ->
  sh_inv_mdl0 t nbSeq K c crep j pos lo st ->
  seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h) = Some (cnt, rep2) ->
  Zlength cnt <= bsm ->
  lo = 0 /\ pos = 0 /\ exists blk, K = Zlength blk /\ sublist (oa_d o) (oa_d o + K) c = zbytes blk /\
    cnt = blk ++ skipn (Z.to_nat j) lits /\ crep = rep2.
Proof.
  intros Hos Hnb Hhv Hinv Hm Hcnt.
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML].
  unfold seqs_model in Hm. rewrite Hos in Hm.
  replace (nbSeq =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; lia).
  destruct (decode_seq_stream tLL tOF tML (iw_s i) nbSeq) as [seqs|] eqn:Hd; [|discriminate].
  destruct (exec_seqs (hc_wsize h) rep (hc_hist h) lits (hc_out h) seqs) as [[[out' lits'] rep']|] eqn:He;
    [|discriminate].
  injection Hm as Hc Hr. subst rep'.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ He) as [mid Hmid].
  assert (Hsk: cnt = mid ++ lits').
  { rewrite <- Hc, Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
  assert (Hsc: sh_cnt out' lits' <= bsm).
  { unfold sh_cnt. rewrite Hsk, Zlength_app in Hcnt. rewrite Hmid, Zlength_app. lia. }
  unfold sh_inv_mdl0 in Hinv. cbv beta iota zeta in Hinv.
  destruct (Hinv Hhv seqs out' lits' rep2 Hd He Hsc) as (_ & Hlo & Hds & blk & HK & Hsub & Hex).
  replace (Z.to_nat (nbSeq - nbSeq)) with O in Hds by lia. simpl in Hds.
  injection Hds as Hnil Hpos.
  rewrite <- Hnil in Hex. simpl in Hex. injection Hex as Ho' Hl' Hr'.
  split; [apply Hlo; reflexivity|]. split; [lia|].
  exists blk. split; [exact HK|]. split; [exact Hsub|]. split; [|exact Hr'].
  rewrite Hsk, <- Hl'. rewrite Hmid in Ho'. apply app_inv_head in Ho'. rewrite Ho'. reflexivity.
Qed.

(* the seqState_t local back to data_at_ *)
Lemma sh_end_ok_ss_split (v: val) :
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

Lemma sh_end_ok_ss (s: list Z) (start: val) (pos lo sLL sOF sML: Z) (pLL pOF pML: val) (r: Z * Z * Z)
    (v: val) :
  BIT_DStream_rep Tsh gv s start pos lo (field_address t_seqstate (DOT _DStream) v) *
  field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) v *
  field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) v *
  field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) v *
  field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v
  |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite sh_end_ok_ss_split. unfold BIT_DStream_rep. Intros ptr lim.
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

(* after the loop: BIT_endOfDStream (an error unless the stream is consumed: never under the model),
   the repeat offsets saved ((U32) prevOffset), the tables given back with fseEntropy = 1 *)
Lemma sh_end_ok (HC: sh_ctx) (HX: sh_lx) (t: fse_table * fse_table * fse_table) (Hos: os = Some t)
    (tp: val * val * val) (sht: share * share * share) (fm: Z * Z * Z) (Rt: mpred)
    (HT: tabs_ok gv p ox t tp sht fm Rt) (Hnb: 0 < nbSeq) :
  semax sh_Delta (sh_inv t tp sht fm Rt nbSeq) sh_END (overridePost sh_aft sh_SR).
Proof using All.
  unfold sh_END, sh_BIG, sh_body. simpl fn_body. cbv [sq_nth sq_drop].
  unfold sh_inv. Intros K c crep j pos lo st. unfold sh_inv_at. Intros.
  rename H10 into Hsb. destruct H9 as [H9 H9x].
  (* the exact model at the end (BlkSeqLoopShortX) *)
  destruct (xs_end fs os rep l lits lxb nbSeq o i h t K c crep j pos lo st (sh_xs_ctx HC HX) Hos Hnb H9x)
    as [XE XA].
  unfold sh_Delta, sh_SR; simplify_func_tycontext.
  assert (HC' := HC).
  destruct HC' as (Hoa & Hiw & Hns & Hla & Hbsm & Hll & Hnbr & Hpos & Hso & Hrep & Hfe & Hc0 & Hlay & Hp1 & Hp2
    & Hp3 & Hldst & Hr1 & Hr2 & Hib1 & Hib2 & Heq & Hxr & Hxb_ctx).
  destruct HT as (Hsht & Hback & Y & HY).
  gather_SEP (seqtabs_at sht t fm tp) Rt. rewrite HY. flatten_sepcon_in_SEP.
  destruct st as [[sLL sOF] sML]; destruct tp as [[pLL pOF] pML].
  unfold seqstate_at. repeat flatten_sepcon_in_SEP.
  assert_PROP (field_compatible t_seqstate (DOT _DStream) v_seqState) as HFC.
  { entailer!. }
  match goal with |- semax _ (PROPx ?A ?B) _ _ =>
    forward_loop (PROPx A B) break: (PROPx ((lo = 0 /\ pos = 0) :: A) B) end.
  - apply ENTAIL_refl.
  - forward_call (Tsh, field_address t_seqstate (DOT _DStream) v_seqState, gv, iw_s i,
                  offset_val (iw_off i) (iw_base i), pos, lo, sh2, offset_val (iw_off i) (iw_base i), iw_s i, 0).
    { entailer!. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    { unfold bit_src_ok. rewrite isptr_offset_val_zero by (apply isptr_offset_val'; auto).
      split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity]. }
    forward_if (lo = 0 /\ pos = 0).
    + apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
      match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
      * apply ENTAIL_refl.
      * forward_if True. { contradiction. } { forward. entailer!. }
        forward. Intros. apply ENTAIL_refl.
      * apply dec_skipbreak_seq. apply dec_skipbreak_seq.
        unfold sh_POST in POSTCONDITION. forward.
        assert (HXN: seqs_exact os rep l lits lxb nbSeq o i h (Int64.unsigned (Int64.repr (-20))) c rep).
        { apply xs_exact_none; [reflexivity|]. apply XE. intros [Hl0 Hp0]. subst lo pos.
          simpl in H10. apply (f_equal Int.unsigned) in H10.
          rewrite Int.unsigned_repr, Int.unsigned_zero in H10 by rep_lia. discriminate. }
        Exists (Int64.unsigned (Int64.repr (-20))) c rep.
        rewrite Int64.repr_unsigned.
        sep_apply (sh_end_ok_ss (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo sLL sOF sML pLL pOF pML crep
                     v_seqState).
        sep_apply (sh_release HC HX).
        sep_apply (derives_refl' _ _ (eq_sym HY)).
        sep_apply (Hback 1).
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr).
        rewrite Hos. replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        apply andp_right; [apply prop_right | cancel].
        assert (Hcap: 0 < oa_cap o) by (apply Hpos; lia).
        assert (Hoe: sh_oend <= oa_d o + oa_cap o).
        { unfold sh_oend. destruct Hla as (_ & _ & Hlb). destruct l; try lia.
          destruct Hlb as (? & ? & _). pose proof (Zlength_nonneg lits). unfold WILDCOPY_OVERLENGTH in *. lia. }
        split; [apply Int64.unsigned_range_2|].
        split; [exact H3|]. split; [exact Hrep|].
        split; [unfold unchanged_outside in *; intros k Hk Hn; apply H4; [exact Hk|]; intros Hk'; apply Hn; lia|].
        assert (HE: is_error_code (Int64.unsigned (Int64.repr (-20))) = true) by reflexivity.
        rewrite HE. split; [discriminate|].
        split; [|split; [intros _; exact (sh_dec_err 20 ltac:(lia) ltac:(lia) ltac:(lia))|
                         split; [exact Hsb | split; [rewrite <- Hos; exact HXN | reflexivity]]]].
        intros Hm. rewrite <- Hos.
        destruct (seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h)) as [[cnt rep2]|] eqn:Esm;
          [|exact I].
        intros Hcnt. exfalso.
        assert (Hhv: sh_hv) by (destruct Hm as [Hm|Hm]; [lia|exact Hm]).
        destruct (sh_end_ok_mdl t K c crep j pos lo (sLL, sOF, sML) cnt rep2 Hos Hnb Hhv H9 Esm Hcnt) as (-> & -> & _).
        simpl in H10. apply (f_equal Int.unsigned) in H10. rewrite Int.unsigned_repr, Int.unsigned_zero in H10 by rep_lia.
        discriminate.
    + assert (Hlp: lo = 0 /\ pos = 0).
      { destruct ((lo =? 0) && (pos =? 0))%bool eqn:E;
          [rewrite andb_true_iff, !Z.eqb_eq in E; exact E | contradiction H10; reflexivity]. }
      forward. entailer!.
    + forward. entailer!.
  - apply semax_extract_PROP; intros [Hlo0 Hpos0].
    pose proof (XA Hlo0 Hpos0 H5) as HXA.
    destruct crep as [[c1 c2] c3] eqn:Ecrep. destruct rep as [[r1 r2] r3] eqn:Erep.
    assert (H5' := H5). destruct H5' as (Hc1 & Hc2 & Hc3).
    forward_for_simple_bound 3 (EX k: Z,
      PROP ()
      LOCAL (temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val sh_oend (oa_base o));
             temp _op (offset_val (oa_d o + K) (oa_base o));
             temp _litEnd (offset_val (sh_li0 + Zlength lits) sh_lb);
             temp _prefixStart (fs_prefixStart fs); temp _vBase (fs_virtualStart fs);
             temp _dictEnd (fs_dictEnd fs); temp _nbSeq (Vint (Int.repr (nbSeq - nbSeq)));
             temp _isLongOffset (Vint (Int.repr 0));
             lvar _sequence (Tstruct ___gp_seq_t noattr) v_sequence;
             lvar _seqState (Tstruct ___gp_seqState_t noattr) v_seqState;
             lvar _litPtr (tptr tuchar) v_litPtr; gvars gv; temp _dctx p)
      SEP (zstd_globals gv; Y; data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_sequence;
           BIT_DStream_rep Tsh gv (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo
             (field_address t_seqstate (DOT _DStream) v_seqState);
           field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) v_seqState;
           field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) v_seqState;
           field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) v_seqState;
           field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals (c1, c2, c3)) v_seqState;
           data_at Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr;
           field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p;
           seq_ptrs p (pLL, pOF, pML);
           field_at Ews t_dctx (DOT _entropy DOT _rep)
             (sublist 0 k (rep_vals (c1, c2, c3)) ++ sublist k 3 (rep_vals (r1, r2, r3))) p;
           pws_pred W; frame_fields p fs; sh_lrest; lit_res sh_ls;
           data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o);
           bit_src sh2 (offset_val (iw_off i) (iw_base i)) (iw_s i); Ri; ext_res (hc_ext h)))%assert.
    + entailer!.
    + assert (Hz: forall d, @Znth val d i0 (rep64_vals (c1, c2, c3)) = Vlong (Int64.repr (Znth i0 [c1; c2; c3]))).
      { intros d. assert (i0 = 0 \/ i0 = 1 \/ i0 = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity. }
      forward.
      { entailer!. rewrite Hz. exact I. }
      rewrite !Hz.
      forward.
      assert (Hl: upd_Znth i0 (sublist 0 i0 (rep_vals (c1, c2, c3)) ++ sublist i0 3 (rep_vals (r1, r2, r3)))
                     (Vint (Int.repr (Int64.Z_mod_modulus (Znth i0 [c1; c2; c3])))) =
                   sublist 0 (i0 + 1) (rep_vals (c1, c2, c3)) ++ sublist (i0 + 1) 3 (rep_vals (r1, r2, r3))).
      { assert (i0 = 0 \/ i0 = 1 \/ i0 = 2) as [ -> | [ -> | -> ] ] by lia; cbn;
          rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia; reflexivity. }
      rewrite Hl. entailer!.
    + assert (HM0: sh_aft_mdl0 K c (c1, c2, c3) j).
      { unfold sh_aft_mdl0. intros Hm.
        destruct (seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h)) as [[cnt rep2]|]
          eqn:Esm; [|exact I].
        intros Hcnt.
        assert (Hcap: 0 < oa_cap o) by (apply Hpos; lia).
        assert (Hhv: sh_hv) by (destruct Hm as [Hm|Hm]; [lia|exact Hm]).
        destruct (sh_end_ok_mdl t K c (c1, c2, c3) j pos lo (sLL, sOF, sML) cnt rep2 Hos Hnb Hhv H9 Esm Hcnt)
          as (_ & _ & HX0).
        exact HX0. }
      assert (HM: sh_aft_mdl K c (c1, c2, c3) j).
      { split; [exact HM0|]. rewrite Erep. rewrite ?Erep in HXA. exact HXA. }
      replace (sublist 0 3 (rep_vals (c1, c2, c3)) ++ sublist 3 3 (rep_vals (r1, r2, r3)))
        with (rep_vals (c1, c2, c3)) by reflexivity.
      unfold sh_aft. Exists K c (c1, c2, c3) j. unfold sh_aft_at.
      sep_apply (sh_end_ok_ss (iw_s i) (offset_val (iw_off i) (iw_base i)) pos lo sLL sOF sML pLL pOF pML
                   (c1, c2, c3) v_seqState).
      sep_apply (derives_refl' _ _ (eq_sym HY)).
      sep_apply (Hback 1).
      rewrite Hos. replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      entailer!.
Qed.

(* ---------- sh_epi_ok helpers ---------- *)
(* bytes [lo, hi) of the byte array v at q *)
Definition sh_epi_ok_seg (sh: share) (v: list val) (q: val) (lo hi: Z) : mpred :=
  data_at sh (tarray tuchar (hi - lo)) (sublist lo hi v) (offset_val lo q).

Lemma sh_epi_ok_fc (n lo hi: Z) (q: val) :
  field_compatible (tarray tuchar n) [] q -> 0 <= lo <= hi -> hi <= n ->
  field_compatible (tarray tuchar (hi - lo)) [] (offset_val lo q).
Proof.
  intros Hf H1 H2.
  destruct (proj1 (field_compatible_Tarray_split tuchar lo n q ltac:(lia)) Hf) as [_ Hf2].
  rewrite arr_field_address0 in Hf2 by (auto; lia). simpl sizeof in Hf2. rewrite Z.mul_1_l in Hf2.
  destruct (proj1 (field_compatible_Tarray_split tuchar (hi - lo) (n - lo) _ ltac:(lia)) Hf2) as [Hf3 _].
  exact Hf3.
Qed.

Lemma sh_epi_ok_seg_split (sh: share) (n: Z) (v: list val) (q: val) (lo m hi: Z) :
  field_compatible (tarray tuchar n) [] q -> Zlength v = n -> 0 <= lo <= m -> m <= hi -> hi <= n ->
  sh_epi_ok_seg sh v q lo hi = sh_epi_ok_seg sh v q lo m * sh_epi_ok_seg sh v q m hi.
Proof.
  intros Hf Hl H1 H2 H3. unfold sh_epi_ok_seg.
  pose proof (sh_epi_ok_fc n lo hi q Hf ltac:(lia) ltac:(lia)) as Hf1.
  rewrite (split2_data_at_Tarray_tuchar sh (hi - lo) (m - lo)) by (try rewrite Zlength_sublist; lia).
  change (Tarray tuchar (hi - lo) noattr) with (tarray tuchar (hi - lo)).
  rewrite arr_field_address0 by (auto; lia). simpl sizeof. rewrite Z.mul_1_l.
  rewrite offset_offset_val. rewrite !sublist_sublist by lia.
  replace (m - lo + lo) with m by lia. replace (lo + (m - lo)) with m by lia.
  replace (0 + lo) with lo by lia. replace (hi - lo + lo) with hi by lia.
  replace (hi - lo - (m - lo)) with (hi - m) by lia. reflexivity.
Qed.

Lemma sh_epi_ok_seg_full (sh: share) (n: Z) (v: list val) (q: val) :
  field_compatible (tarray tuchar n) [] q -> Zlength v = n ->
  data_at sh (tarray tuchar n) v q = sh_epi_ok_seg sh v q 0 n.
Proof.
  intros Hf Hl. unfold sh_epi_ok_seg. rewrite isptr_offset_val_zero by auto.
  rewrite sublist_same by lia. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma sh_epi_ok_seg_ext (sh: share) (v v': list val) (q: val) (lo hi: Z) :
  sublist lo hi v = sublist lo hi v' -> sh_epi_ok_seg sh v q lo hi = sh_epi_ok_seg sh v' q lo hi.
Proof. intros E. unfold sh_epi_ok_seg. rewrite E. reflexivity. Qed.

Lemma sh_epi_ok_seg_mid (sh: share) (n: Z) (v: list val) (q: val) (lo hi a L: Z) :
  field_compatible (tarray tuchar n) [] q -> Zlength v = n -> 0 <= lo <= a -> 0 <= L -> a + L <= hi -> hi <= n ->
  sh_epi_ok_seg sh v q lo hi =
  sh_epi_ok_seg sh v q lo a * data_at sh (tarray tuchar L) (sublist a (a + L) v) (offset_val a q) *
  sh_epi_ok_seg sh v q (a + L) hi.
Proof.
  intros Hf Hl H1 H2 H3 H4.
  rewrite (sh_epi_ok_seg_split sh n v q lo a hi) by (auto; lia).
  rewrite (sh_epi_ok_seg_split sh n v q a (a + L) hi) by (auto; lia).
  unfold sh_epi_ok_seg at 2. replace (a + L - a) with L by lia. rewrite sepcon_assoc. reflexivity.
Qed.

(* the output array after the copy of bs at a *)
Definition sh_epi_ok_put (c: list val) (a: Z) (bs: list val) : list val :=
  sublist 0 a c ++ bs ++ sublist (a + Zlength bs) (Zlength c) c.

Lemma sh_epi_ok_put_len (c: list val) (a: Z) (bs: list val) :
  0 <= a -> a + Zlength bs <= Zlength c -> Zlength (sh_epi_ok_put c a bs) = Zlength c.
Proof. intros. unfold sh_epi_ok_put. list_solve. Qed.

Lemma sh_epi_ok_put_mid (c: list val) (a: Z) (bs: list val) :
  0 <= a -> a + Zlength bs <= Zlength c -> sublist a (a + Zlength bs) (sh_epi_ok_put c a bs) = bs.
Proof. intros. unfold sh_epi_ok_put. list_solve. Qed.

Lemma sh_epi_ok_put_out (c: list val) (a: Z) (bs: list val) (lo hi: Z) :
  0 <= a -> a + Zlength bs <= Zlength c -> 0 <= lo <= hi -> hi <= Zlength c ->
  (hi <= a \/ a + Zlength bs <= lo) -> sublist lo hi (sh_epi_ok_put c a bs) = sublist lo hi c.
Proof.
  intros H1 H2 H3 H4 [H5|H5]; unfold sh_epi_ok_put; list_solve.
Qed.

Lemma sh_epi_ok_put_znth (c: list val) (a: Z) (bs: list val) (k: Z) :
  0 <= a -> a + Zlength bs <= Zlength c -> 0 <= k < Zlength c -> ~ (a <= k < a + Zlength bs) ->
  Znth k (sh_epi_ok_put c a bs) = Znth k c.
Proof. intros. unfold sh_epi_ok_put. list_solve. Qed.

Lemma sh_epi_ok_put_split (c: list val) (a lo: Z) (bs: list val) :
  0 <= lo <= a -> a + Zlength bs <= Zlength c ->
  sublist lo (a + Zlength bs) (sh_epi_ok_put c a bs) = sublist lo a c ++ bs.
Proof. intros. unfold sh_epi_ok_put. list_solve. Qed.

Lemma sh_epi_ok_bytes (l0: list val) : Forall is_byte_val l0 -> exists x, l0 = zbytes x /\ bytes_ok x.
Proof.
  induction 1 as [|v l1 [z [Hz ->]] _ [x [-> Hx]]].
  - exists nil. split; [reflexivity | constructor].
  - exists (z :: x). split; [reflexivity | constructor; [unfold is_byte; lia | exact Hx]].
Qed.

Lemma sh_epi_ok_bytes_skipn (lits0: list Z) (n: nat) : bytes_ok lits0 -> bytes_ok (skipn n lits0).
Proof.
  revert lits0. induction n as [|n IH]; intros lits0 Hb; [exact Hb|].
  destruct lits0 as [|x lits0]; [constructor|]. simpl. apply IH. inversion Hb; auto.
Qed.

Lemma sh_epi_ok_skip (lits0: list Z) (j: Z) :
  0 <= j <= Zlength lits0 -> sublist j (Zlength lits0) (zbytes lits0) = zbytes (skipn (Z.to_nat j) lits0).
Proof. intros. rewrite sublist_map, sublist_skip by lia. reflexivity. Qed.

Lemma sh_epi_ok_unch_sub (oc c: list val) (lo hi a b: Z) :
  unchanged_outside oc c lo hi -> Zlength c = Zlength oc -> 0 <= a <= b -> b <= Zlength oc ->
  (hi <= a \/ b <= lo) -> sublist a b c = sublist a b oc.
Proof.
  intros Hun Hl H1 H2 H3. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros k Hk. rewrite Zlength_sublist in Hk by lia. rewrite !Znth_sublist by lia.
  apply Hun; lia.
Qed.

Lemma sh_epi_ok_unch_put (oc c bs: list val) (lo hi hi' a: Z) :
  unchanged_outside oc c lo hi -> Zlength c = Zlength oc -> 0 <= a -> a + Zlength bs <= Zlength c ->
  lo <= a -> a + Zlength bs <= hi' -> hi <= hi' -> unchanged_outside oc (sh_epi_ok_put c a bs) lo hi'.
Proof.
  intros Hun Hl H1 H2 H3 H4 H5 k Hk Hn.
  rewrite sh_epi_ok_put_znth by lia. apply Hun; lia.
Qed.

Lemma sh_epi_ok_unch_mono (oc c: list val) (lo hi hi': Z) :
  unchanged_outside oc c lo hi -> hi <= hi' -> unchanged_outside oc c lo hi'.
Proof. intros Hun Hh k Hk Hn. apply Hun; lia. Qed.

Lemma sh_epi_ok_cnt_len (blk lits0: list Z) (j: Z) :
  0 <= j <= Zlength lits0 -> Zlength (blk ++ skipn (Z.to_nat j) lits0) = Zlength blk + (Zlength lits0 - j).
Proof. intros. rewrite Zlength_app, Zlength_skipn. lia. Qed.

Lemma sh_epi_ok_ctx (HC: sh_ctx) :
  outarr_ok o /\ isptr (oa_base o) /\ oa_d o <= sh_oend <= oa_d o + oa_cap o /\
  (sh_oend < oa_d o + oa_cap o -> oa_d o + bsm <= sh_oend) /\ (oa_cap o = 0 -> sh_oend = oa_d o) /\
  bytes_ok lits /\ Zlength lits <= bsm /\ bsm <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold sh_ctx, sh_oend in *.
  destruct HC as (Ho & Hi & Hns & Hla & Hb & Hlb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdst & _ & _ & Hob & _).
  destruct Hla as (Hbo & Hn & Hla).
  split; [exact Ho|]. split; [exact Hob|].
  destruct Ho as (_ & _ & _ & Hd & Hcap & _).
  destruct l as [off| |lb|lb]; simpl in *; try contradiction; repeat split; auto; try lia.
  all: unfold WILDCOPY_OVERLENGTH in *; lia.
Qed.

Lemma sh_epi_ok_frame (HC: sh_ctx) (K j: Z) (c: list val) :
  0 <= K -> 0 <= j <= Zlength lits -> oa_d o + K + (Zlength lits - j) <= sh_oend -> Zlength c = oa_N o ->
  unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH)) ->
  exists (shs: share) (F: mpred), readable_share shs /\
   (data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o) * lit_res sh_ls |--
      data_at shs (tarray tuchar (Zlength lits - j)) (zbytes (skipn (Z.to_nat j) lits))
        (offset_val (sh_li0 + j) sh_lb) *
      data_at_ (oa_sh o) (tarray tuchar (Zlength lits - j)) (offset_val (oa_d o + K) (oa_base o)) * F) /\
   (data_at shs (tarray tuchar (Zlength lits - j)) (zbytes (skipn (Z.to_nat j) lits))
        (offset_val (sh_li0 + j) sh_lb) *
      data_at (oa_sh o) (tarray tuchar (Zlength lits - j)) (zbytes (skipn (Z.to_nat j) lits))
        (offset_val (oa_d o + K) (oa_base o)) * F |--
    data_at (oa_sh o) (tarray tuchar (oa_N o)) (sh_epi_ok_put c (oa_d o + K) (zbytes (skipn (Z.to_nat j) lits)))
      (oa_base o) * lit_res sh_ls).
Proof.
  intros HK Hj Hend Hc Hun.
  destruct (sh_epi_ok_ctx HC) as (Ho & Hob & Hoe & Hoe2 & Hcap0 & Hbo & Hlb & Hbm).
  pose proof Ho as (Hosh & Hoc & HoN & Hd & Hcap & HdN).
  set (bs := zbytes (skipn (Z.to_nat j) lits)).
  assert (Hbs: Zlength bs = Zlength lits - j) by (unfold bs; rewrite Zlength_map, Zlength_skipn; lia).
  assert (Hout1: field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
     data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o) =
     sh_epi_ok_seg (oa_sh o) c (oa_base o) 0 (oa_d o + K) *
     data_at (oa_sh o) (tarray tuchar (Zlength lits - j))
       (sublist (oa_d o + K) (oa_d o + K + (Zlength lits - j)) c) (offset_val (oa_d o + K) (oa_base o)) *
     sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (oa_N o)).
  { intros Hf. rewrite (sh_epi_ok_seg_full _ (oa_N o)) by auto.
    apply sh_epi_ok_seg_mid with (n := oa_N o); auto; lia. }
  assert (Hout2: field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
     data_at (oa_sh o) (tarray tuchar (oa_N o)) (sh_epi_ok_put c (oa_d o + K) bs) (oa_base o) =
     sh_epi_ok_seg (oa_sh o) c (oa_base o) 0 (oa_d o + K) *
     data_at (oa_sh o) (tarray tuchar (Zlength lits - j)) bs (offset_val (oa_d o + K) (oa_base o)) *
     sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (oa_N o)).
  { intros Hf. assert (Hpl: Zlength (sh_epi_ok_put c (oa_d o + K) bs) = oa_N o)
      by (rewrite sh_epi_ok_put_len; lia).
    rewrite (sh_epi_ok_seg_full _ (oa_N o)) by auto.
    rewrite (sh_epi_ok_seg_mid _ (oa_N o) _ _ 0 (oa_N o) (oa_d o + K) (Zlength lits - j)) by (auto; lia).
    rewrite <- Hbs at 2. rewrite sh_epi_ok_put_mid by lia.
    rewrite (sh_epi_ok_seg_ext _ (sh_epi_ok_put c (oa_d o + K) bs) c _ 0 (oa_d o + K))
      by (apply sh_epi_ok_put_out; lia).
    rewrite (sh_epi_ok_seg_ext _ (sh_epi_ok_put c (oa_d o + K) bs) c _ (oa_d o + K + (Zlength lits - j)))
      by (apply sh_epi_ok_put_out; lia).
    reflexivity. }
  unfold sh_ctx, sh_lb, sh_ls, sh_li0, sh_oend in *.
  destruct HC as (_ & Hi & Hns & Hla & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdst & Hr1 & _ & _ & Hib & _ & Hx & Hxb_ctx).
  destruct Hla as (_ & _ & Hla).
  destruct l as [off| |lb|lb]; simpl in Hns, Hla, Hdst, Hend, Hun |- *; try contradiction.
  - (* LIn *)
    destruct Hla as (Hoff & HoffN & Hsl & _).
    destruct Hi as (_ & _ & _ & _ & HiN & _).
    set (cs := iw_c i) in *.
    assert (Hsrc: field_compatible (tarray tuchar (Zlength cs)) [] (iw_base i) ->
      data_at sh1 (tarray tuchar (Zlength cs)) cs (iw_base i) =
      sh_epi_ok_seg sh1 cs (iw_base i) 0 (off + j) *
      data_at sh1 (tarray tuchar (Zlength lits - j)) bs (offset_val (off + j) (iw_base i)) *
      sh_epi_ok_seg sh1 cs (iw_base i) (off + j + (Zlength lits - j)) (Zlength cs)).
    { intros Hf. rewrite (sh_epi_ok_seg_full _ (Zlength cs)) by auto.
      rewrite (sh_epi_ok_seg_mid _ (Zlength cs) _ _ 0 (Zlength cs) (off + j) (Zlength lits - j))
        by (auto; unfold WILDCOPY_OVERLENGTH in *; lia).
      replace (sublist (off + j) (off + j + (Zlength lits - j)) cs) with bs; [reflexivity|].
      unfold bs. rewrite <- sh_epi_ok_skip by lia. rewrite <- Hsl.
      rewrite sublist_sublist by lia. f_equal; lia. }
    exists sh1, (andp (prop (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) /\
                     field_compatible (tarray tuchar (Zlength cs)) [] (iw_base i)))
      (sh_epi_ok_seg (oa_sh o) c (oa_base o) 0 (oa_d o + K) *
       sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (oa_N o) *
       sh_epi_ok_seg sh1 cs (iw_base i) 0 (off + j) *
       sh_epi_ok_seg sh1 cs (iw_base i) (off + j + (Zlength lits - j)) (Zlength cs)))%logic.
    split; [auto|]. split.
    + assert_PROP (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) /\
                   field_compatible (tarray tuchar (Zlength cs)) [] (iw_base i)) by entailer!.
      rewrite Hout1, Hsrc by tauto. sep_apply data_at_data_at_. entailer!.
    + Intros. rewrite Hout2, Hsrc by tauto. cancel.
  - (* LExtra *)
    specialize (Hx eq_refl).
    set (cs := zbytes lits ++ xrest).
    assert (Hcs: Zlength cs = Zlength lits + Zlength xrest) by (unfold cs; rewrite Zlength_app, Zlength_map; lia).
    pose proof (Zlength_nonneg xrest).
    assert (Hsrc: field_compatible (tarray tuchar (Zlength cs)) [] (lit_extra p) ->
      data_at Ews (tarray tuchar (Zlength cs)) cs (lit_extra p) =
      sh_epi_ok_seg Ews cs (lit_extra p) 0 j *
      data_at Ews (tarray tuchar (Zlength lits - j)) bs (offset_val j (lit_extra p)) *
      sh_epi_ok_seg Ews cs (lit_extra p) (j + (Zlength lits - j)) (Zlength cs)).
    { intros Hf. rewrite (sh_epi_ok_seg_full _ (Zlength cs)) by auto.
      rewrite (sh_epi_ok_seg_mid _ (Zlength cs) _ _ 0 (Zlength cs) j (Zlength lits - j)) by (auto; lia).
      replace (j + (Zlength lits - j)) with (Zlength lits) at 1 by lia.
      unfold cs at 2. rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
      rewrite sh_epi_ok_skip by lia. reflexivity. }
    exists Ews, (!! (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) /\
                     field_compatible (tarray tuchar (Zlength cs)) [] (lit_extra p)) &&
      (sh_epi_ok_seg (oa_sh o) c (oa_base o) 0 (oa_d o + K) *
       sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (oa_N o) *
       sh_epi_ok_seg Ews cs (lit_extra p) 0 j *
       sh_epi_ok_seg Ews cs (lit_extra p) (j + (Zlength lits - j)) (Zlength cs))).
    rewrite Z.add_0_l. split; [auto|]. split.
    + assert_PROP (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) /\
                   field_compatible (tarray tuchar (Zlength cs)) [] (lit_extra p)) by entailer!.
      rewrite Hout1, Hsrc by tauto. sep_apply data_at_data_at_. entailer!.
    + Intros. rewrite Hout2, Hsrc by tauto. cancel.
  - (* LDst *)
    destruct Hla as (Hdlb & HlbN & Hsl). unfold WILDCOPY_OVERLENGTH in *.
    assert (Hsrc: sublist (lb + j) (lb + j + (Zlength lits - j)) c = bs).
    { rewrite (sh_epi_ok_unch_sub (oa_c o) c (oa_d o) (Z.min lb (oa_d o + K + 32))) by (first [exact Hun | lia]).
      unfold bs. rewrite <- sh_epi_ok_skip by lia. rewrite <- Hsl.
      rewrite sublist_sublist by lia. f_equal; lia. }
    assert (Hmid: field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
      sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (oa_N o) =
      sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (lb + j) *
      data_at (oa_sh o) (tarray tuchar (Zlength lits - j)) bs (offset_val (lb + j) (oa_base o)) *
      sh_epi_ok_seg (oa_sh o) c (oa_base o) (lb + j + (Zlength lits - j)) (oa_N o)).
    { intros Hf. rewrite <- Hsrc. apply sh_epi_ok_seg_mid with (n := oa_N o); auto; lia. }
    exists (oa_sh o), (andp (prop (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o)))
      (sh_epi_ok_seg (oa_sh o) c (oa_base o) 0 (oa_d o + K) *
       sh_epi_ok_seg (oa_sh o) c (oa_base o) (oa_d o + K + (Zlength lits - j)) (lb + j) *
       sh_epi_ok_seg (oa_sh o) c (oa_base o) (lb + j + (Zlength lits - j)) (oa_N o)))%logic.
    split; [apply writable_readable; auto|]. split.
    + assert_PROP (field_compatible (tarray tuchar (oa_N o)) [] (oa_base o)) by entailer!.
      rewrite Hout1 by auto. rewrite Hmid by auto.
      sep_apply (data_at_data_at_ (oa_sh o) (tarray tuchar (Zlength lits - j))
        (sublist (oa_d o + K) (oa_d o + K + (Zlength lits - j)) c) (offset_val (oa_d o + K) (oa_base o))).
      entailer!.
    + Intros. rewrite Hout2 by auto. rewrite Hmid by auto. cancel.
Qed.

(* op is weakly valid (op != NULL): in the output array, or pws_pred W when cap = 0 *)
Lemma sh_epi_ok_wvp (HC: sh_ctx) (K: Z) (c: list val) :
  0 <= K -> oa_d o + K <= sh_oend ->
  pws_pred W * data_at (oa_sh o) (tarray tuchar (oa_N o)) c (oa_base o) |--
  weak_valid_pointer (offset_val (oa_d o + K) (oa_base o)).
Proof.
  intros HK Hend.
  destruct (sh_epi_ok_ctx HC) as (Ho & Hob & Hoe & Hoe2 & Hcap0 & _).
  pose proof Ho as (Hosh & Hoc & HoN & Hd & Hcap & HdN).
  assert (Hw := HC). unfold sh_ctx in Hw.
  destruct Hw as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _).
  destruct (Z.eq_dec (oa_cap o) 0) as [E|E].
  - specialize (Hcap0 E). replace (oa_d o + K) with (oa_d o) by lia.
    apply sepcon_weak_valid_pointer1. apply Hw; auto.
  - apply sepcon_weak_valid_pointer2.
    sep_apply data_at_data_at_. rewrite data_at__memory_block. Intros. simpl sizeof.
    rewrite Z.max_r by lia.
    apply memory_block_weak_valid_pointer; try lia.
    apply readable_nonidentity, writable_readable; auto.
Qed.

Lemma sh_epi_ok_sub_pp (q: val) (a b: Z) : isptr q ->
  force_val (sem_sub_pp tuchar (offset_val a q) (offset_val b q)) = Vlong (Int64.repr (a - b)).
Proof.
  intros. destruct q; try contradiction. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut i0 (Ptrofs.repr a)), (Ptrofs.add_commut i0 (Ptrofs.repr b)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply Int64.eqm_samerepr.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. rewrite <- Zminus_mod.
  change Ptrofs.modulus with Int64.modulus. apply Int64.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma sh_epi_ok_sub (q: val) (a b: Z) : isptr q ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val a q) (offset_val b q)) =
  Vlong (Int64.repr (a - b)).
Proof. intros. apply sh_epi_ok_sub_pp; auto. Qed.

Lemma sh_epi_ok_add (q: val) (a L: Z) : isptr q ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a q) (Vlong (Int64.repr L))) =
  offset_val (a + L) q.
Proof.
  intros. destruct q; try contradiction. simpl.
  f_equal. rewrite Ptrofs.add_assoc. f_equal. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64, Ptrofs.add. apply Ptrofs.eqm_samerepr.
  rewrite !Ptrofs.unsigned_repr_eq, Int64.unsigned_repr_eq. change Int64.modulus with Ptrofs.modulus.
  rewrite Zmod_mod. apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Zbits.eqmod_mod; reflexivity.
Qed.

Lemma sh_epi_ok_sameblock (q: val) (a b: Z) : isptr q -> is_true (sameblock (offset_val a q) (offset_val b q)).
Proof.
  intros. destruct q; try contradiction. simpl. unfold sameblock. destruct (peq b0 b0); [reflexivity | congruence].
Qed.

(* the capacity test lastLLSize > oend - op *)
Lemma sh_epi_ok_ltu (x y: Z) : 0 <= x < Int64.modulus -> 0 <= y < Int64.modulus ->
  Int64.ltu (Int64.repr y) (Int64.repr x) = (y <? x).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
  destruct (zlt y x), (y <? x) eqn:E; auto; [apply Z.ltb_ge in E | apply Z.ltb_lt in E]; lia.
Qed.

Lemma sh_epi_ok_lb (HC: sh_ctx) : lit_res sh_ls |-- !! isptr sh_lb && lit_res sh_ls.
Proof.
  unfold sh_ctx in HC. destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hob & Hib & _).
  unfold sh_lb, sh_ls, lit_base. destruct l; simpl lit_res.
  - entailer!.
  - entailer!.
  - entailer!.
  - entailer!.
Qed.

Lemma sh_epi_ok_test_eq (q: val) : isptr q -> weak_valid_pointer q |-- denote_tc_test_eq q (Vlong (Int64.repr 0)).
Proof.
  intros. destruct q; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq.
Qed.

Ltac sh_epi_ok_wvp_find := first [ apply derives_refl
  | apply sepcon_weak_valid_pointer1; sh_epi_ok_wvp_find | apply sepcon_weak_valid_pointer2; sh_epi_ok_wvp_find ].

(* for (;;break) c; d  (a do { c } while (0) of the macros) *)
Lemma sh_epi_ok_dw0 {cs: compspecs} (Delta: tycontext) (P Q: environ -> mpred) (c d: statement) (R: ret_assert) :
  semax Delta P c (loop1_ret_assert Q (overridePost Q R)) -> semax Delta Q d R ->
  semax Delta P (Ssequence (Sloop c Sbreak) d) R.
Proof.
  intros H1 H2. apply semax_seq with Q; [|exact H2].
  apply semax_loop with Q; [exact H1|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost; simpl.
  intros rho. apply andp_left2, derives_refl.
Qed.

(* the last literals: lastLLSize = litEnd - litPtr, the capacity error, memcpy, the return *)
Lemma sh_epi_ok_put_bytes (c: list val) (a: Z) (bs: list val) :
  byte_cells c -> byte_cells bs -> 0 <= a -> a + Zlength bs <= Zlength c -> byte_cells (sh_epi_ok_put c a bs).
Proof.
  intros Hc Hb Ha Hab. unfold byte_cells, sh_epi_ok_put in *.
  apply Forall_app; split; [apply Forall_sublist; exact Hc|].
  apply Forall_app; split; [exact Hb | apply Forall_sublist; exact Hc].
Qed.

(* the literals left, in their array (BlkSeqLoopShortX.xs_larr): in dst they are unchanged (after oend) *)
Lemma sh_epi_x_src (HC: sh_ctx) (HX: sh_lx) (K j: Z) (c: list val) :
  0 <= j <= Zlength lits -> Zlength c = oa_N o ->
  unchanged_outside (oa_c o) c (oa_d o) (Z.min sh_oend (oa_d o + K + WILDCOPY_OVERLENGTH)) ->
  sublist (xs_li0 l + j) (xs_li0 l + Zlength lits) (xs_larr l lxb i c) = zbytes (skipn (Z.to_nat j) lits).
Proof using All.
  intros Hj Hc Hun.
  destruct HC as (Ho & Hi & Hns & Hla & _).
  destruct HX as (_ & Hlxn & _ & Hlxs).
  destruct Hla as (_ & Hn & Hll).
  rewrite <- sh_epi_ok_skip by lia.
  unfold sh_oend in Hun.
  unfold xs_li0, xs_larr. destruct l as [off| |lb|lb]; simpl in Hns, Hll, Hun; try contradiction.
  - destruct Hll as (Hoff & HoN & Hsub & _). destruct Hi as (_ & _ & _ & _ & HiN & _).
    rewrite <- Hsub. rewrite sublist_sublist by (unfold WILDCOPY_OVERLENGTH in *; lia). f_equal; lia.
  - specialize (Hlxs eq_refl). rewrite !Z.add_0_l, !sublist_map. f_equal.
    set (n := Zlength lits) in *. rewrite <- Hlxs at 1.
    rewrite sublist_sublist by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    f_equal; lia.
  - destruct Hll as (Hdlb & HlbN & Hsub). destruct Ho as (_ & Hoc & _ & Hod & Hocap & HodN).
    unfold WILDCOPY_OVERLENGTH in *.
    rewrite (sh_epi_ok_unch_sub (oa_c o) c (oa_d o) (Z.min lb (oa_d o + K + 32))) by (first [exact Hun | lia]).
    rewrite <- Hsub. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma sh_epi_ok (HC: sh_ctx) (HX: sh_lx) : semax sh_Delta sh_aft sh_EPI sh_SR.
Proof using All.
  unfold sh_aft. Intros K c crep j. unfold sh_aft_at.
  cbv [sh_EPI sq_drop sh_body f_ZSTD_decompressSequences_body fn_body].
  unfold sh_SR, sh_POST.
  unfold sh_Delta. simplify_func_tycontext. abbreviate_semax.
  destruct (sh_epi_ok_ctx HC) as (Ho & Hob & Hoe & Hoe2 & Hcap0 & Hbo & Hlb & Hbm).
  pose proof Ho as (Hosh & Hoc & HoN & Hd & Hcap & HdN). unfold ZSTD_BLOCKSIZE_MAX in Hbm.
  sep_apply (sh_epi_ok_lb HC). Intros.
  rename H7 into Hsbc. destruct H6 as [H6 H6x].
  pose proof (xs_epi fs os rep l lits lxb nbSeq o i h K c crep j (sh_xs_ctx HC HX) H H0 H1 H2
                (sh_epi_x_src HC HX K j c H1 H2 H3) H6x) as [XE XS].
  forward. forward.
  { entailer!; try apply prop_right; apply sh_epi_ok_sameblock; auto. }
  rewrite sh_epi_ok_sub by auto.
  replace (sh_li0 + Zlength lits - (sh_li0 + j)) with (Zlength lits - j) by lia.
  apply -> seq_assoc. apply dec_skipbreak_seq. apply -> seq_assoc.
  match goal with |- semax _ (PROPx _ (LOCALx ?L (SEPx ?S))) _ _ =>
    apply sh_epi_ok_dw0 with (Q := PROPx [Zlength lits - j <= sh_oend - (oa_d o + K)] (LOCALx L (SEPx S))) end.
  - forward_if.
    { entailer!; try apply prop_right; apply sh_epi_ok_sameblock; auto. }
    + (* the capacity error *)
      rewrite sh_epi_ok_sub_pp in H7 by auto. simpl in H7.
      rewrite sh_epi_ok_ltu in H7 by rep_lia.
      assert (Hlt: sh_oend - (oa_d o + K) < Zlength lits - j)
        by (destruct (_ <? _) eqn:E in H7; [apply Z.ltb_lt in E; lia | inversion H7]).
      clear H7.
      apply dec_skipbreak_seq.
      match goal with |- semax _ ?P _ _ => apply sh_epi_ok_dw0 with (Q := P) end.
      { forward_if. { contradiction. } { forward. entailer!. } }
      apply dec_skipbreak_seq. apply dec_skipbreak_seq.
      forward.
      assert (HXN: seqs_exact os rep l lits lxb nbSeq o i h (Int64.unsigned (Int64.repr (-70))) c crep).
      { apply xs_exact_none; [reflexivity|]. apply XE. exact Hlt. }
      Exists (Int64.unsigned (Int64.repr (-70))) c crep.
      apply andp_right.
      { apply prop_right.
        assert (Hr: Int64.unsigned (Int64.repr (-70)) = 18446744073709551546) by reflexivity.
        rewrite Int64.repr_unsigned, Hr.
        split; [rep_lia|]. split; [lia|]. split; [auto|].
        split. { eapply sh_epi_ok_unch_mono; [exact H3 | lia]. }
        split. { intros E. discriminate E. }
        split; [|split; [intros _; exact (sh_dec_err 70 ltac:(lia) ltac:(lia) ltac:(lia)) |
                         split; [exact Hsbc | split; [exact HXN | reflexivity]]]].
        intros Hpre. unfold sh_aft_mdl0 in H6.
        destruct (seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h))
          as [[cnt rep2]|]; auto.
        intros Hcnt. right. split; [reflexivity|].
        destruct (H6 Hpre Hcnt) as (blk & HK & _ & Hc' & _).
        assert (Hl: Zlength cnt = K + (Zlength lits - j)) by (subst cnt; rewrite sh_epi_ok_cnt_len; lia).
        destruct (Z.lt_ge_cases sh_oend (oa_d o + oa_cap o)) as [E|E].
        - specialize (Hoe2 E). lia.
        - lia. }
      sep_apply (sh_release HC HX).
      sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr).
      cancel.
    + rewrite sh_epi_ok_sub_pp in H7 by auto. simpl in H7.
      rewrite sh_epi_ok_ltu in H7 by rep_lia.
      assert (Hle: Zlength lits - j <= sh_oend - (oa_d o + K))
        by (destruct (_ <? _) eqn:E in H7; [inversion H7 | apply Z.ltb_ge in E; lia]).
      clear H7.
      forward. entailer!.
  - Intros. apply semax_if_seq. forward_if.
    { entailer!. eapply derives_trans; [|apply sh_epi_ok_test_eq; destruct (oa_base o); try contradiction; simpl; auto].
      sep_apply (sh_epi_ok_wvp HC K c H H0). sh_epi_ok_wvp_find. }
    2: { exfalso. revert H8. clear - Hob. destruct (oa_base o); try contradiction. discriminate. }
    forward.
    destruct (sh_epi_ok_frame HC K j c H H1 ltac:(lia) H2 H3) as (shs & F & Hrs & Hsplit & Hjoin).
    sep_apply Hsplit.
    forward_call (shs, oa_sh o, offset_val (sh_li0 + j) sh_lb, offset_val (oa_d o + K) (oa_base o),
      existT (fun t => reptype t) (tarray tuchar (Zlength lits - j)) (zbytes (skipn (Z.to_nat j) lits))).
    { simpl projT1. simpl projT2. cancel. }
    { cbn [projT1 projT2]. split; [simpl; rep_lia |].
      apply memcpy_ok_zbytes; [rewrite Zlength_skipn; lia | apply sh_epi_ok_bytes_skipn; exact Hbo]. }
    simpl projT1. simpl projT2.
    sep_apply Hjoin. Intros.
    forward.
    rewrite sh_epi_ok_add by auto.
    apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
    forward.
    { entailer!; try apply prop_right; apply sh_epi_ok_sameblock; auto. }
    rewrite sh_epi_ok_sub_pp by auto.
    replace (oa_d o + K + (Zlength lits - j) - oa_d o) with (K + (Zlength lits - j)) by lia.
    set (bs := zbytes (skipn (Z.to_nat j) lits)).
    assert (Hbs: Zlength bs = Zlength lits - j) by (unfold bs; rewrite Zlength_map, Zlength_skipn; lia).
    Exists (K + (Zlength lits - j)) (sh_epi_ok_put c (oa_d o + K) bs) crep.
    apply andp_right.
    { apply prop_right.
      assert (Hle': oa_d o + K + Zlength bs <= Zlength c) by lia.
      assert (Hne: is_error_code (K + (Zlength lits - j)) = false)
        by (unfold is_error_code; apply Z.ltb_ge; lia).
      assert (Hsub: sublist (oa_d o) (oa_d o + (K + (Zlength lits - j))) (sh_epi_ok_put c (oa_d o + K) bs) =
                    sublist (oa_d o) (oa_d o + K) c ++ bs).
      { rewrite <- sh_epi_ok_put_split by lia. f_equal; lia. }
      assert (HXS: seqs_exact os rep l lits lxb nbSeq o i h (K + (Zlength lits - j)) (sh_epi_ok_put c (oa_d o + K) bs)
                     crep).
      { apply xs_exact_some; [exact Hne|]. intros rb m body bo lr li lim sp ps ds de Hh.
        pose proof (XS ltac:(rewrite <- sh_xs_oend; lia) rb m body bo lr li lim sp ps ds de Hh) as HE.
        destruct (xs_X os rep l lxb nbSeq o i rb m body lr li lim sp ps ds de) as [[[mm op'] rep2]|];
          [|contradiction].
        destruct HE as (E1 & E2 & E3). split; [lia|]. split; [|auto].
        unfold sh_epi_ok_put. rewrite Hbs. exact E2. }
      split; [rep_lia|]. split; [rewrite sh_epi_ok_put_len by lia; lia|]. split; [auto|].
      split. { eapply sh_epi_ok_unch_put; [exact H3 | lia | lia | lia | lia | lia | lia]. }
      split.
      { intros _. split; [lia|]. split.
        { eapply sh_epi_ok_unch_put; [exact H3 | lia | lia | lia | lia | unfold WILDCOPY_OVERLENGTH; lia
            | unfold WILDCOPY_OVERLENGTH; lia]. }
        intros Hh He. destruct H5 as (H5 & _). destruct (sh_epi_ok_bytes _ H5) as (blk0 & Hb0 & Hbo0).
        exists (blk0 ++ skipn (Z.to_nat j) lits). rewrite Hsub, Hb0, map_app. split; [reflexivity|].
        apply Forall_app; split; [exact Hbo0 | apply sh_epi_ok_bytes_skipn; exact Hbo]. }
      split; [|split; [intros E; rewrite Hne in E; discriminate E |
                       split; [|split; [exact HXS | reflexivity]]]].
      2: { intros B1 B2 B3. apply sh_epi_ok_put_bytes; [apply Hsbc; auto | | lia | lia].
           unfold bs. apply sh_release_zbytes. apply Forall_skipn. exact Hbo. }
      intros Hpre. unfold sh_aft_mdl0 in H6.
      destruct (seqs_model os (iw_s i) nbSeq rep (hc_hist h) (hc_out h) lits (hc_wsize h))
        as [[cnt rep2]|]; auto.
      intros Hcnt. left.
      destruct (H6 Hpre Hcnt) as (blk & HK & Hsb & Hc' & Hrep).
      assert (Hl: Zlength cnt = K + (Zlength lits - j)) by (subst cnt; rewrite sh_epi_ok_cnt_len; lia).
      split; [exact Hne|]. split; [lia|]. split; [|auto].
      rewrite Hsub, Hsb, Hc', map_app. reflexivity. }
    sep_apply (sh_release HC HX).
    sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val (sh_li0 + j) sh_lb) v_litPtr).
    cancel.
Qed.

(* the shapes the assembly uses *)
Definition sh_INC : statement := match sh_LOOP with Sloop _ c => c | _ => Sskip end.
Definition sh_TEST : statement := sq_nth 0 sh_LB.
Lemma sh_BREST_eq : sh_BREST = Ssequence sh_LOOP sh_END.
Proof. reflexivity. Qed.
Lemma sh_LOOP_eq : sh_LOOP = Sloop sh_LB sh_INC.
Proof. reflexivity. Qed.
Lemma sh_LB_eq : sh_LB = Ssequence sh_TEST (Ssequence sh_DEC sh_EXEC).
Proof. reflexivity. Qed.

Lemma sh_oend_ge (HC: sh_ctx) : oa_d o <= sh_oend.
Proof.
  destruct HC as (Ho & _ & Hns & Hla & _).
  destruct Ho as (_ & _ & _ & _ & Hcap & _).
  unfold sh_oend. destruct l; try lia.
  destruct Hla as (_ & _ & Hlb & _). lia.
Qed.

Lemma sh_aft_mdl_nb0 (HC: sh_ctx) (Hnb0: nbSeq = 0) : sh_aft_mdl0 0 (oa_c o) rep 0.
Proof.
  unfold sh_aft_mdl0, seqs_model. rewrite Hnb0. cbn [Z.eqb]. intros _.
  cbn [exec_seqs]. rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
  intros _. exists []. rewrite Z.add_0_r, sublist_nil. cbn. auto.
Qed.

Lemma sh_main (HG: GLOBALS_obligation) (HC: sh_ctx) (HX: sh_lx) (HD: sh_dctx) :
  semax sh_Delta S_start sh_body sh_SR.
Proof.
  apply sh_prologue_ok; [exact HC|].
  change (sq_drop 9 sh_body) with (Ssequence (Sifthenelse (Etempvar _nbSeq tint) sh_BIG Sskip) sh_EPI).
  eapply semax_seq; [| apply sh_epi_ok; [exact HC | exact HX]].
  unfold sh_Delta. simplify_func_tycontext. unfold S_pre.
  forward_if sh_aft.
  - (* nbSeq > 0 *)
    assert (HC' := HC). destruct HC' as (_ & _ & _ & _ & _ & _ & Hnb & Hpos & _).
    assert (Ht: exists t, os = Some t)
      by (destruct os as [t|]; [eauto | exfalso; destruct Hpos; [lia | congruence]]).
    destruct Ht as [t Hos].
    unfold POSTCONDITION, Delta, Delta_specs, abbreviate.
    eapply sh_init_ok; [exact HG | exact HC | exact HX | exact HD | exact Hos | lia | ].
    intros tp sht fm Rt HT.
    rewrite sh_BREST_eq.
    eapply semax_seq; [| apply sh_end_ok; [exact HC | exact HX | exact Hos | exact HT | lia]].
    rewrite sh_LOOP_eq.
    eapply semax_pre with (P' := EX id: Z, sh_inv t tp sht fm Rt id).
    { apply andp_left2. apply (exp_right 0). apply derives_refl. }
    apply semax_loop with
      (Q' := EX id: Z, !! (id < nbSeq) &&
             EX K: Z, EX c: list val, EX crep: Z * Z * Z, EX j: Z, EX pos: Z, EX lo: Z, EX st: Z * Z * Z,
               sh_inv_at t tp sht fm Rt (id + 1) (nbSeq - id) K c crep j pos lo st).
    + (* the body *)
      apply extract_exists_pre; intro id. unfold sh_inv.
      apply extract_exists_pre; intro K. apply extract_exists_pre; intro c.
      apply extract_exists_pre; intro crep. apply extract_exists_pre; intro j.
      apply extract_exists_pre; intro pos. apply extract_exists_pre; intro lo.
      apply extract_exists_pre; intro st.
      rewrite sh_LB_eq.
      apply semax_seq with (Q := !! (id < nbSeq) && sh_inv_at t tp sht fm Rt id (nbSeq - id) K c crep j pos lo st).
      { change sh_TEST with (Sifthenelse (Etempvar _nbSeq tint) Sskip Sbreak).
        unfold sh_Delta. simplify_func_tycontext. unfold sh_inv_at. abbreviate_semax. Intros.
        forward_if.
        - eapply semax_post'; [| apply semax_skip].
          apply andp_left2. apply andp_right; [apply prop_right; lia|].
          apply andp_right; [apply prop_right; cbn [fold_right]; repeat match goal with |- _ /\ _ => split end; auto; lia|]. apply andp_left2, derives_refl.
        - assert (Hid: id = nbSeq).
          { assert (Hs: Int.signed (Int.repr (nbSeq - id)) = 0)
              by (match goal with Hx: Int.repr (nbSeq - id) = Int.zero |- _ => rewrite Hx end; reflexivity).
            unfold LONGNBSEQ in Hnb. rewrite Int.signed_repr in Hs by rep_lia. lia. }
          subst id. forward.
          Exists K c crep j pos lo st. entailer!. }
      apply semax_extract_prop; intro Hlt.
      eapply semax_seq'; [apply sh_dec_ok; [exact HC | exact Hos | exact HT | exact Hlt] |].
      apply extract_exists_pre; intro pos'. apply extract_exists_pre; intro lo'.
      apply extract_exists_pre; intro st'. apply extract_exists_pre; intro ll.
      apply extract_exists_pre; intro ml. apply extract_exists_pre; intro ov.
      eapply semax_post; [| | | | apply sh_exec_ok; [exact HC | exact HX | exact Hos | exact HT]];
        unfold loop1_ret_assert, overridePost, sh_SR, frame_ret_assert, function_body_ret_assert;
        cbn [RA_normal RA_break RA_continue RA_return].
      all: try (intros vl; apply andp_left2, derives_refl).
      all: try (apply andp_left2; rewrite FF_sepcon; apply FF_left).
      all: apply andp_left2; Intros K' c' crep' j'; apply (exp_right id);
        apply andp_right; [apply prop_right; lia|]; Exists K' c' crep' j' pos' lo' st'; apply derives_refl.
    + (* nbSeq-- *)
      apply extract_exists_pre; intro id. apply semax_extract_prop; intro Hlt.
      apply extract_exists_pre; intro K. apply extract_exists_pre; intro c.
      apply extract_exists_pre; intro crep. apply extract_exists_pre; intro j.
      apply extract_exists_pre; intro pos. apply extract_exists_pre; intro lo.
      apply extract_exists_pre; intro st.
      eapply semax_post with
        (R' := normal_ret_assert (sh_inv_at t tp sht fm Rt (id + 1) (nbSeq - (id + 1)) K c crep j pos lo st));
        unfold loop2_ret_assert, overridePost, sh_SR, frame_ret_assert, function_body_ret_assert, normal_ret_assert;
        cbn [RA_normal RA_break RA_continue RA_return].
      * apply andp_left2. apply (exp_right (id + 1)). unfold sh_inv. Exists K c crep j pos lo st. apply derives_refl.
      * apply andp_left2, FF_left.
      * apply andp_left2, FF_left.
      * intros vl. apply andp_left2, FF_left.
      * change sh_INC with (Sset _nbSeq (Ebinop Osub (Etempvar _nbSeq tint) (Econst_int (Int.repr 1) tint) tint)).
        unfold sh_Delta. simplify_func_tycontext. unfold sh_inv_at. abbreviate_semax. Intros.
        forward.
        { entailer!. unfold LONGNBSEQ in Hnb. rewrite !Int.signed_repr by rep_lia. rep_lia. }
        rewrite sub_repr. replace (nbSeq - id - 1) with (nbSeq - (id + 1)) by lia.
        entailer!.
  - (* nbSeq = 0 *)
    assert (Hnb0: nbSeq = 0).
    { assert (HC' := HC). destruct HC' as (_ & _ & _ & _ & _ & _ & Hnb & _).
      assert (Hs: Int.signed (Int.repr nbSeq) = 0) by (rewrite H; reflexivity).
      unfold LONGNBSEQ in Hnb. rewrite Int.signed_repr in Hs by rep_lia. lia. }
    pose proof (sh_oend_ge HC) as Hoe. assert (Hm: sh_aft_mdl 0 (oa_c o) rep 0)
      by (split; [exact (sh_aft_mdl_nb0 HC Hnb0) | exact (xs_aft_nb0 fs os rep l lits lxb nbSeq o i h (sh_xs_ctx HC HX) Hnb0)]).
    assert (HC' := HC). destruct HC' as (Ho & _ & _ & Hla & _ & _ & _ & _ & _ & Hrep & _).
    destruct Ho as (_ & HN & _).
    forward.
    unfold sh_aft, sh_aft_at. Exists 0 (oa_c o) rep 0.
    rewrite Hnb0. cbn [Z.eqb]. rewrite !Z.add_0_r.
    entailer!.
    split; [rewrite Z.add_0_r, sublist_nil; constructor | intros Hcap; apply (sh_rd0 HC HD Hcap)].
Qed.

End Short.

(* litfields with LExtra's tail named *)
Lemma sh_lf_intro (p: val) (l: litloc) (lits lxb: list Z) (o: outarr) (i: inwin) :
  (l = LExtra -> Zlength lits <= LITBUFFEREXTRASIZE) ->
  litfields p (oa_base o) (iw_base i) l lits lxb |--
  EX xrest: list val, !! ((l = LExtra -> Zlength xrest = LITEXTRA_N - Zlength lits) /\
                         (l = LExtra -> byte_cells xrest) /\ sh_lx l lits xrest lxb) &&
    sh_lf p l lits o i xrest lxb.
Proof.
  intros Hn.
  assert_PROP (Zlength lxb = LITEXTRA_N /\ bytes_ok lxb) as HL.
  { unfold litfields, lit_extra_at. destruct l; entailer!. }
  destruct HL as [Hlx Hbx].
  destruct l; unfold sh_lf.
  - Exists (@nil val). entailer!. unfold sh_lx. repeat split; auto; discriminate.
  - specialize (Hn eq_refl). unfold litfields, lit_extra_at. Intros.
    set (n := Zlength lits) in *.
    assert (E: zbytes lits ++ zbytes (sublist n LITEXTRA_N lxb) = zbytes lxb).
    { rewrite <- map_app. f_equal. rewrite <- H at 1. rewrite <- Hlx.
      pose proof (Zlength_nonneg lits).
      rewrite sublist_rejoin by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
      apply sublist_same; lia. }
    Exists (zbytes (sublist n LITEXTRA_N lxb)). rewrite E.
    assert (Hb: byte_cells (zbytes (sublist n LITEXTRA_N lxb))).
    { apply sh_release_zbytes. apply Forall_sublist. exact Hbx. }
    pose proof (Zlength_nonneg lits) as Hn0.
    entailer!.
    split; [rewrite Zlength_map, Zlength_sublist; unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia|].
    unfold sh_lx. repeat split; auto.
  - Exists (@nil val). entailer!. unfold sh_lx. repeat split; auto; discriminate.
  - Exists (@nil val). entailer!. unfold sh_lx. repeat split; auto; discriminate.
Qed.

Lemma body_ZSTD_decompressSequences_body :
  GLOBALS_obligation ->
  semax_body Vprog LOOP_GB f_ZSTD_decompressSequences_body (_ZSTD_decompressSequences_body, seqs_spec not_split).
Proof.
  intros HG.
  start_function.
  destruct (inwin_bits i H0) as (sh1 & sh2 & Ri & Hr1 & Hr2 & Hsplit).
  assert_PROP (isptr (oa_base o) /\ isptr (iw_base i)) as Hptrs by entailer!.
  sep_apply (sh_lf_intro p l lits lxb o i
               ltac:(intros ->; destruct H2 as (_ & _ & Hle); exact Hle)). Intros xrest.
  assert_PROP (match hc_ext h with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) as Heb.
  { destruct (hc_ext h); unfold ext_res; entailer!. }
  assert (Hpend: is_pointer_or_null (fs_prefixStart fs) /\ is_pointer_or_null (fs_virtualStart fs) /\
                 is_pointer_or_null (fs_dictEnd fs) /\
                 (match l with LDst lb => oa_d o + bsm <= lb | _ => True end)).
  { destruct H12 as (Hq1 & Hq2 & Hq3). split; [exact Hq1|]. split; [exact Hq2|]. split.
    - destruct Hq3 as [-> | [(k & _ & ->) | Hq3]]; [simpl; auto | destruct Hptrs as [Hb1 _]|].
      + destruct (oa_base o); try contradiction; exact I.
      + destruct (hc_ext h); try contradiction. destruct Hq3 as [-> _].
        destruct eb; try contradiction; exact I.
    - unfold lit_pos in H13. destruct l; auto. unfold WILDCOPY_OVERLENGTH in H13. lia. }
  assert (HC: sh_ctx fs os fe rep l lits nbSeq bsm W o i h sh1 sh2 Ri xrest).
  { destruct Hpend as (Hp1 & Hp2 & Hp3 & Hp4), Hptrs as [Hb1 Hb2].
    unfold sh_ctx; repeat (split; [assumption|]); assumption. }
  assert (HD: sh_dctx l lits o h) by (split; assumption).
  assert (HX: sh_lx l lits xrest lxb) by tauto.
  unfold MORE_COMMANDS, POSTCONDITION, Delta, Delta_specs, abbreviate.
  eapply semax_post; [| | | |
    eapply semax_pre; [| exact (sh_main gv p fs ox os fe rep l lits nbSeq bsm W o i h v_litPtr v_seqState
                                  v_sequence sh1 sh2 Ri xrest lxb HG HC HX HD)]].
  5: { apply andp_left2. unfold S_start. apply andp_derives; [apply derives_refl|].
        apply andp_derives; [apply derives_refl|]. unfold SEPx. intro rho. cbv [fold_right_sepcon]. cancel. }
  1-3: apply andp_left2; unfold sh_SR, frame_ret_assert, function_body_ret_assert;
       cbn [RA_normal RA_break RA_continue]; unfold bind_ret, tulong; rewrite FF_sepcon; apply FF_left.
  intros vl. apply andp_left2. unfold sh_SR, frame_ret_assert, function_body_ret_assert.
  cbn [RA_return]. apply derives_refl.
Qed.
