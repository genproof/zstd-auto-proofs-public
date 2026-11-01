(* FS3 streaming, case zdss_loadHeader: piece D (s14..s21: maxBlockSizeParam cap, buffer sizes, (re)allocation,
   streamStage = zdss_read), with the exact facts of LH3XDefs.lhD_x: oversizedDuration as
   ZSTD_DCtx_updateOversizedDuration sets it, and either the calloc'd (zeroed) buffer of the needed sizes or the same
   buffer. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs.
Local Open Scope logic.

Section CM_LH3D_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers (v2's StreamSeg_lhD.v) ---------- *)

Lemma stab_eq0 : forall b: bool, Int.repr (if b then 1 else 0) = Int.repr 0 -> b = false.
Proof. intros [|] E; auto. apply (f_equal Int.unsigned) in E. rewrite !Int.unsigned_repr in E by rep_lia. lia. Qed.

Lemma stab_ne0 : forall b: bool, Int.repr (if b then 1 else 0) <> Int.repr 0 -> b = true.
Proof. intros [|] E; auto; contradiction E; reflexivity. Qed.

(* do { } while (0) *)
Lemma semax_dowhile0 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_seq with P; [| exact H].
destruct R as [Rn Rb Rc Rr]; simpl.
apply semax_loop with (Q' := P).
- eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto;
    try apply FF_left.
- eapply semax_pre; [| apply semax_break]. simpl. intros; apply andp_left2; auto.
Qed.

Lemma seq_assoc_l : forall {CS: compspecs} {Espec: OracleKind} Delta P s1 s2 s3 R,
  semax Delta P (Ssequence s1 (Ssequence s2 s3)) R -> semax Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof. intros. first [apply -> seq_assoc; exact H | apply <- seq_assoc; exact H]. Qed.

Ltac dw0 :=
  match goal with
  | |- semax _ _ (Ssequence (Sloop Sskip Sbreak) _) _ => apply semax_dowhile0
  | |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply seq_assoc_l; dw0
  end.

(* for (;;) { c; break; }, followed by d (c may return; no break/continue in the context) *)
Lemma semax_loopbrk_seq : forall {CS: compspecs} {Espec: OracleKind} Delta P Q c d R,
  RA_break R = FF -> RA_continue R = FF ->
  semax Delta P c (overridePost Q R) -> semax Delta Q d R ->
  semax Delta P (Ssequence (Sloop c Sbreak) d) R.
Proof.
intros CS Espec Delta P Q c d R Hb Hc H1 H2.
apply semax_seq with Q; [| exact H2].
apply semax_loop with (Q' := Q).
- eapply semax_post; [.. | exact H1]; destruct R as [Rn Rb Rc Rr]; simpl in *; subst; intros;
    try (apply andp_left2; auto; fail); apply andp_left2; apply FF_left.
- eapply semax_pre; [| apply semax_break]. destruct R; simpl. intros; apply andp_left2; auto.
Qed.

(* the stream buffer as ZSTD_customFreeP takes it back: its allocator's token and its bytes (none at NULL) *)
Lemma ring_rep_free : forall am b n c, ring_rep am b n c |--
  (if eq_dec b nullval then emp else blk_tok am (tarray tuchar n) b * data_at_ Ews (tarray tuchar n) b).
Proof.
intros. unfold ring_rep. destruct (eq_dec b nullval).
- entailer!.
- Intros. sep_apply (data_at_data_at_ Ews (tarray tuchar n) c b). cancel.
Qed.

(* the customMem field as the argument of the allocation helpers *)
Lemma cmem_fa : forall am p, field_at Ews t_dctx (DOT _customMem) (cmem_v am) p =
  data_at Ews t_cmem3 (cmem_v am) (field_address t_dctx (DOT _customMem) p).
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

(* return e, whose value is v, into a custom ret_assert *)
Lemma semax_return_v : forall {CS: compspecs} {Espec: OracleKind} Delta P (e: expr) (v: val) R,
  let e' := Ecast e (ret_type Delta) in
  ENTAIL Delta, P |-- tc_expr Delta e' ->
  ENTAIL Delta, P |-- local (fun rho => v = eval_expr e' rho) ->
  ENTAIL Delta, P |-- RA_return R (Some v) ->
  semax Delta P (Sreturn (Some e)) R.
Proof.
intros CS Espec Delta P e v R e' H1 H2 H3.
eapply semax_pre; [| apply semax_return].
apply andp_right; [exact H1|].
eapply derives_trans; [apply andp_right; [exact H2 | exact H3]|].
intro rho. unfold local, lift1, liftx, lift. simpl. normalize.
apply derives_refl.
Qed.

Lemma repr_err_code : forall n, Int64.repr (err_code n) = Int64.repr (- n).
Proof. intros n. apply Int64.eqm_samerepr. exists 1. unfold err_code. reflexivity. Qed.

(* the value of `return (size_t)-n` *)
Ltac ret_err_val :=
  intro rho; unfold local, lift1; apply prop_right; clear; rewrite repr_err_code; reflexivity.

Lemma sizeof_tuchar_arr : forall n, 0 <= n -> sizeof (tarray tuchar n) = n.
Proof. intros n Hn. simpl. lia. Qed.

Lemma byte_cells_nil : byte_cells nil.
Proof. constructor. Qed.

Lemma byte_cells_zeros : forall n, byte_cells (Zrepeat (Vint Int.zero) n).
Proof.
intros n. unfold byte_cells, Zrepeat. apply Forall_forall. intros x Hx.
apply repeat_spec in Hx. subst x. exists 0. split; [lia | reflexivity].
Qed.

(* ---------- the states of piece D ---------- *)

(* the stream fields after piece D: buffer ib (ins + outs bytes, out part at ob), oversizedDuration ov *)
Definition sf_lhD (s: sfields) (st: Z) (ib: val) (ins: Z) (ob: val) (outs: Z) (ov: Z) (ring: list val) : sfields :=
  {| sf_stage := st; sf_inBuff := ib; sf_inSize := ins; sf_inPos := sf_inPos s;
     sf_outBuff := ob; sf_outSize := outs; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := sf_hbuf s; sf_over := ov; sf_ring := ring; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* the context after the maxBlockSizeParam cap *)
Definition lhD_kc (k3: cst3) (h: frame_header) : cst3 :=
  c3_with_fs k3 (fsu_fParams (c3_fs k3) (fh_val (fh_adj h (lh_bsm k3 h)))) (c3_tabs k3).

(* the pieces below work on any context kc whose fParams is the header h with blockSizeMax bsm *)
Definition lhD_nin (bsm: Z) : Z := Z.max bsm 4.
Definition lhD_nout (k: cst3) (h: frame_header) (bsm: Z) : Z := if c3_stable k then 0 else ring_needed h bsm.
Definition lhD_ov (k: cst3) (h: frame_header) (bsm: Z) : Z :=
  if is_overflow (sf_inSize (c3_s k)) (sf_outSize (c3_s k)) (lhD_nin bsm) (lhD_nout k h bsm)
  then (sf_over (c3_s k) + 1) mod 2 ^ 64 else 0.
Definition lhD_ts (k: cst3) (h: frame_header) (bsm: Z) : bool :=
  orb (sf_inSize (c3_s k) <? lhD_nin bsm) (sf_outSize (c3_s k) <? lhD_nout k h bsm).
Definition lhD_tl (k: cst3) (h: frame_header) (bsm: Z) : bool := ZSTD_WORKSPACETOOLARGE_MAXDURATION <=? lhD_ov k h bsm.

(* the context after updateOversizedDuration *)
Definition lhD_k2 (k: cst3) (h: frame_header) (bsm: Z) : cst3 :=
  let s := c3_s k in
  c3_with_s k (sf_lhD s (sf_stage s) (sf_inBuff s) (sf_inSize s) (sf_outBuff s) (sf_outSize s) (lhD_ov k h bsm)
                 (sf_ring s)).

(* the context's allocator has room for the new stream buffer once the old one is given back: it then holds the
   context and its other blocks (dctx_size + sf_held bytes, sf_held >= 0 by sgroup) *)
Definition lhD_room (kc: cst3) (h: frame_header) (bsm: Z) : Prop :=
  0 <= sf_held (c3_s kc) ->
  cm_room (sf_mem (c3_s kc)) (dctx_size + sf_held (c3_s kc)) (lhD_nin bsm + lhD_nout kc h bsm).

(* what the pieces assume of kc and bsm *)
Definition lhD_pre (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3) (bsm: Z) : Prop :=
  fs_fParams (c3_fs kc) = fh_val (fh_adj h bsm) /\ 0 <= bsm <= ZSTD_BLOCKSIZE_MAX /\
  0 <= fh_contentSize h <= Int64.max_unsigned /\ 0 <= fh_windowSize h /\
  Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN <= dp_wmax (c3_par kc) /\
  (forall s', lhD_memfail (c3_s kc) s' ->
     lh_rc a w hb (err_code ZSTD_error_memory_allocation) (a_ipos a) (lw_k w (c3_with_s kc s'))) /\
  lhD_room kc h bsm.

(* the exact facts at the end of the pieces, at the context kc after the cap (before piece D: its stream fields s):
   oversizedDuration as updateOversizedDuration sets it (lhD_ov, with size_t arithmetic), then the calloc'd buffer of
   the needed sizes (zeros) when tooSmall || tooLarge, else the same buffer; with the bounds that let lhD_xg_x read
   the size_t arithmetic as plain arithmetic *)
Definition lhD_xg (kc: cst3) (h: frame_header) (bsm: Z) (s3: sfields) : Prop :=
  let s := c3_s kc in
  0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\ 0 <= sf_over s /\
  4 <= lhD_nin bsm <= ZSTD_BLOCKSIZE_MAX /\ 0 <= lhD_nout kc h bsm <= 2 ^ 32 /\
  sf_over s3 = lhD_ov kc h bsm /\
  if orb (lhD_ts kc h bsm) (lhD_tl kc h bsm)
  then sf_inSize s3 = lhD_nin bsm /\ sf_outSize s3 = lhD_nout kc h bsm /\
       sublist (lhD_nin bsm) (lhD_nin bsm + lhD_nout kc h bsm) (sf_ring s3) = Zrepeat (Vint Int.zero) (lhD_nout kc h bsm)
  else sf_inSize s3 = sf_inSize s /\ sf_outSize s3 = sf_outSize s /\ sf_ring s3 = sf_ring s.

(* the bounds of the needed sizes *)
Lemma lhD_pre_bnds : forall a w hb h kc bsm, lhD_pre a w hb h kc bsm -> dp_wmax (c3_par kc) <= 2 ^ 31 ->
  4 <= lhD_nin bsm <= ZSTD_BLOCKSIZE_MAX /\ 0 <= lhD_nout kc h bsm <= 2 ^ 31 + 2 ^ 20.
Proof.
intros a w hb h kc bsm (Hfp & Hbsm & Hcs & Hws & Hwm & _) Hw.
split; [unfold lhD_nin, ZSTD_BLOCKSIZE_MAX in *; lia |].
unfold lhD_nout, ring_needed. destruct (c3_stable kc); [lia|]. cbv zeta.
unfold ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia.
Qed.

Section Pieces.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the context's fields piece D does not touch (all but fParams, maxBlockSizeParam, cgroup3, sgroup) *)
Definition ff_rest (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
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

Definition ctx_oth (gv: globals) (p: val) (k: cst3) : mpred :=
  dctx_token p * dctx_pad p * cfg_fmt p (dp_fmt (c3_par k)) * cfg_lit p * ff_rest p (c3_fs k) *
  tabs_rep TABS gv p (c3_tabs k) *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore (c3_par k)))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par k)))) p *
  field_at Ews t_dctx (DOT _ddictSet) (c3_sp k) p *
  dgroup DENT gv p (c3_dict k) * hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)).

Lemma ctx_rep3_D : forall gv p k, ctx_rep3 DENT TABS gv p k =
  !! (cold01 (c3_fs k) /\ par_ok (c3_par k)) &&
  (field_at Ews t_dctx (DOT _fParams) (fs_fParams (c3_fs k)) p *
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par k)))) p *
   cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) * sgroup p (c3_s k) * ctx_oth gv p k).
Proof.
intros. unfold ctx_rep3, ctx_body3, fgroup3, frame_fields, ctx_oth, ff_rest.
apply pred_ext; Intros; entailer!.
Qed.

Lemma ctx_oth_fp : forall gv p k v, ctx_oth gv p (c3_with_fs k (fsu_fParams (c3_fs k) v) (c3_tabs k)) = ctx_oth gv p k.
Proof. reflexivity. Qed.

(* the stream fields piece D changes keep the allocator and its other blocks, which the set's representation sees *)
Lemma ctx_oth_s : forall gv p k s, sf_mem s = sf_mem (c3_s k) -> sf_held s = sf_held (c3_s k) ->
  ctx_oth gv p (c3_with_s k s) = ctx_oth gv p k.
Proof. intros gv p k s Hm Hh. unfold ctx_oth; cbn [c3_with_s c3_s c3_sp c3_set c3_dict c3_par c3_fs c3_tabs]. rewrite Hm, Hh. reflexivity. Qed.

Definition lhD_postg (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3) (bsm: Z) : ret_assert :=
  {| RA_normal := EX s3: sfields,
       PROPx [lhD_facts (c3_stable kc) (c3_s kc) s3 h bsm; lhD_xg kc h bsm s3]
       (LOCALx (ds_LI_L a (lw_k w (c3_with_s kc s3)))
       (SEPx (ds_LI_S DENT TABS a (lw_k w (c3_with_s kc s3)))));
     RA_break := FF;
     RA_continue := FF;
     RA_return := lh_ret_x DENT TABS a w hb |}.

Definition lhD_mid1 (a: dsa) (w: lw) (h: frame_header) (kc: cst3) (bsm: Z) : environ -> mpred :=
  PROPx []
  (LOCALx (temp _neededOutBuffSize (Vlong (Int64.repr (lhD_nout kc h bsm))) ::
           temp _neededInBuffSize (Vlong (Int64.repr (lhD_nin bsm))) :: ds_LI_L a (lw_k w kc))
  (SEPx (ds_LI_S DENT TABS a (lw_k w kc)))).

Definition lhD_mid2 (a: dsa) (w: lw) (h: frame_header) (kc: cst3) (bsm: Z) : environ -> mpred :=
  PROPx [0 <= sf_over (c3_s kc)]
  (LOCALx (temp _t'50 (Vint (Int.repr (if orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) then 1 else 0))) ::
           temp _neededInBuffSize (Vlong (Int64.repr (lhD_nin bsm))) ::
           temp _neededOutBuffSize (Vlong (Int64.repr (lhD_nout kc h bsm))) :: ds_LI_L a (lw_k w (lhD_k2 kc h bsm)))
  (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_k2 kc h bsm))))).

(* after free(inBuff), inBuffSize = outBuffSize = 0, inBuff = q = calloc(nin + nout): the allocator has given out
   the context, its other blocks and (q not NULL) the new buffer *)
Definition lhD_cut3 (a: dsa) (w: lw) (h: frame_header) (kc: cst3) (bsm: Z) (q: val) : environ -> mpred :=
  let s := c3_s kc in
  let n := lhD_nin bsm + lhD_nout kc h bsm in
  PROPx [cold01 (c3_fs kc) /\ par_ok (c3_par kc); Int.min_signed <= sf_nfp s <= Int.max_signed; Int.min_signed <= sf_stage s <= Int.max_signed;
         Zlength (sf_hbuf s) = 18; 0 <= sf_held s; cmem_ok (sf_mem s);
         0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\ 0 <= sf_over s]
  (LOCALx (temp _neededInBuffSize (Vlong (Int64.repr (lhD_nin bsm))) ::
           temp _neededOutBuffSize (Vlong (Int64.repr (lhD_nout kc h bsm))) :: ds_LI_L a (lw_k w kc))
  (SEPx [if eq_dec q nullval then emp
         else blk_tok (sf_mem s) (tarray tuchar n) q * data_at Ews (tarray tuchar n) (Zrepeat (Vint Int.zero) n) q;
         cm_have (sf_mem s) (dctx_size + sf_held s + (if eq_dec q nullval then 0 else n));
         field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem s)) (a_d a);
         blk_tok (sf_mem s) (tarray tuchar (sizeof t_dctx)) (a_d a);
         data_at Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
         zstd_globals (a_gv a); ctx_oth (a_gv a) (a_d a) kc;
         field_at Ews t_dctx (DOT _fParams) (fs_fParams (c3_fs kc)) (a_d a);
         field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par kc)))) (a_d a);
         cgroup3 (a_d a) (c3_stable kc) (dp_wmax (c3_par kc));
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) (a_d a);
         field_at Ews t_dctx (DOT _inBuff) q (a_d a);
         field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr 0)) (a_d a);
         field_at Ews t_dctx (DOT _inPos) (sf_inPos s) (a_d a);
         field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) (a_d a);
         field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr 0)) (a_d a);
         field_at Ews t_dctx (DOT _outStart) (sf_outStart s) (a_d a);
         field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) (a_d a);
         field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) (a_d a);
         field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) (a_d a);
         field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) (a_d a);
         field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) (a_d a);
         field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) (a_d a);
         field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (lhD_ov kc h bsm))) (a_d a);
         dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
         set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
         data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong (a_opos a))) (a_outp a);
         data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong (a_ipos a))) (a_inp a);
         data_at (a_shob a) (tarray tuchar (a_osz a)) (w_oc w) (a_ob a);
         data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)])).

End Pieces.

(* the statements at the cuts *)
Definition lhD_c0 : statement := ltac:(
  let t := eval cbv delta [lh_D] in lh_D in let r := lh_drop 1%nat t in exact r).
Definition lhD_c1 : statement := ltac:(
  let t := eval cbv delta [lh_D] in lh_D in let r := lh_drop 3%nat t in exact r).
Definition lhD_c2 : statement := ltac:(
  let t := eval cbv delta [lh_D] in lh_D in let r := lh_drop 6%nat t in
  lazymatch r with Ssequence (Ssequence _ ?y) ?z => exact (Ssequence y z) end).
Definition lhD_c4 : statement := ltac:(
  let t := eval cbv delta [lhD_c2] in lhD_c2 in
  lazymatch t with Ssequence (Sifthenelse _ ?x _) ?z => exact (Ssequence x z) end).
Definition lhD_c5 : statement := ltac:(
  let t := eval cbv delta [lhD_c4] in lhD_c4 in
  lazymatch t with Ssequence ?c1 ?z =>
  lazymatch c1 with context [Ssequence (Ssequence (Sset _t'107 _) (Sifthenelse _ _ ?B)) ?TAIL] =>
  lazymatch B with context [Sloop (Ssequence (Sset _t'108 ?e) ?r) Sbreak] =>
    exact (Ssequence (Sloop (Ssequence (Sset _t'108 e) r) Sbreak) (Ssequence TAIL z)) end end end).

(* P5: the NULL check (RC_mem return), the new sizes, streamStage = zdss_read *)
Lemma lhD_p5 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3)
  (bsm: Z) (q: val),
  lhD_pre a w hb h kc bsm -> orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) = true ->
  semax (ds_Delta DENT TABS BR) (lhD_cut3 DENT TABS a w h kc bsm q) lhD_c5 (lhD_postg DENT TABS a w hb h kc bsm).
Proof.
intros Espec DENT TABS BR a w hb h kc bsm q Hpre E.
unfold lhD_cut3, lhD_postg, ds_Delta. simplify_func_tycontext. unfold lhD_c5. abbreviate_semax.
unfold ds_LI_L. Intros.
destruct Hpre as (Hfp & Hbsm & Hcs & Hws & Hwm & Hrc & Hroom).
pose proof H0 as (_ & _ & _ & Hwmax & _).
set (s := c3_s kc) in *.
set (nin := lhD_nin bsm) in *.
set (nout := lhD_nout kc h bsm) in *.
set (ov := lhD_ov kc h bsm) in *.
assert (Hnin: 4 <= nin <= ZSTD_BLOCKSIZE_MAX) by (unfold nin, lhD_nin, ZSTD_BLOCKSIZE_MAX in *; lia).
assert (Hnout: 0 <= nout <= 2 ^ 31 + 2 ^ 19).
{ unfold nout, lhD_nout, ring_needed. destruct (c3_stable kc); [lia|]. cbv zeta.
  unfold ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
assert (Hov: 0 <= ov <= Int64.max_unsigned).
{ unfold ov, lhD_ov. destruct (is_overflow _ _ _ _); [| rep_lia].
  match goal with |- context [?x mod 2 ^ 64] => pose proof (Z.mod_pos_bound x (2 ^ 64)) end. rep_lia. }
pose proof byte_cells_nil as Hbn. pose proof (byte_cells_zeros (nin + nout)) as Hbz.
destruct (eq_dec q nullval) as [Hq|Hq].
{
  apply (semax_loopbrk_seq _ _ FF); [reflexivity | reflexivity | | apply semax_ff].
  forward. forward_if.
  2: { exfalso. subst q. auto. }
  dw0.
  unfold MORE_COMMANDS, abbreviate; clear MORE_COMMANDS.
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    apply (semax_loopbrk_seq _ P P); [reflexivity | reflexivity | | ] end.
  { forward_if.
    { exfalso. lia. }
    forward. apply ENTAIL_refl. }
  dw0. dw0.
  apply semax_return_v with (v := Vlong (Int64.repr (err_code ZSTD_error_memory_allocation))).
  { entailer!. }
  { ret_err_val. }
  unfold POSTCONDITION, abbreviate. cbn [RA_return loop1_ret_assert overridePost].
  clear POSTCONDITION.
  unfold lh_ret_x. Exists (err_code ZSTD_error_memory_allocation) (a_ipos a)
    (lw_k w (c3_with_s kc (sf_lhD s (sf_stage s) nullval 0 (sf_outBuff s) 0 ov nil))).
  unfold ds_S_ip, ds_LI_L. rewrite ctx_rep3_D. unfold sgroup, mgroup, sf_given.
  cbn [lw_k w_k w_ipc w_smw w_opc w_oc c3_with_s c3_fs c3_s c3_par c3_stable sf_lhD sf_stage sf_inBuff sf_inSize
       sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over
       sf_ring sf_mem sf_held] in *.
  subst q. unfold ring_rep. rewrite !if_true by auto. rewrite !Z.add_0_r.
  go_lower. rewrite ctx_oth_s by reflexivity.
  apply andp_right; [apply prop_right | ].
  { split; [reflexivity |]. split; [unfold err_code, ZSTD_error_memory_allocation; rep_lia |].
    split; [| split; [intros _; left; intros _; left; reflexivity |]; rewrite eqb_type_refl; repeat split; auto].
    apply Hrc. unfold lhD_memfail; cbn [sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
      sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
    repeat split; auto. }
  rewrite (prop_true_andp (0 + 0 = 0)) by lia.
  rewrite (prop_true_andp (cold01 _ /\ _)) by auto.
  rewrite prop_true_andp by (repeat split; try rep_lia; auto; intros X; contradiction X; auto).
  rewrite !sepcon_emp. rewrite (prop_true_andp (cmem_ok _)) by auto. cancel. }
Intros. assert_PROP (isptr q) as Hqp by entailer!.
match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
  apply (semax_loopbrk_seq _ _ (PROPx Pr (LOCALx (temp _t'108 q :: L) (SEPx S)))); [reflexivity | reflexivity | | ] end.
{ forward. forward_if.
  { contradiction. }
  forward. apply ENTAIL_refl. }
unfold MORE_COMMANDS, abbreviate; clear MORE_COMMANDS.
forward. forward. forward. forward. forward. forward.
Exists (sf_lhD s zdss_read q nin (offset_val nin q) nout ov (Zrepeat (Vint Int.zero) (nin + nout))).
unfold ds_LI_S, ds_LI_L. rewrite ctx_rep3_D. unfold sgroup, mgroup, sf_given.
cbn [lw_k w_k w_ipc w_smw w_opc w_oc c3_with_s c3_fs c3_s c3_par c3_stable sf_lhD sf_stage sf_inBuff sf_inSize
     sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over
     sf_ring sf_mem sf_held] in *.
unfold ring_rep. rewrite !if_false by auto. rewrite Z.add_assoc.
replace (force_val (sem_add_ptr_long tschar q (Vlong (Int64.repr nin)))) with (offset_val nin q).
2: { destruct q; try contradiction. unfold sem_add_ptr_long; simpl. f_equal. f_equal.
     rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
     rewrite Int64.unsigned_repr by (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia). reflexivity. }
go_lower. rewrite ctx_oth_s by reflexivity.
apply andp_right; [apply prop_right | ].
{ split; [unfold lhD_facts; cbn [sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
    sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held];
    repeat split; auto; [unfold nin, lhD_nin; lia | unfold ZSTD_BLOCKSIZE_MAX in *; lia |
                                  intros Hs; unfold nout, lhD_nout; rewrite Hs; lia] |].
  split.
  { unfold lhD_xg. fold s nin nout ov. rewrite E.
    cbn [sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
      sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
    repeat split; try lia. rewrite sublist_Zrepeat by lia. f_equal; lia. }
  rewrite eqb_type_refl; repeat split; auto. }
assert (HZ: Zlength (Zrepeat (Vint Int.zero) (nin + nout)) = nin + nout) by (apply Zlength_Zrepeat; lia).
rewrite (prop_true_andp _ _ HZ).
rewrite (prop_true_andp (cold01 _ /\ _)) by auto.
rewrite prop_true_andp by (unfold zdss_read; repeat split; try rep_lia; auto; unfold ZSTD_BLOCKSIZE_MAX in *; lia).
rewrite (prop_true_andp (cmem_ok _)) by auto.
cancel.
Qed.

(* P4: the then branch of if (tooSmall || tooLarge) up to zds->inBuff = calloc(..) (then P5) *)
Lemma lhD_p4 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3)
  (bsm: Z),
  lhD_pre a w hb h kc bsm -> orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) = true ->
  (forall q, semax (ds_Delta DENT TABS BR) (lhD_cut3 DENT TABS a w h kc bsm q) lhD_c5
               (lhD_postg DENT TABS a w hb h kc bsm)) ->
  semax (ds_Delta DENT TABS BR) (lhD_mid2 DENT TABS a w h kc bsm) lhD_c4 (lhD_postg DENT TABS a w hb h kc bsm).
Proof.
intros Espec DENT TABS BR a w hb h kc bsm Hpre E P5.
unfold lhD_mid2, lhD_postg, ds_Delta. simplify_func_tycontext. unfold lhD_c4. abbreviate_semax.
unfold ds_LI_S, ds_LI_L, lhD_k2. cbn [lw_k w_k w_smw w_ipc w_opc w_oc] in *.
rewrite ctx_rep3_D. rewrite ctx_oth_s by reflexivity. unfold sgroup, mgroup, sf_given. Intros.
cbn [c3_s c3_with_s c3_fs c3_par c3_stable sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd
       sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held] in *.
destruct Hpre as (Hfp & Hbsm & Hfcs & Hws & Hwm & _ & Hroom).
assert (Hwmax: dp_wmax (c3_par kc) <= 2 ^ 31)
  by (match goal with Hp: _ /\ par_ok _ |- _ => destruct Hp as [_ (_ & _ & _ & ? & _)]; lia
                  | Hp: par_ok _ |- _ => destruct Hp as (_ & _ & _ & ? & _); lia end).
set (s := c3_s kc) in *.
set (nin := lhD_nin bsm) in *.
set (nout := lhD_nout kc h bsm) in *.
assert (Hnin: 4 <= nin <= ZSTD_BLOCKSIZE_MAX) by (unfold nin, lhD_nin, ZSTD_BLOCKSIZE_MAX in *; lia).
assert (Hnout: 0 <= nout <= 2 ^ 31 + 2 ^ 20).
{ unfold nout, lhD_nout, ring_needed. destruct (c3_stable kc); [lia|].
  unfold ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
forward.
rewrite add64_repr.
dw0. dw0.
unfold cgroup3. Intros.
forward.
apply semax_if_seq. forward_if.
{ exfalso. match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end. }
assert_PROP (is_pointer_or_null (sf_inBuff s) /\ (sf_inBuff s = nullval -> sf_inSize s + sf_outSize s = 0))
  as Hpn0.
{ unfold ring_rep. destruct (eq_dec (sf_inBuff s) nullval) as [Hn|Hn].
  - Intros. rewrite Hn. entailer!.
  - Intros. entailer!. }
destruct Hpn0 as [Hpn Hn0].
(* the bytes the allocator holds once the old buffer is given back *)
set (hs := dctx_size + sf_held s + sf_inSize s + sf_outSize s).
assert (Hgv: (if eq_dec (sf_inBuff s) nullval then hs
              else hs - sizeof (tarray tuchar (sf_inSize s + sf_outSize s))) = dctx_size + sf_held s).
{ unfold hs. destruct (eq_dec (sf_inBuff s) nullval) as [Hn|Hn].
  - specialize (Hn0 Hn). lia.
  - rewrite sizeof_tuchar_arr by lia. lia. }
forward.
sep_apply (ring_rep_free (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s)).
assert_PROP (field_compatible t_dctx (DOT _customMem) (a_d a)) as Hfc by entailer!.
rewrite cmem_fa.
forward_call (a_gv a, tarray tuchar (sf_inSize s + sf_outSize s), sf_inBuff s, Ews,
  field_address t_dctx (DOT _customMem) (a_d a), sf_mem s, hs).
{ rewrite sizeof_tuchar_arr by lia. split.
  - intros _. unfold cm_held. destruct (sf_mem s); [| exact I]. rewrite sizeof_tuchar_arr by lia.
    unfold hs. rewrite dctx_size_eq. lia.
  - intros Hn _. auto. }
rewrite Hgv.
forward. forward.
forward_call (a_gv a, nin + nout, Ews, field_address t_dctx (DOT _customMem) (a_d a), sf_mem s, dctx_size + sf_held s).
{ unfold ZSTD_BLOCKSIZE_MAX in Hnin; rep_lia. }
Intros q.
forward.
eapply semax_pre; [| apply (P5 q)].
unfold lhD_cut3, ds_LI_L. cbn [lw_k w_k w_smw w_ipc w_opc w_oc]. fold s. fold nin. fold nout.
rewrite <- cmem_fa.
destruct (eq_dec q nullval) as [Hq|Hq]; [rewrite Z.add_0_r |].
all: go_lower; change (Int.signed (Int.repr 0)) with 0.
all: apply andp_right; [apply prop_right; split; [split; assumption |]; repeat split; auto; rep_lia | unfold cgroup3; cancel].
Qed.

(* P3: if (tooSmall || tooLarge): the then branch is P4, the else branch keeps the buffer; streamStage = zdss_read *)
Lemma lhD_p3 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3)
  (bsm: Z),
  lhD_pre a w hb h kc bsm ->
  (orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) = true ->
   semax (ds_Delta DENT TABS BR) (lhD_mid2 DENT TABS a w h kc bsm) lhD_c4 (lhD_postg DENT TABS a w hb h kc bsm)) ->
  semax (ds_Delta DENT TABS BR) (lhD_mid2 DENT TABS a w h kc bsm) lhD_c2 (lhD_postg DENT TABS a w hb h kc bsm).
Proof.
intros Espec DENT TABS BR a w hb h kc bsm Hpre P4.
unfold lhD_mid2, lhD_postg, ds_Delta. simplify_func_tycontext. unfold lhD_c2. abbreviate_semax.
unfold ds_LI_L.
apply semax_if_seq. forward_if.
{ assert (E: orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) = true) by (apply stab_ne0; auto).
  eapply semax_pre; [| apply (P4 E)]. unfold lhD_mid2. apply andp_left2.
  apply andp_right; [apply prop_right; split; [assumption | exact I] |]. unfold PROPx. apply andp_left2.
  apply derives_refl. }
assert (E: orb (lhD_ts kc h bsm) (lhD_tl kc h bsm) = false) by (apply stab_eq0; auto).
pose proof E as E0.
clear P4.
unfold ds_LI_S. rewrite ctx_rep3_D. unfold lw_k. cbn [w_k w_ipc w_smw w_opc w_oc]. unfold lhD_k2. cbv zeta.
rewrite ctx_oth_s by reflexivity. unfold sgroup, mgroup, sf_given.
cbn [c3_with_s c3_s c3_fs c3_par c3_stable sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
     sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
Intros.
unfold lhD_ts, lhD_tl in E. apply orb_false_elim in E as [Ets Etl]. apply orb_false_elim in Ets as [E1 E2].
apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
set (s := c3_s kc) in *.
assert (Hnin: 4 <= lhD_nin bsm) by (unfold lhD_nin; lia).
assert_PROP (sf_inBuff s <> nullval /\ isptr (sf_inBuff s)) as Hnnp.
{ unfold ring_rep. destruct (eq_dec (sf_inBuff s) nullval).
  - Intros. lia.
  - Intros. entailer!. }
destruct Hnnp as [Hnn Hip].
forward.
Exists (sf_lhD s zdss_read (sf_inBuff s) (sf_inSize s) (sf_outBuff s) (sf_outSize s) (lhD_ov kc h bsm) (sf_ring s)).
unfold ds_LI_L. rewrite ctx_rep3_D, ctx_oth_s by reflexivity. unfold sgroup, mgroup, sf_given.
cbn [w_k w_ipc w_smw w_opc w_oc c3_with_s c3_s c3_fs c3_par c3_stable sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos
     sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
assert (Hf: lhD_facts (c3_stable kc) s
  (sf_lhD s zdss_read (sf_inBuff s) (sf_inSize s) (sf_outBuff s) (sf_outSize s) (lhD_ov kc h bsm) (sf_ring s)) h bsm).
{ unfold lhD_facts; cbn [sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
    sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
  unfold lhD_nin in E1. repeat split; auto; try lia.
  intros Hs. unfold lhD_nout in E2. rewrite Hs in E2. lia. }
rewrite (prop_true_andp (cold01 (c3_fs kc) /\ par_ok (c3_par kc))) by auto.
rewrite (prop_true_andp (0 <= sf_inSize s /\ _)) by (unfold zdss_read; repeat split; auto; rep_lia).
rewrite (prop_true_andp (cmem_ok _)) by auto.
go_lower. apply andp_right; [apply prop_right | cancel].
split; [exact Hf |].
split.
{ assert (Hw: dp_wmax (c3_par kc) <= 2 ^ 31)
    by (match goal with Hp: _ /\ par_ok _ |- _ => destruct Hp as [_ (_ & _ & _ & ? & _)]; lia
                    | Hp: par_ok _ |- _ => destruct Hp as (_ & _ & _ & ? & _); lia end).
  destruct (lhD_pre_bnds _ _ _ _ _ _ Hpre Hw) as [Hb1 Hb2].
  unfold lhD_xg; cbv zeta; rewrite E0; fold s.
  cbn [sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart
    sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
  repeat split; auto; lia. }
rewrite eqb_type_refl. repeat split; auto.
Qed.

(* P2: updateOversizedDuration, tooSmall, tooLarge (isOversizedTooLong), the condition t'50 (then P3) *)
Lemma lhD_p2 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3)
  (bsm: Z),
  lhD_pre a w hb h kc bsm ->
  semax (ds_Delta DENT TABS BR) (lhD_mid2 DENT TABS a w h kc bsm) lhD_c2 (lhD_postg DENT TABS a w hb h kc bsm) ->
  semax (ds_Delta DENT TABS BR) (lhD_mid1 DENT TABS a w h kc bsm) lhD_c1 (lhD_postg DENT TABS a w hb h kc bsm).
Proof.
intros Espec DENT TABS BR a w hb h kc bsm Hpre K.
destruct Hpre as (Hfp & Hb & Hfcs & Hws & Hwm & _).
unfold lhD_mid1, lhD_postg, ds_Delta. simplify_func_tycontext. unfold lhD_c1. abbreviate_semax.
unfold ds_LI_S, ds_LI_L. cbn [lw_k w_k w_smw w_ipc w_opc w_oc]. rewrite ctx_rep3_D. unfold sgroup, mgroup, sf_given, cgroup3.
Intros.
set (s := c3_s kc) in *.
set (nin := lhD_nin bsm) in *.
set (nout := lhD_nout kc h bsm) in *.
assert (Hnin: 4 <= nin <= ZSTD_BLOCKSIZE_MAX) by (unfold nin, lhD_nin, ZSTD_BLOCKSIZE_MAX in *; lia).
assert (Hnout: 0 <= nout <= Int64.max_unsigned).
{ unfold nout, lhD_nout, ring_needed. destruct (c3_stable kc); [rep_lia|].
  unfold ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *. lia. }
assert (Hnin': 0 <= nin <= Int64.max_unsigned) by (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
forward_call (a_d a, sf_inSize s, sf_outSize s, nin, nout, sf_over s).
set (ov' := if is_overflow (sf_inSize s) (sf_outSize s) nin nout then (sf_over s + 1) mod 2 ^ 64 else 0).
forward.
forward_if (temp _t'47 (Vint (Int.repr (if orb (sf_inSize s <? nin) (sf_outSize s <? nout) then 1 else 0)))).
{ assert (E: (sf_inSize s <? nin) = true) by (apply Z.ltb_lt; auto).
  forward. entailer!. rewrite E. reflexivity. }
{ assert (E: (sf_inSize s <? nin) = false) by (apply Z.ltb_ge; lia).
  forward. forward. entailer!. rewrite E. simpl orb.
  destruct (Z.ltb_spec (sf_outSize s) nout); destruct (zlt (sf_outSize s) nout); try lia; reflexivity. }
forward.
set (ts := orb (sf_inSize s <? nin) (sf_outSize s <? nout)).
assert (Hov: 0 <= ov' <= Int64.max_unsigned).
{ unfold ov'. destruct (is_overflow _ _ _ _); [pose proof (Z.mod_pos_bound (sf_over s + 1) (2 ^ 64)); rep_lia | rep_lia]. }
forward_call (a_d a, ov').
set (tl := ZSTD_WORKSPACETOOLARGE_MAXDURATION <=? ov').
forward_if (temp _t'50 (Vint (Int.repr (if orb ts tl then 1 else 0)))).
{ assert (E: ts = true) by (apply stab_ne0; auto).
  forward. entailer!. rewrite E. reflexivity. }
{ assert (E: ts = false) by (apply stab_eq0; auto).
  forward. entailer!. rewrite E. simpl orb. destruct tl; reflexivity. }
eapply semax_pre; [| exact K].
unfold lhD_mid2, ds_LI_S, ds_LI_L. cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
rewrite ctx_rep3_D. unfold lhD_k2. rewrite ctx_oth_s by reflexivity. unfold sgroup, mgroup, sf_given, cgroup3.
cbn [c3_with_s c3_fs c3_par c3_stable c3_s sf_lhD sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
     sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
fold s. fold nin nout. change (lhD_ts kc h bsm) with ts.
assert (Eov: lhD_ov kc h bsm = ov') by reflexivity. rewrite Eov.
change (lhD_tl kc h bsm) with tl. unfold vlong.
go_lower.
apply andp_right; [apply prop_right; repeat split; auto; rep_lia |].
rewrite (prop_true_andp (cold01 _ /\ par_ok _)) by auto.
rewrite (prop_true_andp (cmem_ok _)) by auto.
cancel. apply andp_right; [apply prop_right; repeat split; auto; rep_lia | cancel].
Qed.

(* P1: neededInBuffSize = MAX(blockSizeMax, 4), neededOutBuffSize (then P2) *)
Lemma lhD_p1 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (kc: cst3)
  (bsm: Z),
  lhD_pre a w hb h kc bsm ->
  semax (ds_Delta DENT TABS BR) (lhD_mid1 DENT TABS a w h kc bsm) lhD_c1 (lhD_postg DENT TABS a w hb h kc bsm) ->
  semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a (lw_k w kc)) lhD_c0 (lhD_postg DENT TABS a w hb h kc bsm).
Proof.
intros Espec DENT TABS BR a w hb h kc bsm Hpre K.
destruct Hpre as (Hfp & Hb & Hfcs & Hws & Hwm & _).
unfold lh_st, lhD_postg, ds_Delta. simplify_func_tycontext. unfold lhD_c0. abbreviate_semax.
unfold ds_LI_S, ds_LI_L. cbn [lw_k w_k w_smw w_ipc w_opc w_oc]. rewrite ctx_rep3_D. unfold cgroup3. rewrite Hfp.
Intros.
assert (Hwm2: dp_wmax (c3_par kc) <= 2 ^ 31) by (match goal with H: par_ok _ |- _ => destruct H as (_ & _ & _ & ? & _); lia
               | H: _ /\ par_ok _ |- _ => destruct H as [_ (_ & _ & _ & ? & _)]; lia end).
forward.
match goal with |- context [temp _t'117 ?v] => change v with (Vint (Int.repr bsm)) end.
assert (Hb4: Int.unsigned (Int.repr bsm) = bsm)
  by (apply Int.unsigned_repr; unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
forward_if (temp _t'44 (Vint (Int.repr (Z.max bsm 4)))).
{ forward.
  match goal with |- context [temp _t'118 ?v] => change v with (Vint (Int.repr bsm)) end.
  forward. entailer!. try rewrite Hb4 in *. rewrite Z.max_l by lia. auto. }
{ forward. entailer!. try rewrite Hb4 in *. rewrite Z.max_r by lia. auto. }
forward.
rewrite (Int.unsigned_repr (Z.max bsm 4)) by (unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
forward.
forward_if (temp _t'45 (Vlong (Int64.repr (if c3_stable kc then 0 else ring_needed h bsm)))).
{ assert (Es: c3_stable kc = false) by (apply stab_eq0; auto).
  forward. forward. forward.
  match goal with |- context [temp _t'114 ?v] =>
    change v with (Vlong (Int64.repr (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN))) end.
  match goal with |- context [temp _t'115 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
  match goal with |- context [temp _t'116 ?v] => change v with (Vint (Int.repr bsm)) end.
  forward_call (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN, fh_contentSize h, bsm).
  forward. entailer!. rewrite Es. auto. }
{ assert (Es: c3_stable kc = true) by (apply stab_ne0; auto).
  forward. entailer!. rewrite Es; auto. }
forward.
eapply semax_pre; [| exact K].
unfold lhD_mid1, ds_LI_S, ds_LI_L, lhD_nout, lhD_nin. cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
rewrite ctx_rep3_D. unfold cgroup3. rewrite Hfp.
entailer!.
Qed.

Definition lhD_cap : statement := ltac:(
  let t := eval cbv delta [lh_D] in lh_D in let r := lh_take 1%nat t in exact r).

Ltac cap_close Hcold Hpar :=
  unfold ds_LI_S, ds_LI_L; cbn [lw_k w_k w_smw w_ipc w_opc w_oc]; rewrite ctx_rep3_D; unfold lhD_kc;
  rewrite ctx_oth_fp;
  rewrite (prop_true_andp (cold01 _ /\ par_ok _)) by (split; [exact Hcold | exact Hpar]);
  cbn [c3_with_fs c3_fs c3_par c3_stable c3_s fsu_fParams fs_fParams];
  try entailer!.

Lemma lhD_cap_ok : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (h: frame_header) (k3: cst3) R,
  fs_fParams (c3_fs k3) = fh_val (fh_adj h (fh_blockSizeMax h)) -> 0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX ->
  (par_ok (c3_par k3) -> semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a (lw_k w (lhD_kc k3 h))) lhD_c0 R) ->
  semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a (lw_k w k3)) lh_D R.
Proof.
intros Espec DENT TABS BR a w h k3 R Hfp Hb K.
unfold lh_st. unfold ds_LI_S at 1, ds_LI_L at 1. cbn [lw_k w_k w_smw w_ipc w_opc w_oc]. rewrite ctx_rep3_D. Intros.
assert (Hpar: par_ok (c3_par k3))
  by (match goal with H: par_ok _ |- _ => exact H | H: _ /\ par_ok _ |- _ => exact (proj2 H) end).
assert (Hcold: cold01 (c3_fs k3))
  by (match goal with H: cold01 _ |- _ => exact H | H: cold01 _ /\ _ |- _ => exact (proj1 H) end).
specialize (K Hpar).
assert (Hbm: dp_bmax (c3_par k3) = 0 \/ 1024 <= dp_bmax (c3_par k3) <= ZSTD_BLOCKSIZE_MAX)
  by (destruct Hpar as (_ & _ & Hbm & _); exact Hbm).
assert (Hu1: Int.unsigned (Int.repr (fh_blockSizeMax h)) = fh_blockSizeMax h)
  by (apply Int.unsigned_repr; unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
assert (Hu2: Int.unsigned (Int.repr (dp_bmax (c3_par k3))) = dp_bmax (c3_par k3))
  by (apply Int.unsigned_repr; unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
destruct R as [Rn Rb Rc Rr].
replace lh_D with (Ssequence lhD_cap lhD_c0) by reflexivity.
unfold ds_Delta. simplify_func_tycontext. unfold lhD_cap. abbreviate_semax.
rewrite Hfp.
forward.
forward_if (PROPx [] (LOCALx (ds_LI_L a (lw_k w (lhD_kc k3 h))) (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_kc k3 h)))))).
{ assert (Hl: lh_bsm k3 h = Z.min (fh_blockSizeMax h) (dp_bmax (c3_par k3))).
  { unfold lh_bsm, dmode_of; cbn [md_bmax]. destruct (dp_bmax (c3_par k3) =? 0) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E. rewrite E in *. contradiction. }
  forward.
  match goal with |- context [temp _t'120 ?v] => change v with (Vint (Int.repr (fh_blockSizeMax h))) end.
  forward.
  forward_if (temp _t'43 (Vint (Int.repr (Z.min (fh_blockSizeMax h) (dp_bmax (c3_par k3)))))).
  { forward.
    match goal with |- context [temp _t'123 ?v] => change v with (Vint (Int.repr (fh_blockSizeMax h))) end.
    forward. entailer!. rewrite Z.min_l by lia. reflexivity. }
  { forward. forward. entailer!. rewrite Z.min_r by lia. reflexivity. }
  forward.
  match goal with |- context [field_at Ews t_dctx (DOT _fParams) ?v] =>
    change v with (fh_val (fh_adj h (Z.min (fh_blockSizeMax h) (dp_bmax (c3_par k3))))) end.
  rewrite <- Hl.
  cap_close Hcold Hpar. }
{ assert (Hl: lh_bsm k3 h = fh_blockSizeMax h).
  { unfold lh_bsm, dmode_of; cbn [md_bmax]. destruct (dp_bmax (c3_par k3) =? 0) eqn:E.
    - unfold ZSTD_BLOCKSIZE_MAX in *; lia.
    - apply Z.eqb_neq in E. lia. }
  forward.
  cap_close Hcold Hpar. rewrite Hl. entailer!. }
exact K.
Qed.

(* the size_t arithmetic of lhD_xg read as the model's: the sums are far below 2^64 *)
Lemma lhD_xg_x : forall k3 h s3, lhD_xg (lhD_kc k3 h) h (lh_bsm k3 h) s3 ->
  lhD_x (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h).
Proof.
intros k3 h s3 Hx Hst Hov.
unfold lhD_xg, lhD_ts, lhD_tl, lhD_ov, lhD_nout, lhD_nin in Hx.
change (c3_s (lhD_kc k3 h)) with (c3_s k3) in Hx. change (c3_stable (lhD_kc k3 h)) with (c3_stable k3) in Hx.
rewrite Hst in Hx. cbv zeta in Hx.
set (s := c3_s k3) in *. set (nout := ring_needed h (lh_bsm k3 h)) in *. set (nin := Z.max (lh_bsm k3 h) 4) in *.
destruct Hx as (H1 & H2 & H3 & H4 & H5 & H6 & Hov' & Hc).
assert (Eo: is_overflow (sf_inSize s) (sf_outSize s) nin nout =
            (sf_inSize s + sf_outSize s >=? (nin + nout) * ExStream.ZS_WORKSPACETOOLARGE_FACTOR)).
{ unfold is_overflow, ZSTD_WORKSPACETOOLARGE_FACTOR, ExStream.ZS_WORKSPACETOOLARGE_FACTOR.
  rewrite !Z.mod_small by (unfold ZSTD_BLOCKSIZE_MAX in *; lia). rewrite Z.geb_leb. reflexivity. }
rewrite Eo in Hov', Hc.
assert (Em: (sf_over s + 1) mod 2 ^ 64 = sf_over s + 1) by (apply Z.mod_small; rep_lia).
rewrite Em in Hov', Hc.
cbv zeta. fold s nin nout.
change ZSTD_WORKSPACETOOLARGE_MAXDURATION with ExStream.ZS_WORKSPACETOOLARGE_MAXDURATION in Hc.
rewrite (Z.geb_leb _ ExStream.ZS_WORKSPACETOOLARGE_MAXDURATION). split; [exact Hov' |].
revert Hc. destruct (_ || _)%bool; intros Hc; [| exact Hc].
destruct Hc as (Hc1 & Hc2 & Hc3). split; [exact Hc1 |]. split; [exact Hc2 |].
rewrite Hc3. unfold ExStream.ring_fresh, Zrepeat. rewrite map_repeat. reflexivity.
Qed.

(* piece D with the exact facts (LH3XDefs.lhD_x_stmt) *)
Lemma lhD_x_okp : lhD_x_stmt.
Proof.
unfold lhD_x_stmt. intros Espec DENT TABS BR a w hb h tbl d1 did1 c HD HT Ha He Hx Hg Hf Hsel HC.
set (k1 := k_A (w_k w) (fh_val h) d1 did1) in *. set (k3 := lhC_k k1 hb h c).
assert (Hfp: fs_fParams (c3_fs k3) = fh_val (fh_adj h (fh_blockSizeMax h))).
{ unfold k3, lhC_k, lhC_fs. cbn [c3_fs]. destruct (fh_frameType h =? 1); reflexivity. }
pose proof Hf as (Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & _).
apply (lhD_cap_ok Espec DENT TABS BR a w h k3); [exact Hfp | lia | intros Hpar].
eapply semax_post with (R' := lhD_postg DENT TABS a w hb h (lhD_kc k3 h) (lh_bsm k3 h)).
1: { unfold lhD_postg, lhD_post_x; cbn [RA_normal]. apply andp_left2. apply exp_left; intros s3. apply (exp_right s3).
     unfold PROPx. apply andp_derives; [| apply derives_refl].
     apply prop_derives. intros (HA & HB & _). split; [exact HA |]. split; [apply lhD_xg_x; exact HB | exact I]. }
1,2: unfold lhD_postg, lhD_post_x; cbn [RA_break RA_continue]; intros; apply andp_left2; apply derives_refl.
1: unfold lhD_postg, lhD_post_x; cbn [RA_return]; intros; apply andp_left2; apply derives_refl.
assert (Hpre: lhD_pre a w hb h (lhD_kc k3 h) (lh_bsm k3 h)).
2: { apply lhD_p1; auto. apply lhD_p2; auto. apply lhD_p3; auto. intros E. apply lhD_p4; auto.
     intros q. apply lhD_p5; auto. }
assert (Hbsm: 0 <= lh_bsm k3 h <= fh_blockSizeMax h).
{ unfold lh_bsm, dmode_of; cbn [md_bmax]. destruct Hpar as (_ & _ & Hbm & _).
  destruct (dp_bmax (c3_par k3) =? 0) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
assert (HW: Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN <= dp_wmax (c3_par k1))
  by (destruct HC as (_ & _ & _ & _ & _ & _ & HW); exact HW).
split; [reflexivity |].
split; [unfold ZSTD_BLOCKSIZE_MAX in *; lia |].
split; [lia |]. split; [lia |]. split; [exact HW |].
split; [intros s' Hm; exact (RC_mem a w hb h tbl d1 did1 c s' Hsel Hg HC Hm) |].
(* the room for the stream buffer: the context entered the call with its allocator's bound raised to the streaming
   estimate of its window limit (mem_call), and the buffer fits in that estimate (CMem.stream_bufs_fit); with other
   blocks given out (a local DDict, a DDict set: sf_held > 0) the bound leaves room for the largest stream buffers
   besides them (FSRep3.mem_room: the estimate of the largest window limit, 2^31) *)
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
destruct Hbc as (_ & Hpe & _ & _ & _ & _ & Hmem & Hroom0 & _).
unfold lhD_room, lhD_nin, lhD_nout. intros Hh0.
change (c3_stable (lhD_kc k3 h)) with (c3_stable (w_k w)).
change (c3_par k1) with (c3_par (w_k w)) in HW.
(* the selection and ZSTD_getDDict kept or freed the local DDict: the allocator holds no more than at the entry *)
assert (Hrd: redict_ok (c3_dict (w_k w)) (snd (getddict_res d1)))
  by (apply (redict_ok_trans _ d1); [exact (lhA_sel_redict _ _ _ _ _ _ _ Hsel) | apply redict_ok_getddict]).
set (s3 := c3_s (lhD_kc k3 h)) in *.
assert (Hs3: s3 = held_redict (held_redict (c3_s (w_k w)) (c3_dict (w_k w)) d1) d1 (snd (getddict_res d1)))
  by reflexivity.
assert (Hroom: mem_room s3).
{ apply (mem_room_le (c3_s (w_k w))); [rewrite Hs3; reflexivity | | exact Hroom0].
  split; [exact Hh0 |]. rewrite Hs3. unfold held_redict, sf_with_held; cbn [sf_held].
  pose proof (local_held_redict_le _ _ Hrd). lia. }
assert (Hm3: sf_mem s3 = sf_mem (c3_s (w_k w))) by (rewrite Hs3; reflexivity).
assert (Hw31: dp_wmax (dc_par (a_st a)) <= 2 ^ 31).
{ rewrite <- Hpe. change (c3_par (w_k w)) with (c3_par k3). destruct Hpar as (_ & _ & _ & Hw & _). lia. }
unfold mem_room in Hroom. rewrite Hm3, Hmem in Hroom |- *. rewrite Hpe in HW.
destruct (dc_mem (a_st a)) as [m|]; [| exact I].
rewrite cm_raise_bound in Hroom |- *. unfold cm_room; cbn [cm_bound] in Hroom |- *.
pose proof (stream_bufs_fit (Z.max (fh_windowSize h) ZSTD_WINDOWSIZE_ABSMIN) (fh_contentSize h) (lh_bsm k3 h)
  (dp_wmax (dc_par (a_st a))) (c3_stable (w_k w))) as Hfit.
unfold ring_needed, ZSTD_WINDOWSIZE_ABSMIN, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX, dstream_size in *.
rewrite dctx_size_eq in *.
specialize (Hfit ltac:(lia) ltac:(lia) ltac:(lia)).
destruct Hroom as [E | E]; destruct (c3_stable (w_k w)); lia.
Qed.

End CM_LH3D_1.
