(* FS3-bl SUB: the context split into what ZSTD_decompressContinue_ispec takes and the rest. *)
Require Export Zstd.proof.dec.v3.FS.BL.sub.SubFacts.
Local Open Scope logic.

Section CM_SubCtx_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.



(* ---------- the context ---------- *)

Definition sf_with_hbuf (s: sfields) (hb: list val) : sfields :=
  {| sf_stage := sf_stage s; sf_inBuff := sf_inBuff s; sf_inSize := sf_inSize s; sf_inPos := sf_inPos s;
     sf_outBuff := sf_outBuff s; sf_outSize := sf_outSize s; sf_outStart := sf_outStart s;
     sf_outEnd := sf_outEnd s; sf_lhSize := sf_lhSize s; sf_hostage := sf_hostage s; sf_nfp := sf_nfp s;
     sf_expOut := sf_expOut s; sf_hbuf := hb; sf_over := sf_over s; sf_ring := sf_ring s; sf_mem := sf_mem s; sf_held := sf_held s |}.

(* the context after a call: new frame fields, tables, headerBuffer *)
Definition c3_bl (k: cst3) (fs: fstate) (t: tabs3) (hb: list val) : cst3 :=
  c3_with_s (c3_with_fs k fs t) (sf_with_hbuf (c3_s k) hb).

(* sgroup without headerBuffer *)
Definition sgroup_nohb (p: val) (s: sfields) : mpred :=
  !! (0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
      Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
      0 <= sf_over s <= Int64.max_unsigned /\ byte_cells (sf_ring s) /\
      (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
      (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s)) &&
  (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
   field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
   field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
   field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
   field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
   field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
   field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
   field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
   field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
   field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
   field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
   field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
   field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
   ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
   mgroup (sf_mem s) p (sf_given s)).

Section Ctx.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition ctx_rest3 (gv: globals) (p: val) (k: cst3) : mpred :=
  dctx_token p * dctx_pad p * cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) * dgroup DENT gv p (c3_dict k) *
  sgroup_nohb p (c3_s k) *
  hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)).

Lemma ctx3_split gv p k :
  ctx_rep3 DENT TABS gv p k |--
  !! (cold01 (c3_fs k) /\ Zlength (sf_hbuf (c3_s k)) = 18) &&
  (fcore3 p (c3_fs k) (c3_par k) (c3_sp k) * tabs_rep TABS gv p (c3_tabs k) *
   field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s k)) p * ctx_rest3 gv p k).
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, fcore3, sgroup, ctx_rest3, sgroup_nohb. Intros. entailer!.
Qed.

Lemma hset_nil_null am sp hb : hset_rep am sp nil hb |-- !! (sp = nullval).
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval); [entailer! | Intros tp tbl; tauto].
Qed.

End Ctx.

End CM_SubCtx_1.
