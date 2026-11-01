(* FS3 streaming, the prologue of ZSTD_decompressStream: the context without the fields
   ZSTD_checkOutBuffer reads. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_P3ProCtx_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the context without the fields ZSTD_checkOutBuffer reads ---------- *)

Definition ctx_rest3 (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) : mpred :=
  let s := c3_s k in
  dctx_token p * dctx_pad p * fgroup3 TABS gv p (c3_fs k) (c3_tabs k) (c3_par k) (c3_sp k) *
  field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
  field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr (dp_wmax (c3_par k)))) p *
  dgroup DENT gv p (c3_dict k) * hset_rep (sf_mem s) (c3_sp k) (c3_set k) (sf_held s - local_held (c3_dict k)) *
  (!! (0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
       Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
       0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
       (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
       (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s)) &&
   (field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
    field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
    field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
    field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
    field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
    field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
    field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
    field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
    field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
    field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
    field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
    field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
    ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
    mgroup (sf_mem s) p (sf_given s))).

Lemma ctx_rep_split : forall DENT TABS gv p k,
  ctx_rep3 DENT TABS gv p k |--
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if c3_stable k then 1 else 0))) p *
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut (c3_s k)) p * ctx_rest3 DENT TABS gv p k.
Proof.
intros. unfold ctx_rep3, ctx_body3, cgroup3, sgroup, ctx_rest3. Intros. entailer!.
Qed.

Lemma ctx_rep_join : forall DENT TABS gv p k,
  field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if c3_stable k then 1 else 0))) p *
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut (c3_s k)) p * ctx_rest3 DENT TABS gv p k |--
  ctx_rep3 DENT TABS gv p k.
Proof.
intros. unfold ctx_rep3, ctx_body3, cgroup3, sgroup, ctx_rest3. Intros. entailer!.
Qed.

End CM_P3ProCtx_1.
