(* FS3 load3: ctx_rep3 split into the fields the loading functions touch and the rest (small VST contexts) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_Load3Split_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* everything of ctx_rep3 but the stream stage, the dictionary group, the customMem field, the allocator's state
   (cm_have), refMultipleDDicts, ddictSet, format and the set (the rest of the allocator's group FSRepC.mgroup stays
   here); it does not see the bytes held for the local DDict and the set (sf_held) *)
Definition ctx_rest3 (TABS: tabs_pred) (gv: globals) (p: val) (fs: fstate) (t: tabs3) (stable: bool)
    (s: sfields) (pr: dparams) : mpred :=
  !! (cold01 fs /\ par_ok pr /\
      0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
      Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
      0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
      (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\
      (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s) /\ cmem_ok (sf_mem s)) &&
  (dctx_token p * dctx_pad p *
   cfg_lit p * frame_fields p fs * tabs_rep TABS gv p t *
   field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
   field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
   field_at Ews t_dctx (DOT _staticSize) (Vlong (Int64.repr 0)) p *
   field_at Ews t_dctx (DOT _maxWindowSize) (Vlong (Int64.repr (dp_wmax pr))) p *
   field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr (if stable then 1 else 0))) p *
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
   field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
   field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
   ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
   blk_tok (sf_mem s) (tarray tuchar (sizeof t_dctx)) p).

Definition ctx_rest3k (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) : mpred :=
  ctx_rest3 TABS gv p (c3_fs k) (c3_tabs k) (c3_stable k) (c3_s k) (c3_par k).

Lemma ctx_rep3_split DENT TABS gv p k :
  ctx_rep3 DENT TABS gv p k =
  !! (0 <= sf_held (c3_s k)) &&
  (field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p *
   dgroup DENT gv p (c3_dict k) *
   field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem (c3_s k))) p *
   cm_have (sf_mem (c3_s k)) (sf_given (c3_s k)) *
   field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par k)))) p *
   field_at Ews t_dctx (DOT _ddictSet) (c3_sp k) p *
   cfg_fmt p (dp_fmt (c3_par k)) *
   hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)) *
   ctx_rest3k TABS gv p k).
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, cgroup3, sgroup, mgroup, ctx_rest3k, ctx_rest3, cfg_fmt, cfg_lit.
  repeat match goal with |- context [field_at ?sh ?t ?gfs ?v ?q] => generalize (field_at sh t gfs v q); intro end.
  apply pred_ext.
  - Intros. repeat (rewrite prop_true_andp by tauto). cancel.
  - Intros. repeat (rewrite prop_true_andp by tauto). cancel.
Qed.

Lemma ctx_rest3_par TABS gv p fs t stable s pr :
  ctx_rest3 TABS gv p fs t stable s pr |-- !! par_ok pr.
Proof. unfold ctx_rest3. entailer!. Qed.

(* the facts of the streaming fields the loading functions need *)
Lemma ctx_rest3k_props TABS gv p k :
  ctx_rest3k TABS gv p k |--
  !! (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed /\ 0 <= sf_inSize (c3_s k) /\
      0 <= sf_outSize (c3_s k) /\ cmem_ok (sf_mem (c3_s k)) /\ par_ok (c3_par k)).
Proof. unfold ctx_rest3k, ctx_rest3. entailer!. Qed.

Lemma ctx_rest3k_with_dict TABS gv p k d : ctx_rest3k TABS gv p (c3_with_dict k d) = ctx_rest3k TABS gv p k.
Proof. reflexivity. Qed.

Lemma ctx_rest3k_with_set TABS gv p k sp l : ctx_rest3k TABS gv p (c3_with_set k sp l) = ctx_rest3k TABS gv p k.
Proof. reflexivity. Qed.

Lemma ctx_rest3k_with_held TABS gv p k h :
  ctx_rest3k TABS gv p (c3_with_s k (sf_with_held (c3_s k) h)) = ctx_rest3k TABS gv p k.
Proof. reflexivity. Qed.

(* the bytes of the set are not negative *)
Lemma hset_rep_hb am sp l hb : hset_rep am sp l hb |-- !! (0 <= hb).
Proof.
  unfold hset_rep. destruct (eq_dec sp nullval).
  - entailer!.
  - Intros tp tbl. unfold hs_table. Intros. entailer!.
    destruct am; simpl; [| lia]. pose proof (Zlength_nonneg tbl). unfold sizeof, t_hset; simpl. lia.
Qed.

End CM_Load3Split_1.
