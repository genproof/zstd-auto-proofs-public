(* FS3 one-shot: ZSTD_decompress *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base.
Local Open Scope logic.

Section CM_O3Dec_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* zstd_globals without ZSTD_defaultCMem *)
Definition zg_nocm (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv)%logic.

(* ZSTD_decompress creates its context with ZSTD_defaultCMem (a global of zstd_globals), the default allocator *)
Lemma zg_split (gv: globals) :
  zstd_globals gv = data_at Ers t_cmem (cmem_v None) (gv _ZSTD_defaultCMem) * zg_nocm gv.
Proof.
  unfold zstd_globals, zg_nocm; simpl cmem_v; unfold ZSTD_defaultCMem_val, t_cmem; apply pred_ext; cancel.
Qed.

Lemma zg_join (gv: globals) :
  data_at Ers t_cmem (cmem_v None) (gv _ZSTD_defaultCMem) * zg_nocm gv |-- zstd_globals gv.
Proof. rewrite zg_split. apply derives_refl. Qed.

Section Oneshot.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.

Lemma ctx_rep3_init gv q : ctx_rep3 DENT TABS gv q k03 |-- DC3x DENT TABS SR BR gv q dctx_init.
Proof.
  unfold DC3x, DC3_of. Exists k03. entailer!.
  (* a new context is clean: the image of no call *)
  split; [ | split; [intros ba E; discriminate |
                     intros _ _ _; apply (sr_ex_clean SR s0 fs0); reflexivity]].
  unfold base_rel3, k03, dctx_init; simpl.
  split3; auto. split; auto. split; [left; split; [reflexivity | left; reflexivity] | ].
  split; [intros dr q0 dd dd' E; discriminate | ].
  split; [exists 0; split; [reflexivity | rep_lia] | ].
  split; [unfold stage_rel3; split; [intros _; unfold s0; simpl; unfold ZSTD_NO_FORWARD_PROGRESS_MAX; lia | intros _; split; reflexivity] | split; [intros E; contradiction | ]].
  unfold mem_rel3, mem_room, local_mem; simpl. split; [reflexivity | split; [reflexivity | intros E; contradiction]].
Qed.

Lemma ctx_rep3_k0_valid gv q : ctx_rep3 DENT TABS gv q k03 |-- valid_pointer q.
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, tabs_rep, tables_uninit. simpl. normalize.
  apply derives_trans with (field_at_ Ews t_dctx (DOT _LLTptr) q * TT).
  - cancel.
  - apply sepcon_valid_pointer1. unfold field_at_.
    apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

(* ZSTD_decompressDCtx's error codes on a new context are those of ZSTD_decompress *)
Lemma codes_dctx_init s cap r :
  (dc_set dctx_init = nil ->
     oneshot_codes (dmode_of (dc_par dctx_init)) sel_none (dictref_model (dc_dict dctx_init)) s cap r) ->
  oneshot_codes md_dflt sel_none (Some no_dict) s cap r.
Proof. intros H. exact (H eq_refl). Qed.

Lemma body_decompress3 :
  body_ok (FS3_G DENT TABS SR BR) ZSTD_decompress_spec.
Proof.
  exists f_ZSTD_decompress; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  rewrite zg_split.
  forward_call (gv, Ers, gv _ZSTD_defaultCMem, @None cmem).
  { simpl cm_have. cancel. }
  Intros q.
  sep_apply (zg_join gv).
  rewrite k03m_none. simpl cm_have.
  destruct (eq_dec q nullval) as [Hq | Hq].
  - subst q.
    forward_loop (PROP() LOCAL(temp _dctx nullval; gvars gv; temp _dst dst;
        temp _dstCapacity (Vlong (Int64.repr cap)); temp _src src;
        temp _srcSize (Vlong (Int64.repr (Zlength s))))
      SEP(mem_mgr gv; zstd_globals gv; pws_pred W; mbuf shd cap (Zrepeat Vundef cap) dst;
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src))
      break: (PROP(False) LOCAL() SEP()).
    + entailer!.
    + forward_if.
      * match goal with |- semax _ ?P _ _ =>
          forward_loop P break: P; [entailer! | forward; entailer! | ] end.
        match goal with |- semax _ ?P _ _ =>
          forward_loop P break: P;
            [entailer! | forward_if P; [contradiction | forward; entailer! | forward; entailer!] | ] end.
        match goal with |- semax _ ?P _ _ =>
          forward_loop P break: P; [entailer! | forward; entailer! | ] end.
        match goal with |- semax _ ?P _ _ =>
          forward_loop P break: P; [entailer! | forward; entailer! | ] end.
        forward.
        Exists (err_code ZSTD_error_memory_allocation) (Zrepeat Vundef cap).
        entailer!.
        repeat match goal with |- _ /\ _ => split end;
          first [ exact (oneshot_ok_mem3 _ _ _ _ _) | exact (oneshot_codes_mem _ _ _ _ _)
                | rewrite Zlength_Zrepeat; lia
                | f_equal; apply Int64.eqm_samerepr; unfold err_code, ZSTD_error_memory_allocation;
                  exists (-1); reflexivity
                | unfold err_code, ZSTD_error_memory_allocation; rep_lia ].
      * contradiction.
  -
    forward_loop (PROP() LOCAL(temp _dctx q; gvars gv; temp _dst dst;
        temp _dstCapacity (Vlong (Int64.repr cap)); temp _src src;
        temp _srcSize (Vlong (Int64.repr (Zlength s))))
      SEP(mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv q k03; pws_pred W;
          mbuf shd cap (Zrepeat Vundef cap) dst;
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src))
      break: (PROP() LOCAL(temp _dctx q; gvars gv; temp _dst dst;
        temp _dstCapacity (Vlong (Int64.repr cap)); temp _src src;
        temp _srcSize (Vlong (Int64.repr (Zlength s))))
      SEP(mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv q k03; pws_pred W;
          mbuf shd cap (Zrepeat Vundef cap) dst;
          data_at shs (tarray tuchar (Zlength s)) (zbytes s) src)).
    + entailer!.
    + forward_if.
      { apply denote_tc_test_eq_split; [ | auto with valid_pointer].
        sep_apply (ctx_rep3_k0_valid gv q). apply sepcon_valid_pointer1. cancel. }
      * exfalso; apply Hq; auto.
      * forward. entailer!.
    + sep_apply (ctx_rep3_init gv q).
      forward_call (W, gv, q, dctx_init, Ews, shd, dst, cap, shs, src, s).
      { simpl dict_res. unfold set_res; simpl. cancel. }
      Intros vret. destruct vret as [[r out] st']. simpl fst in *; simpl snd in *.
      (* the error codes of a new context (no dictionary, no set) *)
      repeat match goal with H: dc_set dctx_init = nil -> _ |- _ => apply codes_dctx_init in H end.
      forward_call (gv, q, Some st').
      forward.
      Exists r out. entailer!.
      (* a new context has no allocator of its own: freeing it gives nothing back (cm_back) *)
      match goal with Ha: oneshot_after _ st' |- _ =>
        destruct (oneshot_after_init dctx_init st' eq_refl Ha) as [-> | ->] end; apply derives_refl.
Qed.

End Oneshot.

End CM_O3Dec_1.
