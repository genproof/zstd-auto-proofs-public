(* FS3 load3: ZSTD_DCtx_refPrefix_advanced (port of v2 body_FS_load.v) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split Zstd.proof.dec.v3.FS.load3.Load3Post.
Local Open Scope logic.

(* do { body } while (0): the loop invariant is the current precondition *)
Ltac dw0 tac :=
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end;
  [ apply ENTAIL_refl | tac | forward; apply ENTAIL_refl | abbreviate_semax ].
Ltac dw0_skip := dw0 ltac:(forward; apply ENTAIL_refl).
Ltac dw0_if0 := dw0 ltac:(forward_if; [contradiction | forward; apply ENTAIL_refl]).

Section CM_Load3Pre_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_refpre (DENT: dent_pred) (TABS: tabs_pred) : funspecs :=
  [ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS; ERR_isError_spec].

Lemma body_refPrefix_advanced3_small DENT TABS :
  body_ok (G_refpre DENT TABS) (ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS).
Proof.
  exists f_ZSTD_DCtx_refPrefix_advanced; split; [reflexivity | split; [reflexivity | ]].
  unfold G_refpre.
  start_function.
  match goal with Hx: sf_stage (c3_s k) = 0 |- _ => rename Hx into Hst end.
  match goal with Hx: sf_mem (c3_s k) = None |- _ => rename Hx into Hsm end.
  match goal with Hx: local_mem _ _ |- _ => rename Hx into Hlm end.
  forward_loop
    (PROP () LOCAL (gvars gv; temp _dctx p; temp _prefix pk;
                    temp _prefixSize (Vlong (Int64.repr (Zlength b)));
                    temp _dictContentType (Vint (Int.repr ctype)))
     SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p k;
          data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))
  continue:
    (EX d0: dfields, PROP (load_res3 None pk b 1 ctype 0 d0) LOCAL (temp _dctx p)
     SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p (c3_with_dict k d0);
          data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))%assert
  break:
    (EX d0: dfields, PROP (load_res3 None pk b 1 ctype 0 d0) LOCAL (temp _dctx p)
     SEP (pws_pred W; mem_mgr gv; zstd_globals gv; ctx_rep3 DENT TABS gv p (c3_with_dict k d0);
          data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))%assert.
  { entailer!. }
  { forward_call (W, gv, p, k, sh, pk, b, 1, ctype).
    { rewrite Hsm; exact I. }
    Intros vret. destruct vret as [r k']. simpl fst in *; simpl snd in *.
    match goal with Hl: load_int_res _ _ _ _ _ _ _ |- _ => rename Hl into Hli end.
    rewrite Hsm in Hlm.
    destruct (load_int_res_none _ _ _ _ _ _ _ Hst Hsm Hlm Hli) as [d0 [Hlr ->]].
    pose proof (load_res3_r _ _ _ _ _ _ _ Hlr) as Hr.
    forward_call r.
    forward_if.
    { dw0_skip. dw0_if0. dw0_skip. dw0_skip.
      forward.
      Exists r d0. entailer!.
      destruct Hr; subst; [match goal with Hx: (if is_error_code _ then 1 else 0) <> 0 |- _ => revert Hx end; vm_compute; congruence|]. exists d0; split; auto. }
    { forward. Exists d0. entailer!.
      destruct Hr; subst; [auto| match goal with Hx: Int.repr (if is_error_code _ then 1 else 0) = Int.zero |- _ => revert Hx end; vm_compute; intro X; inversion X]. } }
  { forward. apply ENTAIL_refl. }
  Intros d0.
  rewrite ctx_rep3_split. Intros.
  freeze FR := (field_at _ _ (DOT _streamStage) _ _) (field_at _ _ (DOT _customMem) _ _) (cm_have _ _)
    (field_at _ _ (DOT _refMultipleDDicts) _ _) (field_at _ _ (DOT _ddictSet) _ _) (cfg_fmt _ _)
    (hset_rep _ _ _ _) (ctx_rest3k _ _ _ _).
  unfold dgroup. Intros.
  forward.
  forward.
  Exists 0 (df_set_uses d0 1).
  thaw FR.
  rewrite (ctx_rep3_split DENT TABS gv p (c3_with_dict k _)), !ctx_rest3k_with_dict.
  replace (local_held (c3_dict (c3_with_dict k (df_set_uses d0 1)))) with (local_held d0) by reflexivity.
  unfold dgroup. cbn [c3_dict c3_with_dict c3_s c3_par c3_sp c3_set df_set_uses df_local df_ddict df_uses df_lx].
  entailer!.
  exists d0; split; auto.
Qed.

Lemma body_refPrefix_advanced3 : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_refpre DENT TABS)); [unfold G_refpre; load3_in | apply body_refPrefix_advanced3_small].
Qed.

End CM_Load3Pre_1.
