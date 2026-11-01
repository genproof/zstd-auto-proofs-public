(* FS3 body of ZSTD_createDCtx_advancedP (a context with its own allocator: res_memory_oneshot, res_memory_stream,
   res_free).  zstd's body is `return ZSTD_createDCtx_internal(customMem);`: the call is made with the allocator
   am = Some m; the new context is the abstract dctx_init_m m.
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_body3_advp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Section Advp3.
Variables (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel).

(* a fresh context points to its struct (its tables are not yet allocated: their pointer fields are there) *)
Lemma ctx03m_valid (gv: globals) (q: val) (am: option cmem) :
  ctx_rep3 DENT TABS gv q (k03m am) |-- valid_pointer q.
Proof.
  unfold ctx_rep3, ctx_body3, fgroup3, k03m, k03; simpl tabs_rep. unfold tables_uninit. normalize.
  assert (V: field_at_ Ews t_dctx (DOT _LLTptr) q |-- valid_pointer q)
    by (apply field_at_valid_ptr0; auto; reflexivity).
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) q * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

(* the fresh context of the allocator m is the abstract dctx_init_m m: no dictionary, no stream, no DDict set, the
   allocator recorded with nothing given out besides the context *)
Lemma dc3_init_m (gv: globals) (q: val) (m: cmem) :
  ctx_rep3 DENT TABS gv q (k03m (Some m)) |-- DC3x DENT TABS SR BR gv q (dctx_init_m m) && valid_pointer q.
Proof.
  apply andp_right; [ | apply ctx03m_valid].
  unfold DC3x, DC3_of. Exists (k03m (Some m)). apply andp_right; [ | apply derives_refl].
  apply prop_right. split; [ | split; [ | split]].
  - unfold base_rel3, set_cur_ok, mem_rel3; simpl. repeat split; auto; try discriminate.
    + left. unfold dict_rel3_of, dctx_init_m, df_none; simpl. auto.
    + exists 0. split; [reflexivity | rep_lia].
    + unfold mem_room. simpl. auto.
  - simpl. intros H; congruence.
  - simpl. intros ba H; discriminate.
  - (* a fresh context is clean: the exact relation holds of no call *)
    intros _ _ _. exact (sr_ex_clean SR (c3_s (k03m (Some m))) (c3_fs (k03m (Some m)))
                           eq_refl eq_refl eq_refl eq_refl eq_refl).
Qed.

Lemma advp3_createDCtx_advancedP:
  semax_body Vprog (FS3_G DENT TABS SR BR) f_ZSTD_createDCtx_advancedP
    (ZSTD_createDCtx_advancedP_spec (DC3x DENT TABS SR BR)).
Proof.
  start_function.
  assert_PROP (cmem_ok (Some m)).
  { unfold cm_funs. sep_apply (func_ptr'_isptr cm_alloc_spec (cm_alloc m)).
    sep_apply (func_ptr'_isptr cm_free_spec (cm_free m)). entailer!.
    unfold cmem_ok. split; [| split]; auto. }
  assert (Hsz: 0 <= dctx_size) by (rewrite dctx_size_eq; lia).
  forward_call (gv, shm, pm, Some m).
  { simpl cmem_v. simpl cm_have. unfold t_cmem. cancel. }
  { unfold cm_room. lia. }
  Intros q.
  forward.
  Exists q. entailer!.
  destruct (eq_dec q nullval); [simpl cm_have; cancel | ].
  apply dc3_init_m.
Qed.

End Advp3.

Lemma body_createDCtx_advancedP :
  FS3_body (fun DENT TABS SR BR => ZSTD_createDCtx_advancedP_spec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  exists f_ZSTD_createDCtx_advancedP; split; [reflexivity | split; [reflexivity | ]].
  apply advp3_createDCtx_advancedP.
Qed.

End CM_body3_advp_1.
