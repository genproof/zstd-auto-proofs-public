(* FS3 load3: ZSTD_DCtx_loadDictionary_advanced and ZSTD_DCtx_refPrefix_advanced (port of v2 body_FS_load.v;
   ctype 2 = fullDict) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split.
Local Open Scope logic.

(* do { body } while (0): the loop invariant is the current precondition *)
Ltac dw0 tac :=
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end;
  [ apply ENTAIL_refl | tac | forward; apply ENTAIL_refl | abbreviate_semax ].
Ltac dw0_skip := dw0 ltac:(forward; apply ENTAIL_refl).
Ltac dw0_if0 := dw0 ltac:(forward_if; [contradiction | forward; apply ENTAIL_refl]).

Section CM_Load3Adv_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition G_loadadv (DENT: dent_pred) : funspecs :=
  [ZSTD_clearDict_spec DENT; ZSTD_createDDict_advancedP_spec3 DENT].

(* room for n bytes from h, for fewer bytes h' given out *)
Lemma cm_room_le (am: option cmem) (h h' n: Z) : cm_room am h n -> 0 <= h' <= h -> cm_room am h' n.
Proof. destruct am as [m|]; simpl; [lia | auto]. Qed.

Lemma ddx_held_nonneg (x: ddx) : 0 <= ddx_held x.
Proof.
  unfold ddx_held. destruct (dx_mem x); [| lia].
  pose proof (Zlength_nonneg (dx_bytes x)). destruct (ddx_copied x); simpl; lia.
Qed.

Lemma local_held_nonneg (d: dfields) : 0 <= local_held d.
Proof.
  unfold local_held. destruct (eq_dec (df_local d) nullval); [lia |].
  destruct (df_lx d) as [[x buf]|]; [apply ddx_held_nonneg | lia].
Qed.

Lemma sf_given_with_held (s: sfields) (h: Z) : sf_given (sf_with_held s h) = sf_given s - sf_held s + h.
Proof. unfold sf_given; simpl. lia. Qed.

Lemma body_loadDictionary_advanced3_small DENT TABS :
  body_ok (G_loadadv DENT) (ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS).
Proof.
  exists f_ZSTD_DCtx_loadDictionary_advanced; split; [reflexivity | split; [reflexivity | ]].
  unfold G_loadadv.
  start_function.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (0 <= sf_held (c3_s k) - local_held (c3_dict k)) as Hhb by (sep_apply hset_rep_hb; entailer!).
  assert_PROP (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed /\ 0 <= sf_inSize (c3_s k) /\
               0 <= sf_outSize (c3_s k) /\ cmem_ok (sf_mem (c3_s k)) /\ par_ok (c3_par k)) as Hrest
    by (sep_apply (ctx_rest3k_props TABS gv p k); entailer!).
  destruct Hrest as (Hsr & Hin & Hout & Hcm & _).
  freeze FR := (field_at _ _ (DOT _refMultipleDDicts) _ _) (field_at _ _ (DOT _ddictSet) _ _) (cfg_fmt _ _)
    (hset_rep _ _ _ _) (ctx_rest3k _ _ _ _).
  match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_loop (PROPx Pr (LOCALx L (SEPx S))) break: (PROPx ((sf_stage (c3_s k) = 0) :: Pr) (LOCALx L (SEPx S))) end.
  { entailer!. }
  { forward. forward_if.
    { (* a frame is being streamed: stage_wrong, nothing changed *)
      dw0_skip. dw0_if0. dw0_skip. dw0_skip.
      forward.
      Exists (Int64.unsigned (Int64.repr (-60))) k.
      thaw FR. rewrite (ctx_rep3_split DENT TABS gv p k).
      entailer!.
      split; [ | rewrite Int64.repr_unsigned; reflexivity].
      left. split; [intros E; rewrite E in *; contradiction | split; [reflexivity | reflexivity]]. }
    { forward. entailer!. } }
  Intros.
  match goal with Hx: sf_stage (c3_s k) = 0 |- _ => rename Hx into Hst0 end.
  match goal with Hx: sf_stage (c3_s k) = 0 -> cm_room _ _ _ |- _ => specialize (Hx Hst0); rename Hx into Hroom end.
  match goal with Hx: local_mem _ _ |- _ => rename Hx into Hlm end.
  match goal with Hx: buf_ok _ _ _ _ |- _ => rename Hx into Hbuf end.
  assert (Hgv: 0 <= sf_given (c3_s k) - local_held (c3_dict k))
    by (unfold sf_given; rewrite dctx_size_eq; lia).
  assert (Hgv': sf_given (c3_s k) - local_held (c3_dict k) <= sf_given (c3_s k))
    by (pose proof (local_held_nonneg (c3_dict k)); lia).
  replace (sf_given (c3_s k)) with ((sf_given (c3_s k) - local_held (c3_dict k)) + local_held (c3_dict k)) by lia.
  forward_call (gv, p, c3_dict k, sf_mem (c3_s k), sf_given (c3_s k) - local_held (c3_dict k)).
  assert_PROP (isptr pk) as Hpk by entailer!.
  forward_if (temp _t'2 (Vint (Int.repr (if Zlength b =? 0 then 0 else 1)))).
  { pose proof Hbuf as H2'; unfold buf_ok in H2'.
    sep_apply (data_at_data_at_ sh (tarray tuchar (Zlength b)) (zbytes b) pk). sep_apply H2'.
    destruct pk; try contradiction.
    Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl. Opaque denote_tc_test_eq.
    apply andp_right. entailer!. apply sepcon_weak_valid_pointer1. apply andp_left1. apply derives_refl. }
  { forward. entailer!. pose proof (Zlength_nonneg b).
    destruct (Z.eqb_spec (Zlength b) 0) as [E|E]; [rewrite E; reflexivity|].
    unfold Int64.cmpu. rewrite Int64.eq_false; [reflexivity|].
    intro Hc; apply (f_equal Int64.unsigned) in Hc; rewrite !Int64.unsigned_repr in Hc; rep_lia. }
  { subst; contradiction. }
  forward_if (EX d': dfields,
    PROP (load_res3 (sf_mem (c3_s k)) pk b method ctype 0 d')
    LOCAL (gvars gv; temp _dctx p)
    SEP (FRZL FR; pws_pred W; mem_mgr gv; zstd_globals gv;
         field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage (c3_s k)))) p; dgroup DENT gv p d';
         field_at Ews t_dctx (DOT _customMem) (cmem_v (sf_mem (c3_s k))) p;
         cm_have (sf_mem (c3_s k)) (sf_given (c3_s k) - local_held (c3_dict k) + local_held d');
         data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))%assert.
  { (* a dictionary of |b| > 0 bytes *)
    assert (Hb: Zlength b <> 0)
      by (intro E; match goal with Hx: (if Zlength b =? 0 then 0 else 1) <> 0 |- _ => rewrite E in Hx; simpl in Hx; congruence end).
    unfold dgroup. Intros.
    assert_PROP (field_compatible t_dctx (DOT _customMem) p) as Hfc by entailer!.
    rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
    rewrite <- (bytes_at_ptr sh b pk Hpk).
    forward_call (W, gv, sh, pk, b, method, ctype, Ews, field_address t_dctx (DOT _customMem) p,
                  sf_mem (c3_s k), sf_given (c3_s k) - local_held (c3_dict k)).
    { apply (cm_room_le _ _ _ _ Hroom); lia. }
    Intros q.
    rewrite (bytes_at_ptr sh b pk Hpk).
    forward.
    destruct (eq_dec q nullval) as [Hq|Hq].
    { subst q.
      match goal with |- semax _ ?P _ _ =>
        forward_loop P continue: (FF: environ -> mpred) break: (FF: environ -> mpred) end.
      { apply ENTAIL_refl. }
      { forward. forward_if.
        2:{ exfalso; auto. }
        dw0_skip. dw0_if0. dw0_skip. dw0_skip.
        forward.
        Exists (err_code ZSTD_error_memory_allocation)
          (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) (sf_held (c3_s k) - local_held (c3_dict k) + local_held df_none))) df_none).
        thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_dict _ _)). rewrite ctx_rest3k_with_dict, ctx_rest3k_with_held.
        unfold dgroup.
        cbn [c3_dict c3_with_dict c3_with_s c3_s c3_par c3_sp c3_set df_local df_ddict df_uses df_lx df_none sf_mem sf_held sf_with_held].
        rewrite sf_given_with_held.
        replace (local_held df_none) with 0 by reflexivity.
        replace (sf_given (c3_s k) - sf_held (c3_s k) + (sf_held (c3_s k) - local_held (c3_dict k) + 0))
          with (sf_given (c3_s k) - local_held (c3_dict k)) by lia.
        replace (sf_held (c3_s k) - local_held (c3_dict k) + 0 - 0) with (sf_held (c3_s k) - local_held (c3_dict k)) by lia.
        rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
        unfold local_rep; rewrite if_true by auto.
        entailer!.
        split; [unfold err_code, ZSTD_error_memory_allocation; rep_lia |].
        split. { right. split; [exact Hst0 |]. exists df_none. split; [| change (local_held df_none) with 0; rewrite Z.add_0_r; reflexivity].
                 unfold load_res3. rewrite (proj2 (Z.eqb_neq _ _) Hb). right; auto. }
        f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. } }
    Intros buf ores.
    assert_PROP (isptr q /\ (method = 1 -> buf = pk)) as Hqb.
    { unfold ddict_rep_at, ddict_struct. Intros. entailer!. }
    destruct Hqb as [Hqp Hbuf'].
    match goal with |- semax _ (PROPx ?Pr (LOCALx ?L ?S)) _ _ =>
      forward_loop (PROPx Pr (LOCALx L S)) continue: (PROPx Pr (LOCALx (temp _t'4 q :: L) S))
         break: (PROPx Pr (LOCALx (temp _t'4 q :: L) S)) end.
    { apply ENTAIL_refl. }
    { forward. forward_if.
      { apply denote_tc_test_eq_split; [ | apply valid_pointer_null ].
        unfold ddict_rep_at, ddict_struct. Intros. simpl dx_q.
        match goal with |- context [field_at Ews ?T (DOT _dictBuffer) ?X q] =>
          apply derives_trans with (sepcon (field_at Ews T (DOT _dictBuffer) X q) TT); [cancel |] end.
        apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; reflexivity. }
      { contradiction. }
      forward. apply ENTAIL_refl. }
    { forward. apply ENTAIL_refl. }
    abbreviate_semax.
    forward. forward. forward.
    Exists {| df_local := q; df_ddict := q; df_uses := -1;
              df_lx := Some (ddx_of3 (sf_mem (c3_s k)) q pk b method ctype ores, buf) |}.
    unfold dgroup, local_rep; cbn [df_local df_ddict df_uses df_lx].
    destruct (eq_dec q nullval); [contradiction |].
    rewrite (field_at_data_at Ews t_dctx (DOT _customMem)).
    replace (local_held {| df_local := q; df_ddict := q; df_uses := -1;
                           df_lx := Some (ddx_of3 (sf_mem (c3_s k)) q pk b method ctype ores, buf) |})
      with (ddx_held (ddx_of3 (sf_mem (c3_s k)) q pk b method ctype ores))
      by (unfold local_held; cbn [df_local df_lx]; rewrite if_false by auto; reflexivity).
    entailer!.
    unfold load_res3. rewrite (proj2 (Z.eqb_neq _ _) Hb). left. split; auto. split; auto.
    exists q, buf, ores. auto. }
  { (* none *)
    forward. Exists df_none.
    replace (local_held df_none) with 0 by reflexivity. rewrite Z.add_0_r.
    entailer!.
    destruct (Zlength b =? 0) eqn:E; [|discriminate].
    unfold load_res3; rewrite E; auto. }
  Intros d'.
  forward.
  Exists 0 (c3_with_dict (c3_with_s k (sf_with_held (c3_s k) (sf_held (c3_s k) - local_held (c3_dict k) + local_held d'))) d').
  thaw FR. rewrite (ctx_rep3_split DENT TABS gv p (c3_with_dict _ _)). rewrite ctx_rest3k_with_dict, ctx_rest3k_with_held.
  cbn [c3_dict c3_with_dict c3_with_s c3_s c3_par c3_sp c3_set sf_mem sf_held sf_with_held].
  rewrite sf_given_with_held.
  replace (sf_given (c3_s k) - sf_held (c3_s k) + (sf_held (c3_s k) - local_held (c3_dict k) + local_held d'))
    with (sf_given (c3_s k) - local_held (c3_dict k) + local_held d') by lia.
  replace (sf_held (c3_s k) - local_held (c3_dict k) + local_held d' - local_held d')
    with (sf_held (c3_s k) - local_held (c3_dict k)) by lia.
  pose proof (local_held_nonneg d').
  entailer!.
  right. split; [exact Hst0 |]. exists d'. split; auto.
Qed.

End CM_Load3Adv_1.
