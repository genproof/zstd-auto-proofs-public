(* The harness obligation of res_free (harness/res_free.c): for ANY predicates DC, DD of the decoder's API
   (Spec_api6) whose contexts let a law read their allocator's state (Spec_api6.dc_cm_ok), the counting allocator
   (count_alloc, count_free: Alloc_res_free.v), the helpers upto, any_bytes and copy_of (laws_common.h, proved once
   in the frames kit) and main satisfy their specifications.

   main's loop keeps the context in the states of Facts_res_free.rf_inv (its own allocator, a dictionary of its own
   or the harness's DDict, a DDict set of at most that DDict) and holds the harness's DDict (ddict_hold), which it
   lends to the calls that read it (dict_res, set_res).  The counter `now` is in the context (dc_cm_ok): main takes
   it out at the early returns, to give its local variable back; ZSTD_freeDCtx gives it back with nothing given
   out (cm_back), so the check now == 0 holds (Alloc_res_free.count_zero). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.res_free.Kit_res_free.
Require Export Zstd.proof.harness.res_free.Stream_res_free.

Local Ltac expand_main_pre ::= idtac.

(* the directive main draws: (1 + u % 3) of a byte u *)
Lemma mods3 u : 0 <= u <= Byte.max_unsigned -> Int.mods (Int.repr u) (Int.repr 3) = Int.repr (u mod 3).
Proof.
  intros Hu. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

(* the harness's copy kept, at the decoder's compspecs, as ZSTD_createDDict takes it (NULL: no bytes) *)
Lemma kept_to_Z kept s :
  (if eq_dec kept nullval then emp
   else (malloc_token Ews (tarray tuchar (Zlength s)) kept * data_at Ews (tarray tuchar (Zlength s)) (zbytes s) kept)) |--
  pws_pred (kept_wits kept s) * bytes_at Ews s kept.
Proof.
  unfold kept_wits, bytes_at, pws_pred. destruct (eq_dec kept nullval); [cancel |]. simpl.
  sep_apply (to_Z Ews (Zlength s) (zbytes s) kept). sep_apply (tok_to_Z Ews (Zlength s) kept). cancel. apply derives_refl.
Qed.

Lemma dd_new_drop (DD: globals -> val -> ddict_st -> mpred) gv q2 dd2 :
  (if eq_dec q2 nullval then emp else (DD gv q2 dd2 && valid_pointer q2)) |--
  (if eq_dec q2 nullval then emp else DD gv q2 dd2).
Proof. destruct (eq_dec q2 nullval); [apply derives_refl | apply drop_vp]. Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Hypothesis DCM : @dc_cm_ok DC count_cm.

Lemma body_main_G0 : semax_body Vprog (G0 DC DD) f_main main_spec.
Proof.
  change (semax_body Vprog (G0 DC DD) f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.res_free.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward.
  make_func_ptr _count_alloc.
  forward.
  make_func_ptr _count_free.
  forward.
  forward.
  change (Int.signed (Int.repr 0)) with 0.
  sep_apply (cmem_to_Z Tsh (gv _count_alloc) (gv _count_free) v_now v_mem).
  sep_apply (count_init_dctx v_now).
  sep_apply (cm_funs_fold gv v_now).
  assert_PROP (isptr v_now) as Hno by entailer!.
  forward_call (gv, Tsh, v_mem, the_cm gv v_now).
  { simpl cm_opaque; simpl cm_bound. cancel. }
  Intros dctx.
  set (m := the_cm gv v_now).
  forward.
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { (* no context: the allocator's state and the ZSTD_customMem go back to main's frame *)
    subst dctx.
    forward_if; [| contradiction].
    unfold m, cm_funs, cmem_val, the_cm; cbn [cm_alloc cm_free cm_opaque cm_bound CM count_cm].
    unfold count_CM. Intros.
    sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_now v_mem).
    forward.
    sep_apply (data_at_data_at_ Tsh tulong). sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)).
    cancel. }
  forward_if.
  { contradiction. }
  Intros. sep_apply (drop_vp (DC gv dctx (dctx_init_m m)) dctx).
  unfold m, cmem_val, the_cm; cbn [cm_alloc cm_free cm_opaque].
  sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_now v_mem).
  fold (the_cm gv v_now). fold m.
  forward_loop (EX st: dctx_st, EX q: val, EX dd: ddict_st,
    PROP (rf_inv m q dd st; rf_ok st; is_pointer_or_null q)
    LOCAL (temp _dctx dctx; temp _ddict q; lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out;
           lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
           lvar _now tulong v_now; gvars gv)
    SEP (DC gv dctx st; data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
         data_at_ Tsh (Tstruct _ZSTD_outBuffer_s noattr) v_out; data_at_ Tsh (Tstruct _ZSTD_inBuffer_s noattr) v_in;
         ddict_hold DD gv q dd; dd_tok q dd; mem_mgr gv; zstd_globals gv; TT))%assert
    break: (EX st: dctx_st, EX q: val, EX dd: ddict_st,
    PROP (rf_inv m q dd st; rf_ok st; is_pointer_or_null q)
    LOCAL (temp _dctx dctx; temp _ddict q; lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out;
           lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
           lvar _now tulong v_now; gvars gv)
    SEP (DC gv dctx st; data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
         data_at_ Tsh (Tstruct _ZSTD_outBuffer_s noattr) v_out; data_at_ Tsh (Tstruct _ZSTD_inBuffer_s noattr) v_in;
         ddict_hold DD gv q dd; dd_tok q dd; mem_mgr gv; zstd_globals gv; TT))%assert.
  { Exists (dctx_init_m m) nullval (Build_ddict_st nil None nullval None).
    unfold ddict_hold, dd_tok. rewrite !if_true by reflexivity.
    pose proof (rf_init m (Build_ddict_st nil None nullval None)) as Hi0. pose proof (rf_ok_init m) as Ho0.
    entailer!. }
  { (* one iteration *)
    Intros st q dd.
    destruct (rf_mem_some _ _ _ _ H0) as (m' & Em & Ea & Ef & Eo).
    unfold m, the_cm in Eo; cbn [cm_opaque] in Eo.
    forward_call 9223372036854775807.
    Intros n.
    forward_call 9223372036854775807.
    Intros c.
    forward_call (gv, n).
    Intros vret. destruct vret as [ps s]. cbn [fst snd] in *.
    forward_call (tarray tuchar c, gv).
    { simpl. rep_lia. }
    Intros pd.
    unfold FSpecs.mbytes.
    repeat apply -> seq_assoc.
    (* src or dst NULL: the run ends; the counter goes back to main's frame *)
    destruct (eq_dec ps nullval) as [Hps|Hps].
    { subst ps. Intros. apply semax_if_seq. forward_if; [| contradiction]. forward.
      forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
      sep_apply (dc_now_out DC DCM gv dctx st m' Em). rewrite Eo.
      forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)). cancel. }
    destruct (eq_dec pd nullval) as [Hpd|Hpd].
    { subst pd. Intros. apply semax_if_seq. forward_if; [contradiction |]. forward.
      change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
      forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
      sep_apply (dc_now_out DC DCM gv dctx st m' Em). rewrite Eo.
      forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)). cancel. }
    Intros.
    assert_PROP (isptr pd) as Hpd' by entailer!.
    assert_PROP (isptr ps) as Hps' by entailer!.
    apply semax_if_seq. forward_if; [contradiction |].
    destruct pd as [| | | | | b i]; try contradiction. forward.
    forward_if; [discriminate |].
    set (pd := Vptr b i) in *. subst n.
    forward. forward. forward. forward. forward. forward.
    forward_call tt. Intros u.
    forward_if (dec_post DC DD gv v_now v_mem v_in v_out dctx m q dd s c ps pd).
    { (* one-shot decoding, in any state of the context (F10) *)
      unfold dec_post.
      set (W := [pw_token Ews (tarray tuchar (Zlength s)) ps; pw_token Ews (tarray tuchar c) pd] ++ dd_wits q dd).
      sep_apply (to_Z Ews (Zlength s) (zbytes s) ps).
      sep_apply (to_Z_ Ews c pd).
      sep_apply (tok_to_Z Ews (Zlength s) ps).
      sep_apply (tok_to_Z Ews c pd).
      assert (Ew: pws_pred W = (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps *
                                (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar c) pd * dd_tok q dd))%logic).
      { unfold W, pws_pred. rewrite map_app, fold_right_app. rewrite <- dd_wits_pred. reflexivity. }
      sep_apply (dd_lend DD m gv q dd st H0).
      assert (HW1: In (pw_token Ews (tarray tuchar (Zlength s)) ps) W) by (unfold W; simpl; tauto).
      assert (HW2: In (pw_token Ews (tarray tuchar c) pd) W) by (unfold W; simpl; tauto).
      assert (HW3: incl (dd_wits q dd) W) by (unfold W; intros x Hx; simpl; tauto).
      destruct (rf_dict_buf_ok m W Ews Ews q dd st c pd H0 HW3 HW2 ltac:(auto) ltac:(lia)) as [Hdb Hsb].
      forward_call (W, gv, dctx, st, Ews, Ews, pd, c, Ews, ps, s).
      { rewrite Ew. cancel. }
      { split; [apply buf_ok_tok; [exact HW2 | auto | lia | auto] |].
        split; [apply buf_ok_tok; [exact HW1 | auto | lia | auto] |].
        destruct H0 as (_ & Hb0 & _); exact Hb0. }
      Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
      sep_apply (dd_unlend DD m gv q dd st H0).
      rewrite Ew. Intros.
      sep_apply (mbuf_e Ews c out pd Hpd').
      sep_apply (of_Z Ews c out pd).
      sep_apply (of_Z Ews (Zlength s) (zbytes s) ps).
      sep_apply (tok_of_Z Ews (Zlength s) ps).
      sep_apply (tok_of_Z Ews c pd).
      Exists st' out (ps, (Vlong (Int64.repr (Int.signed (Int.repr 0))), Vlong (Int64.repr (Int.signed (Int.repr 0)))))
        (Vptr b i, (fst (snd (default_val (Tstruct _ZSTD_outBuffer_s noattr))), Vlong (Int64.repr (Int.signed (Int.repr 0))))).
      assert (Hi1: rf_inv m q dd st') by (eapply rf_oneshot; eassumption).
      assert (Ho1: rf_ok st') by (eapply rf_ok_oneshot; eassumption).
      entailer!. }
    { (* streaming, in any pieces *)
      eapply semax_pre; [| eapply semax_post; [| | | | exact (stream_seg DC DD gv v_now v_mem v_in v_out dctx m q dd st
                                                 s c ps b i eq_refl H0 H1 PNq Hd Hno H2 H3 H5 Hps')]];
        [entailer!; apply derives_refl | intros; unfold POSTCONDITION, abbreviate; simpl_ret_assert;
                     first [apply andp_left2; apply derives_refl | normalize] ..]. }
    unfold dec_post. Intros st1 oc vi vo.
    (* ZSTD_DCtx_reset with any of the three directives *)
    forward_call tt. Intros u2.
    pose proof (Z.mod_pos_bound u2 3 ltac:(lia)) as Hu2.
    forward_call (gv, dctx, st1, 1 + u2 mod 3).
    { rewrite (mods3 u2) by lia. rewrite Int.signed_repr by rep_lia. split; [rep_lia |].
      intros [_ E]. apply (f_equal Int.unsigned) in E. vm_compute in E. discriminate. }
    { entailer!. simpl. rewrite (mods3 u2) by lia. rewrite add_repr. reflexivity. }
    { unfold ZSTD_reset_session_only, ZSTD_reset_parameters, ZSTD_reset_session_and_parameters. lia. }
    Intros vret. destruct vret as [r1 st2]. cbn [fst snd] in *.
    match goal with Hr: reset_post _ _ _ _, Hi: rf_inv _ _ _ st1, Hok: rf_ok st1 |- _ =>
      pose proof (rf_reset m q dd st1 _ r1 st2 Hi Hr) as Hi2; pose proof (rf_ok_reset _ st1 r1 st2 Hok Hr) as Ho2 end.
    (* maybe ZSTD_DCtx_loadDictionary(dctx, src, n): a dictionary of any bytes, by copy *)
    forward_call tt. Intros u3.
    forward_if (EX st3: dctx_st,
      PROP (rf_inv m q dd st3; rf_ok st3)
      LOCAL (temp _dst pd; temp _src ps; temp _cap (Vlong (Int64.repr c)); temp _n (Vlong (Int64.repr (Zlength s)));
             temp _dctx dctx; temp _ddict q; lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out;
             lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
             lvar _now tulong v_now; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st3; malloc_token Ews (tarray tuchar c) pd;
           data_at Ews (tarray tuchar c) oc pd; malloc_token Ews (tarray tuchar (Zlength s)) ps;
           data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
           data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
           ddict_hold DD gv q dd; dd_tok q dd; TT))%assert.
    { set (W := [pw_token Ews (tarray tuchar (Zlength s)) ps]).
      sep_apply (to_Z Ews (Zlength s) (zbytes s) ps).
      sep_apply (tok_to_Z Ews (Zlength s) ps).
      assert (Ew: pws_pred W = @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps)
        by (unfold W, pws_pred; simpl; apply sepcon_emp).
      forward_call (W, gv, dctx, st2, Ews, ps, s).
      { rewrite Ew. cancel. }
      { split; [apply buf_ok_tok; [unfold W; simpl; tauto | auto | lia | auto] |].
        pose proof Hi2 as (_ & Hb2 & _). repeat split; try lia; congruence. }
      Intros vret. destruct vret as [r3 st3]. cbn [fst snd] in *.
      rewrite Ew.
      sep_apply (of_Z Ews (Zlength s) (zbytes s) ps).
      sep_apply (tok_of_Z Ews (Zlength s) ps).
      assert (Hi3: rf_inv m q dd st3) by (eapply rf_load; eassumption).
      assert (Ho3: rf_ok st3) by (eapply rf_ok_load; eassumption).
      Exists st3. entailer!. }
    { forward. Exists st2. entailer!. }
    Intros st3.
    match goal with Hi: rf_inv _ _ _ st3, Ho: rf_ok st3 |- _ => rename Hi into Hin3; rename Ho into Hok3 end.
    (* kept = copy_of(src, n): NULL with n != 0 ends the run *)
    forward_call (gv, Ews, ps, s).
    Intros kept. unfold FSpecs.mbytes.
    assert_PROP (is_pointer_or_null kept) as PNk by entailer!.
    forward_if (PROP ()
      LOCAL (temp _t'21 (Vint (if eq_dec kept nullval then (if Z.eq_dec (Zlength s) 0 then Int.zero else Int.one) else Int.zero));
             temp _kept kept; temp _dst pd; temp _src ps; temp _cap (Vlong (Int64.repr c));
             temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q;
             lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
             lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st3; malloc_token Ews (tarray tuchar c) pd;
           data_at Ews (tarray tuchar c) oc pd; malloc_token Ews (tarray tuchar (Zlength s)) ps;
           data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           if eq_dec kept nullval then emp
           else (malloc_token Ews (tarray tuchar (Zlength s)) kept * data_at Ews (tarray tuchar (Zlength s)) (zbytes s) kept);
           data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
           data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
           ddict_hold DD gv q dd; dd_tok q dd; TT)).
    { destruct (eq_dec kept nullval) as [Ek|Nk]; [subst kept; entailer! |]. entailer!. }
    { forward. rewrite if_true by auto. entailer!.
      destruct (Z.eq_dec (Zlength s) 0) as [Hz|Hz]; rewrite ?if_true by auto; unfold Int64.cmpu, Int64.eq;
        rewrite !Int64.unsigned_repr by rep_lia; destruct (zeq (Zlength s) 0); try contradiction; reflexivity. }
    { forward. rewrite if_false by (intro; subst; contradiction). entailer!. rewrite if_false by auto. reflexivity. }
    destruct (rf_mem_some _ _ _ _ Hin3) as (m3 & Em3 & Ea3 & Ef3 & Eo3).
    unfold m, the_cm in Eo3; cbn [cm_opaque] in Eo3.
    forward_if.
    { (* the run ends: the counter goes back to main's frame *)
      sep_apply (dc_now_out DC DCM gv dctx st3 m3 Em3). rewrite Eo3.
      forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)).
      sep_apply (data_at_data_at_ Tsh (Tstruct _ZSTD_outBuffer_s noattr)).
      sep_apply (data_at_data_at_ Tsh (Tstruct _ZSTD_inBuffer_s noattr)). cancel. }
    assert (Hk: kept = nullval -> Zlength s = 0).
    { intros ->. match goal with H14: (if EqDec_val _ _ then _ else _) = Int.zero |- _ =>
        destruct (EqDec_val nullval nullval) as [_|Hn]; [| contradiction];
        destruct (Z.eq_dec (Zlength s) 0); [auto | exfalso; exact (Int.one_not_zero H14)] end. }
    (* once, while the harness has no DDict: ZSTD_createDDict(kept, n), refMultipleDDicts on or off, refDDict *)
    forward_if (EX t: int,
      PROP (t <> Int.zero -> q = nullval)
      LOCAL (temp _t'24 (Vint t); temp _kept kept; temp _dst pd; temp _src ps; temp _cap (Vlong (Int64.repr c));
             temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q;
             lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
             lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st3; malloc_token Ews (tarray tuchar c) pd;
           data_at Ews (tarray tuchar c) oc pd; malloc_token Ews (tarray tuchar (Zlength s)) ps;
           data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           if eq_dec kept nullval then emp
           else (malloc_token Ews (tarray tuchar (Zlength s)) kept * data_at Ews (tarray tuchar (Zlength s)) (zbytes s) kept);
           data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
           data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
           ddict_hold DD gv q dd; dd_tok q dd; TT))%assert.
    { (* the test ddict == NULL *)
      destruct (eq_dec q nullval) as [Eq|Nq]; [subst q; entailer! |].
      unfold ddict_hold at 1. destruct (eq_dec q nullval); [contradiction |]. unfold ddict_res.
      entailer!. }
    { forward_call tt. Intros u4. forward.
      Exists (Int.repr (if Int.eq (Int.and (Int.repr u4) (Int.repr 1)) Int.zero then 0 else 1)).
      entailer!. destruct (Int.eq (Int.repr (Z.land u4 1)) Int.zero); reflexivity. }
    { forward. Exists Int.zero. entailer!. }
    Intros t.
    forward_if (EX st5: dctx_st, EX q5: val, EX dd5: ddict_st,
      PROP (rf_inv m q5 dd5 st5; rf_ok st5; is_pointer_or_null q5)
      LOCAL (temp _dst pd; temp _src ps; temp _cap (Vlong (Int64.repr c));
             temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; temp _ddict q5;
             lvar _out (Tstruct _ZSTD_outBuffer_s noattr) v_out; lvar _in (Tstruct _ZSTD_inBuffer_s noattr) v_in;
             lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem; lvar _now tulong v_now; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st5; malloc_token Ews (tarray tuchar c) pd;
           data_at Ews (tarray tuchar c) oc pd; malloc_token Ews (tarray tuchar (Zlength s)) ps;
           data_at Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (gv _count_alloc, (gv _count_free, v_now)) v_mem;
           data_at Tsh (Tstruct _ZSTD_outBuffer_s noattr) vo v_out; data_at Tsh (Tstruct _ZSTD_inBuffer_s noattr) vi v_in;
           ddict_hold DD gv q5 dd5; dd_tok q5 dd5; TT))%assert.
    { (* the harness makes its DDict *)
      match goal with Ht: t <> Int.zero -> q = nullval, Hn: t <> Int.zero |- _ => specialize (Ht Hn) end.
      subst q. unfold ddict_hold, dd_tok. destruct (eq_dec nullval nullval) as [_|Hc]; [| contradiction].
      assert (Hs0: kept = nullval -> s = nil) by (intros E; apply Zlength_nil_inv; exact (Hk E)).
      sep_apply (kept_to_Z kept s).
      forward_call (kept_wits kept s, gv, Ews, kept, s).
      { cancel. }
      { match goal with Nk: kept <> nullval |- _ =>
          apply buf_ok_tok; [unfold kept_wits; rewrite if_false by exact Nk; left; reflexivity | auto | lia |
                             apply isptr_of; auto] end. }
      Intros vret. destruct vret as [q2 dd2]. cbn [fst snd] in *.
      forward_call tt. Intros u5.
      forward_call (gv, dctx, st3, ZSTD_d_refMultipleDDicts, Z.land u5 1).
      { assert (E5: Z.land u5 1 = u5 mod 2) by exact (Z.land_ones u5 1 ltac:(lia)).
        pose proof (Z.mod_pos_bound u5 2 ltac:(lia)).
        split; [simpl; tauto |]. split; [rewrite E5; rep_lia | destruct Hin3 as (_ & Hb3 & _); exact Hb3]. }
      Intros vret. destruct vret as [r4 st4]. cbn [fst snd] in *.
      assert (Hk4: ZSTD_d_refMultipleDDicts <> ZSTD_d_stableOutBuffer)
        by (unfold ZSTD_d_refMultipleDDicts, ZSTD_d_stableOutBuffer; lia).
      match goal with Ha: after_stage _ st3 r4 st4 |- _ =>
        pose proof (rf_setpar m nullval dd st3 _ _ r4 st4 Hk4 Hin3 Ha) as Hi4; pose proof (rf_ok_setpar st3 _ _ r4 st4 Hok3 Ha) as Ho4 end.
      assert (Hdd2: rf_dd q2 dd2).
      { intros Nq. match goal with Hr: dd_ref dd2 = _ |- _ => rewrite Hr end.
        destruct (eq_dec kept nullval); [left; reflexivity |].
        destruct (Zlength s =? 0) eqn:Ez; [| left; reflexivity]. right. exists kept.
        apply Z.eqb_eq in Ez. split; [reflexivity |]. split.
        - match goal with Hb: dd_bytes dd2 = s |- _ => rewrite Hb end. apply Zlength_nil_inv; exact Ez.
        - apply isptr_of; auto. }
      destruct (rf_new_ddict m dd q2 dd2 st4 Hi4 Hdd2) as [Hi4' Hn4].
      sep_apply (dd_res_null DD m gv Ews dd st4 Hi4).
      sep_apply (dd_new_drop DD gv q2 dd2).
      forward_call (gv, dctx, st4, q2, dd2, Ews).
      { pose proof Hi4 as (_ & Hb4 & _). pose proof (rf_set_small m q2 dd2 st4 Hi4').
        repeat split; auto. }
      Intros vret. destruct vret as [r5 st5]. cbn [fst snd] in *.
      match goal with Ha: after_stage _ st4 r5 st5 |- _ => pose proof (rf_ref m q2 dd2 st4 r5 st5 Hi4' Hn4 Ha) as Hi5;
        pose proof (rf_ok_ref q2 dd2 st4 r5 st5 Ho4 Ha) as Ho5 end.
      sep_apply (dd_res_null_e DD m gv Ews dd st4 Hi4).
      sep_apply (dd_hold_new DD gv kept s q2 dd2 ltac:(auto) ltac:(assumption) ltac:(assumption)).
      Exists st5 q2 dd2. entailer!. }
    { forward. Exists st3 q dd. entailer!. }
    Intros st5 q5 dd5.
    (* ZSTD_DCtx_setParameter(dctx, ZSTD_d_windowLogMax, any int) *)
    forward_call tt. Intros w.
    forward_call (gv, dctx, st5, ZSTD_d_windowLogMax, Int.signed (Int.repr w)).
    { entailer!. rewrite Int.repr_signed. reflexivity. }
    { pose proof (Int.signed_range (Int.repr w)).
      match goal with Hi: rf_inv _ _ _ st5 |- _ => pose proof Hi as (_ & Hb5 & _) end.
      repeat split; try lia; auto; simpl; tauto. }
    Intros vret. destruct vret as [r6 st6]. cbn [fst snd] in *.
    assert (Hk6: ZSTD_d_windowLogMax <> ZSTD_d_stableOutBuffer) by (unfold ZSTD_d_windowLogMax, ZSTD_d_stableOutBuffer; lia).
    match goal with Ha: after_stage _ st5 r6 st6, Hi: rf_inv _ _ _ st5, Ho: rf_ok st5 |- _ =>
      pose proof (rf_setpar m q5 dd5 st5 _ _ r6 st6 Hk6 Hi Ha) as Hi6; pose proof (rf_ok_setpar st5 _ _ r6 st6 Ho Ha) as Ho6 end.
    (* free(src); free(dst) *)
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength s)) (zbytes s) ps).
    sep_apply (@free_pre CompSpecs (tarray tuchar (Zlength s)) ps Hps').
    forward_call (tarray tuchar (Zlength s), ps, gv).
    sep_apply (data_at_data_at_ Ews (tarray tuchar c) oc pd).
    sep_apply (@free_pre CompSpecs (tarray tuchar c) pd Hpd').
    forward_call (tarray tuchar c, pd, gv).
    (* do ... while (nondet_u8() != 0) *)
    forward_call tt. Intros u7.
    sep_apply (data_at_data_at_ Tsh (Tstruct _ZSTD_outBuffer_s noattr)).
    sep_apply (data_at_data_at_ Tsh (Tstruct _ZSTD_inBuffer_s noattr)).
    forward_if.
    * forward. Exists st6 q5 dd5. entailer!.
    * forward. Exists st6 q5 dd5. entailer!. }
  (* the end: freeing the context gives the counter back with nothing given out; the check; the DDict *)
  Intros st q dd.
  forward_call (gv, dctx, Some st).
  match goal with H: rf_inv _ _ _ _ |- _ => destruct (rf_mem_some _ _ _ _ H) as (m' & Em & Ea & Ef & Eo) end.
  unfold cm_back. rewrite Em. unfold m, the_cm in Eo; cbn [cm_opaque] in Eo. rewrite Eo.
  simpl CM. sep_apply (count_zero v_now (cm_bound m')). unfold cm_funs. Intros.
  change Alloc_res_free.CompSpecs with CompSpecs.
  forward.
  forward_call (Int.one).
  forward_call (gv, q, if eq_dec q nullval then None else Some dd).
  { sep_apply (dd_hold_free DD gv q dd). cancel. }
  { destruct (eq_dec q nullval); auto. }
  forward.
  sep_apply (data_at_data_at_ Tsh tulong). sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)).
  cancel.
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the counting allocator, as an allocator
   a context may be given (CMem.cm_alloc_spec, cm_free_spec with count_cm), and the frames kit's copy_of, any_bytes
   and upto (laws_common.h) *)
Definition Hs : funspecs :=
  [(_count_alloc, @cm_alloc_spec count_cm); (_count_free, @cm_free_spec count_cm);
   @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma find_cons {A} i (a: ident * A) l :
  initial_world.find_id i (a :: l) = if Pos.eqb i (fst a) then Some (snd a) else initial_world.find_id i l.
Proof.
  destruct a as [j x]. simpl. destruct (Memory.EqDec_ident i j) as [E|Hne].
  - subst. rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec i j); [contradiction | reflexivity].
Qed.

Ltac find_steps :=
  repeat (rewrite find_cons;
          match goal with |- context [Pos.eqb ?i (fst ?a)] =>
            let b := eval lazy in (Pos.eqb i (fst a)) in change (Pos.eqb i (fst a)) with b end;
          cbv beta iota).

Lemma Gprog_cons DC DD : Gprog (@Specs_api DC DD count_cm) Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (@Specs_api DC DD count_cm ++ [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
     (_count_alloc, @cm_alloc_spec count_cm); (_count_free, @cm_free_spec count_cm);
     @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs;
     @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec;
     main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (@Specs_api DC DD count_cm) Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Specs_api. cbn [app].
  repeat destruct Hi as [E|Hi];
    try match type of E with ?a = (i, fs) =>
      replace i with (fst a) by (rewrite E; reflexivity);
      replace fs with (snd a) by (rewrite E; reflexivity) end;
    try contradiction;
    find_steps; reflexivity.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma mtg_none (V: varspecs) i : ~ In i (map fst V) -> Maps.PTree.get i (make_tycontext_g V []) = None.
Proof.
  unfold make_tycontext_g. induction V as [|[k t] V IH]; simpl; intros Hn.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); [subst; tauto |]. apply IH. tauto.
Qed.

(* no function name of Gprog is a global variable of the program *)
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (@Specs_api DC DD count_cm) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (@Specs_api DC DD count_cm) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

(* a body proved in a smaller context of functions (same global variables) holds in Gprog *)
Lemma body_in_Gprog DC DD (G: funspecs) f spec :
  semax_body Vprog G f spec ->
  (forall i fs, initial_world.find_id i G = Some fs ->
     initial_world.find_id i (Gprog (@Specs_api DC DD count_cm) Hs) = Some fs) ->
  semax_body Vprog (Gprog (@Specs_api DC DD count_cm) Hs) f spec.
Proof.
  intros B HG.
  eapply semax_body_subsumption; [exact B |].
  apply tycontext_sub_i99. split; intro i.
  - rewrite (make_tycontext_g_find Vprog G i).
    rewrite (make_tycontext_g_find Vprog (Gprog (@Specs_api DC DD count_cm) Hs) i).
    destruct (initial_world.find_id i G) as [fs|] eqn:E.
    + rewrite (HG i fs E). apply sub_option_refl.
    + destruct (initial_world.find_id i (Gprog (@Specs_api DC DD count_cm) Hs)) as [fs'|] eqn:E'.
      * rewrite mtg_none; [exact Logic.I |].
        apply (Gprog_not_var DC DD i).
        apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
      * apply sub_option_refl.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i G) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (HG i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

Theorem res_free_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    @dc_cm_ok DC count_cm -> exists Hs, HarnessOK (@Specs_api DC DD count_cm) Hs.
Proof.
  intros DC DD DCM. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]]].
    + (* count_alloc *)
      exists f_count_alloc. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD G_alloc); [exact body_count_alloc |].
      apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* count_free *)
      exists f_count_free. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD G_alloc); [exact body_count_free |].
      apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* copy_of *)
      exists f_copy_of. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_copy_of = Zstd.proof.harness.frames.FSpecs.f_copy_of) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ (@Zstd.proof.harness.frames.FSpecs.G_copy_of CompSpecs)).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* any_bytes *)
      exists f_any_bytes. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_any_bytes = Zstd.proof.harness.frames.FSpecs.f_any_bytes) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ (@Zstd.proof.harness.frames.FSpecs.G_any_bytes CompSpecs)).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* upto *)
      exists f_upto. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_upto = Zstd.proof.harness.frames.FSpecs.f_upto) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_upto).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD (G0 DC DD)); [exact (body_main_G0 DC DD DCM) |].
      apply G0_in_Gprog.
Qed.
