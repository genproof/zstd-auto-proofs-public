(* FS3 load3: ZSTD_initDStream_usingDDict = ZSTD_DCtx_reset(session only) + ZSTD_DCtx_refDDict (API specifications) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split Zstd.proof.dec.v3.FS.load3.Load3Rdd.
Local Open Scope logic.

(* do { body } while (0): the loop invariant is the current precondition *)
Ltac dw0 tac :=
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end;
  [ apply ENTAIL_refl | tac | forward; apply ENTAIL_refl | abbreviate_semax ].
Ltac dw0_skip := dw0 ltac:(forward; apply ENTAIL_refl).
Ltac dw0_if0 := dw0 ltac:(forward_if; [contradiction | forward; apply ENTAIL_refl]).

Section CM_Load3InitDD_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma refddict_result_par s st' r q dd : refddict_result s st' r q dd -> dc_par st' = dc_par s.
Proof. intros [[_ ->] | [_ [_ ->]]]; reflexivity. Qed.

Lemma refddict_result_r s st' r q dd : refddict_result s st' r q dd -> r = 0 \/ is_error_code r = true.
Proof. intros [[-> _] | [_ [H _]]]; auto. Qed.

Section InitDD.
Variables (DENT : dent_pred) (TABS : tabs_pred) (SR : srel3) (BR : blrel).

Definition G_initddict : funspecs :=
  [ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR); ZSTD_DCtx_refDDict_spec (DC3x DENT TABS SR BR) (DD3x DENT);
   ERR_isError_spec; ZSTD_startingInputLength_spec3].

Lemma body_initDStream_usingDDict3_small :
  body_ok G_initddict (ZSTD_initDStream_usingDDict_aspec (DC3x DENT TABS SR BR) (DD3x DENT)).
Proof.
  exists f_ZSTD_initDStream_usingDDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_initddict.
  start_function.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. } { forward. entailer!. }
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (PROP () LOCAL (gvars gv; temp _dctx d; temp _ddict q)
                           SEP (mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d (set_ex (set_ss st ss_init) false);
                                DD3x DENT gv q dd; dict_res (DD3x DENT) gv shk (dc_dict st);
                                set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))) end.
  { entailer!. }
  { forward_call (gv, d, st, ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with Hr: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ Hr) as [-> ->] end.
    forward_call 0.
    replace (is_error_code 0) with false by reflexivity.
    forward_if. { exfalso; auto. }
    forward. entailer!. }
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (EX st2: dctx_st, EX r0: Z,
      PROP (refddict_result (set_ex (set_ss st ss_init) false) st2 r0 q dd; r0 = 0) LOCAL (gvars gv; temp _dctx d)
      SEP (mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d st2; DD3x DENT gv q dd && valid_pointer q;
           dict_res (DD3x DENT) gv shk (dc_dict st); set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st)))%assert end.
  { entailer!. }
  { change (dict_res (DD3x DENT) gv shk (dc_dict st)) with (dict_res (DD3x DENT) gv shk (dc_dict (set_ex (set_ss st ss_init) false))).
    change (set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))
      with (set_res (DD3x DENT) gv shk (dc_set (set_ex (set_ss st ss_init) false)) (dc_dict (set_ex (set_ss st ss_init) false))).
    assert (Hqn: q <> nullval) by (intros E; subst q; contradiction).
    replace (DD3x DENT gv q dd) with (if eq_dec q nullval then emp else DD3x DENT gv q dd)
      by (rewrite if_false by auto; reflexivity).
    forward_call (gv, d, set_ex (set_ss st ss_init) false, q, dd, shk).
    Intros vret. destruct vret as [r0 st2]. simpl fst in *; simpl snd in *.
    rewrite if_false by auto.
    (* before any stream, with the default allocator: ZSTD_DCtx_refDDict's result on the context *)
    match goal with Hl: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in Hl; [| reflexivity]; rewrite if_false in Hl by auto;
      destruct Hl as [om [Hom HL]] end.
    match goal with Hm: dc_mem st = None |- _ => rename Hm into Hmem end.
    assert (Eom: om = None) by (simpl in Hom; rewrite Hmem in Hom; destruct om; [contradiction | reflexivity]).
    subst om.
    replace (set_mem (set_ex (set_ss st ss_init) false) None) with (set_ex (set_ss st ss_init) false) in HL
      by (unfold set_mem, set_ex, set_ss; simpl; rewrite Hmem; reflexivity).
    forward_call r0.
    destruct (refddict_result_r _ _ _ _ _ HL) as [-> | He].
    - replace (is_error_code 0) with false by reflexivity.
      forward_if. { exfalso; auto. }
      forward. Exists st2 0. entailer!. apply derives_refl.
    - rewrite He.
      forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
      dw0_skip. dw0_if0. dw0_skip. dw0_skip.
      forward.
      Exists r0 st2 r0.
      entailer!; [rewrite He; auto | apply derives_refl]. }
  Intros st2 r0. subst r0.
  match goal with Hl: refddict_result _ _ _ _ _ |- _ => rename Hl into HL end.
  pose proof (refddict_result_par _ _ _ _ _ HL) as Hp2. simpl in Hp2.
  unfold DC3x, DC3_of. Intros k.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (par_ok (c3_par k)) as Hpar by (unfold ctx_rest3k; sep_apply (ctx_rest3_par TABS gv d); entailer!).
  match goal with Hb0: base_rel3 _ _ |- _ => rename Hb0 into Hb end.
  assert (Hpk: c3_par k = dc_par st) by (destruct Hb as [_ [Hp _]]; rewrite Hp, Hp2; reflexivity).
  unfold cfg_fmt.
  forward.
  forward_call (dp_fmt (c3_par k)).
  { destruct Hpar as [Hf _]; exact Hf. }
  forward.
  Exists (starting_len (fmt_mg (dp_fmt (c3_par k)))) st2 0.
  unfold DC3x, DC3_of. Exists k.
  rewrite ctx_rep3_split. unfold cfg_fmt.
  entailer!.
  rewrite Hpk. unfold fmt_mg. split; [| reflexivity].
  unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX. destruct (dp_fmt (dc_par st) =? 1); rep_lia.
Qed.

End InitDD.

End CM_Load3InitDD_1.
