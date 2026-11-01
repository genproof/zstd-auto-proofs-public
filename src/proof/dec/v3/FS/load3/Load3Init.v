(* FS3 load3: ZSTD_initDStream_usingDict = ZSTD_DCtx_reset(session only) + ZSTD_DCtx_loadDictionary *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Lift Zstd.proof.dec.v3.FS.load3.Load3Split.
Local Open Scope logic.

(* do { body } while (0): the loop invariant is the current precondition *)
Ltac dw0 tac :=
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end;
  [ apply ENTAIL_refl | tac | forward; apply ENTAIL_refl | abbreviate_semax ].
Ltac dw0_skip := dw0 ltac:(forward; apply ENTAIL_refl).
Ltac dw0_if0 := dw0 ltac:(forward_if; [contradiction | forward; apply ENTAIL_refl]).

Section CM_Load3Init_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Init.
Variables (DENT : dent_pred) (TABS : tabs_pred) (SR : srel3) (BR : blrel).

Definition G_initdict : funspecs :=
  [ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR); ZSTD_DCtx_loadDictionary_spec (DC3x DENT TABS SR BR);
   ERR_isError_spec; ZSTD_startingInputLength_spec3].

Lemma body_initDStream_usingDict3_small :
  body_ok G_initdict (ZSTD_initDStream_usingDict_aspec (DC3x DENT TABS SR BR)).
Proof.
  exists f_ZSTD_initDStream_usingDict; split; [reflexivity | split; [reflexivity | ]].
  unfold G_initdict.
  start_function.
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { entailer!. } { forward. entailer!. }
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (PROP () LOCAL (gvars gv; temp _zds d; temp _dict p; temp _dictSize (Vlong (Int64.repr (Zlength b))))
                           SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d (set_ex (set_ss st ss_init) false);
                                data_at sh (tarray tuchar (Zlength b)) (zbytes b) p)) end.
  { entailer!. }
  { forward_call (gv, d, st, ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with Hr: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ Hr) as [-> ->] end.
    forward_call 0.
    replace (is_error_code 0) with false by reflexivity.
    forward_if. { exfalso; auto. }
    forward. entailer!. }
  set (dr := {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}).
  match goal with |- semax _ ?P _ _ =>
    forward_loop P break: (EX st2: dctx_st,
      PROP (st2 = set_dict (set_ex (set_ss st ss_init) false) (Some dr)) LOCAL (gvars gv; temp _zds d)
      SEP (pws_pred W; mem_mgr gv; zstd_globals gv; DC3x DENT TABS SR BR gv d st2;
           data_at sh (tarray tuchar (Zlength b)) (zbytes b) p))%assert end.
  { entailer!. }
  { forward_call (W, gv, d, set_ex (set_ss st ss_init) false, sh, p, b).
    Intros vret. destruct vret as [r st2]. simpl fst in *; simpl snd in *.
    (* before any stream, with the default allocator: the load's result on the context *)
    match goal with Hl: after_stage _ _ _ _ |- _ =>
      apply after_stage_init in Hl; [destruct Hl as [om [Hom HL]] | reflexivity] end.
    match goal with Hm: dc_mem st = None |- _ => rename Hm into Hmem end.
    assert (Eom: om = None) by (simpl in Hom; rewrite Hmem in Hom; destruct om; [contradiction | reflexivity]).
    subst om.
    replace (set_mem (set_ex (set_ss st ss_init) false) None) with (set_ex (set_ss st ss_init) false) in HL
      by (unfold set_mem, set_ex, set_ss; simpl; rewrite Hmem; reflexivity).
    forward_call r.
    destruct HL as [[-> ->] | [He [-> Hw]]].
    - replace (is_error_code 0) with false by reflexivity.
      forward_if. { exfalso; auto. }
      forward. Exists (set_dict (set_ex (set_ss st ss_init) false) (Some dr)). entailer!. apply derives_refl.
    - rewrite He.
      forward_if; [ | exfalso; apply Int.one_not_zero; assumption ].
      dw0_skip. dw0_if0. dw0_skip. dw0_skip.
      forward.
      Exists r (set_dict (set_ex (set_ss st ss_init) false) None).
      entailer!.
      right. split; [exact He |]. split; [reflexivity |]. simpl in Hw. destruct Hw as [[_ Hw] | Hw]; auto. }
  Intros st2. subst st2.
  unfold DC3x, DC3_of. Intros k.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (par_ok (c3_par k)) as Hpar by (unfold ctx_rest3k; sep_apply (ctx_rest3_par TABS gv d); entailer!).
  match goal with Hb0: base_rel3 _ _ |- _ => rename Hb0 into Hb end.
  assert (Hpk: c3_par k = dc_par st) by (destruct Hb as [_ [Hp _]]; exact Hp).
  unfold cfg_fmt.
  forward.
  forward_call (dp_fmt (c3_par k)).
  { destruct Hpar as [Hf _]; exact Hf. }
  forward.
  Exists (starting_len (fmt_mg (dp_fmt (c3_par k)))) (set_dict (set_ex (set_ss st ss_init) false) (Some dr)).
  unfold DC3x, DC3_of. Exists k.
  rewrite ctx_rep3_split. unfold cfg_fmt.
  entailer!.
  rewrite Hpk. unfold fmt_mg. split; [| left; split; reflexivity].
  unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX. destruct (dp_fmt (dc_par st) =? 1); rep_lia.
Qed.

End Init.

Lemma body_initDStream_usingDict3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_initDStream_usingDict_aspec (DC3x DENT TABS SR BR)).
Proof.
  intros DENT TABS SR BR HD HT.
  apply (load3_lift (G_initdict DENT TABS SR BR)); [unfold G_initdict; load3_in | apply body_initDStream_usingDict3_small].
Qed.

End CM_Load3Init_1.
