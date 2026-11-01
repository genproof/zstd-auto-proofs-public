(* The harness obligation of res_memory_oneshot (harness/res_memory_oneshot.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6) whose contexts let a law read their allocator's state (Spec_api6.dc_cm_ok), the
   counting allocator (count_alloc, count_free: Alloc_res_memory_oneshot.v), the helpers upto and any_bytes
   (laws_common.h, proved once in the frames kit) and main satisfy their specifications.

   The allocator's bound is the estimate itself: the context is created with cm_bound = ZSTD_estimateDCtxSize()
   (CMem.dctx_size), and every allocation through the allocator is made only within the bound
   (CMem.cm_alloc_spec), so the peak the allocator records stays below it (count_CM).  main's loop keeps the
   context in its initial state: ZSTD_decompressDCtx on a context without a dictionary leaves it as it was
   (after_decode, after_use), errors included.  At the check, and at the early returns of the loop, main takes the
   allocator's state out of the context (dc_cm_ok): to read the peak, and to give its local struct count back. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.res_memory_oneshot.Alloc_res_memory_oneshot.
Require Export Zstd.proof.harness.res_memory_oneshot.HOK_res_memory_oneshot.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.ApiAfterKit.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.res_memory_oneshot.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.res_memory_oneshot.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.res_memory_oneshot.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @data_at_ CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

(* ---------- the buffer witnesses of a one-shot call: the malloc_tokens of its two buffers ---------- *)

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* a malloc'ed buffer (also of 0 bytes) is weakly valid at both ends, given its token *)
Lemma buf_ok_tok W sh n p : In (pw_token Ews (tarray tuchar n) p) W -> readable_share sh -> 0 <= n -> isptr p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold buf_ok.
  eapply derives_trans; [apply sepcon_derives; [apply (pws_in W _ Hin) | apply derives_refl] |].
  simpl pw_pred.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block Zstd.units.Zstd.CS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
      by (eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]).
    apply andp_right; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma vp_frame (P Q: mpred) p : ((P && valid_pointer p) * Q) |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* a context without a dictionary has no dictionary resources *)
Lemma res_none_i DD0 gv sh m ex :
  emp |-- dict_res DD0 gv sh (dc_dict (set_ex (dctx_init_m m) ex)) *
          set_res DD0 gv sh (dc_set (set_ex (dctx_init_m m) ex)) (dc_dict (set_ex (dctx_init_m m) ex)).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_none_e DD0 gv sh m ex :
  dict_res DD0 gv sh (dc_dict (set_ex (dctx_init_m m) ex)) *
  set_res DD0 gv sh (dc_set (set_ex (dctx_init_m m) ex)) (dc_dict (set_ex (dctx_init_m m) ex)) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* a one-shot decoding leaves a new context with its own allocator as it was, except for the flag of a frame
   decoded before (dc_ex), which it clears *)
Lemma dctx_init_after m ex st' :
  after_decode (after_use (set_ex (dctx_init_m m) ex)) st' (dc_dict (set_ex (dctx_init_m m) ex)) ->
  st' = set_ex (dctx_init_m m) false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.


(* the ZSTD_customMem main passes to ZSTD_createDCtx_advancedP, at the decoder's compspecs: the struct is the
   same in both (three pointers) *)
Lemma cmem_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p |--
  @data_at Zstd.units.Zstd.CS sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct ___gp_ZSTD_customMem noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

Lemma cmem_of_Z sh (a b c: val) p :
  @data_at Zstd.units.Zstd.CS sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p |--
  @data_at CompSpecs sh (Tstruct ___gp_ZSTD_customMem noattr) (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs Zstd.units.Zstd.CS
    (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS) sh (Tstruct ___gp_ZSTD_customMem noattr)
    (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  rewrite E. apply derives_refl.
Qed.

(* the allocator main gives the context: count_alloc, count_free, its struct count, and the estimate as bound *)
Definition the_cm (gv: globals) (o: val) : cmem :=
  {| cm_alloc := gv _count_alloc; cm_free := gv _count_free; cm_opaque := o; cm_bound := dctx_size |}.

(* main's struct count, set to zero, is the allocator's state with nothing given out *)
Lemma count_init_dctx o :
  data_at Tsh (Tstruct _count noattr) (Vlong (Int64.repr 0), Vlong (Int64.repr 0)) o |--
  @CM count_cm o dctx_size 0.
Proof. apply count_CM_init. rewrite dctx_size_eq. lia. Qed.

Lemma cm_funs_fold gv o :
  (func_ptr' cm_free_spec (gv _count_free) * func_ptr' cm_alloc_spec (gv _count_alloc)) |--
  @cm_funs count_cm (the_cm gv o).
Proof. unfold cm_funs; simpl. rewrite sepcon_comm. apply derives_refl. Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Hypothesis DCM : @dc_cm_ok DC count_cm.

(* the allocator's struct count, taken out of a context of its own allocator: to give it back to main's frame
   (the context is then dropped) *)
Lemma dc_count_out gv d st m : dc_mem st = Some m ->
  DC gv d st |-- data_at_ Tsh (Tstruct _count noattr) (cm_opaque m) * TT.
Proof.
  intros Hm. sep_apply (DCM gv d st m Hm). Intros h.
  simpl CM. unfold count_CM. Intros peak.
  sep_apply (data_at_data_at_ Tsh (Tstruct _count noattr)). cancel.
Qed.

(* ... and to read the peak it recorded, which is within the bound; then the context is whole again *)
Lemma dc_count_read gv d st m : dc_mem st = Some m ->
  DC gv d st |-- EX h: Z, EX peak: Z,
    !! (0 <= h /\ 0 <= peak <= Int64.max_unsigned /\ peak <= cm_bound m /\ (cm_bound m <= Int64.max_unsigned -> h <= peak)) &&
    (data_at Tsh (Tstruct _count noattr) (Vlong (Int64.repr h), Vlong (Int64.repr peak)) (cm_opaque m) *
     (data_at Tsh (Tstruct _count noattr) (Vlong (Int64.repr h), Vlong (Int64.repr peak)) (cm_opaque m) -*
      DC gv d st) * TT).
Proof.
  intros Hm. sep_apply (DCM gv d st m Hm). Intros h.
  simpl CM. unfold count_CM at 1. Intros peak. Exists h peak.
  rewrite prop_true_andp by auto.
  assert (Hw: (count_CM (cm_opaque m) (cm_bound m) h -* DC gv d st) |--
              (data_at Tsh (Tstruct _count noattr) (Vlong (Int64.repr h), Vlong (Int64.repr peak)) (cm_opaque m) -*
               DC gv d st)).
  { apply wand_sepcon_adjoint. rewrite sepcon_comm.
    eapply derives_trans; [| apply modus_ponens_wand].
    apply sepcon_derives; [| apply derives_refl].
    unfold count_CM. Exists peak. entailer!. }
  sep_apply Hw. cancel.
Qed.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_decompressDCtx_spec DC DD; ZSTD_createDCtx_advancedP_spec DC; ZSTD_freeDCtx_spec DC;
   ZSTD_estimateDCtxSize_spec;
   nondet_u8_spec; gp_assert_spec;
   (_count_alloc, cm_alloc_spec); (_count_free, cm_free_spec);
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.res_memory_oneshot.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward. forward. forward.
  make_func_ptr _count_alloc.
  forward.
  make_func_ptr _count_free.
  forward.
  forward.
  change (Int.signed (Int.repr 0)) with 0.
  sep_apply (cmem_to_Z Tsh (gv _count_alloc) (gv _count_free) v_count__1 v_mem).
  sep_apply (count_init_dctx v_count__1).
  sep_apply (cm_funs_fold gv v_count__1).
  assert_PROP (isptr v_count__1) as Hco by entailer!.
  forward_call (gv, Tsh, v_mem, the_cm gv v_count__1).
  { simpl cm_opaque; simpl cm_bound. cancel. }
  Intros dctx.
  set (m := the_cm gv v_count__1).
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { (* no context: the allocator's state and the ZSTD_customMem go back to main's frame *)
    subst dctx.
    forward_if; [| contradiction].
    unfold m, cm_funs, cmem_val, the_cm; cbn [cm_alloc cm_free cm_opaque cm_bound CM count_cm].
    unfold count_CM. Intros peak.
    sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_count__1 v_mem).
    forward.
    sep_apply (data_at_data_at_ Tsh t_count). sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)).
    unfold t_count. cancel. }
  forward_if.
  { contradiction. }
  Intros. sep_apply (drop_vp (DC gv dctx (dctx_init_m m)) dctx).
  change (dctx_init_m m) with (set_ex (dctx_init_m m) true).
  forward_loop (PROP () LOCAL (temp _dctx dctx; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
                               lvar _count__1 (Tstruct _count noattr) v_count__1; gvars gv)
                SEP (EX ex: bool, DC gv dctx (set_ex (dctx_init_m m) ex); data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (cmem_val m) v_mem;
                     mem_mgr gv; zstd_globals gv; TT))
    break: (PROP () LOCAL (temp _dctx dctx; lvar _mem (Tstruct ___gp_ZSTD_customMem noattr) v_mem;
                           lvar _count__1 (Tstruct _count noattr) v_count__1; gvars gv)
            SEP (EX ex: bool, DC gv dctx (set_ex (dctx_init_m m) ex); data_at Tsh (Tstruct ___gp_ZSTD_customMem noattr) (cmem_val m) v_mem;
                 mem_mgr gv; zstd_globals gv; TT)).
  { Exists true. entailer!. }
  { (* one iteration *)
    Intros ex.
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
    (* src or dst NULL: the run ends; the allocator's struct count goes back to main's frame *)
    destruct (eq_dec ps nullval) as [Hps|Hps].
    { subst ps. Intros. apply semax_if_seq. forward_if; [| contradiction]. forward.
      forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
      sep_apply (dc_count_out gv dctx (set_ex (dctx_init_m m) ex) m eq_refl).
      unfold m, cmem_val, the_cm; cbn [cm_alloc cm_free cm_opaque].
      sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_count__1 v_mem).
      forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)). cancel. }
    destruct (eq_dec pd nullval) as [Hpd|Hpd].
    { subst pd. Intros. apply semax_if_seq. forward_if; [contradiction |]. forward.
      change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
      forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
      sep_apply (dc_count_out gv dctx (set_ex (dctx_init_m m) ex) m eq_refl).
      unfold m, cmem_val, the_cm; cbn [cm_alloc cm_free cm_opaque].
      sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_count__1 v_mem).
      forward.
      sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)). cancel. }
    Intros.
    assert_PROP (isptr pd) as Hpd' by entailer!.
    assert_PROP (isptr ps) as Hps' by entailer!.
    apply semax_if_seq. forward_if; [contradiction |].
    destruct pd as [| | | | | b i]; try contradiction. forward.
    forward_if; [discriminate |].
    set (pd := Vptr b i) in *. subst n.
    (* the buffers at the decoder's compspecs *)
    sep_apply (to_Z Ews (Zlength s) (zbytes s) ps).
    sep_apply (to_Z_ Ews c pd).
    sep_apply (tok_to_Z Ews (Zlength s) ps).
    sep_apply (tok_to_Z Ews c pd).
    (* the decoding leaves the context in its state, whatever the result *)
    sep_apply (pws_fold (tarray tuchar (Zlength s)) ps (tarray tuchar c) pd).
    sep_apply (res_none_i DD gv Ews m ex).
    forward_call ([pw_token Ews (tarray tuchar (Zlength s)) ps; pw_token Ews (tarray tuchar c) pd],
                  gv, dctx, set_ex (dctx_init_m m) ex, Ews, Ews, pd, c, Ews, ps, s).
    { cancel. }
    { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
    Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
    api_init.
    match goal with H4: after_decode _ _ _ |- _ => apply dctx_init_after in H4; subst st' end.
    sep_apply (res_none_e DD gv Ews m ex).
    sep_apply pws_unfold.
    unfold mbuf; rewrite if_false by auto.
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar c) out pd).
    (* free the two buffers *)
    sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) (zbytes s) ps).
    sep_apply (of_Z_ Ews (Zlength s) ps).
    sep_apply (tok_of_Z Ews (Zlength s) ps).
    sep_apply (@free_pre CompSpecs (tarray tuchar (Zlength s)) ps Hps').
    forward_call (tarray tuchar (Zlength s), ps, gv).
    sep_apply (of_Z_ Ews c pd).
    sep_apply (tok_of_Z Ews c pd).
    sep_apply (@free_pre CompSpecs (tarray tuchar c) pd Hpd').
    forward_call (tarray tuchar c, pd, gv).
    (* do ... while (nondet_u8() != 0) *)
    forward_call tt. Intros u2.
    forward_if.
    * forward. Exists false. entailer!.
    * forward. Exists false. entailer!. }
  (* the check: the peak the allocator recorded is within its bound, the estimate *)
  Intros ex.
  forward_call tt.
  sep_apply (dc_count_read gv dctx (set_ex (dctx_init_m m) ex) m eq_refl).
  Intros h peak.
  unfold m, the_cm in *; cbn [cm_opaque cm_bound] in *.
  forward.
  forward_call Int.one.
  { entailer!. rewrite dctx_size_eq in *. simpl.
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
  (* the context is whole again; freeing it gives the allocator's state back, with nothing given out *)
  sep_apply modus_ponens_wand.
  forward_call (gv, dctx, Some (set_ex (dctx_init_m (the_cm gv v_count__1)) ex)).
  unfold cm_back, cm_funs, cmem_val, set_ex, dctx_init_m, the_cm; cbn [dc_mem cm_alloc cm_free cm_opaque cm_bound CM count_cm].
  unfold count_CM. Intros peak'.
  sep_apply (cmem_of_Z Tsh (gv _count_alloc) (gv _count_free) v_count__1 v_mem).
  forward.
  sep_apply (data_at_data_at_ Tsh t_count). sep_apply (data_at_data_at_ Tsh (Tstruct ___gp_ZSTD_customMem noattr)).
  unfold t_count. cancel.
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the counting allocator, as an allocator
   a context may be given (CMem.cm_alloc_spec, cm_free_spec with count_cm), and the frames kit's any_bytes and
   upto (laws_common.h) *)
Definition Hs : funspecs :=
  [(_count_alloc, @cm_alloc_spec count_cm); (_count_free, @cm_free_spec count_cm);
   @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
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
  (@Specs_api DC DD count_cm ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
     (_count_alloc, @cm_alloc_spec count_cm); (_count_free, @cm_free_spec count_cm);
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

Theorem res_memory_oneshot_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    @dc_cm_ok DC count_cm -> exists Hs, HarnessOK (@Specs_api DC DD count_cm) Hs.
Proof.
  intros DC DD DCM. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
    + (* count_alloc *)
      exists f_count_alloc. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD G_alloc); [exact body_count_alloc |].
      apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* count_free *)
      exists f_count_free. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD G_alloc); [exact body_count_free |].
      apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
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
