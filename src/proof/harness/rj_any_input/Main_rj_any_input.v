(* The harness obligation of rj_any_input (harness/rj_any_input.c): for ANY predicates DC, DD of the decoder's
   API (Spec_api6), the helpers upto and any_bytes (laws_common.h, proved once in the frames kit) and main
   satisfy their specifications.

   main's loop keeps one context in its initial state up to dc_ex: ZSTD_decompressDCtx on a context without a
   dictionary leaves it as it was (after_decode, after_use of dctx_init) but for dc_ex, errors included.  Each call's check is the
   first conjunct of oneshot_ok: a result that is not an error code is at most the capacity.  The buffers have
   any size up to PTRDIFF_MAX: this needs the one-shot specifications with sizes up to 2 ^ 63 - 1 (stage 1 of
   the size bounds of Spec_api6). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_any_input.HOK_rj_any_input.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.ApiAfterKit.

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
    (QPprog_vars Zstd.contracts.rj_any_input.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_any_input.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_any_input.whole_prog)).
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
Lemma res_none_i DD0 gv sh ex :
  emp |-- dict_res DD0 gv sh (dc_dict (set_ex dctx_init ex)) *
          set_res DD0 gv sh (dc_set (set_ex dctx_init ex)) (dc_dict (set_ex dctx_init ex)).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_none_e DD0 gv sh ex :
  dict_res DD0 gv sh (dc_dict (set_ex dctx_init ex)) *
  set_res DD0 gv sh (dc_set (set_ex dctx_init ex)) (dc_dict (set_ex dctx_init ex)) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* a one-shot decoding leaves the initial context as it was, except dc_ex (the stream may then read what the
   decoding left behind) *)
Lemma dctx_init_after ex st' :
  after_decode (after_use (set_ex dctx_init ex)) st' (dc_dict (set_ex dctx_init ex)) -> st' = set_ex dctx_init false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompress_spec; ZSTD_decompressDCtx_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC;
   nondet_u8_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_any_input.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call gv.
  Intros dctx.
  destruct (eq_dec dctx nullval) as [Hd|Hd].
  { subst dctx. forward_if; [forward | contradiction]. }
  forward_if.
  { contradiction. }
  Intros. sep_apply (drop_vp (DC gv dctx dctx_init) dctx).
  forward_loop (EX ex: bool, PROP () LOCAL (temp _dctx dctx; gvars gv)
                SEP (DC gv dctx (set_ex dctx_init ex); mem_mgr gv; zstd_globals gv; TT))
    break: (EX ex: bool, PROP () LOCAL (temp _dctx dctx; gvars gv)
            SEP (DC gv dctx (set_ex dctx_init ex); mem_mgr gv; zstd_globals gv; TT)).
  { Exists true. change (set_ex dctx_init true) with dctx_init. entailer!. }
  { (* one iteration *)
    Intros ex.
    forward_call 9223372036854775807.
    Intros n.
    forward_call (gv, n).
    Intros vret. destruct vret as [ps s]. cbn [fst snd] in *.
    forward_call 9223372036854775807.
    Intros c.
    forward_call (tarray tuchar c, gv).
    { simpl. rep_lia. }
    Intros pd.
    unfold FSpecs.mbytes.
    repeat apply -> seq_assoc.
    (* src or dst NULL: the run ends *)
    destruct (eq_dec ps nullval) as [Hps|Hps].
    { subst ps. Intros. apply semax_if_seq. forward_if; [| contradiction]. forward.
      forward_if; [forward | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
    destruct (eq_dec pd nullval) as [Hpd|Hpd].
    { subst pd. Intros. apply semax_if_seq. forward_if; [contradiction |]. forward.
      change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
      forward_if; [forward | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
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
    forward_call tt.
    Intros u.
    (* one of the two decoders: a result that is not an error is at most cap (oneshot_ok's first conjunct) *)
    forward_if (EX r: Z, EX ex1: bool, PROP (0 <= r <= Int64.max_unsigned; is_error_code r = false -> r <= c)
      LOCAL (temp _t'9 (Vlong (Int64.repr r)); temp _dst pd; temp _cap (Vlong (Int64.repr c));
             temp _src ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _dctx dctx; gvars gv)
      SEP (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar c) pd;
           @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps;
           @data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar c) pd;
           @data_at Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
           mem_mgr gv; DC gv dctx (set_ex dctx_init ex1); zstd_globals gv; TT)).
    - sep_apply (pws_fold (tarray tuchar (Zlength s)) ps (tarray tuchar c) pd).
      forward_call ([pw_token Ews (tarray tuchar (Zlength s)) ps; pw_token Ews (tarray tuchar c) pd],
                    gv, Ews, pd, c, Ews, ps, s).
      { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
      Intros vret. destruct vret as [r out]. cbn [fst snd] in *.
      sep_apply pws_unfold.
      unfold mbuf; rewrite if_false by auto.
      sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar c) out pd).
      forward.
      Exists r ex. entailer!.
      match goal with Hk: oneshot_ok _ _ _ _ _ _ |- _ => apply (proj1 Hk); assumption end.
    - sep_apply (pws_fold (tarray tuchar (Zlength s)) ps (tarray tuchar c) pd).
      sep_apply (res_none_i DD gv Ews ex).
      forward_call ([pw_token Ews (tarray tuchar (Zlength s)) ps; pw_token Ews (tarray tuchar c) pd],
                    gv, dctx, set_ex dctx_init ex, Ews, Ews, pd, c, Ews, ps, s).
      { cancel. }
      { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
      Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
      api_init; match goal with H4: after_decode _ _ _ |- _ => apply dctx_init_after in H4; subst st' end.
      sep_apply (res_none_e DD gv Ews ex).
      sep_apply pws_unfold.
      unfold mbuf; rewrite if_false by auto.
      sep_apply (@data_at_data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar c) out pd).
      forward.
      Exists r false. entailer!.
      match goal with Hk: oneshot_dctx _ _ _ _ _ |- _ => apply (proj1 Hk); assumption end.
    - Intros r ex1.
      forward.
      forward_call r.
      (* the check: an error code, or at most cap *)
      forward_if (PROP () LOCAL (temp _t'13 (Vint Int.one); temp _dst pd; temp _src ps; temp _dctx dctx; gvars gv)
        SEP (@malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar c) pd;
             @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) ps;
             @data_at_ Zstd.units.Zstd.CS Ews (tarray tuchar c) pd;
             @data_at Zstd.units.Zstd.CS Ews (tarray tuchar (Zlength s)) (zbytes s) ps;
             mem_mgr gv; DC gv dctx (set_ex dctx_init ex1); zstd_globals gv; TT)).
      + forward. entailer!.
      + forward.
        destruct (is_error_code r) eqn:Er; [exfalso; exact (Int.one_not_zero ltac:(assumption)) |].
        match goal with Hf: false = false -> r <= c |- _ => specialize (Hf eq_refl) end.
        entailer!.
        unfold Int64.cmpu. rewrite ltu_Z by rep_lia.
        replace (c <? r) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      + forward_call Int.one.
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
        * forward. Exists ex1. entailer!.
        * forward. Exists ex1. entailer!. }
  (* after the loop: free the context *)
  Intros ex.
  forward_call (gv, dctx, Some (set_ex dctx_init ex)).
  forward.
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's any_bytes and upto
   (laws_common.h) *)
Definition Hs : funspecs :=
  [@Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec].

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

Lemma Gprog_cons DC DD : Gprog (Specs_api DC DD) Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
                       @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
                       Zstd.proof.harness.frames.FSpecs.upto_spec; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs.
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem rj_any_input_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor]]].
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
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
        remember (Gprog (Specs_api DC DD) Hs) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (make_tycontext_g_find Vprog GP i). subst GP.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (Specs_api DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
