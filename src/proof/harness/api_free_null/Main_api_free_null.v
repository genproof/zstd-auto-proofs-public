(* The harness obligation of api_free_null (harness/api_free_null.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6), main satisfies its specification (the harness has no other function).
   main frees a null context, a null stream and a null dictionary: the free specifications of Spec_api6
   cover a null pointer (their option argument None) and return 0, which is not an error code. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_free_null.HOK_api_free_null.
Require Zstd.proof.top.MainPre6.

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
    (QPprog_vars Zstd.contracts.api_free_null.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_free_null.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_free_null.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* main calls only these functions *)
Definition G0 : funspecs :=
  [ZSTD_isError_spec; ZSTD_freeDCtx_spec DC; ZSTD_freeDStream_spec DC; ZSTD_freeDDict_spec DD; gp_assert_spec].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_free_null.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  (* the three calls with a null pointer: each returns 0, which is not an error code *)
  forward_call (gv, nullval, @None dctx_st); [cancel |].
  forward_call 0.
  change (is_error_code 0) with false.
  forward_if (PROP () LOCAL (temp _t'3 (Vint Int.one); gvars gv) SEP (mem_mgr gv; zstd_globals gv; TT; has_ext tt)).
  { forward_call (gv, nullval, @None dctx_st); [cancel |].
    forward_call 0.
    change (is_error_code 0) with false.
    forward. entailer!. }
  { exfalso. match goal with H: _ |- _ => first [discriminate H | apply H; reflexivity] end. }
  forward_if (PROP () LOCAL (temp _t'6 (Vint Int.one); gvars gv) SEP (mem_mgr gv; zstd_globals gv; TT; has_ext tt)).
  { forward_call (gv, nullval, @None ddict_st); [cancel |].
    forward_call 0.
    change (is_error_code 0) with false.
    forward. entailer!. }
  { exfalso. match goal with H: _ |- _ => first [discriminate H | apply H; reflexivity] end. }
  forward_call Int.one.
  forward.
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) [] ---------- *)

Lemma Externals_eq : Externals = [gp_assert_spec].
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

Lemma Gprog_cons DC DD : Gprog (Specs_api DC DD) [] =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [gp_assert_spec; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) [])) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) [])) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem api_free_null_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + (* the function list is kept abstract while rewriting: comparing the concrete Gprog with the empty list
         by computation unfolds every specification *)
      remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP.
      rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
      rewrite (make_tycontext_g_find Vprog GP i).
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * subst GP. rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * destruct (initial_world.find_id i GP) as [fs'|] eqn:E'.
        -- rewrite mtg_none; [exact Logic.I |].
           apply (Gprog_not_var DC DD i). subst GP.
           apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
        -- apply sub_option_refl.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
