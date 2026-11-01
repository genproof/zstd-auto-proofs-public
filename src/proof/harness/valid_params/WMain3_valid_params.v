(* MainOK of the unit valid_params: the main of the new harness valid_params (added by a later revision of the contract)
   against API v3. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.WTopSpecs_valid_params.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPBody.
Require Zstd.proof.top.MainPre6.

(* main in the context of the functions it calls (VPBody.VP_body), lifted to G0 *)




Lemma VP_Externals_eq : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VP_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Definition VP_ids0 : list ident :=
  [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompressDCtx; _ZSTD_createDCtx;
   _ZSTD_freeDCtx; _ZSTD_DCtx_setParameter; _ZSTD_DCtx_setFormat; _ZSTD_DCtx_setMaxWindowSize;
   _ZSTD_getFrameHeader_advanced; _ZSTD_decompressStream; _gp_assert; _gp_assume;
   _choose; _choose_in; _exact_copy; _within_oneshot; _stall_error; _w_series;
   _vp_chunk; _vp_windows_within; _vp_blocks_within].

Lemma VP_G0_ids DC DD WG WDS : map fst (VP_G0 DC DD WG WDS) = VP_ids0.
Proof. reflexivity. Qed.

Lemma VP_G0_in DC DD WG WDS i fs : initial_world.find_id i (VP_G0 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i VP_ids0).
  { rewrite <- (VP_G0_ids DC DD WG WDS). apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VP_Externals_eq.
  unfold VP_ids0 in Hin.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Lemma VP_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VP_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VP_vars_funs_b DC DD WG WDS :
  forallb (fun i => negb (id_in_list i (map fst (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS))))) (map fst Vprog) = true.
Proof.
  unfold G0, Imports. rewrite VP_Externals_eq. vm_compute. reflexivity.
Qed.

Lemma VP_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = None.
Proof.
  intros H. apply VP_tyc_g_nil_in in H. apply VP_find_id_not_in.
  pose proof (VP_vars_funs_b DC DD WG WDS) as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

Theorem main_ok3_valid_params : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (VP_body DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VP_make_tycontext_g_find Vprog (VP_G0 DC DD WG WDS) i).
    destruct (initial_world.find_id i (VP_G0 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VP_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) i).
      rewrite (VP_G0_in DC DD WG WDS i fs E). apply sub_option_refl.
    * rewrite (VP_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) i) at 1.
      destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
      rewrite (VP_var_not_fun DC DD WG WDS i t EV). reflexivity.
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VP_G0 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VP_G0_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
