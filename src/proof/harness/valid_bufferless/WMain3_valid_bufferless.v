(* MainOK of the unit valid_bufferless: the main of the new harness valid_bufferless (added by a later revision of the
   contract) against API v3. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_bufferless.WTopSpecs_valid_bufferless.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Inv.
Require Import Zstd.proof.harness.valid_bufferless.VBL3Dev.
Require Zstd.proof.top.MainPre6.

(* main is proved in VBLDev.v in the context VL_G1 of the functions it calls; every entry of VL_G1 is found
   unchanged in G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS) *)

Lemma VL_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VL_G1_in DC DD WG WDS i fs : initial_world.find_id i (VL_G1 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_createDCtx; _ZSTD_freeDCtx;
     _ZSTD_createDDict; _ZSTD_freeDDict; _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict;
     _ZSTD_decompressBegin_usingDDict; _ZSTD_nextSrcSizeToDecompress; _ZSTD_nextInputType; _ZSTD_decompressContinue;
     _gp_assert; _choose; _exact_copy; _within_oneshot; _w_dict; _w_series]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VLD_Externals.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Definition VL_fun_ids : list ident := ltac:(
  let l := eval lazy in (map fst (G0 (Specs_api (fun _ _ _ => emp) (fun _ _ _ => emp))
                                     (wtop_specs (fun _ _ _ => emp) (fun _ _ _ => emp) (fun _ => emp) (fun _ _ => True)))) in
  exact l).

Lemma VL_G0_ids DC DD WG WDS : map fst (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = VL_fun_ids.
Proof. reflexivity. Qed.

Lemma VL_vars_funs_b : forallb (fun i => negb (id_in_list i VL_fun_ids)) (map fst Vprog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VL_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VL_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VL_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = None.
Proof.
  intros H. apply VL_tyc_g_nil_in in H. apply VL_find_id_not_in. rewrite VL_G0_ids.
  pose proof VL_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

(* A name that is not a function of G keeps its type of the global variables: stated for an abstract G, so that
   the rewriting never compares the concrete function list with the empty one (which unfolds the specifications). *)
Lemma VL_sub_none (V: varspecs) (G: funspecs) i :
  (forall t, Maps.PTree.get i (make_tycontext_g V nil) = Some t -> initial_world.find_id i G = None) ->
  tycontext.sub_option (Maps.PTree.get i (make_tycontext_g V nil)) (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. rewrite (VL_make_tycontext_g_find V G i).
  destruct (Maps.PTree.get i (make_tycontext_g V nil)) as [t|] eqn:EV; [|exact Logic.I].
  rewrite (H t eq_refl). reflexivity.
Qed.

Theorem main_ok3_valid_bufferless : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (VL_body_main DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VL_make_tycontext_g_find Vprog (VL_G1 DC DD WG WDS) i).
    destruct (initial_world.find_id i (VL_G1 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VL_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) i).
      rewrite (VL_G1_in DC DD WG WDS i fs E). apply sub_option_refl.
    * apply VL_sub_none. intros t EV. exact (VL_var_not_fun DC DD WG WDS i t EV).
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VL_G1 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VL_G1_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
