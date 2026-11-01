(* SideOK of the unit valid_dict_api: the body of vd_stream (the harness's streaming loop, which calls the API)
   satisfies vd_stream_spec in G0, like main. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WriterOK_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDSBody3.

Lemma VDS_Externals_eq : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VDS_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VDS_G0_in DC DD WG WDS i fs : initial_world.find_id i (VD_G0 DC DD) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompressStream;
     _gp_assert; _exact_copy; _within_stream; _stall_error; _vd_chunk]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VDS_Externals_eq.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Lemma VDS_id_in_list_true i l : In i l -> id_in_list i l = true.
Proof.
  induction l as [|j l IH]; simpl; [contradiction | ].
  intros [<- | H]; [rewrite Pos.eqb_refl; reflexivity | rewrite IH by auto; apply orb_true_r].
Qed.

Lemma VDS_vars_funs_b DC DD WG WDS :
  forallb (fun i => negb (id_in_list i (map fst (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS))))) (map fst Vprog) = true.
Proof. unfold G0, Imports. rewrite VDS_Externals_eq. vm_compute. reflexivity. Qed.

Lemma VDS_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VDS_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VDS_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) = None.
Proof.
  intros H. apply VDS_tyc_g_nil_in in H. apply VDS_find_id_not_in.
  pose proof (VDS_vars_funs_b DC DD WG WDS) as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply VDS_id_in_list_true in Hin. rewrite Hin in B. discriminate.
Qed.

Lemma VDS_body_G0 DC DD WG WDS :
  semax_body Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) f_vd_stream (vd_stream_spec DC DD).
Proof.
  eapply semax_body_subsumption; [apply (VD_body DC DD) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VDS_make_tycontext_g_find Vprog (VD_G0 DC DD) i).
    destruct (initial_world.find_id i (VD_G0 DC DD)) as [fs|] eqn:E.
    * rewrite (VDS_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) i).
      rewrite (VDS_G0_in DC DD WG WDS i fs E). apply sub_option_refl.
    * (* G0 is kept abstract during the rewrite: unifying it with the [] of the left side would compute it *)
      remember (G0 (Specs_api DC DD) (wtop_specs DC DD WG WDS)) as G eqn:HG.
      rewrite (VDS_make_tycontext_g_find Vprog G i). subst G.
      destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
      rewrite (VDS_var_not_fun DC DD WG WDS i t EV). reflexivity.
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VD_G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VDS_G0_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

Theorem side_ok_valid_dict_api : SideOK.
Proof.
  intros DC DD WG WDS.
  replace (filter _ _) with [vd_stream_spec DC DD] by reflexivity.
  constructor; [|constructor].
  exists f_vd_stream. split; [reflexivity|]. split; [reflexivity|].
  apply VDS_body_G0.
Qed.
