(* valid_params main: main in the context VP_G0 of the functions it calls, from its segments
   (VPSeg*.v); lifted to MainOK's G0 in WMain3_valid_params.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPPre.
Require Import Zstd.proof.harness.valid_params.VPSegA.
Require Import Zstd.proof.harness.valid_params.VPSegB.
Require Import Zstd.proof.harness.valid_params.VPSegC.
Require Import Zstd.proof.harness.valid_params.VPSegDE.

Lemma VP_body (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred)
    (WG: globals -> mpred) (WDS: wdict -> reptype t_wstate -> Prop) :
  (forall gv, InitGPred wvardefs gv |-- WG gv) ->
  semax_body Vprog (VP_G0 DC DD WG WDS) f_main main_spec.
Proof.
intros HWG.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred (sepcon (Zstd.proof.zstd.Globals.zstd_globals gv)
          (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_params__sr)) TT))) _ _ _
          Zstd.contracts.x_valid_params.whole_prog).
4: idtac.
- intros Hgv. eapply derives_trans; [apply (VP_pre gv Hgv) |].
  sep_apply (HWG gv). cancel.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VP_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto].
  sep_apply (create_mem_mgr gv).
  rewrite VP_rest0. change (fn_return f_main) with tint. fold VP_RR.
  change (func_tycontext f_main Vprog (VP_G0 DC DD WG WDS) []) with (VP_Delta DC DD WG WDS).
  eapply semax_pre; [| apply (VP_segA DC DD WG WDS gv v_zfh v_in v_out)].
  { unfold VP_S0. entailer!. }
  intros mode ws b' src dctx HA Hs Hd.
  apply VP_segB. intros p wlim HB.
  apply VP_segC. apply VP_segD. intros st. apply VP_segE.
Qed.
