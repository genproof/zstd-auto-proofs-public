(* valid_dict_api main: mode 0, ZSTD_d_refMultipleDDicts with 2-3 DDicts and streaming, given the
   model fact VDA_m0_model (proved in VDA3M0Model.v) (VDA3Defs.VDA_mode_ok). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Lemmas Zstd.proof.harness.valid_dict_api.VDA3M0Defs.
Require Import Zstd.proof.harness.valid_dict_api.VDA3M0Setup Zstd.proof.harness.valid_dict_api.VDA3M0Dec.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.

(* the facts of mode 0 *)
Lemma M0_facts nd which wds wd ws cap : vda_facts 0 nd which wds wd ws cap ->
  Zlength wds = nd /\ 2 <= nd <= 3 /\ In wd wds /\ Forall dict_facts wds /\
  Forall (fun w => wd_id w <> 0) wds /\ NoDup (map wd_id wds) /\
  series_facts (wd_model wd) ws /\ wseries_wf ws /\ series_dwin (wd_model wd) ws /\
  Forall (fun f => wi_skippable f = true \/ (wi_did_size f <> 0 /\ wi_did f = wd_id wd)) (ws_frames ws) /\
  0 <= cap <= Zlength (ws_content ws) + 16.
Proof.
  intros (_ & Hl & Hnd & _ & _ & Hn & Hdf & _ & Hm0 & _ & _ & Hs & Hw & Hfr & _ & _ & Hc & Hdw).
  destruct (Hm0 eq_refl) as [Hf Hnd'].
  split; [exact Hl|]. split; [exact Hnd|]. split; [apply (nth_error_In _ _ Hn)|].
  split; [exact Hdf|]. split; [eapply Forall_impl; [| exact Hf]; intros w [_ H]; exact H|].
  split; [exact Hnd'|]. split; [exact Hs|]. split; [exact Hw|]. split; [exact Hdw|]. split; [exact (Hfr eq_refl)|]. exact Hc.
Qed.

Lemma vda_mode0_ok DC DD WG WDS : VDA_m0_model -> VDA_mode_ok DC DD WG WDS 0.
Proof.
  intros Hm Espec gv v_dd nd which wds wd ws cap src buf dctx.
  unfold VDA_A. Intros.
  match goal with H: vda_facts _ _ _ _ _ _ _ |- _ =>
    destruct (M0_facts nd which wds wd ws cap H) as (Hl & Hnd & Hin & Hdf & Hid0 & Hid & Hsf & Hwf & Hdw & Hfr & Hc) end.
  match goal with Hf: field_compatible (tarray tuchar (Z.max 1 _)) [] src |- _ => rename Hf into Hfs end.
  match goal with Hf: field_compatible (tarray tuchar (cap + 1 + _)) [] buf |- _ => rename Hf into Hfb end.
  pose proof (Zlength_nonneg (ws_bytes ws)). pose proof (Zlength_nonneg (wd_bytes wd)).
  eapply semax_pre with (P' := M0_P DC WDS gv v_dd nd wds wd ws cap src buf dctx).
  { unfold M0_P, M0_bufs. entailer!.
    sep_apply (M0L_bufs src buf ws wd cap ltac:(lia) Hfs Hfb). cancel. }
  eapply semax_seq'.
  { apply M0_setup_ok; auto; lia. }
  Intros fail l st.
  subst nd.
  eapply semax_post_flipped'.
  { apply (M0_dec_ok DC DD WG WDS Espec gv v_dd wds wd ws cap src buf dctx fail l st); auto. }
  Intros st' ddv.
  Exists st' ddv. unfold M0_F, M0_bufs, VDA_E.
  entailer!.
  rewrite (VB_Zrepeat Ews cap buf).
  sep_apply (VB_final_merge src (Zlength (ws_bytes ws)) buf cap (Zlength (wd_bytes wd)) (Zrepeat Vundef cap)
               (zbytes (wd_bytes wd)) (zbytes (ws_bytes ws)) ltac:(lia) ltac:(lia) ltac:(lia) Hfs Hfb).
  cancel.
Qed.
