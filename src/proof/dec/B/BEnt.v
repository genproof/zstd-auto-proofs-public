(* Group ENT of subtree B (BGroups.v). *)
Require Export Zstd.proof.dec.B.BGroups.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.ent.EntSpecs.
Require Import Zstd.proof.dec.B.ent.body_ent_fsedec Zstd.proof.dec.B.ent.body_ent_generic Zstd.proof.dec.B.ent.body_ent_builddt Zstd.proof.dec.B.ent.body_ent_buildfse Zstd.proof.dec.B.ent.body_ent_ncount Zstd.proof.dec.B.ent.body_ent_wksp Zstd.proof.dec.B.ent.body_ent_readstats Zstd.proof.dec.B.ent.body_ent_wrappers Zstd.proof.dec.B.ent.body_ent_exports.

(* one specification per function of ids_ENT, in that order *)
Definition ENT_specs : funspecs :=
  [ FSE_decode_copy_spec; FSE_initDState_spec; FSE_decodeSymbol_spec; FSE_decodeSymbolFast_spec;
    FSE_readNCount_body_spec; FSE_readNCount_body_default_spec; FSE_readNCount_bmi2_spec; FSE_readNCount_spec;
    HUF_readStats_body_spec; HUF_readStats_body_default_spec; HUF_readStats_wksp_spec;
    FSE_buildDTable_internal_spec; FSE_decompress_usingDTable_generic_spec; FSE_decompress_wksp_body_spec;
    FSE_decompress_wksp_body_default_spec; FSE_decompress_wksp_bmi2_spec;
    ZSTD_buildFSETable_body_spec; ZSTD_buildFSETable_body_default_spec; ZSTD_buildFSETable_spec ].

Lemma ent_nodup : NoDup (map fst Vprog ++ map fst (G_B0 ++ ENT_specs)).
Proof. apply nodupb_ok. vm_compute. reflexivity. Qed.

(* a body proved against G_B0 ++ (some of ENT_specs) holds in the group's context *)
Lemma ent_lift (L: funspecs) (ix: ident * funspec) (f: function) :
  zstd_fun (fst ix) f -> fn_callconv f = callingconvention_of_funspec (snd ix) ->
  incl L ENT_specs -> semax_body Vprog (G_B0 ++ L) f ix -> body_ok (G_B0 ++ ENT_specs) ix.
Proof.
  intros Hf Hc HL Hb. apply body_ok_mono with (G_B0 ++ L).
  - exists f; auto.
  - apply incl_app; [apply incl_appl, incl_refl | apply incl_appr, HL].
  - exact ent_nodup.
Qed.

Ltac ent_incl := intros ? Hx; simpl in Hx; unfold ENT_specs; simpl; tauto.

Ltac ent_body B :=
  lazymatch type of B with
  | semax_body _ (G_B0 ++ ?L) ?f _ => apply (ent_lift L _ f); [reflexivity | reflexivity | ent_incl | exact B]
  | semax_body _ G_B0 ?f _ =>
      apply (ent_lift [] _ f); [reflexivity | reflexivity | ent_incl | rewrite app_nil_r; exact B]
  end.

Lemma ENT_ok : ENT_obligation.
Proof.
  destruct body_ent_fsedec as [B1 [B2 [B3 B4]]].
  destruct body_ent_wrappers as [W1 [W2 [W3 [W4 [W5 [W6 W7]]]]]].
  pose proof (body_ent_builddt fse_wf_slow fse_fast) as B12.
  pose proof (body_ent_buildfse fse_wf_slow fse_fast) as B17.
  pose proof (body_ent_wksp ncount_res_ok fse_wf_slow) as B14.
  pose proof (body_ent_readncount ncount_res_ok) as B8.
  pose proof (body_ent_readstats_wksp huf_model_c huf_res_ok) as B11.
  exists ENT_specs. split; [reflexivity | split].
  - intros x Hx; unfold ENT_exports in Hx; simpl in Hx; unfold ENT_specs; simpl; tauto.
  - repeat apply Forall_cons; try apply Forall_nil.
    + ent_body B1.
    + ent_body B2.
    + ent_body B3.
    + ent_body B4.
    + ent_body body_ent_ncount.
    + ent_body W1.
    + ent_body W2.
    + ent_body B8.
    + ent_body body_ent_readstats.
    + ent_body W5.
    + ent_body B11.
    + ent_body B12.
    + ent_body body_ent_generic.
    + ent_body B14.
    + ent_body W3.
    + ent_body W4.
    + ent_body B17.
    + ent_body W6.
    + ent_body W7.
Qed.
