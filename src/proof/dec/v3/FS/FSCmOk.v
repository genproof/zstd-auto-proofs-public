(* A context with its own allocator holds that allocator's state (Spec_api6.dc_cm_ok): DC3_of's concrete state has
   the abstract allocator (base_rel3's mem_rel3), whose state CM with the bytes given out sits in the streaming
   group's mgroup; a law may take it out between two calls (to read it) and put it back unchanged (the wand rebuilds
   the context with the same concrete state). *)
Require Export Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CmOk.
Context {CMI: cmem_preds}.

(* the context's allocator state, taken out and put back *)
Lemma ctx_rep3_cm (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) (m: cmem) :
  sf_mem (c3_s k) = Some m ->
  ctx_rep3 DENT TABS gv p k |--
    CM (cm_opaque m) (cm_bound m) (sf_given (c3_s k)) *
    (CM (cm_opaque m) (cm_bound m) (sf_given (c3_s k)) -* ctx_rep3 DENT TABS gv p k).
Proof.
  intros Hm.
  unfold ctx_rep3, ctx_body3, sgroup, mgroup. rewrite Hm. unfold cm_have.
  Intros. rewrite <- !sepcon_assoc.
  match goal with |- ?A * CM ?o ?b ?h * ?B |-- _ => rewrite (sepcon_comm (A * CM o b h) B), <- sepcon_assoc end.
  rewrite (sepcon_comm _ (CM _ _ _)). apply sepcon_derives; [apply derives_refl |].
  rewrite <- wand_sepcon_adjoint. rewrite <- Hm.
  unfold ctx_rep3, ctx_body3, sgroup, mgroup. rewrite Hm. unfold cm_have.
  apply andp_right; [apply prop_right; tauto | cancel].
Qed.

Lemma DC3_cm_ok (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR: blrel) :
  dc_cm_ok (DC3_of DENT TABS SR BR).
Proof.
  intros gv p st m Hst. unfold DC3_of at 1. Intros k.
  rename H into Hb, H0 into Hsr, H1 into Hbr.
  destruct (base_rel3_mem _ _ Hb) as [Hm _]. rewrite Hst in Hm.
  Exists (sf_given (c3_s k)).
  eapply derives_trans; [apply (ctx_rep3_cm DENT TABS gv p k m Hm) |].
  apply sepcon_derives; [apply derives_refl |].
  apply wand_derives; [apply derives_refl |].
  unfold DC3_of. Exists k. rewrite prop_true_andp by tauto. apply derives_refl.
Qed.

End CmOk.
