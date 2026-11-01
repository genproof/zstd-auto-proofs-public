(* FS3-bl BEGIN: ZSTD_decompressBegin's API specification from B's. *)
Require Export Zstd.proof.dec.v3.FS.BL.begin.BeginFacts.
Local Open Scope logic.

Section CM_BeginSub0_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma BR_begin_none (st: dctx_st) (fs: fstate) (hb: list val) (lxb: list Z) :
  par_ok (dc_par st) -> cold01 fs -> Zlength hb = 18 ->
  BR (dc_par st) (bl_begin st None) (fs_begin3 fs (dp_fmt (dc_par st))) (TInit None (tstate_begin lxb)) hb.
Proof.
  intros Hpar Hc Hhb.
  apply (BR_begin st None None); simpl; auto.
  - intros dm E. inversion E; reflexivity.
  - intros dm E. inversion E; subst. split; [reflexivity | exists nil; reflexivity].
Qed.

Lemma begin_sub0 (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) : TABS_OK TABS ->
  funspec_sub (snd (ZSTD_decompressBegin_spec3 TABS))
              (snd (ZSTD_decompressBegin_aspec (DC3x DENT TABS SR BR))).
Proof.
  intros HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[gv d] st] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x at 1, DC3_of. unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
  (* Begin clears dc_ex: the exact relation of the context before is not needed *)
  match goal with Hx: ex_on3 _ _ _ |- _ => clear Hx end.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (Zlength (sf_hbuf (c3_s k)) = 18) as Hhb. { unfold bgf_rest, sgroup. entailer!. }
  (* the tables' contents are forgotten: the precondition of Begin only asks for their cells *)
  eapply derives_trans;
    [apply andp_derives; [apply derives_refl | apply sepcon_derives; [apply derives_refl |
       apply sepcon_derives; [| apply derives_refl]; apply sepcon_derives;
       [apply derives_refl | apply (tabs_rep_uninit TABS HT gv d (c3_tabs k))]]] |].
  Intros lxb.
  Exists (gv, d, c3_fs k, dp_fmt (c3_par k), lxb) (cfg_lit d * bgf_rest DENT gv d k).
  simpl.
  apply andp_right.
  unfold LOCALx, argsassert2assert; simpl. entailer!.
  { destruct H6 as [Hf _]. exact Hf. }
  { unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto. cancel. }
  apply prop_right. intros rho'.
  unfold local, lift1; simpl. normalize.
  assert (Hpr: c3_par k = dc_par st) by (destruct H2 as [_ [Hp _]]; exact Hp).
  change (TABS gv d None (tstate_begin lxb)) with (tabs_rep TABS gv d (TInit None (tstate_begin lxb))).
  assert (HBR: forall ba, Some (bl_begin st None) = Some ba ->
     BR (c3_par k) ba (fs_begin3 (c3_fs k) (dp_fmt (c3_par k))) (TInit None (tstate_begin lxb)) (sf_hbuf (c3_s k))).
  { intros ba Hba. inversion Hba; subst. rewrite Hpr. apply BR_begin_none; auto. rewrite <- Hpr; auto. }
  sep_apply (DC3_begin DENT TABS SR gv d st k (fs_begin3 (c3_fs k) (dp_fmt (c3_par k))) (TInit None (tstate_begin lxb))
               (Some (bl_begin st None)) H2 H1 H5 H6 (fun _ => eq_refl) HBR (base_rel3_fp_ok st k H2)).
  cancel.
Qed.

End CM_BeginSub0_1.
