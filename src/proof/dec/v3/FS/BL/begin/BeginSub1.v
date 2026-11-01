(* FS3-bl BEGIN: ZSTD_decompressBegin_usingDict's API specification from B's. *)
Require Export Zstd.proof.dec.v3.FS.BL.begin.BeginFacts.
Local Open Scope logic.

Section CM_BeginSub1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bgf_dict_dr (p: val) (b: list Z) : dictref :=
  {| dr_src := DSRef p; dr_raw := false; dr_once := false; dr_bytes := b |}.

Definition bgf_dict_od (p: val) (b: list Z) (dm: dict_model) : option bldict :=
  Some {| bd_eb := p; bd_b := b; bd_ds0 := Zlength b - Zlength (dm_content dm); bd_id := dm_id dm; bd_ox := None;
          bd_g0 := 0; bd_de0 := nullval |}.

Definition bgf_dict_fs (fs: fstate) (f: Z) (p: val) (b: list Z) (dm: dict_model) : fstate :=
  fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) p) (offset_val (Zlength b) p) 0
    (dm_id dm).

Lemma BR_begin_dict (st: dctx_st) (p: val) (b: list Z) (ores: option (dstate * Z)) (dm: dict_model) (fs: fstate)
    (hb: list val) (x2: bool) (lxb: list Z) :
  par_ok (dc_par st) -> isptr p -> Zlength b <= 2 ^ 63 - 1 -> bytes_ok b -> ld_rel b ores ->
  dict_auto_c b ores = Some dm -> cold01 fs -> Zlength hb = 18 -> 0 < Zlength b ->
  BR (dc_par st) (bl_begin st (Some (bgf_dict_dr p b))) (bgf_dict_fs fs (dp_fmt (dc_par st)) p b dm)
     (TInit None (mk_tstate (dm_state dm) x2 lxb)) hb.
Proof.
  intros Hpar Hp Hlen Hok Hld E Hc Hhb Hpos.
  pose proof (bgf_dict_auto_c_suffix _ _ _ E) as Hsuf.
  pose proof (bgf_dict_auto_c_id _ _ _ E) as Hid.
  apply (BR_begin st (Some (bgf_dict_dr p b)) (bgf_dict_od p b dm)); auto;
    try (destruct p; try contradiction; reflexivity).
  - unfold bd_wf, bgf_dict_od; simpl. left.
    split; [apply bgf_suffix_len; exact Hsuf|]. split; [exact Hlen|]. split; [exact Hok|].
    split; [exact Hp|]. split; [rewrite Hid; apply bgf_dict_id_of_range; exact Hok|].
    split; [left; reflexivity | split; [left; reflexivity | intros _; exact Hpos]].
  - intros dm' E'. unfold dictref_model, bgf_dict_dr in E'; simpl in E'.
    rewrite (ld_rel_auto_some _ _ _ Hld E') in E. inversion E; reflexivity.
  - intros dm' E'. unfold dictref_model, bgf_dict_dr in E'; simpl in E'.
    rewrite (ld_rel_auto_some _ _ _ Hld E') in E. inversion E; subst dm'.
    unfold bd_idz, bd_content, bgf_dict_od; simpl. split; [reflexivity|].
    exists nil. simpl. apply bgf_suffix_sublist. exact Hsuf.
  - simpl. repeat split; reflexivity.
Qed.

Lemma begin_sub1 (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) : TABS_OK TABS ->
  funspec_sub (snd (ZSTD_decompressBegin_usingDict_spec3 TABS))
              (snd (ZSTD_decompressBegin_usingDict_aspec (DC3x DENT TABS SR BR))).
Proof.
  intros HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[W gv] d] st] sh] p] b] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x at 1, DC3_of. unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
  (* Begin clears dc_ex: the exact relation of the context before is not needed *)
  match goal with Hx: ex_on3 _ _ _ |- _ => clear Hx end.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (Zlength (sf_hbuf (c3_s k)) = 18) as Hhb. { unfold bgf_rest, sgroup. entailer!. }
  assert_PROP (isptr p) as Hp. { rewrite (data_at_isptr sh (tarray tuchar (Zlength b))). entailer!. }
  assert (Hpr: c3_par k = dc_par st) by (destruct H6 as [_ [Hq _]]; exact Hq).
  (* the tables' contents are forgotten: the precondition of Begin only asks for their cells *)
  eapply derives_trans;
    [apply andp_derives; [apply derives_refl |
       sep_apply (tabs_rep_uninit TABS HT gv d (c3_tabs k)); apply derives_refl] |].
  Intros lxb.
  Exists (gv, d, c3_fs k, W, sh, p, b, dp_fmt (c3_par k), lxb) (bgf_rest DENT gv d k).
  simpl.
  rewrite if_false by (intros E; subst p; exact Hp).
  apply andp_right.
  - unfold LOCALx, argsassert2assert; simpl. entailer!.
    { destruct H10 as [Hf _]. exact Hf. }
    unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto. cancel.
  - apply prop_right. intros rho'.
    unfold local, lift1; simpl. normalize.
    rename fs' into r. rename x into ores.
    unfold usingdict_model.
    destruct (EqDec_val p nullval) as [E|_]; [subst p; contradiction|].
    try (destruct (eq_dec p nullval) as [E|_]; [subst p; contradiction|]).
    destruct (Zlength b =? 0) eqn:Ez.
    + (* no dictionary *)
      Intros. Intros x2. subst r.
      change (TABS gv d None (mk_tstate (dm_state no_dict) x2 lxb))
        with (tabs_rep TABS gv d (TInit None (mk_tstate dstate_init x2 lxb))).
      assert (HBR: forall ba, Some (bl_begin st None) = Some ba ->
         BR (c3_par k) ba (fs_begin3 (c3_fs k) (dp_fmt (c3_par k))) (TInit None (mk_tstate dstate_init x2 lxb))
           (sf_hbuf (c3_s k))).
      { intros ba Hba. inversion Hba; subst. rewrite Hpr.
        apply (BR_begin st None None); simpl; auto; try (rewrite <- Hpr; auto).
        - intros dm E. inversion E; reflexivity.
        - intros dm E. inversion E; subst. split; [reflexivity | exists nil; reflexivity]. }
      sep_apply (DC3_begin DENT TABS SR gv d st k (fs_begin3 (c3_fs k) (dp_fmt (c3_par k)))
                   (TInit None (mk_tstate dstate_init x2 lxb))
                   (Some (bl_begin st None)) H6 H1 H9 H10 (fun _ => eq_refl) HBR (base_rel3_fp_ok st k H6)).
      Exists 0 (set_ex (set_bl st (Some (bl_begin st None))) false).
      entailer!.
    + destruct (dict_auto_c b ores) as [dm|] eqn:Ed.
      * Intros. Intros x2. subst r.
        fold (bgf_dict_fs (c3_fs k) (dp_fmt (c3_par k)) p b dm).
        change (TABS gv d None (mk_tstate (dm_state dm) x2 lxb))
          with (tabs_rep TABS gv d (TInit None (mk_tstate (dm_state dm) x2 lxb))).
        assert (HBR: forall ba, Some (bl_begin st (Some (bgf_dict_dr p b))) = Some ba ->
          BR (c3_par k) ba (bgf_dict_fs (c3_fs k) (dp_fmt (c3_par k)) p b dm)
            (TInit None (mk_tstate (dm_state dm) x2 lxb)) (sf_hbuf (c3_s k))).
        { intros ba Hba. inversion Hba; subst. rewrite Hpr. apply (BR_begin_dict st p b ores); auto;
          try (pose proof (Zlength_nonneg b); apply Z.eqb_neq in Ez; lia).
          rewrite <- Hpr; auto. }
        assert (Hc: cold01 (bgf_dict_fs (c3_fs k) (dp_fmt (c3_par k)) p b dm)) by (unfold cold01; simpl; auto).
        sep_apply (DC3_begin DENT TABS SR gv d st k (bgf_dict_fs (c3_fs k) (dp_fmt (c3_par k)) p b dm)
                     (TInit None (mk_tstate (dm_state dm) x2 lxb)) (Some (bl_begin st (Some (bgf_dict_dr p b))))
                     H6 H1 Hc H10 (fun _ => eq_refl) HBR (base_rel3_fp_ok st k H6)).
        Exists 0 (set_ex (set_bl st (Some (bl_begin st (Some (bgf_dict_dr p b))))) false).
        entailer!.
      * Intros fs'. rename H15 into Herr. rename H17 into Hcold.
        sep_apply (tabs_rep_none TABS gv d lxb).
        assert (Hc: cold01 fs') by (unfold cold01 in *; rewrite Hcold; auto).
        assert (HBR: forall ba, (None: option Spec_api6.blabs) = Some ba -> BR (c3_par k) ba fs' (TUninit lxb) (sf_hbuf (c3_s k)))
          by (intros; discriminate).
        assert (Hfp': fp_ok (fs_fParams fs')).
        { match goal with Hf: fs_fParams fs' = _ |- _ => rewrite Hf; exact (base_rel3_fp_ok st k H6) end. }
        sep_apply (DC3_begin DENT TABS SR gv d st k fs' (TUninit lxb) None H6 H1 Hc H10
                     (fun Hn => False_ind _ (Hn eq_refl)) HBR Hfp').
        Exists r (set_ex (set_bl st None) false).
        entailer!.
        right. split; [destruct Herr; auto | split; [| reflexivity]].
        apply (ld_rel_auto_none b ores); auto.
Qed.

End CM_BeginSub1_1.
