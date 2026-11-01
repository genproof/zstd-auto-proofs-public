(* FS3-bl BEGIN: ZSTD_decompressBegin_usingDDict's API specification from B's. *)
Require Export Zstd.proof.dec.v3.FS.BL.begin.BeginFacts.
Local Open Scope logic.

Section CM_BeginSub2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bgf_ddict_od (x: ddx) (buf: val) : option bldict :=
  Some {| bd_eb := buf; bd_b := dx_bytes x; bd_ds0 := 0; bd_id := dict_id_of (dx_bytes x); bd_ox := Some x;
          bd_g0 := if ddx_copied x then 1 else 0; bd_de0 := ddx_end x buf |}.

Definition bgf_ddict_fs (fs: fstate) (f: Z) (cold: val) (x: ddx) (buf: val) : fstate :=
  fs_set_dictEnd
    (fs_with_dict (fs_set_cold (fs_begin3 fs f) cold) buf (ddx_end x buf)
       (if ddx_copied x then 1 else 0) (if dx_raw x then 0 else dict_id_of (dx_bytes x)))
    (ddx_end x buf).

(* buf: the DDict's content, at a pointer or (the DDict without content) at NULL *)
Lemma BR_begin_ddict (st: dctx_st) (q: val) (dd: ddict_st) (x: ddx) (buf: val) (fs: fstate) (cold: val)
    (hb: list val) (lxb: list Z) :
  par_ok (dc_par st) -> dx_bytes x = dd_bytes dd -> dx_raw x = false -> ld_rel (dx_bytes x) (dx_ld x) ->
  (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) ->
  Zlength (dx_bytes x) <= 2 ^ 63 - 1 -> bytes_ok (dx_bytes x) ->
  (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) ->
  (cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)) -> Zlength hb = 18 ->
  x = dd_x q dd -> buf = dd_buf dd ->
  BR (dc_par st) (bl_begin st (Some (ddict_ref q dd))) (bgf_ddict_fs fs (dp_fmt (dc_par st)) cold x buf)
     (TInit (Some x) (mk_tstate (ddx_state x) false lxb)) hb.
Proof.
  intros Hpar Hb Hraw Hld Hbuf Hlen Hok Hcp Hcold Hhb Hx Hbu.
  apply (BR_begin st (Some (ddict_ref q dd)) (bgf_ddict_od x buf)); auto.
  - unfold bgf_ddict_fs, bgf_ddict_od; simpl. rewrite Hraw. reflexivity.
  - unfold bd_wf, bgf_ddict_od; simpl. destruct Hbuf as [Hbuf | (Hn & Hr & Hnil)].
    + left.
      split; [pose proof (Zlength_nonneg (dx_bytes x)); lia|]. split; [exact Hlen|]. split; [exact Hok|].
      split; [exact Hbuf|]. split; [apply bgf_dict_id_of_range; exact Hok|].
      split; [destruct (ddx_copied x); [right; split; auto | left; auto]|].
      split; [right; apply ddx_end_ptr; exact Hbuf | intros Hn; exfalso; destruct buf; inversion Hbuf; discriminate Hn].
    + right. subst buf. unfold bd_nil, ddx_copied; simpl. rewrite Hr, Hnil. repeat split; reflexivity.
  - unfold bgf_ddict_fs, bgf_ddict_od; simpl. destruct Hbuf as [Hbuf | (-> & _)]; [|reflexivity].
    rewrite bd_off_ptr by exact Hbuf. rewrite ?ddx_end_ptr, ?isptr_offset_val_zero by exact Hbuf. reflexivity.
  - unfold bgf_ddict_fs, bgf_ddict_od; simpl. destruct Hbuf as [Hbuf | (-> & _)]; [|reflexivity].
    rewrite bd_off_ptr by exact Hbuf. rewrite ?ddx_end_ptr, ?isptr_offset_val_zero by exact Hbuf. reflexivity.
  - intros dm E. unfold dictref_model, ddict_ref in E; simpl in E. rewrite <- Hb in E.
    assert (Hm: ddx_model x = Some dm) by (apply ddx_model_some; [exact Hld | rewrite Hraw; exact E]).
    destruct (bgf_ddx_model_facts x dm Hm) as [_ [Hs _]]. exact Hs.
  - intros dm E. unfold dictref_model, ddict_ref in E; simpl in E. rewrite <- Hb in E.
    assert (Hm: ddx_model x = Some dm) by (apply ddx_model_some; [exact Hld | rewrite Hraw; exact E]).
    destruct (bgf_ddx_model_facts x dm Hm) as [Hi [_ [pre Hp]]]. rewrite Hraw in Hi.
    unfold bd_idz, bd_content, bgf_ddict_od; simpl. split; [exact Hi|].
    exists pre. rewrite sublist_same by auto. exact Hp.
  - subst x buf. unfold bgf_ddict_od, ddict_ref, ddx_copied; simpl.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    destruct (dd_xref dd); reflexivity.
Qed.

(* a DDict's struct gives its pointer's validity (copy of DDictLayout3.ddict_rep_at_valid) *)
Lemma bgf_DD3_vp (DENT: dent_pred) gv q dd :
  DD3_of DENT gv q dd |-- DD3_of DENT gv q dd && valid_pointer q.
Proof.
  apply andp_right; [apply derives_refl|].
  unfold DD3_of, ddict_rep_at, ddict_struct. Intros.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
  change (dx_q (dd_x q dd)) with q. repeat apply sepcon_valid_pointer1; apply derives_refl.
Qed.

Lemma bgf_DD3_fold_vp (DENT: dent_pred) gv q dd :
  ddict_struct (dd_x q dd) (dd_buf dd) * DENT gv q (ddx_ent (dd_x q dd)) * ddict_mem (dd_x q dd) (dd_buf dd) *
  ddict_pad q |-- DD3_of DENT gv q dd && valid_pointer q.
Proof. eapply derives_trans; [| apply bgf_DD3_vp]. unfold DD3_of, ddict_rep_at. change (dx_q (dd_x q dd)) with q. cancel. Qed.

Lemma begin_sub2 (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) : TABS_OK TABS ->
  funspec_sub (snd (ZSTD_decompressBegin_usingDDict_spec3 DENT TABS))
              (snd (ZSTD_decompressBegin_usingDDict_aspec (DC3x DENT TABS SR BR) (DD3x DENT))).
Proof.
  intros HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[gv d] st] q] odd] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  unfold DC3x at 1, DC3_of. unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
  (* Begin clears dc_ex: the exact relation of the context before is not needed *)
  match goal with Hx: ex_on3 _ _ _ |- _ => clear Hx end.
  rewrite ctx_rep3_split. Intros.
  assert_PROP (Zlength (sf_hbuf (c3_s k)) = 18) as Hhb. { unfold bgf_rest, sgroup. entailer!. }
  assert (Hpr: c3_par k = dc_par st) by (destruct H3 as [_ [Hp _]]; exact Hp).
  (* the tables' contents are forgotten: the precondition of Begin only asks for their cells *)
  eapply derives_trans;
    [apply andp_derives; [apply derives_refl |
       sep_apply (tabs_rep_uninit TABS HT gv d (c3_tabs k)); apply derives_refl] |].
  Intros lxb.
  destruct odd as [dd|].
  - unfold DD3x at 1, DD3_of.
    set (x := dd_x q dd). set (buf := dd_buf dd).
    assert_PROP ((isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ bytes_ok (dx_bytes x) /\
                 ld_rel (dx_bytes x) (dx_ld x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x))) as Hst.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    destruct Hst as [Hbuf [Hlen [Hok [Hld Hcp]]]].
    Exists (gv, d, c3_fs k, @nil ptr_witness, Some x, buf, dp_fmt (c3_par k), lxb)
      (bgf_rest DENT gv d k * ddict_pad (dx_q x)).
    simpl.
    apply andp_right.
    + unfold LOCALx, argsassert2assert; simpl. entailer!.
      { destruct H7 as [Hf _]. exact Hf. }
      unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto.
      unfold ddict_rep_at. change (dx_q x) with q. cancel.
    + apply prop_right. intros rho'.
      unfold local, lift1; simpl. normalize.
      change (dict_id_of (dd_bytes dd)) with (if dx_raw x then 0 else dict_id_of (dx_bytes x)).
      fold (bgf_ddict_fs (c3_fs k) (dp_fmt (c3_par k)) x0 x buf).
      change (TABS gv d (Some x) (mk_tstate (ddx_state x) false lxb))
        with (tabs_rep TABS gv d (TInit (Some x) (mk_tstate (ddx_state x) false lxb))).
      assert (HBR: forall ba, Some (bl_begin st (Some (ddict_ref q dd))) = Some ba ->
        BR (c3_par k) ba (bgf_ddict_fs (c3_fs k) (dp_fmt (c3_par k)) x0 x buf)
          (TInit (Some x) (mk_tstate (ddx_state x) false lxb)) (sf_hbuf (c3_s k))).
      { intros ba Hba. inversion Hba; subst. rewrite Hpr. apply BR_begin_ddict; auto. rewrite <- Hpr; auto. }
      assert (Hc: cold01 (bgf_ddict_fs (c3_fs k) (dp_fmt (c3_par k)) x0 x buf)) by (unfold cold01; simpl; auto).
      sep_apply (DC3_begin DENT TABS SR gv d st k (bgf_ddict_fs (c3_fs k) (dp_fmt (c3_par k)) x0 x buf)
                   (TInit (Some x) (mk_tstate (ddx_state x) false lxb)) (Some (bl_begin st (Some (ddict_ref q dd)))) H3 H1 Hc H7
                   (fun _ => eq_refl) HBR (base_rel3_fp_ok st k H3)).
      unfold x, buf. sep_apply (bgf_DD3_fold_vp DENT gv q dd).
      unfold DD3x. entailer!.
  - subst q.
    Exists (gv, d, c3_fs k, @nil ptr_witness, @None ddx, nullval, dp_fmt (c3_par k), lxb) (bgf_rest DENT gv d k).
    simpl.
    apply andp_right.
    + unfold LOCALx, argsassert2assert; simpl. entailer!.
      { destruct H7 as [Hf _]. exact Hf. }
      unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto. cancel.
    + apply prop_right. intros rho'.
      unfold local, lift1; simpl. normalize.
      change (TABS gv d None (tstate_begin lxb)) with (tabs_rep TABS gv d (TInit None (tstate_begin lxb))).
      assert (HBR: forall ba, Some (bl_begin st None) = Some ba ->
         BR (c3_par k) ba (fs_begin3 (c3_fs k) (dp_fmt (c3_par k))) (TInit None (tstate_begin lxb)) (sf_hbuf (c3_s k))).
      { intros ba Hba. inversion Hba; subst. rewrite Hpr.
        apply (BR_begin st None None); simpl; auto; try (rewrite <- Hpr; auto).
        - intros dm E. inversion E; reflexivity.
        - intros dm E. inversion E; subst. split; [reflexivity | exists nil; reflexivity]. }
      sep_apply (DC3_begin DENT TABS SR gv d st k (fs_begin3 (c3_fs k) (dp_fmt (c3_par k))) (TInit None (tstate_begin lxb))
                   (Some (bl_begin st None)) H3 H1 H6 H7 (fun _ => eq_refl) HBR (base_rel3_fp_ok st k H3)).
      entailer!.
Qed.

End CM_BeginSub2_1.
