(* FS3 streaming, case zdss_load: stable mode, a success on the loaded unit of a skippable frame
   (v2 StreamSeg_load.v load_cont_stable, skippable case). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3StFacts.
Local Open Scope logic.

Section CM_L3StS_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_stable_s : forall a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr got,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = true ->
  sv_fp sv = FP_skip hdr got ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) (o_st a sv opc oc) (ld_u sv (a_ibs a) ipc L)
    rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv2 dl2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) zdss_read (sf_outEnd (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L)))
      sv2 (ipc + L) (opc + rr) oc' dl2.
Proof.
intros a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr got M Hld Hst Hfp Hres Hok.
destruct (ld_st_facts _ _ _ _ _ _ _ _ _ Hld Hst)
  as (Hah&Hpend&Hh0&Hcf&Hring&Hnc&Hnraw&Hoso&Hsz&HPE&HL0&HiL&Hstout&Hls&Hopc&Hloc&Hbsin&Hbnew&Hnew&Hdds).
pose proof Hld as Hld'. destruct Hld' as (Ha&Hi&Hs&HE&HE0&HL&HLE&_).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Halive&_).
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst fp pend ahead.
cbn [fp_inpos] in HPE, HL, HLE.
set (new := sublist ipc (ipc + L) (a_ibs a)) in *.
(* E is the frame's size *)
assert (HEle: E = le_field hdr 4 4).
{ pose proof Hcf as X. destruct X as (_&_&_&_&_&_&_&_&_&Hsz32&Hif).
  cbn [fp_complete] in Hnc. rewrite Hnc in Hif. destruct Hif as [_ Hex].
  rewrite HE in Hex. change (Vlong (Int64.repr (le_field hdr 4 4))) with (vlong (le_field hdr 4 4)) in Hex.
  apply vlong_eq in Hex; [exact Hex|lia|].
  destruct Hcf as (_&_&_&_&_&_&_&_&Hg&_). lia. }
destruct Hres as (Hrr&Hlen'&Hunch&_&Hpost). rewrite Hok in Hpost.
cbn [fp_unit] in Hpost. unfold cont_post in Hpost.
destruct Hpost as (Hr0&Hoc'&ts&Hts&Hcf').
cbn [o_st oa_c] in Hoc'. subst rr oc' tabs'.
assert (HFP: fs_fParams fs' = fs_fParams (c3_fs k0))
  by exact (c_frame_fparams_s _ _ hdr got l dd fs' _ _ _ _ Hcf Hcf').
exists {| sv_fp := FP_skip hdr (le_field hdr 4 4); sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |},
  (dl ++ nil).
replace (opc + 0) with (opc + Zlength (@nil Z)) by (rewrite Zlength_nil; lia).
match goal with |- call_inv _ ?K ?SV _ _ _ _ =>
apply (load_inv_stable_step3 a k0 K
         {| sv_fp := FP_skip hdr got; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}
         ipc opc oc dl L oc SV nil Ha Hi Hst eq_refl eq_refl eq_refl eq_refl eq_refl HFP eq_refl Hs eq_refl eq_refl eq_refl eq_refl
         HL0 HiL) end.
- rewrite Zlength_nil. lia.
- exact Hloc.
- intros i _ _. reflexivity.
- rewrite Zlength_nil, Z.add_0_r, sublist_nil. reflexivity.
- apply Forall_nil.
- reflexivity.
- reflexivity.
- reflexivity.
- (* c_core *)
  rewrite app_nil_r.
  apply c_core_read_stable; cbn [k_cont s_cont c3_s c3_fs c3_tabs sv_fp sv_pend sv_ahead sv_lay sv_dd
                                  sf_stage sf_hostage sf_inSize sf_outSize sf_inPos sf_outStart sf_outEnd tabs_of
                                  option_map].
  + reflexivity.
  + exact Hh0.
  + reflexivity.
  + reflexivity.
  + exact Hsz.
  + reflexivity.
  + exact Hoso.
  + exact Hcf'.
  + exact (c_ring_stable_eq _ _ _ _ _ _ _ _ Hring eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  + right; right. cbn [fp_complete]. apply Z.eqb_refl.
  + right. cbn [fp_complete]. apply Z.eqb_refl.
- (* the model *)
  cbn [sv_fp sv_pend]. fold new.
  destruct Halive as [Hd|(cd&Hm&Hcdok&_)].
  + left. cbn [sv_ahead] in Hd. rewrite app_nil_r in Hd. apply (mf_dead_app M). exact Hd.
  + cbn [sv_ahead sv_fp sv_pend] in Hm, Hcdok. rewrite app_nil_r in Hm.
    destruct Hm as (dsin&fb&recs&Hsin&Hser&Hcd&Hcur&Hmout).
    right. exists cd. split.
    * exists dsin, (fb ++ new), recs. split; [rewrite Hsin, app_assoc; reflexivity|].
      split; [exact Hser|]. split; [exact Hcd|]. split.
      { pose proof (mf_skip_more M _ _ cd fb hdr got new Hcur ltac:(lia)) as Hc.
        rewrite Hnew in Hc. replace (got + L) with (le_field hdr 4 4) in Hc by lia. exact Hc. }
      rewrite !app_nil_r in *. exact Hmout.
    * cbn [next_cd] in Hcdok |- *. eapply cur_dict_ok_eq; [exact Hcdok|reflexivity|exact HFP].
Qed.

End CM_L3StS_1.
