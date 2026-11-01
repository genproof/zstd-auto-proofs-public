(* FS3 streaming, case zdss_load: stable mode, a success on the loaded unit of a Zstandard frame
   (v2 StreamSeg_load.v load_cont_stable, Zstandard case). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3StFacts.
Local Open Scope logic.

Section CM_L3StZ_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_stable_z : forall a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr z,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = true -> ld_dm (a_st a) k0 (sv_fp sv) ->
  sv_fp sv = FP_zstd hdr z ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) (o_st a sv opc oc) (ld_u sv (a_ibs a) ipc L)
    rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv2 dl2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) zdss_read (sf_outEnd (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L)))
      sv2 (ipc + L) (opc + rr) oc' dl2.
Proof.
intros a k0 sv ipc opc oc dl E L rr oc' fs' tabs' lxb hdr z M Hld Hst Hdm Hfp Hres Hok.
destruct (ld_st_facts _ _ _ _ _ _ _ _ _ Hld Hst)
  as (Hah&Hpend&Hh0&Hcf&Hring&Hnc&Hnraw&Hoso&Hsz&HPE&HL0&HiL&Hstout&Hls&Hopc&Hloc&Hbsin&Hbnew&Hnew&Hdds).
pose proof Hld as Hld'. destruct Hld' as (Ha&Hi&Hs&HE&HE0&HL&HLE&_).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Halive&_).
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst fp pend ahead.
cbn [fp_inpos] in HPE, HL, HLE.
pose proof (lcp_unit_z _ _ hdr z l dd E Hcf Hnc Hnraw HE HE0) as Hunit.
set (new := sublist ipc (ipc + L) (a_ibs a)) in *.
set (u := zp_got z ++ new).
assert (Hu: ld_u {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}
              (a_ibs a) ipc L = u) by reflexivity.
rewrite Hu in Hres.
assert (Hgotb: bytes_ok (zp_got z)).
{ destruct Hcf as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hg). exact Hg. }
assert (Hlu: Zlength u = E) by (unfold u; rewrite Zlength_app, Hnew; lia).
assert (Hbu: bytes_ok u) by (apply Forall_app; split; assumption).
destruct Hres as (Hrr&Hlen'&Hunch&_&Hpost). rewrite Hok in Hpost.
cbn [fp_unit] in Hpost. unfold cont_post in Hpost.
destruct Hpost as (cnt&ts'&Hsafe&Hcok&Hchk&Hrr'&Hts'&Hsub&_&Hcf').
subst rr tabs'.
cbn [o_st oa_c oa_d oa_cap oa_N sv_fp is_skip] in Hsub, Hunch, Hlen'.
replace (opc + (a_osz a - opc)) with (a_osz a) in Hunch by lia.
destruct (hist_pre_stable (a_shob a) (a_ob a) (a_osz a) oc _ _ _ _ hdr z l dd opc Hring Hcf Hdds Hstout Hls Hopc)
  as [Hhp HlH].
specialize (Hcok Hhp).
match type of Hcok with cnt_ok _ ?H _ _ _ => assert (HH: H = zp_hist z) by exact HlH; rewrite HH in Hcok end.
assert (Hoz: opc + Zlength cnt <= a_osz a).
{ rewrite <- Hlen'. pose proof (Zlength_nonneg cnt). pose proof (Zlength_nonneg (ss_out (dc_ss (a_st a)) ++ dl)).
  apply (sublist_len_bound oc' opc); [lia|lia|]. rewrite Hsub, Zlength_map. lia. }
assert (Hbc: bytes_ok cnt).
{ pose proof Hcf' as X. destruct X as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hbo&_).
  rewrite (zstep_out _ _ _ _ Hsafe) in Hbo. apply Forall_app in Hbo. tauto. }
assert (HFP: fs_fParams fs' = fs_fParams (c3_fs k0))
  by exact (c_frame_fparams_z _ _ hdr z l dd fs' _ _ _ _ Hcf Hcf' (zstep_h _ _ _ _) (zstep_bsm _ _ _ _)).
assert (Hlf: lay_fields (c3_fs k0) l) by (destruct Hcf as (_&_&_&Hx&_); exact Hx).
set (z0 := zp_set_got z nil) in *.
exists {| sv_fp := FP_zstd hdr (zstep z0 u cnt ts'); sv_pend := nil; sv_ahead := nil;
          sv_lay := lnext (FP_zstd hdr z0) l
                      (o_st a {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                 sv_dd := dd |} opc oc) (Zlength cnt);
          sv_dd := dd |}, (dl ++ cnt).
match goal with |- call_inv _ ?K ?SV _ _ _ _ =>
apply (load_inv_stable_step3 a k0 K
         {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}
         ipc opc oc dl L oc' SV cnt Ha Hi Hst eq_refl eq_refl eq_refl eq_refl eq_refl HFP eq_refl Hs eq_refl eq_refl eq_refl eq_refl
         HL0 HiL Hoz Hlen' Hunch Hsub Hbc eq_refl eq_refl eq_refl) end.
- (* c_core *)
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
  + rewrite app_assoc.
    refine (c_ring_stable_zunit (a_shob a) (a_ob a) (a_osz a) oc _ _ hdr z0 _ l cnt opc (c3_fs k0) _ Hlf Hls Hoz
              (zstep_bsm _ _ _ _) (zstep_out _ _ _ _ Hsafe) _).
    * exact (c_ring_stable_eq _ _ _ _ _ _ _ _ Hring eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
    * unfold cnt_safe in Hsafe. unfold z0 in *. cbn [zp_set_got zp_with zp_ph] in Hsafe |- *.
      destruct (zp_ph z); auto; tauto.
  + cbn [fp_complete fp_rawbody] in Hnc, Hnraw. unfold z0.
    destruct (zp_ph z) eqn:Ep; try discriminate.
    * destruct (zstep_loaded hdr (zp_set_got z nil) u cnt ts' E Hunit
                ltac:(cbn [zp_set_got zp_with zp_ph]; rewrite Ep; discriminate)) as [Hx|Hx];
        [left; exact Hx|right; left; exact Hx].
    * destruct (zstep_loaded hdr (zp_set_got z nil) u cnt ts' E Hunit
                ltac:(cbn [zp_set_got zp_with zp_ph]; rewrite Ep; discriminate)) as [Hx|Hx];
        [left; exact Hx|right; left; exact Hx].
    * right; right. apply zstep_ck_complete. cbn [zp_set_got zp_with zp_ph]. exact Ep.
  + exact I.
- (* the model *)
  cbn [sv_fp sv_pend]. fold new.
  destruct Halive as [Hd|(cd&Hm&Hcdok&_)].
  + left. cbn [sv_ahead] in Hd. rewrite app_nil_r in Hd. apply (mf_dead_app M). exact Hd.
  + cbn [sv_ahead sv_fp sv_pend] in Hm, Hcdok. rewrite app_nil_r in Hm.
    destruct Hm as (dsin&fb&recs&Hsin&Hser&Hcd&Hcur&Hmout).
    assert (Hph: match zp_ph z with ZP_body bh => bp_type (block_props_of bh) <> 0 | ZP_end => False | _ => True end).
    { cbn [fp_rawbody fp_complete] in Hnraw, Hnc. destruct (zp_ph z); auto; try discriminate.
      intro Hb. rewrite Hb in Hnraw. discriminate. }
    destruct (cur_rel_unget _ _ _ fb hdr z Hcur Hph) as (fb0&Hfb&Hcur0).
    assert (Hsin': (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ new = (dsin ++ fb0) ++ u).
    { rewrite Hsin, Hfb. unfold u. rewrite !app_assoc. reflexivity. }
    assert (Hbs0: bytes_ok (dsin ++ fb0)).
    { rewrite Hsin, Hfb, app_assoc in Hbsin. apply Forall_app in Hbsin. tauto. }
    assert (Hm0: m_rel_cd (sm_of (a_st a)) (dsin ++ fb0) (ss_out (dc_ss (a_st a)) ++ dl) (FP_zstd hdr z0) nil cd).
    { exists dsin, fb0, recs. split; [reflexivity|]. split; [exact Hser|]. split; [exact Hcd|].
      split; [exact Hcur0|]. exact Hmout. }
    assert (Hgot0: match zp_ph z0 with
                   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z0 = nil
                   | _ => zp_got z0 = nil end)
      by (unfold z0; cbn [zp_set_got zp_with zp_ph zp_got]; destruct (zp_ph z); auto).
    rewrite <- Hlu in Hunit.
    destruct (model_zunit3 M (sm_of (a_st a)) cd (dsin ++ fb0) (ss_out (dc_ss (a_st a)) ++ dl) hdr z0 (zp_hist z)
                u cnt ts' fs' _ _ dd Hbs0 Hbu (Hdm cd Hcdok hdr z eq_refl) (or_introl eq_refl) Hm0 Hgot0 Hunit Hsafe Hcok
                Hchk Hcf') as [Hd|Hm'].
    * left. rewrite Hsin'. exact Hd.
    * right. exists cd. rewrite Hsin', app_assoc. split; [exact Hm'|].
      cbn [next_cd] in Hcdok |- *. rewrite zstep_dm.
      eapply cur_dict_ok_eq; [exact Hcdok|reflexivity|exact HFP].
Qed.

End CM_L3StZ_1.
