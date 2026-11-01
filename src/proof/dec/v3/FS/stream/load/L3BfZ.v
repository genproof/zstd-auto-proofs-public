(* FS3 streaming, case zdss_load: buffered mode, a success on the loaded unit of a Zstandard frame
   (read/R3Buf.v's read_cont_buf3 with the unit view fp_unit, u = ld_u, the ring as loaded). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3BfLd.
Local Open Scope logic.

Section CM_L3BfZ_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_buf_z : forall a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr z,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = false -> ld_dm (a_st a) k0 (sv_fp sv) ->
  lay_cbound (sv_fp sv) (sv_lay sv) ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) ->
  sv_fp sv = FP_zstd hdr z ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv)
    (o_bf (c3_s k0) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ostart sv) (ld_u sv (a_ibs a) ipc L) rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) (if rr =? 0 then zdss_read else zdss_flush)
                     (if rr =? 0 then sf_outEnd (c3_s k0) else vlong (ostart + rr))
                     (sublist 0 (sf_inSize (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ++ oc')))
      sv2 (ipc + L) opc oc dl.
Proof.
intros a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr z HMF Hld Hst Hdmo Hcb Hos Hor Hfp Hres Herr.
destruct (lb_facts _ _ _ _ _ _ _ _ _ Hld Hst)
  as (Hah&Hpend&Hh0&Hcf&Hring&Hnc&Hnraw&Hoso&Hsz&HPE&HL0&HPL&Hipc&HiL&Hbsin&Hbnew&Hnew&Hr1out&_&_).
pose proof Hld as Hld'. destruct Hld' as (Ha&Hi&Hs&HE&HE0&_&_&HIn&HOut&Hrl0&Hrl&Hbyr&Hdd).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hddok&_&_&_&Halive&_).
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst fp pend ahead.
cbn [fp_inpos] in HPE, HPL.
set (new := sublist ipc (ipc + L) (a_ibs a)) in *.
set (z0 := zp_set_got z nil).
set (u := zp_got z ++ new).
set (sv := {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}) in *.
assert (Hu: ld_u sv (a_ibs a) ipc L = u) by reflexivity.
rewrite Hu in Hres.
set (ring1 := ld_ring sv (c3_s k0) (a_ibs a) ipc L) in *.
set (s1 := s_load (c3_s k0) 0 ring1).
assert (Ho: o_bf (c3_s k0) ring1 ostart sv = oa_ring s1 (FP_zstd hdr z0) ostart) by reflexivity.
assert (Hun: fp_unit (FP_zstd hdr z) = FP_zstd hdr z0) by reflexivity.
rewrite Ho, Hun in Hres. cbn [sv_lay sv_dd sv] in Hres.
assert (Hring1: c_ring false (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl) s1 (FP_zstd hdr z0) nil l)
  by exact (lb_c_ring_unit _ _ _ _ _ _ _ 0 ring1 Hr1out Hring).
destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hldd&Hdm&Hb0&Hbsm&Hws&_).
assert (Hdf: dd_bf (a_W a) dd) by exact (dd_bf_of _ _ Hdd).
assert (Hcb0: lay_cbound (FP_zstd hdr z0) l) by exact Hcb.
assert (Hos1: sf_outStart s1 = vlong ostart) by exact Hos.
assert (Hoe1: sf_outEnd s1 = vlong ostart) by (change (sf_outEnd (c3_s k0) = vlong ostart); rewrite <- Hoso; exact Hos).
assert (Hor1: 0 <= ostart <= sf_outSize s1) by exact Hor.
assert (HN: sf_outSize s1 <= 2 ^ 32) by (cbn [s1 s_load sf_outSize]; lia).
assert (Hlr1: Zlength (sf_ring s1) = sf_inSize s1 + sf_outSize s1) by exact Hrl.
destruct Hres as (Hrr&Hloc&Hunc&Hbyo&Hpost). rewrite Herr in Hpost.
assert (Hbyc'': byte_cells oc') by (apply Hbyo; apply byte_cells_sublist; exact Hbyr).
cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip] in Hloc, Hunc.
set (sm := sm_of (a_st a)) in *.
destruct Hpost as (cnt&ts'&Hsafe&Hok&Hck&Hrr'&Htabs&Hsub&Hunc2&Hcf').
cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip] in Hsub, Hunc2.
assert (HI: 0 <= sf_inSize s1) by exact HIn.
assert (Hc0 := Zlength_nonneg cnt).
assert (Hend: ostart + rr <= sf_outSize s1).
{ destruct (Z.eq_dec rr 0) as [->|Hn0]; [lia|].
  apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_map, Zlength_sublist2 in Hsub. lia. }
assert (Hlu: Zlength u = E) by (unfold u; rewrite Zlength_app, Hnew; lia).
assert (Hu': unit_ok (FP_zstd hdr z0) (Zlength u))
  by (rewrite Hlu; exact (lb_unit_z _ _ hdr z l dd E Hcf Hnc Hnraw HE HE0)).
assert (Hcl: Zlength cnt <= zp_bsm z0).
{ apply (cnt_len hdr z0 u cnt ts' Hsafe ltac:(cbn [z0 zp_set_got zp_with zp_bsm]; lia));
    [|apply Zlength_nonneg|exact Hu'].
  intros bh Ep. destruct (c_frame_body _ _ hdr z _ _ bh Hcf Ep) as (c&Ec&Hc'&_). exists c; split; [auto|exact (proj2 Hc')]. }
set (body := match zp_ph z0 with ZP_body _ => true | _ => false end).
assert (Hbody: body = false -> rr = 0).
{ unfold body. intros Hb. rewrite Hrr'. unfold cnt_safe in Hsafe.
  destruct (zp_ph z0); try discriminate; destruct Hsafe as [-> _]; reflexivity. }
assert (El': lnext (FP_zstd hdr z0) l (oa_ring s1 (FP_zstd hdr z0) ostart) rr =
     if body then lwrite (lmove l (sf_outBuff s1) ostart (sf_outSize s1 - ostart)) (sf_outBuff s1) ostart rr
     else lmove l (sf_outBuff s1) ostart (sf_outSize s1 - ostart)).
{ unfold body, lnext. cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip]. destruct (zp_ph z0); reflexivity. }
rewrite El' in Hcf'.
replace (if rr =? 0 then sf_outEnd (c3_s k0) else vlong (ostart + rr)) with (vlong (ostart + rr))
  by (destruct (rr =? 0) eqn:Er; [apply Z.eqb_eq in Er; rewrite Er, Z.add_0_r, <- Hoso, Hos; reflexivity|reflexivity]).
set (z' := zstep z0 u cnt ts') in *.
set (l' := if body then lwrite (lmove l (sf_outBuff s1) ostart (sf_outSize s1 - ostart)) (sf_outBuff s1) ostart rr
           else lmove l (sf_outBuff s1) ostart (sf_outSize s1 - ostart)) in *.
destruct (ring_new3 _ _ _ hdr z0 z' l dd _ ostart rr oc' cnt (if rr =? 0 then zdss_read else zdss_flush) body
            Hring1 Hldd Hdm Hdf Hcb0 Hos1 Hoe1 Hor1 HN Hws Hbsm Hb0 (zstep_h _ _ _ _) (zstep_bsm _ _ _ _)
            (zstep_out _ _ _ _ Hsafe) Hlr1 Hloc Hrr' Hcl Hend Hsub Hbody Hbyc'') as [Hring' _].
exists {| sv_fp := FP_zstd hdr z'; sv_pend := cnt; sv_ahead := nil; sv_lay := l'; sv_dd := dd |}.
assert (Hfp': fs_fParams fs' = fs_fParams (c3_fs k0)).
{ apply (c_frame_fparams_z _ _ hdr z l dd _ _ z' _ Hcf Hcf'); [exact (zstep_h z0 u cnt ts')|exact (zstep_bsm z0 u cnt ts')]. }
eapply call_inv_next3; [exact Hi|lia|reflexivity|reflexivity|reflexivity|reflexivity| | reflexivity|reflexivity|reflexivity|reflexivity|reflexivity
                       |intros ? ?; discriminate|reflexivity|intros Hx; congruence| | |].
- exact Hfp'.
- apply c_core_rf3; cbn [k_cont s_cont c3_s c3_fs c3_tabs sf_stage sf_hostage sf_inSize sf_outSize
    sf_inPos sf_outStart sf_outEnd sv_fp sv_pend sv_ahead sv_lay sv_dd tabs_of option_map].
  + exact Hh0.
  + reflexivity.
  + destruct Hcf' as (_&Hc'&_). exact Hc'.
  + exact Hsz.
  + destruct (rr =? 0); [left|right]; reflexivity.
  + rewrite Htabs. exact Hcf'.
  + rewrite Hst. exact Hring'.
  + intros Hx; rewrite Hst in Hx; discriminate.
  + reflexivity.
  + assert (Hck': zp_ph z0 = ZP_ck \/ zp_ph z0 <> ZP_ck) by (destruct (zp_ph z0); [right|right|left|right]; congruence).
    destruct Hck' as [Hck'|Hck']; [right; right; apply zstep_loaded_ck; auto|].
    destruct (zstep_loaded_u hdr z0 u cnt ts' Hu' Hck'); auto.
  + exact I.
  + intros Hr2. destruct (rr =? 0) eqn:Er; [|unfold zdss_flush, zdss_read in Hr2; discriminate].
    apply Z.eqb_eq in Er. split; [apply Zlength_nil_inv; lia|]. rewrite Hos, Er, Z.add_0_r. reflexivity.
- apply (lb_dd_ok _ k0 _ sv); [reflexivity|reflexivity|exact Hs|exact Hddok].
- unfold alive_ok in Halive |- *. rewrite app_nil_r in Halive.
  assert (Hsin: a_sin a ++ sublist (a_ipos a) (ipc + L) (a_ibs a) =
                (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ new).
  { assert (Hib: 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a)
      by (destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hp&_&Hz&_); split; [lia|exact Hz]).
    unfold new. rewrite <- app_assoc. f_equal. apply sublist_split; lia. }
  rewrite Hsin. fold sm in Halive |- *.
  destruct Halive as [Hd|(cd&Hm&Hcd&Hho)].
  + left. apply (mf_dead_app HMF). exact Hd.
  + destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcr&Hmo).
    cbn [sv_fp sv_pend sv] in Hcr, Hmo, Hcd.
    assert (Hph: match zp_ph z with ZP_body bh => bp_type (block_props_of bh) <> 0 | ZP_end => False | _ => True end).
    { cbn [fp_rawbody fp_complete] in Hnraw, Hnc. destruct (zp_ph z); auto; try discriminate.
      intro Hb. rewrite Hb in Hnraw. discriminate. }
    destruct (lb_cur_rel_unget _ _ _ fb hdr z Hcr Hph) as (fb0&Hfb&Hcr0).
    assert (Hsin': (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ new = dsin ++ (fb0 ++ u)).
    { rewrite Esin, Hfb. unfold u. rewrite !app_assoc. reflexivity. }
    assert (Hbfb: bytes_ok dsin /\ bytes_ok fb0 /\ bytes_ok (zp_got z)).
    { rewrite Esin, Hfb in Hbsin. unfold bytes_ok in *. apply Forall_app in Hbsin. destruct Hbsin as [B1 B2].
      apply Forall_app in B2. tauto. }
    assert (Hbu: bytes_ok u) by (unfold u, bytes_ok in *; apply Forall_app; tauto).
    unfold hist_ok in Hho. rewrite Hst in Hho.
    specialize (Hho eq_refl ltac:(rewrite Hs; unfold zdss_load, zdss_init; lia)
                  ltac:(rewrite Hs; unfold zdss_load, zdss_loadHeader; lia)).
    assert (Hold: old_hist (ring_cells s1) l z0).
    { unfold old_hist, ring_cells. change (sf_ring s1) with ring1.
      change (sf_inSize s1) with (sf_inSize (c3_s k0)). change (sf_outSize s1) with (sf_outSize (c3_s k0)).
      rewrite Hr1out. cbn [sv sv_lay sv_fp fp_content fp_ws fp_hist] in Hho. destruct l; auto. }
    assert (Hpre: hist_pre (FP_zstd hdr z0) l (oa_ring s1 (FP_zstd hdr z0) ostart))
      by exact (hist_pre_buf3 _ _ _ hdr z0 l dd _ ostart Hring1 Hldd Hdm Hdf Hcb0 Hos1 Hoe1 Hor1 HN Hws Hbsm Hb0 Hold).
    pose proof (Hok Hpre) as Hcok.
    assert (Hbh: forall bh c, zp_ph z' = ZP_body bh -> cblock_size bh = Some c -> c <= zp_bsm z0).
    { intros bh c Ez Ec. destruct (c_frame_body _ _ _ _ _ _ _ Hcf' Ez) as (c'&Ec'&Hc'&_). rewrite Ec in Ec'.
      inversion Ec'; subst c'. unfold z' in Hc'. rewrite zstep_bsm in Hc'. lia. }
    assert (Hgot: match zp_ph z0 with
                  | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z0 = nil
                  | _ => zp_got z0 = nil
                  end) by (unfold z0; cbn [zp_set_got zp_with zp_ph zp_got]; destruct (zp_ph z); auto).
    assert (Hz: zhist_ok sm z0 (lay_H z0 l (oa_ring s1 (FP_zstd hdr z0) ostart)))
      by exact (zhist_buf3 _ _ _ hdr z0 l dd _ ostart sm Hring1 Hldd Hdm Hdf Hcb0 Hos1 Hoe1 Hor1 HN Hws Hbsm Hb0 eq_refl).
    destruct (mf_zunit_step HMF sm cd fb0 hdr z0 _ u cnt ts' (proj1 (proj2 Hbfb)) (Hdmo cd Hcd hdr z eq_refl) Hz Hbh Hcr0
                Hgot Hu' Hbu Hsafe Hcok Hck) as [[Hcr' _]|Hfd].
    * right. exists cd. split; [|split].
      -- exists dsin, (fb0 ++ u), recs. split; [exact Hsin'|]. split; [exact Ef|]. split; [exact Ecd|].
         split; [exact Hcr'|]. cbn [fp_content sv_fp sv_pend]. unfold z'. rewrite (zstep_out _ _ _ _ Hsafe).
         rewrite app_nil_r in Hmo. rewrite Hmo, <- app_assoc. reflexivity.
      -- apply (cur_dict_ok_same _ k0); [reflexivity|exact Hfp'|]. cbn [sv_fp next_cd] in *. unfold z'.
         rewrite zstep_dm. exact Hcd.
      -- unfold hist_ok. intros _ _ _.
         cbn [c3_s k_cont s_cont sf_inSize sf_outSize sf_ring sv_lay sv_fp fp_content fp_ws fp_hist].
         assert (Hloc': Zlength oc' = sf_outSize (c3_s k0)) by exact Hloc.
         rewrite ring_out_cells by lia. unfold z'. rewrite (zstep_out _ _ _ _ Hsafe), zstep_h.
         pose proof (hist_new3 _ _ _ hdr z0 (zstep z0 u cnt ts') l dd _ ostart rr oc' cnt body Hring1 Hldd Hdm Hdf
                       Hcb0 Hos1 Hoe1 Hor1 HN Hws Hbsm Hb0 (zstep_dm _ _ _ _) Hlr1 HI Hloc Hrr' Hsub Hbody Hunc2 Hold)
           as G.
         fold l' in G. destruct l'; exact G.
    * left. rewrite Hsin'. exact (mf_dead_of_fdead HMF sm cd dsin recs (fb0 ++ u) (proj1 Hbfb) Ef Ecd Hfd).
Qed.

End CM_L3BfZ_1.
