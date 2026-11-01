(* FS3 streaming, case zdss_load: buffered mode, a success on the loaded unit of a skippable frame
   (its content skipped, nothing written: zdss_flush with nothing pending). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3BfLd.
Local Open Scope logic.

Section CM_L3BfS_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_cont_buf_s : forall a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr got,
  MF3 -> ld_ok a k0 sv ipc opc oc dl E L -> dc_stable (a_st a) = false ->
  sf_outStart (c3_s k0) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k0) ->
  sv_fp sv = FP_skip hdr got ->
  cont_res (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv)
    (o_bf (c3_s k0) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ostart sv) (ld_u sv (a_ibs a) ipc L) rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv2,
    call_inv a (k_cont k0 fs' tabs' lxb (sv_dd sv)
                  (s_cont (c3_s k0) zdss_flush (vlong (ostart + rr))
                     (sublist 0 (sf_inSize (c3_s k0)) (ld_ring sv (c3_s k0) (a_ibs a) ipc L) ++ oc')))
      sv2 (ipc + L) opc oc dl.
Proof.
intros a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb hdr got HMF Hld Hst Hos Hor Hfp Hres Herr.
destruct (lb_facts _ _ _ _ _ _ _ _ _ Hld Hst)
  as (Hah&Hpend&Hh0&Hcf&Hring&Hnc&Hnraw&Hoso&Hsz&HPE&HL0&HPL&Hipc&HiL&Hbsin&Hbnew&Hnew&Hr1out&_&_).
pose proof Hld as Hld'. destruct Hld' as (Ha&Hi&Hs&HE&HE0&_&_&HIn&HOut&Hrl0&Hrl&Hbyr&Hdd).
pose proof Hi as Hi'. unfold call_inv in Hi'. cbv zeta in Hi'.
destruct Hi' as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hddok&_&_&_&Halive&_).
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst fp pend ahead.
cbn [fp_inpos] in HPE, HPL.
set (new := sublist ipc (ipc + L) (a_ibs a)) in *.
set (sv := {| sv_fp := FP_skip hdr got; sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}) in *.
set (ring1 := ld_ring sv (c3_s k0) (a_ibs a) ipc L) in *.
(* E is the frame's size *)
assert (HEle: E = le_field hdr 4 4).
{ pose proof Hcf as X. destruct X as (_&_&_&_&_&_&_&_&_&Hsz32&Hif).
  cbn [fp_complete] in Hnc. rewrite Hnc in Hif. destruct Hif as [_ Hex].
  rewrite HE in Hex. change (Vlong (Int64.repr (le_field hdr 4 4))) with (vlong (le_field hdr 4 4)) in Hex.
  apply vlong_eq in Hex; [exact Hex|lia|].
  destruct Hcf as (_&_&_&_&_&_&_&_&Hg&_). lia. }
assert (Hl0: l = HL_none \/ exists eb ec gp, l = HL_dict eb ec gp)
  by (destruct Hcf as (_&_&_&_&_&Hl0&_); exact Hl0).
destruct Hres as (Hrr&Hloc&Hunc&Hbyo&Hpost). rewrite Herr in Hpost.
cbn [fp_unit cont_post] in Hpost.
destruct Hpost as (Hr0&Hoc'&(ts&Hts&Hcf')). subst rr tabs'.
cbn [o_bf oa_c oa_N] in Hoc', Hloc.
assert (HFP: fs_fParams fs' = fs_fParams (c3_fs k0))
  by exact (c_frame_fparams_s _ _ hdr got l dd fs' _ _ _ Hcf Hcf').
exists {| sv_fp := FP_skip hdr (le_field hdr 4 4); sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}.
eapply call_inv_next3; [exact Hi|lia|reflexivity|reflexivity|reflexivity|reflexivity| | reflexivity|reflexivity|reflexivity|reflexivity|reflexivity
                       |intros ? ?; discriminate|reflexivity|intros Hx; congruence| | |].
- exact HFP.
- apply c_core_rf3; cbn [k_cont s_cont c3_s c3_fs c3_tabs sf_stage sf_hostage sf_inSize sf_outSize
    sf_inPos sf_outStart sf_outEnd sv_fp sv_pend sv_ahead sv_lay sv_dd tabs_of option_map].
  + exact Hh0.
  + reflexivity.
  + destruct Hcf' as (_&Hc'&_). exact Hc'.
  + exact Hsz.
  + right; reflexivity.
  + exact Hcf'.
  + destruct Hring as (Hib&Hipt&Hisz&os&oe&Hos'&Hoe2&Hoo&Hr). cbv beta iota zeta in Hr.
    destruct Hr as (Hoeb&_&_&_&Hl).
    assert (Hl': os = 0 /\ oe = 0) by (destruct Hl0 as [->|(eb&ec&gp&->)]; destruct Hl as (_&H1&H2); auto).
    destruct Hl' as (->&->).
    assert (ostart = 0).
    { rewrite Hos in Hos'. apply vlong_eq_range in Hos'; lia. }
    subst ostart.
    unfold c_ring. rewrite Hst. cbn [s_cont sf_inBuff sf_inSize sf_outStart sf_outEnd sf_outSize sf_ring sf_outBuff
      fp_bsm fp_content fp_fcs fp_ws] in *.
    split; [exact Hib|]. split; [exact Hipt|]. split; [exact Hisz|].
    exists 0, (0 + 0). split; [exact Hos|]. split; [reflexivity|]. split; [lia|].
    cbv beta iota zeta.
    rewrite ring_out_cells by (try rewrite Hoc', Zlength_sublist; lia).
    split; [lia|]. split; [rewrite sublist_nil; reflexivity|]. split; [rewrite Zlength_nil; lia|].
    split; [exact I|]. destruct Hl0 as [->|(eb&ec&gp&->)]; (split; [reflexivity|]); lia.
  + intros Hx; rewrite Hst in Hx; discriminate.
  + reflexivity.
  + right; left; reflexivity.
  + right; cbn [fp_complete]; apply Z.eqb_refl.
  + unfold zdss_flush, zdss_read. intros; discriminate.
- apply (lb_dd_ok _ k0 _ sv); [reflexivity|reflexivity|exact Hs|exact Hddok].
- unfold alive_ok in Halive |- *. rewrite app_nil_r in Halive.
  assert (Hsin: a_sin a ++ sublist (a_ipos a) (ipc + L) (a_ibs a) =
                (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ new).
  { assert (Hib: 0 <= a_ipos a /\ Zlength (a_ibs a) = a_isz a)
      by (destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hp&_&Hz&_); split; [lia|exact Hz]).
    unfold new. rewrite <- app_assoc. f_equal. apply sublist_split; lia. }
  rewrite Hsin.
  destruct Halive as [Hd|(cd&Hm&Hcdok&_)].
  + left. apply (mf_dead_app HMF). exact Hd.
  + cbn [sv sv_fp sv_pend] in Hm, Hcdok.
    destruct Hm as (dsin&fb&recs&Esin&Hser&Hcd&Hcur&Hmout).
    right. exists cd. split; [|split].
    * exists dsin, (fb ++ new), recs. split; [rewrite Esin, app_assoc; reflexivity|].
      split; [exact Hser|]. split; [exact Hcd|]. split.
      { pose proof (mf_skip_more HMF _ _ cd fb hdr got new Hcur ltac:(lia)) as Hc.
        rewrite Hnew in Hc. replace (got + L) with (le_field hdr 4 4) in Hc by lia. exact Hc. }
      cbn [fp_content sv_pend sv_fp] in *. exact Hmout.
    * cbn [next_cd sv_fp] in Hcdok |- *. apply (cur_dict_ok_same _ k0); [reflexivity|exact HFP|exact Hcdok].
    * unfold hist_ok. intros. cbn [sv_lay]. destruct Hl0 as [->|(eb&ec&gp&->)]; exact I.
Qed.

End CM_L3BfS_1.
