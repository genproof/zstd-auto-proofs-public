(* FS3 streaming, case zdss_read: a unit decoded directly from the caller's input into the stream
   buffer (buffered mode) succeeded: the loop invariant of the new state (v2 StreamSeg_read.v read_cont_buf_gen,
   lines 908-1559). *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Step Zstd.proof.dec.v3.FS.stream.read.R3Dm.
Local Open Scope logic.

Section CM_R3Buf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma read_cont_buf3 : forall a k sv ipc opc oc1 dl ns ostart rr oc' fs' tabs' lxb,
  MF3 -> dsa_ok a -> call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read ->
  dc_stable (a_st a) = false ->
  fp_complete (sv_fp sv) = false -> unit_ok (sv_fp sv) ns -> 0 < ns -> ipc + ns <= a_isz a ->
  sf_outStart (c3_s k) = vlong ostart -> 0 <= ostart <= sf_outSize (c3_s k) ->
  Zlength (sf_ring (c3_s k)) = sf_inSize (c3_s k) + sf_outSize (c3_s k) -> byte_cells (sf_ring (c3_s k)) ->
  (* the frame's DDict facts (R3Borrow.dd_borrow) *)
  dd_facts (a_W a) (sv_dd sv) ->
  (* c_ring's segment bound (c_ring_cbound), the byte content of the context's dictionaries (R3DmV) *)
  lay_cbound (sv_fp sv) (sv_lay sv) -> dicts_bytes (a_st a) ->
  cont_res (sv_fp sv) (sv_lay sv) (sv_dd sv) (oa_ring (c3_s k) (sv_fp sv) ostart)
    (sublist ipc (ipc + ns) (a_ibs a)) rr oc' fs' tabs' ->
  is_error_code rr = false ->
  let s := c3_s k in
  let rd := andb (Z.eqb rr 0) (negb (is_skip (sv_fp sv))) in
  exists sv', call_inv a
    (c3_with_s (c3_with_fs k fs' (tabs_of (sv_dd sv) lxb tabs'))
       (sf_cont s (if rd then zdss_read else zdss_flush) (if rd then sf_outEnd s else vlong (ostart + rr))
          (sublist 0 (sf_inSize s) (sf_ring s) ++ oc')))
    sv' (ipc + ns) opc oc1 dl /\
    sv_dd sv' = sv_dd sv /\ lay_cbound (sv_fp sv') (sv_lay sv').
Proof.
intros a k sv ipc opc oc1 dl ns ostart rr oc' fs' tabs' lxb HMF Ha Hi Hs Hst Hc Hu Hns Hin Hos Hor Hlr Hbyr Hdf Hcb
  Hdmo Hres Herr.
cbv zeta.
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *.
pose proof Hi as Hi0.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&_&_&_&Hmod&_).
cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in Hcore, Hmod.
rewrite Hst in Hcore.
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
cbn [sv_fp sv_pend sv_ahead sv_lay] in Hhost.
destruct Hcs as (_&Hcf&Hring&_&_&Hnl&Hrd).
specialize (Hnl ltac:(unfold zdss_read, zdss_load; lia)). specialize (Hrd eq_refl).
destruct Hnl as (Hip&Hld&Hsk). destruct Hrd as (->&Hoe).
assert (Hah: sf_hostage (c3_s k) = Vint (Int.repr 0) /\ ahead = nil).
{ destruct Hhost as [[Hx _]|[Hx|Hx]]; [rewrite Hs in Hx; discriminate|exact Hx|].
  destruct Hx as (_&_&Hx&_). rewrite Hx in Hc; discriminate. }
destruct Hah as (Hh0&->). rewrite app_nil_r in Hmod.
destruct Ha as (_&_&_&_&_&_&_&_&_&_&_&_&Hip0&_&Hlib&Hbib&_).
set (u := sublist ipc (ipc + ns) (a_ibs a)) in *.
assert (Hul: Zlength u = ns) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hbu: bytes_ok u) by (unfold u, bytes_ok in *; apply Forall_sublist; auto).
assert (Hsin: a_sin a ++ sublist (a_ipos a) (ipc + ns) (a_ibs a) =
              (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ u).
{ unfold u. rewrite <- app_assoc. f_equal. apply sublist_split; lia. }
assert (Hbsin: bytes_ok (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a))).
{ unfold bytes_ok in *. apply Forall_app; split; auto. apply Forall_sublist; auto. }
assert (HN: sf_outSize (c3_s k) <= 2 ^ 32).
{ destruct Hring as (_&_&Hisz&_). lia. }
assert (Hoe': sf_outEnd (c3_s k) = vlong ostart) by (rewrite <- Hoe; exact Hos).
destruct Hres as (Hrr&Hloc&Hunc&Hbyo&Hpost). rewrite Herr in Hpost.
assert (Hbyc'': byte_cells oc') by (apply Hbyo; apply byte_cells_sublist; exact Hbyr).
cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip] in Hloc, Hunc.
set (sm := sm_of (a_st a)) in *.
destruct fp as [|hb|hdr got|hdr z]; [unfold c_frame in Hcf; destruct Hcf as (_&_&_&_&_&F); contradiction F ..| |].
- (* a skippable frame: its content skipped, nothing written *)
  destruct Hpost as (Hr0&Hoc'&(ts&Hts&Hcf')). subst rr tabs'.
  assert (Hl0: l = HL_none \/ exists eb ec gp, l = HL_dict eb ec gp)
    by (destruct Hcf as (_&_&_&_&_&Hl0&_); exact Hl0).
  destruct Hu as (Hg0&Hnsz). subst got.
  exists {| sv_fp := FP_skip hdr (le_field hdr 4 4); sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |}.
  cbn [sv_fp sv_lay sv_dd].
  split; [|split; [reflexivity|]].
  2: { intros b ps pe e E. destruct Hl0 as [->|(eb&ec&gp&->)]; discriminate E. }
  eapply call_inv_next3; [exact Hi0|lia|reflexivity|reflexivity|reflexivity|reflexivity
                         |reflexivity|reflexivity|reflexivity| | reflexivity|reflexivity
                         |intros ? ?; discriminate|reflexivity|intros Hx; congruence| | |].
  + cbn [c3_with_s c3_with_fs c3_fs]. exact (c_frame_fparams_s _ _ _ _ _ _ _ _ _ _ Hcf Hcf').
  + apply c_core_rf3; cbn [c3_s c3_fs c3_tabs c3_with_s c3_with_fs sf_cont sf_stage sf_hostage sf_inSize sf_outSize
      sf_inPos sf_outStart sf_outEnd sv_fp sv_pend sv_ahead sv_lay sv_dd is_skip negb andb Z.eqb tabs_of option_map].
    * exact Hh0.
    * reflexivity.
    * destruct Hcf' as (_&Hc'&_). exact Hc'.
    * exact Hsz.
    * right; reflexivity.
    * exact Hcf'.
    * destruct Hring as (Hib&Hipt&Hisz&os&oe&Hos'&Hoe2&Hoo&Hr). cbv beta iota zeta in Hr.
      destruct Hr as (Hoeb&_&_&_&Hl).
      assert (Hl': fp_content (FP_skip hdr 0) = nil /\ os = 0 /\ oe = 0)
        by (destruct Hl0 as [->|(eb&ec&gp&->)]; exact Hl).
      destruct Hl' as (_&->&->).
      assert (ostart = 0).
      { rewrite Hos in Hos'. apply vlong_eq_range in Hos'; lia. }
      subst ostart.
      unfold c_ring. rewrite Hst. cbn [sf_cont sf_inBuff sf_inSize sf_outStart sf_outEnd sf_outSize sf_ring sf_outBuff
        fp_bsm fp_content fp_fcs fp_ws] in *.
      split; [exact Hib|]. split; [exact Hipt|]. split; [exact Hisz|].
      exists 0, (0 + 0). split; [exact Hos|]. split; [reflexivity|]. split; [lia|].
      cbv beta iota zeta.
      rewrite ring_out_cells by lia.
      split; [lia|]. split; [rewrite sublist_nil; reflexivity|]. split; [rewrite Zlength_nil; lia|].
      split; [exact I|]. destruct Hl0 as [->|(eb&ec&gp&->)]; (split; [reflexivity|]); lia.
    * intros Hx; rewrite Hst in Hx; discriminate.
    * exact Hip.
    * right; left; reflexivity.
    * right; cbn [fp_complete]; apply Z.eqb_refl.
    * unfold zdss_flush, zdss_read. intros; discriminate.
  + refine (sv_dd_ok_same _ k _ _ _ _ _ Hs Hdd); reflexivity.
  + rewrite Hsin. destruct Hmod as [Hd|(cd&Hm&Hcd&_)].
    * left. apply (mf_dead_app HMF). exact Hd.
    * right. exists cd. split; [|split].
      -- destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcr&Ho). exists dsin, (fb ++ u), recs.
         split; [rewrite Esin, app_assoc; reflexivity|]. split; [exact Ef|]. split; [exact Ecd|].
         split; [replace (le_field hdr 4 4) with (0 + Zlength u) by lia; apply (mf_skip_more HMF); [exact Hcr|lia]|].
         cbn [sv_pend sv_fp fp_content] in *. exact Ho.
      -- apply (cur_dict_ok_same _ k); [reflexivity| |exact Hcd].
         cbn [c3_with_s c3_with_fs c3_fs]. exact (c_frame_fparams_s _ _ _ _ _ _ _ _ _ _ Hcf Hcf').
      -- unfold hist_ok. intros. cbn [sv_lay]. destruct Hl0 as [->|(eb&ec&gp&->)]; exact I.
- (* a Zstandard frame: the unit's content written at outStart *)
  destruct Hpost as (cnt&ts'&Hsafe&Hok&Hck&Hrr'&Htabs&Hsub&Hunc2&Hcf').
  cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip] in Hsub, Hunc2.
  pose proof Hcf as Hcf0.
  destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hldd&Hdm&Hb0&Hbsm&Hws&_).
  assert (HI: 0 <= sf_inSize (c3_s k)) by (destruct Hring as (_&_&Hisz&_); lia).
  assert (Hc0 := Zlength_nonneg cnt).
  assert (Hend: ostart + rr <= sf_outSize (c3_s k)).
  { destruct (Z.eq_dec rr 0) as [->|Hn0]; [lia|].
    apply (f_equal (@Zlength val)) in Hsub. rewrite Zlength_map, Zlength_sublist2 in Hsub. lia. }
  assert (Hu': unit_ok (FP_zstd hdr z) (Zlength u)) by (rewrite Hul; exact Hu).
  assert (Hcl: Zlength cnt <= zp_bsm z).
  { apply (cnt_len hdr z u cnt ts' Hsafe ltac:(lia)); [|apply Zlength_nonneg|exact Hu'].
    intros bh Ep. destruct (c_frame_body _ _ _ _ _ _ bh Hcf0 Ep) as (c&Ec&Hc'&_). exists c; split; [auto|lia]. }
  set (body := match zp_ph z with ZP_body _ => true | _ => false end).
  assert (Hbody: body = false -> rr = 0).
  { unfold body. intros Hb. rewrite Hrr'. unfold cnt_safe in Hsafe.
    destruct (zp_ph z); try discriminate; destruct Hsafe as [-> _]; reflexivity. }
  assert (El': lnext (FP_zstd hdr z) l (oa_ring (c3_s k) (FP_zstd hdr z) ostart) rr =
     if body then lwrite (lmove l (sf_outBuff (c3_s k)) ostart (sf_outSize (c3_s k) - ostart)) (sf_outBuff (c3_s k))
                    ostart rr
     else lmove l (sf_outBuff (c3_s k)) ostart (sf_outSize (c3_s k) - ostart)).
  { unfold body, lnext. cbn [oa_d oa_cap oa_base oa_N oa_c oa_ring is_skip]. destruct (zp_ph z); reflexivity. }
  rewrite El' in Hcf'.
  cbn [is_skip negb]. rewrite andb_true_r.
  replace (if rr =? 0 then sf_outEnd (c3_s k) else vlong (ostart + rr)) with (vlong (ostart + rr))
    by (destruct (rr =? 0) eqn:E; [apply Z.eqb_eq in E; rewrite E, Z.add_0_r, Hoe'; reflexivity|reflexivity]).
  set (z' := zstep z u cnt ts') in *.
  set (l' := if body then lwrite (lmove l (sf_outBuff (c3_s k)) ostart (sf_outSize (c3_s k) - ostart))
                            (sf_outBuff (c3_s k)) ostart rr
             else lmove l (sf_outBuff (c3_s k)) ostart (sf_outSize (c3_s k) - ostart)) in *.
  destruct (ring_new3 _ _ _ hdr z z' l dd _ ostart rr oc' cnt (if rr =? 0 then zdss_read else zdss_flush) body
              Hring Hldd Hdm Hdf Hcb Hos Hoe' Hor HN Hws Hbsm Hb0 (zstep_h _ _ _ _) (zstep_bsm _ _ _ _)
              (zstep_out _ _ _ _ Hsafe) Hlr Hloc Hrr' Hcl Hend Hsub Hbody Hbyc'') as [Hring' Hcb'].
  exists {| sv_fp := FP_zstd hdr z'; sv_pend := cnt; sv_ahead := nil; sv_lay := l'; sv_dd := dd |}.
  cbn [sv_fp sv_lay sv_dd].
  split; [|split; [reflexivity|exact Hcb']].
  assert (Hfp': fs_fParams fs' = fs_fParams (c3_fs k)).
  { apply (c_frame_fparams_z _ _ hdr z l dd _ _ z' _ Hcf Hcf'); [apply zstep_h|apply zstep_bsm]. }
  eapply call_inv_next3; [exact Hi0|lia|reflexivity|reflexivity|reflexivity|reflexivity
                         |reflexivity|reflexivity|reflexivity| | reflexivity|reflexivity
                         |intros ? ?; discriminate|reflexivity|intros Hx; congruence| | |].
  + exact Hfp'.
  + apply c_core_rf3; cbn [c3_s c3_fs c3_tabs c3_with_s c3_with_fs sf_cont sf_stage sf_hostage sf_inSize sf_outSize
      sf_inPos sf_outStart sf_outEnd sv_fp sv_pend sv_ahead sv_lay sv_dd tabs_of option_map].
    * exact Hh0.
    * reflexivity.
    * destruct Hcf' as (_&Hc'&_). exact Hc'.
    * exact Hsz.
    * destruct (rr =? 0); [left|right]; reflexivity.
    * rewrite Htabs. exact Hcf'.
    * rewrite Hst. exact Hring'.
    * intros Hx; rewrite Hst in Hx; discriminate.
    * exact Hip.
    * assert (Hck': zp_ph z = ZP_ck \/ zp_ph z <> ZP_ck) by (destruct (zp_ph z); [right|right|left|right]; congruence).
      destruct Hck' as [Hck'|Hck']; [right; right; apply zstep_loaded_ck; auto|].
      destruct (zstep_loaded_u hdr z u cnt ts' Hu' Hck'); auto.
    * exact I.
    * intros Hr2. destruct (rr =? 0) eqn:E; [|unfold zdss_flush, zdss_read in Hr2; discriminate].
      apply Z.eqb_eq in E. split; [apply Zlength_nil_inv; lia|]. rewrite Hos, E, Z.add_0_r. reflexivity.
  + refine (sv_dd_ok_same _ k _ _ _ _ _ Hs Hdd); reflexivity.
  + rewrite Hsin. destruct Hmod as [Hd|(cd&Hm&Hcd&Hho)].
    * left. apply (mf_dead_app HMF). exact Hd.
    * destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcr&Ho).
      assert (Hbfb: bytes_ok dsin /\ bytes_ok fb)
        by (rewrite Esin in Hbsin; unfold bytes_ok in *; apply Forall_app in Hbsin; exact Hbsin).
      unfold hist_ok in Hho. rewrite Hst in Hho. cbn [c3_s sv_lay sv_fp fp_content fp_ws fp_hist] in Hho.
      specialize (Hho eq_refl ltac:(rewrite Hs; unfold zdss_read, zdss_init; lia)
                    ltac:(rewrite Hs; unfold zdss_read, zdss_loadHeader; lia)).
      assert (Hold: old_hist (ring_cells (c3_s k)) l z) by (unfold old_hist, ring_cells; destruct l; auto).
      assert (Hpre: hist_pre (FP_zstd hdr z) l (oa_ring (c3_s k) (FP_zstd hdr z) ostart))
        by (exact (hist_pre_buf3 _ _ _ hdr z l dd _ ostart Hring Hldd Hdm Hdf Hcb Hos Hoe' Hor HN Hws Hbsm Hb0 Hold)).
      pose proof (Hok Hpre) as Hcok.
      assert (Hbh: forall bh c, zp_ph z' = ZP_body bh -> cblock_size bh = Some c -> c <= zp_bsm z).
      { intros bh c Ez Ec. destruct (c_frame_body _ _ _ _ _ _ _ Hcf' Ez) as (c'&Ec'&Hc'&_). rewrite Ec in Ec'.
        inversion Ec'; subst c'. unfold z' in Hc'. rewrite zstep_bsm in Hc'. lia. }
      assert (Hgot: match zp_ph z with
                    | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
                    | _ => zp_got z = nil
                    end).
      { unfold unit_ok in Hu. unfold fp_rawbody, fp_loaded in Hld. destruct (zp_ph z); try tauto.
        destruct Hld as [Hld|[Hld|Hld]]; [left; apply Z.eqb_eq; exact Hld|right; exact Hld|congruence]. }
      assert (Hz: zhist_ok sm z (lay_H z l (oa_ring (c3_s k) (FP_zstd hdr z) ostart)))
        by (exact (zhist_buf3 _ _ _ hdr z l dd _ ostart sm Hring Hldd Hdm Hdf Hcb Hos Hoe' Hor HN Hws Hbsm Hb0 eq_refl)).
      destruct (mf_zunit_step HMF sm cd fb hdr z _ u cnt ts' (proj2 Hbfb) (ld_dm_of _ _ _ _ _ Hdmo Hcd hdr z ltac:(first [reflexivity | congruence])) Hz Hbh Hcr Hgot Hu'
                  Hbu Hsafe Hcok Hck) as [[Hcr' Hsome]|Hfd].
      -- right. exists cd. split; [|split].
         ++ exists dsin, (fb ++ u), recs. split; [rewrite Esin, app_assoc; reflexivity|]. split; [exact Ef|].
            split; [exact Ecd|]. split; [exact Hcr'|]. cbn [fp_content sv_fp sv_pend]. unfold z'.
            rewrite (zstep_out _ _ _ _ Hsafe). rewrite app_nil_r in Ho. rewrite app_assoc, Ho. reflexivity.
         ++ apply (cur_dict_ok_same _ k); [reflexivity|exact Hfp'|]. cbn [sv_fp next_cd] in *. unfold z'.
            rewrite zstep_dm. exact Hcd.
         ++ unfold hist_ok. intros _ _ _.
            cbn [c3_s c3_with_s c3_with_fs sf_cont sf_inSize sf_outSize sf_ring sv_lay sv_fp fp_content fp_ws fp_hist].
            rewrite ring_out_cells by lia. unfold z'. rewrite (zstep_out _ _ _ _ Hsafe), zstep_h.
            pose proof (hist_new3 _ _ _ hdr z (zstep z u cnt ts') l dd _ ostart rr oc' cnt body Hring Hldd Hdm Hdf Hcb
                     Hos Hoe' Hor HN Hws Hbsm Hb0 (zstep_dm _ _ _ _) Hlr HI Hloc Hrr' Hsub Hbody Hunc2 Hold) as G.
            fold l' in G. destruct l'; exact G.
      -- left. rewrite Esin, <- app_assoc. exact (mf_dead_of_fdead HMF sm cd dsin recs (fb ++ u) (proj1 Hbfb) Ef Ecd Hfd).
Qed.

End CM_R3Buf_1.
