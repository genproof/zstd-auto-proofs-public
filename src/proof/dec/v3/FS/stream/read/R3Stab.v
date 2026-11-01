(* FS3 streaming, case zdss_read: a unit decoded directly from the caller's input into the caller's
   stable output buffer succeeded: the loop invariant of the new state (v2 StreamSeg_read.v read_cont_stable_ok,
   lines 525-904). *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3StGen Zstd.proof.dec.v3.FS.stream.read.R3Err Zstd.proof.dec.v3.FS.stream.read.R3Dm.
Local Open Scope logic.

Section CM_R3Stab_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the loop invariant after a unit decoded into the stable buffer at opc (the context's frame fields changed) *)
Lemma call_inv_stable_step3 : forall a k sv ipc opc oc1 dl ns oc' fs' t sv' cnt,
  dsa_ok a -> call_inv a k sv ipc opc oc1 dl -> dc_stable (a_st a) = true -> sv_ahead sv = nil ->
  sf_stage (c3_s k) = zdss_read ->
  0 < ns -> ipc + ns <= a_isz a ->
  opc + Zlength cnt <= a_osz a -> Zlength oc' = a_osz a ->
  unchanged_outside oc1 oc' opc (a_osz a) ->
  sublist opc (opc + Zlength cnt) oc' = zbytes cnt -> bytes_ok cnt ->
  sv_ahead sv' = nil -> fs_fParams fs' = fs_fParams (c3_fs k) ->
  c_core true (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl ++ cnt) (c3_with_fs k fs' t) sv' ->
  sv_dd_ok (a_st a) (c3_with_fs k fs' t) sv' ->
  alive_ok (a_st a) (c3_with_fs k fs' t) sv' (a_sin a ++ sublist (a_ipos a) (ipc + ns) (a_ibs a))
    (ss_out (dc_ss (a_st a)) ++ dl ++ cnt) ->
  call_inv a (c3_with_fs k fs' t) sv' (ipc + ns) (opc + Zlength cnt) oc' (dl ++ cnt).
Proof.
intros a k sv ipc opc oc1 dl ns oc' fs' t sv' cnt Ha Hi Hst Hah Hsr Hns Hisz Ho Hlo Hu Hsub Hbc Hah' Hfp Hcore
  Hdd Hm.
destruct Ha as (_&_&_&_&_&_&_&_&_&Hopos&_&_&Hipos&_&Hlibs&_).
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&_&_&Hstout&_&_&_&_&Hsin&Hexp&_).
rewrite Hst in Hstout. specialize (Hstout eq_refl).
pose proof (Zlength_nonneg cnt).
destruct H8 as (B1&B2&B3&B4&B5&B6).
unfold call_inv. cbv zeta. cbn [c3_with_fs c3_s c3_stable c3_dict c3_par c3_set c3_fs]. rewrite Hst, Hah', app_nil_r.
assert (Hold: sublist 0 opc oc' = sublist 0 opc oc1) by (apply (unch_sublist _ _ opc (a_osz a)); auto; lia).
split; [lia|]. split; [lia|]. split; [exact Hlo|].
split; [rewrite <- H4; apply (unch_sublist _ _ opc (a_osz a)); auto; lia|].
split; [rewrite Zlength_app; lia|].
split.
{ rewrite (sublist_split (a_opos a) opc (opc + Zlength cnt)) by lia.
  rewrite (unch_sublist oc1 oc' opc (a_osz a) (a_opos a) opc) by (auto; lia). rewrite H6, Hsub, map_app. reflexivity. }
split; [apply Forall_app; auto|].
split; [unfold base_call; cbn [c3_with_fs c3_stable c3_par c3_set c3_dict c3_fs]; rewrite B1, B2, B3, Hfp; auto 10|].
do 2 (split; [assumption|]).
split; [left; lia|]. split; [assumption|].
split; [exact Hcore|]. split; [exact Hdd|].
split.
{ intros _. rewrite (sublist_split 0 opc (opc + Zlength cnt)) by lia.
  rewrite Hold, Hstout, Hsub, <- map_app, app_assoc. reflexivity. }
split; [intros []; reflexivity|].
split; [intros _ Hx; discriminate|].
split; [rewrite ?app_assoc in *; exact Hm|].
split; [rewrite Hsr; intros Hx; exfalso; unfold zdss_read, zdss_loadHeader in Hx; lia|].
split; [rewrite Hah, app_nil_r in Hsin; rewrite ?app_nil_r; exact Hsin|].
split; [intros Hx _; apply Hexp; [rewrite Hst; exact Hx|rewrite Hsr; unfold zdss_read, zdss_init; lia]|].
rewrite Hsr; intros Hx; exfalso; unfold zdss_read, zdss_flush in Hx; lia.
Qed.

Lemma read_cont_stable3 : forall a k sv ipc opc oc1 dl ns rr oc' fs' tabs' lxb,
  MF3 -> dsa_ok a -> call_inv a k sv ipc opc oc1 dl -> sf_stage (c3_s k) = zdss_read ->
  dc_stable (a_st a) = true ->
  fp_complete (sv_fp sv) = false -> unit_ok (sv_fp sv) ns -> 0 < ns -> ipc + ns <= a_isz a ->
  (* the frame's DDict facts (R3Borrow.dd_borrow) *)
  dd_facts (a_W a) (sv_dd sv) ->
  (* the byte content of the context's dictionaries (R3DmV.dd_all_bytes) *)
  dicts_bytes (a_st a) ->
  cont_res (sv_fp sv) (sv_lay sv) (sv_dd sv) (oa_stable (a_shob a) (a_ob a) (a_osz a) (sv_fp sv) oc1 opc)
    (sublist ipc (ipc + ns) (a_ibs a)) rr oc' fs' tabs' ->
  is_error_code rr = false ->
  exists sv' dl', call_inv a (c3_with_fs k fs' (tabs_of (sv_dd sv) lxb tabs')) sv' (ipc + ns) (opc + rr) oc' dl' /\
    sv_dd sv' = sv_dd sv.
Proof.
intros a k sv ipc opc oc1 dl ns rr oc' fs' tabs' lxb M Ha Hi Hs Hst Hnc Hunit Hns Hisz Hdf Hdmo Hres Hok.
destruct (read_pre_stable3 a k sv ipc opc oc1 dl Ha Hi Hs Hst Hnc Hdf) as [Hlay Hhp].
pose proof Ha as Ha'.
destruct Ha' as (_&_&_&_&_&_&_&_&_&Hopos&_&_&Hipos&_&Hlibs&Hbibs&_).
pose proof Hi as Hi'.
destruct Hi' as (H1&H2&H3&H4&H5&H6&H7&H8&Hbin&H10&H11&H12&Hcore&Hdd&Hstout&_&_&Hmodel&_).
rewrite Hst in Hcore, Hstout. specialize (Hstout eq_refl).
assert (Hls: Zlength (ss_out (dc_ss (a_st a)) ++ dl) = opc).
{ apply (f_equal (@Zlength val)) in Hstout. rewrite Zlength_map, Zlength_sublist in Hstout by lia. lia. }
destruct Hcore as (Hhost&Hcold&Hsz&Hcs). rewrite Hs in Hcs. simpl in Hcs.
destruct Hcs as (_&Hcf&Hring&_&_&Hnld&Hrd).
destruct Hnld as (Hinpos&Hraw&Hsk); [unfold zdss_load, zdss_read; lia|].
assert (Hraw': fp_rawbody (sv_fp sv) = true \/ fp_loaded (sv_fp sv) = nil)
  by (destruct Hraw as [?|[?|?]]; auto; congruence).
clear Hraw; rename Hraw' into Hraw.
destruct Hrd as (Hpend&Hoso); [reflexivity|].
assert (Hh0: sf_hostage (c3_s k) = Vint (Int.repr 0) /\ sv_ahead sv = nil).
{ destruct Hhost as [[Hx _]|[Hx|Hx]]; [rewrite Hs in Hx; unfold zdss_read, zdss_init in Hx; lia|exact Hx|].
  destruct Hx as (_&Hx&_); discriminate. }
destruct Hh0 as [Hh0 Hah].
destruct Hres as (Hrr&Hlen'&Hunch&_&Hpost). rewrite Hok in Hpost.
set (u := sublist ipc (ipc + ns) (a_ibs a)) in *.
assert (Hu: Zlength u = ns) by (unfold u; rewrite Zlength_sublist; lia).
assert (Hbu: bytes_ok u) by (unfold u; apply Forall_sublist; exact Hbibs).
assert (Hbsin: bytes_ok (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a))).
{ apply Forall_app; split; [exact Hbin|apply Forall_sublist; exact Hbibs]. }
assert (Hsin: a_sin a ++ sublist (a_ipos a) (ipc + ns) (a_ibs a) =
              (a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ u).
{ unfold u. rewrite <- app_assoc. f_equal. apply sublist_split; lia. }
destruct sv as [fp pend ahead l dd]. cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *. subst pend ahead.
rewrite app_nil_r in Hmodel.
destruct fp as [|hb|hdr got|hdr z]; [unfold c_frame in Hcf; destruct Hcf as (_&_&_&_&_&F); contradiction F ..| |].
- (* a skippable frame: its content is skipped, nothing written *)
  unfold cont_post in Hpost. destruct Hpost as (Hr0&Hoc&(ts&Hts&Hcf')). cbn [oa_c oa_stable] in Hoc.
  subst rr oc' tabs'. unfold unit_ok in Hunit. destruct Hunit as [Hg0 HnL]. subst got.
  exists {| sv_fp := FP_skip hdr (le_field hdr 4 4); sv_pend := nil; sv_ahead := nil; sv_lay := l; sv_dd := dd |},
    (dl ++ nil).
  cbn [sv_fp sv_dd]. split; [|reflexivity].
  replace (opc + 0) with (opc + Zlength (@nil Z)) by (rewrite Zlength_nil; lia).
  assert (Hfp: fs_fParams fs' = fs_fParams (c3_fs k)) by exact (c_frame_fparams_s _ _ _ _ _ _ _ _ _ _ Hcf Hcf').
  refine (call_inv_stable_step3 a k {| sv_fp := FP_skip hdr 0; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                       sv_dd := dd |} ipc opc oc1 dl ns _ _ _ _ _ Ha Hi Hst eq_refl Hs Hns Hisz
            _ H3 _ _ _ _ Hfp _ _ _).
  + rewrite Zlength_nil; lia.
  + intros x Hx _. reflexivity.
  + rewrite Zlength_nil, Z.add_0_r, sublist_nil. reflexivity.
  + constructor.
  + reflexivity.
  + rewrite app_nil_r. apply c_core_read_stable; cbn [c3_with_fs c3_s c3_fs c3_tabs sv_ahead sv_pend sv_fp sv_lay sv_dd];
      auto.
    all: first [ (cbn [tabs_of option_map]; exact Hcf')
               | (apply (c_ring_stable_eq _ _ _ _ _ _ _ _ Hring); reflexivity)
               | (right; right; cbn [fp_complete]; apply Z.eqb_refl)
               | (right; cbn [fp_complete]; apply Z.eqb_refl) ].
  + refine (sv_dd_ok_same _ k _ _ _ _ _ Hs Hdd); reflexivity.
  + rewrite app_nil_r, Hsin.
    destruct Hmodel as [Hd|(cd&Hm&Hcd&_)]; [left; apply (mf_dead_app M); exact Hd|right].
    exists cd. split; [|split].
    * destruct Hm as (dsin&fb&recs&Esin&Ef&Ecd&Hcur&Hout).
      exists dsin, (fb ++ u), recs. rewrite Esin, <- app_assoc. split; [reflexivity|].
      split; [exact Ef|]. split; [exact Ecd|]. split; [|exact Hout].
      pose proof (mf_skip_more M _ _ _ fb hdr 0 u Hcur ltac:(lia)) as Hc. rewrite Hu, Z.add_0_l, HnL in Hc. exact Hc.
    * apply (cur_dict_ok_same _ k); [reflexivity|exact Hfp|exact Hcd].
    * unfold hist_ok. intros Hx; congruence.
- (* a Zstandard frame *)
  unfold cont_post in Hpost.
  destruct Hpost as (cnt&ts'&Hsafe&Hcok&Hchk&Hrr'&Hts'&Hsub&_&Hcf').
  specialize (Hcok Hhp). subst rr tabs'.
  cbn [oa_c oa_d oa_cap oa_N oa_stable is_skip] in Hsub, Hunch, Hlen', Hcok.
  rewrite (lay_H_stable _ _ _ _ _ _ _ _ _ _ Hring Hls) in Hcok.
  replace (opc + (a_osz a - opc)) with (a_osz a) in Hunch by lia.
  assert (Hoz: opc + Zlength cnt <= a_osz a).
  { rewrite <- Hlen'. apply (sublist_len_bound oc' opc); [pose proof (Zlength_nonneg cnt); lia|lia|].
    rewrite Hsub, Zlength_map. lia. }
  assert (Hbc: bytes_ok cnt).
  { unfold c_frame in Hcf'. destruct Hcf' as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hbo&_).
    rewrite (zstep_out _ _ _ _ Hsafe) in Hbo. apply Forall_app in Hbo. tauto. }
  assert (Hlf: lay_fields (c3_fs k) l) by (unfold c_frame in Hcf; destruct Hcf as (_&_&_&Hlf&_); exact Hlf).
  assert (Hfp: fs_fParams fs' = fs_fParams (c3_fs k)).
  { apply (c_frame_fparams_z _ _ hdr z l dd _ _ (zstep z u cnt ts') _ Hcf Hcf'); [apply zstep_h|apply zstep_bsm]. }
  exists {| sv_fp := FP_zstd hdr (zstep z u cnt ts'); sv_pend := nil; sv_ahead := nil;
            sv_lay := lnext (FP_zstd hdr z) l (oa_stable (a_shob a) (a_ob a) (a_osz a) (FP_zstd hdr z) oc1 opc)
                        (Zlength cnt); sv_dd := dd |}, (dl ++ cnt).
  cbn [sv_fp sv_dd]. split; [|reflexivity].
  refine (call_inv_stable_step3 a k {| sv_fp := FP_zstd hdr z; sv_pend := nil; sv_ahead := nil; sv_lay := l;
                                       sv_dd := dd |} ipc opc oc1 dl ns _ _ _ _ _ Ha Hi Hst eq_refl Hs Hns Hisz
            Hoz Hlen' Hunch Hsub Hbc _ Hfp _ _ _).
  + reflexivity.
  + apply c_core_read_stable; cbn [c3_with_fs c3_s c3_fs c3_tabs sv_ahead sv_pend sv_fp sv_lay sv_dd]; auto.
    * rewrite app_assoc. eapply c_ring_stable_zunit; eauto.
      -- apply zstep_bsm.
      -- apply zstep_out; exact Hsafe.
      -- unfold cnt_safe in Hsafe. destruct (zp_ph z); auto; tauto.
    * destruct (zp_ph z) eqn:Ep.
      -- destruct (zstep_loaded hdr z u cnt ts' ns Hunit ltac:(congruence)); auto.
      -- destruct (zstep_loaded hdr z u cnt ts' ns Hunit ltac:(congruence)); auto.
      -- right; right. apply zstep_ck_complete; auto.
      -- unfold unit_ok in Hunit. rewrite Ep in Hunit. contradiction.
  + refine (sv_dd_ok_same _ k _ _ _ _ _ Hs Hdd); reflexivity.
  + rewrite Hsin.
    assert (Hgot: match zp_ph z with
                  | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
                  | _ => zp_got z = nil end).
    { unfold fp_rawbody, fp_loaded in Hraw.
      destruct (zp_ph z); destruct Hraw as [H|H]; try discriminate; auto. left; apply Z.eqb_eq; exact H. }
    destruct Hmodel as [Hd|(cd&Hm&Hcd&_)]; [left; apply (mf_dead_app M); exact Hd|].
    destruct (model_zunit3 M (sm_of (a_st a)) cd _ _ hdr z (zp_hist z) u cnt ts' fs' _ _ dd Hbsin Hbu
                (ld_dm_of _ _ _ _ _ Hdmo Hcd hdr z ltac:(first [reflexivity | congruence])) (or_introl eq_refl) Hm Hgot ltac:(rewrite Hu; exact Hunit) Hsafe Hcok Hchk Hcf')
      as [Hd'|Hm'].
    * left. rewrite ?app_assoc in *. exact Hd'.
    * right. exists cd. split; [|split].
      -- rewrite ?app_assoc in *. exact Hm'.
      -- apply (cur_dict_ok_same _ k); [reflexivity|exact Hfp|]. cbn [next_cd sv_fp] in *. rewrite zstep_dm. exact Hcd.
      -- unfold hist_ok. intros Hx; congruence.
Qed.

End CM_R3Stab_1.
