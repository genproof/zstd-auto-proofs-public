(* FS3 streaming, case zdss_load: the loop invariant after a unit decoded in stable mode, from the
   new context's facts (v2 StreamSeg_load.v load_inv_stable_step). *)
Require Export Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3StGen.
Local Open Scope logic.

Section CM_L3StStep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma load_inv_stable_step3 : forall a k k' sv ipc opc oc1 dl ns oc' sv' cnt,
  dsa_ok a -> call_inv a k sv ipc opc oc1 dl -> dc_stable (a_st a) = true -> sv_ahead sv = nil ->
  c3_stable k' = c3_stable k -> c3_par k' = c3_par k -> c3_set k' = c3_set k -> c3_dict k' = c3_dict k ->
  fs_fParams (c3_fs k') = fs_fParams (c3_fs k) ->
  sf_nfp (c3_s k') = sf_nfp (c3_s k) -> sf_stage (c3_s k) = zdss_load ->
  sf_expOut (c3_s k') = sf_expOut (c3_s k) ->
  sf_mem (c3_s k') = sf_mem (c3_s k) -> sf_held (c3_s k') = sf_held (c3_s k) -> c3_sp k' = c3_sp k ->
  0 < ns -> ipc + ns <= a_isz a ->
  opc + Zlength cnt <= a_osz a -> Zlength oc' = a_osz a ->
  unchanged_outside oc1 oc' opc (a_osz a) ->
  sublist opc (opc + Zlength cnt) oc' = zbytes cnt -> bytes_ok cnt ->
  sv_ahead sv' = nil -> sv_dd sv' = sv_dd sv -> sf_stage (c3_s k') = zdss_read ->
  c_core true (Some (a_ob a, a_osz a)) (ss_out (dc_ss (a_st a)) ++ dl ++ cnt) k' sv' ->
  (dead (sm_of (a_st a)) ((a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ sublist ipc (ipc + ns) (a_ibs a)) \/
   exists cd, m_rel_cd (sm_of (a_st a)) ((a_sin a ++ sublist (a_ipos a) ipc (a_ibs a)) ++ sublist ipc (ipc + ns) (a_ibs a))
     (ss_out (dc_ss (a_st a)) ++ dl ++ cnt) (sv_fp sv') (sv_pend sv') cd /\
     cur_dict_ok (a_st a) k' (next_cd (sm_of (a_st a)) (sv_fp sv') cd)) ->
  call_inv a k' sv' (ipc + ns) (opc + Zlength cnt) oc' (dl ++ cnt).
Proof.
intros a k k' sv ipc opc oc1 dl ns oc' sv' cnt Ha Hi Hst Hah Hk1 Hk2 Hk3 Hk4 Hfp Hnfp Hsk Hkexp Hkm Hkh Hksp Hns Hisz Ho Hlo Hu
  Hsub Hbc Hah' Hdd' Hk' Hcore Hm.
destruct Ha as (_&_&_&_&_&_&_&_&_&Hopos&_&_&Hipos&_&Hlibs&_).
unfold call_inv in Hi. cbv zeta in Hi.
destruct Hi as (H1&H2&H3&H4&H5&H6&H7&H8&H9&H10&H11&H12&H13&H14&Hstout&H16&H17&H18&H19&H20&H21&H22).
rewrite Hst in Hstout. specialize (Hstout eq_refl).
pose proof (Zlength_nonneg cnt).
assert (Hold: sublist 0 opc oc' = sublist 0 opc oc1) by (apply (unch_sublist _ _ opc (a_osz a)); auto; lia).
unfold call_inv. cbv zeta.
split; [lia|]. split; [lia|]. split; [exact Hlo|].
split; [rewrite <- H4; apply (unch_sublist _ _ opc (a_osz a)); auto; lia|].
split; [rewrite Zlength_app; lia|].
split.
{ rewrite (sublist_split (a_opos a) opc (opc + Zlength cnt)) by lia.
  rewrite (unch_sublist oc1 oc' opc (a_osz a) (a_opos a) opc) by (auto; lia).
  rewrite H6, Hsub, map_app. reflexivity. }
split; [apply Forall_app; auto|].
split.
{ destruct H8 as (B1&B2&B3&B4&B5&B6&B7). unfold base_call. rewrite Hk1, Hk2, Hk3, Hk4, Hfp.
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  split; [exact B6|]. unfold mem_call, mem_room in *. rewrite Hkm, Hkh, Hk4. exact B7. }
split; [exact H9|]. split; [rewrite Hnfp; exact H10|]. split; [left; lia|].
split; [rewrite Hnfp; exact H12|].
split; [rewrite Hst; exact Hcore|].
split.
{ unfold sv_dd_ok in *. intros _ x buf Hx. rewrite Hdd' in Hx.
  specialize (H14 ltac:(rewrite Hsk; unfold zdss_read, zdss_load; lia) x buf Hx).
  unfold dd_src in *. rewrite Hk4. exact H14. }
split.
{ intros _. rewrite (sublist_split 0 opc (opc + Zlength cnt)) by lia.
  rewrite Hold, Hstout, Hsub, <- map_app, app_assoc. reflexivity. }
split; [rewrite Hah'; intros []; reflexivity|].
split; [intros _ Hf; rewrite Hst in Hf; discriminate|].
split.
{ unfold alive_ok. rewrite Hah', app_nil_r.
  replace (sublist (a_ipos a) (ipc + ns) (a_ibs a))
    with (sublist (a_ipos a) ipc (a_ibs a) ++ sublist ipc (ipc + ns) (a_ibs a))
    by (rewrite <- sublist_split by lia; reflexivity).
  rewrite app_assoc.
  destruct Hm as [Hm|(cd&Hm&Hc)]; [left; exact Hm|right; exists cd; split; [exact Hm|]; split; [exact Hc|]].
  unfold hist_ok. intros Hf. rewrite Hst in Hf. discriminate. }
split; [rewrite Hk'; intros Hx; unfold zdss_read, zdss_loadHeader in Hx; lia|].
split; [rewrite Hah'; rewrite Hah in H20; exact H20|].
split; [intros _ _; rewrite Hkexp; apply H21; [exact Hst|rewrite Hsk; unfold zdss_load, zdss_init; lia]|].
rewrite Hk'; intros Hx; unfold zdss_read, zdss_flush in Hx; lia.
Qed.

End CM_L3StStep_1.
