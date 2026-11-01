(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): the model side of the returns of
   case 1: the window limit, the split of the stream's bytes at the entry, why the error returns fail the model. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Zstd.proof.dec.FS.StreamModelFacts.
Local Open Scope logic.


Module RL.
Section CM_LH3R2Lib_RL.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.
Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma dfm_wlim : forall md d w1 w2 s c k, w1 <= w2 -> decode_frame_m md d w1 s = FOk c k ->
  decode_frame_m md d w2 s = FOk c k.
Proof.
  intros md d w1 w2 s c k Hw H. unfold decode_frame_m in *.
  destruct (Zlength s <? _); [discriminate|].
  destruct (negb _ && negb _); [discriminate|].
  destruct (Zlength s <? _); [discriminate|].
  destruct (negb (Z.land _ 8 =? 0)); [discriminate|].
  destruct (negb _ && _); [discriminate|].
  destruct (get_frame_header_m _ s) as [ | | h]; try discriminate.
  destruct (fh_windowSize h >? w1) eqn:E1; [discriminate|].
  replace (fh_windowSize h >? w2) with false by (symmetry; rewrite Z.gtb_ltb in *; apply Z.ltb_ge; apply Z.ltb_ge in E1; lia).
  exact H.
Qed.

Lemma walk_wlim : forall f md sel cur w1 w2 s off l, w1 <= w2 ->
  walk_m f md sel cur w1 s off = (l, TEnd) -> walk_m f md sel cur w2 s off = (l, TEnd).
Proof.
  induction f; intros md sel cur w1 w2 s off l Hw H; [discriminate|].
  cbn [walk_m] in *.
  destruct (Zlength s <? _); [exact H|].
  destruct (negb _ && _).
  - destruct (skippable_frame_size s); [|exact H].
    destruct (walk_m f md sel _ w1 _ _) as [l0 t0] eqn:W. inversion H; subst.
    rewrite (IHf _ _ _ _ _ _ _ _ Hw W). reflexivity.
  - destruct (frame_dict _ _ _ _) as [d|]; [|exact H].
    destruct (decode_frame_m md d w1 s) eqn:D; try discriminate.
    rewrite (dfm_wlim _ _ _ _ _ _ _ Hw D).
    destruct (walk_m f md sel (Some d) w1 _ _) as [l0 t0] eqn:W. inversion H; subst.
    rewrite (IHf _ _ _ _ _ _ _ _ Hw W). reflexivity.
Qed.

Lemma series_wlim : forall md sel cur w s l, w <= no_wlim ->
  series_frames_m md sel cur w s = (l, TEnd) -> series_frames_m md sel cur no_wlim s = (l, TEnd).
Proof. intros. unfold series_frames_m in *. eapply walk_wlim; eauto. Qed.

Lemma prefix_trans : forall x y s, is_prefix x y -> is_prefix y s -> is_prefix x s.
Proof.
  intros x y s H1 H2. apply StreamModelFacts.is_prefix_ex in H1, H2.
  destruct H1 as [r1 ->]. destruct H2 as [r2 ->]. rewrite <- app_assoc. apply StreamModelFacts.is_prefix_app.
Qed.

End CM_LH3R2Lib_RL.
End RL.

Section CM_LH3R2Lib_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the entry of case 1 ---------- *)

Lemma rl_ahead0 : forall a w hb, lh_ctx a w hb -> ss_ahead (dc_ss (a_st a)) = 0 /\ a_sin a = ss_in (dc_ss (a_st a)).
Proof.
  intros a w hb (Ha & Hst & Hci & _ & _ & _ & _ & _ & Hah & _).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsin & _).
  rewrite Hah, app_nil_r in Hsin. split; [ | exact Hsin ]. unfold a_sin in Hsin.
  destruct Hst as (_ & H01 & Hle & _).
  apply (f_equal (@Zlength Z)) in Hsin. rewrite Zlength_sublist in Hsin by lia. lia.
Qed.

(* every series extending what the stream read and the caller's whole input fails (err_why's second case) *)
Definition lh_fails (a: dsa) : Prop :=
  forall s, bytes_ok s -> is_prefix (a_all a) s -> snd (a_series a s) <> TEnd.

Lemma rl_fails_dead : forall a x, dp_wmax (dc_par (a_st a)) <= no_wlim ->
  dead (sm_of (a_st a)) x -> is_prefix x (a_all a) -> lh_fails a.
Proof.
  intros a x Hw Hd Hx s _ Hs E.
  pose proof (proj1 Hd s (RL.prefix_trans _ _ _ Hx Hs)) as Hd0; clear Hd; rename Hd0 into Hd. unfold sm_of in Hd; cbn [sm_md sm_sel sm_cur] in Hd.
  unfold a_series in E.
  destruct (series_frames_m (dmode_w (dmode_of (dc_par (a_st a)))) (fst (st_sel (a_st a))) (snd (st_sel (a_st a)))
              (dp_wmax (dc_par (a_st a))) s) as [l t] eqn:S.
  cbn [snd] in E. subst t.
  apply RL.series_wlim in S; auto.
  rewrite S in Hd. cbn [snd] in Hd. discriminate.
Qed.

(* the model at the entry: dead, or the frames before the header are complete *)
Definition lh_split_ok (a: dsa) (w: lw) (hb: list Z) (dsin: list Z) (recs: list frec) (cd: option dict_model) : Prop :=
  let sm := sm_of (a_st a) in
  bytes_ok dsin /\ sm_series sm (sm_cur sm) no_wlim dsin = (recs, TEnd) /\ sm_curafter sm (sm_cur sm) dsin = cd /\
  a_all a = dsin ++ hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a) /\
  ss_out (dc_ss (a_st a)) = flat_map fr_content recs /\ cur_dict_ok (a_st a) (w_k w) cd.

Lemma rl_split : forall a w hb, lh_ctx a w hb ->
  dp_wmax (dc_par (a_st a)) <= no_wlim -> lh_fails a \/ exists dsin recs cd, lh_split_ok a w hb dsin recs cd.
Proof.
  intros a w hb Hc Hw.
  destruct (rl_ahead0 a w hb Hc) as [H0 Hsin].
  destruct Hc as (Ha & Hst & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & _).
  destruct Hci as (Hip & _ & _ & _ & _ & _ & _ & _ & Hbin & _ & _ & _ & _ & _ & _ & _ & _ & Hmod & _).
  assert (Hib: Zlength (a_ibs a) = a_isz a /\ bytes_ok (a_ibs a) /\ 0 <= a_ipos a) by (unfold dsa_ok in Ha; tauto).
  destruct Hib as (Hibl & Hibb & Hip0).
  assert (Hall: a_all a = (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a) ++ nil) ++
                          sublist (w_ipc w) (a_isz a) (a_ibs a)).
  { unfold a_all. rewrite H0, Z.add_0_r, Hsin, app_nil_r, <- app_assoc. f_equal.
    rewrite <- sublist_split; auto; lia. }
  rewrite Hah, Hdl in Hmod. unfold alive_ok in Hmod. rewrite Hfp, Hpend in Hmod.
  destruct Hmod as [Hd | (cd & Hm & Hcd & _)].
  - left. apply (rl_fails_dead a _ Hw Hd). rewrite Hall. apply StreamModelFacts.is_prefix_app.
  - right. destruct Hm as (dsin & fb & recs & Hs & Hser & Hcur & Hcr & Hout).
    cbn [cur_rel] in Hcr. destruct Hcr as [Hfb _]. subst fb.
    assert (Hbs: bytes_ok (a_sin a ++ sublist (a_ipos a) (w_ipc w) (a_ibs a) ++ nil)).
    { unfold bytes_ok in *. rewrite app_nil_r. apply Forall_app; split; auto. apply Forall_sublist; auto. }
    rewrite Hs in Hbs.
    exists dsin, recs, cd. split; [ unfold bytes_ok in *; apply Forall_app in Hbs; tauto | ].
    split; [ exact Hser | ]. split; [ exact Hcur | ].
    split; [ rewrite Hall, Hs, <- app_assoc; reflexivity | ].
    split; [ cbn [fp_content] in Hout; rewrite !app_nil_r in Hout; exact Hout | ].
    cbn [next_cd] in Hcd. exact Hcd.
Qed.

Lemma rl_fails_fbad : MF3 -> forall a w hb dsin recs cd y, lh_split_ok a w hb dsin recs cd ->
  is_prefix y (sublist (w_ipc w) (a_isz a) (a_ibs a)) -> fbad (sm_of (a_st a)) cd (hb ++ y) -> lh_fails a.
Proof.
  intros HMF a w hb dsin recs cd y (Hb & Hs & Hcur & Hall & _) Hy Hf s _ Hp.
  pose proof (mf_bad_of_fbad HMF (sm_of (a_st a)) cd dsin recs (hb ++ y) s Hb Hs Hcur Hf) as H.
  apply H. eapply RL.prefix_trans; [ | exact Hp ]. rewrite Hall.
  apply StreamModelFacts.is_prefix_ex in Hy. destruct Hy as [r ->].
  rewrite !app_assoc. apply StreamModelFacts.is_prefix_app.
Qed.

Lemma rl_fails_fdead : MF3 -> forall a w hb dsin recs cd y, dp_wmax (dc_par (a_st a)) <= no_wlim ->
  lh_split_ok a w hb dsin recs cd ->
  is_prefix y (sublist (w_ipc w) (a_isz a) (a_ibs a)) -> fdead (sm_of (a_st a)) cd (hb ++ y) -> lh_fails a.
Proof.
  intros HMF a w hb dsin recs cd y Hw Hsp Hy Hf. destruct Hsp as (Hb & Hs & Hcur & Hall & _).
  apply (rl_fails_dead a (dsin ++ hb ++ y) Hw).
  - apply (mf_dead_of_fdead HMF (sm_of (a_st a)) cd dsin recs (hb ++ y) Hb Hs Hcur Hf).
  - rewrite Hall. apply StreamModelFacts.is_prefix_ex in Hy. destruct Hy as [r ->].
    rewrite !app_assoc. apply StreamModelFacts.is_prefix_app.
Qed.

(* ---------- the context after the case (base_call) ---------- *)

(* a copy of LH3G1's g1_dict_rel *)
Lemma rl_dict_rel : hs_probe_ok -> forall st k hb kk v tbl d1 did1,
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> dict_rel3 st d1.
Proof.
intros Hpr st k hb kk v tbl d1 did1 Hb Hsel.
destruct Hb as (_ & _ & Hset & Hdr & _).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb.
destruct (sel_on (c3_par k) (c3_sp k)).
- destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict.
  destruct (eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval) as [E|E]; [ exact Hdr | ].
  right. unfold sel_r in *.
  destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [[Hn | Hin] _]; [ contradiction | ].
  rewrite Hset in Hin. split.
  + intro Hnil. rewrite Hnil in Hin. contradiction.
  + unfold dict_switched, switch_fields. cbn. rewrite Hset. auto.
- destruct Hsb as [Hd1 _]. subst d1. exact Hdr.
Qed.

Definition not_ref (od: option dictref) : Prop :=
  forall dr, od = Some dr -> match dr_src dr with DSRef _ => False | _ => True end.

Lemma rl_not_ref : forall a, dsa_ok a -> not_ref (dc_dict (a_st a)).
Proof.
  intros a Ha dr E. destruct Ha as (_ & _ & _ & _ & _ & _ & _ & Hsd & _).
  unfold stream_dict_ok in Hsd. rewrite E in Hsd. destruct Hsd as [[_ Hs] _].
  destruct (dr_src dr); auto.
Qed.

(* a copy of LH3G2's getddict_rel3 *)
Lemma rl_getddict_rel3 : forall st d, dict_rel3 st d -> not_ref (dc_dict st) ->
  dict_rel3 st (snd (getddict_res d)).
Proof.
  intros st d Hd Hn. unfold getddict_res.
  destruct Hd as [Hd|[Hne Hsw]].
  - destruct (dc_dict st) as [dr|] eqn:E.
    + specialize (Hn dr eq_refl). unfold dict_rel3_of in Hd. destruct (dr_src dr) eqn:Es; try contradiction.
      * assert (Hd0 := Hd). destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
        -- destruct Hd as (? & ->). cbn. left. rewrite E. unfold dict_rel3_of. rewrite Es, Ez. tauto.
        -- assert (Hu: df_uses d = -1) by (destruct Hd as (_ & ? & ? & ? & _ & _ & ? & _); auto).
           rewrite Hu. cbn. left. rewrite E. unfold dict_rel3_of.
           rewrite Es, Ez. exact Hd0.
      * assert (Hu: df_uses d = -1) by (destruct Hd as (_ & _ & _ & _ & _ & ? & _); auto).
        rewrite Hu. cbn. left. rewrite E. unfold dict_rel3_of. rewrite Es. exact Hd.
    + unfold dict_rel3_of in Hd. destruct Hd as [Hu _]. rewrite Hu. cbn. left. rewrite E. cbn. auto.
  - assert (Hu: df_uses d = -1) by (destruct Hsw as (_ & ? & _); auto).
    rewrite Hu. cbn. right. auto.
Qed.

(* the dictionary fields after the shortcut (getDDict's or a member of the set) keep the local DDict or have none *)
Lemma rl_lhB_redict : forall k1 d', lhB_dict k1 d' -> redict_ok (c3_dict k1) d'.
Proof.
  intros k1 d' [-> | (_ & q & _ & ->)]; [ apply redict_ok_getddict | right; reflexivity ].
Qed.

(* the allocator's bytes besides the context, the stream buffer and the local DDict: nonnegative (the set's) *)
Lemma rl_ctx_held : forall DENT TABS gv p k,
  ctx_rep3 DENT TABS gv p k |-- !! (0 <= sf_held (c3_s k) - local_held (c3_dict k)).
Proof.
  intros. unfold ctx_rep3, ctx_body3. sep_apply hset_rep_held. entailer!.
Qed.

Lemma rl_st_held : forall DENT TABS a w,
  lh_st DENT TABS a w |-- !! (0 <= sf_held (c3_s (w_k w)) - local_held (c3_dict (w_k w))).
Proof.
  intros. unfold lh_st, ds_LI_S. go_lowerx. sep_apply rl_ctx_held. entailer!.
Qed.

(* the selection keeps the allocator's other bytes (held_redict) *)
Lemma rl_kA_held : forall k v d1 did1,
  sf_mem (c3_s (k_A k v d1 did1)) = sf_mem (c3_s k) /\
  sf_held (c3_s (k_A k v d1 did1)) - local_held (c3_dict (k_A k v d1 did1)) =
    sf_held (c3_s k) - local_held (c3_dict k).
Proof.
  intros. unfold k_A, k_redict. cbn. split; [ reflexivity | apply held_redict_set ].
Qed.

(* piece C's ZSTD_getDDict keeps them too *)
Lemma rl_lhC_held : forall k1 hb h c,
  sf_mem (c3_s (lhC_k k1 hb h c)) = sf_mem (c3_s k1) /\
  sf_held (c3_s (lhC_k k1 hb h c)) - local_held (c3_dict (lhC_k k1 hb h c)) =
    sf_held (c3_s k1) - local_held (c3_dict k1).
Proof.
  intros. unfold lhC_k. cbn [c3_s c3_dict]. split; [ reflexivity | apply held_redict_set ].
Qed.

(* and the shortcut (its dictionary fields d') *)
Lemma rl_lhB_held : forall k1 fs' d' lxb',
  sf_mem (c3_s (lhB_k k1 fs' d' lxb')) = sf_mem (c3_s k1) /\
  sf_held (c3_s (lhB_k k1 fs' d' lxb')) - local_held (c3_dict (lhB_k k1 fs' d' lxb')) =
    sf_held (c3_s k1) - local_held (c3_dict k1).
Proof.
  intros. unfold lhB_k, lhB_s. cbn. split; [ reflexivity | apply held_redict_set ].
Qed.

(* the call's allocator facts for a context k' with k's allocator and other bytes, whose dictionary fields keep
   k's local DDict or have none *)
Lemma rl_mem_call_with : forall st k k', mem_call st k ->
  redict_ok (c3_dict k) (c3_dict k') -> sf_mem (c3_s k') = sf_mem (c3_s k) ->
  sf_held (c3_s k') - local_held (c3_dict k') = sf_held (c3_s k) - local_held (c3_dict k) ->
  0 <= sf_held (c3_s k') - local_held (c3_dict k') ->
  mem_call st k'.
Proof.
  intros st k k' (Hm & Hr & Hl) Hd Em Eh H0. unfold mem_call. rewrite Em.
  split; [ exact Hm | ]. split; [ | exact (local_mem_redict _ _ _ Hd Hl) ].
  apply (mem_room_le (c3_s k)); [ exact Em | | exact Hr ].
  pose proof (local_held_redict_le _ _ Hd). pose proof (local_held_nonneg (c3_dict k')). lia.
Qed.

(* the call's facts for a context k' that keeps k's abstract parts and allocator *)
Lemma rl_base_with : forall st k k', base_call st k -> dict_rel3 st (c3_dict k') ->
  c3_stable k' = c3_stable k -> c3_par k' = c3_par k -> c3_set k' = c3_set k -> fp_ok (fs_fParams (c3_fs k')) ->
  redict_ok (c3_dict k) (c3_dict k') -> sf_mem (c3_s k') = sf_mem (c3_s k) ->
  sf_held (c3_s k') - local_held (c3_dict k') = sf_held (c3_s k) - local_held (c3_dict k) ->
  0 <= sf_held (c3_s k') - local_held (c3_dict k') ->
  base_call st k'.
Proof.
  intros st k k' (H1 & H2 & H3 & _ & H5 & _ & Hm) Hd E1 E2 E3 Hf Hr Em Eh H0. unfold base_call.
  rewrite E1, E2, E3. do 6 (split; [assumption|]).
  exact (rl_mem_call_with _ _ _ Hm Hr Em Eh H0).
Qed.

End CM_LH3R2Lib_2.
