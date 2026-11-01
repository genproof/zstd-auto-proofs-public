(* FS3 streaming, case zdss_read: the capacity case of a failing unit (v3 model, S3ModelDefs):
   the frame's content, in any series the model decodes (window limit), holds the unit's output (more than
   cap bytes) after zp_out z. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.ParamsH Zstd.proof.model.ParamsW.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3ErABase Zstd.proof.dec.v3.FS.stream.load.L3ErAFrame Zstd.proof.dec.v3.FS.stream.load.L3ErAFrameM Zstd.proof.dec.v3.FS.stream.load.L3ErAWalk Zstd.proof.dec.v3.FS.stream.load.L3ErBBlk.
Local Open Scope Z_scope.

Module ZCap3.
Local Open Scope bool_scope.

(* a walk with any window limit w2 that ends over dsin ++ y starts with dsin's frames (no_wlim) *)
Lemma walk_app_wlim_full : forall md sel f cur w1 w2 s off l, walk_m f md sel cur w1 s off = (l, TEnd) -> bytes_ok s ->
  forall y F L, (length l <= F)%nat -> walk_m F md sel cur w2 (s ++ y) off = (L, TEnd) ->
  exists l2, L = l ++ l2 /\
    walk_m (F - length l) md sel (walk_cur f md sel cur w1 s) w2 y (off + Zlength s) = (l2, TEnd).
Proof.
  intros md sel. induction f; intros cur w1 w2 s off l H Hs y F L HF HL; [discriminate|].
  rewrite walk_S in H. rewrite walk_cur_S. destruct (wfirst md sel cur w1 s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w1 (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    assert (Hk: Z.to_nat k <> 0%nat).
    { intro Hk. pose proof (walk_loop _ _ _ _ _ _ _ _ _ E Hk f (off + k)). rewrite Hk in E2. simpl in E2.
      rewrite E2 in H. discriminate. }
    destruct (wfirst_ext _ _ _ _ _ _ _ _ _ y E Hs) as [Hkl Hext].
    destruct F as [|F]; [simpl in HF; lia|]. simpl in HF.
    rewrite walk_S, Hext in HL.
    destruct (wfirst_wlim _ _ _ _ w2 _ _ _ _ _ E) as [E'|E']; rewrite E' in HL; [|discriminate].
    rewrite skipn_app_le in HL by (rewrite Zlength_correct in Hkl; lia).
    destruct (walk_m F md sel cur' w2 (skipn (Z.to_nat k) s ++ y) (off + k)) as [L0 T0] eqn:W.
    inversion HL; subst; clear HL.
    destruct (IHf cur' w1 w2 _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F L0 ltac:(lia) W) as [l2 [-> IH]].
    exists l2. split; [reflexivity|].
    rewrite Zlength_skipn in IH by (pose proof (wfirst_len _ _ _ _ _ _ _ _ _ E); pose proof (starting_len_pos (md_magicless md)); lia).
    replace (off + k + (Zlength s - k)) with (off + Zlength s) in IH by lia.
    simpl. exact IH.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    exists L. split; [reflexivity|]. simpl. rewrite Nat.sub_0_r, Z.add_0_r. exact HL.
Qed.

Lemma series_wlim_split : forall md sel cur w2 dsin recs y L,
  series_frames_m md sel cur no_wlim dsin = (recs, TEnd) -> bytes_ok dsin ->
  series_frames_m md sel cur w2 (dsin ++ y) = (L, TEnd) ->
  exists F off l2, L = recs ++ l2 /\ walk_m F md sel (series_cur md sel cur no_wlim dsin) w2 y off = (l2, TEnd).
Proof.
  unfold series_frames_m, series_cur. intros md sel cur w2 dsin recs y L H Hb E.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  destruct (walk_app_wlim_full md sel _ _ _ w2 _ _ _ H Hb y (S (length (dsin ++ y))) L ltac:(rewrite length_app; lia) E) as [l2 [-> W]].
  eauto.
Qed.

Lemma df_fin_ok : forall md h s r c k, df_fin md h s r = FOk c k -> exists k', r = Some (c, k').
Proof.
  unfold df_fin; intros md h s r c k H. destruct r as [[o k0]|]; [|discriminate].
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    try discriminate; inversion H; subst; eauto.
Qed.

Lemma firstn_len_ge : forall (a b: list Z) n, Zlength a <= n -> Zlength a <= Zlength (firstn (Z.to_nat n) (a ++ b)).
Proof.
  intros. rewrite firstn_app, firstn_all2 by (rewrite Zlength_correct in H; lia). rewrite Zlength_app.
  pose proof (Zlength_nonneg (firstn (Z.to_nat n - length a) b)). lia.
Qed.

Lemma firstn_exact : forall (a b: list Z) n, Zlength a = n -> firstn (Z.to_nat n) (a ++ b) = a.
Proof.
  intros. subst. rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  reflexivity.
Qed.

(* the first frame of a walk that ends (a Zstandard frame with the dictionary dm) *)
Lemma walk_first_content : forall md sel cd w y F off l2 dm, walk_m F md sel cd w y off = (l2, TEnd) -> y <> nil ->
  negb (md_magicless md) && is_skippable_magic (le_field y 0 4) = false ->
  frame_dict (md_magicless md) sel cd y = Some dm ->
  exists c k, decode_frame_m md dm w y = FOk c k /\ Zlength c <= Zlength (flat_map fr_content l2).
Proof.
  intros md sel cd w y F off l2 dm E Hy Hk Hf.
  destruct F as [|F]; [discriminate|]. rewrite walk_S in E.
  destruct (wfirst md sel cd w y) as [[[[k c] sk] cur']|t] eqn:W.
  - destruct (walk_m F md sel cur' w _ _) as [l' t'] eqn:E'. inversion E; subst. clear E.
    exists c, k. split.
    + unfold wfirst in W. destruct (Zlength y <? _); [discriminate|]. rewrite Hk, Hf in W.
      destruct (decode_frame_m md dm w y); inversion W; auto.
    + cbn [flat_map fr_content mkrec]. rewrite Zlength_app.
      pose proof (Zlength_nonneg (flat_map fr_content l')). lia.
  - inversion E; subst. apply wfirst_end in W. contradiction.
Qed.

Lemma cap_case3 : forall md sel cd fb hdr z H u cap r w c k,
  bytes_ok fb -> cur_rel md sel cd fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) ->
  (H = zp_hist z \/ (H = nil /\ md_dwin md = true /\ fh_windowSize (zp_h z) < Zlength (zp_out z))) ->
  cont_err (FP_zstd hdr z) H u cap -> ~ cont_err (FP_zstd hdr z) H u (zp_bsm z) ->
  decode_frame_m md (zp_dm z) w (fb ++ u ++ r) = FOk c k ->
  Zlength (zp_out z) + cap < Zlength c.
Proof.
  intros md sel cd fb hdr z H u cap r w c k Hbf Hcr Hph Hun Hz Herr Hnm D.
  unfold cur_rel in Hcr.
  destruct Hcr as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb Hp]]]]]]]]]]].
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun. unfold cont_err in Herr, Hnm. cbv beta iota zeta in Herr, Hnm.
  destruct (zp_ph z) as [|bh| |] eqn:Eph; try (exfalso; apply Hnm; exact Herr).
  destruct Hp as [-> [H3 [c0 [Ec [Hc [Hg Eo]]]]]]. destruct Hun as [c' [Ec' Hn]]. unfold ZSTD_blockHeaderSize in H3.
  rewrite Ec in Ec'. inversion Ec'; subst c'.
  apply bytes_ok_app in Hbr. destruct Hbr as [_ Hbr]. apply bytes_ok_app in Hbr. destruct Hbr as [Hbb _].
  set (t := bh ++ zp_got z ++ u ++ r).
  assert (Et: (hdr ++ zp_bl z ++ bh ++ zp_got z) ++ u ++ r = hdr ++ zp_bl z ++ t)
    by (unfold t; rewrite !app_assoc; reflexivity).
  rewrite Et in D.
  pose proof (Zlength_nonneg (zp_got z)). pose proof (Zlength_nonneg u). pose proof (Zlength_nonneg r).
  assert (Hlt: Zlength t = 3 + Zlength (zp_got z) + Zlength u + Zlength r) by (unfold t; rewrite !Zlength_app; lia).
  rewrite Hbsm in Hbp.
  destruct (dfm_cur md (zp_dm z) w hdr (zp_h z) (zp_bl z) (zp_ts z) outc t G Hl Ht Hd Hbh Hbp)
    as [fuel [Hf E2]]; [rewrite Zlength_app; pose proof (Zlength_nonneg (zp_bl z)); lia|].
  rewrite E2 in D. destruct (fh_windowSize (zp_h z) >? w); [discriminate|].
  apply df_fin_ok in D. destruct D as [k' D].
  destruct fuel as [|fuel]; [rewrite Zlength_correct in Hlt; lia|].
  unfold oshift in D. rewrite db_S_eq in D. rewrite <- Hbsm in D.
  destruct (block_res _ _ _ t outc _ _) as [[[[st2 out2] kb] lst]|] eqn:Eb; [|discriminate].
  assert (Hle: Zlength out2 <= Zlength c).
  { destruct lst.
    - inversion D; subst. lia.
    - destruct (dblocks _ fuel st2 _ _ out2 _ _) as [[o k2]|] eqn:D2; [|discriminate].
      inversion D; subst. destruct (db_out _ _ _ _ _ _ _ _ _ _ D2) as [d ->].
      rewrite Zlength_app. pose proof (Zlength_nonneg d). lia. }
  clear D.
  assert (Ect: cblock_size t = Some c0) by (unfold t; rewrite cblock_size_app; auto; lia).
  destruct (Z_le_gt_dec c0 (Zlength t - 3)) as [Hin|Hout].
  2:{ unfold block_res in Eb. rewrite Ect in Eb. unfold ZSTD_blockHeaderSize in Eb.
      replace (c0 >? Zlength t - 3) with true in Eb by (symmetry; apply Zgtb_gt; lia). discriminate. }
  rewrite (br_eq _ _ _ _ _ _ _ c0) in Eb by auto. unfold blk_body in Eb.
  assert (Ebp: block_props_of t = block_props_of bh) by (unfold t; apply block_props_app; lia).
  assert (Esl: slice t 3 c0 = firstn (Z.to_nat c0) (zp_got z ++ u ++ r)) by (unfold t; apply slice_hdr; auto).
  rewrite Ebp, Esl in Eb.
  destruct (bp_type (block_props_of bh) =? 0) eqn:T0.
  - destruct Herr as [Hu|Hm]; [|exfalso; apply Hnm; right; exact Hm].
    replace (c0 >? zp_bsm z) with false in Eb by (symmetry; apply Zgtb_le; lia).
    injection Eb as _ Eb2 _ _. subst out2.
    rewrite app_assoc in Hle. pose proof (firstn_len_ge (zp_got z ++ u) r c0 ltac:(rewrite Zlength_app; lia)) as Hf2.
    rewrite Zlength_app in Hle. rewrite Eo, Zlength_app. rewrite Zlength_app in Hf2. lia.
  - destruct Hph as [Hph|Hg0]; [rewrite Hph in T0; discriminate|].
    destruct Hn as [_ Hn]. rewrite Hg0 in Eb. cbn [app] in Eb. rewrite firstn_exact in Eb by auto.
    destruct (bp_type (block_props_of bh) =? 1) eqn:T1.
    + destruct Herr as [Hcap|Hm]; [|exfalso; apply Hnm; right; exact Hm].
      assert (Ho: bp_origSize (block_props_of bh) <= zp_bsm z)
        by (apply Z.nlt_ge; intro; apply Hnm; left; lia).
      replace (orb (bp_origSize (block_props_of bh) >? zp_bsm z) (c0 >? zp_bsm z))
        with false in Eb by (symmetry; apply Bool.orb_false_iff; split; apply Zgtb_le; lia).
      injection Eb as _ Eb2 _ _. subst out2.
      pose proof (origSize_nonneg _ Hbb).
      change (Z.shiftr (le_field bh 0 3) 3) with (bp_origSize (block_props_of bh)) in Hle.
      rewrite Zlength_app, Zlength_repeat, Z2Nat.id in Hle by lia. rewrite Eo. lia.
    + rewrite Eo in Herr, Hnm, Hz.
      destruct (dec_block _ _ _ outc u _ _) as [[ts2 c2]|] eqn:Edb; [|discriminate].
      rewrite (dec_hist _ _ _ H _ _ _ _ _ Hz Edb) in Herr, Hnm.
      destruct Herr as [Hcap|Hm]; [|exfalso; apply Hnm; right; exact Hm].
      injection Eb as _ Eb2 _ _. subst out2.
      rewrite Zlength_app in Hle. rewrite Eo. lia.
Qed.

End ZCap3.

Lemma zunit_err_cap3 : MF3 -> forall sm dsin recs fb hdr z H u cap s,
  bytes_ok dsin -> bytes_ok fb ->
  sm_series sm (sm_cur sm) no_wlim dsin = (recs, TEnd) ->
  cur_rel (sm_md sm) (sm_sel sm) (sm_curafter sm (sm_cur sm) dsin) fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u -> zhist_ok sm z H ->
  cont_err (FP_zstd hdr z) H u cap -> 0 <= cap ->
  (* a unit failing even with a capacity of Block_Maximum_Size fails the frame (zunit_err0_3 / P_zunit_err) *)
  (cont_err (FP_zstd hdr z) H u (zp_bsm z) -> fbad sm (sm_curafter sm (sm_cur sm) dsin) (fb ++ u)) ->
  bytes_ok s -> is_prefix (dsin ++ fb ++ u) s -> snd (sm_series sm (sm_cur sm) (sm_wl sm) s) = TEnd ->
  Zlength (flat_map fr_content recs) + Zlength (zp_out z) + cap <
    Zlength (flat_map fr_content (fst (sm_series sm (sm_cur sm) (sm_wl sm) s))).
Proof.
  intros M sm dsin recs fb hdr z H u cap s Hbd Hbf Ef Hcr Hph Hun Hbu Hz Herr Hcap Hbad Hbs Hpre Hend.
  assert (Hnm: ~ cont_err (FP_zstd hdr z) H u (zp_bsm z)).
  { intro Hm. exact (mf_bad_of_fbad M sm _ dsin recs (fb ++ u) s Hbd Ef eq_refl (Hbad Hm) Hpre Hend). }
  destruct (is_prefix_ex _ _ Hpre) as [r ->].
  destruct (sm_series sm (sm_cur sm) (sm_wl sm) ((dsin ++ fb ++ u) ++ r)) as [L t] eqn:EL.
  simpl in Hend |- *. subst t. rewrite <- !app_assoc in EL.
  unfold sm_series in EL, Ef.
  destruct (ZCap3.series_wlim_split _ _ _ _ dsin recs (fb ++ u ++ r) L Ef Hbd EL) as (F & off & l2 & -> & W).
  pose proof Hcr as Hcr'. unfold cur_rel in Hcr'.
  destruct Hcr' as [G [_ [Ht [Hfd [_ [_ [_ [outc [lst [_ [Hfb _]]]]]]]]]]].
  assert (Hbh: bytes_ok hdr) by (rewrite Hfb in Hbf; apply bytes_ok_app in Hbf; tauto).
  assert (Ey: fb ++ u ++ r = hdr ++ ((zp_bl z ++ match zp_ph z with ZP_body bh => bh ++ zp_got z | _ => zp_got z end) ++ u ++ r))
    by (rewrite Hfb, !app_assoc; reflexivity).
  assert (Hy: fb ++ u ++ r <> nil) by (rewrite Ey; apply app_ne_nil_l; eapply hdr_ne_nil3; eauto).
  assert (Hk: (negb (md_magicless (sm_md sm)) && is_skippable_magic (le_field (fb ++ u ++ r) 0 4))%bool = false)
    by (rewrite Ey; eapply hdr_skip_false3; eauto).
  assert (Hf: frame_dict (md_magicless (sm_md sm)) (sm_sel sm) (sm_curafter sm (sm_cur sm) dsin) (fb ++ u ++ r) = Some (zp_dm z))
    by (rewrite Ey, (frame_dict_ext _ _ _ _ _ _ G (bytes_ok_byte_at _ _ Hbh)); exact Hfd).
  destruct (ZCap3.walk_first_content _ _ _ _ _ _ _ _ _ W Hy Hk Hf) as (c & k & D & Hge).
  pose proof (ZCap3.cap_case3 _ _ _ fb hdr z H u cap r _ c k Hbf Hcr Hph Hun Hz Herr Hnm D).
  rewrite flat_map_app, Zlength_app. lia.
Qed.
