(* FS3 streaming, case zdss_loadHeader (on the stream relation's revision R2): err_why of the stable buffer
   smaller than the frame's declared content (zstd's dstSize_tooSmall check before the frame). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib Zstd.proof.dec.v3.FS.stream.lh.LH3RetGfh Zstd.proof.dec.v3.FS.stream.lh.LH3R2Why.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3RetG.
Require Zstd.proof.dec.FS.StreamModelFacts.
Require Zstd.proof.dec.v3.FS.stream.lh.LH3R2MFrame Zstd.proof.dec.v3.FS.stream.lh.LH3R2MFrameM Zstd.proof.dec.v3.FS.stream.lh.LH3R2MWalk.
Local Open Scope logic.


Module RS.
Section CM_LH3R2Small_RS.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.
Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Import Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2MFrame Zstd.proof.dec.v3.FS.stream.lh.LH3R2MFrameM
  Zstd.proof.dec.v3.FS.stream.lh.LH3R2MWalk.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma flat_map_fshift : forall d l, flat_map fr_content (map (fshift d) l) = flat_map fr_content l.
Proof. induction l; cbn; auto. rewrite IHl. reflexivity. Qed.

Lemma first_frame_content : forall md sel cd hb z h l, bytes_ok hb ->
  get_frame_header_m (md_magicless md) hb = FH_ok h -> fh_frameType h = 0 ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN ->
  series_frames_m md sel cd no_wlim (hb ++ z) = (l, TEnd) ->
  fh_contentSize h <= Zlength (flat_map fr_content l).
Proof.
  intros md sel cd hb z h l Hb G Ht Hu Hs.
  assert (G2: get_frame_header_m (md_magicless md) (hb ++ z) = FH_ok h) by (apply LH3RetG.RG.gfh_m_ext; auto).
  unfold series_frames_m in Hs. rewrite walk_S in Hs.
  destruct (wfirst md sel cd no_wlim (hb ++ z)) as [[[[k c] sk] cur']|t] eqn:E.
  2: { inversion Hs; subst. apply wfirst_end in E. apply (f_equal (@Zlength Z)) in E.
       pose proof (gfhm_len _ _ _ G). pose proof (starting_len_pos (md_magicless md)).
       rewrite Zlength_app in E. pose proof (Zlength_nonneg z). rewrite Zlength_nil in E. lia. }
  destruct (walk_m _ _ _ _ _ _ _) as [l0 t0] eqn:W. inversion Hs; subst l t0. clear Hs.
  cbn [flat_map mkrec fr_content]. rewrite Zlength_app. pose proof (Zlength_nonneg (flat_map fr_content l0)).
  unfold wfirst in E.
  destruct (Zlength (hb ++ z) <? starting_len (md_magicless md)); [discriminate|].
  replace (negb (md_magicless md) && is_skippable_magic (le_field (hb ++ z) 0 4)) with false in E.
  2: { destruct (md_magicless md) eqn:Hmg; [reflexivity|].
       destruct (gfhm_info _ _ _ G2) as [[_ [E1 _]] | [_ [_ [Hm _]]]]; [ congruence | ].
       rewrite (Hm eq_refl). reflexivity. }
  destruct (frame_dict _ _ _ _) as [d|]; [|discriminate].
  destruct (decode_frame_m md d no_wlim (hb ++ z)) as [c1 k1| | |] eqn:D; try discriminate.
  injection E as <- <- _ _.
  destruct (dfm_hdr_inv md d no_wlim (hb ++ z)) as [h' [G' [_ [_ [_ [_ [_ D']]]]]]]; try congruence.
  rewrite G2 in G'. injection G' as <-. rewrite D in D'.
  unfold df_tail in D'. cbv zeta in D'.
  destruct (LH3R2MBase.dblocks _ _ _ _ _ _ _ _) as [[out kb]|]; [|discriminate].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h)) eqn:C;
    [discriminate|].
  assert (out = c1).
  { repeat match type of D' with context [if ?b then _ else _] => destruct b end; congruence. }
  subst out. apply andb_false_iff in C. destruct C as [C|C].
  - apply negb_false_iff, Z.eqb_eq in C. contradiction.
  - apply negb_false_iff, Z.eqb_eq in C. lia.
Qed.

End CM_LH3R2Small_RS.
End RS.

Section CM_LH3R2Small_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma why_small : MF3 -> forall a w hb h, lh_ctx a w hb -> par_ok (dc_par (a_st a)) ->
  get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> c3_stable (w_k w) = true -> fh_frameType h <> 1 ->
  fh_contentSize h <> ZSTD_CONTENTSIZE_UNKNOWN -> a_osz a - w_opc w < fh_contentSize h ->
  err_why a (err_code ZSTD_error_dstSize_tooSmall).
Proof.
  intros HMF a w hb h Hc Hp Hh Hst Ht Hu Hlt.
  split.
  { apply dec_err_code; unfold ZSTD_error_dstSize_tooSmall, ZSTD_error_noForwardProgress_destFull,
      ZSTD_error_noForwardProgress_inputEmpty; lia. }
  destruct (rl_entry a w hb Hc) as (Hb & Hbh & Hok & Ha).
  destruct (rl_split a w hb Hc (rl_wmax _ Hp)) as [F | (dsin & recs & cd & Hsp)]; [ right; left; exact F | ].
  destruct (rl_gfh3 _ _ _ Hh Hbh) as (_ & _ & _ & _ & _ & _ & Hft & _).
  assert (Ht0: fh_frameType h = 0) by lia.
  assert (Hs1: dc_stable (a_st a) = true) by (destruct Hb as (Hb1 & _); congruence).
  assert (Hop: w_opc w = a_opos a /\ a_opos a = Zlength (ss_out (dc_ss (a_st a)))).
  { destruct Hc as (_ & _ & Hci & _ & _ & _ & _ & Hdl & _).
    destruct Hci as (_ & _ & _ & _ & Hdll & _). rewrite Hdl, Zlength_nil in Hdll.
    split; [ lia | ]. unfold dsa_ok in Ha. destruct Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlast & _).
    auto. }
  destruct Hop as (Hopc & Hop).
  right; right. split; [ exact Hs1 | ].
  intros s Hbs Hp' E.
  destruct Hsp as (Hbd & Hser & Hcur & Hall & Hout & _).
  unfold a_series in *.
  destruct (series_frames_m (dmode_w (dmode_of (dc_par (a_st a)))) (fst (st_sel (a_st a))) (snd (st_sel (a_st a)))
              (dp_wmax (dc_par (a_st a))) s) as [l t] eqn:S.
  cbn [snd] in E. subst t. cbn [fst].
  apply RL.series_wlim in S; [ | apply (rl_wmax _ Hp) ].
  rewrite Hall in Hp'. apply StreamModelFacts.is_prefix_ex in Hp'. destruct Hp' as [r ->].
  rewrite <- !app_assoc in S.
  unfold sm_series, sm_curafter in Hser, Hcur. cbn [sm_of sm_md sm_sel sm_cur] in Hser, Hcur.
  set (y := hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a) ++ r) in S.
  pose proof (LH3R2MWalk.series_app _ _ _ _ _ _ y Hser Hbd) as [Hsnd _].
  rewrite S, Hcur in Hsnd. cbn [snd] in Hsnd.
  destruct (series_frames_m (dmode_w (dmode_of (dc_par (a_st a)))) (fst (st_sel (a_st a))) cd no_wlim y) as [l2 t2] eqn:S2.
  cbn [snd] in Hsnd. subst t2.
  rewrite <- Hcur in S2.
  rewrite (LH3R2MWalk.series_app_full _ _ _ _ _ _ _ _ _ Hser Hbd S2 ltac:(discriminate)) in S.
  injection S as <-. rewrite Hcur in S2.
  rewrite flat_map_app, Zlength_app, RS.flat_map_fshift, <- Hout.
  assert (Hmg: md_magicless (dmode_w (dmode_of (dc_par (a_st a)))) = lh_mg (w_k w)) by apply (rl_mg _ _ Hb).
  rewrite <- Hmg in Hh.
  pose proof (RS.first_frame_content _ _ _ hb _ h l2 Hbh Hh Ht0 Hu S2). lia.
Qed.

End CM_LH3R2Small_2.
