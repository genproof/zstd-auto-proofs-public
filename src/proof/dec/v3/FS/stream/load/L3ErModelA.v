(* FS3 streaming, case zdss_read: model facts for the error path (v3 model, S3ModelDefs). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelStmts.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Xxh64 Zstd.proof.dec.v3.FS.stream.load.L3ErABase Zstd.proof.dec.v3.FS.stream.load.L3ErAFrame Zstd.proof.dec.v3.FS.stream.load.L3ErAFrameM Zstd.proof.dec.v3.FS.stream.load.L3ErAWalk Zstd.proof.dec.v3.FS.stream.load.L3ErAUnit1.
Import ListNotations.
Local Open Scope Z_scope.

(* a walk that ends under one window limit never stops at an undecoded frame under another one (a frame
   decoded under the first is decoded, or rejected at its header, under the second) *)
Lemma walk_end_not_unk3 : forall md sel f cur w w' s off l,
  walk_m f md sel cur w s off = (l, TEnd) -> snd (walk_m f md sel cur w' s off) <> TUnk.
Proof.
  intros md sel. induction f as [|f IH]; intros cur w w' s off l H; [discriminate|].
  rewrite walk_S in H |- *.
  destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (wfirst_wlim md sel cur w w' s k c sk cur' E) as [E'|E']; rewrite E'; [|discriminate].
    destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    destruct (walk_m f md sel cur' w' (skipn (Z.to_nat k) s) (off + k)) as [l1 t1] eqn:E3.
    simpl. pose proof (IH cur' w w' _ _ _ E2) as IH'. rewrite E3 in IH'. exact IH'.
  - inversion H; subst; clear H. apply wfirst_end in E. subst s.
    unfold wfirst. pose proof (starting_len_pos (md_magicless md)).
    replace (Zlength (@nil Z) <? starting_len (md_magicless md)) with true by (symmetry; apply Z.ltb_lt; change (Zlength (@nil Z)) with 0; lia).
    discriminate.
Qed.

(* a dead stream (no claim, model without window limit) never ends a series under the window limit *)
Lemma dead_not_end3 : forall sm x s, dead sm x -> is_prefix x s ->
  snd (sm_series sm (sm_cur sm) (sm_wl sm) s) <> TEnd.
Proof.
  intros sm x s Hd Hp He. pose proof (proj1 Hd s Hp) as Hd'. clear Hd. rename Hd' into Hd.
  unfold sm_series, series_frames_m in *.
  destruct (walk_m (S (length s)) (sm_md sm) (sm_sel sm) (sm_cur sm) (sm_wl sm) s 0) as [l t] eqn:E.
  simpl in He. subst t.
  exact (walk_end_not_unk3 _ _ _ _ _ no_wlim _ _ _ E Hd).
Qed.

(* a block whose size exceeds bsm (which may be 0) fails *)
Lemma br_big0_3 : forall dw st hist s out bsm ws c, cblock_size s = Some c -> c > bsm -> 0 <= bsm ->
  block_res dw st hist s out bsm ws = None.
Proof.
  intros. destruct (Z_le_gt_dec c (Zlength s - 3)) as [Hin|Hout].
  - rewrite (br_eq _ _ _ _ _ _ _ c) by auto. unfold blk_body.
    destruct (cblock_types _ _ H) as [[Ty1 C1]|[Ty1 [Ty3 Co]]].
    { rewrite Ty1. cbn [Z.eqb Pos.eqb].
      replace (c >? bsm) with true by (symmetry; apply Zgtb_gt; lia). rewrite Bool.orb_true_r. auto. }
    destruct (bp_type (block_props_of s) =? 0).
    { replace (c >? bsm) with true by (symmetry; apply Zgtb_gt; lia). auto. }
    replace (bp_type (block_props_of s) =? 1) with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite dec_block_big; auto.
    unfold slice. rewrite Zlength_correct, length_firstn, length_skipn. rewrite Zlength_correct in Hin. lia.
  - unfold block_res. rewrite H. unfold ZSTD_blockHeaderSize.
    replace (c >? Zlength s - 3) with true by (symmetry; apply Zgtb_gt; lia). auto.
Qed.

(* F6: an empty last block ends the frame; after a content that differs from the declared content size, the
   frame fails whatever follows the block header *)
Lemma br_empty_last_fails3 : forall dw st hist u r out bsm ws h,
  Zlength u = 3 -> cblock_size u = Some 0 -> bp_last (block_props_of u) = 1 -> 0 <= bsm -> fcs_bad h out ->
  blk_fails h (block_res dw st hist (u ++ r) out bsm ws).
Proof.
  intros dw st hist u r out bsm ws h H3 Ec L Hb [B1 B2].
  rewrite (br_app_eq _ _ _ _ _ _ _ 0) by (auto; lia).
  rewrite (br_eq dw st hist u out bsm ws 0 Ec ltac:(lia)).
  replace (slice u 3 0) with (@nil Z) by reflexivity.
  unfold blk_body.
  destruct (cblock_types _ _ Ec) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [discriminate|].
  destruct (bp_type (block_props_of u) =? 0).
  - replace (0 >? bsm) with false by (symmetry; apply Zgtb_le; lia). rewrite app_nil_r.
    cbn [blk_fails]. left. rewrite L. split; [reflexivity |]. intros [F | F]; contradiction.
  - replace (bp_type (block_props_of u) =? 1) with false by (symmetry; apply Z.eqb_neq; auto).
    rewrite dec_block_nil. exact I.
Qed.

(* P_zunit_err when the effective Block_Maximum_Size is 0 (P_zunit_err assumes 0 < zp_bsm z): the unit
   can only be a block header or the checksum, and a failing one fails the frame *)
Lemma zunit_err0_3 : forall sm cd fb hdr z H u cap,
  bytes_ok fb -> zp_bsm z = 0 ->
  cur_rel (sm_md sm) (sm_sel sm) cd fb (FP_zstd hdr z) ->
  (match zp_ph z with
   | ZP_body bh => bp_type (block_props_of bh) = 0 \/ zp_got z = nil
   | _ => zp_got z = nil
   end) ->
  unit_ok (FP_zstd hdr z) (Zlength u) -> bytes_ok u ->
  cont_err (FP_zstd hdr z) H u cap ->
  fbad sm cd (fb ++ u).
Proof.
  intros sm cd fb hdr z H u cap Hbf Hbsm0 Hcr Hph Hun Hu Herr.
  unfold cur_rel in Hcr. destruct Hcr as [G [Hl [Ht [Hfd [Hd [Hbsm [Hign [outc [last [Hbp [Hfb Hp]]]]]]]]]]].
  unfold zp_hist in Hbp.
  subst fb. apply bytes_ok_app in Hbf. destruct Hbf as [Hbh Hbr].
  unfold unit_ok in Hun.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  - destruct Hp as [-> [Eo _]]. destruct Hun as [Eg H3]. unfold ZSTD_blockHeaderSize in H3. rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_err in Herr. rewrite Eph in Herr.
    rewrite Hbsm in Hbp.
    eapply (fbad_zstd3 sm cd hdr (zp_h z) (zp_dm z) G Hl Ht Hfd Hd Hbh (zp_bl z) (zp_ts z) outc u Hbp); [lia|].
    intro r. destruct (cblock_size u) as [c|] eqn:Ec.
    + cbv beta iota zeta in Herr. destruct Herr as [Hbig | (-> & L & Hbad)].
      * rewrite (br_big0_3 _ _ _ _ _ _ _ c); [exact I| | |].
        -- rewrite cblock_size_app, Ec by lia. auto.
        -- lia.
        -- lia.
      * rewrite Eo in Hbad. apply br_empty_last_fails3; auto; lia.
    + rewrite cblock_none_res; [exact I|]. rewrite cblock_size_app, Ec by lia. auto.
  - destruct Hp as [_ [_ [c [_ [Hc _]]]]]. lia.
  - destruct Hp as [-> [Eo [Hf [Hc1 _]]]]. destruct Hun as [Eg H4].
    rewrite Eg, app_nil_r, <- app_assoc.
    unfold cont_err in Herr. rewrite Eph, Eo in Herr. destruct Herr as [Hig Hx].
    rewrite Hbsm in Hbp.
    eapply (fbad_zstd3_last sm cd hdr (zp_h z) (zp_dm z) G Hl Ht Hfd Hd Hbh (zp_bl z) (zp_ts z) outc u Hbp).
    intros r c k.
    unfold df_fin. cbv zeta.
    destruct (andb (negb (fh_contentSize (zp_h z) =? ZSTD_CONTENTSIZE_UNKNOWN)) (negb (Zlength outc =? fh_contentSize (zp_h z))));
      [discriminate|]. rewrite Hc1. cbn [Z.eqb].
    pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg (zp_bl z)).
    rewrite !Zlength_app.
    replace (Zlength hdr + (Zlength (zp_bl z) + (Zlength u + Zlength r)) - fh_headerSize (zp_h z) - Zlength (zp_bl z) <? 4)
      with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite app_assoc. replace (fh_headerSize (zp_h z) + Zlength (zp_bl z)) with (Zlength (hdr ++ zp_bl z) + 0)
      by (rewrite Zlength_app; lia).
    rewrite le_field_app_r by lia. rewrite le_field_app by lia.
    rewrite <- Hign, Hig. cbn [negb andb].
    replace (le_field u 0 4 =? xxh64 outc 0 mod 2 ^ 32) with false by (symmetry; apply Z.eqb_neq; auto).
    discriminate.
  - contradiction.
Qed.
