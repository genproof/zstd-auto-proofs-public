(* FS3 streaming: the content claim of ZSTD_decompressStream's epilogue (plain Coq).  The proof is
   pro2/Q3Content.v (content_ok_of_m_rel_cd ported to the strict stream model), copied with its helper
   files (epi/content/EC3*.v, from pro2/Q3*.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.dec.v3.FS.stream.S3ModelDefs.
Require Import Zstd.proof.model.StreamModel Zstd.proof.dec.v3.FS.stream.epi.content.EC3Base Zstd.proof.dec.v3.FS.stream.epi.content.EC3Frame Zstd.proof.dec.v3.FS.stream.epi.content.EC3FrameM Zstd.proof.dec.v3.FS.stream.epi.content.EC3Walk.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pc_pre_nil : forall c, is_prefix [] c.
Proof. intros. reflexivity. Qed.

Lemma pc_pre_trans : forall a b c, is_prefix a b -> is_prefix b c -> is_prefix a c.
Proof.
intros a b c H1 H2. apply is_prefix_ex in H1. apply is_prefix_ex in H2.
destruct H1 as [r1 ->]. destruct H2 as [r2 ->]. rewrite <- app_assoc. apply is_prefix_app.
Qed.

Lemma pc_pre_app2 : forall a b c, is_prefix b c -> is_prefix (a ++ b) (a ++ c).
Proof.
intros a b c H. apply is_prefix_ex in H. destruct H as [r ->]. rewrite app_assoc. apply is_prefix_app.
Qed.

Lemma pc_flat_map_fshift : forall d l, flat_map fr_content (map (fshift d) l) = flat_map fr_content l.
Proof. intros d l. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pc_df_fin_nodet : forall md h s r, df_fin md h s r <> FDetHdr.
Proof.
intros md h s r. unfold df_fin. destruct r as [[o k]|]; [|discriminate].
repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma pc_df_fin_ok : forall md h s r c k, df_fin md h s r = FOk c k -> exists k', r = Some (c, k').
Proof.
intros md h s r c k H. unfold df_fin in H. destruct r as [[o k1]|]; [|discriminate].
repeat match type of H with context [if ?b then _ else _] => destruct b end; try discriminate;
inversion H; subst; eauto.
Qed.

(* a Zstandard frame cut before its first block header ends *)
Lemma pc_dfm_short : forall md dm w s h, get_frame_header_m (md_magicless md) s = FH_ok h ->
  fh_frameType h = 0 -> Zlength s < fh_headerSize h + 3 -> decode_frame_m md dm w s = FUnk.
Proof.
intros md dm w s h G Ht Hs.
destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|(_ & _ & Hm & Hhs & _)]; [congruence|].
unfold decode_frame_m. destruct (md_magicless md) eqn:Hmg; cbn [fpos fsh] in *; cbv zeta.
- destruct (Zlength s <? _); [reflexivity|]. cbn [negb andb]. change (4 - 4) with 0.
  replace (Zlength s <? fhd_header_size (byte_at s 0) - 4 + ZSTD_blockHeaderSize) with true
    by (symmetry; apply Z.ltb_lt; unfold ZSTD_blockHeaderSize; lia). reflexivity.
- destruct (Zlength s <? _); [reflexivity|]. rewrite (Hm eq_refl), Z.eqb_refl. cbn [negb andb].
  change (4 - 0) with 4.
  replace (Zlength s <? fhd_header_size (byte_at s 4) - 0 + ZSTD_blockHeaderSize) with true
    by (symmetry; apply Z.ltb_lt; unfold ZSTD_blockHeaderSize; lia). reflexivity.
Qed.

(* a raw block whose body starts with got: its content starts with got *)
Lemma pc_db_raw_prefix : forall dw f ts hist bh got rest outc bsm ws c k cc,
  Zlength bh = 3 -> cblock_size bh = Some cc -> bp_type (block_props_of bh) = 0 -> Zlength got < cc ->
  dbs dw f ts hist (bh ++ got ++ rest) outc bsm ws = Some (c, k) ->
  is_prefix (outc ++ got) c.
Proof.
intros dw f ts hist bh got rest outc bsm ws c k cc H3 Hc Ht Hg H.
destruct f as [|f]; [destruct dw; discriminate|].
rewrite db_S_eq in H.
unfold block_res in H. rewrite cblock_size_app, Hc in H by lia.
destruct (cc >? Zlength (bh ++ got ++ rest) - ZSTD_blockHeaderSize) eqn:E1; [discriminate|].
cbv zeta in H. rewrite block_props_app, Ht in H by lia. simpl in H.
destruct (cc >? bsm); [discriminate|].
assert (Hb: slice (bh ++ got ++ rest) ZSTD_blockHeaderSize cc = got ++ firstn (Z.to_nat cc - length got) rest).
{ unfold ZSTD_blockHeaderSize, slice. rewrite skipn_app.
  replace (Z.to_nat 3) with (length bh) by (rewrite Zlength_correct in H3; lia).
  rewrite skipn_all, Nat.sub_diag, app_nil_l. simpl skipn. rewrite firstn_app.
  rewrite firstn_all2 by (rewrite Zlength_correct in Hg; lia). reflexivity. }
rewrite Hb in H.
match type of H with context [if ?b then _ else _] => destruct b end.
- inversion H; subst. rewrite app_assoc. apply is_prefix_app.
- unfold oshift in H.
  destruct (dbs dw f _ _ _ _ _ _) as [[o2 k2]|] eqn:E2; [|discriminate]. inversion H; subst.
  destruct (db_out _ _ _ _ _ _ _ _ _ _ E2) as [d ->].
  rewrite <- !app_assoc, (app_assoc outc got). apply is_prefix_app.
Qed.

(* the frame being decoded (cur_rel FP_zstd): every extension decodes to content that starts with the
   content decoded so far, and is not rejected at its header *)
Lemma pc_cur_zstd_frame : forall md sel cd fb hdr z rest, bytes_ok fb -> cur_rel md sel cd fb (FP_zstd hdr z) ->
  decode_frame_m md (zp_dm z) no_wlim (fb ++ rest) <> FDetHdr /\
  (forall c k, decode_frame_m md (zp_dm z) no_wlim (fb ++ rest) = FOk c k -> is_prefix (zp_out z) c).
Proof.
intros md sel cd fb hdr z rest Hb Hc. unfold cur_rel in Hc.
destruct Hc as (G & Hl & Ht & Hd & Hid & Hbsm & _ & outc & last & Hbp & Hfb & Hph).
unfold zp_hist in Hbp. rewrite Hbsm in Hbp.
set (X := match zp_ph z with ZP_body bh => bh ++ zp_got z | _ => zp_got z end) in *.
set (r := zp_bl z ++ X ++ rest).
assert (Er: fb ++ rest = hdr ++ r) by (subst fb r; rewrite <- !app_assoc; reflexivity).
rewrite Er.
assert (Bh: bytes_ok hdr) by (subst fb; apply bytes_ok_app in Hb; tauto).
destruct (Z_lt_dec (Zlength r) 3) as [Hs|Hs].
{ rewrite (pc_dfm_short md (zp_dm z) no_wlim (hdr ++ r) (zp_h z)).
  - split; [discriminate | intros c k E; discriminate].
  - apply gfhm_ext; auto. apply bytes_ok_byte_at; auto.
  - auto.
  - rewrite Zlength_app. lia. }
rewrite (dfm_cur_pre md (zp_dm z) no_wlim hdr (zp_h z) r G Hl Ht Hid Bh) by lia.
replace (fh_windowSize (zp_h z) >? no_wlim) with false
  by (symmetry; apply Zgtb_le; eapply gfhm_ws; eauto).
split; [apply pc_df_fin_nodet|].
intros c k E. apply pc_df_fin_ok in E. destruct E as [k' Edb].
destruct last.
- assert (Ho: zp_out z = outc).
  { destruct (zp_ph z); try tauto; destruct Hph as [Hx _]; try discriminate; tauto. }
  unfold r in Edb. rewrite (bp_db_last _ _ _ _ _ _ _ _ Hbp) in Edb by (rewrite length_app; lia).
  inversion Edb; subst c. rewrite Ho. unfold is_prefix. apply firstn_all.
- destruct (bp_db _ _ _ _ _ _ _ _ _ Hbp eq_refl) as [n [Hn Hdb]].
  subst r. replace (length (zp_bl z ++ X ++ rest)) with (n + (length (zp_bl z ++ X ++ rest) - n))%nat in Edb
    by (rewrite length_app; lia).
  rewrite Hdb in Edb. unfold oshift in Edb.
  destruct (dbs _ _ (zp_ts z) _ (X ++ rest) outc _ _) as [[o2 k2]|] eqn:E2; [|discriminate].
  inversion Edb; subst o2.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  + destruct Hph as (_ & -> & _). destruct (db_out _ _ _ _ _ _ _ _ _ _ E2) as [d ->]. apply is_prefix_app.
  + destruct Hph as (_ & H3 & cc & Hcc & Hcb & Hg & Ho). subst X.
    destruct (bp_type (block_props_of bh) =? 0) eqn:Eb.
    * rewrite Ho. apply Z.eqb_eq in Eb. rewrite <- app_assoc in E2.
      eapply pc_db_raw_prefix; eauto.
    * rewrite Ho. destruct (db_out _ _ _ _ _ _ _ _ _ _ E2) as [d ->]. apply is_prefix_app.
  + destruct Hph as [Hx _]; discriminate.
  + destruct Hph as [Hx _]; discriminate.
Qed.

Lemma pc_cur_prefix : forall md sel cd fb fp rest l t, bytes_ok fb -> cur_rel md sel cd fb fp ->
  series_frames_m md sel cd no_wlim (fb ++ rest) = (l, t) -> t = TEnd \/ t = TDetHdr ->
  is_prefix (fp_content fp) (flat_map fr_content l).
Proof.
intros md sel cd fb fp rest l t Hb Hc Hs Ht.
destruct fp as [|hb|hdr got|hdr z]; try apply pc_pre_nil. cbn [fp_content].
destruct (pc_cur_zstd_frame md sel cd fb hdr z rest Hb Hc) as [Hnd Hok].
pose proof Hc as Hc'. unfold cur_rel in Hc'.
destruct Hc' as (G & Hl & Ht0 & Hd & _ & _ & _ & outc & last & _ & Hfb & _).
set (X := match zp_ph z with ZP_body bh => bh ++ zp_got z | _ => zp_got z end) in *.
assert (Er: fb ++ rest = hdr ++ (zp_bl z ++ X ++ rest)) by (subst fb; rewrite <- !app_assoc; reflexivity).
assert (Bh: bytes_ok hdr) by (subst fb; apply bytes_ok_app in Hb; tauto).
pose proof (gfhm_len _ _ _ G) as H5.
destruct (gfhm_info _ _ _ G) as [(_ & Ht' & _)|(_ & _ & Hm & _)]; [congruence|].
assert (Hfl: Zlength hdr <= Zlength (fb ++ rest)) by (rewrite Er, Zlength_app; pose proof (Zlength_nonneg (zp_bl z ++ X ++ rest)); lia).
unfold series_frames_m in Hs. rewrite walk_S in Hs. unfold wfirst in Hs.
replace (Zlength (fb ++ rest) <? starting_len (md_magicless md)) with false in Hs by (symmetry; apply Z.ltb_ge; lia).
replace (andb (negb (md_magicless md)) (is_skippable_magic (le_field (fb ++ rest) 0 4))) with false in Hs.
2:{ destruct (md_magicless md) eqn:Hmg; [reflexivity|]. cbn [negb andb]. unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in H5.
    rewrite Er, le_field_app by lia. rewrite (Hm eq_refl). symmetry. apply skip_magic_false. }
rewrite Er, (frame_dict_ext _ _ _ _ _ _ G (bytes_ok_byte_at _ _ Bh)), Hd, <- Er in Hs.
destruct (decode_frame_m md (zp_dm z) no_wlim (fb ++ rest)) as [c k| | |] eqn:E.
- destruct (walk_m _ _ _ _ _ _ _) as [l0 t0]. inversion Hs; subst. cbn [flat_map mkrec fr_content].
  eapply pc_pre_trans; [apply (Hok c k eq_refl) | apply is_prefix_app].
- congruence.
- inversion Hs; subst. destruct Ht; discriminate.
- inversion Hs; subst. destruct Ht; discriminate.
Qed.

Lemma epi3_content : forall sm sin sout fp pend cd,
  bytes_ok sin -> m_rel_cd sm sin sout fp pend cd -> content_ok sm sin sout.
Proof.
intros sm sin sout fp pend cd Hb (dsin & fb & recs & -> & Hs & Hcd & Hc & Ho) s Hp. cbv zeta. intros Ht.
apply bytes_ok_app in Hb. destruct Hb as [Hb1 Hb2].
destruct (is_prefix_ex _ _ Hp) as [rest ->]. rewrite <- app_assoc in *.
destruct (series_frames_m (sm_md sm) (sm_sel sm) cd no_wlim (fb ++ rest)) as [l t] eqn:Ey.
assert (Ht': t = TEnd \/ t = TDetHdr).
{ rewrite (proj1 (series_app _ _ no_wlim _ dsin recs (fb ++ rest) Hs Hb1)), Hcd, Ey in Ht. exact Ht. }
rewrite <- Hcd in Ey.
rewrite (series_app_full _ _ no_wlim _ dsin recs (fb ++ rest) l t Hs Hb1 Ey) by (destruct Ht'; subst; discriminate).
cbn [fst]. rewrite flat_map_app, pc_flat_map_fshift.
eapply pc_pre_trans; [apply is_prefix_app with (r := pend)|]. rewrite Ho.
apply pc_pre_app2. rewrite Hcd in Ey. eapply pc_cur_prefix; eauto.
Qed.
