(* FS3 streaming model facts: zunit_step phase by phase (ported from v2
   src/proof/dec/FS/StreamModelFacts.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Xxh64 Zstd.proof.model.Info Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.ParamsH Zstd.proof.model.Huffman.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Refuse Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM Zstd.proof.dec.v3.FS.stream.modelw.MW3Walk Zstd.proof.dec.v3.FS.stream.modelw.MW3Unit1.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma next_phase_eq : forall h bh, next_phase h bh =
  if (bp_last (block_props_of bh) =? 1) then (if fh_checksumFlag h =? 1 then ZP_ck else ZP_end) else ZP_bhdr.
Proof. reflexivity. Qed.

Lemma next_phase_not_body : forall h bh bh', next_phase h bh <> ZP_body bh'.
Proof. intros. unfold next_phase. destruct (_ =? 1); [destruct (_ =? 1)|]; discriminate. Qed.

Lemma cms_lift : forall A B C : Prop, B -> A \/ C -> (A /\ B) \/ C.
Proof. tauto. Qed.

(* cnt_ok / cont_err with the stream's own block decoder (dec_block dw) behind the frame's dictionary *)
Definition cnt_okw (dw: bool) (z: zprog) (u cnt: list Z) (ts': dstate) : Prop :=
  let h := zp_h z in
  match zp_ph z with
  | ZP_body bh =>
      let bp := block_props_of bh in
      if bp_type bp =? 0 then cnt = u /\ ts' = zp_ts z
      else if bp_type bp =? 1 then cnt = repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)) /\ ts' = zp_ts z
      else bytes_ok cnt /\ Zlength cnt <= zp_bsm z /\
           match dec_block dw (zp_ts z) (zp_hist z) (zp_out z) u (zp_bsm z) (fh_windowSize h) with
           | Some (ts2, c2) => map (fun b => b mod 2 ^ 32) cnt = map (fun b => b mod 2 ^ 32) c2 /\ ts' = ts2
           | None => True
           end
  | _ => cnt = nil /\ ts' = zp_ts z
  end.

Definition cont_errw (dw: bool) (fp: fprog) (u: list Z) (cap: Z) : Prop :=
  match fp with
  | FP_zstd _ z =>
      let h := zp_h z in
      let bsm := zp_bsm z in
      let out := zp_out z in
      match zp_ph z with
      | ZP_bhdr =>
          (* F6: an empty last block ends the frame, with the content size check of a non-empty one *)
          match cblock_size u with
          | None => True
          | Some c => c > bsm \/ (c = 0 /\ bp_last (block_props_of u) = 1 /\ fcs_bad h out)
          end
      | ZP_body bh =>
          let bp := block_props_of bh in
          let lastc o := bp_last bp = 1 /\ fcs_bad h o in
          if bp_type bp =? 0 then
            Zlength u > cap \/ (Some (Zlength (zp_got z ++ u)) = cblock_size bh /\ lastc (out ++ u))
          else if bp_type bp =? 1 then
            bp_origSize bp > cap \/ bp_origSize bp > bsm \/
            lastc (out ++ repeat (byte_at u 0) (Z.to_nat (bp_origSize bp)))
          else
            match dec_block dw (zp_ts z) (zp_hist z) out u bsm (fh_windowSize h) with
            | None => True
            | Some (_, c2) => cap < Zlength c2 \/ lastc (out ++ c2)
            end
      | ZP_ck => zp_ign z = false /\ le_field u 0 4 <> xxh64 out 0 mod 2 ^ 32
      | ZP_end => False
      end
  | _ => False
  end.

Lemma br_big : forall dw st hist s out bsm ws c, cblock_size s = Some c -> c > bsm -> 0 < bsm ->
  block_res dw st hist s out bsm ws = None.
Proof.
  intros. destruct (Z_le_gt_dec c (Zlength s - 3)) as [Hin|Hout].
  - rewrite (br_eq _ _ _ _ _ _ _ c) by auto. unfold blk_body.
    destruct (cblock_types _ _ H) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [lia|].
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
Lemma br_empty_last_fails : forall dw st hist u r out bsm ws h,
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

Lemma origSize_nonneg : forall s, bytes_ok s -> 0 <= bp_origSize (block_props_of s).
Proof.
  intros. unfold block_props_of. cbn [bp_origSize]. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (le_field_bound s 0 3 H ltac:(lia)). apply Z.div_pos; lia.
Qed.

Lemma Zlength_repeat : forall (x: Z) n, Zlength (repeat x n) = Z.of_nat n.
Proof. intros. rewrite Zlength_correct, repeat_length. auto. Qed.

Section Step.
Variable sm : smode.
Variable cd : option dict_model.
Variable hdr : list Z.
Variable z : zprog.
Hypothesis G : get_frame_header_m (md_magicless (sm_md sm)) hdr = FH_ok (zp_h z).
Hypothesis Hl : Zlength hdr = fh_headerSize (zp_h z).
Hypothesis Ht : fh_frameType (zp_h z) = 0.
Hypothesis Hfd : frame_dict (md_magicless (sm_md sm)) (sm_sel sm) cd hdr = Some (zp_dm z).
Hypothesis Hd : fh_dictID (zp_h z) = 0 \/ fh_dictID (zp_h z) = dm_id (zp_dm z).
Hypothesis Hbsm : zp_bsm z = Z.min (fh_blockSizeMax (zp_h z)) (md_bmax (sm_md sm)).
Hypothesis Hign : zp_ign z = md_ignore (sm_md sm).
Hypothesis Hb : bytes_ok hdr.

Local Notation DW := (md_dwin (sm_md sm)).
Local Notation BP := (blocks_pre DW (dm_content (zp_dm z)) (zp_bsm z) (fh_windowSize (zp_h z)) (dm_state (zp_dm z))).
Local Notation CR := (cur_rel (sm_md sm) (sm_sel sm) cd).
Local Notation BR st s out := (block_res DW st (dm_content (zp_dm z)) s out (zp_bsm z) (fh_windowSize (zp_h z))).

Lemma fdz : forall bl ts outc rest, BP bl ts outc false -> 3 <= Zlength rest ->
  (forall r, blk_fails (zp_h z) (BR ts (rest ++ r) outc)) ->
  (forall r, rblk_stop DW (zp_h z) ts (dm_content (zp_dm z)) (rest ++ r) outc (zp_bsm z)) ->
  fdead sm cd (hdr ++ bl ++ rest).
Proof. rewrite Hbsm. intros. eapply fdead_zstd3; eauto. Qed.

Lemma fbz : forall bl ts outc rest, BP bl ts outc false -> 3 <= Zlength rest ->
  (forall r, blk_fails (zp_h z) (BR ts (rest ++ r) outc)) -> fbad sm cd (hdr ++ bl ++ rest).
Proof. rewrite Hbsm. intros. eapply fbad_zstd3; eauto. Qed.

(* the frame after complete blocks: at the next block header, or after the last block in the checksum phase (the
   content size matching Frame_Content_Size modulo 2^64, as zstd checks it) or at the frame's end (exactly) *)
Lemma cur_after_block : forall bl ts out last, BP bl ts out last ->
  (last = true -> if fh_checksumFlag (zp_h z) =? 1 then fcs_okm (zp_h z) out else fcs_ok (zp_h z) out) ->
  CR (hdr ++ bl)
    (FP_zstd hdr (zp_with z bl ts out
       (if last then (if fh_checksumFlag (zp_h z) =? 1 then ZP_ck else ZP_end) else ZP_bhdr) nil)).
Proof.
  intros bl ts out last Hbp Hf.
  unfold cur_rel, zp_with, zp_hist. cbn [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got].
  repeat split; auto. exists out, last. split; auto.
  destruct last; [specialize (Hf eq_refl); destruct (fh_checksumFlag (zp_h z) =? 1) eqn:Ck|];
    rewrite app_nil_r; repeat split; auto.
  all: try (change (Zlength (@nil Z)) with 0; unfold ZSTD_blockHeaderSize; lia).
  all: try (apply Z.eqb_eq; auto; fail).
  all: left; split; auto; destruct (gfhm_ck _ _ _ G) as [E|E]; auto; rewrite E in Ck; discriminate.
Qed.

(* a block accepted by the stream's model after the complete blocks bl: the frame goes on, or (a last block whose
   content size matches Frame_Content_Size only modulo 2^64, without a checksum) the model gives up while the
   frame is complete and not refused *)
Lemma after_block : forall bl ts outc b ts' out' lst,
  BP bl ts outc false -> BR ts b outc = Some (ts', out', Zlength b, lst) ->
  (lst = true -> fcs_okm (zp_h z) out') ->
  CR (hdr ++ bl ++ b) (FP_zstd hdr (zp_with z (bl ++ b) ts' out'
       (if lst then (if fh_checksumFlag (zp_h z) =? 1 then ZP_ck else ZP_end) else ZP_bhdr) nil)) \/
  fdead sm cd (hdr ++ bl ++ b).
Proof.
  intros bl ts outc b ts' out' lst Hbp Hbr Hm.
  pose proof (BPre_snoc _ _ _ _ _ _ _ _ _ _ _ _ Hbp Hbr) as Hbp'.
  destruct lst; [|left; apply (cur_after_block (bl ++ b) ts' out' false); auto; intros E; discriminate].
  specialize (Hm eq_refl).
  destruct (fh_checksumFlag (zp_h z) =? 1) eqn:Ck.
  - left. pose proof (cur_after_block (bl ++ b) ts' out' true Hbp') as X. rewrite Ck in X. apply X. auto.
  - destruct (fcs_ok_dec (zp_h z) out') as [Hf|Hf].
    + left. pose proof (cur_after_block (bl ++ b) ts' out' true Hbp') as X. rewrite Ck in X. apply X. auto.
    + right. destruct (block_res_rblock _ _ _ _ _ _ _ _ _ _ _ Hbr) as [c [Ec [Hc _]]].
      pose proof (cblock_size_len _ _ Ec). eapply fdz; [exact Hbp|lia| |].
      * intro r. rewrite (br_app_eq _ _ _ _ _ _ _ c) by auto. rewrite Hbr. left. auto.
      * intro r. apply rblk_stop_app. eapply rblk_stop_res; [exact Hbr|]. apply fer_no; auto. left.
        destruct (gfhm_ck _ _ _ G) as [E|E]; auto. rewrite E in Ck. discriminate.
Qed.

Lemma step_bhdr : forall u cnt ts' outc,
  (exists c, cblock_size u = Some c /\ c <= zp_bsm z /\
     (c = 0 -> bp_last (block_props_of u) = 1 -> fcs_okm (zp_h z) outc)) ->
  BP (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_bhdr -> zp_got z = nil -> zp_out z = outc -> Zlength u = 3 -> bytes_ok u ->
  CR (hdr ++ zp_bl z ++ u) (FP_zstd hdr (zstep z u cnt ts')) \/ fdead sm cd (hdr ++ zp_bl z ++ u).
Proof.
  intros u cnt ts' outc [c [Ec [Hcb Hm]]] Hbp Eph Eg Eo H3 Hu.
  unfold zstep. rewrite Eph, Ec.
  pose proof (cblock_nonneg _ _ Hu Ec) as Hc0.
  destruct (c =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst c.
    pose proof (br_eq DW (zp_ts z) (dm_content (zp_dm z)) u outc (zp_bsm z) (fh_windowSize (zp_h z)) 0 Ec ltac:(lia)) as Bu.
    replace (slice u 3 0) with (@nil Z) in Bu by reflexivity.
    unfold blk_body in Bu.
    destruct (cblock_types _ _ Ec) as [[Ty1 C1]|[Ty1 [Ty3 Co]]]; [discriminate|].
    destruct (bp_type (block_props_of u) =? 0) eqn:T0.
    + replace (0 >? zp_bsm z) with false in Bu by (symmetry; apply Zgtb_le; lia).
      rewrite app_nil_r in Bu. replace (3 + 0) with (Zlength u) in Bu by lia.
      rewrite Eo, next_phase_eq. apply (after_block (zp_bl z) (zp_ts z) outc u (zp_ts z) outc _ Hbp Bu).
      intros L. apply Z.eqb_eq in L. auto.
    + replace (bp_type (block_props_of u) =? 1) with false in Bu by (symmetry; apply Z.eqb_neq; auto).
      rewrite dec_block_nil in Bu.
      right. eapply fdz; [exact Hbp|lia| |].
      * intro r. rewrite (br_app_eq _ _ _ _ _ _ _ 0) by (auto; lia). rewrite Bu. exact I.
      * intro r. apply rblk_stop_app. apply (rblk_stop_cmp _ _ _ _ _ _ _ 0); auto; [lia| |].
        -- apply Z.eqb_neq; auto.
        -- apply dec_block_nil.
  - apply Z.eqb_neq in E0.
    left. unfold cur_rel, zp_with, zp_hist. cbn [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got].
    repeat split; auto. exists outc, false. split; auto. rewrite !app_nil_r. repeat split; auto.
    exists c. repeat split; auto; try lia.
    all: try (change (Zlength (@nil Z)) with 0; lia).
    all: destruct (bp_type (block_props_of u) =? 0); auto.
Qed.

Lemma step_body_raw : forall u cnt ts' outc bh c,
  BP (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_body bh -> Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= zp_bsm z ->
  Zlength (zp_got z) < c -> bp_type (block_props_of bh) = 0 -> zp_out z = outc ++ zp_got z ->
  1 <= Zlength u <= c - Zlength (zp_got z) -> cnt = u -> ts' = zp_ts z ->
  (Zlength (zp_got z) + Zlength u = c -> bp_last (block_props_of bh) = 1 ->
     fcs_okm (zp_h z) (outc ++ zp_got z ++ u)) ->
  CR (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u) (FP_zstd hdr (zstep z u cnt ts')) \/
  fdead sm cd (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u).
Proof.
  intros u cnt ts' outc bh c Hbp Eph H3 Ec Hc Hg Ty Eo Hu -> -> Hm.
  unfold zstep in *. rewrite Eph in *. rewrite Ty in *. cbn [Z.eqb] in *. rewrite Ec in *.
  rewrite Zlength_app in *.
  destruct (Zlength (zp_got z) + Zlength u =? c) eqn:Ecmp.
  - apply Z.eqb_eq in Ecmp.
    assert (Hbr: BR (zp_ts z) (bh ++ zp_got z ++ u) outc =
                Some (zp_ts z, outc ++ zp_got z ++ u, Zlength (bh ++ zp_got z ++ u), bp_last (block_props_of bh) =? 1)).
    { rewrite (br_eq _ _ _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite !Zlength_app; lia].
      unfold blk_body. rewrite block_props_app by lia. rewrite Ty. cbn [Z.eqb].
      replace (c >? zp_bsm z) with false by (symmetry; apply Zgtb_le; lia).
      rewrite slice_hdr by auto. rewrite firstn_all2 by (rewrite length_app; rewrite !Zlength_correct in Ecmp; lia).
      replace (Zlength (bh ++ zp_got z ++ u)) with (3 + c) by (rewrite !Zlength_app; lia). reflexivity. }
    rewrite <- (app_assoc bh), Eo, <- (app_assoc outc), next_phase_eq.
    apply (after_block (zp_bl z) (zp_ts z) outc _ (zp_ts z) _ _ Hbp Hbr).
    intros L. apply Z.eqb_eq in L. auto.
  - apply Z.eqb_neq in Ecmp. left.
    unfold cur_rel, zp_with, zp_hist. cbn [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got].
    repeat split; auto. exists outc, false. split; auto. split; [rewrite !app_assoc; auto|].
    repeat split; auto. exists c. rewrite Ty. cbn [Z.eqb]. rewrite Zlength_app. repeat split; auto; try lia.
    rewrite Eo, app_assoc. auto.
Qed.

Lemma step_body_nraw : forall u cnt ts' outc bh c,
  BP (zp_bl z) (zp_ts z) outc false ->
  zp_ph z = ZP_body bh -> Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= zp_bsm z ->
  (bp_type (block_props_of bh) =? 0) = false -> zp_got z = nil -> zp_out z = outc ->
  Zlength u = c -> cnt_okw DW z u cnt ts' -> cont_checks z u cnt ->
  (bp_type (block_props_of bh) = 1 -> bp_origSize (block_props_of bh) <= zp_bsm z) ->
  bytes_ok (dm_content (zp_dm z)) -> bytes_ok outc -> st_ok (zp_ts z) -> bytes_ok u ->
  (CR (hdr ++ zp_bl z ++ bh ++ u) (FP_zstd hdr (zstep z u cnt ts')) /\ cnt_model_some DW z u) \/
  fdead sm cd (hdr ++ zp_bl z ++ bh ++ u).
Proof.
  intros u cnt ts' outc bh c Hbp Eph H3 Ec Hc Ty Eg Eo Hu Hcnt Hck Hrle Hhb Hbo Hst Hbu.
  assert (Hm: bp_last (block_props_of bh) = 1 -> fcs_okm (zp_h z) (outc ++ cnt)).
  { intros L. unfold cont_checks in Hck. rewrite Eph in Hck. rewrite <- Eo. apply Hck; auto.
    unfold zstep. rewrite Eph, Ty. unfold zp_with. cbn [zp_ph]. apply next_phase_not_body. }
  unfold cnt_okw, zp_hist in *. rewrite Eph in *. rewrite Ty in Hcnt.
  unfold zstep. rewrite Eph, Ty.
  assert (Hbr: BR (zp_ts z) (bh ++ u) outc =
     match blk_body DW (zp_ts z) (dm_content (zp_dm z)) (block_props_of bh) u outc c (zp_bsm z) (fh_windowSize (zp_h z)) with
     | None => None
     | Some (st', out') => Some (st', out', Zlength (bh ++ u), bp_last (block_props_of bh) =? 1)
     end).
  { rewrite (br_eq _ _ _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
    rewrite block_props_app by lia. rewrite slice_hdr by auto.
    rewrite firstn_all2 by (rewrite Zlength_correct in Hu; lia).
    replace (Zlength (bh ++ u)) with (3 + c) by (rewrite Zlength_app; lia). auto. }
  assert (Hblk: blk_body DW (zp_ts z) (dm_content (zp_dm z)) (block_props_of bh) u outc c (zp_bsm z) (fh_windowSize (zp_h z))
                = Some (ts', outc ++ cnt) \/
                ((bp_type (block_props_of bh) =? 1) = false /\
                 dec_block DW (zp_ts z) (dm_content (zp_dm z)) outc u (zp_bsm z) (fh_windowSize (zp_h z)) = None /\
                 blk_body DW (zp_ts z) (dm_content (zp_dm z)) (block_props_of bh) u outc c (zp_bsm z) (fh_windowSize (zp_h z))
                 = None)).
  { unfold blk_body. rewrite Ty.
    destruct (bp_type (block_props_of bh) =? 1) eqn:T1.
    - destruct Hcnt as [-> ->]. left. apply Z.eqb_eq in T1.
      replace ((bp_origSize (block_props_of bh) >? zp_bsm z) || (c >? zp_bsm z)) with false; auto.
      symmetry. apply Bool.orb_false_iff. split; apply Zgtb_le; [apply Hrle; auto|lia].
    - destruct Hcnt as [Hbc [_ Hdb]]. rewrite Eo in Hdb.
      destruct (dec_block _ _ _ _ _ _ _) as [[ts2 c2]|] eqn:D; [|right; auto]. destruct Hdb as [Hmd ->].
      destruct (dec_block_bytes _ _ _ _ _ _ _ _ _ Hhb Hbo Hbu Hst D) as [Hc2 _].
      rewrite !map_mod_bytes in Hmd by auto. subst. auto. }
  destruct Hblk as [Hblk|[T1 [D Hblk]]]; rewrite Hblk in Hbr.
  - apply cms_lift.
    { unfold cnt_model_some, zp_hist. rewrite Eph, Eo. intros T2 E. unfold blk_body in Hblk. rewrite T2 in Hblk.
      cbn [Z.eqb] in Hblk. rewrite E in Hblk. discriminate. }
    rewrite next_phase_eq, Eo.
    apply (after_block (zp_bl z) (zp_ts z) outc _ ts' _ _ Hbp Hbr).
    intros L. apply Z.eqb_eq in L. auto.
  - right. eapply fdz; [exact Hbp|rewrite Zlength_app; lia| |].
    + intro r. rewrite (br_app_eq _ _ _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
      rewrite Hbr. exact I.
    + intro r. apply rblk_stop_app. apply (rblk_stop_cmp _ _ _ _ _ _ _ c).
      * rewrite cblock_size_app; auto; lia.
      * rewrite Zlength_app. lia.
      * rewrite block_props_app by lia. auto.
      * rewrite block_props_app by lia. auto.
      * rewrite slice_hdr by auto. rewrite firstn_all2 by (rewrite Zlength_correct in Hu; lia). auto.
Qed.

Lemma step_ck : forall u cnt ts' outc,
  BP (zp_bl z) (zp_ts z) outc true ->
  zp_ph z = ZP_ck -> zp_out z = outc -> fcs_okm (zp_h z) outc -> fh_checksumFlag (zp_h z) = 1 ->
  Zlength u = 4 -> cont_checks z u cnt ->
  CR (hdr ++ zp_bl z ++ u) (FP_zstd hdr (zstep z u cnt ts')) \/ fdead sm cd (hdr ++ zp_bl z ++ u).
Proof.
  intros u cnt ts' outc Hbp Eph Eo Hm Hc1 Hu Hck.
  destruct (fcs_ok_dec (zp_h z) outc) as [Hf|Hf].
  - left. unfold cont_checks in Hck. rewrite Eph in Hck.
    unfold zstep. rewrite Eph. unfold cur_rel, zp_with, zp_hist.
    cbn [zp_h zp_dm zp_bsm zp_ign zp_bl zp_ts zp_out zp_ph zp_got].
    repeat split; auto. exists outc, true. split; auto. repeat split; auto.
    right. rewrite <- Eo. repeat split; auto.
  - right. rewrite Hbsm in Hbp.
    apply (fdead_zstd3_last sm cd hdr (zp_h z) (zp_dm z) G Hl Ht Hfd Hd Hb (zp_bl z) (zp_ts z) outc u Hbp).
    + intros r. unfold df_fin. cbv zeta. rewrite fcs_bad_cond by auto. reflexivity.
    + intros r. apply fer_no; auto. right. rewrite Zlength_app. pose proof (Zlength_nonneg r). lia.
Qed.

(* ---------- zunit_err, phase by phase ---------- *)

Lemma err_body_raw : forall u outc bh c cap,
  BP (zp_bl z) (zp_ts z) outc false ->
  Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= zp_bsm z ->
  Zlength (zp_got z) < c -> bp_type (block_props_of bh) = 0 -> zp_out z = outc ++ zp_got z ->
  1 <= Zlength u <= c - Zlength (zp_got z) ->
  (Zlength u > cap \/ (Some (Zlength (zp_got z ++ u)) = cblock_size bh /\
     bp_last (block_props_of bh) = 1 /\ fcs_bad (zp_h z) (zp_out z ++ u))) ->
  cap_room z cap ->
  fbad sm cd (hdr ++ zp_bl z ++ (bh ++ zp_got z) ++ u).
Proof.
  intros u outc bh c cap Hbp H3 Ec Hc Hg Ty Eo Hu Herr Hroom.
  rewrite <- app_assoc. eapply fbz; eauto; [rewrite !Zlength_app; pose proof (Zlength_nonneg (zp_got z)); lia|].
  intro r. rewrite <- !app_assoc.
  set (t := bh ++ zp_got z ++ u ++ r).
  assert (Ect: cblock_size t = Some c) by (unfold t; rewrite cblock_size_app; auto; lia).
  pose proof (Zlength_nonneg r). pose proof (Zlength_nonneg (zp_got z)).
  destruct (Z_le_gt_dec c (Zlength t - 3)) as [Hin|Hout].
  2:{ unfold block_res. rewrite Ect. unfold ZSTD_blockHeaderSize.
      replace (c >? Zlength t - 3) with true by (symmetry; apply Zgtb_gt; lia). exact I. }
  rewrite (br_eq _ _ _ _ _ _ _ c) by auto. unfold blk_body. unfold t at 1. rewrite block_props_app by lia.
  rewrite Ty. cbn [Z.eqb]. replace (c >? zp_bsm z) with false by (symmetry; apply Zgtb_le; lia).
  unfold t. rewrite slice_hdr by auto. rewrite app_assoc, firstn_app.
  rewrite firstn_all2 by (rewrite length_app; rewrite !Zlength_correct in *; lia).
  set (d := firstn _ r). unfold blk_fails. rewrite (block_props_app bh) by lia.
  destruct Herr as [Hcap|[Hcmp [L Hbad]]].
  - right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. split; auto.
    rewrite Eo, !Zlength_app in Hr. rewrite !Zlength_app. pose proof (Zlength_nonneg d). lia.
  - left. rewrite L. split; auto.
    rewrite Ec in Hcmp. inversion Hcmp as [Hcmp']. rewrite Hcmp' in *.
    replace d with (@nil Z).
    2:{ unfold d. rewrite Zlength_app in Hcmp'. rewrite length_app. rewrite !Zlength_correct in Hcmp'.
        replace (Z.to_nat c - (length (zp_got z) + length u))%nat with O by lia. auto. }
    rewrite app_nil_r, app_assoc, <- Eo. intros Hf. destruct Hbad as [Hb1 Hb2]. destruct Hf; contradiction.
Qed.

Lemma err_body_nraw : forall u outc bh c cap, bytes_ok bh ->
  BP (zp_bl z) (zp_ts z) outc false ->
  Zlength bh = 3 -> cblock_size bh = Some c -> 0 < c <= zp_bsm z ->
  (bp_type (block_props_of bh) =? 0) = false -> zp_out z = outc -> Zlength u = c ->
  cont_errw DW (FP_zstd hdr z) u cap -> zp_ph z = ZP_body bh -> cap_room z cap ->
  fbad sm cd (hdr ++ zp_bl z ++ bh ++ u).
Proof.
  intros u outc bh c cap Hbh Hbp H3 Ec Hc Ty Eo Hu Herr Eph Hroom.
  unfold cont_errw, zp_hist in Herr. rewrite Eph, Ty, Eo in Herr. cbv zeta in Herr.
  eapply fbz; eauto; [rewrite Zlength_app; lia|].
  intro r. rewrite (br_app_eq _ _ _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
  rewrite (br_eq _ _ _ _ _ _ _ c); [| rewrite cblock_size_app; auto; lia | rewrite Zlength_app; lia].
  rewrite block_props_app by lia. rewrite slice_hdr by auto.
  rewrite firstn_all2 by (rewrite Zlength_correct in Hu; lia).
  unfold blk_body, blk_fails. rewrite Ty.
  pose proof (Zlength_nonneg outc).
  destruct (bp_type (block_props_of bh) =? 1).
  - replace (c >? zp_bsm z) with false by (symmetry; apply Zgtb_le; lia).
    rewrite Bool.orb_false_r.
    destruct (bp_origSize (block_props_of bh) >? zp_bsm z) eqn:Eb; [exact I|].
    apply Zgtb_le in Eb. pose proof (origSize_nonneg _ Hbh).
    rewrite Zlength_app, Zlength_repeat, Z2Nat.id by lia.
    destruct Herr as [Hcap|[Hbig|[L Hbad]]]; [|lia|].
    + right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. rewrite Eo in Hr. split; auto. lia.
    + left. rewrite L. split; auto. intros Hf. destruct Hbad as [Hb1 Hb2].
      destruct Hf as [Hf|Hf]; [contradiction|]. apply Hb2.
      rewrite <- Hf, !Zlength_app, !Zlength_repeat, !Z2Nat.id by lia. auto.
  - destruct (dec_block _ _ _ _ _ _ _) as [[ts2 c2]|] eqn:Edb; [|exact I].
    pose proof (dec_block_len _ _ _ _ _ _ _ _ _ Edb).
    destruct Herr as [Hcap|[L Hbad]].
    + right. destruct Hroom as [Hr|[Hu' Hr]]; [lia|]. rewrite Eo in Hr. split; auto. rewrite Zlength_app. lia.
    + left. rewrite L. split; auto. intros Hf. destruct Hbad as [Hb1 Hb2]. destruct Hf; contradiction.
Qed.

(* a wrong checksum: the frame is refused (FDetCk), or, with a content size matching Frame_Content_Size only modulo
   2^64, the model gives up on it (FUnk); it never ends in the model *)
Lemma err_ck : forall u outc,
  BP (zp_bl z) (zp_ts z) outc true ->
  fcs_okm (zp_h z) outc -> fh_checksumFlag (zp_h z) = 1 -> Zlength u = 4 ->
  zp_ign z = false -> le_field u 0 4 <> xxh64 outc 0 mod 2 ^ 32 ->
  fbad sm cd (hdr ++ zp_bl z ++ u).
Proof.
  intros u outc Hbp Hm Hc1 Hu Hig Hx.
  rewrite Hbsm in Hbp.
  eapply (fbad_zstd3_last sm cd hdr (zp_h z) (zp_dm z) G Hl Ht Hfd Hd Hb (zp_bl z) (zp_ts z) outc u Hbp).
  intros r c k.
  destruct (fcs_ok_dec (zp_h z) outc) as [Hf|Hf].
  2:{ unfold df_fin. cbv zeta. rewrite fcs_bad_cond by auto. discriminate. }
  unfold df_fin. cbv zeta. rewrite fcs_ok_cond by auto. rewrite Hc1. cbn [Z.eqb].
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
Qed.

Lemma err_bhdr : forall u outc, 0 < zp_bsm z ->
  BP (zp_bl z) (zp_ts z) outc false -> zp_out z = outc ->
  Zlength u = 3 ->
  match cblock_size u with
  | None => True
  | Some c => c > zp_bsm z \/ (c = 0 /\ bp_last (block_props_of u) = 1 /\ fcs_bad (zp_h z) (zp_out z))
  end ->
  fbad sm cd (hdr ++ zp_bl z ++ u).
Proof.
  intros u outc Hbsm0 Hbp Eo H3 Herr.
  eapply fbz; eauto; [lia|]. intro r.
  destruct (cblock_size u) as [c|] eqn:Ec.
  - cbv beta iota zeta in Herr. destruct Herr as [Hbig | (-> & L & Hbad)].
    + rewrite (br_big _ _ _ _ _ _ _ c); [exact I| |auto|auto]. rewrite cblock_size_app, Ec by lia. auto.
    + rewrite Eo in Hbad. apply br_empty_last_fails; auto; lia.
  - rewrite cblock_none_res; [exact I|]. rewrite cblock_size_app, Ec by lia. auto.
Qed.

End Step.
