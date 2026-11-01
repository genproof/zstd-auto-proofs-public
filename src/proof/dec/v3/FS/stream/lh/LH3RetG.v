(* Model helpers for the returns, copied from LH3G2.v (module G3M): the magicless format. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Zstd.proof.dec.FS.StreamModelFacts.
Local Open Scope logic.


Module RG.
Section CM_LH3RetG_RG.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.
Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Import Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Import Zstd.proof.dec.FS.StreamModelFacts.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma bs_pos : forall f t k nb, blocks_size f t = Some (k, nb) -> bytes_ok t -> 3 <= k.
Proof.
  induction f; intros t k nb H Hb; [discriminate|]. rewrite bs_S_eq in H.
  destruct (cblock_size t) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_nonneg _ _ Hb Ec).
  unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength t); [discriminate|].
  destruct (bp_last _ =? 1). { inversion H; lia. }
  destruct (blocks_size f _) as [[k2 nb2]|] eqn:E2; [|discriminate].
  inversion H; subst. pose proof (IHf _ _ _ E2 (bytes_ok_skipn _ _ Hb)). lia.
Qed.

Lemma bs_trunc : forall f t k nb, blocks_size f t = Some (k, nb) -> bytes_ok t ->
  forall t' r f', t = t' ++ r -> k <= Zlength t' -> (Z.to_nat k <= f')%nat ->
  blocks_size f' t' = Some (k, nb).
Proof.
  induction f; intros t k nb H Hb t' r f' Et Hk Hf; [discriminate|].
  pose proof (bs_pos _ _ _ _ H Hb) as H3.
  destruct f' as [|f']; [lia|].
  rewrite bs_S_eq in H |- *. subst t.
  destruct (cblock_size (t' ++ r)) as [c|] eqn:Ec; [|discriminate].
  pose proof (cblock_nonneg _ _ Hb Ec) as Hc.
  rewrite cblock_size_app in Ec by lia.
  rewrite Ec. rewrite block_props_app in H by lia.
  unfold ZSTD_blockHeaderSize in *.
  destruct (3 + c >? Zlength (t' ++ r)) eqn:E1; [discriminate|].
  destruct (bp_last (block_props_of t') =? 1).
  - inversion H; subst. replace (3 + c >? Zlength t') with false by (symmetry; apply Zgtb_le; lia). auto.
  - destruct (blocks_size f (skipn _ (t' ++ r))) as [[k2 nb2]|] eqn:E2; [|discriminate].
    inversion H; subst k nb.
    pose proof (bs_pos _ _ _ _ E2 (bytes_ok_skipn _ _ Hb)).
    replace (3 + c >? Zlength t') with false by (symmetry; apply Zgtb_le; lia).
    rewrite skipn_app_le in E2 by (rewrite Zlength_correct in *; lia).
    erewrite IHf; [reflexivity|exact E2| |reflexivity| |].
    + rewrite <- skipn_app_le by (rewrite Zlength_correct in *; lia). apply bytes_ok_skipn; auto.
    + rewrite Zlength_skipn by lia. lia.
    + lia.
Qed.

Lemma gfh_trunc : forall x r h, get_frame_header (x ++ r) = FH_ok h -> fh_headerSize h <= Zlength x ->
  0 <= byte_at (x ++ r) 4 < 256 -> get_frame_header x = FH_ok h.
Proof.
  intros x r h H Hx Hb. pose proof (Zlength_nonneg r).
  destruct (gfh_info _ _ H) as [[Ht [H8 [Em [Es [Hs Hc]]]]]|[Ht [H5 [Em [Hs [Hle [Hr Hw]]]]]]].
  - rewrite Hs in Hx.
    unfold get_frame_header in *. cbv zeta in *.
    rewrite Zlength_app in H. rewrite !(le_field_app x r) in H by lia. rewrite !(le_field_app x r) in Em, Es by lia.
    replace (Zlength x <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength x + Zlength r <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
    rewrite Em, Es in *. cbn [negb] in *.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *.
    replace (Zlength x <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength x + Zlength r <? 8) with false in H by (symmetry; apply Z.ltb_ge; lia).
    exact H.
  - assert (H5x: 5 <= Zlength x) by (pose proof (fhs_ge5 (byte_at (x ++ r) 4)); lia).
    rewrite (byte_at_app x r 4) in Hs, Hb by lia.
    pose proof (fhs_ge6 _ Hb) as H6. rewrite <- Hs in H6.
    unfold get_frame_header in *. cbv zeta in *.
    rewrite Zlength_app in H. rewrite (le_field_app x r 0 4) in H, Em by lia.
    rewrite (byte_at_app x r 4) in H by lia.
    replace (Zlength x <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength x + Zlength r <? 5) with false in H by (symmetry; apply Z.ltb_ge; lia).
    rewrite Em in *. rewrite Z.eqb_refl in *. cbn [negb] in *.
    set (fhd := byte_at x 4) in *.
    rewrite Hs in Hx.
    replace (Zlength x <? fhd_header_size fhd) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Zlength x + Zlength r <? fhd_header_size fhd) with false in H by (symmetry; apply Z.ltb_ge; lia).
    unfold fhd_header_size in Hx.
    destruct (fhd_cases fhd Hb) as [Hd [Hss Hcc]].
    destruct Hd as [Hd|[Hd|[Hd|Hd]]]; rewrite Hd in *;
    destruct Hss as [Hss|Hss]; rewrite Hss in *;
    destruct Hcc as [Hcc|[Hcc|[Hcc|Hcc]]]; rewrite Hcc in *;
    simpl nth in *; simpl Z.eqb in *; simpl andb in *; cbv iota in *;
    rewrite ?(le_field_app x r) in H by lia; rewrite ?(byte_at_app x r) in H by lia; exact H.
Qed.

Lemma fcs_trunc : forall s k, bytes_ok s -> frame_compressed_size s = Some k ->
  0 <= k /\ frame_compressed_size (firstn (Z.to_nat k) s) = Some k.
Proof.
  intros s k Hb H.
  pose proof (fcs_le _ _ H) as Hle. pose proof (fcs_len _ _ H) as H5.
  set (x := firstn (Z.to_nat k) s). set (r := skipn (Z.to_nat k) s).
  assert (Es: s = x ++ r) by (symmetry; apply firstn_skipn).
  unfold frame_compressed_size in H.
  destruct ((Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field s 0 4)) eqn:Ea.
  - apply andb_true_iff in Ea. destruct Ea as [E8 Em]. apply Z.geb_le in E8.
    unfold ZSTD_SKIPPABLEHEADERSIZE in *.
    unfold skippable_frame_size in H. unfold ZSTD_SKIPPABLEHEADERSIZE in H.
    replace (Zlength s <? 8) with false in H by (symmetry; apply Z.ltb_ge; lia).
    pose proof (le_field_bound s 4 4 Hb ltac:(lia)) as Hsz.
    destruct (le_field s 4 4 + 8 >? Zlength s) eqn:E2; [discriminate|].
    assert (Ek: k = le_field s 4 4 + 8) by congruence. split; [lia|].
    assert (Hx: Zlength x = le_field s 4 4 + 8).
    { unfold x. rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in Hle. lia. }
    assert (L0: le_field s 0 4 = le_field x 0 4) by (rewrite Es; apply le_field_app; lia).
    assert (L4: le_field s 4 4 = le_field x 4 4) by (rewrite Es; apply le_field_app; lia).
    unfold frame_compressed_size, skippable_frame_size, ZSTD_SKIPPABLEHEADERSIZE.
    rewrite <- L0, <- L4, Em, Hx.
    replace (le_field s 4 4 + 8 >=? 8) with true by (symmetry; apply Z.geb_le; lia).
    replace (le_field s 4 4 + 8 <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (le_field s 4 4 + 8 >? le_field s 4 4 + 8) with false by (symmetry; apply Zgtb_le; lia).
    rewrite Ek. reflexivity.
  - destruct (get_frame_header s) as [| |h] eqn:G; try discriminate. cbv zeta in H.
    destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
    assert (Hhs: 5 <= fh_headerSize h <= Zlength s).
    { destruct (gfh_info _ _ G) as [[_ [? [_ [_ [-> _]]]]]|[_ [_ [_ [Hs [Hl _]]]]]]; [lia|].
      pose proof (fhs_ge5 (byte_at s 4)). lia. }
    pose proof (bytes_ok_skipn (Z.to_nat (fh_headerSize h)) _ Hb) as Hbr.
    pose proof (bs_pos _ _ _ _ B Hbr) as Hkb.
    destruct (bs_len _ _ _ _ B) as [_ Bk]. rewrite Zlength_skipn in Bk by lia.
    assert (Hk: k = fh_headerSize h + kb \/ (k = fh_headerSize h + kb + 4 /\ fh_checksumFlag h = 1 /\
               4 <= Zlength s - (fh_headerSize h + kb))).
    { destruct (fh_checksumFlag h =? 1) eqn:Ec.
      - destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|].
        apply Z.ltb_ge in E4. apply Z.eqb_eq in Ec. right. split; [congruence|auto].
      - left; congruence. }
    assert (Hk0: 0 <= k) by lia. split; [exact Hk0|].
    assert (Hx: Zlength x = k).
    { unfold x. rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in Hle. lia. }
    assert (Gx: get_frame_header x = FH_ok h).
    { apply (gfh_trunc x r); [rewrite <- Es; auto|lia|rewrite <- Es; apply bytes_ok_byte_at; auto]. }
    assert (L0: le_field s 0 4 = le_field x 0 4) by (rewrite Es; apply le_field_app; lia).
    unfold frame_compressed_size.
    replace ((Zlength x >=? ZSTD_SKIPPABLEHEADERSIZE) && is_skippable_magic (le_field x 0 4)) with false.
    2:{ rewrite <- L0. destruct (is_skippable_magic (le_field s 0 4)) eqn:Esk.
        - rewrite andb_true_r in Ea |- *. unfold ZSTD_SKIPPABLEHEADERSIZE in *.
          rewrite Z.geb_leb, Z.leb_gt in Ea. symmetry. rewrite Z.geb_leb, Z.leb_gt. lia.
        - rewrite andb_false_r. reflexivity. }
    rewrite Gx. cbv zeta.
    assert (Er: skipn (Z.to_nat (fh_headerSize h)) s = skipn (Z.to_nat (fh_headerSize h)) x ++ r).
    { rewrite Es at 1. apply skipn_app_le. rewrite Zlength_correct in Hx. lia. }
    rewrite (bs_trunc _ _ _ _ B Hbr (skipn (Z.to_nat (fh_headerSize h)) x) r).
    + destruct Hk as [Hk|[Hk [Hc H4]]].
      * destruct (fh_checksumFlag h =? 1) eqn:Ec.
        -- destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|].
           apply Z.ltb_ge in E4. apply Z.eqb_eq in Ec. inversion H. lia.
        -- auto.
      * assert (H0: Zlength x - (fh_headerSize h + kb) <? 4 = false) by (apply Z.ltb_ge; lia).
        rewrite Hc, H0, Hk. reflexivity.
    + exact Er.
    + rewrite Zlength_skipn by lia. lia.
    + rewrite length_skipn. rewrite Zlength_correct in Hx. lia.
Qed.

Lemma hdr_le_fcs : forall s k h, bytes_ok s -> frame_compressed_size s = Some k ->
  get_frame_header s = FH_ok h -> fh_headerSize h <= k.
Proof.
  intros s k h Hb H G. unfold frame_compressed_size in H.
  destruct (gfh_info _ _ G) as [[Ht [H8 [Em [Es [Hs Hc]]]]]|[Ht [H5 [Em [Hs [Hle _]]]]]].
  - unfold ZSTD_SKIPPABLEHEADERSIZE in *.
    replace (Zlength s >=? 8) with true in H by (symmetry; apply Z.geb_le; lia).
    rewrite Es in H. cbn [andb] in H.
    unfold skippable_frame_size, ZSTD_SKIPPABLEHEADERSIZE in H.
    pose proof (le_field_bound s 4 4 Hb ltac:(lia)).
    destruct (Zlength s <? 8); [discriminate|].
    destruct (_ >? _); [discriminate|].
    inversion H. lia.
  - rewrite Em, skip_magic_false, andb_false_r, G in H. cbv zeta in H.
    destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
    pose proof (bs_pos _ _ _ _ B (bytes_ok_skipn _ _ Hb)).
    destruct (fh_checksumFlag h =? 1); [destruct (_ <? 4); [discriminate|]|]; inversion H; lia.
Qed.


(* ---------- the magicless format: get_frame_header_m mg / frame_compressed_size_m mg ---------- *)

Lemma magic_ok : bytes_ok magic_bytes.
Proof. cbv. repeat constructor; cbv; congruence. Qed.

Lemma magic_len : Zlength magic_bytes = 4.
Proof. reflexivity. Qed.

Lemma magic_le : forall x, le_field (magic_bytes ++ x) 0 4 = ZSTD_MAGICNUMBER.
Proof. intros. rewrite le_field_app by (rewrite ?magic_len; lia). reflexivity. Qed.

Lemma gfh_m_ext : forall mg x r h, bytes_ok x -> get_frame_header_m mg x = FH_ok h ->
  get_frame_header_m mg (x ++ r) = FH_ok h.
Proof.
  intros mg x r h Hb H. destruct mg; unfold get_frame_header_m in *; cbn [negb] in *.
  - destruct (Zlength x <? 1) eqn:E; [discriminate|]. apply Z.ltb_ge in E.
    replace (Zlength (x ++ r) <? 1) with false by (symmetry; apply Z.ltb_ge; rewrite Zlength_app; pose proof (Zlength_nonneg r); lia).
    destruct (get_frame_header (magic_bytes ++ x)) as [| |h0] eqn:G; try discriminate.
    rewrite app_assoc, (gfh_ext _ r _ G); auto.
    apply bytes_ok_byte_at. apply bytes_ok_app. split; [apply magic_ok|auto].
  - apply gfh_ext; auto. apply bytes_ok_byte_at; auto.
Qed.

Lemma gfh_m_trunc : forall mg x r h, bytes_ok (x ++ r) -> get_frame_header_m mg (x ++ r) = FH_ok h ->
  fh_headerSize h <= Zlength x -> get_frame_header_m mg x = FH_ok h.
Proof.
  intros mg x r h Hb H Hx. destruct mg; unfold get_frame_header_m in *; cbn [negb] in *.
  - destruct (Zlength (x ++ r) <? 1) eqn:E; [discriminate|].
    destruct (get_frame_header (magic_bytes ++ x ++ r)) as [| |h0] eqn:G; try discriminate.
    injection H as <-.
    destruct (gfh_info _ _ G) as [[_ [_ [Em _]]]|[_ [_ [_ [Hs _]]]]].
    { rewrite magic_le in Em. discriminate. }
    pose proof (fhs_ge5 (byte_at (magic_bytes ++ x ++ r) 4)) as H5.
    cbn [fh_unshift fh_headerSize] in Hx.
    replace (Zlength x <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite app_assoc in G. rewrite (gfh_trunc (magic_bytes ++ x) r h0); auto.
    + rewrite Zlength_app, magic_len. lia.
    + apply bytes_ok_byte_at. rewrite <- app_assoc. apply bytes_ok_app. split; [apply magic_ok|auto].
  - apply (gfh_trunc x r); auto. apply bytes_ok_byte_at; auto.
Qed.

Lemma gfh_m_hs : forall x h, get_frame_header_m true x = FH_ok h -> 1 <= fh_headerSize h <= Zlength x.
Proof.
  intros x h H. unfold get_frame_header_m in H. cbn [negb] in H.
  destruct (Zlength x <? 1) eqn:E; [discriminate|].
  destruct (get_frame_header (magic_bytes ++ x)) as [| |h0] eqn:G; try discriminate.
  injection H as <-.
  destruct (gfh_info _ _ G) as [[_ [_ [Em _]]]|[_ [_ [_ [Hs [Hle _]]]]]].
  { rewrite magic_le in Em. discriminate. }
  pose proof (fhs_ge5 (byte_at (magic_bytes ++ x) 4)).
  rewrite Zlength_app, magic_len in Hle. cbn [fh_unshift fh_headerSize]. lia.
Qed.

Lemma fcs_m_trunc : forall mg s k, bytes_ok s -> frame_compressed_size_m mg s = Some k ->
  0 <= k <= Zlength s /\ frame_compressed_size_m mg (firstn (Z.to_nat k) s) = Some k.
Proof.
  intros mg s k Hb H. destruct mg.
  2:{ rewrite frame_compressed_size_zstd1 in *. pose proof (fcs_le _ _ H).
      destruct (fcs_trunc _ _ Hb H). split; [lia|auto]. }
  unfold frame_compressed_size_m in *. cbn [negb] in *.
  destruct (get_frame_header_m true s) as [| |h] eqn:G; try discriminate. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  pose proof (gfh_m_hs _ _ G) as Hhs.
  pose proof (bytes_ok_skipn (Z.to_nat (fh_headerSize h)) _ Hb) as Hbr.
  pose proof (bs_pos _ _ _ _ B Hbr) as Hkb.
  destruct (bs_len _ _ _ _ B) as [_ Bk]. rewrite Zlength_skipn in Bk by lia.
  assert (Hk: k = fh_headerSize h + kb \/ (k = fh_headerSize h + kb + 4 /\ fh_checksumFlag h = 1 /\
             4 <= Zlength s - (fh_headerSize h + kb))).
  { destruct (fh_checksumFlag h =? 1) eqn:Ec.
    - destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|].
      apply Z.ltb_ge in E4. apply Z.eqb_eq in Ec. right. split; [congruence|auto].
    - left; congruence. }
  assert (Hks: 0 <= k <= Zlength s) by lia. split; [exact Hks|].
  set (x := firstn (Z.to_nat k) s). set (r := skipn (Z.to_nat k) s).
  assert (Es: s = x ++ r) by (symmetry; apply firstn_skipn).
  assert (Hx: Zlength x = k).
  { unfold x. rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in Hks. lia. }
  assert (Gx: get_frame_header_m true x = FH_ok h).
  { apply (gfh_m_trunc true x r); [rewrite <- Es; auto|rewrite <- Es; auto|lia]. }
  rewrite Gx. cbv zeta.
  assert (Er: skipn (Z.to_nat (fh_headerSize h)) s = skipn (Z.to_nat (fh_headerSize h)) x ++ r).
  { rewrite Es at 1. apply skipn_app_le. rewrite Zlength_correct in Hx. lia. }
  rewrite (bs_trunc _ _ _ _ B Hbr (skipn (Z.to_nat (fh_headerSize h)) x) r).
  + destruct Hk as [Hk|[Hk [Hc H4]]].
    * destruct (fh_checksumFlag h =? 1) eqn:Ec.
      -- destruct (Zlength s - (fh_headerSize h + kb) <? 4) eqn:E4; [discriminate|].
         apply Z.ltb_ge in E4. apply Z.eqb_eq in Ec. inversion H. lia.
      -- auto.
    * assert (H0: Zlength x - (fh_headerSize h + kb) <? 4 = false) by (apply Z.ltb_ge; lia).
      rewrite Hc, H0, Hk. reflexivity.
  + exact Er.
  + rewrite Zlength_skipn by lia. lia.
  + rewrite length_skipn. rewrite Zlength_correct in Hx. lia.
Qed.

Lemma hdr_le_fcs_m : forall mg s k h, bytes_ok s -> frame_compressed_size_m mg s = Some k ->
  get_frame_header_m mg s = FH_ok h -> fh_headerSize h <= k.
Proof.
  intros mg s k h Hb H G. destruct mg.
  2:{ eapply hdr_le_fcs; eauto. }
  unfold frame_compressed_size_m in H. cbn [negb] in H. rewrite G in H. cbv zeta in H.
  destruct (blocks_size _ _) as [[kb nb]|] eqn:B; [|discriminate].
  pose proof (bs_pos _ _ _ _ B (bytes_ok_skipn _ _ Hb)).
  destruct (fh_checksumFlag h =? 1); [destruct (_ <? 4); [discriminate|]|]; inversion H; lia.
Qed.

Lemma gap_of_hdr_m : forall mg ibs ipos ipc isz hb h cSize, bytes_ok ibs -> Zlength ibs = isz ->
  0 <= ipos -> ipos <= ipc -> ipc <= isz -> sublist ipos ipc ibs = hb ->
  get_frame_header_m mg hb = FH_ok h -> fh_headerSize h = Zlength hb ->
  frame_compressed_size_m mg (sublist ipos isz ibs) = Some cSize -> ipc <= ipos + cSize.
Proof.
  intros mg ibs ipos ipc isz hb h cSize Hb Hl H0 H1 H2 Ehb G Hs F.
  assert (Hy: sublist ipos isz ibs = hb ++ sublist ipc isz ibs).
  { rewrite <- Ehb. rewrite <- sublist_split; auto; lia. }
  assert (Hbh: bytes_ok hb) by (rewrite <- Ehb; unfold bytes_ok in *; apply Forall_sublist; auto).
  assert (Gy: get_frame_header_m mg (sublist ipos isz ibs) = FH_ok h) by (rewrite Hy; apply gfh_m_ext; auto).
  assert (Hby: bytes_ok (sublist ipos isz ibs)) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  pose proof (hdr_le_fcs_m _ _ _ _ Hby F Gy).
  assert (Zlength hb = ipc - ipos) by (rewrite <- Ehb, Zlength_sublist; lia). lia.
Qed.

End CM_LH3RetG_RG.
End RG.

