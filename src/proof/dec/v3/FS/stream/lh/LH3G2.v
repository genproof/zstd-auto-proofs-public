(* FS3 streaming, case zdss_loadHeader: G2, the break after a successful shortcut -> loop invariant. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib.
Require Zstd.proof.dec.FS.StreamModelFacts Zstd.proof.dec.v3.FS.stream.lh.LH3G2SerR1 Zstd.proof.dec.v3.FS.stream.lh.LH3G2BytesR1 Zstd.proof.dec.v3.FS.stream.lh.LH3G2Sel.
Local Open Scope logic.

Section CM_LH3G2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- model helpers (v2's StreamSeg_lhG2 G2M, and the magicless format) ---------- *)

End CM_LH3G2_1.

Module G3M.
Section CM_LH3G2_G3M.
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

End CM_LH3G2_G3M.
End G3M.


Module G3N.
Section CM_LH3G2_G3N.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.
Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Import Zstd.proof.model.Params Zstd.proof.model.ParamsH.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma zbytes_inj (a b: list Z) : bytes_ok a -> bytes_ok b -> zbytes a = zbytes b -> a = b.
Proof.
  revert b. induction a as [ | x a IH]; intros [ | y b] Ha Hb E; simpl in E; try discriminate; auto.
  assert (Hx: Vint (Int.repr x) = Vint (Int.repr y)) by congruence.
  assert (Ht: zbytes a = zbytes b) by congruence.
  inv Ha. inv Hb. f_equal; [| apply IH; auto].
  unfold is_byte in *.
  apply (f_equal (fun v => match v with Vint i => Int.unsigned i | _ => 0 end)) in Hx. simpl in Hx.
  rewrite !Int.unsigned_repr in Hx by rep_lia. auto.
Qed.

Lemma app_eq_len : forall (l1 l2 l3 l4: list Z), l1 ++ l2 = l3 ++ l4 -> Zlength l2 = Zlength l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  intros l1 l2 l3 l4 E L.
  assert (L1: length l1 = length l3).
  { apply (f_equal (@length Z)) in E. rewrite !length_app in E. rewrite !Zlength_correct in L. lia. }
  split.
  - apply (f_equal (firstn (length l1))) in E. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all in E.
    rewrite L1, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all in E. auto.
  - apply (f_equal (skipn (length l1))) in E. rewrite skipn_app, Nat.sub_diag, skipn_O, skipn_all in E.
    rewrite L1, skipn_app, Nat.sub_diag, skipn_O, skipn_all in E. auto.
Qed.

Lemma walk_cur_none : forall f md wl s, walk_cur f md sel_none None wl s = None.
Proof.
  induction f; intros; cbn [walk_cur]; auto.
  destruct (_ <? _); auto. destruct (_ && _).
  - destruct (skippable_frame_size s); auto. unfold skip_cd, sel_none. destruct (md_dwin md); apply IHf.
  - unfold frame_dict. destruct (get_frame_header_m _ s) eqn:G; [| |unfold sel_none; auto].
    all: destruct (decode_frame_m md no_dict wl s) eqn:D; auto; exfalso;
      destruct (LH3G2SerR1.g2_df_hdr _ _ _ _ _ _ D) as [h' G']; congruence.
Qed.

(* the model side: the old relation on sin0 ++ hb (the header loaded, cd the dictionary current before it), the
   frame x = input[ipos, ipos + cSize) decoded by the shortcut with the frame's dictionary, its content c delivered *)
Lemma brkB_model : MF3 -> forall (sm: smode) sin0 ibs ipos ipc isz hb h cSize sout r out c cap cd,
  bytes_ok sin0 -> bytes_ok ibs -> Zlength ibs = isz -> 0 <= ipos <= ipc -> ipc <= ipos + cSize ->
  ipos + cSize <= isz -> sublist ipos ipc ibs = hb ->
  get_frame_header_m (sm_mg sm) hb = FH_ok h -> fh_frameType h = 0 -> fh_headerSize h = Zlength hb ->
  frame_compressed_size_m (sm_mg sm) (sublist ipos isz ibs) = Some cSize ->
  m_rel_cd sm (sin0 ++ hb ++ nil) sout (FP_hdr hb) nil cd ->
  (forall dm, frame_dict (sm_mg sm) (sm_sel sm) cd hb = Some dm ->
     oneshot_ok (md_len (sm_md sm)) (Some dm) (sublist ipos (ipos + cSize) ibs) cap r out /\
     LH3G2BytesR1.g2_dm_ok dm) ->
  is_error_code r = false -> bytes_ok c -> sublist 0 r out = zbytes c ->
  dead sm (sin0 ++ sublist ipos (ipos + cSize) ibs ++ nil) \/
  exists dm, frame_dict (sm_mg sm) (sm_sel sm) cd hb = Some dm /\
    m_rel_cd sm (sin0 ++ sublist ipos (ipos + cSize) ibs ++ nil) (sout ++ c) FP_none nil (Some dm).
Proof.
  intros MFh sm sin0 ibs ipos ipc isz hb h cSize sout r out c cap cd Hs0 Hib Hlen H0 H1 H2 Ehb
    G Ht Hhs Hfcs Hm Hos Hr Hc Hco.
  set (x := sublist ipos (ipos + cSize) ibs).
  assert (Hx: x = hb ++ sublist ipc (ipos + cSize) ibs).
  { unfold x. rewrite <- Ehb. rewrite <- sublist_split; auto; lia. }
  assert (Hbx: bytes_ok x) by (unfold x, bytes_ok in *; apply Forall_sublist; auto).
  assert (Hbh: bytes_ok hb) by (rewrite <- Ehb; unfold bytes_ok in *; apply Forall_sublist; auto).
  assert (Hy: bytes_ok (sublist ipos isz ibs)) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  destruct Hm as (dsin & fb & recs & Hsin & Hser & Hcur & Hcr & Hout).
  cbn [cur_rel] in Hcr. destruct Hcr as [-> _].
  rewrite app_nil_r in Hsin.
  destruct (app_eq_len _ _ _ _ Hsin) as [<- _]; [reflexivity|].
  cbn [fp_content] in Hout. rewrite !app_nil_r in Hout.
  assert (Hdf: fdead sm cd x -> dead sm (sin0 ++ x ++ nil)).
  { intros Hf. rewrite app_nil_r. eapply (mf_dead_of_fdead MFh); eauto. }
  assert (Hfx: frame_dict (sm_mg sm) (sm_sel sm) cd x = frame_dict (sm_mg sm) (sm_sel sm) cd hb).
  { rewrite Hx. apply LH3G2SerR1.g2_fd_ext with (h := h); auto. }
  destruct (frame_dict (sm_mg sm) (sm_sel sm) cd hb) as [dm|] eqn:Fd.
  2:{ left. apply Hdf.
      destruct (mf_hdr_zstd MFh sm cd hb h Hbh G Ht ltac:(lia)) as [Hn _].
      rewrite Hx. apply (mf_fdead_app MFh). apply Hn. exact Fd. }
  destruct (Hos dm eq_refl) as [Hos1 Hdmok]. fold x in Hos1.
  assert (Hsf: shortcut_frame sm cd x dm).
  { split; [|split].
    - destruct (G3M.fcs_m_trunc _ _ _ Hy Hfcs) as [Hk Hxk].
      rewrite <- sublist_firstn, sublist_sublist in Hxk by lia. rewrite !Z.add_0_l, Z.add_comm in Hxk.
      fold x in Hxk. replace (Zlength x) with cSize; auto. unfold x. rewrite Zlength_sublist; lia.
    - exists h. split; auto. rewrite Hx. apply G3M.gfh_m_ext; auto.
    - exact Hfx. }
  destruct Hos1 as [_ Hos1].
  destruct (series_frames_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x) as [l t] eqn:Ex.
  assert (Hds: decode_series_m (md_len (sm_md sm)) sel_none (Some dm) no_wlim x =
               match t with TEnd => SOk (flat_map fr_content l) | TDetHdr => SDet | TDetCk => SDet | TUnk => SUnk end).
  { unfold decode_series_m. rewrite Ex. destruct t; auto. }
  rewrite Hds in Hos1.
  destruct t.
  - destruct Hos1 as [Hos1 _]. destruct (Hos1 Hr) as [Hrc Hoc].
    assert (Hbc': bytes_ok (flat_map fr_content l)).
    { apply (proj2 LH3G2BytesR1.g2_bytes_facts (md_len (sm_md sm)) dm no_wlim x l TEnd); auto. }
    assert (flat_map fr_content l = c) as Ec by (apply zbytes_inj; auto; congruence).
    destruct (mf_shortcut_ok MFh sm cd x dm (flat_map fr_content l) Hbx Hsf ltac:(rewrite Hds; reflexivity))
      as [(rec & Hs1 & Hrc' & _ & _ & Hca)|Hfd]; [|left; apply Hdf; exact Hfd].
    destruct (LH3G2SerR1.g2_series_app (sm_md sm) (sm_sel sm) (sm_cur sm) sin0 recs x [rec] Hs0 Hbx Hser)
      as [Hser' Hcur'].
    { unfold series_cur in *. unfold sm_curafter, series_cur in Hcur. rewrite Hcur. exact Hs1. }
    right. exists dm. split; [reflexivity|].
    exists (sin0 ++ x), nil, (recs ++ map (StreamModelFacts.fshift (Zlength sin0)) [rec]).
    split; [rewrite !app_nil_r; auto|]. split; [exact Hser'|].
    split.
    { assert (E: series_cur (sm_md sm) (sm_sel sm) (sm_cur sm) no_wlim sin0 = cd) by exact Hcur.
      rewrite Hcur', E. exact Hca. }
    split; [cbn [cur_rel]; auto|].
    cbn [fp_content map]. rewrite flat_map_app. cbn [flat_map]. rewrite !app_nil_r.
    rewrite Hout. cbn [StreamModelFacts.fshift fr_content]. rewrite Hrc', Ec. auto.
  - exfalso. rewrite Hos1 in Hr. discriminate.
  - exfalso. rewrite Hos1 in Hr. discriminate.
  - left. apply Hdf. apply (mf_shortcut_unk MFh sm cd x dm); auto.
    (* the one-shot claim: a refused frame gives an error, and the shortcut succeeded *)
    intros Href. rewrite (Hos1 Href) in Hr. discriminate.
Qed.

End CM_LH3G2_G3N.
End G3N.

Section CM_LH3G2_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* ---------- the dictionaries' bytes ---------- *)

Definition not_ref (od: option dictref) : Prop :=
  forall dr, od = Some dr -> match dr_src dr with DSRef _ => False | _ => True end.

Lemma g2_dm_of : forall od dm, dictref_model od = Some dm -> (forall dr, od = Some dr -> bytes_ok (dr_bytes dr)) ->
  LH3G2BytesR1.g2_dm_ok dm.
Proof.
  intros od dm H Hb. unfold dictref_model in H. destruct od as [dr|].
  - specialize (Hb dr eq_refl). destruct (dr_raw dr).
    + injection H as <-. split; [exact Hb|exact I].
    + exact (proj1 LH3G2BytesR1.g2_bytes_facts _ _ Hb H).
  - injection H as <-. split; [constructor|exact I].
Qed.


(* what the context's representation says: ddictIsCold, a set has a table *)
Lemma g2_ctx_facts : forall DENT TABS gv p k,
  ctx_rep3 DENT TABS gv p k |-- !! (cold01 (c3_fs k) /\ (c3_set k <> nil -> c3_sp k <> nullval) /\
                                    (c3_set k = nil -> c3_sp k = nullval)).
Proof.
  intros DENT TABS gv p k.
  unfold ctx_rep3, ctx_body3, fgroup3, hset_rep.
  destruct (eq_dec (c3_sp k) nullval) as [Esp|Esp].
  - Intros. apply prop_right. split; [auto|split; intros; congruence].
  - Intros tp tbl. apply prop_right. split; [auto|split; intros; congruence].
Qed.

(* the own dictionary's bytes are the local DDict's *)
Lemma g2_own_bytes : forall DENT TABS gv p k,
  ctx_rep3 DENT TABS gv p k |-- !! (forall od, dict_rel3_of od (c3_dict k) -> forall dr, od = Some dr ->
                                     dr_src dr = DSOwn -> bytes_ok (dr_bytes dr)).
Proof.
  intros DENT TABS gv p k. unfold ctx_rep3, ctx_body3, dgroup, local_rep.
  destruct (eq_dec (df_local (c3_dict k)) nullval) as [E0|E0].
  - apply prop_right. intros od Hr dr -> Es. cbv beta iota zeta delta [dict_rel3_of] in Hr. rewrite Es in Hr.
    destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
    + apply Z.eqb_eq, Zlength_nil_inv in Ez. rewrite Ez. constructor.
    + destruct Hr as (buf & ld & am & Hp & _). rewrite E0 in Hp. contradiction.
  - destruct (df_lx (c3_dict k)) as [[x buf]|] eqn:Elx.
    + unfold ddict_rep_at, ddict_struct. Intros. apply prop_right. intros od Hr dr -> Es.
      cbv beta iota zeta delta [dict_rel3_of] in Hr. rewrite Es in Hr.
      destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
      * apply Z.eqb_eq, Zlength_nil_inv in Ez. rewrite Ez. constructor.
      * destruct Hr as (buf' & ld & am' & _ & _ & _ & Hlx). rewrite Elx in Hlx. inversion Hlx; subst. cbn in *. assumption.
    + apply prop_right. intros od Hr dr -> Es. cbv beta iota zeta delta [dict_rel3_of] in Hr. rewrite Es in Hr.
      destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0) eqn:Ez.
      * apply Z.eqb_eq, Zlength_nil_inv in Ez. rewrite Ez. constructor.
      * destruct Hr as (buf' & ld & am' & _ & _ & _ & Hlx). rewrite Elx in Hlx. discriminate.
Qed.

Lemma g2_ddres_bytes : forall DENT gv sh q dd, ddict_res (DD3x DENT) gv sh q dd |-- !! bytes_ok (dd_bytes dd).
Proof.
  intros. unfold ddict_res.
  eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl|apply derives_refl]|].
  unfold DD3x, DD3_of, ddict_rep_at, ddict_struct. Intros. apply prop_right. cbn in *. assumption.
Qed.

Lemma g2_dictres_bytes : forall DENT gv sh od, dict_res (DD3x DENT) gv sh od |--
  !! (forall dr q dd, od = Some dr -> dr_src dr = DSDDict q dd -> bytes_ok (dd_bytes dd)).
Proof.
  intros. unfold dict_res. destruct od as [dr|]; [|apply prop_right; intros; discriminate].
  destruct (dr_src dr) as [pk| |q dd] eqn:Es; try (apply prop_right; intros dr0 q0 dd0 E E2; injection E as <-; congruence).
  sep_apply (g2_ddres_bytes DENT gv sh q dd). Intros. apply prop_right. intros dr0 q0 dd0 E E2. injection E as <-.
  rewrite Es in E2. injection E2 as <- <-. assumption.
Qed.

Lemma g2_setres_bytes : forall DENT gv sh l cur, set_res (DD3x DENT) gv sh l cur |--
  !! Forall (fun e => cur_ddict cur = Some (fst e) \/ bytes_ok (dd_bytes (snd e))) l.
Proof.
  intros DENT gv sh l cur. induction l as [|e l IH]; unfold set_res in *; cbn [map fold_right].
  - apply prop_right. constructor.
  - destruct (cur_ddict cur) as [q|] eqn:Ec; [destruct (Val.eq (fst e) q) as [Eq|Eq]|].
    + sep_apply IH. Intros. apply prop_right. constructor; auto; left; congruence.
    + sep_apply (g2_ddres_bytes DENT gv sh (fst e) (snd e)). Intros. sep_apply IH. Intros.
      apply prop_right. constructor; auto.
    + sep_apply (g2_ddres_bytes DENT gv sh (fst e) (snd e)). Intros. sep_apply IH. Intros.
      apply prop_right. constructor; auto.
Qed.

Lemma not_ref_of : forall W st, stream_dict_ok W st -> not_ref (dc_dict st).
Proof.
  unfold stream_dict_ok, not_ref. intros W st [H _] dr E. rewrite E in H. destruct H as [_ H].
  destruct (dr_src dr); auto.
Qed.

(* the new view: no frame in progress *)
Definition sv0 : sview := {| sv_fp := FP_none; sv_pend := nil; sv_ahead := nil; sv_lay := HL_none; sv_dd := None |}.

Definition lw_sv0 (w: lw) : lw :=
  {| w_smw := w_smw w; w_k := w_k w; w_sv := sv0; w_ipc := w_ipc w; w_opc := w_opc w; w_oc := w_oc w;
     w_dl := w_dl w |}.

Lemma brkB_pure : MF3 -> hs_probe_ok -> forall a w hb h tbl d1 did1 cSize r out c fs' d' lxb',
  lh_ctx a w hb -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
  lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
  lhB_facts a w (k_A (w_k w) (fh_val h) d1 did1) hb h cSize r out -> is_error_code r = false ->
  bytes_ok c -> Zlength c = r -> sublist 0 r out = zbytes c -> lhB_dict (k_A (w_k w) (fh_val h) d1 did1) d' ->
  fp_ok (fs_fParams fs') ->
  lhB_sel_fp (k_A (w_k w) (fh_val h) d1 did1) tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d' ->
  lhB_sw (k_A (w_k w) (fh_val h) d1 did1) tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d' ->
  sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w) ->
  (dc_set (a_st a) = nil -> forall dr q dd, dc_dict (a_st a) = Some dr -> dr_src dr = DSDDict q dd ->
     bytes_ok (dr_bytes dr)) ->
  cold01 (fsu_expected fs' (vlong 0)) -> (c3_set (w_k w) <> nil -> c3_sp (w_k w) <> nullval) ->
  (c3_set (w_k w) = nil -> c3_sp (w_k w) = nullval) ->
  (forall q dd, In (q, dd) (dc_set (a_st a)) -> bytes_ok (dd_bytes dd)) ->
  (dict_rel3_of (dc_dict (a_st a)) d' -> forall dr, dc_dict (a_st a) = Some dr -> dr_src dr = DSOwn ->
     bytes_ok (dr_bytes dr)) ->
  0 <= sf_held (c3_s (w_k (lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c))) -
       local_held (c3_dict (w_k (lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c))) ->
  fold_right and True
    (ds_LI_P a (lw_sv0 (lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c))).
Proof.
  intros MFh HP a w hb h tbl d1 did1 cSize r out c fs' d' lxb' Hc G Hgf HA HB Hr Hcb Hcl Hco HD Hfp' HSF HD2 Hut Hdrb
    Hcold Hsp Hsp0 HBset HBown Hheld.
  set (k1 := k_A (w_k w) (fh_val h) d1 did1) in *.
  set (x := sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) in *.
  destruct Hc as (Ha & Hstart & Hci & Hsmw & Hle & He & Hfp & Hdl & Hah & Hpend & Hen & Hunt).
  destruct He as (Hstg & Hlh & Hhb18 & Hbhb & Hhbuf & Hhost & Hinpos & Hos & Hoe & Hipc & Hopc & Hloc & _ & Hbase & Hlenok).
  assert (Hsd: stream_dict_ok (a_W a) (a_st a)).
  { unfold dsa_ok in Ha. destruct Ha as (_ & _ & _ & _ & _ & _ & _ & Hsd & _). exact Hsd. }
  assert (Hdr': dict_rel3 (a_st a) d') by (eapply (LH3G2Sel.g2s_dict_rel_brk HP (a_W a)); eauto).
  assert (Hbase' := Hbase).
  destruct Hbase' as (Hstab & Hpar & Hset & Hdr & Hsco & Hfp0).
  unfold call_inv in Hci. cbv zeta in Hci. rewrite Hdl, Hah, Hfp, Hpend in Hci.
  destruct Hci as (Hipc0 & Hopc0 & Hloc0 & Hpre & Hldl & Hdlc & Hdlb & Hbc & Hsin & Hnfp & Hprog & Hss & Hcore &
                   Hsvdd & Hstabo & Hah' & Hemp & Halive & Hlhj & Hsin' & Hexp & Hflush).
  destruct HB as (Hft & Hcs & Hcap & Hipcl & Hfcs & HcS & Hr0 & Hlo & Hrcap & Herr & Hosk).
  assert (Hopc_eq: w_opc w = a_opos a) by (rewrite Zlength_nil in Hldl; lia).
  assert (Hrc: r <= a_osz a - w_opc w) by auto.
  assert (Hib: bytes_ok (a_ibs a) /\ Zlength (a_ibs a) = a_isz a /\ 0 <= a_ipos a /\ a_isz a <= 2 ^ 63 - 1 /\
               0 <= a_opos a /\ a_osz a <= 2 ^ 63 - 1).
  { unfold dsa_ok in Ha. tauto. }
  destruct Hib as (Hibb & Hibl & Hip0 & Hisz & Hop0 & Hosz).
  assert (Hhb: hb = sublist (a_ipos a) (w_ipc w) (a_ibs a)).
  { destruct (Hlhj Hstg hb eq_refl) as (pre & j & Hj & Hhb & Hjj). subst j.
    destruct pre as [ | p0 pre ]; [exact Hhb|].
    exfalso. rewrite Hhb, Zlength_app, Zlength_sublist, Zlength_cons in Hipcl by lia.
    pose proof (Zlength_nonneg pre). lia. }
  assert (Hhs: fh_headerSize h = Zlength hb) by (unfold hdr_lenok in Hlenok; rewrite G in Hlenok; exact Hlenok).
  assert (Ht0: fh_frameType h = 0) by (destruct Hgf as (_ & _ & _ & _ & _ & _ & [?|?] & _); [auto|contradiction]).
  assert (Hid: 0 <= fh_dictID h <= Int.max_unsigned) by (destruct Hgf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); auto).
  assert (Hhb1: 1 <= Zlength hb).
  { destruct Hgf as (Hsl & _). unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in Hsl.
    destruct (lh_mg (w_k w)); lia. }
  assert (Hgap: w_ipc w <= a_ipos a + cSize).
  { apply (G3M.gap_of_hdr_m (lh_mg (w_k w)) (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) hb h cSize); auto; try lia. }
  assert (Hcsz1: 1 <= cSize) by lia.
  assert (Hmg: sm_mg (sm_of (a_st a)) = lh_mg (w_k w)) by (unfold sm_mg, sm_of, lh_mg; cbn; rewrite Hpar; reflexivity).
  assert (Hxs: x = hb ++ sublist (w_ipc w) (a_ipos a + cSize) (a_ibs a)).
  { unfold x. rewrite Hhb. rewrite <- sublist_split; auto; lia. }
  assert (Hgx: get_frame_header_m (lh_mg (w_k w)) x = FH_ok h).
  { rewrite Hxs. apply G3M.gfh_m_ext; auto. }
  assert (Hy: bytes_ok (sublist (a_ipos a) (a_isz a) (a_ibs a))) by (unfold bytes_ok in *; apply Forall_sublist; auto).
  assert (Hfx: frame_compressed_size_m (lh_mg (w_k w)) x = Some (Zlength x)).
  { destruct (G3M.fcs_m_trunc _ _ _ Hy Hfcs) as [Hk Hxk].
    rewrite <- sublist_firstn, sublist_sublist in Hxk by lia. rewrite !Z.add_0_l, Z.add_comm in Hxk.
    fold x in Hxk. replace (Zlength x) with cSize; auto. unfold x. rewrite Zlength_sublist; lia. }
  (* the bytes of the frame's dictionary *)
  assert (Hdmok: forall dm, lh_fdm a k1 x dm -> LH3G2BytesR1.g2_dm_ok dm).
  { intros dm [(Hn & Hdm)|(Hn & _ & _ & _ & h' & q & dd & _ & _ & _ & _ & Hin & Hda)].
    - apply (g2_dm_of (dc_dict (a_st a))); auto. intros dr E.
      pose proof (not_ref_of _ _ Hsd dr E) as Hnr.
      destruct (dr_src dr) eqn:Es; [contradiction| |].
      + apply (HBown) with (dr := dr); auto. destruct Hdr' as [?|[? _]]; [auto|contradiction].
      + eapply Hdrb; eauto.
    - apply (proj1 LH3G2BytesR1.g2_bytes_facts (dd_bytes dd)); auto. eapply HBset; eauto. }
  set (wB := lhB_brk w k1 fs' d' lxb' (a_ipos a + cSize) r out c).
  assert (Hnew: dead (sm_of (a_st a)) (a_sin a ++ x ++ nil) \/
    exists dm, m_rel_cd (sm_of (a_st a)) (a_sin a ++ x ++ nil) ((ss_out (dc_ss (a_st a)) ++ nil) ++ c) FP_none nil
                 (Some dm) /\ cur_dict_ok (a_st a) (w_k wB) (Some dm)).
  { unfold alive_ok in Halive. rewrite <- Hhb in Halive.
    destruct Halive as [Hd|(cd & Hm & Hcd & _)].
    { left. rewrite Hxs, !app_nil_r. rewrite app_assoc. rewrite app_nil_r in Hd. apply (mf_dead_app MFh). exact Hd. }
    rewrite Hfp, Hpend in Hm. rewrite Hfp in Hcd. cbn [next_cd] in Hcd.
    assert (Hcdn: fst (st_sel (a_st a)) = sel_none -> snd (st_sel (a_st a)) = None -> cd = None).
    { intros E1 E2. destruct Hm as (dsin & fb & recs & _ & _ & Hcur & _). rewrite <- Hcur.
      cbn [sm_of sm_sel sm_cur sm_md] in *. rewrite E1, E2. unfold series_cur. apply G3N.walk_cur_none. }
    assert (Hsel: forall dm, frame_dict (lh_mg (w_k w)) (fst (st_sel (a_st a))) cd hb = Some dm ->
                  lh_fdm a k1 x dm /\ cur_dict_ok (a_st a) (w_k wB) (Some dm)).
    { intros dm Fd. eapply (LH3G2Sel.g2s_sel HP a (w_k w) hb x h tbl d1 did1 cd dm d' fs' (w_k wB)); eauto. }
    assert (G': get_frame_header_m (sm_mg (sm_of (a_st a))) hb = FH_ok h) by (rewrite Hmg; exact G).
    assert (Hfcs': frame_compressed_size_m (sm_mg (sm_of (a_st a))) (sublist (a_ipos a) (a_isz a) (a_ibs a)) =
                   Some cSize) by (rewrite Hmg; exact Hfcs).
    assert (Hos': forall dm, frame_dict (sm_mg (sm_of (a_st a))) (sm_sel (sm_of (a_st a))) cd hb = Some dm ->
              oneshot_ok (md_len (sm_md (sm_of (a_st a)))) (Some dm) x (a_osz a - w_opc w) r out /\
              LH3G2BytesR1.g2_dm_ok dm).
    { intros dm Fd. rewrite Hmg in Fd. destruct (Hsel dm Fd) as [Hf _]. split; [|exact (Hdmok dm Hf)].
      replace (md_len (sm_md (sm_of (a_st a)))) with (dmode_of (c3_par k1)) by (cbn; rewrite Hpar; reflexivity).
      apply Hosk. exact Hf. }
    destruct (G3N.brkB_model MFh (sm_of (a_st a)) (a_sin a) (a_ibs a) (a_ipos a) (w_ipc w) (a_isz a) hb h cSize
             (ss_out (dc_ss (a_st a)) ++ nil) r out c (a_osz a - w_opc w) cd Hsin Hibb Hibl
             ltac:(lia) Hgap ltac:(lia) (eq_sym Hhb) G' Ht0 Hhs Hfcs' Hm Hos' Hr Hcb Hco)
      as [Hd|(dm & Fd & Hm')]; [left; exact Hd|].
    right. exists dm. split; [exact Hm'|]. rewrite Hmg in Fd. exact (proj2 (Hsel dm Fd)). }
  subst wB. unfold ds_LI_P. cbn [fold_right].
  clear Hosk Halive.
  split; [|split; [left; reflexivity|split; [|split; [|split; [|split; [|exact I]]]]]].
  5:{ (* the shortcut wrote the frame's content only *)
      unfold untouched_ok. cbn [lw_sv0 lhB_brk w_opc w_oc]. intros Hs. rewrite Hut.
      pose proof (Hunt Hs) as Hu.
      pose proof Ha as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hloca & _).
      assert (E1: sublist (w_opc w + r) (a_osz a) (w_oc w) =
                  sublist r (a_osz a - w_opc w) (sublist (w_opc w) (a_osz a) (w_oc w))) by list_solve.
      assert (E2: sublist (w_opc w + r) (a_osz a) (a_oc a) =
                  sublist r (a_osz a - w_opc w) (sublist (w_opc w) (a_osz a) (a_oc a))) by list_solve.
      rewrite E1, E2, Hu. reflexivity. }
  4:{ unfold entry_ok. cbn [lw_sv0 lhB_brk w_smw]. intros; discriminate. }
  2:{ unfold loop_extra. cbn [lw_sv0 lhB_brk w_smw]. intros; discriminate. }
  2:{ unfold exit_ok. cbn [lw_sv0 lhB_brk w_smw w_k w_sv w_ipc w_opc c3_with_s c3_s c3_fs c3_with_fs
        lhB_s held_redict sf_with_held sf_stage_set sf_stage sf_outStart sf_outEnd sf_hostage sv0 sv_ahead sv_fp
        fs_expected fsu_expected].
      intros _. unfold zdss_init, zdss_loadHeader, zdss_read, zdss_load, zdss_flush.
      split; [lia|]. split; [intros; lia|]. split; [intros; lia|]. split; [intros; lia|].
      intros _. split; [reflexivity|]. split.
      - exists 0. split; [exact Hos|]. split; [exact Hoe|]. rep_lia.
      - left. split; [exact Hhost|]. split; [reflexivity|]. right. split; [reflexivity|lia]. }
  cbn [lw_sv0 lhB_brk w_k w_sv w_ipc w_opc w_oc w_dl w_smw]. rewrite Hdl, app_nil_l. unfold call_inv. cbv zeta.
  cbn [sv0 sv_ahead sv_fp sv_pend sv_lay sv_dd c3_with_s c3_s c3_fs c3_with_fs lhB_k c3_with_dict c3_par c3_stable
       c3_set c3_dict c3_sp k_A k_redict lhB_s held_redict sf_with_held sf_stage_set sf_stage sf_nfp].
  assert (Hlsub: Zlength (sublist 0 (w_opc w) (w_oc w)) = w_opc w) by (rewrite Zlength_sublist; lia).
  assert (Hpref: sublist 0 (w_opc w + r) (sublist 0 (w_opc w) (w_oc w) ++ out) =
                 sublist 0 (w_opc w) (w_oc w) ++ sublist 0 r out).
  { rewrite (sublist_split 0 (w_opc w) (w_opc w + r)) by (rewrite ?Zlength_app; lia).
    rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
    rewrite sublist_sublist00 by lia. f_equal; f_equal; lia. }
  split; [lia|]. split; [lia|]. split; [rewrite Zlength_app; lia|].
  split. { rewrite sublist_app1 by lia. rewrite sublist_sublist00 by lia. auto. }
  split; [lia|].
  split. { rewrite sublist_app2 by lia. rewrite <- Hco. f_equal; lia. }
  split; [auto|].
  split. { unfold base_call. cbn. split; [auto|split; [auto|split; [auto|split; [exact Hdr'|split; [auto|]]]]].
    split; [exact Hfp'|].
    destruct (rl_kA_held (w_k w) (fh_val h) d1 did1) as [EmA EhA].
    apply (rl_mem_call_with _ (w_k w)); [ exact (proj2 Hfp0) | | | | exact Hheld ].
    - exact (redict_ok_trans _ _ _ (lhA_sel_redict _ _ _ _ _ _ _ HA) (rl_lhB_redict _ _ HD)).
    - exact EmA.
    - etransitivity; [ | exact EhA ]. exact (held_redict_set _ _ _). }
  split; [auto|]. split; [cbn; auto|].
  split; [right; right; right; left; reflexivity|].
  split; [auto|].
  split.
  { unfold c_core in *. destruct Hcore as (_ & _ & Hio & _).
    cbn [c3_with_s c3_with_fs lhB_k c3_with_dict c3_s c3_fs c3_par k_A k_redict lhB_s held_redict sf_with_held sf_stage_set sf_stage sf_inSize sf_outSize
         sv0 sv_ahead sv_fp sv_pend].
    split; [left; split; reflexivity|]. split; [exact Hcold|]. split; [exact Hio|].
    unfold zdss_init. cbn. split; [left; reflexivity|reflexivity]. }
  split. { unfold sv_dd_ok. cbn. intros Hx. unfold zdss_read, zdss_init in Hx. lia. }
  split. { intros Hs. rewrite Hpref, (Hstabo Hs), Hco, app_nil_r, map_app. reflexivity. }
  split; [intros Hx; congruence|].
  split; [intros; lia|].
  split.
  { unfold alive_ok. destruct Hnew as [Hd|(dm & Hm & Hcd)]; [left; exact Hd|right]. exists (Some dm).
    replace ((ss_out (dc_ss (a_st a)) ++ nil) ++ c) with (ss_out (dc_ss (a_st a)) ++ c) in Hm
      by (rewrite app_nil_r; reflexivity).
    cbn [sv0 sv_fp sv_pend]. split; [exact Hm|]. split.
    - cbn [next_cd sv0 sv_fp]. exact Hcd.
    - unfold hist_ok. cbn. intros _ Hx. exfalso. apply Hx. reflexivity. }
  split. { intros Hx. cbn in Hx. unfold zdss_init, zdss_loadHeader in Hx. lia. }
  split; [exact Hsin'|].
  split. { intros _ Hx. exfalso. apply Hx. reflexivity. }
  intros Hx. cbn in Hx. unfold zdss_init, zdss_flush in Hx. lia.
Qed.

Lemma g2_frame : forall (P: list Prop) (L1 L2: list localdef) (S1 S2: list mpred),
  L1 = L2 -> S1 = S2 -> fold_right and True P ->
  PROPx [] (LOCALx L1 (SEPx S1)) |-- PROPx P (LOCALx L2 (SEPx S2)).
Proof.
  intros P L1 L2 S1 S2 -> -> HP. unfold PROPx. apply andp_right.
  - apply andp_left1. intro rho. simpl. apply prop_derives. intros _. exact HP.
  - apply andp_left2. apply derives_refl.
Qed.

(* G2: the break after a successful shortcut (with or without the selection) -> the loop invariant *)
Lemma lh_brkB_ok : lh_brkB_stmt.
Proof.
  intros MFh HP Hdd0 DENT TABS a w hb h tbl d1 did1 cSize r out c fs' d' lxb' Hc G Hgf HA k1 HB Hr Hcb Hcl Hco HD Hfp'
    HSF HD2 Hut. subst k1.
  set (wB := lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c).
  unfold lh_st, ds_inv. Exists (lw_sv0 wB).
  assert_PROP ((cold01 (c3_fs (w_k wB)) /\ (c3_set (w_k wB) <> nil -> c3_sp (w_k wB) <> nullval) /\
                (c3_set (w_k wB) = nil -> c3_sp (w_k wB) = nullval)) /\
     (forall od, dict_rel3_of od (c3_dict (w_k wB)) -> forall dr, od = Some dr -> dr_src dr = DSOwn ->
        bytes_ok (dr_bytes dr)) /\
     (forall dr q dd, dc_dict (a_st a) = Some dr -> dr_src dr = DSDDict q dd -> bytes_ok (dd_bytes dd)) /\
     Forall (fun e => cur_ddict (dc_dict (a_st a)) = Some (fst e) \/ bytes_ok (dd_bytes (snd e))) (dc_set (a_st a)) /\
     0 <= sf_held (c3_s (w_k wB)) - local_held (c3_dict (w_k wB)))
    as HF.
  { unfold ds_LI_S. go_lowerx.
    sep_apply (g2_ctx_facts DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    sep_apply (g2_own_bytes DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    sep_apply (g2_dictres_bytes DENT (a_gv a) Ews (dc_dict (a_st a))). Intros.
    sep_apply (g2_setres_bytes DENT (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a))). Intros.
    sep_apply (rl_ctx_held DENT TABS (a_gv a) (a_d a) (w_k wB)). Intros.
    apply prop_right. tauto. }
  destruct HF as ((Hcold & Hsp & Hsp0) & Hown & Hddb & Hsetb & Hheld).
  assert (Hsco: set_cur_ok (a_st a)).
  { destruct Hc as (_ & _ & _ & _ & _ & He & _). destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
    destruct Hb as (_ & _ & _ & _ & ? & _). auto. }
  assert (Hdrb: dc_set (a_st a) = nil -> forall dr q dd, dc_dict (a_st a) = Some dr -> dr_src dr = DSDDict q dd ->
                bytes_ok (dr_bytes dr)).
  { intros Hnil dr q dd Ed Es. rewrite (Hdd0 a w hb Hc Hnil dr q dd Ed Es). eapply Hddb; eauto. }
  apply g2_frame; [reflexivity|reflexivity|].
  eapply brkB_pure; eauto.
  - intros q dd Hin. rewrite Forall_forall in Hsetb. destruct (Hsetb _ Hin) as [Ec|Hb]; [|exact Hb].
    cbn [fst] in Ec. unfold cur_ddict in Ec. destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [|discriminate].
    destruct (dr_src dr) as [| |q' dd'] eqn:Es; try discriminate. injection Ec as <-.
    rewrite (Hsco dr q' dd' dd Ed Es Hin). eapply Hddb; eauto.
Qed.

End CM_LH3G2_3.
