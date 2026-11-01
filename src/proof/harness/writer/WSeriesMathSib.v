(* A local copy of the proof of TopMath.series_math (same statement), used by w_series' body (WB_wseries) in place
   of TopMath.series_math. *)
Require Export Zstd.proof.harness.writer.TopMath.
Local Open Scope Z_scope.

(* ---------- series_math: helpers ---------- *)

Lemma tm_le_value_le_bytes : forall k x, le_value (le_bytes k x) = x mod 256 ^ Z.of_nat k.
Proof.
  induction k as [|k IH]; intros x; simpl le_bytes; simpl le_value.
  - rewrite Z.mod_1_r. reflexivity.
  - rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    symmetry. apply Z.rem_mul_r; [lia|]. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma tm_length_le_bytes : forall k x, length (le_bytes k x) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma tm_le_bytes_ok : forall k x, bytes_ok (le_bytes k x).
Proof.
  unfold bytes_ok. induction k; intros; simpl; constructor; auto.
  unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma tm_Zlength_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

Lemma tm_skipn_app : forall (a b: list Z), skipn (Z.to_nat (Zlength a)) (a ++ b) = b.
Proof.
  intros. rewrite Zlength_correct, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma tm_firstn_app : forall (a b: list Z), firstn (Z.to_nat (Zlength a)) (a ++ b) = a.
Proof.
  intros. rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag. simpl.
  apply app_nil_r.
Qed.

Lemma tm_slice_app : forall (a b: list Z) k, slice (a ++ b) (Zlength a) k = slice b 0 k.
Proof. intros. unfold slice. rewrite tm_skipn_app. reflexivity. Qed.

Lemma tm_slice0_app : forall (a b: list Z), slice (a ++ b) 0 (Zlength a) = a.
Proof. intros. unfold slice. simpl skipn. apply tm_firstn_app. Qed.

Lemma tm_Zlength_le_bytes4 : forall x, Zlength (le_bytes 4 x) = 4.
Proof. intros. rewrite Zlength_correct, tm_length_le_bytes. reflexivity. Qed.

Lemma tm_skip_bytes : forall v d t, 0 <= v < 16 -> Zlength d <= 64 ->
  Zlength (skip_bytes v d ++ t) = 8 + Zlength d + Zlength t /\
  Zlength (skip_bytes v d) = 8 + Zlength d /\
  le_field (skip_bytes v d ++ t) 0 4 = ZSTD_MAGIC_SKIPPABLE_START + v /\
  le_field (skip_bytes v d ++ t) 4 4 = Zlength d /\
  slice (skip_bytes v d ++ t) 8 (Zlength d) = d /\
  skipn (Z.to_nat (8 + Zlength d)) (skip_bytes v d ++ t) = t /\
  is_skippable_magic (ZSTD_MAGIC_SKIPPABLE_START + v) = true /\
  (ZSTD_MAGIC_SKIPPABLE_START + v =? ZSTD_MAGICNUMBER) = false.
Proof.
  intros v d t Hv Hd. unfold skip_bytes.
  pose proof (tm_Zlength_le_bytes4 (ZSTD_MAGIC_SKIPPABLE_START + v)) as L1.
  pose proof (tm_Zlength_le_bytes4 (Zlength d)) as L2.
  assert (Hd0 : 0 <= Zlength d) by (rewrite Zlength_correct; lia).
  rewrite <- !app_assoc. unfold le_field.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - rewrite !tm_Zlength_app. lia.
  - rewrite !tm_Zlength_app. lia.
  - rewrite <- L1 at 1. rewrite tm_slice0_app, tm_le_value_le_bytes.
    apply Z.mod_small. unfold ZSTD_MAGIC_SKIPPABLE_START. change (256 ^ Z.of_nat 4) with 4294967296. lia.
  - rewrite <- L1 at 1. rewrite tm_slice_app. rewrite <- L2 at 1. rewrite tm_slice0_app, tm_le_value_le_bytes.
    apply Z.mod_small. change (256 ^ Z.of_nat 4) with 4294967296. lia.
  - replace 8 with (Zlength (le_bytes 4 (ZSTD_MAGIC_SKIPPABLE_START + v) ++ le_bytes 4 (Zlength d)))
      by (rewrite tm_Zlength_app; lia).
    rewrite app_assoc, tm_slice_app. unfold slice. simpl skipn. apply tm_firstn_app.
  - replace (8 + Zlength d) with (Zlength ((le_bytes 4 (ZSTD_MAGIC_SKIPPABLE_START + v) ++
      le_bytes 4 (Zlength d)) ++ d)) by (rewrite !tm_Zlength_app; lia).
    rewrite !app_assoc, tm_skipn_app. reflexivity.
  - assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/
            v = 10 \/ v = 11 \/ v = 12 \/ v = 13 \/ v = 14 \/ v = 15) as HH by lia.
    repeat (destruct HH as [HH | HH]; [subst v; vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
  - apply Z.eqb_neq. unfold ZSTD_MAGIC_SKIPPABLE_START, ZSTD_MAGICNUMBER. lia.
Qed.

Lemma tm_Zlength_nonneg : forall (l: list Z), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

(* what ZSTD's inspection functions give on a skippable frame followed by anything *)
Lemma tm_skip_info : forall v d t s, s = skip_bytes v d ++ t -> 0 <= v < 16 -> Zlength d <= 64 ->
  is_frame s = 1 /\ is_skippable_frame s = 1 /\ skippable_frame_size s = Some (8 + Zlength d) /\
  frame_compressed_size s = Some (8 + Zlength d) /\
  get_frame_header s = FH_ok {| fh_contentSize := Zlength d; fh_windowSize := 0; fh_blockSizeMax := 0;
                                fh_frameType := 1; fh_headerSize := ZSTD_SKIPPABLEHEADERSIZE; fh_dictID := v;
                                fh_checksumFlag := 0 |} /\
  frame_size_info s = Some (8 + Zlength d, 0) /\
  (forall cap, read_skippable s cap = if cap >=? Zlength d then Some (d, v) else None).
Proof.
  intros v d t s Hs Hv Hd.
  destruct (tm_skip_bytes v d t Hv Hd) as (L & L0 & M & N & D & K & SM & NM). rewrite <- Hs in *.
  pose proof (tm_Zlength_nonneg d). pose proof (tm_Zlength_nonneg t).
  assert (E8 : (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) = false)
    by (apply Z.ltb_ge; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  assert (E8' : (Zlength s >=? ZSTD_SKIPPABLEHEADERSIZE) = true)
    by (rewrite Z.geb_leb; apply Z.leb_le; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  assert (E4 : (Zlength s <? 4) = false) by (apply Z.ltb_ge; lia).
  assert (E5 : (Zlength s <? 5) = false) by (apply Z.ltb_ge; lia).
  assert (Hsfs : skippable_frame_size s = Some (8 + Zlength d)).
  { unfold skippable_frame_size. rewrite E8, N.
    assert (A2 : (Zlength d + ZSTD_SKIPPABLEHEADERSIZE >? Zlength s) = false)
      by (rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
    rewrite A2. f_equal. unfold ZSTD_SKIPPABLEHEADERSIZE. lia. }
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - unfold is_frame. rewrite E4, M, NM, SM. reflexivity.
  - unfold is_skippable_frame. rewrite E4, M, SM. reflexivity.
  - exact Hsfs.
  - unfold frame_compressed_size. rewrite E8', M, SM. exact Hsfs.
  - unfold get_frame_header. cbv zeta. rewrite E5, M, NM, SM. cbn [negb]. cbv iota beta.
    rewrite E8, N. do 2 f_equal. lia.
  - unfold frame_size_info. rewrite E8', M, SM, Hsfs. reflexivity.
  - intros cap. unfold read_skippable. rewrite E8, M, SM, Hsfs. cbv zeta iota beta. cbn [negb]. cbv iota.
    replace (8 + Zlength d - ZSTD_SKIPPABLEHEADERSIZE) with (Zlength d) by (unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
    change ZSTD_SKIPPABLEHEADERSIZE with 8. rewrite D. replace (ZSTD_MAGIC_SKIPPABLE_START + v - ZSTD_MAGIC_SKIPPABLE_START) with v by lia.
    rewrite Z.gtb_ltb, Z.geb_leb.
    destruct (Z.ltb_spec cap (Zlength d)), (Z.leb_spec (Zlength d) cap); try reflexivity; lia.
Qed.

(* the facts of one written frame, at its place in the series *)
Lemma tm_ff_frame : forall dm ws f fb c t,
  frame_written dm f fb c -> wi_size f = Zlength fb ->
  skipn (Z.to_nat (wi_start f)) (ws_bytes ws) = fb ++ t -> wi_bytes ws f = fb -> wi_content ws f = c ->
  frame_facts dm ws f.
Proof.
  intros dm ws f fb c t Hfw Hsz Hs Hwb Hwc. unfold frame_facts. cbv zeta. rewrite Hs, Hwb.
  unfold frame_written in Hfw. destruct (wi_skippable f) eqn:Esk.
  - destruct Hfw as (data & -> & Hok & Hd & Hv & Hn & Hh & ->).
    destruct (tm_skip_bytes (wi_variant f) data t Hv Hd) as (L & L0 & M & N & D & K & SM & NM).
    destruct (tm_skip_bytes (wi_variant f) data nil Hv Hd) as (_ & _ & M0 & _ & D0 & _ & _ & _).
    rewrite app_nil_r in M0, D0.
    destruct (tm_skip_info (wi_variant f) data t _ eq_refl Hv Hd) as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    assert (Eb : wi_big f = false) by (unfold wi_big; rewrite Esk; reflexivity).
    rewrite Eb. pose proof (tm_Zlength_nonneg data) as Hd0.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + exact I1.
    + exact I2.
    + rewrite I4, Hsz, L0. reflexivity.
    + rewrite I5. unfold wi_header. rewrite Esk, Hn. reflexivity.
    + unfold frame_content_size. rewrite I5. reflexivity.
    + unfold dict_id_from_frame. rewrite I5. reflexivity.
    + intros H; discriminate.
    + intros _. split; [|split; [|split; [|split]]].
      * rewrite Hsz, L0, Hn. unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
      * rewrite L0. unfold ZSTD_SKIPPABLEHEADERSIZE. lia.
      * rewrite M0. exact SM.
      * intros t'. destruct (tm_skip_info (wi_variant f) data t' _ eq_refl Hv Hd) as (_ & _ & J & _).
        rewrite J, Hsz, L0. reflexivity.
      * intros cap. rewrite I7, Hn. unfold ZSTD_SKIPPABLEHEADERSIZE. rewrite D0. reflexivity.
    + intros H; discriminate.
  - destruct Hfw as (Hb & Hc & _ & Hfcs & Hhs & Hall).
    destruct (Hall t) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & _).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + exact I1.
    + exact I2.
    + rewrite Hsz. exact I3.
    + exact I4.
    + exact I5.
    + exact I6.
    + intros _. exact I7.
    + intros H; discriminate.
    + intros _. split; [|split].
      * intros wl t'. rewrite Hwc, Hsz. destruct (Hall t') as (_ & _ & _ & _ & _ & _ & _ & _ & J & _). apply J.
      * intros wl t'. destruct (Hall t') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J & _). apply J.
      * intros Hck wl t' x Hx Hr. rewrite Hsz.
        destruct (Hall t') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J). apply J; auto.
Qed.

(* the frames written, from the front: frame by frame from byte offset off and content offset coff *)
Inductive tm_wr (dm: dict_model) : list winfo -> Z -> Z -> list Z -> list Z -> Prop :=
| tm_wr_nil : forall off coff, tm_wr dm nil off coff nil nil
| tm_wr_cons : forall f fs fb c bs cs off coff,
    wi_start f = off -> wi_cstart f = coff -> wi_size f = Zlength fb -> wi_csize f = Zlength c ->
    frame_written dm f fb c -> winfo_wf f -> winfo_zeros f ->
    tm_wr dm fs (off + Zlength fb) (coff + Zlength c) bs cs ->
    tm_wr dm (f :: fs) off coff (fb ++ bs) (c ++ cs).

Lemma tm_wr_snoc : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs -> forall f fb c,
  wi_start f = off + Zlength bs -> wi_cstart f = coff + Zlength cs ->
  wi_size f = Zlength fb -> wi_csize f = Zlength c ->
  frame_written dm f fb c -> winfo_wf f -> winfo_zeros f ->
  tm_wr dm (fs ++ [f]) off coff (bs ++ fb) (cs ++ c).
Proof.
  intros dm fs off coff bs cs H. induction H as [off coff | f0 fs fb0 c0 bs cs off coff H1 H2 H3 H4 H5 H6 H7 Hr IH];
    intros f fb c Hst Hcst Hsz Hcsz Hfw Hwf Hz.
  - simpl. pose proof (tm_wr_cons dm f nil fb c nil nil off coff) as Hc.
    rewrite !app_nil_r in Hc. apply Hc; auto.
    + change (Zlength (@nil Z)) with 0 in Hst. lia.
    + change (Zlength (@nil Z)) with 0 in Hcst. lia.
    + constructor.
  - simpl. rewrite <- !app_assoc. apply tm_wr_cons; auto.
    apply IH; auto; rewrite tm_Zlength_app in *; lia.
Qed.

Lemma tm_written : forall dm fs bs cs, written dm fs bs cs -> tm_wr dm fs 0 0 bs cs.
Proof.
  intros dm fs bs cs H. induction H.
  - constructor.
  - apply tm_wr_snoc; auto; lia.
Qed.

Lemma tm_frame_size : forall dm f fb c, frame_written dm f fb c -> winfo_wf f -> 3 <= Zlength fb.
Proof.
  intros dm f fb c Hfw Hwf. unfold frame_written in Hfw. destruct (wi_skippable f).
  - destruct Hfw as (data & -> & _ & Hd & Hv & _).
    destruct (tm_skip_bytes (wi_variant f) data nil Hv Hd) as (_ & L0 & _).
    pose proof (tm_Zlength_nonneg data). lia.
  - destruct Hfw as (_ & _ & _ & _ & Hhs & _). unfold winfo_wf, u64, u32 in Hwf.
    destruct (wi_checksum f); lia.
Qed.

Lemma tm_local : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs ->
  bytes_ok bs /\ bytes_ok cs /\
  Forall (fun f => wi_skippable f = false -> wi_fcs_present f = true -> wi_fcs f = wi_csize f) fs /\
  Forall winfo_wf fs /\ Forall winfo_zeros fs /\ Forall winfo_layout fs.
Proof.
  intros dm fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH].
  - unfold bytes_ok. split; [constructor|split; [constructor|split; [constructor|split; [constructor|split; constructor]]]].
  - destruct IH as (B & C & F1 & F2 & F3 & F4). unfold bytes_ok in *.
    assert (Hfb : Forall is_byte fb /\ Forall is_byte c /\ (wi_skippable f = false -> wi_fcs f = Zlength c) /\
                  winfo_layout f).
    { unfold frame_written in Hfw. unfold winfo_layout. destruct (wi_skippable f) eqn:Esk.
      - destruct Hfw as (data & -> & Hok & Hd & Hv & Hn & Hh & ->).
        split; [|split; [constructor|split; intros; discriminate]].
        unfold skip_bytes. apply Forall_app. split; [apply tm_le_bytes_ok|].
        apply Forall_app. split; [apply tm_le_bytes_ok|exact Hok].
      - destruct Hfw as (Hb & Hc & _ & Hfcs & Hhs & _).
        split; [exact Hb|split; [exact Hc|split]].
        + intros _. exact Hfcs.
        + intros _ Hck. rewrite Hck in Hhs. lia. }
    destruct Hfb as (Fb & Fc & Hfcs & Hl).
    split; [apply Forall_app; auto|]. split; [apply Forall_app; auto|].
    split; [constructor; auto; intros Hs _; rewrite Hcsz; auto|].
    split; [constructor; auto|]. split; constructor; auto.
Qed.

Lemma tm_tiles : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs ->
  tiles fs off coff (off + Zlength bs) (coff + Zlength cs).
Proof.
  intros dm fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH].
  - simpl. change (Zlength (@nil Z)) with 0. split; lia.
  - cbn [tiles]. pose proof (tm_frame_size _ _ _ _ Hfw Hwf). pose proof (tm_Zlength_nonneg c).
    rewrite Hsz, Hcsz, !tm_Zlength_app, !Z.add_assoc.
    split; [exact Hst|]. split; [exact Hcst|]. split; [lia|]. split; [lia|]. split; [|exact IH].
    intros Hs. unfold frame_written in Hfw. rewrite Hs in Hfw.
    destruct Hfw as (data & _ & _ & _ & _ & _ & _ & ->). reflexivity.
Qed.

Lemma tm_ff_all : forall dm ws fs off coff bs cs, tm_wr dm fs off coff bs cs -> 0 <= off -> 0 <= coff ->
  skipn (Z.to_nat off) (ws_bytes ws) = bs -> skipn (Z.to_nat coff) (ws_content ws) = cs ->
  Forall (frame_facts dm ws) fs.
Proof.
  intros dm ws fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH];
    intros Ho Hco Hs Hcs.
  - constructor.
  - pose proof (tm_Zlength_nonneg fb). pose proof (tm_Zlength_nonneg c). constructor.
    + apply (tm_ff_frame dm ws f fb c bs); auto.
      * rewrite Hst. exact Hs.
      * unfold wi_bytes, slice. rewrite Hst, Hs, Hsz. apply tm_firstn_app.
      * unfold wi_content, slice. rewrite Hcst, Hcs, Hcsz. apply tm_firstn_app.
    + apply IH; try lia.
      * rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, Hs by lia. apply tm_skipn_app.
      * rewrite Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn, Hcs by lia. apply tm_skipn_app.
Qed.

Lemma tm_fds : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs ->
  forall fuel acc, (length bs < fuel)%nat -> 0 <= acc -> acc + Zlength cs <= 2 ^ 18 ->
  fds_loop fuel bs acc = expected_fds fs acc.
Proof.
  intros dm fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH];
    intros fuel acc Hf Ha Hc.
  - destruct fuel as [|fuel]; [simpl in Hf; lia|]. reflexivity.
  - destruct fuel as [|fuel]; [lia|].
    pose proof (tm_frame_size _ _ _ _ Hfw Hwf) as H3. rewrite Zlength_correct in H3.
    rewrite length_app in Hf. pose proof (tm_Zlength_nonneg c). pose proof (tm_Zlength_nonneg cs).
    cbn [fds_loop expected_fds]. unfold frame_written in Hfw. destruct (wi_skippable f) eqn:Esk.
    + destruct Hfw as (data & -> & Hok & Hd & Hv & Hn & Hh & ->).
      destruct (tm_skip_bytes (wi_variant f) data bs Hv Hd) as (L & L0 & M & N & D & K & SM & NM).
      destruct (tm_skip_info (wi_variant f) data bs _ eq_refl Hv Hd) as (_ & _ & I3 & _).
      pose proof (tm_Zlength_nonneg data). pose proof (tm_Zlength_nonneg bs).
      assert (E5 : (Zlength (skip_bytes (wi_variant f) data ++ bs) <? ZSTD_FRAMEHEADERSIZE_PREFIX) = false)
        by (apply Z.ltb_ge; unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
      rewrite E5, M, SM, I3. cbv iota beta. rewrite K.
      cbn [app] in Hc. apply IH; lia.
    + destruct Hfw as (Hb & Hcok & _ & Hfcs & Hhs & Hall).
      destruct (Hall bs) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & _).
      assert (E5 : (Zlength (fb ++ bs) <? ZSTD_FRAMEHEADERSIZE_PREFIX) = false).
      { unfold Info.frame_header_size in I7. destruct (_ <? _); [discriminate|reflexivity]. }
      assert (Hns : is_skippable_magic (le_field (fb ++ bs) 0 4) = false).
      { unfold is_skippable_frame in I2. destruct (Zlength (fb ++ bs) <? 4) eqn:E4.
        - apply Z.ltb_lt in E4. apply Z.ltb_ge in E5. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in E5. lia.
        - destruct (is_skippable_magic _); [discriminate|reflexivity]. }
      rewrite E5, Hns. cbv iota beta zeta. rewrite I5. rewrite tm_Zlength_app in Hc.
      destruct (wi_big f) eqn:Eb; [reflexivity|].
      destruct (wi_fcs_present f) eqn:Ep; [|reflexivity]. cbn [negb]. cbv iota.
      rewrite Hfcs.
      assert (E1 : (Zlength c >=? ZSTD_CONTENTSIZE_ERROR) = false)
        by (rewrite Z.geb_leb; apply Z.leb_gt; unfold ZSTD_CONTENTSIZE_ERROR; lia).
      assert (E2 : (acc + Zlength c >=? 2 ^ 64) = false) by (rewrite Z.geb_leb; apply Z.leb_gt; lia).
      rewrite E1, E2, I3. cbv iota beta. rewrite tm_skipn_app. apply IH; lia.
Qed.

Lemma tm_bound : forall dm fs off coff bs cs, tm_wr dm fs off coff bs cs ->
  forall fuel acc, (length bs < fuel)%nat -> 0 <= acc -> acc + Z.of_nat (length fs) * 2 ^ 50 <= 2 ^ 60 ->
  Zlength cs <= 2 ^ 18 ->
  bound_loop fuel bs acc = expected_bound fs acc.
Proof.
  intros dm fs off coff bs cs H.
  induction H as [off coff | f fs fb c bs cs off coff Hst Hcst Hsz Hcsz Hfw Hwf Hz Hr IH];
    intros fuel acc Hf Ha Hacc Hc.
  - destruct fuel as [|fuel]; [simpl in Hf; lia|]. reflexivity.
  - destruct fuel as [|fuel]; [lia|].
    pose proof (tm_frame_size _ _ _ _ Hfw Hwf) as H3.
    rewrite length_app in Hf. pose proof (tm_Zlength_nonneg c). pose proof (tm_Zlength_nonneg cs).
    cbn [length] in Hacc.
    assert (E0 : (Zlength (fb ++ bs) =? 0) = false).
    { apply Z.eqb_neq. rewrite tm_Zlength_app. pose proof (tm_Zlength_nonneg bs). lia. }
    rewrite Zlength_correct in H3.
    cbn [bound_loop expected_bound]. rewrite E0.
    unfold frame_written in Hfw. destruct (wi_skippable f) eqn:Esk.
    + destruct Hfw as (data & -> & Hok & Hd & Hv & Hn & Hh & ->).
      destruct (tm_skip_bytes (wi_variant f) data bs Hv Hd) as (L & L0 & M & N & D & K & SM & NM).
      destruct (tm_skip_info (wi_variant f) data bs _ eq_refl Hv Hd) as (_ & _ & _ & _ & _ & I6 & _).
      rewrite I6. cbv iota beta.
      assert (Ez : (0 =? ZSTD_CONTENTSIZE_ERROR) = false) by reflexivity.
      rewrite Ez, Z.add_0_r, Z.mod_small by lia. rewrite K.
      cbn [app] in Hc. apply IH; lia.
    + destruct Hfw as (Hb & Hcok & _ & Hfcs & Hhs & Hall).
      destruct (Hall bs) as (_ & _ & _ & _ & _ & _ & _ & I8 & _).
      rewrite I8. rewrite tm_Zlength_app in Hc.
      destruct (wi_big f) eqn:Eb; [reflexivity|]. cbv iota beta.
      assert (Hzb : 0 <= zframe_bound f < 2 ^ 50).
      { unfold zframe_bound. destruct (wi_fcs_present f).
        - rewrite Hfcs. lia.
        - unfold winfo_wf, u32, u64 in Hwf.
          assert (0 <= Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX <= 131072)
            by (unfold ZSTD_BLOCKSIZE_MAX; lia).
          assert (wi_blocks f * Z.min (wi_window f) ZSTD_BLOCKSIZE_MAX <= wi_blocks f * 131072)
            by (apply Z.mul_le_mono_nonneg_l; lia).
          split; [apply Z.mul_nonneg_nonneg; lia|]. lia. }
      assert (E1 : (zframe_bound f =? ZSTD_CONTENTSIZE_ERROR) = false)
        by (apply Z.eqb_neq; unfold ZSTD_CONTENTSIZE_ERROR; lia).
      rewrite E1, Z.mod_small by lia. rewrite tm_skipn_app.
      apply (IH fuel (acc + zframe_bound f)); lia.
Qed.

Theorem series_math_sib : forall dm fs bs cs,
  written dm fs bs cs -> (1 <= length fs <= 4)%nat ->
  Zlength bs <= 2 ^ 19 -> Zlength cs <= 2 ^ 18 ->
  series_facts dm {| ws_bytes := bs; ws_content := cs; ws_frames := fs |} /\
  wseries_wf {| ws_bytes := bs; ws_content := cs; ws_frames := fs |}.
Proof.
  intros dm fs bs cs Hw Hlen Hb Hc. apply tm_written in Hw.
  destruct (tm_local _ _ _ _ _ _ Hw) as (B & C & F1 & F2 & F3 & F4).
  pose proof (tm_Zlength_nonneg cs).
  split; [|split; [exact F2|split; [exact F3|exact F4]]].
  unfold series_facts. cbn [ws_bytes ws_content ws_frames].
  split; [exact B|]. split; [exact C|]. split; [exact Hb|]. split; [exact Hc|]. split; [exact Hlen|].
  split; [pose proof (tm_tiles _ _ _ _ _ _ Hw) as Ht; rewrite !Z.add_0_l in Ht; exact Ht|].
  split; [apply (tm_ff_all dm _ fs 0 0 bs cs Hw); reflexivity|].
  split; [exact F1|]. split.
  - unfold find_decompressed_size. apply (tm_fds _ _ _ _ _ _ Hw); lia.
  - unfold decompress_bound. apply (tm_bound _ _ _ _ _ _ Hw); lia.
Qed.
