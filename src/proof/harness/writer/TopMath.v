(* The plain-Coq facts behind the bodies of w_series and w_dict (harness/writer.h).
   The VST proofs (WB_wseries_<u>.v, WB_wdict_<u>.v) reduce each body to these lemmas.

   - w_series: the frames written so far (`written`, built frame by frame as the loop runs), each one a
     Zstandard frame from w_frame (zframe_ok) or a skippable frame (skip_bytes); `series_math` turns a
     complete series into series_facts and wseries_wf.
   - w_dict: the bytes of a raw-content dictionary (`dict_raw_math`) or of a formatted one (`fmt_dict_bytes`,
     `dict_fmt_math`): dict_facts, wdict_wf, and the state (wst) its wstate_t holds (WDS_impl). *)
Require Export Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits Zstd.proof.harness.writer.model.WM_NCount.
Local Open Scope Z_scope.

(* ---------- series ---------- *)

(* a skippable frame as w_series writes it: magic 0x184D2A50 + variant, the user data size, the data *)
Definition skip_bytes (variant: Z) (data: list Z) : list Z :=
  le_bytes 4 (ZSTD_MAGIC_SKIPPABLE_START + variant) ++ le_bytes 4 (Zlength data) ++ data.

(* the frame record f, its bytes fb and content c, as w_series leaves them *)
Definition frame_written (dm: dict_model) (f: winfo) (fb c: list Z) : Prop :=
  if wi_skippable f then
    exists data, fb = skip_bytes (wi_variant f) data /\ bytes_ok data /\ Zlength data <= 64 /\
      0 <= wi_variant f < 16 /\ wi_skip_n f = Zlength data /\ wi_hsize f = 8 /\ c = nil
  else zframe_ok dm f fb c.

(* the frames fs written so far, their bytes bs and content cs (in the order of the loop) *)
Inductive written (dm: dict_model) : list winfo -> list Z -> list Z -> Prop :=
| written_nil : written dm nil nil nil
| written_snoc : forall fs bs cs f fb c,
    written dm fs bs cs ->
    wi_start f = Zlength bs -> wi_cstart f = Zlength cs ->
    wi_size f = Zlength fb -> wi_csize f = Zlength c ->
    frame_written dm f fb c -> winfo_wf f -> winfo_zeros f ->
    written dm (fs ++ [f]) (bs ++ fb) (cs ++ c).

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

Theorem series_math : forall dm fs bs cs,
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

(* ---------- dictionaries ---------- *)

(* a dictionary of at least 8 bytes whose first four bytes are not the magic number is raw content *)
Lemma dict_raw_not_magic : forall b,
  bytes_ok b -> 8 <= Zlength b ->
  ~ (byte_at b 0 = 55 /\ byte_at b 1 = 164 /\ byte_at b 2 = 48 /\ byte_at b 3 = 236) ->
  (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY) = false.
Proof.
  intros b Hb Hl Hn.
  destruct b as [|b0 [|b1 [|b2 [|b3 rest]]]];
    try (rewrite Zlength_correct in Hl; cbn in Hl; lia).
  unfold bytes_ok in Hb. rewrite !Forall_cons_iff in Hb. destruct Hb as (H0 & H1 & H2 & H3 & _).
  unfold is_byte in *. cbn in Hn.
  apply Z.eqb_neq. unfold le_field, slice, ZSTD_MAGIC_DICTIONARY. cbn.
  intro E. apply Hn.
  change (le_value (firstn (Pos.to_nat 4) (b0 :: b1 :: b2 :: b3 :: rest)))
    with (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * le_value nil)))) in E.
  cbn [le_value] in E. simpl. lia.
Qed.

(* a raw-content dictionary: k bytes (8 <= k <= 4096), not starting with the dictionary magic number (the
   gp_assume of w_dict, byte by byte); its state is wst_init *)
Theorem dict_raw_math : forall b,
  bytes_ok b -> 8 <= Zlength b <= 4096 ->
  ~ (byte_at b 0 = 55 /\ byte_at b 1 = 164 /\ byte_at b 2 = 48 /\ byte_at b 3 = 236) ->
  let wd := {| wd_bytes := b; wd_formatted := false; wd_id := 0; wd_content := b |} in
  dict_facts wd /\ wdict_wf wd /\ wt_ok wst_init /\ wt_dstate wst_init = dm_state (wd_model wd).
Proof.
  intros b Hb Hl Hn wd.
  pose proof (dict_raw_not_magic b Hb ltac:(lia) Hn) as Hm.
  assert (Ha : dict_auto b = Some (dict_raw b)).
  { unfold dict_auto. replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Hm. reflexivity. }
  assert (Hi : dict_id_of b = 0).
  { unfold dict_id_of. replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Hm. reflexivity. }
  assert (Hw : wd_model wd = dict_raw b) by (unfold wd_model; cbn; rewrite Ha; reflexivity).
  split; [|split; [|split]].
  - unfold dict_facts; cbn [wd_bytes wd_formatted wd_id wd_content wd]. rewrite Hw.
    repeat split; auto; try lia; rewrite ?Ha; try discriminate.
  - unfold wdict_wf; cbn [wd_bytes wd_id wd_content wd]. repeat split; try lia.
    replace (Zlength b - Zlength b) with 0 by lia. reflexivity.
  - unfold wt_ok, wst_init; cbn. repeat split; try lia; discriminate.
  - rewrite Hw. reflexivity.
Qed.

(* a formatted dictionary as w_dict writes it: magic, Dictionary_ID, the Huffman tree description hd, the FSE
   table descriptions of offsets, match lengths, literals lengths (in this order), the three repeat offsets,
   the content *)
Definition fmt_dict_bytes (id: Z) (hd: list Z) (logO: Z) (normO: list Z) (logM: Z) (normM: list Z)
    (logL: Z) (normL: list Z) (r1 r2 r3: Z) (content: list Z) : list Z :=
  le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++
  fse_desc_bytes normO logO ++ fse_desc_bytes normM logM ++ fse_desc_bytes normL logL ++
  le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content.

Definition dist_wfse (log: Z) (norm: list Z) : wfse := {| wf_log := log; wf_nsym := Zlength norm; wf_norm := norm |}.

(* its state: tables in wstate_t order (literals lengths, offsets, match lengths) *)
Definition fmt_dict_wst (H: whuf) (logO: Z) (normO: list Z) (logM: Z) (normM: list Z)
    (logL: Z) (normL: list Z) (r1 r2 r3: Z) : wst :=
  {| wt_rep := (r1, r2, r3); wt_huf := Some H;
     wt_tabs := Some (dist_wfse logL normL, dist_wfse logO normO, dist_wfse logM normM) |}.

(* helpers of dict_fmt_math *)
Lemma dfm_skipn : forall (a b: list Z) n, n = Zlength a -> skipn (Z.to_nat n) (a ++ b) = b.
Proof. intros a b n ->. rewrite Zlength_correct, Nat2Z.id. induction a; simpl; auto. Qed.

Lemma dfm_zlen_app : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, app_length. lia. Qed.

Lemma dfm_len4 : forall v, Zlength (le_bytes 4 v) = 4.
Proof. intros. rewrite Zlength_correct, wmb_length_le_bytes. reflexivity. Qed.

Lemma dfm_field_at : forall (pre rest: list Z) v n, n = Zlength pre -> 0 <= v < 2 ^ 32 ->
  le_field (pre ++ le_bytes 4 v ++ rest) n 4 = v.
Proof.
  intros pre rest v n Hn Hv. unfold le_field, slice. rewrite dfm_skipn by auto.
  change (Z.to_nat 4) with (length (le_bytes 4 v)).
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite wmb_le_value_le_bytes. apply Z.mod_small. simpl. lia.
Qed.

Lemma dfm_gtb_false : forall a b, a <= b -> (a >? b) = false.
Proof. intros. rewrite Z.gtb_ltb. apply Z.ltb_ge. lia. Qed.

Theorem dict_fmt_math : forall id H hd logO normO logM normM logL normL r1 r2 r3 content,
  1 <= id < 2 ^ 32 -> huf_ok H -> huf_desc_ok H hd ->
  ndist_ok logO normO -> logO <= 8 -> Zlength normO <= 32 ->
  ndist_ok logM normM -> logM <= 9 -> Zlength normM <= 53 ->
  ndist_ok logL normL -> logL <= 9 -> Zlength normL <= 36 ->
  bytes_ok content -> 1 <= Zlength content <= 4096 ->
  1 <= r1 <= Zlength content -> 1 <= r2 <= Zlength content -> 1 <= r3 <= Zlength content ->
  let wd := {| wd_bytes := fmt_dict_bytes id hd logO normO logM normM logL normL r1 r2 r3 content;
               wd_formatted := true; wd_id := id; wd_content := content |} in
  let S := fmt_dict_wst H logO normO logM normM logL normL r1 r2 r3 in
  dict_facts wd /\ wdict_wf wd /\ wt_ok S /\ wt_dstate S = dm_state (wd_model wd).
Proof.
  intros id H hd logO normO logM normM logL normL r1 r2 r3 content Hid HH Hhd HO HO8 HOn HM HM9 HMn
    HL HL9 HLn Hc Hcn Hr1 Hr2 Hr3 wd S.
  destruct Hhd as (Hhdb & Hhdn & Hhdp).
  destruct (fse_desc_bytes_ok normO logO HO) as [HdOb HdOn].
  destruct (fse_desc_bytes_ok normM logM HM) as [HdMb HdMn].
  destruct (fse_desc_bytes_ok normL logL HL) as [HdLb HdLn].
  pose proof (fun rest => fse_desc_read normO logO MaxOff rest HO ltac:(unfold MaxOff; lia)
                ltac:(unfold MaxOff; lia)) as RO.
  pose proof (fun rest => fse_desc_read normM logM MaxML rest HM ltac:(unfold MaxML; lia)
                ltac:(unfold MaxML; lia)) as RM.
  pose proof (fun rest => fse_desc_read normL logL MaxLL rest HL ltac:(unfold MaxLL; lia)
                ltac:(unfold MaxLL; lia)) as RL.
  assert (HlO: 5 <= logO) by apply HO. assert (HlM: 5 <= logM) by apply HM. assert (HlL: 5 <= logL) by apply HL.
  set (dO := fse_desc_bytes normO logO) in *.
  set (dM := fse_desc_bytes normM logM) in *.
  set (dL := fse_desc_bytes normL logL) in *.
  set (b := fmt_dict_bytes id hd logO normO logM normM logL normL r1 r2 r3 content) in *.
  set (st := {| st_huf := Some (huf_model H);
                st_seq := Some (fse_build normL logL, fse_build normO logO, fse_build normM logM);
                st_rep := (r1, r2, r3) |}).
  assert (Hlb: Zlength b = 8 + Zlength hd + Zlength dO + Zlength dM + Zlength dL + 12 + Zlength content).
  { unfold b, fmt_dict_bytes. fold dO dM dL. rewrite !dfm_zlen_app, !dfm_len4. lia. }
  assert (Hauto: dict_auto b = Some {| dm_content := content; dm_id := id; dm_state := st |}).
  { unfold dict_auto.
    replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (le_field b 0 4) with ZSTD_MAGIC_DICTIONARY
      by (symmetry; apply (dfm_field_at nil); [reflexivity | unfold ZSTD_MAGIC_DICTIONARY; lia]).
    rewrite Z.eqb_refl. cbn [negb].
    replace (le_field b 4 4) with id
      by (symmetry; apply (dfm_field_at (le_bytes 4 ZSTD_MAGIC_DICTIONARY)); [rewrite dfm_len4; reflexivity | lia]).
    unfold load_dentropy.
    replace (Zlength b <=? 8) with false by (symmetry; apply Z.leb_gt; lia).
    replace (skipn 8 b) with (hd ++ (dO ++ dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)).
    2: { symmetry. change 8%nat with (Z.to_nat 8).
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id) ++
                          hd ++ dO ++ dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_skipn. rewrite !dfm_zlen_app, !dfm_len4. reflexivity. }
    rewrite Hhdp. cbv beta iota zeta.
    replace (skipn (Z.to_nat (8 + Zlength hd)) b)
      with (dO ++ dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content).
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd) ++
                          dO ++ dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_skipn. rewrite !dfm_zlen_app, !dfm_len4. lia. }
    rewrite RO. cbv beta iota zeta.
    rewrite dfm_gtb_false by (unfold OffFSELog; lia).
    replace (skipn (Z.to_nat (8 + Zlength hd + Zlength dO)) b)
      with (dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content).
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO) ++
                          dM ++ dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_skipn. rewrite !dfm_zlen_app, !dfm_len4. lia. }
    rewrite RM. cbv beta iota zeta.
    rewrite dfm_gtb_false by (unfold MLFSELog; lia).
    replace (skipn (Z.to_nat (8 + Zlength hd + Zlength dO + Zlength dM)) b)
      with (dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content).
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM) ++
                          dL ++ le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_skipn. rewrite !dfm_zlen_app, !dfm_len4. lia. }
    rewrite RL. cbv beta iota zeta.
    rewrite dfm_gtb_false by (unfold LLFSELog; lia).
    rewrite dfm_gtb_false by lia.
    set (p := 8 + Zlength hd + Zlength dO + Zlength dM + Zlength dL).
    replace (le_field b p 4) with r1.
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM ++ dL) ++
                          le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_field_at; [unfold p; rewrite !dfm_zlen_app, !dfm_len4; lia | lia]. }
    replace (le_field b (p + 4) 4) with r2.
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM ++ dL ++
                          le_bytes 4 r1) ++ le_bytes 4 r2 ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_field_at; [unfold p; rewrite !dfm_zlen_app, !dfm_len4; lia | lia]. }
    replace (le_field b (p + 8) 4) with r3.
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM ++ dL ++
                          le_bytes 4 r1 ++ le_bytes 4 r2) ++ le_bytes 4 r3 ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_field_at; [unfold p; rewrite !dfm_zlen_app, !dfm_len4; lia | lia]. }
    replace (existsb _ _) with false.
    2: { cbn [existsb]. rewrite !dfm_gtb_false by lia.
         replace (r1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
         replace (r2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
         replace (r3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
         reflexivity. }
    replace (skipn (Z.to_nat (p + 12)) b) with content.
    2: { symmetry.
         replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM ++ dL ++
                          le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3) ++ content)
           by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
         apply dfm_skipn. unfold p; rewrite !dfm_zlen_app, !dfm_len4; lia. }
    reflexivity. }
  assert (Hmag: le_field b 0 4 = ZSTD_MAGIC_DICTIONARY)
    by (apply (dfm_field_at nil); [reflexivity | unfold ZSTD_MAGIC_DICTIONARY; lia]).
  assert (Hidf: le_field b 4 4 = id)
    by (apply (dfm_field_at (le_bytes 4 ZSTD_MAGIC_DICTIONARY)); [rewrite dfm_len4; reflexivity | lia]).
  assert (Hwf: forall log norm, 5 <= log -> wf_table (dist_wfse log norm) = fse_build norm log).
  { intros log norm Hl. unfold wf_table, dist_wfse. cbn [wf_log wf_norm wf_nsym].
    replace (log =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (Hwok: forall log norm, ndist_ok log norm -> wf_ok (dist_wfse log norm)).
  { intros log norm (Hl & Hn & Hf & Hs & _). unfold wf_ok, dist_wfse. cbn [wf_log wf_norm wf_nsym].
    replace (log =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; [repeat split; auto; lia | reflexivity]. }
  assert (Hmodel: wd_model wd = {| dm_content := content; dm_id := id; dm_state := st |}).
  { unfold wd_model, wd. cbn [wd_bytes]. rewrite Hauto. reflexivity. }
  split; [| split; [| split]].
  - unfold dict_facts. rewrite Hmodel. unfold wd. cbn [wd_bytes wd_formatted wd_id wd_content dm_content dm_id].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + unfold b, fmt_dict_bytes. fold dO dM dL.
      repeat (apply Forall_app; split); auto; apply wmb_le_bytes_ok.
    + lia.
    + rewrite Hauto. discriminate.
    + reflexivity.
    + reflexivity.
    + unfold dict_id_of. replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite Hmag, Z.eqb_refl. exact Hidf.
    + discriminate.
  - unfold wdict_wf, wd, u32. cbn [wd_bytes wd_id wd_content].
    split; [lia | split; [lia |]].
    symmetry.
    replace b with ((le_bytes 4 ZSTD_MAGIC_DICTIONARY ++ le_bytes 4 id ++ hd ++ dO ++ dM ++ dL ++
                     le_bytes 4 r1 ++ le_bytes 4 r2 ++ le_bytes 4 r3) ++ content) at 2
      by (unfold b, fmt_dict_bytes; fold dO dM dL; rewrite <- !app_assoc; reflexivity).
    apply dfm_skipn. rewrite Hlb, !dfm_zlen_app, !dfm_len4. lia.
  - unfold wt_ok, S, fmt_dict_wst. cbn [wt_rep wt_huf wt_tabs].
    split; [| split].
    + lia.
    + intros H0 E. injection E as <-. exact HH.
    + intros a c d E. injection E as <- <- <-. auto.
  - rewrite Hmodel. unfold wt_dstate, S, fmt_dict_wst, st. cbn.
    rewrite !Hwf by lia. reflexivity.
Qed.

