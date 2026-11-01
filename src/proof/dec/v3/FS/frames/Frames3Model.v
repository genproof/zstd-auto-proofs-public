(* FS3 one-shot frames: the model facts of ONE frame under the decoding mode md (Params.decode_frame_m: the
   magicless format, forceIgnoreChecksum, maxBlockSize), used by ZSTD_decompressFrame's body.  Plain Coq facts; the v2
   analogues (zstd1, default mode) are FramesHdr.v and the
   model lemmas of v2 body_frame.v (copied, with fr_DB/fr_OT/blk_res, into Frames3Pure.v).  Target of this
   file: frames3_model_all. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Pure.
Local Open Scope Z_scope.

Section CM_Frames3Model_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- helpers: the magicless header read behind a magic number ---------- *)

Lemma f3m_magic: magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma f3m_byte_at: forall s i, 0 <= i -> byte_at (magic_bytes ++ s) (i + 4) = byte_at s i.
Proof.
  intros. rewrite f3m_magic. unfold byte_at. rewrite Z2Nat.inj_add by lia.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma f3m_le_field: forall s i k, 0 <= i -> le_field (magic_bytes ++ s) (i + 4) k = le_field s i k.
Proof.
  intros. rewrite f3m_magic. unfold le_field, slice. rewrite Z2Nat.inj_add by lia.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma f3m_le_field0: forall s, le_field (magic_bytes ++ s) 0 4 = ZSTD_MAGICNUMBER.
Proof. intros. rewrite f3m_magic. reflexivity. Qed.

Lemma f3m_len: forall s, Zlength (magic_bytes ++ s) = Zlength s + 4.
Proof. intros. rewrite Zlength_app, f3m_magic. change (Zlength [40; 181; 47; 253]) with 4. lia. Qed.

Lemma f3m_bytes_ok: forall s, bytes_ok s -> bytes_ok (magic_bytes ++ s).
Proof.
  intros. unfold bytes_ok. apply Forall_app. split; [|exact H].
  rewrite f3m_magic. repeat constructor; unfold is_byte; lia.
Qed.

Lemma f3m_sublist0: forall (s: list Z) n, sublist 0 n s = firstn (Z.to_nat n) s.
Proof. intros. unfold sublist. reflexivity. Qed.

(* the header of the bytes s read in the format mg: the zstd1 header of sx mg s *)
Definition f3m_sx (mg: bool) (s: list Z) : list Z := if mg then magic_bytes ++ s else s.

Lemma f3m_gfh: forall mg s h, get_frame_header_m mg s = FH_ok h ->
  exists h', get_frame_header (f3m_sx mg s) = FH_ok h' /\ h = if mg then fh_unshift h' else h'.
Proof.
  intros [|] s h H; cbn [f3m_sx get_frame_header_m negb] in *.
  - destruct (Zlength s <? 1); [discriminate|].
    destruct (get_frame_header (magic_bytes ++ s)) as [|k|h']; try discriminate.
    injection H as <-. eauto.
  - eauto.
Qed.


Lemma f3m_byte_at4: forall s, byte_at (magic_bytes ++ s) 4 = byte_at s 0.
Proof. intros. exact (f3m_byte_at s 0 ltac:(lia)). Qed.

Lemma f3m_byte_at5: forall s, byte_at (magic_bytes ++ s) 5 = byte_at s 1.
Proof. intros. exact (f3m_byte_at s 1 ltac:(lia)). Qed.

(* the header read from its first header_size_m bytes *)
Lemma f3m_prefix: forall mg s,
  bytes_ok s -> starting_len mg <= Zlength s -> (mg = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) ->
  header_size_m mg s <= Zlength s ->
  get_frame_header_m mg (sublist 0 (header_size_m mg s) s) = get_frame_header_m mg s.
Proof.
  intros [|] s Hb Hl Hm Hh; cbn [get_frame_header_m negb header_size_m starting_len] in *.
  - pose proof (frm_byte_at_bound s 0 Hb) as B. pose proof (frm_hs_range _ B) as R.
    rewrite Zlength_sublist by lia.
    destruct (Z.ltb_spec (fhd_header_size (byte_at s 0) - 4 - 0) 1); [lia|].
    destruct (Z.ltb_spec (Zlength s) 1); [lia|].
    assert (E: magic_bytes ++ sublist 0 (fhd_header_size (byte_at s 0) - 4) s =
               firstn (Z.to_nat (fhd_header_size (byte_at (magic_bytes ++ s) 4))) (magic_bytes ++ s)).
    { rewrite f3m_byte_at4, firstn_app, f3m_sublist0. rewrite (firstn_all2 (n := Z.to_nat _) magic_bytes) by (rewrite f3m_magic; simpl; lia).
      f_equal. f_equal. rewrite f3m_magic. simpl length. rewrite Z2Nat.inj_sub by lia. reflexivity. }
    rewrite E, frm_gfh_prefix; [reflexivity|..].
    + rewrite f3m_byte_at4. exact B.
    + rewrite f3m_len. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia.
    + apply f3m_le_field0.
    + rewrite f3m_byte_at4, f3m_len. lia.
  - rewrite f3m_sublist0. apply frm_gfh_prefix; auto.
    apply frm_byte_at_bound; auto.
Qed.


(* the frame after a parsed header (Params.decode_frame_m's tail) *)
Definition f3m_tail (md: dmode) (dm: dict_model) (s: list Z) (h: frame_header) : fres :=
  if andb (negb (fh_dictID h =? 0)) (negb (fh_dictID h =? dm_id dm)) then FUnk else
  let hs := fh_headerSize h in
  let rest := skipn (Z.to_nat hs) s in
  match decode_blocks (length rest) (dm_state dm) (dm_content dm) rest nil (Z.min (fh_blockSizeMax h) (md_bmax md))
          (fh_windowSize h) with
  | None => FUnk
  | Some (out, k) =>
      if andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN)) (negb (Zlength out =? fh_contentSize h))
      then FUnk else
      if fh_checksumFlag h =? 1 then
        (if Zlength s - hs - k <? 4 then FUnk
         else if andb (negb (md_ignore md)) (negb (le_field s (hs + k) 4 =? xxh64 out 0 mod 2 ^ 32)) then FDetCk
         else FOk out (hs + k + 4))
      else FOk out (hs + k)
  end.

Lemma f3m_dec_ok: forall md dm s h,
  md_dwin md = false -> bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize <= Zlength s ->
  (md_magicless md = false -> le_field s 0 4 = ZSTD_MAGICNUMBER) ->
  header_size_m (md_magicless md) s + ZSTD_blockHeaderSize <= Zlength s ->
  get_frame_header_m (md_magicless md) s = FH_ok h ->
  fh_headerSize h = header_size_m (md_magicless md) s /\ decode_frame_m md dm no_wlim s = f3m_tail md dm s h.
Proof.
  intros [mg ig bm dw] dm s h Hdw Hb Hl Hm Hh Hg. cbn [md_magicless md_ignore md_bmax md_dwin] in *. subst dw.
  destruct (f3m_gfh _ _ _ Hg) as [h' [Hg' ->]].
  assert (Hbx: bytes_ok (f3m_sx mg s)) by (destruct mg; [apply f3m_bytes_ok|]; auto).
  assert (Hmx: le_field (f3m_sx mg s) 0 4 = ZSTD_MAGICNUMBER) by (destruct mg; [apply f3m_le_field0|]; auto).
  assert (Hlx: Zlength (f3m_sx mg s) = Zlength s + mg_sh mg) by (destruct mg; [apply f3m_len|cbn; lia]).
  destruct (frm_gfh_ok _ h' Hbx Hmx Hg') as (Ht & Hhs & _ & _ & _ & _ & Hw & _).
  assert (G := Hg'). unfold get_frame_header in G.
  destruct (Z.ltb_spec (Zlength (f3m_sx mg s)) 5).
  { destruct mg; cbn [mg_sh] in *; unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in *; lia. }
  rewrite Hmx, Z.eqb_refl in G. cbn [negb] in G.
  destruct (Zlength (f3m_sx mg s) <? _); [discriminate|].
  destruct (negb (Z.land (byte_at (f3m_sx mg s) 4) 8 =? 0)) eqn:R; [discriminate|].
  destruct (andb (Z.land (Z.shiftr (byte_at (f3m_sx mg s) 4) 5) 1 =? 0)
            (Z.shiftr (byte_at (f3m_sx mg s) 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX)) eqn:W;
    [discriminate|].
  clear G.
  assert (B4: 0 <= byte_at (f3m_sx mg s) 4 < 256) by (apply frm_byte_at_bound; auto).
  assert (Hsg: negb (Z.land (Z.shiftr (byte_at (f3m_sx mg s) 4) 5) 1 =? 1) =
               (Z.land (Z.shiftr (byte_at (f3m_sx mg s) 4) 5) 1 =? 0)).
  { destruct (frm_fhd_bits _ B4) as (_ & Hss & _).
    assert (Z.land (Z.shiftr (byte_at (f3m_sx mg s) 4) 5) 1 = 0 \/
            Z.land (Z.shiftr (byte_at (f3m_sx mg s) 4) 5) 1 = 1) as [-> | ->] by lia; reflexivity. }
  destruct mg; cbn [f3m_sx mg_sh header_size_m] in *.
  - rewrite f3m_byte_at4 in Hhs, R, W, Hsg, B4. rewrite f3m_byte_at5 in W.
    split; [cbn [fh_unshift fh_headerSize]; lia|].
    unfold decode_frame_m. cbn [md_magicless md_ignore md_bmax md_dwin negb andb].
    change (4 - 4) with 0. change (5 - 4) with 1.
    destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN - 4 + ZSTD_blockHeaderSize)); [lia|].
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 0) - 4 + ZSTD_blockHeaderSize)); [lia|].
    rewrite R, Hsg, W, Hg.
    cbn [fh_unshift fh_windowSize fh_frameType].
    destruct (Z.gtb_spec (fh_windowSize h') no_wlim); [unfold no_wlim in *; lia|].
    rewrite Ht. reflexivity.
  - split; [lia|].
    unfold decode_frame_m. cbn [md_magicless md_ignore md_bmax md_dwin negb andb].
    change (4 - 0) with 4. change (5 - 0) with 5.
    destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN - 0 + ZSTD_blockHeaderSize)); [lia|].
    rewrite Hm, Z.eqb_refl by auto. cbn [negb].
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) - 0 + ZSTD_blockHeaderSize)); [lia|].
    rewrite R, Hsg, W, Hg.
    destruct (Z.gtb_spec (fh_windowSize h') no_wlim); [unfold no_wlim in *; lia|].
    rewrite Ht. reflexivity.
Qed.


(* a frame the model decodes or rejects at its checksum has the magic number (zstd1) and a parsed header *)
Lemma f3m_magic_need: forall md dm w s,
  decode_frame_m md dm w s <> FUnk -> md_magicless md = false -> le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros md dm w s H E. destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [|N]; auto.
  exfalso. apply H. unfold decode_frame_m. cbv zeta. rewrite E. cbn [negb andb].
  destruct (Zlength s <? _); [reflexivity|]. apply Z.eqb_neq in N. rewrite N. reflexivity.
Qed.

Lemma f3m_dec_noh: forall md dm w s,
  (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  (forall c sz, decode_frame_m md dm w s <> FOk c sz) /\ decode_frame_m md dm w s <> FDetCk.
Proof.
  intros md dm w s H. unfold decode_frame_m. cbv zeta.
  destruct (get_frame_header_m (md_magicless md) s) eqn:G; [| |exfalso; eapply H; eauto];
    split; try intros c sz;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

End CM_Frames3Model_1.

Ltac f3m_side :=
  first [assumption |
         destruct (md_magicless _); cbn [mg_sh starting_len] in *;
         unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_blockHeaderSize in *; lia].

(* fr_hdr3's header is the frame's; decode_frame_m is its tail E *)
Ltac f3m_setup Hdf Hg E :=
  let Hm := fresh "Hm" in let Hhs := fresh "Hhs" in let D := fresh "D" in
  assert (Hm := f3m_magic_need _ _ _ _ ltac:(rewrite Hdf; discriminate));
  rewrite f3m_prefix in Hg by f3m_side;
  match goal with Hd: false = false -> _ |- _ => specialize (Hd eq_refl) end;
  match goal with Hd: fh_dictID ?h0 = 0 \/ fh_dictID ?h0 = dm_id ?dm |- _ =>
    assert (D: andb (negb (fh_dictID h0 =? 0)) (negb (fh_dictID h0 =? dm_id dm)) = false)
      by (destruct Hd as [-> | ->]; rewrite Z.eqb_refl; [reflexivity | apply andb_false_r]) end;
  edestruct f3m_dec_ok as [Hhs E]; [eassumption.. | rewrite Hdf in E];
  unfold f3m_tail in E; rewrite Hhs in E;
  rewrite D in E;
  try (unfold fr_DB, fr_rest; rewrite frm_sub_end;
       cbn [fh_cap fh_blockSizeMax fh_windowSize fh_contentSize fh_checksumFlag]).

Section CM_Frames3Model_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the probe stops at a non-NULL slot of the table *)
Lemma f3m_probe: forall fuel l tbl j n id, n = Zlength tbl -> 0 <= j < n ->
  hs_probe_f fuel l tbl j n id <> nullval -> In (hs_probe_f fuel l tbl j n id) tbl.
Proof.
  induction fuel as [|f IH]; intros l tbl j n id En Hj H; cbn [hs_probe_f] in *; [contradiction|].
  destruct (eq_dec (Znth j tbl) nullval) as [N|N]; [contradiction|].
  destruct (orb _ _).
  - apply Znth_In. lia.
  - apply IH; auto. apply Z.mod_pos_bound. lia.
Qed.

(* ZSTD_frameHeaderSize_internal(ip, ZSTD_FRAMEHEADERSIZE_PREFIX(format), format) reads the prefix *)
Lemma hsz3_prefix: forall mg s,
  starting_len mg <= Zlength s ->
  frame_header_size_m mg (sublist 0 (starting_len mg) s) = Some (header_size_m mg s).
Proof.
  intros [|] s H; cbn [frame_header_size_m negb header_size_m starting_len] in *.
  - rewrite Zlength_sublist by lia.
    destruct (Z.ltb_spec (1 - 0) 1); [lia|].
    rewrite f3m_sublist0, frm_byte_at_firstn by lia. reflexivity.
  - unfold frame_header_size, ZSTD_FRAMEHEADERSIZE_PREFIX in *. rewrite Zlength_sublist by lia.
    destruct (Z.ltb_spec (5 - 0) 5); [lia|].
    rewrite f3m_sublist0, frm_byte_at_firstn by lia. reflexivity.
Qed.

(* the header size: 6..18 bytes (zstd1), 2..14 (magicless) *)
Lemma hs3_range: forall mg s,
  bytes_ok s -> starting_len mg <= Zlength s ->
  6 - mg_sh mg <= header_size_m mg s <= 18 - mg_sh mg.
Proof.
  intros [|] s Hb _; cbn [mg_sh header_size_m];
    match goal with |- context [fhd_header_size (byte_at s ?i)] =>
      pose proof (frm_hs_range _ (frm_byte_at_bound s i Hb)) end; lia.
Qed.

(* the early exits of ZSTD_decompressFrame before ZSTD_decodeFrameHeader: the model does not decode the frame *)
Lemma decode_frame3_short: forall md dm s,
  Zlength s < ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize \/
  Zlength s < header_size_m (md_magicless md) s + ZSTD_blockHeaderSize ->
  decode_frame_m md dm no_wlim s = FUnk.
Proof.
  intros [[|] ig bm] dm s H; unfold decode_frame_m; cbv zeta; cbn [md_magicless mg_sh header_size_m negb andb] in *.
  - change (4 - 4) with 0.
    destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN - 4 + ZSTD_blockHeaderSize)); [reflexivity|].
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 0) - 4 + ZSTD_blockHeaderSize)); [reflexivity|].
    lia.
  - change (4 - 0) with 4.
    destruct (Z.ltb_spec (Zlength s) (ZSTD_FRAMEHEADERSIZE_MIN - 0 + ZSTD_blockHeaderSize)); [reflexivity|].
    destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [reflexivity|].
    destruct (Z.ltb_spec (Zlength s) (fhd_header_size (byte_at s 4) - 0 + ZSTD_blockHeaderSize)); [reflexivity|].
    lia.
Qed.

(* ZSTD_decodeFrameHeader failed (without the selection): the model does not decode the frame *)
Lemma hdr_err_model3: forall md dm s d l tbl fs r fs' d',
  md_dwin md = false -> bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize <= Zlength s ->
  header_size_m (md_magicless md) s + ZSTD_blockHeaderSize <= Zlength s ->
  dfh_post3 md false d l tbl fs (dm_id dm) 0 (sublist 0 (header_size_m (md_magicless md) s) s) r fs' d' ->
  is_error_code r = true ->
  forall c sz, decode_frame_m md dm no_wlim s = FOk c sz -> False.
Proof.
  intros md dm s d l tbl fs r fs' d' Hdw Hb Hl Hh Hd Her c sz Hdf.
  assert (Hm := f3m_magic_need md dm no_wlim s ltac:(rewrite Hdf; discriminate)).
  unfold dfh_post3 in Hd. rewrite f3m_prefix in Hd by f3m_side.
  destruct (get_frame_header_m (md_magicless md) s) as [|k|h] eqn:G.
  1,2: eapply (proj1 (f3m_dec_noh md dm no_wlim s ltac:(intros h0; rewrite G; discriminate))); eauto.
  cbv zeta in Hd. destruct (eq_dec nullval nullval) as [_|N]; [|congruence].
  destruct Hd as [_ Hd]. destruct (orb (fh_dictID h =? 0) (fh_dictID h =? dm_id dm)) eqn:O.
  - destruct Hd as [-> _]. vm_compute in Her. discriminate.
  - destruct (f3m_dec_ok md dm s h Hdw Hb Hl Hm Hh G) as [_ E]. rewrite Hdf in E.
    apply orb_false_iff in O. destruct O as [O1 O2]. unfold f3m_tail in E. rewrite O1, O2 in E.
    discriminate.
Qed.

(* the values of a parsed header the C reads back *)
Lemma gfh3_range: forall mg x h,
  bytes_ok x -> get_frame_header_m mg x = FH_ok h ->
  0 <= fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX /\ (fh_checksumFlag h = 0 \/ fh_checksumFlag h = 1) /\
  0 <= fh_contentSize h < 2 ^ 64 /\ 0 <= fh_windowSize h < 2 ^ 64 /\ 0 <= fh_dictID h < 2 ^ 32.
Proof.
  intros [|] x h Hb H.
  - cbn [get_frame_header_m negb] in H. destruct (Zlength x <? 1); [discriminate|].
    destruct (get_frame_header (magic_bytes ++ x)) as [|k|h'] eqn:G; try discriminate.
    injection H as <-. exact (gfh_range _ h' (f3m_bytes_ok _ Hb) G).
  - exact (gfh_range x h Hb H).
Qed.

(* the frame, after a successful header (without the selection): Ok *)
Lemma fr_frame_ok3: forall md dm s hs h c sz,
  fr_hdr3 md false dm s hs h -> decode_frame_m md dm no_wlim s = FOk c sz ->
  exists k, fr_DB dm h s hs = Some (c, k) /\
    (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength c = fh_contentSize h) /\
    (if fh_checksumFlag h =? 1
     then hs + k + 4 <= Zlength s /\ (md_ignore md = false -> le_field s (hs + k) 4 = xxh64 c 0 mod 2 ^ 32) /\
          sz = hs + k + 4
     else sz = hs + k).
Proof.
  intros md dm s hs h c sz (Hb & Hl & -> & Hh & h0 & Hg & -> & Hdict & Hdw) Hdf.
  f3m_setup Hdf Hg E.
  destruct (decode_blocks _ _ _ _ _ _ _) as [[o k]|]; [|discriminate].
  symmetry in E.
  destruct (andb (negb (fh_contentSize h0 =? _)) _) eqn:C; [discriminate|].
  assert (HC: fh_contentSize h0 = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength o = fh_contentSize h0).
  { apply andb_false_iff in C. destruct C as [C|C]; apply negb_false_iff, Z.eqb_eq in C; auto. }
  exists k. destruct (fh_checksumFlag h0 =? 1).
  - destruct (Z.ltb_spec (Zlength s - header_size_m (md_magicless md) s - k) 4); [discriminate|].
    destruct (andb (negb (md_ignore md)) _) eqn:X; [discriminate|].
    injection E as -> <-. split; [reflexivity|]. split; [exact HC|]. split; [lia|]. split; [|reflexivity].
    intros Hi. rewrite Hi in X. cbn [negb andb] in X. apply negb_false_iff, Z.eqb_eq in X. exact X.
  - injection E as -> <-. auto.
Qed.

(* ... a wrong checksum *)
Lemma fr_frame_ck3: forall md dm s hs h,
  fr_hdr3 md false dm s hs h -> decode_frame_m md dm no_wlim s = FDetCk ->
  exists c k, fr_DB dm h s hs = Some (c, k) /\ fh_checksumFlag h = 1 /\ md_ignore md = false /\
    (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength c = fh_contentSize h) /\
    hs + k + 4 <= Zlength s /\ le_field s (hs + k) 4 <> xxh64 c 0 mod 2 ^ 32.
Proof.
  intros md dm s hs h (Hb & Hl & -> & Hh & h0 & Hg & -> & Hdict & Hdw) Hdf.
  f3m_setup Hdf Hg E.
  destruct (decode_blocks _ _ _ _ _ _ _) as [[o k]|]; [|discriminate].
  exists o, k. split; [reflexivity|]. symmetry in E.
  destruct (andb (negb (fh_contentSize h0 =? _)) _) eqn:C; [discriminate|].
  destruct (fh_checksumFlag h0 =? 1) eqn:CK; [|discriminate].
  destruct (Z.ltb_spec (Zlength s - header_size_m (md_magicless md) s - k) 4); [discriminate|].
  destruct (andb (negb (md_ignore md)) _) eqn:X; [|discriminate].
  apply andb_true_iff in X. destruct X as [X1 X2]. apply negb_true_iff in X1, X2. apply Z.eqb_neq in X2.
  apply Z.eqb_eq in CK.
  split; [exact CK|]. split; [exact X1|]. split; [|split; [lia|exact X2]].
  apply andb_false_iff in C. destruct C as [C|C]; apply negb_false_iff, Z.eqb_eq in C; [left|right]; exact C.
Qed.

(* ... never rejected at the header *)
Lemma fr_frame_hdr3: forall md dm s hs h,
  fr_hdr3 md false dm s hs h -> decode_frame_m md dm no_wlim s <> FDetHdr.
Proof.
  intros md dm s hs h (Hb & Hl & -> & Hh & h0 & Hg & -> & Hdict & Hdw) Hdf.
  f3m_setup Hdf Hg E.
  repeat match type of E with context [match ?c with _ => _ end] => destruct c end; discriminate.
Qed.

(* the DDict ZSTD_DDictHashSet_getDDict's probe finds is one of the set (hs_inv: the table's non-NULL slots are
   the set's DDicts) *)
Lemma hs_probe_in: forall l tbl id,
  hs_inv l tbl -> hs_probe l tbl id <> nullval -> In (hs_probe l tbl id) (map fst l).
Proof.
  intros l tbl id Hi Hn. destruct Hi as ([k [Hk En]] & _ & _ & _ & _ & _ & Hp & _).
  unfold hs_probe in *.
  assert (Hj: 0 <= hs_home id (Zlength tbl) < Zlength tbl).
  { unfold hs_home. rewrite En. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  pose proof (f3m_probe _ l tbl _ _ id eq_refl Hj Hn) as Hin.
  eapply Permutation_in; [exact Hp|]. apply filter_In. split; [exact Hin|].
  unfold veqb. destruct (Val.eq _ nullval); [contradiction|reflexivity].
Qed.

(* a Zstandard frame's header (Frame_Type 0) parses only behind the magic number *)
Lemma gfh_type0_magic: forall s h,
  get_frame_header s = FH_ok h -> fh_frameType h = 0 -> le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros s h G T. destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [|N]; [assumption|].
  exfalso. unfold get_frame_header in G.
  destruct (Zlength s <? 5).
  { repeat match type of G with context [if ?c then _ else _] => destruct c end; discriminate. }
  apply Z.eqb_neq in N. rewrite N in G. cbn [negb] in G.
  destruct (is_skippable_magic _); [|discriminate].
  destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE); [discriminate|].
  injection G as <-. discriminate T.
Qed.

(* the refusal walk reads only the window size, the content size and the checksum flag of the header: the cap of
   Block_Maximum_Size does not change it *)
Lemma br_cap: forall dw f md h0 st hist s out bsm,
  blocks_refused dw f (fh_cap md h0) st hist s out bsm <-> blocks_refused dw f h0 st hist s out bsm.
Proof.
  induction f as [|f IH]; intros; cbn [blocks_refused]; [tauto|].
  change (fh_windowSize (fh_cap md h0)) with (fh_windowSize h0).
  destruct (_ <? _); [tauto|]. destruct (_ =? 3); [tauto|]. destruct (cblock_size s); [|tauto].
  destruct (_ >? _); [tauto|]. destruct (rblock _ _ _ _ _ _ _ _) as [[st' out']|]; [|tauto].
  destruct (_ =? 1); [unfold frame_end_refused; cbn [fh_cap fh_contentSize fh_checksumFlag]; tauto | apply IH].
Qed.

(* a frame zstd certainly refuses (Refuse.frame_refused_m), after the header the C parsed (fr_hdr3): its blocks
   are refused, from the first one *)
Lemma fr_refused_blocks3: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> frame_refused_m md dm no_wlim s ->
  exists f0, blocks_refused false f0 h (dm_state dm) (dm_content dm) (fr_rest s hs) [] (fh_blockSizeMax h).
Proof.
  intros md sel dm s hs h (Hb & Hl & Ehs & Hh & h0 & Hg & Eh & _ & Hdw) Hr.
  unfold frame_refused_m in Hr. cbv zeta in Hr. rewrite <- Ehs in Hr.
  destruct (Z.ltb_spec (Zlength s) hs); [unfold ZSTD_blockHeaderSize in Hh; lia|].
  destruct (get_frame_header_m (md_magicless md) s) as [| |h1] eqn:G; try contradiction.
  destruct Hr as (_ & Ht & _ & Hbr).
  assert (Hm: md_magicless md = false -> le_field s 0 4 = ZSTD_MAGICNUMBER).
  { intros E. rewrite E in G. cbn [get_frame_header_m negb] in G. exact (gfh_type0_magic s h1 G Ht). }
  assert (Hst: starting_len (md_magicless md) <= Zlength s) by f3m_side.
  subst hs. rewrite f3m_prefix in Hg by (first [assumption | unfold ZSTD_blockHeaderSize in Hh; lia]).
  rewrite G in Hg. injection Hg as <-.
  destruct (f3m_dec_ok md dm s h1 Hdw Hb Hl Hm Hh G) as [Hhs _].
  rewrite Hdw, Hhs in Hbr. exists (S (length (skipn (Z.to_nat (header_size_m (md_magicless md) s)) s))).
  subst h. unfold fr_rest. rewrite frm_sub_end. apply br_cap. exact Hbr.
Qed.

(* all the lemmas above (the target of this file: its assumptions are theirs) *)
Lemma frames3_model_all : True.
Proof.
  pose proof hsz3_prefix. pose proof hs3_range. pose proof decode_frame3_short. pose proof hdr_err_model3.
  pose proof gfh3_range. pose proof fr_frame_ok3. pose proof fr_frame_ck3. pose proof fr_frame_hdr3.
  pose proof hs_probe_in. exact I.
Qed.

End CM_Frames3Model_2.
