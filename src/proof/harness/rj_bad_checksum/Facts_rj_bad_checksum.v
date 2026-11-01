(* The model facts of the law rj_bad_checksum (harness/rj_bad_checksum.c), plain Coq.

   The harness builds a frame with new_frame (frames.h) for data d, with Frame_Content_Size |d| (or no such
   field), no dictionary and a window up to STREAM_WINDOW (2^27), keeps it only if its Frame_Header_Descriptor
   (byte 4) has the Content_Checksum_flag (bit 2), and overwrites its last 4 bytes, the Content_Checksum, with a
   value v other than the low 32 bits of XXH64 of the frame's content (bad_frame d c v).  zstd's format model
   decodes all the blocks of this frame and then refuses it by its checksum (FDetCk), in every mode that checks
   checksums: ZSTD_decompress's (md_dflt) and buffered streaming's (dmode_w md_dflt). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params Zstd.proof.model.ErrCodes.
Require Export Zstd.proof.harness.frames.FKit.
Local Open Scope Z_scope.

(* new_frame's frame for d (Frame_Content_Size |d|, no dictionary) with its last 4 bytes replaced by v *)
Definition bad_frame (d: list Z) (c: nf_choice) (v: Z) : list Z :=
  firstn (Z.to_nat (Zlength (nf_bytes d (Zlength d) 0 c) - 4)) (nf_bytes d (Zlength d) 0 c) ++ le_bytes 4 v.

(* the changed frame is new_frame's header and blocks followed by the 4 bytes of v *)
Lemma bad_frame_split : forall d c v, nh_checksum (nc_hdr c) = true ->
  bad_frame d c v =
  nh_bytes (Zlength d) 0 (nc_hdr c) ++ nf_blocks_bytes d 0 (nc_blocks c) ++ le_bytes 4 v.
Proof.
  intros d c v Eck. unfold bad_frame.
  assert (HK: nf_checksum d c = le_bytes 4 (xxh64 (nf_data d c) 0)) by (unfold nf_checksum; rewrite Eck; reflexivity).
  unfold nf_bytes. rewrite HK, !app_assoc.
  set (A := nh_bytes (Zlength d) 0 (nc_hdr c) ++ nf_blocks_bytes d 0 (nc_blocks c)). f_equal.
  rewrite ff_Zlength_app, ff_le_bytes_Zlength. change (Z.of_nat 4) with 4.
  replace (Zlength A + 4 - 4) with (Zlength A) by lia. rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

(* byte 4 of a frame of new_frame is its Frame_Header_Descriptor *)
Lemma bad_byte4 : forall d fcs did c,
  byte_at (nf_bytes d fcs did c) 4 = nh_fhd (nc_hdr c).
Proof.
  intros. unfold nf_bytes, nh_bytes. rewrite <- !app_assoc. reflexivity.
Qed.

(* the descriptor's bit 2 is the Content_Checksum_flag *)
Lemma bad_fhd_checksum : forall fcs maxw did h,
  nh_ok fcs maxw did h -> Z.land (nh_fhd h) 4 <> 0 -> nh_checksum h = true.
Proof.
  intros fcs maxw did [f sg b df wd] (Hf & _ & _ & _ & _ & Hb & Hd & _) Hck.
  cbn [nh_fcs_flag nh_bits nh_did_flag] in *. revert Hck.
  unfold nh_fhd, nh_checksum; cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd].
  destruct (ff_flag_cases _ Hf) as [-> | [-> | [-> | ->]]];
  destruct (ff_flag_cases _ Hd) as [-> | [-> | [-> | ->]]];
  destruct Hb as [<- | [<- | [<- | [<- | []]]]]; destruct sg; vm_compute; congruence.
Qed.

(* the changed frame has the frame's length and is made of bytes *)
Lemma bad_frame_length : forall d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> nh_checksum (nc_hdr c) = true ->
  Zlength (bad_frame d c v) = Zlength (nf_bytes d (Zlength d) 0 c).
Proof.
  intros d c v _ Eck. rewrite bad_frame_split by exact Eck.
  unfold nf_bytes, nf_checksum. rewrite Eck, !ff_Zlength_app, !ff_le_bytes_Zlength. reflexivity.
Qed.

Lemma bad_frame_ok : forall d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d ->
  bytes_ok (bad_frame d c v).
Proof.
  intros d c v Hok Hd. unfold bad_frame.
  pose proof (nf_bytes_ok d (Zlength d) (2 ^ 27) 0 c Hok Hd) as H.
  apply ff_bytes_ok_app; [| apply ff_le_bytes_ok].
  set (l := nf_bytes d (Zlength d) 0 c) in *. set (n := Z.to_nat (Zlength l - 4)).
  rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. exact (proj1 H).
Qed.

(* ZSTD_decompressFrame in any mode that checks checksums, with the default (or a larger) block maximum: the
   blocks decode to the frame's content (frame_out_m), and the frame is refused by its checksum *)
Theorem bad_decode_frame : forall md d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
  nh_checksum (nc_hdr c) = true -> 0 <= v < 2 ^ 32 -> v <> xxh64 (nf_data d c) 0 mod 2 ^ 32 ->
  md_magicless md = false -> md_ignore md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  decode_frame_m md no_dict no_wlim (bad_frame d c v) = FDetCk /\
  frame_out_m md no_dict (bad_frame d c v) = Some (nf_data d c).
Proof.
  intros md d c v Hok Hd Hd64 Eck Hv Hne Hmg Hig Hbmax.
  pose proof (nf_data_length d (Zlength d) (2 ^ 27) 0 c Hok) as Hdl.
  destruct Hok as [Hh Hb].
  pose proof (ff_Zlength_nonneg d) as Hn.
  assert (Hw: nh_wlog_ok (nc_hdr c)) by (eapply nf_wlog_ok; [exact Hh | lia]).
  assert (Hwl: nh_window (Zlength d) (nc_hdr c) <= no_wlim).
  { destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw'). unfold no_wlim. lia. }
  rewrite bad_frame_split by exact Eck.
  set (h := nc_hdr c) in *.
  set (B := nf_blocks_bytes d 0 (nc_blocks c)) in *.
  set (K := le_bytes 4 v).
  set (fcs := Zlength d) in *.
  assert (Hg: get_frame_header (nh_bytes fcs 0 h ++ B ++ K) = FH_ok (nf_header_of fcs 0 h))
    by (apply (ff_get_frame_header fcs (2 ^ 27)); auto; lia).
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as HB. fold B in HB.
  assert (HK: Zlength K = 4) by (unfold K; rewrite ff_le_bytes_Zlength; reflexivity).
  assert (Hmb: Z.min (nh_max_block fcs h) (md_bmax md) = nh_max_block fcs h)
    by (apply Z.min_l; unfold nh_max_block; unfold ZSTD_BLOCKSIZE_MAX in Hbmax; lia).
  assert (Hwd: 0 <= nh_wd h) by (destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); lia).
  assert (Hwin0: 0 <= nh_window fcs h /\ (0 < fcs -> 1 <= nh_window fcs h)).
  { unfold nh_window. destruct (nh_single h) eqn:Es; [lia |].
    assert (1 <= 2 ^ (10 + nh_wd h / 8)).
    { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; [lia |]. pose proof (Z.div_pos (nh_wd h) 8). lia. }
    assert (0 <= 2 ^ (10 + nh_wd h / 8) / 8 * (nh_wd h mod 8)).
    { apply Z.mul_nonneg_nonneg; [apply Z.div_pos | apply Z.mod_pos_bound]; lia. }
    lia. }
  assert (Hblk: forall (w: bool) st hist wsize fuel, (length (B ++ K) <= fuel)%nat ->
    (if w then decode_blocks_w else decode_blocks) fuel st hist (B ++ K) nil (nh_max_block fcs h) wsize =
    Some (nf_data d c, Zlength B)).
  { intros w st hist wsize fuel Hf. unfold B. rewrite ff_decode_blocks with (mb := nh_max_block fcs h);
      [reflexivity | lia | unfold nh_max_block; lia | lia | unfold nh_max_block; lia | exact Hb |
       rewrite length_app in Hf; unfold B in Hf; lia]. }
  split.
  - destruct (ff_nh_read fcs (2 ^ 27) 0 h (B ++ K) Hh ltac:(lia) ltac:(lia)) as (Hm & H4 & H5 & _).
    pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
    destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (Hfb & _ & Hs5 & _ & H8 & _ & _ & Hhs).
    pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
    pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
    pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
    assert (Hzb: 0 <= zb (nh_single h) <= 1) by (destruct (nh_single h); simpl; lia).
    unfold decode_frame_m. rewrite Hmg. cbv iota beta zeta.
    set (s := nh_bytes fcs 0 h ++ B ++ K) in *.
    assert (Hs: Zlength s = Zlength (nh_bytes fcs 0 h) + Zlength B + Zlength K)
      by (unfold s; rewrite !ff_Zlength_app; lia).
    change (4 - 0) with 4. change (5 - 0) with 5.
    rewrite H4, Hm, Hhs, H8, Hs5, Z.eqb_refl, <- Hlen.
    unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
    rewrite (proj2 (Z.ltb_ge (Zlength s) (6 - 0 + 3))) by lia.
    rewrite (proj2 (Z.ltb_ge (Zlength s) (Zlength (nh_bytes fcs 0 h) - 0 + 3))) by lia.
    change (0 =? 0) with true. cbn [negb andb].
    assert (Hwin: (negb (zb (nh_single h) =? 1) &&
                  (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX))%bool = false).
    { destruct (nh_single h) eqn:Es; [reflexivity |].
      rewrite H5 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold nh_wlog_ok in Hw. rewrite Es in Hw. destruct Hw as [Hw | Hw]; [discriminate |].
      cbn [zb]. change (0 =? 1) with false. cbn [negb andb].
      rewrite Z.gtb_ltb. apply Z.ltb_ge. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN. lia. }
    rewrite Hwin.
    change (get_frame_header_m false s) with (get_frame_header s). rewrite Hg.
    cbn [nf_header_of fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize
         fh_checksumFlag].
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge no_wlim _)) by lia. change (0 =? 0) with true. cbn [negb andb].
    unfold s at 1 2. rewrite ff_skipn_app by reflexivity. rewrite Hmb, Hblk by lia.
    assert (Hcsz: (negb ((if ((nh_fcs_flag h =? 0) && negb (nh_single h))%bool then ZSTD_CONTENTSIZE_UNKNOWN
                          else fcs) =? ZSTD_CONTENTSIZE_UNKNOWN) &&
                  negb (Zlength (nf_data d c) =?
                        (if ((nh_fcs_flag h =? 0) && negb (nh_single h))%bool then ZSTD_CONTENTSIZE_UNKNOWN
                         else fcs)))%bool = false).
    { destruct ((nh_fcs_flag h =? 0) && negb (nh_single h))%bool.
      + rewrite Z.eqb_refl. reflexivity.
      + rewrite Hdl, Z.eqb_refl, Bool.andb_false_r. reflexivity. }
    rewrite Hcsz. rewrite Eck. cbn [zb]. change (1 =? 1) with true. cbv iota.
    rewrite (proj2 (Z.ltb_ge _ 4)) by lia.
    unfold s. rewrite app_assoc.
    rewrite <- (app_nil_r K). rewrite ff_le_field_at by (rewrite ?ff_Zlength_app; lia).
    unfold K. rewrite ff_le_value_le_bytes. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite Z.mod_small by lia. rewrite Hig. cbn [negb andb].
    rewrite (proj2 (Z.eqb_neq _ _) Hne). reflexivity.
  - unfold frame_out_m. rewrite Hmg.
    change (get_frame_header_m false (nh_bytes fcs 0 h ++ B ++ K))
      with (get_frame_header (nh_bytes fcs 0 h ++ B ++ K)). rewrite Hg.
    cbn [nf_header_of fh_windowSize fh_headerSize fh_blockSizeMax].
    rewrite ff_skipn_app by reflexivity. rewrite Hmb, Hblk by lia. reflexivity.
Qed.

(* the changed frame keeps new_frame's header: it starts with zstd's magic number and is at least as long as
   a frame header's prefix *)
Lemma bad_magic : forall d c v, nh_checksum (nc_hdr c) = true ->
  le_field (bad_frame d c v) 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros d c v Eck. rewrite bad_frame_split by exact Eck. unfold nh_bytes. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bad_starting_len : forall d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> nh_checksum (nc_hdr c) = true ->
  starting_len false <= Zlength (bad_frame d c v).
Proof.
  intros d c v Hok Eck. rewrite bad_frame_length by assumption.
  pose proof (nf_bytes_length d (Zlength d) (2 ^ 27) 0 c Hok). unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX.
  lia.
Qed.

(* one-shot (ZSTD_decompress): a series refused by a checksum, after the content nf_data d c
   (Spec_codes.oneshot_codes then gives ZSTD_error_checksum_wrong with room for it) *)
Theorem bad_series_ck : forall d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
  nh_checksum (nc_hdr c) = true -> 0 <= v < 2 ^ 32 -> v <> xxh64 (nf_data d c) 0 mod 2 ^ 32 ->
  series_ck_m md_dflt sel_none no_wlim (Some no_dict) (bad_frame d c v) (nf_data d c).
Proof.
  intros d c v Hok Hd Hd64 Eck Hv Hne.
  destruct (bad_decode_frame md_dflt d c v Hok Hd Hd64 Eck Hv Hne eq_refl eq_refl ltac:(reflexivity || lia))
    as [Hdec Hout].
  apply sck_last with (d := no_dict); [apply bad_starting_len; auto | | apply frame_dict_sel_none | exact Hdec |
    exact Hout].
  cbn [md_dflt md_magicless negb andb]. rewrite bad_magic by exact Eck. reflexivity.
Qed.

(* streamed (or one-shot): the walk over the series finds no complete frame and ends at the checksum refusal *)
Theorem bad_series_frames : forall md d c v,
  nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
  nh_checksum (nc_hdr c) = true -> 0 <= v < 2 ^ 32 -> v <> xxh64 (nf_data d c) 0 mod 2 ^ 32 ->
  md_magicless md = false -> md_ignore md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  series_frames_m md sel_none (Some no_dict) no_wlim (bad_frame d c v) = (nil, TDetCk).
Proof.
  intros md d c v Hok Hd Hd64 Eck Hv Hne Hmg Hig Hbmax.
  destruct (bad_decode_frame md d c v Hok Hd Hd64 Eck Hv Hne Hmg Hig Hbmax) as [Hdec _].
  pose proof (bad_starting_len d c v Hok Eck) as Hsl.
  unfold series_frames_m. cbn [walk_m]. rewrite Hmg.
  rewrite (proj2 (Z.ltb_ge _ _) Hsl). rewrite bad_magic by exact Eck. cbn [negb andb].
  change (is_skippable_magic ZSTD_MAGICNUMBER) with false.
  rewrite frame_dict_sel_none, Hdec. reflexivity.
Qed.
