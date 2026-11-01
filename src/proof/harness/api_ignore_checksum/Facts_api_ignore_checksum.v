(* The model facts of the law api_ignore_checksum (harness/api_ignore_checksum.c), plain Coq.

   The harness builds a frame with new_frame (frames.h), keeps it only if its Frame_Header_Descriptor (byte 4)
   has the Content_Checksum_flag (bit 2), and overwrites its last 4 bytes, the Content_Checksum, with any
   value.  With ZSTD_d_forceIgnoreChecksum set (md_ignore = true) the model decodes this frame to the
   frame's content, whatever the 4 bytes are. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FKit.

(* byte 4 of a frame of new_frame is its Frame_Header_Descriptor *)
Lemma nf_byte4 : forall d fcs did c rest,
  byte_at (nf_bytes d fcs did c ++ rest) 4 = nh_fhd (nc_hdr c).
Proof.
  intros. unfold nf_bytes, nh_bytes. rewrite <- !app_assoc. reflexivity.
Qed.

(* the descriptor's bit 2 is the Content_Checksum_flag *)
Lemma nf_fhd_checksum : forall fcs maxw did h,
  nh_ok fcs maxw did h -> Z.land (nh_fhd h) 4 <> 0 -> nh_checksum h = true.
Proof.
  intros fcs maxw did [f sg b df wd] Hh.
  destruct Hh as (Hf & _ & _ & _ & _ & Hb & Hd & _).
  cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd] in *.
  unfold nh_fhd, nh_checksum; cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd].
  destruct (ff_flag_cases _ Hf) as [-> | [-> | [-> | ->]]];
  destruct (ff_flag_cases _ Hd) as [-> | [-> | [-> | ->]]];
  destruct Hb as [<- | [<- | [<- | [<- | []]]]]; destruct sg; vm_compute; congruence.
Qed.

Local Open Scope bool_scope.

(* nf_decode_frame_m (FFacts.v) with the Content_Checksum K any 4 bytes, when checksums are ignored *)
Lemma nf_decode_frame_ignore : forall md dm wlim d fcs maxw did c K rest,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  nh_wlog_ok (nc_hdr c) ->
  md_magicless md = false -> md_ignore md = true -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  nh_window fcs (nc_hdr c) <= wlim ->
  (did = 0 \/ did = dm_id dm) ->
  (fcs = Zlength d \/ (nh_fcs_flag (nc_hdr c) = 0 /\ nh_single (nc_hdr c) = false)) ->
  nh_checksum (nc_hdr c) = true -> Zlength K = 4 ->
  decode_frame_m md dm wlim (nh_bytes fcs did (nc_hdr c) ++ nf_blocks_bytes d 0 (nc_blocks c) ++ K ++ rest) =
  FOk (nf_data d c)
    (Zlength (nh_bytes fcs did (nc_hdr c)) + Zlength (nf_blocks_bytes d 0 (nc_blocks c)) + 4).
Proof.
  intros md dm wlim d fcs maxw did c K rest Hok Hd Hfcs Hdid Hw Hmg Hig Hbmax Hwl Hdm Hcs Eck HK.
  pose proof (nf_data_length d fcs maxw did c Hok) as Hdl.
  destruct Hok as [Hh Hb].
  set (h := nc_hdr c) in *.
  set (B := nf_blocks_bytes d 0 (nc_blocks c)) in *.
  pose proof (ff_get_frame_header fcs maxw did h (B ++ K ++ rest) Hh Hfcs Hdid Hw) as Hg.
  destruct (ff_nh_read fcs maxw did h (B ++ K ++ rest) Hh Hfcs Hdid) as (Hm & H4 & H5 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (Hfb & _ & Hs5 & _ & H8 & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
  pose proof (ff_Zlength_nonneg d) as Hn.
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as HB.
  pose proof (ff_Zlength_nonneg rest) as Hr.
  assert (Hzb: 0 <= zb (nh_single h) <= 1) by (destruct (nh_single h); simpl; lia).
  unfold decode_frame_m. rewrite Hmg. cbv iota beta zeta.
  set (s := nh_bytes fcs did h ++ B ++ K ++ rest) in *.
  assert (Hs: Zlength s = Zlength (nh_bytes fcs did h) + Zlength B + Zlength K + Zlength rest)
    by (unfold s; rewrite !ff_Zlength_app; lia).
  change (4 - 0) with 4. change (5 - 0) with 5.
  rewrite H4, Hm, Hhs, H8, Hs5, Z.eqb_refl, <- Hlen. fold B in HB.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
  rewrite (proj2 (Z.ltb_ge (Zlength s) (6 - 0 + 3))) by lia.
  rewrite (proj2 (Z.ltb_ge (Zlength s) (Zlength (nh_bytes fcs did h) - 0 + 3))) by lia.
  change (0 =? 0) with true. cbn [negb andb].
  (* the window *)
  assert (Hwd: 0 <= nh_wd h) by (destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ? & _); lia).
  assert (Hwin: negb (zb (nh_single h) =? 1) &&
                (Z.shiftr (byte_at s 5) 3 + ZSTD_WINDOWLOG_ABSOLUTEMIN >? ZSTD_WINDOWLOG_MAX) = false).
  { destruct (nh_single h) eqn:Es; [reflexivity |].
    rewrite H5 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    unfold nh_wlog_ok in Hw. rewrite Es in Hw. destruct Hw as [Hw | Hw]; [discriminate |].
    cbn [zb]. change (0 =? 1) with false. cbn [negb andb].
    rewrite Z.gtb_ltb. apply Z.ltb_ge. unfold ZSTD_WINDOWLOG_ABSOLUTEMIN. lia. }
  rewrite Hwin.
  assert (Hwin0: 0 <= nh_window fcs h /\ (0 < Zlength d -> 1 <= nh_window fcs h)).
  { unfold nh_window. destruct (nh_single h) eqn:Es.
    - split; [lia |]. destruct Hcs as [-> | [_ E]]; [lia | discriminate].
    - assert (1 <= 2 ^ (10 + nh_wd h / 8)).
      { change 1 with (2 ^ 0). apply Z.pow_le_mono_r; [lia |]. pose proof (Z.div_pos (nh_wd h) 8). lia. }
      assert (0 <= 2 ^ (10 + nh_wd h / 8) / 8 * (nh_wd h mod 8)).
      { apply Z.mul_nonneg_nonneg; [apply Z.div_pos | apply Z.mod_pos_bound]; lia. }
      lia. }
  change (get_frame_header_m false s) with (get_frame_header s). rewrite Hg.
  cbn [nf_header_of fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize
       fh_checksumFlag].
  rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge wlim _)) by lia. change (0 =? 0) with true. cbn [negb andb].
  (* the dictionary *)
  assert (Hdd: negb (did =? 0) && negb (did =? dm_id dm) = false).
  { destruct Hdm as [-> | ->]; [reflexivity | rewrite Z.eqb_refl, Bool.andb_false_r; reflexivity]. }
  rewrite Hdd.
  (* the blocks *)
  unfold s at 1 2. rewrite ff_skipn_app by reflexivity.
  rewrite Z.min_l by (unfold nh_max_block; unfold ZSTD_BLOCKSIZE_MAX in Hbmax; lia).
  unfold B. rewrite ff_decode_blocks with (mb := nh_max_block fcs h);
    [| lia | unfold nh_max_block; lia | lia | unfold nh_max_block; lia | exact Hb | rewrite length_app; lia].
  fold B. rewrite app_nil_l. change (nf_content d 0 (nc_blocks c)) with (nf_data d c).
  (* the content size *)
  assert (Hcsz: negb ((if (nh_fcs_flag h =? 0) && negb (nh_single h) then ZSTD_CONTENTSIZE_UNKNOWN else fcs)
                      =? ZSTD_CONTENTSIZE_UNKNOWN) &&
                negb (Zlength (nf_data d c) =?
                      (if (nh_fcs_flag h =? 0) && negb (nh_single h) then ZSTD_CONTENTSIZE_UNKNOWN else fcs))
                = false).
  { destruct Hcs as [-> | [E1 E2]].
    - destruct ((nh_fcs_flag h =? 0) && negb (nh_single h)).
      + rewrite Z.eqb_refl. reflexivity.
      + rewrite Hdl, Z.eqb_refl, Bool.andb_false_r. reflexivity.
    - rewrite E1, E2. cbn [Z.eqb negb andb]. rewrite Z.eqb_refl. reflexivity. }
  rewrite Hcsz.
  (* the checksum, ignored *)
  rewrite Eck; cbn [zb]. change (1 =? 1) with true. cbv iota.
  rewrite (proj2 (Z.ltb_ge _ 4)) by lia.
  rewrite Hig. cbn [negb andb]. reflexivity.
Qed.

(* a frame of new_frame with a Content_Checksum, its last 4 bytes replaced by any 4 bytes, decodes to its
   content when checksums are ignored *)
Theorem nf_series_ignore : forall md dm wlim d fcs maxw did c v,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  nh_wlog_ok (nc_hdr c) ->
  md_magicless md = false -> md_ignore md = true -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  nh_window fcs (nc_hdr c) <= wlim ->
  (did = 0 \/ did = dm_id dm) ->
  (fcs = Zlength d \/ (nh_fcs_flag (nc_hdr c) = 0 /\ nh_single (nc_hdr c) = false)) ->
  nh_checksum (nc_hdr c) = true ->
  decode_series_m md sel_none (Some dm) wlim
    (firstn (Z.to_nat (Zlength (nf_bytes d fcs did c) - 4)) (nf_bytes d fcs did c) ++ le_bytes 4 v) =
  SOk (nf_data d c).
Proof.
  intros md dm wlim d fcs maxw did c v Hok Hd Hf Hdid Hw Hmg Hig Hbm Hwl Hdm Hfcs Hck.
  pose proof Hok as [Hh Hb].
  set (H0 := nh_bytes fcs did (nc_hdr c)).
  set (B := nf_blocks_bytes d 0 (nc_blocks c)).
  assert (HK: Zlength (le_bytes 4 v) = 4) by apply ff_le_bytes_Zlength.
  (* the frame without its Content_Checksum, then the 4 new bytes *)
  assert (E: firstn (Z.to_nat (Zlength (nf_bytes d fcs did c) - 4)) (nf_bytes d fcs did c) ++ le_bytes 4 v =
             H0 ++ B ++ le_bytes 4 v).
  { unfold nf_bytes, nf_checksum. rewrite Hck. fold H0 B. rewrite app_assoc.
    rewrite ff_Zlength_app, ff_le_bytes_Zlength.
    replace (Zlength (H0 ++ B) + Z.of_nat 4 - 4) with (Zlength (H0 ++ B)) by lia.
    rewrite Zlength_correct, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite <- app_assoc. reflexivity. }
  rewrite E. rewrite <- (app_nil_r (H0 ++ B ++ le_bytes 4 v)).
  destruct (ff_nh_read fcs maxw did (nc_hdr c) (B ++ le_bytes 4 v ++ []) Hh Hf Hdid) as (Hm & _).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  assert (Hzb: 0 <= zb (nh_single (nc_hdr c)) <= 1) by (destruct (nh_single (nc_hdr c)); simpl; lia).
  pose proof (ff_Zlength_nonneg B).
  rewrite series_m_frame with (d := dm) (c := nf_data d c).
  - rewrite series_m_nil, app_nil_r. reflexivity.
  - exact Hmg.
  - rewrite !ff_Zlength_app. fold H0 in Hlen. lia.
  - rewrite <- !app_assoc. fold H0 in Hm. rewrite Hm. reflexivity.
  - apply frame_dict_sel_none.
  - rewrite <- !app_assoc. unfold H0, B.
    rewrite (nf_decode_frame_ignore md dm wlim d fcs maxw did c) by auto.
    f_equal. rewrite !ff_Zlength_app. fold H0 B. lia.
Qed.
