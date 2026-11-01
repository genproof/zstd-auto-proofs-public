(* The model facts of the law rj_content_size (harness/rj_content_size.c), plain Coq.

   The harness builds a frame with new_frame (frames.h) for data d whose Frame_Content_Size field declares fcs, a
   value other than |d|, with no dictionary and a window up to STREAM_WINDOW (2^27); it keeps it only if the frame
   has the field (Frame_Content_Size_flag > 0, or Single_Segment).  zstd certainly refuses such a frame
   (model/Refuse.v: after its last block, the content's size differs from the declared one; the frames kit's
   FRefuse.nf_refused_content_size), unless fcs is 2^64 - 1: that value reads as ZSTD_CONTENTSIZE_UNKNOWN
   (model/Frame.v, as in zstd), the frame then decodes, and the harness ends the run on it.

   One-shot (ZSTD_decompress, md_dflt) and buffered streaming (dmode_w of the default parameters) both read the
   frame alone, with no dictionary selection (sel_none) and the context's dictionary model; the model's walk
   over the frame finds no complete frame and ends refused. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params Zstd.proof.model.Refuse.
Require Export Zstd.proof.harness.frames.FKit.
Require Import Zstd.proof.harness.frames.FRefuse.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ZSTD_decompressFrame's walk over new_frame's blocks, followed by anything, under any block maximum: when it
   succeeds, its output is the data new_frame left (it may fail, e.g. a block larger than the maximum) *)
Lemma cs_decode_blocks : forall (w: bool) d mb bsm wsize st hist bl done out fuel t,
  0 <= done <= Zlength d -> mb <= 131072 -> nf_blocks_ok mb (Zlength d) done bl ->
  match (if w then decode_blocks_w else decode_blocks) fuel st hist (nf_blocks_bytes d done bl ++ t) out bsm wsize
  with
  | Some (o, _) => o = out ++ nf_content d done bl
  | None => True
  end.
Proof.
  intros w d mb bsm wsize st hist bl.
  induction bl as [| b bl IH]; intros done out fuel t Hd Hmb H; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  destruct H as (_ & _ & _ & _ & Hr).
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes nf_content] in *.
  set (rest := nf_blocks_bytes d (done + nb_size b) bl) in *.
  destruct fuel as [| f]; [destruct w; exact I |].
  pose proof (ff_Zlength_nonneg rest). pose proof (ff_Zlength_nonneg t).
  rewrite <- !app_assoc.
  destruct w; cbn [decode_blocks decode_blocks_w]; unfold cblock_size;
    rewrite ff_block_props by lia; cbn [bp_type bp_last bp_origSize];
    rewrite !ff_Zlength_app, Hh3; unfold ZSTD_blockHeaderSize;
    destruct (nb_rle b) eqn:Er; cbn [zb]; cbn [Z.eqb Pos.eqb]; cbv iota.
  all: try (set (x := if nb_size b =? 0 then nb_byte b else byte_at d done) in *;
            change (Zlength [x]) with 1 in *).
  all: try (assert (Hbl: Zlength (slice d done (nb_size b)) = nb_size b) by (apply ff_slice_length; lia);
            rewrite Hbl).
  all: rewrite (proj2 (Z.ltb_ge _ 3)) by lia; rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
  all: try (rewrite ff_slice_mid by (rewrite ?Hh3, ?Hbl; reflexivity)).
  all: rewrite ff_skipn_mid by (rewrite Hh3, ?Hbl; reflexivity).
  all: try (change (byte_at [x] 0) with x; unfold x; rewrite ff_repeat_rle).
  all: match goal with |- context [if ?c then None else _] => destruct c; [exact I |] end.
  all: destruct bl as [| b' bl']; cbn [is_nil zb Z.eqb Pos.eqb]; cbv iota;
    [cbn [nf_content]; rewrite !app_nil_r; reflexivity | destruct Hr as (Hpos & Hr)].
  all: match goal with
       | |- context [decode_blocks_w ?fu ?s0 ?h0 ?r ?o ?b0 ?w0] =>
         pose proof (IH (done + nb_size b) o fu t ltac:(lia) Hmb Hr) as IH'; fold rest in IH';
         destruct (decode_blocks_w fu s0 h0 r o b0 w0) as [[o' k] |]; [rewrite IH', app_assoc; reflexivity | exact I]
       | |- context [decode_blocks ?fu ?s0 ?h0 ?r ?o ?b0 ?w0] =>
         pose proof (IH (done + nb_size b) o fu t ltac:(lia) Hmb Hr) as IH'; fold rest in IH';
         destruct (decode_blocks fu s0 h0 r o b0 w0) as [[o' k] |]; [rewrite IH', app_assoc; reflexivity | exact I]
       end.
Qed.

(* the header zstd reads declares fcs when it has a Frame_Content_Size field *)
Lemma cs_content_size : forall h, (nh_fcs_flag h <> 0 \/ nh_single h = true) ->
  ((nh_fcs_flag h =? 0) && negb (nh_single h)) = false.
Proof.
  intros h [E | E]; [apply Z.eqb_neq in E; rewrite E; reflexivity | rewrite E, Bool.andb_false_r; reflexivity].
Qed.

(* ZSTD_decompressFrame on new_frame's frame declaring fcs, other than |d| and than ZSTD_CONTENTSIZE_UNKNOWN, in a
   Frame_Content_Size field: no claim (FUnk), as the blocks either fail or decode to |d| bytes, which the content
   size check refuses.  The steps up to the blocks are those of FFacts.nf_decode_frame_m. *)
Lemma cs_decode_frame_funk : forall md dm wlim d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  nh_wlog_ok (nc_hdr c) ->
  md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  nh_window fcs (nc_hdr c) <= wlim ->
  (did = 0 \/ did = dm_id dm) ->
  fcs <> ZSTD_CONTENTSIZE_UNKNOWN -> fcs <> Zlength d ->
  (nh_fcs_flag (nc_hdr c) <> 0 \/ nh_single (nc_hdr c) = true) ->
  decode_frame_m md dm wlim (nf_bytes d fcs did c ++ rest) = FUnk.
Proof.
  intros md dm wlim d fcs maxw did c rest Hok Hfcs Hdid Hw Hmg Hbmax Hwl Hdm Hunk Hne Hfield.
  pose proof (nf_get_frame_header d fcs maxw did c rest Hok Hfcs Hdid Hw) as Hg.
  pose proof (nf_data_length d fcs maxw did c Hok) as Hdl.
  destruct Hok as [Hh Hb].
  set (h := nc_hdr c) in *.
  set (B := nf_blocks_bytes d 0 (nc_blocks c)) in *.
  set (K := nf_checksum d c) in *.
  destruct (ff_nh_read fcs maxw did h (B ++ K ++ rest) Hh Hfcs Hdid) as (Hm & H4 & H5 & _).
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts h Hf03 Hbits Hd03) as (Hfb & _ & Hs5 & _ & H8 & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as Hlen.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hz.
  pose proof (ff_Zlength_nonneg d) as Hn.
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as HB.
  pose proof (ff_Zlength_nonneg rest) as Hr.
  assert (HK: Zlength K = 4 * zb (nh_checksum h)) by apply ff_checksum_length.
  assert (Hzb: 0 <= zb (nh_single h) <= 1) by (destruct (nh_single h); simpl; lia).
  assert (Hzc: 0 <= zb (nh_checksum h) <= 1) by (destruct (nh_checksum h); simpl; lia).
  unfold decode_frame_m. rewrite Hmg. cbv iota beta zeta.
  rewrite ff_frame_split in *. fold h B K in Hg |- *.
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
  pose proof (cs_decode_blocks (md_dwin md) d (nh_max_block fcs h) (nh_max_block fcs h) (nh_window fcs h)
                (dm_state dm) (dm_content dm) (nc_blocks c) 0 nil (length (B ++ K ++ rest)) (K ++ rest)
                ltac:(lia) (Z.le_min_r _ _) Hb) as HD.
  fold B in HD.
  destruct ((if md_dwin md then decode_blocks_w else decode_blocks) (length (B ++ K ++ rest)) (dm_state dm)
              (dm_content dm) (B ++ K ++ rest) [] (nh_max_block fcs h) (nh_window fcs h)) as [[o k] |];
    [| reflexivity].
  rewrite HD, app_nil_l. change (nf_content d 0 (nc_blocks c)) with (nf_data d c).
  (* the content size *)
  rewrite (cs_content_size h Hfield), Hdl.
  rewrite (proj2 (Z.eqb_neq _ _) Hunk), (proj2 (Z.eqb_neq _ _) (not_eq_sym Hne)). reflexivity.
Qed.

(* new_frame's frame for d declaring fcs (fcs <> |d|, fcs <> 2^64 - 1) in a Frame_Content_Size field, alone, is a
   series zstd certainly refuses, in any mode with the magic number and a block maximum at least the default's,
   with no dictionary selection and any dictionary model; the model's walk finds no complete frame in it *)
Theorem cs_series_refused : forall md dm d fcs c,
  nf_ok (Zlength d) fcs (2 ^ 27) 0 c -> bytes_ok d -> Zlength d < 2 ^ 63 ->
  0 <= fcs < 2 ^ 64 - 1 -> fcs <> Zlength d ->
  (nh_fcs_flag (nc_hdr c) <> 0 \/ nh_single (nc_hdr c) = true) ->
  md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  series_refused_m md sel_none (Some dm) no_wlim (nf_bytes d fcs 0 c) /\
  fst (series_frames_m md sel_none (Some dm) no_wlim (nf_bytes d fcs 0 c)) = nil.
Proof.
  intros md dm d fcs c Hok Hd Hn Hfcs Hne Hfield Hmg Hbm.
  assert (Hw: nh_wlog_ok (nc_hdr c)) by (eapply nf_wlog_ok; [exact (proj1 Hok) | lia]).
  assert (Hwin: nh_window fcs (nc_hdr c) <= no_wlim).
  { destruct Hok as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwl) _]. unfold no_wlim. lia. }
  assert (Hunk: fcs <> ZSTD_CONTENTSIZE_UNKNOWN) by (unfold ZSTD_CONTENTSIZE_UNKNOWN; lia).
  pose proof (nf_bytes_length d fcs (2 ^ 27) 0 c Hok) as HL.
  assert (HF: decode_frame_m md dm no_wlim (nf_bytes d fcs 0 c) = FUnk).
  { rewrite <- (app_nil_r (nf_bytes d fcs 0 c)).
    eapply cs_decode_frame_funk; eauto; lia. }
  assert (Hm: le_field (nf_bytes d fcs 0 c) 0 4 = ZSTD_MAGICNUMBER).
  { rewrite <- (app_nil_r (nf_bytes d fcs 0 c)). apply nf_magic. }
  split.
  - (* the refusal: the frames kit's FRefuse *)
    exact (nf_refused_content_size md sel_none dm d fcs (2 ^ 27) c Hmg Hd Hok ltac:(lia)
             ltac:(unfold ZSTD_CONTENTSIZE_UNKNOWN; lia) ltac:(lia) Hne Hfield).
  - (* no complete frame: the walk stops at the first one, which the model does not decode *)
    unfold series_frames_m. cbn [walk_m].
    rewrite Hmg. unfold starting_len. cbv iota.
    rewrite (proj2 (Z.ltb_ge _ _)) by (unfold ZSTD_FRAMEHEADERSIZE_PREFIX; lia).
    rewrite Hm. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbn [negb andb].
    rewrite frame_dict_sel_none, HF. reflexivity.
Qed.
