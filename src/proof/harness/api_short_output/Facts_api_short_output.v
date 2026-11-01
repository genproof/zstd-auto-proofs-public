(* The model's side of api_short_output (harness/api_short_output.c): a frame of new_frame (frames.h), alone, is
   a series the model decodes to the data new_frame left (nf_data) and whose Zstandard frame has only Raw and RLE
   blocks (model/ErrCodes.v, series_rr_m).  ZSTD_decompress's error codes (Spec_codes.oneshot_codes) then say that
   a capacity below that content is refused with ZSTD_error_dstSize_tooSmall (or a memory error). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params Zstd.proof.model.ErrCodes.
Require Import Zstd.proof.harness.frames.FKit.
Local Open Scope Z_scope.

(* the blocks new_frame writes, followed by anything, are Raw and RLE blocks up to the last one *)
Lemma nf_blocks_rr : forall d mb bl done t, 0 <= done <= Zlength d -> mb <= 131072 ->
  nf_blocks_ok mb (Zlength d) done bl -> blocks_rr (nf_blocks_bytes d done bl ++ t).
Proof.
  intros d mb bl. induction bl as [| b bl IH]; intros done t Hd Hmb H; [destruct H |].
  pose proof (ff_block_bound _ _ _ _ _ Hd Hmb H) as Hs.
  set (body := if nb_rle b then [if nb_size b =? 0 then nb_byte b else byte_at d done]
               else slice d done (nb_size b)).
  assert (Hbody: Zlength body = if nb_rle b then 1 else nb_size b).
  { unfold body. destruct (nb_rle b); [reflexivity | apply ff_slice_length; lia]. }
  assert (Hh3: Zlength (nb_header (is_nil bl) b) = 3) by (unfold nb_header; rewrite ff_le_bytes_Zlength; reflexivity).
  cbn [nf_blocks_bytes]. fold body.
  set (rest := nf_blocks_bytes d (done + nb_size b) bl).
  rewrite <- !app_assoc.
  assert (Hp: block_props_of (nb_header (is_nil bl) b ++ body ++ rest ++ t) =
              {| bp_last := zb (is_nil bl); bp_type := zb (nb_rle b); bp_origSize := nb_size b |})
    by (apply ff_block_props; lia).
  assert (Hc: cblock_size (nb_header (is_nil bl) b ++ body ++ rest ++ t) = Some (Zlength body)).
  { unfold cblock_size. rewrite Hp. cbn [bp_type bp_origSize].
    rewrite !ff_Zlength_app, Hh3. unfold ZSTD_blockHeaderSize.
    pose proof (ff_Zlength_nonneg rest). pose proof (ff_Zlength_nonneg t). pose proof (ff_Zlength_nonneg body).
    rewrite (proj2 (Z.ltb_ge _ 3)) by lia.
    rewrite Hbody. destruct (nb_rle b); reflexivity. }
  assert (Ht: bp_type (block_props_of (nb_header (is_nil bl) b ++ body ++ rest ++ t)) < 2)
    by (rewrite Hp; cbn [bp_type]; destruct (nb_rle b); simpl; lia).
  destruct H as (_ & _ & _ & _ & Hr). destruct bl as [| b' bl'].
  - apply (brr_last _ (Zlength body)); [exact Hc | exact Ht |]. rewrite Hp. reflexivity.
  - apply (brr_more _ (Zlength body)); [exact Hc | exact Ht | rewrite Hp; cbn; discriminate |].
    rewrite ff_skipn_mid by (unfold ZSTD_blockHeaderSize; rewrite Hh3; reflexivity).
    destruct Hr as (_ & Hr). apply (IH (done + nb_size b)); [lia | exact Hmb | exact Hr].
Qed.

(* a frame of new_frame has only Raw and RLE blocks *)
Lemma nf_frame_rr : forall d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> nh_wlog_ok (nc_hdr c) ->
  frame_rr_m md_dflt (nf_bytes d fcs did c ++ rest).
Proof.
  intros d fcs maxw did c rest Hok Hfcs Hdid Hw.
  exists (nf_header_of fcs did (nc_hdr c)). split.
  - change (get_frame_header_m (md_magicless md_dflt) (nf_bytes d fcs did c ++ rest))
      with (get_frame_header (nf_bytes d fcs did c ++ rest)).
    eapply nf_get_frame_header; eauto.
  - cbn [nf_header_of fh_headerSize]. rewrite ff_frame_split.
    rewrite ff_skipn_app by reflexivity.
    destruct Hok as [Hh Hb]. pose proof (ff_Zlength_nonneg d).
    apply (nf_blocks_rr d (nh_max_block fcs (nc_hdr c))); [lia | unfold nh_max_block; lia | exact Hb].
Qed.

(* the law's input: new_frame's frame for data d with Frame_Content_Size n = |d| (or none), no dictionary, a
   window up to ONE_CALL_WINDOW (2^31): ZSTD_decompress's model decodes it to nf_data d c with Raw and RLE blocks
   only *)
Theorem nf_series_rr : forall d c,
  nf_ok (Zlength d) (Zlength d) (2 ^ 31) 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 ->
  series_rr_m md_dflt sel_none no_wlim (Some no_dict) (nf_bytes d (Zlength d) 0 c) (nf_data d c).
Proof.
  intros d c Hok Hd Hn.
  pose proof (ff_Zlength_nonneg d) as Hn0.
  assert (Hw: nh_wlog_ok (nc_hdr c)) by (eapply nf_wlog_ok; [exact (proj1 Hok) | reflexivity]).
  assert (Hwin: nh_window (Zlength d) (nc_hdr c) <= no_wlim).
  { destruct Hok as [Hh _]. destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwm).
    unfold no_wlim. lia. }
  pose proof (nf_bytes_length d (Zlength d) (2 ^ 31) 0 c Hok) as L.
  rewrite <- (app_nil_r (nf_bytes d (Zlength d) 0 c)) at 1.
  rewrite <- (app_nil_r (nf_data d c)).
  apply (srr_frame _ _ _ _ _ no_dict _ (Zlength (nf_bytes d (Zlength d) 0 c))).
  - unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX, md_dflt. cbn [md_magicless]. rewrite app_nil_r. lia.
  - unfold md_dflt. cbn [md_magicless negb andb]. rewrite nf_magic. reflexivity.
  - apply frame_dict_sel_none.
  - eapply nf_decode_frame_m; eauto; [split; [lia | reflexivity] | unfold md_dflt; cbn; lia].
  - eapply nf_frame_rr; eauto; lia.
  - rewrite app_nil_r. rewrite <- (app_nil_r (nf_bytes d (Zlength d) 0 c)) at 2.
    rewrite ff_skipn_app by reflexivity. apply srr_nil.
Qed.
