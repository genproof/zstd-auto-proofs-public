(* The model facts of the law rj_reserved_bit (harness/rj_reserved_bit.c), plain Coq.

   The harness builds a frame F with new_frame (frames.h) and sets bit 3 of its byte 4, the Reserved_bit of the
   Frame_Header_Descriptor (rb_frame F).  The bit does not change the header's size (which depends on the
   descriptor's bits 0-1, 5 and 6-7), so the frame is still long enough for its header and a block header, and
   zstd's format model refuses it at its header (FDetHdr): the walk over the series finds no frame and ends with
   TDetHdr, in every mode with magic numbers (ZSTD_decompress's md_dflt, buffered streaming's dmode_w md_dflt),
   with any dictionary selection.  One-shot decoding then returns an error (Spec_api6.oneshot_ok, SDet), and no
   call of streaming reports a frame complete (FStreamNoEnd.stream_no_end). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FKit.
Require Import Lia List Bool.
Import ListNotations.
Local Open Scope Z_scope.

(* F with the Reserved_bit (bit 3 of byte 4) set: the C statement frame[4] |= 8 *)
Definition rb_frame (F: list Z) : list Z := firstn 4 F ++ Z.lor (byte_at F 4) 8 :: skipn 5 F.

(* the Reserved_bit on a descriptor byte: still a byte, the header's size unchanged, the bit read back
   (checked on the 256 bytes) *)
Lemma rb_fhd : forall x, 0 <= x < 256 ->
  0 <= Z.lor x 8 < 256 /\ fhd_header_size (Z.lor x 8) = fhd_header_size x /\ Z.land (Z.lor x 8) 8 <> 0.
Proof.
  intros x Hx.
  assert (Hall: forallb (fun x => (0 <=? Z.lor x 8) && (Z.lor x 8 <? 256) &&
                                  (fhd_header_size (Z.lor x 8) =? fhd_header_size x) &&
                                  negb (Z.land (Z.lor x 8) 8 =? 0))
                  (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  assert (Hin: In x (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia]. }
  specialize (Hall x Hin).
  apply andb_prop in Hall as [Hall H4]. apply andb_prop in Hall as [Hall H3]. apply andb_prop in Hall as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. apply negb_true_iff, Z.eqb_neq in H4.
  auto.
Qed.

Lemma rb_frame_length : forall F, 5 <= Zlength F -> Zlength (rb_frame F) = Zlength F.
Proof.
  intros F HF. unfold rb_frame. rewrite !Zlength_correct in *. rewrite app_length. cbn [length].
  rewrite firstn_length, skipn_length. lia.
Qed.

Lemma rb_frame_ok : forall F, bytes_ok F -> bytes_ok (rb_frame F).
Proof.
  intros F HF. unfold rb_frame, bytes_ok in *.
  pose proof (ff_byte_at_ok F 4 HF) as Hb. unfold is_byte in Hb.
  destruct (rb_fhd _ Hb) as (Hb' & _).
  apply Forall_app. split.
  - rewrite <- (firstn_skipn 4 F) in HF. apply Forall_app in HF. tauto.
  - constructor; [unfold is_byte; lia |].
    rewrite <- (firstn_skipn 5 F) in HF. apply Forall_app in HF. tauto.
Qed.

(* the walk over a Zstandard frame whose descriptor has the Reserved_bit and whose bytes hold its header and a
   block header: refused at the header, before any frame *)
Lemma rb_walk : forall md sel cur wlim off f y T,
  md_magicless md = false -> Z.land y 8 <> 0 ->
  fhd_header_size y + 3 <= 5 + Zlength T -> 4 <= Zlength T ->
  walk_m (S f) md sel cur wlim (40 :: 181 :: 47 :: 253 :: y :: T) off = (nil, TDetHdr).
Proof.
  intros md sel cur wlim off f y T Hmg H8 Hhs HT.
  assert (HL: Zlength (40 :: 181 :: 47 :: 253 :: y :: T) = 5 + Zlength T)
    by (rewrite !Zlength_correct; cbn [length]; lia).
  set (R := 40 :: 181 :: 47 :: 253 :: y :: T) in *.
  assert (Hm: le_field R 0 4 = ZSTD_MAGICNUMBER) by reflexivity.
  assert (H4: byte_at R 4 = y) by reflexivity.
  assert (Hgh: get_frame_header R = FH_err).
  { unfold get_frame_header. cbv zeta. rewrite HL, Hm, H4.
    rewrite (proj2 (Z.ltb_ge _ 5)) by lia. rewrite Z.eqb_refl. cbn [negb].
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    destruct (Z.land y 8 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity]. }
  assert (Hdec: forall dm, decode_frame_m md dm wlim R = FDetHdr).
  { intros dm. unfold decode_frame_m. cbv zeta. rewrite Hmg. change (if false then 4 else 0) with 0.
    rewrite HL. unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hm, Z.eqb_refl. cbn [negb andb].
    change (4 - 0) with 4. rewrite H4.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    destruct (Z.land y 8 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity]. }
  assert (Hfd: exists dm, frame_dict false sel cur R = Some dm).
  { unfold frame_dict, get_frame_header_m. cbn [negb]. rewrite Hgh. destruct cur; eauto. }
  destruct Hfd as [dm Hfd].
  cbn [walk_m]. rewrite Hmg.
  change (starting_len false) with 5. rewrite HL. rewrite (proj2 (Z.ltb_ge _ 5)) by lia.
  rewrite Hm. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbn [negb andb].
  rewrite Hfd, Hdec. reflexivity.
Qed.

(* the walk over the changed frame of new_frame: refused at its header, no frame before *)
Theorem rb_series_frames : forall md sel cur wlim d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> bytes_ok d ->
  md_magicless md = false ->
  series_frames_m md sel cur wlim (rb_frame (nf_bytes d fcs did c)) = (nil, TDetHdr).
Proof.
  intros md sel cur wlim d fcs maxw did c Hok Hfcs Hdid Hd Hmg.
  destruct Hok as [Hh Hb].
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts _ Hf03 Hbits Hd03) as (Hfb & _ & _ & _ & _ & _ & _ & Hhs).
  pose proof (ff_nh_bytes_Zlength _ _ _ _ Hh) as HHl.
  pose proof (ff_field_sizes _ _ _ _ Hh) as Hsz.
  pose proof (ff_fcs_size_single _ _ _ _ Hh) as Hsg.
  pose proof (ff_Zlength_nonneg d) as Hd0.
  pose proof (ff_blocks_bytes_length d _ 0 _ ltac:(lia) Hb) as HBl.
  pose proof (ff_Zlength_nonneg (nf_checksum d c)) as HC.
  destruct (rb_fhd _ Hfb) as (_ & Hrs & H8).
  set (W := if nh_single (nc_hdr c) then [] else [nh_wd (nc_hdr c)]).
  set (T := (W ++ le_bytes (Z.to_nat (nh_did_size (nc_hdr c))) did ++
             le_bytes (Z.to_nat (nh_fcs_size (nc_hdr c))) (nh_fcs_value fcs (nc_hdr c))) ++
            nf_blocks_bytes d 0 (nc_blocks c) ++ nf_checksum d c).
  (* the changed frame: the magic number, the changed descriptor, the rest *)
  assert (HR: rb_frame (nf_bytes d fcs did c) = 40 :: 181 :: 47 :: 253 :: Z.lor (nh_fhd (nc_hdr c)) 8 :: T)
    by reflexivity.
  assert (HT: 5 + Zlength T = Zlength (nh_bytes fcs did (nc_hdr c)) + Zlength (nf_blocks_bytes d 0 (nc_blocks c)) +
                              Zlength (nf_checksum d c)).
  { unfold T, nh_bytes. fold W. rewrite !ff_Zlength_app. change (Zlength (le_bytes 4 ZSTD_MAGICNUMBER)) with 4.
    change (Zlength [nh_fhd (nc_hdr c)]) with 1. lia. }
  unfold series_frames_m. rewrite HR. apply rb_walk; auto.
  - rewrite Hrs, Hhs. lia.
  - destruct (nh_single (nc_hdr c)); simpl zb in *; lia.
Qed.

(* one-shot: zstd certainly refuses the series *)
Corollary rb_decode_series : forall md sel cur wlim d fcs maxw did c,
  nf_ok (Zlength d) fcs maxw did c -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 -> bytes_ok d ->
  md_magicless md = false ->
  decode_series_m md sel cur wlim (rb_frame (nf_bytes d fcs did c)) = SDet.
Proof.
  intros. unfold decode_series_m. erewrite rb_series_frames by eauto. reflexivity.
Qed.
