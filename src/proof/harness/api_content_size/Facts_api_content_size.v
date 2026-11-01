(* What the law api_content_size checks, in the format model (plain Coq, no VST).

   The harness builds an empty frame with new_frame(none, 0, declared, ONE_CALL_WINDOW, 0, &len) (FModel.nf_bytes
   [] declared 0 c) or a skippable frame (FModel.sk_bytes k u), followed by any bytes rest.
   ZSTD_getFrameContentSize returns frame_content_size of the whole input (Spec_api6).  For the frame, the
   harness reads its descriptor byte src[4]: the frame has no Frame_Content_Size field iff its
   Frame_Content_Size_flag (bits 7-6) is 0 and its Single_Segment_flag (bit 5) is 0; then the size is
   ZSTD_CONTENTSIZE_UNKNOWN, else the declared one.  The skippable frame reports 0. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame.
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* the descriptor's bit 5 is Single_Segment_flag *)
Lemma acs_fhd_bit5 : forall h, 0 <= nh_fcs_flag h <= 3 -> In (nh_bits h) [0; 4; 16; 20] ->
  0 <= nh_did_flag h <= 3 ->
  Z.land (nh_fhd h) 32 = 32 * zb (nh_single h).
Proof.
  intros [f sg b df wd] Hf Hb Hd. cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd] in *.
  unfold nh_fhd; cbn [nh_fcs_flag nh_single nh_bits nh_did_flag nh_wd].
  destruct (ff_flag_cases _ Hf) as [-> | [-> | [-> | ->]]];
  destruct (ff_flag_cases _ Hd) as [-> | [-> | [-> | ->]]];
  destruct Hb as [<- | [<- | [<- | [<- | []]]]]; destruct sg; vm_compute; reflexivity.
Qed.

(* the frame of new_frame (no data, dictionary ID 0, window limit ONE_CALL_WINDOW = 2^31), then any bytes:
   its fifth byte is the descriptor, and the content size zstd reports is UNKNOWN exactly when the
   descriptor has neither a Frame_Content_Size_flag nor the Single_Segment_flag, else the declared size *)
Lemma acs_frame : forall fcs c rest,
  nf_ok 0 fcs (2 ^ 31) 0 c -> 0 <= fcs < 2 ^ 64 ->
  nth 4 (nf_bytes [] fcs 0 c ++ rest) 0 = nh_fhd (nc_hdr c) /\
  0 <= nh_fhd (nc_hdr c) < 256 /\
  Z.shiftr (nh_fhd (nc_hdr c)) 6 = nh_fcs_flag (nc_hdr c) /\
  Z.land (nh_fhd (nc_hdr c)) 32 = 32 * zb (nh_single (nc_hdr c)) /\
  frame_content_size (nf_bytes [] fcs 0 c ++ rest) =
    (if (nh_fcs_flag (nc_hdr c) =? 0) && negb (nh_single (nc_hdr c)) then ZSTD_CONTENTSIZE_UNKNOWN else fcs).
Proof.
  intros fcs c rest Hok Hfcs.
  pose proof Hok as [Hh _].
  pose proof Hh as (Hf & _ & _ & _ & _ & Hb & Hd & _).
  destruct (ff_fhd_facts _ Hf Hb Hd) as (Hr & _ & _ & Hs6 & _).
  split; [| split; [exact Hr | split; [exact Hs6 | split; [apply acs_fhd_bit5; assumption |]]]].
  - unfold nf_bytes, nh_bytes. rewrite <- !app_assoc.
    change (le_bytes 4 ZSTD_MAGICNUMBER) with [40; 181; 47; 253]. reflexivity.
  - assert (Hw: nh_wlog_ok (nc_hdr c)) by (apply (nf_wlog_ok fcs (2 ^ 31) 0); [exact Hh | lia]).
    change 0 with (Zlength (@nil Z)) in Hok at 1.
    rewrite (nf_frame_content_size [] fcs (2 ^ 31) 0 c rest Hok Hfcs ltac:(lia) Hw).
    reflexivity.
Qed.

(* a skippable frame of new_skippable, then any bytes: content size 0 *)
Lemma acs_skippable : forall k u rest, 0 <= k < 16 -> Zlength u <= 4294967295 ->
  frame_content_size (sk_bytes k u ++ rest) = 0.
Proof.
  intros k u rest Hk Hu. unfold frame_content_size.
  rewrite (sk_get_frame_header k u rest Hk ltac:(lia)). reflexivity.
Qed.
