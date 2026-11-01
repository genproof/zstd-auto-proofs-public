(* The model fact of the law rfc_frame (harness/rfc_frame.c), in plain Coq: a frame of new_frame (frames.h) with
   its content size field fcs = n (or no field), Dictionary_ID 0 and a window up to maxw < 2^32 (ONE_CALL_WINDOW =
   2^31), decoded as a series by ZSTD_decompress's model (default mode, no dictionary, no window limit), gives
   exactly its content: the data with each RLE block's part made its repeated byte (nf_data). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FKit.
Local Open Scope Z_scope.

Lemma rfc_frame_series : forall d maxw c,
  nf_ok (Zlength d) (Zlength d) maxw 0 c -> bytes_ok d -> Zlength d < 2 ^ 64 -> maxw < 2 ^ 32 ->
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim (nf_bytes d (Zlength d) 0 c) = SOk (nf_data d c).
Proof.
  intros d maxw c Hok Hd Hn Hm.
  pose proof (proj1 Hok) as Hh. unfold nh_ok in Hh.
  rewrite <- (app_nil_r (nf_bytes d (Zlength d) 0 c)).
  rewrite (nf_series_m md_dflt no_dict no_wlim d (Zlength d) maxw 0 c []);
    [ rewrite series_m_nil, app_nil_r; reflexivity | exact Hok | exact Hd
    | split; [rewrite Zlength_correct; lia | exact Hn] | lia
    | apply (nf_wlog_ok (Zlength d) maxw 0); [apply Hok | exact Hm]
    | reflexivity | simpl; lia | unfold no_wlim; lia | left; reflexivity | left; reflexivity ].
Qed.
