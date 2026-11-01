(* The frames kit's facts for the laws: a frame of new_frame in a series (FFacts.v, FSeries.v). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.

(* new_frame's frames start with zstd's magic number *)
Lemma nf_magic : forall d fcs did c rest,
  le_field (nf_bytes d fcs did c ++ rest) 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros. unfold nf_bytes, nh_bytes. rewrite <- !app_assoc. reflexivity.
Qed.

(* a frame of new_frame in front of the rest of a series, decoded without a DDict set *)
Theorem nf_series_m : forall md dm wlim d fcs maxw did c rest,
  nf_ok (Zlength d) fcs maxw did c -> bytes_ok d -> 0 <= fcs < 2 ^ 64 -> 0 <= did < 2 ^ 32 ->
  nh_wlog_ok (nc_hdr c) ->
  md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md ->
  nh_window fcs (nc_hdr c) <= wlim ->
  (did = 0 \/ did = dm_id dm) ->
  (fcs = Zlength d \/ (nh_fcs_flag (nc_hdr c) = 0 /\ nh_single (nc_hdr c) = false)) ->
  decode_series_m md sel_none (Some dm) wlim (nf_bytes d fcs did c ++ rest) =
  match decode_series_m md sel_none (Some dm) wlim rest with SOk c' => SOk (nf_data d c ++ c') | r => r end.
Proof.
  intros md dm wlim d fcs maxw did c rest Hok Hd Hf Hdid Hw Hmg Hbm Hwl Hdm Hfcs.
  pose proof (nf_bytes_length d fcs maxw did c Hok) as L.
  apply series_m_frame;
    [exact Hmg | lia | rewrite nf_magic; reflexivity | apply frame_dict_sel_none |
     eapply nf_decode_frame_m; eauto].
Qed.
