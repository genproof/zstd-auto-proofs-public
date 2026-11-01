(* api_split_invariant (harness/api_split_invariant.c): the series its main builds, and what the format model says
   of it (plain Coq).

   main appends, one at a time, frames of new_frame (any n bytes of its data, content size n declared, no
   dictionary ID, a window of at most max_window) and skippable frames of new_skippable (any of the 16 magic
   numbers, up to 2^32 - 1 bytes of user data).  si_series maxw S C: S is such a series (its bytes) and C its
   content, the frames' contents one after the other.  si_decode: every decoding model that reads Zstandard
   frames (not magicless, blocks of up to ZSTD_BLOCKSIZE_MAX) with a window limit of at least maxw decodes S
   to C, without a DDict set and with the empty dictionary: one-shot decoding (md_dflt, no window limit) as
   much as a stream with the context's parameters (dmode_w, its windowLogMax). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FKit.
Import ListNotations.
Local Open Scope Z_scope.

Inductive si_series (maxw: Z) : list Z -> list Z -> Prop :=
| si_nil : si_series maxw [] []
| si_frame : forall S C d c,
    si_series maxw S C ->
    nf_ok (Zlength d) (Zlength d) maxw 0 c -> bytes_ok d -> Zlength d <= (2 ^ 63 - 1 - 26) / 4 ->
    si_series maxw (S ++ nf_bytes d (Zlength d) 0 c) (C ++ nf_data d c)
| si_skip : forall S C k u,
    si_series maxw S C ->
    0 <= k < 16 -> Zlength u <= 2 ^ 32 - 1 -> bytes_ok u ->
    si_series maxw (S ++ sk_bytes k u) C.

(* a skippable frame of new_skippable is a frame of the model: its size field is |u|, at most 2^32 - 1
   (fix F5 of patch/GENPROOF-PATCH.md: zstd adds the 8 header bytes in 64 bits) *)
Definition si_f5 : Prop := forall k u rest, 0 <= k < 16 -> Zlength u <= 2 ^ 32 - 1 ->
  skippable_frame_size (sk_bytes k u ++ rest) = Some (8 + Zlength u).

Lemma si_sk_size : si_f5.
Proof.
  intros k u rest Hk Hu. pose proof (sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold skippable_frame_size. rewrite sk_size_field by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
  replace (Zlength (sk_bytes k u ++ rest) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength u + 8 >? Zlength (sk_bytes k u ++ rest)) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

(* the decoding models on the series *)
Definition si_decode_stmt : Prop := forall maxw S C md wl,
  si_series maxw S C -> 0 <= maxw < 2 ^ 32 ->
  md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md -> maxw <= wl ->
  bytes_ok S /\ decode_series_m md sel_none (Some no_dict) wl S = SOk C.

(* the series in front of any rest that decodes: its content comes first (the induction behind si_decode) *)
Lemma si_decode_app : si_f5 -> forall maxw S C, si_series maxw S C -> 0 <= maxw < 2 ^ 32 ->
  forall md wl, md_magicless md = false -> ZSTD_BLOCKSIZE_MAX <= md_bmax md -> maxw <= wl ->
  bytes_ok S /\ forall R C', decode_series_m md sel_none (Some no_dict) wl R = SOk C' ->
    decode_series_m md sel_none (Some no_dict) wl (S ++ R) = SOk (C ++ C').
Proof.
  intros F5 maxw S C H Hm md wl Hmg Hbm Hwl.
  induction H as [| S C d c H IH Hok Hd Hn | S C k u H IH Hk Hu Hub].
  - split; [apply Forall_nil | intros R C' HR; exact HR].
  - destruct IH as [Hb IH]. split.
    + apply ff_bytes_ok_app; [exact Hb | eapply nf_bytes_ok; eauto].
    + intros R C' HR. rewrite <- app_assoc, <- app_assoc. apply IH.
      assert (0 <= Zlength d) by (rewrite Zlength_correct; lia).
      assert (Hh := proj1 Hok).
      erewrite nf_series_m; eauto.
      * rewrite HR. reflexivity.
      * cbn in Hn |- *. lia.
      * cbn. lia.
      * eapply nf_wlog_ok; [exact Hh | lia].
      * destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw). lia.
  - destruct IH as [Hb IH]. split.
    + apply ff_bytes_ok_app; [exact Hb | apply sk_bytes_ok; auto].
    + intros R C' HR. rewrite <- app_assoc. apply IH.
      rewrite sk_series_m by auto. destruct (md_dwin md); exact HR.
Qed.

Theorem si_decode : si_f5 -> si_decode_stmt.
Proof.
  intros F5 maxw S C md wl H Hm Hmg Hbm Hwl.
  destruct (si_decode_app F5 maxw S C H Hm md wl Hmg Hbm Hwl) as [Hb HS].
  split; [exact Hb |].
  rewrite <- (app_nil_r S), <- (app_nil_r C). apply HS, series_m_nil.
Qed.
