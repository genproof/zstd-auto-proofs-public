(* Facts of the error codes of one-shot decoding (model/ErrCodes.v, Spec_codes.v): a frame the model decodes or
   refuses by its checksum has a parsed header; without a known dictionary and without a selection the claims of
   oneshot_codes are void (ZSTD_decompressDCtx with a dictionary the model does not load). *)
Require Export Zstd.proof.zstd.Spec_codes.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Local Open Scope Z_scope.

(* a frame the model decodes, or refuses by its checksum, has a parsed header *)
Lemma decode_frame_m_hdr: forall md dm wlim s,
  (exists c k, decode_frame_m md dm wlim s = FOk c k) \/ decode_frame_m md dm wlim s = FDetCk ->
  exists h, get_frame_header_m (md_magicless md) s = FH_ok h.
Proof.
  intros md dm wlim s H. unfold decode_frame_m in H.
  destruct (get_frame_header_m (md_magicless md) s) as [| | h] eqn:E; [| | eauto];
    repeat match type of H with context [if ?b then _ else _] => destruct b end;
    destruct H as [(? & ? & ?) | ?]; discriminate.
Qed.

(* without a known dictionary and without a selection, the model decodes no Zstandard frame (Params.frame_dict:
   a parsed header takes the current dictionary): no series is refused by a checksum, and a series decodes only
   to nothing (skippable frames) *)
Lemma frame_dict_none_hdr: forall mg s d h,
  frame_dict mg sel_none None s = Some d -> get_frame_header_m mg s = FH_ok h -> False.
Proof. intros mg s d h Hd Hh. unfold frame_dict in Hd. rewrite Hh in Hd. discriminate. Qed.

Lemma skip_dict_none: forall md s, skip_dict md sel_none None s = None.
Proof. intros. unfold skip_dict. destruct (md_dwin md); reflexivity. Qed.

Lemma series_ck_none: forall md wlim s c, series_ck_m md sel_none wlim None s c -> False.
Proof.
  intros md wlim s c H. remember None as cur eqn:E. revert E.
  induction H as [cur s k c _ _ _ _ IH | cur s d c0 k c _ _ Hd Hf _ _ | cur s d c _ _ Hd Hf _]; intros E; subst cur.
  - apply IH. apply skip_dict_none.
  - destruct (decode_frame_m_hdr md d wlim s) as [h Hh]; [left; eauto |]. exact (frame_dict_none_hdr _ _ _ _ Hd Hh).
  - destruct (decode_frame_m_hdr md d wlim s) as [h Hh]; [right; exact Hf |]. exact (frame_dict_none_hdr _ _ _ _ Hd Hh).
Qed.

Lemma series_rr_none: forall md wlim s c, series_rr_m md sel_none wlim None s c -> c = nil.
Proof.
  intros md wlim s c H. remember None as cur eqn:E. revert E.
  induction H as [cur | cur s k c _ _ _ _ IH | cur s d c0 k c _ _ Hd Hf _ _ _]; intros E; subst cur.
  - reflexivity.
  - apply IH. apply skip_dict_none.
  - destruct (decode_frame_m_hdr md d wlim s) as [h Hh]; [left; eauto |].
    destruct (frame_dict_none_hdr _ _ _ _ Hd Hh).
Qed.

(* without a known dictionary (and no selection) the claims are void *)
Lemma oneshot_codes_none: forall md s cap r, 0 <= cap -> oneshot_codes md sel_none None s cap r.
Proof.
  intros md s cap r Hc. split; intros c H.
  - destruct (series_ck_none _ _ _ _ H).
  - rewrite (series_rr_none _ _ _ _ H). rewrite Zlength_nil. intros Hl. exfalso. lia.
Qed.
