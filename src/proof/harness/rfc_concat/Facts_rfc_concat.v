(* What the law rfc_concat checks, in the format model (plain Coq, no VST).

   The harness cuts its data into pieces and writes one frame per piece with
   new_frame(data + done, piece, piece, ONE_CALL_WINDOW, 0, &len): the frame nf_bytes d |d| 0 c of the piece d for
   some choices c (nf_ok), the piece then holding nf_data d c (RLE blocks repeat their first byte).  The frames
   are joined one after the other.  ZSTD_decompress decodes them as the series decode_series_m md_dflt sel_none
   (Some no_dict) no_wlim (Spec_api6.oneshot_ok): the series of these frames decodes to the contents of the
   frames one after the other, which is what the data array holds at the end. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Import Zstd.proof.harness.frames.FKit.
Local Open Scope Z_scope.

(* a piece of the data and the choices new_frame made for its frame *)
Definition rc_piece : Type := (list Z * nf_choice)%type.

(* the piece's frame (content size declared, dictionary ID 0) and the content it decodes to *)
Definition rc_frame (p: rc_piece) : list Z := nf_bytes (fst p) (Zlength (fst p)) 0 (snd p).
Definition rc_content (p: rc_piece) : list Z := nf_data (fst p) (snd p).

Definition rc_frames (ps: list rc_piece) : list Z := concat (map rc_frame ps).
Definition rc_contents (ps: list rc_piece) : list Z := concat (map rc_content ps).

(* what new_frame guarantees of a frame it returns, with the window limit ONE_CALL_WINDOW = 2 ^ 31 *)
Definition rc_ok (p: rc_piece) : Prop :=
  nf_ok (Zlength (fst p)) (Zlength (fst p)) (2 ^ 31) 0 (snd p) /\ bytes_ok (fst p) /\ Zlength (fst p) < 2 ^ 64.

Lemma rc_frames_app : forall ps p, rc_frames (ps ++ [p]) = rc_frames ps ++ rc_frame p.
Proof. intros. unfold rc_frames. rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma rc_contents_app : forall ps p, rc_contents (ps ++ [p]) = rc_contents ps ++ rc_content p.
Proof. intros. unfold rc_contents. rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma rc_frames_nil : rc_frames [] = [].
Proof. reflexivity. Qed.

Lemma rc_contents_nil : rc_contents [] = [].
Proof. reflexivity. Qed.

(* a frame of new_frame in front of any rest, as ZSTD_decompress decodes it *)
Lemma rc_series_cons : forall p rest, rc_ok p ->
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim (rc_frame p ++ rest) =
  match decode_series_m md_dflt sel_none (Some no_dict) no_wlim rest with
  | SOk c' => SOk (rc_content p ++ c') | r => r end.
Proof.
  intros [d c] rest (Hok & Hd & Hl). unfold rc_frame, rc_content; cbn [fst snd] in *.
  pose proof (ff_Zlength_nonneg d) as Hn.
  pose proof Hok as [Hh _].
  assert (Hw: nh_window (Zlength d) (nc_hdr c) <= 2 ^ 31)
    by (destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw); exact Hw).
  apply (nf_series_m md_dflt no_dict no_wlim d (Zlength d) (2 ^ 31) 0 c rest Hok Hd); try lia.
  - eapply nf_wlog_ok; [exact Hh | lia].
  - reflexivity.
  - unfold md_dflt; simpl. lia.
  - unfold no_wlim. lia.
Qed.

(* the frames one after the other decode to their contents one after the other *)
Theorem rc_series : forall ps, Forall rc_ok ps ->
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim (rc_frames ps) = SOk (rc_contents ps).
Proof.
  induction ps as [| p ps IH]; intros Hps.
  - apply series_m_nil.
  - inversion Hps as [| ? ? Hp Hps']; subst.
    unfold rc_frames, rc_contents. cbn [map concat].
    rewrite rc_series_cons by exact Hp.
    fold (rc_frames ps). rewrite (IH Hps'). reflexivity.
Qed.

(* sizes and byte values *)
Lemma rc_frames_ok : forall ps, Forall rc_ok ps -> bytes_ok (rc_frames ps).
Proof.
  induction ps as [| p ps IH]; intros Hps.
  - apply Forall_nil.
  - inversion Hps as [| ? ? (Hok & Hd & _) Hps']; subst.
    unfold rc_frames. cbn [map concat]. apply Forall_app. split.
    + apply (nf_bytes_ok _ _ _ _ _ Hok Hd).
    + apply IH. exact Hps'.
Qed.

Lemma rc_contents_ok : forall ps, Forall rc_ok ps -> bytes_ok (rc_contents ps).
Proof.
  induction ps as [| p ps IH]; intros Hps.
  - apply Forall_nil.
  - inversion Hps as [| ? ? (Hok & Hd & _) Hps']; subst.
    unfold rc_contents. cbn [map concat]. apply Forall_app. split.
    + apply (nf_data_ok _ _ _ _ _ Hok Hd).
    + apply IH. exact Hps'.
Qed.

Lemma rc_content_length : forall p, rc_ok p -> Zlength (rc_content p) = Zlength (fst p).
Proof. intros [d c] (Hok & _ & _). apply (nf_data_length _ _ _ _ _ Hok). Qed.

Lemma rc_frame_length : forall p, rc_ok p -> 9 <= Zlength (rc_frame p) <= 26 + 4 * Zlength (fst p).
Proof. intros [d c] (Hok & _ & _). apply (nf_bytes_length _ _ _ _ _ Hok). Qed.
