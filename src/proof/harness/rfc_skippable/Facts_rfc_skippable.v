(* The model facts of the law rfc_skippable (harness/rfc_skippable.c), in plain Coq: the series main builds, a list
   of pieces each either a skippable frame of new_skippable or a frame of new_frame (content size given, window up to
   ONE_CALL_WINDOW = 2^31, no Dictionary_ID), decodes in the model of ZSTD_decompress (no dictionary, no window
   limit) to the contents of the frames one after the other: the skippable frames add nothing.  This needs the
   model's skippable_frame_size without the former 32-bit test (fix F5): a skippable frame may hold up to
   2^32 - 1 bytes of user data. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Import Zstd.proof.harness.frames.FModel Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Import Zstd.proof.harness.frames.FKit.
Import ListNotations.
Local Open Scope Z_scope.

(* one piece of the series: a skippable frame (magic variant k, user data u) or a frame of new_frame on the data d
   with the choices c *)
Inductive chunk : Type :=
| CSkip (k: Z) (u: list Z)
| CFrame (d: list Z) (c: nf_choice).

(* what new_skippable and new_frame(d, |d|, |d|, ONE_CALL_WINDOW, 0, ..) promise of their results *)
Definition chunk_ok (x: chunk) : Prop :=
  match x with
  | CSkip k u => 0 <= k < 16 /\ Zlength u <= 4294967295 /\ bytes_ok u
  | CFrame d c => nf_ok (Zlength d) (Zlength d) (2 ^ 31) 0 c /\ bytes_ok d /\ Zlength d < 2 ^ 63
  end.

Definition chunk_bytes (x: chunk) : list Z :=
  match x with
  | CSkip k u => sk_bytes k u
  | CFrame d c => nf_bytes d (Zlength d) 0 c
  end.

(* the content of a piece: nothing for a skippable frame *)
Definition chunk_data (x: chunk) : list Z :=
  match x with
  | CSkip _ _ => []
  | CFrame d c => nf_data d c
  end.

Definition series_of (l: list chunk) : list Z := concat (map chunk_bytes l).
Definition content_of (l: list chunk) : list Z := concat (map chunk_data l).

(* readSkippableFrameSize of a skippable frame of new_skippable (F5: no 32-bit test) *)
Lemma sk_frame_size_f5 : forall k u rest, Zlength u < 2 ^ 32 ->
  skippable_frame_size (sk_bytes k u ++ rest) = Some (8 + Zlength u).
Proof.
  intros k u rest Hu. pose proof (sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold skippable_frame_size. rewrite sk_size_field by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
  replace (Zlength (sk_bytes k u ++ rest) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength u + 8 >? Zlength (sk_bytes k u ++ rest)) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

(* the law's model claim *)
Theorem chunks_decode : forall l, Forall chunk_ok l ->
  decode_series_m md_dflt sel_none (Some no_dict) no_wlim (series_of l) = SOk (content_of l).
Proof.
  induction l as [|x l IH]; intros H; inversion H as [|? ? Hx Hl]; subst.
  - apply series_m_nil.
  - unfold series_of, content_of in *. cbn [map concat]. destruct x as [k u | d c]; cbn [chunk_bytes chunk_data] in *.
    + destruct Hx as (Hk & Hu & Hb).
      rewrite (sk_series_m md_dflt sel_none (Some no_dict) no_wlim k u _ Hk eq_refl
                 (sk_frame_size_f5 k u _ ltac:(lia))).
      exact (IH Hl).
    + destruct Hx as (Hok & Hd & Hn).
      assert (0 <= Zlength d) by (rewrite Zlength_correct; lia).
      rewrite (nf_series_m md_dflt no_dict no_wlim d (Zlength d) (2 ^ 31) 0 c _ Hok Hd);
        [rewrite (IH Hl); reflexivity | lia | lia | | reflexivity | cbn; unfold ZSTD_BLOCKSIZE_MAX; lia | | left; reflexivity | left; reflexivity].
      * apply (nf_wlog_ok (Zlength d) (2 ^ 31) 0); [apply Hok | lia].
      * destruct Hok as [Hh _]. unfold no_wlim. destruct Hh as (_&_&_&_&_&_&_&_&_&_&_&Hw). lia.
Qed.

Lemma series_of_snoc : forall l x, series_of (l ++ [x]) = series_of l ++ chunk_bytes x.
Proof.
  intros. unfold series_of. rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma content_of_snoc : forall l x, content_of (l ++ [x]) = content_of l ++ chunk_data x.
Proof.
  intros. unfold content_of. rewrite map_app, concat_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma chunk_bytes_ok : forall x, chunk_ok x -> bytes_ok (chunk_bytes x).
Proof.
  intros [k u | d c] Hx; cbn [chunk_ok chunk_bytes] in *.
  - destruct Hx as (Hk & _ & Hb). apply sk_bytes_ok; auto.
  - destruct Hx as (Hok & Hd & _). exact (nf_bytes_ok d (Zlength d) (2 ^ 31) 0 c Hok Hd).
Qed.

Lemma series_of_ok : forall l, Forall chunk_ok l -> bytes_ok (series_of l).
Proof.
  induction l as [|x l IH]; intros H; inversion H; subst; unfold series_of in *; cbn [map concat].
  - constructor.
  - apply ff_bytes_ok_app; [apply chunk_bytes_ok; auto | apply IH; auto].
Qed.

