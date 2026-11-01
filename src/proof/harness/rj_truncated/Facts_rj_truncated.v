(* The model facts of the law rj_truncated (harness/rj_truncated.c), plain Coq.

   The harness builds a frame F with new_frame (frames.h) for data d, with Frame_Content_Size |d| (or no such
   field), no dictionary and a window up to STREAM_WINDOW (2^27), and keeps its first k bytes, 0 < k < |F|.
   - One-shot (ZSTD_decompress, md_dflt, no dictionary): the model certainly refuses the cut frame
     (Refuse.series_refused_m), so its walk ends TUnk and ZSTD_decompress's claims (Spec_api6.oneshot_ok, the
     branch of a refused series) give an error.
   - Streamed (a new context: dmode_w (dmode_of dparams_dflt), no dictionary): the whole frame F extends the
     input, the model decodes it to one frame that ends at |F|, after every byte of the input; so a return of 0,
     which ends a frame of F at the bytes read so far, never happens (FStreamNoEnd.stream_no_end_ext). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.StreamModel Zstd.proof.model.Params Zstd.proof.model.Refuse.
Require Import Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.frames.FKit.
Require Import Zstd.proof.harness.frames.FRefuse.
Local Open Scope Z_scope.

Section Cut.
Variables (d: list Z) (c: nf_choice).
Variable Hok : nf_ok (Zlength d) (Zlength d) (2 ^ 27) 0 c.
Variable Hd : bytes_ok d.
Variable Hn : Zlength d < 2 ^ 64.

(* the frame of new_frame for d: Frame_Content_Size |d| (or none), Dictionary_ID 0 *)
Let F := nf_bytes d (Zlength d) 0 c.

(* a frame of new_frame cut before its end (at least one byte, at least one byte missing) is certainly refused
   by ZSTD_decompress: the cut is in the header, in a block header, in a block's content or in the checksum *)
Lemma trunc_refused : forall k, 0 < k < Zlength F ->
  series_refused_m md_dflt sel_none (Some no_dict) no_wlim (sublist 0 k F).
Proof.
  intros k Hk. rewrite sublist_firstn.
  apply (nf_refused_truncated md_dflt sel_none no_dict d (2 ^ 27) c k); auto; lia.
Qed.

(* ZSTD_decompress on the cut frame returns an error *)
Theorem trunc_oneshot_error : forall k cap r out, 0 < k < Zlength F ->
  oneshot_ok md_dflt (Some no_dict) (sublist 0 k F) cap r out -> is_error_code r = true.
Proof.
  intros k cap r out Hk [_ Hm].
  assert (Hb: bytes_ok (sublist 0 k F)).
  { apply Forall_sublist. eapply nf_bytes_ok; eauto. }
  pose proof (trunc_refused k Hk) as Hr.
  pose proof (series_refused_tunk _ _ _ _ _ Hb Hr) as Ht.
  unfold decode_series_m in Hm.
  destruct (series_frames_m md_dflt sel_none (Some no_dict) no_wlim (sublist 0 k F)) as [l t].
  simpl in Ht. subst t. exact (Hm Hr).
Qed.

(* buffered streaming from a new context decodes the whole frame to one frame that ends at its end *)
Theorem trunc_stream_frames :
  series_frames_m (dmode_w (dmode_of dparams_dflt)) sel_none (Some no_dict) no_wlim F =
  ([{| fr_start := 0; fr_size := Zlength F; fr_content := nf_data d c; fr_skippable := false |}], TEnd).
Proof.
  pose proof (nf_bytes_length d (Zlength d) (2 ^ 27) 0 c Hok) as L. fold F in L.
  pose proof Hok as [Hh _].
  assert (Hdec: decode_frame_m (dmode_w (dmode_of dparams_dflt)) no_dict no_wlim F = FOk (nf_data d c) (Zlength F)).
  { pose proof (nf_decode_frame_m (dmode_w (dmode_of dparams_dflt)) no_dict no_wlim d (Zlength d) (2 ^ 27) 0 c []
      Hok Hd) as H.
    rewrite app_nil_r in H. fold F in H. apply H; clear H.
    - pose proof (Zlength_nonneg d). lia.
    - lia.
    - apply (nf_wlog_ok (Zlength d) (2 ^ 27) 0); [exact Hh | lia].
    - reflexivity.
    - cbv. congruence.
    - unfold no_wlim. destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw). lia.
    - left; reflexivity.
    - left; reflexivity. }
  assert (Hmag: le_field F 0 4 = ZSTD_MAGICNUMBER).
  { pose proof (nf_magic d (Zlength d) 0 c []) as H. rewrite app_nil_r in H. exact H. }
  unfold series_frames_m. cbn [walk_m].
  replace (md_magicless (dmode_w (dmode_of dparams_dflt))) with false by reflexivity.
  replace (Zlength F <? starting_len false) with false
    by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; symmetry; apply Z.ltb_ge; lia).
  rewrite Hmag. cbn [negb andb].
  replace (is_skippable_magic ZSTD_MAGICNUMBER) with false by reflexivity.
  rewrite frame_dict_sel_none, Hdec.
  rewrite Zlength_correct in L |- *. rewrite Nat2Z.id, skipn_all.
  destruct (length F) as [|n] eqn:E; [simpl in L; lia|].
  cbn [walk_m]. reflexivity.
Qed.

End Cut.
