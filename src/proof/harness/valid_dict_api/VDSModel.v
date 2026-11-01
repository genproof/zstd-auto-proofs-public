(* vd_stream (harness/valid_dict_api.c) against the model (plain Coq): the delivered bytes, zero returns and
   errors from the claims of ZSTD_decompressStream (API v3: Params.stream_claims_m) on the stream of a series
   written for the dictionary dm, when the context's model decodes the series as dm (vds_desc). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.VSModel2.
Require Export Zstd.proof.harness.valid_stream.VSFacts.
Require Export Zstd.proof.model.Params.
Local Open Scope bool_scope.

Section D.
Variables (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (dm: dict_model) (ws: wseries).
Hypothesis HD: forall wl, series_frames_m md sel cur wl (ws_bytes ws) = series_frames dm wl (ws_bytes ws).
Hypothesis Hsf: series_facts dm ws.

Lemma VDP_alive sin : is_prefix sin (ws_bytes ws) -> stream_alive_m md sel cur sin.
Proof.
  intros Hp. exists (ws_bytes ws). split; [exact (proj1 Hsf)|]. split; [exact Hp|].
  rewrite HD, (VSP_written _ _ no_wlim Hsf). simpl. destruct (all_ok no_wlim (ws_frames ws)); auto.
Qed.

Lemma VDP_content wl sin0 sout0 sin sall sout a1 ocap r :
  is_prefix sin (ws_bytes ws) -> stream_claims_m md sel cur wl sin0 sout0 sin sall sout a1 ocap r ->
  is_prefix sout (ws_content ws).
Proof.
  intros Hp Hcl. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as [Hc _].
  rewrite HD, (VSP_written _ _ no_wlim Hsf) in Hc. simpl in Hc.
  specialize (Hc ltac:(destruct (all_ok no_wlim (ws_frames ws)); auto)).
  eapply VSP_prefix_trans; [exact Hc|].
  rewrite <- (VSP_written_content dm ws Hsf).
  rewrite (VSP_ok_prefix_firstn no_wlim (ws_frames ws)), VSP_map_firstn.
  apply VSP_flat_map_firstn.
Qed.

Lemma VDP_zero wl sin0 sout0 sin sall sout a1 ocap r :
  is_prefix sin (ws_bytes ws) -> stream_claims_m md sel cur wl sin0 sout0 sin sall sout a1 ocap r -> r = 0 ->
  h_at_end (ws_frames ws) (Zlength sin) (Zlength sout) = true.
Proof.
  intros Hp Hcl Hr. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as (_ & Hz & _).
  rewrite HD, (VSP_written _ _ no_wlim Hsf) in Hz. simpl in Hz.
  destruct (Hz Hr ltac:(destruct (all_ok no_wlim (ws_frames ws)); discriminate)) as (n & Hn & Hin & Hout).
  clear Hz. rewrite length_map in Hn.
  set (op := ok_prefix no_wlim (ws_frames ws)) in *.
  assert (Hop: op = firstn (length op) (ws_frames ws)) by apply VSP_ok_prefix_firstn.
  assert (Hlen: (length op <= length (ws_frames ws))%nat) by (rewrite Hop, length_firstn; lia).
  set (f := nth (n - 1) (ws_frames ws) winfo0).
  assert (Hf: nth (n - 1) op winfo0 = f).
  { subst f. rewrite Hop at 1. rewrite nth_firstn. destruct (n - 1 <? length op)%nat eqn:E; auto.
    apply Nat.ltb_ge in E. lia. }
  pose proof Hsf as (_ & _ & _ & _ & _ & Ht & _).
  unfold h_at_end. apply existsb_exists. exists f. split.
  - subst f. apply nth_In. lia.
  - rewrite (nth_indep _ _ (frec_of ws winfo0)) in Hin by (rewrite length_map; lia).
    rewrite map_nth, Hf in Hin. unfold fr_end, frec_of in Hin; simpl in Hin.
    apply andb_true_intro. split; apply Z.eqb_eq; [unfold wi_end; lia|].
    rewrite Hout. rewrite Hop. rewrite VSP_map_firstn, firstn_firstn, Nat.min_l by lia.
    pose proof (VSP_tiles_len ws (ws_frames ws) 0 0 _ n Ht ltac:(lia) ltac:(lia)) as L. fold f in L. lia.
Qed.

Lemma VDP_err sin0 sout0 sin sall sout a1 r :
  within_stream_b (ws_frames ws) = true ->
  is_prefix sin (ws_bytes ws) -> is_prefix sall (ws_bytes ws) ->
  stream_claims_m md sel cur stream_wlim sin0 sout0 sin sall sout a1 None r ->
  is_error_code r = true ->
  forall e, r = 2 ^ 64 - e ->
  e = ZSTD_error_memory_allocation \/ e = ZSTD_error_noForwardProgress_destFull \/
  e = ZSTD_error_noForwardProgress_inputEmpty.
Proof.
  intros Hws Hp Hpa Hcl Herr e He. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as (_ & _ & _ & Hx).
  rewrite !HD, (VSP_written _ _ stream_wlim Hsf) in Hx. simpl in Hx.
  rewrite (VSP_within_stream_all_ok ws Hws) in Hx.
  destruct (Hx Hpa eq_refl Herr e He) as [X | [X | [X | (osz & X & _)]]]; auto. discriminate X.
Qed.

End D.
