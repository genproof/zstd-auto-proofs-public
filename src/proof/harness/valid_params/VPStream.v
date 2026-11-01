(* valid_params's main against the model (plain Coq + VST's list lemmas): from a series as zstd sees it
   (VPModel.vp_written md ws'), what the one-shot claim (oneshot_ok) and the stream claims (stream_claims_m)
   of the API give main's checks: the generic forms of valid_stream's VSModel2 (VSP_content, VSP_zero, VSP_err). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.VSModel2.
Require Export Zstd.proof.harness.valid_params.VPModel.
Require Export Zstd.proof.harness.valid_params.VPParamsW.
Local Open Scope bool_scope.

Lemma VPS_content_written md ws' : vp_written md ws' ->
  flat_map fr_content (map (frec_of ws') (ws_frames ws')) = ws_content ws'.
Proof.
  intros (_ & _ & _ & Ht & _).
  assert (forall fs coff off n, tiles fs off coff n (Zlength (ws_content ws')) -> 0 <= coff ->
            flat_map fr_content (map (frec_of ws') fs) = skipn (Z.to_nat coff) (ws_content ws')).
  { induction fs as [|f fs IH]; simpl; intros coff off n H Hc.
    - destruct H as [_ ->]. rewrite Zlength_correct, Nat2Z.id, skipn_all. reflexivity.
    - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite (IH _ _ _ H6) by lia.
      unfold wi_content, slice. rewrite H2, Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn by lia.
      apply firstn_skipn. }
  apply (H _ 0 0 _ Ht). lia.
Qed.

(* a one-shot decoding of the whole series (no window limit) *)
Lemma VPS_oneshot md ws' : vp_written md ws' -> all_ok no_wlim (ws_frames ws') = true ->
  decode_series_m md sel_none (Some no_dict) no_wlim (ws_bytes ws') = SOk (ws_content ws').
Proof.
  intros Hw Ha. pose proof Hw as (_ & _ & _ & _ & Hs).
  unfold decode_series_m. rewrite Hs, Ha. rewrite VSP_ok_prefix_all by exact Ha.
  f_equal. apply (VPS_content_written md). exact Hw.
Qed.

(* the bytes read are a prefix of the series, whose walk ends (TEnd) or stops at a rejected header (TDetHdr) *)
Lemma VPS_alive md ws' sin : vp_written md ws' -> is_prefix sin (ws_bytes ws') ->
  stream_alive_m md sel_none (Some no_dict) sin.
Proof.
  intros Hw Hp. pose proof Hw as (Hb & _ & _ & _ & Hs).
  exists (ws_bytes ws'). split; [exact Hb|]. split; [exact Hp|].
  rewrite Hs. simpl. destruct (all_ok no_wlim (ws_frames ws')); auto.
Qed.

Lemma VPS_content md ws' wl sin0 sout0 sin sall sout a1 ocap r :
  vp_written md ws' -> is_prefix sin (ws_bytes ws') ->
  stream_claims_m md sel_none (Some no_dict) wl sin0 sout0 sin sall sout a1 ocap r ->
  is_prefix sout (ws_content ws').
Proof.
  intros Hw Hp Hcl. pose proof Hw as (Hb & _ & _ & _ & Hs).
  destruct (Hcl (ws_bytes ws') Hb Hp) as [Hc _].
  rewrite (Hs no_wlim) in Hc. simpl in Hc.
  specialize (Hc ltac:(destruct (all_ok no_wlim (ws_frames ws')); auto)).
  eapply VSP_prefix_trans; [exact Hc|].
  rewrite <- (VPS_content_written md ws' Hw).
  rewrite (VSP_ok_prefix_firstn no_wlim (ws_frames ws')), VSP_map_firstn.
  apply VSP_flat_map_firstn.
Qed.

Lemma VPS_zero md ws' wl sin0 sout0 sin sall sout a1 ocap r :
  vp_written md ws' -> is_prefix sin (ws_bytes ws') ->
  stream_claims_m md sel_none (Some no_dict) wl sin0 sout0 sin sall sout a1 ocap r -> r = 0 ->
  h_at_end (ws_frames ws') (Zlength sin) (Zlength sout) = true.
Proof.
  intros Hw Hp Hcl Hr. pose proof Hw as (Hb & _ & _ & Ht & Hs).
  destruct (Hcl (ws_bytes ws') Hb Hp) as (_ & Hz & _).
  rewrite (Hs no_wlim) in Hz. simpl in Hz.
  destruct (Hz Hr ltac:(destruct (all_ok no_wlim (ws_frames ws')); discriminate)) as (n & Hn & Hin & Hout).
  clear Hz. rewrite length_map in Hn.
  set (op := ok_prefix no_wlim (ws_frames ws')) in *.
  assert (Hop: op = firstn (length op) (ws_frames ws')) by apply VSP_ok_prefix_firstn.
  assert (Hlen: (length op <= length (ws_frames ws'))%nat) by (rewrite Hop, length_firstn; lia).
  set (f := nth (n - 1) (ws_frames ws') winfo0).
  assert (Hf: nth (n - 1) op winfo0 = f).
  { subst f. rewrite Hop at 1. rewrite nth_firstn. destruct (n - 1 <? length op)%nat eqn:E; auto.
    apply Nat.ltb_ge in E. lia. }
  unfold h_at_end. apply existsb_exists. exists f. split.
  - subst f. apply nth_In. lia.
  - rewrite (nth_indep _ _ (frec_of ws' winfo0)) in Hin by (rewrite length_map; lia).
    rewrite map_nth, Hf in Hin. unfold fr_end, frec_of in Hin; simpl in Hin.
    apply andb_true_intro. split; apply Z.eqb_eq; [unfold wi_end; lia|].
    rewrite Hout. rewrite Hop. rewrite VSP_map_firstn, firstn_firstn, Nat.min_l by lia.
    pose proof (VSP_tiles_len ws' (ws_frames ws') 0 0 _ n Ht ltac:(lia) ltac:(lia)) as L. fold f in L. lia.
Qed.

Lemma VPS_err md ws' wl sin0 sout0 sin sall sout a1 r :
  vp_written md ws' -> all_ok wl (ws_frames ws') = true ->
  is_prefix sin (ws_bytes ws') -> is_prefix sall (ws_bytes ws') ->
  stream_claims_m md sel_none (Some no_dict) wl sin0 sout0 sin sall sout a1 None r ->
  is_error_code r = true ->
  forall e, r = 2 ^ 64 - e ->
  e = ZSTD_error_memory_allocation \/ e = ZSTD_error_noForwardProgress_destFull \/
  e = ZSTD_error_noForwardProgress_inputEmpty.
Proof.
  intros Hw Ha Hp Hpa Hcl Herr e He. pose proof Hw as (Hb & _ & _ & _ & Hs).
  destruct (Hcl (ws_bytes ws') Hb Hp) as (_ & _ & _ & Hx).
  rewrite (Hs wl) in Hx. simpl in Hx. rewrite Ha in Hx.
  destruct (Hx Hpa eq_refl Herr e He) as [X | [X | [X | (osz & X & _)]]]; auto. discriminate X.
Qed.

(* ---------- the harness's window checks ---------- *)

Lemma VPS_all_ok_within wl lim fs : lim <= wl ->
  within_oneshot_b fs = true -> forallb (fun f => orb (wi_skippable f) (wi_window f <=? lim)) fs = true ->
  all_ok wl fs = true.
Proof.
  intros Hl. unfold within_oneshot_b, all_ok. induction fs as [|f fs IH]; simpl; auto.
  intros H1 H2. apply andb_prop in H1. apply andb_prop in H2. destruct H1 as [A B]. destruct H2 as [C D].
  rewrite IH by auto. rewrite andb_true_r. unfold wi_rejected. apply negb_true_iff in A. rewrite A.
  destruct (wi_skippable f); [reflexivity|]. simpl in C |- *. apply Z.leb_le in C.
  assert (wi_window f >? wl = false) as -> by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma VPS_all_ok_oneshot ws : wseries_wf ws -> within_oneshot_b (ws_frames ws) = all_ok no_wlim (ws_frames ws).
Proof. apply within_oneshot_all_ok. Qed.

(* API v3.1: streaming claims are under the strict model dmode_w; without a dictionary it walks as the lenient one *)
Lemma VPS_written_w md ws' : vp_written md ws' -> vp_written (dmode_w md) ws'.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). repeat (split; [assumption|]).
  intros wl. rewrite vpw_series_frames. apply H5.
Qed.
