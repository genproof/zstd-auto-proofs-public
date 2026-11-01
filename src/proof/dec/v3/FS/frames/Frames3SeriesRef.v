(* FS3 one-shot frames: one step of ZSTD_decompressMultiFrame's loop for a series zstd certainly refuses
   (Refuse.series_refused_m), as Frames3SeriesSel.v does for decode_series_m: the refusal of a series is the refusal
   of its rest after a skippable frame or a frame the model decodes, the refusal of the frame itself when the model
   does not decode it (FUnk), and a non-empty rest shorter than a frame's first bytes.  Plain Coq. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3SeriesSel.
Require Export Zstd.proof.model.Refuse.
Local Open Scope Z_scope.

Section CM_Frames3SeriesRef_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma wrefS_step: forall n md sel cur wlim s,
  walk_refused (S n) md sel cur wlim s <->
  if Zlength s <? starting_len (md_magicless md) then Zlength s <> 0 else
  if (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool then
    match skippable_frame_size s with
    | None => False
    | Some k => walk_refused n md sel (skip_cur md sel cur s) wlim (skipn (Z.to_nat k) s)
    end
  else
    match frame_dict (md_magicless md) sel cur s with
    | None => False
    | Some d =>
        match decode_frame_m md d wlim s with
        | FOk _ k => walk_refused n md sel (Some d) wlim (skipn (Z.to_nat k) s)
        | FUnk => frame_refused_m md d wlim s
        | _ => False
        end
    end.
Proof. intros. cbn [walk_refused]. fold (skip_cur md sel cur s). reflexivity. Qed.

Lemma wrefS_loop_skip: forall md sel wlim s k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = true ->
  skippable_frame_size s = Some k -> Z.to_nat k = 0%nat ->
  forall n cur, ~ walk_refused n md sel cur wlim s.
Proof.
  intros md sel wlim s k H1 H2 H3 H4 n. induction n; intros cur; [simpl; tauto |].
  rewrite wrefS_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia |].
  rewrite H2, H3, H4. apply IHn.
Qed.

Lemma wrefS_loop_frame: forall md sel wlim s d c k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false ->
  frame_dict (md_magicless md) sel (Some d) s = Some d ->
  decode_frame_m md d wlim s = FOk c k -> Z.to_nat k = 0%nat ->
  forall n, ~ walk_refused n md sel (Some d) wlim s.
Proof.
  intros md sel wlim s d c k H1 H2 Hd H3 H4 n. induction n; [simpl; tauto |].
  rewrite wrefS_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia |].
  rewrite H2, Hd, H3, H4. exact IHn.
Qed.

Lemma wrefS_fuel: forall n md sel cur wlim s m,
  (length s < n)%nat -> (length s < m)%nat ->
  (walk_refused n md sel cur wlim s <-> walk_refused m md sel cur wlim s).
Proof.
  induction n; intros md sel cur wlim s m Hn Hm; [lia |].
  destruct m as [| m]; [lia |].
  rewrite !wrefS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [reflexivity |].
  apply Z.ltb_ge in E.
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool) eqn:Es.
  - destruct (skippable_frame_size s) as [k |] eqn:Ek; [| reflexivity].
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk | Hk].
    + rewrite Hk. simpl skipn.
      split; intro H; exfalso; eapply wrefS_loop_skip; eauto.
    + pose proof (skipn3_shorter _ s k E Hk). apply IHn; lia.
  - destruct (frame_dict _ sel cur s) as [d |] eqn:Ed; [| reflexivity].
    destruct (decode_frame_m md d wlim s) as [c k | | |] eqn:Ef; try reflexivity.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk | Hk].
    + rewrite Hk. simpl skipn. apply frame_dict_fix in Ed.
      split; intro H; exfalso; eapply wrefS_loop_frame; eauto.
    + pose proof (skipn3_shorter _ s k E Hk). apply IHn; lia.
Qed.

Lemma wrefS_series: forall n md sel cur wlim s,
  (length s < n)%nat -> (walk_refused n md sel cur wlim s <-> series_refused_m md sel cur wlim s).
Proof. intros. unfold series_refused_m. apply wrefS_fuel; lia. Qed.

(* a refused walk ends TUnk, at any fuel and offset *)
Lemma wref_tunk: forall n md sel cur wlim s off,
  walk_refused n md sel cur wlim s -> snd (walk_m n md sel cur wlim s off) = TUnk.
Proof.
  induction n; intros md sel cur wlim s off H; [destruct H |].
  cbn [walk_refused] in H. cbn [walk_m].
  destruct (Zlength s <? starting_len (md_magicless md)).
  - destruct (Zlength s =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
  - destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool).
    + destruct (skippable_frame_size s) as [k |]; [| destruct H].
      match goal with |- context [walk_m n md sel ?c wlim ?s' ?o'] =>
        pose proof (IHn md sel c wlim s' o' H) as IH; destruct (walk_m n md sel c wlim s' o') end.
      exact IH.
    + destruct (frame_dict _ sel cur s) as [d |]; [| destruct H].
      destruct (decode_frame_m md d wlim s) as [c k | | |]; try destruct H; [| reflexivity].
      match goal with |- context [walk_m n md sel ?c' wlim ?s' ?o'] =>
        pose proof (IHn md sel c' wlim s' o' H) as IH; destruct (walk_m n md sel c' wlim s' o') end.
      exact IH.
Qed.

(* a refused series is one the model does not decide (SUnk) *)
Lemma series_refused_sunk: forall md sel cur wlim s,
  series_refused_m md sel cur wlim s -> decode_series_m md sel cur wlim s = SUnk.
Proof.
  intros md sel cur wlim s H. unfold decode_series_m, series_frames_m.
  pose proof (wref_tunk _ md sel cur wlim s 0 H) as E.
  destruct (walk_m (S (length s)) md sel cur wlim s 0) as [l t]. simpl in E. subst t. reflexivity.
Qed.

Lemma series_refusedS_short: forall md sel cur wlim s,
  Zlength s < starting_len (md_magicless md) ->
  (series_refused_m md sel cur wlim s <-> Zlength s <> 0).
Proof.
  intros. unfold series_refused_m. rewrite wrefS_step. apply Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma series_refusedS_skip: forall md sel cur wlim s k,
  md_magicless md = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k -> md_dwin md = false ->
  (series_refused_m md sel cur wlim s <-> series_refused_m md sel cur wlim (skipn (Z.to_nat k) s)).
Proof.
  intros md sel cur wlim s k H0 H1 H2 H3 Hdw.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk | Hk]; [rewrite Hk; reflexivity |].
  assert (H1': starting_len (md_magicless md) <= Zlength s) by (rewrite H0; exact H1).
  unfold series_refused_m at 1. rewrite wrefS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia |].
  rewrite H0, H2. cbn [negb andb]. rewrite H3, skip_cur_nw by exact Hdw.
  apply wrefS_series. pose proof (skipn3_shorter _ s k H1' Hk). lia.
Qed.

(* a Zstandard frame: the series is refused when the frame is (the model does not decode it) or, after a frame the
   model decodes, when the rest is, from the frame's dictionary *)
Lemma series_refusedS_frame: forall md sel cur wlim s,
  starting_len (md_magicless md) <= Zlength s ->
  (md_magicless md = true \/ is_skippable_magic (le_field s 0 4) = false) ->
  (series_refused_m md sel cur wlim s <->
    match frame_dict (md_magicless md) sel cur s with
    | None => False
    | Some d =>
        match decode_frame_m md d wlim s with
        | FOk _ k => series_refused_m md sel (Some d) wlim (skipn (Z.to_nat k) s)
        | FUnk => frame_refused_m md d wlim s
        | _ => False
        end
    end).
Proof.
  intros md sel cur wlim s H1 H2.
  assert (H2': (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false)
    by (destruct H2 as [-> | ->]; [reflexivity | destruct (negb _); reflexivity]).
  unfold series_refused_m at 1. rewrite wrefS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia |].
  rewrite H2'. destruct (frame_dict _ sel cur s) as [d |] eqn:Ed; [| reflexivity].
  destruct (decode_frame_m md d wlim s) as [c k | | |] eqn:Ef; try reflexivity.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk | Hk].
  - rewrite Hk. simpl skipn. apply frame_dict_fix in Ed.
    split; intro H; exfalso.
    + eapply wrefS_loop_frame; eauto.
    + unfold series_refused_m in H. eapply wrefS_loop_frame; eauto.
  - apply wrefS_series. pose proof (skipn3_shorter _ s k H1 Hk). lia.
Qed.

End CM_Frames3SeriesRef_1.
