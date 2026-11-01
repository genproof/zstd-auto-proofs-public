(* FS3 one-shot frames: one step of ZSTD_decompressMultiFrame's loop in the model with ANY dictionary selection
   sel and current dictionary cur (Params.decode_series_m; fix F4: the frame's DDict found in the set, else the
   current one, which then stays current).  Generalises Frames3Series.v (sel_none).  Plain Coq. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Series.
Local Open Scope Z_scope.

Section CM_Frames3SeriesSel_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the current dictionary after a skippable frame (v3.4: with md_dwin, the frame's magic variant selects) *)
Definition skip_cur (md: dmode) (sel: Z -> option dict_model) (cur: option dict_model) (s: list Z)
    : option dict_model :=
  if md_dwin md then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end else cur.

Lemma skip_cur_nw: forall md sel cur s, md_dwin md = false -> skip_cur md sel cur s = cur.
Proof. intros. unfold skip_cur. rewrite H. reflexivity. Qed.

Lemma walkS_step: forall n md sel cur wlim s off,
  wres (walk_m (S n) md sel cur wlim s off) =
  if Zlength s <? starting_len (md_magicless md) then (if Zlength s =? 0 then SOk nil else SUnk) else
  if (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool then
    match skippable_frame_size s with
    | None => SUnk
    | Some k => wres (walk_m n md sel (skip_cur md sel cur s) wlim (skipn (Z.to_nat k) s) (off + k))
    end
  else
    match frame_dict (md_magicless md) sel cur s with
    | None => SUnk
    | Some d =>
        match decode_frame_m md d wlim s with
        | FOk c k => sres_prepend c (wres (walk_m n md sel (Some d) wlim (skipn (Z.to_nat k) s) (off + k)))
        | FDetHdr | FDetCk => SDet
        | FUnk => SUnk
        end
    end.
Proof.
  intros. cbn [walk_m]. fold (skip_cur md sel cur s).
  destruct (Zlength s <? starting_len (md_magicless md)); [destruct (Zlength s =? 0); reflexivity|].
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool).
  - destruct (skippable_frame_size s); [|reflexivity].
    destruct (walk_m n md sel (skip_cur md sel cur s) wlim _ _) as [l []]; reflexivity.
  - destruct (frame_dict _ sel cur s) as [d|]; [|reflexivity].
    destruct (decode_frame_m md d wlim s); try reflexivity.
    destruct (walk_m n md sel (Some d) wlim _ _) as [l []]; reflexivity.
Qed.

(* the dictionary a frame selects stays selected with itself current *)
Lemma frame_dict_fix: forall mg sel cur s d,
  frame_dict mg sel cur s = Some d -> frame_dict mg sel (Some d) s = Some d.
Proof.
  intros mg sel cur s d. unfold frame_dict.
  destruct (get_frame_header_m mg s) as [|k|h]; try (intros; reflexivity).
  destruct (sel (fh_dictID h)); auto.
Qed.

Lemma walkS_loop_skip: forall md sel wlim s k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = true ->
  skippable_frame_size s = Some k -> Z.to_nat k = 0%nat ->
  forall n cur off, wres (walk_m n md sel cur wlim s off) = SUnk.
Proof.
  intros md sel wlim s k H1 H2 H3 H4 n. induction n; intros cur off; [reflexivity|].
  rewrite walkS_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, H3, H4. apply IHn.
Qed.

Lemma walkS_loop_frame: forall md sel wlim s d c k,
  starting_len (md_magicless md) <= Zlength s ->
  (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false ->
  frame_dict (md_magicless md) sel (Some d) s = Some d ->
  decode_frame_m md d wlim s = FOk c k -> Z.to_nat k = 0%nat ->
  forall n off, wres (walk_m n md sel (Some d) wlim s off) = SUnk.
Proof.
  intros md sel wlim s d c k H1 H2 Hd H3 H4 n. induction n; intros off; [reflexivity|].
  rewrite walkS_step. destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2, Hd, H3, H4. simpl skipn. rewrite IHn. reflexivity.
Qed.

Lemma walkS_fuel: forall n md sel cur wlim s off m off',
  (length s < n)%nat -> (length s < m)%nat ->
  wres (walk_m n md sel cur wlim s off) = wres (walk_m m md sel cur wlim s off').
Proof.
  induction n; intros md sel cur wlim s off m off' Hn Hm; [lia|].
  destruct m as [|m]; [lia|].
  rewrite !walkS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [reflexivity|].
  apply Z.ltb_ge in E.
  destruct ((negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool) eqn:Es.
  - destruct (skippable_frame_size s) as [k|] eqn:Ek; [|reflexivity].
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn. rewrite !(walkS_loop_skip md sel wlim s k); auto.
    + pose proof (skipn3_shorter _ s k E Hk). apply IHn; lia.
  - destruct (frame_dict _ sel cur s) as [d|] eqn:Ed; [|reflexivity].
    destruct (decode_frame_m md d wlim s) as [c k| | |] eqn:Ef; try reflexivity.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
    + rewrite Hk. simpl skipn. apply frame_dict_fix in Ed.
      rewrite !(walkS_loop_frame md sel wlim s d c k); auto.
    + pose proof (skipn3_shorter _ s k E Hk). f_equal. apply IHn; lia.
Qed.

Lemma decode_seriesS_wres: forall md sel cur wlim s,
  decode_series_m md sel cur wlim s = wres (series_frames_m md sel cur wlim s).
Proof. intros. unfold decode_series_m. destruct (series_frames_m md sel cur wlim s) as [l []]; reflexivity. Qed.

Lemma walkS_series: forall n md sel cur wlim s off,
  (length s < n)%nat -> wres (walk_m n md sel cur wlim s off) = decode_series_m md sel cur wlim s.
Proof.
  intros. rewrite decode_seriesS_wres. unfold series_frames_m. apply walkS_fuel; lia.
Qed.

Lemma decode_seriesS_short: forall md sel cur wlim s,
  Zlength s < starting_len (md_magicless md) ->
  decode_series_m md sel cur wlim s = if Zlength s =? 0 then SOk nil else SUnk.
Proof.
  intros. rewrite <- (walkS_series (S (length s)) md sel cur wlim s 0) by lia. rewrite walkS_step.
  apply Z.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma decode_seriesS_skip: forall md sel cur wlim s k,
  md_magicless md = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k -> md_dwin md = false ->
  decode_series_m md sel cur wlim s = decode_series_m md sel cur wlim (skipn (Z.to_nat k) s).
Proof.
  intros md sel cur wlim s k H0 H1 H2 H3 Hdw.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk]; [rewrite Hk; reflexivity|].
  assert (H1': starting_len (md_magicless md) <= Zlength s) by (rewrite H0; exact H1).
  rewrite <- (walkS_series (S (length s)) md sel cur wlim s 0) by lia. rewrite walkS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H0, H2. cbn [negb andb]. rewrite H3, skip_cur_nw by exact Hdw.
  apply walkS_series. pose proof (skipn3_shorter _ s k H1' Hk). lia.
Qed.

Lemma decode_seriesS_skip_bad: forall md sel cur wlim s,
  md_magicless md = false ->
  ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s ->
  is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = None ->
  decode_series_m md sel cur wlim s = SUnk.
Proof.
  intros md sel cur wlim s H0 H1 H2 H3.
  assert (H1': starting_len (md_magicless md) <= Zlength s) by (rewrite H0; exact H1).
  rewrite <- (walkS_series (S (length s)) md sel cur wlim s 0) by lia. rewrite walkS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H0, H2. cbn [negb andb]. rewrite H3. reflexivity.
Qed.

(* a Zstandard frame: decoded with the dictionary the selection gives (else the current one), which then
   becomes current for the rest *)
Lemma decode_seriesS_frame: forall md sel cur wlim s,
  starting_len (md_magicless md) <= Zlength s ->
  (md_magicless md = true \/ is_skippable_magic (le_field s 0 4) = false) ->
  decode_series_m md sel cur wlim s =
    match frame_dict (md_magicless md) sel cur s with
    | None => SUnk
    | Some d =>
        match decode_frame_m md d wlim s with
        | FOk c k => sres_prepend c (decode_series_m md sel (Some d) wlim (skipn (Z.to_nat k) s))
        | FDetHdr | FDetCk => SDet
        | FUnk => SUnk
        end
    end.
Proof.
  intros md sel cur wlim s H1 H2.
  assert (H2': (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool = false)
    by (destruct H2 as [-> | ->]; [reflexivity | destruct (negb _); reflexivity]).
  rewrite <- (walkS_series (S (length s)) md sel cur wlim s 0) by lia. rewrite walkS_step.
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite H2'. destruct (frame_dict _ sel cur s) as [d|] eqn:Ed; [|reflexivity].
  destruct (decode_frame_m md d wlim s) as [c k| | |] eqn:Ef; try reflexivity.
  destruct (Nat.eq_dec (Z.to_nat k) 0) as [Hk|Hk].
  - rewrite Hk. simpl skipn. apply frame_dict_fix in Ed.
    rewrite (walkS_loop_frame md sel wlim s d c k) by auto.
    rewrite <- (walkS_series (S (length s)) md sel (Some d) wlim s 0) by lia.
    rewrite (walkS_loop_frame md sel wlim s d c k) by auto. reflexivity.
  - f_equal. apply walkS_series. pose proof (skipn3_shorter _ s k H1 Hk). lia.
Qed.

End CM_Frames3SeriesSel_1.
