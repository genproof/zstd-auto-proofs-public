(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the series invariant of the loop under any
   selection sel (Params.decode_series_m), with the current dictionary cur (v2's series_inv generalised). *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Pre Zstd.proof.dec.v3.FS.frames.Frames3SeriesRef.
Local Open Scope Z_scope.

Section CM_Multi3Ser_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* what the body claims: v2's oneshot_ok under the selection sel, from the dictionary odm0, and an error on a
   series zstd certainly refuses (Refuse.series_refused_m) *)
Definition oneshot_g (md: dmode) (sel: Z -> option dict_model) (odm0: option dict_model) (s: list Z) (cap r: Z)
    (out: list val) : Prop :=
  (is_error_code r = false -> r <= cap) /\
  match odm0 with
  | None => True
  | Some _ =>
      match decode_series_m md sel odm0 no_wlim s with
      | SOk c => (is_error_code r = false -> r = Zlength c /\ sublist 0 r out = zbytes c) /\
                 (is_error_code r = true -> cap < Zlength c \/ r = err_code ZSTD_error_memory_allocation)
      | SDet => is_error_code r = true
      | SUnk => series_refused_m md sel odm0 no_wlim s -> is_error_code r = true
      end
  end.

Lemma oneshot_g_ok: forall md odm s cap r out, oneshot_g md sel_none odm s cap r out -> oneshot_ok md odm s cap r out.
Proof. intros md odm s cap r out [H1 H2]. split; auto. destruct odm; auto. Qed.

Lemma oneshot_g_sel: forall md sel odm s cap r out, oneshot_g md sel odm s cap r out -> odm <> None ->
  oneshot_sel md sel odm s cap r out.
Proof.
  intros md sel odm s cap r out [H1 H2] Hn. split; auto. destruct odm; [exact H2 | congruence].
Qed.

(* at src offset off with u bytes written in the output cells oc: the series is unknown to the model and zstd does
   not certainly refuse it (a frame the C decoded is not refused, by frame_res3), or it is the content acc already
   written followed by the series of the rest from the current dictionary cur, and it is refused only if the rest
   is (from cur) *)
Definition series_inv (md: dmode) (sel: Z -> option dict_model) (odm0 cur: option dict_model) (s: list Z)
    (off u: Z) (oc: list val) : Prop :=
  match odm0 with
  | None => True
  | Some _ =>
      (decode_series_m md sel odm0 no_wlim s = SUnk /\ ~ series_refused_m md sel odm0 no_wlim s) \/
      exists acc, Zlength acc = u /\ sublist 0 u oc = zbytes acc /\
        decode_series_m md sel odm0 no_wlim s =
          sres_prepend acc (decode_series_m md sel cur no_wlim (sublist off (Zlength s) s)) /\
        (series_refused_m md sel odm0 no_wlim s -> series_refused_m md sel cur no_wlim (sublist off (Zlength s) s))
  end.

Lemma series_inv_init: forall md sel odm s oc, series_inv md sel odm odm s 0 0 oc.
Proof.
  intros. destruct odm as [dm |]; simpl; auto. right. exists nil. split; [reflexivity | split; [| split]].
  - rewrite sublist_nil. reflexivity.
  - rewrite sres_prepend_nil, sublist_same by lia. reflexivity.
  - rewrite sublist_same by lia. auto.
Qed.

Lemma series_inv_skip: forall md sel odm0 cur s off u oc k,
  md_magicless md = false -> md_dwin md = false ->
  bytes_ok s -> 0 <= off -> ZSTD_FRAMEHEADERSIZE_PREFIX <= Zlength s - off ->
  is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = true ->
  skippable_frame_size (sublist off (Zlength s) s) = Some k ->
  series_inv md sel odm0 cur s off u oc -> series_inv md sel odm0 cur s (off + k) u oc.
Proof.
  intros md sel odm0 cur s off u oc k Hmg Hdw Hbs Hoff H5 Hm Hk Hinv.
  pose proof (skippable_frame_size_bound _ _ (bytes_ok_sublist _ _ _ Hbs) Hk) as Hb.
  unfold ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_SKIPPABLEHEADERSIZE in *.
  rewrite Zlength_sublist in Hb by lia.
  destruct odm0 as [dm0 |]; simpl in *; auto.
  destruct Hinv as [? | (acc & Hl & Hs & Hd & Hr)]; [left; auto | right].
  exists acc; split; [auto | split; [auto | split]].
  - rewrite Hd, (decode_seriesS_skip md sel cur no_wlim (sublist off (Zlength s) s) k);
      [| auto | unfold ZSTD_FRAMEHEADERSIZE_PREFIX; rewrite Zlength_sublist by lia; lia | auto | auto | exact Hdw].
    rewrite skipn_sublist_end by lia. reflexivity.
  - intros Hs0. specialize (Hr Hs0).
    rewrite (series_refusedS_skip md sel cur no_wlim (sublist off (Zlength s) s) k) in Hr;
      [| auto | unfold ZSTD_FRAMEHEADERSIZE_PREFIX; rewrite Zlength_sublist by lia; lia | auto | auto | exact Hdw].
    rewrite skipn_sublist_end in Hr by lia. exact Hr.
Qed.

(* a Zstandard frame at off decoded with dm, the dictionary the model selects (frame_dict) *)
Lemma series_inv_frame: forall md sel odm0 cur dm s off u oc oc' r k cap,
  0 <= off -> starting_len (md_magicless md) <= Zlength s - off ->
  (md_magicless md = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_dict (md_magicless md) sel cur (sublist off (Zlength s) s) = Some dm ->
  0 <= u <= cap -> Zlength oc = cap -> Zlength oc' = cap - u ->
  frame_res3 md dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  is_error_code r = false -> 0 <= k <= Zlength s - off ->
  series_inv md sel odm0 cur s off u oc -> series_inv md sel odm0 (Some dm) s (off + k) (u + r) (sublist 0 u oc ++ oc').
Proof.
  intros md sel odm0 cur dm s off u oc oc' r k cap Hoff H5 Hm Hfd Hu Hoc Hoc' Hf He Hk Hinv.
  destruct odm0 as [dm0 |]; simpl in *; auto.
  destruct Hinv as [? | (acc & Hl & Hs & Hd & Hrf)]; [left; auto |].
  rewrite (decode_seriesS_frame md sel cur no_wlim (sublist off (Zlength s) s)) in Hd;
    [| rewrite Zlength_sublist by lia; lia | auto].
  rewrite (series_refusedS_frame md sel cur no_wlim (sublist off (Zlength s) s)) in Hrf;
    [| rewrite Zlength_sublist by lia; lia | auto].
  rewrite Hfd in Hd, Hrf.
  unfold frame_res3 in Hf.
  destruct (decode_frame_m md dm no_wlim (sublist off (Zlength s) s)) as [c sz | | |] eqn:Ef.
  - destruct Hf as [Hf _]. destruct (Hf He) as (Hr & Hc & ->).
    right. exists (acc ++ c). split; [rewrite Zlength_app; lia | split; [| split]].
    + rewrite Z.add_0_l in Hc.
      assert (r <= Zlength oc').
      { assert (Zlength (sublist 0 r oc') = Zlength (zbytes c)) as Hz by congruence.
        rewrite Zlength_map in Hz. subst r. destruct (zle (Zlength c) (Zlength oc')); auto.
        unfold sublist in Hz. simpl skipn in Hz. rewrite !Zlength_correct, firstn_length in Hz.
        rewrite !Zlength_correct. lia. }
      rewrite map_app, <- Hs, <- Hc. list_solve.
    + rewrite Hd, sres_prepend_app, skipn_sublist_end by lia. reflexivity.
    + rewrite skipn_sublist_end in Hrf by lia. exact Hrf.
  - rewrite Hf in He. discriminate.
  - rewrite Hf in He. discriminate.
  - (* the C decoded a frame the model does not: the frame, hence the series, is not refused *)
    left. split; [rewrite Hd; destruct acc; reflexivity |].
    intros Hs0. rewrite (Hf (Hrf Hs0)) in He. discriminate.
Qed.

(* what an error return needs: a series the model decodes does not fit *)
Definition series_err (md: dmode) (sel: Z -> option dict_model) (odm0: option dict_model) (s: list Z) (cap: Z) : Prop :=
  match odm0 with
  | Some _ => match decode_series_m md sel odm0 no_wlim s with SOk c => cap < Zlength c | _ => True end
  | None => True
  end.

Lemma oneshot_err: forall md sel odm0 s cap r out,
  is_error_code r = true -> series_err md sel odm0 s cap -> oneshot_g md sel odm0 s cap r out.
Proof.
  intros. unfold oneshot_g, series_err in *. rewrite H. split; [discriminate |].
  destruct odm0 as [dm |]; auto. destruct (decode_series_m md sel (Some dm) no_wlim s); auto.
  split; [discriminate | auto].
Qed.

Lemma series_err_unk: forall md sel odm0 cur s off u oc cap,
  series_inv md sel odm0 cur s off u oc ->
  (odm0 <> None -> decode_series_m md sel cur no_wlim (sublist off (Zlength s) s) = SUnk) ->
  series_err md sel odm0 s cap.
Proof.
  intros. unfold series_err, series_inv in *. destruct odm0 as [dm |]; auto.
  destruct H as [[-> _] | (acc & _ & _ & -> & _)]; auto. rewrite H0 by discriminate. exact I.
Qed.

Lemma series_err_frame: forall md sel odm0 cur dm s off u oc oc' r k cap,
  0 <= off -> starting_len (md_magicless md) <= Zlength s - off ->
  (md_magicless md = true \/ is_skippable_magic (le_field (sublist off (Zlength s) s) 0 4) = false) ->
  frame_dict (md_magicless md) sel cur (sublist off (Zlength s) s) = Some dm ->
  0 <= u <= cap ->
  frame_res3 md dm (sublist off (Zlength s) s) (cap - u) r oc' 0 k ->
  is_error_code r = true ->
  series_inv md sel odm0 cur s off u oc -> series_err md sel odm0 s cap.
Proof.
  intros md sel odm0 cur dm s off u oc oc' r k cap Hoff H5 Hm Hfd Hu Hf He Hinv.
  pose proof (starting_len_pos (md_magicless md)).
  destruct odm0 as [dm0 |]; simpl in *; auto.
  destruct Hinv as [[-> _] | (acc & Hl & Hs & Hd & _)]; [exact I |]. rewrite Hd.
  rewrite (decode_seriesS_frame md sel cur no_wlim (sublist off (Zlength s) s));
    [| rewrite Zlength_sublist by lia; lia | auto].
  rewrite Hfd.
  unfold frame_res3 in Hf.
  destruct (decode_frame_m md dm no_wlim (sublist off (Zlength s) s)) as [c sz | | |]; simpl; auto.
  destruct Hf as [_ Hf]. specialize (Hf He).
  destruct (decode_series_m md sel (Some dm) no_wlim (skipn (Z.to_nat sz) (sublist off (Zlength s) s))); simpl; auto.
  rewrite !Zlength_app. pose proof (Zlength_nonneg c0). lia.
Qed.

Lemma oneshot_end: forall md sel odm0 cur s off u oc cap,
  series_inv md sel odm0 cur s off u oc -> off = Zlength s -> 0 <= u <= cap -> cap <= 2 ^ 30 ->
  oneshot_g md sel odm0 s cap u oc.
Proof.
  intros md sel odm0 cur s off u oc cap Hinv -> Hu Hc.
  assert (Hne: is_error_code u = false) by (unfold is_error_code; apply Z.ltb_ge; lia).
  unfold oneshot_g, series_inv in *. split; [intros; lia |].
  destruct odm0 as [dm |]; auto.
  destruct Hinv as [[-> Hnr] | (acc & Hl & Hs & Hd & _)]; [intros Hr; contradiction |]. rewrite Hd.
  rewrite sublist_nil.
  rewrite decode_seriesS_short by (rewrite Zlength_nil; pose proof (starting_len_pos (md_magicless md)); lia).
  simpl. rewrite app_nil_r. split; [intros; split; [lia | congruence] | rewrite Hne; discriminate].
Qed.

End CM_Multi3Ser_1.
