(* valid_stream's main against the model (plain Coq): the delivered bytes, zero returns and errors, from
   StreamModel.stream_claims on the stream of a written series and SeriesLemmas. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.VSModel.
Local Open Scope bool_scope.

Lemma VSP_tiles_bounds : forall fs off coff n cn, tiles fs off coff n cn ->
  off <= n /\ coff <= cn /\
  Forall (fun f => off <= wi_start f /\ 0 < wi_size f /\ wi_end f <= n /\ coff <= wi_cstart f /\
                   0 <= wi_csize f /\ wi_cstart f + wi_csize f <= cn) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H.
  - split; [lia|split; [lia|constructor]].
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). apply IH in H6. destruct H6 as (A & B & C).
    unfold wi_end in *. split; [lia|]. split; [lia|]. constructor; [lia|].
    eapply Forall_impl; [|exact C]. simpl. intros g Hg. lia.
Qed.

Lemma VSP_frames_bounds dm ws : series_facts dm ws ->
  Forall (fun f => 0 <= wi_start f /\ 0 < wi_size f /\ wi_end f <= Zlength (ws_bytes ws) /\
                   0 <= wi_cstart f /\ 0 <= wi_csize f /\ wi_cstart f + wi_csize f <= Zlength (ws_content ws))
         (ws_frames ws).
Proof.
  intros (_ & _ & _ & _ & _ & Ht & _). apply VSP_tiles_bounds in Ht. destruct Ht as (_ & _ & Hf).
  eapply Forall_impl; [|exact Hf]. simpl. intros f Hf'. lia.
Qed.

Lemma VSP_ok_prefix_firstn wl fs : ok_prefix wl fs = firstn (length (ok_prefix wl fs)) fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto. destruct (wi_rejected wl f); simpl; auto. f_equal; auto.
Qed.

Lemma VSP_prefix_app (p t: list Z) : is_prefix p (p ++ t).
Proof. unfold is_prefix. rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. apply app_nil_r. Qed.

Lemma VSP_prefix_trans (a b c: list Z) : is_prefix a b -> is_prefix b c -> is_prefix a c.
Proof.
  unfold is_prefix. intros Hab Hbc.
  assert (Hl: (length a <= length b)%nat) by (rewrite <- Hab, length_firstn; lia).
  rewrite <- Hbc in Hab. rewrite firstn_firstn, Nat.min_l in Hab by lia. exact Hab.
Qed.

Lemma VSP_flat_map_firstn {A} (g: A -> list Z) n l : is_prefix (flat_map g (firstn n l)) (flat_map g l).
Proof.
  rewrite <- (firstn_skipn n l) at 2. rewrite flat_map_app. apply VSP_prefix_app.
Qed.

Lemma VSP_map_firstn {A B} (g: A -> B) n l : map g (firstn n l) = firstn n (map g l).
Proof. revert l; induction n; intros [|a l]; simpl; f_equal; auto. Qed.

Lemma VSP_written dm ws wl : series_facts dm ws ->
  series_frames dm wl (ws_bytes ws) =
    (map (frec_of ws) (ok_prefix wl (ws_frames ws)), if all_ok wl (ws_frames ws) then TEnd else TDetHdr).
Proof.
  intros (Hb & Hc & _ & _ & _ & Ht & Hff & _).
  pose proof (VSP_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  unfold series_frames. change (ws_bytes ws) with (skipn (Z.to_nat 0) (ws_bytes ws)) at 1.
  apply (vsh_walk_frames dm ws wl (ws_bytes ws) (Zlength (ws_bytes ws)) (Zlength (ws_content ws))
           TEnd _ 0 0); auto; try lia.
  - eapply Forall_impl; [|exact Hbd]. simpl. intros f Hf. split; [reflexivity|lia].
  - intros fuel Hfuel. rewrite Zlength_correct, Nat2Z.id, skipn_all.
    destruct fuel; [simpl in Hfuel; lia|]. reflexivity.
Qed.

Lemma VSP_written_content dm ws :
  series_facts dm ws -> flat_map fr_content (map (frec_of ws) (ws_frames ws)) = ws_content ws.
Proof.
  intros (_ & _ & _ & _ & _ & Ht & _).
  assert (forall fs coff off n, tiles fs off coff n (Zlength (ws_content ws)) -> 0 <= coff ->
            flat_map fr_content (map (frec_of ws) fs) = skipn (Z.to_nat coff) (ws_content ws)).
  { induction fs as [|f fs IH]; simpl; intros coff off n H Hc.
    - destruct H as [_ ->]. rewrite Zlength_correct, Nat2Z.id, skipn_all. reflexivity.
    - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). rewrite (IH _ _ _ H6) by lia.
      unfold wi_content, slice. rewrite H2, Z2Nat.inj_add, Nat.add_comm, <- skipn_skipn by lia.
      apply firstn_skipn. }
  apply (H _ 0 0 _ Ht). lia.
Qed.

Lemma VSP_within_stream_all_ok ws :
  within_stream_b (ws_frames ws) = true -> all_ok stream_wlim (ws_frames ws) = true.
Proof.
  unfold within_stream_b, within_oneshot_b, all_ok.
  induction (ws_frames ws) as [|f fs IH]; simpl; auto. intros H.
  apply andb_prop in H. destruct H as [H1 H2]. apply andb_prop in H1. apply andb_prop in H2.
  destruct H1 as [Ha Hb]. destruct H2 as [Hc Hd]. rewrite IH by (apply andb_true_intro; split; [exact Hb | exact Hd]).
  rewrite Bool.andb_true_r. unfold wi_rejected. rewrite Bool.negb_true_iff in Hc. rewrite Hc.
  destruct (wi_skippable f) eqn:E; [reflexivity|]. simpl in Ha |- *. unfold stream_wlim.
  apply Z.leb_le in Ha. assert (wi_window f >? 2 ^ 27 + 1 = false) as -> by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma VSP_content ws sin0 sout0 sin sall sout a1 ocap r :
  series_facts no_dict ws -> is_prefix sin (ws_bytes ws) -> stream_claims sin0 sout0 sin sall sout a1 ocap r ->
  is_prefix sout (ws_content ws).
Proof.
  intros Hsf Hp Hcl. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as [Hc _].
  rewrite (VSP_written _ _ no_wlim Hsf) in Hc. simpl in Hc.
  specialize (Hc ltac:(destruct (all_ok no_wlim (ws_frames ws)); auto)).
  eapply VSP_prefix_trans; [exact Hc|].
  rewrite <- (VSP_written_content no_dict ws Hsf).
  rewrite (VSP_ok_prefix_firstn no_wlim (ws_frames ws)), VSP_map_firstn.
  apply VSP_flat_map_firstn.
Qed.

Lemma VSP_wi_content_len ws f : 0 <= wi_cstart f -> 0 <= wi_csize f ->
  wi_cstart f + wi_csize f <= Zlength (ws_content ws) -> Zlength (wi_content ws f) = wi_csize f.
Proof.
  intros. unfold wi_content, slice. rewrite Zlength_correct, length_firstn, length_skipn.
  rewrite Zlength_correct in H1. lia.
Qed.

(* the content of the first n frames ends where frame n-1 ends *)
Lemma VSP_tiles_len ws : forall fs off coff N n,
  tiles fs off coff N (Zlength (ws_content ws)) -> 0 <= coff -> (1 <= n <= length fs)%nat ->
  coff + Zlength (flat_map fr_content (firstn n (map (frec_of ws) fs))) =
    wi_cstart (nth (n - 1) fs winfo0) + wi_csize (nth (n - 1) fs winfo0).
Proof.
  induction fs as [|f fs IH]; intros off coff N n Ht Hc Hn; simpl in Hn; [lia|].
  pose proof (VSP_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hb).
  inversion Hb as [|? ? Hbf _]; subst.
  simpl in Ht. destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6).
  destruct n as [|n]; [lia|]. simpl firstn. simpl flat_map. rewrite Zlength_app.
  change (fr_content (frec_of ws f)) with (wi_content ws f). rewrite VSP_wi_content_len by lia.
  destruct n as [|n].
  - simpl. rewrite Zlength_nil. lia.
  - specialize (IH _ _ _ (S n) H6 ltac:(lia) ltac:(lia)). rewrite Nat.sub_succ, Nat.sub_0_r in IH.
    replace (S (S n) - 1)%nat with (S n) by lia. simpl nth. lia.
Qed.

Lemma VSP_zero ws sin0 sout0 sin sall sout a1 ocap r :
  series_facts no_dict ws -> is_prefix sin (ws_bytes ws) -> stream_claims sin0 sout0 sin sall sout a1 ocap r -> r = 0 ->
  h_at_end (ws_frames ws) (Zlength sin) (Zlength sout) = true.
Proof.
  intros Hsf Hp Hcl Hr. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as (_ & Hz & _).
  rewrite (VSP_written _ _ no_wlim Hsf) in Hz. simpl in Hz.
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

Lemma VSP_err ws sin0 sout0 sin sall sout a1 r :
  series_facts no_dict ws -> wseries_wf ws -> within_stream_b (ws_frames ws) = true ->
  is_prefix sin (ws_bytes ws) -> is_prefix sall (ws_bytes ws) -> stream_claims sin0 sout0 sin sall sout a1 None r ->
  is_error_code r = true ->
  forall e, r = 2 ^ 64 - e ->
  e = ZSTD_error_memory_allocation \/ e = ZSTD_error_noForwardProgress_destFull \/
  e = ZSTD_error_noForwardProgress_inputEmpty.
Proof.
  intros Hsf Hwf Hws Hp Hpa Hcl Herr e He. destruct (Hcl (ws_bytes ws) (proj1 Hsf) Hp) as (_ & _ & _ & Hx).
  rewrite (VSP_written _ _ stream_wlim Hsf) in Hx. simpl in Hx.
  rewrite (VSP_within_stream_all_ok ws Hws) in Hx.
  destruct (Hx Hpa eq_refl Herr e He) as [X | [X | [X | (osz & X & _)]]]; auto. discriminate X.
Qed.

(* ---------- the hint (API v2.4): the claims on the series cut at main's `end` (or one byte beyond) ---------- *)

Lemma VSP_h_end_prefix : forall fs off coff n cn ipos got, tiles fs off coff n cn ->
  exists j cE, tiles (firstn j fs) off coff (h_end fs ipos got n) cE /\ h_end fs ipos got n <= n /\
    h_end (firstn j fs) ipos got (h_end fs ipos got n) = h_end fs ipos got n /\
    (ipos < h_end fs ipos got n \/ got < cE \/ (h_end fs ipos got n = n /\ cE = cn)).
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn ipos got Ht.
  - exists O, coff. simpl. destruct Ht as [-> ->]. split; [auto|]. split; [lia|]. split; [reflexivity|]. auto.
  - destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6).
    pose proof (vsh_tiles_bounds _ _ _ _ _ H6) as (Hb & _).
    destruct ((wi_end f >? ipos) || ((wi_end f =? ipos) && (got <? wi_cstart f + wi_csize f))) eqn:E.
    + exists 1%nat, (coff + wi_csize f). simpl. rewrite E. unfold wi_end in *.
      split; [repeat split; auto; lia|]. split; [lia|]. split; [reflexivity|].
      apply Bool.orb_true_iff in E. destruct E as [E|E].
      * left. apply Z.gtb_lt in E. lia.
      * right; left. apply Bool.andb_true_iff in E as [_ E]. apply Z.ltb_lt in E. lia.
    + destruct (IH _ _ _ _ ipos got H6) as (j & cE & Hj1 & Hj2 & Hj3 & Hj4).
      exists (S j), cE. simpl. rewrite E. split; [repeat split; auto|]. split; [lia|]. split; [exact Hj3|exact Hj4].
Qed.

Lemma VSP_cur_end_le : forall fl ip got c d B, Forall (fun f => fr_end f <= B) fl -> d <= B ->
  cur_end_aux fl ip got c d <= B.
Proof.
  induction fl as [|f fl IH]; simpl; intros ip got c d B HF Hd; auto.
  inversion HF; subst. destruct (_ || _)%bool; auto.
Qed.

Lemma VSP_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  unfold all_ok. induction fs as [|f fs IH]; simpl; auto. intros H.
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.negb_true_iff in H1. rewrite H1. f_equal; auto.
Qed.

Lemma VSP_ok_prefix_Forall (P: winfo -> Prop) wl fs : Forall P fs -> Forall P (ok_prefix wl fs).
Proof. intros H. rewrite VSP_ok_prefix_firstn. apply vsh_Forall_firstn. exact H. Qed.

Lemma VSP_content_len ws : forall fs off coff n cn, tiles fs off coff n cn ->
  Forall (fun f => Zlength (wi_content ws f) = wi_csize f) fs ->
  Zlength (flat_map fr_content (map (frec_of ws) fs)) = cn - coff.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn Ht Hc.
  - destruct Ht as [_ ->]. rewrite Zlength_nil. lia.
  - destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6). inversion Hc as [|? ? Hcf Hc']; subst.
    rewrite Zlength_app. change (fr_content (frec_of ws f)) with (wi_content ws f).
    rewrite (IH _ _ _ _ H6 Hc'). lia.
Qed.

Lemma VSP_prefix_len (p l: list Z) : is_prefix p l -> Zlength p <= Zlength l.
Proof.
  unfold is_prefix. intros H. rewrite <- H, !Zlength_correct, length_firstn. lia.
Qed.

Lemma VSP_bytes_firstn (l: list Z) k tl : bytes_ok l -> bytes_ok tl -> bytes_ok (firstn k l ++ tl).
Proof. unfold bytes_ok. intros H1 H2. apply Forall_app. split; [apply vsh_Forall_firstn|]; auto. Qed.

Lemma VSP_hint ws ipos got ip2 sout sall a1 ocap r :
  series_facts no_dict ws -> 0 <= ipos <= ip2 -> ip2 <= Zlength (ws_bytes ws) ->
  0 <= got <= Zlength (ws_content ws) -> got <= Zlength sout -> 0 <= a1 <= 1 ->
  (ipos < Zlength (ws_bytes ws) \/ got < Zlength (ws_content ws)) ->
  stream_claims (sublist 0 ipos (ws_bytes ws)) (sublist 0 got (ws_content ws)) (sublist 0 ip2 (ws_bytes ws))
    sall sout a1 ocap r ->
  is_error_code r = false -> 0 < r ->
  r <= Z.max 1 (h_end (ws_frames ws) ip2 (Zlength sout) (Zlength (ws_bytes ws)) - ip2).
Proof.
  intros Hsf Hi Hi2 Hg Hgs Ha1 Hinv Hcl Herr Hr.
  pose proof Hsf as (Hb & Hc & _ & _ & _ & Ht & Hff & _).
  set (fs := ws_frames ws) in *. set (B := ws_bytes ws) in *. set (N := Zlength B) in *.
  set (got2 := Zlength sout) in *.
  destruct (VSP_h_end_prefix fs 0 0 N (Zlength (ws_content ws)) ip2 got2 Ht) as (j & cE & Hj1 & HEN & Hj3 & Hj4).
  set (E := h_end fs ip2 got2 N) in *.
  assert (HiE : ip2 <= E) by (apply VS_h_end_ge; lia).
  pose proof (vsh_tiles_bounds _ _ _ _ _ Hj1) as (_ & _ & Hbd).
  pose proof (vsh_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd0).
  assert (Hcl0 : Forall (fun f => Zlength (wi_content ws f) = wi_csize f) (firstn j fs)).
  { apply vsh_Forall_firstn. pose proof (vsh_tiles_csize _ _ _ _ _ Ht) as Hcs.
    rewrite Forall_forall in Hbd0, Hcs |- *. intros f Hf. destruct (Hbd0 f Hf) as (_ & _ & _ & Hc1 & Hc2).
    specialize (Hcs f Hf). apply VSP_wi_content_len; lia. }
  assert (HlE : Zlength (firstn (Z.to_nat E) B) = E).
  { rewrite Zlength_correct, length_firstn. unfold N in HEN. rewrite Zlength_correct in HEN. lia. }
  assert (HlenE : length (firstn (Z.to_nat E) B) = Z.to_nat E) by (rewrite Zlength_correct in HlE; lia).
  assert (Hwalk : forall tl T, (forall fuel, (length tl < fuel)%nat -> walk fuel no_dict no_wlim tl E = (nil, T)) ->
     series_frames no_dict no_wlim (firstn (Z.to_nat E) B ++ tl) =
     (map (frec_of ws) (ok_prefix no_wlim (firstn j fs)), if all_ok no_wlim (firstn j fs) then T else TDetHdr)).
  { intros tl T HT. set (s := firstn (Z.to_nat E) B ++ tl).
    assert (HfE : firstn (Z.to_nat E) s = firstn (Z.to_nat E) B).
    { unfold s. rewrite firstn_app, HlenE, Nat.sub_diag. simpl. rewrite app_nil_r, firstn_firstn, Nat.min_id.
      reflexivity. }
    assert (HsE : skipn (Z.to_nat E) s = tl).
    { unfold s. rewrite skipn_app, HlenE, Nat.sub_diag, skipn_all2 by lia. reflexivity. }
    unfold series_frames. change s with (skipn (Z.to_nat 0) s) at 1.
    apply (vsh_walk_frames no_dict ws no_wlim s E cE T _ 0 0); auto; try lia.
    - apply vsh_Forall_firstn; auto.
    - eapply Forall_impl; [|exact Hbd]. simpl. intros f (Hf1 & Hf0 & Hf2 & _). split.
      + unfold wi_bytes, slice. apply (vsh_firstn_agree _ _ (Z.to_nat E)); [exact HfE|].
        unfold wi_end in Hf2. lia.
      + unfold s. rewrite Zlength_app, HlE. pose proof (Zlength_nonneg tl). lia.
    - intros fuel Hfuel. rewrite HsE in Hfuel |- *. apply HT; auto.
    }
  assert (Hpin : forall tl, is_prefix (sublist 0 ip2 B) (firstn (Z.to_nat E) B ++ tl)).
  { intros tl. unfold is_prefix. rewrite sublist_firstn, length_firstn.
    replace (Nat.min (Z.to_nat ip2) (length B)) with (Z.to_nat ip2)
      by (unfold N in Hi2; rewrite Zlength_correct in Hi2; lia).
    rewrite firstn_app, HlenE. replace (Z.to_nat ip2 - Z.to_nat E)%nat with O by lia. simpl.
    rewrite app_nil_r, firstn_firstn, Nat.min_l by lia. reflexivity. }
  assert (Hce : cur_end_aux (map (frec_of ws) (ok_prefix no_wlim (firstn j fs))) ip2 got2 0
                  (h_end (firstn j fs) ip2 got2 E) = h_end (firstn j fs) ip2 got2 E)
    by (eapply vsh_cur_end_h_end; eauto).
  rewrite Hj3 in Hce.
  assert (Hlsin : Zlength (sublist 0 ip2 B) = ip2) by (rewrite Zlength_sublist by lia; lia).
  assert (Hlsin0 : Zlength (sublist 0 ipos B) = ipos) by (rewrite Zlength_sublist by lia; lia).
  assert (Hnil : forall fuel, (length (@nil Z) < fuel)%nat -> walk fuel no_dict no_wlim nil E = (nil, TEnd)).
  { intros [|fuel] Hf; [simpl in Hf; lia|]. reflexivity. }
  destruct (Z_lt_ge_dec ipos E) as [HA | HB].
  - (* the call started before `end`: s = the series up to `end` *)
    specialize (Hcl (firstn (Z.to_nat E) B ++ nil) (VSP_bytes_firstn B _ nil Hb (Forall_nil _)) (Hpin nil)).
    rewrite (Hwalk nil TEnd Hnil) in Hcl. cbn [fst snd] in Hcl. destruct Hcl as (_ & _ & Hh & _).
    assert (Ht' : (if all_ok no_wlim (firstn j fs) then TEnd else TDetHdr) = TEnd \/
                  (if all_ok no_wlim (firstn j fs) then TEnd else TDetHdr) = TDetHdr) by (destruct (all_ok _ _); auto).
    rewrite app_nil_r, HlE, Hlsin, Hlsin0 in Hh. fold got2 in Hh. unfold cur_end in Hh. rewrite Hce in Hh.
    specialize (Hh Ht' Herr Hr ltac:(left; exact HA)).
    destruct (_ || _)%bool; lia.
  - assert (ipos = E /\ ip2 = E) as [-> HE2] by lia.
    destruct (all_ok no_wlim (firstn j fs)) eqn:Eok.
    + (* everything up to `end` read, its frames all accepted: the content of the frame ending there is not all
         delivered before the call *)
      specialize (Hcl (firstn (Z.to_nat E) B ++ nil) (VSP_bytes_firstn B _ nil Hb (Forall_nil _)) (Hpin nil)).
      rewrite (Hwalk nil TEnd Hnil) in Hcl. cbn [fst snd] in Hcl. destruct Hcl as (_ & _ & Hh & _).
      rewrite VSP_ok_prefix_all in Hh by exact Eok.
      rewrite app_nil_r, HlE, Hlsin, Hlsin0, (VSP_content_len ws _ _ _ _ _ Hj1 Hcl0) in Hh.
      fold got2 in Hh. unfold cur_end in Hh. rewrite VSP_ok_prefix_all in Hce by exact Eok. rewrite Hce in Hh.
      rewrite Zlength_sublist in Hh by lia.
      assert (got < cE).
      { destruct Hj4 as [X | [X | [X1 X2]]]; [lia | lia |].
        fold E in X1. destruct Hinv as [Y | Y]; [unfold N in *; lia | lia]. }
      specialize (Hh (or_introl eq_refl) Herr Hr ltac:(right; lia)).
      destruct (_ || _)%bool; lia.
    + (* a frame up to `end` is rejected at its header: s = the series up to `end` and one more byte *)
      assert (Hone : forall fuel, (length [0] < fuel)%nat -> walk fuel no_dict no_wlim [0] E = (nil, TUnk)).
      { intros [|fuel] Hf; [simpl in Hf; lia|]. reflexivity. }
      assert (Hb0 : bytes_ok [0]) by (unfold bytes_ok; repeat constructor; unfold is_byte; lia).
      specialize (Hcl (firstn (Z.to_nat E) B ++ [0]) (VSP_bytes_firstn B _ [0] Hb Hb0) (Hpin [0])).
      rewrite (Hwalk [0] TUnk Hone) in Hcl. cbn [fst snd] in Hcl. destruct Hcl as (_ & _ & Hh & _).
      rewrite Zlength_app, HlE, Hlsin, Hlsin0 in Hh. change (Zlength [0]) with 1 in Hh. fold got2 in Hh.
      specialize (Hh (or_intror eq_refl) Herr Hr ltac:(left; lia)).
      assert (Hle : cur_end (map (frec_of ws) (ok_prefix no_wlim (firstn j fs))) ip2 got2 (E + 1) <= E + 1).
      { apply VSP_cur_end_le; [|lia]. apply Forall_map. apply VSP_ok_prefix_Forall.
        eapply Forall_impl; [|exact Hbd]. simpl. intros f Hf. unfold fr_end, frec_of; simpl. unfold wi_end in Hf. lia. }
      destruct (_ || _)%bool; lia.
Qed.

(* a call that ends with the whole series read and delivered, started before that, returns no positive hint *)
Lemma VSP_hint_end ws ipos got sout sall ocap r :
  series_facts no_dict ws -> 0 <= ipos <= Zlength (ws_bytes ws) -> 0 <= got <= Zlength (ws_content ws) ->
  Zlength sout = Zlength (ws_content ws) ->
  (ipos < Zlength (ws_bytes ws) \/ got < Zlength (ws_content ws)) ->
  stream_claims (sublist 0 ipos (ws_bytes ws)) (sublist 0 got (ws_content ws)) (ws_bytes ws) sall sout 0 ocap r ->
  is_error_code r = false -> 0 < r -> False.
Proof.
  intros Hsf Hi Hg Hso Hinv Hcl Herr Hr.
  pose proof Hsf as (Hb & _ & _ & _ & _ & Ht & _).
  assert (Hp: is_prefix (ws_bytes ws) (ws_bytes ws)) by (unfold is_prefix; rewrite firstn_all; reflexivity).
  destruct (Hcl (ws_bytes ws) Hb Hp) as (Hc & _ & Hh & _).
  rewrite (VSP_written _ _ no_wlim Hsf) in Hc, Hh. cbn [fst snd] in Hc, Hh.
  assert (Ht' : (if all_ok no_wlim (ws_frames ws) then TEnd else TDetHdr) = TEnd \/
                (if all_ok no_wlim (ws_frames ws) then TEnd else TDetHdr) = TDetHdr) by (destruct (all_ok _ _); auto).
  specialize (Hc Ht').
  assert (HC0: is_prefix (flat_map fr_content (map (frec_of ws) (ok_prefix no_wlim (ws_frames ws)))) (ws_content ws)).
  { rewrite <- (VSP_written_content no_dict ws Hsf).
    rewrite (VSP_ok_prefix_firstn no_wlim (ws_frames ws)), VSP_map_firstn. apply VSP_flat_map_firstn. }
  apply VSP_prefix_len in Hc. apply VSP_prefix_len in HC0.
  rewrite !Zlength_sublist in Hh by lia. rewrite Hso in Hh.
  specialize (Hh Ht' Herr Hr ltac:(destruct Hinv; [left | right]; lia)).
  pose proof (VSP_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  assert (Hle : cur_end (map (frec_of ws) (ok_prefix no_wlim (ws_frames ws))) (Zlength (ws_bytes ws))
                  (Zlength (ws_content ws)) (Zlength (ws_bytes ws)) <= Zlength (ws_bytes ws)).
  { apply VSP_cur_end_le; [|lia]. apply Forall_map. apply VSP_ok_prefix_Forall.
    eapply Forall_impl; [|exact Hbd]. simpl. intros f Hf. unfold fr_end, frec_of; simpl. unfold wi_end in Hf. lia. }
  rewrite Z.ltb_irrefl in Hh. simpl orb in Hh.
  destruct (Zlength (ws_content ws) <? _) eqn:X; [apply Z.ltb_lt in X; lia|]. lia.
Qed.
