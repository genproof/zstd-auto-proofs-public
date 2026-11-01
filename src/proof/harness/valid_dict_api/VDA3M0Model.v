(* valid_dict_api main: mode 0's model fact (plain Coq): the DDict set describes the series. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.WTopSpecs_valid_dict_api.
Require Import Zstd.proof.harness.valid_dict_api.VDA3Defs.

(* ---------- md_dflt walks as Series.walk (ParamsDflt.pd_walk, repeated here) ---------- *)

Lemma m0_fh_bmax (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  unfold ZSTD_BLOCKSIZE_MAX; lia.
Qed.

Lemma m0_pd_frame (dm: dict_model) (wl: Z) (s: list Z) : decode_frame_m md_dflt dm wl s = decode_frame dm wl s.
Proof.
  unfold decode_frame_m, decode_frame, get_frame_header_m. simpl md_magicless. simpl md_ignore. simpl md_bmax.
  cbv beta iota zeta. rewrite !Z.sub_0_r.
  destruct (get_frame_header s) as [|k|h] eqn:E; try reflexivity.
  cbn [negb andb]. rewrite (Z.min_l _ _ (m0_fh_bmax s h E)). reflexivity.
Qed.

Lemma m0_pd_walk (n: nat) (dm: dict_model) (wl: Z) (s: list Z) (off: Z) :
  walk_m n md_dflt sel_none (Some dm) wl s off = walk n dm wl s off.
Proof.
  revert s off. induction n as [|n IH]; intros s off; [reflexivity|].
  simpl. unfold starting_len.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [reflexivity|].
  destruct (is_skippable_magic (le_field s 0 4)).
  - destruct (skippable_frame_size s); [|reflexivity]. rewrite IH. reflexivity.
  - assert (Hd: frame_dict false sel_none (Some dm) s = Some dm).
    { unfold frame_dict, sel_none. destruct (get_frame_header_m false s); reflexivity. }
    rewrite Hd, m0_pd_frame. destruct (decode_frame dm wl s); try reflexivity. rewrite IH. reflexivity.
Qed.

(* ---------- helpers (as in writer/SeriesLemmas.v) ---------- *)

Lemma m0_le_field_app : forall (a b: list Z) p k,
  0 <= p -> 0 <= k -> p + k <= Zlength a -> le_field (a ++ b) p k = le_field a p k.
Proof.
  intros a b p k Hp Hk H. unfold le_field, slice. f_equal.
  rewrite Zlength_correct in H. rewrite skipn_app, firstn_app, length_skipn.
  replace (Z.to_nat k - (length a - Z.to_nat p))%nat with 0%nat by lia.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma m0_tiles_bounds : forall fs off coff n cn, tiles fs off coff n cn ->
  off <= n /\ coff <= cn /\
  Forall (fun f => off <= wi_start f /\ 0 < wi_size f /\ wi_end f <= n /\ coff <= wi_cstart f /\
                   wi_cstart f + wi_csize f <= cn) fs.
Proof.
  induction fs as [|f fs IH]; simpl; intros off coff n cn H.
  - split; [lia|split; [lia|constructor]].
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). apply IH in H6. destruct H6 as (A & B & C).
    unfold wi_end in *. split; [lia|]. split; [lia|]. constructor; [lia|].
    eapply Forall_impl; [|exact C]. simpl. intros g Hg. lia.
Qed.

Lemma m0_decode_frame_not_unk : forall dm wl s, decode_frame dm wl s <> FUnk ->
  9 <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros dm wl s H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
  apply Z.ltb_ge in E1. apply Bool.negb_false_iff, Z.eqb_eq in E2.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in E1. split; [lia|exact E2].
Qed.

Lemma m0_walk_S : forall f dm wlim s off, walk (S f) dm wlim s off =
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match decode_frame dm wlim s with
        | FOk c k =>
            let '(l, t) := walk f dm wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
        | FDetHdr => (nil, TDetHdr)
        | FDetCk => (nil, TDetCk)
        | FUnk => (nil, TUnk)
        end.
Proof. reflexivity. Qed.

Lemma m0_walk_m_S : forall f md sel cur wlim s off, md_magicless md = false ->
  walk_m (S f) md sel cur wlim s off =
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk_m f md sel
                             (if md_dwin md
                              then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end
                              else cur) wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match frame_dict false sel cur s with
        | None => (nil, TUnk)
        | Some d =>
            match decode_frame_m md d wlim s with
            | FOk c k =>
                let '(l, t) := walk_m f md sel (Some d) wlim (skipn (Z.to_nat k) s) (off + k) in
                ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
            | FDetHdr => (nil, TDetHdr)
            | FDetCk => (nil, TDetCk)
            | FUnk => (nil, TUnk)
            end
        end.
Proof. intros f md sel cur wlim s off H. simpl. rewrite H. reflexivity. Qed.

(* decode_frame_m does not use the dictionary when the header does not parse *)
Lemma m0_dict_irrel md d1 d2 wl s :
  (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  decode_frame_m md d1 wl s = decode_frame_m md d2 wl s.
Proof.
  intros H. unfold decode_frame_m.
  destruct (get_frame_header_m (md_magicless md) s) eqn:E.
  - reflexivity.
  - reflexivity.
  - exfalso. eapply H. reflexivity.
Qed.

(* ---------- the walk with a selection that gives dm at every frame of a written series ---------- *)

Lemma m0_walk : forall md sel dm ws wl fs off coff n cn fuel cur,
  md_magicless md = false ->
  Forall (fun f => wi_skippable f = false -> wi_big f = false -> sel (wi_did f) = Some dm) fs ->
  tiles fs off coff n cn -> 0 <= off -> n = Zlength (ws_bytes ws) ->
  Forall (frame_facts dm ws) fs ->
  walk_m fuel md sel_none (Some dm) wl (skipn (Z.to_nat off) (ws_bytes ws)) off =
    walk fuel dm wl (skipn (Z.to_nat off) (ws_bytes ws)) off ->
  walk_m fuel md sel cur wl (skipn (Z.to_nat off) (ws_bytes ws)) off =
    walk_m fuel md sel_none (Some dm) wl (skipn (Z.to_nat off) (ws_bytes ws)) off.
Proof.
  intros md sel dm ws wl fs. induction fs as [|f fs IH];
    intros off coff n cn fuel cur Hmg Hsel Ht Hoff Hn Hff Heq.
  - simpl in Ht. destruct Ht as [-> ->]. subst n.
    rewrite Zlength_correct, Nat2Z.id, skipn_all.
    destruct fuel as [|fuel]; [reflexivity|]. rewrite !m0_walk_m_S by exact Hmg. reflexivity.
  - pose proof (m0_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
    inversion Hbd as [|? ? Hbf _]; subst. clear Hbd.
    simpl in Ht. destruct Ht as (Hst & Hcst & Hsz & Hcsz & Hskc & Ht).
    inversion Hff as [|? ? Hf Hff']; subst. inversion Hsel as [|? ? Hself Hsel']; subst.
    set (S := ws_bytes ws) in *.
    set (fb := wi_bytes ws f) in *.
    set (r := skipn (Z.to_nat (wi_start f + wi_size f)) S).
    assert (Hfb : firstn (Z.to_nat (wi_size f)) (skipn (Z.to_nat (wi_start f)) S) = fb) by reflexivity.
    assert (Hlenfb : length fb = Z.to_nat (wi_size f)).
    { subst fb. rewrite <- Hfb, length_firstn, length_skipn. unfold wi_end in Hbf.
      rewrite Zlength_correct in Hbf. lia. }
    assert (Hs : skipn (Z.to_nat (wi_start f)) S = fb ++ r).
    { subst r. rewrite <- Hfb, Z2Nat.inj_add by lia. rewrite Nat.add_comm, <- skipn_skipn.
      symmetry. apply firstn_skipn. }
    assert (Hskr : skipn (Z.to_nat (wi_size f)) (fb ++ r) = r).
    { rewrite skipn_app, Hlenfb, Nat.sub_diag, skipn_all2 by lia. reflexivity. }
    destruct Hf as (_ & _ & _ & Hgfh & _ & _ & _ & Hsk & Hdec). fold S fb in Hsk, Hdec, Hgfh.
    rewrite Hs in Hgfh, Heq |- *.
    destruct fuel as [|fuel]; [reflexivity|].
    rewrite m0_walk_S in Heq. rewrite (m0_walk_m_S fuel md sel_none (Some dm)) in Heq |- * by exact Hmg.
    rewrite (m0_walk_m_S fuel md sel cur) by exact Hmg.
    assert (IHr : forall cur',
      walk_m fuel md sel_none (Some dm) wl r (wi_start f + wi_size f) =
        walk fuel dm wl r (wi_start f + wi_size f) ->
      walk_m fuel md sel cur' wl r (wi_start f + wi_size f) =
        walk_m fuel md sel_none (Some dm) wl r (wi_start f + wi_size f)).
    { intros cur' H. subst r. apply (IH _ (wi_cstart f + wi_csize f) (Zlength S) cn); auto; lia. }
    destruct (wi_skippable f) eqn:Eskip.
    + destruct (Hsk eq_refl) as (_ & Hl8 & Hmag & Hsfs & _).
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as Hlt.
      { apply Z.ltb_ge. rewrite Zlength_correct, length_app. rewrite Zlength_correct in Hl8.
        unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_FRAMEHEADERSIZE_PREFIX in *. lia. }
      rewrite Hlt in Heq |- *.
      rewrite m0_le_field_app, Hmag, Hsfs, Hskr in Heq |- *
        by (unfold ZSTD_SKIPPABLEHEADERSIZE in Hl8; lia).
      (* v3.4: under md_dwin the skippable frame may select by its variant; with sel_none it keeps Some dm *)
      match goal with |- context [walk_m fuel md sel_none ?c wl r _] =>
        replace c with (Some dm) by (destruct (md_dwin md); reflexivity) end.
      match type of Heq with context [walk_m fuel md sel_none ?c wl r _] =>
        replace c with (Some dm) in Heq by (destruct (md_dwin md); reflexivity) end.
      destruct (walk_m fuel md sel_none (Some dm) wl r (wi_start f + wi_size f)) as [l1 t1] eqn:E1.
      destruct (walk fuel dm wl r (wi_start f + wi_size f)) as [l2 t2] eqn:E2.
      injection Heq as Hl Htt. subst l2 t2.
      match goal with |- context [walk_m fuel md sel ?c wl r _] =>
        rewrite (IHr c) by (rewrite ?E1, ?E2; reflexivity) end.
      rewrite ?E1. reflexivity.
    + destruct (Hdec eq_refl) as (Hd & _ & _). specialize (Hd wl r).
      assert (decode_frame dm wl (fb ++ r) <> FUnk) as Hnu
        by (rewrite Hd; destruct (wi_rejected wl f); discriminate).
      apply m0_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as Hlt.
      { apply Z.ltb_ge. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
      rewrite Hlt, Hmag in Heq |- *. change (is_skippable_magic ZSTD_MAGICNUMBER) with false in Heq |- *.
      cbv iota beta in Heq |- *.
      assert (Hfd1 : frame_dict false sel_none (Some dm) (fb ++ r) = Some dm).
      { unfold frame_dict, sel_none. destruct (get_frame_header_m false (fb ++ r)); reflexivity. }
      assert (Hfd2 : exists d, frame_dict false sel cur (fb ++ r) = Some d /\
                               decode_frame_m md d wl (fb ++ r) = decode_frame_m md dm wl (fb ++ r)).
      { unfold frame_dict. change (get_frame_header_m false (fb ++ r)) with (get_frame_header (fb ++ r)).
        rewrite Hgfh. destruct (wi_big f) eqn:Ebig.
        - exists (match cur with Some d => d | None => no_dict end). split; [destruct cur; reflexivity|].
          apply m0_dict_irrel. rewrite Hmg.
          change (get_frame_header_m false (fb ++ r)) with (get_frame_header (fb ++ r)).
          rewrite Hgfh. discriminate.
        - assert (Hid : fh_dictID (wi_header f) = wi_did f) by (unfold wi_header; rewrite Eskip; reflexivity).
          rewrite Hid, (Hself eq_refl eq_refl). eexists; split; reflexivity. }
      destruct Hfd2 as (d & Hd1 & Hd2).
      rewrite Hfd1 in Heq |- *. rewrite Hd1, Hd2.
      destruct (decode_frame_m md dm wl (fb ++ r)) as [c k| | |] eqn:Ed; try reflexivity.
      rewrite Hd in Heq.
      destruct (walk_m fuel md sel_none (Some dm) wl (skipn (Z.to_nat k) (fb ++ r)) (wi_start f + k))
        as [l1 t1] eqn:E1.
      destruct (wi_rejected wl f); [discriminate|].
      rewrite Hskr in Heq.
      destruct (walk fuel dm wl r (wi_start f + wi_size f)) as [l2 t2] eqn:E2.
      injection Heq as Hk Hc Hl Htt. subst k l2 t2. rewrite Hskr in E1 |- *.
      rewrite (IHr (Some d)) by (rewrite ?E1, ?E2; reflexivity). rewrite ?E1. reflexivity.
Qed.

(* ---------- the DDict set ---------- *)

Lemma m0_model_auto wd : dict_facts wd -> dict_auto (wd_bytes wd) = Some (wd_model wd).
Proof.
  intros (_ & _ & Ha & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); congruence.
Qed.

Lemma m0_ids (l: list (val * ddict_st)) wds :
  Forall dict_facts wds -> map (fun e => dd_bytes (snd e)) l = map wd_bytes wds ->
  map (fun e => dd_id (snd e)) l = map wd_id wds.
Proof.
  revert l. induction wds as [|w wds IH]; intros [|e l] Hf Hm; simpl in Hm; try discriminate; [reflexivity|].
  inversion Hf as [|? ? Hw Hf']; subst. injection Hm as Hb Hm. simpl. f_equal.
  - unfold dd_id. rewrite Hb. apply Hw.
  - apply IH; auto.
Qed.

Lemma m0_distinct (l: list Z) : NoDup l -> ids_distinct l = true.
Proof.
  induction 1 as [|x l Hx Hnd IH]; [reflexivity|]. simpl. rewrite IH, andb_true_r.
  destruct (existsb (Z.eqb x) l) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as (y & Hy & Hxy). apply Z.eqb_eq in Hxy. subst y. contradiction.
Qed.

Lemma m0_forallb (l: list (val * ddict_st)) wds :
  Forall dict_facts wds -> Forall (fun w => wd_id w <> 0) wds ->
  map (fun e => dd_bytes (snd e)) l = map wd_bytes wds ->
  forallb (fun e => (negb (dd_id (snd e) =? 0) &&
                    match dict_auto (dd_bytes (snd e)) with Some _ => true | None => false end)%bool) l = true.
Proof.
  revert l. induction wds as [|w wds IH]; intros [|e l] Hf Hz Hm; simpl in Hm; try discriminate; [reflexivity|].
  inversion Hf as [|? ? Hw Hf']; subst. inversion Hz as [|? ? Hwz Hz']; subst. injection Hm as Hb Hm.
  simpl. rewrite IH by auto. rewrite andb_true_r. unfold dd_id. rewrite Hb.
  destruct Hw as (_ & _ & Ha & _ & _ & Hid & _). rewrite Hid.
  destruct (dict_auto (wd_bytes w)); [|congruence].
  destruct (wd_id w =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma m0_find (l: list (val * ddict_st)) wds wd :
  Forall dict_facts wds -> NoDup (map wd_id wds) -> In wd wds ->
  map (fun e => dd_bytes (snd e)) l = map wd_bytes wds ->
  exists e, find (fun e => dd_id (snd e) =? wd_id wd) l = Some e /\ dd_bytes (snd e) = wd_bytes wd.
Proof.
  revert l. induction wds as [|w wds IH]; intros [|e l] Hf Hnd Hin Hm; simpl in Hm; try discriminate.
  - destruct Hin.
  - inversion Hf as [|? ? Hw Hf']; subst. simpl in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
    injection Hm as Hb Hm. simpl.
    assert (Hide : dd_id (snd e) = wd_id w) by (unfold dd_id; rewrite Hb; apply Hw).
    rewrite Hide. destruct Hin as [<-|Hin].
    + rewrite Z.eqb_refl. exists e. auto.
    + destruct (wd_id w =? wd_id wd) eqn:E.
      * apply Z.eqb_eq in E. exfalso. apply Hni. rewrite E. apply in_map. exact Hin.
      * apply IH; auto.
Qed.

Lemma vda_m0_model : VDA_m0_model.
Proof.
  intros wds wd ws st Hin Hdf Hnz Hnd Hsf Hwf Hdw Hfr Hpar Hdict Hset.
  set (dm := wd_model wd).
  assert (Hwdf : dict_facts wd) by (rewrite Forall_forall in Hdf; auto).
  assert (Hwz : wd_id wd <> 0) by (rewrite Forall_forall in Hnz; auto).
  (* the selection *)
  assert (Hst : st_sel st = (set_sel (dc_set st), None)).
  { unfold st_sel. destruct (dc_set st) as [|e l] eqn:El.
    - simpl in Hset. destruct wds; [destruct Hin|discriminate].
    - revert Hdict. destruct (dc_dict st) as [d|]; intros Hdict; [|contradiction]. rewrite Hpar. simpl dp_multi.
      rewrite <- El in Hset |- *. unfold set_clean.
      rewrite (m0_ids _ wds Hdf Hset), (m0_distinct _ Hnd), (m0_forallb _ wds Hdf Hnz Hset).
      revert Hdict. destruct (dr_src d); intros Hdict; try contradiction. reflexivity. }
  assert (Hsel : set_sel (dc_set st) (wd_id wd) = Some dm).
  { unfold set_sel. destruct (wd_id wd =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
    destruct (m0_find (dc_set st) wds wd Hdf Hnd Hin Hset) as (e & -> & Hb).
    rewrite Hb. apply m0_model_auto. exact Hwdf. }
  assert (Hmd : dmode_of (dc_par st) = md_dflt) by (rewrite Hpar; reflexivity).
  rewrite Hst, Hmd. simpl fst. simpl snd.
  destruct Hsf as (_ & _ & _ & _ & _ & Ht & Hff & _).
  assert (Hself : Forall (fun f => wi_skippable f = false -> wi_big f = false ->
                                   set_sel (dc_set st) (wi_did f) = Some dm) (ws_frames ws)).
  { eapply Forall_impl; [|exact Hfr]. simpl. intros f [Hs|(_ & Hd)] Hs' _; [congruence|]. rewrite Hd. exact Hsel. }
  assert (Hgen : forall md wl, md_magicless md = false ->
            walk_m (S (length (ws_bytes ws))) md sel_none (Some dm) wl (ws_bytes ws) 0 =
              walk (S (length (ws_bytes ws))) dm wl (ws_bytes ws) 0 ->
            series_frames_m md (set_sel (dc_set st)) None wl (ws_bytes ws) =
              series_frames_m md sel_none (Some dm) wl (ws_bytes ws)).
  { intros md wl Hmg H. unfold series_frames_m.
    change (ws_bytes ws) with (skipn (Z.to_nat 0) (ws_bytes ws)) at 2 4.
    apply (m0_walk md _ dm ws wl (ws_frames ws) 0 0 (Zlength (ws_bytes ws)) (Zlength (ws_content ws)));
      auto; lia. }
  split.
  - split; [rewrite Hpar; reflexivity|].
    intros wl. rewrite Hst, Hmd. simpl fst. simpl snd.
    rewrite Hgen; [apply Hdw|reflexivity|apply Hdw].
  - unfold decode_series_m, decode_series. rewrite Hgen; [|reflexivity|apply m0_pd_walk].
    unfold series_frames_m, series_frames. rewrite m0_pd_walk. reflexivity.
Qed.
