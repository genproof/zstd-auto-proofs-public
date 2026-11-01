(* harness/valid_params.c against the model (plain Coq): the bytes zstd decodes in each mode, and what the
   model's walk under the mode's parameters (model/Params.v) gives on them, as a written series (frames at
   their places, their contents).  Used by WMain3_valid_params.v. *)
Require Export Zstd.proof.harness.writer.SeriesLemmas.
Require Export Zstd.proof.model.Params Zstd.proof.model.ParamsDflt.
Local Open Scope bool_scope.

(* ---------- the decoding modes (dmode_of of the parameters main sets) ---------- *)

(* mode 0: ZSTD_d_forceIgnoreChecksum *)
Definition md_ck : dmode := {| md_magicless := false; md_ignore := true; md_bmax := ZSTD_BLOCKSIZE_MAX; md_dwin := false |}.
(* mode 2: ZSTD_d_maxBlockSize blim *)
Definition md_bm (blim: Z) : dmode := {| md_magicless := false; md_ignore := false; md_bmax := blim; md_dwin := false |}.
(* mode 3: ZSTD_f_zstd1_magicless *)
Definition md_mg : dmode := {| md_magicless := true; md_ignore := false; md_bmax := ZSTD_BLOCKSIZE_MAX; md_dwin := false |}.

(* ---------- a series as zstd sees it ---------- *)

(* ws' (its bytes: what zstd is given; its frames: where they lie in those bytes; its content) is decoded by
   the model under md, at every window limit, as SeriesLemmas.series_frames_written describes a written
   series: the frames up to the first one rejected at its header, then the end or TDetHdr *)
Definition vp_written (md: dmode) (ws': wseries) : Prop :=
  bytes_ok (ws_bytes ws') /\ bytes_ok (ws_content ws') /\ (1 <= length (ws_frames ws'))%nat /\
  tiles (ws_frames ws') 0 0 (Zlength (ws_bytes ws')) (Zlength (ws_content ws')) /\
  forall wl, series_frames_m md sel_none (Some no_dict) wl (ws_bytes ws') =
    (map (frec_of ws') (ok_prefix wl (ws_frames ws')), if all_ok wl (ws_frames ws') then TEnd else TDetHdr).

(* mode 0: b' is the series' bytes b with any Content_Checksum fields (the last 4 bytes of a Zstandard frame
   with a checksum) replaced by any bytes *)
Definition ck_agree (fs: list winfo) (b b': list Z) : Prop :=
  Zlength b' = Zlength b /\ bytes_ok b' /\
  forall i, 0 <= i < Zlength b -> byte_at b' i <> byte_at b i ->
    exists f, In f fs /\ wi_skippable f = false /\ wi_checksum f = true /\ wi_end f - 4 <= i < wi_end f.

Definition ws_ck (ws: wseries) (b': list Z) : wseries :=
  {| ws_bytes := b'; ws_content := ws_content ws; ws_frames := ws_frames ws |}.

(* mode 3: a frame without its 4-byte magic number (its header 4 bytes shorter); the series of one frame *)
Definition wi_unmagic (f: winfo) : winfo :=
  {| wi_skippable := wi_skippable f; wi_variant := wi_variant f; wi_start := wi_start f;
     wi_size := wi_size f - 4; wi_cstart := wi_cstart f; wi_csize := wi_csize f;
     wi_fcs_present := wi_fcs_present f; wi_fcs := wi_fcs f; wi_did_size := wi_did_size f; wi_did := wi_did f;
     wi_single := wi_single f; wi_window := wi_window f; wi_window_log := wi_window_log f;
     wi_checksum := wi_checksum f; wi_blocks := wi_blocks f; wi_skip_n := wi_skip_n f;
     wi_hsize := wi_hsize f - 4; wi_uses_dict := wi_uses_dict f |}.

Definition ws_unmagic (ws: wseries) : wseries :=
  {| ws_bytes := skipn 4 (ws_bytes ws); ws_content := ws_content ws;
     ws_frames := map wi_unmagic (ws_frames ws) |}.

(* ---------- the modes' theorems ---------- *)

(* modes 1 (a window limit) and 2 with b = 0: zstd's default decoding *)
Theorem vp_dflt_written ws : series_facts no_dict ws -> vp_written md_dflt ws.
Proof.
  intros Hsf. pose proof Hsf as (Hb & Hc & _ & _ & Hn & Ht & _).
  split; [exact Hb|]. split; [exact Hc|]. split; [lia|]. split; [exact Ht|].
  intros wl. rewrite series_frames_m_dflt. apply series_frames_written; exact Hsf.
Qed.

(* ---------- mode 0 helpers: decode_blocks reads only the bytes it takes (and the length) ---------- *)

Lemma vp_le_value_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= le_value l.
Proof. induction l as [|a l IH]; cbn [le_value]; intros H; [lia|]. inversion H; subst. specialize (IH H3). lia. Qed.

Lemma vp_bytes_skipn : forall n (l: list Z), bytes_ok l -> bytes_ok (skipn n l).
Proof. intros n l H. unfold bytes_ok in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. apply H. Qed.

Lemma vp_le_field_nonneg : forall s i k, bytes_ok s -> 0 <= le_field s i k.
Proof.
  intros s i k H. unfold le_field, slice. apply vp_le_value_nonneg.
  apply sl_Forall_firstn. apply vp_bytes_skipn with (n := Z.to_nat i) in H.
  eapply Forall_impl; [|exact H]. unfold is_byte. intros; lia.
Qed.

Lemma vp_cblock_size_nonneg : forall s c, bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  intros s c Hb H. unfold cblock_size in H.
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (bp_type (block_props_of s) =? 1); [injection H as <-; lia|].
  destruct (bp_type (block_props_of s) =? 3); [discriminate|].
  injection H as <-. unfold block_props_of; cbn [bp_origSize].
  apply Z.shiftr_nonneg. apply vp_le_field_nonneg; auto.
Qed.

Lemma vp_cblock_size_agree : forall (s s': list Z) m, firstn m s = firstn m s' -> length s = length s' ->
  (3 <= m)%nat -> cblock_size s = cblock_size s' /\ block_props_of s = block_props_of s'.
Proof.
  intros s s' m H Hl Hm.
  assert (E : le_field s 0 3 = le_field s' 0 3) by (apply (sl_le_field_agree _ _ m); auto; lia).
  assert (Hz : Zlength s = Zlength s') by (rewrite !Zlength_correct, Hl; reflexivity).
  unfold cblock_size, block_props_of. rewrite E, Hz. split; reflexivity.
Qed.

Lemma vp_db_k : forall f st hist s out bsm wsize o k,
  bytes_ok s -> decode_blocks f st hist s out bsm wsize = Some (o, k) -> 3 <= k <= Zlength s.
Proof.
  induction f; intros st hist s out bsm wsize o k Hb H; [discriminate|].
  cbn [decode_blocks] in H.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (vp_cblock_size_nonneg s c Hb Ec) as Hc0.
  destruct (Z.gtb_spec c (Zlength s - ZSTD_blockHeaderSize)); [discriminate|].
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|]; [|discriminate] end.
  destruct (bp_last (block_props_of s) =? 1).
  - assert (k = ZSTD_blockHeaderSize + c) as -> by congruence. change ZSTD_blockHeaderSize with 3 in *. lia.
  - destruct (decode_blocks f st' hist _ out' bsm wsize) as [[o' k']|] eqn:Ed; [|discriminate].
    assert (k = ZSTD_blockHeaderSize + c + k') as -> by congruence.
    apply IHf in Ed; [|apply vp_bytes_skipn; auto].
    rewrite Zlength_correct, length_skipn in Ed. rewrite Zlength_correct in *.
    change ZSTD_blockHeaderSize with 3 in *. lia.
Qed.

Lemma vp_db_first : forall f st hist s out bsm wsize o k c,
  bytes_ok s -> decode_blocks f st hist s out bsm wsize = Some (o, k) -> cblock_size s = Some c ->
  ZSTD_blockHeaderSize + c <= k.
Proof.
  intros [|f] st hist s out bsm wsize o k c Hb H Ec; [discriminate|].
  cbn [decode_blocks] in H. rewrite Ec in H.
  destruct (Z.gtb_spec c (Zlength s - ZSTD_blockHeaderSize)); [discriminate|].
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|]; [|discriminate] end.
  destruct (bp_last (block_props_of s) =? 1).
  - assert (k = ZSTD_blockHeaderSize + c) as -> by congruence. lia.
  - destruct (decode_blocks f st' hist _ out' bsm wsize) as [[o' k']|] eqn:Ed; [|discriminate].
    assert (k = ZSTD_blockHeaderSize + c + k') as -> by congruence.
    apply vp_db_k in Ed; [|apply vp_bytes_skipn; auto]. lia.
Qed.

Lemma vp_db_agree : forall f st hist s s' out bsm wsize o k m,
  bytes_ok s -> length s = length s' -> firstn m s = firstn m s' -> (Z.to_nat k <= m)%nat ->
  decode_blocks f st hist s out bsm wsize = Some (o, k) ->
  decode_blocks f st hist s' out bsm wsize = Some (o, k).
Proof.
  induction f; intros st hist s s' out bsm wsize o k m Hb Hl Hf Hm H; [discriminate|].
  pose proof (vp_db_k _ _ _ _ _ _ _ _ _ Hb H) as Hk.
  pose proof (fun c => vp_db_first _ _ _ _ _ _ _ _ _ c Hb H) as Hfirst.
  cbn [decode_blocks] in H |- *.
  destruct (vp_cblock_size_agree s s' m Hf Hl ltac:(lia)) as [Ec' Ep].
  assert (Hz : Zlength s = Zlength s') by (rewrite !Zlength_correct, Hl; reflexivity).
  rewrite <- Ec', <- Ep, <- Hz.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (vp_cblock_size_nonneg s c Hb Ec) as Hc0. specialize (Hfirst c eq_refl).
  destruct (Z.gtb_spec c (Zlength s - ZSTD_blockHeaderSize)); [discriminate|].
  assert (Hbody : slice s ZSTD_blockHeaderSize c = slice s' ZSTD_blockHeaderSize c).
  { unfold slice. apply (sl_firstn_agree _ _ m); auto. change ZSTD_blockHeaderSize with 3 in *. lia. }
  rewrite <- Hbody.
  match type of H with context [match ?r with None => None | Some _ => _ end] =>
    destruct r as [[st' out']|]; [|discriminate] end.
  destruct (bp_last (block_props_of s) =? 1); [exact H|].
  destruct (decode_blocks f st' hist (skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) s) out' bsm wsize)
    as [[o' k']|] eqn:Ed; [|discriminate].
  assert (o = o' /\ k = ZSTD_blockHeaderSize + c + k') as [-> ->] by (split; congruence).
  pose proof (vp_db_k _ _ _ _ _ _ _ _ _ (vp_bytes_skipn (Z.to_nat (ZSTD_blockHeaderSize + c)) _ Hb) Ed) as Hk'.
  change ZSTD_blockHeaderSize with 3 in *.
  assert (A1 : length (skipn (Z.to_nat (3 + c)) s) = length (skipn (Z.to_nat (3 + c)) s'))
    by (rewrite !length_skipn, Hl; reflexivity).
  assert (A2 : firstn (m - Z.to_nat (3 + c)) (skipn (Z.to_nat (3 + c)) s) =
               firstn (m - Z.to_nat (3 + c)) (skipn (Z.to_nat (3 + c)) s')).
  { rewrite !firstn_skipn_comm. replace (Z.to_nat (3 + c) + (m - Z.to_nat (3 + c)))%nat with m by lia.
    rewrite Hf. reflexivity. }
  assert (A3 : (Z.to_nat k' <= m - Z.to_nat (3 + c))%nat) by lia.
  rewrite (IHf _ _ _ _ _ _ _ _ _ _ (vp_bytes_skipn _ _ Hb) A1 A2 A3 Ed). reflexivity.
Qed.

Lemma vp_fh_bmax (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  unfold ZSTD_BLOCKSIZE_MAX; lia.
Qed.

(* md_ck decodes as the default decoder, except that a wrong checksum is accepted *)
Lemma vp_ck_frame_dflt : forall dm wl s, decode_frame dm wl s <> FDetCk ->
  decode_frame_m md_ck dm wl s = decode_frame dm wl s.
Proof.
  intros dm wl s H.
  unfold decode_frame_m, decode_frame, get_frame_header_m in *. simpl md_magicless. simpl md_ignore. simpl md_bmax. change (md_dwin md_ck) with false.
  cbv beta iota zeta. rewrite !Z.sub_0_r.
  destruct (get_frame_header s) as [|k|h] eqn:E; try reflexivity.
  cbn [negb andb]. rewrite (Z.min_l _ _ (vp_fh_bmax s h E)).
  repeat match goal with
  | |- context [if ?c then _ else _] => destruct c; try reflexivity
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[? ?]|]; try reflexivity
  end; congruence.
Qed.

Lemma vp_fhd_header_size_nonneg : forall fhd, 0 <= fhd_header_size fhd.
Proof.
  intros fhd. unfold fhd_header_size.
  assert (0 <= Z.land (Z.shiftr fhd 5) 1 <= 1).
  { rewrite (Z.land_ones _ 1) by lia. pose proof (Z.mod_pos_bound (Z.shiftr fhd 5) (2 ^ 1)). simpl in *. lia. }
  assert (forall n, 0 <= nth n [0; 1; 2; 4] 0) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  assert (forall n, 0 <= nth n [0; 2; 4; 8] 0) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  match goal with |- context [if ?c then _ else _] => destruct c end;
  specialize (H0 (Z.to_nat (Z.land fhd 3))); specialize (H1 (Z.to_nat (Z.shiftr fhd 6))); lia.
Qed.

Lemma vp_fh_hs (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> 0 <= fh_headerSize h.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  first [apply vp_fhd_header_size_nonneg | unfold ZSTD_SKIPPABLEHEADERSIZE; lia].
Qed.

Lemma vp_ck_not_unk : forall dm wl s, decode_frame_m md_ck dm wl s <> FUnk ->
  9 <= Zlength s /\ le_field s 0 4 = ZSTD_MAGICNUMBER.
Proof.
  intros dm wl s H. unfold decode_frame_m in H. simpl md_magicless in H. cbv beta iota zeta in H.
  repeat rewrite Z.sub_0_r in H. cbn [negb andb] in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize) eqn:E1; [congruence|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)) eqn:E2; [congruence|].
  apply Z.ltb_ge in E1. apply Bool.negb_false_iff, Z.eqb_eq in E2.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize in E1. split; [lia|exact E2].
Qed.

(* md_ck's result depends only on the bytes the frame takes, up to its checksum, and the length *)
Lemma vp_ck_frame_agree : forall dm wl s s' m R,
  bytes_ok s -> length s = length s' -> firstn m s = firstn m s' ->
  (Z.to_nat (fhd_header_size (byte_at s 4)) <= m)%nat ->
  decode_frame_m md_ck dm wl s = R -> R <> FUnk ->
  (forall c n, R = FOk c n -> (Z.to_nat n <= m)%nat \/
     ((Z.to_nat (n - 4) <= m)%nat /\ forall h, get_frame_header s = FH_ok h -> fh_checksumFlag h = 1)) ->
  decode_frame_m md_ck dm wl s' = R.
Proof.
  intros dm wl s s' m R Hb Hl Hf Hm H HR Hn.
  assert (Hnu : decode_frame_m md_ck dm wl s <> FUnk) by congruence.
  apply vp_ck_not_unk in Hnu. destruct Hnu as [H9 Hmag].
  assert (Hb4 : 0 <= byte_at s 4 < 256).
  { unfold byte_at. unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply Hb, nth_In.
    rewrite Zlength_correct in H9. simpl. lia. }
  pose proof (sl_fhd_header_size_ge6 _ Hb4) as H6.
  assert (Hz : Zlength s' = Zlength s) by (rewrite !Zlength_correct, Hl; reflexivity).
  assert (E0 : le_field s' 0 4 = le_field s 0 4) by (symmetry; apply (sl_le_field_agree _ _ m); auto; simpl; lia).
  assert (E4 : byte_at s' 4 = byte_at s 4) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; simpl; lia).
  assert (E5 : byte_at s' 5 = byte_at s 5) by (symmetry; apply (sl_byte_at_agree _ _ m); auto; simpl; lia).
  assert (Eg : get_frame_header s' = get_frame_header s)
    by (symmetry; apply (sl_gfh_agree _ _ m); auto; lia).
  subst R. unfold decode_frame_m, get_frame_header_m in *. simpl md_magicless in *. simpl md_ignore in *.
  simpl md_bmax in *. change (md_dwin md_ck) with false in *. cbv beta iota zeta in *. repeat rewrite Z.sub_0_r in *. cbn [negb andb] in *.
  rewrite Hz, E0, E4, E5, Eg.
  destruct (get_frame_header s) as [|k0|h] eqn:Eh; [reflexivity|reflexivity|].
  pose proof (vp_fh_hs s h Eh) as Hhs.
  set (hs := fh_headerSize h) in *.
  assert (Hdb : forall bsm out k, decode_blocks (length (skipn (Z.to_nat hs) s)) (dm_state dm) (dm_content dm)
              (skipn (Z.to_nat hs) s) [] bsm (fh_windowSize h) = Some (out, k) -> (Z.to_nat (hs + k) <= m)%nat ->
            decode_blocks (length (skipn (Z.to_nat hs) s')) (dm_state dm) (dm_content dm)
              (skipn (Z.to_nat hs) s') [] bsm (fh_windowSize h) = Some (out, k)).
  { intros bsm out k Eb Hk.
    pose proof (vp_db_k _ _ _ _ _ _ _ _ _ (vp_bytes_skipn (Z.to_nat hs) _ Hb) Eb) as Hk3.
    assert (Hls : length (skipn (Z.to_nat hs) s') = length (skipn (Z.to_nat hs) s))
      by (rewrite !length_skipn, Hl; reflexivity).
    rewrite Hls.
    apply (vp_db_agree _ _ _ (skipn (Z.to_nat hs) s) _ _ _ _ _ _ (m - Z.to_nat hs)); auto.
    - apply vp_bytes_skipn; auto.
    - rewrite !firstn_skipn_comm. replace (Z.to_nat hs + (m - Z.to_nat hs))%nat with m by lia. rewrite Hf. reflexivity.
    - lia. }
  destruct (fh_checksumFlag h =? 1) eqn:Eck;
  repeat match goal with
  | |- context [if ?c then _ else _] =>
      lazymatch c with
      | context [decode_blocks] => fail
      | context [s'] => fail
      | _ => destruct c; try reflexivity
      end
  end.
  all: match goal with |- _ = match ?x with Some _ => _ | None => _ end => destruct x as [[out k]|] eqn:Eb end;
    [|congruence].
  all: destruct (_ && _) eqn:E1; [congruence|].
  - destruct (Zlength s - hs - k <? 4) eqn:E2; [congruence|].
    destruct (Hn _ _ eq_refl) as [Hn1|[Hn1 _]]; rewrite (Hdb _ _ _ Eb) by lia; cbv beta iota;
      rewrite E1, E2; reflexivity.
  - destruct (Hn _ _ eq_refl) as [Hn1|[Hn1 Hn2]].
    + rewrite (Hdb _ _ _ Eb) by lia; cbv beta iota; rewrite E1; reflexivity.
    + specialize (Hn2 h eq_refl). rewrite Hn2 in Eck. discriminate.
Qed.

(* ---------- mode 0: the walk of md_ck over frames whose decoding is known ---------- *)

Lemma vp_walk_S : forall f wl s off, walk_m (S f) md_ck sel_none (Some no_dict) wl s off =
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk_m f md_ck sel_none (Some no_dict) wl (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match decode_frame_m md_ck no_dict wl s with
        | FOk c k =>
            let '(l, t) := walk_m f md_ck sel_none (Some no_dict) wl (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
        | FDetHdr => (nil, TDetHdr)
        | FDetCk => (nil, TDetCk)
        | FUnk => (nil, TUnk)
        end.
Proof.
  intros f wl s off. cbn [walk_m]. simpl md_magicless. unfold starting_len. cbn [negb andb].
  assert (Hd : frame_dict false sel_none (Some no_dict) s = Some no_dict).
  { unfold frame_dict, sel_none. destruct (get_frame_header_m false s); reflexivity. }
  rewrite Hd. reflexivity.
Qed.

Lemma vp_walk_ck : forall ws wl S n cn T fs off coff fuel,
  tiles fs off coff n cn -> 0 <= off ->
  Forall (fun f => wi_end f <= Zlength S /\
     5 <= Zlength (skipn (Z.to_nat (wi_start f)) S) /\
     (wi_skippable f = true ->
        is_skippable_magic (le_field (skipn (Z.to_nat (wi_start f)) S) 0 4) = true /\
        skippable_frame_size (skipn (Z.to_nat (wi_start f)) S) = Some (wi_size f)) /\
     (wi_skippable f = false ->
        is_skippable_magic (le_field (skipn (Z.to_nat (wi_start f)) S) 0 4) = false /\
        decode_frame_m md_ck no_dict wl (skipn (Z.to_nat (wi_start f)) S) =
          if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f))) fs ->
  (forall fuel, (length (skipn (Z.to_nat n) S) < fuel)%nat ->
     walk_m fuel md_ck sel_none (Some no_dict) wl (skipn (Z.to_nat n) S) n = (nil, T)) ->
  (length (skipn (Z.to_nat off) S) < fuel)%nat ->
  walk_m fuel md_ck sel_none (Some no_dict) wl (skipn (Z.to_nat off) S) off =
    (map (frec_of ws) (ok_prefix wl fs), if all_ok wl fs then T else TDetHdr).
Proof.
  intros ws wl S n cn T fs. induction fs as [|f fs IH]; intros off coff fuel Ht Hoff Hff HT Hfuel.
  - simpl in Ht. destruct Ht as [-> ->]. simpl. apply HT; auto.
  - simpl in Ht. destruct Ht as (Hst & Hcst & Hsz & Hcsz & Hskc & Ht).
    inversion Hff as [|? ? (Hend & H5 & Hsk & Hdec) Hff']; subst.
    unfold wi_end in Hend.
    assert (Hskr : skipn (Z.to_nat (wi_size f)) (skipn (Z.to_nat (wi_start f)) S) =
                   skipn (Z.to_nat (wi_start f + wi_size f)) S).
    { rewrite skipn_skipn, Z2Nat.inj_add by lia. f_equal. lia. }
    destruct fuel as [|fuel]; [lia|].
    assert (Hfr : (length (skipn (Z.to_nat (wi_start f + wi_size f)) S) < fuel)%nat).
    { rewrite !length_skipn in *. rewrite Zlength_correct in Hend. lia. }
    rewrite vp_walk_S.
    assert (Zlength (skipn (Z.to_nat (wi_start f)) S) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
    { apply Z.ltb_ge. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
    destruct (wi_skippable f) eqn:Eskip.
    + destruct (Hsk eq_refl) as [Hmag Hsfs]. rewrite Hmag, Hsfs, Hskr.
      rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
      assert (Hrej : wi_rejected wl f = false) by (unfold wi_rejected; rewrite Eskip; reflexivity).
      simpl. rewrite Hrej. simpl. f_equal. f_equal. unfold frec_of, wi_content, slice.
      rewrite Eskip, (Hskc eq_refl). simpl. f_equal; auto.
    + destruct (Hdec eq_refl) as [Hmag Hd]. rewrite Hmag, Hd.
      simpl ok_prefix. simpl all_ok. destruct (wi_rejected wl f) eqn:Erej.
      * reflexivity.
      * rewrite Hskr. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
        simpl. f_equal. f_equal. unfold frec_of. rewrite Eskip. f_equal; auto.
Qed.

(* two frames of a tiling that share a position are the same *)
Lemma vp_tiles_unique : forall fs off coff n cn f g i, tiles fs off coff n cn -> In f fs -> In g fs ->
  wi_start f <= i < wi_end f -> wi_start g <= i < wi_end g -> f = g.
Proof.
  induction fs as [|h fs IH]; intros off coff n cn f g i Ht Hf Hg Hif Hig; [destruct Hf|].
  simpl in Ht. destruct Ht as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (sl_tiles_bounds _ _ _ _ _ H6) as (_ & _ & Hbd). rewrite Forall_forall in Hbd.
  unfold wi_end in *.
  destruct Hf as [<- | Hf], Hg as [<- | Hg].
  - reflexivity.
  - specialize (Hbd g Hg). lia.
  - specialize (Hbd f Hf). lia.
  - eapply IH; eauto.
Qed.

Lemma vp_byte_at_skipn : forall (l: list Z) a j, 0 <= a -> 0 <= j ->
  byte_at (skipn (Z.to_nat a) l) j = byte_at l (a + j).
Proof.
  intros l a j Ha Hj. unfold byte_at. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma vp_firstn_ext : forall (s s': list Z) m, length s = length s' ->
  (forall j, 0 <= j < Z.of_nat m -> byte_at s j = byte_at s' j) -> firstn m s = firstn m s'.
Proof.
  intros s s' m Hl H. apply nth_ext with (d := 0) (d' := 0).
  - rewrite !length_firstn, Hl. reflexivity.
  - intros i Hi. rewrite length_firstn in Hi. rewrite !nth_firstn.
    destruct (i <? m)%nat eqn:E; [|reflexivity]. apply Nat.ltb_lt in E.
    specialize (H (Z.of_nat i) ltac:(lia)). unfold byte_at in H. rewrite Nat2Z.id in H. exact H.
Qed.

Lemma vp_decode_frame_hs : forall dm wl s, decode_frame dm wl s <> FUnk ->
  fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= Zlength s.
Proof.
  intros dm wl s H. unfold decode_frame in H.
  destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_MIN + ZSTD_blockHeaderSize); [congruence|].
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)); [congruence|].
  destruct (Zlength s <? fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize) eqn:E; [congruence|].
  apply Z.ltb_ge in E. exact E.
Qed.

(* a frame of the series, in b': its decoding by md_ck is the original frame's *)
Lemma vp_ck_frame_step : forall ws b' wl f,
  series_facts no_dict ws -> wseries_wf ws -> ck_agree (ws_frames ws) (ws_bytes ws) b' -> In f (ws_frames ws) ->
  wi_end f <= Zlength b' /\
  5 <= Zlength (skipn (Z.to_nat (wi_start f)) b') /\
  (wi_skippable f = true ->
     is_skippable_magic (le_field (skipn (Z.to_nat (wi_start f)) b') 0 4) = true /\
     skippable_frame_size (skipn (Z.to_nat (wi_start f)) b') = Some (wi_size f)) /\
  (wi_skippable f = false ->
     is_skippable_magic (le_field (skipn (Z.to_nat (wi_start f)) b') 0 4) = false /\
     decode_frame_m md_ck no_dict wl (skipn (Z.to_nat (wi_start f)) b') =
       if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f)).
Proof.
  intros ws b' wl f Hsf (_ & _ & Hlay) (Hlen & Hb' & Hdiff) Hin.
  pose proof Hsf as (Hb & _ & _ & _ & _ & Ht & Hff & _).
  pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd). rewrite Forall_forall in Hbd.
  rewrite Forall_forall in Hff, Hlay.
  (* every Zstandard frame is at least 9 bytes *)
  assert (Hsz9 : forall g, In g (ws_frames ws) -> wi_skippable g = false -> 9 <= wi_size g).
  { intros g Hg Hgs. destruct (Hff g Hg) as (_ & _ & _ & _ & _ & _ & _ & _ & Hdec).
    destruct (Hdec Hgs) as (Hd & _). destruct (Hbd g Hg) as (Hg0 & Hgz & Hge & _). unfold wi_end in Hge.
    assert (Hnu : decode_frame no_dict wl (wi_bytes ws g ++ nil) <> FUnk)
      by (rewrite Hd; destruct (wi_rejected wl g); discriminate).
    apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 _]. rewrite app_nil_r in H9.
    unfold wi_bytes, slice in H9. rewrite Zlength_correct, length_firstn, length_skipn in H9.
    rewrite Zlength_correct in Hge. lia. }
  destruct (Hbd f Hin) as (Hs0 & Hsz & Hend & _). unfold wi_end in Hend.
  set (s := skipn (Z.to_nat (wi_start f)) (ws_bytes ws)).
  set (s' := skipn (Z.to_nat (wi_start f)) b').
  assert (Hlb : length b' = length (ws_bytes ws)) by (rewrite !Zlength_correct in Hlen; lia).
  assert (Hls : length s = length s') by (subst s s'; rewrite !length_skipn, Hlb; reflexivity).
  assert (Hlsz : (Z.to_nat (wi_size f) <= length s)%nat)
    by (subst s; rewrite length_skipn; rewrite Zlength_correct in Hend; lia).
  (* the bytes of f agree, except a Zstandard frame's last 4 when it has a checksum *)
  assert (Hagree : forall j, 0 <= j < wi_size f ->
            (wi_skippable f = true \/ wi_checksum f = false \/ j < wi_size f - 4) -> byte_at s j = byte_at s' j).
  { intros j Hj Hc. subst s s'. rewrite !vp_byte_at_skipn by lia.
    destruct (Z.eq_dec (byte_at b' (wi_start f + j)) (byte_at (ws_bytes ws) (wi_start f + j))) as [E|E];
      [symmetry; exact E|].
    destruct (Hdiff (wi_start f + j)) as (g & Hg & Hgs & Hgc & Hgi); [rewrite Zlength_correct in *; lia|exact E|].
    pose proof (Hsz9 g Hg Hgs) as Hg9.
    assert (f = g) as <-.
    { apply (vp_tiles_unique _ _ _ _ _ f g (wi_start f + j) Ht Hin Hg); unfold wi_end in *; lia. }
    unfold wi_end in Hgi. rewrite Hgs, Hgc in Hc. destruct Hc as [Hc|[Hc|Hc]]; try discriminate; lia. }
  set (m := if wi_skippable f then wi_size f else if wi_checksum f then wi_size f - 4 else wi_size f).
  assert (Hm0 : wi_size f - 4 <= m <= wi_size f) by (subst m; destruct (wi_skippable f), (wi_checksum f); lia).
  assert (Hpre : firstn (Z.to_nat m) s = firstn (Z.to_nat m) s').
  { apply vp_firstn_ext; auto. intros j Hj. apply Hagree; [lia|].
    subst m. destruct (wi_skippable f); [auto|]. destruct (wi_checksum f); [right; right; lia|auto]. }
  assert (Hs'split : s' = firstn (Z.to_nat (wi_size f)) s' ++ skipn (Z.to_nat (wi_size f)) s')
    by (symmetry; apply firstn_skipn).
  assert (Hssplit : s = wi_bytes ws f ++ skipn (Z.to_nat (wi_size f)) s)
    by (subst s; unfold wi_bytes, slice; symmetry; apply firstn_skipn).
  assert (Hzs : Zlength s' = Zlength s) by (rewrite !Zlength_correct, Hls; reflexivity).
  destruct (Hff f Hin) as (_ & _ & _ & Hgfh & _ & _ & Hfhs & Hsk & Hdec).
  fold s in Hgfh, Hfhs.
  split; [rewrite Hlen; exact Hend|].
  destruct (wi_skippable f) eqn:Eskip.
  - destruct (Hsk eq_refl) as (_ & Hl8 & Hmag & Hsfs & _).
    assert (Hfb : firstn (Z.to_nat (wi_size f)) s' = wi_bytes ws f).
    { subst m. rewrite <- Hpre. reflexivity. }
    rewrite Hfb in Hs'split. rewrite Hs'split.
    unfold ZSTD_SKIPPABLEHEADERSIZE in Hl8.
    split; [rewrite !Zlength_correct, length_app; rewrite Zlength_correct in Hl8; lia|].
    split; [|intros; discriminate].
    intros _. rewrite sl_le_field_app by lia. split; [exact Hmag | apply Hsfs].
  - destruct (Hdec eq_refl) as (Hd & _ & _).
    set (R0 := if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f)).
    assert (HdS : decode_frame no_dict wl s = R0) by (rewrite Hssplit; apply Hd).
    assert (HR0 : R0 <> FUnk /\ R0 <> FDetCk) by (subst R0; destruct (wi_rejected wl f); split; discriminate).
    assert (Hnu : decode_frame no_dict wl s <> FUnk) by (rewrite HdS; apply HR0).
    apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
    pose proof (Hsz9 f Hin Eskip) as Hf9.
    assert (Hfbl : length (wi_bytes ws f) = Z.to_nat (wi_size f)).
    { unfold wi_bytes, slice. rewrite length_firstn, length_skipn. rewrite Zlength_correct in Hend. lia. }
    assert (Hhs3 : fhd_header_size (byte_at s 4) + ZSTD_blockHeaderSize <= wi_size f).
    { assert (Hnu : decode_frame no_dict wl (wi_bytes ws f ++ nil) <> FUnk)
        by (rewrite Hd; destruct (wi_rejected wl f); discriminate).
      apply vp_decode_frame_hs in Hnu. rewrite app_nil_r in Hnu.
      assert (E4 : byte_at (wi_bytes ws f) 4 = byte_at s 4).
      { rewrite Hssplit. unfold byte_at. rewrite app_nth1 by (simpl; lia). reflexivity. }
      rewrite E4, Zlength_correct, Hfbl in Hnu. lia. }
    specialize (Hfhs eq_refl). unfold Info.frame_header_size in Hfhs.
    destruct (Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX); [discriminate|]. injection Hfhs as Hfhs.
    assert (Hhm : (Z.to_nat (fhd_header_size (byte_at s 4)) <= Z.to_nat m)%nat).
    { subst m. destruct (wi_checksum f) eqn:Eck.
      - specialize (Hlay f Hin Eskip Eck). lia.
      - unfold ZSTD_blockHeaderSize in Hhs3. lia. }
    split; [rewrite Hzs; lia|].
    split; [intros; discriminate|]. intros _.
    assert (E0 : le_field s' 0 4 = le_field s 0 4).
    { symmetry. apply (sl_le_field_agree _ _ (Z.to_nat m)); auto; simpl; lia. }
    split; [rewrite E0, Hmag; reflexivity|].
    apply (vp_ck_frame_agree no_dict wl s s' (Z.to_nat m) R0); auto.
    + apply vp_bytes_skipn; auto.
    + rewrite vp_ck_frame_dflt; [exact HdS|]. rewrite HdS. apply HR0.
    + apply HR0.
    + intros c n Ec. assert (n = wi_size f) as ->.
      { subst R0. destruct (wi_rejected wl f); [discriminate|]. congruence. }
      subst m. destruct (wi_checksum f) eqn:Eck.
      * right. split; [lia|]. intros h Hh. rewrite Hgfh in Hh. destruct (wi_big f); [discriminate|].
        injection Hh as <-. unfold wi_header. rewrite Eskip, Eck. reflexivity.
      * left. lia.
Qed.

(* mode 0: checksums replaced, decoded with ZSTD_d_forceIgnoreChecksum *)
Theorem vp_ck_written ws b' : series_facts no_dict ws -> wseries_wf ws -> ck_agree (ws_frames ws) (ws_bytes ws) b' ->
  vp_written md_ck (ws_ck ws b').
Proof.
  intros Hsf Hwf Hck. pose proof Hsf as (Hb & Hc & _ & _ & Hn & Ht & _).
  pose proof Hck as (Hlen & Hb' & _).
  unfold vp_written, ws_ck. cbn [ws_bytes ws_content ws_frames].
  split; [exact Hb'|]. split; [exact Hc|]. split; [lia|]. split; [rewrite Hlen; exact Ht|].
  intros wl. change (frec_of {| ws_bytes := b'; ws_content := ws_content ws; ws_frames := ws_frames ws |})
    with (frec_of ws).
  unfold series_frames_m. change b' with (skipn (Z.to_nat 0) b') at 1.
  apply (vp_walk_ck ws wl b' (Zlength b') (Zlength (ws_content ws)) TEnd _ 0 0); auto; try lia.
  - rewrite Hlen. exact Ht.
  - rewrite Forall_forall. intros f Hin. apply vp_ck_frame_step; auto.
  - intros fuel Hfuel. rewrite Zlength_correct, Nat2Z.id, skipn_all.
    destruct fuel; [simpl in Hfuel; lia|]. reflexivity.
Qed.

(* ---------- mode 2: a smaller Block_Maximum_Size changes nothing on blocks that fit it ---------- *)

Module VPBlk.
Import Zstd.proof.model.Bitstream Zstd.proof.model.Huffman Zstd.proof.model.Block.


Lemma vb_huf_syms_len t V k pos l p : huf_decode_syms t V k pos = Some (l, p) -> length l = k.
Proof.
  revert pos l p. induction k as [|k IH]; simpl; intros pos l p H.
  - inversion H; reflexivity.
  - destruct (nth _ (huf_cells t) (0, 0)) as [x nb].
    destruct (pos - nb <? 0); [discriminate|].
    destruct (huf_decode_syms t V k (pos - nb)) as [[l' p']|] eqn:E; [|discriminate].
    inversion H; subst. simpl. f_equal. eapply IH; exact E.
Qed.

Lemma vb_huf_stream_len t s k l : huf_decode_stream t s k = Some l -> length l = Z.to_nat k.
Proof.
  unfold huf_decode_stream. destruct (negb (bs_okb s)); [discriminate|].
  destruct (huf_decode_syms t s (Z.to_nat k) (bs_total s)) as [[l' p]|] eqn:E; [|discriminate].
  destruct p; try discriminate. intros H; inversion H; subst. eapply vb_huf_syms_len; exact E.
Qed.

Lemma vb_huf_4_len t b k l : huf_decode_4streams t b k = Some l -> 0 < k -> Zlength l = k.
Proof.
  unfold huf_decode_4streams. intros H Hk.
  destruct (Z.of_nat (length b) <? 10); [discriminate|].
  destruct (_ - 6 - _ - _ - _ <? 1); [discriminate|].
  destruct (k - 3 * ((k + 3) / 4) <? 0) eqn:E3; [discriminate|].
  apply Z.ltb_ge in E3.
  destruct (huf_decode_stream t (slice b 6 (le_field b 0 2)) ((k + 3) / 4)) as [l1|] eqn:D1; [|discriminate].
  destruct (huf_decode_stream t (slice b (6 + le_field b 0 2) (le_field b 2 2)) ((k + 3) / 4))
    as [l2|] eqn:D2; [|discriminate].
  destruct (huf_decode_stream t (slice b (6 + le_field b 0 2 + le_field b 2 2) (le_field b 4 2)) ((k + 3) / 4))
    as [l3|] eqn:D3; [|discriminate].
  destruct (huf_decode_stream t _ (k - 3 * ((k + 3) / 4))) as [l4|] eqn:D4; [|discriminate].
  inversion H; subst.
  apply vb_huf_stream_len in D1, D2, D3, D4.
  assert (0 <= (k + 3) / 4) by (apply Z.div_pos; lia).
  rewrite Zlength_correct, !length_app, D1, D2, D3, D4. rewrite !Nat2Z.inj_add, !Z2Nat.id by lia. lia.
Qed.

Lemma vb_lits h b bsm B lits u h' :
  decode_literals h b bsm = Some (lits, u, h') -> Zlength b <= B -> Zlength lits <= B ->
  decode_literals h b (Z.min bsm B) = Some (lits, u, h').
Proof.
  unfold decode_literals. intros H Hb Hl.
  assert (HB: forall x, x <= bsm -> x <= B -> (x >? Z.min bsm B) = false)
    by (intros; rewrite Z.gtb_ltb, Z.ltb_ge; lia).
  repeat match type of H with
  | context [if ?c then _ else _] => lazymatch c with context [bsm] => fail | _ => destruct c eqn:? end
  | context [match ?x with Some _ => _ | None => _ end] =>
      lazymatch x with context [bsm] => fail | _ => destruct x eqn:? end
  | context [match ?x with (_, _) => _ end] => lazymatch x with context [bsm] => fail | _ => destruct x eqn:? end
  end; try discriminate.
  all: match type of H with context [if ?x >? ?m then _ else _] =>
    destruct (x >? m) eqn:Ebsm; [discriminate|];
    assert (Hx: x <= B); [ | rewrite (HB x) by (rewrite Z.gtb_ltb, Z.ltb_ge in Ebsm; lia); exact H ] end.
  all: try discriminate.
  all: assert (0 <= Zlength b) by (rewrite Zlength_correct; lia).
  all: try (rewrite Z.gtb_ltb, Z.ltb_ge in *; lia).
  all: apply (f_equal (fun o => match o with Some (a, _, _) => a | None => nil end)) in H;
       cbv beta iota in H; rewrite <- H in Hl.
  all: try (rewrite Zlength_correct, repeat_length in Hl; lia).
  all: repeat match goal with
       | E: huf_decode_stream _ _ _ = Some _ |- _ => apply vb_huf_stream_len in E; rewrite Zlength_correct, E in Hl
       | E: huf_decode_4streams _ _ ?k = Some _ |- _ =>
           destruct (Z.lt_ge_cases 0 k); [apply vb_huf_4_len in E; lia | lia]
       end.
  all: lia.
Qed.

Lemma vb_lz_copy hist out off ml : exists d, lz_copy hist out off ml = out ++ d.
Proof.
  revert out. induction ml as [|ml IH]; simpl; intros out.
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct (IH (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - off)])) as [d Hd].
    rewrite Hd. eexists. rewrite <- app_assoc. reflexivity.
Qed.

Lemma vb_exec_seqs ws rep hist seqs : forall lits out out' lits' rep',
  exec_seqs ws rep hist lits out seqs = Some (out', lits', rep') ->
  exists d, out' = out ++ d /\ (length lits <= length d + length lits')%nat.
Proof.
  revert rep. induction seqs as [|sq seqs IH]; simpl; intros rep lits out out' lits' rep' H.
  - inversion H; subst. exists nil. rewrite app_nil_r. split; [reflexivity|]. simpl. lia.
  - destruct (sq_ll sq >? Zlength lits) eqn:E1; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[off rep1]|]; [|discriminate].
    destruct (off >? Zlength hist + _); [discriminate|]. destruct (off >? ws + Zlength hist); [discriminate|].
    destruct (vb_lz_copy hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) off (Z.to_nat (sq_ml sq))) as [e He].
    rewrite He in H. apply IH in H. destruct H as [d [-> Hl]].
    exists (firstn (Z.to_nat (sq_ll sq)) lits ++ e ++ d). split; [rewrite !app_assoc; reflexivity|].
    rewrite !length_app. rewrite length_skipn in Hl.
    pose proof (length_firstn (Z.to_nat (sq_ll sq)) lits). lia.
Qed.

Lemma vb_block st hist out b bsm ws st' content B :
  decode_block st hist out b bsm ws = Some (st', content) -> Zlength b <= B -> Zlength content <= B ->
  decode_block st hist out b (Z.min bsm B) ws = Some (st', content).
Proof.
  unfold decode_block. intros H Hb Hc.
  destruct (Zlength b >? bsm) eqn:E1; [discriminate|].
  assert (Zlength b >? Z.min bsm B = false) as -> by (rewrite Z.gtb_ltb, Z.ltb_ge in *; lia).
  destruct (decode_literals (st_huf st) b bsm) as [[[lits lused] huf]|] eqn:EL; [|discriminate].
  destruct (decode_seq_header (st_seq st) (skipn (Z.to_nat lused) b)) as [[[nbSeq tabs] hused]|] eqn:DS;
    [|discriminate].
  destruct (if nbSeq =? 0 then Some nil else _) as [seqs|] eqn:DQ; [|discriminate].
  destruct (exec_seqs ws (st_rep st) hist lits out seqs) as [[[out' lits'] rep']|] eqn:EX; [|discriminate].
  destruct (Zlength (skipn (length out) (out' ++ lits')) >? bsm) eqn:E2; [discriminate|].
  inversion H; subst content. clear H.
  pose proof EX as EX'. apply vb_exec_seqs in EX'. destruct EX' as [d [-> Hl]].
  rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag in Hc, E2. simpl in Hc, E2.
  rewrite (vb_lits _ _ _ _ _ _ _ EL) by (auto; rewrite Zlength_correct in *; rewrite length_app in Hc; lia).
  rewrite DS, DQ, EX.
  rewrite <- app_assoc, skipn_app, skipn_all, Nat.sub_diag. simpl.
  assert (Zlength (d ++ lits') >? Z.min bsm B = false) as -> by (rewrite Z.gtb_ltb, Z.ltb_ge in *; lia).
  reflexivity.
Qed.

Lemma vb_some_pair {A C} (a a': A) (b b': C) : Some (a, b) = Some (a', b') -> a = a' /\ b = b'.
Proof. intros H. inversion H. auto. Qed.

Lemma vb_fok a a' b b' : FOk a b = FOk a' b' -> a = a' /\ b = b'.
Proof. intros H. inversion H. auto. Qed.

Lemma vb_bytes_skipn n s : bytes_ok s -> bytes_ok (skipn n s).
Proof.
  unfold bytes_ok. intros H. rewrite <- (firstn_skipn n s) in H. apply Forall_app in H. tauto.
Qed.

Lemma vb_bytes_firstn n s : bytes_ok s -> bytes_ok (firstn n s).
Proof.
  unfold bytes_ok. intros H. rewrite <- (firstn_skipn n s) in H. apply Forall_app in H. tauto.
Qed.

Lemma vb_le_value_nonneg l : bytes_ok l -> 0 <= le_value l.
Proof.
  unfold bytes_ok. intros H. induction H; cbn [le_value]; unfold is_byte in *; lia.
Qed.

Lemma vb_cblock_nonneg s c : bytes_ok s -> cblock_size s = Some c -> 0 <= c.
Proof.
  intros Hs. unfold cblock_size, block_props_of. cbn zeta.
  destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
  destruct (_ =? 1); [intros H; inversion H; lia|].
  destruct (_ =? 3); [discriminate|]. intros H; inversion H; subst.
  apply Z.shiftr_nonneg. apply vb_le_value_nonneg. unfold slice.
  apply vb_bytes_firstn, vb_bytes_skipn, Hs.
Qed.

Lemma vb_blocks_mono hist bsm ws fuel : forall st s out o k, bytes_ok s ->
  decode_blocks fuel st hist s out bsm ws = Some (o, k) -> 3 <= k /\ exists d, o = out ++ d.
Proof.
  induction fuel as [|fuel IH]; cbn [decode_blocks]; intros st s out o k Hs H; [discriminate|].
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (vb_cblock_nonneg _ _ Hs Ec) as Hc0.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [discriminate|].
  match type of H with context [match ?r with None => _ | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Eres; [|discriminate] end.
  assert (Hd: exists d, out' = out ++ d).
  { repeat match type of Eres with
    | context [if ?c then _ else _] => destruct c
    | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[? ?]|]
    end; try discriminate; inversion Eres; subst; eexists; reflexivity. }
  destruct Hd as [d ->].
  destruct (bp_last (block_props_of s) =? 1).
  - apply vb_some_pair in H. destruct H as [<- <-]. unfold ZSTD_blockHeaderSize. split; [lia|].
    eexists; reflexivity.
  - destruct (decode_blocks fuel st' hist _ (out ++ d) bsm ws) as [[o' k']|] eqn:Er; [|discriminate].
    apply vb_some_pair in H. destruct H as [<- <-]. apply IH in Er; [|apply vb_bytes_skipn, Hs].
    destruct Er as [Hk' [d' ->]]. unfold ZSTD_blockHeaderSize. split; [lia|].
    exists (d ++ d'). rewrite app_assoc. reflexivity.
Qed.

Lemma vb_blocks hist bsm ws B fuel : forall st s out o k, bytes_ok s -> 0 <= B ->
  decode_blocks fuel st hist s out bsm ws = Some (o, k) -> k <= B -> Zlength o - Zlength out <= B ->
  decode_blocks fuel st hist s out (Z.min bsm B) ws = Some (o, k).
Proof.
  induction fuel as [|fuel IH]; intros st s out o k Hs HB H Hk Ho; [discriminate|].
  pose proof H as Hm. apply vb_blocks_mono in Hm; [|exact Hs].
  cbn [decode_blocks] in H |- *.
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  pose proof (vb_cblock_nonneg _ _ Hs Ec) as Hc0.
  destruct (c >? Zlength s - ZSTD_blockHeaderSize); [discriminate|].
  match type of H with context [match ?r with None => _ | Some _ => _ end] =>
    destruct r as [[st' out']|] eqn:Eres; [|discriminate] end.
  assert (Hd: exists d, out' = out ++ d).
  { clear H. repeat match type of Eres with
    | context [if ?c then _ else _] => destruct c
    | context [match ?x with Some _ => _ | None => _ end] => destruct x as [[? ?]|]
    end; try discriminate; apply vb_some_pair in Eres; destruct Eres as [_ <-]; eexists; reflexivity. }
  assert (Hpost: 3 + c <= k /\ exists e, o = out' ++ e).
  { destruct (bp_last (block_props_of s) =? 1).
    - apply vb_some_pair in H. destruct H as [<- <-]. unfold ZSTD_blockHeaderSize. split; [lia|].
      exists nil; rewrite app_nil_r; reflexivity.
    - destruct (decode_blocks fuel st' hist _ out' bsm ws) as [[o' k']|] eqn:Er; [|discriminate].
      apply vb_some_pair in H. destruct H as [<- <-]. apply vb_blocks_mono in Er; [|apply vb_bytes_skipn, Hs].
      destruct Er as [Hk' [e ->]]. unfold ZSTD_blockHeaderSize. split; [lia|]. exists e; reflexivity. }
  destruct Hd as [d Hd]. destruct Hpost as [Hck [e He]].
  assert (Hdl: Zlength d <= B).
  { subst o out'. rewrite !Zlength_correct, !length_app in Ho. rewrite Zlength_correct. lia. }
  assert (HcB: c <= B) by lia.
  assert (Hbody: Zlength (slice s ZSTD_blockHeaderSize c) <= B).
  { unfold slice. rewrite Zlength_correct, length_firstn. lia. }
  match goal with |- match ?r with Some _ => _ | None => _ end = _ =>
    assert (Hres: r = Some (st', out')) end.
  { clear H. subst out'.
    assert (Hgt: forall x, (x >? bsm) = false -> x <= B -> (x >? Z.min bsm B) = false)
      by (intros x; rewrite !Z.gtb_ltb, !Z.ltb_ge; lia).
    destruct (bp_type (block_props_of s) =? 0).
    - destruct (c >? bsm) eqn:E1; [discriminate|]. rewrite (Hgt c E1 HcB). exact Eres.
    - destruct (bp_type (block_props_of s) =? 1).
      + destruct (bp_origSize (block_props_of s) >? bsm) eqn:E1; [discriminate|].
        destruct (c >? bsm) eqn:E2; [discriminate|]. cbn [orb] in Eres |- *.
        pose proof Eres as Ec2. apply vb_some_pair in Ec2. destruct Ec2 as [_ Ec2]. apply app_inv_head in Ec2.
        assert (Hos: bp_origSize (block_props_of s) <= B).
        { rewrite <- Ec2, Zlength_correct, repeat_length in Hdl. lia. }
        rewrite (Hgt _ E1 Hos), (Hgt c E2 HcB). exact Eres.
      + destruct (decode_block st hist out (slice s ZSTD_blockHeaderSize c) bsm ws) as [[st0 content]|] eqn:Eb;
          [|discriminate].
        pose proof Eres as Ec2. apply vb_some_pair in Ec2. destruct Ec2 as [_ Ec2]. apply app_inv_head in Ec2.
        subst content. rewrite (vb_block _ _ _ _ _ _ _ _ _ Eb Hbody Hdl). exact Eres. }
  rewrite Hres. cbv beta iota.
  destruct (bp_last (block_props_of s) =? 1); [exact H|].
  destruct (decode_blocks fuel st' hist _ out' bsm ws) as [[o' k']|] eqn:Er; [|discriminate].
  apply vb_some_pair in H. destruct H as [<- <-].
  pose proof Er as Erm. apply vb_blocks_mono in Erm; [|apply vb_bytes_skipn, Hs]. destruct Erm as [Hk' _].
  assert (Hl1: Zlength o' - Zlength out' <= B).
  { rewrite He, Hd in Ho |- *. rewrite !Zlength_correct, !length_app in *. lia. }
  unfold ZSTD_blockHeaderSize in Hck.
  rewrite (IH _ _ _ _ _ (vb_bytes_skipn _ _ Hs) HB Er) by (unfold ZSTD_blockHeaderSize in *; lia).
  reflexivity.
Qed.

Lemma vb_nth4_nonneg n (l: list Z) : Forall (fun x => 0 <= x) l -> 0 <= nth n l 0.
Proof.
  intros H. revert n. induction H as [|x l Hx _ IH]; intros [|n]; cbn [nth]; try lia. apply IH.
Qed.

Lemma vb_fhd_nonneg x : 0 <= fhd_header_size x.
Proof.
  unfold fhd_header_size. cbv zeta.
  assert (0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { assert (Z.land (Z.shiftr x 5) 1 = Z.shiftr x 5 mod 2) as ->
      by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2). lia. }
  pose proof (vb_nth4_nonneg (Z.to_nat (Z.land x 3)) [0; 1; 2; 4] ltac:(repeat constructor; lia)).
  pose proof (vb_nth4_nonneg (Z.to_nat (Z.shiftr x 6)) [0; 2; 4; 8] ltac:(repeat constructor; lia)).
  destruct (_ && _); lia.
Qed.

Lemma vb_gfh_hs s h : get_frame_header s = FH_ok h -> 0 <= fh_headerSize h.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; apply (f_equal (fun r => match r with FH_ok h => fh_headerSize h | _ => 0 end)) in H;
  cbv beta iota in H; cbn [fh_headerSize] in H; rewrite <- H;
  first [apply vb_fhd_nonneg | unfold ZSTD_SKIPPABLEHEADERSIZE; lia].
Qed.

Lemma vb_frame dm wl s blim c k : bytes_ok s -> 0 <= blim ->
  decode_frame dm wl s = FOk c k -> k <= blim -> Zlength c <= blim ->
  decode_frame_m (md_bm blim) dm wl s = FOk c k.
Proof.
  intros Hs HB H Hk Hc.
  unfold decode_frame in H. unfold decode_frame_m, get_frame_header_m.
  cbn [md_magicless md_ignore md_bmax md_dwin md_bm negb andb]. rewrite !Z.sub_0_r.
  repeat match type of H with
  | context [if ?c then _ else _] => lazymatch c with context [decode_blocks] => fail | _ => destruct c end
  | context [match ?x with FH_ok _ => _ | _ => _ end] => destruct x as [| |h] eqn:Eh
  end; try discriminate.
  all: match type of H with context [decode_blocks ?a ?b ?c ?d ?e ?f ?g] =>
    destruct (decode_blocks a b c d e f g) as [[out k0]|] eqn:Eb; [|discriminate] end.
  all: pose proof (vb_gfh_hs _ _ Eh) as Hhs.
  all: assert (Hpost: out = c /\ fh_headerSize h + k0 <= k)
         by (clear - H; repeat match type of H with context [if ?c then _ else _] => destruct c end;
             try discriminate; apply vb_fok in H; destruct H as [-> <-]; split; [reflexivity | lia]).
  all: destruct Hpost as [-> Hk0]; pose proof (vb_blocks_mono _ _ _ _ _ _ _ _ _ (vb_bytes_skipn _ _ Hs) Eb) as [Hk3 _].
  all: rewrite (vb_blocks _ _ _ _ _ _ _ _ _ _ (vb_bytes_skipn _ _ Hs) HB Eb) by (simpl; rewrite ?Z.sub_0_r; lia).
  all: exact H.
Qed.

Lemma vb_frame_hdr dm wl s blim :
  decode_frame dm wl s = FDetHdr -> decode_frame_m (md_bm blim) dm wl s = FDetHdr.
Proof.
  intros H.
  unfold decode_frame in H. unfold decode_frame_m, get_frame_header_m.
  cbn [md_magicless md_ignore md_bmax md_dwin md_bm negb andb]. rewrite !Z.sub_0_r.
  repeat match type of H with
  | context [if ?c then _ else _] => lazymatch c with context [decode_blocks] => fail | _ => destruct c end
  | context [match ?x with FH_ok _ => _ | _ => _ end] => destruct x as [| |h] eqn:Eh
  end; try discriminate; try reflexivity.
  all: exfalso; match type of H with context [decode_blocks ?a ?b ?c ?d ?e ?f ?g] =>
    destruct (decode_blocks a b c d e f g) as [[out k0]|]; [|discriminate] end.
  all: repeat match type of H with context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Lemma vb_walk_S f dm blim wl s off : walk_m (S f) (md_bm blim) sel_none (Some dm) wl s off =
      if Zlength s <? ZSTD_FRAMEHEADERSIZE_PREFIX then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk_m f (md_bm blim) sel_none (Some dm) wl (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match decode_frame_m (md_bm blim) dm wl s with
        | FOk c k =>
            let '(l, t) := walk_m f (md_bm blim) sel_none (Some dm) wl (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
        | FDetHdr => (nil, TDetHdr)
        | FDetCk => (nil, TDetCk)
        | FUnk => (nil, TUnk)
        end.
Proof.
  cbn [walk_m md_magicless md_bm negb andb]. unfold starting_len.
  assert (Hd: frame_dict false sel_none (Some dm) s = Some dm).
  { unfold frame_dict, sel_none. destruct (get_frame_header_m false s); reflexivity. }
  rewrite Hd. reflexivity.
Qed.

Lemma vb_walk_frames : forall dm ws wl blim S n cn T fs off coff fuel,
  0 <= blim -> bytes_ok S ->
  tiles fs off coff n cn -> 0 <= off ->
  Forall (frame_facts dm ws) fs ->
  Forall (fun f => firstn (Z.to_nat (wi_size f)) (skipn (Z.to_nat (wi_start f)) S) = wi_bytes ws f /\
                   wi_end f <= Zlength S) fs ->
  Forall (fun f => wi_skippable f = false -> wi_csize f <= blim /\ wi_size f <= blim) fs ->
  (forall fuel, (length (skipn (Z.to_nat n) S) < fuel)%nat ->
     walk_m fuel (md_bm blim) sel_none (Some dm) wl (skipn (Z.to_nat n) S) n = (nil, T)) ->
  (length (skipn (Z.to_nat off) S) < fuel)%nat ->
  walk_m fuel (md_bm blim) sel_none (Some dm) wl (skipn (Z.to_nat off) S) off =
    (map (frec_of ws) (ok_prefix wl fs), if all_ok wl fs then T else TDetHdr).
Proof.
  intros dm ws wl blim S n cn T fs. induction fs as [|f fs IH];
    intros off coff fuel HB HS Ht Hoff Hff Hpl Hlim HT Hfuel.
  - simpl in Ht. destruct Ht as [-> ->]. simpl. apply HT; auto.
  - simpl in Ht. destruct Ht as (Hst & Hcst & Hsz & Hcsz & Hskc & Ht).
    inversion Hff as [|? ? Hf Hff']; subst. inversion Hpl as [|? ? [Hfb Hend] Hpl']; subst.
    inversion Hlim as [|? ? Hl1 Hlim']; subst.
    set (fb := wi_bytes ws f) in *.
    set (r := skipn (Z.to_nat (wi_start f + wi_size f)) S).
    assert (Hlenfb : length fb = Z.to_nat (wi_size f)).
    { subst fb. rewrite <- Hfb, length_firstn, length_skipn. unfold wi_end in Hend.
      rewrite Zlength_correct in Hend. lia. }
    assert (Hs : skipn (Z.to_nat (wi_start f)) S = fb ++ r).
    { subst r. rewrite <- Hfb, Z2Nat.inj_add by lia. rewrite Nat.add_comm, <- skipn_skipn.
      symmetry. apply firstn_skipn. }
    assert (Hskr : skipn (Z.to_nat (wi_size f)) (fb ++ r) = r).
    { rewrite skipn_app, Hlenfb, Nat.sub_diag, skipn_all2 by lia. reflexivity. }
    assert (Hbs : bytes_ok (fb ++ r)) by (rewrite <- Hs; apply vb_bytes_skipn, HS).
    rewrite Hs in Hfuel |- *. rewrite length_app in Hfuel.
    destruct fuel as [|fuel]; [lia|].
    assert (Hfr : (length (skipn (Z.to_nat (wi_start f + wi_size f)) S) < fuel)%nat).
    { fold r. assert (0 < length fb)%nat by lia. lia. }
    destruct Hf as (_ & _ & _ & _ & _ & _ & _ & Hsk & Hdec). fold fb in Hsk, Hdec.
    rewrite vb_walk_S. destruct (wi_skippable f) eqn:Eskip.
    + destruct (Hsk eq_refl) as (_ & Hl8 & Hmag & Hsfs & _).
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. rewrite Zlength_correct, length_app. rewrite Zlength_correct in Hl8.
        unfold ZSTD_SKIPPABLEHEADERSIZE, ZSTD_FRAMEHEADERSIZE_PREFIX in *. lia. }
      rewrite sl_le_field_app, Hmag, Hsfs, Hskr
        by (unfold ZSTD_SKIPPABLEHEADERSIZE in Hl8; lia).
      subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
      assert (Hrej : wi_rejected wl f = false) by (unfold wi_rejected; rewrite Eskip; reflexivity).
      simpl. rewrite Hrej. simpl. f_equal. f_equal. unfold frec_of, wi_content, slice.
      rewrite Eskip, (Hskc eq_refl). simpl. f_equal; auto.
    + destruct (Hdec eq_refl) as (Hd & _ & _). specialize (Hd wl r).
      destruct (Hl1 eq_refl) as [Hcb Hsb].
      assert (Hdm : decode_frame_m (md_bm blim) dm wl (fb ++ r) =
                    if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f)).
      { destruct (wi_rejected wl f).
        - apply vb_frame_hdr. exact Hd.
        - apply vb_frame; auto. unfold wi_content, slice. rewrite Zlength_correct, length_firstn. lia. }
      assert (decode_frame dm wl (fb ++ r) <> FUnk) as Hnu
        by (rewrite Hd; destruct (wi_rejected wl f); discriminate).
      apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
      assert (Zlength (fb ++ r) <? ZSTD_FRAMEHEADERSIZE_PREFIX = false) as ->.
      { apply Z.ltb_ge. unfold ZSTD_FRAMEHEADERSIZE_PREFIX. lia. }
      rewrite Hmag. change (is_skippable_magic ZSTD_MAGICNUMBER) with false. cbv iota beta.
      rewrite Hdm. simpl ok_prefix. simpl all_ok. destruct (wi_rejected wl f) eqn:Erej.
      * reflexivity.
      * rewrite Hskr. subst r. rewrite (IH (wi_start f + wi_size f) (wi_cstart f + wi_csize f) fuel) by (auto; lia).
        simpl. f_equal. f_equal. unfold frec_of. rewrite Eskip. f_equal; auto.
Qed.

End VPBlk.
Import VPBlk.

(* mode 2: every Zstandard frame (its content and its bytes) within the block size limit *)
Theorem vp_bm_written ws blim : series_facts no_dict ws -> wseries_wf ws -> 1024 <= blim <= ZSTD_BLOCKSIZE_MAX ->
  Forall (fun f => wi_skippable f = false -> wi_csize f <= blim /\ wi_size f <= blim) (ws_frames ws) ->
  vp_written (md_bm blim) ws.
Proof.
  intros Hsf _ Hbl Hlim. pose proof Hsf as (Hb & Hc & _ & _ & Hn & Ht & Hff & _).
  split; [exact Hb|]. split; [exact Hc|]. split; [lia|]. split; [exact Ht|].
  intros wl. pose proof (sl_tiles_bounds _ _ _ _ _ Ht) as (_ & _ & Hbd).
  unfold series_frames_m. change (ws_bytes ws) with (skipn (Z.to_nat 0) (ws_bytes ws)) at 1.
  apply (vb_walk_frames no_dict ws wl blim (ws_bytes ws) (Zlength (ws_bytes ws)) (Zlength (ws_content ws))
           TEnd _ 0 0); auto; try lia.
  - eapply Forall_impl; [|exact Hbd]. simpl. intros f Hf. split; [reflexivity|lia].
  - intros fuel Hfuel. rewrite Zlength_correct, Nat2Z.id, skipn_all.
    destruct fuel; [simpl in Hfuel; lia|]. reflexivity.
Qed.

(* ---------- mode 3: the magicless format reads the frame behind its magic number ---------- *)

Lemma vpm_bytes_skipn : forall n (l: list Z), bytes_ok l -> bytes_ok (skipn n l).
Proof.
  intros n l H. unfold bytes_ok in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. apply H.
Qed.

Lemma vpm_bytes_firstn : forall n (l: list Z), bytes_ok l -> bytes_ok (firstn n l).
Proof.
  intros n l H. unfold bytes_ok in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. apply H.
Qed.

Lemma vpm_le_value_nonneg : forall l, bytes_ok l -> 0 <= le_value l.
Proof.
  induction l as [|b l IH]; cbn [le_value]; intros H; [lia|]. inversion H as [|? ? Hb Hl]; subst.
  specialize (IH Hl). unfold is_byte in Hb. lia.
Qed.

Lemma vpm_le_field_nonneg : forall l i k, bytes_ok l -> 0 <= le_field l i k.
Proof.
  intros l i k H. unfold le_field, slice. apply vpm_le_value_nonneg, vpm_bytes_firstn, vpm_bytes_skipn, H.
Qed.

Lemma vpm_decode_blocks_k : forall fuel st hist s out bsm wsize o k, bytes_ok s ->
  decode_blocks fuel st hist s out bsm wsize = Some (o, k) -> 0 <= k.
Proof.
  induction fuel as [|fuel IH]; intros st hist s out bsm wsize o k Hb H; cbn [decode_blocks] in H; [discriminate|].
  destruct (cblock_size s) as [c|] eqn:Ec; [|discriminate].
  assert (Hc : 0 <= c).
  { unfold cblock_size in Ec. destruct (Zlength s <? ZSTD_blockHeaderSize); [discriminate|].
    destruct (bp_type (block_props_of s) =? 1); [injection Ec as <-; lia|].
    destruct (bp_type (block_props_of s) =? 3); [discriminate|]. injection Ec as <-.
    simpl. apply Z.shiftr_nonneg, vpm_le_field_nonneg, Hb. }
  repeat match type of H with
  | context [if ?x then _ else _] => destruct x
  | context [match ?x with _ => _ end] =>
      lazymatch x with
      | decode_blocks _ _ _ _ _ _ _ => destruct x as [[o' k']|] eqn:Er
      | _ => lazymatch type of x with option _ => destruct x eqn:? | bool => destruct x eqn:? | prod _ _ => destruct x end
      end
  end; try discriminate;
  pose proof (f_equal (fun p => match p with Some (_, k) => k | None => 0 end) H) as Hk; cbv beta iota in Hk;
  subst k; assert (E3 : ZSTD_blockHeaderSize = 3) by reflexivity; try lia;
  try (apply IH in Er; [lia|apply vpm_bytes_skipn, Hb]).
Qed.

Lemma vpm_fhd_ge5 : forall x, 5 <= fhd_header_size x.
Proof.
  intros x. unfold fhd_header_size.
  assert (Hs : 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { assert (Z.land (Z.shiftr x 5) 1 = Z.shiftr x 5 mod 2) as ->
      by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2). lia. }
  assert (H1 : forall n, 0 <= nth n [0; 1; 2; 4] 0) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; lia).
  assert (H2 : forall n, 0 <= nth n [0; 2; 4; 8] 0) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; lia).
  specialize (H1 (Z.to_nat (Z.land x 3))). specialize (H2 (Z.to_nat (Z.shiftr x 6))).
  destruct ((Z.land (Z.shiftr x 5) 1 =? 1) && (Z.shiftr x 6 =? 0)); lia.
Qed.

Lemma vpm_gfh_hs : forall s h, get_frame_header s = FH_ok h -> 5 <= fh_headerSize h.
Proof.
  intros s h H. unfold get_frame_header in H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia); apply vpm_fhd_ge5.
Qed.

Lemma vpm_fh_bmax (s: list Z) (h: frame_header) :
  get_frame_header s = FH_ok h -> fh_blockSizeMax h <= ZSTD_BLOCKSIZE_MAX.
Proof.
  unfold get_frame_header. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c
  end; try discriminate; inversion H; subst; simpl;
  unfold ZSTD_BLOCKSIZE_MAX; lia.
Qed.

Lemma vpm_magic_bytes : magic_bytes = [40; 181; 47; 253].
Proof. reflexivity. Qed.

Lemma vpm_frame_mg : forall dm wl s, bytes_ok s ->
  decode_frame_m md_mg dm wl s =
    match decode_frame dm wl (magic_bytes ++ s) with FOk c k => FOk c (k - 4) | r => r end.
Proof.
  intros dm wl s Hb.
  assert (HZ : Zlength (magic_bytes ++ s) = Zlength s + 4)
    by (rewrite vpm_magic_bytes, !Zlength_correct, length_app; simpl length; lia).
  assert (HM : le_field (magic_bytes ++ s) 0 4 = ZSTD_MAGICNUMBER)
    by (rewrite vpm_magic_bytes; reflexivity).
  assert (H4 : byte_at (magic_bytes ++ s) 4 = byte_at s 0) by (rewrite vpm_magic_bytes; reflexivity).
  assert (H5 : byte_at (magic_bytes ++ s) 5 = byte_at s 1) by (rewrite vpm_magic_bytes; reflexivity).
  assert (Hsk : forall p, 4 <= p -> skipn (Z.to_nat p) (magic_bytes ++ s) = skipn (Z.to_nat (p - 4)) s).
  { intros p Hp. rewrite vpm_magic_bytes. replace (Z.to_nat p) with (4 + Z.to_nat (p - 4))%nat by lia.
    reflexivity. }
  unfold decode_frame_m, decode_frame. cbn [md_magicless md_ignore md_bmax md_dwin md_mg negb andb].
  rewrite HZ, HM, H4, H5. change (4 - 4) with 0. change (5 - 4) with 1.
  change (negb (ZSTD_MAGICNUMBER =? ZSTD_MAGICNUMBER)) with false. cbv iota.
  unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize.
  destruct (Zlength s <? 6 - 4 + 3) eqn:E1.
  { assert (Zlength s + 4 <? 6 + 3 = true) as -> by (apply Z.ltb_lt; apply Z.ltb_lt in E1; lia). reflexivity. }
  assert (Zlength s + 4 <? 6 + 3 = false) as -> by (apply Z.ltb_ge; apply Z.ltb_ge in E1; lia).
  destruct (Zlength s <? fhd_header_size (byte_at s 0) - 4 + 3) eqn:E2.
  { assert (Zlength s + 4 <? fhd_header_size (byte_at s 0) + 3 = true) as ->
      by (apply Z.ltb_lt; apply Z.ltb_lt in E2; lia). reflexivity. }
  assert (Zlength s + 4 <? fhd_header_size (byte_at s 0) + 3 = false) as ->
    by (apply Z.ltb_ge; apply Z.ltb_ge in E2; lia).
  destruct (negb (Z.land (byte_at s 0) 8 =? 0)); [reflexivity|].
  match goal with |- (if ?c then _ else _) = _ => destruct c end; [reflexivity|].
  unfold get_frame_header_m. cbn [negb].
  assert (Zlength s <? 1 = false) as -> by (apply Z.ltb_ge; apply Z.ltb_ge in E1; lia).
  destruct (get_frame_header (magic_bytes ++ s)) as [|k|h] eqn:Eg; try reflexivity.
  pose proof (vpm_gfh_hs _ _ Eg) as Hhs. pose proof (vpm_fh_bmax _ _ Eg) as Hbm.
  cbn [fh_unshift fh_windowSize fh_frameType fh_dictID fh_headerSize fh_blockSizeMax fh_contentSize
       fh_checksumFlag].
  destruct (fh_windowSize h >? wl); [reflexivity|].
  destruct (negb (fh_frameType h =? 0)); [reflexivity|].
  destruct (negb (fh_dictID h =? 0) && negb (fh_dictID h =? dm_id dm)); [reflexivity|].
  rewrite (Z.min_l _ _ Hbm), (Hsk (fh_headerSize h)) by lia.
  destruct (decode_blocks _ _ _ _ _ _ _) as [[out k]|] eqn:Ed; [|reflexivity].
  apply vpm_decode_blocks_k in Ed; [|apply vpm_bytes_skipn, Hb].
  destruct (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) && negb (Zlength out =? fh_contentSize h));
    [reflexivity|].
  destruct (fh_checksumFlag h =? 1).
  - replace (Zlength s - (fh_headerSize h - 4) - k) with (Zlength s + 4 - fh_headerSize h - k) by lia.
    destruct (Zlength s + 4 - fh_headerSize h - k <? 4); [reflexivity|].
    assert (Hf : le_field s (fh_headerSize h - 4 + k) 4 = le_field (magic_bytes ++ s) (fh_headerSize h + k) 4).
    { unfold le_field, slice. rewrite (Hsk (fh_headerSize h + k)) by lia. do 3 f_equal. lia. }
    rewrite Hf. cbn [negb andb].
    destruct (negb (le_field (magic_bytes ++ s) (fh_headerSize h + k) 4 =? Xxh64.xxh64 out 0 mod 2 ^ 32));
      [reflexivity|].
    f_equal. lia.
  - f_equal. lia.
Qed.

Lemma vpm_magic_split : forall s, bytes_ok s -> 4 <= Zlength s -> le_field s 0 4 = ZSTD_MAGICNUMBER ->
  s = magic_bytes ++ skipn 4 s.
Proof.
  intros s Hb Hl Hm. rewrite vpm_magic_bytes.
  destruct s as [|a [|b [|c [|d s]]]]; rewrite ?Zlength_cons, ?Zlength_nil in Hl;
    try lia.
  unfold bytes_ok in Hb.
  pose proof (Forall_inv Hb) as Ha. apply Forall_inv_tail in Hb.
  pose proof (Forall_inv Hb) as Hbb. apply Forall_inv_tail in Hb.
  pose proof (Forall_inv Hb) as Hc. apply Forall_inv_tail in Hb.
  pose proof (Forall_inv Hb) as Hd.
  unfold le_field, slice in Hm. change (Z.to_nat 4) with 4%nat in Hm. change (Z.to_nat 0) with 0%nat in Hm.
  cbn [skipn firstn le_value] in Hm. unfold is_byte, ZSTD_MAGICNUMBER in *.
  simpl. repeat f_equal; lia.
Qed.

Lemma vpm_walk_S : forall fu md sel cur wlim s off, walk_m (S fu) md sel cur wlim s off =
      let mg := md_magicless md in
      if Zlength s <? starting_len mg then (nil, if Zlength s =? 0 then TEnd else TUnk) else
      if negb mg && is_skippable_magic (le_field s 0 4) then
        match skippable_frame_size s with
        | None => (nil, TUnk)
        | Some k =>
            let '(l, t) := walk_m fu md sel
                             (if md_dwin md
                              then match sel (Z.land (le_field s 0 4) 15) with Some d => Some d | None => cur end
                              else cur) wlim (skipn (Z.to_nat k) s) (off + k) in
            ({| fr_start := off; fr_size := k; fr_content := nil; fr_skippable := true |} :: l, t)
        end
      else
        match frame_dict mg sel cur s with
        | None => (nil, TUnk)
        | Some d =>
            match decode_frame_m md d wlim s with
            | FOk c k =>
                let '(l, t) := walk_m fu md sel (Some d) wlim (skipn (Z.to_nat k) s) (off + k) in
                ({| fr_start := off; fr_size := k; fr_content := c; fr_skippable := false |} :: l, t)
            | FDetHdr => (nil, TDetHdr)
            | FDetCk => (nil, TDetCk)
            | FUnk => (nil, TUnk)
            end
        end.
Proof. reflexivity. Qed.

(* mode 3: one Zstandard frame without its magic number, decoded in the magicless format; and
   ZSTD_getFrameHeader_advanced(ZSTD_f_zstd1_magicless) on it *)
Theorem vp_mg_written ws f : series_facts no_dict ws -> wseries_wf ws -> ws_frames ws = [f] ->
  wi_skippable f = false ->
  vp_written md_mg (ws_unmagic ws) /\
  get_frame_header_m true (ws_bytes (ws_unmagic ws)) =
    (if wi_big f then FH_err else FH_ok (fh_unshift (wi_header f))).
Proof.
  intros Hsf Hwf Hfs Hnsk.
  pose proof Hsf as (Hb & Hc & _ & _ & _ & Ht & Hff & _).
  rewrite Hfs in Ht, Hff. simpl in Ht. destruct Ht as (Hst & Hcst & Hsz & Hcsz & _ & Hn & Hcn).
  inversion Hff as [|? ? Hf _]; subst.
  destruct Hf as (_ & _ & _ & Hgfh & _ & _ & _ & _ & Hdec).
  destruct (Hdec Hnsk) as (Hd & _ & _). clear Hdec Hff.
  set (s := ws_bytes ws) in *.
  assert (Hfb : wi_bytes ws f = s).
  { unfold wi_bytes, slice. fold s. rewrite Hst. simpl skipn. rewrite Hn.
    rewrite Zlength_correct, Nat2Z.id. apply firstn_all. }
  rewrite Hst in Hgfh. simpl in Hgfh. fold s in Hgfh.
  assert (Hd' : forall wl, decode_frame no_dict wl s =
            if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f)).
  { intros wl. rewrite <- (app_nil_r s), <- Hfb at 1. apply Hd. }
  assert (Hnu : decode_frame no_dict 0 s <> FUnk) by (rewrite Hd'; destruct (wi_rejected 0 f); discriminate).
  apply sl_decode_frame_not_unk in Hnu. destruct Hnu as [H9 Hmag].
  pose proof (vpm_magic_split s Hb ltac:(lia) Hmag) as Hsplit.
  assert (Hb' : bytes_ok (skipn 4 s)) by (apply vpm_bytes_skipn, Hb).
  assert (Hl' : Zlength (skipn 4 s) = Zlength s - 4).
  { rewrite !Zlength_correct, length_skipn. rewrite Zlength_correct in H9. lia. }
  assert (Hmg : forall wl, decode_frame_m md_mg no_dict wl (skipn 4 s) =
            if wi_rejected wl f then FDetHdr else FOk (wi_content ws f) (wi_size f - 4)).
  { intros wl. rewrite vpm_frame_mg, <- Hsplit, Hd' by exact Hb'. destruct (wi_rejected wl f); reflexivity. }
  assert (Hrej : forall wl, wi_rejected wl (wi_unmagic f) = wi_rejected wl f) by reflexivity.
  unfold vp_written. cbn [ws_unmagic ws_bytes ws_content ws_frames]. fold s. rewrite Hfs. cbn [map].
  split.
  2:{ unfold get_frame_header_m. cbn [negb].
      assert (Zlength (skipn 4 s) <? 1 = false) as -> by (apply Z.ltb_ge; lia).
      rewrite <- Hsplit, Hgfh. destruct (wi_big f); reflexivity. }
  split; [exact Hb'|]. split; [exact Hc|]. split; [simpl; lia|]. split.
  { cbn [tiles wi_unmagic wi_start wi_cstart wi_size wi_csize wi_skippable]. rewrite Hl'.
    repeat split; try lia; intros; congruence. }
  intros wl. unfold series_frames_m. rewrite vpm_walk_S. cbv zeta. cbn [md_magicless md_mg starting_len negb andb].
  assert (Zlength (skipn 4 s) <? 1 = false) as -> by (apply Z.ltb_ge; lia).
  assert (Hfd : frame_dict true sel_none (Some no_dict) (skipn 4 s) = Some no_dict)
    by (unfold frame_dict, sel_none; destruct (get_frame_header_m true (skipn 4 s)); reflexivity).
  rewrite Hfd, Hmg. cbn [ok_prefix all_ok forallb]. rewrite Hrej.
  destruct (wi_rejected wl f) eqn:Er; [reflexivity|].
  assert (Hnil : skipn (Z.to_nat (wi_size f - 4)) (skipn 4 s) = nil).
  { apply skipn_all2. rewrite Zlength_correct in Hl'. lia. }
  remember (length (skipn 4 s)) as n eqn:En. destruct n as [|n].
  { rewrite Zlength_correct, <- En in Hl'. lia. }
  rewrite Hnil, vpm_walk_S. cbv zeta. cbn [md_magicless md_mg starting_len Zlength Zlength_aux].
  simpl. unfold frec_of. cbn [wi_unmagic wi_start wi_size wi_skippable]. rewrite Hst, Hnsk. reflexivity.
Qed.
