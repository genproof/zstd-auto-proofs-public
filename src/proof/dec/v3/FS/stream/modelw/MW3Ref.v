(* FS3 streaming model facts: the refusal walk of model/Refuse.v (walk_refused, series_refused_m,
   frame_refused_m) along the walk of the model (MW3Walk.wfirst).  What the stream's dead states need:
   - a refusal of a series that starts with frames the model decodes is a refusal of the rest
     (series_refused_app), so a dead current frame makes the whole stream dead;
   - the refusal of a Zstandard frame survives cutting the bytes after its header (frame_refused_prefix: a
     refusal is a cut, a bad block header or a bad end, all of which stay where they are) and dropping the
     dictionary window rule (frame_refused_len: where decode_block_w decodes, decode_block agrees). *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series Zstd.proof.model.StreamModel Zstd.proof.model.Params.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Zstd.proof.model.ParamsW Zstd.proof.model.Refuse Zstd.proof.dec.v3.FS.stream.S3ModelDefs Zstd.proof.dec.v3.FS.stream.modelw.MW3Base Zstd.proof.dec.v3.FS.stream.modelw.MW3Frame Zstd.proof.dec.v3.FS.stream.modelw.MW3FrameM Zstd.proof.dec.v3.FS.stream.modelw.MW3Walk.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------- the series walk ---------- *)

Section R.
Variable md : dmode.
Variable sel : Z -> option dict_model.
Local Notation mg := (md_magicless md).

(* the refusal where the model's walk stops (wfirst answers inr) *)
Definition wref (cur: option dict_model) (w: Z) (s: list Z) : Prop :=
  if Zlength s <? starting_len mg then Zlength s <> 0 else
  if negb mg && is_skippable_magic (le_field s 0 4) then False else
  match frame_dict mg sel cur s with
  | None => False
  | Some d => match decode_frame_m md d w s with FUnk => frame_refused_m md d w s | _ => False end
  end.

Lemma wref_S : forall f cur w s, walk_refused (S f) md sel cur w s =
  match wfirst md sel cur w s with
  | inl (k, _, _, cur') => walk_refused f md sel cur' w (skipn (Z.to_nat k) s)
  | inr _ => wref cur w s
  end.
Proof.
  intros. unfold wfirst, wref. cbn [walk_refused]. unfold skip_cd.
  destruct (Zlength s <? starting_len mg); auto.
  destruct (negb mg && _); [destruct (skippable_frame_size s); auto|].
  destruct (frame_dict _ _ _ _); auto. destruct (decode_frame_m _ _ _ _); auto.
Qed.

(* the refusal at a Zstandard frame the dictionary d decodes *)
Lemma wref_dict : forall cur w s d, starting_len mg <= Zlength s ->
  negb mg && is_skippable_magic (le_field s 0 4) = false -> frame_dict mg sel cur s = Some d ->
  wref cur w s = match decode_frame_m md d w s with FUnk => frame_refused_m md d w s | _ => False end.
Proof.
  intros cur w s d Hl Hsk Hd. unfold wref.
  replace (Zlength s <? starting_len mg) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hsk, Hd. reflexivity.
Qed.

Lemma walk_refused_loop : forall cur w s k c sk cur', wfirst md sel cur w s = inl (k, c, sk, cur') ->
  Z.to_nat k = 0%nat -> forall f, ~ walk_refused f md sel cur' w s.
Proof.
  intros cur w s k c sk cur' H Hk. apply wfirst_loop_cur in H. induction f; [simpl; tauto|].
  rewrite wref_S, H, Hk. simpl skipn. auto.
Qed.

Lemma walk_refused_fuel : forall n s, (length s <= n)%nat -> forall cur w f1 f2,
  (S (length s) <= f1)%nat -> (S (length s) <= f2)%nat ->
  walk_refused f1 md sel cur w s -> walk_refused f2 md sel cur w s.
Proof.
  induction n; intros s Hn cur w f1 f2 H1 H2 R.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    rewrite wref_S in *. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E; auto.
    apply wfirst_len in E. pose proof (starting_len_pos mg). rewrite Zlength_correct in E. lia.
  - destruct f1 as [|f1]; [lia|]. destruct f2 as [|f2]; [lia|].
    rewrite wref_S in *. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E; auto.
    destruct (Nat.eq_dec (Z.to_nat k) 0) as [e|e].
    + exfalso. rewrite e in R. simpl skipn in R. exact (walk_refused_loop _ _ _ _ _ _ _ E e f1 R).
    + pose proof (wfirst_len _ _ _ _ _ _ _ _ _ E). pose proof (starting_len_pos mg). rewrite Zlength_correct in *.
      assert (length (skipn (Z.to_nat k) s) < length s)%nat by (rewrite length_skipn; lia).
      apply (IHn (skipn (Z.to_nat k) s) ltac:(lia) cur' w f1 f2); auto; lia.
Qed.

(* the refusal walk over s ++ y goes through the frames of s (decoded, walk_m ends at TEnd) to y *)
Lemma walk_refused_app : forall f cur w s off l, walk_m f md sel cur w s off = (l, TEnd) -> bytes_ok s ->
  forall y F, walk_refused F md sel cur w (s ++ y) ->
  walk_refused (F - length l) md sel (walk_cur f md sel cur w s) w y.
Proof.
  induction f; intros cur w s off l H Hs y F R; [discriminate|].
  rewrite walk_S in H. rewrite walk_cur_S. destruct (wfirst md sel cur w s) as [[[[k c] sk] cur']|t] eqn:E.
  - destruct (walk_m f md sel cur' w (skipn (Z.to_nat k) s) (off + k)) as [l0 t0] eqn:E2.
    inversion H; subst; clear H.
    destruct (wfirst_ext md sel cur w s k c sk cur' y E Hs) as [Hkl Hext].
    destruct F as [|F]; [simpl in R; tauto|].
    rewrite wref_S, Hext, E in R.
    rewrite skipn_app_le in R by (rewrite Zlength_correct in Hkl; lia).
    exact (IHf _ _ _ _ _ E2 (bytes_ok_skipn _ _ Hs) y F R).
  - inversion H; subst; clear H. apply wfirst_end in E. subst s. simpl in *. rewrite Nat.sub_0_r. auto.
Qed.

Lemma series_refused_app : forall w cur dsin recs y,
  series_frames_m md sel cur w dsin = (recs, TEnd) -> bytes_ok dsin ->
  series_refused_m md sel cur w (dsin ++ y) -> series_refused_m md sel (series_cur md sel cur w dsin) w y.
Proof.
  unfold series_frames_m, series_cur, series_refused_m. intros w cur dsin recs y H Hb R.
  pose proof (walk_len _ _ _ _ _ _ _ _ _ H ltac:(discriminate)) as HL.
  pose proof (walk_refused_app _ _ _ _ _ _ H Hb y _ R) as R'.
  apply (walk_refused_fuel (length y) y (le_n _) _ _ (S (length (dsin ++ y)) - length recs)); auto;
    rewrite length_app in *; lia.
Qed.

End R.

(* ---------- the refusal of one frame ---------- *)

Lemma rblock_app : forall dw st hist s r out c bsm ws, 0 <= c -> ZSTD_blockHeaderSize + c <= Zlength s ->
  rblock dw st hist (s ++ r) out c bsm ws = rblock dw st hist s out c bsm ws.
Proof.
  intros. unfold rblock, ZSTD_blockHeaderSize in *. rewrite block_props_app by lia. rewrite slice_app by lia.
  reflexivity.
Qed.

(* the blocks of s ++ r end refused: those of s too (with enough fuel) *)
Lemma blocks_refused_prefix : forall f dw h st hist s r out bsm f', bytes_ok s -> (length s < f')%nat ->
  blocks_refused dw f h st hist (s ++ r) out bsm -> blocks_refused dw f' h st hist s out bsm.
Proof.
  induction f; intros dw h st hist s r out bsm f' Hb Hf R; [simpl in R; tauto|].
  destruct f' as [|f']; [lia|]. cbn [blocks_refused] in *.
  rewrite Zlength_app in R. pose proof (Zlength_nonneg r).
  destruct (Zlength s <? ZSTD_blockHeaderSize) eqn:E1; [exact I|]. apply Z.ltb_ge in E1.
  unfold ZSTD_blockHeaderSize in *.
  replace (Zlength s + Zlength r <? 3) with false in R by (symmetry; apply Z.ltb_ge; lia).
  rewrite block_props_app, cblock_size_app in R by lia.
  destruct (bp_type (block_props_of s) =? 3); [exact I|].
  destruct (cblock_size s) as [c|] eqn:Ec; [|exact R].
  pose proof (cblock_nonneg _ _ Hb Ec).
  destruct (c >? Zlength s - 3) eqn:E2; [exact I|]. apply Zgtb_le in E2.
  replace (c >? Zlength s + Zlength r - 3) with false in R by (symmetry; apply Zgtb_le; lia).
  rewrite rblock_app in R by (unfold ZSTD_blockHeaderSize; lia).
  destruct (rblock dw st hist s out c bsm (fh_windowSize h)) as [[st' out']|]; [|exact R].
  rewrite skipn_app_le in R by (rewrite Zlength_correct in E2; lia).
  destruct (bp_last (block_props_of s) =? 1).
  - unfold frame_end_refused in *. rewrite Zlength_app in R. pose proof (Zlength_nonneg r).
    destruct R as [R|[R1 R2]]; [left; auto|right; split; auto; lia].
  - eapply IHf; [apply bytes_ok_skipn; auto| |exact R].
    rewrite length_skipn. rewrite Zlength_correct in *. lia.
Qed.

(* with the dictionary window rule, the blocks end refused: without it too *)
Lemma blocks_refused_len : forall f h st hist s out bsm,
  blocks_refused true f h st hist s out bsm -> blocks_refused false f h st hist s out bsm.
Proof.
  induction f; intros h st hist s out bsm R; [exact R|]. cbn [blocks_refused] in *.
  destruct (Zlength s <? _); auto. destruct (_ =? 3); auto. destruct (cblock_size s) as [c|]; auto.
  destruct (c >? _); auto.
  destruct (rblock true st hist s out c bsm (fh_windowSize h)) as [[st' out']|] eqn:E; [|contradiction].
  replace (rblock false st hist s out c bsm (fh_windowSize h)) with (Some (st', out')).
  { destruct (bp_last _ =? 1); auto. }
  revert E. unfold rblock, rdec_block. cbv zeta.
  destruct (bp_type _ =? 0); auto. destruct (bp_type _ =? 1); auto.
  destruct (decode_block_w _ _ _ _ _ _) as [[st2 c2]|] eqn:D; [|discriminate].
  rewrite (pw_decode_block_w _ _ _ _ _ _ _ D). auto.
Qed.

Lemma frame_refused_len : forall md dm w s, frame_refused_m md dm w s -> frame_refused_m (md_len md) dm w s.
Proof.
  intros [a b c [|]] dm w s R; [|exact R]. unfold frame_refused_m, md_len in *.
  cbn [md_magicless md_dwin md_bmax] in *.
  destruct (Zlength s <? _); auto. destruct (get_frame_header_m a s); auto.
  destruct R as [R1 [R2 [R3 R4]]]. repeat split; auto. apply blocks_refused_len; auto.
Qed.

(* a frame whose header is in x, refused on x ++ r: refused on x *)
Lemma frame_refused_prefix : forall md dm w x r h, bytes_ok x -> get_frame_header_m (md_magicless md) x = FH_ok h ->
  frame_refused_m md dm w (x ++ r) -> frame_refused_m md dm w x.
Proof.
  intros md dm w x r h Hb G R. unfold frame_refused_m in *. cbv zeta in *.
  pose proof (gfhm_len _ _ _ G) as Hl.
  assert (Hhs: header_size_m (md_magicless md) (x ++ r) = header_size_m (md_magicless md) x).
  { unfold header_size_m, starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX in *.
    destruct (md_magicless md); rewrite byte_at_app; auto; lia. }
  rewrite Hhs, Zlength_app in R. pose proof (Zlength_nonneg r).
  destruct (Zlength x <? header_size_m _ x) eqn:E; [exact I|]. apply Z.ltb_ge in E.
  replace (Zlength x + Zlength r <? _) with false in R by (symmetry; apply Z.ltb_ge; lia).
  rewrite (gfhm_ext _ _ r _ G (bytes_ok_byte_at _ _ Hb)) in R. rewrite G.
  destruct R as [R1 [R2 [R3 R4]]]. split; [auto|]. split; [auto|]. split; [auto|].
  destruct (gfhm_info _ _ _ G) as [[_ [Ht _]]|[_ [_ [_ [Hs [Hle _]]]]]]; [congruence|].
  assert (0 <= fh_headerSize h)
    by (rewrite Hs; pose proof (fhs_ge5 (byte_at x (fpos (md_magicless md)))); unfold fsh;
        destruct (md_magicless md); lia).
  rewrite skipn_app_le in R4 by (rewrite Zlength_correct in Hle; lia).
  eapply blocks_refused_prefix; [apply bytes_ok_skipn; auto| |exact R4]. lia.
Qed.

(* a refused Zstandard frame with a complete header has a Dictionary_ID of 0 or the dictionary's *)
Lemma frame_refused_dict : forall md dm w x h, get_frame_header_m (md_magicless md) x = FH_ok h ->
  fh_frameType h = 0 -> fh_headerSize h <= Zlength x ->
  frame_refused_m md dm w x -> fh_dictID h = 0 \/ fh_dictID h = dm_id dm.
Proof.
  intros md dm w x h G Ht Hl R. unfold frame_refused_m in R. cbv zeta in R.
  destruct (gfhm_info _ _ _ G) as [[_ [Ht' _]]|[_ [_ [_ [Hs _]]]]]; [congruence|].
  replace (Zlength x <? header_size_m (md_magicless md) x) with false in R.
  2:{ symmetry. apply Z.ltb_ge. unfold header_size_m. rewrite Hs in Hl. unfold fpos, fsh in Hl.
      destruct (md_magicless md); lia. }
  rewrite G in R. tauto.
Qed.
