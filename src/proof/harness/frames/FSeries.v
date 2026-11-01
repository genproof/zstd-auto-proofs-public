(* Series of hand-built frames (harness/frames.h: new_frame, new_skippable, join) in zstd's format model
   (model/Params.v: decode_series_m, what ZSTD_decompress's specification states its result against).
   Plain Coq.  A series written frame by frame decodes frame by frame: a Zstandard frame of new_frame adds its
   data (nf_data), a skippable frame of new_skippable adds nothing.

   The skippable frame's size: the model's skippable_frame_size keeps zstd's former 32-bit test; the
   facts below that depend on it take its result as a hypothesis (sk_frame_size gives
   it below 2^32 bytes), so that they stay true when the test is dropped. *)
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Frame Zstd.proof.model.Block Zstd.proof.model.Series.
Require Import Zstd.proof.model.Params.
Require Export Zstd.proof.harness.frames.FModel.
Local Open Scope bool_scope.

(* ---------- the walk over a series ---------- *)

(* What decode_series_m makes of a walk: the walk's result.  It does not depend on the frames' offsets. *)
Definition walk_res (w: list frec * Series.tail) : sres :=
  match w with
  | (l, TEnd) => SOk (flat_map fr_content l)
  | (_, TDetHdr) => SDet
  | (_, TDetCk) => SDet
  | (_, TUnk) => SUnk
  end.

Lemma decode_series_m_walk_res : forall md sel dm wlim s,
  decode_series_m md sel dm wlim s = walk_res (walk_m (S (length s)) md sel dm wlim s 0).
Proof.
  intros. unfold decode_series_m, series_frames_m.
  destruct (walk_m _ _ _ _ _ _ _) as [l [| | |]]; reflexivity.
Qed.

(* a frame in front of a walk adds its content *)
Lemma walk_res_cons : forall fr l t,
  walk_res (fr :: l, t) = match walk_res (l, t) with SOk c => SOk (fr_content fr ++ c) | r => r end.
Proof. intros fr l [| | |]; reflexivity. Qed.

(* skipping n bytes either leaves s as it is (n = 0 or s empty) or shortens it *)
Lemma skipn_progress : forall (n: nat) (s: list Z), skipn n s = s \/ (length (skipn n s) < length s)%nat.
Proof.
  intros [|n] [|b s]; cbn [skipn]; auto.
  right. cbn [length]. pose proof (skipn_length n s). lia.
Qed.

(* the dictionary frame_dict chose is chosen again once it is the current one *)
Lemma frame_dict_idem : forall mg sel cur s d,
  frame_dict mg sel cur s = Some d -> frame_dict mg sel (Some d) s = Some d.
Proof.
  unfold frame_dict. intros mg sel cur s d H.
  destruct (get_frame_header_m mg s); [destruct cur; congruence | destruct cur; congruence |].
  destruct (sel (fh_dictID h)); congruence.
Qed.

(* A skippable frame that does not advance the walk (a negative size field: the list s is not bytes) makes
   the walk repeat it until the fuel runs out: the walk ends unknown, whatever its fuel. *)
Lemma walk_m_skippable_loop : forall md sel wlim s k,
  (Zlength s <? starting_len (md_magicless md)) = false ->
  negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = true ->
  skippable_frame_size s = Some k -> skipn (Z.to_nat k) s = s ->
  forall f cur off, snd (walk_m f md sel cur wlim s off) = TUnk.
Proof.
  intros md sel wlim s k E1 E2 E3 E4 f. induction f as [|f IH]; intros cur off; [reflexivity|].
  cbn [walk_m]. rewrite E1, E2, E3, E4.
  match goal with |- context [walk_m f md sel ?c wlim s ?o] =>
    specialize (IH c o); destruct (walk_m f md sel c wlim s o) as [l t] end.
  exact IH.
Qed.

(* the same for a Zstandard frame that does not advance the walk *)
Lemma walk_m_frame_loop : forall md sel wlim s d c k,
  (Zlength s <? starting_len (md_magicless md)) = false ->
  negb (md_magicless md) && is_skippable_magic (le_field s 0 4) = false ->
  frame_dict (md_magicless md) sel (Some d) s = Some d ->
  decode_frame_m md d wlim s = FOk c k -> skipn (Z.to_nat k) s = s ->
  forall f off, snd (walk_m f md sel (Some d) wlim s off) = TUnk.
Proof.
  intros md sel wlim s d c k E1 E2 E3 E4 E5 f. induction f as [|f IH]; intros off; [reflexivity|].
  cbn [walk_m]. rewrite E1, E2, E3, E4, E5.
  specialize (IH (off + k)). destruct (walk_m f md sel (Some d) wlim s (off + k)) as [l t].
  exact IH.
Qed.

(* the walk's result only needs fuel beyond the series' length (a frame that advances takes at least one
   byte; one that does not loops to an unknown end with any fuel), and does not depend on the offset *)
Lemma walk_res_fuel : forall f1 f2 md sel cur wlim s off1 off2,
  (length s < f1)%nat -> (length s < f2)%nat ->
  walk_res (walk_m f1 md sel cur wlim s off1) = walk_res (walk_m f2 md sel cur wlim s off2).
Proof.
  induction f1 as [|f1 IH]; intros f2 md sel cur wlim s off1 off2 H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [walk_m].
  destruct (Zlength s <? starting_len (md_magicless md)) eqn:E1; [reflexivity|].
  destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4)) eqn:E2.
  - destruct (skippable_frame_size s) as [k|] eqn:E3; [|reflexivity].
    match goal with |- walk_res (let '(_, _) := walk_m f1 md sel ?c wlim _ _ in _) = _ =>
      set (cur' := c) end.
    destruct (skipn_progress (Z.to_nat k) s) as [E4|E4].
    + pose proof (walk_m_skippable_loop md sel wlim s k E1 E2 E3 E4 f1 cur' (off1 + k)) as L1.
      pose proof (walk_m_skippable_loop md sel wlim s k E1 E2 E3 E4 f2 cur' (off2 + k)) as L2.
      rewrite E4.
      destruct (walk_m f1 md sel cur' wlim s (off1 + k)) as [l1 t1].
      destruct (walk_m f2 md sel cur' wlim s (off2 + k)) as [l2 t2].
      cbn in L1, L2. subst. reflexivity.
    + specialize (IH f2 md sel cur' wlim (skipn (Z.to_nat k) s) (off1 + k) (off2 + k) ltac:(lia) ltac:(lia)).
      destruct (walk_m f1 md sel cur' wlim (skipn (Z.to_nat k) s) (off1 + k)) as [l1 t1].
      destruct (walk_m f2 md sel cur' wlim (skipn (Z.to_nat k) s) (off2 + k)) as [l2 t2].
      rewrite !walk_res_cons, IH. reflexivity.
  - destruct (frame_dict (md_magicless md) sel cur s) as [d|] eqn:E3; [|reflexivity].
    destruct (decode_frame_m md d wlim s) as [c k| | |] eqn:E4; try reflexivity.
    destruct (skipn_progress (Z.to_nat k) s) as [E5|E5].
    + pose proof (frame_dict_idem _ _ _ _ _ E3) as E3'.
      pose proof (walk_m_frame_loop md sel wlim s d c k E1 E2 E3' E4 E5 f1 (off1 + k)) as L1.
      pose proof (walk_m_frame_loop md sel wlim s d c k E1 E2 E3' E4 E5 f2 (off2 + k)) as L2.
      rewrite E5.
      destruct (walk_m f1 md sel (Some d) wlim s (off1 + k)) as [l1 t1].
      destruct (walk_m f2 md sel (Some d) wlim s (off2 + k)) as [l2 t2].
      cbn in L1, L2. subst. reflexivity.
    + specialize (IH f2 md sel (Some d) wlim (skipn (Z.to_nat k) s) (off1 + k) (off2 + k) ltac:(lia) ltac:(lia)).
      destruct (walk_m f1 md sel (Some d) wlim (skipn (Z.to_nat k) s) (off1 + k)) as [l1 t1].
      destruct (walk_m f2 md sel (Some d) wlim (skipn (Z.to_nat k) s) (off2 + k)) as [l2 t2].
      rewrite !walk_res_cons, IH. reflexivity.
Qed.

(* The walk's result only needs fuel beyond the series' length.  The walk itself (its list of frames) may
   depend on the fuel: on a list that is not bytes, a frame can take no byte (a skippable frame whose size
   field is negative), and the walk repeats it until the fuel runs out; its result is then SUnk for any
   fuel (walk_res_fuel above). *)
Lemma walk_m_fuel : forall f1 f2 md sel cur wlim s off,
  (length s < f1)%nat -> (length s < f2)%nat ->
  walk_res (walk_m f1 md sel cur wlim s off) = walk_res (walk_m f2 md sel cur wlim s off).
Proof. intros. apply walk_res_fuel; assumption. Qed.

Lemma series_m_nil : forall md sel cur wlim, decode_series_m md sel cur wlim [] = SOk [].
Proof.
  intros. unfold decode_series_m, series_frames_m. cbn [walk_m length].
  destruct (md_magicless md); reflexivity.
Qed.

(* a Zstandard frame F that decodes (with the dictionary frame_dict selects) in front of the rest *)
Theorem series_m_frame : forall md sel cur d wlim F rest c,
  md_magicless md = false -> 5 <= Zlength F ->
  is_skippable_magic (le_field (F ++ rest) 0 4) = false ->
  frame_dict false sel cur (F ++ rest) = Some d ->
  decode_frame_m md d wlim (F ++ rest) = FOk c (Zlength F) ->
  decode_series_m md sel cur wlim (F ++ rest) =
  match decode_series_m md sel (Some d) wlim rest with SOk c' => SOk (c ++ c') | r => r end.
Proof.
  intros md sel cur d wlim F rest c Hmg HF Hsk Hd Hf.
  rewrite (decode_series_m_walk_res md sel cur). cbn [walk_m].
  rewrite Hmg, Hsk, Hd, Hf. cbn [negb andb].
  rewrite (decode_series_m_walk_res md sel (Some d)).
  rewrite !Zlength_correct in *. rewrite length_app.
  replace (Z.of_nat (length F + length rest) <? starting_len false) with false
    by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; symmetry; apply Z.ltb_ge; lia).
  rewrite skipn_app, Nat2Z.id, skipn_all, Nat.sub_diag. cbn [skipn app].
  rewrite <- (walk_res_fuel (length F + length rest) (S (length rest)) md sel (Some d) wlim rest
                (0 + Z.of_nat (length F)) 0) by lia.
  destruct (walk_m (length F + length rest) md sel (Some d) wlim rest (0 + Z.of_nat (length F))) as [l1 t1].
  apply walk_res_cons.
Qed.

(* a skippable frame S in front of the rest (with buffered streaming's DDict selection by its magic variant) *)
Theorem series_m_skippable : forall md sel cur wlim S rest,
  md_magicless md = false -> 5 <= Zlength S ->
  is_skippable_magic (le_field (S ++ rest) 0 4) = true ->
  skippable_frame_size (S ++ rest) = Some (Zlength S) ->
  decode_series_m md sel cur wlim (S ++ rest) =
  decode_series_m md sel
    (if md_dwin md then match sel (Z.land (le_field (S ++ rest) 0 4) 15) with Some d => Some d | None => cur end
     else cur) wlim rest.
Proof.
  intros md sel cur wlim S rest Hmg HS Hsk Hsz.
  rewrite (decode_series_m_walk_res md sel cur). cbn [walk_m].
  rewrite Hmg, Hsk, Hsz. cbn [negb andb].
  rewrite (decode_series_m_walk_res md sel).
  rewrite !Zlength_correct in *. rewrite length_app.
  replace (Z.of_nat (length S + length rest) <? starting_len false) with false
    by (unfold starting_len, ZSTD_FRAMEHEADERSIZE_PREFIX; symmetry; apply Z.ltb_ge; lia).
  rewrite skipn_app, Nat2Z.id, skipn_all, Nat.sub_diag. cbn [skipn app].
  match goal with |- walk_res (let '(_, _) := walk_m _ md sel ?c wlim _ _ in _) = _ =>
    set (cur' := c) end.
  rewrite <- (walk_res_fuel (length S + length rest) (Datatypes.S (length rest)) md sel cur' wlim rest
                (0 + Z.of_nat (length S)) 0) by lia.
  destruct (walk_m (length S + length rest) md sel cur' wlim rest (0 + Z.of_nat (length S))) as [l1 t1].
  rewrite walk_res_cons. destruct (walk_res (l1, t1)); reflexivity.
Qed.

(* without a DDict set, a frame is decoded with the current dictionary *)
Lemma frame_dict_sel_none : forall s dm, frame_dict false sel_none (Some dm) s = Some dm.
Proof. intros. unfold frame_dict, sel_none. destruct (get_frame_header_m false s); reflexivity. Qed.

(* ---------- new_skippable's frames ---------- *)

Lemma le_bytes_length : forall n v, length (le_bytes n v) = n.
Proof. induction n as [|n IH]; intros v; cbn [le_bytes length]; [reflexivity | now rewrite IH]. Qed.

Lemma le_bytes_bytes_ok : forall n v, bytes_ok (le_bytes n v).
Proof.
  induction n as [|n IH]; intros v; cbn [le_bytes]; constructor; [|apply IH].
  unfold is_byte. apply Z.mod_pos_bound. lia.
Qed.

(* le_bytes n v encodes v mod 256^n *)
Lemma le_value_le_bytes_mod : forall n v, le_value (le_bytes n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
  induction n as [|n IH]; intros v; cbn [le_bytes le_value].
  - rewrite Z.mod_1_r. reflexivity.
  - rewrite IH. replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
    rewrite Z.pow_add_r by lia. rewrite (Z.rem_mul_r v (2 ^ 8)); [reflexivity | lia | apply Z.pow_pos_nonneg; lia].
Qed.

(* the magic number of skippable variant k (0..15): skippable, and its low 4 bits are k *)
Lemma sk_magic_variant : forall k, 0 <= k < 16 ->
  is_skippable_magic (ZSTD_MAGIC_SKIPPABLE_START + k) = true /\
  Z.land (ZSTD_MAGIC_SKIPPABLE_START + k) 15 = k.
Proof.
  intros k Hk.
  assert (C: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
             k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15) by lia.
  repeat (destruct C as [C|C]; [subst k; split; reflexivity|]). subst k. split; reflexivity.
Qed.

(* the two fields of a skippable frame's header *)
Lemma sk_field_0 : forall k u rest,
  le_field (sk_bytes k u ++ rest) 0 4 = le_value (le_bytes 4 (ZSTD_MAGIC_SKIPPABLE_START + k)).
Proof. reflexivity. Qed.

Lemma sk_field_4 : forall k u rest, le_field (sk_bytes k u ++ rest) 4 4 = le_value (le_bytes 4 (Zlength u)).
Proof. reflexivity. Qed.

Lemma sk_bytes_length : forall k u, Zlength (sk_bytes k u) = 8 + Zlength u.
Proof.
  intros. unfold sk_bytes. rewrite !Zlength_correct, !length_app, !le_bytes_length. lia.
Qed.

Lemma sk_bytes_ok : forall k u, 0 <= k < 16 -> bytes_ok u -> bytes_ok (sk_bytes k u).
Proof.
  intros k u _ Hu. unfold sk_bytes, bytes_ok in *.
  apply Forall_app; split; [apply le_bytes_bytes_ok|].
  apply Forall_app; split; [apply le_bytes_bytes_ok | exact Hu].
Qed.

Lemma sk_magic : forall k u rest, 0 <= k < 16 ->
  le_field (sk_bytes k u ++ rest) 0 4 = ZSTD_MAGIC_SKIPPABLE_START + k /\
  is_skippable_magic (le_field (sk_bytes k u ++ rest) 0 4) = true.
Proof.
  intros k u rest Hk. rewrite sk_field_0, le_value_le_bytes_mod, Z.mod_small.
  - split; [reflexivity | apply sk_magic_variant; exact Hk].
  - unfold ZSTD_MAGIC_SKIPPABLE_START. change (8 * Z.of_nat 4) with 32. lia.
Qed.

Lemma sk_size_field : forall k u rest, Zlength u < 2 ^ 32 ->
  le_field (sk_bytes k u ++ rest) 4 4 = Zlength u.
Proof.
  intros k u rest H. rewrite sk_field_4, le_value_le_bytes_mod, Z.mod_small; [reflexivity|].
  change (8 * Z.of_nat 4) with 32. rewrite Zlength_correct in *. lia.
Qed.

Lemma sk_bytes_app_length : forall k u rest, Zlength (sk_bytes k u ++ rest) = 8 + Zlength u + Zlength rest.
Proof.
  intros. rewrite (Zlength_correct (_ ++ _)), length_app, Nat2Z.inj_add, <- !Zlength_correct, sk_bytes_length.
  reflexivity.
Qed.

(* ZSTD_getFrameHeader of a skippable frame *)
Lemma sk_get_frame_header : forall k u rest, 0 <= k < 16 -> Zlength u < 2 ^ 32 ->
  get_frame_header (sk_bytes k u ++ rest) =
  FH_ok {| fh_contentSize := Zlength u; fh_windowSize := 0; fh_blockSizeMax := 0; fh_frameType := 1;
           fh_headerSize := 8; fh_dictID := k; fh_checksumFlag := 0 |}.
Proof.
  intros k u rest Hk Hu. destruct (sk_magic k u rest Hk) as [M S].
  pose proof (sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold get_frame_header.
  replace (Zlength (sk_bytes k u ++ rest) <? 5) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength (sk_bytes k u ++ rest) <? ZSTD_SKIPPABLEHEADERSIZE) with false
    by (symmetry; apply Z.ltb_ge; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  rewrite S, M.
  replace (ZSTD_MAGIC_SKIPPABLE_START + k =? ZSTD_MAGICNUMBER) with false
    by (symmetry; apply Z.eqb_neq; unfold ZSTD_MAGIC_SKIPPABLE_START, ZSTD_MAGICNUMBER; lia).
  cbn [negb]. rewrite sk_size_field by exact Hu.
  replace (ZSTD_MAGIC_SKIPPABLE_START + k - ZSTD_MAGIC_SKIPPABLE_START) with k by lia.
  reflexivity.
Qed.

(* readSkippableFrameSize under the model's current test *)
Lemma sk_frame_size : forall k u rest, 0 <= k < 16 -> 8 + Zlength u < 2 ^ 32 ->
  skippable_frame_size (sk_bytes k u ++ rest) = Some (8 + Zlength u).
Proof.
  intros k u rest Hk Hu. pose proof (sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold skippable_frame_size. rewrite sk_size_field by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
  replace (Zlength (sk_bytes k u ++ rest) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength u + 8 >=? 2 ^ 32) with false by (symmetry; rewrite Z.geb_leb; apply Z.leb_gt; lia).
  replace (Zlength u + 8 >? Zlength (sk_bytes k u ++ rest)) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

(* ZSTD_findFrameCompressedSize of a skippable frame *)
Lemma sk_frame_compressed_size : forall k u rest, 0 <= k < 16 ->
  skippable_frame_size (sk_bytes k u ++ rest) = Some (8 + Zlength u) ->
  frame_compressed_size (sk_bytes k u ++ rest) = Some (8 + Zlength u).
Proof.
  intros k u rest Hk Hs. destruct (sk_magic k u rest Hk) as [_ S].
  pose proof (sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold frame_compressed_size. rewrite S.
  replace (Zlength (sk_bytes k u ++ rest) >=? ZSTD_SKIPPABLEHEADERSIZE) with true
    by (symmetry; rewrite Z.geb_leb; apply Z.leb_le; unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  exact Hs.
Qed.

Theorem sk_series_m : forall md sel cur wlim k u rest, 0 <= k < 16 ->
  md_magicless md = false ->
  skippable_frame_size (sk_bytes k u ++ rest) = Some (8 + Zlength u) ->
  decode_series_m md sel cur wlim (sk_bytes k u ++ rest) =
  decode_series_m md sel
    (if md_dwin md then match sel k with Some d => Some d | None => cur end else cur) wlim rest.
Proof.
  intros md sel cur wlim k u rest Hk Hmg Hs.
  destruct (sk_magic k u rest Hk) as [M S].
  rewrite series_m_skippable; auto.
  - rewrite M, (proj2 (sk_magic_variant k Hk)). reflexivity.
  - rewrite sk_bytes_length. rewrite Zlength_correct. lia.
  - rewrite sk_bytes_length. exact Hs.
Qed.
