(* Model facts for main of harness/detect.c (WMain_detect.v): the bytes the harness corrupts, and what
   the model says of them.  Plain Coq on top of SeriesLemmas. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.writer.SeriesLemmas.
Local Open Scope bool_scope.

(* the bytes pos .. pos+j-1 of b xor'ed with the little-endian bytes of x (the C loop after j steps) *)
Definition xorn (b: list Z) (pos x j: Z) : list Z :=
  map (fun i => let v := byte_at b (Z.of_nat i) in
                if (pos <=? Z.of_nat i) && (Z.of_nat i <? pos + j)
                then Z.lxor v (Z.land (Z.shiftr x (8 * (Z.of_nat i - pos))) 255) else v)
      (seq 0 (length b)).

(* helpers: position-wise maps over a byte list *)
Definition pmap (g: Z -> Z -> Z) (b: list Z) : list Z :=
  map (fun i => g (Z.of_nat i) (byte_at b (Z.of_nat i))) (seq 0 (length b)).

Lemma pmap_Zlength g b : Zlength (pmap g b) = Zlength b.
Proof. unfold pmap. rewrite !Zlength_correct, map_length, seq_length. reflexivity. Qed.

Lemma Znth_pmap g b i : 0 <= i < Zlength b -> Znth i (pmap g b) = g i (Znth i b).
Proof.
  intros Hi. pose proof (pmap_Zlength g b) as Hl.
  rewrite <- (nth_Znth i (pmap g b)) by lia. rewrite <- (nth_Znth i b) by lia.
  unfold pmap. rewrite Zlength_correct in Hi.
  set (f := fun i0 : nat => g (Z.of_nat i0) (byte_at b (Z.of_nat i0))).
  rewrite nth_indep with (d' := f 0%nat) by (rewrite map_length, seq_length; lia).
  rewrite map_nth, seq_nth by lia. subst f. simpl. unfold byte_at. rewrite !Z2Nat.id by lia. reflexivity.
Qed.

Lemma xorn_pmap b pos x j : xorn b pos x j =
  pmap (fun i v => if (pos <=? i) && (i <? pos + j)
                   then Z.lxor v (Z.land (Z.shiftr x (8 * (i - pos))) 255) else v) b.
Proof. reflexivity. Qed.

Lemma xor4_pmap b pos x : xor4 b pos x =
  pmap (fun i v => if (pos <=? i) && (i <? pos + 4)
                   then Z.lxor v (Z.land (Z.shiftr x (8 * (i - pos))) 255) else v) b.
Proof. reflexivity. Qed.

Lemma set_bit3_pmap b pos : set_bit3 b pos = pmap (fun i v => if i =? pos then Z.lor v 8 else v) b.
Proof. reflexivity. Qed.

Lemma log2_byte a : is_byte a -> Z.log2 a < 8.
Proof.
  unfold is_byte. intros Ha. destruct (Z.eq_dec a 0) as [->|E]. simpl; lia.
  apply Z.log2_lt_pow2; [lia | change (2 ^ 8) with 256; lia].
Qed.

Lemma byte_of_log2 a : 0 <= a -> Z.log2 a < 8 -> is_byte a.
Proof.
  unfold is_byte. intros H0 H. split; auto. destruct (Z.eq_dec a 0) as [->|E]. lia.
  change 256 with (2 ^ 8). apply Z.log2_lt_pow2; lia.
Qed.

Lemma byte_lxor a b : is_byte a -> is_byte b -> is_byte (Z.lxor a b).
Proof.
  intros Ha Hb. pose proof (log2_byte a Ha). pose proof (log2_byte b Hb). unfold is_byte in *.
  apply byte_of_log2. apply Z.lxor_nonneg; lia.
  eapply Z.le_lt_trans. apply Z.log2_lxor; lia. lia.
Qed.

Lemma byte_lor a b : is_byte a -> is_byte b -> is_byte (Z.lor a b).
Proof.
  intros Ha Hb. pose proof (log2_byte a Ha). pose proof (log2_byte b Hb). unfold is_byte in *.
  apply byte_of_log2. apply Z.lor_nonneg; lia.
  rewrite Z.log2_lor by lia. lia.
Qed.

Lemma byte_land255 y : is_byte (Z.land y 255).
Proof.
  unfold is_byte. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound y (2 ^ 8)). change (2 ^ 8) with 256 in *. lia.
Qed.


Ltac zb := repeat match goal with
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end; simpl; try lia.

Lemma xorn_0 b pos x : xorn b pos x 0 = b.
Proof.
  rewrite xorn_pmap. apply Znth_eq_ext. apply pmap_Zlength.
  intros i Hi. rewrite pmap_Zlength in Hi. rewrite Znth_pmap by auto. zb.
Qed.

Lemma xorn_Zlength b pos x j : Zlength (xorn b pos x j) = Zlength b.
Proof.
  rewrite xorn_pmap. apply pmap_Zlength.
Qed.

Lemma xorn_Znth_out b pos x j i : 0 <= i < Zlength b -> ~ (pos <= i < pos + j) ->
  Znth i (xorn b pos x j) = Znth i b.
Proof.
  intros Hi Hn. rewrite xorn_pmap, Znth_pmap by auto. zb.
Qed.

Lemma xorn_step b pos x j : 0 <= j -> 0 <= pos + j < Zlength b ->
  xorn b pos x (j + 1) =
  upd_Znth (pos + j) (xorn b pos x j) (Z.lxor (Znth (pos + j) b) (Z.land (Z.shiftr x (8 * j)) 255)).
Proof.
  intros Hj Hp. rewrite !xorn_pmap. apply Znth_eq_ext.
  rewrite Zlength_upd_Znth, !pmap_Zlength; auto.
  intros i Hi. rewrite pmap_Zlength in Hi. destruct (Z.eq_dec i (pos + j)) as [->|E].
  - rewrite upd_Znth_same by (rewrite pmap_Zlength; lia). rewrite Znth_pmap by lia. zb.
    replace (pos + j - pos) with j by lia. reflexivity.
  - rewrite upd_Znth_diff by (rewrite ?pmap_Zlength; lia). rewrite !Znth_pmap by lia. zb.
Qed.

Lemma xorn_bytes b pos x j : bytes_ok b -> 0 <= x -> bytes_ok (xorn b pos x j).
Proof.
  unfold bytes_ok. rewrite !Forall_Znth. intros Hb Hx i Hi.
  rewrite xorn_pmap in *. rewrite pmap_Zlength in Hi. rewrite Znth_pmap by auto.
  destruct (_ && _). apply byte_lxor; auto. apply byte_land255. auto.
Qed.

Lemma set_bit3_upd b pos : 0 <= pos < Zlength b ->
  set_bit3 b pos = upd_Znth pos b (Z.lor (Znth pos b) 8).
Proof.
  intros Hp. rewrite set_bit3_pmap. apply Znth_eq_ext.
  rewrite Zlength_upd_Znth, !pmap_Zlength; auto.
  intros i Hi. rewrite pmap_Zlength in Hi. destruct (Z.eq_dec i pos) as [->|E].
  - rewrite upd_Znth_same by lia. rewrite Znth_pmap by lia. zb.
  - rewrite upd_Znth_diff by lia. rewrite !Znth_pmap by lia. zb.
Qed.

Lemma set_bit3_Zlength b pos : Zlength (set_bit3 b pos) = Zlength b.
Proof.
  rewrite set_bit3_pmap. apply pmap_Zlength.
Qed.

Lemma set_bit3_bytes b pos : bytes_ok b -> bytes_ok (set_bit3 b pos).
Proof.
  unfold bytes_ok. rewrite !Forall_Znth. intros Hb i Hi.
  rewrite set_bit3_pmap in *. rewrite pmap_Zlength in Hi. rewrite Znth_pmap by auto.
  destruct (_ =? _). apply byte_lor; auto. hnf; lia. auto.
Qed.

(* helpers: the tiling of a series by its frames *)
Lemma tiles_le fs off coff n cn : tiles fs off coff n cn -> off <= n.
Proof.
  revert off coff. induction fs as [|f fs IH]; simpl; intros off coff H. lia.
  destruct H as (_ & _ & Hz & _ & _ & H). apply IH in H. lia.
Qed.

Lemma tiles_nth fs off coff n cn k : tiles fs off coff n cn -> (k < length fs)%nat ->
  off <= wi_start (nth k fs winfo0) /\ 0 < wi_size (nth k fs winfo0) /\ wi_start (nth k fs winfo0) + wi_size (nth k fs winfo0) <= n.
Proof.
  revert off coff k. induction fs as [|f fs IH]; simpl; intros off coff k H Hk. lia.
  destruct H as (Hs & _ & Hz & _ & _ & H). destruct k as [|k].
  - pose proof (tiles_le _ _ _ _ _ H). lia.
  - destruct (IH _ _ k H ltac:(lia)) as (? & ? & ?). lia.
Qed.

Lemma tiles_order fs off coff n cn j k : tiles fs off coff n cn -> (j < k)%nat -> (k < length fs)%nat ->
  wi_start (nth j fs winfo0) + wi_size (nth j fs winfo0) <= wi_start (nth k fs winfo0).
Proof.
  revert off coff j k. induction fs as [|f fs IH]; simpl; intros off coff j k H Hjk Hk. lia.
  destruct H as (Hs & _ & Hz & _ & _ & H). destruct k as [|k]. lia. destruct j as [|j].
  - destruct (tiles_nth _ _ _ _ _ k H ltac:(lia)) as (? & ? & ?). lia.
  - eapply IH; eauto; lia.
Qed.

Lemma slice_sublist (B: list Z) st sz : 0 <= st -> 0 <= sz -> st + sz <= Zlength B ->
  slice B st sz = sublist st (st + sz) B.
Proof.
  intros. unfold slice. rewrite <- sublist_skip by lia. rewrite <- sublist_firstn. list_solve.
Qed.

Lemma pmap_ext g1 g2 b : (forall i v, 0 <= i < Zlength b -> g1 i v = g2 i v) -> pmap g1 b = pmap g2 b.
Proof.
  intros H. apply Znth_eq_ext. rewrite !pmap_Zlength; auto.
  intros i Hi. rewrite pmap_Zlength in Hi. rewrite !Znth_pmap by auto. auto.
Qed.

Lemma pmap_firstn g (B: list Z) st : 0 <= st <= Zlength B -> (forall i v, i < st -> g i v = v) ->
  firstn (Z.to_nat st) (pmap g B) = firstn (Z.to_nat st) B.
Proof.
  intros Hst H. rewrite <- !sublist_firstn. apply Znth_eq_ext.
  rewrite !Zlength_sublist; rewrite ?pmap_Zlength; lia.
  intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?pmap_Zlength; lia).
  rewrite !Znth_sublist by (rewrite ?pmap_Zlength; lia). rewrite Znth_pmap by lia. apply H; lia.
Qed.

Lemma pmap_skipn g (B: list Z) st sz : 0 <= st -> 0 <= sz -> st + sz <= Zlength B ->
  (forall i v, st + sz <= i -> g i v = v) ->
  skipn (Z.to_nat st) (pmap g B) =
  pmap (fun i v => g (i + st) v) (sublist st (st + sz) B) ++ skipn (Z.to_nat (st + sz)) B.
Proof.
  intros H0 H1 H2 H. rewrite <- !sublist_skip by lia. rewrite pmap_Zlength. apply Znth_eq_ext.
  rewrite Zlength_app, pmap_Zlength, !Zlength_sublist; rewrite ?pmap_Zlength; lia.
  intros i Hi. rewrite Zlength_sublist in Hi by (rewrite ?pmap_Zlength; lia).
  rewrite Znth_sublist by (rewrite ?pmap_Zlength; lia). rewrite Znth_pmap by lia.
  destruct (Z_lt_dec i sz).
  - rewrite Znth_app1 by (rewrite pmap_Zlength, Zlength_sublist; lia).
    rewrite Znth_pmap by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia. reflexivity.
  - rewrite Znth_app2 by (rewrite pmap_Zlength, Zlength_sublist; lia).
    rewrite pmap_Zlength, Zlength_sublist by lia. rewrite Znth_sublist by lia.
    rewrite H by lia. f_equal. lia.
Qed.

Lemma ok_prefix_In wl f l : In f (ok_prefix wl l) -> In f l.
Proof.
  induction l as [|g l IH]; simpl. auto. destruct (wi_rejected wl g); simpl. tauto. intuition.
Qed.

(* where frame k is in the series' bytes; a Zstandard frame has at least 9 bytes (decode_frame needs a
   header and a block header) *)
Lemma DM_frame_bounds dm ws k : series_facts dm ws -> (k < length (ws_frames ws))%nat ->
  0 <= wi_start (nth k (ws_frames ws) winfo0) /\ 0 < wi_size (nth k (ws_frames ws) winfo0) /\
  wi_start (nth k (ws_frames ws) winfo0) + wi_size (nth k (ws_frames ws) winfo0) <= Zlength (ws_bytes ws) /\
  (wi_skippable (nth k (ws_frames ws) winfo0) = false -> 9 <= wi_size (nth k (ws_frames ws) winfo0)).
Proof.
  intros (Hb & _ & _ & _ & _ & Ht & Hf & _) Hk.
  destruct (tiles_nth _ _ _ _ _ k Ht Hk) as (H0 & H1 & H2). split; [lia|split; [lia|split; [lia|]]].
  intros Hsk. rewrite Forall_forall in Hf. specialize (Hf _ (nth_In _ winfo0 Hk)).
  destruct Hf as (_ & _ & _ & _ & _ & _ & _ & _ & Hdec). destruct (Hdec Hsk) as (Hd & _ & _).
  specialize (Hd no_wlim nil). rewrite app_nil_r in Hd.
  unfold wi_bytes in Hd. rewrite slice_sublist in Hd by lia.
  destruct (Z_lt_dec (wi_size (nth k (ws_frames ws) winfo0)) 9); [|lia]. exfalso.
  unfold decode_frame in Hd. rewrite Zlength_sublist in Hd by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) in Hd by (unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_blockHeaderSize; lia).
  destruct (wi_rejected _ _); discriminate.
Qed.

(* helper: the corrupted series as the walk sees it, for any window limit *)
Lemma DM_corrupt_frames ws k s' wl :
  series_facts no_dict ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  wi_skippable (nth k (ws_frames ws) winfo0) = false ->
  ((exists x, wi_checksum (nth k (ws_frames ws) winfo0) = true /\ 0 < x < 2 ^ 32 /\
     s' = xorn (ws_bytes ws)
            (wi_start (nth k (ws_frames ws) winfo0) + wi_size (nth k (ws_frames ws) winfo0) - 4) x 4) \/
   s' = set_bit3 (ws_bytes ws) (wi_start (nth k (ws_frames ws) winfo0) + 4)) ->
  exists r, (r = FDetHdr \/ r = FDetCk) /\
  series_frames no_dict wl s' =
    (map (frec_of ws) (ok_prefix wl (firstn k (ws_frames ws))),
     if all_ok wl (firstn k (ws_frames ws)) then tail_of r else TDetHdr).
Proof.
  intros Hsf Hwf Hk Hsk Hs'.
  destruct (DM_frame_bounds _ _ _ Hsf Hk) as (H0 & H1 & H2 & H9). specialize (H9 Hsk).
  pose proof Hsf as (_ & _ & _ & _ & _ & _ & Hf & _). rewrite Forall_forall in Hf.
  pose proof (nth_In _ winfo0 Hk) as Hin. pose proof (Hf _ Hin) as Hff.
  destruct Hff as (_ & _ & _ & _ & _ & _ & _ & _ & Hdec). destruct (Hdec Hsk) as (_ & Hbit & _).
  set (f := nth k (ws_frames ws) winfo0) in *.
  set (st := wi_start f) in *. set (sz := wi_size f) in *. set (B := ws_bytes ws) in *.
  assert (Hfb: wi_bytes ws f = sublist st (st + sz) B) by (apply slice_sublist; lia).
  destruct Hs' as [(x & Hck & Hx & ->) | ->].
  - rewrite xorn_pmap.
    exists (decode_frame no_dict wl (skipn (Z.to_nat st) (pmap (fun i v =>
        if (st + sz - 4 <=? i) && (i <? st + sz - 4 + 4)
        then Z.lxor v (Z.land (Z.shiftr x (8 * (i - (st + sz - 4)))) 255) else v) B))).
    assert (Hd: decode_frame no_dict wl (skipn (Z.to_nat st) (pmap (fun i v =>
        if (st + sz - 4 <=? i) && (i <? st + sz - 4 + 4)
        then Z.lxor v (Z.land (Z.shiftr x (8 * (i - (st + sz - 4)))) 255) else v) B)) =
        if wi_rejected wl f then FDetHdr else FDetCk).
    { rewrite (pmap_skipn _ B st sz) by (try lia; intros; zb).
      rewrite <- Hfb. rewrite <- (decode_checksum_corrupt no_dict ws f wl (skipn (Z.to_nat (st + sz)) B) x Hsf Hwf Hin Hsk Hck Hx).
      f_equal. f_equal. rewrite xor4_pmap. apply pmap_ext. intros i v Hi. change (wi_size f) with sz.
      replace (i + st - (st + sz - 4)) with (i - (sz - 4)) by lia. zb. }
    split. rewrite Hd. destruct (wi_rejected wl f); auto.
    eapply series_frames_corrupt; eauto;
      change (nth k (ws_frames ws) winfo0) with f; change (wi_start f) with st;
      change (ws_bytes ws) with B.
    apply pmap_firstn. lia. intros; zb.
    rewrite Hd. destruct (wi_rejected wl f); auto.
  - rewrite set_bit3_pmap.
    assert (Hd: decode_frame no_dict wl (skipn (Z.to_nat st)
        (pmap (fun i v => if i =? st + 4 then Z.lor v 8 else v) B)) = FDetHdr).
    { rewrite (pmap_skipn _ B st sz) by (try lia; intros; zb).
      rewrite <- Hfb. rewrite <- (Hbit wl (skipn (Z.to_nat (st + sz)) B)).
      f_equal. f_equal. rewrite set_bit3_pmap. apply pmap_ext. intros i v Hi. zb. }
    exists FDetHdr. split. auto.
    eapply series_frames_corrupt; eauto;
      change (nth k (ws_frames ws) winfo0) with f; change (wi_start f) with st;
      change (ws_bytes ws) with B.
    apply pmap_firstn. lia. intros; zb.
Qed.

(* the corrupted series (kind 0: the checksum of frame k xor'ed with x; kind 1: its Reserved_bit set):
   one-shot decoding certainly fails, and the streaming walk ends with a certain rejection after frames
   that all end before frame k starts
   (proof: DM_corrupt_frames at no_wlim and stream_wlim, then ok_prefix_In + tiles_order) *)
Lemma DM_detect ws k s' :
  series_facts no_dict ws -> wseries_wf ws -> (k < length (ws_frames ws))%nat ->
  wi_skippable (nth k (ws_frames ws) winfo0) = false ->
  ((exists x, wi_checksum (nth k (ws_frames ws) winfo0) = true /\ 0 < x < 2 ^ 32 /\
     s' = xorn (ws_bytes ws)
            (wi_start (nth k (ws_frames ws) winfo0) + wi_size (nth k (ws_frames ws) winfo0) - 4) x 4) \/
   s' = set_bit3 (ws_bytes ws) (wi_start (nth k (ws_frames ws) winfo0) + 4)) ->
  decode_series no_dict no_wlim s' = SDet /\
  snd (series_frames no_dict stream_wlim s') <> TUnk /\
  Forall (fun fr => fr_end fr <= wi_start (nth k (ws_frames ws) winfo0))
         (fst (series_frames no_dict stream_wlim s')).
Proof.
  intros Hsf Hwf Hk Hsk Hs'.
  destruct (DM_corrupt_frames ws k s' no_wlim Hsf Hwf Hk Hsk Hs') as (r1 & Hr1 & E1).
  destruct (DM_corrupt_frames ws k s' stream_wlim Hsf Hwf Hk Hsk Hs') as (r2 & Hr2 & E2).
  split; [|split].
  - unfold decode_series. rewrite E1. destruct (all_ok _ _); auto.
    destruct Hr1 as [->| ->]; reflexivity.
  - rewrite E2. simpl. destruct (all_ok stream_wlim (firstn k (ws_frames ws))); [destruct Hr2 as [->| ->]|]; simpl; congruence.
  - rewrite E2. simpl. rewrite Forall_map, Forall_forall. intros g Hg.
    apply ok_prefix_In in Hg. apply (In_nth _ _ winfo0) in Hg. destruct Hg as (j & Hj & <-).
    rewrite firstn_length in Hj. rewrite nth_firstn. destruct (Nat.ltb_spec j k); [|lia].
    unfold fr_end. simpl. pose proof Hsf as (_ & _ & _ & _ & _ & Ht & _).
    eapply tiles_order; eauto.
Qed.
