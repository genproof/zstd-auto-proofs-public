(* More helpers for main of harness/valid_info.c (WMain_valid_info): the frame pointer of the loop, the facts of
   frame k, the accumulators one frame further. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_info.WTopSpecs_valid_info.
Require Import Zstd.proof.harness.valid_info.VIModel Zstd.proof.harness.valid_info.VIVst.

Local Notation HCS := Zstd.proof.harness.valid_info.HOK_valid_info.CompSpecs.

Lemma VI_fptr p k :
  isptr (@field_address HCS t_wseries (DOT _f) p) -> 0 <= k < 4 ->
  force_val (@sem_binary_operation' HCS Oadd (tarray t_winfo 4) tuint (@eval_field HCS t_wseries _f p) (Vint (Int.repr k))) =
  offset_val (@sizeof HCS t_winfo * k) (@field_address HCS t_wseries (DOT _f) p).
Proof.
  intros Hp Hk. unfold field_address in *.
  destruct (field_compatible_dec t_wseries (DOT _f) p) as [Hc|Hc]; [|contradiction].
  destruct p; try contradiction. simpl.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite Int.unsigned_repr by rep_lia.
  rewrite ptrofs_mul_repr. reflexivity.
Qed.

Lemma VI_frame_k dm ws k :
  series_facts dm ws -> wseries_wf ws -> 0 <= k < Zlength (ws_frames ws) ->
  frame_facts dm ws (Znth k (ws_frames ws)) /\ winfo_wf (Znth k (ws_frames ws)) /\
  winfo_zeros (Znth k (ws_frames ws)) /\
  0 <= wi_start (Znth k (ws_frames ws)) /\
  wi_start (Znth k (ws_frames ws)) + wi_size (Znth k (ws_frames ws)) <= Zlength (ws_bytes ws) /\
  0 < wi_size (Znth k (ws_frames ws)) /\
  (wi_skippable (Znth k (ws_frames ws)) = false -> wi_fcs_present (Znth k (ws_frames ws)) = true ->
   wi_fcs (Znth k (ws_frames ws)) = wi_csize (Znth k (ws_frames ws))).
Proof.
  intros (_ & _ & _ & _ & _ & Ht & Hff & Hfcs & _) (Hwf & Hz & _) Hk.
  assert (Hk': (Z.to_nat k < length (ws_frames ws))%nat).
  { rewrite Zlength_correct in Hk. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
  pose proof (vi_tiles_nth _ _ _ _ _ Ht _ Hk') as (A & B & C).
  replace (Znth k (ws_frames ws)) with (nth (Z.to_nat k) (ws_frames ws) winfo0)
    by (rewrite <- nth_Znth by lia; reflexivity).
  rewrite Forall_forall in Hff, Hfcs, Hwf, Hz.
  pose proof (nth_In _ winfo0 Hk') as Hin.
  exact (conj (Hff _ Hin) (conj (Hwf _ Hin) (conj (Hz _ Hin) (conj A (conj B (conj C (Hfcs _ Hin))))))).

Qed.

Lemma VI_sublist_S (fs: list winfo) k : 0 <= k < Zlength fs ->
  sublist 0 (k + 1) fs = sublist 0 k fs ++ [Znth k fs].
Proof.
  intros Hk. rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma VI_bsum_S fs k : 0 <= k < Zlength fs ->
  vi_bsum (sublist 0 (k + 1) fs) = vi_bsum (sublist 0 k fs) + vi_bterm (Znth k fs).
Proof. intros Hk. rewrite VI_sublist_S, vi_bsum_app by lia. simpl. lia. Qed.

Lemma VI_allfcs_S fs k : 0 <= k < Zlength fs ->
  vi_allfcs (sublist 0 (k + 1) fs) =
  (vi_allfcs (sublist 0 k fs) && (wi_skippable (Znth k fs) || wi_fcs_present (Znth k fs)))%bool.
Proof. intros Hk. rewrite VI_sublist_S by lia. unfold vi_allfcs. rewrite forallb_app. simpl. rewrite andb_true_r. reflexivity. Qed.

Lemma VI_anybig_S fs k : 0 <= k < Zlength fs ->
  vi_anybig (sublist 0 (k + 1) fs) = (vi_anybig (sublist 0 k fs) || wi_big (Znth k fs))%bool.
Proof. intros Hk. rewrite VI_sublist_S by lia. unfold vi_anybig. rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity. Qed.

Lemma VI_bytes_skipn n (l: list Z) : bytes_ok l -> bytes_ok (skipn n l).
Proof.
  revert l. induction n as [|n IH]; intros l H; [exact H|].
  destruct l as [|b l]; [constructor|]. simpl. inversion H; subst. apply IH; auto.
Qed.

Lemma VI_len_skipn (l: list Z) s : 0 <= s <= Zlength l -> Zlength (skipn (Z.to_nat s) l) = Zlength l - s.
Proof.
  intros H. rewrite !Zlength_correct, skipn_length. rewrite Zlength_correct in H. lia.
Qed.

Lemma VI_fhd_bound x : 5 <= fhd_header_size x <= 19.
Proof.
  unfold fhd_header_size. cbv zeta.
  assert (A: forall n, 0 <= nth n [0; 1; 2; 4] 0 <= 4) by (intros n; destruct n as [|[|[|[|n]]]]; simpl; try destruct n; lia).
  assert (B: forall n, 0 <= nth n [0; 2; 4; 8] 0 <= 8) by (intros n; destruct n as [|[|[|[|n]]]]; simpl; try destruct n; lia).
  assert (C: 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { replace (Z.land (Z.shiftr x 5) 1) with (Z.shiftr x 5 mod 2) by (rewrite <- (Z.land_ones _ 1) by lia; reflexivity).
    pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2 ltac:(lia)). lia. }
  specialize (A (Z.to_nat (Z.land x 3))). specialize (B (Z.to_nat (Z.shiftr x 6))).
  destruct (andb _ _); lia.
Qed.

Lemma VI_fhs_bound s k : Info.frame_header_size s = Some k -> 5 <= k <= 19.
Proof.
  unfold Info.frame_header_size. destruct (_ <? _); intros H; inversion H; subst. apply VI_fhd_bound.
Qed.

Lemma VI_skip_byte (bytes: list Z) start size i :
  0 <= i -> 8 + i < size ->
  Znth i (slice (slice bytes start size) 8 (size - 8)) = Znth (8 + i) (skipn (Z.to_nat start) bytes).
Proof.
  intros H3 H4. unfold slice, Znth.
  destruct (Z_lt_dec i 0); [lia|]. destruct (Z_lt_dec (8 + i) 0); [lia|].
  rewrite nth_firstn by (apply Z2Nat.inj_lt; lia). rewrite List.nth_skipn.
  rewrite nth_firstn by (rewrite <- Z2Nat.inj_add by lia; apply Z2Nat.inj_lt; lia).
  rewrite <- Z2Nat.inj_add by lia.
  rewrite (proj2 (Nat.ltb_lt _ _)) by (apply Z2Nat.inj_lt; lia).
  rewrite (proj2 (Nat.ltb_lt _ _)) by (apply Z2Nat.inj_lt; lia). reflexivity.
Qed.

Lemma VI_slice_len (l: list Z) i k : 0 <= i -> 0 <= k -> i + k <= Zlength l -> Zlength (slice l i k) = k.
Proof.
  intros H1 H2 H3. unfold slice. rewrite Zlength_correct, firstn_length, skipn_length.
  rewrite Zlength_correct in H3. lia.
Qed.

Lemma VI_ltu31 wl : 0 <= wl < 2 ^ 32 -> Int.ltu (Int.repr 31) (Int.repr wl) = (wl >? 31).
Proof.
  intros H. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.gtb_ltb. destruct (zlt 31 wl); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma VI_or_vb (a b: bool) :
  Int.or (Int.repr (if a then 1 else 0)) (Int.repr (if b then 1 else 0)) = Int.repr (if (a || b)%bool then 1 else 0).
Proof. destruct a, b; reflexivity. Qed.
