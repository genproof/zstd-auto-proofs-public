(* Small list facts for valid_stream's main (plain Coq). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_stream.VSModel.

#[export] Instance VSF_inh_winfo : Inhabitant winfo := winfo0.

Lemma VSF_is_prefix_sublist (l: list Z) k : 0 <= k <= Zlength l -> is_prefix (sublist 0 k l) l.
Proof.
  intros Hk. unfold is_prefix. rewrite sublist_firstn.
  rewrite length_firstn. rewrite Zlength_correct in Hk.
  rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma VSF_in_app (l: list Z) ipos ilen ip' : 0 <= ipos -> 0 <= ip' <= ilen -> ipos + ilen <= Zlength l ->
  sublist 0 ipos l ++ sublist 0 ip' (sublist ipos (ipos + ilen) l) = sublist 0 (ipos + ip') l.
Proof. intros. rewrite sublist_sublist by lia. rewrite sublist_rejoin by lia. f_equal; lia. Qed.

Lemma VSF_prefix_app (c dl: list Z) got : 0 <= got <= Zlength c ->
  is_prefix (sublist 0 got c ++ dl) c ->
  got + Zlength dl <= Zlength c /\ dl = sublist got (got + Zlength dl) c.
Proof.
  intros Hg H. pose proof (Zlength_nonneg dl). unfold is_prefix in H.
  assert (Hl: length (firstn (length (sublist 0 got c ++ dl)) c) = length (sublist 0 got c ++ dl)) by (rewrite H; auto).
  rewrite length_firstn in Hl.
  assert (Hlen: Zlength (sublist 0 got c ++ dl) <= Zlength c).
  { rewrite !Zlength_correct. lia. }
  rewrite Zlength_app, Zlength_sublist in Hlen by lia.
  split; [lia|].
  assert (E: sublist 0 (got + Zlength dl) c = sublist 0 got c ++ dl).
  { rewrite sublist_firstn. rewrite <- H. f_equal.
    rewrite length_app, <- !ZtoNat_Zlength, Zlength_sublist by lia. pose proof (Zlength_nonneg dl). rewrite <- Z2Nat.inj_add by lia. f_equal; lia. }
  assert (E2: sublist got (got + Zlength dl) c = sublist got (got + Zlength dl) (sublist 0 got c ++ dl)).
  { rewrite <- E. rewrite sublist_sublist by lia. f_equal; lia. }
  rewrite E2. rewrite sublist_app2 by (rewrite Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia. replace (got - (got - 0)) with 0 by lia.
  replace (got + Zlength dl - (got - 0)) with (Zlength dl) by lia. rewrite sublist_same by lia. auto.
Qed.

Lemma VSF_oc (oc': list val) dl opos' j : sublist 0 opos' oc' = map (fun b => Vint (Int.repr b)) dl ->
  0 <= j < opos' -> opos' <= Zlength oc' -> Znth j oc' = Vint (Int.repr (Znth j dl)).
Proof.
  intros H Hj Ho. assert (Znth j (sublist 0 opos' oc') = Znth j oc') by (rewrite Znth_sublist by lia; f_equal; lia).
  rewrite <- H0, H. apply (f_equal (@Zlength val)) in H. rewrite Zlength_map, Zlength_sublist in H by lia.
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VSF_zb (c: list Z) N k : 0 <= k < Zlength c ->
  Znth k (map (fun b => Vint (Int.repr b)) c ++ Zrepeat (Vint Int.zero) (N - Zlength c)) = Vint (Int.repr (Znth k c)).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Lemma VSF_dl (c dl: list Z) got j : 0 <= got -> got + Zlength dl <= Zlength c ->
  dl = sublist got (got + Zlength dl) c -> 0 <= j < Zlength dl -> Znth j dl = Znth (got + j) c.
Proof.
  intros H1 H2 H3 H4. rewrite H3 at 1. rewrite Znth_sublist by lia. f_equal; lia.
Qed.

(* main's at_end loop after k frames *)
Definition VSF_at (fs: list winfo) (ipos got: Z) (k: Z) : bool :=
  existsb (fun f => andb (wi_end f =? ipos) (got =? wi_cstart f + wi_csize f)) (firstn (Z.to_nat k) fs).

Lemma VSF_at_step fs ipos got k : 0 <= k < Zlength fs ->
  VSF_at fs ipos got (k + 1) =
  orb (VSF_at fs ipos got k) (andb (wi_end (Znth k fs) =? ipos) (got =? wi_cstart (Znth k fs) + wi_csize (Znth k fs))).
Proof.
  intros. unfold VSF_at. rewrite <- !sublist_firstn.
  rewrite (sublist_split 0 k (k + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite existsb_app. simpl. rewrite orb_false_r. reflexivity.
Qed.

Lemma VSF_at_all fs ipos got : VSF_at fs ipos got (Zlength fs) = h_at_end fs ipos got.
Proof. unfold VSF_at, h_at_end. rewrite ZtoNat_Zlength, firstn_all. reflexivity. Qed.

Lemma VSF_skipn_cons {A} {d: Inhabitant A} (l: list A) i : 0 <= i < Zlength l ->
  skipn (Z.to_nat i) l = Znth i l :: skipn (Z.to_nat (i + 1)) l.
Proof.
  intros. assert (G: forall n (l: list A), (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l).
  { induction n as [|n IH]; intros [|a l'] Hn; simpl in *; try lia; auto. apply IH. lia. }
  rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. simpl (Z.to_nat 1 + _)%nat.
  unfold Znth. rewrite if_false by lia. apply G. rewrite <- ZtoNat_Zlength. lia.
Qed.

Lemma VSF_h_end_step fs ipos got dflt k : 0 < k <= Zlength fs ->
  h_end (skipn (Z.to_nat (k - 1)) fs) ipos got dflt =
  if orb (wi_end (Znth (k - 1) fs) >? ipos)
     (andb (wi_end (Znth (k - 1) fs) =? ipos) (got <? wi_cstart (Znth (k - 1) fs) + wi_csize (Znth (k - 1) fs)))
  then wi_end (Znth (k - 1) fs) else h_end (skipn (Z.to_nat k) fs) ipos got dflt.
Proof.
  intros. rewrite (VSF_skipn_cons fs (k - 1)) by lia. simpl h_end.
  replace (k - 1 + 1) with k by lia. reflexivity.
Qed.

(* the harness's stall_error from the API's stall_ok *)
Lemma VSF_stall r e stall stalled ip isz op osz :
  stall_ok r stall 0 ip isz 0 op osz -> stall <= stalled -> r = 2 ^ 64 - e ->
  (e = ZSTD_error_noForwardProgress_destFull \/ e = ZSTD_error_noForwardProgress_inputEmpty) ->
  stall_error_b e stalled ip isz op osz 0 = true.
Proof.
  intros Hs Hle Hr He. unfold stall_ok in Hs.
  destruct Hs as (H1 & H2 & H3 & H4); [subst r; destruct He; subst e; auto|].
  unfold stall_error_b, NO_PROGRESS_MAX in *. unfold ZSTD_NO_FORWARD_PROGRESS_MAX in H1.
  subst ip op.
  replace (stalled + 1 <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  simpl.
  destruct H4 as [[H4 H5] | (H4 & H5 & H6)]; subst r.
  - assert (e = ZSTD_error_noForwardProgress_destFull) by lia. subst e.
    subst osz. reflexivity.
  - assert (e = ZSTD_error_noForwardProgress_inputEmpty) by lia. subst e.
    unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
    simpl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. subst isz. reflexivity.
Qed.

Lemma VSF_out_app (c dl: list Z) got : 0 <= got -> got + Zlength dl <= Zlength c ->
  dl = sublist got (got + Zlength dl) c -> sublist 0 got c ++ dl = sublist 0 (got + Zlength dl) c.
Proof. intros H1 H2 H3. pose proof (Zlength_nonneg dl). rewrite H3 at 1. rewrite sublist_rejoin by lia. reflexivity. Qed.

(* the bytes read after a call on the chunk bs[ipos..ipos+ilen) *)
Lemma VSF_read (l: list Z) ipos ilen a ip' a' :
  0 <= ipos -> 0 <= a -> ipos + a <= Zlength l -> 0 <= ilen -> ipos + ilen <= Zlength l ->
  0 <= ip' <= ilen -> 0 <= a' -> 0 + a <= ip' + a' -> (ip' + a' <= ilen \/ ip' + a' = 0 + a) ->
  sublist 0 (ipos + a) l ++ sublist (0 + a) (ip' + a') (sublist ipos (ipos + ilen) l) =
    sublist 0 (ipos + ip' + a') l /\ ipos + ip' + a' <= Zlength l.
Proof.
  intros. destruct H7 as [H7 | H7].
  - rewrite sublist_sublist by lia. replace (0 + a + ipos) with (ipos + a) by lia.
    replace (ip' + a' + ipos) with (ipos + ip' + a') by lia. rewrite sublist_rejoin by lia. split; [reflexivity | lia].
  - rewrite (sublist_nil_gen _ (0 + a) (ip' + a')) by lia. rewrite app_nil_r. split; [f_equal; lia | lia].
Qed.

(* all bytes of the call (read, and the unread rest of the chunk) are a prefix of the series *)
Lemma VSF_sall (l: list Z) ipos ilen ip' a' :
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength l -> 0 <= ip' + a' -> ipos + ip' + a' <= Zlength l ->
  is_prefix (sublist 0 (ipos + ip' + a') l ++ sublist (ip' + a') ilen (sublist ipos (ipos + ilen) l)) l.
Proof.
  intros. destruct (Z_le_gt_dec (ip' + a') ilen) as [Hle | Hgt].
  - rewrite sublist_sublist by lia. replace (ip' + a' + ipos) with (ipos + ip' + a') by lia.
    rewrite sublist_rejoin by lia. apply VSF_is_prefix_sublist. lia.
  - rewrite (sublist_nil_gen _ (ip' + a') ilen) by lia. rewrite app_nil_r. apply VSF_is_prefix_sublist. lia.
Qed.
