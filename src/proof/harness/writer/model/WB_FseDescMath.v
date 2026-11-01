(* Plain-Coq facts for the body of fse_put_description (harness/writer.h): the fields the C loop
   puts, step by step, are those of fse_desc_fields (WModel.ncount_fields). *)
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Require Import Zstd.proof.harness.writer.model.WM_NCount.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields still to put from symbol s on, with remaining r; the remaining count from s on *)

Definition fd_NF (norm: list Z) (s r: Z) : list (Z * Z) :=
  ncount_fields (length (skipn (Z.to_nat s) norm)) (skipn (Z.to_nat s) norm) r.

Definition fd_rsum (norm: list Z) (s: Z) : Z := zsum (map ncount_of (skipn (Z.to_nat s) norm)).

(* the state of the bit writer: fields RF still to put lead from W / L to FIN *)
Definition fd_ok (RF: list (Z * Z)) (FIN: Z * Z) (W L: Z) : Prop :=
  fields_ok RF /\ fields_wl RF W L = FIN /\ 0 <= L /\ 0 <= W < 2 ^ L.

Lemma ncf_fuel : forall f1 f2 l r, (length l <= f1)%nat -> (length l <= f2)%nat ->
  ncount_fields f1 l r = ncount_fields f2 l r.
Proof.
  induction f1 as [|f1 IH]; intros f2 l r H1 H2.
  - destruct l; [|simpl in H1; lia]. destruct f2; reflexivity.
  - destruct l as [|p l]; [destruct f2; reflexivity|].
    destruct f2 as [|f2]; [simpl in H2; lia|]. simpl in H1, H2. cbn [ncount_fields].
    destruct (p =? 0).
    + rewrite (IH f2); auto; rewrite length_skipn; lia.
    + rewrite (IH f2); auto; lia.
Qed.

Lemma zrun_le : forall l, (zrun l <= length l)%nat.
Proof. induction l as [|p l IH]; simpl; [lia|]. destruct (p =? 0); simpl; lia. Qed.

Lemma zrun_step : forall l z, (z <= zrun l)%nat -> (z < length l)%nat -> nth z l 0 = 0 -> (S z <= zrun l)%nat.
Proof.
  induction l as [|p l IH]; intros z H1 H2 H3; simpl in *; [lia|].
  destruct z as [|z].
  - subst p. simpl. lia.
  - destruct (p =? 0); [|lia]. specialize (IH z ltac:(lia) ltac:(lia) H3). lia.
Qed.

Lemma zrun_stop : forall l z, (z <= zrun l)%nat -> (z < length l)%nat -> nth z l 0 <> 0 -> zrun l = z.
Proof.
  induction l as [|p l IH]; intros z H1 H2 H3; simpl in *; [lia|].
  destruct z as [|z].
  - destruct (p =? 0) eqn:E; [apply Z.eqb_eq in E; congruence | reflexivity].
  - destruct (p =? 0); [|lia]. rewrite (IH z); auto; lia.
Qed.

Lemma zrun_end : forall l z, (z <= zrun l)%nat -> (length l <= z)%nat -> zrun l = z.
Proof. intros. pose proof (zrun_le l). lia. Qed.

Lemma zrun_sum : forall l z, (z <= zrun l)%nat -> zsum (map ncount_of (skipn z l)) = zsum (map ncount_of l).
Proof.
  induction l as [|p l IH]; intros z H; [destruct z; reflexivity|].
  destruct z as [|z]; [reflexivity|]. simpl in H. destruct (p =? 0) eqn:E; [|lia].
  apply Z.eqb_eq in E. subst p. simpl skipn. rewrite (IH z) by lia. simpl. reflexivity.
Qed.

Lemma skipn_S_nth : forall (l: list Z) n, (n < length l)%nat -> skipn n l = nth n l 0 :: skipn (S n) l.
Proof. induction l as [|a l IH]; intros n H; simpl in H; [lia|]. destruct n; simpl; auto. apply IH. lia. Qed.

Lemma skipn_skipn' : forall {A} (l: list A) a b, skipn a (skipn b l) = skipn (a + b) l.
Proof. intros. rewrite skipn_skipn. reflexivity. Qed.

(* one iteration of the C loop *)
Lemma fd_NF_step : forall norm s r, 0 <= s < Zlength norm ->
  fd_NF norm s r = ncount_field (zn norm s) r ::
    (if zn norm s =? 0 then
       repeat (3, 2) (zrun (skipn (Z.to_nat (s + 1)) norm) / 3) ++
       [(Z.of_nat (zrun (skipn (Z.to_nat (s + 1)) norm) mod 3), 2)] ++
       fd_NF norm (s + 1 + Z.of_nat (zrun (skipn (Z.to_nat (s + 1)) norm))) (r - ncount_of (zn norm s))
     else fd_NF norm (s + 1) (r - ncount_of (zn norm s))).
Proof.
  intros norm s r Hs. rewrite Zlength_correct in Hs. unfold fd_NF.
  rewrite (skipn_S_nth norm (Z.to_nat s)) by lia.
  replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia.
  set (rest := skipn (S (Z.to_nat s)) norm). unfold zn.
  cbn [length ncount_fields].
  destruct (nth (Z.to_nat s) norm 0 =? 0); [|reflexivity].
  f_equal. f_equal. f_equal.
  replace (Z.to_nat (s + 1 + Z.of_nat (zrun rest))) with (zrun rest + S (Z.to_nat s))%nat by lia.
  rewrite <- skipn_skipn'. fold rest.
  apply ncf_fuel; rewrite ?length_skipn; lia.
Qed.

Lemma fd_NF_end : forall norm r, fd_NF norm (Zlength norm) r = nil.
Proof.
  intros. unfold fd_NF. rewrite Zlength_correct, Nat2Z.id, skipn_all. reflexivity.
Qed.

Lemma fd_rsum_step : forall norm s, 0 <= s < Zlength norm ->
  fd_rsum norm s = ncount_of (zn norm s) + fd_rsum norm (s + 1).
Proof.
  intros norm s Hs. rewrite Zlength_correct in Hs. unfold fd_rsum, zn.
  rewrite (skipn_S_nth norm (Z.to_nat s)) by lia.
  replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia. reflexivity.
Qed.

Lemma fd_rsum_zeros : forall norm s z, 0 <= s -> (z <= zrun (skipn (Z.to_nat s) norm))%nat ->
  fd_rsum norm (s + Z.of_nat z) = fd_rsum norm s.
Proof.
  intros norm s z Hs Hz. unfold fd_rsum.
  replace (Z.to_nat (s + Z.of_nat z)) with (z + Z.to_nat s)%nat by lia.
  rewrite <- skipn_skipn'. apply zrun_sum. auto.
Qed.

Lemma fd_rsum_end : forall norm, fd_rsum norm (Zlength norm) = 0.
Proof. intros. unfold fd_rsum. rewrite Zlength_correct, Nat2Z.id, skipn_all. reflexivity. Qed.

Lemma zsum_skipn_le : forall l n, Forall (fun p => -1 <= p) l ->
  0 <= zsum (map ncount_of (skipn n l)) <= zsum (map ncount_of l).
Proof.
  induction l as [|p l IH]; intros n H; [destruct n; simpl; lia|].
  inversion H; subst. pose proof (ncount_of_facts p H2). pose proof (zsum_nonneg l H3).
  destruct n as [|n].
  - simpl. lia.
  - simpl skipn. specialize (IH n H3). simpl. lia.
Qed.

Lemma fd_rsum_range : forall norm log s, ndist_ok log norm -> 0 <= fd_rsum norm s <= 2 ^ log.
Proof.
  intros norm log s [_ [_ [Hf [Hs _]]]]. unfold fd_rsum. rewrite <- Hs.
  apply zsum_skipn_le. eapply Forall_impl; [|exact Hf]. simpl. lia.
Qed.

Lemma fd_rsum_0 : forall norm log, ndist_ok log norm -> fd_rsum norm 0 = 2 ^ log.
Proof. intros norm log [_ [_ [_ [Hs _]]]]. exact Hs. Qed.

(* the start: the first field (log - 5 in 4 bits) put *)
Lemma fd_start : forall norm log, ndist_ok log norm ->
  fd_ok (fd_NF norm 0 (2 ^ log)) (fields_wl (fse_desc_fields norm log) 0 0) (log - 5) 4 /\
  0 <= log - 5 < 2 ^ 4.
Proof.
  intros norm log Hnd. pose proof (fse_desc_fields_ok norm log Hnd) as Hok.
  pose proof Hnd as [Hl _].
  unfold fse_desc_fields in Hok. inversion Hok; subst.
  unfold fd_ok, fd_NF, fse_desc_fields. simpl skipn. change (Z.to_nat 0) with O. simpl skipn.
  split; [|change (2 ^ 4) with 16; lia].
  split; [auto|]. split; [cbn [fields_wl]; f_equal; lia|]. split; [lia|]. change (2 ^ 4) with 16; lia.
Qed.

(* one field put by bits_put *)
Lemma fd_put : forall v nb RF FIN W L, fd_ok ((v, nb) :: RF) FIN W L ->
  (0 <= nb <= 32 /\ 0 <= v < 2 ^ nb) /\ fd_ok RF FIN (W + v * 2 ^ L) (L + nb).
Proof.
  intros v nb RF FIN W L [Hok [Hwl [HL HW]]].
  pose proof (Forall_inv Hok) as [Hnb Hv]. pose proof (Forall_inv_tail Hok) as Hok'.
  simpl in Hnb, Hv. split; [auto|].
  split; [auto|]. split; [exact Hwl|]. split; [lia|].
  rewrite Z.pow_add_r by lia. pose proof (Z.pow_pos_nonneg 2 L ltac:(lia) ltac:(lia)). nia.
Qed.

(* the end: nothing left to put *)
Lemma fd_end : forall norm log W L, fd_ok nil (fields_wl (fse_desc_fields norm log) 0 0) W L ->
  bw_pad W L = fse_desc_bytes norm log /\ 0 <= L /\ 0 <= W < 2 ^ L.
Proof.
  intros norm log W L [_ [Hwl [HL HW]]]. change (fields_wl nil W L) with (W, L) in Hwl.
  unfold fse_desc_bytes, fields_pad, fields_W, fields_L. rewrite <- Hwl. auto.
Qed.

(* the length of the bytes put so far *)
Lemma fd_full_len : forall W L, 0 <= L -> Zlength (bw_full W L) = L / 8.
Proof.
  intros. unfold bw_full. rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id. apply Z.div_pos; lia.
Qed.

Lemma fd_pad_len : forall W L, 0 <= L -> Zlength (bw_pad W L) = (L + 7) / 8.
Proof.
  intros. unfold bw_pad. rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id. apply Z.div_pos; lia.
Qed.

(* the C's computation of a field: bits, lower_mask, threshold *)
Lemma fd_field_arith : forall r, 0 <= r <= 512 ->
  let bits := Z.log2 (r + 1) + 1 in
  1 <= bits <= 10 /\ r + 1 < 2 ^ bits /\ 2 ^ (bits - 1) <= r + 1 /\
  2 ^ bits <= 1024.
Proof.
  intros r Hr bits. unfold bits.
  pose proof (Z.log2_spec (r + 1) ltac:(lia)) as [H1 H2].
  assert (Z.log2 (r + 1) <= 9).
  { assert (Z.log2 (r + 1) <= Z.log2 1023) by (apply Z.log2_le_mono; lia). exact H. }
  pose proof (Z.log2_nonneg (r + 1)).
  replace (Z.log2 (r + 1) + 1 - 1) with (Z.log2 (r + 1)) by lia.
  rewrite Z.pow_succ_r in * by lia.
  assert (2 ^ Z.log2 (r + 1) <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 9) with 512 in *. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
Qed.

Lemma fd_field_eq : forall p r,
  ncount_field p r =
  (let bits := Z.log2 (r + 1) + 1 in
   let th := 2 ^ bits - 1 - (r + 1) in
   if p + 1 <? th then (p + 1, bits - 1)
   else if p + 1 <=? 2 ^ (bits - 1) - 1 then (p + 1, bits) else (p + 1 + th, bits)).
Proof. intros. reflexivity. Qed.

(* the norm in the C's short array *)
Lemma fd_norm_range : forall norm log s, ndist_ok log norm -> 0 <= s < Zlength norm ->
  -1 <= zn norm s <= 2 ^ log /\ 2 ^ log <= 512.
Proof.
  intros norm log s [Hl [_ [Hf _]]] Hs. split.
  - rewrite Forall_forall in Hf. apply Hf. unfold zn. apply nth_In. rewrite Zlength_correct in Hs. lia.
  - change 512 with (2 ^ 9). apply Z.pow_le_mono_r; lia.
Qed.

Lemma fd_zn_nth : forall norm s z, 0 <= s -> nth z (skipn (Z.to_nat s) norm) 0 = zn norm (s + Z.of_nat z).
Proof.
  intros. unfold zn. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma fd_zrun_bound : forall norm s, 0 <= s ->
  s + Z.of_nat (zrun (skipn (Z.to_nat s) norm)) <= Z.max s (Zlength norm).
Proof.
  intros. pose proof (zrun_le (skipn (Z.to_nat s) norm)). rewrite length_skipn in H0.
  rewrite Zlength_correct. lia.
Qed.

(* the C loop counting the zeros after a probability 0 *)
Lemma fd_zrun_loop : forall norm s z, 0 <= s -> 0 <= z <= Z.of_nat (zrun (skipn (Z.to_nat s) norm)) ->
  ((s + z <? Zlength norm) && (zn norm (s + z) =? 0) = true -> z + 1 <= Z.of_nat (zrun (skipn (Z.to_nat s) norm))) /\
  ((s + z <? Zlength norm) && (zn norm (s + z) =? 0) = false -> z = Z.of_nat (zrun (skipn (Z.to_nat s) norm))).
Proof.
  intros norm s z Hs Hz. set (l := skipn (Z.to_nat s) norm) in *.
  assert (Hlen: Z.of_nat (length l) = Z.max 0 (Zlength norm - s)).
  { unfold l. rewrite length_skipn, Zlength_correct. lia. }
  assert (Hn: nth (Z.to_nat z) l 0 = zn norm (s + z)).
  { unfold l. rewrite fd_zn_nth by lia. f_equal. lia. }
  split; intros Hb.
  - apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.ltb_lt in H1. apply Z.eqb_eq in H2.
    assert (A1: (Z.to_nat z <= zrun l)%nat) by lia.
    assert (A2: (Z.to_nat z < length l)%nat) by lia.
    assert (A3: nth (Z.to_nat z) l 0 = 0) by (rewrite Hn; auto).
    pose proof (zrun_step l (Z.to_nat z) A1 A2 A3). lia.
  - apply Bool.andb_false_iff in Hb. destruct Hb as [H1 | H2].
    + apply Z.ltb_ge in H1. rewrite (zrun_end l (Z.to_nat z)) by lia. lia.
    + destruct (Z.ltb_spec (s + z) (Zlength norm)).
      * apply Z.eqb_neq in H2. rewrite (zrun_stop l (Z.to_nat z)) by (try rewrite Hn; auto; lia). lia.
      * rewrite (zrun_end l (Z.to_nat z)) by lia. lia.
Qed.

(* the C loop putting the repeat flags 3 *)
Lemma fd_div3_step : forall n j, 0 <= n -> 0 <= j <= n / 3 -> n - 3 * j >= 3 -> j + 1 <= n / 3.
Proof. intros. apply Z.div_le_lower_bound; lia. Qed.

Lemma fd_div3_end : forall n j, 0 <= n -> 0 <= j <= n / 3 -> n - 3 * j < 3 -> j = n / 3 /\ n - 3 * j = n mod 3.
Proof.
  intros n j Hn Hj Hlt. pose proof (Z.div_mod n 3 ltac:(lia)). pose proof (Z.mod_pos_bound n 3 ltac:(lia)).
  assert (j = n / 3) by lia. split; lia.
Qed.

Lemma fd_repeat_step : forall (x: Z * Z) k j, j < k -> repeat x (Z.to_nat (k - j)) = x :: repeat x (Z.to_nat (k - (j + 1))).
Proof. intros. replace (Z.to_nat (k - j)) with (S (Z.to_nat (k - (j + 1)))) by lia. reflexivity. Qed.

Lemma fd_zr_nat : forall zr: nat, repeat (3, 2) (zr / 3) = repeat (3, 2) (Z.to_nat (Z.of_nat zr / 3 - 0)) /\
  Z.of_nat (zr mod 3) = Z.of_nat zr mod 3.
Proof.
  intros. split.
  - f_equal. rewrite Z.sub_0_r. change 3 with (Z.of_nat 3). rewrite <- (Nat2Z.inj_div zr 3). lia.
  - apply Nat2Z.inj_mod.
Qed.
