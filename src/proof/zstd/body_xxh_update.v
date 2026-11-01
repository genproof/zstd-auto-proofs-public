(* Body of ZSTD_XXH64_update (group xxh).
   Removed: the unfinished body_ZSTD_XXH64_update; this file keeps its helper lemmas (proof: AllBodies_xxh.v, body_ZSTD_XXH64_update_v2). *)
Require Import Zstd.proof.zstd.Gprog.
Require Import Zstd.proof.zstd.XxhLemmas.

(* ---------- the stripes of the model, consumed piecewise ---------- *)

Definition xxh_round4 (v: Z * Z * Z * Z) (c: list Z) : Z * Z * Z * Z :=
  match v with (v1, v2, v3, v4) =>
    (xxh_round v1 (le_field c 0 8), xxh_round v2 (le_field c 8 8),
     xxh_round v3 (le_field c 16 8), xxh_round v4 (le_field c 24 8)) end.

Lemma xxh_stripes_S: forall n v l, xxh_stripes (S n) v l =
  match v with (v1, v2, v3, v4) =>
    if Z.of_nat (length l) <? 32 then (v, l) else
    xxh_stripes n (xxh_round v1 (le_field l 0 8), xxh_round v2 (le_field l 8 8),
                   xxh_round v3 (le_field l 16 8), xxh_round v4 (le_field l 24 8)) (skipn 32 l) end.
Proof. reflexivity. Qed.

Lemma xxh_stripes_fuel: forall n m v l, (length l <= n)%nat -> (length l <= m)%nat ->
  xxh_stripes n v l = xxh_stripes m v l.
Proof.
  induction n; intros m v l Hn Hm.
  - destruct l; simpl in Hn; [|lia]. destruct m; simpl; auto. destruct v as [[[? ?] ?] ?]. reflexivity.
  - destruct m.
    + destruct l; simpl in Hm; [|lia]. simpl. destruct v as [[[? ?] ?] ?]. reflexivity.
    + cbn [xxh_stripes]. destruct v as [[[v1 v2] v3] v4].
      destruct (Z.of_nat (length l) <? 32) eqn:E; auto.
      apply Z.ltb_ge in E. apply IHn; rewrite length_skipn; lia.
Qed.

Lemma xxh_stripes_small: forall n v l, (length l < 32)%nat -> xxh_stripes n v l = (v, l).
Proof.
  intros. destruct n; cbn [xxh_stripes]; auto. destruct v as [[[v1 v2] v3] v4].
  replace (Z.of_nat (length l) <? 32) with true by (symmetry; apply Z.ltb_lt; lia). auto.
Qed.

Lemma xxh_stripes_step: forall v c t, length c = 32%nat ->
  xxh_stripes (length (c ++ t)) v (c ++ t) = xxh_stripes (length t) (xxh_round4 v c) t.
Proof.
  intros v c t Hc. replace (length (c ++ t)) with (S (31 + length t)) by (rewrite length_app; lia).
  rewrite xxh_stripes_S.
  destruct v as [[[v1 v2] v3] v4].
  replace (Z.of_nat (length (c ++ t)) <? 32) with false
    by (symmetry; apply Z.ltb_ge; rewrite length_app; lia).
  rewrite skipn_app, Hc. replace (32 - 32)%nat with O by lia.
  rewrite (skipn_all2 c) by lia. simpl app.
  unfold xxh_round4, le_field, slice.
  assert (forall i, (i + 8 <= 32)%nat -> firstn 8 (skipn i (c ++ t)) = firstn 8 (skipn i c)).
  { intros i Hi. rewrite skipn_app. rewrite firstn_app. rewrite length_skipn.
    replace (8 - (length c - i))%nat with O by lia. rewrite firstn_O, app_nil_r. reflexivity. }
  rewrite !H by lia.
  apply xxh_stripes_fuel; lia.
Qed.

Lemma xxh_stripes_rest_length: forall n v l, (length l <= n)%nat ->
  (length (snd (xxh_stripes n v l)) < 32)%nat.
Proof.
  induction n; intros v l H.
  - destruct l; simpl in H; [|lia]. simpl. lia.
  - cbn [xxh_stripes]. destruct v as [[[v1 v2] v3] v4].
    destruct (Z.of_nat (length l) <? 32) eqn:E.
    + apply Z.ltb_lt in E. simpl. lia.
    + apply Z.ltb_ge in E. apply IHn. rewrite length_skipn. lia.
Qed.

(* consuming l ++ bs = consuming l, then its rest followed by bs *)
Lemma xxh_stripes_app: forall n v l bs, (length l <= n)%nat ->
  xxh_stripes (length (l ++ bs)) v (l ++ bs) =
  xxh_stripes (length (snd (xxh_stripes n v l) ++ bs)) (fst (xxh_stripes n v l))
              (snd (xxh_stripes n v l) ++ bs).
Proof.
  induction n; intros v l bs H.
  - destruct l; simpl in H; [|lia]. simpl. destruct v as [[[? ?] ?] ?]. reflexivity.
  - destruct (Nat.lt_ge_cases (length l) 32).
    + rewrite (xxh_stripes_small (S n) v l H0). reflexivity.
    + rewrite <- (firstn_skipn 32 l) at 1 2.
      rewrite <- app_assoc. rewrite xxh_stripes_step by (rewrite length_firstn; lia).
      rewrite xxh_stripes_S. destruct v as [[[v1 v2] v3] v4].
      replace (Z.of_nat (length l) <? 32) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite <- IHn by (rewrite length_skipn; lia).
      f_equal.
      unfold xxh_round4, le_field, slice.
      assert (Hf: forall i, (i + 8 <= 32)%nat -> firstn 8 (skipn i (firstn 32 l)) = firstn 8 (skipn i l)).
      { intros i Hi. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia. }
      change (Z.to_nat 8) with 8%nat; change (Z.to_nat 0) with 0%nat;
      change (Z.to_nat 16) with 16%nat; change (Z.to_nat 24) with 24%nat.
      rewrite !Hf by lia. reflexivity.
Qed.

(* the facts about xxh_lanes / xxh_rest the body uses *)
Lemma xxh_rest_length: forall seed l, Zlength (xxh_rest seed l) < 32.
Proof.
  intros. unfold xxh_rest. rewrite Zlength_correct.
  pose proof (xxh_stripes_rest_length (length l) (xxh_init seed) l ltac:(lia)). lia.
Qed.

Lemma xxh_stripes_lr: forall seed l,
  xxh_stripes (length l) (xxh_init seed) l = (xxh_lanes seed l, xxh_rest seed l).
Proof. intros. unfold xxh_lanes, xxh_rest. destruct (xxh_stripes _ _ _); reflexivity. Qed.

Lemma xxh_app_small: forall seed l bs, Zlength (xxh_rest seed l ++ bs) < 32 ->
  xxh_lanes seed (l ++ bs) = xxh_lanes seed l /\ xxh_rest seed (l ++ bs) = xxh_rest seed l ++ bs.
Proof.
  intros. assert (E := xxh_stripes_app (length l) (xxh_init seed) l bs ltac:(lia)).
  rewrite !xxh_stripes_lr in E. simpl fst in E; simpl snd in E.
  rewrite (xxh_stripes_small _ _ (xxh_rest seed l ++ bs)) in E by (rewrite Zlength_correct in H; lia).
  injection E; auto.
Qed.

Lemma xxh_stripes_chunk: forall v c, length c = 32%nat ->
  xxh_stripes (length c) v c = (xxh_round4 v c, []).
Proof.
  intros. rewrite <- (app_nil_r c) at 1 2. rewrite xxh_stripes_step by auto.
  apply xxh_stripes_small. simpl; lia.
Qed.

Lemma xxh_app_fill: forall seed l c, Zlength (xxh_rest seed l ++ c) = 32 ->
  xxh_lanes seed (l ++ c) = xxh_round4 (xxh_lanes seed l) (xxh_rest seed l ++ c) /\ xxh_rest seed (l ++ c) = [].
Proof.
  intros. assert (E := xxh_stripes_app (length l) (xxh_init seed) l c ltac:(lia)).
  rewrite !xxh_stripes_lr in E. simpl fst in E; simpl snd in E.
  rewrite Zlength_correct in H.
  rewrite (xxh_stripes_chunk _ (xxh_rest seed l ++ c)) in E by lia.
  injection E; auto.
Qed.

Lemma xxh_app_chunk: forall seed l c, xxh_rest seed l = [] -> Zlength c = 32 ->
  xxh_lanes seed (l ++ c) = xxh_round4 (xxh_lanes seed l) c /\ xxh_rest seed (l ++ c) = [].
Proof.
  intros. pose proof (xxh_app_fill seed l c). rewrite H in H1. simpl app in H1. auto.
Qed.

(* ---------- byte arrays ---------- *)

Lemma xu_arr_split3: forall sh n i k (l: list val) p,
  0 <= i -> 0 <= k -> i + k <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) l p =
  (data_at sh (tarray tuchar i) (sublist 0 i l) p *
   data_at sh (tarray tuchar k) (sublist i (i + k) l) (offset_val i p) *
   data_at sh (tarray tuchar (n - (i + k))) (sublist (i + k) n l) (offset_val (i + k) p))%logic.
Proof.
  intros. rewrite (split3_data_at_Tarray_tuchar sh n i (i + k)) by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite !arr_field_address0 by (auto; lia).
  replace (i + k - i) with k by lia. simpl sizeof. rewrite !Z.mul_1_l. reflexivity.
Qed.
