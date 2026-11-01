(* w_compressed_block, the codes and extra bits of a sequence (plain Coq): ll_code_of / ml_code_of / Z.log2 give codes
   whose baseline and extra
   bits cover the value. *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.

Lemma lcode_spec : forall (base bits: list Z) (n: nat) (x: Z),
  (forall c, (c < n)%nat -> nth (S c) base 0 = nth c base 0 + 2 ^ nth c bits 0) ->
  (forall c, (c <= n)%nat -> 0 <= nth c bits 0) ->
  nth 0 base 0 <= x < nth n base 0 + 2 ^ nth n bits 0 ->
  0 <= lcode base n x <= Z.of_nat n /\
  nth (Z.to_nat (lcode base n x)) base 0 <= x <
    nth (Z.to_nat (lcode base n x)) base 0 + 2 ^ nth (Z.to_nat (lcode base n x)) bits 0.
Proof.
  intros base bits n. induction n as [|m IH]; intros x Hc Hb Hx.
  - simpl. lia.
  - change (lcode base (S m) x) with
      (if nth (S m) base 0 <=? x then Z.of_nat (S m) else lcode base m x).
    destruct (Z.leb_spec (nth (S m) base 0) x) as [Hle|Hlt].
    + rewrite Nat2Z.id. lia.
    + destruct (IH x) as [H1 H2].
      * intros c Hc'. apply Hc. lia.
      * intros c Hc'. apply Hb. lia.
      * rewrite Hc in Hlt by lia. lia.
      * lia.
Qed.

Lemma nth_bound_all : forall (l: list Z) lo hi i, lo <= 0 <= hi ->
  Forall (fun z => lo <= z <= hi) l -> lo <= nth i l 0 <= hi.
Proof.
  intros l lo hi i H HF. revert i. induction HF as [|a l Ha HF IH]; intros [|i]; simpl; auto; lia.
Qed.

Lemma LL_bits_range : Forall (fun z => 0 <= z <= 16) LL_bits_tab.
Proof. unfold LL_bits_tab. repeat constructor; lia. Qed.
Lemma ML_bits_range : Forall (fun z => 0 <= z <= 16) ML_bits_tab.
Proof. unfold ML_bits_tab. repeat constructor; lia. Qed.

Lemma LL_contig : forall c, (c < 35)%nat ->
  nth (S c) LL_base_tab 0 = nth c LL_base_tab 0 + 2 ^ nth c LL_bits_tab 0.
Proof.
  intros c Hc. do 35 (destruct c as [|c]; [reflexivity|]). lia.
Qed.
Lemma ML_contig : forall c, (c < 52)%nat ->
  nth (S c) ML_base_tab 0 = nth c ML_base_tab 0 + 2 ^ nth c ML_bits_tab 0.
Proof.
  intros c Hc. do 52 (destruct c as [|c]; [reflexivity|]). lia.
Qed.

Lemma ll_code_spec : forall ll, 0 <= ll < 2 ^ 17 - 1 ->
  0 <= ll_code_of ll <= 35 /\
  zn LL_base_tab (ll_code_of ll) <= ll < zn LL_base_tab (ll_code_of ll) + 2 ^ zn LL_bits_tab (ll_code_of ll).
Proof.
  intros ll H. unfold ll_code_of, zn.
  apply (lcode_spec LL_base_tab LL_bits_tab 35 ll LL_contig).
  - intros c _. apply (nth_bound_all _ 0 16); [lia | exact LL_bits_range].
  - simpl. lia.
Qed.

Lemma ml_code_spec : forall ml, 3 <= ml < 65539 + 2 ^ 16 ->
  0 <= ml_code_of ml <= 52 /\
  zn ML_base_tab (ml_code_of ml) <= ml < zn ML_base_tab (ml_code_of ml) + 2 ^ zn ML_bits_tab (ml_code_of ml).
Proof.
  intros ml H. unfold ml_code_of, zn.
  apply (lcode_spec ML_base_tab ML_bits_tab 52 ml ML_contig).
  - intros c _. apply (nth_bound_all _ 0 16); [lia | exact ML_bits_range].
  - simpl. lia.
Qed.

Lemma of_code_spec : forall ov, 1 <= ov < 2 ^ 32 ->
  0 <= Z.log2 ov <= 31 /\ 2 ^ Z.log2 ov <= ov < 2 ^ Z.log2 ov + 2 ^ Z.log2 ov.
Proof.
  intros ov H. destruct (Z.log2_spec ov) as [H1 H2]; [lia|].
  rewrite Z.pow_succ_r in H2 by (apply Z.log2_nonneg).
  split; [split; [apply Z.log2_nonneg|] | lia].
  assert (Z.log2 ov < 32); [|lia].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma sq_ll_unf : forall sq,
  sq_code 0 sq = ll_code_of (sq_ll sq) /\ sq_nbits 0 sq = zn LL_bits_tab (ll_code_of (sq_ll sq)) /\
  sq_extra 0 sq = sq_ll sq - zn LL_base_tab (ll_code_of (sq_ll sq)).
Proof. intros. repeat split. Qed.
Lemma sq_of_unf : forall sq,
  sq_code 1 sq = Z.log2 (sq_ov sq) /\ sq_nbits 1 sq = Z.log2 (sq_ov sq) /\
  sq_extra 1 sq = sq_ov sq - 2 ^ Z.log2 (sq_ov sq).
Proof. intros. repeat split. Qed.
Lemma sq_ml_unf : forall sq,
  sq_code 2 sq = ml_code_of (sq_ml sq) /\ sq_nbits 2 sq = zn ML_bits_tab (ml_code_of (sq_ml sq)) /\
  sq_extra 2 sq = sq_ml sq - zn ML_base_tab (ml_code_of (sq_ml sq)).
Proof. intros. repeat split. Qed.

Lemma sq_code_facts : forall ty sq, seq_ok sq -> 0 <= ty <= 2 ->
  0 <= sq_code ty sq <= ty_max ty /\ 0 <= sq_nbits ty sq <= 31 /\
  0 <= sq_extra ty sq < 2 ^ sq_nbits ty sq.
Proof.
  intros ty sq [H0 [H1 [H2 H3]]] Hty.
  change (2 ^ 17) with 131072 in H2. change (2 ^ 32) with 4294967296 in H3.
  assert (ty = 0 \/ ty = 1 \/ ty = 2) as [Ht|[Ht|Ht]] by lia; subst ty.
  - destruct (sq_ll_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 0) with 35.
    destruct (ll_code_spec (sq_ll sq)) as [A B]; [lia|].
    pose proof (nth_bound_all LL_bits_tab 0 16 (Z.to_nat (ll_code_of (sq_ll sq)))
      ltac:(lia) LL_bits_range). unfold zn in *. lia.
  - destruct (sq_of_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 1) with 31.
    destruct (of_code_spec (sq_ov sq)) as [A B]; [lia|]. lia.
  - destruct (sq_ml_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 2) with 52.
    destruct (ml_code_spec (sq_ml sq)) as [A B]; [lia|].
    pose proof (nth_bound_all ML_bits_tab 0 16 (Z.to_nat (ml_code_of (sq_ml sq)))
      ltac:(lia) ML_bits_range). unfold zn in *. lia.
Qed.

(* what the decoder rebuilds from a code and its extra bits *)
Lemma sq_rebuild : forall sq, seq_ok sq ->
  nth (Z.to_nat (sq_code 0 sq)) LL_base_tab 0 + sq_extra 0 sq = sq_ll sq /\
  nth (Z.to_nat (sq_code 2 sq)) ML_base_tab 0 + sq_extra 2 sq = sq_ml sq /\
  2 ^ sq_code 1 sq + sq_extra 1 sq = sq_ov sq /\
  nth (Z.to_nat (sq_code 0 sq)) LL_bits_tab 0 = sq_nbits 0 sq /\
  nth (Z.to_nat (sq_code 2 sq)) ML_bits_tab 0 = sq_nbits 2 sq /\
  sq_code 1 sq = sq_nbits 1 sq.
Proof.
  intros sq _.
  destruct (sq_ll_unf sq) as [A1 [A2 A3]]. destruct (sq_of_unf sq) as [B1 [B2 B3]].
  destruct (sq_ml_unf sq) as [C1 [C2 C3]].
  rewrite A1, A2, A3, B1, B2, B3, C1, C2, C3. unfold zn. repeat split; lia.
Qed.

(* every lemma above together *)
Theorem wm_blkcodes_all :
  (forall ty sq, seq_ok sq -> 0 <= ty <= 2 ->
     0 <= sq_code ty sq <= ty_max ty /\ 0 <= sq_nbits ty sq <= 31 /\ 0 <= sq_extra ty sq < 2 ^ sq_nbits ty sq) /\
  (forall sq, seq_ok sq ->
     nth (Z.to_nat (sq_code 0 sq)) LL_base_tab 0 + sq_extra 0 sq = sq_ll sq /\
     nth (Z.to_nat (sq_code 2 sq)) ML_base_tab 0 + sq_extra 2 sq = sq_ml sq /\
     2 ^ sq_code 1 sq + sq_extra 1 sq = sq_ov sq /\
     nth (Z.to_nat (sq_code 0 sq)) LL_bits_tab 0 = sq_nbits 0 sq /\
     nth (Z.to_nat (sq_code 2 sq)) ML_bits_tab 0 = sq_nbits 2 sq /\
     sq_code 1 sq = sq_nbits 1 sq).
Proof. exact (conj sq_code_facts sq_rebuild). Qed.
