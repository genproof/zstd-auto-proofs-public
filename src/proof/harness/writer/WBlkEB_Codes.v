(* Phase B of segment E: the code facts of a sequence (a copy of the proof of
   WM_BlkCodes.sq_code_facts, renamed). *)
Require Import Zstd.proof.harness.writer.model.WM_BlkDefs.

Lemma ebc_lcode_spec : forall (base bits: list Z) (n: nat) (x: Z),
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

Lemma ebc_nth_bound_all : forall (l: list Z) lo hi i, lo <= 0 <= hi ->
  Forall (fun z => lo <= z <= hi) l -> lo <= nth i l 0 <= hi.
Proof.
  intros l lo hi i H HF. revert i. induction HF as [|a l Ha HF IH]; intros [|i]; simpl; auto; lia.
Qed.

Lemma ebc_LL_bits_range : Forall (fun z => 0 <= z <= 16) LL_bits_tab.
Proof. unfold LL_bits_tab. repeat constructor; lia. Qed.
Lemma ebc_ML_bits_range : Forall (fun z => 0 <= z <= 16) ML_bits_tab.
Proof. unfold ML_bits_tab. repeat constructor; lia. Qed.

Lemma ebc_LL_contig : forall c, (c < 35)%nat ->
  nth (S c) LL_base_tab 0 = nth c LL_base_tab 0 + 2 ^ nth c LL_bits_tab 0.
Proof.
  intros c Hc. do 35 (destruct c as [|c]; [reflexivity|]). lia.
Qed.
Lemma ebc_ML_contig : forall c, (c < 52)%nat ->
  nth (S c) ML_base_tab 0 = nth c ML_base_tab 0 + 2 ^ nth c ML_bits_tab 0.
Proof.
  intros c Hc. do 52 (destruct c as [|c]; [reflexivity|]). lia.
Qed.

Lemma ebc_ll_code_spec : forall ll, 0 <= ll < 2 ^ 17 - 1 ->
  0 <= ll_code_of ll <= 35 /\
  zn LL_base_tab (ll_code_of ll) <= ll < zn LL_base_tab (ll_code_of ll) + 2 ^ zn LL_bits_tab (ll_code_of ll).
Proof.
  intros ll H. unfold ll_code_of, zn.
  apply (ebc_lcode_spec LL_base_tab LL_bits_tab 35 ll ebc_LL_contig).
  - intros c _. apply (ebc_nth_bound_all _ 0 16); [lia | exact ebc_LL_bits_range].
  - simpl. lia.
Qed.

Lemma ebc_ml_code_spec : forall ml, 3 <= ml < 65539 + 2 ^ 16 ->
  0 <= ml_code_of ml <= 52 /\
  zn ML_base_tab (ml_code_of ml) <= ml < zn ML_base_tab (ml_code_of ml) + 2 ^ zn ML_bits_tab (ml_code_of ml).
Proof.
  intros ml H. unfold ml_code_of, zn.
  apply (ebc_lcode_spec ML_base_tab ML_bits_tab 52 ml ebc_ML_contig).
  - intros c _. apply (ebc_nth_bound_all _ 0 16); [lia | exact ebc_ML_bits_range].
  - simpl. lia.
Qed.

Lemma ebc_of_code_spec : forall ov, 1 <= ov < 2 ^ 32 ->
  0 <= Z.log2 ov <= 31 /\ 2 ^ Z.log2 ov <= ov < 2 ^ Z.log2 ov + 2 ^ Z.log2 ov.
Proof.
  intros ov H. destruct (Z.log2_spec ov) as [H1 H2]; [lia|].
  rewrite Z.pow_succ_r in H2 by (apply Z.log2_nonneg).
  split; [split; [apply Z.log2_nonneg|] | lia].
  assert (Z.log2 ov < 32); [|lia].
  apply Z.log2_lt_pow2; lia.
Qed.

Lemma ebc_sq_ll_unf : forall sq,
  sq_code 0 sq = ll_code_of (sq_ll sq) /\ sq_nbits 0 sq = zn LL_bits_tab (ll_code_of (sq_ll sq)) /\
  sq_extra 0 sq = sq_ll sq - zn LL_base_tab (ll_code_of (sq_ll sq)).
Proof. intros. repeat split. Qed.
Lemma ebc_sq_of_unf : forall sq,
  sq_code 1 sq = Z.log2 (sq_ov sq) /\ sq_nbits 1 sq = Z.log2 (sq_ov sq) /\
  sq_extra 1 sq = sq_ov sq - 2 ^ Z.log2 (sq_ov sq).
Proof. intros. repeat split. Qed.
Lemma ebc_sq_ml_unf : forall sq,
  sq_code 2 sq = ml_code_of (sq_ml sq) /\ sq_nbits 2 sq = zn ML_bits_tab (ml_code_of (sq_ml sq)) /\
  sq_extra 2 sq = sq_ml sq - zn ML_base_tab (ml_code_of (sq_ml sq)).
Proof. intros. repeat split. Qed.

Lemma ebc_sq_code_facts : forall ty sq, seq_ok sq -> 0 <= ty <= 2 ->
  0 <= sq_code ty sq <= ty_max ty /\ 0 <= sq_nbits ty sq <= 31 /\
  0 <= sq_extra ty sq < 2 ^ sq_nbits ty sq.
Proof.
  intros ty sq [H0 [H1 [H2 H3]]] Hty.
  change (2 ^ 17) with 131072 in H2. change (2 ^ 32) with 4294967296 in H3.
  assert (ty = 0 \/ ty = 1 \/ ty = 2) as [Ht|[Ht|Ht]] by lia; subst ty.
  - destruct (ebc_sq_ll_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 0) with 35.
    destruct (ebc_ll_code_spec (sq_ll sq)) as [A B]; [lia|].
    pose proof (ebc_nth_bound_all LL_bits_tab 0 16 (Z.to_nat (ll_code_of (sq_ll sq)))
      ltac:(lia) ebc_LL_bits_range). unfold zn in *. lia.
  - destruct (ebc_sq_of_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 1) with 31.
    destruct (ebc_of_code_spec (sq_ov sq)) as [A B]; [lia|]. lia.
  - destruct (ebc_sq_ml_unf sq) as [E1 [E2 E3]]. rewrite E1, E2, E3. change (ty_max 2) with 52.
    destruct (ebc_ml_code_spec (sq_ml sq)) as [A B]; [lia|].
    pose proof (ebc_nth_bound_all ML_bits_tab 0 16 (Z.to_nat (ml_code_of (sq_ml sq)))
      ltac:(lia) ebc_ML_bits_range). unfold zn in *. lia.
Qed.
