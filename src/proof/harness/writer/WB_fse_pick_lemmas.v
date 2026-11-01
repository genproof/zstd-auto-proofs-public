(* Unit-independent math of fse_pick's body: the loop invariant of the drawing
   loop over the drawn prefix `pre` of norm, its steps for the three kinds of probability, and the post. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Local Open Scope Z_scope.

(* what remains to distribute, the non-zero counts so far, the needed symbols in s..maxsym *)
Definition fp_rem (log: Z) (pre: list Z) : Z := 2 ^ log - zsum (map ncount_of pre).
Definition fp_nz (pre: list Z) : Z := Zlength (filter (fun p => negb (p =? 0)) pre).
Definition fp_left (need: list Z) (s maxsym: Z) : Z := zsum (sublist s (maxsym + 1) need).
(* points to keep for later symbols if s gets a non-zero probability (L: needed in s+1..maxsym) *)
Definition fp_rsv (n L: Z) : Z := L + Z.max 0 (2 - (n + 1 + L)).

Definition fp_inv (log maxsym: Z) (need pre: list Z) : Prop :=
  Zlength pre <= maxsym + 1 /\ 0 <= fp_rem log pre /\
  fp_left need (Zlength pre) maxsym + Z.max 0 (2 - fp_nz pre - fp_left need (Zlength pre) maxsym)
    <= fp_rem log pre /\
  (Zlength pre <= maxsym -> 2 <= fp_nz pre + (maxsym - Zlength pre + 1)) /\
  (0 < fp_rem log pre -> Zlength pre <= maxsym) /\
  (fp_rem log pre = 0 -> last pre 0 <> 0) /\
  Forall (fun p => -1 <= p <= 2 ^ log) pre /\
  (forall i, 0 <= i < Zlength pre -> zn need i <> 0 -> zn pre i <> 0).

(* the options of symbol s = Zlength pre (n = fp_nz pre, L = fp_left need (s + 1) maxsym, R = fp_rem) *)
Definition fp_c0 (maxsym s ns n L R: Z) : bool :=
  (ns =? 0) && negb (s =? maxsym) && (2 <=? n + (maxsym - s)) && (L + Z.max 0 (2 - (n + L)) <=? R).
Definition fp_c1 (maxsym s n L R: Z) : bool :=
  (fp_rsv n L <=? R - 1) && (negb (s =? maxsym) || (R =? 1)).
Definition fp_c2 (maxsym s n L R: Z) : bool :=
  (1 <=? R - fp_rsv n L) && (negb (s =? maxsym) || (fp_rsv n L =? 0)).

Definition fp_opts (c0 c1 c2: bool) : list Z :=
  (if c0 then [0] else []) ++ (if c1 then [1] else []) ++ (if c2 then [2] else []).

(* the probability p drawn for symbol s = Zlength pre, by its kind *)
Definition fp_choice (log maxsym: Z) (need pre: list Z) (p: Z) : Prop :=
  let s := Zlength pre in let n := fp_nz pre in let L := fp_left need (s + 1) maxsym in
  let R := fp_rem log pre in
  (p = 0 /\ fp_c0 maxsym s (Znth s need) n L R = true) \/
  (p = -1 /\ fp_c1 maxsym s n L R = true) \/
  (fp_c2 maxsym s n L R = true /\ (s = maxsym -> p = R) /\ (s <> maxsym -> 1 <= p <= R - fp_rsv n L)).

Section FP.
Variables (log maxsym: Z) (need: list Z).
Hypotheses (Hlog: 5 <= log <= 9) (Hmax: 1 <= maxsym <= 52) (Hlen: Zlength need = 53)
  (Hneed: Forall (fun x => 0 <= x <= 1) need).

Lemma fp_pow_bounds : 32 <= 2 ^ log <= 512.
Proof.
  split; [replace 32 with (2 ^ 5) by reflexivity | replace 512 with (2 ^ 9) by reflexivity];
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. intros. unfold zsum. rewrite fold_right_app. induction a; simpl; [lia|]. unfold zsum in *. lia. Qed.

Lemma zsum_bounds01 : forall l, Forall (fun x => 0 <= x <= 1) l -> 0 <= zsum l <= Zlength l.
Proof.
  induction l as [|a l IH]; intros H.
  - unfold zsum; simpl. rewrite Zlength_nil. lia.
  - inversion H as [|x l' Ha Hl]; subst. specialize (IH Hl).
    change (zsum (a :: l)) with (a + zsum l). rewrite Zlength_cons. lia.
Qed.

Lemma fp_need_Znth : forall i, 0 <= i < 53 -> 0 <= Znth i need <= 1.
Proof. intros. eapply Forall_forall in Hneed; [exact Hneed|]. apply Znth_In. lia. Qed.

Lemma zn_Znth : forall l i, 0 <= i -> zn l i = Znth i l.
Proof. intros. unfold zn, Znth. destruct (Z_lt_dec i 0); [lia|]. reflexivity. Qed.

Lemma fp_left_bounds : forall s, 0 <= s <= maxsym + 1 -> 0 <= fp_left need s maxsym <= maxsym + 1 - s.
Proof.
  intros. unfold fp_left. pose proof (zsum_bounds01 (sublist s (maxsym + 1) need)) as B.
  rewrite Zlength_sublist in B by lia. apply B. apply Forall_sublist. auto.
Qed.

Lemma fp_left_step : forall s, 0 <= s <= maxsym ->
  fp_left need s maxsym = Znth s need + fp_left need (s + 1) maxsym.
Proof.
  intros. unfold fp_left. rewrite (sublist_split s (s + 1) (maxsym + 1)) by lia.
  rewrite zsum_app, sublist_len_1 by lia. change (zsum [Znth s need]) with (Znth s need + 0). lia.
Qed.

Lemma fp_left_end : fp_left need (maxsym + 1) maxsym = 0.
Proof. unfold fp_left. rewrite sublist_nil. reflexivity. Qed.

Lemma fp_rem_app : forall pre p, fp_rem log (pre ++ [p]) = fp_rem log pre - ncount_of p.
Proof. intros. unfold fp_rem. rewrite map_app, zsum_app. unfold zsum at 2; simpl. lia. Qed.

Lemma fp_nz_app : forall pre p, fp_nz (pre ++ [p]) = fp_nz pre + (if p =? 0 then 0 else 1).
Proof.
  intros. unfold fp_nz. rewrite filter_app, Zlength_app. simpl.
  destruct (p =? 0); simpl; rewrite ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma fp_nz_bounds : forall pre, 0 <= fp_nz pre <= Zlength pre.
Proof.
  intros. unfold fp_nz. split; [apply Zlength_nonneg|].
  rewrite !Zlength_correct. apply inj_le. apply filter_length_le.
Qed.

Lemma fp_inv_init : fp_left need 0 maxsym + Z.max 0 (2 - fp_left need 0 maxsym) <= 2 ^ log ->
  fp_inv log maxsym need [].
Proof.
  intros H. pose proof fp_pow_bounds. unfold fp_inv. rewrite Zlength_nil.
  assert (R: fp_rem log [] = 2 ^ log) by (unfold fp_rem, zsum; simpl; lia).
  assert (N: fp_nz [] = 0) by reflexivity.
  rewrite R, N, Z.sub_0_r.
  split; [lia|]. split; [lia|]. split; [exact H|]. split; [intros; lia|]. split; [intros; lia|].
  split; [intros; lia|]. split; [constructor|]. intros; lia.
Qed.

Lemma fp_inv_rem : forall pre, fp_inv log maxsym need pre -> 0 <= fp_rem log pre <= 2 ^ log.
Proof.
  intros pre (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8). split; auto.
  unfold fp_rem. assert (0 <= zsum (map ncount_of pre)); [|lia].
  clear -I7. induction pre; [simpl; lia|]. inv I7. unfold zsum in *; simpl.
  unfold ncount_of at 1. destruct (a =? -1) eqn:E; [|apply Z.eqb_neq in E]; specialize (IHpre H2); lia.
Qed.

(* the facts the body needs from the invariant in an iteration (R > 0) *)
Lemma fp_inv_iter : forall pre, fp_inv log maxsym need pre -> 0 < fp_rem log pre ->
  Zlength pre <= maxsym /\ fp_rem log pre <= 2 ^ log /\
  0 <= fp_left need (Zlength pre + 1) maxsym <= maxsym - Zlength pre /\
  fp_left need (Zlength pre) maxsym = Znth (Zlength pre) need + fp_left need (Zlength pre + 1) maxsym /\
  0 <= fp_nz pre <= Zlength pre.
Proof.
  intros pre (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8) R.
  assert (Hs: Zlength pre <= maxsym) by auto. pose proof (Zlength_nonneg pre).
  split; [auto|]. split.
  - unfold fp_rem. assert (0 <= zsum (map ncount_of pre)); [|lia].
    clear -I7. induction pre; [simpl; lia|]. inv I7. unfold zsum in *; simpl.
    unfold ncount_of at 1. destruct (a =? -1) eqn:E; [|apply Z.eqb_neq in E]; specialize (IHpre H2); lia.
  - split; [pose proof (fp_left_bounds (Zlength pre + 1)); lia|]. split; [apply fp_left_step; lia|].
    apply fp_nz_bounds.
Qed.

Lemma fp_nopt : forall pre, fp_inv log maxsym need pre -> 0 < fp_rem log pre ->
  let s := Zlength pre in let n := fp_nz pre in let L := fp_left need (s + 1) maxsym in
  let R := fp_rem log pre in
  0 < Zlength (fp_opts (fp_c0 maxsym s (Znth s need) n L R) (fp_c1 maxsym s n L R) (fp_c2 maxsym s n L R)).
Proof.
  intros pre HI HR s n L R.
  pose proof (fp_inv_iter pre HI HR) as (Hs & HR2 & HL & Hstep & Hn). fold s n L R in Hs, HR2, HL, Hstep, Hn.
  destruct HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8). fold s n R in I1, I2, I3, I4, I5.
  rewrite Hstep in I3. specialize (I4 Hs).
  assert (Hns: 0 <= Znth s need <= 1) by (apply fp_need_Znth; lia).
  cut (fp_c0 maxsym s (Znth s need) n L R = true \/ fp_c1 maxsym s n L R = true \/ fp_c2 maxsym s n L R = true).
  { intros [E|[E|E]]; unfold fp_opts; rewrite E;
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    simpl; rewrite ?Zlength_cons, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try lia;
    pose proof (Zlength_nonneg (if fp_c2 maxsym s n L R then [2] else [])); lia. }
  unfold fp_c0, fp_c1, fp_c2, fp_rsv.
  destruct (Z.eq_dec s maxsym) as [Elast|Nlast].
  - (* last: L = 0, n >= 1, reserve 0: a positive probability *)
    right; right. subst s. rewrite Elast, Z.eqb_refl. simpl.
    assert (L = 0) by lia. unfold L in *. rewrite H, andb_true_iff, Z.leb_le, Z.eqb_eq. lia.
  - rewrite <- Z.eqb_neq in Nlast. rewrite Nlast. simpl. rewrite Z.eqb_neq in Nlast.
    destruct (Z.eq_dec (Znth s need) 1) as [N1|N0].
    + right; left. rewrite andb_true_r, Z.leb_le. rewrite N1 in I3. lia.
    + assert (Znth s need = 0) as N0' by lia. rewrite N0' in I3. rewrite N0', Z.eqb_refl. simpl.
      destruct (Z_le_gt_dec 2 (n + (maxsym - s))) as [C|C].
      * left. rewrite andb_true_iff, !Z.leb_le. lia.
      * right; left. rewrite andb_true_r, Z.leb_le. lia.
Qed.

Lemma fp_opts_in : forall c0 c1 c2 k, In k (fp_opts c0 c1 c2) ->
  (k = 0 /\ c0 = true) \/ (k = 1 /\ c1 = true) \/ (k = 2 /\ c2 = true).
Proof.
  intros. unfold fp_opts in H. destruct c0, c1, c2; simpl in H; intuition.
Qed.

(* the invariant after appending p, from facts about the new values *)
Lemma fp_inv_snoc : forall pre p, fp_inv log maxsym need pre -> Zlength pre <= maxsym ->
  let s := Zlength pre in let n' := fp_nz pre + (if p =? 0 then 0 else 1) in
  let L := fp_left need (s + 1) maxsym in let R' := fp_rem log pre - ncount_of p in
  0 <= R' -> L + Z.max 0 (2 - n' - L) <= R' ->
  (s + 1 <= maxsym -> 2 <= n' + (maxsym - s)) -> (0 < R' -> s + 1 <= maxsym) -> (R' = 0 -> p <> 0) ->
  -1 <= p <= 2 ^ log -> (Znth s need <> 0 -> p <> 0) ->
  fp_inv log maxsym need (pre ++ [p]).
Proof.
  intros pre p HI Hs s n' L R' A B C D E F G.
  destruct HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
  assert (Hlen': Zlength (pre ++ [p]) = s + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  unfold fp_inv. rewrite Hlen', fp_rem_app, fp_nz_app, last_last. fold n' L R'.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; specialize (C ltac:(lia)); lia|].
  split; [exact D|]. split; [exact E|]. split; [rewrite Forall_app; split; [exact I7|constructor; [exact F|constructor]]|].
  intros i Hi Hni. rewrite !zn_Znth in * by lia. destruct (Z.eq_dec i s) as [->|Ne].
  - rewrite Znth_app2 by lia. fold s. rewrite Z.sub_diag. apply G. exact Hni.
  - rewrite Znth_app1 by lia. specialize (I8 i ltac:(lia)). rewrite !zn_Znth in I8 by lia. auto.
Qed.

(* the step: p drawn for symbol s *)
Lemma fp_step : forall pre p, fp_inv log maxsym need pre -> 0 < fp_rem log pre ->
  let s := Zlength pre in let n := fp_nz pre in let L := fp_left need (s + 1) maxsym in
  let R := fp_rem log pre in
  (p = 0 /\ fp_c0 maxsym s (Znth s need) n L R = true) \/
  (p = -1 /\ fp_c1 maxsym s n L R = true) \/
  (fp_c2 maxsym s n L R = true /\ (s = maxsym -> p = R) /\ (s <> maxsym -> 1 <= p <= R - fp_rsv n L)) ->
  fp_inv log maxsym need (pre ++ [p]).
Proof.
  intros pre p HI HR s n L R Hp.
  pose proof (fp_inv_iter pre HI HR) as (Hs & HR2 & HL & Hstep & Hn). fold s n L R in Hs, HR2, HL, Hstep, Hn.
  pose proof HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8). fold s n R in I1, I2, I3, I4, I5.
  rewrite Hstep in I3. specialize (I4 Hs).
  assert (Hns: 0 <= Znth s need <= 1) by (apply fp_need_Znth; lia).
  pose proof fp_pow_bounds.
  apply fp_inv_snoc; auto; fold s n L R.
  all: unfold fp_c0, fp_c1, fp_c2, fp_rsv in Hp.
  all: destruct Hp as [[-> C]|[[-> C]|[C [P1 P2]]]].
  all: try (rewrite !andb_true_iff, !Z.leb_le, Z.eqb_eq, negb_true_iff, Z.eqb_neq in C;
            destruct C as [[[C1 C2] C3] C4]; unfold ncount_of; simpl; lia).
  all: try (rewrite !andb_true_iff, !Z.leb_le, orb_true_iff, negb_true_iff, Z.eqb_neq, Z.eqb_eq in C;
            destruct C as [C1 C2]; unfold ncount_of; simpl; lia).
  all: rewrite !andb_true_iff, !Z.leb_le, orb_true_iff, negb_true_iff, Z.eqb_neq, Z.eqb_eq in C;
       destruct C as [C1 C2].
  all: assert (Pp: 1 <= p <= R - (L + Z.max 0 (2 - (n + 1 + L))))
         by (destruct (Z.eq_dec s maxsym) as [E|E]; [rewrite (P1 E); destruct C2 as [C2|C2]; lia | apply P2; auto]).
  all: assert (Ep: (p =? 0) = false) by (apply Z.eqb_neq; lia).
  all: assert (Eq: ncount_of p = p)
         by (unfold ncount_of; destruct (p =? -1) eqn:E; [apply Z.eqb_eq in E; lia|auto]).
  all: rewrite ?Ep, ?Eq; try lia.
  all: intros; destruct (Z.eq_dec s maxsym) as [E|E]; [rewrite (P1 E) in *; lia | lia].
Qed.

Lemma fp_step' : forall pre p, fp_inv log maxsym need pre -> 0 < fp_rem log pre ->
  fp_choice log maxsym need pre p -> fp_inv log maxsym need (pre ++ [p]).
Proof. intros. apply fp_step; auto. Qed.

(* the range of a drawn p *)
Lemma fp_choice_range : forall pre p, fp_inv log maxsym need pre -> 0 < fp_rem log pre ->
  fp_choice log maxsym need pre p -> -1 <= p <= fp_rem log pre.
Proof.
  intros pre p HI HR Hp. pose proof (fp_inv_iter pre HI HR) as (Hs & HR2 & HL & Hstep & Hn).
  unfold fp_choice, fp_c0, fp_c1, fp_c2, fp_rsv in Hp.
  pose proof (fp_left_bounds (Zlength pre + 1)).
  destruct Hp as [[-> C]|[[-> C]|[C [P1 P2]]]]; [lia|lia|].
  destruct (Z.eq_dec (Zlength pre) maxsym) as [E|E]; [rewrite (P1 E); lia|].
  specialize (P2 E). lia.
Qed.

(* the end: nothing remains *)
Lemma fp_final : forall pre, fp_inv log maxsym need pre -> fp_rem log pre <= 0 ->
  ndist_ok log pre /\ ndist_need maxsym need pre /\ 2 <= fp_nz pre /\ 1 <= Zlength pre <= 53.
Proof.
  intros pre (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8) R.
  assert (R0: fp_rem log pre = 0) by lia.
  pose proof (Zlength_nonneg pre).
  assert (Hne: pre <> []) by (intro E; subst pre; apply (I6 R0); reflexivity).
  assert (Zlength pre <> 0) by (intro E; apply Zlength_nil_inv in E; auto).
  pose proof (fp_left_bounds (Zlength pre)) as B. specialize (B ltac:(lia)).
  assert (L0: fp_left need (Zlength pre) maxsym = 0) by lia.
  rewrite L0 in I3.
  assert (2 <= fp_nz pre) by lia.
  split; [|split; [|split; [auto|lia]]].
  - unfold ndist_ok. repeat split; try lia; auto.
    unfold fp_rem in R0. lia.
  - split; [lia|]. intros i Hi Hni. destruct (Z_lt_dec i (Zlength pre)) as [Lt|Ge].
    + split; auto. apply I8; auto. lia.
    + exfalso. unfold fp_left in L0.
      assert (Znth i need = 0).
      { assert (Forall (fun x => x = 0) (sublist (Zlength pre) (maxsym + 1) need)).
        { assert (Forall (fun x => 0 <= x <= 1) (sublist (Zlength pre) (maxsym + 1) need))
            by (apply Forall_sublist; auto).
          revert L0 H2. generalize (sublist (Zlength pre) (maxsym + 1) need).
          induction l; intros; [constructor|]. inv H2. unfold zsum in L0; simpl in L0.
          pose proof (zsum_bounds01 l H6). unfold zsum in H2. constructor; [lia|]. apply IHl; auto.
          unfold zsum; lia. }
        rewrite Forall_forall in H2. apply H2.
        replace i with ((i - Zlength pre) + Zlength pre) by lia. rewrite <- Znth_sublist with (hi := maxsym + 1) by lia.
        apply Znth_In. rewrite Zlength_sublist by lia. lia. }
      rewrite zn_Znth in Hni by lia. contradiction.
Qed.

End FP.
