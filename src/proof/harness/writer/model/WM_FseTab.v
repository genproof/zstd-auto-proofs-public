(* Properties of the FSE decoding tables the writer builds (Fse.fse_build of a distribution; plain Coq). *)
Require Import Zstd.proof.harness.writer.model.WModel.

(* ---------------------------------------------------------------------------------------------- *)
(* helpers: list updates as write lists *)
Local Open Scope Z_scope.

Lemma wft_upd_length : forall {A} (l: list A) i x, length (upd l i x) = length l.
Proof. induction l; destruct i; simpl; intros; auto. Qed.

Lemma wft_nth_upd_same : forall {A} (l: list A) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. induction l; destruct i; simpl; intros; try lia; auto. apply IHl; lia. Qed.

Lemma wft_nth_upd_other : forall {A} (l: list A) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof. induction l; destruct i, j; simpl; intros; auto; congruence. Qed.

Lemma wft_nth_upd_cases : forall (l: list Z) k j y,
  nth j (upd l k y) 0 = nth j l 0 \/ (j = k /\ nth j (upd l k y) 0 = y).
Proof.
  intros. destruct (Nat.eq_dec j k).
  - subst. destruct (Nat.lt_ge_cases k (length l)).
    + right. split; auto. apply wft_nth_upd_same; auto.
    + left. rewrite !nth_overflow; auto. rewrite wft_upd_length; auto.
  - left. apply wft_nth_upd_other; auto.
Qed.

Definition wft_pn (pv: Z * Z) : nat := Z.to_nat (fst pv).

Definition apw (tab: list Z) (ws: list (Z * Z)) : list Z :=
  fold_left (fun t pv => upd t (wft_pn pv) (snd pv)) ws tab.
Arguments apw : simpl never.

Lemma apw_length : forall ws tab, length (apw tab ws) = length tab.
Proof. induction ws; intros; auto. unfold apw in *. simpl. rewrite IHws, wft_upd_length; auto. Qed.

Lemma apw_app : forall a b tab, apw tab (a ++ b) = apw (apw tab a) b.
Proof. intros. unfold apw. apply fold_left_app. Qed.

Lemma apw_cons : forall a ws tab, apw tab (a :: ws) = apw (upd tab (wft_pn a) (snd a)) ws.
Proof. reflexivity. Qed.

Lemma apw_notin : forall ws tab q d, ~ In q (map wft_pn ws) -> nth q (apw tab ws) d = nth q tab d.
Proof.
  induction ws; simpl; intros; auto. rewrite apw_cons, IHws by tauto.
  apply wft_nth_upd_other. tauto.
Qed.

Lemma apw_in : forall ws tab p v d, NoDup (map wft_pn ws) -> In (p, v) ws ->
  (Z.to_nat p < length tab)%nat -> nth (Z.to_nat p) (apw tab ws) d = v.
Proof.
  induction ws; simpl; intros; [contradiction|]. inversion H; subst. rewrite apw_cons.
  destruct H0 as [H0 | H0].
  - subst a. unfold wft_pn in *; simpl in *. rewrite apw_notin by exact H4.
    apply wft_nth_upd_same; auto.
  - apply IHws; auto. rewrite wft_upd_length; auto.
Qed.

Lemma apw_some : forall ws tab q d, In q (map wft_pn ws) -> (q < length tab)%nat ->
  In (nth q (apw tab ws) d) (map snd ws).
Proof.
  induction ws; simpl; intros; [contradiction|]. rewrite apw_cons.
  destruct (in_dec Nat.eq_dec q (map wft_pn ws)).
  - right. apply IHws; auto. rewrite wft_upd_length; auto.
  - left. destruct H; [|contradiction]. subst. rewrite apw_notin by auto.
    rewrite wft_nth_upd_same; auto.
Qed.

Lemma wft_combine_app_r : forall {A B} (R: list A) (x y: list B), (length x <= length R)%nat ->
  combine R (x ++ y) = combine R x ++ combine (skipn (length x) R) y.
Proof.
  intros A B R x. revert R. induction x; simpl; intros.
  - destruct R; auto.
  - destruct R; simpl in *; [lia|]. rewrite IHx by lia. auto.
Qed.

Lemma wft_map_fst_combine : forall {A B} (a: list A) (b: list B), length a = length b ->
  map fst (combine a b) = a.
Proof. induction a; destruct b; simpl; intros; try discriminate; auto. rewrite IHa; auto. Qed.

Lemma wft_map_snd_combine : forall {A B} (a: list A) (b: list B), length a = length b ->
  map snd (combine a b) = b.
Proof. induction a; destruct b; simpl; intros; try discriminate; auto. rewrite IHa; auto. Qed.

Lemma wft_in_combine_r : forall {A B} (a: list A) (b: list B) y, length a = length b -> In y b ->
  exists x, In (x, y) (combine a b).
Proof.
  induction a; destruct b; simpl; intros; try discriminate; try contradiction.
  destruct H0 as [<-|H0]; eauto. destruct (IHa b0 y) as [x Hx]; auto. eauto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the orbit of the spread: positions j * step mod 2^log *)
Definition wft_stp (log: Z) : Z := Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3.
Definition wft_gp (log: Z) (j: nat) : Z := (Z.of_nat j * wft_stp log) mod 2 ^ log.
Definition wft_LL (log high: Z) (j: nat) : list Z :=
  filter (fun p => p <=? high) (map (wft_gp log) (seq j (Z.to_nat (2 ^ log) - j))).

Lemma wft_gp_S : forall log j, 0 <= log ->
  Z.land (wft_gp log j + (Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3)) (2 ^ log - 1) = wft_gp log (S j).
Proof.
  intros. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by auto. unfold wft_gp. fold (wft_stp log).
  rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia). f_equal. lia.
Qed.

Lemma wft_gp_range : forall log j, 0 <= log -> 0 <= wft_gp log j < 2 ^ log.
Proof. intros. unfold wft_gp. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma wft_LL_cons : forall log high j, (j < Z.to_nat (2 ^ log))%nat ->
  wft_LL log high j = if wft_gp log j <=? high then wft_gp log j :: wft_LL log high (S j)
                      else wft_LL log high (S j).
Proof.
  intros. unfold wft_LL. replace (Z.to_nat (2 ^ log) - j)%nat with (S (Z.to_nat (2 ^ log) - S j)) by lia.
  reflexivity.
Qed.

Lemma wft_LL_N : forall log high, wft_LL log high (Z.to_nat (2 ^ log)) = nil.
Proof. intros. unfold wft_LL. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma wft_skip_ok : forall log high fuel j, 0 <= log -> (j <= Z.to_nat (2 ^ log))%nat ->
  (Z.to_nat (2 ^ log) - j <= fuel)%nat ->
  exists j', (j <= j' <= Z.to_nat (2 ^ log))%nat /\ wft_LL log high j' = wft_LL log high j /\
   (wft_LL log high j <> nil -> skip_high log fuel high (wft_gp log j) = wft_gp log j' /\ wft_gp log j' <= high).
Proof.
  intros log high fuel. induction fuel; intros j Hl Hj Hf.
  - assert (j = Z.to_nat (2 ^ log)) by lia. subst. exists (Z.to_nat (2 ^ log)).
    rewrite wft_LL_N. split; [lia|]. split; auto. tauto.
  - destruct (Nat.eq_dec j (Z.to_nat (2 ^ log))).
    + subst. exists (Z.to_nat (2 ^ log)). rewrite wft_LL_N. split; [lia|]. split; auto. tauto.
    + simpl skip_high. rewrite (wft_LL_cons log high j) by lia.
      destruct (wft_gp log j >? high) eqn:E.
      * rewrite wft_gp_S by auto.
        assert (wft_gp log j <=? high = false) as E' by lia. rewrite E'.
        destruct (IHfuel (S j)) as [j' [Hj' [HL HS]]]; try lia.
        exists j'. split; [lia|]. auto.
      * assert (wft_gp log j <=? high = true) as E' by lia. rewrite E'.
        exists j. split; [lia|]. rewrite (wft_LL_cons log high j) by lia. rewrite E'.
        split; auto. intros _. split; auto. lia.
Qed.

Definition wft_inv (log high: Z) (R: list Z) (pos: Z) : Prop :=
  exists j, (j <= Z.to_nat (2 ^ log))%nat /\ R = wft_LL log high j /\
    (R <> nil -> pos = wft_gp log j /\ wft_gp log j <= high).

Lemma wft_spread_one_ok : forall log high k s tab pos R, 0 <= log -> wft_inv log high R pos ->
  (k <= length R)%nat ->
  exists pos', spread_one log k s high tab pos = (apw tab (combine R (repeat s k)), pos') /\
    wft_inv log high (skipn k R) pos'.
Proof.
  intros log high k. induction k; intros s tab pos R Hl HI Hk.
  - exists pos. simpl. rewrite combine_nil. auto.
  - destruct HI as [j [Hj [HR HP]]].
    assert (R <> nil) as Hn by (intro E; rewrite E in Hk; simpl in Hk; lia).
    destruct (HP Hn) as [Hpos Hle]. clear HP.
    assert (j < Z.to_nat (2 ^ log))%nat as Hj'.
    { destruct (Nat.eq_dec j (Z.to_nat (2 ^ log))); [|lia]. subst. rewrite wft_LL_N in Hn. congruence. }
    rewrite wft_LL_cons in HR by auto. assert (wft_gp log j <=? high = true) as E by lia.
    rewrite E in HR. subst R. simpl spread_one. rewrite Hpos, wft_gp_S by auto.
    destruct (wft_skip_ok log high (Z.to_nat (2 ^ log)) (S j)) as [j' [Hj1 [HL HS]]]; auto; try lia.
    destruct (IHk s (upd tab (Z.to_nat (wft_gp log j)) s)
                (skip_high log (Z.to_nat (2 ^ log)) high (wft_gp log (S j))) (wft_LL log high (S j)))
      as [pos' [H1 H2]].
    { auto. }
    { exists j'. split; [lia|]. split; auto. }
    { simpl in Hk. lia. }
    exists pos'. rewrite H1. split; auto.
Qed.

(* the symbols spread, in order *)
Fixpoint wft_syms (norm: list Z) (s n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => (let c := nth s norm 0 in if c >? 0 then repeat (Z.of_nat s) (Z.to_nat c) else nil)
              ++ wft_syms norm (S s) n'
  end.

Lemma wft_spread_ok : forall norm log high n s tab pos R, 0 <= log -> wft_inv log high R pos ->
  (length (wft_syms norm s n) <= length R)%nat ->
  spread norm log s n high tab pos = apw tab (combine R (wft_syms norm s n)).
Proof.
  intros norm log high n. induction n; intros s tab pos R Hl HI Hk.
  - simpl. rewrite combine_nil. auto.
  - simpl spread. simpl wft_syms in *. destruct (nth s norm 0 >? 0) eqn:E.
    + rewrite app_length, repeat_length in Hk.
      destruct (wft_spread_one_ok log high (Z.to_nat (nth s norm 0)) (Z.of_nat s) tab pos R)
        as [pos' [H1 H2]]; auto; try lia.
      rewrite H1. rewrite wft_combine_app_r by (rewrite repeat_length; lia).
      rewrite apw_app, repeat_length. apply IHn; auto. rewrite skipn_length. lia.
    + simpl. apply IHn; auto.
Qed.


Lemma wft_syms_in : forall norm n s v, In v (wft_syms norm s n) ->
  exists i, (s <= i < s + n)%nat /\ v = Z.of_nat i /\ nth i norm 0 > 0.
Proof.
  induction n; simpl; intros; [contradiction|]. apply in_app_or in H. destruct H.
  - destruct (nth s norm 0 >? 0) eqn:E; [|contradiction]. apply repeat_spec in H.
    exists s. split; [lia|]. split; auto. lia.
  - destruct (IHn (S s) v H) as [i [Hi [Hv Hc]]]. exists i. split; [lia|]. auto.
Qed.

Lemma wft_syms_has : forall norm n s i, (s <= i < s + n)%nat -> nth i norm 0 > 0 ->
  In (Z.of_nat i) (wft_syms norm s n).
Proof.
  induction n; simpl; intros; [lia|]. apply in_or_app.
  destruct (Nat.eq_dec i s).
  - subst. left. assert (nth s norm 0 >? 0 = true) as E by lia. rewrite E.
    destruct (Z.to_nat (nth s norm 0)) eqn:En; [lia|]. simpl. auto.
  - right. apply IHn; auto. lia.
Qed.

(* the writes of place_low *)
Fixpoint wft_lw (norm: list Z) (s n: nat) (high: Z) : list (Z * Z) :=
  match n with
  | O => nil
  | S n' => if nth s norm 0 =? -1 then (high, Z.of_nat s) :: wft_lw norm (S s) n' (high - 1)
            else wft_lw norm (S s) n' high
  end.

Lemma wft_place_low_ok : forall norm n s tab high,
  place_low norm s n tab high = (apw tab (wft_lw norm s n high), high - Z.of_nat (length (wft_lw norm s n high))).
Proof.
  induction n; simpl; intros.
  - f_equal. lia.
  - destruct (nth s norm 0 =? -1).
    + rewrite IHn. rewrite apw_cons. simpl length. f_equal. lia.
    + apply IHn.
Qed.

Lemma wft_lw_in : forall norm n s h p v, In (p, v) (wft_lw norm s n h) ->
  h - Z.of_nat (length (wft_lw norm s n h)) < p <= h /\
  exists i, (s <= i < s + n)%nat /\ v = Z.of_nat i /\ nth i norm 0 = -1.
Proof.
  induction n; simpl; intros; [contradiction|]. destruct (nth s norm 0 =? -1) eqn:E.
  - destruct H as [H|H].
    + inversion H; subst. split; [simpl length; lia|]. exists s. split; [lia|]. split; auto. lia.
    + destruct (IHn _ _ _ _ H) as [H1 [i [Hi Hv]]]. simpl length. split; [lia|].
      exists i. split; [lia|]. auto.
  - destruct (IHn _ _ _ _ H) as [H1 [i [Hi Hv]]]. split; [lia|]. exists i. split; [lia|]. auto.
Qed.

Lemma wft_lw_cover : forall norm n s h q, h - Z.of_nat (length (wft_lw norm s n h)) < q <= h ->
  In q (map fst (wft_lw norm s n h)).
Proof.
  induction n; simpl; intros; [lia|]. destruct (nth s norm 0 =? -1) eqn:E.
  - simpl in *. destruct (Z.eq_dec q h); [auto|]. right. apply IHn. lia.
  - apply IHn; auto.
Qed.

Lemma wft_lw_has : forall norm n s h i, (s <= i < s + n)%nat -> nth i norm 0 = -1 ->
  exists p, In (p, Z.of_nat i) (wft_lw norm s n h).
Proof.
  induction n; simpl; intros; [lia|]. destruct (Nat.eq_dec i s).
  - subst. rewrite H0, Z.eqb_refl. eauto with datatypes.
  - destruct (nth s norm 0 =? -1).
    + destruct (IHn (S s) (h - 1) i) as [p Hp]; auto; try lia. exists p. right; auto.
    + apply IHn; auto. lia.
Qed.

Lemma wft_lw_nodup : forall norm n s h, 0 <= h + 1 - Z.of_nat (length (wft_lw norm s n h)) ->
  NoDup (map wft_pn (wft_lw norm s n h)).
Proof.
  induction n; simpl; intros; [constructor|]. destruct (nth s norm 0 =? -1) eqn:E.
  - simpl in *. constructor; [|apply IHn; lia].
    intro HI. apply in_map_iff in HI. destruct HI as [[p v] [Hp HI]]. unfold wft_pn in Hp; simpl in Hp.
    apply wft_lw_in in HI. lia.
  - apply IHn; auto.
Qed.

Lemma wft_skipn_nth : forall (l: list Z) s, (s < length l)%nat -> skipn s l = nth s l 0 :: skipn (S s) l.
Proof. induction l; destruct s; simpl; intros; try lia; auto. apply IHl. lia. Qed.

Lemma wft_count : forall norm n s h, (s + n = length norm)%nat -> Forall (fun p => -1 <= p) norm ->
  Z.of_nat (length (wft_lw norm s n h)) + Z.of_nat (length (wft_syms norm s n)) =
  zsum (map ncount_of (skipn s norm)).
Proof.
  induction n; simpl; intros.
  - rewrite skipn_all2 by lia. reflexivity.
  - rewrite (wft_skipn_nth norm s) by lia. rewrite map_cons.
    assert (forall a l, zsum (a :: l) = a + zsum l) as ZC by reflexivity. rewrite ZC.
    assert (-1 <= nth s norm 0) as Hc.
    { rewrite Forall_forall in H0. apply H0. apply nth_In. lia. }
    rewrite app_length. unfold ncount_of at 1.
    destruct (nth s norm 0 =? -1) eqn:E1; destruct (nth s norm 0 >? 0) eqn:E2; try lia.
    + cbn [length]. rewrite <- (IHn (S s) (h - 1)) by (auto; lia). lia.
    + rewrite repeat_length. rewrite <- (IHn (S s) h) by (auto; lia). lia.
    + cbn [length]. rewrite <- (IHn (S s) h) by (auto; lia). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the orbit facts, computed for each accuracy log 5..9 *)
Fixpoint wft_nodupb (l: list Z) : bool :=
  match l with nil => true | x :: l' => negb (existsb (Z.eqb x) l') && wft_nodupb l' end.

Lemma wft_nodupb_ok : forall l, wft_nodupb l = true -> NoDup l.
Proof.
  induction l; simpl; intros; constructor.
  - apply andb_prop in H. destruct H as [H _]. intro HI. apply Bool.negb_true_iff in H.
    assert (existsb (Z.eqb a) l = true) by (apply existsb_exists; exists a; split; auto; apply Z.eqb_refl).
    congruence.
  - apply andb_prop in H. tauto.
Qed.

Definition wft_check (log: Z) : bool :=
  let l := map (wft_gp log) (seq 0 (Z.to_nat (2 ^ log))) in
  wft_nodupb l &&
  forallb (fun p => existsb (Z.eqb p) l) (map Z.of_nat (seq 0 (Z.to_nat (2 ^ log)))) &&
  forallb (fun h => Nat.eqb (length (filter (fun p => p <=? h) l)) (Z.to_nat (h + 1)))
    (map (fun i => Z.of_nat i - 1) (seq 0 (S (Z.to_nat (2 ^ log))))).

Lemma wft_check_ok : forall log, 5 <= log <= 9 -> wft_check log = true.
Proof.
  intros. assert (log = 5 \/ log = 6 \/ log = 7 \/ log = 8 \/ log = 9) as HL by lia.
  destruct HL as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; vm_compute; reflexivity.
Qed.

Lemma wft_orbit : forall log, 5 <= log <= 9 ->
  NoDup (map (wft_gp log) (seq 0 (Z.to_nat (2 ^ log)))) /\
  (forall p, 0 <= p < 2 ^ log -> In p (map (wft_gp log) (seq 0 (Z.to_nat (2 ^ log))))) /\
  (forall h, -1 <= h <= 2 ^ log - 1 -> length (wft_LL log h 0) = Z.to_nat (h + 1)).
Proof.
  intros log Hl. pose proof (wft_check_ok log Hl) as C. unfold wft_check in C.
  apply andb_prop in C. destruct C as [C C3]. apply andb_prop in C. destruct C as [C1 C2].
  split; [apply wft_nodupb_ok; auto|]. split.
  - intros p Hp. rewrite forallb_forall in C2.
    specialize (C2 p). rewrite existsb_exists in C2. destruct C2 as [x [Hx Ex]].
    + apply in_map_iff. exists (Z.to_nat p). split; [lia|]. apply in_seq. lia.
    + apply Z.eqb_eq in Ex. subst. auto.
  - intros h Hh. rewrite forallb_forall in C3. specialize (C3 h). apply Nat.eqb_eq in C3.
    + unfold wft_LL. rewrite Nat.sub_0_r. auto.
    + apply in_map_iff. exists (Z.to_nat (h + 1)). split; [lia|]. apply in_seq. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the states *)
Lemma wft_states_length : forall log tab next, length (states log tab next) = length tab.
Proof. induction tab; simpl; intros; auto. Qed.

Lemma wft_states_nth : forall log tab next i d, (i < length tab)%nat ->
  exists x, nth (Z.to_nat (nth i tab 0)) next 0 <= x <= nth (Z.to_nat (nth i tab 0)) next 0 + Z.of_nat i /\
    nth i (states log tab next) d =
      {| fe_sym := nth i tab 0; fe_nb := log - highbit x; fe_base := Z.shiftl x (log - highbit x) - 2 ^ log |}.
Proof.
  induction tab; simpl; intros; [lia|]. destruct i.
  - eexists. split; [|reflexivity]. lia.
  - destruct (IHtab (upd next (Z.to_nat a) (nth (Z.to_nat a) next 0 + 1)) i d) as [x [Hx Hc]]; [lia|].
    exists x. split; auto.
    destruct (wft_nth_upd_cases next (Z.to_nat a) (Z.to_nat (nth i tab 0)) (nth (Z.to_nat a) next 0 + 1))
      as [E|[E1 E2]].
    + rewrite E in Hx. lia.
    + rewrite E2 in Hx. rewrite E1. lia.
Qed.

Lemma wft_cell_bounds : forall log x, 0 <= log -> 1 <= x < 2 ^ (log + 1) ->
  0 <= log - highbit x <= log /\ 0 <= Z.shiftl x (log - highbit x) - 2 ^ log /\
  Z.shiftl x (log - highbit x) - 2 ^ log + 2 ^ (log - highbit x) <= 2 ^ log.
Proof.
  intros log x Hl Hx. unfold highbit.
  pose proof (Z.log2_spec x ltac:(lia)) as Hs. pose proof (Z.log2_nonneg x) as Hn.
  assert (Z.log2 x < log + 1) by (apply Z.log2_lt_pow2; lia).
  set (h := Z.log2 x) in *.
  assert (2 ^ h * 2 ^ (log - h) = 2 ^ log) as P1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (2 ^ Z.succ h = 2 * 2 ^ h) as P2 by (rewrite Z.pow_succ_r by lia; lia).
  rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (log - h) ltac:(lia) ltac:(lia)).
  split; [lia|]. split; nia.
Qed.

Lemma wft_map_nth0 : forall (f: Z -> Z) l k, f 0 = 0 -> nth k (map f l) 0 = f (nth k l 0).
Proof. intros. induction l in k |- *; destruct k; simpl; auto. Qed.

Lemma wft_nodup_to_nat : forall l, NoDup l -> Forall (fun p => 0 <= p) l -> NoDup (map Z.to_nat l).
Proof.
  induction l as [|a l IH]; simpl; intros Hd Hf; constructor.
  - apply NoDup_cons_iff in Hd. destruct Hd as [Hn _]. pose proof (Forall_inv Hf) as Ha.
    pose proof (Forall_inv_tail Hf) as Hl. rewrite Forall_forall in Hl.
    intro HI. apply in_map_iff in HI. destruct HI as [y [Hy HI]].
    specialize (Hl y HI). simpl in Ha. assert (y = a) by lia. subst. contradiction.
  - apply IH; [apply NoDup_cons_iff in Hd; tauto | exact (Forall_inv_tail Hf)].
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* fse_build as the states of one write list W over the zero table *)
Definition wft_next0 (norm: list Z) : list Z := map (fun c => if c =? -1 then 1 else c) norm.

Lemma wft_build_eq : forall norm log, ndist_base log norm ->
  exists W,
    ft_cells (fse_build norm log) = states log (apw (repeat 0 (Z.to_nat (2 ^ log))) W) (wft_next0 norm) /\
    NoDup (map wft_pn W) /\
    (forall p v, In (p, v) W -> 0 <= p < 2 ^ log /\
       exists i, (i < length norm)%nat /\ v = Z.of_nat i /\ nth i norm 0 <> 0) /\
    (forall q, (q < Z.to_nat (2 ^ log))%nat -> In q (map wft_pn W)) /\
    (forall i, (i < length norm)%nat -> nth i norm 0 <> 0 -> exists p, In (p, Z.of_nat i) W).
Proof.
  intros norm log [Hlog [Hlen [Hf Hsum]]].
  assert (Hf1 : Forall (fun p => -1 <= p) norm) by (eapply Forall_impl; [|exact Hf]; simpl; intros; lia).
  pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) ltac:(lia)) as Hpos.
  destruct (wft_orbit log Hlog) as [O1 [O2 O3]].
  unfold fse_build. rewrite wft_place_low_ok. cbv beta iota zeta.
  set (LW := wft_lw norm 0 (length norm) (2 ^ log - 1)).
  set (high := 2 ^ log - 1 - Z.of_nat (length LW)).
  set (S := wft_syms norm 0 (length norm)).
  set (L0 := wft_LL log high 0).
  pose proof (wft_count norm (length norm) 0 (2 ^ log - 1) eq_refl Hf1) as HC.
  fold LW S in HC. simpl skipn in HC. rewrite Hsum in HC.
  assert (Hh : -1 <= high <= 2 ^ log - 1) by lia.
  assert (HL0 : length L0 = length S) by (unfold L0; rewrite O3 by lia; lia).
  assert (HI : wft_inv log high L0 0).
  { exists O%nat. split; [lia|]. split; auto. intros Hn.
    assert (wft_gp log 0 = 0) as G by (unfold wft_gp; simpl; apply Z.mod_0_l; lia).
    rewrite G. split; auto. destruct L0; [congruence|]. simpl in HL0. lia. }
  rewrite (wft_spread_ok norm log high (length norm) 0 _ 0 L0) by (try fold S; auto; lia).
  rewrite <- apw_app.
  (* facts on L0 *)
  assert (HL0r : forall p, In p L0 -> 0 <= p <= high /\ 0 <= p < 2 ^ log).
  { intros p Hp. unfold L0, wft_LL in Hp. apply filter_In in Hp. destruct Hp as [Hp Hle].
    apply in_map_iff in Hp. destruct Hp as [j [<- _]]. pose proof (wft_gp_range log j). lia. }
  assert (HLW : forall p v, In (p, v) LW -> high < p <= 2 ^ log - 1 /\
            exists i, (0 <= i < 0 + length norm)%nat /\ v = Z.of_nat i /\ nth i norm 0 = -1).
  { intros p v Hp. apply wft_lw_in in Hp. fold LW in Hp. unfold high. destruct Hp as [H1 H2]. split; [lia|exact H2]. }
  assert (HpnC : map wft_pn (combine L0 S) = map Z.to_nat L0).
  { unfold wft_pn. rewrite <- (map_map fst Z.to_nat). rewrite wft_map_fst_combine; auto. }
  exists (LW ++ combine L0 S). split; [reflexivity|]. split; [|split; [|split]].
  - rewrite map_app, HpnC. apply NoDup_app.
    + apply wft_lw_nodup. fold LW. lia.
    + apply wft_nodup_to_nat.
      * unfold L0, wft_LL. apply NoDup_filter. rewrite Nat.sub_0_r. auto.
      * rewrite Forall_forall. intros p Hp. apply HL0r in Hp. lia.
    + intros a Ha Hb. apply in_map_iff in Ha. destruct Ha as [[p v] [Ha Hp]]. unfold wft_pn in Ha; simpl in Ha.
      apply in_map_iff in Hb. destruct Hb as [p' [Hb Hp']]. apply HL0r in Hp'. apply HLW in Hp. lia.
  - intros p v Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp].
    + apply HLW in Hp. destruct Hp as [H1 [i [Hi [Hv Hn]]]]. split; [lia|]. exists i. split; [lia|]. split; auto. lia.
    + pose proof (in_combine_l _ _ _ _ Hp) as H1. pose proof (in_combine_r _ _ _ _ Hp) as H2.
      apply HL0r in H1. apply wft_syms_in in H2. destruct H2 as [i [Hi [Hv Hn]]].
      split; [lia|]. exists i. split; [lia|]. split; auto. lia.
  - intros q Hq. rewrite map_app, HpnC. apply in_or_app.
    destruct (Z_le_gt_dec (Z.of_nat q) high).
    + right. apply in_map_iff. exists (Z.of_nat q). split; [lia|].
      unfold L0, wft_LL. apply filter_In. split; [|lia]. rewrite Nat.sub_0_r. apply O2. lia.
    + left. pose proof (wft_lw_cover norm (length norm) 0 (2 ^ log - 1) (Z.of_nat q)) as Hc. fold LW in Hc.
      assert (In (Z.of_nat q) (map fst LW)) as Hc' by (apply Hc; unfold high in *; lia).
      apply in_map_iff in Hc'. destruct Hc' as [[p v] [Hp Hin]]. simpl in Hp.
      apply in_map_iff. exists (p, v). split; auto. unfold wft_pn. simpl. lia.
  - intros i Hi Hn. assert (-1 <= nth i norm 0) as Hc.
    { rewrite Forall_forall in Hf1. apply Hf1. apply nth_In. auto. }
    destruct (Z.eq_dec (nth i norm 0) (-1)) as [E|E].
    + destruct (wft_lw_has norm (length norm) 0 (2 ^ log - 1) i) as [p Hp]; auto; try lia.
      exists p. apply in_or_app. left. exact Hp.
    + assert (In (Z.of_nat i) S) as HS by (apply wft_syms_has; lia).
      destruct (wft_in_combine_r L0 S (Z.of_nat i) HL0 HS) as [p Hp].
      exists p. apply in_or_app. right. exact Hp.
Qed.

(* the cells: 2^log of them; each one's symbol has a non-zero count; nb <= log; [base, base + 2^nb)
   is within the table *)
Theorem fse_build_cells : forall norm log,
  ndist_base log norm ->
  ft_log (fse_build norm log) = log /\
  Z.of_nat (length (ft_cells (fse_build norm log))) = 2 ^ log /\
  forall i, 0 <= i < 2 ^ log ->
    let e := fse_cell (fse_build norm log) i in
    0 <= fe_sym e < Zlength norm /\ zn norm (fe_sym e) <> 0 /\
    0 <= fe_nb e <= log /\ 0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ log.
Proof.
  intros norm log Hnd. pose proof Hnd as [Hlog [Hlen [Hf Hsum]]].
  destruct (wft_build_eq norm log Hnd) as [W [HE [HN [HW [HC HH]]]]].
  pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) ltac:(lia)) as Hpos.
  split; [unfold fse_build; destruct (place_low _ _ _ _ _); reflexivity|].
  split; [rewrite HE, wft_states_length, apw_length, repeat_length; lia|].
  intros i Hi. cbv zeta. unfold fse_cell. rewrite HE.
  set (T := apw (repeat 0 (Z.to_nat (2 ^ log))) W).
  assert (HT : length T = Z.to_nat (2 ^ log)) by (unfold T; rewrite apw_length, repeat_length; auto).
  destruct (wft_states_nth log T (wft_next0 norm) (Z.to_nat i) {| fe_sym := 0; fe_nb := 0; fe_base := 0 |})
    as [x [Hx Hc]]; [lia|].
  rewrite Hc. cbn [fe_sym fe_nb fe_base].
  assert (Hs : In (nth (Z.to_nat i) T 0) (map snd W)) by (apply apw_some; [apply HC; lia | rewrite repeat_length; lia]).
  apply in_map_iff in Hs. destruct Hs as [[p v] [Hv Hin]]. simpl in Hv.
  destruct (HW p v Hin) as [_ [i0 [Hi0 [Hv0 Hn0]]]]. rewrite <- Hv in *. rewrite Hv0 in *.
  rewrite Nat2Z.id in Hx. unfold wft_next0 in Hx. rewrite wft_map_nth0 in Hx by reflexivity.
  assert (Hb : -1 <= nth i0 norm 0 <= 2 ^ log).
  { rewrite Forall_forall in Hf. apply Hf. apply nth_In. auto. }
  assert (H2 : 2 ^ (log + 1) = 2 * 2 ^ log) by (rewrite Z.pow_add_r by lia; lia).
  assert (Hx1 : 1 <= x < 2 ^ (log + 1)) by (destruct (nth i0 norm 0 =? -1) eqn:E; lia).
  destruct (wft_cell_bounds log x ltac:(lia) Hx1) as [B1 [B2 B3]].
  split; [rewrite Zlength_correct; lia|]. split; [unfold zn; rewrite Nat2Z.id; auto|]. auto.
Qed.

(* every symbol with a non-zero count has a state *)
Theorem fse_build_has : forall norm log s,
  ndist_base log norm -> 0 <= s < Zlength norm -> zn norm s <> 0 ->
  exists i, 0 <= i < 2 ^ log /\ fe_sym (fse_cell (fse_build norm log) i) = s.
Proof.
  intros norm log s Hnd Hs Hz. pose proof Hnd as [Hlog [Hlen [Hf Hsum]]].
  destruct (wft_build_eq norm log Hnd) as [W [HE [HN [HW [HC HH]]]]].
  rewrite Zlength_correct in Hs. unfold zn in Hz.
  destruct (HH (Z.to_nat s)) as [p Hp]; [lia|auto|].
  destruct (HW p _ Hp) as [Hpr _].
  exists p. split; auto. unfold fse_cell. rewrite HE.
  set (T := apw (repeat 0 (Z.to_nat (2 ^ log))) W).
  assert (HT : length T = Z.to_nat (2 ^ log)) by (unfold T; rewrite apw_length, repeat_length; auto).
  destruct (wft_states_nth log T (wft_next0 norm) (Z.to_nat p) {| fe_sym := 0; fe_nb := 0; fe_base := 0 |})
    as [x [Hx Hc]]; [lia|].
  rewrite Hc. cbn [fe_sym]. unfold T. rewrite (apw_in W _ p (Z.of_nat (Z.to_nat s))); auto; [lia|].
  rewrite repeat_length. lia.
Qed.

(* fse_has_state (with s >= 0: for s < 0, zn would read element 0) *)
Lemma wft_has_state_nn : forall F s, 0 <= s ->
  wf_ok F -> fse_has_b F s = true ->
  exists i, 0 <= i < 2 ^ wf_log F /\ fe_sym (fse_cell (wf_table F) i) = s.
Proof.
  intros F s Hs0 Hok Hb. unfold wf_ok, fse_has_b, wf_table in *.
  destruct (wf_log F =? 0) eqn:E.
  - apply Z.eqb_eq in E. apply Z.eqb_eq in Hb. rewrite E. exists 0. split; [simpl; lia|].
    unfold fse_cell, fse_rle. simpl. lia.
  - destruct Hok as [Hnd Hn]. apply andb_prop in Hb. destruct Hb as [H1 H2].
    apply Z.ltb_lt in H1. apply Bool.negb_true_iff, Z.eqb_neq in H2.
    apply fse_build_has; auto. lia.
Qed.

(* the same for any table of the writer (fse_has) *)
Theorem fse_has_state : forall F s,
  wf_ok F -> 0 <= s -> fse_has_b F s = true ->
  exists i, 0 <= i < 2 ^ wf_log F /\ fe_sym (fse_cell (wf_table F) i) = s.
Proof.
  intros F s Hok Hs Hb. exact (wft_has_state_nn F s Hs Hok Hb).
Qed.

Theorem pre_wfse_ok : forall ty, 0 <= ty <= 2 -> wf_ok (pre_wfse ty).
Proof.
  intros ty Hty. assert (ty = 0 \/ ty = 1 \/ ty = 2) as E by lia.
  destruct E as [ -> | [ -> | -> ] ]; unfold wf_ok, pre_wfse; simpl;
    (split; [|vm_compute; reflexivity]);
    (split; [lia|]); (split; [vm_compute; split; discriminate|]);
    (split; [|vm_compute; reflexivity]);
    (apply Forall_forall; intros x Hx; repeat (destruct Hx as [<- | Hx]; [vm_compute; split; discriminate|]);
     contradiction).
Qed.

(* every lemma above together (fse_build_cells, fse_build_has, fse_has_state, pre_wfse_ok) *)
Theorem wm_fsetab_all :
  (forall norm log, ndist_base log norm -> ft_log (fse_build norm log) = log /\ Z.of_nat (length (ft_cells (fse_build norm log))) = 2 ^ log /\ forall i, 0 <= i < 2 ^ log -> let e := fse_cell (fse_build norm log) i in 0 <= fe_sym e < Zlength norm /\ zn norm (fe_sym e) <> 0 /\ 0 <= fe_nb e <= log /\ 0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ log) /\
  (forall norm log s, ndist_base log norm -> 0 <= s < Zlength norm -> zn norm s <> 0 -> exists i, 0 <= i < 2 ^ log /\ fe_sym (fse_cell (fse_build norm log) i) = s) /\
  (forall F s, wf_ok F -> 0 <= s -> fse_has_b F s = true -> exists i, 0 <= i < 2 ^ wf_log F /\ fe_sym (fse_cell (wf_table F) i) = s) /\
  (forall ty, 0 <= ty <= 2 -> wf_ok (pre_wfse ty)).
Proof.
  exact (conj fse_build_cells (conj fse_build_has (conj fse_has_state pre_wfse_ok))).
Qed.
