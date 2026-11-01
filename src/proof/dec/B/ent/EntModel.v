(* Group ENT of subtree B: model-side definitions shaped like the C, and the model
   lemmas the bodies use.  Plain Coq over the model (src/proof/model). *)
Require Export Zstd.proof.dec.B.BIface.
Require Export Zstd.proof.model.EntC.

(* ---------- FSE decoding tables (Fse.fse_build) ---------- *)

(* FSE_buildDTable_internal's / ZSTD_buildFSETable_body's fastMode: 0 iff some count >= 2^(log-1) *)
Definition fse_fm (norm: list Z) (log: Z) : Z :=
  if existsb (fun c => 2 ^ (log - 1) <=? c) norm then 0 else 1.

Definition fse_step (log: Z) : Z := Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3.

(* the symbol table of fse_build before the states (low-probability symbols, then the spread) *)
Definition fse_symtab (norm: list Z) (log: Z) : list Z :=
  let '(tab, high) := place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1) in
  spread norm log 0 (length norm) high tab 0.

(* the slow spread of the C (no -1 symbols needed), keeping the final position (FSE_buildDTable_internal
   returns ERROR(GENERIC) unless it is 0) *)
Fixpoint spread_pos (norm: list Z) (log: Z) (s: nat) (n: nat) (high: Z) (tab: list Z) (pos: Z) : list Z * Z :=
  match n with
  | O => (tab, pos)
  | S n' =>
      let c := nth s norm 0 in
      let '(tab, pos) := if c >? 0 then spread_one log (Z.to_nat c) (Z.of_nat s) high tab pos else (tab, pos) in
      spread_pos norm log (S s) n' high tab pos
  end.

(* the fast spread of the C (no -1 symbol): the symbols in order, symbol s norm[s] times (the `spread`
   byte array), then cell (i * step) mod 2^log gets the i-th one, i = 0 .. 2^log - 1 *)
Definition spread_bytes (norm: list Z) : list Z :=
  flat_map (fun s => repeat (Z.of_nat s) (Z.to_nat (nth s norm 0))) (seq 0 (length norm)).

Fixpoint fast_fill (log: Z) (sb: list Z) (i: nat) (n: nat) (tab: list Z) : list Z :=
  match n with
  | O => tab
  | S n' =>
      fast_fill log sb (S i) n'
        (upd tab (Z.to_nat ((Z.of_nat i * fse_step log) mod 2 ^ log)) (nth i sb 0))
  end.

Definition fast_tab (norm: list Z) (log: Z) : list Z :=
  fast_fill log (spread_bytes norm) 0 (Z.to_nat (2 ^ log)) (repeat 0 (Z.to_nat (2 ^ log))).

(* The model facts the table builders need, as propositions (the bodies take them as hypotheses; they are
   proved once below).
   FSE_WF_SLOW: the table of a valid distribution is well formed (fastMode = 1: every cell reads a bit),
   and the slow spread (C's loop with the low-probability area) gives fse_symtab and ends at position 0. *)
Definition FSE_WF_SLOW : Prop :=
  forall (norm: list Z) (log m: Z), ncount_ok norm log m ->
  ft_log (fse_build norm log) = log /\
  Zlength (ft_cells (fse_build norm log)) = 2 ^ log /\
  Forall (fun e => 0 <= fe_sym e < Zlength norm /\ 0 <= fe_nb e <= log /\
                   0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ log) (ft_cells (fse_build norm log)) /\
  (fse_fm norm log = 1 -> Forall (fun e => 1 <= fe_nb e) (ft_cells (fse_build norm log))) /\
  (let '(tab, high) := place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1) in
   spread_pos norm log 0 (length norm) high tab 0 = (fse_symtab norm log, 0)).

(* FSE_FAST: the fast spread (no -1 symbol) builds fse_symtab *)
Definition FSE_FAST : Prop :=
  forall (norm: list Z) (log m: Z), ncount_ok norm log m -> Forall (fun c => 0 <= c) norm ->
  fast_tab norm log = fse_symtab norm log.

(* ---------- proof of FSE_WF_SLOW: helpers, prefix wf_ ---------- *)

Lemma wf_upd_length : forall {A} (l: list A) i x, length (upd l i x) = length l.
Proof. induction l; destruct i; simpl; auto. Qed.

Lemma wf_nth_upd_same : forall {A} (l: list A) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. induction l; destruct i; simpl; intros; auto; try lia. apply IHl; lia. Qed.

Lemma wf_nth_upd_other : forall {A} (l: list A) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof. induction l; destruct i, j; simpl; intros; auto; try lia. Qed.

Lemma wf_upd_app_mid : forall {A} (a x: list A) y v, upd (a ++ y :: x) (length a) v = a ++ v :: x.
Proof. induction a; simpl; intros; auto. f_equal; auto. Qed.

(* the step *)
Lemma wf_step_eq : forall log, 4 <= log -> fse_step log = 10 * 2 ^ (log - 4) + 3.
Proof.
  intros. unfold fse_step. rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ log) with (2 ^ (log - 4) * 16).
  2:{ replace 16 with (2 ^ 4) by reflexivity. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  replace (2 ^ 1) with 2 by reflexivity. replace (2 ^ 3) with 8 by reflexivity.
  replace (2 ^ (log - 4) * 16) with ((2 ^ (log - 4) * 8) * 2) by ring. rewrite Z.div_mul by lia.
  replace (2 ^ (log - 4) * 8 * 2) with ((2 ^ (log - 4) * 2) * 8) by ring. rewrite Z.div_mul by lia.
  ring.
Qed.

Definition wf_gp (log: Z) (k: nat) : Z := (Z.of_nat k * fse_step log) mod 2 ^ log.

Lemma wf_gp_range : forall log k, 0 <= log -> 0 <= wf_gp log k < 2 ^ log.
Proof. intros. unfold wf_gp. apply Z.mod_pos_bound. lia. Qed.

Lemma wf_gp_S : forall log k, 0 <= log ->
  Z.land (wf_gp log k + (Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3)) (2 ^ log - 1) = wf_gp log (S k).
Proof.
  intros. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. unfold wf_gp. fold (fse_step log).
  rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma wf_gp_size : forall log, 0 <= log -> wf_gp log (Z.to_nat (2 ^ log)) = 0.
Proof.
  intros. unfold wf_gp. rewrite Z2Nat.id by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

Lemma wf_pow2_divide_odd : forall n x t, (2 ^ Z.of_nat n | x * (2 * t + 1)) -> (2 ^ Z.of_nat n | x).
Proof.
  induction n; intros x t H.
  - simpl. apply Z.divide_1_l.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (H2: (2 | x * (2 * t + 1))).
    { apply Z.divide_trans with (2 * 2 ^ Z.of_nat n); auto. apply Z.divide_factor_l. }
    apply prime_mult in H2; [|apply prime_2]. destruct H2 as [[y Hy] | [y Hy]]; [|lia].
    subst x. replace (y * 2 * (2 * t + 1)) with (2 * (y * (2 * t + 1))) in H by ring.
    apply Z.mul_divide_cancel_l in H; [|lia]. apply IHn in H.
    rewrite (Z.mul_comm y 2). apply Z.mul_divide_mono_l. auto.
Qed.

Lemma wf_gp_inj : forall log i j, 4 <= log -> (i < Z.to_nat (2 ^ log))%nat -> (j < Z.to_nat (2 ^ log))%nat ->
  wf_gp log i = wf_gp log j -> i = j.
Proof.
  intros log i j Hl Hi Hj H. unfold wf_gp in H. rewrite wf_step_eq in H by lia.
  set (t := 5 * 2 ^ (log - 4) + 1) in *.
  replace (10 * 2 ^ (log - 4) + 3) with (2 * t + 1) in H by (subst t; ring).
  assert (Hd: (2 ^ log | (Z.of_nat i - Z.of_nat j) * (2 * t + 1))).
  { apply Z.mod_divide; [lia|]. rewrite Z.mul_sub_distr_r, Zminus_mod, H, Z.sub_diag. reflexivity. }
  replace log with (Z.of_nat (Z.to_nat log)) in Hd by lia.
  apply wf_pow2_divide_odd in Hd. rewrite Z2Nat.id in Hd by lia.
  destruct Hd as [q Hq].
  assert (0 < 2 ^ log) by lia.
  apply Nat2Z.inj_lt in Hi; apply Nat2Z.inj_lt in Hj. rewrite Z2Nat.id in Hi, Hj by lia.
  assert (q = 0) by nia. subst q. lia.
Qed.

(* the orbit of the step covers every cell *)
Lemma wf_orbit_perm : forall log, 4 <= log ->
  Permutation (map (wf_gp log) (seq 0 (Z.to_nat (2 ^ log)))) (map Z.of_nat (seq 0 (Z.to_nat (2 ^ log)))).
Proof.
  intros log Hl. apply NoDup_Permutation_bis.
  - apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros x y Hx Hy E. apply in_seq in Hx; apply in_seq in Hy. eapply wf_gp_inj; eauto; lia.
  - rewrite !map_length; lia.
  - intros p Hp. apply in_map_iff in Hp. destruct Hp as [k [<- Hk]].
    apply in_map_iff. exists (Z.to_nat (wf_gp log k)). pose proof (wf_gp_range log k).
    split; [lia|]. apply in_seq. lia.
Qed.

Lemma wf_perm_filter : forall {A} (f: A -> bool) l l', Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros A f l l' H. induction H; simpl.
  - constructor.
  - destruct (f x); auto.
  - destruct (f x), (f y); try constructor; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma wf_filter_true : forall {A} (f: A -> bool) l, (forall x, In x l -> f x = true) -> filter f l = l.
Proof. induction l; simpl; intros; auto. rewrite H by auto. f_equal; auto. Qed.

Lemma wf_filter_false : forall {A} (f: A -> bool) l, (forall x, In x l -> f x = false) -> filter f l = nil.
Proof. induction l; simpl; intros; auto. rewrite H by auto. auto. Qed.

Lemma wf_filter_low : forall n h, -1 <= h < Z.of_nat n ->
  filter (fun p => p <=? h) (map Z.of_nat (seq 0 n)) = map Z.of_nat (seq 0 (Z.to_nat (h + 1))).
Proof.
  intros. replace n with (Z.to_nat (h + 1) + (n - Z.to_nat (h + 1)))%nat at 1 by lia.
  rewrite seq_app, map_app, filter_app. rewrite (wf_filter_false _ (map _ (seq (0 + _) _))).
  - rewrite app_nil_r. apply wf_filter_true. intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [k [<- Hk]]. apply in_seq in Hk. apply Z.leb_le. lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- Hk]]. apply in_seq in Hk.
    apply Z.leb_gt. lia.
Qed.

Definition wf_R (log high: Z) (k m: nat) : list Z := filter (fun p => p <=? high) (map (wf_gp log) (seq k m)).

Lemma wf_R_perm : forall log high, 4 <= log -> -1 <= high < 2 ^ log ->
  Permutation (wf_R log high 0 (Z.to_nat (2 ^ log))) (map Z.of_nat (seq 0 (Z.to_nat (high + 1)))).
Proof.
  intros. unfold wf_R. rewrite <- (wf_filter_low (Z.to_nat (2 ^ log))) by lia. apply wf_perm_filter. apply wf_orbit_perm; auto.
Qed.

(* writing values at positions *)
Fixpoint wf_wapp (tab: list Z) (ps vs: list Z) : list Z :=
  match ps, vs with
  | p :: ps', v :: vs' => wf_wapp (upd tab (Z.to_nat p) v) ps' vs'
  | _, _ => tab
  end.

Lemma wf_wapp_length : forall ps vs tab, length (wf_wapp tab ps vs) = length tab.
Proof. induction ps; destruct vs; simpl; intros; auto. rewrite IHps. apply wf_upd_length. Qed.

Lemma wf_wapp_other : forall ps vs tab i d, (forall p, In p ps -> Z.to_nat p <> i) ->
  nth i (wf_wapp tab ps vs) d = nth i tab d.
Proof.
  induction ps; destruct vs; simpl; intros; auto.
  rewrite IHps by auto. apply wf_nth_upd_other. auto.
Qed.

Lemma wf_wapp_at : forall ps vs tab j d, NoDup ps -> Forall (fun p => 0 <= p < Z.of_nat (length tab)) ps ->
  length ps = length vs -> (j < length ps)%nat ->
  nth (Z.to_nat (nth j ps 0)) (wf_wapp tab ps vs) d = nth j vs d.
Proof.
  induction ps; destruct vs; simpl; intros tab j d Hn Hf Hl Hj; try lia.
  inversion Hn; subst. inversion Hf; subst. destruct j.
  - rewrite wf_wapp_other. apply wf_nth_upd_same. lia.
    intros p Hp E. apply H1. pose proof Hp as Hp'. apply Forall_forall with (x := p) in H4; auto. replace a with p by lia. auto.
  - apply IHps; auto. eapply Forall_impl; [|exact H4]. simpl. intros. rewrite wf_upd_length. auto. lia.
Qed.

(* the walk of the spread *)
Fixpoint wf_wseq (log high: Z) (vs: list Z) (tab: list Z) (pos: Z) : list Z * Z :=
  match vs with
  | nil => (tab, pos)
  | v :: vs' => wf_wseq log high vs' (upd tab (Z.to_nat pos) v)
                  (skip_high log (Z.to_nat (2 ^ log)) high
                     (Z.land (pos + (Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3)) (2 ^ log - 1)))
  end.

Lemma wf_wseq_app : forall log high a b tab pos,
  wf_wseq log high (a ++ b) tab pos = wf_wseq log high b (fst (wf_wseq log high a tab pos)) (snd (wf_wseq log high a tab pos)).
Proof. induction a; simpl; intros; auto. Qed.

Lemma wf_spread_one_wseq : forall log k s high tab pos,
  spread_one log k s high tab pos = wf_wseq log high (repeat s k) tab pos.
Proof. induction k; simpl; intros; auto. Qed.

Definition wf_w (norm: list Z) (s n: nat) : list Z :=
  flat_map (fun i => let c := nth i norm 0 in if c >? 0 then repeat (Z.of_nat i) (Z.to_nat c) else nil) (seq s n).

Lemma wf_spread_pos_wseq : forall norm log n s high tab pos,
  spread_pos norm log s n high tab pos = wf_wseq log high (wf_w norm s n) tab pos.
Proof.
  induction n; simpl; intros; auto. unfold wf_w in *. simpl.
  destruct (nth s norm 0 >? 0).
  - rewrite wf_spread_one_wseq, wf_wseq_app.
    destruct (wf_wseq log high (repeat (Z.of_nat s) (Z.to_nat (nth s norm 0))) tab pos); simpl. apply IHn.
  - apply IHn.
Qed.

Lemma wf_spread_fst : forall norm log n s high tab pos,
  spread norm log s n high tab pos = fst (spread_pos norm log s n high tab pos).
Proof.
  induction n; simpl; intros; auto.
  destruct (nth s norm 0 >? 0); [destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos)|];
  apply IHn.
Qed.

Lemma wf_walk : forall log high m k fuel tab vs, 0 <= log -> 0 <= high ->
  (k + m = Z.to_nat (2 ^ log))%nat -> (m <= fuel)%nat -> length vs = length (wf_R log high k m) ->
  wf_wseq log high vs tab (skip_high log fuel high (wf_gp log k)) = (wf_wapp tab (wf_R log high k m) vs, 0).
Proof.
  induction m; intros k fuel tab vs Hl Hh Hk Hf Hv.
  - replace k with (Z.to_nat (2 ^ log)) by lia. rewrite wf_gp_size by lia.
    unfold wf_R in Hv; simpl in Hv. destruct vs; [|simpl in Hv; lia].
    destruct fuel; simpl; auto. destruct (0 >? high) eqn:E; [lia|]. reflexivity.
  - destruct fuel; [lia|]. simpl skip_high. unfold wf_R in *. simpl seq in *. simpl map in *.
    simpl filter in *. rewrite wf_gp_S by lia.
    destruct (wf_gp log k >? high) eqn:E.
    + assert (E2: (wf_gp log k <=? high) = false) by lia. rewrite E2 in *.
      apply IHm; auto; lia.
    + assert (E2: (wf_gp log k <=? high) = true) by lia. rewrite E2 in *.
      destruct vs as [|v vs]; simpl in Hv; [lia|]. simpl. rewrite wf_gp_S by lia.
      apply IHm; auto; lia.
Qed.

(* place_low *)
Definition wf_low (norm: list Z) (s n: nat) : list Z :=
  flat_map (fun i => if nth i norm 0 =? -1 then [Z.of_nat i] else nil) (seq s n).

Lemma wf_place_low : forall norm n s A X high, length A = Z.to_nat (high + 1) ->
  Z.of_nat (length (wf_low norm s n)) <= high + 1 ->
  exists A', place_low norm s n (A ++ X) high = (A' ++ rev (wf_low norm s n) ++ X, high - Z.of_nat (length (wf_low norm s n))) /\
             length A' = Z.to_nat (high + 1 - Z.of_nat (length (wf_low norm s n))).
Proof.
  induction n; intros s A X high HA Hlow.
  - exists A. simpl. rewrite !Z.sub_0_r. split; auto.
  - unfold wf_low in *. simpl seq in *. simpl flat_map in *. simpl place_low.
    destruct (nth s norm 0 =? -1).
    + simpl app in *. simpl length in Hlow. destruct (exists_last (l := A)) as [A0 [a EA]].
      { intro; subst; simpl in HA; lia. }
      subst A. rewrite app_length in HA; simpl in HA.
      rewrite <- app_assoc. simpl.
      replace (Z.to_nat high) with (length A0) by lia. rewrite wf_upd_app_mid.
      destruct (IHn (S s) A0 (Z.of_nat s :: X) (high - 1)) as [A' [E1 E2]]; [lia|lia|].
      exists A'. rewrite E1. simpl length. split.
      * f_equal. rewrite <- !app_assoc. reflexivity. lia.
      * rewrite E2. f_equal. lia.
    + simpl app in *. apply IHn; auto.
Qed.

(* counting *)
Lemma wf_flat_perm : forall {A B} (f g: A -> list B) l,
  Permutation (flat_map f l ++ flat_map g l) (flat_map (fun x => f x ++ g x) l).
Proof.
  induction l; simpl; auto.
  rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_swap_app|]. apply Permutation_app_head. auto.
Qed.

Definition wf_K (norm: list Z) (i: nat) : Z := let c := nth i norm 0 in if c =? -1 then 1 else c.

Definition wf_M (norm: list Z) (s n: nat) : list Z :=
  flat_map (fun i => repeat (Z.of_nat i) (Z.to_nat (wf_K norm i))) (seq s n).

Lemma wf_nth_ge : forall norm i, Forall (fun c => -1 <= c) norm -> -1 <= nth i norm 0.
Proof.
  intros. destruct (Nat.lt_ge_cases i (length norm)).
  - apply Forall_forall with (x := nth i norm 0) in H; auto. apply nth_In; auto.
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma wf_wlow_M : forall norm s n, Forall (fun c => -1 <= c) norm ->
  Permutation (wf_w norm s n ++ wf_low norm s n) (wf_M norm s n).
Proof.
  intros. unfold wf_w, wf_low, wf_M. eapply Permutation_trans; [apply wf_flat_perm|].
  apply Permutation_refl'. apply flat_map_ext. intros i. unfold wf_K.
  pose proof (wf_nth_ge norm i H). destruct (Z.eq_dec (nth i norm 0) (-1)) as [E|E].
  - rewrite E. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E). destruct (nth i norm 0 >? 0) eqn:G.
    + apply app_nil_r.
    + replace (Z.to_nat (nth i norm 0)) with 0%nat by lia. reflexivity.
Qed.

Lemma wf_flat_map_map : forall {A B C} (f: B -> list C) (g: A -> B) l,
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l; simpl; auto. f_equal; auto. Qed.

Lemma wf_len_M : forall l (g: nat -> Z), Forall (fun c => -1 <= c) l ->
  Z.of_nat (length (flat_map (fun i => repeat (g i) (Z.to_nat (wf_K l i))) (seq 0 (length l)))) =
  fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) l).
Proof.
  induction l; intros g Hf; simpl; auto. inversion Hf; subst.
  rewrite app_length, repeat_length, <- seq_shift, wf_flat_map_map.
  change (fun x => repeat (g (S x)) (Z.to_nat (wf_K (a :: l) (S x))))
    with (fun i => repeat ((fun i => g (S i)) i) (Z.to_nat (wf_K l i))).
  rewrite Nat2Z.inj_add, (IHl (fun i => g (S i))) by auto. unfold wf_K at 1. simpl.
  destruct (a =? -1) eqn:E; lia.
Qed.

Lemma wf_count_repeat : forall (x y: Z) k, count_occ Z.eq_dec (repeat x k) y = if Z.eq_dec x y then k else 0%nat.
Proof.
  induction k; simpl; destruct (Z.eq_dec x y); auto; rewrite IHk; destruct (Z.eq_dec x y); auto; congruence.
Qed.

Lemma wf_M_count : forall norm n s i, (s <= i < s + n)%nat ->
  count_occ Z.eq_dec (wf_M norm s n) (Z.of_nat i) = Z.to_nat (wf_K norm i).
Proof.
  assert (Z0: forall norm n s i, (i < s)%nat -> count_occ Z.eq_dec (wf_M norm s n) (Z.of_nat i) = 0%nat).
  { induction n; simpl; intros; auto. unfold wf_M in *. simpl. rewrite count_occ_app, wf_count_repeat.
    destruct (Z.eq_dec (Z.of_nat s) (Z.of_nat i)); [lia|]. simpl. apply IHn. lia. }
  induction n; intros s i H; [lia|]. unfold wf_M in *. simpl. rewrite count_occ_app, wf_count_repeat.
  destruct (Nat.eq_dec s i).
  - subst. destruct (Z.eq_dec (Z.of_nat i) (Z.of_nat i)); [|congruence]. rewrite Z0 by lia. lia.
  - destruct (Z.eq_dec (Z.of_nat s) (Z.of_nat i)); [lia|]. simpl. apply IHn. lia.
Qed.

Lemma wf_M_in : forall norm n s x, In x (wf_M norm s n) ->
  exists i, (s <= i < s + n)%nat /\ x = Z.of_nat i /\ 1 <= wf_K norm i.
Proof.
  intros. unfold wf_M in H. apply in_flat_map in H. destruct H as [i [Hi Hx]].
  apply in_seq in Hi. exists i. destruct (Z.to_nat (wf_K norm i)) eqn:E; [simpl in Hx; tauto|].
  apply repeat_spec in Hx. split; [lia|]. split; [auto|lia].
Qed.

Lemma wf_cell : forall log K x, 1 <= log -> 1 <= K <= 2 ^ log -> K <= x -> x + 1 <= 2 * K ->
  0 <= log - Z.log2 x <= log /\ 0 <= Z.shiftl x (log - Z.log2 x) - 2 ^ log /\
  Z.shiftl x (log - Z.log2 x) - 2 ^ log + 2 ^ (log - Z.log2 x) <= 2 ^ log /\
  (K <= 2 ^ (log - 1) -> 1 <= log - Z.log2 x).
Proof.
  intros log K x Hl HK Hx1 Hx2.
  assert (Hp: 2 ^ log = 2 * 2 ^ (log - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hsp: 2 ^ (log + 1) = 2 * 2 ^ log) by (rewrite Z.pow_add_r by lia; lia).
  pose proof (Z.log2_spec x ltac:(lia)) as [Hs1 Hs2]. pose proof (Z.log2_nonneg x).
  set (h := Z.log2 x) in *.
  assert (Hh: h < log + 1) by (apply Z.log2_lt_pow2; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hm: 2 ^ h * 2 ^ (log - h) = 2 ^ log) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hs: 2 ^ Z.succ h = 2 * 2 ^ h) by (rewrite Z.pow_succ_r by lia; lia).
  assert (0 < 2 ^ (log - h)) by (apply Z.pow_pos_nonneg; lia).
  split; [lia|]. split; [nia|]. split; [nia|].
  intros HK2. assert (h < log) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma wf_states_ok : forall log (P: Z -> Prop) (Kf: Z -> Z) (fmb: bool) tab nx, 1 <= log ->
  (forall s, In s tab -> P s /\ 0 <= s /\ 1 <= Kf s <= 2 ^ log /\ (fmb = true -> Kf s <= 2 ^ (log - 1)) /\
     Kf s <= nth (Z.to_nat s) nx 0 /\ nth (Z.to_nat s) nx 0 + Z.of_nat (count_occ Z.eq_dec tab s) <= 2 * Kf s) ->
  Forall (fun e => P (fe_sym e) /\ 0 <= fe_nb e <= log /\ 0 <= fe_base e /\ fe_base e + 2 ^ fe_nb e <= 2 ^ log /\
                   (fmb = true -> 1 <= fe_nb e)) (states log tab nx).
Proof.
  induction tab; intros nx Hl H; simpl; constructor.
  - destruct (H a (or_introl eq_refl)) as [HP [Ha [HK [Hfm [Hx1 Hx2]]]]].
    rewrite count_occ_cons_eq in Hx2 by auto. simpl. unfold highbit.
    destruct (wf_cell log (Kf a) (nth (Z.to_nat a) nx 0)) as [C1 [C2 [C3 C4]]]; auto; try lia.
    repeat split; auto; try lia; intros F; apply C4, Hfm, F.
  - apply IHtab; auto. intros s Hs.
    destruct (H s (or_intror Hs)) as [HP [Ha [HK [Hfm [Hx1 Hx2]]]]].
    destruct (H a (or_introl eq_refl)) as [_ [Ha' _]].
    repeat split; auto; try lia.
    + destruct (Z.eq_dec a s).
      * subst. rewrite wf_nth_upd_same. lia.
        destruct (Nat.lt_ge_cases (Z.to_nat s) (length nx)); auto. rewrite nth_overflow in Hx1 by auto. lia.
      * rewrite wf_nth_upd_other by lia. auto.
    + destruct (Z.eq_dec a s).
      * subst. rewrite count_occ_cons_eq in Hx2 by auto. rewrite wf_nth_upd_same. lia.
        destruct (Nat.lt_ge_cases (Z.to_nat s) (length nx)); auto. rewrite nth_overflow in Hx1 by auto. lia.
      * rewrite count_occ_cons_neq in Hx2 by auto. rewrite wf_nth_upd_other by lia. auto.
Qed.

Lemma wf_states_length : forall log tab nx, length (states log tab nx) = length tab.
Proof. induction tab; simpl; intros; auto. Qed.

Lemma wf_next0_nth : forall norm i, nth i (map (fun c => if c =? -1 then 1 else c) norm) 0 = wf_K norm i.
Proof.
  unfold wf_K. induction norm; intros [|i]; simpl; auto.
Qed.

Lemma wf_firstn_map : forall (l: list Z) n, (n <= length l)%nat -> firstn n l = map (fun i => nth i l 0) (seq 0 n).
Proof.
  intros. apply nth_ext with (d := 0) (d' := 0).
  - rewrite firstn_length_le by auto. rewrite map_length, seq_length; auto.
  - intros i Hi. rewrite firstn_length_le in Hi by auto. rewrite nth_firstn.
    destruct (Nat.ltb_spec i n); [|lia].
    transitivity (nth i (map (fun i => nth i l 0) (seq 0 n)) ((fun i => nth i l 0) 0%nat)).
    + pose proof (map_nth (fun j => nth j l 0) (seq 0 n) 0%nat i) as E. cbv beta in E.
      rewrite seq_nth in E by auto. rewrite E. reflexivity.
    + apply nth_indep. rewrite map_length, seq_length; auto.
Qed.

(* the table after the spread is a permutation of (w ++ low) *)
Lemma wf_T_perm : forall A' low w R, NoDup R -> Permutation R (map Z.of_nat (seq 0 (length A'))) ->
  length w = length A' ->
  Permutation (wf_wapp (A' ++ rev low) R w) (w ++ low).
Proof.
  intros A' low w R HR HP Hw. set (N := length A') in *. set (T := wf_wapp (A' ++ rev low) R w).
  assert (HRin: forall p, In p R -> 0 <= p < Z.of_nat N).
  { intros p Hp. eapply Permutation_in in Hp; eauto. apply in_map_iff in Hp. destruct Hp as [k [<- Hk]].
    apply in_seq in Hk. lia. }
  assert (HlR: length R = N) by (rewrite (Permutation_length HP), map_length, seq_length; auto).
  assert (HlT: length T = (N + length low)%nat) by (unfold T; rewrite wf_wapp_length, app_length, rev_length; auto).
  rewrite <- (firstn_skipn N T). apply Permutation_app.
  - rewrite wf_firstn_map by lia.
    replace (map (fun i => nth i T 0) (seq 0 N)) with (map (fun p => nth (Z.to_nat p) T 0) (map Z.of_nat (seq 0 N))).
    2:{ rewrite map_map. apply map_ext. intros. rewrite Nat2Z.id. auto. }
    eapply Permutation_trans; [apply Permutation_map; apply Permutation_sym; exact HP|].
    assert (Em: map (fun p => nth (Z.to_nat p) T 0) R = w).
    { apply nth_ext with (d := 0) (d' := 0).
      + rewrite length_map; lia.
      + intros j Hj. rewrite length_map in Hj.
        pose proof (map_nth (fun p => nth (Z.to_nat p) T 0) R 0 j) as E. cbv beta in E.
        transitivity (nth j (map (fun p => nth (Z.to_nat p) T 0) R) (nth (Z.to_nat 0) T 0)).
        { apply nth_indep. rewrite length_map; auto. }
        rewrite E. unfold T. apply wf_wapp_at; auto; try lia.
        apply Forall_forall. intros p Hp. apply HRin in Hp. rewrite app_length. lia. }
    rewrite Em. apply Permutation_refl.
  - apply Permutation_trans with (rev low); [|apply Permutation_sym, Permutation_rev].
    apply Permutation_refl'. apply nth_ext with (d := 0) (d' := 0).
    + rewrite length_skipn, rev_length. lia.
    + intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. unfold T. rewrite wf_wapp_other.
      * rewrite app_nth2 by lia. f_equal. lia.
      * intros p Hp. apply HRin in Hp. lia.
Qed.

Lemma fse_wf_slow : FSE_WF_SLOW.
Proof.
  intros norm log m [Hlog [Hlen [Hc Hsum]]].
  assert (Hge: Forall (fun c => -1 <= c) norm) by (eapply Forall_impl; [|exact Hc]; simpl; intros; lia).
  assert (Hsz: 32 <= 2 ^ log) by (replace 32 with (2 ^ 5) by reflexivity; apply Z.pow_le_mono_r; lia).
  set (w := wf_w norm 0 (length norm)). set (low := wf_low norm 0 (length norm)).
  set (M := wf_M norm 0 (length norm)).
  assert (HwlM: Permutation (w ++ low) M) by (apply wf_wlow_M; auto).
  assert (HlM: Z.of_nat (length M) = 2 ^ log) by (rewrite <- Hsum; apply wf_len_M; auto).
  assert (Hwl: (length w + length low)%nat = Z.to_nat (2 ^ log)).
  { rewrite <- app_length, (Permutation_length HwlM). lia. }
  destruct (wf_place_low norm (length norm) 0 (repeat 0 (Z.to_nat (2 ^ log))) nil (2 ^ log - 1)) as [A' [Epl HA']].
  { rewrite repeat_length. lia. } { fold low. lia. }
  fold low in Epl, HA'. rewrite app_nil_r in Epl, Epl.
  set (high := 2 ^ log - 1 - Z.of_nat (length low)) in *.
  set (R := wf_R log high 0 (Z.to_nat (2 ^ log))).
  assert (HRP: Permutation R (map Z.of_nat (seq 0 (length A')))).
  { rewrite HA'. replace (2 ^ log - 1 + 1 - Z.of_nat (length low)) with (high + 1) by lia.
    apply wf_R_perm; lia. }
  assert (HRN: NoDup R).
  { eapply Permutation_NoDup; [apply Permutation_sym; exact HRP|].
    apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup]. intros x y _ _ E. lia. }
  assert (Hlw: length w = length A') by lia.
  assert (Hsp: spread_pos norm log 0 (length norm) high (A' ++ rev low) 0 = (wf_wapp (A' ++ rev low) R w, 0)).
  { rewrite wf_spread_pos_wseq. fold w.
    destruct (Z.eq_dec high (-1)) as [Eh|Eh].
    - assert (length w = 0%nat) by lia. destruct w; [|simpl in *; lia].
      assert (length R = 0%nat) by (rewrite (Permutation_length HRP), map_length, seq_length; lia).
      destruct R; [|simpl in *; lia]. reflexivity.
    - replace 0 with (skip_high log (Z.to_nat (2 ^ log)) high (wf_gp log 0)) at 1.
      2:{ unfold wf_gp. simpl. destruct (Z.to_nat (2 ^ log)) eqn:E; [lia|]. simpl.
          rewrite Z.mod_0_l by lia. destruct (0 >? high) eqn:E2; auto. lia. }
      apply wf_walk; try lia.
      fold R. rewrite Hlw, (Permutation_length HRP), map_length, seq_length. auto. }
  set (T := wf_wapp (A' ++ rev low) R w) in *.
  assert (HTM: Permutation T M).
  { eapply Permutation_trans; [apply wf_T_perm; auto|]. auto. }
  assert (HbT: fse_build norm log = {| ft_log := log; ft_cells := states log T (map (fun c => if c =? -1 then 1 else c) norm) |}).
  { unfold fse_build. cbv zeta. rewrite Epl. rewrite wf_spread_fst, Hsp. reflexivity. }
  assert (HsT: fse_symtab norm log = T).
  { unfold fse_symtab. rewrite Epl. rewrite wf_spread_fst, Hsp. reflexivity. }
  assert (HF: Forall (fun e => (0 <= fe_sym e < Zlength norm) /\ 0 <= fe_nb e <= log /\ 0 <= fe_base e /\
                   fe_base e + 2 ^ fe_nb e <= 2 ^ log /\ (fse_fm norm log =? 1 = true -> 1 <= fe_nb e))
                (states log T (map (fun c => if c =? -1 then 1 else c) norm))).
  { apply (wf_states_ok log (fun s => 0 <= s < Zlength norm) (fun s => wf_K norm (Z.to_nat s))); [lia|].
    intros s Hs. apply (Permutation_in _ HTM) in Hs. apply wf_M_in in Hs.
    destruct Hs as [i [Hi [-> HK]]]. rewrite Nat2Z.id, wf_next0_nth.
    rewrite (proj1 (Permutation_count_occ Z.eq_dec T M) HTM). unfold M. rewrite wf_M_count by lia.
    assert (Hci: -1 <= nth i norm 0 <= 2 ^ log) by (apply Forall_forall with (x := nth i norm 0) in Hc; auto; apply nth_In; lia).
    rewrite Zlength_correct. repeat split; try lia.
    - unfold wf_K in *. destruct (nth i norm 0 =? -1); lia.
    - intros Hfm. unfold fse_fm in Hfm. destruct (existsb _ norm) eqn:Ex; [discriminate|].
      assert (Hn: (2 ^ (log - 1) <=? nth i norm 0) = false).
      { destruct (2 ^ (log - 1) <=? nth i norm 0) eqn:E; auto. rewrite <- Ex. symmetry. apply existsb_exists.
        exists (nth i norm 0). split; auto. apply nth_In. lia. }
      assert (0 < 2 ^ (log - 1)) by (apply Z.pow_pos_nonneg; lia).
      unfold wf_K. destruct (nth i norm 0 =? -1); lia. }
  rewrite HbT, HsT. simpl. rewrite Epl. split; [auto|]. split.
  { rewrite Zlength_correct, wf_states_length. unfold T. rewrite wf_wapp_length, app_length, rev_length. lia. }
  split; [|split].
  - eapply Forall_impl; [|exact HF]. simpl. intros e He. tauto.
  - intros Hfm. eapply Forall_impl; [|exact HF]. simpl. intros e He. apply He. rewrite Hfm. reflexivity.
  - auto.
Qed.

(* fse_fast: with no -1 count, place_low leaves the table, skip_high never skips, and spread writes the
   same symbols at the same positions (i * step) mod 2^log as fast_fill *)
Lemma fse_fast_place_low : forall norm s n tab high,
  Forall (fun c => 0 <= c) norm -> place_low norm s n tab high = (tab, high).
Proof.
  intros norm s n; revert s; induction n as [|n IH]; intros s tab high Hnn; simpl; auto.
  assert (Hs: 0 <= nth s norm 0).
  { destruct (Nat.lt_ge_cases s (length norm)) as [Hl|Hl].
    - rewrite Forall_forall in Hnn. apply Hnn, nth_In; auto.
    - rewrite nth_overflow by auto. lia. }
  destruct (nth s norm 0 =? -1) eqn:E; [lia|]. auto.
Qed.

Fixpoint fse_fast_gfill (log: Z) (i: nat) (l: list Z) (tab: list Z) : list Z :=
  match l with
  | nil => tab
  | x :: l' => fse_fast_gfill log (S i) l' (upd tab (Z.to_nat ((Z.of_nat i * fse_step log) mod 2 ^ log)) x)
  end.

Lemma fse_fast_gfill_app : forall log l1 l2 i tab,
  fse_fast_gfill log i (l1 ++ l2) tab = fse_fast_gfill log (i + length l1) l2 (fse_fast_gfill log i l1 tab).
Proof.
  induction l1 as [|x l1 IH]; intros l2 i tab; simpl.
  - rewrite Nat.add_0_r; auto.
  - rewrite IH. f_equal. lia.
Qed.

Lemma fse_fast_fill_gfill : forall log l pre tab,
  fast_fill log (pre ++ l) (length pre) (length l) tab = fse_fast_gfill log (length pre) l tab.
Proof.
  induction l as [|x l IH]; intros pre tab; simpl; auto.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. simpl.
  replace (pre ++ x :: l) with ((pre ++ [x]) ++ l) by (rewrite <- app_assoc; auto).
  replace (S (length pre)) with (length (pre ++ [x])) by (rewrite app_length; simpl; lia).
  apply IH.
Qed.

Lemma fse_fast_next_pos : forall log (i: nat), 0 <= log ->
  skip_high log (Z.to_nat (2 ^ log)) (2 ^ log - 1)
    (Z.land ((Z.of_nat i * fse_step log) mod 2 ^ log + (Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3))
            (2 ^ log - 1))
  = (Z.of_nat (S i) * fse_step log) mod 2 ^ log.
Proof.
  intros log i Hlog.
  assert (HN: 0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  assert (Hst: 0 <= fse_step log).
  { unfold fse_step. pose proof (Z.shiftr_nonneg (2 ^ log) 1). pose proof (Z.shiftr_nonneg (2 ^ log) 3). lia. }
  fold (fse_step log).
  replace (2 ^ log - 1) with (Z.ones log) at 2 by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia.
  rewrite Z.add_mod_idemp_l by lia.
  replace (Z.of_nat i * fse_step log + fse_step log) with (Z.of_nat (S i) * fse_step log) by lia.
  assert (Hm: 0 <= (Z.of_nat (S i) * fse_step log) mod 2 ^ log < 2 ^ log) by (apply Z.mod_pos_bound; lia).
  remember ((Z.of_nat (S i) * fse_step log) mod 2 ^ log) as p.
  destruct (Z.to_nat (2 ^ log)); cbn [skip_high]; auto.
  destruct (p >? 2 ^ log - 1) eqn:E; auto. apply Z.gtb_lt in E. lia.
Qed.

Lemma fse_fast_spread_one : forall log k s i tab, 0 <= log ->
  spread_one log k s (2 ^ log - 1) tab ((Z.of_nat i * fse_step log) mod 2 ^ log)
  = (fse_fast_gfill log i (repeat s k) tab, (Z.of_nat (i + k) * fse_step log) mod 2 ^ log).
Proof.
  induction k as [|k IH]; intros s i tab Hlog; simpl.
  - rewrite Nat.add_0_r; auto.
  - rewrite fse_fast_next_pos by auto. rewrite IH by auto. f_equal. f_equal. f_equal. lia.
Qed.

Lemma fse_fast_spread : forall norm log n s i tab, 0 <= log ->
  spread norm log s n (2 ^ log - 1) tab ((Z.of_nat i * fse_step log) mod 2 ^ log)
  = fse_fast_gfill log i (flat_map (fun s => repeat (Z.of_nat s) (Z.to_nat (nth s norm 0))) (seq s n)) tab.
Proof.
  induction n as [|n IH]; intros s i tab Hlog; simpl; auto.
  rewrite fse_fast_gfill_app.
  destruct (nth s norm 0 >? 0) eqn:E.
  - rewrite fse_fast_spread_one by auto. rewrite IH by auto. rewrite repeat_length. auto.
  - rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. replace (Z.to_nat (nth s norm 0)) with O by lia. simpl.
    rewrite Nat.add_0_r. auto.
Qed.

Lemma fse_fast_len : forall l pre, Forall (fun c => 0 <= c) l ->
  Z.of_nat (length (flat_map (fun s => repeat (Z.of_nat s) (Z.to_nat (nth s (pre ++ l) 0)))
                             (seq (length pre) (length l))))
  = fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) l).
Proof.
  induction l as [|x l IH]; intros pre Hnn; simpl; auto.
  inversion Hnn; subst.
  rewrite app_length, repeat_length.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. simpl.
  replace (pre ++ x :: l) with ((pre ++ [x]) ++ l) by (rewrite <- app_assoc; auto).
  replace (S (length pre)) with (length (pre ++ [x])) by (rewrite app_length; simpl; lia).
  rewrite Nat2Z.inj_add, IH by auto.
  destruct (x =? -1) eqn:E; lia.
Qed.

Lemma fse_fast : FSE_FAST.
Proof.
  intros norm log m Hok Hnn.
  destruct Hok as (Hlog & _ & _ & Hsum).
  unfold fast_tab, fse_symtab.
  rewrite fse_fast_place_low by auto.
  assert (HN: 0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  pose proof (fse_fast_spread norm log (length norm) 0 0 (repeat 0 (Z.to_nat (2 ^ log)))) as Hs.
  change ((Z.of_nat 0 * fse_step log) mod 2 ^ log) with 0 in Hs.
  rewrite Hs by lia.
  fold (spread_bytes norm).
  assert (Hl: Z.to_nat (2 ^ log) = length (spread_bytes norm)).
  { pose proof (fse_fast_len norm nil Hnn) as H. simpl in H. unfold spread_bytes. lia. }
  rewrite Hl.
  apply (fse_fast_fill_gfill log (spread_bytes norm) nil).
Qed.

(* ---------- FSE_readNCount, FSE_decompress_wksp and HUF_readStats as C computes them ----------
   The C-exact functions themselves (fse_weights_dec, wrapP, reps, zeros_c, ncount_loop_c, ncount_c, fse_dwksp,
   weights_of, huf_desc_weights_w, huf_parse_w, huf_parse_res, rs_window) are plain Coq in model/EntC.v,
   exported by this file, which the exact model (model/ExHuf.v) shares; the relations to the specifications'
   results follow. *)

(* FSE_readNCount_body / _bmi2 on any window s: >= 8 bytes ncount_c; fewer: FSE_readNCount (the exported
   function, whose specification is NCount.read_ncount) on a zero-padded 8-byte copy, then size <= hbSize *)
Definition ncount_res (s: list Z) (maxsv: Z) : option (list Z * Z * Z) :=
  if Zlength s <? 8 then
    match read_ncount (s ++ repeat 0 (Z.to_nat (8 - Zlength s))) maxsv with
    | Some (norm, log, size) => if size >? Zlength s then None else Some (norm, log, size)
    | None => None
    end
  else ncount_c s maxsv.

(* C's result of FSE_readNCount_body on the window s: exact (ncount_res) on >= 8 bytes; on fewer, the
   exported FSE_readNCount (C-result form) on the zero-padded copy: the model's result when it reads the
   description, else any valid distribution within s or an error *)
Definition nc_rel (s: list Z) (maxsv: Z) (res: option (list Z * Z * Z)) : Prop :=
  if Zlength s <? 8 then
    (forall x, ncount_res s maxsv = Some x -> res = Some x) /\
    match res with
    | Some (norm, log, size) => size <= Zlength s /\ ncount_ok norm log maxsv
    | None => True
    end
  else res = ncount_res s maxsv.

Definition weights_res (nk: Z) (s: list Z) : option (list Z) := weights_of (ncount_res s 255) nk s.

Lemma huf_parse_w_model (b: list Z) : huf_parse_w huf_fse_weights b = huf_parse_desc b.
Proof. reflexivity. Qed.

(* the C stores a count as (short)count *)
Definition short_val (x: Z) : val := Vint (Int.sign_ext 16 (Int.repr x)).

(* NCOUNT_RES_OK: a description FSE_readNCount_body accepts is a valid distribution within the window *)
Definition NCOUNT_RES_OK : Prop :=
  forall (s: list Z) (maxsv: Z) (norm: list Z) (log size: Z),
  0 <= maxsv <= 255 -> ncount_res s maxsv = Some (norm, log, size) ->
  ncount_ok norm log maxsv /\ 1 <= size <= Zlength s.

Definition ncw (c: Z) : Z := if c =? -1 then 1 else c.
Definition nsum (l: list Z) : Z := fold_right Z.add 0 (map ncw l).

Lemma nsum_app (l1 l2: list Z) : nsum (l1 ++ l2) = nsum l1 + nsum l2.
Proof. unfold nsum. induction l1 as [|a l1 IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma nsum_repeat0 (k: nat) : nsum (repeat 0 k) = 0.
Proof. unfold nsum. induction k as [|k IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nsum_one (c: Z) : -1 <= c -> nsum [c] + (if c >=? 0 then - c else c) = 0.
Proof. intros Hc. unfold nsum, ncw; simpl. destruct (c =? -1) eqn:E1, (c >=? 0) eqn:E2; lia. Qed.

Lemma nsum_bound (l: list Z) : Forall (fun c => -1 <= c) l ->
  Forall (fun c => -1 <= c <= nsum l) l /\ 0 <= nsum l.
Proof.
  induction l as [|a l IH]; intros H; [split; [constructor | unfold nsum; simpl; lia]|].
  inversion H as [|? ? Ha Hl]; subst. destruct (IH Hl) as [IH1 IH2].
  assert (Hs: nsum (a :: l) = ncw a + nsum l) by reflexivity.
  assert (Hw: a <= ncw a /\ 0 <= ncw a) by (unfold ncw; destruct (a =? -1) eqn:E; lia).
  rewrite Hs. split; [|lia]. constructor; [lia|].
  eapply Forall_impl; [|exact IH1]. simpl. intros c Hc; lia.
Qed.

Lemma fbits_range (b: list Z) (p n: Z) : 0 <= n -> 0 <= fbits b p n < 2 ^ n.
Proof. intros Hn. unfold fbits. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma ncount_zeros_pos (f: nat) (b: list Z) (p: Z) : p <= snd (ncount_zeros f b p).
Proof.
  revert p; induction f as [|f IH]; intros p; simpl; [lia|].
  destruct (fbits b p 2 =? 3).
  - specialize (IH (p + 2)). destruct (ncount_zeros f b (p + 2)); simpl in *; lia.
  - simpl; lia.
Qed.

Lemma wrapP_ge4 (n p: Z) : 8 <= n -> 4 <= p -> 4 <= wrapP n p.
Proof.
  intros Hn Hp. unfold wrapP. destruct (p <? 8 * n); [lia|].
  pose proof (Z.mod_pos_bound (p - 8 * (n - 4)) 32 ltac:(lia)). lia.
Qed.

Lemma reps_nonneg (k: nat) (b: list Z) (p: Z) : 0 <= reps k b p.
Proof. revert p; induction k as [|k IH]; intros p; cbn [reps]; [lia|]. destruct (fbits b p 2 =? 3); [specialize (IH (p + 2)); lia|lia]. Qed.

Lemma zeros_c_pos (f: nat) (b: list Z) (n p z: Z) : 8 <= n -> 4 <= p -> 4 <= snd (zeros_c f b n p z).
Proof.
  intros Hn. revert p z; induction f as [|f IH]; intros p z Hp; cbn [zeros_c]; [simpl; lia|].
  pose proof (wrapP_ge4 n p Hn Hp). pose proof (reps_nonneg 12 b (wrapP n p)).
  destruct (reps 12 b (wrapP n p) =? 12); [apply IH; lia|cbn [snd]; lia].
Qed.

Lemma nc_read_ok (b: list Z) (p nb T R cnt pc: Z) : T <= R -> 1 <= nb ->
  (if fbits b p (nb - 1) <? 2 * T - 1 - R then (fbits b p (nb - 1), p + nb - 1)
   else (if fbits b p nb >=? T then fbits b p nb - (2 * T - 1 - R) else fbits b p nb, p + nb)) = (cnt, pc) ->
  0 <= cnt /\ p <= pc.
Proof.
  intros HTR Hnb E. remember (2 * T - 1 - R) as mx eqn:Hmx. pose proof (fbits_range b p (nb - 1) ltac:(lia)). pose proof (fbits_range b p nb ltac:(lia)).
  destruct (fbits b p (nb - 1) <? mx) eqn:E1.
  - injection E as <- <-; lia.
  - destruct (fbits b p nb >=? T) eqn:E2; injection E as <- <-; [apply Z.geb_le in E2|]; lia.
Qed.

Lemma nc_next_ok (R1 T: Z) : (((R1 <? T) && (R1 <=? 1))%bool = false) -> R1 <? T = true ->
  2 ^ highbit R1 <= R1 /\ 1 <= highbit R1 + 1.
Proof.
  intros H1 H2. apply Bool.andb_false_iff in H1. destruct H1 as [H1|H1]; [congruence|].
  apply Z.leb_gt in H1. unfold highbit. pose proof (Z.log2_spec R1 ltac:(lia)). pose proof (Z.log2_nonneg R1). lia.
Qed.

Lemma nc_app_nn (l: list Z) (x: Z) : l ++ [x] <> nil.
Proof. intros Hn. apply app_eq_nil in Hn. destruct Hn as [_ Hn]. discriminate. Qed.

Ltac nc_body IH H HTR Hnb R T maxsv1 :=
  lazymatch type of H with context [match ?X with (_, _) => _ end] =>
    let cnt := fresh "cnt" in let pc := fresh "pc" in let Ec := fresh "Ec" in
    destruct X as [cnt pc] eqn:Ec;
    apply nc_read_ok in Ec; [|exact HTR|exact Hnb];
    cbv beta iota in H;
    let R1 := fresh "R1" in
    set (R1 := if cnt - 1 >=? 0 then _ else _) in H;
    let HR1 := fresh "HR1" in
    assert (HR1: nsum [cnt - 1] + R1 = R)
      by (unfold R1; pose proof (nsum_one (cnt - 1) ltac:(lia)); destruct (cnt - 1 >=? 0); lia);
    clearbody R1;
    let Estop := fresh "Estop" in let ET := fresh "ET" in let EL := fresh "EL" in
    destruct ((R1 <? T) && (R1 <=? 1))%bool eqn:Estop;
    [ inversion H; subst; rewrite nsum_app;
      split; [rewrite Forall_app; split; [assumption|apply Forall_cons; [lia|constructor]]|];
      split; [lia|]; split; [apply nc_app_nn|lia]
    | let Hnext := fresh "Hnext" in let Hge := fresh "Hge" in
      assert (Hnext: R1 <? T = true -> 2 ^ highbit R1 <= R1 /\ 1 <= highbit R1 + 1)
        by (intros; apply nc_next_ok with T; auto);
      assert (Hge: R1 <? T = false -> T <= R1) by (intros Hx; apply Z.ltb_ge in Hx; exact Hx);
      destruct (R1 <? T) eqn:ET; cbv beta iota in H;
      (destruct (Zlength _ >=? maxsv1) eqn:EL;
       [ inversion H; subst; rewrite nsum_app;
         split; [rewrite Forall_app; split; [assumption|apply Forall_cons; [lia|constructor]]|];
         split; [lia|]; split; [apply nc_app_nn|lia]
       | eapply IH in H;
         [ rewrite nsum_app in H; destruct H as (? & ? & ? & ?); split; [assumption|]; split; [lia|]; split; assumption
         | first [specialize (Hnext eq_refl); lia | specialize (Hge eq_refl); lia]
         | first [specialize (Hnext eq_refl); lia | lia]
         | lia
         | rewrite Forall_app; split; [assumption|apply Forall_cons; [lia|constructor]]
         | intros _; apply nc_app_nn ] ]) ]
  end.

Lemma ncount_loop_inv (fuel: nat) (b: list Z) (maxsv1 p R T nb: Z) (prev0: bool) (acc acc': list Z) (R' p': Z) :
  ncount_loop fuel b maxsv1 p R T nb prev0 acc = Some (acc', R', p') ->
  T <= R -> 1 <= nb -> 4 <= p -> Forall (fun c => -1 <= c) acc -> (prev0 = true -> acc <> nil) ->
  Forall (fun c => -1 <= c) acc' /\ nsum acc' + R' = nsum acc + R /\ acc' <> nil /\ 4 <= p'.
Proof.
  revert p R T nb prev0 acc. induction fuel as [|fuel IH]; intros p R T nb prev0 acc H HTR Hnb Hp Hacc Hpr;
    cbn [ncount_loop] in H; [discriminate|].
  destruct prev0.
  - destruct (ncount_zeros _ b p) as [z pz] eqn:Ez. cbv beta iota zeta in H.
    pose proof (ncount_zeros_pos (Z.to_nat (8 * Zlength b + 8)) b p) as Hpz. rewrite Ez in Hpz; simpl in Hpz.
    destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1) eqn:Es.
    + inversion H; subst. rewrite nsum_app, nsum_repeat0. split.
      * apply Forall_app; split; [assumption|]. apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia.
      * split; [lia|]. split; [|lia]. intros Hn. apply app_eq_nil in Hn. destruct Hn as [Hn _]. exact (Hpr eq_refl Hn).
    + remember (acc ++ repeat 0 (Z.to_nat z)) as acc1 eqn:Hacc1d.
      assert (Hacc1: Forall (fun c => -1 <= c) acc1).
      { subst acc1. apply Forall_app; split; [assumption|]. apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia. }
      assert (Hs1: nsum acc1 = nsum acc) by (subst acc1; rewrite nsum_app, nsum_repeat0; lia).
      assert (Hp1: 4 <= pz) by lia.
      rewrite <- Hs1. clear Hacc1d Ez Es Hpr Hs1.
      nc_body IH H HTR Hnb R T maxsv1.
  - cbv beta iota zeta in H. nc_body IH H HTR Hnb R T maxsv1.
Qed.

Lemma ncount_loop_c_inv (fuel: nat) (b: list Z) (n maxsv1 p R T nb: Z) (prev0: bool) (acc acc': list Z) (R' p': Z) :
  8 <= n -> ncount_loop_c fuel b n maxsv1 p R T nb prev0 acc = Some (acc', R', p') ->
  T <= R -> 1 <= nb -> 4 <= p -> Forall (fun c => -1 <= c) acc -> (prev0 = true -> acc <> nil) ->
  Forall (fun c => -1 <= c) acc' /\ nsum acc' + R' = nsum acc + R /\ acc' <> nil /\ 4 <= p'.
Proof.
  intros Hn. revert p R T nb prev0 acc. induction fuel as [|fuel IH]; intros p R T nb prev0 acc H HTR Hnb Hp Hacc Hpr;
    cbn [ncount_loop_c] in H; [discriminate|].
  destruct prev0.
  - destruct (zeros_c _ b n p 0) as [z pz] eqn:Ez. cbv beta iota zeta in H.
    pose proof (zeros_c_pos (Z.to_nat (8 * n + 8)) b n p 0 Hn Hp) as Hpz. rewrite Ez in Hpz; simpl in Hpz.
    destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1) eqn:Es.
    + inversion H; subst. rewrite nsum_app, nsum_repeat0. split.
      * apply Forall_app; split; [assumption|]. apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia.
      * split; [lia|]. split; [|lia]. intros Hn0. apply app_eq_nil in Hn0. destruct Hn0 as [Hn0 _]. exact (Hpr eq_refl Hn0).
    + remember (acc ++ repeat 0 (Z.to_nat z)) as acc1 eqn:Hacc1d.
      assert (Hacc1: Forall (fun c => -1 <= c) acc1).
      { subst acc1. apply Forall_app; split; [assumption|]. apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia. }
      assert (Hs1: nsum acc1 = nsum acc) by (subst acc1; rewrite nsum_app, nsum_repeat0; lia).
      pose proof (wrapP_ge4 n pz Hn Hpz) as Hw.
      rewrite <- Hs1. clear Hacc1d Ez Es Hpr Hs1.
      nc_body IH H HTR Hnb R T maxsv1.
  - cbv beta iota zeta in H. pose proof (wrapP_ge4 n p Hn Hp) as Hw. nc_body IH H HTR Hnb R T maxsv1.
Qed.

Lemma nc_finish (norm: list Z) (log maxsv: Z) : 5 <= log <= 15 -> Forall (fun c => -1 <= c) norm ->
  nsum norm + 1 = nsum nil + (2 ^ log + 1) -> norm <> nil -> Zlength norm <= maxsv + 1 ->
  ncount_ok norm log maxsv.
Proof.
  intros Hl Hf Hs Hne Hz. assert (Hs': nsum norm = 2 ^ log) by (unfold nsum in Hs at 2; simpl in Hs; lia).
  destruct (nsum_bound norm Hf) as [Hb _]. rewrite Hs' in Hb.
  split; [exact Hl|]. split.
  - split; [|exact Hz]. destruct norm as [|c l]; [congruence|]. rewrite Zlength_correct. simpl length. lia.
  - split; [exact Hb|]. exact Hs'.
Qed.

Lemma ncount_res_ok : NCOUNT_RES_OK.
Proof.
  intros s maxsv norm log size Hm H. unfold ncount_res in H.
  destruct (Zlength s <? 8) eqn:E8.
  - unfold read_ncount in H.
    set (b := s ++ repeat 0 (Z.to_nat (8 - Zlength s))) in H.
    destruct (Zlength b =? 0); [discriminate|].
    set (lg := fbits b 0 4 + FSE_MIN_TABLELOG) in H.
    destruct (lg >? FSE_TABLELOG_ABSOLUTE_MAX) eqn:El; [discriminate|].
    destruct (ncount_loop _ b (maxsv + 1) 4 (2 ^ lg + 1) (2 ^ lg) (lg + 1) false nil) as [[[nm r] pp]|] eqn:Eloop;
      [|discriminate].
    destruct (negb (r =? 1)) eqn:Er; [discriminate|].
    destruct (Zlength nm >? maxsv + 1) eqn:Ez; [discriminate|].
    destruct ((pp + 7) / 8 >? Zlength b) eqn:Eb; [discriminate|].
    destruct ((pp + 7) / 8 >? Zlength s) eqn:Es; [discriminate|].
    injection H as <- <- <-.
    assert (Hlg: 5 <= lg) by (unfold lg, FSE_MIN_TABLELOG; pose proof (fbits_range b 0 4 ltac:(lia)); lia).
    apply ncount_loop_inv in Eloop; [|lia|lia|lia|constructor|discriminate].
    destruct Eloop as (Hf & Hs & Hne & Hp).
    apply Bool.negb_false_iff, Z.eqb_eq in Er. subst r.
    rewrite Z.gtb_ltb in El, Ez, Es. apply Z.ltb_ge in El. apply Z.ltb_ge in Ez. apply Z.ltb_ge in Es.
    unfold FSE_TABLELOG_ABSOLUTE_MAX in *.
    split; [apply nc_finish; auto; lia|].
    assert (Hd: 1 <= (pp + 7) / 8) by (apply Z.div_le_lower_bound; lia). exact (conj Hd Es).
  - unfold ncount_c in H.
    set (lg := fbits s 0 4 + FSE_MIN_TABLELOG) in H.
    destruct (lg >? FSE_TABLELOG_ABSOLUTE_MAX) eqn:El; [discriminate|].
    destruct (ncount_loop_c _ s (Zlength s) (maxsv + 1) 4 (2 ^ lg + 1) (2 ^ lg) (lg + 1) false nil)
      as [[[nm r] pp]|] eqn:Eloop; [|discriminate].
    destruct (negb (r =? 1)) eqn:Er; [discriminate|].
    destruct (Zlength nm >? maxsv + 1) eqn:Ez; [discriminate|].
    destruct ((pp + 7) / 8 >? Zlength s) eqn:Es; [discriminate|].
    injection H as <- <- <-.
    apply Z.ltb_ge in E8.
    assert (Hlg: 5 <= lg) by (unfold lg, FSE_MIN_TABLELOG; pose proof (fbits_range s 0 4 ltac:(lia)); lia).
    apply ncount_loop_c_inv in Eloop; [|lia|lia|lia|lia|constructor|discriminate].
    destruct Eloop as (Hf & Hs & Hne & Hp).
    apply Bool.negb_false_iff, Z.eqb_eq in Er. subst r.
    rewrite Z.gtb_ltb in El, Ez, Es. apply Z.ltb_ge in El. apply Z.ltb_ge in Ez. apply Z.ltb_ge in Es.
    unfold FSE_TABLELOG_ABSOLUTE_MAX in *.
    split; [apply nc_finish; auto; lia|].
    assert (Hd: 1 <= (pp + 7) / 8) by (apply Z.div_le_lower_bound; lia). exact (conj Hd Es).
Qed.

(* ---------- facts for the exported wrappers FSE_readNCount and HUF_readStats_wksp ---------- *)

(* ---------- helpers of ncount_model_c (prefix ncmc_) ---------- *)

Lemma ncmc_lv_app (l1 l2: list Z) : le_value l2 = 0 -> le_value (l1 ++ l2) = le_value l1.
Proof. intros H. induction l1; simpl; auto. rewrite IHl1; lia. Qed.

Lemma ncmc_lv_rep (i j m: nat) : le_value (firstn i (skipn j (repeat 0 m))) = 0.
Proof.
  revert i j; induction m; intros i j; simpl.
  - destruct j; simpl; rewrite firstn_nil; auto.
  - destruct j; simpl.
    + destruct i; simpl; auto. specialize (IHm i O). simpl in IHm. lia.
    + apply IHm.
Qed.

Lemma ncmc_fbits_pad (s: list Z) (m: nat) (p k: Z) : fbits (s ++ repeat 0 m) p k = fbits s p k.
Proof.
  unfold fbits, slice. rewrite skipn_app, firstn_app, ncmc_lv_app; auto. apply ncmc_lv_rep.
Qed.

Lemma ncmc_fbits_nonneg (b: list Z) (p k: Z) : 0 <= k -> 0 <= fbits b p k.
Proof. intros. unfold fbits. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma ncmc_fbits3_lt (b: list Z) (p: Z) : 0 <= p -> fbits b p 2 = 3 -> p < 8 * Zlength b.
Proof.
  intros Hp H. destruct (Z_lt_le_dec p (8 * Zlength b)) as [|Hle]; auto. exfalso.
  unfold fbits, slice in H. rewrite skipn_all2 in H.
  - rewrite firstn_nil in H. simpl in H. discriminate.
  - rewrite Zlength_correct in Hle. assert (Z.of_nat (length b) <= p / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma ncmc_nz_ge (f: nat) (b: list Z) (p: Z) : p <= snd (ncount_zeros f b p).
Proof.
  revert p; induction f; intros p; simpl; [lia|].
  destruct (fbits b p 2 =? 3); [|simpl; lia].
  specialize (IHf (p + 2)). destruct (ncount_zeros f b (p + 2)); simpl in *; lia.
Qed.

Lemma ncmc_nz_gt (f: nat) (b: list Z) (p: Z) : (0 < f)%nat -> p + 2 <= snd (ncount_zeros f b p).
Proof.
  destruct f; intros; [lia|]. simpl.
  destruct (fbits b p 2 =? 3); [|simpl; lia].
  pose proof (ncmc_nz_ge f b (p + 2)). destruct (ncount_zeros f b (p + 2)); simpl in *; lia.
Qed.

Lemma ncmc_nz_fuel (b: list Z) (f g: nat) (p: Z) : 0 <= p -> (0 < f)%nat -> (0 < g)%nat ->
  8 * Zlength b + 2 <= 2 * Z.of_nat f + p -> 8 * Zlength b + 2 <= 2 * Z.of_nat g + p ->
  ncount_zeros f b p = ncount_zeros g b p.
Proof.
  revert g p; induction f; intros g p Hp Hf Hg H1 H2; [lia|]. destruct g; [lia|].
  simpl. destruct (fbits b p 2 =? 3) eqn:E; auto.
  apply Z.eqb_eq in E. apply ncmc_fbits3_lt in E; auto.
  rewrite (IHf g (p + 2)); auto; lia.
Qed.

Lemma ncmc_nz_congr (f: nat) (b b': list Z) (p: Z) :
  (forall q k, 0 <= q -> fbits b q k = fbits b' q k) -> 0 <= p ->
  ncount_zeros f b p = ncount_zeros f b' p.
Proof.
  intros Hb. revert p; induction f; intros p Hp; simpl; auto.
  rewrite Hb by lia. destruct (fbits b' p 2 =? 3); auto. rewrite IHf by lia. auto.
Qed.

Lemma ncmc_loop_congr (f: nat) (b b': list Z) (maxsv1 p rem thr nb: Z) (prev0: bool) (acc: list Z) :
  (forall q k, 0 <= q -> fbits b q k = fbits b' q k) -> Zlength b <= Zlength b' -> 0 <= p -> 1 <= nb ->
  ncount_loop f b maxsv1 p rem thr nb prev0 acc = ncount_loop f b' maxsv1 p rem thr nb prev0 acc.
Proof.
  intros Hb Hl. revert p rem thr nb prev0 acc; induction f; intros p rem thr nb prev0 acc Hp Hnb; simpl; auto.
  assert (Hz: ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p
              = ncount_zeros (Z.to_nat (8 * Zlength b' + 8)) b' p).
  { rewrite (ncmc_nz_fuel b _ (Z.to_nat (8 * Zlength b' + 8))) by (pose proof (Zlength_nonneg b); lia).
    apply ncmc_nz_congr; auto. }
  rewrite Hz.
  pose proof (ncmc_nz_ge (Z.to_nat (8 * Zlength b' + 8)) b' p) as Hge.
  destruct (ncount_zeros (Z.to_nat (8 * Zlength b' + 8)) b' p) as [z pz]. simpl in Hge.
  assert (Hstep: forall a q, 0 <= q -> p <= q ->
    (let max := 2 * thr - 1 - rem in
     let low := fbits b q (nb - 1) in
     let '(count, p0) := if low <? max then (low, q + nb - 1)
       else let c := fbits b q nb in ((if c >=? thr then c - max else c), q + nb) in
     let count := count - 1 in
     let remaining := if count >=? 0 then rem - count else rem + count in
     let acc := a ++ [count] in
     let prev0 := count =? 0 in
     if andb (remaining <? thr) (remaining <=? 1) then Some (acc, remaining, p0) else
     let '(nbBits, threshold) := if remaining <? thr then (highbit remaining + 1, 2 ^ highbit remaining)
       else (nb, thr) in
     if Zlength acc >=? maxsv1 then Some (acc, remaining, p0) else
     ncount_loop f b maxsv1 p0 remaining threshold nbBits prev0 acc) =
    (let max := 2 * thr - 1 - rem in
     let low := fbits b' q (nb - 1) in
     let '(count, p0) := if low <? max then (low, q + nb - 1)
       else let c := fbits b' q nb in ((if c >=? thr then c - max else c), q + nb) in
     let count := count - 1 in
     let remaining := if count >=? 0 then rem - count else rem + count in
     let acc := a ++ [count] in
     let prev0 := count =? 0 in
     if andb (remaining <? thr) (remaining <=? 1) then Some (acc, remaining, p0) else
     let '(nbBits, threshold) := if remaining <? thr then (highbit remaining + 1, 2 ^ highbit remaining)
       else (nb, thr) in
     if Zlength acc >=? maxsv1 then Some (acc, remaining, p0) else
     ncount_loop f b' maxsv1 p0 remaining threshold nbBits prev0 acc)).
  { intros a q Hq _. rewrite !(Hb q) by lia. cbv zeta.
    destruct (fbits b' q (nb - 1) <? 2 * thr - 1 - rem); [|destruct (fbits b' q nb >=? thr)];
    repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => destruct c end);
    try reflexivity; apply IHf; unfold highbit; pose proof (ncmc_fbits_nonneg b' q (nb - 1));
    try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia. }
  destruct prev0; simpl.
  - destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1); auto. apply Hstep; lia.
  - apply Hstep; lia.
Qed.

Lemma ncmc_loop_mono (f: nat) (b: list Z) (maxsv1 p rem thr nb: Z) (prev0: bool) (acc a: list Z) (r pf: Z) :
  ncount_loop f b maxsv1 p rem thr nb prev0 acc = Some (a, r, pf) -> 1 <= nb -> p <= pf.
Proof.
  revert p rem thr nb prev0 acc; induction f; intros p rem thr nb prev0 acc H Hnb; simpl in H; [discriminate|].
  destruct prev0.
  - pose proof (ncmc_nz_ge (Z.to_nat (8 * Zlength b + 8)) b p) as Hge.
    destruct (ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p) as [z pz]; simpl in Hge.
    destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1); [injection H; intros; lia|].
    revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => destruct c end);
    intros H; try (injection H; intros; lia); eapply IHf in H; try lia;
    unfold highbit; try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia.
  - revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => destruct c end);
    intros H; try (injection H; intros; lia); eapply IHf in H; try lia;
    unfold highbit; try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia.
Qed.

Lemma ncmc_reps (k: nat) (b: list Z) (p: Z) :
  0 <= reps k b p <= Z.of_nat k /\ (forall i, 0 <= i < reps k b p -> fbits b (p + 2 * i) 2 = 3) /\
  (reps k b p < Z.of_nat k -> fbits b (p + 2 * reps k b p) 2 <> 3).
Proof.
  revert p; induction k; intros p; simpl.
  - split; [lia|]. split; intros; lia.
  - destruct (fbits b p 2 =? 3) eqn:E.
    + apply Z.eqb_eq in E. destruct (IHk (p + 2)) as (H1 & H2 & H3). split; [lia|]. split.
      * intros i Hi. destruct (Z.eq_dec i 0); [subst; rewrite Z.add_0_r; auto|].
        replace (p + 2 * i) with (p + 2 + 2 * (i - 1)) by lia. apply H2; lia.
      * intros Hlt. replace (p + 2 * (1 + reps k b (p + 2))) with (p + 2 + 2 * reps k b (p + 2)) by lia.
        apply H3; lia.
    + apply Z.eqb_neq in E. split; [lia|]. split; intros; [lia|]. rewrite Z.add_0_r; auto.
Qed.

Lemma ncmc_nz_prefix (j f: nat) (b: list Z) (p: Z) :
  (forall i, 0 <= i < Z.of_nat j -> fbits b (p + 2 * i) 2 = 3) ->
  ncount_zeros (j + f) b p =
  let '(z, p') := ncount_zeros f b (p + 2 * Z.of_nat j) in (3 * Z.of_nat j + z, p').
Proof.
  revert p; induction j; intros p H; cbn [ncount_zeros Nat.add].
  - simpl Z.of_nat. rewrite Z.add_0_r. destruct (ncount_zeros f b p); auto.
  - replace (fbits b p 2) with 3 by (rewrite <- (H 0) by lia; f_equal; lia). simpl Z.eqb. cbv iota.
    rewrite IHj.
    + replace (p + 2 + 2 * Z.of_nat j) with (p + 2 * Z.of_nat (S j)) by lia.
      destruct (ncount_zeros f b (p + 2 * Z.of_nat (S j))). f_equal; lia.
    + intros i Hi. replace (p + 2 + 2 * i) with (p + 2 * (i + 1)) by lia. apply H; lia.
Qed.

Lemma ncmc_zeros_c (G F: nat) (b: list Z) (p z: Z) :
  0 <= p -> (0 < F)%nat -> 8 * Zlength b + 2 <= 2 * Z.of_nat F + p ->
  8 * Zlength b + 26 <= 24 * Z.of_nat G + p -> snd (ncount_zeros F b p) <= 8 * Zlength b ->
  zeros_c G b (Zlength b) p z = (z + fst (ncount_zeros F b p), snd (ncount_zeros F b p)).
Proof.
  revert F p z; induction G; intros F p z Hp HF HF2 HG Hs; pose proof (ncmc_nz_gt F b p HF) as Hgt; [lia|].
  pose proof (Zlength_nonneg b) as Hn.
  cbn [zeros_c]. unfold wrapP. replace (p <? 8 * Zlength b) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (ncmc_reps 12 b p) as (Hj & Hall & Hlast).
  remember (reps 12 b p) as j eqn:Ej. clear Ej.
  assert (HF1: Z.of_nat (Z.to_nat (8 * Zlength b + 8)) = 8 * Zlength b + 8) by lia.
  remember (Z.to_nat (8 * Zlength b + 8)) as F1 eqn:EF1. clear EF1.
  destruct (Z.eqb_spec j 12) as [->|Hne].
  - rewrite (ncmc_nz_fuel b F (12 + F1)) in Hs |- * by lia.
    rewrite (ncmc_nz_prefix 12 F1 b p) in Hs |- * by (intros; apply Hall; lia).
    change (Z.of_nat 12) with 12 in *. replace (p + 2 * 12) with (p + 24) in * by lia.
    pose proof (ncmc_nz_gt F1 b (p + 24)) as Hgt1.
    destruct (ncount_zeros F1 b (p + 24)) as [z1 p1] eqn:E1. cbn [fst snd] in *.
    rewrite (IHG F1); rewrite ?E1; cbn [fst snd]; try lia. f_equal; lia.
  - assert (Hjn: j = Z.of_nat (Z.to_nat j)) by lia.
    rewrite (ncmc_nz_fuel b F (Z.to_nat j + S F1)) in Hs |- * by lia.
    rewrite (ncmc_nz_prefix (Z.to_nat j) (S F1) b p) in Hs |- * by (intros; apply Hall; lia).
    rewrite <- Hjn in *. simpl.
    destruct (Z.eqb_spec (fbits b (p + 2 * j) 2) 3) as [E|E]; [exfalso; apply Hlast; auto; lia|].
    simpl. f_equal; lia.
Qed.

Lemma ncmc_loop_c (f: nat) (b: list Z) (maxsv1 p rem thr nb: Z) (prev0: bool) (acc a: list Z) (r pf: Z) :
  ncount_loop f b maxsv1 p rem thr nb prev0 acc = Some (a, r, pf) -> pf <= 8 * Zlength b -> 0 <= p -> 2 <= nb ->
  ncount_loop_c f b (Zlength b) maxsv1 p rem thr nb prev0 acc = Some (a, r, pf).
Proof.
  revert p rem thr nb prev0 acc; induction f; intros p rem thr nb prev0 acc H Hpf Hp Hnb; [discriminate|].
  cbn [ncount_loop ncount_loop_c] in H |- *.
  pose proof (Zlength_nonneg b) as Hn.
  destruct prev0.
  - pose proof (ncmc_nz_gt (Z.to_nat (8 * Zlength b + 8)) b p ltac:(lia)) as Hgt.
    assert (Hz: snd (ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p) <= pf).
    { destruct (ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p) as [z pz]; cbn [snd] in *.
      destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1); [injection H; intros; lia|].
      revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end);
      intros H; try (injection H; intros; lia); eapply ncmc_loop_mono in H; try lia;
      unfold highbit; try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia. }
    rewrite (ncmc_zeros_c _ (Z.to_nat (8 * Zlength b + 8))) by lia.
    destruct (ncount_zeros (Z.to_nat (8 * Zlength b + 8)) b p) as [z q]; cbn [fst snd] in *.
    rewrite Z.add_0_l.
    destruct (Zlength (acc ++ repeat 0 (Z.to_nat z)) >=? maxsv1); [exact H|].
    assert (Hq: 0 <= q) by lia. clear Hz Hgt.
    revert H Hq; generalize (acc ++ repeat 0 (Z.to_nat z)); intros acc0 H Hq.
    assert (q + 1 <= pf).
    { clear IHf; revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end);
      intros H; try (injection H; intros; lia); eapply ncmc_loop_mono in H; try lia;
      unfold highbit; try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia. }
    unfold wrapP; replace (q <? 8 * Zlength b) with true by (symmetry; apply Z.ltb_lt; lia).
    revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end); intros H; try exact H; repeat match goal with
     | E: andb _ _ = false |- _ => apply andb_false_iff in E; destruct E as [E|E]
     | E: andb _ _ = true |- _ => apply andb_true_iff in E; destruct E
     | E: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in E
     | E: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in E
     | E: Z.leb _ _ = true |- _ => apply Z.leb_le in E
     | E: Z.leb _ _ = false |- _ => apply Z.leb_gt in E
     | E: Z.geb _ _ = _ |- _ => rewrite Z.geb_leb in E
     end;
    eapply IHf; try exact H; try lia;
    unfold highbit; match goal with |- context [Z.log2 ?x] =>
      pose proof (Z.log2_le_mono 2 x ltac:(lia)) as HL; change (Z.log2 2) with 1 in HL end; lia.
  - assert (p + 1 <= pf).
    { clear IHf; revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end);
      intros H; try (injection H; intros; lia); eapply ncmc_loop_mono in H; try lia;
      unfold highbit; try (match goal with |- context [Z.log2 ?x] => pose proof (Z.log2_nonneg x) end); lia. }
    unfold wrapP; replace (p <? 8 * Zlength b) with true by (symmetry; apply Z.ltb_lt; lia).
    revert H; repeat (cbv beta iota zeta; match goal with |- context [if ?c then _ else _] => lazymatch c with context [if _ then _ else _] => fail | _ => destruct c eqn:? end end); intros H; try exact H; repeat match goal with
     | E: andb _ _ = false |- _ => apply andb_false_iff in E; destruct E as [E|E]
     | E: andb _ _ = true |- _ => apply andb_true_iff in E; destruct E
     | E: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in E
     | E: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in E
     | E: Z.leb _ _ = true |- _ => apply Z.leb_le in E
     | E: Z.leb _ _ = false |- _ => apply Z.leb_gt in E
     | E: Z.geb _ _ = _ |- _ => rewrite Z.geb_leb in E
     end;
    eapply IHf; try exact H; try lia;
    unfold highbit; match goal with |- context [Z.log2 ?x] =>
      pose proof (Z.log2_le_mono 2 x ltac:(lia)) as HL; change (Z.log2 2) with 1 in HL end; lia.
Qed.

(* the model's reading is C's whenever the model reads the description, for a window of any length *)
Definition NCOUNT_MODEL_C : Prop :=
  forall (s: list Z) (maxsv: Z) x, 0 <= maxsv <= 255 ->
  read_ncount s maxsv = Some x -> ncount_res s maxsv = Some x.

Lemma ncount_model_c : NCOUNT_MODEL_C.
Proof.
  intros s maxsv x Hm H. unfold ncount_res.
  pose proof (Zlength_nonneg s) as Hn.
  destruct (Z.ltb_spec (Zlength s) 8) as [Hlt|Hge].
  - set (s' := s ++ repeat 0 (Z.to_nat (8 - Zlength s))).
    assert (Hl': Zlength s' = 8).
    { unfold s'. rewrite Zlength_app, (Zlength_correct (repeat _ _)), repeat_length. lia. }
    assert (Hb: forall q k, 0 <= q -> fbits s q k = fbits s' q k).
    { intros. unfold s'. rewrite ncmc_fbits_pad. auto. }
    unfold read_ncount in H |- *.
    rewrite Hl'. simpl (8 =? 0). cbv iota.
    destruct (Zlength s =? 0); [discriminate|].
    rewrite <- (Hb 0 4) by lia.
    destruct (fbits s 0 4 + FSE_MIN_TABLELOG >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
    rewrite <- (ncmc_loop_congr _ s s') by (auto; try lia; pose proof (ncmc_fbits_nonneg s 0 4); unfold FSE_MIN_TABLELOG; lia).
    destruct (ncount_loop _ s _ _ _ _ _ _ _) as [[[norm rem] p]|]; [|discriminate].
    destruct (negb (rem =? 1)); [discriminate|].
    destruct (Zlength norm >? maxsv + 1); [discriminate|].
    destruct (Z.gtb_spec ((p + 7) / 8) (Zlength s)); [discriminate|].
    replace ((p + 7) / 8 >? 8) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    replace ((p + 7) / 8 >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    exact H.
  - unfold ncount_c. unfold read_ncount in H.
    replace (Zlength s =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
    destruct (fbits s 0 4 + FSE_MIN_TABLELOG >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
    destruct (ncount_loop _ s _ _ _ _ _ _ _) as [[[norm rem] p]|] eqn:EL; [|discriminate].
    destruct (negb (rem =? 1)) eqn:E1; [discriminate|].
    destruct (Zlength norm >? maxsv + 1) eqn:E2; [discriminate|].
    destruct (Z.gtb_spec ((p + 7) / 8) (Zlength s)); [discriminate|].
    cbv zeta. rewrite (ncmc_loop_c _ _ _ _ _ _ _ _ _ _ _ _ EL); try lia.
    + rewrite E1, E2.
      replace ((p + 7) / 8 >? Zlength s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
      exact H.
    + assert (p < 8 * Zlength s + 1); [|lia].
      assert (Hd: (p + 7) / 8 * 8 > p + 7 - 8) by (pose proof (Z.mul_div_le (p + 7) 8); pose proof (Z.mod_pos_bound (p + 7) 8); pose proof (Z.div_mod (p + 7) 8); lia).
      lia.
    + pose proof (ncmc_fbits_nonneg s 0 4). unfold FSE_MIN_TABLELOG. lia.
Qed.

(* a tree description C accepts (statsWksp of 219 U32) is a well-formed table within the window *)
Definition HUF_RES_OK : Prop :=
  forall res (s: list Z) (ht: huf_table) (size: Z), bytes_ok s ->
  huf_parse_res res 219 s = Some (ht, size) ->
  1 <= size <= Zlength s /\ huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\
  Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht).

(* ---------- huf_res_ok: helpers ---------- *)

Fixpoint hro_sum {A} (f: A -> Z) (l: list A) : Z :=
  match l with nil => 0 | x :: l' => f x + hro_sum f l' end.

Lemma hro_sum_app {A} (f: A -> Z) l1 l2 : hro_sum f (l1 ++ l2) = hro_sum f l1 + hro_sum f l2.
Proof. induction l1 as [|x l1 IH]; simpl; [lia|]. rewrite IH. lia. Qed.

Lemma hro_sum_ext {A} (f g: A -> Z) l : (forall x, In x l -> f x = g x) -> hro_sum f l = hro_sum g l.
Proof.
  induction l as [|x l IH]; simpl; intros H; auto.
  rewrite H by auto. rewrite IH by auto. auto.
Qed.

Lemma hro_sum_plus {A} (f g: A -> Z) l : hro_sum (fun x => f x + g x) l = hro_sum f l + hro_sum g l.
Proof. induction l as [|x l IH]; simpl; [lia|]. rewrite IH. lia. Qed.

Lemma hro_sum_swap {A B} (f: A -> B -> Z) la lb :
  hro_sum (fun a => hro_sum (fun b => f a b) lb) la = hro_sum (fun b => hro_sum (fun a => f a b) la) lb.
Proof.
  induction la as [|a la IH]; simpl.
  - induction lb as [|b lb IHb]; simpl; lia.
  - rewrite IH. rewrite hro_sum_plus. reflexivity.
Qed.

Lemma hro_sum_nonneg {A} (f: A -> Z) l : (forall x, In x l -> 0 <= f x) -> 0 <= hro_sum f l.
Proof.
  induction l as [|x l IH]; simpl; intros H; [lia|].
  specialize (H x (or_introl eq_refl)) as Hx. assert (0 <= hro_sum f l) by (apply IH; auto). lia.
Qed.

Lemma hro_sum_in_le {A} (f: A -> Z) l y : (forall x, In x l -> 0 <= f x) -> In y l -> f y <= hro_sum f l.
Proof.
  induction l as [|x l IH]; simpl; intros H Hy; [contradiction|].
  destruct Hy as [<-|Hy].
  - assert (0 <= hro_sum f l) by (apply hro_sum_nonneg; auto). lia.
  - specialize (H x (or_introl eq_refl)) as Hx. assert (f y <= hro_sum f l) by (apply IH; auto). lia.
Qed.

Lemma hro_len_flat_map {A B} (f: A -> list B) l :
  Z.of_nat (length (flat_map f l)) = hro_sum (fun x => Z.of_nat (length (f x))) l.
Proof. induction l as [|x l IH]; simpl; auto. rewrite app_length, Nat2Z.inj_add, IH. auto. Qed.

Lemma hro_sum_seq_nth (G: Z -> Z) (ws: list Z) :
  hro_sum (fun s => G (nth s ws 0)) (seq 0 (length ws)) = hro_sum G ws.
Proof.
  induction ws as [|x ws IH]; simpl; auto.
  rewrite <- seq_shift. f_equal. rewrite <- IH.
  clear IH. generalize (seq 0 (length ws)). intros l. induction l as [|a l IHl]; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma hro_fold_total (l: list Z) :
  fold_right (fun w acc => Z.shiftr (2 ^ w) 1 + acc) 0 l = hro_sum (fun w => Z.shiftr (2 ^ w) 1) l.
Proof. induction l as [|x l IH]; simpl; auto. rewrite IH. auto. Qed.

Lemma hro_shiftr (x: Z) : Z.shiftr (2 ^ x) 1 = if 1 <=? x then 2 ^ (x - 1) else 0.
Proof.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  destruct (Z.leb_spec 1 x).
  - replace x with (x - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
    apply Z.div_mul. lia.
  - destruct (Z.eq_dec x 0) as [->|Hx]; [reflexivity|].
    rewrite Z.pow_neg_r by lia. reflexivity.
Qed.

Lemma hro_sum_range (x: Z) (n: nat) :
  hro_sum (fun w => if x =? w then Z.of_nat (Z.to_nat (2 ^ (w - 1))) else 0) (map Z.of_nat (seq 1 n))
  = if andb (1 <=? x) (x <=? Z.of_nat n) then 2 ^ (x - 1) else 0.
Proof.
  induction n as [|n IH].
  - simpl. destruct (1 <=? x) eqn:E1, (x <=? 0) eqn:E2; simpl; auto.
    apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - rewrite seq_S, map_app, hro_sum_app, IH. cbn [hro_sum map].
    rewrite !Nat2Z.inj_succ. replace (Z.of_nat (1 + n)) with (Z.succ (Z.of_nat n)) by lia.
    assert (Hp: 0 <= 2 ^ (x - 1)) by (apply Z.pow_nonneg; lia).
    destruct (Z.eqb_spec x (Z.succ (Z.of_nat n))) as [Hx|Hx].
    + subst x. rewrite Z2Nat.id by (apply Z.pow_nonneg; lia).
      destruct (Z.leb_spec 1 (Z.succ (Z.of_nat n))), (Z.leb_spec (Z.succ (Z.of_nat n)) (Z.of_nat n)),
               (Z.leb_spec (Z.succ (Z.of_nat n)) (Z.succ (Z.of_nat n))); cbn [andb]; lia.
    + destruct (Z.leb_spec 1 x), (Z.leb_spec x (Z.of_nat n)), (Z.leb_spec x (Z.succ (Z.of_nat n)));
        cbn [andb]; lia.
Qed.

(* the length of huf_cells: the sum over the symbols of weight 1..log of 2^(w-1) *)
Lemma hro_cells_len (ht: huf_table) :
  0 <= ht_log ht -> Forall (fun x => x <= ht_log ht) (ht_weights ht) ->
  Z.of_nat (length (huf_cells ht)) = hro_sum (fun w => Z.shiftr (2 ^ w) 1) (ht_weights ht).
Proof.
  intros Hlog Hle. unfold huf_cells.
  set (ws := ht_weights ht) in *. set (log := ht_log ht) in *.
  rewrite hro_len_flat_map.
  erewrite hro_sum_ext.
  2:{ intros w _. rewrite hro_len_flat_map.
      erewrite hro_sum_ext.
      2:{ intros s _.
          instantiate (1 := fun s => (fun x => if x =? w then Z.of_nat (Z.to_nat (2 ^ (w - 1))) else 0) (nth s ws 0)).
          simpl. destruct (nth s ws 0 =? w); simpl; auto. rewrite repeat_length. auto. }
      rewrite hro_sum_seq_nth. reflexivity. }
  rewrite hro_sum_swap.
  apply hro_sum_ext. intros x Hx.
  rewrite hro_sum_range, hro_shiftr.
  rewrite Forall_forall in Hle. specialize (Hle x Hx).
  rewrite Z2Nat.id by lia.
  destruct (Z.leb_spec 1 x), (Z.leb_spec x log); simpl; auto; lia.
Qed.

Lemma hro_cells_forall (ht: huf_table) :
  Forall (fun c => 0 <= fst c < Zlength (ht_weights ht) /\ 1 <= snd c <= ht_log ht) (huf_cells ht).
Proof.
  unfold huf_cells. rewrite Forall_forall. intros c Hc.
  apply in_flat_map in Hc. destruct Hc as [w [Hw Hc]].
  apply in_map_iff in Hw. destruct Hw as [k [<- Hk]]. apply in_seq in Hk.
  apply in_flat_map in Hc. destruct Hc as [s [Hs Hc]]. apply in_seq in Hs.
  destruct (nth s (ht_weights ht) 0 =? Z.of_nat k); [|contradiction].
  apply repeat_spec in Hc. subst c. simpl. rewrite Zlength_correct. lia.
Qed.

Lemma hro_parse fw b ht size :
  (forall ws0 sz, huf_desc_weights_w fw b = Some (ws0, sz) ->
     Zlength ws0 <= 255 /\ 1 <= sz <= Zlength b /\ (Forall (fun w => 0 <= w) ws0 \/ True)) ->
  huf_parse_w fw b = Some (ht, size) ->
  1 <= size <= Zlength b /\ huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\
  (forall ws0 sz, huf_desc_weights_w fw b = Some (ws0, sz) -> Forall (fun w => 0 <= w) ws0 ->
     Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht)).
Proof.
  intros Hd. unfold huf_parse_w.
  destruct (huf_desc_weights_w fw b) as [[ws0 sz]|] eqn:D; [|discriminate].
  destruct (Hd ws0 sz eq_refl) as [Hl0 [Hsz _]]. clear Hd.
  rewrite hro_fold_total.
  set (total := hro_sum (fun w => Z.shiftr (2 ^ w) 1) ws0).
  destruct (existsb (fun w => w >? HUF_TABLELOG_MAX) ws0) eqn:E1; [discriminate|].
  destruct (total =? 0) eqn:E2; [discriminate|].
  destruct (highbit total + 1 >? HUF_TABLELOG_MAX) eqn:E3; [discriminate|].
  match goal with |- context [if negb ?c then _ else _] => destruct c eqn:E4 end; [|discriminate].
  simpl negb. cbv iota.
  match goal with |- context [if orb ?a ?c then _ else _] => destruct (orb a c) eqn:E5 end; [discriminate|].
  intros H; inversion H; subst; clear H.
  assert (Hnn: forall x, In x ws0 -> 0 <= Z.shiftr (2 ^ x) 1).
  { intros x _. apply Z.shiftr_nonneg. apply Z.pow_nonneg. lia. }
  assert (Ht0: 0 <= total) by (apply hro_sum_nonneg; auto).
  apply Z.eqb_neq in E2.
  rewrite Z.gtb_ltb in E3. apply Z.ltb_ge in E3. unfold HUF_TABLELOG_MAX in E3.
  apply Z.eqb_eq in E4.
  unfold highbit in *.
  set (log := Z.log2 total + 1) in *.
  pose proof (Z.log2_spec total ltac:(lia)) as [_ Hlt].
  replace (2 ^ Z.succ (Z.log2 total)) with (2 ^ log) in Hlt by (unfold log; f_equal; lia).
  pose proof (Z.log2_nonneg total) as Hl2.
  set (rest := 2 ^ log - total) in *.
  assert (Hr: 0 < rest < 2 ^ log) by (unfold rest; lia).
  pose proof (Z.log2_nonneg rest) as Hlr.
  assert (Hle0: forall x, In x ws0 -> x <= log).
  { intros x Hx.
    assert (H12: x <= 12).
    { destruct (Z.leb_spec x 12) as [|Hgt]; auto.
      assert (existsb (fun w => w >? HUF_TABLELOG_MAX) ws0 = true).
      { apply existsb_exists. exists x. split; auto. unfold HUF_TABLELOG_MAX. apply Z.gtb_lt. lia. }
      congruence. }
    destruct (Z.leb_spec x 0); [lia|].
    pose proof (hro_sum_in_le _ ws0 x Hnn Hx) as Hin. fold total in Hin. cbv beta in Hin.
    rewrite hro_shiftr in Hin. destruct (Z.leb_spec 1 x); [|lia].
    assert (Hpl: 2 ^ (x - 1) < 2 ^ log) by lia.
    apply Z.pow_lt_mono_r_iff in Hpl; lia. }
  assert (Hlw: Z.log2 rest + 1 <= log).
  { assert (Hpl: 2 ^ Z.log2 rest < 2 ^ log) by lia.
    apply Z.pow_lt_mono_r_iff in Hpl; lia. }
  set (ws := ws0 ++ [Z.log2 rest + 1]).
  assert (Hle: Forall (fun x => x <= log) ws).
  { apply Forall_forall. intros x Hx. unfold ws in Hx. apply in_app_or in Hx.
    destruct Hx as [Hx|[<-|[]]]; auto. }
  assert (Hlen: Z.of_nat (length (huf_cells {| ht_log := log; ht_weights := ws |})) = 2 ^ log).
  { rewrite hro_cells_len by (simpl; auto; lia). simpl.
    unfold ws. rewrite hro_sum_app. fold total. simpl.
    rewrite hro_shiftr. destruct (Z.leb_spec 1 (Z.log2 rest + 1)); [|lia].
    replace (Z.log2 rest + 1 - 1) with (Z.log2 rest) by lia. unfold rest in *. lia. }
  assert (Hwl: Zlength ws = Zlength ws0 + 1) by (unfold ws; rewrite Zlength_app; reflexivity).
  assert (Hr1: 2 <= Zlength ws).
  { fold ws in E5. apply orb_false_iff in E5. destruct E5 as [E5 _]. apply Z.ltb_ge in E5.
    pose proof (filter_length_le (fun w => w =? 1) ws). rewrite Zlength_correct. lia. }
  assert (Hz0: 0 <= Zlength ws0) by apply Zlength_nonneg.
  split; [lia|]. split; [|split; [simpl; lia|]].
  - unfold huf_ok. simpl. split; [unfold HUF_TABLELOG_MAX; lia|]. split.
    + rewrite Zlength_correct. exact Hlen.
    + pose proof (hro_cells_forall {| ht_log := log; ht_weights := ws |}) as Hf. simpl in Hf.
      eapply Forall_impl; [|exact Hf]. simpl. intros c Hc. lia.
  - intros ws1 sz1 D1 Hpos. injection D1 as <- <-. simpl.
    apply Forall_forall. intros x Hx. rewrite Forall_forall in Hle, Hpos. split; [|apply Hle; auto].
    unfold ws in Hx. apply in_app_or in Hx. destruct Hx as [Hx|[<-|[]]]; [apply Hpos; auto|lia].
Qed.

Lemma hro_desc res nk b ws sz : 0 <= byte_at b 0 < 256 ->
  huf_desc_weights_w (weights_of res nk) b = Some (ws, sz) -> Zlength ws <= 255 /\ 1 <= sz <= Zlength b.
Proof.
  intros Hb. unfold huf_desc_weights_w.
  destruct (Zlength b <? 1) eqn:E0; [discriminate|]. apply Z.ltb_ge in E0.
  destruct (byte_at b 0 >=? 128) eqn:E1.
  - apply Z.geb_le in E1.
    destruct (Zlength b <? (byte_at b 0 - 127 + 1) / 2 + 1) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
    intros H; inversion H; subst; clear H.
    unfold huf_direct_weights. rewrite Zlength_map, Zlength_correct, seq_length.
    rewrite Z2Nat.id by lia.
    assert (1 <= (byte_at b 0 - 127 + 1) / 2) by (apply Z.div_le_lower_bound; lia).
    change (let (q, _) := Z.div_eucl (byte_at b 0 - 127 + 1) 2 in q) with ((byte_at b 0 - 127 + 1) / 2).
    lia.
  - destruct (Zlength b <? byte_at b 0 + 1) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
    destruct (weights_of res nk (slice b 1 (byte_at b 0))) as [l|] eqn:E3; [|discriminate].
    intros H; inversion H; subst; clear H.
    split; [|lia].
    unfold weights_of, fse_weights_dec in E3.
    destruct res as [[[norm log] nsize]|]; [|discriminate].
    destruct (log >? 6); [discriminate|].
    destruct (fse_dwksp _ _ >? _); [discriminate|].
    destruct (negb _); [discriminate|].
    destruct (_ <? 0); [discriminate|].
    destruct (fse2_loop _ _ _ _ _ _ _) as [l'|]; [|discriminate].
    destruct (Zlength l' >? 255) eqn:E4; [discriminate|].
    inversion E3; subst. rewrite Z.gtb_ltb in E4. apply Z.ltb_ge in E4. lia.
Qed.

(* ---- the weights are nonnegative on a byte window ---- *)

Lemma hro_upd_nn (l: list Z) i x : Forall (fun v => 0 <= v) l -> 0 <= x -> Forall (fun v => 0 <= v) (upd l i x).
Proof.
  revert i. induction l as [|y l IH]; intros i Hl Hx; destruct i; simpl; auto;
    inversion Hl; subst; constructor; auto.
Qed.

Lemma hro_place_low_nn norm s n tab high : Forall (fun v => 0 <= v) tab ->
  Forall (fun v => 0 <= v) (fst (place_low norm s n tab high)).
Proof.
  revert s tab high. induction n as [|n IH]; intros s tab high Ht; simpl; auto.
  destruct (nth s norm 0 =? -1); apply IH; auto. apply hro_upd_nn; auto. lia.
Qed.

Lemma hro_spread_one_nn log k s high tab pos : Forall (fun v => 0 <= v) tab -> 0 <= s ->
  Forall (fun v => 0 <= v) (fst (spread_one log k s high tab pos)).
Proof.
  revert tab pos. induction k as [|k IH]; intros tab pos Ht Hs; simpl; auto.
  apply IH; auto. apply hro_upd_nn; auto.
Qed.

Lemma hro_spread_nn norm log s n high tab pos : Forall (fun v => 0 <= v) tab ->
  Forall (fun v => 0 <= v) (spread norm log s n high tab pos).
Proof.
  revert s tab pos. induction n as [|n IH]; intros s tab pos Ht; simpl; auto.
  destruct (nth s norm 0 >? 0).
  - destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos) as [t p] eqn:E.
    apply IH. pose proof (hro_spread_one_nn log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos Ht) as H.
    rewrite E in H. apply H. lia.
  - apply IH; auto.
Qed.

Lemma hro_states_nn log tab nx : Forall (fun v => 0 <= v) tab ->
  Forall (fun e => 0 <= fe_sym e) (states log tab nx).
Proof.
  revert nx. induction tab as [|a tab IH]; intros nx Ht; simpl; constructor; inversion Ht; subst; simpl; auto.
Qed.

Lemma hro_cell_nn norm log st : 0 <= fe_sym (fse_cell (fse_build norm log) st).
Proof.
  unfold fse_cell, fse_build.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [tab high] eqn:E.
  simpl.
  assert (Ht: Forall (fun v => 0 <= v) tab).
  { pose proof (hro_place_low_nn norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as H.
    rewrite E in H. apply H. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia. }
  pose proof (hro_states_nn log (spread norm log 0 (length norm) high tab 0)
                (map (fun c => if c =? -1 then 1 else c) norm) (hro_spread_nn _ _ _ _ _ _ _ Ht)) as Hs.
  destruct (Nat.lt_ge_cases (Z.to_nat st) (length (states log (spread norm log 0 (length norm) high tab 0)
                (map (fun c => if c =? -1 then 1 else c) norm)))) as [Hlt|Hge].
  - rewrite Forall_forall in Hs. apply Hs. apply nth_In. auto.
  - rewrite nth_overflow by auto. simpl. lia.
Qed.

Lemma hro_fse2_nn t (Hc: forall st, 0 <= fe_sym (fse_cell t st)) f V pos s1 s2 acc ws :
  Forall (fun v => 0 <= v) acc -> fse2_loop f t V pos s1 s2 acc = Some ws -> Forall (fun v => 0 <= v) ws.
Proof.
  revert pos s1 s2 acc. induction f as [|f IH]; intros pos s1 s2 acc Ha E; simpl in E; [discriminate|].
  assert (Hcons: forall l x, Forall (fun v => 0 <= v) l -> 0 <= x -> Forall (fun v => 0 <= v) (l ++ [x])).
  { intros l x Hl Hx. apply Forall_app. split; auto. }
  destruct (_ <? 0) in E.
  { injection E as <-. apply Hcons; auto. }
  destruct (_ <? 0) in E.
  { injection E as <-. apply Hcons; auto. }
  eapply IH; [|exact E]. auto.
Qed.

Lemma hro_byte_nn b i : bytes_ok b -> 0 <= byte_at b i.
Proof.
  intros Hb. unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat i) (length b)) as [Hlt|Hge].
  - unfold bytes_ok in Hb. rewrite Forall_forall in Hb. apply (Hb _ (nth_In _ 0 Hlt)).
  - rewrite nth_overflow by auto. lia.
Qed.

Lemma hro_desc_nn res nk b ws sz : bytes_ok b ->
  huf_desc_weights_w (weights_of res nk) b = Some (ws, sz) -> Forall (fun w => 0 <= w) ws.
Proof.
  intros Hb. unfold huf_desc_weights_w.
  destruct (Zlength b <? 1); [discriminate|].
  destruct (byte_at b 0 >=? 128).
  - destruct (Zlength b <? _); [discriminate|].
    intros H; inversion H; subst; clear H.
    unfold huf_direct_weights. apply Forall_forall. intros w Hw. apply in_map_iff in Hw.
    destruct Hw as [n [<- _]]. pose proof (hro_byte_nn b (1 + Z.of_nat n / 2) Hb).
    destruct (Nat.even n); [apply Z.shiftr_nonneg; lia|apply Z.land_nonneg; lia].
  - destruct (Zlength b <? _); [discriminate|].
    destruct (weights_of res nk (slice b 1 (byte_at b 0))) as [l|] eqn:E3; [|discriminate].
    intros H; inversion H; subst; clear H.
    unfold weights_of, fse_weights_dec in E3.
    destruct res as [[[norm log] nsize]|]; [|discriminate].
    destruct (log >? 6); [discriminate|].
    destruct (fse_dwksp _ _ >? _); [discriminate|].
    destruct (negb _); [discriminate|].
    destruct (_ <? 0); [discriminate|].
    destruct (fse2_loop _ _ _ _ _ _ _) as [l'|] eqn:E5; [|discriminate].
    destruct (Zlength l' >? 255); [discriminate|].
    inversion E3; subst.
    eapply hro_fse2_nn; [apply hro_cell_nn| |exact E5]. constructor.
Qed.

(* HUF_RES_OK on a window whose first byte is a byte (all but the weights' sign) *)
Lemma hro_main res (s: list Z) (ht: huf_table) (size: Z) : 0 <= byte_at s 0 < 256 ->
  huf_parse_res res 219 s = Some (ht, size) ->
  1 <= size <= Zlength s /\ huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256.
Proof.
  intros Hb H. unfold huf_parse_res in H. apply hro_parse in H.
  - destruct H as (? & ? & ? & _). auto.
  - intros ws0 sz D. destruct (hro_desc res 219 s ws0 sz Hb D) as [? ?]. auto.
Qed.

(* HUF_RES_OK with the weights' range, on a byte window *)
Lemma hro_main_bytes res (s: list Z) (ht: huf_table) (size: Z) : bytes_ok s ->
  huf_parse_res res 219 s = Some (ht, size) ->
  1 <= size <= Zlength s /\ huf_ok ht /\ 2 <= Zlength (ht_weights ht) <= 256 /\
  Forall (fun w => 0 <= w <= ht_log ht) (ht_weights ht).
Proof.
  intros Hb H.
  assert (Hb0: 0 <= byte_at s 0 < 256).
  { unfold byte_at. destruct s as [|x s]; simpl; [lia|]. inversion Hb; subst. auto. }
  unfold huf_parse_res in H.
  destruct (huf_desc_weights_w (weights_of res 219) s) as [[ws0 sz]|] eqn:D.
  2:{ unfold huf_parse_w in H. rewrite D in H. discriminate. }
  apply hro_parse in H.
  - destruct H as (? & ? & ? & Hf). split; auto. split; auto. split; auto.
    eapply Hf; [exact D|]. eapply hro_desc_nn; eauto.
  - intros ws1 sz1 D1. destruct (hro_desc res 219 s ws1 sz1 Hb0 D1) as [? ?]. auto.
Qed.

Lemma huf_res_ok : HUF_RES_OK.
Proof.
  intros res s ht size Hb H. exact (hro_main_bytes res s ht size Hb H).
Qed.

(* the model's tree description is C's (HUF_readStats_wksp's export): holds once Huffman.huf_fse_weights has C's
   workspace check (model/Huffman.v has it) *)
Definition HUF_MODEL_C : Prop :=
  forall (s: list Z) res x, bytes_ok s ->
  match rs_window s with Some w => nc_rel w 255 res | None => True end ->
  huf_parse_desc s = Some x -> huf_parse_res res 219 s = Some x.

Lemma hmc_ftlog (norm: list Z) (log: Z) : ft_log (fse_build norm log) = log.
Proof. unfold fse_build. destruct (place_low _ _ _ _ _). reflexivity. Qed.

Lemma hmc_weights (w: list Z) res ws : nc_rel w 255 res ->
  huf_fse_weights w = Some ws -> weights_of res 219 w = Some ws.
Proof.
  intros Hr H. unfold huf_fse_weights in H.
  destruct (read_ncount w 255) as [[[norm log] nsize]|] eqn:E; [|discriminate].
  pose proof (ncount_model_c w 255 _ ltac:(lia) E) as Hc.
  assert (Hres: res = Some (norm, log, nsize)).
  { unfold nc_rel in Hr. destruct (Zlength w <? 8).
    - destruct Hr as [Hr _]. auto.
    - rewrite Hr. exact Hc. }
  subst res. unfold weights_of, fse_weights_dec.
  destruct (log >? 6); [discriminate|].
  replace (fse_dwksp log (Zlength norm - 1) >? 4 * 219) with
    (4 * ((2 ^ log + 1) + 1 + (2 * Zlength norm + 2 ^ log + 8 + 3) / 4 + 129) >? 876)
    by (unfold fse_dwksp; replace (2 * (Zlength norm - 1 + 1)) with (2 * Zlength norm) by lia; reflexivity).
  destruct (_ >? 876); [discriminate|].
  rewrite hmc_ftlog. exact H.
Qed.

Lemma hmc_desc (s: list Z) res y :
  match rs_window s with Some w => nc_rel w 255 res | None => True end ->
  huf_desc_weights_w huf_fse_weights s = Some y -> huf_desc_weights_w (weights_of res 219) s = Some y.
Proof.
  intros Hw H. unfold huf_desc_weights_w in H |- *.
  destruct (Zlength s <? 1) eqn:E1; [discriminate|].
  destruct (byte_at s 0 >=? 128) eqn:E2; [exact H|].
  destruct (Zlength s <? byte_at s 0 + 1) eqn:E3; [discriminate|].
  destruct (huf_fse_weights (slice s 1 (byte_at s 0))) as [ws|] eqn:E4; [|discriminate].
  unfold rs_window in Hw.
  apply Z.ltb_ge in E1. apply Z.ltb_ge in E3. rewrite Z.geb_leb in E2. apply Z.leb_gt in E2.
  replace (andb (andb (1 <=? Zlength s) (byte_at s 0 <? 128)) (byte_at s 0 + 1 <=? Zlength s)) with true in Hw
    by (symmetry; rewrite !andb_true_iff, !Z.leb_le, Z.ltb_lt; lia).
  rewrite (hmc_weights _ _ _ Hw E4).
  exact H.
Qed.

Lemma huf_model_c : HUF_MODEL_C.
Proof.
  intros s res x _ Hw H. unfold huf_parse_res. rewrite <- huf_parse_w_model in H.
  unfold huf_parse_w in H |- *.
  destruct (huf_desc_weights_w huf_fse_weights s) as [y|] eqn:E; [|discriminate].
  rewrite (hmc_desc s res y Hw E). exact H.
Qed.
