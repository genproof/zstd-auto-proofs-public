(* Group ENT: body of ZSTD_buildFSETable_body. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* ---------- coverage: the C writes into an uninitialised table, so every cell must be written.
   Starting the model's spreads from an all -1 table (-1 = "not written") gives the same result. ---------- *)

(* ---------- helpers for slow_cover ---------- *)
Section SlowCover.
Local Open Scope Z_scope.

Lemma sc_upd_length {A} (l: list A) i x : length (upd l i x) = length l.
Proof. revert i; induction l as [|a l IH]; intros [|i]; simpl; auto. Qed.

Lemma sc_upd_diff : forall (t1 t2: list Z) i x j, length t1 = length t2 ->
  nth j (upd t1 i x) 0 <> nth j (upd t2 i x) 0 -> j <> i /\ nth j t1 0 <> nth j t2 0.
Proof.
  induction t1 as [|a t1 IH]; intros [|b t2] i x j Hl H; simpl in *; try discriminate.
  - exfalso; apply H; reflexivity.
  - injection Hl as Hl. destruct i as [|i], j as [|j]; simpl in *.
    + contradiction.
    + split; [lia | exact H].
    + split; [lia | exact H].
    + destruct (IH t2 i x j Hl H) as [H1 H2]. split; [lia | exact H2].
Qed.

Definition sc_diff (S: nat -> Prop) (t1 t2: list Z) : Prop :=
  length t1 = length t2 /\ forall j, nth j t1 0 <> nth j t2 0 -> S j.

Lemma sc_diff_upd : forall S t1 t2 i x, sc_diff S t1 t2 ->
  sc_diff (fun j => S j /\ j <> i) (upd t1 i x) (upd t2 i x).
Proof.
  intros S t1 t2 i x [Hl H]. split.
  - rewrite !sc_upd_length; auto.
  - intros j Hj. destruct (sc_upd_diff t1 t2 i x j Hl Hj). auto.
Qed.

Lemma sc_diff_weaken : forall (S S': nat -> Prop) t1 t2, sc_diff S t1 t2 -> (forall j, S j -> S' j) ->
  sc_diff S' t1 t2.
Proof. intros S S' t1 t2 [Hl H] HS. split; auto. Qed.

Lemma sc_skip_S : forall log f high pos, skip_high log (S f) high pos =
  if pos >? high then skip_high log f high (Z.land (pos + fse_step log) (2 ^ log - 1)) else pos.
Proof. reflexivity. Qed.

Lemma sc_one_S : forall log k s high tab pos, spread_one log (S k) s high tab pos =
  spread_one log k s high (upd tab (Z.to_nat pos) s)
    (skip_high log (Z.to_nat (2 ^ log)) high (Z.land (pos + fse_step log) (2 ^ log - 1))).
Proof. reflexivity. Qed.

Lemma sc_pl_S : forall norm s n tab high, place_low norm s (S n) tab high =
  if nth s norm 0 =? -1 then place_low norm (S s) n (upd tab (Z.to_nat high) (Z.of_nat s)) (high - 1)
  else place_low norm (S s) n tab high.
Proof. reflexivity. Qed.

Lemma sc_sp_S : forall norm log s n high tab pos, spread_pos norm log s (S n) high tab pos =
  let p := if nth s norm 0 >? 0 then spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos
           else (tab, pos) in
  spread_pos norm log (S s) n high (fst p) (snd p).
Proof.
  intros. cbn [spread_pos]. destruct (nth s norm 0 >? 0); [|reflexivity].
  destruct (spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos); reflexivity.
Qed.

Fixpoint sc_neg (norm: list Z) (s n: nat) : nat :=
  match n with O => O | S n' => ((if (nth s norm 0 =? -1)%Z then 1 else 0) + sc_neg norm (S s) n')%nat end.
Fixpoint sc_w (norm: list Z) (s n: nat) : nat :=
  match n with O => O | S n' =>
    ((if (nth s norm 0 >? 0)%Z then Z.to_nat (nth s norm 0%Z) else 0) + sc_w norm (S s) n')%nat end.

Lemma sc_pl_diff : forall norm n s t1 t2 high, sc_diff (fun j => Z.of_nat j <= high) t1 t2 ->
  snd (place_low norm s n t1 high) = high - Z.of_nat (sc_neg norm s n) /\
  snd (place_low norm s n t2 high) = high - Z.of_nat (sc_neg norm s n) /\
  sc_diff (fun j => Z.of_nat j <= high - Z.of_nat (sc_neg norm s n))
    (fst (place_low norm s n t1 high)) (fst (place_low norm s n t2 high)).
Proof.
  induction n as [|n IH]; intros s t1 t2 high H.
  - simpl. rewrite Z.sub_0_r. auto.
  - rewrite !sc_pl_S. cbn [sc_neg]. destruct (nth s norm 0 =? -1).
    + destruct (IH (S s) (upd t1 (Z.to_nat high) (Z.of_nat s)) (upd t2 (Z.to_nat high) (Z.of_nat s)) (high - 1))
        as [H1 [H2 H3]].
      { eapply sc_diff_weaken; [apply sc_diff_upd, H|]. intros j [Hj Hne]. lia. }
      rewrite H1, H2. split; [lia|split; [lia|]].
      eapply sc_diff_weaken; [exact H3|]. intros j Hj; cbv beta in Hj; lia.
    + destruct (IH (S s) t1 t2 high H) as [H1 [H2 H3]]. rewrite H1, H2. split; [lia|split; [lia|]].
      eapply sc_diff_weaken; [exact H3|]. intros j Hj; cbv beta in Hj; lia.
Qed.

Fixpoint sc_after (log high: Z) (k: nat) (pos: Z) : Z :=
  match k with O => pos | S k' =>
    sc_after log high k' (skip_high log (Z.to_nat (2 ^ log)) high (Z.land (pos + fse_step log) (2 ^ log - 1))) end.
Fixpoint sc_seq (log high: Z) (k: nat) (pos: Z) : list Z :=
  match k with O => nil | S k' =>
    pos :: sc_seq log high k' (skip_high log (Z.to_nat (2 ^ log)) high (Z.land (pos + fse_step log) (2 ^ log - 1))) end.

Lemma sc_seq_length : forall log high k pos, length (sc_seq log high k pos) = k.
Proof. induction k; intros; simpl; auto. Qed.

Lemma sc_after_add : forall log high a b pos, sc_after log high (a + b) pos = sc_after log high b (sc_after log high a pos).
Proof. induction a; intros; simpl; auto. Qed.

Lemma sc_seq_app : forall log high a b pos,
  sc_seq log high (a + b) pos = sc_seq log high a pos ++ sc_seq log high b (sc_after log high a pos).
Proof. induction a; intros; simpl; auto. f_equal; auto. Qed.

Lemma sc_one_snd : forall log k s high t pos, snd (spread_one log k s high t pos) = sc_after log high k pos.
Proof. induction k; intros; [reflexivity|]. rewrite sc_one_S. simpl sc_after. apply IHk. Qed.

Lemma sc_one_diff : forall log k s high t1 t2 pos S, sc_diff S t1 t2 ->
  sc_diff (fun j => S j /\ ~ In j (map Z.to_nat (sc_seq log high k pos)))
    (fst (spread_one log k s high t1 pos)) (fst (spread_one log k s high t2 pos)).
Proof.
  induction k; intros s high t1 t2 pos S H.
  - eapply sc_diff_weaken; [exact H|]. simpl; auto.
  - rewrite !sc_one_S. eapply sc_diff_weaken; [apply IHk, sc_diff_upd, H|].
    intros j [[Hj Hne] Hni]. split; auto. simpl. intros [Heq|Hin]; [congruence|]. exact (Hni Hin).
Qed.

Lemma sc_sp_snd : forall norm log n s high t pos,
  snd (spread_pos norm log s n high t pos) = sc_after log high (sc_w norm s n) pos.
Proof.
  induction n; intros; [reflexivity|]. rewrite sc_sp_S. cbn zeta. rewrite IHn. cbn [sc_w].
  destruct (nth s norm 0 >? 0).
  - rewrite sc_after_add, sc_one_snd. reflexivity.
  - reflexivity.
Qed.

Lemma sc_sp_diff : forall norm log n s high t1 t2 pos S, sc_diff S t1 t2 ->
  sc_diff (fun j => S j /\ ~ In j (map Z.to_nat (sc_seq log high (sc_w norm s n) pos)))
    (fst (spread_pos norm log s n high t1 pos)) (fst (spread_pos norm log s n high t2 pos)).
Proof.
  induction n; intros s high t1 t2 pos S H.
  - eapply sc_diff_weaken; [exact H|]. simpl; auto.
  - rewrite !sc_sp_S. cbn zeta. cbn [sc_w]. destruct (nth s norm 0 >? 0).
    + rewrite !sc_one_snd. eapply sc_diff_weaken; [apply IHn, sc_one_diff, H|].
      intros j [[Hj H1] H2]. split; auto. rewrite sc_seq_app, map_app, in_app_iff. tauto.
    + eapply sc_diff_weaken; [apply IHn, H|]. simpl. tauto.
Qed.

Lemma sc_neg_shift : forall a l s n, sc_neg (a :: l) (S s) n = sc_neg l s n.
Proof. intros a l s n; revert s; induction n; intros; simpl; auto. Qed.
Lemma sc_w_shift : forall a l s n, sc_w (a :: l) (S s) n = sc_w l s n.
Proof. intros a l s n; revert s; induction n; intros; simpl; auto. Qed.

Lemma sc_sum : forall l, Forall (fun c => -1 <= c) l ->
  fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) l) =
  Z.of_nat (sc_neg l 0 (length l)) + Z.of_nat (sc_w l 0 (length l)).
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|]. inversion H; subst.
  simpl length. cbn [sc_neg sc_w nth map fold_right]. rewrite sc_neg_shift, sc_w_shift, IH by auto.
  destruct (Z.eqb_spec a (-1)), (Z.gtb_spec a 0); lia.
Qed.

(* the orbit of the spread: position t * step mod 2^log *)
Definition sc_o (log: Z) (T: nat) : Z := (Z.of_nat T * fse_step log) mod 2 ^ log.

Lemma sc_pow_pos : forall log, 0 <= log -> 0 < 2 ^ log.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma sc_step_pos : forall log, 0 < fse_step log.
Proof.
  intros. unfold fse_step. assert (0 <= 2 ^ log) by (apply Z.pow_nonneg; lia).
  pose proof (proj2 (Z.shiftr_nonneg (2 ^ log) 1) H). pose proof (proj2 (Z.shiftr_nonneg (2 ^ log) 3) H). lia.
Qed.

Lemma sc_o_range : forall log T, 0 <= log -> 0 <= sc_o log T < 2 ^ log.
Proof. intros. unfold sc_o. apply Z.mod_pos_bound, sc_pow_pos; auto. Qed.

Lemma sc_o_next : forall log T, 0 <= log ->
  Z.land (sc_o log T + fse_step log) (2 ^ log - 1) = sc_o log (S T).
Proof.
  intros. pose proof (sc_pow_pos log H). pose proof (sc_step_pos log). pose proof (sc_o_range log T H).
  replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. unfold sc_o. rewrite Z.add_mod_idemp_l by lia.
  rewrite Nat2Z.inj_succ. f_equal; ring.
Qed.

Lemma sc_o_mul : forall log k, 0 <= log -> sc_o log (k * Z.to_nat (2 ^ log)) = 0.
Proof.
  intros. pose proof (sc_pow_pos log H). unfold sc_o. rewrite Nat2Z.inj_mul, Z2Nat.id by lia.
  replace (Z.of_nat k * 2 ^ log * fse_step log) with ((Z.of_nat k * fse_step log) * 2 ^ log) by ring.
  apply Z.mod_mul; lia.
Qed.

Lemma sc_skip : forall log, 0 <= log -> forall fuel T high,
  (exists d, (d <= fuel)%nat /\ sc_o log (T + d) <= high) ->
  exists d, skip_high log fuel high (sc_o log T) = sc_o log (T + d) /\ sc_o log (T + d) <= high /\
    forall e, (e < d)%nat -> high < sc_o log (T + e).
Proof.
  intros log Hlog. induction fuel as [|fuel IH]; intros T high [d [Hd Ho]].
  - assert (d = 0%nat) by lia. subst. exists 0%nat. rewrite Nat.add_0_r in *. split; [reflexivity|split; [auto|intros; lia]].
  - rewrite sc_skip_S. destruct (Z.gtb_spec (sc_o log T) high).
    + rewrite sc_o_next by auto. destruct d as [|d]. { rewrite Nat.add_0_r in Ho; lia. }
      destruct (IH (S T) high) as [d' [E1 [E2 E3]]].
      { exists d; split; [lia|]. replace (S T + d)%nat with (T + S d)%nat by lia; auto. }
      exists (S d'). replace (T + S d')%nat with (S T + d')%nat by lia. split; [auto|split; [auto|]].
      intros e He. destruct e as [|e]. { rewrite Nat.add_0_r; lia. }
      replace (T + S e)%nat with (S T + e)%nat by lia. apply E3; lia.
    + exists 0%nat. rewrite Nat.add_0_r. split; [reflexivity|split; [lia | intros; lia]].
Qed.

Lemma sc_filter_nil : forall (f: Z -> bool) l, (forall x, In x l -> f x = false) -> filter f l = [].
Proof. intros f l; induction l as [|a l IH]; simpl; intros H; auto. rewrite H by auto. apply IH; auto. Qed.

Lemma sc_orbit : forall log high, 0 <= log -> 0 <= high -> forall k T, sc_o log T <= high ->
  exists T', (T <= T')%nat /\
    sc_seq log high k (sc_o log T) = filter (fun x => x <=? high) (map (sc_o log) (seq T (T' - T))).
Proof.
  intros log high Hlog Hh. induction k as [|k IH]; intros T HT.
  - exists T. split; [lia|]. rewrite Nat.sub_diag. reflexivity.
  - cbn [sc_seq]. rewrite sc_o_next by auto.
    pose proof (sc_pow_pos log Hlog) as Hp.
    set (N := Z.to_nat (2 ^ log)).
    assert (HN: (0 < N)%nat) by (unfold N; lia).
    destruct (sc_skip log Hlog N (S T) high) as [d [E1 [E2 E3]]].
    { exists (N - S T mod N)%nat.
      pose proof (Nat.div_mod_eq (S T) N). pose proof (Nat.mod_upper_bound (S T) N ltac:(lia)).
      remember (S T / N)%nat as q. remember (S T mod N)%nat as r.
      split; [lia|].
      replace (S T + (N - r))%nat with ((q + 1) * N)%nat by nia.
      unfold N; rewrite sc_o_mul; lia. }
    rewrite E1. destruct (IH (S T + d)%nat E2) as [T' [HT' Eq]]. rewrite Eq. exists T'. split; [lia|].
    replace (T' - T)%nat with (1 + (d + (T' - (S T + d))))%nat by lia.
    rewrite seq_app, seq_app. replace (T + 1)%nat with (S T) by lia.
    rewrite !map_app, !filter_app.
    rewrite (sc_filter_nil _ (map (sc_o log) (seq (S T) d))).
    + cbn [seq map filter app]. rewrite (proj2 (Z.leb_le _ _) HT). reflexivity.
    + intros x Hx. apply in_map_iff in Hx as [u [<- Hu]]. apply in_seq in Hu.
      apply Z.leb_gt. replace u with (S T + (u - S T))%nat by lia. apply E3; lia.
Qed.

Lemma sc_o_inj : forall log, 0 <= log -> Z.gcd (2 ^ log) (fse_step log) = 1 ->
  forall u v, (u < Z.to_nat (2 ^ log))%nat -> (v < Z.to_nat (2 ^ log))%nat -> sc_o log u = sc_o log v -> u = v.
Proof.
  intros log Hlog Hrp u v Hu Hv E. pose proof (sc_pow_pos log Hlog). unfold sc_o in E.
  assert (Hd: (2 ^ log | fse_step log * (Z.of_nat u - Z.of_nat v))).
  { apply Z.mod_divide; [lia|].
    replace (fse_step log * (Z.of_nat u - Z.of_nat v)) with (Z.of_nat u * fse_step log - Z.of_nat v * fse_step log)
      by ring.
    rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
  apply Z.gauss in Hd; auto. destruct Hd as [z Hz].
  assert (0 <= Z.of_nat u < 2 ^ log) by lia. assert (0 <= Z.of_nat v < 2 ^ log) by lia.
  set (P := 2 ^ log) in *. assert (z = 0) by nia. subst. lia.
Qed.

Lemma sc_o_nodup : forall log T, 0 <= log -> Z.gcd (2 ^ log) (fse_step log) = 1 ->
  (T <= Z.to_nat (2 ^ log))%nat -> NoDup (map (sc_o log) (seq 0 T)).
Proof.
  intros. apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
  intros x y Hx Hy E. apply in_seq in Hx, Hy. apply (sc_o_inj log); auto; lia.
Qed.

Lemma sc_o_surj : forall log j, 0 <= log -> Z.gcd (2 ^ log) (fse_step log) = 1 -> 0 <= j < 2 ^ log ->
  exists u, (u < Z.to_nat (2 ^ log))%nat /\ sc_o log u = j.
Proof.
  intros log j Hlog Hrp Hj.
  assert (Hi: incl (map Z.of_nat (seq 0 (Z.to_nat (2 ^ log)))) (map (sc_o log) (seq 0 (Z.to_nat (2 ^ log))))).
  { apply NoDup_length_incl.
    - apply sc_o_nodup; auto.
    - rewrite !map_length; lia.
    - intros x Hx. apply in_map_iff in Hx as [u [<- Hu]]. pose proof (sc_o_range log u Hlog).
      apply in_map_iff. exists (Z.to_nat (sc_o log u)). split; [lia|]. apply in_seq; lia. }
  destruct (proj1 (in_map_iff _ _ _) (Hi j ltac:(apply in_map_iff; exists (Z.to_nat j); split; [lia|apply in_seq; lia])))
    as [u [Hu1 Hu2]].
  apply in_seq in Hu2. exists u. split; [lia|auto].
Qed.

Lemma sc_cover : forall log h T', 0 <= log -> Z.gcd (2 ^ log) (fse_step log) = 1 -> 0 <= h < 2 ^ log ->
  length (filter (fun x => x <=? h) (map (sc_o log) (seq 0 T'))) = Z.to_nat (h + 1) ->
  forall j, 0 <= j <= h -> In j (filter (fun x => x <=? h) (map (sc_o log) (seq 0 T'))).
Proof.
  intros log h T' Hlog Hrp Hh Hlen j Hj.
  destruct (le_lt_dec T' (Z.to_nat (2 ^ log))) as [Hle|Hlt].
  - assert (Hnd: NoDup (filter (fun x => x <=? h) (map (sc_o log) (seq 0 T'))))
      by (apply NoDup_filter, sc_o_nodup; auto).
    assert (Hi: incl (map Z.of_nat (seq 0 (Z.to_nat (h + 1)))) (filter (fun x => x <=? h) (map (sc_o log) (seq 0 T')))).
    { apply NoDup_length_incl; auto.
      - rewrite map_length, seq_length; lia.
      - intros x Hx. apply filter_In in Hx as [Hx Hle']. apply in_map_iff in Hx as [u [<- _]].
        apply Z.leb_le in Hle'. pose proof (sc_o_range log u Hlog).
        apply in_map_iff. exists (Z.to_nat (sc_o log u)). split; [lia|]. apply in_seq; lia. }
    apply Hi. apply in_map_iff. exists (Z.to_nat j). split; [lia|]. apply in_seq; lia.
  - destruct (sc_o_surj log j Hlog Hrp ltac:(lia)) as [u [Hu <-]].
    apply filter_In. split; [apply in_map, in_seq; lia | apply Z.leb_le; lia].
Qed.

End SlowCover.

(* the slow spread (low-probability area, then spread_pos) writes every cell *)
Lemma slow_cover : forall (norm: list Z) (log m: Z), ncount_ok norm log m -> log <= 9 ->
  (let '(tab, high) := place_low norm 0 (length norm) (repeat (-1) (Z.to_nat (2 ^ log))) (2 ^ log - 1) in
   spread_pos norm log 0 (length norm) high tab 0) =
  (let '(tab, high) := place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1) in
   spread_pos norm log 0 (length norm) high tab 0).
Proof.
  intros norm log m [Hlog [Hlen [Hall Hsum]]] H9.
  assert (Hlog0: 0 <= log) by lia. pose proof (sc_pow_pos log Hlog0) as Hp.
  assert (Hgcd: Z.gcd (2 ^ log) (fse_step log) = 1).
  { assert (log = 5 \/ log = 6 \/ log = 7 \/ log = 8 \/ log = 9) as Hc by lia.
    destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; reflexivity. }
  assert (Hneg: Forall (fun c => -1 <= c) norm) by (eapply Forall_impl; [|exact Hall]; simpl; intros; lia).
  pose proof (sc_sum norm Hneg) as Hs. rewrite Hsum in Hs.
  destruct (sc_pl_diff norm (length norm) 0 (repeat (-1) (Z.to_nat (2 ^ log))) (repeat 0 (Z.to_nat (2 ^ log)))
              (2 ^ log - 1)) as [H1 [H2 H3]].
  { split; [rewrite !repeat_length; auto|]. intros j Hj. destruct (lt_dec j (Z.to_nat (2 ^ log))); [lia|].
    rewrite !nth_overflow in Hj by (rewrite repeat_length; lia). contradiction. }
  destruct (place_low norm 0 (length norm) (repeat (-1) (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [a1 h1].
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [a2 h2].
  simpl in H1, H2, H3. subst h1 h2.
  set (h := 2 ^ log - 1 - Z.of_nat (sc_neg norm 0 (length norm))) in *.
  rewrite (surjective_pairing (spread_pos norm log 0 (length norm) h a1 0)).
  rewrite (surjective_pairing (spread_pos norm log 0 (length norm) h a2 0)).
  rewrite !sc_sp_snd. f_equal.
  destruct (sc_sp_diff norm log (length norm) 0 h a1 a2 0 _ H3) as [Hl Hd].
  apply nth_ext with (d := 0) (d' := 0); auto.
  intros j _. destruct (Z.eq_dec (nth j (fst (spread_pos norm log 0 (length norm) h a1 0)) 0)
                                  (nth j (fst (spread_pos norm log 0 (length norm) h a2 0)) 0)) as [E|E]; auto.
  exfalso. apply Hd in E as [Hj Hni]. apply Hni.
  set (W := sc_w norm 0 (length norm)) in *.
  assert (Hh: 0 <= h) by lia. assert (HW: Z.of_nat W = h + 1) by lia.
  assert (E0: sc_o log 0 = 0) by (unfold sc_o; simpl; apply Zmod_0_l).
  destruct (sc_orbit log h Hlog0 Hh W 0 ltac:(rewrite E0; lia)) as [T' [_ Eq]].
  rewrite E0 in Eq. rewrite Eq.
  apply in_map_iff. exists (Z.of_nat j). split; [lia|]. rewrite Nat.sub_0_r in *.
  apply sc_cover; auto; [lia | rewrite <- Eq, sc_seq_length; lia | lia].
Qed.

(* helpers of fast_cover: an upd-iteration whose positions cover every index forgets the initial table *)
Lemma fc_upd_length : forall {A} (l: list A) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; simpl; auto. Qed.

Lemma fc_nth_upd_eq : forall {A} (l: list A) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. induction l; intros [|i] x d H; simpl in *; try lia; auto. apply IHl; lia. Qed.

Lemma fc_nth_upd_neq : forall {A} (l: list A) i j x d, j <> i -> nth j (upd l i x) d = nth j l d.
Proof.
  induction l; intros [|i] [|j] x d H; simpl; auto; try congruence; apply IHl; lia.
Qed.

Definition fc_pos (log: Z) (k: nat) : nat := Z.to_nat ((Z.of_nat k * fse_step log) mod 2 ^ log).

Lemma fc_fill_agree : forall log sb n i (t1 t2: list Z), length t1 = length t2 ->
  (forall j, (j < length t1)%nat -> nth j t1 0 = nth j t2 0 \/
     exists k, (k < n)%nat /\ fc_pos log (i + k) = j) ->
  fast_fill log sb i n t1 = fast_fill log sb i n t2.
Proof.
  induction n; intros i t1 t2 Hlen H; simpl.
  - apply nth_ext with (d := 0) (d' := 0); auto.
    intros j Hj. destruct (H j Hj) as [E | [k [Hk _]]]; [exact E | lia].
  - apply IHn. rewrite !fc_upd_length; auto.
    intros j Hj. rewrite fc_upd_length in Hj.
    set (p := Z.to_nat ((Z.of_nat i * fse_step log) mod 2 ^ log)).
    destruct (Nat.eq_dec j p) as [-> | Hne].
    + left. rewrite !fc_nth_upd_eq; auto. lia.
    + rewrite !fc_nth_upd_neq by exact Hne.
      destruct (H j Hj) as [E | [k [Hk Hp]]]; [left; exact E | right].
      destruct k as [|k].
      * exfalso. apply Hne. rewrite <- Hp. unfold fc_pos, p. f_equal. f_equal. f_equal. lia.
      * exists k. split; [lia|]. rewrite <- Hp. f_equal. lia.
Qed.

Definition fc_check (log: Z) : bool :=
  let N := Z.to_nat (2 ^ log) in
  forallb (fun j => existsb (fun k => Nat.eqb (fc_pos log k) j) (seq 0 N)) (seq 0 N).

Lemma fc_check_cover : forall log, fc_check log = true ->
  forall j, (j < Z.to_nat (2 ^ log))%nat -> exists k, (k < Z.to_nat (2 ^ log))%nat /\ fc_pos log (0 + k) = j.
Proof.
  intros log Hc j Hj. unfold fc_check in Hc. rewrite forallb_forall in Hc.
  specialize (Hc j). rewrite in_seq in Hc. specialize (Hc ltac:(lia)).
  apply existsb_exists in Hc. destruct Hc as [k [Hk E]].
  rewrite in_seq in Hk. apply Nat.eqb_eq in E. exists k. split; [lia | exact E].
Qed.

Lemma fc_check_5 : fc_check 5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fc_check_6 : fc_check 6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fc_check_7 : fc_check 7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fc_check_8 : fc_check 8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma fc_check_9 : fc_check 9 = true. Proof. vm_compute. reflexivity. Qed.

(* the fast spread (no -1 symbol) writes every cell *)
Lemma fast_cover : forall (norm: list Z) (log m: Z), ncount_ok norm log m -> log <= 9 ->
  Forall (fun c => 0 <= c) norm ->
  fast_fill log (spread_bytes norm) 0 (Z.to_nat (2 ^ log)) (repeat (-1) (Z.to_nat (2 ^ log))) = fast_tab norm log.
Proof.
  intros norm log m Hok H9 _. unfold fast_tab.
  assert (Hc : fc_check log = true).
  { destruct Hok as [[H5 _] _].
    assert (log = 5 \/ log = 6 \/ log = 7 \/ log = 8 \/ log = 9) as [-> | [-> | [-> | [-> | ->]]]] by lia.
    - exact fc_check_5.
    - exact fc_check_6.
    - exact fc_check_7.
    - exact fc_check_8.
    - exact fc_check_9. }
  apply fc_fill_agree; rewrite !repeat_length; auto.
  intros j Hj. right. apply fc_check_cover; auto.
Qed.


(* ---------- the base / extra-bits tables of kind k inside zstd_globals ---------- *)

Definition sk_bvals (k: seqkind) : list val :=
  match k with KLL => LL_base_val | KOF => OF_base_val | KML => ML_base_val end.
Definition sk_nvals (k: seqkind) : list val :=
  match k with KLL => LL_bits_val | KOF => OF_bits_val | KML => ML_bits_val end.

Definition zg_common (gv: globals) : mpred :=
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) *
  eb_res gv.

Definition zg_rest (k: seqkind) (gv: globals) : mpred :=
  zg_common gv *
  match k with
  | KLL => data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
           data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
           data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
           data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base)
  | KOF => data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
           data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
           data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
           data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base)
  | KML => data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
           data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
           data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
           data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits)
  end.

Lemma zg_split (k: seqkind) (gv: globals) :
  zstd_globals gv =
  data_at Ers (tarray tuint (sk_max k + 1)) (sk_bvals k) (gv (sk_gbase k)) *
  data_at Ers (tarray tuchar (sk_max k + 1)) (sk_nvals k) (gv (sk_gbits k)) * zg_rest k gv.
Proof.
  destruct k; unfold zstd_globals, zg_rest, zg_common, sk_max, sk_bvals, sk_nvals, sk_gbase, sk_gbits;
    simpl; apply pred_ext; cancel.
Qed.

Lemma zg_unjoin (k: seqkind) (gv: globals) (pb pbits: val) :
  pb = gv (sk_gbase k) -> pbits = gv (sk_gbits k) ->
  zstd_globals gv |--
  data_at Ers (tarray tuint (sk_max k + 1)) (sk_bvals k) pb *
  data_at Ers (tarray tuchar (sk_max k + 1)) (sk_nvals k) pbits * zg_rest k gv.
Proof. intros -> ->. rewrite (zg_split k gv). auto. Qed.

Lemma zg_join (k: seqkind) (gv: globals) (pb pbits: val) :
  pb = gv (sk_gbase k) -> pbits = gv (sk_gbits k) ->
  data_at Ers (tarray tuint (sk_max k + 1)) (sk_bvals k) pb *
  data_at Ers (tarray tuchar (sk_max k + 1)) (sk_nvals k) pbits * zg_rest k gv |-- zstd_globals gv.
Proof. intros -> ->. rewrite (zg_split k gv). auto. Qed.

Lemma sk_bvals_eq (k: seqkind) :
  sk_bvals k = map (fun i => Vint (Int.repr (sk_base k i))) (upto (Z.to_nat (sk_max k + 1))).
Proof. destruct k; vm_compute; reflexivity. Qed.

Lemma sk_nvals_eq (k: seqkind) :
  sk_nvals k = map (fun i => Vint (Int.repr (sk_bits k i))) (upto (Z.to_nat (sk_max k + 1))).
Proof. destruct k; vm_compute; reflexivity. Qed.

Lemma sk_max_bounds (k: seqkind) : 31 <= sk_max k <= 52 /\ 8 <= sk_maxlog k <= 9.
Proof. destruct k; simpl; unfold MaxLL, MaxOff, MaxML, LLFSELog, OffFSELog, MLFSELog; lia. Qed.

Lemma sk_ranges_b (k: seqkind) :
  forallb (fun i => ((0 <=? sk_base k i) && (sk_base k i <=? 2147483645) && (0 <=? sk_bits k i) && (sk_bits k i <=? 31))%bool)
    (upto (Z.to_nat (sk_max k + 1))) = true.
Proof. destruct k; vm_compute; reflexivity. Qed.

Lemma sk_ranges (k: seqkind) (i: Z) : 0 <= i <= sk_max k ->
  0 <= sk_base k i <= 2147483645 /\ 0 <= sk_bits k i <= 31.
Proof.
  intros Hi. pose proof (sk_ranges_b k) as H. rewrite forallb_forall in H.
  specialize (H i). rewrite In_upto in H. destruct (sk_max_bounds k).
  spec H; [lia|]. rewrite !andb_true_iff, !Z.leb_le in H. lia.
Qed.



(* ---------- pure facts about the model loops, in the C's order ---------- *)

Definition nxt (c: Z) : Z := if c =? -1 then 1 else c.
Definition bvz (z: Z) : val := if z <? 0 then Vundef else Vint (Int.repr z).
Definition cellb (b: val) : val * (val * (val * val)) := (Vundef, (Vundef, (Vundef, b))).

Lemma upd_length {A} (l: list A) i x : length (upd l i x) = length l.
Proof. revert i; induction l; destruct i; simpl; auto. Qed.

Lemma upd_Zlength {A} (l: list A) i x : Zlength (upd l i x) = Zlength l.
Proof. rewrite !Zlength_correct, upd_length; auto. Qed.



Lemma map_upd {A B} (f: A -> B) (l: list A) i x : map f (upd l i x) = upd (map f l) i (f x).
Proof. revert i; induction l; destruct i; simpl; f_equal; auto. Qed.

Lemma nth_upd_same {A} (l: list A) i x d : (i < length l)%nat -> nth i (upd l i x) d = x.
Proof. revert i; induction l; destruct i; simpl; intros; try lia; auto. apply IHl; lia. Qed.

Lemma nth_upd_other {A} (l: list A) i j x d : i <> j -> nth j (upd l i x) d = nth j l d.
Proof. revert i j; induction l; destruct i, j; simpl; intros; auto; congruence || apply IHl; lia. Qed.

Lemma upd_upd_Znth {A} {d: Inhabitant A} (l: list A) (i: Z) x :
  0 <= i < Zlength l -> upd l (Z.to_nat i) x = upd_Znth i l x.
Proof.
  intros Hi. apply Znth_eq_ext. { rewrite upd_Zlength, Zlength_upd_Znth; auto. }
  intros j Hj. rewrite upd_Zlength in Hj.
  destruct (Z.eq_dec j i).
  - subst. rewrite upd_Znth_same by auto. rewrite <- nth_Znth by (rewrite upd_Zlength; auto). apply nth_upd_same. rewrite Zlength_correct in Hi; lia.
  - rewrite upd_Znth_diff by auto. rewrite <- !nth_Znth by (rewrite ?upd_Zlength; auto). apply nth_upd_other. lia.
Qed.

Lemma firstn_S_nth {A} n (l: list A) d : (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  revert l; induction n; intros l Hn; destruct l as [|a l]; simpl in Hn; try lia; auto.
  change (firstn (S (S n)) (a :: l)) with (a :: firstn (S n) l).
  rewrite IHn by lia. auto.
Qed.

(* place_low over a prefix *)
Lemma place_low_app norm s0 a b tab h :
  place_low norm s0 (a + b) tab h =
  let '(t, h') := place_low norm s0 a tab h in place_low norm (s0 + a) b t h'.
Proof.
  revert s0 tab h; induction a; intros; simpl.
  - rewrite Nat.add_0_r. auto.
  - destruct (nth s0 norm 0 =? -1); rewrite IHa; replace (S s0 + a)%nat with (s0 + S a)%nat by lia; auto.
Qed.

Lemma place_low_S norm n tab h :
  place_low norm 0 (S n) tab h =
  let '(t, h') := place_low norm 0 n tab h in
  if nth n norm 0 =? -1 then (upd t (Z.to_nat h') (Z.of_nat n), h' - 1) else (t, h').
Proof.
  replace (S n) with (n + 1)%nat by lia. rewrite place_low_app.
  destruct (place_low norm 0 n tab h). simpl. destruct (nth n norm 0 =? -1); auto.
Qed.

Lemma place_low_len norm s n tab h : length (fst (place_low norm s n tab h)) = length tab.
Proof.
  revert s tab h; induction n; intros; simpl; auto.
  destruct (nth s norm 0 =? -1); rewrite IHn; auto using upd_length.
Qed.

(* the number of -1 among the first n counts *)
Definition cntm1 (norm: list Z) (n: nat) : Z :=
  Z.of_nat (length (filter (fun c => c =? -1) (firstn n norm))).

Lemma place_low_high norm n tab h : snd (place_low norm 0 n tab h) = h - cntm1 norm n.
Proof.
  induction n.
  - simpl. unfold cntm1. simpl. lia.
  - rewrite place_low_S. destruct (place_low norm 0 n tab h) as [t h'] eqn:E. simpl in IHn.
    unfold cntm1 in *.
    destruct (le_lt_dec (length norm) n).
    + rewrite nth_overflow by lia. rewrite (firstn_all2 (n := S n)) by lia. rewrite firstn_all2 in IHn by lia. exact IHn.
    + rewrite (firstn_S_nth n norm 0) by lia.
      rewrite filter_app, app_length. simpl.
      destruct (nth n norm 0 =? -1); simpl; lia.
Qed.

(* ---------- small integer facts ---------- *)

Lemma shl_1 (n: Z) : 0 <= n < 31 -> Int.shl (Int.repr 1) (Int.repr n) = Int.repr (2 ^ n).
Proof.
  intros Hn. rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia.
  rewrite two_p_equiv. unfold Int.mul. rewrite !Int.unsigned_repr; [f_equal; lia | | rep_lia].
  split; [lia|]. apply Z.le_trans with (2 ^ 31); [apply Z.pow_le_mono_r; lia | rep_lia].
Qed.

Lemma tdec_eq (dt: val) : isptr dt ->
  force_val (sem_binary_operation' Oadd (tptr t_seqSymbol) tint dt (Vint (Int.repr 1))) = offset_val 8 dt.
Proof. destruct dt; try contradiction; reflexivity. Qed.

(* ---------- loop 1 (low-probability symbols, symbolNext, fastMode) in Z terms ---------- *)

Lemma nthZ (l: list Z) (s: Z) : 0 <= s < Zlength l -> nth (Z.to_nat s) l 0 = Znth s l.
Proof. intros. apply nth_Znth. auto. Qed.

Definition pl0 (norm: list Z) (log s: Z) : list Z * Z :=
  place_low norm 0 (Z.to_nat s) (repeat (-1) (Z.to_nat (2 ^ log))) (2 ^ log - 1).
Definition fm0 (norm: list Z) (log s: Z) : Z :=
  if existsb (fun c => 2 ^ (log - 1) <=? c) (sublist 0 s norm) then 0 else 1.
Definition cells0 (tab: list Z) : list (val * (val * (val * val))) := map (fun z => cellb (bvz z)) tab.
Definition snext (norm: list Z) (s: Z) : list val :=
  map (fun c => Vint (Int.repr (nxt c))) (sublist 0 s norm) ++ Zrepeat Vundef (53 - s).

Lemma pl0_step norm log s : 0 <= s ->
  pl0 norm log (s + 1) =
  let '(t, h) := pl0 norm log s in
  if Znth s norm =? -1 then (upd t (Z.to_nat h) s, h - 1) else (t, h).
Proof.
  intros Hs. unfold pl0. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite place_low_S.
  destruct (place_low _ _ _ _ _). rewrite Z2Nat.id by lia.
  destruct (Z_lt_le_dec s (Zlength norm)).
  - rewrite nthZ by lia. auto.
  - rewrite (Znth_overflow s norm) by lia. rewrite nth_overflow by (rewrite Zlength_correct in *; lia). auto.
Qed.

Lemma pl0_len norm log s : Zlength (fst (pl0 norm log s)) = Z.of_nat (Z.to_nat (2 ^ log)).
Proof. unfold pl0. rewrite Zlength_correct, place_low_len, repeat_length. auto. Qed.

Lemma pl0_high norm log s : snd (pl0 norm log s) = 2 ^ log - 1 - cntm1 norm (Z.to_nat s).
Proof. unfold pl0. rewrite place_low_high. auto. Qed.

Lemma cntm1_step norm s : 0 <= s < Zlength norm ->
  cntm1 norm (Z.to_nat (s + 1)) = cntm1 norm (Z.to_nat s) + (if Znth s norm =? -1 then 1 else 0).
Proof.
  intros Hs. unfold cntm1. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
  rewrite (firstn_S_nth _ _ 0) by (rewrite Zlength_correct in Hs; lia).
  rewrite filter_app, app_length, Nat2Z.inj_add. rewrite nthZ by lia. simpl.
  destruct (Znth s norm =? -1); simpl; lia.
Qed.

Lemma cntm1_le_sum (l: list Z) : Forall (fun c => -1 <= c) l ->
  Z.of_nat (length (filter (fun c => c =? -1) l)) <= fold_right Z.add 0 (map nxt l).
Proof.
  induction l; intros Hf; simpl; [lia|]. inv Hf. specialize (IHl H2).
  unfold nxt at 1. destruct (a =? -1) eqn:E; simpl; [lia|]. apply Z.eqb_neq in E. lia.
Qed.

Lemma cntm1_bound norm log m n : ncount_ok norm log m -> cntm1 norm n <= 2 ^ log.
Proof.
  intros (_ & _ & Hr & Hs). unfold cntm1.
  assert (Hle: (length (filter (fun c => (c =? -1)%Z) (firstn n norm)) <= length (filter (fun c => (c =? -1)%Z) norm))%nat).
  { rewrite <- (firstn_skipn n norm) at 2. rewrite filter_app, app_length. lia. }
  pose proof (cntm1_le_sum norm (Forall_impl _ (fun c H => proj1 H) Hr)).
  unfold nxt in H. rewrite Hs in H. lia.
Qed.

Lemma fm0_step norm log s : 0 <= s < Zlength norm ->
  fm0 norm log (s + 1) = if 2 ^ (log - 1) <=? Znth s norm then 0 else fm0 norm log s.
Proof.
  intros Hs. unfold fm0. rewrite (sublist_split 0 s (s + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite existsb_app. simpl. rewrite orb_false_r.
  destruct (2 ^ (log - 1) <=? Znth s norm), (existsb _ (sublist 0 s norm)); auto.
Qed.

Lemma snext_step norm s : 0 <= s < Zlength norm -> Zlength norm <= 53 ->
  upd_Znth s (snext norm s) (Vint (Int.repr (nxt (Znth s norm)))) = snext norm (s + 1).
Proof.
  intros Hs Hl. unfold snext. rewrite (sublist_split 0 s (s + 1)) by lia. rewrite sublist_len_1 by lia.
  list_solve.
Qed.

Lemma spread_eq (pw: val) : isptr pw ->
  force_val (sem_binary_operation' Oadd (tptr tushort) tint
               (eval_binop Oadd (tptr tushort) tint pw (Vint (Int.repr 52))) (Vint (Int.repr 1))) =
  offset_val 106 pw.
Proof. destruct pw; try contradiction. intros _. simpl. rewrite Ptrofs.add_assoc. reflexivity. Qed.

Lemma ll_eq (log: Z) : 1 <= log <= 15 ->
  Int.sign_ext 16 (Int.sign_ext 16 (Int.shl (Int.repr 1) (Int.sub (Int.repr log) (Int.repr 1)))) =
  Int.repr (2 ^ (log - 1)).
Proof.
  intros Hl. rewrite sub_repr, shl_1 by lia.
  assert (2 ^ (log - 1) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia).
  assert (0 < 2 ^ (log - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hs: Int.sign_ext 16 (Int.repr (2 ^ (log - 1))) = Int.repr (2 ^ (log - 1))).
  { apply sign_ext_inrange. rewrite Int.signed_repr by rep_lia. change (two_p (16 - 1)) with 32768. rep_lia. }
  rewrite !Hs. auto.
Qed.

Lemma cells0_init (shd: share) (n: Z) (p: val) :
  data_at_ shd (tarray t_seqSymbol n) p = data_at shd (tarray t_seqSymbol n) (cells0 (repeat (-1) (Z.to_nat n))) p.
Proof. unfold data_at_, cells0. rewrite map_repeat. reflexivity. Qed.

Lemma nc_nth (nc: list val) (norm: list Z) (s: Z) :
  Zlength norm <= Zlength nc -> sublist 0 (Zlength norm) nc = zbytes norm -> 0 <= s < Zlength norm ->
  Znth s nc = Vint (Int.repr (Znth s norm)).
Proof.
  intros H1 H2 Hs. pose proof (Znth_sublist 0 s (Zlength norm) nc ltac:(lia) ltac:(lia)) as E.
  rewrite Z.add_0_r, H2, Znth_map in E by lia. rewrite <- E. auto.
Qed.

Lemma cells0_upd {d: Inhabitant (val * (val * (val * val)))} (t: list Z) (h s: Z) :
  0 <= h < Zlength t -> 0 <= s ->
  upd_Znth h (cells0 t)
    (fst (Znth h (cells0 t)), (fst (snd (Znth h (cells0 t))), (fst (snd (snd (Znth h (cells0 t)))), Vint (Int.repr s)))) =
  cells0 (upd t (Z.to_nat h) s).
Proof.
  intros Hh Hs. unfold cells0. rewrite (upd_upd_Znth t h s Hh), <- upd_Znth_map. f_equal.
  rewrite Znth_map by auto. unfold cellb, bvz. cbn [fst snd].
  replace (s <? 0) with false by (symmetry; apply Z.ltb_ge; lia). auto.
Qed.

Lemma zext_small (n c: Z) : 0 <= c < two_p n -> two_p n <= Int.modulus -> Int.zero_ext n (Int.repr c) = Int.repr c.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr; rep_lia. Qed.

(* ---------- the slow spread's skip loop (C: while (position > highThreshold) position = (position+step)&mask) ---------- *)

(* the j-th position after p *)
Definition iterp (log p j: Z) : Z := (p + j * fse_step log) mod 2 ^ log.

Lemma iterp_land (log q: Z) : 0 <= log -> 0 <= q ->
  Z.land (q + fse_step log) (2 ^ log - 1) = (q + fse_step log) mod 2 ^ log.
Proof.
  intros Hl Hq. assert (0 <= fse_step log).
  { unfold fse_step. pose proof (Z.shiftr_nonneg (2 ^ log) 1). pose proof (Z.shiftr_nonneg (2 ^ log) 3).
    assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia). lia. }
  replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones; lia.
Qed.

Lemma iterp_succ (log p j: Z) : 0 <= log ->
  iterp log ((p + fse_step log) mod 2 ^ log) j = iterp log p (j + 1).
Proof.
  intros Hl. unfold iterp. assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma iterp_0 (log p: Z) : 0 <= p < 2 ^ log -> iterp log p 0 = p.
Proof. intros. unfold iterp. rewrite Z.add_0_r. apply Z.mod_small; lia. Qed.

Lemma iterp_period (log p j: Z) : 0 <= log -> iterp log p (j + 2 ^ log) = iterp log p j.
Proof.
  intros Hl. unfold iterp. assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  replace (p + (j + 2 ^ log) * fse_step log)%Z with (p + j * fse_step log + fse_step log * 2 ^ log)%Z by lia.
  apply Z_mod_plus_full.
Qed.

Lemma skip_high_fuel (log high: Z) (n: nat) : 0 <= log -> forall p j,
  0 <= p < 2 ^ log -> 0 <= j < Z.of_nat n ->
  (forall j', 0 <= j' < j -> iterp log p j' > high) -> iterp log p j <= high ->
  skip_high log n high p = iterp log p j.
Proof.
  intros Hl. assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  induction n as [| n IH]; intros p j Hp Hj Hbef Hat; [lia |].
  cbn [skip_high]. destruct (Z.gtb_spec p high) as [Hg | Hg].
  - assert (Hj0: j <> 0) by (intros ->; rewrite iterp_0 in Hat by lia; lia).
    fold (fse_step log). rewrite iterp_land by lia.
    replace (iterp log p j) with (iterp log ((p + fse_step log) mod 2 ^ log) (j - 1))
      by (rewrite iterp_succ by lia; f_equal; lia).
    apply IH.
    + apply Z.mod_pos_bound; lia.
    + lia.
    + intros j' Hj'. rewrite iterp_succ by lia. apply Hbef; lia.
    + rewrite iterp_succ by lia. replace (j - 1 + 1) with j by lia. auto.
  - destruct (Z.eq_dec j 0) as [-> | Hj0].
    + rewrite iterp_0 by lia. auto.
    + specialize (Hbef 0 ltac:(lia)). rewrite iterp_0 in Hbef by lia. lia.
Qed.

(* when the j-th position is the first one <= high, the model's fuelled skip_high finds it *)
Lemma skip_high_first (log high p j: Z) :
  0 <= log -> 0 <= p < 2 ^ log -> 0 <= j ->
  (forall j', 0 <= j' < j -> iterp log p j' > high) -> iterp log p j <= high ->
  skip_high log (Z.to_nat (2 ^ log)) high p = iterp log p j.
Proof.
  intros Hl Hp Hj Hbef Hat. assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  apply skip_high_fuel; auto. split; auto. rewrite Z2Nat.id by lia.
  destruct (Z_lt_le_dec j (2 ^ log)) as [Hlt | Hge]; auto.
  specialize (Hbef (j - 2 ^ log) ltac:(lia)).
  rewrite <- (iterp_period log p (j - 2 ^ log)) in Hbef by lia.
  replace (j - 2 ^ log + 2 ^ log) with j in Hbef by lia. lia.
Qed.

(* ---------- the fast spread, part 1: the symbols laid down in order (8 bytes at a time) ---------- *)

Definition sbp (norm: list Z) (s: Z) : list Z :=
  flat_map (fun j => repeat (Z.of_nat j) (Z.to_nat (nth j norm 0))) (seq 0 (Z.to_nat s)).
Definition psum (norm: list Z) (s: Z) : Z := fold_right Z.add 0 (sublist 0 s norm).
Definition SVADD : Z := 72340172838076673.

Lemma sbp_step norm s : 0 <= s < Zlength norm ->
  sbp norm (s + 1) = sbp norm s ++ repeat s (Z.to_nat (Znth s norm)).
Proof.
  intros Hs. unfold sbp. rewrite Z2Nat.inj_add, seq_app, flat_map_app by lia. simpl.
  rewrite app_nil_r, Z2Nat.id, nthZ by lia. auto.
Qed.

Lemma psum_step norm s : 0 <= s < Zlength norm -> psum norm (s + 1) = psum norm s + Znth s norm.
Proof.
  intros Hs. unfold psum. rewrite (sublist_split 0 s (s + 1)) by lia. rewrite sublist_len_1 by lia.
  rewrite fold_right_app. simpl. generalize (sublist 0 s norm). induction l; simpl; lia.
Qed.

Lemma psum_nonneg norm s : Forall (fun c => 0 <= c) norm -> 0 <= psum norm s.
Proof.
  intros Hf. unfold psum. assert (Forall (fun c => 0 <= c) (sublist 0 s norm)) by (apply Forall_sublist; auto).
  induction H; simpl; lia.
Qed.

Lemma psum_mono norm s t : Forall (fun c => 0 <= c) norm -> 0 <= s <= t -> t <= Zlength norm ->
  psum norm s <= psum norm t.
Proof.
  intros Hf Hst Ht. unfold psum. rewrite (sublist_split 0 s t) by lia. rewrite fold_right_app.
  pose proof (psum_nonneg (sublist s t norm) (Zlength (sublist s t norm)) (Forall_sublist _ _ _ _ Hf)) as Hn.
  unfold psum in Hn. rewrite sublist_same in Hn by lia.
  generalize (sublist 0 s norm). induction l; simpl; lia.
Qed.

Lemma psum_all norm log : Forall (fun c => 0 <= c) norm ->
  fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) norm) = 2 ^ log ->
  psum norm (Zlength norm) = 2 ^ log.
Proof.
  intros Hf Hs. unfold psum. rewrite sublist_same by lia. rewrite <- Hs. clear Hs.
  induction Hf; simpl; auto. rewrite IHHf. destruct (x =? -1) eqn:E; auto. apply Z.eqb_eq in E. lia.
Qed.

Lemma sbp_len norm s : Forall (fun c => 0 <= c) norm -> 0 <= s <= Zlength norm -> Zlength (sbp norm s) = psum norm s.
Proof.
  intros Hf Hs. rewrite <- (Z2Nat.id s) in * by lia. induction (Z.to_nat s) as [|n IH].
  - reflexivity.
  - rewrite Nat2Z.inj_succ in *. unfold Z.succ in *. rewrite sbp_step, psum_step by lia.
    rewrite Zlength_app, IH by lia. rewrite Zlength_repeat'. f_equal. apply Z2Nat.id.
    eapply Forall_Znth in Hf; [exact Hf|lia].
Qed.

Lemma sbp_all norm : sbp norm (Zlength norm) = spread_bytes norm.
Proof. unfold sbp, spread_bytes. rewrite Zlength_correct, Nat2Z.id. auto. Qed.

Lemma le_bytes_sv_b : forallb (fun s => list_eq_dec Z.eq_dec (le_bytes 8 (s * SVADD)) (repeat s 8)
                                         ) (upto 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma le_bytes_sv (s: Z) : 0 <= s < 256 -> le_bytes 8 (s * SVADD) = repeat s 8.
Proof.
  intros Hs. pose proof le_bytes_sv_b as H. rewrite forallb_forall in H.
  specialize (H s). rewrite In_upto in H. specialize (H ltac:(lia)).
  destruct (list_eq_dec Z.eq_dec _ _); auto. discriminate.
Qed.

Lemma write8_ok (cs: list val) (P: list Z) (p i s: Z) :
  0 <= p -> 0 <= i -> p + i + 8 <= Zlength cs -> 0 <= s < 256 -> Zlength P = p ->
  sublist 0 p cs = zbytes P -> sublist p (p + i) cs = zbytes (Zrepeat s i) ->
  Zlength (mem_written cs (p + i) 8 (s * SVADD)) = Zlength cs /\
  sublist 0 p (mem_written cs (p + i) 8 (s * SVADD)) = zbytes P /\
  sublist p (p + i + 8) (mem_written cs (p + i) 8 (s * SVADD)) = zbytes (Zrepeat s (i + 8)).
Proof.
  intros Hp Hi Hl Hs HP H0 H1. unfold mem_written. rewrite le_bytes_sv by auto.
  change (repeat s 8) with (Zrepeat s 8).
  split3; [list_solve | |].
  - rewrite sublist0_app1 by list_solve. rewrite sublist_sublist00 by lia. auto.
  - rewrite (sublist_split p (p + i) (p + i + 8)) by list_solve.
    rewrite sublist_app1 by list_solve. rewrite sublist_sublist by lia. rewrite !Z.add_0_r, H1.
    replace (sublist (p + i) (p + i + 8) _) with (zbytes (Zrepeat s 8)) by list_solve.
    rewrite <- map_app. f_equal. unfold Zrepeat. rewrite <- repeat_app. f_equal. lia.
Qed.

(* the fast branch: no -1 count *)
Lemma no_m1 norm log (s: Z) : Forall (fun c => -1 <= c) norm -> 0 <= s -> s = Zlength norm ->
  snd (pl0 norm log s) = 2 ^ log - 1 -> Forall (fun c => 0 <= c) norm.
Proof.
  intros Hr Hs E H. rewrite pl0_high in H. unfold cntm1 in H. subst s.
  rewrite firstn_all2 in H by (rewrite Zlength_correct; lia).
  assert (Hn: length (filter (fun c => (c =? -1)%Z) norm) = O) by lia.
  clear H. induction Hr; constructor; simpl in Hn.
  - destruct (x =? -1) eqn:Ex; [simpl in Hn; lia|]. apply Z.eqb_neq in Ex. lia.
  - apply IHHr; [rewrite Zlength_correct; lia|]. destruct (x =? -1); simpl in Hn; lia.
Qed.

Lemma place_low_none norm s0 n tab h : Forall (fun c => 0 <= c) norm -> place_low norm s0 n tab h = (tab, h).
Proof.
  intros Hf. revert s0. induction n; intros; simpl; auto.
  replace (nth s0 norm 0 =? -1) with false; auto. symmetry. apply Z.eqb_neq.
  destruct (le_lt_dec (length norm) s0). { rewrite nth_overflow by lia. lia. }
  eapply Forall_nth in Hf; [|exact l]. intro E. rewrite E in Hf. lia.
Qed.

Lemma step_eq (log: Z) : 0 <= log <= 20 ->
  Int.unsigned (Int.add (Int.add (Int.shru (Int.repr (2 ^ log)) (Int.repr 1)) (Int.shru (Int.repr (2 ^ log)) (Int.repr 3)))
                        (Int.repr 3)) = fse_step log.
Proof.
  intros Hl. assert (0 < 2 ^ log <= 2 ^ 20) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  unfold fse_step, Int.shru. rewrite !(Int.unsigned_repr (2 ^ log)) by rep_lia.
  rewrite !(Int.unsigned_repr 1), !(Int.unsigned_repr 3) by rep_lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8.
  assert (0 <= 2 ^ log / 2 <= 2 ^ 20) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= 2 ^ log / 8 <= 2 ^ 20) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold Int.add. rewrite (Int.unsigned_repr (2 ^ log / 2)) by rep_lia.
  rewrite (Int.unsigned_repr (2 ^ log / 8)) by rep_lia.
  rewrite (Int.unsigned_repr (2 ^ log / 2 + 2 ^ log / 8)) by rep_lia.
  rewrite (Int.unsigned_repr 3) by rep_lia. rewrite Int.unsigned_repr by rep_lia. auto.
Qed.

Lemma fse_step_bounds (log: Z) : 3 <= log <= 20 -> 3 <= fse_step log <= 2 ^ log.
Proof.
  intros Hl. unfold fse_step. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8.
  assert (E: (2 ^ log = 8 * 2 ^ (log - 3))%Z).
  { replace log with (3 + (log - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  assert (H1: 2 ^ 0 <= 2 ^ (log - 3)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 0) with 1 in H1.
  rewrite E. replace (8 * 2 ^ (log - 3))%Z with (2 ^ (log - 3) * 8)%Z by lia. rewrite Z.div_mul by lia.
  replace (2 ^ (log - 3) * 8)%Z with ((4 * 2 ^ (log - 3)) * 2)%Z by lia. rewrite Z.div_mul by lia.
  lia.
Qed.

(* ---------- the fast spread, part 2: cell (i * step) mod 2^log gets the i-th byte ---------- *)

Lemma fast_fill_app log sb i a b tab :
  fast_fill log sb i (a + b) tab = fast_fill log sb (i + a) b (fast_fill log sb i a tab).
Proof.
  revert i tab; induction a; intros; simpl. { rewrite Nat.add_0_r. auto. }
  rewrite IHa. replace (S i + a)%nat with (i + S a)%nat by lia. auto.
Qed.

Lemma fast_fill_end log sb (n: Z) tab : 0 <= n ->
  fast_fill log sb 0 (Z.to_nat (n + 1)) tab =
  upd (fast_fill log sb 0 (Z.to_nat n) tab) (Z.to_nat ((n * fse_step log) mod 2 ^ log)) (nth (Z.to_nat n) sb 0).
Proof.
  intros Hn. rewrite Z2Nat.inj_add by lia. rewrite fast_fill_app. simpl. rewrite Z2Nat.id by lia. auto.
Qed.

Lemma fast_fill_len log sb i n tab : length (fast_fill log sb i n tab) = length tab.
Proof. revert i tab; induction n; intros; simpl; auto. rewrite IHn, upd_length. auto. Qed.

Lemma land_mod (a log: Z) : 0 <= a -> 0 <= log -> Z.land a (2 ^ log - 1) = a mod 2 ^ log.
Proof. intros. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia). apply Z.land_ones. lia. Qed.

Lemma pos_and (log P u st: Z) : 0 <= log <= 20 -> 0 <= P < 2 ^ 20 -> 0 <= u <= 2 -> 0 <= st <= 2 ^ 20 ->
  Int64.and (Int64.add (Int64.repr P) (Int64.mul (Int64.repr u) (Int64.repr st))) (Int64.repr (2 ^ log - 1)) =
  Int64.repr ((P + u * st) mod 2 ^ log).
Proof.
  intros Hl HP Hu Hs. assert (0 < 2 ^ log <= 2 ^ 20) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  assert (0 <= u * st <= 2 * 2 ^ 20) by nia.
  rewrite mul64_repr, add64_repr. unfold Int64.and. rewrite !Int64.unsigned_repr by rep_lia.
  rewrite land_mod by lia. auto.
Qed.

Lemma pos_next (log s u: Z) : 0 < 2 ^ log ->
  ((s * fse_step log) mod 2 ^ log + u * fse_step log) mod 2 ^ log = ((s + u) * fse_step log) mod 2 ^ log.
Proof. intros. rewrite Zplus_mod_idemp_l. f_equal. lia. Qed.

Lemma spread_bytes_range norm x : In x (spread_bytes norm) -> 0 <= x < Zlength norm.
Proof.
  unfold spread_bytes. rewrite in_flat_map. intros (j & Hj & Hx).
  apply repeat_spec in Hx. subst. apply in_seq in Hj. rewrite Zlength_correct. lia.
Qed.

Lemma bytes_nth (cs: list val) (l: list Z) (n j: Z) :
  sublist 0 n cs = zbytes l -> Zlength l = n -> 0 <= j < n -> n <= Zlength cs ->
  Znth j cs = Vint (Int.repr (Znth j l)).
Proof.
  intros H Hl Hj Hn. pose proof (Znth_sublist 0 j n cs ltac:(lia) ltac:(lia)) as E.
  rewrite Z.add_0_r, H, Znth_map in E by lia. rewrite <- E. auto.
Qed.

Lemma even_step (s log: Z) : Z.even s = true -> 0 <= s < 2 ^ log -> 1 <= log ->
  0 <= s + 2 <= 2 ^ log /\ Z.even (s + 2) = true.
Proof.
  intros He Hs Hl. apply Z.even_spec in He. destruct He as [m Hm].
  assert (E: (2 ^ log = 2 * 2 ^ (log - 1))%Z).
  { replace log with (1 + (log - 1)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  split; [lia|]. apply Z.even_spec. exists (m + 1). lia.
Qed.

(* ---------- the slow spread ---------- *)

Definition sp0 (norm: list Z) (log high: Z) (tab: list Z) (s: Z) : list Z * Z :=
  spread_pos norm log 0 (Z.to_nat s) high tab 0.
Definition sp1 (log s high: Z) (tp: list Z * Z) (i: Z) : list Z * Z :=
  spread_one log (Z.to_nat i) s high (fst tp) (snd tp).

Lemma spread_pos_app norm log s0 a b high tab pos :
  spread_pos norm log s0 (a + b) high tab pos =
  let '(t, p) := spread_pos norm log s0 a high tab pos in spread_pos norm log (s0 + a) b high t p.
Proof.
  revert s0 tab pos; induction a; intros; simpl. { rewrite Nat.add_0_r. auto. }
  destruct (if nth s0 norm 0 >? 0 then _ else _) as [t p]. rewrite IHa.
  replace (S s0 + a)%nat with (s0 + S a)%nat by lia. auto.
Qed.

Lemma sp0_step norm log high tab s : 0 <= s < Zlength norm ->
  sp0 norm log high tab (s + 1) =
  if Znth s norm >? 0 then sp1 log s high (sp0 norm log high tab s) (Znth s norm) else sp0 norm log high tab s.
Proof.
  intros Hs. unfold sp0, sp1. rewrite Z2Nat.inj_add, spread_pos_app by lia.
  destruct (spread_pos norm log 0 (Z.to_nat s) high tab 0) as [t p]. simpl.
  rewrite nthZ, Z2Nat.id by lia. destruct (Znth s norm >? 0); [destruct (spread_one _ _ _ _ _ _); auto | auto].
Qed.

Lemma spread_one_app log s high a b tab pos :
  spread_one log (a + b) s high tab pos =
  let '(t, p) := spread_one log a s high tab pos in spread_one log b s high t p.
Proof. revert tab pos; induction a; intros; simpl; auto. Qed.

Lemma sp1_step log s high tp i : 0 <= i ->
  sp1 log s high tp (i + 1) =
  (upd (fst (sp1 log s high tp i)) (Z.to_nat (snd (sp1 log s high tp i))) s,
   skip_high log (Z.to_nat (2 ^ log)) high (Z.land (snd (sp1 log s high tp i) + fse_step log) (2 ^ log - 1))).
Proof.
  intros Hi. unfold sp1. rewrite Z2Nat.inj_add, spread_one_app by lia.
  destruct (spread_one log (Z.to_nat i) s high (fst tp) (snd tp)) as [t p]. reflexivity.
Qed.

Lemma skip_high_range log f high p : 0 <= log -> 0 <= p < 2 ^ log -> 0 <= skip_high log f high p < 2 ^ log.
Proof.
  intros Hl. revert p; induction f; intros p Hp; simpl; auto.
  destruct (p >? high); auto. apply IHf.
  assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= Z.shiftr (2 ^ log) 1 + Z.shiftr (2 ^ log) 3 + 3).
  { rewrite !Z.shiftr_div_pow2 by lia. assert (0 <= 2 ^ log / 2 ^ 1) by (apply Z.div_pos; lia).
    assert (0 <= 2 ^ log / 2 ^ 3) by (apply Z.div_pos; lia). lia. }
  rewrite land_mod by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma sp1_range log s high tp i : 0 <= log -> 0 <= snd tp < 2 ^ log -> 0 <= i ->
  0 <= snd (sp1 log s high tp i) < 2 ^ log.
Proof.
  intros Hl Hp Hi. rewrite <- (Z2Nat.id i) by lia. induction (Z.to_nat i) as [|n IH].
  - exact Hp.
  - rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite sp1_step by lia. apply skip_high_range; auto.
    assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
    assert (Hs := fse_step_bounds log). unfold fse_step in *.
    rewrite land_mod; [apply Z.mod_pos_bound; lia | | lia].
    rewrite !Z.shiftr_div_pow2 by lia. assert (0 <= 2 ^ log / 2 ^ 1) by (apply Z.div_pos; lia).
    assert (0 <= 2 ^ log / 2 ^ 3) by (apply Z.div_pos; lia). lia.
Qed.

Lemma sp1_len log s high tp i : 0 <= i -> length (fst (sp1 log s high tp i)) = length (fst tp).
Proof.
  intros Hi. rewrite <- (Z2Nat.id i) by lia. induction (Z.to_nat i) as [|n IH]; auto.
  rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite sp1_step by lia. simpl. rewrite upd_length. auto.
Qed.

Lemma spread_one_len log k s high tab pos : length (fst (spread_one log k s high tab pos)) = length tab.
Proof. revert tab pos; induction k; intros; simpl; auto. rewrite IHk, upd_length. auto. Qed.

Lemma spread_one_range log k s high tab pos : 0 <= log -> 0 <= pos < 2 ^ log ->
  0 <= snd (spread_one log k s high tab pos) < 2 ^ log.
Proof.
  intros Hl. revert tab pos; induction k; intros tab pos Hp; simpl; auto. apply IHk.
  apply skip_high_range; auto. assert (0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  rewrite land_mod; [apply Z.mod_pos_bound; lia | | lia].
  rewrite !Z.shiftr_div_pow2 by lia. assert (0 <= 2 ^ log / 2 ^ 1) by (apply Z.div_pos; lia).
  assert (0 <= 2 ^ log / 2 ^ 3) by (apply Z.div_pos; lia). lia.
Qed.

Lemma spread_pos_len norm log n s0 high tab pos : length (fst (spread_pos norm log s0 n high tab pos)) = length tab.
Proof.
  revert s0 tab pos; induction n; intros; simpl; auto.
  destruct (nth s0 norm 0 >? 0).
  - destruct (spread_one log _ _ _ _ _) as [t p] eqn:Ep. rewrite IHn.
    pose proof (spread_one_len log (Z.to_nat (nth s0 norm 0)) (Z.of_nat s0) high tab pos) as L.
    rewrite Ep in L. auto.
  - auto.
Qed.

Lemma spread_pos_range norm log n s0 high tab pos : 0 <= log -> 0 <= pos < 2 ^ log ->
  0 <= snd (spread_pos norm log s0 n high tab pos) < 2 ^ log.
Proof.
  intros Hl. revert s0 tab pos; induction n; intros s0 tab pos Hp; simpl; auto.
  destruct (nth s0 norm 0 >? 0).
  - destruct (spread_one log _ _ _ _ _) as [t p] eqn:Ep. apply IHn.
    pose proof (spread_one_range log (Z.to_nat (nth s0 norm 0)) (Z.of_nat s0) high tab pos Hl Hp) as L.
    rewrite Ep in L. auto.
  - auto.
Qed.

Lemma sp0_len norm log high tab s : length (fst (sp0 norm log high tab s)) = length tab.
Proof. apply spread_pos_len. Qed.

Lemma sp0_range norm log high tab s : 0 <= log -> 0 <= snd (sp0 norm log high tab s) < 2 ^ log.
Proof. intros. apply spread_pos_range; auto. split; [lia|]. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pos_and32 (log P st: Z) : 0 <= log <= 20 -> 0 <= P < 2 ^ 20 -> 0 <= st <= 2 ^ 20 ->
  Int.and (Int.add (Int.repr P) (Int.repr st)) (Int.repr (2 ^ log - 1)) = Int.repr ((P + st) mod 2 ^ log).
Proof.
  intros Hl HP Hs. assert (0 < 2 ^ log <= 2 ^ 20) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  rewrite add_repr. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. rewrite land_mod by lia. auto.
Qed.

Lemma iterp_next log p j : 0 < 2 ^ log -> (iterp log p j + fse_step log) mod 2 ^ log = iterp log p (j + 1).
Proof. intros. unfold iterp. rewrite Zplus_mod_idemp_l. f_equal. lia. Qed.

(* a positive count leaves room: fewer than 2^log low-probability symbols *)
Lemma cnt_pos (l: list Z) (s: Z) : Forall (fun c => -1 <= c) l -> 0 <= s < Zlength l -> 0 < Znth s l ->
  Z.of_nat (length (filter (fun c => (c =? -1)%Z) l)) + Znth s l <= fold_right Z.add 0 (map nxt l).
Proof.
  revert s. induction l as [|a l IH]; intros s Hf Hs Hp; [rewrite Zlength_nil in Hs; lia|].
  inv Hf. rewrite Zlength_cons in Hs. pose proof (cntm1_le_sum l H2) as Hle.
  simpl. unfold nxt at 1. destruct (Z.eq_dec s 0).
  - subst. rewrite Znth_0_cons in Hp. rewrite Znth_0_cons.
    destruct (a =? -1) eqn:E; [apply Z.eqb_eq in E; lia|]. simpl. lia.
  - rewrite Znth_pos_cons in * by lia. specialize (IH (s - 1) H2 ltac:(lia) Hp).
    destruct (a =? -1) eqn:E; simpl; [|apply Z.eqb_neq in E]; lia.
Qed.

Lemma slow_final norm log m : FSE_WF_SLOW -> ncount_ok norm log m -> log <= 9 ->
  fst (sp0 norm log (snd (pl0 norm log (Zlength norm))) (fst (pl0 norm log (Zlength norm))) (Zlength norm))
  = fse_symtab norm log.
Proof.
  intros HW Hn Hl. destruct (HW _ _ _ Hn) as (_ & _ & _ & _ & E).
  pose proof (slow_cover norm log m Hn Hl) as E2. unfold sp0, pl0. rewrite Zlength_correct, Nat2Z.id.
  destruct (place_low norm 0 (length norm) (repeat (-1) (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [t1 h1].
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [t0 h0].
  simpl. rewrite E2, E. auto.
Qed.

Lemma step_eq32 (log: Z) : 0 <= log <= 20 ->
  Int.add (Int.add (Int.shru (Int.repr (2 ^ log)) (Int.repr 1)) (Int.shru (Int.repr (2 ^ log)) (Int.repr 3)))
          (Int.repr 3) = Int.repr (fse_step log).
Proof. intros. rewrite <- step_eq by auto. rewrite Int.repr_unsigned. auto. Qed.

Lemma sp1_0 log s high tp : sp1 log s high tp 0 = tp.
Proof. destruct tp. reflexivity. Qed.

(* ---------- the state loop (Fse.states) ---------- *)

Fixpoint advn (tab next: list Z) (u: nat) : list Z :=
  match u, tab with
  | S u', s :: tab' => advn tab' (upd next (Z.to_nat s) (nth (Z.to_nat s) next 0 + 1)) u'
  | _, _ => next
  end.

Definition mkent (log s x: Z) : fse_entry :=
  {| fe_sym := s; fe_nb := log - highbit x; fe_base := Z.shiftl x (log - highbit x) - 2 ^ log |}.

Lemma states_nth log tab next u d : (u < length tab)%nat ->
  nth u (states log tab next) d = mkent log (nth u tab 0) (nth (Z.to_nat (nth u tab 0)) (advn tab next u) 0).
Proof.
  revert next u; induction tab as [|a tab IH]; intros next u Hu; simpl in Hu; [lia|].
  destruct u; simpl; auto. apply IH. lia.
Qed.

Lemma advn_S tab next u : (u < length tab)%nat ->
  advn tab next (S u) =
  upd (advn tab next u) (Z.to_nat (nth u tab 0)) (nth (Z.to_nat (nth u tab 0)) (advn tab next u) 0 + 1).
Proof.
  revert next u; induction tab as [|a tab IH]; intros next u Hu; simpl in Hu; [lia|].
  destruct u; simpl; [destruct tab; reflexivity | apply IH; lia].
Qed.

Lemma advn_0 tab next : advn tab next 0 = next.
Proof. destruct tab; reflexivity. Qed.

Lemma advn_len tab next u : length (advn tab next u) = length next.
Proof. revert next u; induction tab; intros; destruct u; simpl; auto. rewrite IHtab, upd_length. auto. Qed.

Lemma states_len log tab next : length (states log tab next) = length tab.
Proof. revert next; induction tab; intros; simpl; auto. Qed.

Lemma fse_build_cells norm log : ft_cells (fse_build norm log) = states log (fse_symtab norm log) (map nxt norm).
Proof. unfold fse_build, fse_symtab. destruct (place_low _ _ _ _ _). reflexivity. Qed.

(* the arithmetic of one cell: nextState x >= 1 and its shifted value fits *)
Lemma cell_math (log x: Z) : 0 <= log ->
  0 <= log - highbit x <= log -> 0 <= Z.shiftl x (log - highbit x) - 2 ^ log ->
  Z.shiftl x (log - highbit x) - 2 ^ log + 2 ^ (log - highbit x) <= 2 ^ log ->
  (1 <= x /\ x * 2 ^ (log - highbit x) <= 2 * 2 ^ log /\ x + 1 <= 2 * 2 ^ log /\
   Z.shiftl x (log - highbit x) = x * 2 ^ (log - highbit x))%Z.
Proof.
  intros Hl Hnb Hb Hb2. rewrite Z.shiftl_mul_pow2 in * by lia.
  assert (Hp: 1 <= 2 ^ (log - highbit x)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (HS: 0 < 2 ^ log) by (apply Z.pow_pos_nonneg; lia).
  assert (1 <= x) by nia.
  split3; [lia | nia |]. split; [nia | auto].
Qed.

Lemma snext_all norm : Zlength norm <= 53 ->
  snext norm (Zlength norm) = map (fun z => Vint (Int.repr z)) (map nxt norm) ++ Zrepeat Vundef (53 - Zlength norm).
Proof. intros. unfold snext. rewrite sublist_same by lia. rewrite map_map. auto. Qed.

Lemma cf_nth norm log u : 0 <= u < Zlength (fse_symtab norm log) ->
  Znth u (ft_cells (fse_build norm log)) =
  mkent log (Znth u (fse_symtab norm log))
    (nth (Z.to_nat (Znth u (fse_symtab norm log))) (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u)) 0).
Proof.
  intros Hu. rewrite fse_build_cells.
  rewrite <- (nth_Znth u) by (rewrite Zlength_correct, states_len, <- Zlength_correct; lia).
  rewrite states_nth by (rewrite Zlength_correct in Hu; lia). rewrite nthZ by lia. auto.
Qed.

Lemma advn_step (st nx: list Z) u : 0 <= u < Zlength st ->
  advn st nx (Z.to_nat (u + 1)) =
  upd (advn st nx (Z.to_nat u)) (Z.to_nat (Znth u st)) (nth (Z.to_nat (Znth u st)) (advn st nx (Z.to_nat u)) 0 + 1).
Proof.
  intros Hu. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. rewrite advn_S by (rewrite Zlength_correct in Hu; lia).
  rewrite nthZ by lia. auto.
Qed.

Lemma cell_at_u (k: seqkind) (cF: list fse_entry) (st: list Z) (u S: Z) {d: Inhabitant (val * (val * (val * val)))} :
  Zlength cF = S -> Zlength st = S -> 0 <= u < S -> 0 <= Znth u st ->
  Znth u (map (seqcell k) (sublist 0 u cF) ++ cells0 (sublist u S st)) =
  (Vundef, (Vundef, (Vundef, Vint (Int.repr (Znth u st))))).
Proof.
  intros H1 H2 Hu Hs. rewrite app_Znth2 by (rewrite Zlength_map, Zlength_sublist; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (u - (u - 0)) with 0 by lia.
  unfold cells0. rewrite Znth_map by (rewrite Zlength_sublist; lia). rewrite Znth_sublist by lia.
  unfold cellb, bvz. replace (Znth (0 + u) st <? 0) with false by (symmetry; apply Z.ltb_ge; rewrite Z.add_0_l; lia).
  rewrite Z.add_0_l. auto.
Qed.

Lemma snext_upd (A: list Z) (R: list val) (sym x: Z) : 0 <= sym < Zlength A ->
  upd_Znth sym (map (fun z => Vint (Int.repr z)) A ++ R) (Vint (Int.repr x)) =
  map (fun z => Vint (Int.repr z)) (upd A (Z.to_nat sym) x) ++ R.
Proof.
  intros Hs. rewrite upd_Znth_app1 by (rewrite Zlength_map; lia). f_equal.
  rewrite (upd_upd_Znth A sym x Hs), <- upd_Znth_map. reflexivity.
Qed.

Lemma cells_step (k: seqkind) (cF: list fse_entry) (st: list Z) (u S: Z) :
  Zlength cF = S -> Zlength st = S -> 0 <= u < S ->
  upd_Znth u (map (seqcell k) (sublist 0 u cF) ++ cells0 (sublist u S st)) (seqcell k (Znth u cF)) =
  map (seqcell k) (sublist 0 (u + 1) cF) ++ cells0 (sublist (u + 1) S st).
Proof.
  intros H1 H2 Hu. unfold cells0.
  rewrite (sublist_split 0 u (u + 1) cF) by lia. rewrite (sublist_split u (u + 1) S st) by lia.
  rewrite sublist_len_1 by lia. rewrite sublist_len_1 by lia. rewrite !map_app. simpl.
  rewrite <- app_assoc. rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist; list_solve).
  rewrite Zlength_map, Zlength_sublist by lia. replace (u - (u - 0)) with 0 by lia.
  rewrite upd_Znth0. auto.
Qed.

Lemma shl_xn (x n: Z) : 0 <= n < 31 -> 0 <= x -> x * 2 ^ n <= Int.max_unsigned ->
  Int.shl (Int.repr x) (Int.repr n) = Int.repr (x * 2 ^ n).
Proof.
  intros Hn Hx Hm. assert (1 <= 2 ^ n) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (2 ^ n <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. rewrite two_p_equiv. unfold Int.mul.
  rewrite !Int.unsigned_repr; [auto | rep_lia | nia].
Qed.

Lemma sk_nvals_nth (k: seqkind) (s: Z) : 0 <= s <= sk_max k ->
  @Znth val Vundef s (sk_nvals k) = Vint (Int.repr (sk_bits k s)).
Proof.
  intros Hs. change (@Znth val Vundef s (sk_nvals k)) with (@Znth val Inhabitant_val s (sk_nvals k)).
  rewrite sk_nvals_eq, Znth_map, Znth_upto by (rewrite ?Zlength_upto; lia). auto.
Qed.

Lemma sk_bvals_nth (k: seqkind) (s: Z) : 0 <= s <= sk_max k ->
  @Znth val Vundef s (sk_bvals k) = Vint (Int.repr (sk_base k s)).
Proof.
  intros Hs. change (@Znth val Vundef s (sk_bvals k)) with (@Znth val Inhabitant_val s (sk_bvals k)).
  rewrite sk_bvals_eq, Znth_map, Znth_upto by (rewrite ?Zlength_upto; lia). auto.
Qed.

Lemma seqspace_intro (sh: share) (k: seqkind) (t: fse_table) (log fm: Z) (p: val) :
  ft_log t = log -> fse_ok k t -> 0 <= fm <= Int.max_unsigned ->
  data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr log)) p *
  data_at sh (tarray t_seqSymbol (2 ^ log)) (map (seqcell k) (ft_cells t)) (offset_val 8 p) *
  data_at_ sh (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) p)
  |-- seqspace_at sh k (Some t) p.
Proof.
  intros Hl Hok Hfm. unfold seqspace_at, seqtab_at, seqtab_at_fm. rewrite Hl. Exists fm. entailer!.
Qed.

(* ---------- memory layout ---------- *)

(* the workspace: symbolNext = U16[MaxSeq + 1] at wksp, the spread bytes after it *)
Lemma wksp_split (shw: share) (pw: val) (nw: Z) :
  157 <= nw <= 640 -> field_compatible (tarray tuint nw) [] pw ->
  data_at_ shw (tarray tuint nw) pw =
  data_at_ shw (tarray tushort 53) pw * data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw).
Proof.
  intros Hn Hf. destruct pw as [| | | | | b o]; try (destruct Hf as [Hp _]; contradiction).
  pose proof Hf as (_ & _ & Hsz & Hal & _). simpl in Hsz.
  rewrite !data_at__memory_block.
  rewrite (prop_true_andp _ _ Hf).
  simpl sizeof. rewrite !Z.max_r in * by lia.
  assert (H4: (4 | Ptrofs.unsigned o)).
  { red in Hal. eapply align_compatible_rec_Tarray_inv with (i := 0) in Hal; [|lia].
    inv Hal. simpl in H. inv H. simpl in H0. rewrite Z.add_0_r in H0. auto. }
  rewrite (prop_true_andp (field_compatible (tarray tushort 53) [] (Vptr b o))).
  2:{ split3; [auto | reflexivity |]. split3; [simpl; lia | | split; auto].
      red. apply align_compatible_rec_Tarray. intros j Hj. eapply align_compatible_rec_by_value; [reflexivity|].
      simpl. apply Z.divide_add_r; [ eapply Z.divide_trans; [|exact H4]; exists 2; reflexivity | exists j; lia]. }
  rewrite prop_true_andp.
  2:{ split3; [auto | reflexivity |]. split3; [simpl; rewrite Z.max_r by lia; rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 106) by rep_lia; rewrite Ptrofs.unsigned_repr by rep_lia; lia | | split; auto].
      red. apply align_compatible_rec_Tarray. intros j Hj. eapply align_compatible_rec_by_value; [reflexivity|].
      simpl. apply Z.divide_1_l. }
  rewrite Z.mul_1_l. replace (4 * nw)%Z with (106 + (4 * nw - 106))%Z at 1 by lia.
  simpl offset_val. rewrite <- (Ptrofs.repr_unsigned o) at 1 2. rewrite memory_block_split by rep_lia.
  rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 106) by rep_lia. auto.
Qed.

(* the table field: header cell, the 2^log cells, the rest *)
Lemma dt_split (shd: share) (dt: val) (N S: Z) :
  0 <= S -> 1 + S <= N <= 1000 -> field_compatible (tarray t_seqSymbol N) [] dt ->
  data_at_ shd (tarray t_seqSymbol N) dt =
  data_at_ shd t_seqhdr dt * data_at_ shd (tarray t_seqSymbol S) (offset_val 8 dt) *
  data_at_ shd (tarray t_seqSymbol (N - 1 - S)) (offset_val (8 * (1 + S)) dt).
Proof.
  intros HS HN Hf.
  pose proof (proj1 (field_compatible_Tarray_split t_seqSymbol 1 N dt ltac:(lia)) Hf) as [Hf1 Hf2].
  rewrite (arr_field_address0 _ _ _ _ Hf) in Hf2 by lia.
  rewrite (split2_data_at__Tarray_app 1 N) by lia.
  rewrite (split2_data_at__Tarray_app S (N - 1)) by lia.
  rewrite (arr_field_address0 _ _ _ _ Hf) by lia.
  rewrite (arr_field_address0 _ _ _ _ Hf2) by lia.
  change (sizeof t_seqSymbol) with 8. rewrite offset_offset_val.
  replace (8 * 1 + 8 * S)%Z with (8 * (1 + S))%Z by lia. rewrite sepcon_assoc. f_equal.
  destruct dt as [| | | | | b o]; try (destruct Hf as [Hp _]; contradiction).
  pose proof Hf1 as (_ & _ & Hsz & Hal & _).
  assert (H4: (4 | Ptrofs.unsigned o)).
  { red in Hal. eapply align_compatible_rec_Tarray_inv with (i := 0) in Hal; [|lia].
    unfold t_seqSymbol in Hal. inv Hal; [discriminate|].
    vm_compute in H1. inv H1.
    assert (Hb: align_compatible_rec cenv_cs tuint
                  (Ptrofs.unsigned o + Ctypes.sizeof (Tstruct ___gp_ZSTD_seqSymbol noattr) * 0 + 4)).
    { apply H4 with (i0 := _baseValue); reflexivity. }
    inv Hb. simpl in H. inv H. rewrite Z.mul_0_r, Z.add_0_r in H0. simpl in H0.
    replace (Ptrofs.unsigned o) with (Ptrofs.unsigned o + 4 - 4)%Z by lia.
    apply Z.divide_sub_r; [auto|apply Z.divide_refl]. }
  rewrite !data_at__memory_block. rewrite (prop_true_andp _ _ Hf1).
  rewrite prop_true_andp; [reflexivity|].
  split3; [auto | reflexivity |]. split3; [ | | split; auto].
  - unfold size_compatible in *. change (sizeof t_seqhdr) with 8.
    change (sizeof (tarray t_seqSymbol 1)) with 8 in Hsz. lia.
  - red. eapply align_compatible_rec_Tstruct; [vm_compute; reflexivity | reflexivity |].
    intros i0 t0 z0 Ht Ho. unfold Ctypes.field_type in Ht. simpl co_members in Ht.
    cbn beta iota in Ht. simpl name_member in Ht.
    destruct (ident_eq i0 343967563891343%positive);
      [subst; inv Ht; vm_compute in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|];
       simpl; rewrite Z.add_0_r; auto|].
    destruct (ident_eq i0 353543694627485%positive);
      [subst; inv Ht; vm_compute in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|];
       simpl; apply Z.divide_add_r; [auto | apply Z.divide_refl]|].
    discriminate.
Qed.


Lemma body_ent_buildfse : FSE_WF_SLOW -> FSE_FAST ->
  semax_body Vprog G_B0 f_ZSTD_buildFSETable_body ZSTD_buildFSETable_body_spec.
Proof.
  intros HWF HFAST.
  start_function.
  destruct H as (Hlog & HL & Hrange & Hsum).
  destruct (sk_max_bounds k) as [Hmk Hlk].
  assert (HS: 32 <= 2 ^ log <= 512).
  { split; [change 32 with (2 ^ 5) | change 512 with (2 ^ 9)]; apply Z.pow_le_mono_r; lia. }
  assert (HSk: 2 ^ log <= 2 ^ sk_maxlog k) by (apply Z.pow_le_mono_r; lia).
  assert (HSk9: 2 ^ sk_maxlog k <= 512) by (change 512 with (2 ^ 9); apply Z.pow_le_mono_r; lia).
  remember (gv (sk_gbase k)) as pb eqn:Hpb. remember (gv (sk_gbits k)) as pbits eqn:Hpbits.
  assert_PROP (field_compatible (tarray t_seqSymbol (sk_size k)) [] dt /\
               field_compatible (tarray tuint nw) [] pw) as Hfdw by entailer!.
  destruct Hfdw as [Hfd Hfw].
  rewrite (wksp_split shw pw nw) by auto.
  rewrite (dt_split shd dt (sk_size k) (2 ^ log)) by (first [assumption | unfold sk_size; lia]).
  Intros. forward. forward.
  forward. { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite shl_1 by lia. rewrite tdec_eq by (destruct Hfd; auto).
  rewrite add_repr, Z.sub_add.
  forward.
  forward_if (temp _t'1 (Vint (Int.repr 52))).
  { inv H. }
  { forward. entailer!. }
  forward. rewrite spread_eq by (destruct Hfw; auto).
  forward. forward. forward.
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite ll_eq, sub_repr by lia.
  forward_for_simple_bound (Zlength norm) (EX s: Z,
    PROP ()
    LOCAL (temp _largeLimit (Vint (Int.repr (2 ^ (log - 1))));
           temp _highThreshold (Vint (Int.repr (snd (pl0 norm log s))));
           temp _spread (offset_val 106 pw); temp _symbolNext pw; temp _tableSize (Vint (Int.repr (2 ^ log)));
           temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _tableDecode (offset_val 8 dt);
           lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv; temp _dt dt;
           temp _normalizedCounter pn;
           temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log)); temp _wksp pw)
    SEP (data_at Tsh (Tstruct ___gp_ZSTD_seqSymbol_header noattr)
           (Vint (Int.repr (fm0 norm log s)), Vint (Int.repr log)) v_DTableH;
         zstd_globals gv; data_at_ shd t_seqhdr dt;
         data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fst (pl0 norm log s))) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53) (snext norm s) pw;
         data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert.
  { entailer!. rewrite (cells0_init shd (2 ^ log)). unfold pl0. apply derives_refl. }
  { assert (Hnc := nc_nth nc norm i H1 H2 ltac:(lia)).
    assert (Hnc': @Znth val Vundef i nc = Vint (Int.repr (Znth i norm))) by exact Hnc.
    assert (Hc: -1 <= Znth i norm <= 2 ^ log) by (eapply Forall_Znth in Hrange; eauto).
    assert (Hlen0 := pl0_len norm log i). rewrite Z2Nat.id in Hlen0 by lia.
    pose proof (fm0_step norm log i H) as Hfm.
    pose proof (snext_step norm i H ltac:(lia)) as Hsn.
    pose proof (pl0_step norm log i ltac:(lia)) as Hst.
    pose proof (pl0_high norm log i) as Hh.
    forward.
    { entailer!. rewrite Hnc'. simpl. rewrite Int.signed_repr by rep_lia. rep_lia. }
    rewrite Hnc'.
    forward_if.
    - assert (Em: Znth i norm = -1).
      { rewrite Int.neg_repr in H4. apply repr_inj_signed in H4; rep_lia. }
      pose proof (cntm1_step norm i H) as Hcs. rewrite Em in Hcs. simpl in Hcs.
      pose proof (cntm1_bound norm log (sk_max k) (Z.to_nat (i + 1)) ltac:(split; auto)) as Hcb.
      assert (Hc0: 0 <= cntm1 norm (Z.to_nat i)) by (unfold cntm1; lia).
      rewrite Em in Hst, Hsn. simpl in Hst.
      assert (Hfm': fm0 norm log (i + 1) = fm0 norm log i).
      { rewrite Hfm, Em. replace (2 ^ (log - 1) <=? -1) with false; auto. symmetry; apply Z.leb_gt.
        pose proof (Z.pow_pos_nonneg 2 (log - 1)). lia. }
      destruct (pl0 norm log i) as [t h] eqn:Ept. simpl in Hh, Hlen0.
      forward. forward. forward. forward.
      entailer!.
      + rewrite Hst. auto.
      + rewrite Hfm', Hst. cancel. apply derives_refl'. f_equal. simpl fst.
        apply cells0_upd; lia.
    - assert (Em: Znth i norm <> -1).
      { intros E. apply H4. rewrite E, Int.neg_repr. auto. }
      assert (Hc': 0 <= Znth i norm) by lia.
      replace (Znth i norm =? -1) with false in Hst by (symmetry; apply Z.eqb_neq; auto).
      assert (Hnx: nxt (Znth i norm) = Znth i norm) by (unfold nxt; rewrite (proj2 (Z.eqb_neq _ _) Em); auto).
      rewrite Hnx in Hsn.
      destruct (pl0 norm log i) as [t h] eqn:Ept. simpl in Hh, Hlen0.
      forward.
      rewrite Hnc'.
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
        forward_if (PROPx P (LOCALx Q (SEPx (data_at Tsh (Tstruct ___gp_ZSTD_seqSymbol_header noattr)
          (Vint (Int.repr (fm0 norm log (i + 1))), Vint (Int.repr log)) v_DTableH :: R)))) end.
      + forward. entailer!. rewrite Hfm.
        rewrite Int.signed_repr in H5 by (pose proof (Z.pow_le_mono_r 2 (log - 1) 14); rep_lia).
        replace (2 ^ (log - 1) <=? Znth i norm) with true by (symmetry; apply Z.leb_le; lia). auto.
      + forward. entailer!. rewrite Hfm.
        rewrite Int.signed_repr in H5 by (pose proof (Z.pow_le_mono_r 2 (log - 1) 14); rep_lia).
        replace (2 ^ (log - 1) <=? Znth i norm) with false by (symmetry; apply Z.leb_gt; lia). auto.
      + forward.
        rewrite Hnc'. forward. entailer!.
        rewrite Hst, !zext_small by (change (two_p 16) with 65536; rep_lia). rewrite Hsn. cancel. }
  forward_call (Tsh, shd, v_DTableH, dt, existT (fun t => reptype t) t_seqhdr
                 (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log))).
  { memcpy_side_B. }
  cbv beta iota delta [projT1 projT2].
  pose proof (pl0_high norm log (Zlength norm)) as HhL.
  pose proof (cntm1_bound norm log (sk_max k) (Z.to_nat (Zlength norm)) ltac:(split; auto)) as HcL.
  assert (Hc0L: 0 <= cntm1 norm (Z.to_nat (Zlength norm))) by (unfold cntm1; lia).
  forward_if (PROP ()
    LOCAL (temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
           lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
           temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
           temp _tableLog (Vint (Int.repr log)))
    SEP (data_at Tsh (Tstruct ___gp_ZSTD_seqSymbol_header noattr)
           (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
         data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
         zstd_globals gv;
         data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fse_symtab norm log)) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
         data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw))).
  { (* fast spread *)
    assert (HhS: snd (pl0 norm log (Zlength norm)) = 2 ^ log - 1).
    { rewrite sub_repr in H. destruct (Z.eq_dec (cntm1 norm (Z.to_nat (Zlength norm))) (2 ^ log)) as [E|E].
      - rewrite HhL, E in H. replace (2 ^ log - 1 - 2 ^ log) with (-1) in H by lia.
        apply (f_equal Int.unsigned) in H. rewrite (Int.unsigned_repr (2 ^ log - 1)) in H by rep_lia.
        rewrite Int.unsigned_repr_eq in H. change ((-1) mod Int.modulus) with (Int.modulus - 1) in H. rep_lia.
      - apply repr_inj_unsigned in H; rep_lia. }
    assert (Hnn := no_m1 norm log (Zlength norm) (Forall_impl _ (fun c H => proj1 H) Hrange) ltac:(lia) eq_refl HhS).
    assert (Htab: fst (pl0 norm log (Zlength norm)) = repeat (-1) (Z.to_nat (2 ^ log))).
    { unfold pl0. rewrite place_low_none by auto. auto. }
    rewrite Htab.
    assert (HL53: Zlength norm <= 53) by lia.
    assert (Hst := fse_step_bounds log ltac:(lia)).
    assert (HpL := psum_all norm log Hnn Hsum).
    forward. forward. forward. forward. forward. forward.
    rewrite step_eq by lia. rewrite sub_repr, Int.unsigned_repr by rep_lia.
    change (Int.signed (Int.repr 0)) with 0. change 72340172838076673 with SVADD.
    forward_loop (EX s: Z, EX cs: list val,
      PROP (0 <= s <= Zlength norm; Zlength cs = 4 * nw - 106; sublist 0 (psum norm s) cs = zbytes (sbp norm s))
      LOCAL (temp _s__1 (Vint (Int.repr s)); temp _sv (Vlong (Int64.repr (s * SVADD)));
             temp _pos (Vlong (Int64.repr (psum norm s))); temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
           temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
           temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
           temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
           gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
           temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
         data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
         zstd_globals gv;
         data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
         data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert
    continue: (EX s: Z, EX cs: list val,
      PROP (0 <= s < Zlength norm; Zlength cs = 4 * nw - 106;
            sublist 0 (psum norm (s + 1)) cs = zbytes (sbp norm (s + 1)))
      LOCAL (temp _s__1 (Vint (Int.repr s)); temp _sv (Vlong (Int64.repr (s * SVADD)));
             temp _pos (Vlong (Int64.repr (psum norm (s + 1)))); temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
           temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
           temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
           temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
           gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
           temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
         data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
         zstd_globals gv;
         data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
         data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert
    break: (EX cs: list val,
      PROP (Zlength cs = 4 * nw - 106; sublist 0 (2 ^ log) cs = zbytes (spread_bytes norm))
      LOCAL (temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
           temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
           temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
           temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
           gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
           temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
         data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
         zstd_globals gv;
         data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
         data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert.
    { Exists 0 (Zrepeat Vundef (4 * nw - 106)). entailer!. list_solve. }
    { Intros s cs. forward_if.
      - assert (Hnc := nc_nth nc norm s H1 H2 ltac:(lia)).
        assert (Hnc': @Znth val Vundef s nc = Vint (Int.repr (Znth s norm))) by exact Hnc.
        assert (Hc: 0 <= Znth s norm).
        { rewrite Forall_forall in Hnn. apply Hnn. apply Znth_In; lia. }
        assert (Hc2: Znth s norm <= 2 ^ log).
        { rewrite Forall_forall in Hrange. specialize (Hrange (Znth s norm) ltac:(apply Znth_In; lia)). lia. }
        assert (Hps := psum_step norm s ltac:(lia)).
        assert (Hpm := psum_mono norm (s + 1) (Zlength norm) Hnn ltac:(lia) ltac:(lia)).
        assert (Hp0 := psum_nonneg norm s Hnn).
        assert (Hsb := sbp_step norm s ltac:(lia)).
        assert (Hsl := sbp_len norm s Hnn ltac:(lia)).
        assert (HSV: 0 <= s * SVADD < 2 ^ 64) by (unfold SVADD; lia).
        forward.
        { entailer!. rewrite Hnc'. simpl. rewrite Int.signed_repr by rep_lia. rep_lia. }
        rewrite Hnc'.
        rewrite <- H5.
        forward_call (shw, offset_val 106 pw, cs, psum norm s, (s * SVADD)%Z).
        { red. split3; [auto | lia | lia]. }
        pose proof (write8_ok cs (sbp norm s) (psum norm s) 0 s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl H6
                      ltac:(rewrite Z.add_0_r, sublist_nil; reflexivity)) as (Hw1 & Hw2 & Hw3).
        rewrite Z.add_0_r in Hw1, Hw2, Hw3. rewrite H5 in *.
        forward_loop (EX i: Z, EX cs1: list val,
          PROP (8 <= i <= Z.max 8 (Znth s norm + 7); Zlength cs1 = 4 * nw - 106;
                sublist 0 (psum norm s) cs1 = zbytes (sbp norm s);
                sublist (psum norm s) (psum norm s + i) cs1 = zbytes (Zrepeat s i))
          LOCAL (temp _i (Vint (Int.repr i)); temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
                   temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
                   temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
                   temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
                   temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
                   temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
                   gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
                   temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
                 data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
                 zstd_globals gv;
                 data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
                 data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
                 data_at shn (tarray tshort (Zlength nc)) nc pn;
                 data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
                 data_at shw (tarray tuchar (4 * nw - 106)) cs1 (offset_val 106 pw)))%assert
        continue: (EX i: Z, EX cs1: list val,
          PROP (8 <= i < Znth s norm; Zlength cs1 = 4 * nw - 106;
                sublist 0 (psum norm s) cs1 = zbytes (sbp norm s);
                sublist (psum norm s) (psum norm s + i + 8) cs1 = zbytes (Zrepeat s (i + 8)))
          LOCAL (temp _i (Vint (Int.repr i)); temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
                   temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
                   temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
                   temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
                   temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
                   temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
                   gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
                   temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
                 data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
                 zstd_globals gv;
                 data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
                 data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
                 data_at shn (tarray tshort (Zlength nc)) nc pn;
                 data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
                 data_at shw (tarray tuchar (4 * nw - 106)) cs1 (offset_val 106 pw)))%assert
        break: (EX cs1: list val,
          PROP (Zlength cs1 = 4 * nw - 106; sublist 0 (psum norm (s + 1)) cs1 = zbytes (sbp norm (s + 1)))
          LOCAL (temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
                   temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
                   temp _add (Vlong (Int64.repr SVADD)); temp _step (Vlong (Int64.repr (fse_step log)));
                   temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
                   temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
                   temp _tableDecode (offset_val 8 dt); lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
                   gvars gv; temp _normalizedCounter pn; temp _baseValue pb; temp _nbAdditionalBits pbits;
                   temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
                 data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
                 zstd_globals gv;
                 data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (repeat (-1) (Z.to_nat (2 ^ log)))) (offset_val 8 dt);
                 data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
                 data_at shn (tarray tshort (Zlength nc)) nc pn;
                 data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
                 data_at shw (tarray tuchar (4 * nw - 106)) cs1 (offset_val 106 pw)))%assert.
        { forward. Exists 8 (mem_written cs (psum norm s) 8 (s * SVADD)). entailer!. }
        { Intros i cs1. forward_if.
          - pose proof (write8_ok cs1 (sbp norm s) (psum norm s) i s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl
                          ltac:(assumption) ltac:(assumption)) as (Hw1' & Hw2' & Hw3').
            rewrite <- H9.
            forward_call (shw, offset_val 106 pw, cs1, psum norm s + i, (s * SVADD)%Z).
            { entailer!. destruct Hfw as [Hp _]. destruct pw; try contradiction. simpl. normalize.
              rewrite Z.add_assoc. reflexivity. }
            { red. split3; [auto | lia | lia]. }
            Exists i (mem_written cs1 (psum norm s + i) 8 (s * SVADD)). entailer!.
          - forward. Exists cs1. entailer!.
            rewrite Hps, Hsb, map_app. rewrite (sublist_split 0 (psum norm s) (psum norm s + Znth s norm)) by lia.
            rewrite H10. f_equal.
            replace (sublist (psum norm s) (psum norm s + Znth s norm) cs1)
              with (sublist 0 (Znth s norm) (sublist (psum norm s) (psum norm s + i) cs1))
              by (rewrite sublist_sublist by lia; f_equal; lia).
            rewrite H11. unfold Zrepeat. list_solve. }
        { Intros i cs1. forward. Exists (i + 8) cs1. entailer!. rewrite Z.add_assoc. auto. }
        Intros cs1. forward. Exists s cs1.
        rewrite Int.signed_repr by rep_lia. rewrite add64_repr, <- Hps. entailer!.
      - assert (s = Zlength norm) by lia. subst s. forward. Exists cs. entailer!.
        rewrite <- HpL, <- sbp_all. auto. }
    { Intros s cs. forward. forward. Exists (s + 1) cs. entailer!.
      rewrite Z.mul_add_distr_r, Z.mul_1_l. auto. }
    Intros cs.
    assert (Hsbl: Zlength (spread_bytes norm) = 2 ^ log).
    { rewrite <- sbp_all, sbp_len by (auto; lia). auto. }
    assert (Hsbv: forall j, 0 <= j < 2 ^ log -> Znth j cs = Vint (Int.repr (Znth j (spread_bytes norm)))).
    { intros j Hj. apply (bytes_nth cs (spread_bytes norm) (2 ^ log) j); auto; lia. }
    assert (Hsbr: forall j, 0 <= j < 2 ^ log -> 0 <= Znth j (spread_bytes norm) < Zlength norm).
    { intros j Hj. apply spread_bytes_range. apply Znth_In. lia. }
    forward. forward.
    forward_loop (EX s2: Z,
      PROP (0 <= s2 <= 2 ^ log; Z.even s2 = true)
      LOCAL (temp _s__2 (Vlong (Int64.repr s2)); temp _position (Vlong (Int64.repr ((s2 * fse_step log) mod 2 ^ log)));
             temp _unroll (Vlong (Int64.repr 2)); temp _step (Vlong (Int64.repr (fse_step log)));
               temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
               gvars gv; temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fast_fill log (spread_bytes norm) 0 (Z.to_nat (s2)) (repeat (-1) (Z.to_nat (2 ^ log))))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert
    continue: (EX s2: Z,
      PROP (0 <= s2 < 2 ^ log; Z.even s2 = true)
      LOCAL (temp _s__2 (Vlong (Int64.repr s2));
             temp _position (Vlong (Int64.repr (((s2 + 2) * fse_step log) mod 2 ^ log)));
             temp _unroll (Vlong (Int64.repr 2)); temp _step (Vlong (Int64.repr (fse_step log)));
               temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
               gvars gv; temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fast_fill log (spread_bytes norm) 0 (Z.to_nat (s2 + 2)) (repeat (-1) (Z.to_nat (2 ^ log))))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert
    break: (PROP () LOCAL (temp _unroll (Vlong (Int64.repr 2)); temp _step (Vlong (Int64.repr (fse_step log)));
               temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
               gvars gv; temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log))) SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fast_fill log (spread_bytes norm) 0 (Z.to_nat (2 ^ log)) (repeat (-1) (Z.to_nat (2 ^ log))))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert.
    { forward. Exists 0. entailer!. }
    { Intros s2. forward_if.
      - rewrite Int.unsigned_repr in H8 by rep_lia.
        assert (Hev: s2 + 2 <= 2 ^ log).
        { apply Z.even_spec in H7. destruct H7 as [m Hm].
          assert (E: (2 ^ log = 2 * 2 ^ (log - 1))%Z).
          { replace log with (1 + (log - 1)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
          lia. }
        forward_for_simple_bound 2 (EX u: Z,
          PROP ()
          LOCAL (temp _s__2 (Vlong (Int64.repr s2)); temp _position (Vlong (Int64.repr ((s2 * fse_step log) mod 2 ^ log)));
                 temp _unroll (Vlong (Int64.repr 2)); temp _step (Vlong (Int64.repr (fse_step log)));
                 temp _tableMask (Vlong (Int64.repr (2 ^ log - 1))); temp _spread (offset_val 106 pw); temp _symbolNext pw;
                 temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
                 lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH;
                 gvars gv; temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
               data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
               zstd_globals gv;
               data_at shd (tarray t_seqSymbol (2 ^ log))
                 (cells0 (fast_fill log (spread_bytes norm) 0 (Z.to_nat (s2 + u)) (repeat (-1) (Z.to_nat (2 ^ log)))))
                 (offset_val 8 dt);
               data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
               data_at shn (tarray tshort (Zlength nc)) nc pn;
               data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
               data_at shw (tarray tuchar (4 * nw - 106)) cs (offset_val 106 pw)))%assert.
        { rewrite Z.add_0_r. entailer!. }
        { assert (Hlen := fast_fill_len log (spread_bytes norm) 0 (Z.to_nat (s2 + i)) (repeat (-1) (Z.to_nat (2 ^ log)))).
          rewrite repeat_length in Hlen.
          assert (Hm: 0 <= ((s2 + i) * fse_step log) mod 2 ^ log < 2 ^ log) by (apply Z.mod_pos_bound; lia).
          forward.
          assert (H20: 2 ^ log <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
          pose proof (Z.mod_pos_bound (s2 * fse_step log) (2 ^ log) ltac:(lia)).
          rewrite pos_and by lia.
          rewrite pos_next by lia.
          assert (Hb := Hsbr (s2 + i) ltac:(lia)).
          assert (Hsbv': @Znth val Vundef (s2 + i) cs = Vint (Int.repr (Znth (s2 + i) (spread_bytes norm))))
            by (exact (Hsbv (s2 + i) ltac:(lia))).
          forward.
          { entailer!. rewrite Hsbv'. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
          rewrite Hsbv'.
          forward.
          entailer!. apply derives_refl'. f_equal. replace (s2 + (i + 1)) with (s2 + i + 1) by lia.
          rewrite fast_fill_end, nthZ by lia. apply cells0_upd; [rewrite Zlength_correct, Hlen, Z2Nat.id; lia | lia]. }
        assert (H20: 2 ^ log <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
        pose proof (Z.mod_pos_bound (s2 * fse_step log) (2 ^ log) ltac:(lia)).
        forward. rewrite pos_and by lia. rewrite pos_next by lia.
        Exists s2. entailer!.
      - rewrite Int.unsigned_repr in H8 by rep_lia. assert (s2 = 2 ^ log) by lia. subst s2.
        forward. entailer!. }
    { Intros s2. forward. Exists (s2 + 2). entailer!. apply even_step; auto; lia. }
    assert (Hncok: ncount_ok norm log (sk_max k)) by (repeat split; auto; lia).
    assert (Hfc: fast_fill log (spread_bytes norm) 0 (Z.to_nat (2 ^ log)) (repeat (-1) (Z.to_nat (2 ^ log)))
                 = fse_symtab norm log).
    { rewrite (fast_cover norm log (sk_max k)) by (auto; lia). apply (HFAST norm log (sk_max k)); auto. }
    rewrite Hfc. sep_apply (data_at_data_at_ shw (tarray tuchar (4 * nw - 106)) cs).
    unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. }
  { (* slow spread *)
    assert (Hlen0 := pl0_len norm log (Zlength norm)). rewrite Z2Nat.id in Hlen0 by lia.
    remember (snd (pl0 norm log (Zlength norm))) as high eqn:Ehigh.
    remember (fst (pl0 norm log (Zlength norm))) as tabL eqn:EtabL.
    assert (Hst := fse_step_bounds log ltac:(lia)).
    assert (H20: 2 ^ log <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
    forward. forward. forward.
    rewrite sub_repr, step_eq32 by lia.
    forward_for_simple_bound (Zlength norm) (EX s3: Z,
      PROP ()
      LOCAL (temp _position__1 (Vint (Int.repr (snd (sp0 norm log high tabL s3)))); temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
               temp _highThreshold (Vint (Int.repr high)); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
               temp _normalizedCounter pn; temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
               temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fst (sp0 norm log high tabL s3))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert.
    { entailer!. }
    { rename i into s3. assert (Hnc := nc_nth nc norm s3 H1 H2 ltac:(lia)).
      assert (Hnc': @Znth val Vundef s3 nc = Vint (Int.repr (Znth s3 norm))) by exact Hnc.
      assert (Hc: -1 <= Znth s3 norm <= 2 ^ log).
      { rewrite Forall_forall in Hrange. apply Hrange. apply Znth_In; lia. }
      assert (Hr0 := sp0_range norm log high tabL s3 ltac:(lia)).
      assert (Hl0 := sp0_len norm log high tabL s3).
      assert (Hs0 := sp0_step norm log high tabL s3 H4).
      forward.
      { entailer!. rewrite Hnc'. simpl. rewrite Int.signed_repr by rep_lia. rep_lia. }
      rewrite Hnc'.
      forward_loop (EX i: Z,
        PROP (0 <= i <= Z.max 0 (Znth s3 norm))
        LOCAL (temp _i__1 (Vint (Int.repr i)); temp _n__1 (Vint (Int.repr (Znth s3 norm)));
               temp _s__3 (Vint (Int.repr s3)); temp _position__1 (Vint (Int.repr (snd (sp1 log s3 high (sp0 norm log high tabL s3) i)))); temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
               temp _highThreshold (Vint (Int.repr high)); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
               temp _normalizedCounter pn; temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
               temp _tableLog (Vint (Int.repr log)))
        SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fst (sp1 log s3 high (sp0 norm log high tabL s3) i))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert
      continue: (EX i: Z,
        PROP (0 <= i < Znth s3 norm)
        LOCAL (temp _i__1 (Vint (Int.repr i)); temp _n__1 (Vint (Int.repr (Znth s3 norm)));
               temp _s__3 (Vint (Int.repr s3)); temp _position__1 (Vint (Int.repr (snd (sp1 log s3 high (sp0 norm log high tabL s3) (i + 1))))); temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
               temp _highThreshold (Vint (Int.repr high)); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
               temp _normalizedCounter pn; temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
               temp _tableLog (Vint (Int.repr log)))
        SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fst (sp1 log s3 high (sp0 norm log high tabL s3) (i + 1)))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert
      break: (PROP ()
        LOCAL (temp _n__1 (Vint (Int.repr (Znth s3 norm))); temp _s__3 (Vint (Int.repr s3));
               temp _position__1 (Vint (Int.repr (snd (sp0 norm log high tabL (s3 + 1))))); temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
               temp _highThreshold (Vint (Int.repr high)); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
               temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
               lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
               temp _normalizedCounter pn; temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
               temp _tableLog (Vint (Int.repr log)))
        SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
             data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
             zstd_globals gv;
             data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (fst (sp0 norm log high tabL (s3 + 1)))) (offset_val 8 dt);
             data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
             data_at shn (tarray tshort (Zlength nc)) nc pn;
             data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
             data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert.
      { forward. Exists 0. rewrite sp1_0. entailer!. }
      { Intros i. forward_if.
        - assert (Hcp: 0 < Znth s3 norm) by lia.
          assert (Hh0: 0 <= high).
          { pose proof (cnt_pos norm s3 (Forall_impl _ (fun c H => proj1 H) Hrange) H4 Hcp) as Hcp'.
            unfold cntm1 in HhL. rewrite firstn_all2 in HhL by (rewrite Zlength_correct in *; lia).
            unfold nxt in Hcp'. rewrite Hsum in Hcp'. lia. }
          assert (Hr1 := sp1_range log s3 high (sp0 norm log high tabL s3) i ltac:(lia) Hr0 ltac:(lia)).
          assert (Hl1 := sp1_len log s3 high (sp0 norm log high tabL s3) i ltac:(lia)).
          rewrite Hl0 in Hl1.
          forward.
          rewrite (cells0_upd (fst (sp1 log s3 high (sp0 norm log high tabL s3) i)) (snd (sp1 log s3 high (sp0 norm log high tabL s3) i)) s3) by (rewrite ?Zlength_correct, ?Hl1, <- ?Zlength_correct; lia).
          forward.
          rewrite pos_and32 by lia.
          assert (HP1: 0 <= (snd (sp1 log s3 high (sp0 norm log high tabL s3) i) + fse_step log) mod 2 ^ log < 2 ^ log) by (apply Z.mod_pos_bound; lia).
          forward_while (EX j: Z,
            PROP (0 <= j; forall j', 0 <= j' < j -> iterp log ((snd (sp1 log s3 high (sp0 norm log high tabL s3) i) + fse_step log) mod 2 ^ log) j' > high)
            LOCAL (temp _position__1 (Vint (Int.repr (iterp log ((snd (sp1 log s3 high (sp0 norm log high tabL s3) i) + fse_step log) mod 2 ^ log) j)));
                   temp _i__1 (Vint (Int.repr i)); temp _n__1 (Vint (Int.repr (Znth s3 norm)));
                   temp _s__3 (Vint (Int.repr s3)); temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
                 temp _highThreshold (Vint (Int.repr high)); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
                 temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
                 lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
                 temp _normalizedCounter pn; temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits;
                 temp _tableLog (Vint (Int.repr log)))
            SEP (data_at Tsh t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
                 data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
                 zstd_globals gv;
                 data_at shd (tarray t_seqSymbol (2 ^ log)) (cells0 (upd (fst (sp1 log s3 high (sp0 norm log high tabL s3) i)) (Z.to_nat (snd (sp1 log s3 high (sp0 norm log high tabL s3) i))) s3)) (offset_val 8 dt);
                 data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
                 data_at shn (tarray tshort (Zlength nc)) nc pn;
                 data_at shw (tarray tushort 53) (snext norm (Zlength norm)) pw;
                 data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert.
          { Exists 0. rewrite iterp_0 by lia. entailer!. }
          { entailer!. }
          { match type of HRE with context [iterp log ?P ?J] =>
              assert (Hir: 0 <= iterp log P J < 2 ^ log) by (unfold iterp; apply Z.mod_pos_bound; lia) end.
            rewrite Int.unsigned_repr in HRE by rep_lia.
            forward. rewrite pos_and32 by lia. rewrite iterp_next by lia.
            Exists (j + 1). entailer!. intros j' Hj'. destruct (Z.eq_dec j' j); [subst; lia | apply H8; lia]. }
          match type of HRE with context [iterp log ?P ?J] =>
            assert (Hir: 0 <= iterp log P J < 2 ^ log) by (unfold iterp; apply Z.mod_pos_bound; lia) end.
          try rewrite Int.unsigned_repr in HRE by rep_lia.
          forward. Exists i.
          assert (E1: sp1 log s3 high (sp0 norm log high tabL s3) (i + 1) =
                      (upd (fst (sp1 log s3 high (sp0 norm log high tabL s3) i))
                           (Z.to_nat (snd (sp1 log s3 high (sp0 norm log high tabL s3) i))) s3,
                       iterp log ((snd (sp1 log s3 high (sp0 norm log high tabL s3) i) + fse_step log) mod 2 ^ log) j)).
          { rewrite sp1_step by lia. f_equal. rewrite land_mod by lia. apply skip_high_first; auto; lia. }
          rewrite E1. entailer!.
        - forward.
          assert (E: sp0 norm log high tabL (s3 + 1) = sp1 log s3 high (sp0 norm log high tabL s3) i).
          { rewrite Hs0. destruct (Znth s3 norm >? 0) eqn:Ec.
            - apply Z.gtb_lt in Ec. f_equal. lia.
            - rewrite Z.gtb_ltb, Z.ltb_ge in Ec. assert (i = 0) by lia. subst i. rewrite sp1_0. auto. }
          rewrite E. entailer!. }
      { Intros i. forward. Exists (i + 1). entailer!. }
      unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!. }
    assert (Hncok: ncount_ok norm log (sk_max k)) by (repeat split; auto; lia).
    subst high tabL. rewrite (slow_final norm log (sk_max k)) by (auto; lia).
    entailer!. }
  assert (Hncok: ncount_ok norm log (sk_max k)) by (repeat split; auto; lia).
  destruct (HWF norm log (sk_max k) Hncok) as (Hlg & Hcl & Hfa & _ & _).
  assert (Hst2: Zlength (fse_symtab norm log) = 2 ^ log).
  { rewrite <- Hcl, fse_build_cells, !Zlength_correct, states_len. auto. }
  rewrite snext_all by lia.
  forward_for_simple_bound (2 ^ log) (EX u: Z,
    PROP ()
    LOCAL (temp _tableSize (Vint (Int.repr (2 ^ log))); temp _tableDecode (offset_val 8 dt);
           lvar _DTableH (Tstruct ___gp_ZSTD_seqSymbol_header noattr) v_DTableH; gvars gv;
           temp _symbolNext pw; temp _baseValue pb; temp _nbAdditionalBits pbits; temp _tableLog (Vint (Int.repr log)))
    SEP (data_at Tsh (Tstruct ___gp_ZSTD_seqSymbol_header noattr)
           (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) v_DTableH;
         data_at shd t_seqhdr (Vint (Int.repr (fm0 norm log (Zlength norm))), Vint (Int.repr log)) dt;
         zstd_globals gv;
         data_at shd (tarray t_seqSymbol (2 ^ log))
           (map (seqcell k) (sublist 0 u (ft_cells (fse_build norm log))) ++
            cells0 (sublist u (2 ^ log) (fse_symtab norm log))) (offset_val 8 dt);
         data_at_ shd (tarray t_seqSymbol (sk_size k - 1 - 2 ^ log)) (offset_val (8 * (1 + 2 ^ log)) dt);
         data_at shn (tarray tshort (Zlength nc)) nc pn;
         data_at shw (tarray tushort 53)
           (map (fun z => Vint (Int.repr z)) (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u)) ++
            Zrepeat Vundef (53 - Zlength norm)) pw;
         data_at_ shw (tarray tuchar (4 * nw - 106)) (offset_val 106 pw)))%assert.
  { entailer!. rewrite sublist_same by lia. change (Z.to_nat 0) with O. rewrite advn_0. cancel. }
  { rename i into u.
    assert (Hcu := cf_nth norm log u ltac:(lia)).
    assert (Hfu := proj1 (Forall_Znth _ _) Hfa u ltac:(lia)). rewrite Hcu in Hfu. unfold mkent in Hfu. simpl in Hfu.
    destruct Hfu as (Hsym & Hnb & Hb0 & Hb1).
    assert (HAl: Zlength (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u)) = Zlength norm).
    { rewrite !Zlength_correct, advn_len, map_length. auto. }
    rewrite nthZ in Hcu, Hnb, Hb0, Hb1 by lia.
    destruct (cell_math log _ ltac:(lia) Hnb Hb0 Hb1) as (Hx1 & Hx2 & Hx3 & Hx4).
    assert (HLu := @cell_at_u k (ft_cells (fse_build norm log)) (fse_symtab norm log) u (2 ^ log) (Vundef, (Vundef, (Vundef, Vundef))) Hcl Hst2 H ltac:(lia)).
    forward.
    { entailer!. rewrite HLu. simpl. auto. }
    rewrite HLu. cbv beta iota zeta.
    assert (Hsn: @Znth val Vundef (Znth u (fse_symtab norm log)) (zbytes (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u)) ++ Zrepeat Vundef (53 - Zlength norm)) = Vint (Int.repr (Znth (Znth u (fse_symtab norm log)) (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u))))).
    { rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. auto. }
    forward.
    { entailer!. rewrite Hsn. simpl. rewrite Int.unsigned_repr; rep_lia. }
    rewrite Hsn.
    forward. forward.
    forward_call ((Znth (Znth u (fse_symtab norm log)) (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u))), gv).
    rewrite add_repr, zext_small by (change (two_p 16) with 65536; rep_lia).
    rewrite snext_upd by lia.
    assert (Hadv := advn_step (fse_symtab norm log) (map nxt norm) u ltac:(lia)).
    rewrite nthZ in Hadv by lia.
    remember (map (seqcell k) (sublist 0 u (ft_cells (fse_build norm log))) ++
              cells0 (sublist u (2 ^ log) (fse_symtab norm log))) as L eqn:EL.
    assert (HLl: Zlength L = 2 ^ log) by (subst L; unfold cells0; list_solve).
    remember (Znth u (fse_symtab norm log)) as sym eqn:Esym.
    remember (advn (fse_symtab norm log) (map nxt norm) (Z.to_nat u)) as A eqn:EA.
    remember (Znth sym A) as x eqn:Ex.
    remember (highbit x) as hb eqn:Ehb.
    assert (Hpow: 1 <= 2 ^ (log - hb) <= 2 ^ log) by (split; [change 1 with (2 ^ 0) |]; apply Z.pow_le_mono_r; lia).
    forward.
    forward.
    { entailer!. rewrite upd_Znth_same by lia. simpl. rewrite ?sub_repr, !zext_small by (change (two_p 8) with 256; rep_lia).
      rewrite Int.unsigned_repr; rep_lia. }
    rewrite upd_Znth_same by lia. cbv beta iota zeta. cbn [fst snd].
    rewrite sub_repr, !zext_small by (change (two_p 8) with 256; rep_lia).
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite upd_Znth_same by lia. rewrite upd_Znth_twice by lia. rewrite HLu. cbn [fst snd].
    rewrite shl_xn by rep_lia. rewrite sub_repr, !zext_small by (change (two_p 16) with 65536; rep_lia).
    assert (Hsk := sk_ranges k sym ltac:(lia)).
    rewrite (zg_split k gv). rewrite <- Hpb, <- Hpbits. Intros.
    forward.
    { entailer!. rewrite sk_nvals_nth by lia. simpl. rewrite Int.unsigned_repr; rep_lia. }
    rewrite sk_nvals_nth by lia.
    forward.
    forward.
    { entailer!. rewrite sk_bvals_nth by lia. simpl. auto. }
    rewrite sk_bvals_nth by lia.
    forward.
    repeat first [ rewrite upd_Znth_same by (rewrite ?Zlength_upd_Znth; lia)
                 | rewrite upd_Znth_twice by (rewrite ?Zlength_upd_Znth; lia) ].
    cbn [fst snd]. rewrite <- Hadv.
    match goal with |- context [upd_Znth u L ?c] =>
      replace (upd_Znth u L c) with
        (map (seqcell k) (sublist 0 (u + 1) (ft_cells (fse_build norm log))) ++
         cells0 (sublist (u + 1) (2 ^ log) (fse_symtab norm log))) end.
    2:{ rewrite EL, <- cells_step by auto. f_equal. rewrite Hcu. unfold mkent, seqcell. cbn [fe_base fe_sym fe_nb].
        rewrite zext_small by (change (two_p 8) with 256; rep_lia). rewrite <- Ehb, Hx4. auto. }
    entailer!. rewrite (zg_split k gv). cancel. }
  rewrite sublist_same by lia. rewrite sublist_nil. unfold cells0 at 1. simpl map. rewrite app_nil_r.
  sep_apply (data_at_data_at_ shw (tarray tushort 53)).
  assert (Hok: fse_ok k (fse_build norm log)).
  { unfold fse_ok. rewrite Hlg. split3; [lia | auto |].
    eapply Forall_impl; [|exact Hfa]. intros e (? & ? & ? & ?). lia. }
  assert (Hfm: 0 <= fm0 norm log (Zlength norm) <= Int.max_unsigned) by (unfold fm0; destruct existsb; rep_lia).
  sep_apply (seqspace_intro shd k (fse_build norm log) log (fm0 norm log (Zlength norm)) dt Hlg Hok Hfm).
  entailer!.
  rewrite (wksp_split shw pw nw) by auto. cancel.
Qed.
