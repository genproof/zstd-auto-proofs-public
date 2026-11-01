(* Group ENT: body of FSE_buildDTable_internal. *)
Require Import Zstd.proof.dec.B.ent.EntSpecs Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* ---------- model side: the walk of the slow spread, coverage of the cells ---------- *)

(* one step of the spread: position + step, masked *)
Definition fse_g (log x: Z) : Z := Z.land (x + fse_step log) (2 ^ log - 1).

(* the next position of the slow spread (Fse.spread_one): one step, then skip the low-probability area *)
Definition fse_nxt (log high p: Z) : Z := skip_high log (Z.to_nat (2 ^ log)) high (fse_g log p).

(* the k positions the slow spread writes from p *)
Fixpoint walkpos (log high: Z) (k: nat) (p: Z) : list Z :=
  match k with
  | O => nil
  | S k' => p :: walkpos log high k' (fse_nxt log high p)
  end.

(* C's `while (position > highThreshold) position = (position + step) & tableMask;`: when it stops (after
   j < 2^log steps, the iterates before it above high), it gives skip_high's result *)
Lemma fse_g_range : forall log x, 0 <= log -> 0 <= fse_g log x < 2 ^ log.
Proof.
  intros. unfold fse_g. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Lemma fse_g_iter : forall log n x, 0 <= log -> 0 <= x < 2 ^ log ->
  Nat.iter n (fse_g log) x = Z.modulo (Z.add x (Z.mul (Z.of_nat n) (fse_step log))) (2 ^ log).
Proof.
  intros log n x Hl Hx. induction n as [|n IH]; simpl Nat.iter.
  - rewrite Z.mul_0_l, Z.add_0_r, Z.mod_small by lia. reflexivity.
  - rewrite IH. unfold fse_g. replace (2 ^ log - 1) with (Z.ones log) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma fse_g_period : forall log x, 0 <= log -> 0 <= x < 2 ^ log ->
  Nat.iter (Z.to_nat (2 ^ log)) (fse_g log) x = x.
Proof.
  intros log x Hl Hx. rewrite fse_g_iter by lia. rewrite Z2Nat.id by lia.
  rewrite (Z.mul_comm (2 ^ log)), Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma skip_high_iter : forall log high (j n: nat) x, (j < n)%nat ->
  (forall i, (i < j)%nat -> high < Nat.iter i (fse_g log) x) ->
  Nat.iter j (fse_g log) x <= high ->
  skip_high log n high x = Nat.iter j (fse_g log) x.
Proof.
  intros log high j. induction j as [|j IH]; intros n x Hn Hlt Hle.
  - destruct n as [|n]; [lia|]. simpl in Hle |- *.
    destruct (x >? high) eqn:E; [apply Z.gtb_lt in E; lia|reflexivity].
  - destruct n as [|n]; [lia|]. simpl skip_high.
    assert (H0 : high < x) by (apply (Hlt 0%nat); lia).
    destruct (x >? high) eqn:E; [|rewrite Z.gtb_ltb, Z.ltb_ge in E; lia].
    change (skip_high log n high (Z.land _ _) = Nat.iter (S j) (fse_g log) x) with (skip_high log n high (fse_g log x) = Nat.iter (S j) (fse_g log) x).
    rewrite Nat.iter_succ_r. apply IH; [lia| |].
    + intros i Hi. rewrite <- Nat.iter_succ_r. apply Hlt. lia.
    + rewrite <- Nat.iter_succ_r. exact Hle.
Qed.

Lemma skip_high_while : forall log high x j,
  0 <= log -> 0 <= x < 2 ^ log -> 0 <= j < 2 ^ log ->
  (forall i, 0 <= i < j -> high < Nat.iter (Z.to_nat i) (fse_g log) x) ->
  Nat.iter (Z.to_nat j) (fse_g log) x <= high ->
  skip_high log (Z.to_nat (2 ^ log)) high x = Nat.iter (Z.to_nat j) (fse_g log) x.
Proof.
  intros log high x j Hlog Hx Hj Hlt Hle. apply skip_high_iter; [lia| |exact Hle].
  intros i Hi. specialize (Hlt (Z.of_nat i)). rewrite Nat2Z.id in Hlt. apply Hlt. lia.
Qed.

Section CoverSlow.
Local Open Scope Z_scope.

Lemma cs_nth_upd_ne : forall {A} (l: list A) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof.
  induction l as [|y l IH]; intros i j x d H; destruct i, j; simpl; auto; try congruence.
Qed.

Lemma cs_place_low_S : forall norm s n tab h,
  place_low norm s (S n) tab h =
  if nth s norm 0 =? -1 then place_low norm (S s) n (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)
  else place_low norm (S s) n tab h.
Proof. reflexivity. Qed.

Lemma cs_place_low_le : forall norm n s tab h, snd (place_low norm s n tab h) <= h.
Proof.
  induction n as [|n IH]; intros; [simpl; lia|].
  rewrite cs_place_low_S. destruct (nth s norm 0 =? -1).
  - specialize (IH (S s) (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)). lia.
  - apply IH.
Qed.

Lemma cs_place_low_keep : forall norm n s tab h i,
  Z.of_nat i <= snd (place_low norm s n tab h) ->
  nth i (fst (place_low norm s n tab h)) 0 = nth i tab 0.
Proof.
  induction n as [|n IH]; intros s tab h i Hi; [reflexivity|].
  rewrite cs_place_low_S in *. destruct (nth s norm 0 =? -1).
  - pose proof (cs_place_low_le norm n (S s) (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)).
    rewrite IH by auto. apply cs_nth_upd_ne. lia.
  - apply IH; auto.
Qed.

Lemma cs_place_low_m1 : forall norm k n s tab h,
  (forall i, (i < k)%nat -> nth (s + i) norm 0 = -1) ->
  exists tab', place_low norm s (k + n) tab h = place_low norm (s + k) n tab' (h - Z.of_nat k).
Proof.
  induction k as [|k IH]; intros n s tab h H.
  - exists tab. rewrite Nat.add_0_r, Z.sub_0_r. reflexivity.
  - simpl (S k + n)%nat. rewrite cs_place_low_S.
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Nat.add_0_r in H0. rewrite H0. simpl (-1 =? -1).
    destruct (IH n (S s) (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)) as [tab' E].
    { intros i Hi. rewrite <- (H (S i)) by lia. f_equal. lia. }
    exists tab'. rewrite E. f_equal; lia.
Qed.

Lemma cs_spread_S : forall norm log s n high tab pos,
  spread norm log s (S n) high tab pos =
  let '(tab, pos) := if nth s norm 0 >? 0
                     then spread_one log (Z.to_nat (nth s norm 0)) (Z.of_nat s) high tab pos
                     else (tab, pos) in
  spread norm log (S s) n high tab pos.
Proof. reflexivity. Qed.

Lemma cs_spread_skip : forall norm log high k n s tab pos,
  (forall i, (i < k)%nat -> nth (s + i) norm 0 <= 0) ->
  spread norm log s (k + n) high tab pos = spread norm log (s + k) n high tab pos.
Proof.
  induction k as [|k IH]; intros n s tab pos H.
  - rewrite Nat.add_0_r. reflexivity.
  - simpl (S k + n)%nat. rewrite cs_spread_S.
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Nat.add_0_r in H0.
    destruct (Z.gtb_spec (nth s norm 0) 0); [lia|].
    rewrite IH.
    + f_equal. lia.
    + intros i Hi. replace (S s + i)%nat with (s + S i)%nat by lia. apply H. lia.
Qed.

Lemma cs_spread_one_S : forall log k s high tab pos,
  spread_one log (S k) s high tab pos =
  spread_one log k s high (upd tab (Z.to_nat pos) s) (fse_nxt log high pos).
Proof. reflexivity. Qed.

Lemma cs_skip_high_nonneg : forall log fuel high x, 0 <= log -> 0 <= x -> 0 <= skip_high log fuel high x.
Proof.
  induction fuel as [|f IH]; intros high x Hl Hx; simpl; auto.
  destruct (x >? high); auto. apply IH; auto. apply Z.land_nonneg. right.
  pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) Hl). lia.
Qed.

Lemma cs_spread_one_keep : forall log high k s tab pos j, 0 <= log -> 0 <= pos ->
  ~ In (Z.of_nat j) (walkpos log high k pos) ->
  nth j (fst (spread_one log k s high tab pos)) 0 = nth j tab 0.
Proof.
  induction k as [|k IH]; intros s tab pos j Hl Hp Hn; [reflexivity|].
  rewrite cs_spread_one_S. cbn [walkpos] in Hn.
  rewrite IH; auto.
  - apply cs_nth_upd_ne. intro E. apply Hn. left. lia.
  - unfold fse_nxt. apply cs_skip_high_nonneg; auto. apply fse_g_range; auto.
  - intro. apply Hn. right. auto.
Qed.

Lemma cs_states_sym : forall log tab next, map fe_sym (states log tab next) = tab.
Proof. induction tab; intros; simpl; f_equal; auto. Qed.

Lemma cs_states_neg : forall log tab next, 0 <= log ->
  Forall (fun s => 0 <= s) tab -> In 0 tab -> nth 0 next 0 = 0 ->
  exists e, In e (states log tab next) /\ fe_base e < 0.
Proof.
  induction tab as [|s tab IH]; intros next Hl Hf Hin H0; [destruct Hin|].
  inversion Hf; subst. cbn [states].
  destruct (Z.eq_dec s 0).
  - subst. eexists; split; [left; reflexivity|]. cbn [fe_base]. change (Z.to_nat 0) with 0%nat. rewrite H0, Z.shiftl_0_l.
    pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) Hl). lia.
  - destruct Hin as [?|Hin]; [congruence|].
    destruct (IH (upd next (Z.to_nat s) (nth (Z.to_nat s) next 0 + 1))) as [e [? ?]]; auto.
    + rewrite cs_nth_upd_ne; auto. lia.
    + exists e; split; [right|]; auto.
Qed.

Lemma cs_sum_rep : forall k a,
  fold_right Z.add a (map (fun c => if c =? -1 then 1 else c) (repeat (-1) k)) = Z.of_nat k + a.
Proof. induction k as [|k IH]; intros; [simpl; lia|]. cbn [repeat map fold_right]. rewrite IH. simpl (-1 =? -1). lia. Qed.


Lemma cover_slow_aux : FSE_WF_SLOW -> forall norm log m, ncount_ok norm log m ->
  let high := snd (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) in
  forall j, 0 <= j <= high -> In j (walkpos log high (Z.to_nat (high + 1)) 0).
Proof.
  intros WF norm log m Hok high j Hj.
  destruct (in_dec Z.eq_dec j (walkpos log high (Z.to_nat (high + 1)) 0)) as [?|Hnot]; [auto|exfalso].
  assert (Hlog: 5 <= log <= 15) by apply Hok.
  assert (HS: 32 <= 2 ^ log).
  { replace 32 with (2 ^ 5) by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (Hh: high <= 2 ^ log - 1) by apply cs_place_low_le.
  set (L := Z.to_nat (2 ^ log - 1 - high)).
  set (norm' := 0 :: repeat (-1) L ++ [high + 1]).
  assert (Hlen': length norm' = (L + 2)%nat).
  { unfold norm'. cbn [length]. rewrite app_length, repeat_length. simpl. lia. }
  assert (Hrep: forall i, (i < L)%nat -> nth (S i) norm' 0 = -1).
  { intros i Hi. unfold norm'. cbn [nth]. rewrite app_nth1 by (rewrite repeat_length; lia).
    apply (repeat_spec L). apply nth_In. rewrite repeat_length. lia. }
  assert (Hlast: nth (S L) norm' 0 = high + 1).
  { unfold norm'. cbn [nth]. rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length, Nat.sub_diag. reflexivity. }
  assert (Hok': ncount_ok norm' log (Zlength norm')).
  { split; [lia|]. split; [rewrite Zlength_correct, Hlen'; lia|]. split.
    - unfold norm'. constructor; [lia|]. apply Forall_app; split.
      + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
      + constructor; [lia|constructor].
    - unfold norm'. cbn [map fold_right]. rewrite map_app, fold_right_app. cbn [map fold_right].
      rewrite cs_sum_rep. destruct (high + 1 =? -1) eqn:E; [lia|]. simpl (0 =? -1).
      unfold L. rewrite Z2Nat.id by lia. lia. }
  (* place_low on norm' *)
  assert (Hpl: exists tab', place_low norm' 0 (length norm') (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)
                            = (tab', high)).
  { rewrite Hlen'. replace (L + 2)%nat with (S (L + 1)) by lia. rewrite cs_place_low_S.
    replace (nth 0 norm' 0 =? -1) with false by reflexivity.
    destruct (cs_place_low_m1 norm' L 1 1 (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [tab' E].
    { intros i Hi. apply Hrep. auto. }
    exists tab'. rewrite E. rewrite cs_place_low_S. replace (1 + L)%nat with (S L) by lia.
    rewrite Hlast. destruct (Z.eqb_spec (high + 1) (-1)); [lia|]. simpl.
    f_equal. unfold L. rewrite Z2Nat.id by lia. lia. }
  destruct Hpl as [tab' Hpl].
  assert (Hkeep: nth (Z.to_nat j) tab' 0 = 0).
  { pose proof (cs_place_low_keep norm' (length norm') 0 (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)
                  (Z.to_nat j)) as K. rewrite Hpl in K. simpl in K. rewrite K by lia.
    apply nth_repeat. }
  (* the spread on norm' *)
  destruct (spread_one log (Z.to_nat (high + 1)) (Z.of_nat (S L)) high tab' 0) as [t p] eqn:Esp.
  assert (Hsp: spread norm' log 0 (length norm') high tab' 0 = t).
  { rewrite Hlen'. replace (L + 2)%nat with ((S L) + 1)%nat by lia. rewrite cs_spread_skip.
    - simpl (0 + S L)%nat. rewrite cs_spread_S. rewrite Hlast.
      destruct (Z.gtb_spec (high + 1) 0); [|lia]. rewrite Esp. reflexivity.
    - intros i Hi. destruct i as [|i]; [reflexivity|]. simpl (0 + S i)%nat. rewrite Hrep; lia. }
  assert (Hcells: ft_cells (fse_build norm' log) =
                  states log t (map (fun c => if c =? -1 then 1 else c) norm')).
  { unfold fse_build. rewrite Hpl. rewrite Hsp. reflexivity. }
  destruct (WF norm' log (Zlength norm') Hok') as (_ & Hzl & Hall & _).
  rewrite Hcells in Hzl, Hall.
  assert (Ht0: nth (Z.to_nat j) t 0 = 0).
  { replace t with (fst (spread_one log (Z.to_nat (high + 1)) (Z.of_nat (S L)) high tab' 0))
      by (rewrite Esp; reflexivity).
    rewrite cs_spread_one_keep; auto; try lia. rewrite Z2Nat.id by lia. auto. }
  assert (Htlen: Zlength t = 2 ^ log).
  { rewrite <- Hzl. rewrite <- (cs_states_sym log t) at 1. rewrite !Zlength_correct, map_length. reflexivity. }
  assert (Hnn: Forall (fun s => 0 <= s) t).
  { rewrite <- (cs_states_sym log t (map (fun c => if c =? -1 then 1 else c) norm')).
    apply Forall_map. eapply Forall_impl; [|exact Hall]. simpl. intros e He. lia. }
  assert (Hin0: In 0 t).
  { rewrite <- Ht0. apply nth_In. rewrite Zlength_correct in Htlen. lia. }
  destruct (cs_states_neg log t (map (fun c => if c =? -1 then 1 else c) norm')) as [e [He1 He2]];
    auto; try lia.
  rewrite Forall_forall in Hall. specialize (Hall e He1). lia.
Qed.

End CoverSlow.

(* every cell below the low-probability area is written by the slow spread (high + 1 writes from 0) *)
Lemma cover_slow : FSE_WF_SLOW -> forall norm log m, ncount_ok norm log m ->
  let high := snd (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) in
  forall j, 0 <= j <= high -> In j (walkpos log high (Z.to_nat (high + 1)) 0).
Proof.
  exact cover_slow_aux.
Qed.

Section CoverFastArith.
Local Open Scope Z_scope.

Lemma cover_of_inv : forall M s inv, 0 < M -> (s * inv) mod M = 1 ->
  forall j, 0 <= j < M -> exists i, 0 <= i < M /\ (i * s) mod M = j.
Proof.
  intros M s inv HM Hinv j Hj. exists ((j * inv) mod M). split.
  - apply Z.mod_pos_bound. lia.
  - rewrite Z.mul_mod_idemp_l by lia.
    replace (j * inv * s) with (j * (s * inv)) by ring.
    rewrite <- Z.mul_mod_idemp_r by lia. rewrite Hinv, Z.mul_1_r.
    apply Z.mod_small. lia.
Qed.

Lemma fse_step_inv : forall log, 5 <= log <= 15 ->
  exists inv, (fse_step log * inv) mod 2 ^ log = 1.
Proof.
  intros log Hlog.
  assert (log = 5 \/ log = 6 \/ log = 7 \/ log = 8 \/ log = 9 \/ log = 10 \/ log = 11 \/
          log = 12 \/ log = 13 \/ log = 14 \/ log = 15) as H by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
  [exists 7 | exists 3 | exists 91 | exists 11 | exists 363 | exists 43 | exists 1451 | exists 171
  | exists 5803 | exists 683 | exists 23211]; vm_compute; reflexivity.
Qed.

End CoverFastArith.

(* every cell is written by the fast spread: i * step mod 2^log, i < 2^log, covers all cells *)
Lemma cover_fast : FSE_WF_SLOW -> FSE_FAST -> forall log, 5 <= log <= 15 ->
  forall j, 0 <= j < 2 ^ log -> exists i, 0 <= i < 2 ^ log /\ (i * fse_step log) mod 2 ^ log = j.
Proof.
  intros _ _ log Hlog. destruct (fse_step_inv log Hlog) as [inv Hinv].
  apply (cover_of_inv _ _ inv); [|exact Hinv]. apply Z.pow_pos_nonneg; lia.
Qed.

(* ---------- model side: the C's state, step by step ---------- *)

Definition nx (c: Z) : Z := if c =? -1 then 1 else c.

(* after the first s symbols of the low-probability loop: (symbol table, highThreshold) *)
Definition pl (norm: list Z) (log s: Z) : list Z * Z :=
  place_low norm 0 (Z.to_nat s) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1).

(* DTableH.fastMode after the first s symbols *)
Definition fmp (norm: list Z) (log s: Z) : Z :=
  if existsb (fun c => 2 ^ (log - 1) <=? c) (sublist 0 s norm) then 0 else 1.

Definition cnt1 (l: list Z) : Z := Zlength (filter (fun c => c =? -1) l).

(* the symbol fields of the C table: the cells w says are written hold tab's symbols *)
Definition mkC (n: Z) (w: Z -> bool) (tab: list Z) : list val :=
  map (fun j => if w j then Vint (Int.repr (Znth j tab)) else Vundef) (upto (Z.to_nat n)).

Definition symcells (cs: list val) : list (val * (val * val)) := map (fun v => (Vundef, (v, Vundef))) cs.

Lemma place_low_S : forall norm n tab h,
  place_low norm 0 (S n) tab h =
  let '(t, h') := place_low norm 0 n tab h in
  if nth n norm 0 =? -1 then (upd t (Z.to_nat h') (Z.of_nat n), h' - 1) else (t, h').
Proof.
  intros norm n. assert (G: forall s tab h, place_low norm s (S n) tab h =
    let '(t, h') := place_low norm s n tab h in
    if nth (s + n) norm 0 =? -1 then (upd t (Z.to_nat h') (Z.of_nat (s + n)), h' - 1) else (t, h')).
  { induction n; intros s tab h.
    - simpl. rewrite Nat.add_0_r. destruct (nth s norm 0 =? -1); reflexivity.
    - change (place_low norm s (S (S n)) tab h) with
        (if nth s norm 0 =? -1 then place_low norm (S s) (S n) (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)
         else place_low norm (S s) (S n) tab h).
      change (place_low norm s (S n) tab h) with
        (if nth s norm 0 =? -1 then place_low norm (S s) n (upd tab (Z.to_nat h) (Z.of_nat s)) (h - 1)
         else place_low norm (S s) n tab h).
      replace (s + S n)%nat with (S s + n)%nat by lia.
      destruct (nth s norm 0 =? -1); apply IHn. }
  intros. apply G.
Qed.

Lemma upd_length {A} : forall (l: list A) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; simpl; auto. Qed.

Lemma Zlength_upd {A} : forall (l: list A) i x, Zlength (upd l i x) = Zlength l.
Proof. intros. rewrite !Zlength_correct, upd_length. reflexivity. Qed.

Lemma upd_upd_Znth {A} {d: Inhabitant A} : forall (l: list A) i x, 0 <= i < Zlength l ->
  upd l (Z.to_nat i) x = upd_Znth i l x.
Proof.
  induction l; intros i x Hi. { rewrite Zlength_nil in Hi; lia. }
  rewrite Zlength_cons in Hi. destruct (Z.eq_dec i 0) as [->|Hne].
  - simpl. rewrite upd_Znth0. reflexivity.
  - replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. simpl.
    rewrite upd_Znth_cons by lia. f_equal. apply IHl. lia.
Qed.

Lemma nth_Znth' : forall (l: list Z) s, 0 <= s -> nth (Z.to_nat s) l 0 = Znth s l.
Proof. intros. unfold Znth. rewrite zlt_false by lia. reflexivity. Qed.

Lemma pl_succ norm log s : 0 <= s ->
  pl norm log (s + 1) = let '(t, h) := pl norm log s in
                        if Znth s norm =? -1 then (upd t (Z.to_nat h) s, h - 1) else (t, h).
Proof.
  intros Hs. unfold pl. rewrite Z2Nat.inj_add, Nat.add_1_r, place_low_S by lia.
  rewrite nth_Znth', Z2Nat.id by lia. reflexivity.
Qed.

Lemma pl_len norm log s : 0 <= s -> 0 <= log -> Zlength (fst (pl norm log s)) = 2 ^ log.
Proof.
  intros Hs Hl. pattern s. apply natlike_ind; [ | | exact Hs].
  - unfold pl. simpl. pose proof (Z.pow_pos_nonneg 2 log). rewrite Zlength_repeat; lia.
  - intros x Hx IH. rewrite <- Z.add_1_r, pl_succ by lia. destruct (pl norm log x) as [t h].
    destruct (Znth x norm =? -1); simpl in *; rewrite ?Zlength_upd; auto.
Qed.

Lemma cnt1_app : forall a b, cnt1 (a ++ b) = cnt1 a + cnt1 b.
Proof. intros. unfold cnt1. rewrite filter_app, Zlength_app. reflexivity. Qed.

Lemma cnt1_one : forall c, cnt1 [c] = if c =? -1 then 1 else 0.
Proof. intros. unfold cnt1. simpl. destruct (c =? -1); reflexivity. Qed.

Lemma pl_high norm log s : 0 <= s <= Zlength norm ->
  snd (pl norm log s) = 2 ^ log - 1 - cnt1 (sublist 0 s norm).
Proof.
  intros Hs. destruct Hs as [Hs0 Hs1]. revert Hs1. pattern s. apply natlike_ind; [ | | exact Hs0].
  - intros. unfold pl. simpl. rewrite sublist_nil. unfold cnt1. simpl. rewrite Zlength_nil. lia.
  - intros x Hx IH Hx1. rewrite <- Z.add_1_r in *. rewrite pl_succ by lia.
    rewrite (sublist_split 0 x (x + 1)) by lia. rewrite cnt1_app, sublist_len_1, cnt1_one by lia.
    specialize (IH ltac:(lia)). destruct (pl norm log x) as [t h]. simpl in IH.
    destruct (Znth x norm =? -1); simpl; lia.
Qed.

(* the -1 symbols are fewer than the cells *)
Lemma sum_nx_nonneg : forall l, Forall (fun c => -1 <= c) l -> 0 <= fold_right Z.add 0 (map nx l).
Proof.
  induction l; intros H; simpl. lia. inv H. specialize (IHl H3). unfold nx at 1.
  destruct (a =? -1) eqn:E; [|apply Z.eqb_neq in E]; lia.
Qed.

Lemma cnt1_le_sum : forall l, Forall (fun c => -1 <= c) l -> cnt1 l <= fold_right Z.add 0 (map nx l).
Proof.
  induction l; intros H. { unfold cnt1. simpl. rewrite Zlength_nil. lia. }
  inv H. specialize (IHl H3). change (a :: l) with ([a] ++ l). rewrite cnt1_app, cnt1_one. simpl.
  unfold nx at 1. destruct (a =? -1) eqn:E; [|apply Z.eqb_neq in E]; lia.
Qed.

Lemma sum_nx_app : forall a b, fold_right Z.add 0 (map nx (a ++ b)) =
  fold_right Z.add 0 (map nx a) + fold_right Z.add 0 (map nx b).
Proof. induction a; intros; simpl. lia. rewrite IHa. lia. Qed.

Lemma Zlength_mkC n w tab : 0 <= n -> Zlength (mkC n w tab) = n.
Proof. intros. unfold mkC. rewrite Zlength_map, Zlength_upto. lia. Qed.

Lemma Znth_mkC n w tab j : 0 <= j < n ->
  Znth j (mkC n w tab) = if w j then Vint (Int.repr (Znth j tab)) else Vundef.
Proof. intros. unfold mkC. rewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto; lia). reflexivity. Qed.

Lemma mkC_upd n w tab p v : 0 <= p < n -> Zlength tab = n ->
  upd_Znth p (mkC n w tab) (Vint (Int.repr v)) = mkC n (fun j => orb (w j) (j =? p)) (upd_Znth p tab v).
Proof.
  intros Hp Ht. apply Znth_eq_ext. { rewrite Zlength_upd_Znth, !Zlength_mkC; lia. }
  intros j Hj. rewrite Zlength_upd_Znth, Zlength_mkC in Hj by lia.
  rewrite !Znth_mkC by lia. destruct (Z.eq_dec j p) as [->|Hne].
  - rewrite upd_Znth_same, upd_Znth_same by (rewrite ?Zlength_mkC; lia). rewrite Z.eqb_refl, orb_true_r. reflexivity.
  - rewrite !upd_Znth_diff by (rewrite ?Zlength_mkC; lia). rewrite Znth_mkC by lia.
    replace (j =? p) with false by (symmetry; apply Z.eqb_neq; auto). rewrite orb_false_r. reflexivity.
Qed.

Lemma mkC_ext n w w' tab : 0 <= n -> (forall j, 0 <= j < n -> w j = w' j) -> mkC n w tab = mkC n w' tab.
Proof.
  intros Hn H. apply Znth_eq_ext. { rewrite !Zlength_mkC; lia. }
  intros j Hj. rewrite Zlength_mkC in Hj by lia. rewrite !Znth_mkC, H by lia. reflexivity.
Qed.

Lemma mkC_all n w tab : (forall j, 0 <= j < n -> w j = true) -> Zlength tab = n ->
  mkC n w tab = map (fun z => Vint (Int.repr z)) tab.
Proof.
  intros H Ht. pose proof (Zlength_nonneg tab). apply Znth_eq_ext. { rewrite Zlength_map, Zlength_mkC; lia. }
  intros j Hj. rewrite Zlength_mkC in Hj by lia. rewrite Znth_mkC, H, Znth_map by lia. reflexivity.
Qed.

Lemma mkC_none n tab : 0 <= n -> mkC n (fun _ => false) tab = Zrepeat Vundef n.
Proof.
  intros. apply Znth_eq_ext. { rewrite Zlength_Zrepeat, Zlength_mkC; lia. }
  intros j Hj. rewrite Zlength_mkC in Hj by lia. rewrite Znth_mkC, Znth_Zrepeat by lia. reflexivity.
Qed.

Lemma zext16 x : 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma zext8 x : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof. intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia. Qed.

Lemma symcells_none n : symcells (Zrepeat Vundef n) = Zrepeat (Vundef, (Vundef, Vundef)) n.
Proof. unfold symcells, Zrepeat. rewrite map_repeat. reflexivity. Qed.

Lemma data_at__fdec sh n p :
  data_at_ sh (tarray t_fdec n) p = data_at sh (tarray t_fdec n) (Zrepeat (Vundef, (Vundef, Vundef)) n) p.
Proof. reflexivity. Qed.

Lemma data_at__ushort sh n p :
  data_at_ sh (tarray tushort n) p = data_at sh (tarray tushort n) (Zrepeat Vundef n) p.
Proof. reflexivity. Qed.

Lemma cnt1_nonneg l : 0 <= cnt1 l.
Proof. unfold cnt1. apply Zlength_nonneg. Qed.

Lemma high_range norm log s : Forall (fun c => -1 <= c) norm -> fold_right Z.add 0 (map nx norm) = 2 ^ log ->
  0 <= s < Zlength norm -> Znth s norm = -1 -> 0 <= snd (pl norm log s) < 2 ^ log.
Proof.
  intros Hr Hs Hi Hc. rewrite pl_high by lia. pose proof (cnt1_nonneg (sublist 0 s norm)).
  assert (cnt1 (sublist 0 (s + 1) norm) <= 2 ^ log).
  { assert (E: norm = sublist 0 (s + 1) norm ++ sublist (s + 1) (Zlength norm) norm)
      by (rewrite sublist_rejoin, sublist_same; auto; lia).
    rewrite E, sum_nx_app in Hs. pose proof (sum_nx_nonneg (sublist (s + 1) (Zlength norm) norm)).
    pose proof (cnt1_le_sum (sublist 0 (s + 1) norm)).
    assert (Forall (fun c => -1 <= c) (sublist (s + 1) (Zlength norm) norm)) by (apply Forall_sublist; auto).
    assert (Forall (fun c => -1 <= c) (sublist 0 (s + 1) norm)) by (apply Forall_sublist; auto).
    specialize (H0 H2). specialize (H1 H3). lia. }
  rewrite (sublist_split 0 s (s + 1)), cnt1_app, sublist_len_1, cnt1_one, Hc in H0 by lia. simpl in H0. lia.
Qed.

Lemma symcells_upd cs i v : 0 <= i < Zlength cs ->
  upd_Znth i (symcells cs) (fst (Znth i (symcells cs)), (v, snd (snd (Znth i (symcells cs))))) =
  symcells (upd_Znth i cs v).
Proof. intros. unfold symcells. rewrite Znth_map by lia. simpl. rewrite <- upd_Znth_map. reflexivity. Qed.

Lemma Zlength_symcells cs : Zlength (symcells cs) = Zlength cs.
Proof. unfold symcells. apply Zlength_map. Qed.

Lemma prefix_upd {A} {d: Inhabitant A} (f: Z -> A) (l: list Z) (u: A) s v : 0 <= s < Zlength l ->
  v = f (Znth s l) ->
  upd_Znth s (map f (sublist 0 s l) ++ Zrepeat u (Zlength l - s)) v =
  map f (sublist 0 (s + 1) l) ++ Zrepeat u (Zlength l - (s + 1)).
Proof.
  intros Hs ->. rewrite (sublist_split 0 s (s + 1)), map_app, sublist_len_1 by lia.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, Zlength_sublist, Zlength_Zrepeat; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (s - (s - 0))%Z with 0 by lia.
  replace (Zlength l - s)%Z with (1 + (Zlength l - (s + 1)))%Z by lia.
  rewrite <- Zrepeat_app by lia. rewrite upd_Znth_app1 by (rewrite Zlength_Zrepeat; lia).
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma fmp_succ norm log s : 0 <= s < Zlength norm ->
  fmp norm log (s + 1) = if 2 ^ (log - 1) <=? Znth s norm then 0 else fmp norm log s.
Proof.
  intros. unfold fmp. rewrite (sublist_split 0 s (s + 1)), existsb_app, sublist_len_1 by lia. simpl.
  destruct (existsb _ (sublist 0 s norm)); destruct (2 ^ (log - 1) <=? Znth s norm); reflexivity.
Qed.

(* ---------- memory: the U32 table and workspace as typed regions ---------- *)

Lemma fc_align4 : forall n b ofs, 0 < n -> field_compatible (tarray tuint n) nil (Vptr b ofs) ->
  (4 | Ptrofs.unsigned ofs).
Proof.
  intros n b ofs Hn (_ & _ & _ & Ha & _).
  red in Ha. pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ Ha 0 ltac:(lia)) as H0.
  rewrite Z.mul_0_r, Z.add_0_r in H0. inv H0. inv H. assumption.
Qed.

Ltac ac_struct :=
  eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity | ];
  let i0 := fresh "i0" in let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros i0 ? ? H1 H2; simpl in H1;
  repeat match type of H1 with context [ident_eq i0 ?x] => destruct (ident_eq i0 x); [subst i0; inv H1 | ] end;
  try discriminate;
  vm_compute in H2; inv H2; (eapply align_compatible_rec_by_value; [reflexivity | ]).

Lemma ac_fdec z : (2 | z) -> align_compatible_rec cenv_cs t_fdec z.
Proof.
  intros [k ->]. ac_struct; simpl align_chunk.
  - exists k; lia.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
Qed.

Lemma ac_fhdr z : (2 | z) -> align_compatible_rec cenv_cs t_fhdr z.
Proof.
  intros [k ->]. ac_struct; simpl align_chunk.
  - exists k; lia.
  - exists (k + 1); lia.
Qed.

Lemma ac_fdec_arr z n : (2 | z) -> align_compatible_rec cenv_cs (tarray t_fdec n) z.
Proof.
  intros Hz. apply align_compatible_rec_Tarray. intros. apply ac_fdec.
  change (Ctypes.sizeof t_fdec) with 4. destruct Hz as [k ->]. exists (k + 2 * i)%Z. lia.
Qed.

Lemma dt_split sh dt log : 0 <= log <= 12 ->
  data_at_ sh (tarray tuint (1 + 2 ^ log)) dt |--
  data_at_ sh t_fhdr dt * data_at_ sh (tarray t_fdec (2 ^ log)) (offset_val 4 dt).
Proof.
  intros Hl. rewrite data_at__memory_block. Intros. rename H into Hfc.
  assert (Hp: 1 <= 2 ^ log <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 log); lia|
    change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]).
  destruct dt; try (destruct Hfc; contradiction).
  pose proof (fc_align4 (1 + 2 ^ log) _ _ ltac:(lia) Hfc) as Ha.
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * (1 + 2 ^ log))%Z with (4 + 4 * 2 ^ log)%Z by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr by rep_lia. change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
  rewrite <- (memory_block_data_at_ sh t_fhdr), <- (memory_block_data_at_ sh (tarray t_fdec (2 ^ log))).
  simpl sizeof. rewrite Z.max_r by lia. cancel.
  all: split3; [simpl; auto | reflexivity | ]; split3; [ | | simpl; auto]; red; rewrite Ptrofs.unsigned_repr by rep_lia.
  all: simpl sizeof; try rewrite Z.max_r by lia; try lia.
  - apply ac_fdec_arr. destruct Ha as [k ->]. exists (2 * k + 2)%Z. lia.
  - apply ac_fhdr. destruct Ha as [k ->]. exists (2 * k)%Z. lia.
Qed.

Lemma ac_ushort_arr z n : (2 | z) -> align_compatible_rec cenv_cs (tarray tushort n) z.
Proof.
  intros [k ->]. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | ]. simpl align_chunk.
  change (Ctypes.sizeof tushort) with 2. exists (k + i)%Z. lia.
Qed.

Lemma ac_uchar_arr z n : align_compatible_rec cenv_cs (tarray tuchar n) z.
Proof.
  apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | ]. apply Z.divide_1_l.
Qed.

(* the workspace: symbolNext (U16[N]) then the spread bytes *)
Lemma wk_split sh pw nw N : 0 <= 2 * N <= 4 * nw ->
  data_at_ sh (tarray tuint nw) pw |--
  !! field_compatible (tarray tuint nw) nil pw &&
  (data_at_ sh (tarray tushort N) pw * data_at_ sh (tarray tuchar (4 * nw - 2 * N)) (offset_val (2 * N) pw)).
Proof.
  intros Hn. rewrite data_at__memory_block. Intros. rename H into Hfc.
  apply andp_right; [apply prop_right; auto | ].
  destruct pw; try (destruct Hfc; contradiction).
  assert (Ha: (4 | Ptrofs.unsigned i) \/ nw = 0).
  { destruct (Z.eq_dec nw 0); [right; auto | left]. apply (fc_align4 nw b); auto.
    destruct Hfc as (_ & _ & Hs & _). red in Hs. simpl sizeof in Hs. lia. }
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * nw)%Z with (2 * N + (4 * nw - 2 * N))%Z at 1 by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr, (Ptrofs.unsigned_repr (2 * N)) by rep_lia.
  rewrite <- (memory_block_data_at_ sh (tarray tushort N)), <- (memory_block_data_at_ sh (tarray tuchar _)).
  simpl sizeof. rewrite !Z.max_r by lia. rewrite Z.mul_1_l. cancel.
  all: split3; [simpl; auto | reflexivity | ]; split3; [ | | simpl; auto]; red; rewrite ?Ptrofs.unsigned_repr by rep_lia.
  all: simpl sizeof; rewrite ?Z.max_r by lia; try lia.
  - apply ac_uchar_arr.
  - destruct Ha as [Ha | ->].
    + apply ac_ushort_arr. destruct Ha as [k ->]. exists (2 * k)%Z. lia.
    + assert (N = 0) by lia. subst. apply align_compatible_rec_Tarray. lia.
Qed.

Lemma wk_join sh pw nw N : 0 <= 2 * N <= 4 * nw -> field_compatible (tarray tuint nw) nil pw ->
  data_at_ sh (tarray tushort N) pw * data_at_ sh (tarray tuchar (4 * nw - 2 * N)) (offset_val (2 * N) pw) |--
  data_at_ sh (tarray tuint nw) pw.
Proof.
  intros Hn Hfc. rewrite (data_at__memory_block sh (tarray tuint nw)). apply andp_right; [apply prop_right; auto | ].
  destruct pw; try (destruct Hfc; contradiction).
  destruct Hfc as (_ & _ & Hs & _ & _). red in Hs. simpl sizeof in *. rewrite Z.max_r in * by lia.
  pose proof (Ptrofs.unsigned_range i).
  rewrite <- (Ptrofs.repr_unsigned i).
  replace (4 * nw)%Z with (2 * N + (4 * nw - 2 * N))%Z at 2 by ring.
  rewrite memory_block_split by rep_lia. simpl offset_val.
  rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr, (Ptrofs.unsigned_repr (2 * N)) by rep_lia.
  rewrite !data_at__memory_block. Intros. simpl sizeof. rewrite !Z.max_r by lia. rewrite Z.mul_1_l. cancel.
Qed.

Lemma cnt1_zero_nonneg : forall l, Forall (fun c => -1 <= c) l -> cnt1 l = 0 -> Forall (fun c => 0 <= c) l.
Proof.
  induction l; intros H C; constructor; inv H; change (a :: l) with ([a] ++ l) in C;
    rewrite cnt1_app, cnt1_one in C; pose proof (cnt1_nonneg l).
  - destruct (Z.eqb_spec a (-1)); lia.
  - apply IHl; auto. destruct (a =? -1); lia.
Qed.

Lemma cnt1_pos_in : forall l, 0 < cnt1 l -> In (-1) l.
Proof.
  induction l; intros C. { unfold cnt1 in C. simpl in C. rewrite Zlength_nil in C. lia. }
  change (a :: l) with ([a] ++ l) in C. rewrite cnt1_app, cnt1_one in C.
  destruct (Z.eqb_spec a (-1)). { left; auto. } right. apply IHl. lia.
Qed.

Lemma semax_normal_ret {Espec: OracleKind} Delta P c Q R :
  semax Delta P c (normal_ret_assert Q) -> ENTAIL Delta, Q |-- RA_normal R -> semax Delta P c R.
Proof.
  intros H E. eapply semax_post; [ | | | | exact H]; intros; simpl RA_normal; simpl RA_break;
    simpl RA_continue; simpl RA_return; try exact E; go_lowerx; contradiction.
Qed.

(* ---------- the states loop (Fse.states) ---------- *)

Definition nx_step (nx: list Z) (s: Z) : list Z := upd nx (Z.to_nat s) (nth (Z.to_nat s) nx 0 + 1).

(* symbolNext after the first u cells *)
Definition nexts_after (tab next: list Z) (u: Z) : list Z := fold_left nx_step (sublist 0 u tab) next.

Definition st_cell (log s x: Z) : fse_entry :=
  {| fe_sym := s; fe_nb := log - highbit x; fe_base := Z.shiftl x (log - highbit x) - 2 ^ log |}.

Lemma states_cons log s tab next :
  states log (s :: tab) next = st_cell log s (nth (Z.to_nat s) next 0) :: states log tab (nx_step next s).
Proof. reflexivity. Qed.

Lemma Zlength_states log : forall tab next, Zlength (states log tab next) = Zlength tab.
Proof.
  induction tab; intros. reflexivity. rewrite states_cons, !Zlength_cons, IHtab. reflexivity.
Qed.

Lemma Znth_states log : forall tab next u, 0 <= u < Zlength tab ->
  Znth u (states log tab next) = st_cell log (Znth u tab) (nth (Z.to_nat (Znth u tab)) (nexts_after tab next u) 0).
Proof.
  induction tab; intros next u Hu. { rewrite Zlength_nil in Hu; lia. }
  rewrite Zlength_cons in Hu. rewrite states_cons. destruct (Z.eq_dec u 0) as [->|Hne].
  - rewrite !Znth_0_cons. unfold nexts_after. rewrite sublist_nil. reflexivity.
  - rewrite !Znth_pos_cons by lia. rewrite IHtab by lia. f_equal. f_equal.
    unfold nexts_after. rewrite sublist_0_cons by lia. reflexivity.
Qed.

Lemma nexts_after_succ tab next u : 0 <= u < Zlength tab ->
  nexts_after tab next (u + 1) = nx_step (nexts_after tab next u) (Znth u tab).
Proof.
  intros. unfold nexts_after. rewrite (sublist_split 0 u (u + 1)), fold_left_app, sublist_len_1 by lia.
  reflexivity.
Qed.

Lemma Zlength_nx_step nx s : Zlength (nx_step nx s) = Zlength nx.
Proof. unfold nx_step. apply Zlength_upd. Qed.

Lemma Zlength_nexts_after tab next u : Zlength (nexts_after tab next u) = Zlength next.
Proof.
  unfold nexts_after. generalize (sublist 0 u tab) next. induction l; intros; simpl. reflexivity.
  rewrite IHl, Zlength_nx_step. reflexivity.
Qed.

Lemma fse_build_eq norm log :
  fse_build norm log = {| ft_log := log; ft_cells := states log (fse_symtab norm log) (map nx norm) |}.
Proof.
  unfold fse_build, fse_symtab.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)). reflexivity.
Qed.

(* the cell's state x is in [1, 2^(log+1)) when the cell is well formed *)
Lemma st_cell_x log s x : 0 <= log -> 0 <= x -> 0 <= fe_nb (st_cell log s x) -> 0 <= fe_base (st_cell log s x) ->
  1 <= x < 2 ^ (log + 1).
Proof.
  unfold st_cell, highbit; simpl. intros Hl Hx Hnb Hb.
  destruct (Z.eq_dec x 0) as [->|Hne].
  - simpl in Hb. rewrite Z.sub_0_r, Z.shiftl_0_l in Hb. pose proof (Z.pow_pos_nonneg 2 log). lia.
  - split; [lia|]. destruct (Z.log2_spec x) as [_ H2]; [lia|].
    apply Z.lt_le_trans with (2 ^ Z.succ (Z.log2 x)); auto. apply Z.pow_le_mono_r; lia.
Qed.

Lemma Forall_upd {A} (P: A -> Prop) : forall l i x, Forall P l -> P x -> Forall P (upd l i x).
Proof. induction l; intros [|i] x H Hx; simpl; auto; inv H; constructor; auto. Qed.

Lemma Forall_nth_d {A} (P: A -> Prop) : forall l i d, Forall P l -> P d -> P (nth i l d).
Proof. induction l; intros [|i] d H Hd; simpl; auto; inv H; auto. Qed.

Lemma nexts_nonneg tab next u : Forall (fun v => 0 <= v) next -> Forall (fun v => 0 <= v) (nexts_after tab next u).
Proof.
  unfold nexts_after. generalize (sublist 0 u tab) next. induction l; intros nx H; simpl; auto.
  apply IHl. unfold nx_step. apply Forall_upd; auto.
  pose proof (Forall_nth_d (fun v => 0 <= v) nx (Z.to_nat a) 0 H ltac:(simpl; lia)). simpl in H0. lia.
Qed.

Lemma st_cells_step {B} {dB: Inhabitant B} (f: B -> val * (val * val)) (l1: list B) (l2: list (val * (val * val))) n u e :
  Zlength l1 = n -> Zlength l2 = n -> 0 <= u < n -> e = f (Znth u l1) ->
  upd_Znth u (map f (sublist 0 u l1) ++ sublist u n l2) e = map f (sublist 0 (u + 1) l1) ++ sublist (u + 1) n l2.
Proof.
  intros H1 H2 Hu ->.
  rewrite upd_Znth_app2 by (rewrite Zlength_map, !Zlength_sublist; lia).
  rewrite Zlength_map, Zlength_sublist by lia. replace (u - (u - 0))%Z with 0 by lia.
  rewrite (sublist_split u (u + 1) n l2) by lia. rewrite upd_Znth_app1 by (rewrite Zlength_sublist; lia).
  rewrite (sublist_split 0 u (u + 1) l1), map_app by lia. rewrite <- app_assoc. f_equal.
  rewrite sublist_len_1 by lia. rewrite (sublist_len_1 u l1) by lia.
  rewrite upd_Znth0. reflexivity.
Qed.

(* ---------- the two spreads of FSE_buildDTable_internal, as statements ---------- *)

Definition bd_fast_stmt : statement := ltac:(
  let b := eval cbv delta [f_FSE_buildDTable_internal] in (fn_body f_FSE_buildDTable_internal) in
  let b := eval cbv beta iota in b in
  match b with context [Sifthenelse (Ebinop Oeq (Etempvar _highThreshold tuint) _ tint) ?T ?E] => exact T end).

Definition bd_slow_stmt : statement := ltac:(
  let b := eval cbv delta [f_FSE_buildDTable_internal] in (fn_body f_FSE_buildDTable_internal) in
  let b := eval cbv beta iota in b in
  match b with context [Sifthenelse (Ebinop Oeq (Etempvar _highThreshold tuint) _ tint) ?T ?E] => exact E end).

Definition bd_Delta : tycontext := func_tycontext f_FSE_buildDTable_internal Vprog G_B0 nil.

(* the state before `if (highThreshold == tableSize - 1)`: the low-probability symbols are placed (pl), symbolNext
   holds next0 (nx), the header is written *)
Definition bd_pre (norm: list Z) (log: Z) (nc: list val) (pn: val) (bd: block) (od: ptrofs) (bw: block) (ow: ptrofs)
    (nw: Z) (shd shn shw: share) (vh: val) (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (temp _highThreshold (Vint (Int.repr (snd (pl norm log (Zlength norm)))));
         temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
         temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
         temp _tableDecode (offset_val 4 (Vptr bd od));
         lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
         temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
  SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
       data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
       data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
       data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
       data_at shd (tarray t_fdec (2 ^ log))
         (symcells (mkC (2 ^ log) (fun j => snd (pl norm log (Zlength norm)) <? j) (fst (pl norm log (Zlength norm)))))
         (offset_val 4 (Vptr bd od));
       zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn).

(* the state after the spread: every cell's symbol is fse_symtab's *)
Definition bd_mid (norm: list Z) (log: Z) (nc: list val) (pn: val) (bd: block) (od: ptrofs) (bw: block) (ow: ptrofs)
    (nw: Z) (shd shn shw: share) (vh: val) (gv: globals) : environ -> mpred :=
  PROP ()
  LOCAL (temp _tableSize (Vint (Int.repr (2 ^ log))); temp _symbolNext (Vptr bw ow);
         temp _tableDecode (offset_val 4 (Vptr bd od));
         lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
         temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
  SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
       data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
       data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
       data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
       data_at shd (tarray t_fdec (2 ^ log)) (symcells (map (fun z => Vint (Int.repr z)) (fse_symtab norm log)))
         (offset_val 4 (Vptr bd od));
       zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn).

(* the pure facts of the spec's precondition *)
Definition bd_facts (norm: list Z) (log: Z) (nc: list val) (nw: Z) (shd shn shw: share) : Prop :=
  writable_share shd /\ readable_share shn /\ writable_share shw /\
  ncount_ok norm log 255 /\ log <= 12 /\
  Zlength norm <= Zlength nc /\ sublist 0 (Zlength norm) nc = map (fun x => Vint (Int.repr x)) norm /\
  2 * Zlength norm + 2 ^ log + 8 <= 4 * nw <= Int.max_unsigned.

(* the model lemmas above, as hypotheses of the segment lemmas *)
Definition COVER_FAST : Prop := forall log, 5 <= log <= 15 ->
  forall j, 0 <= j < 2 ^ log -> exists i, 0 <= i < 2 ^ log /\ (i * fse_step log) mod 2 ^ log = j.

Definition COVER_SLOW : Prop := forall norm log m, ncount_ok norm log m ->
  let high := snd (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) in
  forall j, 0 <= j <= high -> In j (walkpos log high (Z.to_nat (high + 1)) 0).

Definition G_PERIOD : Prop := forall log x, 0 <= log -> 0 <= x < 2 ^ log ->
  Nat.iter (Z.to_nat (2 ^ log)) (fse_g log) x = x.

Definition SKIP_WHILE : Prop := forall log high x j,
  0 <= log -> 0 <= x < 2 ^ log -> 0 <= j < 2 ^ log ->
  (forall i, 0 <= i < j -> high < Nat.iter (Z.to_nat i) (fse_g log) x) ->
  Nat.iter (Z.to_nat j) (fse_g log) x <= high ->
  skip_high log (Z.to_nat (2 ^ log)) high x = Nat.iter (Z.to_nat j) (fse_g log) x.

(* ---------- the fast spread: model helpers (as in body_ent_buildfse.v) ---------- *)

Lemma nthZ (l: list Z) (s: Z) : 0 <= s < Zlength l -> nth (Z.to_nat s) l 0 = Znth s l.
Proof. intros. apply nth_Znth. auto. Qed.

Lemma nc_nth (nc: list val) (norm: list Z) (s: Z) :
  Zlength norm <= Zlength nc -> sublist 0 (Zlength norm) nc = zbytes norm -> 0 <= s < Zlength norm ->
  Znth s nc = Vint (Int.repr (Znth s norm)).
Proof.
  intros H1 H2 Hs. pose proof (Znth_sublist 0 s (Zlength norm) nc ltac:(lia) ltac:(lia)) as E.
  rewrite Z.add_0_r, H2, Znth_map in E by lia. rewrite <- E. auto.
Qed.

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

(* ---------- the fast spread: the C cells as mkC over the cells written so far ---------- *)

Lemma pl_none norm log : Forall (fun c => 0 <= c) norm ->
  pl norm log (Zlength norm) = (repeat 0 (Z.to_nat (2 ^ log)), 2 ^ log - 1).
Proof. intros. unfold pl. apply place_low_none. auto. Qed.

(* cell j is written by the first n steps of the fast spread *)
Fixpoint wr (log: Z) (n: nat) (j: Z) : bool :=
  match n with
  | O => false
  | S n' => orb (wr log n' j) (j =? (Z.of_nat n' * fse_step log) mod 2 ^ log)
  end.

Lemma wr_succ log (n: Z) j : 0 <= n ->
  wr log (Z.to_nat (n + 1)) j = orb (wr log (Z.to_nat n) j) (j =? (n * fse_step log) mod 2 ^ log).
Proof. intros. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl. rewrite Z2Nat.id by lia. auto. Qed.

Lemma wr_spec log n j : (exists i, 0 <= i < Z.of_nat n /\ (i * fse_step log) mod 2 ^ log = j) -> wr log n j = true.
Proof.
  induction n; intros (i & Hi & E). { lia. }
  simpl. destruct (Z.eq_dec i (Z.of_nat n)) as [->|Hne].
  - rewrite E, Z.eqb_refl, orb_true_r. auto.
  - rewrite IHn; auto. exists i. split; auto. lia.
Qed.

Definition ffz (log: Z) (sb: list Z) (n: Z) : list Z :=
  fast_fill log sb 0 (Z.to_nat n) (repeat 0 (Z.to_nat (2 ^ log))).

Lemma Zlength_ffz log sb n : 0 <= log -> Zlength (ffz log sb n) = 2 ^ log.
Proof.
  intros. unfold ffz. rewrite Zlength_correct, fast_fill_len, repeat_length, Z2Nat.id; auto.
  pose proof (Z.pow_pos_nonneg 2 log). lia.
Qed.

Lemma cells_step log sb (n: Z) : 0 <= log -> 0 <= n ->
  upd_Znth ((n * fse_step log) mod 2 ^ log) (mkC (2 ^ log) (wr log (Z.to_nat n)) (ffz log sb n))
    (Vint (Int.repr (Znth n sb))) =
  mkC (2 ^ log) (wr log (Z.to_nat (n + 1))) (ffz log sb (n + 1)).
Proof.
  intros Hl Hn. pose proof (Z.pow_pos_nonneg 2 log ltac:(lia) Hl).
  assert (Hm: 0 <= (n * fse_step log) mod 2 ^ log < 2 ^ log) by (apply Z.mod_pos_bound; lia).
  rewrite mkC_upd by (auto; apply Zlength_ffz; auto).
  unfold ffz at 2. rewrite fast_fill_end by lia. fold (ffz log sb n).
  rewrite nth_Znth' by lia. rewrite upd_upd_Znth by (rewrite Zlength_ffz; lia).
  apply mkC_ext; [lia|]. intros j Hj. rewrite wr_succ by lia. auto.
Qed.

Lemma cells_init norm log : 0 <= log -> Forall (fun c => 0 <= c) norm ->
  mkC (2 ^ log) (fun j => snd (pl norm log (Zlength norm)) <? j) (fst (pl norm log (Zlength norm))) =
  mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0).
Proof.
  intros Hl Hf. rewrite pl_none by auto. simpl. unfold ffz. simpl.
  apply mkC_ext. { pose proof (Z.pow_pos_nonneg 2 log). lia. }
  intros j Hj. apply Z.ltb_ge. lia.
Qed.

Lemma cells_final norm log m : FSE_FAST -> COVER_FAST -> ncount_ok norm log m -> Forall (fun c => 0 <= c) norm ->
  mkC (2 ^ log) (wr log (Z.to_nat (2 ^ log))) (ffz log (spread_bytes norm) (2 ^ log)) =
  map (fun z => Vint (Int.repr z)) (fse_symtab norm log).
Proof.
  intros HF HC Hn Hf. destruct Hn as (Hl & Hn2). rewrite mkC_all.
  - f_equal. apply (HF norm log m); auto. split; auto.
  - intros j Hj. apply wr_spec. destruct (HC log Hl j Hj) as (i & Hi & E). exists i.
    rewrite Z2Nat.id by lia. auto.
  - apply Zlength_ffz. lia.
Qed.

(* the fast spread (no -1 symbol): the symbols in order into the spread bytes (MEM_write64), then cell
   (i * step) mod 2^log gets the i-th (FSE_FAST, COVER_FAST: every cell is written) *)
Lemma bd_fast_ok {Espec: OracleKind} : FSE_FAST -> COVER_FAST ->
  forall norm log nc pn bd od bw ow nw shd shn shw vh gv,
  bd_facts norm log nc nw shd shn shw -> Forall (fun c => 0 <= c) norm ->
  semax bd_Delta (bd_pre norm log nc pn bd od bw ow nw shd shn shw vh gv) bd_fast_stmt
    (normal_ret_assert (bd_mid norm log nc pn bd od bw ow nw shd shn shw vh gv)).
Proof.
  intros HF HC norm log nc pn bd od bw ow nw shd shn shw vh gv Hfacts Hnn.
  unfold bd_pre, bd_mid, bd_Delta, bd_fast_stmt.
  destruct Hfacts as (Hshd & Hshn & Hshw & Hok & Hl12 & Hnc1 & Hnc2 & Hnw).
  assert (Hlog: 5 <= log <= 15) by (destruct Hok; lia).
  assert (Hp12: 32 <= 2 ^ log <= 4096).
  { split; [change 32 with (2 ^ 5) | change 4096 with (2 ^ 12)]; apply Z.pow_le_mono_r; lia. }
  destruct Hok as (Hl & HN & Hrange & Hsum).
  assert (HpL := psum_all norm log Hnn Hsum).
  assert (Hst := fse_step_bounds log ltac:(lia)).
  rewrite cells_init by (auto; lia). rewrite pl_none by auto. simpl fst; simpl snd.
  abbreviate_semax.
  forward. forward.
  rewrite step_eq by lia. rewrite sub_repr, Int.unsigned_repr by rep_lia.
  forward. forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0. change 72340172838076673 with SVADD.
  forward_loop (EX s: Z, EX cs: list val,
      PROP (0 <= s <= Zlength norm; Zlength cs = 4 * nw - 2 * Zlength norm; sublist 0 (psum norm s) cs = zbytes (sbp norm s))
      LOCAL (temp _s__1 (Vint (Int.repr s)); temp _sv (Vlong (Int64.repr (s * SVADD)));
             temp _pos (Vlong (Int64.repr (psum norm s))); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
    continue: (EX s: Z, EX cs: list val,
      PROP (0 <= s < Zlength norm; Zlength cs = 4 * nw - 2 * Zlength norm;
            sublist 0 (psum norm (s + 1)) cs = zbytes (sbp norm (s + 1)))
      LOCAL (temp _s__1 (Vint (Int.repr s)); temp _sv (Vlong (Int64.repr (s * SVADD)));
             temp _pos (Vlong (Int64.repr (psum norm (s + 1)))); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
    break: (EX cs: list val,
      PROP (Zlength cs = 4 * nw - 2 * Zlength norm; sublist 0 (2 ^ log) cs = zbytes (spread_bytes norm))
      LOCAL (temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
  { Exists 0 (Zrepeat Vundef (4 * nw - 2 * Zlength norm)). entailer!. list_solve. }
  { Intros s cs. forward_if.
    - assert (Hnc := nc_nth nc norm s Hnc1 Hnc2 ltac:(lia)).
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
      rewrite <- H0.
      forward_call (shw, offset_val (2 * Zlength norm) (Vptr bw ow), cs, psum norm s, (s * SVADD)%Z).
      { entailer!. simpl. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
        rewrite Int64.unsigned_repr by rep_lia. rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity. }
      { red. split3; [auto | lia | lia]. }
      pose proof (write8_ok cs (sbp norm s) (psum norm s) 0 s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl H1
                    ltac:(rewrite Z.add_0_r, sublist_nil; reflexivity)) as (Hw1 & Hw2 & Hw3).
      rewrite Z.add_0_r in Hw1, Hw2, Hw3. rewrite Z.add_0_l in Hw3. rewrite H0 in *.
      forward.
      forward_loop (EX i: Z, EX cs1: list val,
          PROP (8 <= i <= Z.max 8 (Znth s norm + 7); Zlength cs1 = 4 * nw - 2 * Zlength norm;
                sublist 0 (psum norm s) cs1 = zbytes (sbp norm s);
                sublist (psum norm s) (psum norm s + i) cs1 = zbytes (Zrepeat s i))
          LOCAL (temp _i (Vint (Int.repr i)); temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
             temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
             temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs1 (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
        continue: (EX i: Z, EX cs1: list val,
          PROP (8 <= i < Znth s norm; Zlength cs1 = 4 * nw - 2 * Zlength norm;
                sublist 0 (psum norm s) cs1 = zbytes (sbp norm s);
                sublist (psum norm s) (psum norm s + i + 8) cs1 = zbytes (Zrepeat s (i + 8)))
          LOCAL (temp _i (Vint (Int.repr i)); temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
             temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
             temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs1 (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
        break: (EX cs1: list val,
          PROP (Zlength cs1 = 4 * nw - 2 * Zlength norm; sublist 0 (psum norm (s + 1)) cs1 = zbytes (sbp norm (s + 1)))
          LOCAL (temp _n (Vint (Int.repr (Znth s norm))); temp _s__1 (Vint (Int.repr s));
             temp _sv (Vlong (Int64.repr (s * SVADD))); temp _pos (Vlong (Int64.repr (psum norm s)));
             temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
          SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs1 (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat 0)) (ffz log (spread_bytes norm) 0)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
      { Exists 8 (mem_written cs (psum norm s) 8 (s * SVADD)). entailer!. }
      { Intros i cs1. forward_if.
        - pose proof (write8_ok cs1 (sbp norm s) (psum norm s) i s ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsl
                        ltac:(assumption) ltac:(assumption)) as (Hw1' & Hw2' & Hw3').
          rewrite <- H4.
          forward_call (shw, offset_val (2 * Zlength norm) (Vptr bw ow), cs1, psum norm s + i, (s * SVADD)%Z).
          { entailer!. simpl. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
            rewrite Int64.unsigned_repr by rep_lia. rewrite !Ptrofs.add_assoc, !ptrofs_add_repr. reflexivity. }
          { red. split3; [auto | lia | lia]. }
          Exists i (mem_written cs1 (psum norm s + i) 8 (s * SVADD)). entailer!.
        - forward. Exists cs1. entailer!.
          rewrite Hps, Hsb, map_app. rewrite (sublist_split 0 (psum norm s) (psum norm s + Znth s norm)) by lia.
          rewrite H5. f_equal.
          replace (sublist (psum norm s) (psum norm s + Znth s norm) cs1)
            with (sublist 0 (Znth s norm) (sublist (psum norm s) (psum norm s + i) cs1))
            by (rewrite sublist_sublist by lia; f_equal; lia).
          rewrite H6. unfold Zrepeat. list_solve. }
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
  forward. forward. forward.
  forward_loop (EX s2: Z,
      PROP (0 <= s2 <= 2 ^ log; Z.even s2 = true)
      LOCAL (temp _s__2 (Vlong (Int64.repr s2)); temp _position (Vlong (Int64.repr ((s2 * fse_step log) mod 2 ^ log)));
             temp _unroll (Vlong (Int64.repr 2)); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat s2)) (ffz log (spread_bytes norm) s2)))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
    continue: (EX s2: Z,
      PROP (0 <= s2 < 2 ^ log; Z.even s2 = true)
      LOCAL (temp _s__2 (Vlong (Int64.repr s2)); temp _position (Vlong (Int64.repr (((s2 + 2) * fse_step log) mod 2 ^ log)));
             temp _unroll (Vlong (Int64.repr 2)); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat (s2 + 2))) (ffz log (spread_bytes norm) (s2 + 2))))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert
    break: (PROP ()
      LOCAL (temp _unroll (Vlong (Int64.repr 2)); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
      SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat (2 ^ log))) (ffz log (spread_bytes norm) (2 ^ log))))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
  { Exists 0. entailer!. }
  { Intros s2. forward_if.
    - rewrite Int.unsigned_repr in H3 by rep_lia.
      assert (Hev: s2 + 2 <= 2 ^ log).
      { apply Z.even_spec in H2. destruct H2 as [m Hm].
        assert (E: (2 ^ log = 2 * 2 ^ (log - 1))%Z).
        { replace log with (1 + (log - 1)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
        lia. }
      forward_for_simple_bound 2 (EX u: Z,
        PROP ()
        LOCAL (temp _s__2 (Vlong (Int64.repr s2)); temp _position (Vlong (Int64.repr ((s2 * fse_step log) mod 2 ^ log)));
               temp _unroll (Vlong (Int64.repr 2)); temp _add (Vlong (Int64.repr SVADD));
             temp _step (Vlong (Int64.repr (fse_step log))); temp _tableMask (Vlong (Int64.repr (2 ^ log - 1)));
             temp _highThreshold (Vint (Int.repr (2 ^ log - 1))); temp _tableSize (Vint (Int.repr (2 ^ log)));
             temp _maxSV1 (Vint (Int.repr (Zlength norm))); temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow));
             temp _symbolNext (Vptr bw ow); temp _tableDecode (offset_val 4 (Vptr bd od));
             lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv; temp _dt (Vptr bd od);
             temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
        SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
             data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
             data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
             data_at shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs (offset_val (2 * Zlength norm) (Vptr bw ow));
             data_at shd (tarray t_fdec (2 ^ log)) (symcells (mkC (2 ^ log) (wr log (Z.to_nat (s2 + u))) (ffz log (spread_bytes norm) (s2 + u))))
               (offset_val 4 (Vptr bd od));
             zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
      { rewrite Z.add_0_r. entailer!. }
      { assert (Hm: 0 <= ((s2 + i) * fse_step log) mod 2 ^ log < 2 ^ log) by (apply Z.mod_pos_bound; lia).
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
        rewrite zext8 by rep_lia. rewrite symcells_upd by (rewrite Zlength_mkC; lia).
        replace (s2 + (i + 1)) with (s2 + i + 1) by lia. rewrite cells_step by lia. entailer!. }
      assert (H20: 2 ^ log <= 2 ^ 20) by (apply Z.pow_le_mono_r; lia).
      pose proof (Z.mod_pos_bound (s2 * fse_step log) (2 ^ log) ltac:(lia)).
      forward. rewrite pos_and by lia. rewrite pos_next by lia.
      Exists s2. entailer!.
    - rewrite Int.unsigned_repr in H3 by rep_lia. assert (s2 = 2 ^ log) by lia. subst s2.
      forward. entailer!. }
  { Intros s2. forward. Exists (s2 + 2). entailer!. apply even_step; auto; lia. }
  rewrite (cells_final norm log 255) by (auto; split; auto).
  sep_apply (data_at_data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) cs).
  unfold POSTCONDITION, abbreviate. simpl_ret_assert. entailer!.
Qed.

(* ---------- the slow spread: model helpers ---------- *)

Lemma spread_one_unfold log k sym h tab p :
  spread_one log (S k) sym h tab p = spread_one log k sym h (upd tab (Z.to_nat p) sym) (fse_nxt log h p).
Proof. reflexivity. Qed.

Lemma spread_one_S log k sym h tab p :
  spread_one log (S k) sym h tab p =
  let '(t, q) := spread_one log k sym h tab p in (upd t (Z.to_nat q) sym, fse_nxt log h q).
Proof.
  revert tab p. induction k; intros tab p. { reflexivity. }
  rewrite spread_one_unfold, IHk. rewrite <- spread_one_unfold. reflexivity.
Qed.

Lemma spread_pos_S norm log s0 n h tab p :
  spread_pos norm log s0 (S n) h tab p =
  let '(t, q) := spread_pos norm log s0 n h tab p in
  if nth (s0 + n) norm 0 >? 0 then spread_one log (Z.to_nat (nth (s0 + n) norm 0)) (Z.of_nat (s0 + n)) h t q
  else (t, q).
Proof.
  revert s0 tab p. induction n; intros s0 tab p.
  - simpl. rewrite Nat.add_0_r. destruct (nth s0 norm 0 >? 0); [destruct (spread_one _ _ _ _ _ _)|]; reflexivity.
  - change (spread_pos norm log s0 (S (S n)) h tab p) with
      (let c := nth s0 norm 0 in
       let '(tab, pos) := if c >? 0 then spread_one log (Z.to_nat c) (Z.of_nat s0) h tab p else (tab, p) in
       spread_pos norm log (S s0) (S n) h tab pos).
    change (spread_pos norm log s0 (S n) h tab p) with
      (let c := nth s0 norm 0 in
       let '(tab, pos) := if c >? 0 then spread_one log (Z.to_nat c) (Z.of_nat s0) h tab p else (tab, p) in
       spread_pos norm log (S s0) n h tab pos).
    replace (s0 + S n)%nat with (S s0 + n)%nat by lia.
    cbv zeta. destruct (if nth s0 norm 0 >? 0 then _ else _) as [t q]. apply IHn.
Qed.

Lemma walkpos_S log h k p :
  walkpos log h (S k) p = walkpos log h k p ++ [Nat.iter k (fse_nxt log h) p].
Proof.
  revert p. induction k; intros p. { reflexivity. }
  change (walkpos log h (S (S k)) p) with (p :: walkpos log h (S k) (fse_nxt log h p)).
  rewrite IHk. rewrite Nat.iter_succ_r. reflexivity.
Qed.

Lemma skip_high_range log f h x : 0 <= log -> 0 <= x < 2 ^ log -> 0 <= skip_high log f h x < 2 ^ log.
Proof.
  revert x. induction f; intros x Hl Hx. { exact Hx. }
  change (skip_high log (S f) h x) with (if x >? h then skip_high log f h (fse_g log x) else x).
  destruct (x >? h). { apply IHf; auto. apply fse_g_range; auto. } exact Hx.
Qed.

Lemma fse_nxt_range log h p : 0 <= log -> 0 <= fse_nxt log h p < 2 ^ log.
Proof. intros. unfold fse_nxt. apply skip_high_range; auto. apply fse_g_range; auto. Qed.

Lemma iter_g_range log j x : 0 <= log -> 0 <= x < 2 ^ log -> 0 <= Nat.iter j (fse_g log) x < 2 ^ log.
Proof. intros. destruct j. exact H0. rewrite Nat.iter_succ. apply fse_g_range; auto. Qed.

Lemma iter_nxt_range log h k : 0 <= log -> 0 <= Nat.iter k (fse_nxt log h) 0 < 2 ^ log.
Proof.
  intros. destruct k. { simpl. pose proof (Z.pow_pos_nonneg 2 log). lia. }
  rewrite Nat.iter_succ. apply fse_nxt_range; auto.
Qed.

(* the number of cells the slow spread writes for the first s symbols *)
Definition kpos (norm: list Z) (s: Z) : Z := fold_right Z.add 0 (map (fun c => Z.max c 0) (sublist 0 s norm)).

Lemma sum_max_app : forall a b, fold_right Z.add 0 (map (fun c => Z.max c 0) (a ++ b)) =
  fold_right Z.add 0 (map (fun c => Z.max c 0) a) + fold_right Z.add 0 (map (fun c => Z.max c 0) b).
Proof. induction a; intros; simpl. lia. rewrite IHa. lia. Qed.

Lemma sum_max_nonneg : forall l, 0 <= fold_right Z.add 0 (map (fun c => Z.max c 0) l).
Proof. induction l; simpl; lia. Qed.

Lemma kpos_succ norm s : 0 <= s < Zlength norm -> kpos norm (s + 1) = kpos norm s + Z.max (Znth s norm) 0.
Proof.
  intros. unfold kpos. rewrite (sublist_split 0 s (s + 1)), sum_max_app, sublist_len_1 by lia. simpl. lia.
Qed.

Lemma kpos_le norm s : 0 <= s <= Zlength norm -> kpos norm s <= kpos norm (Zlength norm).
Proof.
  intros. unfold kpos. rewrite (sublist_split 0 s (Zlength norm) norm), sum_max_app by lia.
  pose proof (sum_max_nonneg (sublist s (Zlength norm) norm)). lia.
Qed.

Lemma sum_nx_split : forall l, Forall (fun c => -1 <= c) l ->
  fold_right Z.add 0 (map nx l) = cnt1 l + fold_right Z.add 0 (map (fun c => Z.max c 0) l).
Proof.
  induction l; intros H. { unfold cnt1. simpl. rewrite ?Zlength_nil. reflexivity. }
  inv H. specialize (IHl H3). change (a :: l) with ([a] ++ l). rewrite cnt1_app, cnt1_one. simpl.
  unfold nx at 1. destruct (a =? -1) eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia.
Qed.

(* the cells the slow spread has written after k writes: the high area (place_low) and the walk *)
Definition wslow (log h: Z) (k: nat) (j: Z) : bool := orb (h <? j) (existsb (Z.eqb j) (walkpos log h k 0)).

Lemma wslow_S log h k j :
  wslow log h (S k) j = orb (wslow log h k j) (j =? Nat.iter k (fse_nxt log h) 0).
Proof.
  unfold wslow. rewrite walkpos_S, existsb_app. simpl. rewrite orb_false_r, orb_assoc. reflexivity.
Qed.

(* one write of the slow spread: the model state, the walk, the written cells *)
Lemma slow_step log h k i s tb p tc q : spread_one log (Z.to_nat i) s h tb p = (tc, q) -> 0 <= i -> 0 <= k ->
  q = Nat.iter (Z.to_nat (k + i)) (fse_nxt log h) 0 ->
  spread_one log (Z.to_nat (i + 1)) s h tb p = (upd tc (Z.to_nat q) s, fse_nxt log h q) /\
  Nat.iter (Z.to_nat (k + (i + 1))) (fse_nxt log h) 0 = fse_nxt log h q /\
  (forall j, wslow log h (Z.to_nat (k + (i + 1))) j = orb (wslow log h (Z.to_nat (k + i)) j) (j =? q)).
Proof.
  intros E Hi Hk Hq.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  replace (Z.to_nat (k + (i + 1))) with (S (Z.to_nat (k + i))) by lia.
  rewrite spread_one_S, E. split; [reflexivity|]. split.
  - rewrite Nat.iter_succ, <- Hq. reflexivity.
  - intros j. rewrite wslow_S, <- Hq. reflexivity.
Qed.

(* the slow spread (some -1 symbol): position walks by step, skipping the low-probability area; it ends at 0
   (FSE_WF_SLOW), so `return ERROR(GENERIC)` is never taken; every cell <= high is written (COVER_SLOW) *)
Lemma bd_slow_ok {Espec: OracleKind} : FSE_WF_SLOW -> COVER_SLOW -> G_PERIOD -> SKIP_WHILE ->
  forall norm log nc pn bd od bw ow nw shd shn shw vh gv,
  bd_facts norm log nc nw shd shn shw -> In (-1) norm ->
  semax bd_Delta (bd_pre norm log nc pn bd od bw ow nw shd shn shw vh gv) bd_slow_stmt
    (normal_ret_assert (bd_mid norm log nc pn bd od bw ow nw shd shn shw vh gv)).
Proof.
  intros WF COV GP SKW norm log nc pn bd od bw ow nw shd shn shw vh gv Hf Hin.
  destruct Hf as (Hshd & Hshn & Hshw & Hok & Hlog12 & HN & Hsub & Hnw).
  pose proof Hok as (Hlog & HN1 & Hrange & Hsum).
  assert (Hsz: 32 <= 2 ^ log <= 4096) by (split; [change 32 with (2 ^ 5) | change 4096 with (2 ^ 12)];
    apply Z.pow_le_mono_r; lia).
  assert (Hnc: forall s, 0 <= s < Zlength norm -> Znth s nc = Vint (Int.repr (Znth s norm))).
  { intros. pose proof (Znth_sublist 0 s (Zlength norm) nc ltac:(lia) ltac:(lia)) as E.
    replace (s + 0)%Z with s in E by lia. rewrite <- E, Hsub, Znth_map by lia. reflexivity. }
  assert (Hr1: Forall (fun c => -1 <= c) norm) by (eapply Forall_impl; [|exact Hrange]; simpl; lia).
  assert (Hcr: forall s, 0 <= s < Zlength norm -> -1 <= Znth s norm <= 2 ^ log)
    by (intros; rewrite Forall_Znth in Hrange; apply Hrange; lia).
  pose proof (sum_nx_split norm Hr1) as Hsplit. change (fold_right Z.add 0 (map nx norm)) with
    (fold_right Z.add 0 (map (fun c => if c =? -1 then 1 else c) norm)) in Hsplit. rewrite Hsum in Hsplit.
  assert (Hc1: 0 < cnt1 norm).
  { assert (I: In (-1) (filter (fun c => c =? -1) norm)) by (apply filter_In; split; auto).
    unfold cnt1. destruct (filter (fun c => c =? -1) norm). { contradiction. }
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
  pose proof (sum_max_nonneg norm) as Hmx.
  pose proof (pl_high norm log (Zlength norm) ltac:(lia)) as Hhi. rewrite sublist_same in Hhi by lia.
  pose proof (pl_len norm log (Zlength norm) ltac:(lia) ltac:(lia)) as Hlen.
  assert (HK: kpos norm (Zlength norm) = snd (pl norm log (Zlength norm)) + 1)
    by (unfold kpos; rewrite sublist_same by lia; lia).
  pose proof (COV norm log 255 Hok) as Hcov. cbv zeta in Hcov.
  pose proof (WF norm log 255 Hok) as Hwf. destruct Hwf as (_ & _ & _ & _ & Hwf).
  unfold bd_pre, bd_mid. unfold pl in *. rewrite ZtoNat_Zlength in *.
  destruct (place_low norm 0 (length norm) (repeat 0 (Z.to_nat (2 ^ log))) (2 ^ log - 1)) as [t0 h] eqn:Epl.
  simpl fst in *; simpl snd in *.
  assert (Hh: -1 <= h <= 2 ^ log - 2) by lia. clear Hhi Epl.
  assert (Hstep: 0 < fse_step log < 2 ^ log).
  { unfold fse_step. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 3) with 8.
    clear -Hsz. remember (2 ^ log) as L. pose proof (Z.div_mod L 2 ltac:(lia)). pose proof (Z.mod_pos_bound L 2 ltac:(lia)).
    pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)). lia. }
  assert (Estep: Int.add (Int.add (Int.shru (Int.repr (2 ^ log)) (Int.repr 1)) (Int.shru (Int.repr (2 ^ log)) (Int.repr 3)))
    (Int.repr 3) = Int.repr (fse_step log)).
  { unfold Int.shru, fse_step. rewrite !Int.unsigned_repr by rep_lia. rewrite !add_repr. reflexivity. }
  unfold bd_slow_stmt, bd_Delta. abbreviate_semax.
  forward. forward. forward.
  rewrite Estep, sub_repr.
  forward_for_simple_bound (Zlength norm)
    (EX s: Z,
     PROP (Zlength (fst (spread_pos norm log 0 (Z.to_nat s) h t0 0)) = 2 ^ log;
           snd (spread_pos norm log 0 (Z.to_nat s) h t0 0) = Nat.iter (Z.to_nat (kpos norm s)) (fse_nxt log h) 0)
     LOCAL (temp _position__1 (Vint (Int.repr (snd (spread_pos norm log 0 (Z.to_nat s) h t0 0))));
            temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
            temp _highThreshold (Vint (Int.repr h));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          data_at shd (tarray t_fdec (2 ^ log))
            (symcells (mkC (2 ^ log) (wslow log h (Z.to_nat (kpos norm s))) (fst (spread_pos norm log 0 (Z.to_nat s) h t0 0))))
            (offset_val 4 (Vptr bd od));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
  { entailer!. change (Z.to_nat 0) with O. unfold kpos. rewrite sublist_nil. simpl.
    rewrite (mkC_ext _ (wslow log h 0) (fun j => h <? j)). cancel. lia.
    intros. unfold wslow. simpl. rewrite orb_false_r. reflexivity. }
  { rename i into s. Intros. rename H into Hs. rename H0 into Hl0. rename H1 into Hp0.
    assert (Hc: -1 <= Znth s norm <= 2 ^ log) by (apply Hcr; lia).
    assert (Hks: kpos norm (s + 1) = kpos norm s + Z.max (Znth s norm) 0) by (apply kpos_succ; lia).
    pose proof (kpos_le norm (s + 1) ltac:(lia)) as Hkl.
    assert (Hk0: 0 <= kpos norm s) by (unfold kpos; apply sum_max_nonneg).
    assert (Esp: spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0 =
      let '(t, q) := spread_pos norm log 0 (Z.to_nat s) h t0 0 in
      if Znth s norm >? 0 then spread_one log (Z.to_nat (Znth s norm)) s h t q else (t, q)).
    { rewrite Z2Nat.inj_add, Nat.add_1_r, spread_pos_S by lia. simpl Nat.add.
      rewrite nth_Znth', Z2Nat.id by lia. reflexivity. }
    destruct (spread_pos norm log 0 (Z.to_nat s) h t0 0) as [tb p] eqn:Etb. simpl fst in *; simpl snd in *.
    forward.
    forward_loop (EX i: Z,
     PROP (0 <= i <= Z.max (Znth s norm) 0;
           Zlength (fst (spread_one log (Z.to_nat (i)) s h tb p)) = 2 ^ log;
           snd (spread_one log (Z.to_nat (i)) s h tb p) = Nat.iter (Z.to_nat (kpos norm s + (i))) (fse_nxt log h) 0)
     LOCAL (temp _i__1 (Vint (Int.repr i)); temp _s__3 (Vint (Int.repr s));
            temp _position__1 (Vint (Int.repr (snd (spread_one log (Z.to_nat (i)) s h tb p))));
            temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
            temp _highThreshold (Vint (Int.repr h));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn;
          data_at shd (tarray t_fdec (2 ^ log))
            (symcells (mkC (2 ^ log) (wslow log h (Z.to_nat (kpos norm s + (i)))) (fst (spread_one log (Z.to_nat (i)) s h tb p))))
            (offset_val 4 (Vptr bd od))))%assert
    continue: (EX i: Z,
     PROP (0 <= i < Z.max (Znth s norm) 0;
           Zlength (fst (spread_one log (Z.to_nat (i + 1)) s h tb p)) = 2 ^ log;
           snd (spread_one log (Z.to_nat (i + 1)) s h tb p) = Nat.iter (Z.to_nat (kpos norm s + (i + 1))) (fse_nxt log h) 0)
     LOCAL (temp _i__1 (Vint (Int.repr i)); temp _s__3 (Vint (Int.repr s));
            temp _position__1 (Vint (Int.repr (snd (spread_one log (Z.to_nat (i + 1)) s h tb p))));
            temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
            temp _highThreshold (Vint (Int.repr h));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn;
          data_at shd (tarray t_fdec (2 ^ log))
            (symcells (mkC (2 ^ log) (wslow log h (Z.to_nat (kpos norm s + (i + 1)))) (fst (spread_one log (Z.to_nat (i + 1)) s h tb p))))
            (offset_val 4 (Vptr bd od))))%assert
    break: (PROP (Zlength (fst (spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0)) = 2 ^ log;
           snd (spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0) = Nat.iter (Z.to_nat (kpos norm (s + 1))) (fse_nxt log h) 0)
     LOCAL (temp _s__3 (Vint (Int.repr s));
            temp _position__1 (Vint (Int.repr (snd (spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0))));
            temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
            temp _highThreshold (Vint (Int.repr h));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn;
          data_at shd (tarray t_fdec (2 ^ log))
            (symcells (mkC (2 ^ log) (wslow log h (Z.to_nat (kpos norm (s + 1)))) (fst (spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0))))
            (offset_val 4 (Vptr bd od))))%assert.
    { Exists 0. entailer!. change (Z.to_nat 0) with O. simpl fst. cancel. }
    { Intros i. forward.
      { entailer!. rewrite Hnc by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
      rewrite Hnc by lia. forward_if.
      2:{ forward. assert (Ei: i = Z.max (Znth s norm) 0) by lia.
        assert (Ems: spread_pos norm log 0 (Z.to_nat (s + 1)) h t0 0 = spread_one log (Z.to_nat i) s h tb p).
        { rewrite Esp. destruct (Z.gtb_spec (Znth s norm) 0). { rewrite Ei, Z.max_l by lia. reflexivity. }
          replace i with 0 by lia. reflexivity. }
        rewrite Ems, Hks, <- Ei. entailer!. }
      assert (Hq: 0 <= snd (spread_one log (Z.to_nat i) s h tb p) < 2 ^ log) by (rewrite H1; apply iter_nxt_range; lia).
      destruct (spread_one log (Z.to_nat i) s h tb p) as [tc q] eqn:Est. simpl fst in *; simpl snd in *.
      assert (Hh0: 0 <= h) by lia.
      forward.
      rewrite !zext8 by rep_lia.
      rewrite symcells_upd by (rewrite Zlength_mkC; lia). rewrite mkC_upd by lia.
      forward.
      rewrite add_repr, and_repr. change (Z.land (q + fse_step log) (2 ^ log - 1)) with (fse_g log q).
      pose proof (fse_g_range log q ltac:(lia)) as Hx.
      forward_while
        (EX j: Z,
         PROP (0 <= j < 2 ^ log; forall i', 0 <= i' < j -> h < Nat.iter (Z.to_nat i') (fse_g log) (fse_g log q))
         LOCAL (temp _i__1 (Vint (Int.repr i)); temp _s__3 (Vint (Int.repr s));
                temp _position__1 (Vint (Int.repr (Nat.iter (Z.to_nat j) (fse_g log) (fse_g log q))));
                temp _step__1 (Vint (Int.repr (fse_step log))); temp _tableMask__1 (Vint (Int.repr (2 ^ log - 1)));
            temp _highThreshold (Vint (Int.repr h));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) vh; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
         SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) vh;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun c => Vint (Int.repr (nx c))) norm) (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn;
              data_at shd (tarray t_fdec (2 ^ log))
                (symcells (mkC (2 ^ log) (fun j => orb (wslow log h (Z.to_nat (kpos norm s + i)) j) (j =? q))
                  (upd_Znth q tc s)))
                (offset_val 4 (Vptr bd od))))%assert.
      { Exists 0. entailer!. }
      { entailer!. }
      { forward.
        pose proof (iter_g_range log (Z.to_nat j) (fse_g log q) ltac:(lia) Hx) as Hjr.
        rewrite Int.unsigned_repr in HRE by rep_lia.
        rewrite add_repr, and_repr. fold (fse_g log (Nat.iter (Z.to_nat j) (fse_g log) (fse_g log q))).
        rewrite <- Nat.iter_succ.
        destruct (Z.eq_dec (j + 1) (2 ^ log)) as [Ej|Ej].
        - assert (E: Nat.iter (S (Z.to_nat j)) (fse_g log) (fse_g log q) = fse_g log q)
            by (replace (S (Z.to_nat j)) with (Z.to_nat (2 ^ log)) by lia; apply GP; lia).
          rewrite E. Exists 0. entailer!.
        - Exists (j + 1). replace (S (Z.to_nat j)) with (Z.to_nat (j + 1)) by lia. entailer!.
          intros i' Hi'. destruct (Z.eq_dec i' j); [subst; auto | apply H4; lia]. }
      { pose proof (iter_g_range log (Z.to_nat j) (fse_g log q) ltac:(lia) Hx) as Hjr.
        rewrite Int.unsigned_repr in HRE by rep_lia.
        assert (Ewh: fse_nxt log h q = Nat.iter (Z.to_nat j) (fse_g log) (fse_g log q))
          by (unfold fse_nxt; apply SKW; auto; lia).
        destruct (slow_step log h (kpos norm s) i s tb p tc q Est ltac:(lia) Hk0 H1) as (E1 & E2 & E3).
        rewrite <- Ewh.
        forward. Exists i. rewrite E1, E2. simpl fst; simpl snd. entailer!.
        { rewrite Zlength_upd. auto. }
        rewrite upd_upd_Znth by lia. apply derives_refl'. f_equal. f_equal.
        apply mkC_ext; [lia | intros; symmetry; apply E3]. } }
    { Intros i. forward. Exists (i + 1). entailer!. }
    { unfold abbreviate in POSTCONDITION. subst POSTCONDITION. simpl RA_normal. entailer!. } }
  rewrite ZtoNat_Zlength, Hwf, HK. simpl fst; simpl snd. Intros.
  forward_if.
  { discriminate. }
  forward. entailer!.
  rewrite mkC_all. cancel. 2: lia.
  intros j Hj. unfold wslow. destruct (Z.ltb_spec h j); simpl; auto. apply existsb_exists. exists j.
  split; [apply Hcov; lia | apply Z.eqb_refl].
Qed.

Lemma builddt_body : FSE_WF_SLOW -> FSE_FAST ->
  semax_body Vprog G_B0 f_FSE_buildDTable_internal FSE_buildDTable_internal_spec.
Proof.
  intros WF FAST.
  start_function.
  pose proof H as Hok. destruct H as (Hlog & HN & Hrange & Hsum).
  assert (Hsz: 32 <= 2 ^ log <= 4096) by (split; [change 32 with (2 ^ 5) | change 4096 with (2 ^ 12)];
    apply Z.pow_le_mono_r; lia).
  assert (Hnc: forall s, 0 <= s < Zlength norm -> Znth s nc = Vint (Int.repr (Znth s norm))).
  { intros. pose proof (Znth_sublist 0 s (Zlength norm) nc ltac:(lia) ltac:(lia)) as E.
    replace (s + 0)%Z with s in E by lia. rewrite <- E, H2, Znth_map by lia. reflexivity. }
  sep_apply (dt_split shd dt log). lia.
  sep_apply (wk_split shw pw nw (Zlength norm)). lia. Intros. rename H into Hfcw.
  assert_PROP (isptr dt) as Pdt by entailer!.
  destruct pw as [| | | | | bw ow]; try (destruct Hfcw; contradiction).
  destruct dt as [| | | | | bd od]; try contradiction.
  forward. forward. forward. forward.
  assert (E1: Vptr bw (Ptrofs.add (Ptrofs.add ow (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tushort))
    (ptrofs_of_int Unsigned (Int.repr (Zlength norm - 1))))) (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tushort))
    (ptrofs_of_int Signed (Int.repr 1)))) = offset_val (2 * Zlength norm) (Vptr bw ow)).
  { simpl. f_equal. cbv [Ptrofs.of_intu Ptrofs.of_int Ptrofs.of_ints].
    rewrite Int.unsigned_repr, Int.signed_repr by rep_lia. rewrite Ptrofs.add_assoc. f_equal.
    rewrite !ptrofs_mul_repr, ptrofs_add_repr. f_equal. lia. }
  assert (E2: Vptr bd (Ptrofs.add od (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tuint))
    (ptrofs_of_int Signed (Int.repr 1)))) = offset_val 4 (Vptr bd od)) by (simpl; f_equal).
  rewrite E1, E2. clear E1 E2.
  forward. forward. { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  assert (Esh: Int.shl (Int.repr 1) (Int.repr log) = Int.repr (2 ^ log)).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
  rewrite Esh, add_repr. replace (Zlength norm - 1 + 1)%Z with (Zlength norm) by lia.
  forward.
  forward_if.
  { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
  { assert (Esh64: Int64.shl (Int64.repr 1) (Int64.repr log) = Int64.repr (2 ^ log)).
    { unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
    rewrite Int.unsigned_repr in H by rep_lia. rewrite Int.unsigned_repr in H by rep_lia.
    rewrite Esh64, mul64_repr, !add64_repr in H. rewrite !Int64.unsigned_repr in H by rep_lia. lia. }
  clear H. forward_if.
  { lia. }
  clear H. forward_if.
  { lia. }
  clear H. forward. forward. forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  assert (Ell: Int.sign_ext 16 (Int.sign_ext 16 (Int.shl (Int.repr 1) (Int.sub (Int.repr log) (Int.repr 1))))
    = Int.repr (2 ^ (log - 1))).
  { rewrite sub_repr. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l.
    assert (2 ^ (log - 1) <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia).
    assert (0 < 2 ^ (log - 1)) by (apply Z.pow_pos_nonneg; lia).
    rewrite !sign_ext_inrange; auto; rewrite Int.signed_repr; change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647; simpl; lia. }
  rewrite Ell. clear Ell.
  forward_for_simple_bound (Zlength norm)
    (EX s: Z,
     PROP ()
     LOCAL (temp _highThreshold (Vint (Int.repr (snd (pl norm log s))));
            temp _largeLimit (Vint (Int.repr (2 ^ (log - 1))));
            temp _tableSize (Vint (Int.repr (2 ^ log))); temp _maxSV1 (Vint (Int.repr (Zlength norm)));
            temp _spread (offset_val (2 * Zlength norm) (Vptr bw ow)); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) v_DTableH; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at shw (tarray tushort (Zlength norm))
            (map (fun c => Vint (Int.repr (nx c))) (sublist 0 s norm) ++ Zrepeat Vundef (Zlength norm - s))
            (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          data_at_ shd t_fhdr (Vptr bd od);
          data_at shd (tarray t_fdec (2 ^ log))
            (symcells (mkC (2 ^ log) (fun j => snd (pl norm log s) <? j) (fst (pl norm log s))))
            (offset_val 4 (Vptr bd od));
          data_at Tsh (Tstruct ___gp_FSE_DTableHeader noattr) (Vint (Int.repr log), Vint (Int.repr (fmp norm log s)))
            v_DTableH;
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
  { entailer!. rewrite !zext16 by rep_lia.
    replace (pl norm log 0) with (repeat 0 (Z.to_nat (2 ^ log)), 2 ^ log - 1) by reflexivity.
    replace (fmp norm log 0) with 1 by reflexivity. simpl fst; simpl snd.
    rewrite (mkC_ext _ _ (fun _ => false)), mkC_none, symcells_none by (intros; lia || (apply Z.ltb_ge; lia)).
    rewrite data_at__fdec, data_at__ushort. cancel. }
  { rename i into s. assert (Hc: -1 <= Znth s norm <= 2 ^ log) by (rewrite Forall_Znth in Hrange; apply Hrange; lia).
    forward.
    { entailer!. rewrite Hnc by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
    rewrite Hnc by lia.
    assert (Hr1: Forall (fun c => -1 <= c) norm) by (eapply Forall_impl; [|exact Hrange]; simpl; lia).
    assert (Hsum1: fold_right Z.add 0 (map nx norm) = 2 ^ log) by exact Hsum.
    forward_if.
    { assert (Ec: Znth s norm = -1).
      { rewrite Int.neg_repr in H4. apply repr_inj_signed in H4; rep_lia. }
      pose proof (high_range norm log s Hr1 Hsum1 ltac:(lia) Ec) as Hh.
      forward. forward. forward. forward.
      rewrite (pl_succ norm log s), (fmp_succ norm log s) by lia.
      replace (2 ^ (log - 1) <=? Znth s norm) with false by (symmetry; apply Z.leb_gt; rewrite Ec;
        pose proof (Z.pow_pos_nonneg 2 (log - 1)); lia).
      pose proof (pl_len norm log s ltac:(lia) ltac:(lia)) as Hlen.
      destruct (pl norm log s) as [tab h]. simpl fst in *; simpl snd in *. rewrite Ec, Z.eqb_refl.
      entailer!.
      rewrite zext16, !zext8 by rep_lia.
      rewrite symcells_upd by (rewrite Zlength_mkC; lia). rewrite mkC_upd, upd_upd_Znth by lia.
      rewrite (prefix_upd (fun c => Vint (Int.repr (nx c)))) by (rewrite ?Ec; auto; lia).
      rewrite (mkC_ext _ (fun j => orb (h <? j) (j =? h)) (fun j => h - 1 <? j)) by
        (lia || (intros j _; destruct (Z.ltb_spec h j), (Z.eqb_spec j h), (Z.ltb_spec (h - 1) j); simpl;
                 try reflexivity; lia)).
      cancel. }
    { assert (Ec: Znth s norm <> -1) by (intro E; apply H4; rewrite E; reflexivity).
      forward.
      { entailer!. rewrite Hnc by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
      rewrite Hnc by lia.
      assert (HL: 0 < 2 ^ (log - 1) <= 2 ^ 11) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
      apply semax_if_seq. forward_if.
      { try rewrite Int.signed_repr in H5 by rep_lia.
        forward.
        forward.
        { entailer!. rewrite Hnc by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
        rewrite Hnc by lia. forward.
        rewrite (pl_succ norm log s), (fmp_succ norm log s) by lia.
        try (replace (2 ^ (log - 1) <=? Znth s norm) with true by (symmetry; apply Z.leb_le; lia)).
        try (replace (2 ^ (log - 1) <=? Znth s norm) with false by (symmetry; apply Z.leb_gt; lia)).
        replace (Znth s norm =? -1) with false by (symmetry; apply Z.eqb_neq; auto).
        destruct (pl norm log s) as [tab h]. simpl fst; simpl snd.
        entailer!.
        rewrite ?zext16 by rep_lia.
        rewrite (prefix_upd (fun c => Vint (Int.repr (nx c)))) by (unfold nx; rewrite ?(proj2 (Z.eqb_neq _ _) Ec); auto; lia).
        cancel. }
      { try rewrite Int.signed_repr in H5 by rep_lia.
        forward.
        { entailer!. rewrite Hnc by lia. simpl. rewrite Int.signed_repr by rep_lia. lia. }
        rewrite Hnc by lia. forward.
        rewrite (pl_succ norm log s), (fmp_succ norm log s) by lia.
        try (replace (2 ^ (log - 1) <=? Znth s norm) with true by (symmetry; apply Z.leb_le; lia)).
        try (replace (2 ^ (log - 1) <=? Znth s norm) with false by (symmetry; apply Z.leb_gt; lia)).
        replace (Znth s norm =? -1) with false by (symmetry; apply Z.eqb_neq; auto).
        destruct (pl norm log s) as [tab h]. simpl fst; simpl snd.
        entailer!.
        rewrite ?zext16 by rep_lia.
        rewrite (prefix_upd (fun c => Vint (Int.repr (nx c)))) by (unfold nx; rewrite ?(proj2 (Z.eqb_neq _ _) Ec); auto; lia).
        cancel. } }
  }
  rewrite sublist_same, Z.sub_diag by lia. change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
  assert (Efm: fmp norm log (Zlength norm) = fse_fm norm log) by (unfold fmp, fse_fm; rewrite sublist_same by lia; reflexivity).
  rewrite Efm. clear Efm.
  forward_call (Tsh, shd, v_DTableH, Vptr bd od,
    existT (fun t => reptype t) t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log)))).
  { cbn [projT1 projT2]. split; [simpl; rep_lia |].
    apply memcpy_ok_fhdr; [rep_lia | unfold fse_fm; destruct existsb; lia]. }
  unfold projT1, projT2.
  assert (Hr1: Forall (fun c => -1 <= c) norm) by (eapply Forall_impl; [|exact Hrange]; simpl; lia).
  assert (Hsum1: fold_right Z.add 0 (map nx norm) = 2 ^ log) by exact Hsum.
  assert (Hc1: cnt1 norm <= 2 ^ log) by (pose proof (cnt1_le_sum norm Hr1); lia).
  pose proof (cnt1_nonneg norm) as Hc0.
  assert (Hfacts: bd_facts norm log nc nw shd shn shw)
    by (split3; [auto|auto|]; split; [auto|]; split; [exact Hok|]; split; [lia|]; split; [lia|]; split; [exact H2|]; lia).
  pose proof (pl_high norm log (Zlength norm) ltac:(lia)) as Hhi. rewrite sublist_same in Hhi by lia.
  forward_if (bd_mid norm log nc pn bd od bw ow nw shd shn shw v_DTableH gv).
  { assert (C0: cnt1 norm = 0).
    { rewrite Hhi, sub_repr in H. apply repr_inj_signed in H; rep_lia. }
    eapply semax_normal_ret.
    { eapply semax_pre; [ | apply (bd_fast_ok FAST (cover_fast WF FAST) norm log nc pn bd od bw ow nw shd shn shw
        v_DTableH gv Hfacts (cnt1_zero_nonneg norm Hr1 C0)) ].
      unfold bd_pre. entailer!. }
    simpl RA_normal. apply ENTAIL_refl. }
  { assert (C0: 0 < cnt1 norm).
    { destruct (Z.eq_dec (cnt1 norm) 0) as [E|]; [|lia]. exfalso. apply H. rewrite Hhi, sub_repr, E. f_equal. lia. }
    eapply semax_normal_ret.
    { eapply semax_pre; [ | apply (bd_slow_ok WF (cover_slow WF) fse_g_period skip_high_while norm log nc pn bd od
        bw ow nw shd shn shw v_DTableH gv Hfacts (cnt1_pos_in norm C0)) ].
      unfold bd_pre. entailer!. }
    simpl RA_normal. apply ENTAIL_refl. }
  unfold bd_mid. abbreviate_semax.
  destruct (WF norm log 255 Hok) as (Wlog & Wlen & Wcells & Wfm & _).
  rewrite fse_build_eq in Wlen, Wcells, Wfm. simpl ft_cells in *.
  set (tab := fse_symtab norm log) in *. set (next0 := map nx norm) in *.
  assert (Htab: Zlength tab = 2 ^ log) by (rewrite Zlength_states in Wlen; auto).
  replace (map (fun c => Vint (Int.repr (nx c))) norm) with (map (fun x => Vint (Int.repr x)) (nexts_after tab next0 0))
    by (unfold nexts_after, next0; rewrite sublist_nil; simpl fold_left; rewrite map_map; reflexivity).
  replace (symcells (map (fun z => Vint (Int.repr z)) tab))
    with (map fdcell (sublist 0 0 (states log tab next0)) ++ sublist 0 (2 ^ log) (symcells (map (fun z => Vint (Int.repr z)) tab)))
    by (rewrite sublist_nil, sublist_same; auto; rewrite Zlength_symcells, Zlength_map; auto).
  forward_for_simple_bound (2 ^ log)
    (EX u: Z,
     PROP ()
     LOCAL (temp _tableSize (Vint (Int.repr (2 ^ log))); temp _symbolNext (Vptr bw ow);
            temp _tableDecode (offset_val 4 (Vptr bd od));
            lvar _DTableH (Tstruct ___gp_FSE_DTableHeader noattr) v_DTableH; gvars gv;
            temp _dt (Vptr bd od); temp _normalizedCounter pn; temp _tableLog (Vint (Int.repr log)))
     SEP (data_at Tsh t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) v_DTableH;
          data_at shd t_fhdr (Vint (Int.repr log), Vint (Int.repr (fse_fm norm log))) (Vptr bd od);
          data_at shw (tarray tushort (Zlength norm)) (map (fun x => Vint (Int.repr x)) (nexts_after tab next0 u))
            (Vptr bw ow);
          data_at_ shw (tarray tuchar (4 * nw - 2 * Zlength norm)) (offset_val (2 * Zlength norm) (Vptr bw ow));
          data_at shd (tarray t_fdec (2 ^ log))
            (map fdcell (sublist 0 u (states log tab next0)) ++
             sublist u (2 ^ log) (symcells (map (fun z => Vint (Int.repr z)) tab)))
            (offset_val 4 (Vptr bd od));
          zstd_globals gv; data_at shn (tarray tshort (Zlength nc)) nc pn))%assert.
  { entailer!. }
  { rename i into u.
    assert (Hst: Znth u (states log tab next0) =
      st_cell log (Znth u tab) (nth (Z.to_nat (Znth u tab)) (nexts_after tab next0 u) 0))
      by (apply Znth_states; lia).
    assert (Wu: 0 <= fe_sym (Znth u (states log tab next0)) < Zlength norm /\
                0 <= fe_nb (Znth u (states log tab next0)) <= log /\
                0 <= fe_base (Znth u (states log tab next0)) /\
                fe_base (Znth u (states log tab next0)) + 2 ^ fe_nb (Znth u (states log tab next0)) <= 2 ^ log)
      by (rewrite Forall_Znth in Wcells; apply Wcells; lia).
    pose proof (nexts_nonneg tab next0 u) as Hnn.
    assert (Hn0: Forall (fun v => 0 <= v) next0).
    { unfold next0. rewrite Forall_map. eapply Forall_impl; [|exact Hrange]. intros c Hc. unfold nx.
      simpl in Hc. destruct (Z.eqb_spec c (-1)); lia. }
    specialize (Hnn Hn0).
    assert (Hcell: forall d, @Znth _ d u (map fdcell (sublist 0 u (states log tab next0)) ++
                     sublist u (2 ^ log) (symcells (map (fun z => Vint (Int.repr z)) tab)))
                   = (Vundef, (Vint (Int.repr (Znth u tab)), Vundef))).
    { intros d. rewrite Znth_app2 by (rewrite Zlength_map, Zlength_sublist; lia).
      rewrite Zlength_map, Zlength_sublist by lia. rewrite Znth_sublist by (rewrite ?Zlength_symcells, ?Zlength_map; lia).
      unfold symcells. rewrite Znth_map by (rewrite Zlength_map; lia). rewrite Znth_map by lia.
      replace (u - (u - 0) + u)%Z with u by lia. reflexivity. }
    rewrite Hst in Wu. unfold st_cell in Wu. simpl in Wu. destruct Wu as (Hs & Hnb & Hb & Hb2).
    set (sy := Znth u tab) in *. set (nxu := nexts_after tab next0 u) in *.
    set (x := nth (Z.to_nat sy) nxu 0) in *.
    assert (Hx0: 0 <= x) by (apply (Forall_nth_d (fun v => 0 <= v)); auto; lia).
    assert (Hx: 1 <= x < 2 ^ (log + 1)) by (apply (st_cell_x log sy x); simpl; lia).
    forward.
    { entailer!. rewrite Hcell. simpl. rewrite Int.unsigned_repr by rep_lia. change Byte.max_unsigned with 255. lia. }
    rewrite Hcell. simpl fst; simpl snd.
    assert (Ex: x = Znth sy nxu) by (apply nth_Znth'; lia).
    assert (Hlnx: Zlength nxu = Zlength norm) by (unfold nxu; rewrite Zlength_nexts_after; unfold next0; apply Zlength_map).
    forward.
    rewrite !zext8 by rep_lia.
    forward.
    { assert (2 ^ (log + 1) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia).
      entailer!. rewrite <- Ex. try rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
      change (2 ^ 13) with 8192 in *. lia. }
    rewrite <- Ex.
    assert (H13: 2 ^ (log + 1) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in H13.
    forward.
    forward.
    forward_call (x, gv).
    forward.
    rewrite Hcell. simpl fst; simpl snd. rewrite sub_repr, !zext8 by lia.
    forward.
    { entailer!. rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_map, !Zlength_sublist; try rewrite Zlength_symcells, Zlength_map; lia).
      simpl. rewrite Int.unsigned_repr by rep_lia. change Byte.max_unsigned with 255. lia. }
    rewrite upd_Znth_same by (rewrite Zlength_app, Zlength_map, !Zlength_sublist; try rewrite Zlength_symcells, Zlength_map; lia).
    simpl fst; simpl snd.
    forward.
    { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
    rewrite upd_Znth_same, upd_Znth_twice by (rewrite Zlength_app, Zlength_map, !Zlength_sublist; try rewrite Zlength_symcells, Zlength_map; lia).
    simpl fst; simpl snd.
    rewrite add_repr, zext16 by lia.
    assert (Hshl: Int.shl (Int.repr x) (Int.repr (log - highbit x)) = Int.repr (Z.shiftl x (log - highbit x))).
    { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
    assert (0 < 2 ^ (log - highbit x)) by (apply Z.pow_pos_nonneg; lia).
    rewrite Hshl, sub_repr, !zext16 by lia.
    rewrite (st_cells_step fdcell (states log tab next0) (symcells (map (fun z => Vint (Int.repr z)) tab)) (2 ^ log) u)
      by (rewrite ?Zlength_symcells, ?Zlength_map; auto; lia || (rewrite Hst; reflexivity)).
    rewrite nexts_after_succ by lia. fold sy nxu. unfold nx_step. fold x.
    rewrite upd_upd_Znth by lia. rewrite <- upd_Znth_map.
    entailer!. }
  rewrite sublist_nil, app_nil_r. rewrite sublist_same by lia.
  forward.
  unfold fsedt_at. rewrite fse_build_eq. simpl ft_log; simpl ft_cells.
  sep_apply (data_at_data_at_ shw (tarray tushort (Zlength norm))).
  sep_apply (wk_join shw (Vptr bw ow) nw (Zlength norm)). lia. auto.
  entailer!. split.
  - change (fse_symtab norm log) with tab. change (map nx norm) with next0.
    unfold fse_dt_ok; simpl ft_log; simpl ft_cells. split; [lia|]. split; [auto|].
    eapply Forall_impl; [|exact Wcells]. simpl. intros e (? & ? & ? & ?). lia.
  - unfold fse_fm. destruct existsb; auto.
Qed.

Lemma body_ent_builddt : FSE_WF_SLOW -> FSE_FAST ->
  semax_body Vprog G_B0 f_FSE_buildDTable_internal FSE_buildDTable_internal_spec.
Proof. exact builddt_body. Qed.
