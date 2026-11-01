(* The arithmetic of huf_pick's body (harness/writer.h): the splits keep a
   full binary tree (Kraft sum of 2^(11-depth) = 2^11), the shuffle permutes the depths, the weights
   log+1-depth go to increasing symbols, and the codes are assigned by weight, then symbol (huf_start). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Coq.Sorting.Sorted.
Local Open Scope Z_scope.

(* ---------- sums ---------- *)

Lemma hp_zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a; intros; simpl; [lia | rewrite IHa; lia]. Qed.

Lemma hp_zsum_upd : forall (f: Z -> Z) (L: list Z) s v, 0 <= s < Zlength L ->
  zsum (map f (upd_Znth s L v)) = zsum (map f L) - f (Znth s L) + f v.
Proof.
  intros.
  assert (E: L = sublist 0 s L ++ [Znth s L] ++ sublist (s + 1) (Zlength L) L) by list_solve.
  rewrite upd_Znth_unfold by lia.
  transitivity (zsum (map f (sublist 0 s L ++ [Znth s L] ++ sublist (s + 1) (Zlength L) L)) - f (Znth s L) + f v);
    [| rewrite <- E; auto].
  rewrite !map_app, !hp_zsum_app. simpl. lia.
Qed.

Lemma hp_zsum_perm : forall l l', Permutation l l' -> zsum l = zsum l'.
Proof. intros. induction H; simpl; lia. Qed.

Lemma hp_zsum_le : forall (f g: Z -> Z) l, (forall x, In x l -> f x <= g x) ->
  zsum (map f l) <= zsum (map g l).
Proof.
  induction l; intros; simpl; [lia |].
  assert (f a <= g a) by (apply H; left; auto).
  assert (zsum (map f l) <= zsum (map g l)) by (apply IHl; intros; apply H; right; auto). lia.
Qed.

Lemma hp_zsum_nonneg : forall (f: Z -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof.
  intros. replace 0 with (zsum (map (fun _ => 0) l)).
  - apply hp_zsum_le. auto.
  - induction l; simpl; auto. rewrite IHl; auto. intros; apply H; right; auto.
Qed.

(* two sums over a list without duplicates whose terms differ only at s *)
Lemma hp_zsum_diff1 : forall (f g: Z -> Z) l s, NoDup l -> In s l ->
  (forall k, In k l -> k <> s -> f k = g k) ->
  zsum (map f l) = zsum (map g l) - g s + f s.
Proof.
  induction l; intros s ND Hin Hfg; [destruct Hin |]. inversion ND; subst. simpl.
  destruct Hin as [-> | Hin].
  - assert (zsum (map f l) = zsum (map g l)).
    { f_equal. apply map_ext_in. intros. apply Hfg; [right; auto | intro; subst; contradiction]. }
    lia.
  - assert (a <> s) by (intro; subst; contradiction).
    assert (zsum (map f l) = zsum (map g l) - g s + f s).
    { apply IHl; auto. intros k Hk Hks. apply Hfg; [right; exact Hk | exact Hks]. }
    rewrite (Hfg a) by (auto; left; auto). lia.
Qed.

(* ---------- the splits: Kraft sum of 2^(11-depth) ---------- *)

Definition hp_kraft (d: list Z) : Z := zsum (map (fun x => 2 ^ (11 - x)) d).

Lemma hp_kraft_split : forall d j, 0 <= j < Zlength d -> 0 <= Znth j d < 11 ->
  hp_kraft (upd_Znth j d (Znth j d + 1) ++ [Znth j d + 1]) = hp_kraft d.
Proof.
  intros. unfold hp_kraft. rewrite map_app, hp_zsum_app, hp_zsum_upd by auto. simpl.
  replace (11 - Znth j d) with (Z.succ (11 - (Znth j d + 1))) by lia.
  rewrite Z.pow_succ_r by lia. lia.
Qed.

Lemma hp_kraft_one : forall x, 0 <= x <= 11 -> hp_kraft [x] = 2 ^ 11 -> x = 0.
Proof.
  intros. unfold hp_kraft in H0. simpl in H0.
  assert (x = 0 \/ 1 <= x) as [ | ] by lia; auto.
  assert (2 ^ (11 - x) <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in H0.
  change (2 ^ 10) with 1024 in H2. lia.
Qed.

Lemma hp_kraft_pos : forall d, Forall (fun x => 0 <= x <= 11) d -> d <> [] -> 0 < hp_kraft d.
Proof.
  intros d F N. destruct d as [| a d]; [congruence |]. inversion F; subst. unfold hp_kraft. simpl.
  assert (0 < 2 ^ (11 - a)) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= zsum (map (fun x => 2 ^ (11 - x)) d)).
  { apply hp_zsum_nonneg. intros. apply Z.pow_nonneg. lia. }
  lia.
Qed.

Lemma hp_kraft_app : forall a b, hp_kraft (a ++ b) = hp_kraft a + hp_kraft b.
Proof. intros. unfold hp_kraft. rewrite map_app, hp_zsum_app. auto. Qed.

(* a complete code of at least two leaves has no leaf at depth 0 *)
Lemma hp_kraft_ge1 : forall d, 2 <= Zlength d -> Forall (fun x => 0 <= x <= 11) d -> hp_kraft d = 2 ^ 11 ->
  Forall (fun x => 1 <= x <= 11) d.
Proof.
  intros d L F K. rewrite Forall_forall in *. intros x Hx. pose proof (F x Hx) as Fx.
  assert (x <> 0); [| lia]. intro; subst.
  apply in_split in Hx. destruct Hx as (A & B & ->).
  rewrite hp_kraft_app in K. change (0 :: B) with ([0] ++ B) in K. rewrite hp_kraft_app in K.
  change (hp_kraft [0]) with (2 ^ 11) in K.
  assert (A ++ B <> []).
  { intro E. assert (Zlength (A ++ B) = 0) by (rewrite E; auto).
    rewrite Zlength_app in H, L. change (0 :: B) with ([0] ++ B) in L. rewrite Zlength_app in L.
    change (Zlength [0]) with 1 in L. lia. }
  assert (0 < hp_kraft (A ++ B)).
  { apply hp_kraft_pos; auto. rewrite Forall_forall. intros. apply F. apply in_app_or in H0.
    apply in_or_app. destruct H0; [left | right; right]; auto. }
  rewrite hp_kraft_app in H0. lia.
Qed.

(* the Kraft sum at Max_Number_of_Bits log instead of 11 *)
Lemma hp_kraft_scale : forall d log, Forall (fun x => x <= log) d -> 0 <= log <= 11 ->
  hp_kraft d = zsum (map (fun x => 2 ^ (log - x)) d) * 2 ^ (11 - log).
Proof.
  induction d; intros log F Hl; [reflexivity |]. inversion F; subst. unfold hp_kraft in *. simpl.
  rewrite (IHd log) by auto. rewrite Z.mul_add_distr_r. f_equal.
  rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma hp_kraft_log : forall d log, Forall (fun x => x <= log) d -> 0 <= log <= 11 -> hp_kraft d = 2 ^ 11 ->
  zsum (map (fun x => 2 ^ (log - x)) d) = 2 ^ log.
Proof.
  intros. rewrite hp_kraft_scale with (log := log) in H1 by auto.
  replace (2 ^ 11) with (2 ^ log * 2 ^ (11 - log)) in H1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  apply Z.mul_reg_r in H1; auto. apply Z.pow_nonzero; lia.
Qed.

(* ---------- the shuffle: a swap is a permutation ---------- *)

Lemma hp_perm_swap_decomp : forall (l: list Z) a b, 0 <= a < b -> b < Zlength l ->
  Permutation l (sublist 0 a l ++ [Znth b l] ++ sublist (a + 1) b l ++ [Znth a l] ++ sublist (b + 1) (Zlength l) l).
Proof.
  intros.
  assert (E: l = sublist 0 a l ++ [Znth a l] ++ sublist (a + 1) b l ++ [Znth b l] ++ sublist (b + 1) (Zlength l) l)
    by list_solve.
  rewrite E at 1. apply Permutation_app_head. simpl.
  set (m := sublist (a + 1) b l). set (r := sublist (b + 1) (Zlength l) l).
  apply perm_trans with (Znth b l :: Znth a l :: m ++ r).
  - apply perm_trans with (Znth a l :: Znth b l :: m ++ r); [| apply perm_swap].
    apply perm_skip. apply Permutation_sym. apply Permutation_middle.
  - apply perm_skip. apply Permutation_middle.
Qed.

(* the C swap: depth[i-1] = depth[j]; depth[j] = old depth[i-1], with j < i *)
Lemma hp_perm_swap : forall (l: list Z) j i, 0 <= j < i -> i <= Zlength l ->
  Permutation l (upd_Znth j (upd_Znth (i - 1) l (Znth j l)) (Znth (i - 1) l)).
Proof.
  intros. destruct (zeq j (i - 1)).
  - subst. replace (upd_Znth (i - 1) (upd_Znth (i - 1) l (Znth (i - 1) l)) (Znth (i - 1) l)) with l
      by list_solve. apply Permutation_refl.
  - replace (upd_Znth j (upd_Znth (i - 1) l (Znth j l)) (Znth (i - 1) l)) with
      (sublist 0 j l ++ [Znth (i - 1) l] ++ sublist (j + 1) (i - 1) l ++ [Znth j l] ++ sublist (i - 1 + 1) (Zlength l) l)
      by list_solve.
    apply hp_perm_swap_decomp; lia.
Qed.

Lemma hp_perm_kraft : forall d d', Permutation d d' -> hp_kraft d = hp_kraft d'.
Proof. intros. unfold hp_kraft. apply hp_zsum_perm. apply Permutation_map. auto. Qed.

Lemma hp_perm_forall : forall (P: Z -> Prop) d d', Permutation d d' -> Forall P d -> Forall P d'.
Proof.
  intros. rewrite Forall_forall in *. intros. apply H0. eapply Permutation_in; [apply Permutation_sym |]; eauto.
Qed.

(* ---------- the maximum depth ---------- *)

Definition hp_max (l: list Z) : Z := fold_left Z.max l 0.

Lemma hp_max_snoc : forall l x, hp_max (l ++ [x]) = Z.max (hp_max l) x.
Proof. intros. unfold hp_max. rewrite fold_left_app. reflexivity. Qed.

Lemma hp_max_gen : forall l a,
  a <= fold_left Z.max l a /\ Forall (fun x => x <= fold_left Z.max l a) l /\
  (fold_left Z.max l a = a \/ In (fold_left Z.max l a) l).
Proof.
  induction l; intros; simpl; [split; [lia | split; auto] |].
  destruct (IHl (Z.max a0 a)) as (H1 & H2 & H3). split; [lia |]. split.
  - constructor; auto. lia.
  - destruct H3 as [H3 | H3]; [| right; right; auto]. rewrite H3.
    destruct (Z.max_spec a0 a) as [[_ ->] | [_ ->]]; [right; left | left]; auto.
Qed.

Lemma hp_max_range : forall l, Forall (fun x => 0 <= x <= 11) l -> 0 <= hp_max l <= 11.
Proof.
  intros. destruct (hp_max_gen l 0) as (H1 & H2 & H3). fold (hp_max l) in *. split; [lia |].
  destruct H3 as [-> | H3]; [lia |]. rewrite Forall_forall in H. apply H in H3. lia.
Qed.

Lemma hp_max_props : forall l, Forall (fun x => 1 <= x <= 11) l -> l <> [] ->
  1 <= hp_max l <= 11 /\ Forall (fun x => 1 <= x <= hp_max l) l /\ In (hp_max l) l.
Proof.
  intros l F N. destruct (hp_max_gen l 0) as (H1 & H2 & H3). fold (hp_max l) in *.
  assert (In (hp_max l) l).
  { destruct H3; auto. destruct l as [| a l']; [congruence |]. inversion F; inversion H2; subst. lia. }
  rewrite Forall_forall in F, H2. pose proof (F _ H).
  split; [lia | split; auto]. rewrite Forall_forall. intros. specialize (F _ H4). specialize (H2 _ H4). lia.
Qed.

(* ---------- the symbols: increasing, their weights in W ---------- *)

Definition hp_f (w: Z) : Z := if w =? 0 then 0 else 2 ^ (w - 1).

(* W: the weights of 0..255 after the symbols syms got the weights ws *)
Definition hp_symw (W syms ws: list Z) : Prop :=
  Zlength W = 256 /\ Zlength syms = Zlength ws /\ StronglySorted Z.lt syms /\
  Forall (fun k => 0 <= k < 256) syms /\
  (forall m, 0 <= m < Zlength syms -> Znth (Znth m syms) W = Znth m ws) /\
  (forall k, 0 <= k < 256 -> ~ In k syms -> Znth k W = 0) /\
  zsum (map hp_f W) = zsum (map hp_f ws).

Lemma hp_zsum_repeat0 : forall n, zsum (map hp_f (repeat 0 n)) = 0.
Proof. induction n; simpl; auto. Qed.

Lemma hp_symw_init : hp_symw (Zrepeat 0 256) [] [].
Proof.
  split; [reflexivity |]. split; [reflexivity |]. split; [constructor |]. split; [constructor |].
  split; [intros; rewrite Zlength_nil in H; lia |]. split.
  - intros. apply Znth_repeat_inrange. lia.
  - unfold Zrepeat. rewrite hp_zsum_repeat0. reflexivity.
Qed.

Lemma hp_sorted_snoc : forall l s, StronglySorted Z.lt l -> Forall (fun x => x < s) l ->
  StronglySorted Z.lt (l ++ [s]).
Proof.
  induction l; intros; simpl.
  - constructor; constructor.
  - inversion H; inversion H0; subst. constructor; auto. apply Forall_app; split; auto.
Qed.

Lemma hp_symw_step : forall W syms ws s v, hp_symw W syms ws -> 0 <= s < 256 -> Forall (fun x => x < s) syms ->
  hp_symw (upd_Znth s W v) (syms ++ [s]) (ws ++ [v]).
Proof.
  intros W syms ws s v (HW & Hl & Hs & Hr & Hm & Hz & Hk) Hsr Hlt.
  assert (Ns: ~ In s syms) by (intro I; rewrite Forall_forall in Hlt; specialize (Hlt _ I); lia).
  split; [list_solve |]. split; [list_solve |]. split; [apply hp_sorted_snoc; auto |].
  split; [apply Forall_app; split; auto |]. split; [| split].
  - intros m Hm'. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hm'.
    destruct (zeq m (Zlength syms)).
    + subst. rewrite Znth_app2 by lia. rewrite Z.sub_diag, Znth_0_cons.
      rewrite Znth_app2 by lia. replace (Zlength syms - Zlength ws) with 0 by lia. rewrite Znth_0_cons.
      apply upd_Znth_same. lia.
    + rewrite !Znth_app1 by lia. rewrite Forall_forall in Hr.
      assert (0 <= Znth m syms < 256) by (apply Hr; apply Znth_In; lia).
      assert (Znth m syms <> s) by (intro E; apply Ns; rewrite <- E; apply Znth_In; lia).
      rewrite upd_Znth_diff by lia. apply Hm. lia.
  - intros k Hk' Ni. rewrite upd_Znth_diff by (try lia; intro; subst; apply Ni; apply in_or_app; right; left; auto).
    apply Hz; auto. intro; apply Ni; apply in_or_app; left; auto.
  - rewrite hp_zsum_upd by lia. rewrite (Hz s) by auto. rewrite map_app, hp_zsum_app. simpl.
    change (hp_f 0) with 0. lia.
Qed.

(* ---------- the code is complete (huf_ok) ---------- *)

Lemma hp_zn_Znth : forall (W: list Z) k, 0 <= k -> zn W k = Znth k W.
Proof. intros. unfold zn, Znth. destruct (Z_lt_dec k 0); [lia | reflexivity]. Qed.

Lemma hp_seq_sorted : forall n a, StronglySorted Z.lt (map Z.of_nat (seq a n)).
Proof.
  induction n; intros; simpl; constructor; auto.
  rewrite Forall_forall. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
  apply in_seq in Hy. lia.
Qed.

Lemma hp_filter_sorted : forall (f: Z -> bool) l, StronglySorted Z.lt l -> StronglySorted Z.lt (filter f l).
Proof.
  induction l; intros; simpl; auto. inversion H; subst. destruct (f a); auto. constructor; auto.
  rewrite Forall_forall in *. intros. apply filter_In in H0. apply H3. tauto.
Qed.

Lemma hp_sorted_eq : forall l1 l2, StronglySorted Z.lt l1 -> StronglySorted Z.lt l2 ->
  (forall x, In x l1 <-> In x l2) -> l1 = l2.
Proof.
  induction l1; intros l2 S1 S2 E.
  - destruct l2; auto. exfalso. apply (E z). left; auto.
  - destruct l2 as [| b l2]; [exfalso; apply (E a); left; auto |].
    inversion S1; inversion S2; subst. rewrite Forall_forall in *.
    assert (a = b).
    { destruct (proj1 (E a) (or_introl eq_refl)) as [| Ha]; auto.
      destruct (proj2 (E b) (or_introl eq_refl)) as [| Hb]; auto.
      specialize (H6 _ Ha). specialize (H2 _ Hb). lia. }
    subst. f_equal. apply IHl1; auto. intros x. split; intros Hx.
    + destruct (proj1 (E x) (or_intror Hx)); auto. subst. specialize (H2 _ Hx). lia.
    + destruct (proj2 (E x) (or_intror Hx)); auto. subst. specialize (H6 _ Hx). lia.
Qed.

Lemma hp_in_syms256 : forall k, In k syms256 <-> 0 <= k < 256.
Proof.
  intros. unfold syms256. rewrite in_map_iff. split.
  - intros (n & <- & Hn). apply in_seq in Hn. lia.
  - intros. exists (Z.to_nat k). split; [lia |]. apply in_seq. lia.
Qed.

Lemma hp_symw_at : forall W syms ws k, hp_symw W syms ws -> 0 <= k < 256 ->
  (exists m, 0 <= m < Zlength syms /\ Znth m syms = k /\ Znth k W = Znth m ws) \/ (~ In k syms /\ Znth k W = 0).
Proof.
  intros W syms ws k (HW & Hl & Hs & Hr & Hm & Hz & Hk) Hkr.
  destruct (in_dec Z.eq_dec k syms) as [I | N]; [left | right; auto].
  apply In_Znth in I. destruct I as (m & Hm' & <-). exists m. try rewrite <- Zlength_correct in Hm'.
  split; [lia | split; auto].
Qed.

(* the weights are log+1-depth of the leaves, of depths 1..log, Kraft-complete *)
Lemma hp_huf_ok : forall d log W syms,
  2 <= Zlength d -> Forall (fun x => 1 <= x <= log) d -> 1 <= log <= 11 -> In log d -> hp_kraft d = 2 ^ 11 ->
  hp_symw W syms (map (fun x => log + 1 - x) d) ->
  huf_ok {| wh_w := W; wh_log := log; wh_last := last syms 0; wh_used := syms |}.
Proof.
  intros d log W syms Hd F Hlog Hin K S.
  assert (S' := S). destruct S' as (HW & Hl & Hs & Hr & Hm & Hz & Hk). rewrite Zlength_map in Hl.
  assert (Hws: forall m, 0 <= m < Zlength d -> 1 <= Znth m (map (fun x => log + 1 - x) d) <= log).
  { intros. rewrite Znth_map by lia. rewrite Forall_forall in F. pose proof (F (Znth m d) (Znth_In _ _ H)). lia. }
  assert (HWk: forall k, 0 <= k < 256 -> (In k syms /\ 1 <= Znth k W <= log) \/ (~ In k syms /\ Znth k W = 0)).
  { intros. destruct (hp_symw_at _ _ _ k S H) as [(m & Hm1 & Hm2 & Hm3) | ]; auto.
    left. split; [rewrite <- Hm2; apply Znth_In; lia |]. rewrite Hm3. apply Hws. lia. }
  unfold huf_ok; cbn [wh_w wh_log wh_last wh_used]. split; [auto |]. split; [lia |]. split; [| split; [| split; [| split; [lia | split; [auto |]]]]].
  - apply Forall_Znth. intros k Hk'. rewrite HW in Hk'. destruct (HWk k Hk') as [[_ ?] | [_ ->]]; lia.
  - change (zsum (map hp_f W) = 2 ^ log). rewrite Hk. rewrite map_map.
    rewrite (map_ext_in _ (fun x => 2 ^ (log - x))).
    + apply hp_kraft_log; auto; [| lia]. rewrite Forall_forall in *. intros. specialize (F _ H). lia.
    + intros x Hx. rewrite Forall_forall in F. specialize (F _ Hx). unfold hp_f.
      destruct (Z.eqb_spec (log + 1 - x) 0); [lia |]. f_equal. lia.
  - apply hp_sorted_eq; auto.
    + apply hp_filter_sorted. apply hp_seq_sorted.
    + intros x. rewrite filter_In, hp_in_syms256. unfold wh_weight; cbn [wh_w]. split.
      * intros I. assert (0 <= x < 256) by (rewrite Forall_forall in Hr; auto). split; auto.
        rewrite hp_zn_Znth by lia. destruct (HWk x H) as [[_ ?] | [? _]]; [| contradiction].
        destruct (Z.eqb_spec (Znth x W) 0); [lia | reflexivity].
      * intros [Hx E]. rewrite hp_zn_Znth in E by lia. destruct (HWk x Hx) as [[? _] | [_ E']]; auto.
        rewrite E' in E. discriminate.
  - apply In_Znth in Hin. destruct Hin as (m & Hm' & Em). try rewrite <- Zlength_correct in Hm'.
    replace 1 with (Znth (Znth m syms) W).
    + apply Znth_In. rewrite HW. rewrite Forall_forall in Hr. apply Hr. apply Znth_In. lia.
    + rewrite Hm by lia. rewrite Znth_map by lia. rewrite Em. lia.
Qed.

(* ---------- the canonical codes: cell = huf_start ---------- *)

Definition hp_done (W: list Z) (w s k: Z) : bool :=
  (0 <? zn W k) && ((zn W k <? w) || ((zn W k =? w) && (k <? s))).

Definition hp_csum (W: list Z) (w s: Z) : Z :=
  zsum (map (fun k => if hp_done W w s k then 2 ^ (zn W k - 1) else 0) syms256).

Lemma hp_start_csum : forall H s, huf_start H s = hp_csum (wh_w H) (wh_weight H s) s.
Proof. reflexivity. Qed.

Lemma hp_nodup_syms256 : NoDup syms256.
Proof. unfold syms256. apply NoDup_map_inv with (f := Z.to_nat). rewrite map_map.
  rewrite (map_ext_in _ (fun x => x)) by (intros; lia). rewrite map_id. apply seq_NoDup. Qed.

Lemma hp_csum_init : forall W, hp_csum W 1 0 = 0.
Proof.
  intros. unfold hp_csum. transitivity (zsum (map (fun _ : Z => 0) syms256));
    [| generalize syms256; intros l; induction l; simpl; auto].
  f_equal. apply map_ext_in. intros k Hk. apply hp_in_syms256 in Hk. unfold hp_done.
  destruct (Z.ltb_spec 0 (zn W k)); simpl; auto.
  destruct (Z.ltb_spec (zn W k) 1); [lia |]. destruct (Z.ltb_spec k 0); [lia |].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma hp_done_hit : forall W w s k, 0 <= s -> zn W s = w -> 1 <= w ->
  hp_done W w (s + 1) k = orb (hp_done W w s k) (k =? s).
Proof.
  intros W w s k Hs Hw H1. unfold hp_done. destruct (Z.eqb_spec k s) as [-> | Hne].
  - rewrite Hw, Z.eqb_refl. destruct (Z.ltb_spec 0 w); [| lia]. destruct (Z.ltb_spec w w); [lia |].
    destruct (Z.ltb_spec s (s + 1)); [| lia]. destruct (Z.ltb_spec s s); [lia |]. reflexivity.
  - rewrite orb_false_r. destruct (Z.ltb_spec k (s + 1)), (Z.ltb_spec k s); try reflexivity; lia.
Qed.

Lemma hp_done_miss : forall W w s k, zn W s <> w -> hp_done W w (s + 1) k = hp_done W w s k.
Proof.
  intros W w s k Hw. unfold hp_done. destruct (Z.eqb_spec k s) as [-> | Hne].
  - destruct (Z.eqb_spec (zn W s) w); [contradiction |]. reflexivity.
  - destruct (Z.ltb_spec k (s + 1)), (Z.ltb_spec k s); try reflexivity; lia.
Qed.

Lemma hp_csum_hit : forall W w s, 0 <= s < 256 -> zn W s = w -> 1 <= w ->
  hp_csum W w (s + 1) = hp_csum W w s + 2 ^ (w - 1).
Proof.
  intros W w s Hs H0 H1. unfold hp_csum.
  rewrite (hp_zsum_diff1 (fun k => if hp_done W w (s + 1) k then 2 ^ (zn W k - 1) else 0)
             (fun k => if hp_done W w s k then 2 ^ (zn W k - 1) else 0) syms256 s).
  - rewrite hp_done_hit by lia. rewrite Z.eqb_refl, orb_true_r.
    assert (H2: hp_done W w s s = false).
    { unfold hp_done. rewrite H0, Z.ltb_irrefl, Z.eqb_refl, Z.ltb_irrefl. simpl. apply andb_false_r. }
    rewrite H2, H0. lia.
  - apply hp_nodup_syms256.
  - apply hp_in_syms256. auto.
  - intros. rewrite hp_done_hit by lia. destruct (Z.eqb_spec k s); [contradiction |]. rewrite orb_false_r. auto.
Qed.

Lemma hp_csum_miss : forall W w s, zn W s <> w -> hp_csum W w (s + 1) = hp_csum W w s.
Proof. intros. unfold hp_csum. f_equal. apply map_ext. intros. rewrite hp_done_miss by auto. auto. Qed.

(* beyond the last symbol the weights are 0: the next weight starts *)
Lemma hp_done_wrap : forall W w last k, 0 <= k < 256 -> (forall k, last < k < 256 -> zn W k = 0) ->
  hp_done W w (last + 1) k = hp_done W (w + 1) 0 k.
Proof.
  intros W w last k Hk Hz. unfold hp_done. destruct (Z_lt_le_dec last k).
  - rewrite Hz by lia. reflexivity.
  - destruct (Z.ltb_spec k (last + 1)); [| lia]. destruct (Z.ltb_spec k 0); [lia |].
    rewrite andb_true_r, andb_false_r, orb_false_r. f_equal.
    destruct (Z.ltb_spec (zn W k) w), (Z.eqb_spec (zn W k) w), (Z.ltb_spec (zn W k) (w + 1)); auto; lia.
Qed.

Lemma hp_csum_wrap : forall W w last, (forall k, last < k < 256 -> zn W k = 0) ->
  hp_csum W w (last + 1) = hp_csum W (w + 1) 0.
Proof.
  intros. unfold hp_csum. f_equal. apply map_ext_in. intros k Hk. apply hp_in_syms256 in Hk.
  rewrite hp_done_wrap with (last := last) by auto. reflexivity.
Qed.

Lemma hp_done_full : forall W log k, 0 <= k -> zn W k <= log ->
  hp_done W (log + 1) 0 k = (0 <? zn W k).
Proof.
  intros. unfold hp_done. destruct (Z.ltb_spec (zn W k) (log + 1)); [| lia]. destruct (0 <? zn W k); auto.
Qed.

Lemma hp_map_nth_seq : forall (g: Z -> Z) (l: list Z),
  map (fun n => g (nth n l 0)) (seq 0 (length l)) = map g l.
Proof.
  induction l; auto. simpl. rewrite <- seq_shift, map_map. f_equal. simpl. exact IHl.
Qed.

Lemma hp_map_zn : forall (g: Z -> Z) (W: list Z), Zlength W = 256 ->
  map (fun k => g (zn W k)) syms256 = map g W.
Proof.
  intros. unfold syms256. rewrite map_map. rewrite Zlength_correct in H.
  replace 256%nat with (length W) by lia. rewrite <- hp_map_nth_seq. apply map_ext. intros.
  unfold zn. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma hp_csum_full : forall W log, Zlength W = 256 -> Forall (fun w => 0 <= w <= log) W ->
  hp_csum W (log + 1) 0 = zsum (map hp_f W).
Proof.
  intros. unfold hp_csum. rewrite <- (hp_map_zn hp_f W) by auto. f_equal. apply map_ext_in.
  intros k Hk. apply hp_in_syms256 in Hk. rewrite hp_done_full.
  - unfold hp_f.
    assert (0 <= zn W k) by (rewrite hp_zn_Znth by lia; rewrite Forall_forall in H0; apply H0; apply Znth_In; lia).
    destruct (Z.ltb_spec 0 (zn W k)), (Z.eqb_spec (zn W k) 0); auto; lia.
  - lia.
  - rewrite hp_zn_Znth by lia. rewrite Forall_forall in H0. apply H0. apply Znth_In. lia.
Qed.

Lemma hp_csum_bound : forall W log w s, Zlength W = 256 -> Forall (fun w => 0 <= w <= log) W ->
  0 <= hp_csum W w s <= zsum (map hp_f W).
Proof.
  intros. rewrite <- hp_csum_full with (log := log) by auto. unfold hp_csum. split.
  - apply hp_zsum_nonneg. intros. destruct (hp_done _ _ _ _); [apply Z.pow_nonneg; lia | lia].
  - apply hp_zsum_le. intros k Hk. apply hp_in_syms256 in Hk.
    assert (zn W k <= log).
    { rewrite hp_zn_Znth by lia. rewrite Forall_forall in H0. apply H0. apply Znth_In. lia. }
    rewrite hp_done_full by (auto; lia). unfold hp_done.
    destruct (Z.ltb_spec 0 (zn W k)); simpl.
    + assert (0 <= 2 ^ (zn W k - 1)) by (apply Z.pow_nonneg; lia).
      match goal with |- context [if ?b then _ else _] => destruct b end; lia.
    + lia.
Qed.

(* ---------- after the symbols: everything the code loop needs ---------- *)

Lemma hp_last_in : forall (l: list Z), l <> [] -> In (last l 0) l.
Proof.
  induction l; intros N; [congruence |]. destruct l as [| b l'].
  - left; auto.
  - right. change (last (a :: b :: l') 0) with (last (b :: l') 0). apply IHl. discriminate.
Qed.

Lemma hp_sorted_last : forall l k, StronglySorted Z.lt l -> In k l -> k <= last l 0.
Proof.
  induction l; intros k S I; [destruct I |]. inversion S; subst.
  destruct l as [| b l'].
  - destruct I as [-> | []]. simpl. lia.
  - change (last (a :: b :: l') 0) with (last (b :: l') 0).
    destruct I as [-> | I].
    + assert (In (last (b :: l') 0) (b :: l')) by (apply hp_last_in; discriminate).
      rewrite Forall_forall in H2. specialize (H2 _ H). lia.
    + apply IHl; auto.
Qed.


Definition hp_H (W syms: list Z) (log: Z) : whuf :=
  {| wh_w := W; wh_log := log; wh_last := last syms 0; wh_used := syms |}.

Lemma hp_final : forall e log W syms,
  2 <= Zlength e -> Forall (fun x => 1 <= x <= log) e -> 1 <= log <= 11 -> In log e -> hp_kraft e = 2 ^ 11 ->
  hp_symw W syms (map (fun x => log + 1 - x) e) ->
  huf_ok (hp_H W syms log) /\ 0 <= last syms 0 < 256 /\ (forall k, last syms 0 < k < 256 -> zn W k = 0) /\
  Forall (fun w => 0 <= w <= log) W /\ zsum (map hp_f W) = 2 ^ log /\ Zlength W = 256 /\
  Zlength syms = Zlength e.
Proof.
  intros e log W syms H1 H2 H3 H4 H5 S.
  pose proof (hp_huf_ok e log W syms H1 H2 H3 H4 H5 S) as OK.
  destruct S as (HW & Hl & Hs & Hr & Hm & Hz & Hk). rewrite Zlength_map in Hl.
  assert (NE: syms <> []) by (intro E; subst; rewrite Zlength_nil in Hl; lia).
  assert (LI := hp_last_in syms NE).
  assert (LR: 0 <= last syms 0 < 256) by (rewrite Forall_forall in Hr; auto).
  assert (OK' := OK). destruct OK' as (_ & _ & F & K & _).
  split; [exact OK |]. split; [auto |]. split; [| split; [auto | split; [exact K | split; auto]]].
  intros k Hk'. rewrite hp_zn_Znth by lia. apply Hz; [lia |]. intro I.
  pose proof (hp_sorted_last syms k Hs I). lia.
Qed.

(* an array whose entries k are f k where done k, else the old ones *)
Definition hp_arr (cl c0: list val) (f: Z -> val) (done: Z -> bool) : Prop :=
  Zlength cl = 256 /\ forall k, 0 <= k < 256 -> Znth k cl = if done k then f k else Znth k c0.

Lemma hp_arr_init : forall c0 f W, Zlength c0 = 256 -> hp_arr c0 c0 f (hp_done W 1 0).
Proof.
  intros. split; auto. intros. unfold hp_done.
  destruct (Z.ltb_spec 0 (zn W k)); simpl; auto.
  destruct (Z.ltb_spec (zn W k) 1); [lia |]. destruct (Z.ltb_spec k 0); [lia |].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma hp_arr_hit : forall cl c0 f W w s, hp_arr cl c0 f (hp_done W w s) -> 0 <= s < 256 -> zn W s = w -> 1 <= w ->
  hp_arr (upd_Znth s cl (f s)) c0 f (hp_done W w (s + 1)).
Proof.
  intros cl c0 f W w s [L A] Hs Hw H1. split; [list_solve |]. intros k Hk.
  rewrite hp_done_hit by lia. destruct (Z.eqb_spec k s).
  - subst. rewrite upd_Znth_same by lia. rewrite orb_true_r. reflexivity.
  - rewrite upd_Znth_diff by lia. rewrite orb_false_r. auto.
Qed.

Lemma hp_arr_miss : forall cl c0 f W w s, hp_arr cl c0 f (hp_done W w s) -> zn W s <> w ->
  hp_arr cl c0 f (hp_done W w (s + 1)).
Proof.
  intros cl c0 f W w s [L A] Hw. split; auto. intros k Hk. rewrite hp_done_miss by auto. auto.
Qed.

Lemma hp_arr_wrap : forall cl c0 f W w last, hp_arr cl c0 f (hp_done W w (last + 1)) ->
  (forall k, last < k < 256 -> zn W k = 0) -> hp_arr cl c0 f (hp_done W (w + 1) 0).
Proof.
  intros cl c0 f W w last [L A] Hz. split; auto. intros k Hk. rewrite <- hp_done_wrap with (last := last) by auto.
  auto.
Qed.

Lemma hp_arr_full : forall cl c0 f W log k, hp_arr cl c0 f (hp_done W (log + 1) 0) ->
  Forall (fun w => 0 <= w <= log) W -> Zlength W = 256 -> 0 <= k < 256 -> zn W k <> 0 -> Znth k cl = f k.
Proof.
  intros cl c0 f W log k [L A] F LW Hk Hn. rewrite A by auto. rewrite hp_done_full.
  - assert (0 <= zn W k).
    { rewrite hp_zn_Znth by lia. rewrite Forall_forall in F. apply F. apply Znth_In. lia. }
    destruct (Z.ltb_spec 0 (zn W k)); [reflexivity | lia].
  - lia.
  - rewrite hp_zn_Znth by lia. rewrite Forall_forall in F. apply F. apply Znth_In. lia.
Qed.

Lemma hp_arr_def : forall cl c0 f done, hp_arr cl c0 f done -> Zlength c0 = 256 ->
  (forall k, exists i, f k = Vint i) -> Forall (fun v => exists i, v = Vint i) c0 ->
  Forall (fun v => exists i, v = Vint i) cl.
Proof.
  intros cl c0 f done [L A] L0 Hf F0. apply Forall_Znth. intros k Hk. rewrite L in Hk. rewrite A by auto.
  destruct (done k); auto. apply Forall_Znth; auto. lia.
Qed.

(* the C arithmetic of the code loop *)
Lemma hp_code_val : forall cell w, 0 <= cell <= 2048 -> 1 <= w <= 11 ->
  Int.zero_ext 16 (Int.shru (Int.repr cell) (Int.repr (w - 1))) = Int.repr (cell / 2 ^ (w - 1)).
Proof.
  intros. rewrite Int.shru_div_two_p. rewrite !Int.unsigned_repr by rep_lia. rewrite two_p_correct.
  assert (0 <= cell / 2 ^ (w - 1) <= 2048).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia |].
    assert (1 <= 2 ^ (w - 1)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
    nia. }
  remember (cell / 2 ^ (w - 1)) as q.
  apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma hp_cell_add : forall cell w, 1 <= w <= 11 ->
  Int.add (Int.repr cell) (Int.shl (Int.repr 1) (Int.repr (w - 1))) = Int.repr (cell + 2 ^ (w - 1)).
Proof.
  intros. rewrite Int.shl_mul_two_p. rewrite !Int.unsigned_repr by rep_lia. rewrite two_p_correct.
  rewrite Int.mul_commut, Int.mul_one. rewrite add_repr. reflexivity.
Qed.

Lemma hp_shl_one : forall n, 0 <= n <= 11 -> Int.shl (Int.repr 1) (Int.repr n) = Int.repr (2 ^ n).
Proof.
  intros. rewrite Int.shl_mul_two_p. rewrite !Int.unsigned_repr by rep_lia. rewrite two_p_correct.
  rewrite Int.mul_commut, Int.mul_one. reflexivity.
Qed.
