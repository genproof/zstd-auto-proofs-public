(* Unit-independent lemmas for the body proofs of huf_put_fse_weights (WB_huf_fw_<u>.v): the weights
   of a huf_t, the need[] array (need_of), the counting / selection loops, the bit fields written. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.writer.model.WModel.
Require Import Zstd.proof.harness.writer.model.WM_FseTab.
Require Import Zstd.proof.harness.writer.model.WM_Bits.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* the weights of a huf_t *)

Lemma hfl_last_In : forall (l: list Z) d, l <> nil -> In (last l d) l.
Proof.
  induction l as [| a l IH]; intros d Hl; [congruence |].
  destruct l as [| b l]; [left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma hfl_syms256_range : forall x, In x syms256 -> 0 <= x <= 255.
Proof.
  intros x Hx. unfold syms256 in Hx. apply in_map_iff in Hx. destruct Hx as [k [Hk Hin]].
  apply in_seq in Hin. lia.
Qed.

Lemma hfl_last_le : forall H, huf_ok H -> 0 <= wh_last H <= 255.
Proof.
  intros H Hok. destruct Hok as [_ [_ [_ [_ [Hu [H2 [Hl _]]]]]]].
  rewrite Hl. apply hfl_syms256_range.
  assert (Hne : wh_used H <> nil) by (intro E; rewrite E, Zlength_nil in H2; lia).
  pose proof (hfl_last_In (wh_used H) 0 Hne) as HI. rewrite Hu in HI.
  apply filter_In in HI. destruct HI as [HI _]. rewrite <- Hu in HI. exact HI.
Qed.

Lemma hfl_w : forall H, huf_ok H ->
  Zlength (wh_w H) = 256 /\ forall k, 0 <= k < 256 -> 0 <= Znth k (wh_w H) <= 11.
Proof.
  intros H Hok. destruct Hok as [Hlen [Hlog [Hf _]]]. split; auto.
  intros k Hk. rewrite Forall_forall in Hf.
  assert (In (Znth k (wh_w H)) (wh_w H)) by (apply Znth_In; lia).
  specialize (Hf _ H0). lia.
Qed.

Lemma hfl_zn : forall (l: list Z) i, 0 <= i -> zn l i = Znth i l.
Proof.
  intros. unfold zn, Znth. destruct (Z_lt_dec i 0); [lia | reflexivity].
Qed.

Lemma hfl_weights : forall H, 0 <= wh_last H <= Zlength (wh_w H) ->
  hfw_weights H = sublist 0 (wh_last H) (wh_w H).
Proof.
  intros. unfold hfw_weights. rewrite sublist_firstn. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* need_of *)

Lemma need_of_Zlength : forall l, Zlength (need_of l) = 53.
Proof. intros. unfold need_of. rewrite Zlength_map, Zlength_correct, seq_length. reflexivity. Qed.

Lemma need_of_Znth : forall l k, 0 <= k < 53 ->
  Znth k (need_of l) = if existsb (Z.eqb k) l then 1 else 0.
Proof.
  intros. unfold need_of. rewrite Znth_map by (rewrite Zlength_correct, seq_length; simpl; lia).
  unfold Znth. destruct (Z_lt_dec k 0); [lia |]. rewrite seq_nth by lia. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma need_of_snoc : forall l w, 0 <= w < 53 ->
  need_of (l ++ [w]) = upd_Znth w (need_of l) 1.
Proof.
  intros l w Hw. apply Znth_eq_ext.
  - rewrite upd_Znth_Zlength by (rewrite need_of_Zlength; lia). rewrite !need_of_Zlength. reflexivity.
  - intros k Hk. rewrite need_of_Zlength in Hk. rewrite need_of_Znth by lia.
    rewrite existsb_app. simpl. rewrite orb_false_r.
    destruct (Z.eq_dec k w) as [E | E].
    + subst k. rewrite upd_Znth_same by (rewrite need_of_Zlength; lia). rewrite Z.eqb_refl, orb_true_r. reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?need_of_Zlength; lia). rewrite need_of_Znth by lia.
      rewrite (proj2 (Z.eqb_neq k w) E), orb_false_r. reflexivity.
Qed.

Lemma need_of_01 : forall l, Forall (fun x => 0 <= x <= 1) (need_of l).
Proof.
  intros. unfold need_of. rewrite Forall_map. apply Forall_forall. intros x _.
  destruct (existsb _ _); lia.
Qed.

Lemma need_of_In : forall l w, 0 <= w < 53 -> In w l -> zn (need_of l) w <> 0.
Proof.
  intros l w Hw Hin. rewrite hfl_zn by lia. rewrite need_of_Znth by lia.
  assert (existsb (Z.eqb w) l = true) by (apply existsb_exists; exists w; split; auto; apply Z.eqb_refl).
  rewrite H. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* counting loops *)

Fixpoint hcnt (f: Z -> bool) (k: nat) : Z :=
  match k with O => 0 | S k' => hcnt f k' + (if f (Z.of_nat k') then 1 else 0) end.

Lemma hcnt_step : forall f s, 0 <= s ->
  hcnt f (Z.to_nat (s + 1)) = hcnt f (Z.to_nat s) + (if f s then 1 else 0).
Proof.
  intros. rewrite Z2Nat.inj_add by lia. rewrite Nat.add_1_r. simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma hcnt_range : forall f k, 0 <= hcnt f k <= Z.of_nat k.
Proof. induction k; [simpl; lia |]. cbn [hcnt]. rewrite Nat2Z.inj_succ. destruct (f _); lia. Qed.

Lemma hcnt_pos : forall f k i, 0 <= i < Z.of_nat k -> f i = true -> 1 <= hcnt f k.
Proof.
  induction k; intros i Hi Hf; [simpl in Hi; lia |]. cbn [hcnt]. rewrite Nat2Z.inj_succ in Hi.
  destruct (Z.eq_dec i (Z.of_nat k)).
  - subst. rewrite Hf. pose proof (hcnt_range f k). lia.
  - pose proof (IHk i ltac:(lia) Hf). destruct (f (Z.of_nat k)); lia.
Qed.

Lemma hcnt_zero : forall f, hcnt f (Z.to_nat 0) = 0.
Proof. reflexivity. Qed.

(* the selection loops: pick (unsigned) is p0 - count *)
Lemma hrepr_zero : forall x, - Int.modulus < x < Int.modulus -> Int.repr x = Int.zero -> x = 0.
Proof.
  intros x Hx E. apply (f_equal Int.unsigned) in E. rewrite Int.unsigned_repr_eq in E.
  change (Int.unsigned Int.zero) with 0 in E.
  destruct (Z_le_dec 0 x).
  - rewrite Z.mod_small in E by lia. auto.
  - assert (x mod Int.modulus = x + Int.modulus).
    { rewrite <- (Z.mod_small (x + Int.modulus) Int.modulus) by lia.
      rewrite <- Z.add_mod_idemp_r, Z_mod_same_full, Z.add_0_r by lia. reflexivity. }
    lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the output tail *)

(* tl_after k tl = sublist k (Zlength tl) tl *)
Lemma hfl_tl_after_after : forall (tl: list val) a b, 0 <= a -> 0 <= b ->
  sublist a (Zlength (sublist b (Zlength tl) tl)) (sublist b (Zlength tl) tl) = sublist (b + a) (Zlength tl) tl.
Proof.
  intros.
  destruct (Z_le_dec b (Zlength tl)).
  - rewrite Zlength_sublist by lia.
    destruct (Z_le_dec a (Zlength tl - b)).
    + rewrite sublist_sublist by lia. f_equal; lia.
    + rewrite !sublist_over by (try rewrite Zlength_sublist; lia). reflexivity.
  - rewrite (sublist_over tl b) by lia. rewrite (sublist_over tl (b + a)) by lia.
    unfold sublist. simpl. destruct (Z.to_nat _); reflexivity.
Qed.


(* ---------------------------------------------------------------------------------------------- *)
(* the tables *)

Lemma hfl_table : forall log norm, log <> 0 ->
  wf_table {| wf_log := log; wf_nsym := Zlength norm; wf_norm := norm |} = fse_build norm log.
Proof.
  intros. unfold wf_table. simpl. rewrite (proj2 (Z.eqb_neq log 0) H). reflexivity.
Qed.

Lemma hfl_base : forall log norm, ndist_ok log norm -> ndist_base log norm.
Proof. intros log norm [A [B [C [D _]]]]. repeat split; auto; lia. Qed.

Lemma hshl1 : forall k, 0 <= k < 31 -> Int.shl (Int.repr 1) (Int.repr k) = Int.repr (2 ^ k).
Proof.
  intros. unfold Int.shl. rewrite !Int.unsigned_repr by (try split; try lia; rep_lia).
  rewrite Z.shiftl_1_l. reflexivity.
Qed.

Lemma hze16 : forall x, 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

Lemma hze8 : forall x, 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros. apply zero_ext_inrange. rewrite Int.unsigned_repr by rep_lia. simpl. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the chains of states (st[i] for i >= the loop index) *)

Definition hchain (tab: fse_table) (W: list Z) (n log i: Z) (sts: list Z) : Prop :=
  Zlength sts = n /\
  (forall k, i <= k < n -> 0 <= Znth k sts < 2 ^ log /\ fe_sym (fse_cell tab (Znth k sts)) = Znth k W) /\
  (forall k, i <= k < n - 2 ->
     fe_base (fse_cell tab (Znth k sts)) <= Znth (k + 2) sts <
       fe_base (fse_cell tab (Znth k sts)) + 2 ^ fe_nb (fse_cell tab (Znth k sts))) /\
  0 < fe_nb (fse_cell tab (Znth (n - 2) sts)).

(* the array st (values) holds sts from i on *)
Definition hstv (stv: list val) (n i: Z) (sts: list Z) : Prop :=
  Zlength stv = 258 /\ forall k, i <= k < n -> Znth k stv = Vint (Int.repr (Znth k sts)).

Lemma hchain_init : forall tab W n log x1 x2, 2 <= n ->
  0 <= x1 < 2 ^ log -> fe_sym (fse_cell tab x1) = Znth (n - 1) W ->
  0 <= x2 < 2 ^ log -> fe_sym (fse_cell tab x2) = Znth (n - 2) W -> 0 < fe_nb (fse_cell tab x2) ->
  hchain tab W n log (n - 2) (Zrepeat 0 (n - 2) ++ [x2; x1]).
Proof.
  intros tab W n log x1 x2 Hn H1 E1 H2 E2 N2.
  assert (Z2 : Znth (n - 2) (Zrepeat 0 (n - 2) ++ [x2; x1]) = x2) by list_solve.
  assert (Z1 : Znth (n - 1) (Zrepeat 0 (n - 2) ++ [x2; x1]) = x1) by list_solve.
  split; [list_solve |]. split; [| split].
  - intros k Hk. assert (k = n - 2 \/ k = n - 1) as [-> | ->] by lia.
    + rewrite Z2. auto.
    + rewrite Z1. auto.
  - intros k Hk. lia.
  - rewrite Z2. auto.
Qed.

Lemma hstv_init : forall n x1 x2, 2 <= n <= 255 ->
  hstv (upd_Znth (n - 2) (upd_Znth (n - 1) (Zrepeat Vundef 258) (Vint (Int.repr x1))) (Vint (Int.repr x2)))
       n (n - 2) (Zrepeat 0 (n - 2) ++ [x2; x1]).
Proof.
  intros n x1 x2 Hn. split; [list_solve |].
  intros k Hk. assert (k = n - 2 \/ k = n - 1) as [-> | ->] by lia; list_solve.
Qed.

Lemma hchain_step : forall tab W n log i sts x, 1 <= i <= n - 2 ->
  hchain tab W n log i sts ->
  0 <= x < 2 ^ log -> fe_sym (fse_cell tab x) = Znth (i - 1) W ->
  fe_base (fse_cell tab x) <= Znth (i + 1) sts < fe_base (fse_cell tab x) + 2 ^ fe_nb (fse_cell tab x) ->
  hchain tab W n log (i - 1) (upd_Znth (i - 1) sts x).
Proof.
  intros tab W n log i sts x Hi [Hl [HA [HB HC]]] Hx Ex Bx.
  assert (Hs : forall k, 0 <= k < n -> k <> i - 1 -> Znth k (upd_Znth (i - 1) sts x) = Znth k sts).
  { intros. rewrite upd_Znth_diff by lia. auto. }
  assert (Hs0 : Znth (i - 1) (upd_Znth (i - 1) sts x) = x) by (rewrite upd_Znth_same by lia; auto).
  split; [rewrite upd_Znth_Zlength by lia; auto |]. split; [| split].
  - intros k Hk. destruct (Z.eq_dec k (i - 1)) as [-> | E].
    + rewrite Hs0. auto.
    + rewrite Hs by lia. apply HA. lia.
  - intros k Hk. destruct (Z.eq_dec k (i - 1)) as [-> | E].
    + rewrite Hs0. rewrite Hs by lia. replace (i - 1 + 2) with (i + 1) by lia. auto.
    + rewrite !Hs by lia. apply HB. lia.
  - rewrite Hs by lia. auto.
Qed.

Lemma hstv_step : forall stv n i sts x, 1 <= i <= n - 2 -> n <= 258 ->
  hstv stv n i sts -> Zlength sts = n ->
  hstv (upd_Znth (i - 1) stv (Vint (Int.repr x))) n (i - 1) (upd_Znth (i - 1) sts x).
Proof.
  intros stv n i sts x Hi Hn [Hl HE] Hsl. split; [rewrite upd_Znth_Zlength by lia; auto |].
  intros k Hk. destruct (Z.eq_dec k (i - 1)) as [-> | E].
  - rewrite !upd_Znth_same by lia. auto.
  - rewrite !upd_Znth_diff by lia. apply HE. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the fields written *)

Definition hloopf (tab: fse_table) (n: Z) (sts: list Z) (j: nat) : Z * Z :=
  let i := n - 3 - Z.of_nat j in
  (zn sts (i + 2) - fe_base (fse_cell tab (zn sts i)), fe_nb (fse_cell tab (zn sts i))).

Lemma hfw_fields_eq : forall H norm log sts,
  hfw_fields H norm log sts =
  map (hloopf (fse_build norm log) (wh_last H) sts) (seq 0 (Z.to_nat (wh_last H - 2))) ++
  [(zn sts 1, log); (zn sts 0, log)].
Proof. reflexivity. Qed.

Lemma hloop_snoc : forall tab n sts k,
  map (hloopf tab n sts) (seq 0 (S k)) = map (hloopf tab n sts) (seq 0 k) ++ [hloopf tab n sts k].
Proof. intros. rewrite seq_S, map_app. reflexivity. Qed.

Lemma hloop_ok : forall tab W n log sts k, 0 <= log <= 32 ->
  (forall s, 0 <= s < 2 ^ log -> 0 <= fe_nb (fse_cell tab s) <= log) ->
  hchain tab W n log 0 sts -> (k <= Z.to_nat (n - 2))%nat ->
  fields_ok (map (hloopf tab n sts) (seq 0 k)).
Proof.
  intros tab W n log sts k Hl Hnb [Hlen [HA [HB HC]]] Hk.
  unfold fields_ok. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  unfold hloopf. cbv zeta. simpl fst. simpl snd.
  set (i := n - 3 - Z.of_nat j).
  assert (Hi : 0 <= i <= n - 3) by (unfold i; lia).
  rewrite !hfl_zn by lia.
  destruct (HA i ltac:(lia)) as [Hr _]. specialize (Hnb _ Hr). specialize (HB i ltac:(lia)).
  split; lia.
Qed.

Lemma hbw_full_len : forall W L, 0 <= L -> Zlength (bw_full W L) = L / 8.
Proof.
  intros. unfold bw_full. rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id. apply Z.div_pos; lia.
Qed.

Lemma hbw_mark_len : forall W L, 0 <= L -> Zlength (bw_mark W L) = L / 8 + 1.
Proof.
  intros. unfold bw_mark. rewrite Zlength_correct, wmb_length_le_bytes. apply Z2Nat.id.
  pose proof (Z.div_pos L 8). lia.
Qed.

Lemma hfields_snoc : forall pre v nb,
  fields_wl (pre ++ [(v, nb)]) 0 0 =
  (fst (fields_wl pre 0 0) + v * 2 ^ snd (fields_wl pre 0 0), snd (fields_wl pre 0 0) + nb).
Proof. intros. rewrite fields_wl_app. reflexivity. Qed.

(* the bit writer after the first k fields *)
Definition hwl (tab: fse_table) (n: Z) (sts: list Z) (k: nat) : Z * Z :=
  fields_wl (map (hloopf tab n sts) (seq 0 k)) 0 0.

Lemma hwl_S : forall tab n sts k,
  hwl tab n sts (S k) =
  (fst (hwl tab n sts k) + fst (hloopf tab n sts k) * 2 ^ snd (hwl tab n sts k),
   snd (hwl tab n sts k) + snd (hloopf tab n sts k)).
Proof.
  intros. unfold hwl. rewrite hloop_snoc. destruct (hloopf tab n sts k) as [v nb] eqn:E.
  rewrite hfields_snoc. reflexivity.
Qed.

Lemma hwl_range : forall tab W n log sts k, 0 <= log <= 32 ->
  (forall s, 0 <= s < 2 ^ log -> 0 <= fe_nb (fse_cell tab s) <= log) ->
  hchain tab W n log 0 sts -> (k <= Z.to_nat (n - 2))%nat ->
  0 <= snd (hwl tab n sts k) /\ 0 <= fst (hwl tab n sts k) < 2 ^ snd (hwl tab n sts k).
Proof.
  intros. unfold hwl.
  destruct (fields_wl_range (map (hloopf tab n sts) (seq 0 k)) 0 0
              (hloop_ok tab W n log sts k H H0 H1 H2) ltac:(lia) ltac:(simpl; lia)).
  split; lia.
Qed.

Lemma hfw_final : forall H norm log sts,
  fields_wl (hfw_fields H norm log sts) 0 0 =
  let wl := hwl (fse_build norm log) (wh_last H) sts (Z.to_nat (wh_last H - 2)) in
  (fst wl + zn sts 1 * 2 ^ snd wl + zn sts 0 * 2 ^ (snd wl + log), snd wl + log + log).
Proof.
  intros. rewrite hfw_fields_eq, fields_wl_app. unfold hwl.
  destruct (fields_wl _ 0 0) as [W L]. reflexivity.
Qed.

(* the conclusion *)
Lemma hfw_ok_of_chain : forall W lg n used norm log sts,
  2 <= n <= 255 -> Zlength W = 256 -> 5 <= log <= 6 -> ndist_ok log norm ->
  ndist_need 11 (need_of (sublist 0 n W)) norm ->
  hchain (fse_build norm log) W n log 0 sts ->
  hfw_ok {| wh_w := W; wh_log := lg; wh_last := n; wh_used := used |} norm log sts.
Proof.
  intros W lg n used norm log sts Hn HW Hl Hnd Hneed [Hlen [HA [HB HC]]].
  unfold hfw_ok. cbv zeta. rewrite hfl_weights by (cbn; lia). cbn [wh_last wh_w].
  split; [lia |]. split; [lia |]. split; [exact Hnd |]. split; [exact Hneed |]. split; [exact Hlen |].
  split; [| split].
  - intros i Hi. rewrite !hfl_zn by lia. destruct (HA i Hi) as [R E]. split; [exact R |].
    rewrite E. rewrite Znth_sublist by lia. f_equal; lia.
  - intros i Hi. rewrite !hfl_zn by lia. apply HB. lia.
  - rewrite hfl_zn by lia. auto.
Qed.

Lemma hfw_bytes_eq : forall W lg n used norm log sts,
  hfw_bytes {| wh_w := W; wh_log := lg; wh_last := n; wh_used := used |} norm log sts =
  fse_desc_bytes norm log ++
  (let wl := hwl (fse_build norm log) n sts (Z.to_nat (n - 2)) in
   bw_mark (fst wl + zn sts 1 * 2 ^ snd wl + zn sts 0 * 2 ^ (snd wl + log)) (snd wl + log + log)).
Proof.
  intros. unfold hfw_bytes, fields_mark, fields_W, fields_L. rewrite hfw_final. reflexivity.
Qed.
