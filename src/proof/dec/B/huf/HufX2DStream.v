(* X2D: the body of HUF_decodeStreamX2 (spec in HufX2DSpecs.v). *)
Require Export Zstd.proof.dec.B.huf.HufX2DSpecs.
Local Open Scope logic.

(* ---------- pure facts ---------- *)

Lemma bit_rep_inv sh gv s start pos lo p :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

(* BIT_reloadDStream never raises the window base; from a non-overflowed state, unfinished leaves at
   least 57 bits in the container, any other status puts the window at the bottom. *)
Lemma bs_reload_facts (pos lo: Z) :
  0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
  snd (bs_reload pos lo) <= lo /\
  (lo <= pos ->
   (fst (bs_reload pos lo) = BIT_unfinished -> snd (bs_reload pos lo) + 57 <= pos) /\
   (fst (bs_reload pos lo) <> BIT_unfinished -> snd (bs_reload pos lo) = 0)).
Proof.
  intros H0 H8 H64. unfold bs_reload.
  pose proof (Z.div_mod (lo + 64 - pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (lo + 64 - pos) 8 ltac:(lia)).
  pose proof (Z.div_mod lo 8 ltac:(lia)).
  assert (0 <= (lo + 64 - pos) / 8) by (apply Z.div_pos; lia).
  destruct (pos <? lo) eqn:E1; [cbn [fst snd]; split; [lia | intros; lia]|].
  destruct (8 <=? lo / 8) eqn:E2; [cbn [fst snd]; unfold BIT_unfinished; split; [lia|split; intros; lia]|].
  destruct (lo / 8 =? 0) eqn:E3.
  - assert (lo = 0) by lia. subst lo. cbn [fst snd].
    split; [lia|]. intros _. destruct (0 <? pos); unfold BIT_unfinished, BIT_endOfBuffer, BIT_completed;
    split; intros; lia.
  - destruct (lo / 8 <? (lo + 64 - pos) / 8) eqn:E4; cbn [fst snd];
      unfold BIT_unfinished, BIT_endOfBuffer; split; try lia; split; intros; lia.
Qed.

Lemma bs_reload_inv (s: list Z) (pos lo: Z) :
  bit_inv s pos lo -> 0 <= lo -> snd (bs_reload pos lo) <= lo.
Proof. intros (_ & _ & H0 & H8 & _ & H64 & _) _. apply (bs_reload_facts pos lo H0 H8 H64). Qed.

Section Model.
Variables (ht: huf_table) (s: list Z) (L: Z) (c2: list (val * (val * val))) (pos lo k: Z).
Hypotheses (Hf: hsym_facts) (Htab: x2_tab_ok ht L c2) (Hs: bytes_ok s) (Hk: 0 <= k).

(* the valid world: not overflowed, and the model decodes exactly k symbols from pos down to 0 *)
Definition xW : Prop := lo <= pos /\ exists l', huf_decode_syms ht s (Z.to_nat k) pos = Some (l', 0).

(* the ghost validity: the model's run goes through (j, pos1) having produced l *)
Definition vgood (j pos1: Z) (l: list Z) : Prop :=
  forall l', huf_decode_syms ht s (Z.to_nat k) pos = Some (l', 0) ->
  exists r, huf_decode_syms ht s (Z.to_nat (k - j)) pos1 = Some (r, 0) /\ l' = l ++ r.

(* the state after j bytes *)
Definition minv (j pos1 lo1: Z) (l: list Z) : Prop :=
  0 <= j <= k /\ Zlength l = j /\ bytes_ok l /\ lo1 + 64 - pos1 <= lo + 64 - pos + 12 * j /\
  (xW -> vgood j pos1 l /\ lo1 <= pos1).

Lemma minv_0 : minv 0 pos lo [].
Proof.
  split; [lia|]. split; [reflexivity|]. split; [constructor|]. split; [lia|].
  intros [Hlp _]. split; [|lia]. intros l' H. exists l'. rewrite Z.sub_0_r. auto.
Qed.

Lemma tab_facts : huf_ok ht /\ ht_log ht <= L <= HUF_TABLELOG_MAX /\ 1 <= L <= 12.
Proof. destruct Htab as (Hok & HL & _). destruct Hok as (H1 & H2 & H3). unfold HUF_TABLELOG_MAX in *.
  split; [split; auto|]. lia. Qed.

Lemma decode_pos_nonneg (m: nat) (p: Z) (r: list Z) :
  huf_decode_syms ht s m p = Some (r, 0) -> 0 <= p.
Proof.
  destruct tab_facts as ((_ & _ & Hall) & _). intros H. destruct m as [|m].
  - simpl in H. inversion H. lia.
  - simpl in H.
    assert (Hnb: 0 <= snd (nth (Z.to_nat (bs_peek_s s p (ht_log ht))) (huf_cells ht) (0, 0))).
    { destruct (lt_dec (Z.to_nat (bs_peek_s s p (ht_log ht))) (length (huf_cells ht))) as [Hi|Hi].
      - rewrite Forall_forall in Hall. specialize (Hall _ (nth_In _ (0, 0) Hi)). lia.
      - rewrite nth_overflow by lia. simpl. lia. }
    destruct (nth _ (huf_cells ht) (0, 0)) as [sy nb]. simpl in Hnb.
    destruct (p - nb <? 0) eqn:E; [discriminate|]. apply Z.ltb_ge in E. lia.
Qed.

(* the run from (j, pos1): k - j symbols, pos1 within [k - j, 12 (k - j)] *)
Lemma vgood_run (j pos1 lo1: Z) (l: list Z) :
  minv j pos1 lo1 l -> xW ->
  exists r, huf_decode_syms ht s (Z.to_nat (k - j)) pos1 = Some (r, 0) /\
    Zlength r = k - j /\ k - j <= pos1 <= 12 * (k - j).
Proof.
  intros (Hj & _ & _ & _ & Hw) HW. destruct (Hw HW) as [Hg Hlp].
  destruct HW as [Hlo [l0 Hl0]]. destruct (Hg l0 Hl0) as [r [Hr _]].
  exists r. split; [exact Hr|].
  destruct tab_facts as (Hok & HL & HL12).
  assert (Hp: 0 <= pos1) by exact (decode_pos_nonneg _ _ _ Hr).
  destruct (huf_decode_syms_bounds ht s _ pos1 0 r Hok Hp Hr) as (H1 & _ & H3 & _).
  rewrite Z2Nat.id in H1, H3 by lia. split; [exact H1|]. nia.
Qed.

(* a reload left >= 57 bits but at most one symbol remains: impossible in the valid world *)
Lemma minv_far_false (j pos1 lo1: Z) (l: list Z) :
  minv j pos1 lo1 l -> xW -> k - j <= 1 -> 0 <= lo1 -> lo1 + 57 <= pos1 -> False.
Proof.
  intros Hm HW Hkj Hlo1 Hp. destruct (vgood_run j pos1 lo1 l Hm HW) as (r & _ & _ & H). lia.
Qed.

(* one decodeSymbolX2: kk (1 or 2) bytes; e: the reserve left after it *)
Lemma minv_step (j pos1 lo1 e v kk b2 nb: Z) (l: list Z) :
  minv j pos1 lo1 l -> j + 2 <= k -> 0 <= e -> (xW -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  0 <= v < 2 ^ L -> (lo1 <= pos1 - L \/ (lo1 = 0 /\ 0 < pos1) -> v = bs_peek (bs_value s) pos1 L) ->
  x2_step ht L v kk b2 nb ->
  1 <= kk <= 2 /\ 1 <= nb <= L /\
  minv (j + kk) (pos1 - nb) lo1 (l ++ sublist 0 kk [fst (hsym ht L v); b2]) /\
  (xW -> lo1 + e <= pos1 - nb \/ lo1 = 0).
Proof.
  intros Hm Hjk He Hres Hv Hex Hst.
  destruct tab_facts as (Hok & HL & HL12).
  assert (Hkk: 1 <= kk <= 2 /\ 1 <= nb <= L).
  { destruct Hst as (_ & Hnb & Hc). destruct (hsym ht L v) as [s1 n1].
    destruct Hc as [[-> _]|Hc]; [lia|]. destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2].
    destruct Hc as (-> & _). lia. }
  pose proof (hsym_range ht L v Hok ltac:(lia) Hv) as [Hs1 _].
  assert (Hb2: 0 <= b2 < 256) by (destruct Hst; lia).
  pose proof Hm as Hm0. destruct Hm as (Hj & Hl & Hlb & Hsafe & Hw).
  split; [lia|]. split; [lia|].
  assert (HW2: xW -> (lo1 + e <= pos1 - nb \/ lo1 = 0) /\ vgood (j + kk) (pos1 - nb)
                     (l ++ sublist 0 kk [fst (hsym ht L v); b2]) /\ lo1 <= pos1 - nb).
  { intros HW. destruct (vgood_run j pos1 lo1 l Hm0 HW) as (r0 & Hr0 & Hlr0 & Hp1).
    destruct (Hw HW) as [Hg Hlp].
    assert (Hvx: v = bs_peek (bs_value s) pos1 L).
    { apply Hex. destruct (Hres HW) as [H|H]; [left; lia | right; lia]. }
    assert (Hkm: kk <= Z.of_nat (Z.to_nat (k - j))) by lia.
    destruct (x2_step_syms Hf ht s L pos1 v kk b2 nb _ r0 0 Hok HL Hs ltac:(lia) Hvx Hst Hkm Hr0) as [_ Hn0].
    assert (Hpn: 0 <= pos1 - nb) by exact (decode_pos_nonneg _ _ _ Hn0).
    split; [destruct (Hres HW); [left|right]; lia|].
    split; [|destruct (Hres HW); lia].
    intros l' Hl'. destruct (Hg l' Hl') as [r [Hr ->]].
    destruct (x2_step_syms Hf ht s L pos1 v kk b2 nb _ r 0 Hok HL Hs ltac:(lia) Hvx Hst Hkm Hr) as [H1 H2].
    exists (sublist kk (Zlength r) r). split.
    - replace (Z.to_nat (k - (j + kk))) with (Z.to_nat (k - j) - Z.to_nat kk)%nat by lia. exact H2.
    - rewrite <- app_assoc. f_equal. rewrite <- H1.
      assert (Zlength r = k - j).
      { destruct (huf_decode_syms_bounds ht s _ pos1 0 r Hok ltac:(lia) Hr) as (Hz & _).
        rewrite Hz. lia. }
      rewrite sublist_rejoin by lia. rewrite sublist_same by lia. reflexivity. }
  split; [|intros HW; apply HW2, HW].
  split; [lia|]. split; [list_solve|].
  split.
  { apply Forall_app. split; [exact Hlb|]. apply Forall_sublist. repeat constructor; unfold is_byte; lia. }
  split; [lia|]. intros HW. destruct (HW2 HW) as (_ & ? & ?). auto.
Qed.

Lemma x2_last_pos_ge (pos1 lo1 kk nb: Z) : 0 <= nb -> pos1 - nb <= x2_last_pos pos1 lo1 kk nb.
Proof. intros. unfold x2_last_pos. destruct (kk =? 1); [lia|]. destruct (pos1 <=? lo1); lia. Qed.

(* the last decodeLastSymbolX2 (one byte left) *)
Lemma minv_last (j pos1 lo1 v kk b2 nb: Z) (l: list Z) :
  minv j pos1 lo1 l -> j + 1 = k -> (xW -> lo1 = 0) ->
  0 <= v < 2 ^ L -> (lo1 <= pos1 - L \/ (lo1 = 0 /\ 0 < pos1) -> v = bs_peek (bs_value s) pos1 L) ->
  x2_step ht L v kk b2 nb ->
  1 <= nb <= L /\
  minv k (x2_last_pos pos1 lo1 kk nb) lo1 (l ++ [fst (hsym ht L v)]) /\
  (xW -> x2_last_pos pos1 lo1 kk nb = 0).
Proof.
  intros Hm Hjk Hz Hv Hex Hst.
  destruct tab_facts as (Hok & HL & HL12).
  assert (Hnb: 1 <= nb <= L) by (destruct Hst as (_ & ? & _); lia).
  pose proof (hsym_range ht L v Hok ltac:(lia) Hv) as [Hs1 _].
  pose proof (x2_last_pos_ge pos1 lo1 kk nb ltac:(lia)).
  assert (HW2: xW -> x2_last_pos pos1 lo1 kk nb = 0 /\ vgood k (x2_last_pos pos1 lo1 kk nb) (l ++ [fst (hsym ht L v)])).
  { intros HW. destruct (vgood_run j pos1 lo1 l Hm HW) as (r0 & Hr0 & Hlr0 & Hp1).
    destruct Hm as (_ & _ & _ & _ & Hw). destruct (Hw HW) as [Hg _]. specialize (Hz HW). subst lo1.
    assert (Hvx: v = bs_peek (bs_value s) pos1 L) by (apply Hex; right; lia).
    replace (Z.to_nat (k - j)) with 1%nat in Hr0 by lia.
    destruct (x2_first Hf ht s L pos1 v 0 r0 0 Hok HL Hs ltac:(lia) Hvx Hr0) as (r' & -> & Hp & Hr').
    simpl in Hr'. injection Hr' as Hp0.
    assert (Hpos: x2_last_pos pos1 0 kk nb = 0).
    { destruct Hst as (_ & _ & Hc). unfold x2_last_pos.
      destruct (hsym ht L v) as [s1 n1] eqn:Eh. simpl in *.
      destruct Hc as [[-> ->]|Hc]; [simpl; lia|].
      pose proof (hsym_range ht L ((v * 2 ^ n1) mod 2 ^ L) Hok ltac:(lia)
                    (Z.mod_pos_bound (v * 2 ^ n1) (2 ^ L) ltac:(apply Z.pow_pos_nonneg; lia))) as [_ Hn2].
      destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2]. destruct Hc as (-> & _ & ->). simpl in Hn2.
      simpl. destruct (pos1 <=? 0) eqn:E; [apply Z.leb_le in E; lia|]. lia. }
    split; [exact Hpos|]. rewrite Hpos.
    intros l' Hl'. destruct (Hg l' Hl') as [r [Hr ->]].
    replace (Z.to_nat (k - j)) with 1%nat in Hr by lia.
    destruct (x2_first Hf ht s L pos1 v 0 r 0 Hok HL Hs ltac:(lia) Hvx Hr) as (r1 & -> & _ & Hr1).
    simpl in Hr1. injection Hr1 as Hr1e _. subst r1.
    exists []. rewrite Z.sub_diag. simpl. split; [reflexivity|]. rewrite <- app_assoc. reflexivity. }
  split; [exact Hnb|]. split; [|intros HW; apply HW2, HW].
  destruct Hm as (Hj & Hl & Hlb & Hsafe & Hw).
  split; [lia|]. split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia|].
  split; [apply Forall_app; split; [exact Hlb | repeat constructor; unfold is_byte; lia]|].
  split; [lia|]. intros HW. destruct (HW2 HW) as [Hp Hg]. split; [exact Hg|]. rewrite Hp, (Hz HW). lia.
Qed.

Lemma minv_end (pos1 lo1: Z) (l: list Z) :
  minv k pos1 lo1 l -> lo <= pos -> forall l', huf_decode_syms ht s (Z.to_nat k) pos = Some (l', 0) ->
  l = l' /\ pos1 = 0.
Proof.
  intros (_ & _ & _ & _ & Hw) Hlp l' Hl'.
  destruct (Hw (conj Hlp (ex_intro _ l' Hl'))) as [Hg _].
  destruct (Hg l' Hl') as [r [Hr ->]]. rewrite Z.sub_diag in Hr. simpl in Hr. inversion Hr; subst.
  rewrite app_nil_r. auto.
Qed.

Lemma minv_reload (j pos1 lo1: Z) (l: list Z) :
  minv j pos1 lo1 l -> bit_inv s pos1 lo1 ->
  minv j pos1 (snd (bs_reload pos1 lo1)) l /\
  (xW -> (fst (bs_reload pos1 lo1) = BIT_unfinished -> snd (bs_reload pos1 lo1) + 57 <= pos1) /\
         (fst (bs_reload pos1 lo1) <> BIT_unfinished -> snd (bs_reload pos1 lo1) = 0)).
Proof.
  intros (Hj & Hl & Hb & Hsafe & Hw) (_ & _ & H0 & H8 & _ & H64 & _).
  destruct (bs_reload_facts pos1 lo1 H0 H8 H64) as [Hle Hr].
  split.
  - split; [lia|]. split; [auto|]. split; [auto|]. split; [lia|].
    intros HW. destruct (Hw HW) as [Hg Hlp]. split; [auto | lia].
  - intros HW. destruct (Hw HW) as [_ Hlp]. apply Hr, Hlp.
Qed.

End Model.

(* ---------- the exact model: ExHuf's run of HUF_decodeStreamX2 follows the C ----------
   The C state (pos, lo) of the reader stands for any ExHuf container d with xb_rel s pos lo d.  Each decode
   moves the model's container as the C moves (pos, lo) (xstep), and the model's loops (xh_x2_loopr,
   xh_x2_loop1) unfold one iteration per iteration of the C's loops; the loop invariants of the body state
   that the model's run from the initial container is the run of the same loop from the current one. *)

Section Exact.
Variables (ht: huf_table) (s: list Z).

(* one decode emits w and moves the reader from (pos1, lo1) to (pos2, lo1) *)
Definition xstep (pos1 lo1 pos2: Z) (w: list Z) : Prop :=
  forall d1, xb_rel s pos1 lo1 d1 ->
  fst (xh_x2_sym (xhuf_of true ht) d1) = w /\ xb_rel s pos2 lo1 (snd (xh_x2_sym (xhuf_of true ht) d1)).

(* n decodes without reload *)
Definition xsteps (pos1 lo1 pos2: Z) (n: nat) (w: list Z) : Prop :=
  forall d1, xb_rel s pos1 lo1 d1 ->
  fst (xh_x2_n (xhuf_of true ht) d1 n) = w /\ xb_rel s pos2 lo1 (snd (xh_x2_n (xhuf_of true ht) d1 n)).

(* HUF_decodeSymbolX2's exact clause as one model decode: the cell's sequence is (s1, b2), kk bytes *)
Lemma xstep_of (L pos1 lo1 v kk b2 nb: Z) :
  L = xh_x2_log ht -> v = xb_look_fast (xb_of s pos1 lo1) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  0 <= fst (hsym ht L v) < 256 -> 0 <= b2 < 256 -> 1 <= kk <= 2 -> 0 <= nb ->
  0 <= lo1 + 64 - (pos1 - nb) <= Int.max_unsigned ->
  xstep pos1 lo1 (pos1 - nb) (sublist 0 kk [fst (hsym ht L v); b2]).
Proof.
  intros HLx Hv Hc Hs1 Hb2 Hkk Hnb Hb d1 Hr.
  assert (HL: 1 <= L <= 64) by (subst L; unfold xh_x2_log; destruct (ht_log ht <=? 11); lia).
  assert (Hlook: xb_look_fast d1 L = v).
  { rewrite Hv, (xb_look_rel s pos1 lo1 d1 L Hr HL). symmetry.
    apply (xb_look_rel s pos1 lo1 _ L (xb_rel_of s pos1 lo1) HL). }
  unfold xh_x2_sym, xh_cell. unfold xhuf_of. cbn [xh_log xh_cells]. rewrite <- HLx, Hlook, Hc.
  cbn [fst snd]. split.
  - set (s1 := fst (hsym ht L v)) in *.
    assert (E1: (s1 + 256 * b2) mod 256 = s1)
      by (rewrite Z.mul_comm, Z.mod_add by lia; apply Z.mod_small; lia).
    assert (E2: (s1 + 256 * b2) / 256 = b2)
      by (rewrite Z.mul_comm, Z.div_add by lia; rewrite Z.div_small by lia; lia).
    rewrite E1, E2.
    destruct (Z.eq_dec kk 1) as [->|Hk1]; [reflexivity|]. assert (kk = 2) as -> by lia. reflexivity.
  - apply xb_skip_rel; [exact Hr | lia | lia].
Qed.

Lemma xsteps_0 (p q: Z) : xsteps p q p O [].
Proof. intros d1 Hr. simpl. auto. Qed.

Lemma xsteps_S (p1 q p2 p3: Z) (n: nat) (w1 w2: list Z) :
  xstep p1 q p2 w1 -> xsteps p2 q p3 n w2 -> xsteps p1 q p3 (S n) (w1 ++ w2).
Proof.
  intros H1 H2 d1 Hr. cbn [xh_x2_n].
  destruct (H1 d1 Hr) as [E1 R1].
  destruct (xh_x2_sym (xhuf_of true ht) d1) as [c d] eqn:Ec. cbn [fst snd] in E1, R1. subst c.
  destruct (H2 d R1) as [E2 R2].
  destruct (xh_x2_n (xhuf_of true ht) d n) as [l d'] eqn:En. cbn [fst snd] in *. subst l. auto.
Qed.

(* one iteration of a reload loop (xh_x2_loopr): the reload, then K decodes *)
Lemma loopr_cont (f K: nat) (cnd: Z -> bool) (d1: xbit) (rem: Z) (acc w: list Z) (pos1 lo1 pos2: Z) :
  bit_inv s pos1 lo1 -> xb_rel s pos1 lo1 d1 -> fst (bs_reload pos1 lo1) = BIT_unfinished -> cnd rem = true ->
  xsteps pos1 (snd (bs_reload pos1 lo1)) pos2 K w ->
  exists d2, xb_rel s pos2 (snd (bs_reload pos1 lo1)) d2 /\
    xh_x2_loopr (S f) s (xhuf_of true ht) K cnd d1 rem acc =
    xh_x2_loopr f s (xhuf_of true ht) K cnd d2 (rem - Zlength w) (acc ++ w).
Proof.
  intros Hi Hr Hu Hc Hx.
  destruct (xb_reload_rel s pos1 lo1 d1 Hi Hr) as [E R].
  cbn [xh_x2_loopr].
  destruct (xb_reload s d1) as [st d] eqn:Ed. cbn [fst snd] in E, R.
  replace (st =? XB_unfinished) with true by (rewrite E, Hu; reflexivity).
  rewrite Hc. cbn [andb].
  destruct (Hx d R) as [Ew Rw].
  destruct (xh_x2_n (xhuf_of true ht) d K) as [l d'] eqn:En. cbn [fst snd] in *. subst l.
  exists d'. auto.
Qed.

(* the exit of a reload loop: the reload's state, nothing emitted *)
Lemma loopr_exit (f K: nat) (cnd: Z -> bool) (d1: xbit) (rem: Z) (acc: list Z) (pos1 lo1: Z) :
  bit_inv s pos1 lo1 -> xb_rel s pos1 lo1 d1 ->
  andb (fst (bs_reload pos1 lo1) =? BIT_unfinished) (cnd rem) = false ->
  exists d2, xb_rel s pos1 (snd (bs_reload pos1 lo1)) d2 /\
    xh_x2_loopr (S f) s (xhuf_of true ht) K cnd d1 rem acc = (acc, d2, rem).
Proof.
  intros Hi Hr Hc.
  destruct (xb_reload_rel s pos1 lo1 d1 Hi Hr) as [E R].
  cbn [xh_x2_loopr].
  destruct (xb_reload s d1) as [st d] eqn:Ed. cbn [fst snd] in E, R.
  replace (st =? XB_unfinished) with (fst (bs_reload pos1 lo1) =? BIT_unfinished) by (rewrite E; reflexivity).
  rewrite Hc. exists d. auto.
Qed.

(* one iteration of the loop without reload (xh_x2_loop1) *)
Lemma loop1_cont (f: nat) (d1: xbit) (rem: Z) (acc w: list Z) (pos1 lo1 pos2: Z) :
  xb_rel s pos1 lo1 d1 -> 2 <= rem -> xstep pos1 lo1 pos2 w ->
  exists d2, xb_rel s pos2 lo1 d2 /\
    xh_x2_loop1 (S f) (xhuf_of true ht) d1 rem acc = xh_x2_loop1 f (xhuf_of true ht) d2 (rem - Zlength w) (acc ++ w).
Proof.
  intros Hr Hrem Hx. cbn [xh_x2_loop1].
  replace (2 <=? rem) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Hx d1 Hr) as [E R].
  destruct (xh_x2_sym (xhuf_of true ht) d1) as [c d] eqn:Ec. cbn [fst snd] in *. subst c.
  exists d. auto.
Qed.

Lemma loop1_exit (f: nat) (d1: xbit) (rem: Z) (acc: list Z) :
  rem < 2 -> xh_x2_loop1 (S f) (xhuf_of true ht) d1 rem acc = (acc, d1, rem).
Proof.
  intros Hrem. cbn [xh_x2_loop1]. replace (2 <=? rem) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* HUF_decodeLastSymbolX2's exact clause as the model's xh_x2_last *)
Lemma xlast_of (L pos1 lo1 v kk b2 nb: Z) (d1: xbit) :
  L = xh_x2_log ht -> v = xb_look_fast (xb_of s pos1 lo1) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  0 <= fst (hsym ht L v) < 256 -> 0 <= b2 < 256 -> 1 <= kk <= 2 -> 0 <= nb ->
  0 <= lo1 + 64 - pos1 -> lo1 + 64 - (pos1 - nb) <= Int.max_unsigned ->
  xb_rel s pos1 lo1 d1 ->
  fst (xh_x2_last (xhuf_of true ht) d1) = [fst (hsym ht L v)] /\
  xb_rel s (x2_last_pos pos1 lo1 kk nb) lo1 (snd (xh_x2_last (xhuf_of true ht) d1)).
Proof.
  intros HLx Hv Hc Hs1 Hb2 Hkk Hnb Hb0 Hb Hr.
  assert (HL: 1 <= L <= 64) by (subst L; unfold xh_x2_log; destruct (ht_log ht <=? 11); lia).
  assert (Hlook: xb_look_fast d1 L = v).
  { rewrite Hv, (xb_look_rel s pos1 lo1 d1 L Hr HL). symmetry.
    apply (xb_look_rel s pos1 lo1 _ L (xb_rel_of s pos1 lo1) HL). }
  unfold xh_x2_last, xh_cell. unfold xhuf_of. cbn [xh_log xh_cells]. rewrite <- HLx, Hlook, Hc.
  cbn [fst snd]. split.
  - f_equal. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small; lia.
  - pose proof Hr as (Hcr & Hbc & Hp). unfold x2_last_pos.
    destruct (Z.eq_dec kk 1) as [->|Hk1].
    + cbn. apply xb_skip_rel; [exact Hr | lia | lia].
    + replace (kk =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hk1).
      rewrite Hbc.
      destruct (lo1 + 64 - pos1 <? 64) eqn:E1.
      * apply Z.ltb_lt in E1. replace (pos1 <=? lo1) with false by (symmetry; apply Z.leb_gt; lia).
        assert (Hs: xb_bc (xb_skip d1 nb) = lo1 + 64 - (pos1 - nb)).
        { unfold xb_skip. cbn [xb_bc]. rewrite Hbc, Z.mod_small by rep_lia. lia. }
        rewrite Hs.
        destruct (64 <? lo1 + 64 - (pos1 - nb)) eqn:E2.
        -- apply Z.ltb_lt in E2. rewrite Z.max_l by lia.
           unfold xb_rel. cbn [xb_c xb_bc xb_ptr]. unfold xb_skip. cbn [xb_c xb_ptr].
           split; [exact Hcr|]. split; [lia|].
           destruct Hp as [Hp | [Hlt _]]; [left; exact Hp | lia].
        -- apply Z.ltb_ge in E2. rewrite Z.max_r by lia. apply xb_skip_rel; [exact Hr | lia | lia].
      * apply Z.ltb_ge in E1. replace (pos1 <=? lo1) with true by (symmetry; apply Z.leb_le; lia).
        exact Hr.
Qed.

End Exact.

(* the three phases of ExHuf.xh_x2_stream: the first loop (or one reload), the loops of the tail, the last
   symbol *)
Definition xPA (t: xhuf) (s: list Z) (d: xbit) (k: Z) : list Z * xbit * Z :=
  if 8 <=? k then
    if xh_log t <=? 11 then xh_x2_loopr (Z.to_nat k + 1) s t 5 (fun r => 9 <? r) d k nil
    else xh_x2_loopr (Z.to_nat k + 1) s t 4 (fun r => 7 <? r) d k nil
  else let '(_, d) := xb_reload s d in (nil, d, k).

Definition xPB1 (F: nat) (t: xhuf) (s: list Z) (d: xbit) (rem: Z) : list Z * xbit * Z :=
  let '(b1, d, rem) := xh_x2_loopr F s t 1 (fun r => 2 <=? r) d rem nil in
  let '(b2, d, rem) := xh_x2_loop1 F t d rem nil in (b1 ++ b2, d, rem).

Definition xPB (F: nat) (t: xhuf) (s: list Z) (d: xbit) (rem: Z) : list Z * xbit * Z :=
  if 2 <=? rem then xPB1 F t s d rem else (nil, d, rem).

Definition xPC (t: xhuf) (d: xbit) (rem: Z) : list Z * xbit :=
  if 0 <? rem then xh_x2_last t d else (nil, d).

Lemma xh_x2_stream_eq (t: xhuf) (s: list Z) (d: xbit) (k: Z) :
  xh_x2_stream t s d k =
  let '(a, d, rem) := xPA t s d k in
  let '(b, d, rem) := xPB (Z.to_nat k + 1) t s d rem in
  let '(c, d) := xPC t d rem in (a ++ b ++ c, d).
Proof. reflexivity. Qed.

(* the accumulator of xh_x2_loop1 *)
Lemma loop1_acc (f: nat) (t: xhuf) (d: xbit) (rem: Z) (acc: list Z) :
  xh_x2_loop1 f t d rem acc = let '(x, d', r) := xh_x2_loop1 f t d rem nil in (acc ++ x, d', r).
Proof.
  revert d rem acc. induction f as [|f IH]; intros d rem acc; cbn [xh_x2_loop1].
  - rewrite app_nil_r. reflexivity.
  - destruct (2 <=? rem); [|rewrite app_nil_r; reflexivity].
    destruct (xh_x2_sym t d) as [c d1].
    rewrite (IH d1 _ (acc ++ c)), (IH d1 _ (nil ++ c)).
    destruct (xh_x2_loop1 f t d1 (rem - Zlength c) nil) as [[x d'] r]. rewrite app_assoc. reflexivity.
Qed.

(* The invariants of the body: for any model container dx of the initial reader (pos, lo), the model's
   phases run as the C ran so far, from a container of the C's current reader. *)
Section Phases.
Variables (ht: huf_table) (s: list Z) (pos lo k: Z).

(* after the first loop: xPA emitted l and left a container of (pos1, lo1), k - j bytes to go *)
Definition XA (j pos1 lo1: Z) (l: list Z) : Prop :=
  forall dx, xb_rel s pos lo dx -> exists d1, xb_rel s pos1 lo1 d1 /\ xPA (xhuf_of true ht) s dx k = (l, d1, k - j).

(* in the first loop (K decodes while cnd): xPA is the rest of the loop from (pos1, lo1), with enough fuel *)
Definition XLA (K: nat) (cnd: Z -> bool) (j pos1 lo1: Z) (l: list Z) : Prop :=
  exists f, (Z.to_nat (k - j) < f)%nat /\
  forall dx, xb_rel s pos lo dx -> exists d1, xb_rel s pos1 lo1 d1 /\
    xPA (xhuf_of true ht) s dx k = xh_x2_loopr f s (xhuf_of true ht) K cnd d1 (k - j) l.

Lemma XLA_init (K: nat) (cnd: Z -> bool) : 0 <= k ->
  (forall dx, xPA (xhuf_of true ht) s dx k = xh_x2_loopr (Z.to_nat k + 1) s (xhuf_of true ht) K cnd dx k nil) ->
  XLA K cnd 0 pos lo [].
Proof.
  intros Hk H. exists (Z.to_nat k + 1)%nat. split; [lia|]. intros dx Hdx. exists dx. split; [exact Hdx|].
  rewrite Z.sub_0_r. apply H.
Qed.

Lemma XLA_step (K: nat) (cnd: Z -> bool) (j pos1 lo1: Z) (l: list Z) (pos2: Z) (w: list Z) (j2: Z) (l2: list Z) :
  XLA K cnd j pos1 lo1 l -> bit_inv s pos1 lo1 -> fst (bs_reload pos1 lo1) = BIT_unfinished -> cnd (k - j) = true ->
  xsteps ht s pos1 (snd (bs_reload pos1 lo1)) pos2 K w -> 1 <= Zlength w -> j + Zlength w <= k ->
  l2 = l ++ w -> j2 = j + Zlength w ->
  XLA K cnd j2 pos2 (snd (bs_reload pos1 lo1)) l2.
Proof.
  intros [f [Hf H]] Hi Hu Hc Hx Hw Hjk -> ->.
  destruct f as [|f]; [lia|].
  exists f. split; [lia|].
  intros dx Hdx. destruct (H dx Hdx) as [d1 [Hr1 E]].
  destruct (loopr_cont ht s f K cnd d1 (k - j) l w pos1 lo1 pos2 Hi Hr1 Hu Hc Hx) as [d2 [Hr2 E2]].
  exists d2. split; [exact Hr2|]. rewrite E, E2. replace (k - (j + Zlength w)) with (k - j - Zlength w) by lia.
  reflexivity.
Qed.

Lemma XLA_exit (K: nat) (cnd: Z -> bool) (j pos1 lo1: Z) (l: list Z) :
  XLA K cnd j pos1 lo1 l -> bit_inv s pos1 lo1 ->
  andb (fst (bs_reload pos1 lo1) =? BIT_unfinished) (cnd (k - j)) = false ->
  XA j pos1 (snd (bs_reload pos1 lo1)) l.
Proof.
  intros [f [Hf H]] Hi Hc dx Hdx. destruct f as [|f]; [lia|].
  destruct (H dx Hdx) as [d1 [Hr1 E]].
  destruct (loopr_exit ht s f K cnd d1 (k - j) l pos1 lo1 Hi Hr1 Hc) as [d2 [Hr2 E2]].
  exists d2. split; [exact Hr2|]. rewrite E, E2. reflexivity.
Qed.

(* fewer than 8 bytes: one reload *)
Lemma XA_short : k < 8 -> bit_inv s pos lo -> XA 0 pos (snd (bs_reload pos lo)) [].
Proof.
  intros Hk Hi dx Hdx. unfold xPA. replace (8 <=? k) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (xb_reload_rel s pos lo dx Hi Hdx) as [_ R].
  destruct (xb_reload s dx) as [st d]. exists d. split; [exact R|]. rewrite Z.sub_0_r. reflexivity.
Qed.

(* the tail loops, from the reader (pos1, lo1) after j bytes l: xPB emitted b and left (pos2, lo2) *)
Definition XB (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) : Prop :=
  exists b, l2 = l ++ b /\ forall d1, xb_rel s pos1 lo1 d1 -> exists d2, xb_rel s pos2 lo2 d2 /\
    xPB (Z.to_nat k + 1) (xhuf_of true ht) s d1 (k - j) = (b, d2, k - j2).

(* in the tail loop with reload *)
Definition XLB1 (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) : Prop :=
  exists f b, (Z.to_nat (k - j2) < f)%nat /\ l2 = l ++ b /\
  forall d1, xb_rel s pos1 lo1 d1 -> exists d2, xb_rel s pos2 lo2 d2 /\
    xPB1 (Z.to_nat k + 1) (xhuf_of true ht) s d1 (k - j) =
    (let '(b1, d, rem) := xh_x2_loopr f s (xhuf_of true ht) 1 (fun r => 2 <=? r) d2 (k - j2) b in
     let '(b2, d, rem) := xh_x2_loop1 (Z.to_nat k + 1) (xhuf_of true ht) d rem nil in (b1 ++ b2, d, rem)).

(* in the tail loop without reload *)
Definition XL1 (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) : Prop :=
  exists f b, (Z.to_nat (k - j2) < f)%nat /\ l2 = l ++ b /\
  forall d1, xb_rel s pos1 lo1 d1 -> exists d2, xb_rel s pos2 lo2 d2 /\
    xPB1 (Z.to_nat k + 1) (xhuf_of true ht) s d1 (k - j) = xh_x2_loop1 f (xhuf_of true ht) d2 (k - j2) b.

Lemma XLB1_init (j pos1 lo1: Z) (l: list Z) : 0 <= j <= k -> XLB1 j pos1 lo1 l j pos1 lo1 l.
Proof.
  intros Hj. exists (Z.to_nat k + 1)%nat, nil. split; [lia|]. split; [rewrite app_nil_r; reflexivity|].
  intros d1 Hr. exists d1. split; [exact Hr|]. reflexivity.
Qed.

Lemma XLB1_step (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) (pos3: Z) (w: list Z) :
  XLB1 j pos1 lo1 l j2 pos2 lo2 l2 -> bit_inv s pos2 lo2 -> fst (bs_reload pos2 lo2) = BIT_unfinished ->
  2 <= k - j2 -> xstep ht s pos2 (snd (bs_reload pos2 lo2)) pos3 w -> 1 <= Zlength w -> j2 + Zlength w <= k ->
  XLB1 j pos1 lo1 l (j2 + Zlength w) pos3 (snd (bs_reload pos2 lo2)) (l2 ++ w).
Proof.
  intros (f & b & Hf & -> & H) Hi Hu Hc Hx Hw Hjk.
  destruct f as [|f]; [lia|].
  exists f, (b ++ w). split; [lia|]. split; [rewrite app_assoc; reflexivity|].
  intros d1 Hr1. destruct (H d1 Hr1) as [d2 [Hr2 E]].
  assert (Hxs: xsteps ht s pos2 (snd (bs_reload pos2 lo2)) pos3 1 (w ++ [])).
  { eapply xsteps_S; [exact Hx | apply xsteps_0]. }
  rewrite app_nil_r in Hxs.
  destruct (loopr_cont ht s f 1 (fun r => 2 <=? r) d2 (k - j2) b w pos2 lo2 pos3 Hi Hr2 Hu
              ltac:(apply Z.leb_le; lia) Hxs) as [d3 [Hr3 E3]].
  exists d3. split; [exact Hr3|]. rewrite E, E3. replace (k - (j2 + Zlength w)) with (k - j2 - Zlength w) by lia.
  reflexivity.
Qed.

Lemma XLB1_exit (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) :
  XLB1 j pos1 lo1 l j2 pos2 lo2 l2 -> bit_inv s pos2 lo2 -> 0 <= j2 ->
  andb (fst (bs_reload pos2 lo2) =? BIT_unfinished) (2 <=? k - j2) = false ->
  XL1 j pos1 lo1 l j2 pos2 (snd (bs_reload pos2 lo2)) l2.
Proof.
  intros (f & b & Hf & -> & H) Hi Hj2 Hc.
  destruct f as [|f]; [lia|].
  exists (Z.to_nat k + 1)%nat, b. split; [lia|]. split; [reflexivity|].
  intros d1 Hr1. destruct (H d1 Hr1) as [d2 [Hr2 E]].
  destruct (loopr_exit ht s f 1 (fun r => 2 <=? r) d2 (k - j2) b pos2 lo2 Hi Hr2 Hc) as [d3 [Hr3 E3]].
  exists d3. split; [exact Hr3|]. rewrite E, E3. symmetry. apply loop1_acc.
Qed.

Lemma XL1_step (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) (pos3: Z) (w: list Z) :
  XL1 j pos1 lo1 l j2 pos2 lo2 l2 -> 2 <= k - j2 -> xstep ht s pos2 lo2 pos3 w -> 1 <= Zlength w ->
  j2 + Zlength w <= k ->
  XL1 j pos1 lo1 l (j2 + Zlength w) pos3 lo2 (l2 ++ w).
Proof.
  intros (f & b & Hf & -> & H) Hc Hx Hw Hjk.
  destruct f as [|f]; [lia|].
  exists f, (b ++ w). split; [lia|]. split; [rewrite app_assoc; reflexivity|].
  intros d1 Hr1. destruct (H d1 Hr1) as [d2 [Hr2 E]].
  destruct (loop1_cont ht s f d2 (k - j2) b w pos2 lo2 pos3 Hr2 Hc Hx) as [d3 [Hr3 E3]].
  exists d3. split; [exact Hr3|]. rewrite E, E3. replace (k - (j2 + Zlength w)) with (k - j2 - Zlength w) by lia.
  reflexivity.
Qed.

Lemma XL1_exit (j pos1 lo1: Z) (l: list Z) (j2 pos2 lo2: Z) (l2: list Z) :
  XL1 j pos1 lo1 l j2 pos2 lo2 l2 -> 2 <= k - j -> k - j2 < 2 -> XB j pos1 lo1 l j2 pos2 lo2 l2.
Proof.
  intros (f & b & Hf & -> & H) Hj Hc. exists b. split; [reflexivity|].
  intros d1 Hr1. destruct (H d1 Hr1) as [d2 [Hr2 E]].
  destruct f as [|f]; [lia|].
  exists d2. split; [exact Hr2|]. unfold xPB. replace (2 <=? k - j) with true by (symmetry; apply Z.leb_le; lia).
  rewrite E. apply loop1_exit. exact Hc.
Qed.

Lemma XB_skip (j pos1 lo1: Z) (l: list Z) : k - j < 2 -> XB j pos1 lo1 l j pos1 lo1 l.
Proof.
  intros Hc. exists nil. split; [rewrite app_nil_r; reflexivity|].
  intros d1 Hr1. exists d1. split; [exact Hr1|]. unfold xPB.
  replace (2 <=? k - j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

(* the last symbol, from (pos1, lo1) after j bytes l *)
Definition XC (j pos1 lo1: Z) (l: list Z) (pos2 lo2: Z) (l2: list Z) : Prop :=
  exists c, l2 = l ++ c /\ forall d1, xb_rel s pos1 lo1 d1 ->
    fst (xPC (xhuf_of true ht) d1 (k - j)) = c /\ xb_rel s pos2 lo2 (snd (xPC (xhuf_of true ht) d1 (k - j))).

(* the three phases together are ExHuf's run *)
Lemma stream_exact (jA posA loA: Z) (lA: list Z) (jB posB loB: Z) (lB: list Z) (posC loC: Z) (lC: list Z) :
  XA jA posA loA lA -> XB jA posA loA lA jB posB loB lB -> XC jB posB loB lB posC loC lC ->
  forall dx, xb_rel s pos lo dx ->
    fst (xh_x2_stream (xhuf_of true ht) s dx k) = lC /\
    xb_rel s posC loC (snd (xh_x2_stream (xhuf_of true ht) s dx k)).
Proof.
  intros HA (b & -> & HB) (c & -> & HC) dx Hdx.
  destruct (HA dx Hdx) as [d1 [Hr1 E1]].
  destruct (HB d1 Hr1) as [d2 [Hr2 E2]].
  destruct (HC d2 Hr2) as [E3 Hr3].
  rewrite xh_x2_stream_eq, E1, E2.
  destruct (xPC (xhuf_of true ht) d2 (k - jB)) as [c' d3]. cbn [fst snd] in *. subst c'.
  rewrite app_assoc. auto.
Qed.

End Phases.

(* ---------- VST helpers ---------- *)

Lemma sub_pp_uchar (ob: val) (a k: Z) :
  isptr ob -> 0 <= k <= Ptrofs.max_unsigned ->
  sem_sub_pp tuchar (offset_val (a + k) ob) (offset_val a ob) = Some (Vlong (Int64.repr k)).
Proof.
  destruct ob; try contradiction; intros _ Hk. unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  replace (Ptrofs.sub (Ptrofs.add i (Ptrofs.repr (a + k))) (Ptrofs.add i (Ptrofs.repr a))) with (Ptrofs.repr k).
  2: { rewrite !(Ptrofs.add_commut i), Ptrofs.sub_shifted, ptrofs_sub_repr. f_equal; lia. }
  change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs, Ptrofs.to_int64. simpl. rewrite Ptrofs.unsigned_repr by lia. reflexivity.
Qed.

Lemma sub_pp_gen (ob: val) (x y: Z) :
  isptr ob -> 0 <= x - y <= Ptrofs.max_unsigned ->
  sem_sub_pp tuchar (offset_val x ob) (offset_val y ob) = Some (Vlong (Int64.repr (x - y))).
Proof. intros. replace x with (y + (x - y)) at 1 by lia. apply sub_pp_uchar; auto. Qed.

Lemma ltu_tt (x: Z) (y: int64) :
  0 <= x <= Int64.max_unsigned ->
  typed_true tint (bool2val (negb (Int64.ltu (Int64.repr x) y))) -> Int64.unsigned y <= x.
Proof.
  intros Hx H. unfold Int64.ltu in H. rewrite Int64.unsigned_repr in H by lia.
  destruct (zlt x (Int64.unsigned y)); [|lia]. compute in H. discriminate.
Qed.

Lemma ltu_tf (x: Z) (y: int64) :
  0 <= x <= Int64.max_unsigned ->
  typed_false tint (bool2val (negb (Int64.ltu (Int64.repr x) y))) -> x < Int64.unsigned y.
Proof.
  intros Hx H. unfold Int64.ltu in H. rewrite Int64.unsigned_repr in H by lia.
  destruct (zlt x (Int64.unsigned y)); [lia|]. compute in H. discriminate.
Qed.

Lemma sameblock_off (ob: val) (x y: Z) : isptr ob -> is_true (sameblock (offset_val x ob) (offset_val y ob)).
Proof. destruct ob; try contradiction; intros _. simpl. destruct (peq b b); [reflexivity|congruence]. Qed.

Lemma sub_pl_gen (ob: val) (x n: Z) :
  isptr ob -> 0 <= n <= Int64.max_unsigned ->
  sem_sub_pl tuchar (offset_val x ob) (Vlong (Int64.repr n)) = Some (offset_val (x - n) ob).
Proof.
  destruct ob; try contradiction; intros _ Hn. unfold sem_sub_pl. simpl. f_equal. f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite ptrofs_add_repr, ptrofs_mul_repr, ptrofs_sub_repr, ptrofs_add_repr.
  f_equal. lia.
Qed.

Lemma x_wvp_off (sh: share) (n: Z) (c: list val) (p: val) (i: Z) :
  readable_share sh -> 0 <= i <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite data_at__memory_block. Intros. simpl sizeof.
  apply memory_block_weak_valid_pointer; try lia. apply readable_nonidentity; auto.
Qed.

Lemma x_test_order (R: mpred) (a b: Z) (p: val) : isptr p ->
  (R |-- weak_valid_pointer (offset_val a p)) -> (R |-- weak_valid_pointer (offset_val b p)) ->
  R |-- denote_tc_test_order (offset_val a p) (offset_val b p).
Proof.
  intros. destruct p; try contradiction.
  apply derives_trans with (weak_valid_pointer (offset_val a (Vptr b0 i)) && weak_valid_pointer (offset_val b (Vptr b0 i))).
  { apply andp_right; auto. }
  Transparent denote_tc_test_order. unfold denote_tc_test_order. Opaque denote_tc_test_order.
  simpl. unfold test_order_ptrs. simpl. destruct (peq b0 b0); [|contradiction]. simpl. apply derives_refl.
Qed.

Ltac wvp_find := first [ eapply x_wvp_off; [eassumption | lia | lia]
  | apply sepcon_weak_valid_pointer2; wvp_find | apply sepcon_weak_valid_pointer1; wvp_find ].

Lemma x_ofs (b: block) (i: ptrofs) (n a: Z) : field_compatible (tarray tuchar n) [] (Vptr b i) -> 0 <= a <= n ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr a)) = Ptrofs.unsigned i + a.
Proof.
  intros. destruct H as [_ [_ [Hs _]]]. simpl in Hs. rewrite Z.max_r in Hs by lia.
  pose proof (Ptrofs.unsigned_range i).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr a) by rep_lia. apply Ptrofs.unsigned_repr. rep_lia.
Qed.

Lemma x_cmp (p: val) (n a c: Z) : field_compatible (tarray tuchar n) [] p -> 0 <= a <= n -> 0 <= c <= n ->
  sem_cmp_pp Cle (offset_val a p) (offset_val c p) = Some (bool2val (a <=? c)) /\
  sem_cmp_pp Clt (offset_val a p) (offset_val c p) = Some (bool2val (a <? c)).
Proof.
  intros. destruct p; try (destruct H; contradiction).
  unfold sem_cmp_pp. simpl. destruct (eq_block b b); [|congruence]. simpl.
  unfold Ptrofs.ltu. rewrite !(x_ofs b i n) by auto.
  split; f_equal; f_equal.
  - destruct (zlt _ _), (a <=? c) eqn:E; simpl; auto; try (apply Z.leb_le in E; lia); try (apply Z.leb_gt in E; lia).
  - destruct (zlt _ _), (a <? c) eqn:E; simpl; auto; try (apply Z.ltb_lt in E; lia); try (apply Z.ltb_ge in E; lia).
Qed.

(* do { c } while (0) *)
Lemma semax_dw0 {cs: compspecs} {Espec: OracleKind} (Delta: tycontext) (P Q: environ -> mpred) (c: statement) :
  semax Delta P c (normal_ret_assert Q) -> semax Delta P (Sloop c Sbreak) (normal_ret_assert Q).
Proof.
  intros H. apply semax_loop with (Q' := Q).
  - eapply semax_post; [.. | exact H]; simpl; intros;
      first [apply andp_left2; apply derives_refl | apply andp_left2; apply prop_left; intros []].
  - eapply semax_pre; [| apply semax_break]. simpl. intros x. apply andp_left2. apply derives_refl.
Qed.

(* the three parts of the body after pStart = p: loop 1 (or one reload), loops 2-3, the last symbol *)
Definition segA : statement :=
  match fn_body f_HUF_decodeStreamX2 with Ssequence _ (Ssequence A _) => A | _ => Sskip end.
Definition segB : statement :=
  match fn_body f_HUF_decodeStreamX2 with Ssequence _ (Ssequence _ (Ssequence B _)) => B | _ => Sskip end.

Section Body.
Context {Espec: OracleKind}.
Variables (sh: share) (bD: val) (gv: globals) (s: list Z) (start: val) (pos lo: Z)
  (shs: share) (bp: val) (buf: list Z) (off: Z) (sht: share) (dt: val) (ht: huf_table) (L: Z)
  (c2: list (val * (val * val))) (sho: share) (ob: val) (oc: list val) (a k: Z).
Hypotheses (Hf: hsym_facts) (SH: writable_share sh) (SH0: readable_share shs)
  (Hsrc: bit_src_ok s start bp buf off) (SH1: readable_share sht) (Htab: x2_tab_ok ht L c2)
  (SH2: writable_share sho) (Hoc: 1 <= Zlength oc) (Ha: 0 <= a) (Hk: 0 <= k) (Hak: a + k <= Zlength oc)
  (Hmax: lo + 64 - pos + 12 * k <= Int.max_unsigned) (Hs: bytes_ok s)
  (HLx: L = xh_x2_log ht) (HcX: c2 = map x2v (xh_cells_x2 ht L)).

Definition cur (l: list Z) (g: list val) : list val :=
  sublist 0 a oc ++ zbytes l ++ g ++ sublist (a + k) (Zlength oc) oc.

Definition st (j pos1 lo1: Z) (l: list Z) (g: list val) (Q: Prop) : environ -> mpred :=
  PROP (minv ht s pos lo k j pos1 lo1 l; Zlength g = k - j; Q)
  LOCAL (temp _pStart (offset_val a ob); gvars gv; temp _p (offset_val (a + j) ob); temp _bitDPtr bD;
         temp _pEnd (offset_val (a + k) ob); temp _dt dt; temp _dtLog (Vint (Int.repr L)))
  SEP (BIT_DStream_rep sh gv s start pos1 lo1 bD; bit_src shs bp buf;
       data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
       data_at sho (tarray tuchar (Zlength oc)) (cur l g) ob).

Lemma cur_len (l: list Z) (g: list val) (j: Z) :
  Zlength l = j -> Zlength g = k - j -> 0 <= j <= k -> Zlength (cur l g) = Zlength oc.
Proof. intros. unfold cur. list_solve. Qed.

Lemma cur_step (l: list Z) (g: list val) (j kk x y: Z) :
  Zlength l = j -> Zlength g = k - j -> 0 <= j -> j + 2 <= k -> 1 <= kk <= 2 ->
  sublist 0 (a + j) (cur l g) ++ zbytes [x; y] ++ sublist (a + j + 2) (Zlength oc) (cur l g) =
  cur (l ++ sublist 0 kk [x; y]) (zbytes (sublist kk 2 [x; y]) ++ sublist 2 (k - j) g).
Proof.
  intros. unfold cur. assert (kk = 1 \/ kk = 2) as [-> | ->] by lia; simpl; list_solve.
Qed.

Definition tX2 : type :=
  Tfunction ((tptr tvoid) :: (tptr (Tstruct ___gp_BIT_DStream_t noattr)) ::
             (tptr (Tstruct ___gp_HUF_DEltX2 noattr)) :: tuint :: nil) tuint cc_default.

Definition dcall (t: ident) : statement :=
  Ssequence
    (Scall (Some t) (Evar _HUF_decodeSymbolX2 tX2)
       ((Etempvar _p (tptr tuchar)) :: (Etempvar _bitDPtr (tptr (Tstruct ___gp_BIT_DStream_t noattr))) ::
        (Etempvar _dt (tptr (Tstruct ___gp_HUF_DEltX2 noattr))) :: (Etempvar _dtLog tuint) :: nil))
    (Sset _p (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar t tuint) (tptr tuchar))).

Definition DeltaX2 : tycontext := func_tycontext f_HUF_decodeStreamX2 Vprog G_stream2 nil.

(* after one decode: kk bytes w, the reader moved from (pos1, lo1) to (pos2, lo1) as the model's decode *)
Definition dpost (j pos1 lo1: Z) (l: list Z) (e: Z) : environ -> mpred :=
  EX kk: Z, EX pos2: Z, EX w: list Z, EX g2: list val,
    st (j + kk) pos2 lo1 (l ++ w) g2
      (1 <= kk <= 2 /\ (xW ht s pos lo k -> lo1 + e <= pos2 \/ lo1 = 0) /\ xstep ht s pos1 lo1 pos2 w).

(* the exact clause of HUF_decodeSymbolX2 as one model decode *)
Lemma xstep_call (pos1 lo1 v kk b2 nb: Z) :
  0 <= v < 2 ^ L -> x2_step ht L v kk b2 nb ->
  (v = xb_look_fast (xb_of s pos1 lo1) L /\
   nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk))%type ->
  1 <= kk <= 2 -> 0 <= lo1 + 64 - (pos1 - nb) <= Int.max_unsigned ->
  xstep ht s pos1 lo1 (pos1 - nb) (sublist 0 kk [fst (hsym ht L v); b2]).
Proof.
  intros Hv Hst [Hx1 Hx2] Hkk Hb.
  destruct (tab_facts ht L c2 Htab) as (Hok & HL & _).
  pose proof (hsym_range ht L v Hok ltac:(lia) Hv) as [Hs1 _].
  destruct Hst as (Hb2 & Hnb & _).
  apply (xstep_of ht s L pos1 lo1 v kk b2 nb HLx Hx1 Hx2); lia.
Qed.

Ltac dstep_tac :=
  unfold dpost, st, dcall, tX2, DeltaX2; Intros;
  abbreviate (func_tycontext f_HUF_decodeStreamX2 Vprog G_stream2 nil) as Delta;
  match goal with Hm0: minv _ _ _ _ _ ?j ?pos1 ?lo1 ?l, Hg: Zlength ?g = _ - _ |- _ =>
  let Hinv := fresh "Hinv" in
  assert_PROP (bit_inv s pos1 lo1) as Hinv by (sep_apply bit_rep_inv; entailer!);
  let Hb0 := fresh "Hb0" in
  assert (Hb0: pos1 <= lo1 + 64) by (destruct Hinv as (_ & _ & _ & _ & _ & ? & _); lia);
  let Hm := fresh "Hm" in pose proof Hm0 as Hm;
  let Hj := fresh "Hj" in let Hl := fresh "Hl" in let Hsafe := fresh "Hsafe" in
  destruct Hm0 as (Hj & Hl & _ & Hsafe & _);
  let HL := fresh "HL" in
  match goal with Htab: x2_tab_ok ?ht ?L ?c2 |- _ => pose proof (tab_facts ht L c2 Htab) as (_ & _ & HL) end;
  forward_call (sh, bD, gv, s, start, pos1, lo1, sht, dt, ht, L, c2, sho, ob, cur l g, a + j, false);
  [ unfold BIT_DStream_rep_g; rewrite (cur_len l g j) by lia; cancel | rewrite (cur_len l g j) by lia; lia | ];
  let vret := fresh "vret" in Intros vret;
  let v := fresh "v" in let kk := fresh "kk" in let b2 := fresh "b2" in let nb := fresh "nb" in
  destruct vret as [[[v kk] b2] nb]; simpl fst in *; simpl snd in *; unfold BIT_DStream_rep_g;
  rewrite (cur_len l g j) by lia;
  forward;
  match goal with Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _, Hst: x2_step _ _ _ _ _ _,
    Hxa1: v = xb_look_fast _ _, Hxa2: nth (Z.to_nat v) _ _ = _,
    Hjk: j + 2 <= k, He: 0 <= ?e, Hres: xW _ _ _ _ _ -> _ |- _ =>
  let Hkk := fresh "Hkk" in let Hnb := fresh "Hnb" in let Hm' := fresh "Hm'" in let Hres' := fresh "Hres'" in
  destruct (minv_step ht s L c2 pos lo k Hf Htab Hs j pos1 lo1 e v kk b2 nb l Hm Hjk He Hres Hv Hx Hst)
    as (Hkk & Hnb & Hm' & Hres');
  let Hxs := fresh "Hxs" in
  assert (Hxs: xstep ht s pos1 lo1 (pos1 - nb) (sublist 0 kk [fst (hsym ht L v); b2]))
    by (apply (xstep_call pos1 lo1 v kk b2 nb Hv Hst (conj Hxa1 Hxa2)); lia);
  clear Hxa1 Hxa2;
  Exists kk (pos1 - nb) (sublist 0 kk [fst (hsym ht L v); b2])
    (zbytes (sublist kk 2 [fst (hsym ht L v); b2]) ++ sublist 2 (k - j) g);
  rewrite (cur_step l g j kk) by lia;
  entailer!; split; [list_solve | f_equal; lia]
  end end.

Lemma dstep_2 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'2)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_3 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'3)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_4 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'4)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_5 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'5)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_6 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'6)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_8 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'8)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_10 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'10)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_13 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'13)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_15 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'15)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_19 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'19)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep_20 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall _t'20)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof. intros Hjk He Hres. dstep_tac. Qed.

Lemma dstep (t: ident) (Ht: In t [_t'2; _t'3; _t'4; _t'5; _t'6; _t'8; _t'10; _t'13; _t'15; _t'19; _t'20])
    (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (dcall t)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof.
  simpl in Ht. repeat destruct Ht as [<- | Ht];
    [ apply dstep_2 | apply dstep_3 | apply dstep_4 | apply dstep_5 | apply dstep_6 | apply dstep_8
    | apply dstep_10 | apply dstep_13 | apply dstep_15 | apply dstep_19 | apply dstep_20 | contradiction ].
Qed.

Lemma bs_reload_fst_range (p q: Z) : 0 <= fst (bs_reload p q) <= 3.
Proof.
  unfold bs_reload, BIT_overflow, BIT_unfinished, BIT_endOfBuffer, BIT_completed.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl; lia.
Qed.

Lemma int_eq_small (x: Z) : 0 <= x <= 3 -> Int.eq (Int.repr x) (Int.repr 0) = (x =? 0).
Proof.
  intros Hx. destruct (Z.eq_dec x 0) as [->|Hn]; [reflexivity|].
  rewrite Int.eq_false; [symmetry; apply Z.eqb_neq; auto|].
  intros C. apply (f_equal Int.unsigned) in C. rewrite !Int.unsigned_repr in C by rep_lia. lia.
Qed.

Lemma ltu64_repr (n x: Z) :
  0 <= n <= Int64.max_unsigned -> 0 <= x <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr n) (Int64.repr x) = (n <? x).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt n x); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma and_b2z_tt (b1 b2: bool) :
  typed_true tint (Vint (Int.and (Int.repr (Z.b2z b1)) (Int.repr (Z.b2z b2)))) -> b1 = true /\ b2 = true.
Proof. destruct b1, b2; compute; intros H; first [split; reflexivity | discriminate H]. Qed.

Lemma and_b2z_tf (b1 b2: bool) :
  typed_false tint (Vint (Int.and (Int.repr (Z.b2z b1)) (Int.repr (Z.b2z b2)))) -> b1 = false \/ b2 = false.
Proof. destruct b1, b2; compute; intros H; first [left; reflexivity | right; reflexivity | discriminate H]. Qed.

(* one do { decode } while (0), then the rest c *)
Lemma dstep_seq (t: ident) (Ht: In t [_t'2; _t'3; _t'4; _t'5; _t'6; _t'8; _t'10; _t'13; _t'15; _t'19; _t'20])
    (e j pos1 lo1: Z) (l: list Z) (g: list val) (c: statement) (R: ret_assert) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  (forall kk pos2 w g2, 1 <= kk <= 2 -> (xW ht s pos lo k -> lo1 + e <= pos2 \/ lo1 = 0) ->
     xstep ht s pos1 lo1 pos2 w ->
     semax DeltaX2 (st (j + kk) pos2 lo1 (l ++ w) g2 True) c R) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (Ssequence (Sloop (dcall t) Sbreak) c) R.
Proof.
  intros Hjk He Hres Hc. eapply semax_seq'.
  { apply semax_dw0. apply dstep; auto; lia. }
  unfold dpost. Intros kk pos2 w g2. unfold st at 1. Intros.
  match goal with H: xW _ _ _ _ _ -> _, Hx: xstep _ _ _ _ _ _ |- _ =>
    eapply semax_pre; [| apply (Hc kk pos2 w g2 ltac:(lia) H Hx)] end.
  unfold st. entailer!.
Qed.

Lemma semax_normal_post {cs: compspecs} {Esp: OracleKind} (Delta: tycontext) (P Q: environ -> mpred)
    (c: statement) (R: ret_assert) :
  semax Delta P c (normal_ret_assert Q) -> ENTAIL Delta, Q |-- RA_normal R -> semax Delta P c R.
Proof.
  intros H HQ. eapply semax_post; [.. | exact H]; simpl; intros;
    first [exact (HQ x) | apply andp_left2; apply prop_left; intros []].
Qed.


Lemma dseq (d c: statement) (R: ret_assert) (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  semax DeltaX2 (st j pos1 lo1 l g True) d (normal_ret_assert (dpost j pos1 lo1 l e)) ->
  (forall kk pos2 w g2, 1 <= kk <= 2 -> (xW ht s pos lo k -> lo1 + e <= pos2 \/ lo1 = 0) ->
     xstep ht s pos1 lo1 pos2 w ->
     semax DeltaX2 (st (j + kk) pos2 lo1 (l ++ w) g2 True) c R) ->
  semax DeltaX2 (st j pos1 lo1 l g True) (Ssequence d c) R.
Proof.
  intros Hd Hc. eapply semax_seq'; [exact Hd|]. unfold dpost.
  Intros kk pos2 w g2. unfold st at 1. Intros.
  match goal with H: xW _ _ _ _ _ -> _, Hx: xstep _ _ _ _ _ _ |- _ =>
    eapply semax_pre; [| apply (Hc kk pos2 w g2 ltac:(lia) H Hx)] end.
  unfold st. entailer!.
Qed.

Definition mcall (t: ident) : statement := Scall (Some t) (Evar _MEM_64bits (Tfunction nil tuint cc_default)) nil.

Ltac dm_tac tm t :=
  intros Hjk He Hres; apply semax_dw0; unfold mcall, st, DeltaX2; Intros;
  abbreviate (func_tycontext f_HUF_decodeStreamX2 Vprog G_stream2 nil) as Delta;
  forward_call tt.

Lemma dm8 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True)
    (Sloop (Ssequence (mcall _t'9) (Sifthenelse (Etempvar _t'9 tuint) (dcall _t'8) Sskip)) Sbreak)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof.
  dm_tac _t'9 _t'8.
  forward_if (dpost j pos1 lo1 l e).
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dstep _t'8 ltac:(simpl; tauto) e j pos1 lo1 l g Hjk He Hres)].
      unfold st. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma dm13 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True)
    (Sloop (Ssequence (mcall _t'14) (Sifthenelse (Etempvar _t'14 tuint) (dcall _t'13) Sskip)) Sbreak)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof.
  dm_tac _t'14 _t'13.
  forward_if (dpost j pos1 lo1 l e).
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dstep _t'13 ltac:(simpl; tauto) e j pos1 lo1 l g Hjk He Hres)].
      unfold st. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Lemma dm10 (e j pos1 lo1: Z) (l: list Z) (g: list val) :
  j + 2 <= k -> 0 <= e -> (xW ht s pos lo k -> lo1 + L + e <= pos1 \/ lo1 = 0) ->
  semax DeltaX2 (st j pos1 lo1 l g True)
    (Sloop (Ssequence
       (Ssequence (mcall _t'11)
          (Sifthenelse (Etempvar _t'11 tuint) (Sset _t'12 (Econst_int (Int.repr 1) tint))
             (Sset _t'12 (Ecast (Ebinop Ole (Econst_int (Int.repr 12) tint) (Econst_int (Int.repr 12) tint) tint) tbool))))
       (Sifthenelse (Etempvar _t'12 tint) (dcall _t'10) Sskip)) Sbreak)
    (normal_ret_assert (dpost j pos1 lo1 l e)).
Proof.
  dm_tac _t'11 _t'10.
  forward_if (temp _t'12 (Vint Int.one)).
  { forward. entailer!. }
  { exfalso. discriminate. }
  forward_if (dpost j pos1 lo1 l e).
  - eapply semax_normal_post.
    + eapply semax_pre; [| apply (dstep _t'10 ltac:(simpl; tauto) e j pos1 lo1 l g Hjk He Hres)].
      unfold st. entailer!.
    + simpl. intros rho. apply andp_left2. apply derives_refl.
  - exfalso. discriminate.
Qed.

Ltac res_tac H := let HW := fresh "HW" in intros HW; destruct (H HW); [left; lia | right; assumption].
Ltac in_tac := simpl; tauto.

Lemma sub_pi_gen (p: val) (x n: Z) :
  isptr p -> Int.min_signed <= n <= Int.max_signed ->
  sem_sub_pi tuchar Signed (offset_val x p) (Vint (Int.repr n)) = Some (offset_val (x - n) p).
Proof.
  destruct p; try contradiction; intros _ Hn. unfold sem_sub_pi. simpl. f_equal. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by lia.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite ptrofs_add_repr, ptrofs_mul_repr, ptrofs_sub_repr, ptrofs_add_repr.
  f_equal. lia.
Qed.

Lemma bool2val_tt (b: bool) : typed_true tint (bool2val b) -> b = true.
Proof. destruct b; compute; intros H; [reflexivity | discriminate H]. Qed.

Lemma bool2val_tf (b: bool) : typed_false tint (bool2val b) -> b = false.
Proof. destruct b; compute; intros H; [discriminate H | reflexivity]. Qed.

Lemma tc_order_out (R1: mpred) (l: list Z) (g: list val) (x y: Z) :
  0 <= x <= Zlength oc -> 0 <= y <= Zlength oc -> isptr ob ->
  R1 * data_at sho (tarray tuchar (Zlength oc)) (cur l g) ob |--
  denote_tc_test_order (offset_val x ob) (offset_val y ob).
Proof.
  intros. apply x_test_order; auto; apply sepcon_weak_valid_pointer2; apply x_wvp_off; auto; lia.
Qed.

(* the first loop of xh_x2_stream, by the table's log *)
Lemma xPA_5 : 8 <= k -> L <= 11 -> forall dx,
  xPA (xhuf_of true ht) s dx k = xh_x2_loopr (Z.to_nat k + 1) s (xhuf_of true ht) 5 (fun r => 9 <? r) dx k nil.
Proof.
  intros H8 HL dx. unfold xPA. replace (8 <=? k) with true by (symmetry; apply Z.leb_le; lia).
  replace (xh_log (xhuf_of true ht) <=? 11) with true by (symmetry; apply Z.leb_le; simpl; lia). reflexivity.
Qed.

Lemma xPA_4 : 8 <= k -> 11 < L -> forall dx,
  xPA (xhuf_of true ht) s dx k = xh_x2_loopr (Z.to_nat k + 1) s (xhuf_of true ht) 4 (fun r => 7 <? r) dx k nil.
Proof.
  intros H8 HL dx. unfold xPA. replace (8 <=? k) with true by (symmetry; apply Z.leb_le; lia).
  replace (xh_log (xhuf_of true ht) <=? 11) with false by (symmetry; apply Z.leb_gt; simpl; lia). reflexivity.
Qed.

Lemma segA_ok (g: list val) :
  semax DeltaX2 (st 0 pos lo [] g True) segA
    (normal_ret_assert (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z, EX g1: list val,
       st j pos1 lo1 l g1 ((xW ht s pos lo k -> lo1 = 0 \/ lo1 + 57 <= pos1) /\ XA ht s pos lo k j pos1 lo1 l))).
Proof.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv [segA f_HUF_decodeStreamX2 fn_body] in c in change c with c' end.
  unfold st, DeltaX2. Intros.
  abbreviate (func_tycontext f_HUF_decodeStreamX2 Vprog G_stream2 nil) as Delta.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as Hfc by entailer!.
  assert_PROP (bit_inv s pos lo) as Hinv by (sep_apply bit_rep_inv; entailer!).
  assert (Hob: isptr ob) by (destruct Hfc; auto).
  assert (Hmo: Zlength oc <= Ptrofs.max_unsigned).
  { destruct Hfc as (_ & _ & Hsz & _). destruct ob; try contradiction. simpl in Hsz.
    rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.max_unsigned. lia. }
  forward_if.
  { entailer!. apply sameblock_off; auto. }
  { rewrite sub_pp_gen in H1 by (auto; lia). simpl in H1. apply ltu_tt in H1; [|rep_lia].
    change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H1.
    pose proof (tab_facts ht L c2 Htab) as (_ & _ & HL).
    destruct (Z_le_gt_dec L 11) as [HL11 | HL12].
    - forward_if (temp _t'16 (Vint Int.one)).
      { forward_call tt. forward. entailer!. }
      { exfalso. lia. }
      forward_if; [| exfalso; discriminate H2].
      forward_loop (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z, EX g1: list val,
                    st j pos1 lo1 l g1 (XLA ht s pos lo k 5 (fun r => 9 <? r) j pos1 lo1 l))
        break: (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z, EX g1: list val,
                st j pos1 lo1 l g1 ((xW ht s pos lo k -> lo1 = 0 \/ lo1 + 57 <= pos1) /\ XA ht s pos lo k j pos1 lo1 l)).
      { assert (HX0: XLA ht s pos lo k 5 (fun r => 9 <? r) 0 pos lo []) by (apply XLA_init; [lia | apply xPA_5; lia]).
        Exists 0 pos lo (@nil Z) g. unfold st. entailer!. }
      { clear H. Intros j pos1 lo1 l g1. unfold st. Intros.
        match goal with H': XLA _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXL end.
        assert_PROP (bit_inv s pos1 lo1) as Hinv1 by (sep_apply bit_rep_inv; entailer!).
        forward_call (sh, bD, gv, s, start, pos1, lo1, shs, bp, buf, off).
        destruct (minv_reload ht s pos lo k j pos1 lo1 l H Hinv1) as [Hm Hr].
        assert (Hj: 0 <= j <= k) by (destruct H; lia).
        forward_if.
        { entailer!. apply sameblock_off; auto. }
        { match goal with H': typed_true _ _ |- _ => rename H' into H4 end.
          rewrite sub_pp_gen in H4 by (auto; lia). simpl in H4.
          apply and_b2z_tt in H4. destruct H4 as [Hc1 Hc2].
          rewrite int_eq_small in Hc1 by apply bs_reload_fst_range. apply Z.eqb_eq in Hc1.
          rewrite Int.signed_repr in Hc2 by rep_lia. rewrite ltu64_repr in Hc2 by rep_lia. apply Z.ltb_lt in Hc2.
          assert (Hres0: xW ht s pos lo k -> snd (bs_reload pos1 lo1) + L + (4 * L)%Z <= pos1 \/ snd (bs_reload pos1 lo1) = 0).
          { intros HW. left. destruct (Hr HW) as [Hu _]. specialize (Hu Hc1). lia. }
          eapply semax_pre with (P' := st j pos1 (snd (bs_reload pos1 lo1)) l g1 True); [unfold st; entailer! |].
          unfold MORE_COMMANDS, abbreviate. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'2) (e := (4 * L)%Z); [in_tac | lia | lia | exact Hres0 |].
          intros kk1 pos2 w1 g2 Hk1 Hr1 Hx1. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'3) (e := (3 * L)%Z); [in_tac | lia | lia | res_tac Hr1 |].
          intros kk2 pos3 w2 g3 Hk2 Hr2 Hx2. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'4) (e := (2 * L)%Z); [in_tac | lia | lia | res_tac Hr2 |].
          intros kk3 pos4 w3 g4 Hk3 Hr3 Hx3. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'5) (e := (1 * L)%Z); [in_tac | lia | lia | res_tac Hr3 |].
          intros kk4 pos5 w4 g5 Hk4 Hr4 Hx4. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'6) (e := 0); [in_tac | lia | lia | res_tac Hr4 |].
          intros kk5 pos6 w5 g6 Hk5 Hr5 Hx5. unfold st. Intros.
          forward.
          match goal with H': minv _ _ _ _ _ _ pos6 _ _ |- _ => rename H' into Hm6 end.
          assert (Hlw: Zlength (w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ []) = kk1 + kk2 + kk3 + kk4 + kk5).
          { destruct Hm6 as (_ & Hl6 & _). destruct H as (_ & Hl & _). rewrite !Zlength_app in Hl6.
            rewrite !Zlength_app, Zlength_nil. lia. }
          assert (HX: XLA ht s pos lo k 5 (fun r => 9 <? r) (j + kk1 + kk2 + kk3 + kk4 + kk5) pos6
                        (snd (bs_reload pos1 lo1)) (((((l ++ w1) ++ w2) ++ w3) ++ w4) ++ w5)).
          { eapply (XLA_step ht s pos lo k 5 (fun r => 9 <? r) j pos1 lo1 l pos6 (w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ []));
              [exact HXL | exact Hinv1 | exact Hc1 | apply Z.ltb_lt; lia | | lia | destruct Hm6 as (? & _); lia
              | rewrite app_nil_r, <- !app_assoc; reflexivity | lia].
            repeat (eapply xsteps_S; [eassumption|]). apply xsteps_0. }
          Exists (j + kk1 + kk2 + kk3 + kk4 + kk5) pos6 (snd (bs_reload pos1 lo1))
            (((((l ++ w1) ++ w2) ++ w3) ++ w4) ++ w5) g6. unfold st. entailer!. }
        { match goal with H': typed_false _ _ |- _ => rename H' into H4 end.
          rewrite sub_pp_gen in H4 by (auto; lia). simpl in H4. apply and_b2z_tf in H4.
          rewrite int_eq_small in H4 by apply bs_reload_fst_range.
          rewrite Int.signed_repr in H4 by rep_lia. rewrite ltu64_repr in H4 by rep_lia.
          assert (HXA: XA ht s pos lo k j pos1 (snd (bs_reload pos1 lo1)) l).
          { apply (XLA_exit ht s pos lo k 5 (fun r => 9 <? r) j pos1 lo1 l HXL Hinv1).
            unfold BIT_unfinished. apply andb_false_iff.
            destruct H4 as [H4|H4]; [left; exact H4 | right; apply Z.ltb_ge; apply Z.ltb_ge in H4; lia]. }
          forward. Exists j pos1 (snd (bs_reload pos1 lo1)) l g1. unfold st. entailer!.
          try intros HW. match goal with HW: xW _ _ _ _ _ |- _ => destruct (Hr HW) as [Hu Hn] end.
          destruct (Z.eq_dec (fst (bs_reload pos1 lo1)) BIT_unfinished) as [E|E]; [right; auto | left; auto]. } }
      apply andp_left2. unfold st. apply derives_refl.
    - forward_if (temp _t'16 (Vint Int.zero)).
      { exfalso. lia. }
      { forward. entailer!. }
      forward_if; [exfalso; apply H2; reflexivity |].
      forward_loop (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z, EX g1: list val,
                    st j pos1 lo1 l g1 (XLA ht s pos lo k 4 (fun r => 7 <? r) j pos1 lo1 l))
        break: (EX j: Z, EX pos1: Z, EX lo1: Z, EX l: list Z, EX g1: list val,
                st j pos1 lo1 l g1 ((xW ht s pos lo k -> lo1 = 0 \/ lo1 + 57 <= pos1) /\ XA ht s pos lo k j pos1 lo1 l)).
      { assert (HX0: XLA ht s pos lo k 4 (fun r => 7 <? r) 0 pos lo []) by (apply XLA_init; [lia | apply xPA_4; lia]).
        Exists 0 pos lo (@nil Z) g. unfold st. entailer!. }
      { clear H. Intros j pos1 lo1 l g1. unfold st. Intros.
        match goal with H': XLA _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXL end.
        assert_PROP (bit_inv s pos1 lo1) as Hinv1 by (sep_apply bit_rep_inv; entailer!).
        forward_call (sh, bD, gv, s, start, pos1, lo1, shs, bp, buf, off).
        destruct (minv_reload ht s pos lo k j pos1 lo1 l H Hinv1) as [Hm Hr].
        assert (Hj: 0 <= j <= k) by (destruct H; lia).
        forward_if.
        { change (Int64.repr (8 - 1)) with (Int64.repr 7).
          rewrite sub_pl_gen by (auto; rep_lia). simpl force_val.
          apply tc_order_out; auto; lia. }
        { match goal with H': typed_true _ _ |- _ => rename H' into H4 end.
          change (Int64.sub (Int64.repr 8) (Int64.repr 1)) with (Int64.repr 7) in H4.
          rewrite sub_pl_gen in H4 by (auto; rep_lia). simpl force_val in H4.
          rewrite (proj2 (x_cmp ob (Zlength oc) (a + j) (a + k - 7) Hfc ltac:(lia) ltac:(lia))) in H4.
          simpl in H4. apply and_b2z_tt in H4. destruct H4 as [Hc1 Hc2].
          rewrite int_eq_small in Hc1 by apply bs_reload_fst_range. apply Z.eqb_eq in Hc1.
          apply Z.ltb_lt in Hc2.
          assert (Hres0: xW ht s pos lo k -> snd (bs_reload pos1 lo1) + L + (3 * L)%Z <= pos1 \/ snd (bs_reload pos1 lo1) = 0).
          { intros HW. left. destruct (Hr HW) as [Hu _]. specialize (Hu Hc1). lia. }
          eapply semax_pre with (P' := st j pos1 (snd (bs_reload pos1 lo1)) l g1 True); [unfold st; entailer! |].
          unfold MORE_COMMANDS, abbreviate. repeat (apply -> seq_assoc).
          eapply (dseq _ _ _ (3 * L)%Z); [apply dm8; [lia | lia | exact Hres0] |].
          intros kk1 pos2 w1 g2 Hk1 Hr1 Hx1. repeat (apply -> seq_assoc).
          eapply (dseq _ _ _ (2 * L)%Z); [apply dm10; [lia | lia | res_tac Hr1] |].
          intros kk2 pos3 w2 g3 Hk2 Hr2 Hx2. repeat (apply -> seq_assoc).
          eapply (dseq _ _ _ (1 * L)%Z); [apply dm13; [lia | lia | res_tac Hr2] |].
          intros kk3 pos4 w3 g4 Hk3 Hr3 Hx3. repeat (apply -> seq_assoc).
          eapply dstep_seq with (t := _t'15) (e := 0); [in_tac | lia | lia | res_tac Hr3 |].
          intros kk4 pos5 w4 g5 Hk4 Hr4 Hx4. unfold st. Intros.
          forward.
          match goal with H': minv _ _ _ _ _ _ pos5 _ _ |- _ => rename H' into Hm5 end.
          assert (Hlw: Zlength (w1 ++ w2 ++ w3 ++ w4 ++ []) = kk1 + kk2 + kk3 + kk4).
          { destruct Hm5 as (_ & Hl5 & _). destruct H as (_ & Hl & _). rewrite !Zlength_app in Hl5.
            rewrite !Zlength_app, Zlength_nil. lia. }
          assert (HX: XLA ht s pos lo k 4 (fun r => 7 <? r) (j + kk1 + kk2 + kk3 + kk4) pos5
                        (snd (bs_reload pos1 lo1)) ((((l ++ w1) ++ w2) ++ w3) ++ w4)).
          { eapply (XLA_step ht s pos lo k 4 (fun r => 7 <? r) j pos1 lo1 l pos5 (w1 ++ w2 ++ w3 ++ w4 ++ []));
              [exact HXL | exact Hinv1 | exact Hc1 | apply Z.ltb_lt; lia | | lia | destruct Hm5 as (? & _); lia
              | rewrite app_nil_r, <- !app_assoc; reflexivity | lia].
            repeat (eapply xsteps_S; [eassumption|]). apply xsteps_0. }
          Exists (j + kk1 + kk2 + kk3 + kk4) pos5 (snd (bs_reload pos1 lo1))
            ((((l ++ w1) ++ w2) ++ w3) ++ w4) g5. unfold st. entailer!. }
        { match goal with H': typed_false _ _ |- _ => rename H' into H4 end.
          change (Int64.sub (Int64.repr 8) (Int64.repr 1)) with (Int64.repr 7) in H4.
          rewrite sub_pl_gen in H4 by (auto; rep_lia). simpl force_val in H4.
          rewrite (proj2 (x_cmp ob (Zlength oc) (a + j) (a + k - 7) Hfc ltac:(lia) ltac:(lia))) in H4.
          simpl in H4. apply and_b2z_tf in H4.
          rewrite int_eq_small in H4 by apply bs_reload_fst_range.
          assert (HXA: XA ht s pos lo k j pos1 (snd (bs_reload pos1 lo1)) l).
          { apply (XLA_exit ht s pos lo k 4 (fun r => 7 <? r) j pos1 lo1 l HXL Hinv1).
            unfold BIT_unfinished. apply andb_false_iff.
            destruct H4 as [H4|H4]; [left; exact H4 | right; apply Z.ltb_ge; apply Z.ltb_ge in H4; lia]. }
          forward. Exists j pos1 (snd (bs_reload pos1 lo1)) l g1. unfold st. entailer!.
          try intros HW. match goal with HW: xW _ _ _ _ _ |- _ => destruct (Hr HW) as [Hu Hn] end.
          destruct (Z.eq_dec (fst (bs_reload pos1 lo1)) BIT_unfinished) as [E|E]; [right; auto | left; auto]. } }
      apply andp_left2. unfold st. apply derives_refl. }
  { rewrite sub_pp_gen in H1 by (auto; lia). simpl in H1. apply ltu_tf in H1; [|rep_lia].
    change (Int64.unsigned (Ptrofs.to_int64 (Ptrofs.repr 8))) with 8 in H1.
    forward_call (sh, bD, gv, s, start, pos, lo, shs, bp, buf, off).
    destruct (minv_reload ht s pos lo k 0 pos lo [] H Hinv) as [Hm Hr].
    assert (HXA: XA ht s pos lo k 0 pos (snd (bs_reload pos lo)) []) by (apply XA_short; [lia | exact Hinv]).
    Exists 0 pos (snd (bs_reload pos lo)) (@nil Z) g. entailer!.
    try intros HW. match goal with HW: xW _ _ _ _ _ |- _ => destruct (Hr HW) as [Hu Hn] end.
    destruct (Z.eq_dec (fst (bs_reload pos lo)) BIT_unfinished) as [E|E]; [right; auto | left; auto]. }
Qed.

Lemma segB_ok (j pos1 lo1: Z) (l: list Z) (g: list val) :
  semax DeltaX2 (st j pos1 lo1 l g (xW ht s pos lo k -> lo1 = 0 \/ lo1 + 57 <= pos1)) segB
    (normal_ret_assert (EX j2: Z, EX pos2: Z, EX lo2: Z, EX l2: list Z, EX g2: list val,
       st j2 pos2 lo2 l2 g2 (k - j2 <= 1 /\ (xW ht s pos lo k -> lo2 = 0) /\
                             XB ht s k j pos1 lo1 l j2 pos2 lo2 l2))).
Proof.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv [segB f_HUF_decodeStreamX2 fn_body] in c in change c with c' end.
  unfold st, DeltaX2. Intros.
  abbreviate (func_tycontext f_HUF_decodeStreamX2 Vprog G_stream2 nil) as Delta.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as Hfc by entailer!.
  assert_PROP (bit_inv s pos1 lo1) as Hinv by (sep_apply bit_rep_inv; entailer!).
  assert (Hob: isptr ob) by (destruct Hfc; auto).
  assert (Hmo: Zlength oc <= Ptrofs.max_unsigned).
  { destruct Hfc as (_ & _ & Hsz & _). destruct ob; try contradiction. simpl in Hsz.
    rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.max_unsigned. lia. }
  assert (Hj: 0 <= j <= k) by (destruct H; lia).
  pose proof (tab_facts ht L c2 Htab) as (_ & _ & HL).
  forward_if.
  { entailer!. apply sameblock_off; auto. }
  { rewrite sub_pp_gen in H2 by (auto; lia). simpl in H2. apply ltu_tt in H2; [|rep_lia].
    change (Int64.unsigned (Int64.repr (Int.signed (Int.repr 2)))) with 2 in H2.
    assert (Hk2: 2 <= k) by lia.
    forward_loop (EX j1: Z, EX pos2: Z, EX lo2: Z, EX l2: list Z, EX g2: list val,
                  st j1 pos2 lo2 l2 g2 (XLB1 ht s k j pos1 lo1 l j1 pos2 lo2 l2))
      break: (EX j1: Z, EX pos2: Z, EX lo2: Z, EX l2: list Z, EX g2: list val,
              st j1 pos2 lo2 l2 g2 ((xW ht s pos lo k -> lo2 = 0 \/ (lo2 + 57 <= pos2 /\ k - j1 <= 1)) /\
                                    XL1 ht s k j pos1 lo1 l j1 pos2 lo2 l2)).
    { pose proof (XLB1_init ht s k j pos1 lo1 l Hj) as HX0.
      Exists j pos1 lo1 l g. unfold st. entailer!. }
    { clear H H0 H1 Hinv Hj. Intros j1 pos2 lo2 l2 g2. unfold st. Intros.
      match goal with H': XLB1 _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXL end.
      assert_PROP (bit_inv s pos2 lo2) as Hinv1 by (sep_apply bit_rep_inv; entailer!).
      forward_call (sh, bD, gv, s, start, pos2, lo2, shs, bp, buf, off).
      destruct (minv_reload ht s pos lo k j1 pos2 lo2 l2 H Hinv1) as [Hm Hr].
      assert (Hj: 0 <= j1 <= k) by (destruct H; lia).
      forward_if.
      { rewrite sub_pi_gen by (auto; rep_lia). simpl force_val. apply tc_order_out; auto; lia. }
      { match goal with H: typed_true _ _ |- _ => rename H into Hc end.
        rewrite sub_pi_gen in Hc by (auto; rep_lia). simpl force_val in Hc.
        rewrite (proj1 (x_cmp ob (Zlength oc) (a + j1) (a + k - 2) Hfc ltac:(lia) ltac:(lia))) in Hc.
        simpl in Hc. apply and_b2z_tt in Hc. destruct Hc as [Hc1 Hc2].
        rewrite int_eq_small in Hc1 by apply bs_reload_fst_range. apply Z.eqb_eq in Hc1.
        apply Z.leb_le in Hc2.
        assert (Hres0: xW ht s pos lo k -> snd (bs_reload pos2 lo2) + L + 0 <= pos2 \/ snd (bs_reload pos2 lo2) = 0).
        { intros HW. left. destruct (Hr HW) as [Hu _]. specialize (Hu Hc1). lia. }
        eapply semax_pre with (P' := st j1 pos2 (snd (bs_reload pos2 lo2)) l2 g2 True); [unfold st; entailer! |].
        unfold MORE_COMMANDS, abbreviate.
        eapply dstep_seq with (t := _t'19) (e := 0); [in_tac | lia | lia | exact Hres0 |].
        intros kk1 pos3 w g3 Hk1 Hr1 Hx1. unfold st. Intros.
        forward.
        match goal with H': minv _ _ _ _ _ _ pos3 _ _ |- _ => rename H' into Hm3 end.
        assert (Hw: Zlength w = kk1).
        { destruct Hm3 as (_ & Hl3 & _). destruct H as (_ & Hl & _). rewrite Zlength_app in Hl3. lia. }
        assert (HX: XLB1 ht s k j pos1 lo1 l (j1 + kk1) pos3 (snd (bs_reload pos2 lo2)) (l2 ++ w)).
        { rewrite <- Hw. apply XLB1_step; auto; try lia; destruct Hm3 as (? & _); lia. }
        Exists (j1 + kk1) pos3 (snd (bs_reload pos2 lo2)) (l2 ++ w) g3. unfold st. entailer!. }
      { match goal with H: typed_false _ _ |- _ => rename H into H4 end.
        rewrite sub_pi_gen in H4 by (auto; rep_lia). simpl force_val in H4.
        rewrite (proj1 (x_cmp ob (Zlength oc) (a + j1) (a + k - 2) Hfc ltac:(lia) ltac:(lia))) in H4.
        simpl in H4. apply and_b2z_tf in H4.
        rewrite int_eq_small in H4 by apply bs_reload_fst_range.
        assert (HXL1: XL1 ht s k j pos1 lo1 l j1 pos2 (snd (bs_reload pos2 lo2)) l2).
        { apply XLB1_exit; auto; try lia.
          unfold BIT_unfinished. apply andb_false_iff.
          destruct H4 as [H4|H4]; [left; exact H4 | right; apply Z.leb_gt; apply Z.leb_gt in H4; lia]. }
        forward. Exists j1 pos2 (snd (bs_reload pos2 lo2)) l2 g2. unfold st. entailer!.
        try intros HW. match goal with HW: xW _ _ _ _ _ |- _ => destruct (Hr HW) as [Hu Hn] end.
        destruct (Z.eq_dec (fst (bs_reload pos2 lo2)) BIT_unfinished) as [E|E]; [right | left; auto].
        split; [apply Hu, E|]. destruct H4 as [H4|H4].
        - rewrite E in H4. discriminate.
        - apply Z.leb_gt in H4. lia. } }
    Intros j1 pos2 lo2 l2 g2.
    forward_while (EX j3: Z, EX pos3: Z, EX lo3: Z, EX l3: list Z, EX g3: list val,
              st j3 pos3 lo3 l3 g3 ((xW ht s pos lo k -> lo3 = 0 \/ (lo3 + 57 <= pos3 /\ k - j3 <= 1)) /\
                                    XL1 ht s k j pos1 lo1 l j3 pos3 lo3 l3)).
    { apply andp_left2. Exists j1 pos2 lo2 l2 g2. apply derives_refl. }
    { unfold st. entailer!. rewrite sub_pi_gen by (auto; rep_lia). simpl force_val.
      assert (0 <= j3 <= k) by (destruct H3; lia). apply tc_order_out; auto; lia. }
    { rewrite sub_pi_gen in HRE by (auto; rep_lia). simpl force_val in HRE.
      match goal with H': (_ -> lo3 = 0 \/ _) /\ XL1 _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H' as [? ?] end.
      match goal with Hm3: minv _ _ _ _ _ j3 _ _ _, Hq: xW _ _ _ _ _ -> lo3 = 0 \/ _ |- _ =>
        rename Hm3 into Hm3', Hq into Hq3 end.
      assert (Hj3: 0 <= j3 <= k) by (destruct Hm3'; lia).
      rewrite (proj1 (x_cmp ob (Zlength oc) (a + j3) (a + k - 2) Hfc ltac:(lia) ltac:(lia))) in HRE.
      apply bool2val_tt, Z.leb_le in HRE.
      assert (Hz: xW ht s pos lo k -> lo3 = 0) by (intros HW; destruct (Hq3 HW) as [|[_ ?]]; [auto | lia]).
      eapply semax_pre with (P' := st j3 pos3 lo3 l3 g3 True); [unfold st; entailer! |].
      rewrite semax_seq_skip.
      eapply dstep_seq with (t := _t'20) (e := 0); [in_tac | lia | lia | intros HW; right; apply Hz, HW |].
      intros kk1 pos4 w g4 Hk1 Hr1 Hx1. unfold st. Intros. forward.
      match goal with H': minv _ _ _ _ _ _ pos4 _ _ |- _ => rename H' into Hm4 end.
      match goal with H': XL1 _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXL end.
      assert (Hw: Zlength w = kk1).
      { destruct Hm4 as (_ & Hl4 & _). destruct Hm3' as (_ & Hl & _). rewrite Zlength_app in Hl4. lia. }
      assert (HX: XL1 ht s k j pos1 lo1 l (j3 + kk1) pos4 lo3 (l3 ++ w)).
      { rewrite <- Hw. apply (XL1_step ht s k j pos1 lo1 l j3 pos3 lo3 l3 pos4 w); auto; try lia; destruct Hm4 as (? & _); lia. }
      Exists (j3 + kk1, pos4, lo3, l3 ++ w, g4). entailer!. all: first [apply derives_refl | intros HW; left; apply Hz, HW]. }
    { rewrite sub_pi_gen in HRE by (auto; rep_lia). simpl force_val in HRE.
      match goal with H': (_ -> lo3 = 0 \/ _) /\ XL1 _ _ _ _ _ _ _ _ _ _ _ |- _ => destruct H' as [? ?] end.
      match goal with Hm3: minv _ _ _ _ _ j3 _ _ _, Hq: xW _ _ _ _ _ -> lo3 = 0 \/ _ |- _ =>
        rename Hm3 into Hm3', Hq into Hq3 end.
      assert (Hj3: 0 <= j3 <= k) by (destruct Hm3'; lia).
      rewrite (proj1 (x_cmp ob (Zlength oc) (a + j3) (a + k - 2) Hfc ltac:(lia) ltac:(lia))) in HRE.
      apply bool2val_tf, Z.leb_gt in HRE.
      assert_PROP (bit_inv s pos3 lo3) as Hinv3 by (sep_apply bit_rep_inv; entailer!).
      match goal with H': XL1 _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXL end.
      assert (HXB: XB ht s k j pos1 lo1 l j3 pos3 lo3 l3) by (apply XL1_exit; auto; lia).
      forward. Exists j3 pos3 lo3 l3 g3. unfold st. entailer!.
      match goal with |- _ /\ _ => split; [lia | intros HW] | _ => try intros HW end.
      match goal with H': xW _ _ _ _ _ |- _ => rename H' into HW0 end.
      destruct (Hq3 HW0) as [|[? ?]]; [auto|].
      exfalso. apply (minv_far_false ht s _ _ pos lo k Htab j3 pos3 lo3 l3 Hm3' HW0 ltac:(lia)
        ltac:(destruct Hinv3 as (_ & _ & ? & _); lia) ltac:(lia)). } }
  { match goal with H: typed_false _ _ |- _ => rename H into Hc end.
    rewrite sub_pp_gen in Hc by (auto; lia). simpl in Hc. apply ltu_tf in Hc; [|rep_lia].
    change (Int64.unsigned (Int64.repr (Int.signed (Int.repr 2)))) with 2 in Hc.
    assert (HXB: XB ht s k j pos1 lo1 l j pos1 lo1 l) by (apply XB_skip; lia).
    forward. Exists j pos1 lo1 l g. unfold st. entailer!.
    match goal with |- _ /\ _ => split; [lia | intros HW] | _ => try intros HW end.
    match goal with H': xW _ _ _ _ _ |- _ => rename H' into HW0 end.
    destruct (H1 HW0) as [|?]; [auto|].
    exfalso. apply (minv_far_false ht s _ _ pos lo k Htab j pos1 lo1 l H HW0 ltac:(lia)
      ltac:(destruct Hinv as (_ & _ & ? & _); lia) ltac:(lia)). }
Qed.

Lemma cur_last (l: list Z) (g: list val) (j x: Z) :
  Zlength l = j -> Zlength g = k - j -> 0 <= j -> j + 1 = k ->
  sublist 0 (a + j) (cur l g) ++ zbytes [x] ++ sublist (a + j + 1) (Zlength oc) (cur l g) = cur (l ++ [x]) [].
Proof. intros. unfold cur. list_solve. Qed.

End Body.

(* HUF_decodeLastSymbolX2's exact clause as the model's last phase *)
Lemma xlast_call (ht: huf_table) (s: list Z) (L: Z) (c2: list (val * (val * val))) (pos1 lo1 v kk b2 nb j k: Z) :
  x2_tab_ok ht L c2 -> L = xh_x2_log ht -> 0 <= v < 2 ^ L -> x2_step ht L v kk b2 nb ->
  v = xb_look_fast (xb_of s pos1 lo1) L ->
  nth (Z.to_nat v) (xh_cells_x2 ht L) (0, 0, 0) = ((fst (hsym ht L v) + 256 * b2)%Z, nb, kk) ->
  0 <= lo1 + 64 - pos1 -> lo1 + 64 - (pos1 - nb) <= Int.max_unsigned -> 0 < k - j ->
  forall d1, xb_rel s pos1 lo1 d1 ->
    fst (xPC (xhuf_of true ht) d1 (k - j)) = [fst (hsym ht L v)] /\
    xb_rel s (x2_last_pos pos1 lo1 kk nb) lo1 (snd (xPC (xhuf_of true ht) d1 (k - j))).
Proof.
  intros Htab HLx Hv Hst Hx1 Hx2 Hb0 Hb Hkj d1 Hr.
  destruct (tab_facts ht L c2 Htab) as (Hok & HL & _).
  pose proof (hsym_range ht L v Hok ltac:(lia) Hv) as [Hs1 _].
  assert (Hkk: 1 <= kk <= 2 /\ 0 <= b2 < 256 /\ 1 <= nb).
  { destruct Hst as (Hb2 & Hnb & Hc). split; [|lia]. destruct (hsym ht L v) as [s1 n1].
    destruct Hc as [[-> _]|Hc]; [lia|].
    destruct (hsym ht L ((v * 2 ^ n1) mod 2 ^ L)) as [s2 n2]. destruct Hc as (-> & _). lia. }
  unfold xPC. replace (0 <? k - j) with true by (symmetry; apply Z.ltb_lt; lia).
  apply (xlast_of ht s L pos1 lo1 v kk b2 nb d1 HLx Hx1 Hx2); [lia | lia | lia | lia | lia | lia | exact Hr].
Qed.

Lemma body_HUF_decodeStreamX2 :
  hsym_facts -> semax_body Vprog G_stream2 f_HUF_decodeStreamX2 HUF_decodeStreamX2_spec.
Proof.
  intros Hf. start_function.
  assert_PROP (field_compatible (tarray tuchar (Zlength oc)) [] ob) as Hfc by entailer!.
  assert_PROP (bit_inv s pos lo) as Hinv by (sep_apply bit_rep_inv; entailer!).
  assert (Hob: isptr ob) by (destruct Hfc; auto).
  assert (Hs: bytes_ok s) by (destruct Hinv; auto).
  forward.
  eapply semax_seq'.
  { eapply semax_pre; [| eapply segA_ok with (sh := sh) (bD := bD) (gv := gv) (s := s) (start := start) (pos := pos) (lo := lo) (shs := shs) (bp := bp) (buf := buf) (sht := sht) (dt := dt) (ht := ht) (L := L) (c2 := c2) (sho := sho) (ob := ob) (oc := oc) (a := a) (k := k) (g := sublist a (a + k) oc); eassumption].
    unfold st, cur. entailer!.
    { split; [apply minv_0; lia | list_solve]. }
    rewrite app_nil_l, (sublist_rejoin a (a + k)), (sublist_rejoin 0 a), sublist_same by lia. cancel. }
  Intros j pos1 lo1 l g.
  unfold st at 1. Intros.
  match goal with H': XA _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXA end.
  eapply semax_seq'.
  { eapply semax_pre; [| eapply segB_ok with (sh := sh) (bD := bD) (gv := gv) (s := s) (start := start) (pos := pos) (lo := lo) (shs := shs) (bp := bp) (buf := buf) (sht := sht) (dt := dt) (ht := ht) (L := L) (c2 := c2) (sho := sho) (ob := ob) (oc := oc) (a := a) (k := k) (j := j) (pos1 := pos1) (lo1 := lo1) (l := l) (g := g); eassumption].
    unfold st. entailer!. }
  rename j into jA, pos1 into posA, lo1 into loA, l into lA, g into gA.
  Intros j pos1 lo1 l g.
  unfold st. Intros.
  match goal with H': XB _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXB end.
  match goal with H': minv _ _ _ _ _ j _ _ _ |- _ => rename H' into Hm end.
  match goal with H': Zlength g = _ |- _ => rename H' into Hg end.
  match goal with H': k - j <= 1 |- _ => rename H' into Hkj end.
  match goal with H': xW _ _ _ _ _ -> lo1 = 0 |- _ => rename H' into Hz end.
  pose proof (tab_facts ht L c2 H0) as (_ & _ & HL).
  assert_PROP (bit_inv s pos1 lo1) as Hinv1 by (sep_apply bit_rep_inv; entailer!).
  assert (Hj: 0 <= j <= k) by (destruct Hm; lia).
  assert (Hlj: Zlength l = j) by (destruct Hm as (_ & ? & _); auto).
  forward_if (EX pos2: Z, EX lo2: Z, EX l2: list Z,
    PROP (minv ht s pos lo k k pos2 lo2 l2; xW ht s pos lo k -> pos2 = 0 /\ lo2 = 0;
          XC ht s k j pos1 lo1 l pos2 lo2 l2)
    LOCAL (temp _pStart (offset_val a ob); gvars gv; temp _p (offset_val (a + k) ob); temp _bitDPtr bD;
           temp _pEnd (offset_val (a + k) ob); temp _dt dt; temp _dtLog (Vint (Int.repr L)))
    SEP (BIT_DStream_rep sh gv s start pos2 lo2 bD; bit_src shs bp buf;
         data_at sht (tarray t_deltx2 (2 ^ L)) c2 dt;
         data_at sho (tarray tuchar (Zlength oc)) (cur oc a k l2 []) ob))%assert.
  { eapply tc_order_out with (sho := sho) (ob := ob) (oc := oc) (a := a) (k := k); auto; lia. }
  { match goal with H': typed_true _ _ |- _ => rename H' into Hc end.
    rewrite (proj2 (x_cmp ob (Zlength oc) (a + j) (a + k) Hfc ltac:(lia) ltac:(lia))) in Hc.
    apply bool2val_tt, Z.ltb_lt in Hc.
    assert (Hjk: j + 1 = k) by lia.
    assert (Hcl: Zlength (cur oc a k l g) = Zlength oc) by (unfold cur; list_solve).
    assert (Hsafe: lo1 + 64 - pos1 <= lo + 64 - pos + 12 * j) by (destruct Hm as (_ & _ & _ & ? & _); auto).
    forward_call (sh, bD, gv, s, start, pos1, lo1, sht, dt, ht, L, c2, sho, ob, cur oc a k l g, a + j).
    all: try (rewrite Hcl; solve [cancel | lia]).
    Intros vret. destruct vret as [[[v kk] b2] nb]. simpl fst in *; simpl snd in *.
    rewrite Hcl.
    forward.
    match goal with Hv: 0 <= v < 2 ^ L, Hx: _ -> v = _, Hst: x2_step _ _ _ _ _ _ |- _ =>
      destruct (minv_last ht s L c2 pos lo k Hf H0 Hs H3 j pos1 lo1 v kk b2 nb l Hm Hjk Hz Hv Hx Hst)
        as (Hnb & Hm' & Hp0) end.
    match goal with Hv: 0 <= v < 2 ^ L, Hst: x2_step _ _ _ _ _ _, Hxa1: v = xb_look_fast _ _,
                    Hxa2: nth (Z.to_nat v) _ _ = _ |- _ =>
      pose proof (xlast_call ht s L c2 pos1 lo1 v kk b2 nb j k H0 ltac:(assumption) Hv Hst Hxa1 Hxa2
                    ltac:(destruct Hinv1 as (_ & _ & _ & _ & _ & ? & _); lia) ltac:(lia) ltac:(lia)) as HXc;
      clear Hxa1 Hxa2 end.
    assert (HXC: XC ht s k j pos1 lo1 l (x2_last_pos pos1 lo1 kk nb) lo1 (l ++ [fst (hsym ht L v)]))
      by (exists [fst (hsym ht L v)]; split; [reflexivity | exact HXc]).
    Exists (x2_last_pos pos1 lo1 kk nb) lo1 (l ++ [fst (hsym ht L v)]).
    assert (Hcl2: sublist 0 (a + j) (cur oc a k l g) ++ zbytes [fst (hsym ht L v)] ++
                  sublist (a + j + 1) (Zlength oc) (cur oc a k l g) = cur oc a k (l ++ [fst (hsym ht L v)]) [])
      by (unfold cur; list_solve).
    rewrite Hcl2. entailer!.
    all: first [f_equal; lia | intros HW; split; [apply Hp0, HW | apply Hz, HW] | exact HXC | idtac]. }
  { match goal with H': typed_false _ _ |- _ => rename H' into Hc end.
    rewrite (proj2 (x_cmp ob (Zlength oc) (a + j) (a + k) Hfc ltac:(lia) ltac:(lia))) in Hc.
    apply bool2val_tf, Z.ltb_ge in Hc.
    assert (j = k) by lia. subst j.
    assert (g = []) by (apply Zlength_nil_inv; lia). subst g.
    assert (HXC: XC ht s k k pos1 lo1 l pos1 lo1 l).
    { exists nil. split; [rewrite app_nil_r; reflexivity|]. intros d1 Hr. unfold xPC. rewrite Z.sub_diag. auto. }
    forward. Exists pos1 lo1 l. entailer!.
    try intros HW. match goal with H': xW _ _ _ _ _ |- _ => rename H' into HW end.
    split; [|apply Hz, HW].
    destruct HW as [Hlp [l' Hl']]. apply (minv_end ht s pos lo _ pos1 lo1 l Hm Hlp l' Hl'). }
  Intros pos2 lo2 l2.
  forward.
  { entailer!. apply sameblock_off; auto. }
  Exists pos2 lo2 l2. entailer!.
  match goal with H': minv _ _ _ _ _ k pos2 lo2 l2 |- _ => rename H' into Hm2 end.
  match goal with H': xW _ _ _ _ _ -> pos2 = 0 /\ lo2 = 0 |- _ => rename H' into Hw2 end.
  pose proof Hm2 as (_ & Hl2 & Hb2 & Hsafe2 & _).
  match goal with H': XC _ _ _ _ _ _ _ _ _ _ |- _ => rename H' into HXC end.
  split; [exact Hl2|]. split; [exact Hb2|]. split; [lia|]. split; [|split].
  - intros Hlp l' Hl'.
    destruct (minv_end ht s pos lo k pos2 lo2 l2 Hm2 Hlp l' Hl') as [-> ->].
    split; [reflexivity|]. split; [reflexivity|]. apply (Hw2 (conj Hlp (ex_intro _ l' Hl'))).
  - eapply stream_exact; eassumption.
  - assert (Hmo: Zlength oc <= Ptrofs.max_unsigned).
    { destruct Hfc as (_ & _ & Hsz & _). destruct ob; try contradiction. simpl in Hsz.
      rewrite Z.max_r in Hsz by lia. pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.max_unsigned. lia. }
    rewrite sub_pp_gen by (auto; lia). simpl. do 2 f_equal. lia.
Qed.
