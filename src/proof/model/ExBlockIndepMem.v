(* Two runs of the exact block model's copies (ExBlock.xm_fwd, xm_move, xm_chunks16, ...) on memories that may
   differ: the relation `rel c m1 m2` says the two memories have the same shape (the same destination cells
   written, the same litExtraBuffer length) and hold the same values on the cells c calls clean (c R_dst: cells
   of the destination, c R_lxb: cells of litExtraBuffer).  Each copy keeps the relation, both failing or both
   succeeding, and a cell it writes is clean when the cell it read was (or, for a forward copy within the
   destination, when it read cells that are clean or that the same copy already wrote).

   This is the memory part of ExBlockIndep.xblock_indep (a block does not depend on litExtraBuffer's stale
   bytes).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Fse Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeBlkDefs Zstd.proof.model.ExAgreeBlkLitCopy.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma Zlength_nonneg : forall {A} (l: list A), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

(* ---------- the relation ---------- *)

Definition creg : Type := xreg -> Z -> Prop.

Definition rel (c: creg) (m1 m2: xmem) : Prop :=
  (forall p, 0 <= p -> (dcell m1 p = None <-> dcell m2 p = None)) /\
  (forall p, 0 <= p -> c R_dst p -> dcell m1 p = dcell m2 p) /\
  Zlength (xm_dst m1) = Zlength (xm_dst m2) /\
  Zlength (xm_lxb m1) = Zlength (xm_lxb m2) /\
  (forall i, 0 <= i < Zlength (xm_lxb m1) -> c R_lxb i -> byte_at (xm_lxb m1) i = byte_at (xm_lxb m2) i).

(* a cell of the block's input is always the same in both runs *)
Definition cl_of (c: creg) (r: xreg) (i: Z) : Prop :=
  match r with R_src => True | _ => c r i end.

Definition xreg_eqb (a b: xreg) : bool :=
  match a, b with R_dst, R_dst | R_lxb, R_lxb | R_src, R_src => true | _, _ => false end.

Lemma xreg_eqb_spec : forall a b, xreg_eqb a b = true <-> a = b.
Proof. destruct a, b; simpl; split; congruence. Qed.

(* c after writing k cells of region r from d, the cell d + j clean iff E j *)
Definition cwr (c: creg) (r: xreg) (d k: Z) (E: Z -> Prop) : creg :=
  fun r' x => if xreg_eqb r' r && (d <=? x) && (x <? d + k) then E (x - d) else c r' x.

(* both fail, or both succeed with related results *)
Definition orel {A} (R: A -> A -> Prop) (o1 o2: option A) : Prop :=
  match o1, o2 with None, None => True | Some a, Some b => R a b | _, _ => False end.

Lemma orel_mono : forall {A} (R R': A -> A -> Prop) o1 o2,
  (forall a b, R a b -> R' a b) -> orel R o1 o2 -> orel R' o1 o2.
Proof. intros A R R' [a|] [b|] H; simpl; auto. Qed.

Definition cle (c c': creg) : Prop := forall r x, c r x -> c' r x.

Lemma rel_mono : forall c c' m1 m2, cle c' c -> rel c m1 m2 -> rel c' m1 m2.
Proof.
  intros c c' m1 m2 Hc (H1 & H2 & H3 & H4 & H5). unfold cle in Hc.
  repeat split; auto.
  - apply H1; auto.
  - apply H1; auto.
Qed.

Lemma cwr_cases : forall c r d k E r' x,
  (r' = r /\ d <= x < d + k /\ cwr c r d k E r' x = E (x - d)) \/
  (~ (r' = r /\ d <= x < d + k) /\ cwr c r d k E r' x = c r' x).
Proof.
  intros c r d k E r' x. unfold cwr.
  destruct (xreg_eqb r' r) eqn:Er.
  - apply xreg_eqb_spec in Er. subst r'.
    destruct (Z.leb_spec d x); destruct (Z.ltb_spec x (d + k)); simpl; [left|right..]; split; auto; lia.
  - right. simpl. split; auto. intros [He _]. subst r'.
    assert (xreg_eqb r r = true) by (apply xreg_eqb_spec; reflexivity). congruence.
Qed.

Lemma cwr_empty : forall c r d k E r' x, k <= 0 -> cwr c r d k E r' x -> c r' x.
Proof.
  intros c r d k E r' x Hk H.
  destruct (cwr_cases c r d k E r' x) as [(_ & Hx & _)|(_ & Hcw)]; [lia|]. rewrite Hcw in H. exact H.
Qed.

Lemma cwr_inv : forall c r d k E r' x, cwr c r d k E r' x ->
  (r' = r /\ d <= x < d + k /\ E (x - d)) \/ (~ (r' = r /\ d <= x < d + k) /\ c r' x).
Proof.
  intros c r d k E r' x H.
  destruct (cwr_cases c r d k E r' x) as [(? & ? & Hcw)|(? & Hcw)]; rewrite Hcw in H; auto.
Qed.

Lemma cwr_in : forall c r d k (E: Z -> Prop) r' x, r' = r -> d <= x < d + k -> E (x - d) -> cwr c r d k E r' x.
Proof.
  intros c r d k E r' x Hr Hx HE.
  destruct (cwr_cases c r d k E r' x) as [(? & ? & Hcw)|(Hn & Hcw)]; rewrite Hcw; auto.
  exfalso; apply Hn; auto.
Qed.

Lemma cwr_out : forall c r d k (E: Z -> Prop) r' x, ~ (r' = r /\ d <= x < d + k) -> c r' x -> cwr c r d k E r' x.
Proof.
  intros c r d k E r' x Hn Hc.
  destruct (cwr_cases c r d k E r' x) as [(? & ? & Hcw)|(? & Hcw)]; rewrite Hcw; auto.
  exfalso; apply Hn; auto.
Qed.

(* writing clean values keeps every clean cell clean *)
Lemma cwr_true_sup : forall c r d k r' x, c r' x -> cwr c r d k (fun _ => True) r' x.
Proof.
  intros c r d k r' x Hc.
  destruct (cwr_cases c r d k (fun _ => True) r' x) as [(? & ? & Hcw)|(? & Hcw)]; rewrite Hcw; auto.
Qed.

Lemma cwr_other : forall c r d k E r' x, r' <> r -> (cwr c r d k E r' x <-> c r' x).
Proof.
  intros c r d k E r' x Hr.
  destruct (cwr_cases c r d k E r' x) as [(? & ? & Hcw)|(? & Hcw)]; rewrite Hcw; [congruence|tauto].
Qed.

(* ---------- one read, one store ---------- *)

Lemma rd_rel : forall src c m1 m2 r i, rel c m1 m2 ->
  (xm_rd src m1 r i = None <-> xm_rd src m2 r i = None) /\
  ((i < 0 \/ cl_of c r i) -> xm_rd src m1 r i = xm_rd src m2 r i).
Proof.
  intros src c m1 m2 r i (H1 & H2 & H3 & H4 & H5). unfold xm_rd.
  destruct (Z.ltb_spec i 0); [split; [tauto|auto]|].
  destruct r.
  - split; [apply H1; lia|]. intros [Hi|Hi]; [lia|]. apply H2; auto; lia.
  - rewrite <- H4. destruct (Z.ltb_spec i (Zlength (xm_lxb m1))).
    + split; [split; discriminate|]. intros [Hi|Hi]; [lia|]. f_equal. apply H5; auto; lia.
    + split; [tauto|auto].
  - split; [tauto|auto].
Qed.

Lemma upd_len : forall {A} (l: list A) i x, length (upd l i x) = length l.
Proof. induction l as [|y l IH]; intros [|i] x; simpl; auto. Qed.

Lemma upd_Zlength : forall {A} (l: list A) i x, Zlength (upd l i x) = Zlength l.
Proof. intros. rewrite !Zlength_correct, upd_len. reflexivity. Qed.

Lemma dst_len_wr : forall (d: list (option Z)) i v, 0 <= i ->
  Zlength (if i <? Zlength d then upd d (Z.to_nat i) (Some v)
           else d ++ repeat None (Z.to_nat (i - Zlength d)) ++ [Some v]) = Z.max (Zlength d) (i + 1).
Proof.
  intros d i v Hi. destruct (Z.ltb_spec i (Zlength d)).
  - rewrite upd_Zlength. lia.
  - rewrite !Zlength_correct, !app_length, repeat_length. simpl. rewrite Zlength_correct in H. lia.
Qed.


Lemma byte_at_upd : forall l i j v, 0 <= i < Zlength l -> 0 <= j ->
  byte_at (upd l (Z.to_nat i) v) j = if j =? i then v else byte_at l j.
Proof.
  intros l i j v Hi Hj. unfold byte_at. rewrite Zlength_correct in Hi.
  rewrite nth_upd_any by lia.
  destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat i)); destruct (Z.eqb_spec j i); auto; lia.
Qed.

Lemma wr_rel : forall c m1 m2 r i v1 v2 (P: Prop), rel c m1 m2 -> (P -> v1 = v2) ->
  orel (rel (cwr c r i 1 (fun _ => P))) (xm_wr m1 r i v1) (xm_wr m2 r i v2).
Proof.
  intros c m1 m2 r i v1 v2 P HR HP.
  pose proof HR as (H1 & H2 & H3 & H4 & H5).
  unfold xm_wr. destruct (Z.ltb_spec i 0); [exact I|].
  destruct r.
  - simpl. destruct (wr_dst m1 i v1 ltac:(lia)) as (m1' & E1 & L1 & D1).
    destruct (wr_dst m2 i v2 ltac:(lia)) as (m2' & E2 & L2 & D2).
    unfold xm_wr in E1, E2. destruct (Z.ltb_spec i 0); [lia|]. injection E1 as <-. injection E2 as <-.
    split; [|split; [|split; [|split]]]; simpl.
    + intros p Hp. rewrite D1, D2 by lia. destruct (p =? i); [split; discriminate|]. apply H1; auto.
    + intros p Hp Hc. rewrite D1, D2 by lia.
      destruct (cwr_cases c R_dst i 1 (fun _ => P) R_dst p) as [(_ & Hpi & Hcw)|(Hpi & Hcw)];
        rewrite Hcw in Hc.
      * replace p with i by lia. rewrite Z.eqb_refl. f_equal; auto.
      * destruct (Z.eqb_spec p i); [exfalso; apply Hpi; split; auto; lia|]. auto.
    + rewrite !dst_len_wr by lia. congruence.
    + exact H4.
    + intros j Hj Hc. apply H5; auto.
  - rewrite <- H4. destruct (Z.ltb_spec i (Zlength (xm_lxb m1))); [|exact I].
    simpl. split; [|split; [|split; [|split]]]; simpl; auto.
    + rewrite !upd_Zlength. exact H4.
    + rewrite upd_Zlength. intros j Hj Hc.
      rewrite !byte_at_upd by lia.
      destruct (cwr_cases c R_lxb i 1 (fun _ => P) R_lxb j) as [(_ & Hji & Hcw)|(Hji & Hcw)];
        rewrite Hcw in Hc.
      * replace j with i by lia. rewrite Z.eqb_refl. auto.
      * destruct (Z.eqb_spec j i); [exfalso; apply Hji; split; auto; lia|]. apply H5; auto.
  - exact I.
Qed.

(* ---------- copies ---------- *)

(* a copy between two different regions: cell d + j clean iff its source s + j was *)
Lemma fwd_x : forall src k c m1 m2 rd d rs s, rs <> rd -> rel c m1 m2 ->
  orel (rel (cwr c rd d (Z.of_nat k) (fun j => s + j < 0 \/ cl_of c rs (s + j))))
       (xm_fwd src k m1 rd d rs s) (xm_fwd src k m2 rd d rs s).
Proof.
  induction k as [|k IH]; intros c m1 m2 rd d rs s Hne HR; cbn [xm_fwd orel]; [|rewrite Nat2Z.inj_succ].
  - eapply rel_mono; [|exact HR]. intros r x Hx. apply cwr_empty in Hx; [exact Hx|lia].
  - destruct (rd_rel src c m1 m2 rs s HR) as [Hn He].
    destruct (xm_rd src m1 rs s) as [v1|] eqn:R1; destruct (xm_rd src m2 rs s) as [v2|] eqn:R2;
      try (exfalso; destruct Hn; intuition congruence); [|exact I].
    pose proof (wr_rel c m1 m2 rd d v1 v2 (s + 0 < 0 \/ cl_of c rs (s + 0)) HR) as HW.
    rewrite Z.add_0_r in HW. specialize (HW ltac:(intros Hc; specialize (He Hc); congruence)).
    destruct (xm_wr m1 rd d v1) as [m1'|]; destruct (xm_wr m2 rd d v2) as [m2'|]; simpl in HW;
      try contradiction; [|exact I].
    specialize (IH _ m1' m2' rd (d + 1) rs (s + 1) Hne HW).
    eapply orel_mono; [|exact IH]. intros a b Hab. eapply rel_mono; [|exact Hab].
    intros r x Hx.
    set (c1 := cwr c rd d 1 (fun _ => s < 0 \/ cl_of c rs s)).
    assert (Hc0: forall y, c1 rs y = c rs y).
    { intros y. unfold c1. destruct (cwr_cases c rd d 1 (fun _ => s < 0 \/ cl_of c rs s) rs y)
        as [(? & _)|(_ & Hcw)]; [congruence|exact Hcw]. }
    assert (Hc1: forall y, cl_of c1 rs y = cl_of c rs y).
    { intros y. unfold cl_of. destruct rs; try reflexivity; apply Hc0. }
    destruct (cwr_cases c rd d (Z.succ (Z.of_nat k)) (fun j => s + j < 0 \/ cl_of c rs (s + j)) r x)
      as [(Hr & Hx' & Hcw)|(Hx' & Hcw)]; rewrite Hcw in Hx.
    + destruct (cwr_cases c1 rd (d + 1) (Z.of_nat k) (fun j => s + 1 + j < 0 \/ cl_of c1 rs (s + 1 + j)) r x)
        as [(_ & _ & Hcw')|(Hx'' & Hcw')]; rewrite Hcw'.
      * rewrite Hc1. replace (s + 1 + (x - (d + 1))) with (s + (x - d)) by lia. exact Hx.
      * unfold c1. destruct (cwr_cases c rd d 1 (fun _ => s < 0 \/ cl_of c rs s) r x)
          as [(_ & _ & Hcw'')|(Hx3 & _)].
        -- rewrite Hcw''. assert (x = d) by (destruct (Z.eq_dec x d); [auto|exfalso; apply Hx''; split; [auto|lia]]).
           subst x. rewrite Z.sub_diag, Z.add_0_r in Hx. exact Hx.
        -- exfalso. apply Hx3. split; [auto|]. destruct (Z.eq_dec x d); [lia|]. exfalso; apply Hx''; split; [auto|lia].
    + destruct (cwr_cases c1 rd (d + 1) (Z.of_nat k) (fun j => s + 1 + j < 0 \/ cl_of c1 rs (s + 1 + j)) r x)
        as [(Hr & Hx3 & _)|(_ & Hcw')]; [exfalso; apply Hx'; split; auto; lia|].
      rewrite Hcw'. unfold c1.
      destruct (cwr_cases c rd d 1 (fun _ => s < 0 \/ cl_of c rs s) r x) as [(Hr & Hx3 & _)|(_ & Hcw'')];
        [exfalso; apply Hx'; split; auto; lia|].
      rewrite Hcw''. exact Hx.
Qed.

(* a forward copy within the destination whose every read is of a clean cell, or of a cell the copy itself
   wrote: every cell it writes is clean *)
Lemma fwd_dd : forall src k c m1 m2 d s, rel c m1 m2 ->
  (forall j, 0 <= j < Z.of_nat k -> s + j < 0 \/ c R_dst (s + j) \/ d <= s + j < d + j) ->
  orel (rel (cwr c R_dst d (Z.of_nat k) (fun _ => True)))
       (xm_fwd src k m1 R_dst d R_dst s) (xm_fwd src k m2 R_dst d R_dst s).
Proof.
  induction k as [|k IH]; intros c m1 m2 d s HR Hpre; cbn [xm_fwd orel]; [|rewrite Nat2Z.inj_succ].
  - eapply rel_mono; [|exact HR]. intros r x Hx. apply cwr_empty in Hx; [exact Hx|lia].
  - destruct (rd_rel src c m1 m2 R_dst s HR) as [Hn He].
    destruct (xm_rd src m1 R_dst s) as [v1|] eqn:R1; destruct (xm_rd src m2 R_dst s) as [v2|] eqn:R2;
      try (exfalso; destruct Hn; intuition congruence); [|exact I].
    assert (Hv: v1 = v2).
    { specialize (Hpre 0 ltac:(lia)). rewrite Z.add_0_r in Hpre.
      assert (Hs: s < 0 \/ cl_of c R_dst s) by (simpl; destruct Hpre as [?|[?|?]]; auto; lia).
      specialize (He Hs). congruence. }
    pose proof (wr_rel c m1 m2 R_dst d v1 v2 True HR (fun _ => Hv)) as HW.
    destruct (xm_wr m1 R_dst d v1) as [m1'|]; destruct (xm_wr m2 R_dst d v2) as [m2'|]; simpl in HW;
      try contradiction; [|exact I].
    set (c1 := cwr c R_dst d 1 (fun _ => True)) in HW.
    assert (Hpre1: forall j, 0 <= j < Z.of_nat k -> s + 1 + j < 0 \/ c1 R_dst (s + 1 + j) \/
                     d + 1 <= s + 1 + j < d + 1 + j).
    { intros j Hj. destruct (Hpre (j + 1) ltac:(lia)) as [?|[?|?]].
      - left; lia.
      - right; left. apply cwr_true_sup. replace (s + 1 + j) with (s + (j + 1)) by lia. auto.
      - destruct (Z.eq_dec (s + 1 + j) d).
        + right; left. apply cwr_in; auto; lia.
        + right; right; lia. }
    specialize (IH c1 m1' m2' (d + 1) (s + 1) HW Hpre1).
    eapply orel_mono; [|exact IH]. intros a b Hab. eapply rel_mono; [|exact Hab].
    intros r x Hx. apply cwr_inv in Hx as [(Hr & Hx & _)|(Hx & Hc)].
    + destruct (Z.eq_dec x d).
      * apply cwr_true_sup. apply cwr_in; auto; lia.
      * apply cwr_in; auto; lia.
    + apply cwr_true_sup. apply cwr_out; auto. intros (? & ?); apply Hx; split; auto; lia.
Qed.

(* reading k cells: both fail, or both give k values, equal where the cell read is clean *)
Lemma rdn_rel : forall src k c m1 m2 r s, rel c m1 m2 ->
  orel (fun vs1 vs2 => length vs1 = k /\ length vs2 = k /\
          forall j, 0 <= j < Z.of_nat k -> s + j < 0 \/ cl_of c r (s + j) ->
            nth (Z.to_nat j) vs1 0 = nth (Z.to_nat j) vs2 0)
       (xm_rdn src k m1 r s) (xm_rdn src k m2 r s).
Proof.
  induction k as [|k IH]; intros c m1 m2 r s HR; cbn [xm_rdn orel].
  - split; [reflexivity|split; [reflexivity|]]. intros j Hj; simpl in Hj; lia.
  - destruct (rd_rel src c m1 m2 r s HR) as [Hn He].
    specialize (IH c m1 m2 r (s + 1) HR).
    destruct (xm_rd src m1 r s) as [v1|] eqn:R1; destruct (xm_rd src m2 r s) as [v2|] eqn:R2;
      try (exfalso; destruct Hn; intuition congruence);
    destruct (xm_rdn src k m1 r (s + 1)) as [l1|]; destruct (xm_rdn src k m2 r (s + 1)) as [l2|];
      simpl in IH |- *; try contradiction; auto.
    destruct IH as (L1 & L2 & Hl). split; [simpl; auto|split; [simpl; auto|]].
    intros j Hj Hc. rewrite ?Nat2Z.inj_succ in Hj.
    destruct (Z.eq_dec j 0).
    + subst j. simpl. rewrite Z.add_0_r in Hc. specialize (He Hc). congruence.
    + replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. simpl.
      apply Hl; [lia|]. replace (s + 1 + (j - 1)) with (s + j) by lia. exact Hc.
Qed.

(* writing two lists: cell d + j is clean when E j makes the j-th values equal *)
Lemma wrn_rel : forall vs1 vs2 c m1 m2 r d (E: Z -> Prop), rel c m1 m2 -> length vs1 = length vs2 ->
  (forall j, 0 <= j < Zlength vs1 -> E j -> nth (Z.to_nat j) vs1 0 = nth (Z.to_nat j) vs2 0) ->
  orel (rel (cwr c r d (Zlength vs1) E)) (xm_wrn vs1 m1 r d) (xm_wrn vs2 m2 r d).
Proof.
  induction vs1 as [|v1 vs1 IH]; intros [|v2 vs2] c m1 m2 r d E HR HL HE; simpl in HL; try discriminate;
    cbn [xm_wrn orel].
  - eapply rel_mono; [|exact HR]. intros r' x Hx. apply cwr_empty in Hx; [exact Hx|rewrite Zlength_nil; lia].
  - rewrite Zlength_cons in *. pose proof (Zlength_nonneg vs1).
    pose proof (wr_rel c m1 m2 r d v1 v2 (E 0) HR) as HW.
    specialize (HW ltac:(intros H0; apply (HE 0 ltac:(pose proof (Zlength_nonneg vs1); lia) H0))).
    destruct (xm_wr m1 r d v1) as [m1'|]; destruct (xm_wr m2 r d v2) as [m2'|]; simpl in HW;
      try contradiction; [|exact I].
    specialize (IH vs2 _ m1' m2' r (d + 1) (fun j => E (j + 1)) HW ltac:(lia)).
    specialize (IH ltac:(intros j Hj Hj'; pose proof (HE (j + 1) ltac:(lia) Hj') as Hq;
                         replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in Hq by lia; exact Hq)).
    eapply orel_mono; [|exact IH]. intros a b Hab. eapply rel_mono; [|exact Hab].
    intros r' x Hx. apply cwr_inv in Hx as [(Hr & Hx & HEx)|(Hx & Hc)].
    + destruct (Z.eq_dec x d).
      * subst x. apply cwr_out; [intros (? & ?); lia|]. apply cwr_in; auto; [lia|]. rewrite Z.sub_diag in HEx. auto.
      * apply cwr_in; auto; [lia|]. replace (x - (d + 1) + 1) with (x - d) by lia. auto.
    + apply cwr_out; [intros (? & ?); apply Hx; split; auto; lia|].
      apply cwr_out; [intros (? & ?); apply Hx; split; auto; lia|]. auto.
Qed.

(* a move (all cells read, then written) from any region *)
Lemma move_rel : forall src k c m1 m2 rd d rs s, rel c m1 m2 ->
  orel (rel (cwr c rd d (Z.of_nat k) (fun j => s + j < 0 \/ cl_of c rs (s + j))))
       (xm_move src k m1 rd d rs s) (xm_move src k m2 rd d rs s).
Proof.
  intros src k c m1 m2 rd d rs s HR. unfold xm_move.
  pose proof (rdn_rel src k c m1 m2 rs s HR) as HN.
  destruct (xm_rdn src k m1 rs s) as [l1|]; destruct (xm_rdn src k m2 rs s) as [l2|]; simpl in HN;
    try contradiction; [|exact I].
  destruct HN as (L1 & L2 & Hl).
  replace (Z.of_nat k) with (Zlength l1) by (rewrite Zlength_correct; congruence).
  apply wrn_rel; auto; [congruence|].
  intros j Hj HE. apply Hl; auto. rewrite Zlength_correct in Hj. lia.
Qed.

(* 16-byte chunks from litExtraBuffer or the input *)
Lemma chunks_x : forall src n c m1 m2 d rs s, rs <> R_dst -> rel c m1 m2 ->
  orel (rel (cwr c R_dst d (16 * Z.of_nat n) (fun j => s + j < 0 \/ cl_of c rs (s + j))))
       (xm_chunks16 src n m1 d rs s) (xm_chunks16 src n m2 d rs s).
Proof.
  induction n as [|n IH]; intros c m1 m2 d rs s Hne HR; cbn [xm_chunks16 orel]; [|rewrite Nat2Z.inj_succ].
  - eapply rel_mono; [|exact HR]. intros r x Hx. apply cwr_empty in Hx; [exact Hx|lia].
  - pose proof (move_rel src 16 c m1 m2 R_dst d rs s HR) as HM.
    destruct (xm_move src 16 m1 R_dst d rs s) as [m1'|]; destruct (xm_move src 16 m2 R_dst d rs s) as [m2'|];
      simpl in HM; try contradiction; [|exact I].
    set (c1 := cwr c R_dst d (Z.of_nat 16) (fun j => s + j < 0 \/ cl_of c rs (s + j))) in HM.
    specialize (IH c1 m1' m2' (d + 16) rs (s + 16) Hne HM).
    assert (Hc1: forall y, cl_of c1 rs y <-> cl_of c rs y).
    { intros y. unfold cl_of. destruct rs; try tauto; apply cwr_other; congruence. }
    eapply orel_mono; [|exact IH]. intros a b Hab. eapply rel_mono; [|exact Hab].
    intros r x Hx. apply cwr_inv in Hx as [(Hr & Hx & HEx)|(Hx & Hc)].
    + destruct (Z.lt_ge_cases x (d + 16)).
      * apply cwr_out; [intros (? & ?); lia|]. apply cwr_in; auto. simpl; lia.
      * apply cwr_in; auto; [lia|]. rewrite Hc1. replace (s + 16 + (x - (d + 16))) with (s + (x - d)) by lia.
        exact HEx.
    + apply cwr_out; [intros (? & ?); apply Hx; split; auto; lia|].
      unfold c1; apply cwr_out; [intros (? & ?); apply Hx; split; auto; lia|]. auto.
Qed.

(* 16-byte chunks within the destination, every chunk reading clean cells or cells of earlier chunks *)
Lemma chunks_dd : forall src n c m1 m2 d s, rel c m1 m2 ->
  (forall j, 0 <= j < 16 * Z.of_nat n -> s + j < 0 \/ c R_dst (s + j) \/ d <= s + j < d + 16 * (j / 16)) ->
  orel (rel (cwr c R_dst d (16 * Z.of_nat n) (fun _ => True)))
       (xm_chunks16 src n m1 d R_dst s) (xm_chunks16 src n m2 d R_dst s).
Proof.
  induction n as [|n IH]; intros c m1 m2 d s HR Hpre; cbn [xm_chunks16 orel]; [|rewrite Nat2Z.inj_succ].
  - eapply rel_mono; [|exact HR]. intros r x Hx. apply cwr_empty in Hx; [exact Hx|lia].
  - pose proof (move_rel src 16 c m1 m2 R_dst d R_dst s HR) as HM.
    destruct (xm_move src 16 m1 R_dst d R_dst s) as [m1'|]; destruct (xm_move src 16 m2 R_dst d R_dst s) as [m2'|];
      simpl in HM; try contradiction; [|exact I].
    set (c1 := cwr c R_dst d 16 (fun _ => True)).
    assert (HM1: rel c1 m1' m2').
    { eapply rel_mono; [|exact HM]. intros r x Hx. apply cwr_inv in Hx as [(Hr & Hx & _)|(Hx & Hc)].
      - apply cwr_in; auto. destruct (Hpre (x - d) ltac:(lia)) as [?|[?|?]]; [left|right|]; auto.
        rewrite Z.div_small in H by lia. lia.
      - apply cwr_out; auto. }
    assert (Hpre1: forall j, 0 <= j < 16 * Z.of_nat n -> s + 16 + j < 0 \/ c1 R_dst (s + 16 + j) \/
                     d + 16 <= s + 16 + j < d + 16 + 16 * (j / 16)).
    { intros j Hj. destruct (Hpre (j + 16) ltac:(lia)) as [?|[?|?]].
      - left; lia.
      - right; left. apply cwr_true_sup. replace (s + 16 + j) with (s + (j + 16)) by lia. auto.
      - replace ((j + 16) / 16) with (j / 16 + 1) in H by
          (rewrite <- (Z.div_add j 1 16) by lia; f_equal; lia).
        destruct (Z.lt_ge_cases (s + 16 + j) (d + 16)).
        + right; left. apply cwr_in; auto; lia.
        + right; right; lia. }
    specialize (IH c1 m1' m2' (d + 16) (s + 16) HM1 Hpre1).
    eapply orel_mono; [|exact IH]. intros a b Hab. eapply rel_mono; [|exact Hab].
    intros r x Hx. apply cwr_inv in Hx as [(Hr & Hx & _)|(Hx & Hc)].
    + destruct (Z.lt_ge_cases x (d + 16)).
      * apply cwr_true_sup. apply cwr_in; auto; lia.
      * apply cwr_in; auto; lia.
    + apply cwr_true_sup. apply cwr_out; auto. intros (? & ?); apply Hx; split; auto; lia.
Qed.
