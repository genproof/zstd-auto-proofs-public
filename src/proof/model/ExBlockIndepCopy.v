(* zstd's composite copies (ExBlock.xm_wild, xm_ov8, xm_safecopy, xm_sdbs, xm_prefix, xm_match) on two related
   memories (ExBlockIndepMem.rel), in the three ways a block uses them:
   - a match in a one-shot destination (prefixStart = virtualStart = 0) with an offset >= 1: every cell it reads
     is below its write pointer or was written by the same copy, so when the output so far [0, op) is clean,
     the match's cells are clean too (and nothing clean becomes dirty);
   - literals copied from the destination or the block's input while the whole destination is clean: the whole
     destination stays clean;
   - literals copied from litExtraBuffer: the cells below the copy stay clean, and the literals' cells are clean
     when the literals they read were (the wild-copy overshoot past them may not be).
   Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeBlkDefs Zstd.proof.model.ExBlockIndepMem.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* every destination cell clean *)
Definition Aall (c: creg) : Prop := forall x, c R_dst x.
(* the destination cells [0, P) clean *)
Definition PC (c: creg) (P: Z) : Prop := forall x, 0 <= x < P -> c R_dst x.

(* related, nothing clean became dirty *)
Definition RC (c: creg) (m1 m2: xmem) : Prop := exists c', rel c' m1 m2 /\ cle c c'.
(* ... and [0, P) clean *)
Definition RM (c: creg) (P: Z) (m1 m2: xmem) : Prop := exists c', rel c' m1 m2 /\ cle c c' /\ PC c' P.
(* a copy of len literals from litExtraBuffer at s to the destination at d: litExtraBuffer and the cells below d
   keep their clean cells, and [d, d + len) is clean when the literals read are *)
Definition RL (c: creg) (d s len: Z) (m1 m2: xmem) : Prop :=
  exists c', rel c' m1 m2 /\ (forall x, c R_lxb x -> c' R_lxb x) /\ (forall x, x < d -> c R_dst x -> c' R_dst x) /\
    ((forall j, 0 <= j < len -> s + j < 0 \/ c R_lxb (s + j)) -> forall x, d <= x < d + len -> c' R_dst x).

Lemma cle_refl : forall c, cle c c.
Proof. intros c r x H; exact H. Qed.

Lemma cle_trans : forall c1 c2 c3, cle c1 c2 -> cle c2 c3 -> cle c1 c3.
Proof. intros c1 c2 c3 H1 H2 r x H. auto. Qed.

Lemma cwr_cle : forall c r d k (E: Z -> Prop), (forall j, E j) -> cle c (cwr c r d k E).
Proof.
  intros c r d k E HE r' x Hc.
  destruct (cwr_cases c r d k E r' x) as [(? & ? & Hcw)|(? & Hcw)]; rewrite Hcw; auto.
Qed.

Lemma PC_mono : forall c P P', PC c P -> P' <= P -> PC c P'.
Proof. intros c P P' H HP x Hx. apply H. lia. Qed.

Lemma PC_cle : forall c c' P, PC c P -> cle c c' -> PC c' P.
Proof. intros c c' P H Hc x Hx. apply Hc, H, Hx. Qed.

Lemma RC_cle : forall c c1 o1 o2, cle c c1 -> orel (RC c1) o1 o2 -> orel (RC c) o1 o2.
Proof.
  intros c c1 o1 o2 Hc H. eapply orel_mono; [|exact H]. intros a b (c' & Hr & Hc'). exists c'.
  split; auto. eapply cle_trans; eauto.
Qed.

Lemma RM_cle : forall c c1 P o1 o2, cle c c1 -> orel (RM c1 P) o1 o2 -> orel (RM c P) o1 o2.
Proof.
  intros c c1 P o1 o2 Hc H. eapply orel_mono; [|exact H]. intros a b (c' & Hr & Hc' & HP). exists c'.
  split; auto. split; auto. eapply cle_trans; eauto.
Qed.

Lemma RM_mono : forall c P P' o1 o2, P' <= P -> orel (RM c P) o1 o2 -> orel (RM c P') o1 o2.
Proof.
  intros c P P' o1 o2 HP H. eapply orel_mono; [|exact H]. intros a b (c' & Hr & Hc' & HP').
  exists c'. split; [auto|split; [auto|eapply PC_mono; eauto]].
Qed.

(* destruct two related optional results *)
Ltac odest H :=
  let a := fresh "ma" in let b := fresh "mb" in
  match type of H with
  | orel _ ?o1 ?o2 => destruct o1 as [a|]; destruct o2 as [b|]; cbn [orel] in H; try contradiction; [|exact I]
  end.

Lemma nat_cnt : forall k, Z.of_nat (Z.to_nat k) = Z.max 0 k.
Proof. intros k. lia. Qed.

(* ---------- literals while the whole destination is clean ---------- *)

Lemma fwd_A : forall src k c m1 m2 d rs s, rel c m1 m2 -> (rs = R_src \/ (rs = R_dst /\ Aall c)) ->
  orel (RC c) (xm_fwd src k m1 R_dst d rs s) (xm_fwd src k m2 R_dst d rs s).
Proof.
  intros src k c m1 m2 d rs s HR [->|[-> HA]].
  - pose proof (fwd_x src k c m1 m2 R_dst d R_src s ltac:(discriminate) HR) as H.
    eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. apply cwr_cle. intros; right; exact I.
  - pose proof (fwd_dd src k c m1 m2 d s HR ltac:(intros; right; left; apply HA)) as H.
    eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. apply cwr_cle. auto.
Qed.

Lemma move_A : forall src k c m1 m2 d rs s, rel c m1 m2 -> (rs = R_src \/ (rs = R_dst /\ Aall c)) ->
  orel (RC c) (xm_move src k m1 R_dst d rs s) (xm_move src k m2 R_dst d rs s).
Proof.
  intros src k c m1 m2 d rs s HR Hrs.
  pose proof (move_rel src k c m1 m2 R_dst d rs s HR) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. apply cwr_cle.
  intros j; right. destruct Hrs as [->|[-> HA]]; [exact I|apply HA].
Qed.

Lemma chunks_A : forall src n c m1 m2 d rs s, rel c m1 m2 -> (rs = R_src \/ (rs = R_dst /\ Aall c)) ->
  orel (RC c) (xm_chunks16 src n m1 d rs s) (xm_chunks16 src n m2 d rs s).
Proof.
  intros src n c m1 m2 d rs s HR [->|[-> HA]].
  - pose proof (chunks_x src n c m1 m2 d R_src s ltac:(discriminate) HR) as H.
    eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. apply cwr_cle. intros; right; exact I.
  - pose proof (chunks_dd src n c m1 m2 d s HR ltac:(intros; right; left; apply HA)) as H.
    eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. apply cwr_cle. auto.
Qed.

Lemma wild_A : forall src c m1 m2 d rs s len b, rel c m1 m2 -> (rs = R_src \/ (rs = R_dst /\ Aall c)) ->
  orel (RC c) (xm_wild src m1 d rs s len b) (xm_wild src m2 d rs s len b).
Proof.
  intros src c m1 m2 d rs s len b HR Hrs. unfold xm_wild.
  destruct (b && (d - s <? 16)); [apply fwd_A|apply chunks_A]; auto.
Qed.

(* chaining: a second copy on the results of a first, the destination still all clean *)
Lemma RC_A : forall c c', Aall c -> cle c c' -> Aall c'.
Proof. intros c c' HA Hc x. apply Hc, HA. Qed.

Lemma safecopy_A : forall src c m1 m2 op w rs ip len, rel c m1 m2 -> Aall c -> rs <> R_lxb ->
  orel (RC c) (xm_safecopy src m1 op w rs ip len false) (xm_safecopy src m2 op w rs ip len false).
Proof.
  intros src c m1 m2 op w rs ip len HR HA Hrs.
  assert (Hrs': forall c', Aall c' -> rs = R_src \/ (rs = R_dst /\ Aall c')) by (destruct rs; auto; congruence).
  unfold xm_safecopy.
  destruct (len <? 8); [apply fwd_A; auto|].
  cbv iota beta.
  destruct (w - (op + len) >=? 0); [apply wild_A; auto|].
  destruct (w - op >=? 0).
  - pose proof (wild_A src c m1 m2 op rs ip (w - op) false HR (Hrs' c HA)) as H.
    odest H. destruct H as (c1 & H1 & Hc1).
    eapply RC_cle; [exact Hc1|]. apply fwd_A; auto. apply Hrs'. eapply RC_A; eauto.
  - apply fwd_A; auto.
Qed.

Lemma sdbs_A : forall src c m1 m2 op ip len, rel c m1 m2 -> Aall c ->
  orel (RC c) (xm_sdbs src m1 op ip len) (xm_sdbs src m2 op ip len).
Proof.
  intros src c m1 m2 op ip len HR HA. unfold xm_sdbs.
  destruct ((len <? 8) || (op - ip >? -8)); [apply fwd_A; auto|].
  destruct ((len >=? 32) && (op - ip <? -16)).
  - pose proof (wild_A src c m1 m2 op R_dst ip (len - 32) false HR (or_intror (conj eq_refl HA))) as H.
    odest H. destruct H as (c1 & H1 & Hc1).
    eapply RC_cle; [exact Hc1|]. apply fwd_A; auto. right; split; auto. eapply RC_A; eauto.
  - apply fwd_A; auto.
Qed.

(* ---------- a match: every read below the write pointer or of a cell the copy wrote ---------- *)

Lemma fwd_M : forall src k c m1 m2 d s, rel c m1 m2 -> PC c d -> 1 <= d - s ->
  orel (RM c (d + Z.of_nat k)) (xm_fwd src k m1 R_dst d R_dst s) (xm_fwd src k m2 R_dst d R_dst s).
Proof.
  intros src k c m1 m2 d s HR HP Hd.
  assert (Hpre: forall j, 0 <= j < Z.of_nat k -> s + j < 0 \/ c R_dst (s + j) \/ d <= s + j < d + j).
  { intros j Hj. destruct (Z.lt_ge_cases (s + j) 0); [left; lia|].
    destruct (Z.lt_ge_cases (s + j) d); [right; left; apply HP; lia|right; right; lia]. }
  pose proof (fwd_dd src k c m1 m2 d s HR Hpre) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. split.
  - apply cwr_cle; auto.
  - intros x Hx. destruct (Z.lt_ge_cases x d).
    + apply cwr_true_sup, HP; lia.
    + apply cwr_in; auto; lia.
Qed.

Lemma chunks_M : forall src n c m1 m2 d s, rel c m1 m2 -> PC c d -> 16 <= d - s ->
  orel (RM c (d + 16 * Z.of_nat n)) (xm_chunks16 src n m1 d R_dst s) (xm_chunks16 src n m2 d R_dst s).
Proof.
  intros src n c m1 m2 d s HR HP Hd.
  assert (Hpre: forall j, 0 <= j < 16 * Z.of_nat n -> s + j < 0 \/ c R_dst (s + j) \/
                  d <= s + j < d + 16 * (j / 16)).
  { intros j Hj. destruct (Z.lt_ge_cases (s + j) 0); [left; lia|].
    destruct (Z.lt_ge_cases (s + j) d); [right; left; apply HP; lia|right; right].
    pose proof (Z.div_mod j 16 ltac:(lia)). pose proof (Z.mod_pos_bound j 16 ltac:(lia)). lia. }
  pose proof (chunks_dd src n c m1 m2 d s HR Hpre) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eexists; split; [exact Hab|]. split.
  - apply cwr_cle; auto.
  - intros x Hx. destruct (Z.lt_ge_cases x d).
    + apply cwr_true_sup, HP; lia.
    + apply cwr_in; auto; lia.
Qed.

Lemma wild_cnt8 : forall len, len <= Z.of_nat (Z.to_nat (8 * Z.max 1 ((len + 7) / 8))).
Proof.
  intros len. pose proof (Z.div_mod (len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma wild_cnt16 : forall len,
  len <= 16 * Z.of_nat (Z.to_nat (if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32))).
Proof.
  intros len. destruct (Z.leb_spec len 16); [lia|].
  pose proof (Z.div_mod (len - 16 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (len - 16 + 31) 32 ltac:(lia)).
  assert (0 <= (len - 16 + 31) / 32) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma wild_M : forall src c m1 m2 d s len b, rel c m1 m2 -> PC c d -> 1 <= d - s -> (b = false -> 16 <= d - s) ->
  orel (RM c (d + len)) (xm_wild src m1 d R_dst s len b) (xm_wild src m2 d R_dst s len b).
Proof.
  intros src c m1 m2 d s len b HR HP Hd Hb. unfold xm_wild.
  destruct (b && (d - s <? 16)) eqn:E.
  - eapply RM_mono; [|apply fwd_M; auto]. pose proof (wild_cnt8 len). lia.
  - eapply RM_mono; [|apply chunks_M; auto].
    + pose proof (wild_cnt16 len). lia.
    + destruct b; [|auto]. simpl in E. apply Z.ltb_ge in E. lia.
Qed.

(* ZSTD_overlapCopy8: op advances by 8, the distance op - ip stays >= 1 (8 to 14 for offsets below 8) *)
Lemma ov8_M : forall src c m1 m2 op ip off, off = op - ip -> rel c m1 m2 -> PC c op -> 1 <= op - ip ->
  orel (fun a b => let '(m1', o1, i1) := a in let '(m2', o2, i2) := b in
                   o1 = o2 /\ i1 = i2 /\ o1 = op + 8 /\ 1 <= o1 - i1 /\ RM c o1 m1' m2')
       (xm_ov8 src m1 op ip off) (xm_ov8 src m2 op ip off).
Proof.
  intros src c m1 m2 op ip off -> HR HP Hd. unfold xm_ov8.
  destruct (Z.ltb_spec (op - ip) 8).
  - pose proof (fwd_M src 4 c m1 m2 op ip HR HP Hd) as H0. odest H0. destruct H0 as (c1 & H1 & Hc1 & HP1).
    assert (Hdec: xdec32 (op - ip) < op - ip + 4 /\ 1 <= op - ip - xdec32 (op - ip) + xdec64 (op - ip)).
    { assert (op - ip = 1 \/ op - ip = 2 \/ op - ip = 3 \/ op - ip = 4 \/ op - ip = 5 \/ op - ip = 6 \/
              op - ip = 7) as Hc by lia.
      destruct Hc as [E|[E|[E|[E|[E|[E|E]]]]]]; rewrite E; cbv; split; congruence. }
    pose proof (fwd_M src 4 c1 ma mb (op + 4) (ip + xdec32 (op - ip)) H1 HP1 ltac:(lia)) as H2.
    odest H2. destruct H2 as (c2 & H2 & Hc2 & HP2).
    cbn [orel]. split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [lia|]]]].
    exists c2. split; auto. split; [eapply cle_trans; eauto|]. eapply PC_mono; [exact HP2|lia].
  - pose proof (fwd_M src 8 c m1 m2 op ip HR HP Hd) as H0. odest H0. destruct H0 as (c1 & H1 & Hc1 & HP1).
    cbn [orel]. split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [lia|]]]].
    exists c1. split; auto.
Qed.

Lemma safecopy_M : forall src c m1 m2 op w ip len, rel c m1 m2 -> PC c op -> 1 <= op - ip ->
  orel (RM c (op + len)) (xm_safecopy src m1 op w R_dst ip len true) (xm_safecopy src m2 op w R_dst ip len true).
Proof.
  intros src c m1 m2 op w ip len HR HP Hd. unfold xm_safecopy.
  destruct (Z.ltb_spec len 8).
  - eapply RM_mono; [|apply fwd_M; auto]. lia.
  - cbv beta iota zeta.
    pose proof (ov8_M src c m1 m2 op ip (op - ip) eq_refl HR HP Hd) as H0.
    destruct (xm_ov8 src m1 op ip (op - ip)) as [[[ma o1] i1]|];
      destruct (xm_ov8 src m2 op ip (op - ip)) as [[[mb o2] i2]|]; cbn [orel] in H0; try contradiction; [|exact I].
    destruct H0 as (<- & <- & -> & Hd1 & (c1 & H1 & Hc1 & HP1)).
    eapply RM_cle; [exact Hc1|].
    destruct (Z.geb_spec (w - (op + len)) 0).
    + eapply RM_mono; [|apply wild_M; auto; discriminate]. lia.
    + destruct (Z.geb_spec (w - (op + 8)) 0).
      * pose proof (wild_M src c1 ma mb (op + 8) i1 (w - (op + 8)) true H1 HP1 Hd1 ltac:(discriminate)) as Hw.
        odest Hw. destruct Hw as (c2 & Hw & Hc2 & HP2).
        eapply RM_cle; [exact Hc2|]. eapply RM_mono; [|apply fwd_M; auto].
        -- lia.
        -- eapply PC_mono; [exact HP2|lia].
        -- lia.
      * eapply RM_mono; [|apply fwd_M; auto]. lia.
Qed.

Lemma prefix_M : forall e c m1 m2 op ml off wo, rel c m1 m2 -> PC c op -> 1 <= off ->
  orel (RM c (op + ml)) (xm_prefix e m1 op (op - off) ml off wo) (xm_prefix e m2 op (op - off) ml off wo).
Proof.
  intros e c m1 m2 op ml off wo HR HP Hoff. unfold xm_prefix.
  destruct wo as [w|].
  - apply safecopy_M; auto. lia.
  - destruct (Z.geb_spec off 16).
    + apply wild_M; auto; lia.
    + pose proof (ov8_M (xe_src e) c m1 m2 op (op - off) off ltac:(lia) HR HP ltac:(lia)) as H0.
      destruct (xm_ov8 (xe_src e) m1 op (op - off) off) as [[[ma o1] i1]|];
        destruct (xm_ov8 (xe_src e) m2 op (op - off) off) as [[[mb o2] i2]|]; cbn [orel] in H0;
        try contradiction; [|exact I].
      destruct H0 as (<- & <- & -> & Hd1 & (c1 & H1 & Hc1 & HP1)).
      destruct (Z.gtb_spec ml 8).
      * eapply RM_cle; [exact Hc1|]. eapply RM_mono; [|apply wild_M; auto; discriminate]. lia.
      * cbn [orel]. exists c1. split; auto. split; auto. eapply PC_mono; [exact HP1|lia].
Qed.

(* the match of a sequence in a one-shot destination without dictionary *)
Lemma match_M : forall e c m1 m2 oLitEnd ml off wo, xe_ps e = 0 -> xe_vs e = 0 -> rel c m1 m2 ->
  PC c oLitEnd -> 1 <= off ->
  orel (RM c (oLitEnd + ml)) (xm_match e m1 oLitEnd ml off wo) (xm_match e m2 oLitEnd ml off wo).
Proof.
  intros e c m1 m2 oLitEnd ml off wo Hps Hvs HR HP Hoff. unfold xm_match. rewrite Hps, Hvs, !Z.sub_0_r.
  destruct (Z.gtb_spec off oLitEnd); [exact I|].
  apply prefix_M; auto.
Qed.

(* ---------- literals from litExtraBuffer ---------- *)

Lemma cwr_RL : forall c m1 m2 d s K len,
  rel (cwr c R_dst d K (fun j => s + j < 0 \/ cl_of c R_lxb (s + j))) m1 m2 -> len <= K -> RL c d s len m1 m2.
Proof.
  intros c m1 m2 d s K len HR HK. eexists; split; [exact HR|]. split; [|split].
  - intros x Hx. apply cwr_other; [discriminate|exact Hx].
  - intros x Hx Hc. apply cwr_out; auto. intros (_ & ?); lia.
  - intros Hl x Hx. apply cwr_in; auto; [lia|]. apply (Hl (x - d)). lia.
Qed.

Lemma fwd_L : forall src k c m1 m2 d s len, rel c m1 m2 -> len <= Z.of_nat k ->
  orel (RL c d s len) (xm_fwd src k m1 R_dst d R_lxb s) (xm_fwd src k m2 R_dst d R_lxb s).
Proof.
  intros src k c m1 m2 d s len HR Hk.
  pose proof (fwd_x src k c m1 m2 R_dst d R_lxb s ltac:(discriminate) HR) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eapply cwr_RL; eauto.
Qed.

Lemma move_L : forall src k c m1 m2 d s len, rel c m1 m2 -> len <= Z.of_nat k ->
  orel (RL c d s len) (xm_move src k m1 R_dst d R_lxb s) (xm_move src k m2 R_dst d R_lxb s).
Proof.
  intros src k c m1 m2 d s len HR Hk.
  pose proof (move_rel src k c m1 m2 R_dst d R_lxb s HR) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eapply cwr_RL; eauto.
Qed.

Lemma wild_L : forall src c m1 m2 d s len, rel c m1 m2 ->
  orel (RL c d s len) (xm_wild src m1 d R_lxb s len false) (xm_wild src m2 d R_lxb s len false).
Proof.
  intros src c m1 m2 d s len HR. unfold xm_wild. cbn [andb].
  pose proof (chunks_x src (Z.to_nat (if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32))) c m1 m2 d R_lxb s
                ltac:(discriminate) HR) as H.
  eapply orel_mono; [|exact H]. intros a b Hab. eapply cwr_RL; [exact Hab|]. apply wild_cnt16.
Qed.

Lemma safecopy_L : forall src c m1 m2 op w ip len, rel c m1 m2 ->
  orel (RL c op ip len) (xm_safecopy src m1 op w R_lxb ip len false) (xm_safecopy src m2 op w R_lxb ip len false).
Proof.
  intros src c m1 m2 op w ip len HR. unfold xm_safecopy.
  destruct (Z.ltb_spec len 8).
  - apply fwd_L; auto. lia.
  - cbv beta iota zeta.
    destruct (Z.geb_spec (w - (op + len)) 0); [apply wild_L; auto|].
    destruct (Z.geb_spec (w - op) 0).
    + pose proof (wild_L src c m1 m2 op ip (w - op) HR) as Hw1. odest Hw1.
      destruct Hw1 as (c1 & Hw1 & Hl1 & Hb1 & Hr1).
      pose proof (fwd_x src (Z.to_nat (op + len - w)) c1 ma mb R_dst w R_lxb (ip + (w - op))
                    ltac:(discriminate) Hw1) as Hw2.
      eapply orel_mono; [|exact Hw2]. intros a b Hab. eexists; split; [exact Hab|]. split; [|split].
      * intros x Hx. apply cwr_other; [discriminate|]. auto.
      * intros x Hx Hc. apply cwr_out; [intros (_ & ?); lia|]. auto.
      * intros Hl x Hx. destruct (Z.lt_ge_cases x w).
        -- apply cwr_out; [intros (_ & ?); lia|]. apply Hr1; [|lia].
           intros j Hj. apply Hl. lia.
        -- apply cwr_in; auto; [lia|]. simpl.
           destruct (Hl (x - op) ltac:(lia)) as [?|?]; [left; lia|right].
           replace (ip + (w - op) + (x - w)) with (ip + (x - op)) by lia. auto.
    + apply fwd_L; auto. lia.
Qed.
