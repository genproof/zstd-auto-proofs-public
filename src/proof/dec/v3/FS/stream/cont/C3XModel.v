(* ZSTD_decompressContinue exactly: facts of the block decoder's model (model/ExBlock.v's x_block at model/Exact.v's
   instance xblock) that the streaming call needs beyond DecIface.block_exact.  Plain Coq.

   - the region a compressed block returns is never shorter than the one it was given (its written cells only
     grow), so with the C's output array of the region's length it is exactly that array;
   - without an extDict (dictStart = dictEnd) the block does not depend on where that empty extDict is: the C
     (DecIface.hc_region of ExtNone) places it at prefixStart, ExStream.d_hist at op;
   - with no room (capacity 0) a block's outcome depends neither on the region nor on the history pointers, and a
     success writes nothing (the streaming call with capacity 0 passes the C decoder an empty window). *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Lia.
Require Import Zstd.proof.model.Bytes.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact Zstd.proof.model.ExBlockWritten.
Require Import Zstd.proof.model.ExAgreeBlkDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the region after a compressed block is at least as long as before *)
Lemma xblock_len_ge (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  0 <= op <= Zlength mem ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  Zlength mem <= Zlength m'.
Proof.
  intros Hop H. unfold xblock, x_block in H. cbv zeta in H.
  destruct (Z.gtb_spec (Zlength body) bsm) as [Hb|Hb]; [discriminate|]. revert H.
  match goal with |- context [match x_lits ?a ?b ?c ?d ?e ?f ?g with _ => _ end] =>
    destruct (x_lits a b c d e f g) as [[[lits lused] huf]|] eqn:El; [|discriminate] end.
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|discriminate].
  destruct ((nbSeq >? 0) && (cap =? 0))%bool; [discriminate|].
  destruct (x_lits_store body lits lused {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf st |} op
              (Z.min bsm cap) bsm cap str) as [[[[[m lr] li] lim] sp]|] eqn:Es; [|discriminate].
  apply lits_len in El.
  apply lits_store_wf in Es; [|lia|rewrite Zlength_correct in Hb; lia|intros; unfold XLITEXTRA in *; lia].
  destruct Es as [W0 I0].
  (* the initial region's cells are all written, and no store unwrites one *)
  assert (A0: allsome {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf st |} (Zlength mem)).
  { intros k Hk. unfold dcell. cbn [xm_dst].
    rewrite (nth_indep _ None (Some 0)) by (rewrite map_length; rewrite Zlength_correct in Hk; lia).
    rewrite map_nth. discriminate. }
  assert (Fin: forall m1, allsome m1 (Zlength mem) -> Zlength mem <= Zlength (x_written (xm_dst m1))).
  { intros m1 A. apply written_len. intros k Hk. exact (A k Hk). }
  destruct W0 as (_ & _ & W0 & _).
  destruct (nbSeq =? 0).
  - match goal with |- context [match x_last ?e ?s with _ => _ end] =>
      destruct (x_last e s) as [[m1 op1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply last_wf in Ex; [|cbn [xli xlim]; lia]. destruct Ex as (W & _).
    apply Fin. destruct W as (_ & _ & W & _). apply W, W0, A0.
  - destruct tabs as [t|]; [|discriminate].
    match goal with |- context [match x_seqs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 with _ => _ end] =>
      destruct (x_seqs a1 a2 a3 a4 a5 a6 a7 a8) as [[[m1 op1] rep1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply seqs_wf in Ex; [|cbn [xli xlim]; lia]. destruct Ex as (W & _).
    apply Fin. destruct W as (_ & _ & W & _). apply W, W0, A0.
Qed.

(* ---------- an empty extDict ---------- *)

(* two environments of the block's execution that agree on everything but dictEnd, both without an extDict
   (virtualStart = prefixStart): dictEnd is read only for a match reaching below prefixStart, which is then
   beyond virtualStart, an error in both *)
Definition xe_noext (e1 e2: xenv) : Prop :=
  xe_src e1 = xe_src e2 /\ xe_ps e1 = xe_ps e2 /\ xe_oend e1 = xe_oend e2 /\
  xe_vs e1 = xe_ps e1 /\ xe_vs e2 = xe_ps e2.

(* destructs the scrutinees shared by both sides, rewriting with the given equations in between *)
Local Ltac dmatch_with rw :=
  repeat (rw; match goal with |- context [match ?x with _ => _ end] => destruct x end); rw; try reflexivity.

Lemma xm_match_noext e1 e2 : xe_noext e1 e2 ->
  forall m o ml off wo, xm_match e1 m o ml off wo = xm_match e2 m o ml off wo.
Proof.
  intros (Hs & Hp & Ho & H1 & H2) m o ml off wo. unfold xm_match. rewrite H1, H2, Hp.
  destruct (off >? o - xe_ps e2); [reflexivity|]. unfold xm_prefix. rewrite Hs. reflexivity.
Qed.

Lemma x_exec_noext e1 e2 : xe_noext e1 e2 ->
  forall m op lr li llim ll ml off, x_exec e1 m op lr li llim ll ml off = x_exec e2 m op lr li llim ll ml off.
Proof.
  intros H. pose proof (xm_match_noext _ _ H) as Hm. destruct H as (Hs & _ & Ho & _ & _).
  intros. unfold x_exec. rewrite Hs, Ho. dmatch_with ltac:(rewrite ?Hm).
Qed.

Lemma x_exec_split_noext e1 e2 : xe_noext e1 e2 ->
  forall m op li llim ll ml off, x_exec_split e1 m op li llim ll ml off = x_exec_split e2 m op li llim ll ml off.
Proof.
  intros H. pose proof (xm_match_noext _ _ H) as Hm. destruct H as (Hs & _ & Ho & _ & _).
  intros. unfold x_exec_split. rewrite Hs, Ho. dmatch_with ltac:(rewrite ?Hm).
Qed.

Lemma x_step_noext e1 e2 : xe_noext e1 e2 -> forall s ll ml off, x_step e1 s ll ml off = x_step e2 s ll ml off.
Proof.
  intros H. pose proof (x_exec_noext _ _ H) as He. pose proof (x_exec_split_noext _ _ H) as Hx.
  destruct H as (Hs & _ & Ho & _ & _).
  intros. unfold x_step. rewrite Hs, Ho. dmatch_with ltac:(rewrite ?He, ?Hx).
Qed.

Lemma x_seq_loop_noext dso co e1 e2 : xe_noext e1 e2 -> forall tLL tOF tML V k st pos rep s,
  x_seq_loop dso co e1 tLL tOF tML V k st pos rep s = x_seq_loop dso co e2 tLL tOF tML V k st pos rep s.
Proof.
  intros H. pose proof (x_step_noext _ _ H) as Hst. intros tLL tOF tML V k.
  induction k as [|k IH]; intros st pos rep s; [reflexivity|].
  cbn [x_seq_loop]. dmatch_with ltac:(rewrite ?Hst, ?IH).
Qed.

Lemma x_last_noext e1 e2 : xe_noext e1 e2 -> forall s, x_last e1 s = x_last e2 s.
Proof.
  intros (Hs & _ & Ho & _ & _) s. unfold x_last. rewrite Hs, Ho. reflexivity.
Qed.

Lemma x_seqs_noext dso co e1 e2 : xe_noext e1 e2 -> forall tabs rep bits nbSeq s0,
  x_seqs dso co e1 tabs rep bits nbSeq s0 = x_seqs dso co e2 tabs rep bits nbSeq s0.
Proof.
  intros H. pose proof (x_seq_loop_noext dso co _ _ H) as Hl. pose proof (x_last_noext _ _ H) as Hx.
  intros. unfold x_seqs. dmatch_with ltac:(rewrite ?Hl, ?Hx).
Qed.

(* rewrites the last literals or the sequences run in one environment to the other (x_block's two environments,
   closed once the matches they depend on are destructed) *)
Local Ltac rw_noext :=
  match goal with
  | |- context [x_last ?e1 _] =>
      match goal with |- context [x_last ?e2 _] =>
        tryif constr_eq e1 e2 then fail else rewrite (x_last_noext e1 e2) by (repeat split; cbn; lia) end
  | |- context [x_seqs _ _ ?e1 _ _ _ _ _] =>
      match goal with |- context [x_seqs _ _ ?e2 _ _ _ _ _] =>
        tryif constr_eq e1 e2 then fail else rewrite (x_seqs_noext _ _ e1 e2) by (repeat split; cbn; lia) end
  end.

(* an empty extDict: its position does not matter *)
Lemma xblock_noext (st: xstate) (mem: list Z) (ps op a b: Z) (body: list Z) (bsm cap: Z) (str: bool) :
  xblock st mem ps op a a body bsm cap str = xblock st mem ps op b b body bsm cap str.
Proof.
  unfold xblock, x_block.
  (* the scrutinees of x_block's two environments differ until they are rewritten: never destruct those *)
  repeat (cbv zeta; try rw_noext;
          match goal with |- context [match ?x with _ => _ end] =>
            lazymatch x with context [x_last] => fail | context [x_seqs] => fail | _ => destruct x end end).
  all: cbv zeta; try rw_noext; dmatch_with ltac:(idtac).
Qed.

(* the stores of an empty literals section with no room, for either streaming flag: none; the literal pointer
   does not depend on the destination *)
Lemma c3x_store0: forall body lused bsm (str: bool), 0 <= bsm ->
  exists lr li, forall m op, x_lits_store body [] lused m op 0 bsm 0 str = Some (m, lr, li, li, false).
Proof.
  intros body lused bsm str Hb. unfold x_lits_store, x_alloc_loc. rewrite Zlength_nil.
  replace (0 >? bsm + XWILDCOPY + 0 + XWILDCOPY) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold XWILDCOPY; lia).
  rewrite Bool.andb_false_r.
  change (0 <=? XLITEXTRA) with true. cbn [xl_is_split].
  destruct (Z.land (byte_at body 0) 3 =? 0).
  - destruct (lused + XWILDCOPY <=? Zlength body).
    + exists R_src, (lused - 0). intros m op. rewrite Z.add_0_r. reflexivity.
    + exists R_lxb, 0. intros m op. reflexivity.
  - destruct (Z.land (byte_at body 0) 3 =? 1); exists R_lxb, 0; intros m op; reflexivity.
Qed.

(* the last literals when none are left: nothing copied *)
Lemma c3x_last0: forall e s, xsp s = false -> xlim s = xli s -> xop s <= xe_oend e ->
  x_last e s = Some (xmm s, xop s).
Proof.
  intros e s Hsp Hl Ho. unfold x_last. rewrite Hsp. rewrite Hl, Z.sub_diag.
  replace (0 >? xe_oend e - xop s) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  cbn. rewrite Z.add_0_r. reflexivity.
Qed.

(* nothing written: the cells of a region all defined read back as the region *)
Lemma c3x_written_map: forall mem, x_written (map Some mem) = mem.
Proof. induction mem as [|x mem IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* no room: the outcome is the same for any region and history pointers, and a success writes nothing *)
Lemma xblock_cap0 (st: xstate) mem1 ps1 op1 ds1 de1 mem2 ps2 op2 ds2 de2 (body: list Z) (bsm: Z) (str: bool) :
  0 <= bsm ->
  match xblock st mem1 ps1 op1 ds1 de1 body bsm 0 str, xblock st mem2 ps2 op2 ds2 de2 body bsm 0 str with
  | None, None => True
  | Some (a, m1, n1), Some (b, m2, n2) => a = b /\ m1 = mem1 /\ m2 = mem2 /\ n1 = 0 /\ n2 = 0
  | _, _ => False
  end.
Proof.
  intros Hbsm. unfold xblock, x_block.
  destruct (Z.gtb_spec (Zlength body) bsm) as [Hb|Hb]; [exact I|].
  pose proof (Zlength_correct body) as Hb0.
  replace (Z.min bsm 0) with 0 by lia.
  destruct (x_lits xhuf x_lits_huf (x_huf xhuf st) body bsm 0 str) as [[[lits lused] huf]|] eqn:El; [|exact I].
  pose proof (lits_len _ _ _ _ _ _ _ _ El) as Hl.
  destruct lits as [|x lits]; [| rewrite Zlength_correct in Hl; cbn [length] in Hl; lia].
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|exact I].
  destruct (Z.gtb_spec nbSeq 0) as [Hn|Hn]; cbn [andb Z.eqb]; [exact I|].
  destruct (c3x_store0 body lused bsm str Hbsm) as (lr & li & Hs). rewrite !Hs.
  assert (Hloc: forall op, op <= match x_litloc body lused (Zlength (@nil Z)) bsm 0 str with
                                 | XL_in_dst => op + bsm + XWILDCOPY | _ => op + 0 end).
  { intros op. unfold x_litloc, x_alloc_loc. rewrite Zlength_nil.
    destruct (_ && _)%bool; [lia|].
    replace (0 >? bsm + XWILDCOPY + 0 + XWILDCOPY) with false
      by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold XWILDCOPY; lia).
    rewrite Bool.andb_false_r. change (0 <=? XLITEXTRA) with true. cbn. lia. }
  destruct (nbSeq =? 0) eqn:E0.
  - rewrite !c3x_last0 by (cbn; first [reflexivity | apply Hloc]).
    cbn [xmm xop xm_lxb xm_dst]. rewrite !c3x_written_map, !Z.sub_diag. auto.
  - apply Z.eqb_neq in E0. destruct tabs as [tb|]; [|exact I].
    unfold x_seqs. destruct tb as [[tLL tOF] tML]. cbv beta iota.
    destruct (negb (Bitstream.bs_okb _)); [exact I|].
    replace (Z.to_nat nbSeq) with O by lia.
    repeat match goal with |- context [match Block.rd ?a ?b ?c with _ => _ end] =>
      destruct (Block.rd a b c) as [[? ?]|]; [|exact I] end.
    cbn [x_seq_loop].
    match goal with |- context [negb (?p =? 0)] => destruct (negb (p =? 0)); [exact I|] end.
    rewrite !c3x_last0 by (cbn; first [reflexivity | apply Hloc]).
    cbn [xmm xop xm_lxb xm_dst]. rewrite !c3x_written_map, !Z.sub_diag. auto.
Qed.
