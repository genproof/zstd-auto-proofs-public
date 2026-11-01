(* One sequence as zstd executes it (ExBlock.x_step: ZSTD_execSequence, ZSTD_execSequenceSplitLitBuffer, the
   transition of split literals to litExtraBuffer) does what Block.exec_seqs does with it: ll literals, then
   the match of length ml at offset off, keeping the loop invariant ex_inv.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Require Import Zstd.proof.model.ExAgreeBlkMatch Zstd.proof.model.ExAgreeBlkLitCopy.
Local Open Scope Z_scope.

(* ---------- list facts ---------- *)

Lemma zl_nonneg : forall (l: list Z), 0 <= Zlength l.
Proof. intros. rewrite Zlength_correct. lia. Qed.

Lemma zl_app : forall (l1 l2: list Z), Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof. intros. rewrite !Zlength_correct, length_app. lia. Qed.

(* a match of n bytes appends n bytes *)
Lemma lz_copy_len : forall hist out off n, Zlength (lz_copy hist out off n) = Zlength out + Z.of_nat n.
Proof.
  intros hist out off n. revert out. induction n as [|n IH]; intros out; simpl.
  - lia.
  - rewrite IH, zl_app, !Zlength_correct. simpl. lia.
Qed.

Lemma Zlength_firstn_le : forall (l: list Z) n, 0 <= n <= Zlength l -> Zlength (firstn (Z.to_nat n) l) = n.
Proof.
  intros l n H. rewrite Zlength_correct, firstn_length_le; [lia|].
  rewrite Zlength_correct in H. lia.
Qed.

Lemma Zlength_skipn_le : forall (l: list Z) n, 0 <= n <= Zlength l -> Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros l n H. rewrite Zlength_correct, skipn_length. rewrite Zlength_correct in *. lia.
Qed.

(* ---------- reading regions ---------- *)

(* a read of the destination does not depend on the block's input *)
Lemma reg_has_dst_src : forall src src' m i l, reg_has src m R_dst i l -> reg_has src' m R_dst i l.
Proof. unfold reg_has, xm_rd. auto. Qed.

Lemma reg_def_dst_src : forall src src' m i n, reg_def src m R_dst i n -> reg_def src' m R_dst i n.
Proof. unfold reg_def, xm_rd. auto. Qed.

(* a read of a cell that a copy did not store (litExtraBuffer unchanged, destination unchanged from a on)
   sees the same value *)
Lemma rd_same : forall src m m' a r i,
  xm_lxb m' = xm_lxb m -> dst_same_from m m' a -> (r = R_dst -> a <= i) ->
  xm_rd src m' r i = xm_rd src m r i.
Proof.
  intros src m m' a r i Hl Hd Ha. unfold xm_rd.
  destruct (i <? 0) eqn:Hi; [reflexivity|].
  destruct r.
  - apply Hd. auto.
  - rewrite Hl. reflexivity.
  - reflexivity.
Qed.

Lemma reg_has_same : forall src m m' a r i l,
  xm_lxb m' = xm_lxb m -> dst_same_from m m' a -> (r = R_dst -> a <= i) ->
  reg_has src m r i l -> reg_has src m' r i l.
Proof.
  intros src m m' a r i l Hl Hd Ha H k Hk. rewrite (rd_same src m m' a); auto.
  intros E. specialize (Ha E). lia.
Qed.

Lemma reg_def_same : forall src m m' a r i n,
  xm_lxb m' = xm_lxb m -> dst_same_from m m' a -> (r = R_dst -> a <= i) ->
  reg_def src m r i n -> reg_def src m' r i n.
Proof.
  intros src m m' a r i n Hl Hd Ha H k Hk. rewrite (rd_same src m m' a); auto.
  intros E. specialize (Ha E). lia.
Qed.

Lemma dst_same_trans : forall m1 m2 m3 a b c,
  dst_same_from m1 m2 a -> dst_same_from m2 m3 b -> a <= c -> b <= c -> dst_same_from m1 m3 c.
Proof.
  intros m1 m2 m3 a b c H1 H2 Ha Hb p Hp. rewrite H2 by lia. apply H1. lia.
Qed.

Lemma reg_has_firstn : forall src m r i l n, 0 <= n ->
  reg_has src m r i l -> reg_has src m r i (firstn (Z.to_nat n) l).
Proof.
  intros src m r i l n Hn H k Hk.
  assert (Hk' : 0 <= k < Zlength l /\ k < n).
  { rewrite Zlength_correct, firstn_length in Hk. rewrite Zlength_correct. lia. }
  rewrite H by lia. unfold byte_at. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat k) (Z.to_nat n)); [reflexivity|lia].
Qed.

Lemma reg_has_skipn : forall src m r i l n, 0 <= n <= Zlength l ->
  reg_has src m r i l -> reg_has src m r (i + n) (skipn (Z.to_nat n) l).
Proof.
  intros src m r i l n Hn H k Hk. rewrite Zlength_skipn_le in Hk by lia.
  replace (i + n + k) with (i + (n + k)) by lia. rewrite H by lia.
  unfold byte_at. rewrite nth_skipn. f_equal. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

(* the cells after the first n bytes of l are defined: the rest of l, then the defined cells after l *)
Lemma reg_def_inside : forall src m r i l n w, 0 <= n <= Zlength l -> 0 <= w ->
  reg_has src m r i l -> reg_def src m r (i + Zlength l) w -> reg_def src m r (i + n) w.
Proof.
  intros src m r i l n w Hn Hw H Hd k Hk.
  destruct (Z_lt_le_dec (n + k) (Zlength l)).
  - exists (byte_at l (n + k)). replace (i + n + k) with (i + (n + k)) by lia. apply H. lia.
  - destruct (Hd (n + k - Zlength l)) as [v Hv]; [lia|]. exists v.
    replace (i + n + k) with (i + Zlength l + (n + k - Zlength l)) by lia. exact Hv.
Qed.

(* ---------- ZSTD_execSequence ---------- *)

(* One sequence of ll literals (the first ll of lits, in region lr at li..llim, 32 defined cells after) and a
   match (ml, off) executed by x_exec after the output outc, all of it before the output end: the output
   becomes outc, the ll literals, then the match; the literals left stay readable after them; litExtraBuffer
   is not written and no store reaches the cells at or above oend. *)
Lemma x_exec_agree : forall (e: xenv) (m: xmem) (op: Z) (lr: xreg) (li llim ll ml off M: Z) (outc lits: list Z),
  xe_ps e = 0 -> xe_vs e = 0 -> Zlength outc = op -> dst_has m 0 outc ->
  0 <= li -> reg_has (xe_src e) m lr li lits -> llim = li + Zlength lits ->
  reg_def (xe_src e) m lr llim XWILDCOPY -> (lr = R_dst -> xe_oend e <= li) ->
  0 <= ml <= M -> op + Zlength lits + M <= xe_oend e -> 0 <= ll <= Zlength lits -> 1 <= off <= op + ll ->
  exists m', x_exec e m op lr li llim ll ml off = Some (m', op + ll + ml, li + ll) /\
    dst_has m' 0 (lz_copy nil (outc ++ firstn (Z.to_nat ll) lits) off (Z.to_nat ml)) /\
    xm_lxb m' = xm_lxb m /\ dst_same_from m m' (xe_oend e) /\
    reg_has (xe_src e) m' lr (li + ll) (skipn (Z.to_nat ll) lits) /\
    reg_def (xe_src e) m' lr llim XWILDCOPY.
Proof.
  intros e m op lr li llim ll ml off M outc lits Hps Hvs Hop Hout Hli Hreg Hlim Hdef Hlr HM Hend Hll Hoff.
  set (L := firstn (Z.to_nat ll) lits).
  assert (HL : Zlength L = ll) by (apply Zlength_firstn_le; lia).
  assert (HregL : reg_has (xe_src e) m lr li L) by (apply reg_has_firstn; [lia|exact Hreg]).
  assert (HdefL : reg_def (xe_src e) m lr (li + Zlength L) XWILDCOPY).
  { rewrite HL. apply (reg_def_inside _ _ _ _ lits); [lia|unfold XWILDCOPY; lia|exact Hreg|rewrite <- Hlim; exact Hdef]. }
  assert (Hop0 : 0 <= op) by (rewrite <- Hop; apply zl_nonneg).
  assert (Hlits0 := zl_nonneg lits).
  (* what is left once the copies are done *)
  assert (Hfin : forall m', xm_lxb m' = xm_lxb m -> dst_same_from m m' (xe_oend e) ->
            reg_has (xe_src e) m' lr (li + ll) (skipn (Z.to_nat ll) lits) /\
            reg_def (xe_src e) m' lr llim XWILDCOPY).
  { intros m' Hl Hd. split.
    - apply (reg_has_same _ m m' (xe_oend e)); auto.
      + intros E. specialize (Hlr E). lia.
      + apply reg_has_skipn; [lia|exact Hreg].
    - apply (reg_def_same _ m m' (xe_oend e)); auto.
      intros E. specialize (Hlr E). lia. }
  unfold x_exec. cbv zeta.
  destruct (orb (llim - li <? ll) (xe_oend e - XWILDCOPY - op <? ll + ml)) eqn:Hpath.
  - (* slow path: ZSTD_execSequenceEnd *)
    replace (ll + ml >? xe_oend e - op) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    replace (ll >? llim - li) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    destruct (proj1 (proj2 lit_copies_agree) (xe_src e) m op (xe_oend e - XWILDCOPY) lr li L outc
                Hop Hout Hli HregL HdefL) as [m1 [Hc1 [Hout1 [Hlx1 Hsame1]]]].
    { unfold XWILDCOPY in *. lia. }
    { intros E. specialize (Hlr E). unfold XWILDCOPY. lia. }
    rewrite HL in Hc1. rewrite Hc1.
    destruct (xm_match_agree e m1 (op + ll) ml off (Some (xe_oend e - XWILDCOPY)) (outc ++ L) (xe_oend e))
      as [m2 [Hc2 [Hout2 [Hlx2 Hsame2]]]];
      auto; try (rewrite zl_app; lia); try (unfold XWILDCOPY in *; lia).
    rewrite Hc2. exists m2.
    assert (Hlx : xm_lxb m2 = xm_lxb m) by congruence.
    assert (Hd : dst_same_from m m2 (xe_oend e)).
    { apply (dst_same_trans m m1 m2 (xe_oend e - XWILDCOPY + XWILDCOPY) (xe_oend e)); auto; lia. }
    destruct (Hfin m2 Hlx Hd). repeat split; auto.
  - (* fast path: ZSTD_execSequence *)
    apply Bool.orb_false_iff in Hpath. destruct Hpath as [_ Hpath]. apply Z.ltb_ge in Hpath.
    destruct (proj1 lit_copies_agree (xe_src e) m op lr li L outc Hop Hout Hli HregL HdefL)
      as [m1 [m1' [Hc1 [Hc1' [Hout1 [Hlx1 Hsame1]]]]]].
    { intros E. specialize (Hlr E). unfold XWILDCOPY in *. lia. }
    rewrite HL in Hc1'. rewrite Hc1. rewrite Hc1'.
    destruct (xm_match_agree e m1' (op + ll) ml off None (outc ++ L) (xe_oend e))
      as [m2 [Hc2 [Hout2 [Hlx2 Hsame2]]]];
      auto; try (rewrite zl_app; lia); try (unfold XWILDCOPY in *; lia).
    rewrite Hc2. exists m2.
    assert (Hlx : xm_lxb m2 = xm_lxb m) by congruence.
    assert (Hd : dst_same_from m m2 (xe_oend e)).
    { apply (dst_same_trans m m1' m2 (op + Zlength L + XWILDCOPY) (xe_oend e)); auto; unfold XWILDCOPY in *; lia. }
    destruct (Hfin m2 Hlx Hd). repeat split; auto.
Qed.

(* the split literals Ld ++ Lx, cut at ll *)
Lemma firstn_split_le : forall (Ld Lx: list Z) ll, 0 <= ll <= Zlength Ld ->
  firstn (Z.to_nat ll) (Ld ++ Lx) = firstn (Z.to_nat ll) Ld.
Proof.
  intros Ld Lx ll H. rewrite firstn_app. rewrite Zlength_correct in H.
  replace (Z.to_nat ll - length Ld)%nat with O by lia. simpl. apply app_nil_r.
Qed.

Lemma skipn_split_le : forall (Ld Lx: list Z) ll, 0 <= ll <= Zlength Ld ->
  skipn (Z.to_nat ll) (Ld ++ Lx) = skipn (Z.to_nat ll) Ld ++ Lx.
Proof.
  intros Ld Lx ll H. rewrite skipn_app. rewrite Zlength_correct in H.
  replace (Z.to_nat ll - length Ld)%nat with O by lia. reflexivity.
Qed.

Lemma firstn_split_ge : forall (Ld Lx: list Z) ll, Zlength Ld <= ll ->
  firstn (Z.to_nat ll) (Ld ++ Lx) = Ld ++ firstn (Z.to_nat (ll - Zlength Ld)) Lx.
Proof.
  intros Ld Lx ll H. rewrite firstn_app. rewrite Zlength_correct in *.
  rewrite firstn_all2 by lia. f_equal. f_equal. lia.
Qed.

Lemma skipn_split_ge : forall (Ld Lx: list Z) ll, Zlength Ld <= ll ->
  skipn (Z.to_nat ll) (Ld ++ Lx) = skipn (Z.to_nat (ll - Zlength Ld)) Lx.
Proof.
  intros Ld Lx ll H. rewrite skipn_app. rewrite Zlength_correct in *.
  rewrite skipn_all2 by lia. simpl. f_equal. lia.
Qed.

(* litExtraBuffer reads see only litExtraBuffer *)
Lemma reg_has_lxb : forall src m m' i l, xm_lxb m' = xm_lxb m ->
  reg_has src m R_lxb i l -> reg_has src m' R_lxb i l.
Proof. unfold reg_has, xm_rd. intros src m m' i l E H k Hk. rewrite E. apply H. exact Hk. Qed.

Lemma reg_def_lxb : forall src m i n, 0 <= i -> i + n <= Zlength (xm_lxb m) -> reg_def src m R_lxb i n.
Proof.
  intros src m i n Hi Hn k Hk. unfold xm_rd.
  replace (i + k <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i + k <? Zlength (xm_lxb m)) with true by (symmetry; apply Z.ltb_lt; lia).
  eexists. reflexivity.
Qed.

Lemma x_step_agree : forall (e: xenv) (s: xex) (outc lits: list Z) (M ll ml off: Z),
  ex_inv e s outc lits M -> 0 <= ll <= Zlength lits -> 0 <= ml <= M -> 1 <= off <= Zlength outc + ll ->
  exists s', x_step e s ll ml off = Some s' /\
    ex_inv e s' (lz_copy nil (outc ++ firstn (Z.to_nat ll) lits) off (Z.to_nat ml))
               (skipn (Z.to_nat ll) lits) (M - ml) /\
    xm_lxb (xmm s') = xm_lxb (xmm s).
Proof.
  intros e s outc lits M ll ml off Hinv Hll Hml Hoff.
  destruct Hinv as (Hps & Hvs & Hop & Hout & HM0 & Hend & Hlit).
  unfold lit_inv in Hlit. unfold x_step.
  assert (Hop0 : 0 <= xop s) by (rewrite Hop; apply zl_nonneg).
  destruct (xsp s) eqn:Hsp.
  - destruct Hlit as (Ld & Lx & Hlits & HLx & HLd & Hlim & Hdef & HLxr & Hlxb & Hroom).
    subst lits. rewrite zl_app in Hll, Hend.
    assert (HLd0 := zl_nonneg Ld).
    destruct (xlim s - xli s <? ll) eqn:Hleft.
    + (* the dst part runs out: its leftover, then the sequence from litExtraBuffer *)
      apply Z.ltb_lt in Hleft.
      rewrite firstn_split_ge, skipn_split_ge by lia. rewrite app_assoc.
      assert (Hcont : forall m1, dst_has m1 0 (outc ++ Ld) -> xm_lxb m1 = xm_lxb (xmm s) ->
        exists s',
          match x_exec e m1 (xop s + Zlength Ld) R_lxb 0 XLITEXTRA (ll - Zlength Ld) ml off with
          | Some (m, op, li) => Some {| xmm := m; xop := op; xlr := R_lxb; xli := li; xlim := XLITEXTRA; xsp := false |}
          | None => None
          end = Some s' /\
          ex_inv e s' (lz_copy [] ((outc ++ Ld) ++ firstn (Z.to_nat (ll - Zlength Ld)) Lx) off (Z.to_nat ml))
            (skipn (Z.to_nat (ll - Zlength Ld)) Lx) (M - ml) /\ xm_lxb (xmm s') = xm_lxb (xmm s)).
      { intros m1 Hout1 Hlx1.
        destruct (x_exec_agree e m1 (xop s + Zlength Ld) R_lxb 0 XLITEXTRA (ll - Zlength Ld) ml off M
                    (outc ++ Ld) Lx) as (m2 & Hc & Hout2 & Hlx2 & Hsame2 & Hreg2 & Hdef2);
          auto; try (unfold XLITEXTRA, XWILDCOPY in *; lia).
        - rewrite zl_app. lia.
        - apply (reg_has_lxb _ (xmm s)); auto.
        - apply reg_def_lxb; [unfold XLITEXTRA; lia|]. rewrite Hlx1, Hlxb. lia.
        - intros E. discriminate.
        - rewrite Hc. eexists. split; [reflexivity|].
          assert (HLf : Zlength (firstn (Z.to_nat (ll - Zlength Ld)) Lx) = ll - Zlength Ld)
            by (apply Zlength_firstn_le; lia).
          assert (HLs : Zlength (skipn (Z.to_nat (ll - Zlength Ld)) Lx) = Zlength Lx - (ll - Zlength Ld))
            by (apply Zlength_skipn_le; lia).
          unfold ex_inv, lit_inv; simpl.
          rewrite lz_copy_len, !zl_app, HLf, HLs. rewrite Z2Nat.id by lia.
          repeat split; auto; try (unfold XLITEXTRA in *; lia).
          all: first [congruence | intros E; discriminate]. }
      destruct (xlim s - xli s =? 0) eqn:H0.
      * apply Z.eqb_eq in H0. assert (Zlength Ld = 0) by lia.
        destruct (Hcont (xmm s)) as (s' & Hc & Hinv & Hlx); auto.
        { destruct Ld; [rewrite app_nil_r; exact Hout|].
          rewrite Zlength_correct in *. simpl in *. lia. }
        rewrite H, Z.add_0_r in Hc. rewrite H in *. rewrite H0. exists s'. auto.
      * replace (xlim s - xli s >? xe_oend e - xop s) with false
          by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; unfold XLITEXTRA in *; lia).
        destruct (proj2 (proj2 lit_copies_agree) (xe_src e) (xmm s) (xop s) (xli s) Ld outc)
          as (m1 & Hc1 & Hout1 & Hlx1 & _); auto.
        { unfold XLITEXTRA, XWILDCOPY in *. lia. }
        replace (xlim s - xli s) with (Zlength Ld) by lia. rewrite Hc1.
        destruct (Hcont m1 Hout1 Hlx1) as (s' & Hc & Hinv & Hlx). exists s'. auto.
    + (* ZSTD_execSequenceSplitLitBuffer, always on its fast path *)
      apply Z.ltb_ge in Hleft.
      rewrite firstn_split_le, skipn_split_le by lia.
      set (L := firstn (Z.to_nat ll) Ld).
      assert (HL : Zlength L = ll) by (apply Zlength_firstn_le; lia).
      unfold x_exec_split. cbv zeta.
      replace (orb (xlim s - xli s <? ll) (xli s + ll - XWILDCOPY - xop s <? ll + ml)) with false
        by (symmetry; apply Bool.orb_false_iff; split; apply Z.ltb_ge; unfold XLITEXTRA, XWILDCOPY in *; lia).
      assert (HregL : reg_has (xe_src e) (xmm s) R_dst (xli s) L)
        by (apply reg_has_firstn; [lia|]; apply (reg_has_dst_src nil); exact HLd).
      assert (HdefL : reg_def (xe_src e) (xmm s) R_dst (xli s + Zlength L) XWILDCOPY).
      { rewrite HL. apply (reg_def_inside _ _ _ _ Ld); [lia|unfold XWILDCOPY; lia| |].
        - apply (reg_has_dst_src nil). exact HLd.
        - rewrite <- Hlim. exact Hdef. }
      destruct (proj1 lit_copies_agree (xe_src e) (xmm s) (xop s) R_dst (xli s) L outc)
        as (m1 & m1' & Hc1 & Hc1' & Hout1 & Hlx1 & Hsame1); auto;
        try (unfold XLITEXTRA, XWILDCOPY in *; lia).
      rewrite HL in Hc1'. rewrite Hc1, Hc1'.
      destruct (xm_match_agree e m1' (xop s + ll) ml off None (outc ++ L) (xli s + ll))
        as (m2 & Hc2 & Hout2 & Hlx2 & Hsame2);
        auto; try (rewrite zl_app; lia); try (unfold XLITEXTRA, XWILDCOPY in *; lia).
      rewrite Hc2. eexists. split; [reflexivity|].
      assert (Hlx : xm_lxb m2 = xm_lxb (xmm s)) by congruence.
      assert (Hd : dst_same_from (xmm s) m2 (xli s + ll)).
      { apply (dst_same_trans _ m1' _ (xop s + Zlength L + XWILDCOPY) (xli s + ll)); auto;
          unfold XLITEXTRA, XWILDCOPY in *; lia. }
      assert (HLs : Zlength (skipn (Z.to_nat ll) Ld) = Zlength Ld - ll) by (apply Zlength_skipn_le; lia).
      unfold ex_inv, lit_inv; simpl.
      rewrite lz_copy_len, !zl_app, HL, HLs. rewrite Z2Nat.id by lia.
      split; [|exact Hlx].
      split; [auto|]. split; [auto|]. split; [lia|]. split; [exact Hout2|]. split; [lia|]. split; [lia|].
      exists (skipn (Z.to_nat ll) Ld), Lx.
      split; [reflexivity|]. split; [exact HLx|].
      split; [|split; [lia|split; [|split; [|split]]]].
      * apply (reg_has_same nil (xmm s) m2 (xli s + ll)); auto; [lia|].
        apply reg_has_skipn; [lia|exact HLd].
      * apply (reg_def_same _ (xmm s) m2 (xli s + ll)); auto. intros _. lia.
      * apply (reg_has_lxb _ (xmm s)); auto.
      * rewrite Hlx, Hlxb. reflexivity.
      * lia.
  - (* not split: ZSTD_execSequence *)
    destruct Hlit as (Hli & Hreg & Hlim & Hdef & Hlr).
    destruct (x_exec_agree e (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off M outc lits)
      as (m2 & Hc & Hout2 & Hlx2 & Hsame2 & Hreg2 & Hdef2); auto; try lia.
    rewrite Hc. eexists. split; [reflexivity|].
    assert (HLf : Zlength (firstn (Z.to_nat ll) lits) = ll) by (apply Zlength_firstn_le; lia).
    assert (HLs : Zlength (skipn (Z.to_nat ll) lits) = Zlength lits - ll) by (apply Zlength_skipn_le; lia).
    unfold ex_inv, lit_inv; simpl.
    rewrite lz_copy_len, !zl_app, HLf, HLs. rewrite Z2Nat.id by lia.
    repeat split; auto; try lia.
    intros E. specialize (Hlr E). lia.
Qed.
