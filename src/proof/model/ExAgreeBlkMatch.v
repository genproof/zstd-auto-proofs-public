(* The match of a sequence as zstd copies it (ExBlock.xm_match: ZSTD_overlapCopy8, ZSTD_wildcopy, ZSTD_safecopy,
   in a one-shot destination without dictionary: prefixStart = virtualStart = 0) writes the format model's
   match (Block.lz_copy) after the output so far.  Its stores stay below W: oLitEnd + ml + 32 on the fast path
   (wo = None), oend_w + 32 on the slow path (wo = Some oend_w).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Local Open Scope Z_scope.

(* ---------- one store in the destination ---------- *)

Lemma nth_upd_eq : forall {A} (l: list A) i x d, (i < length l)%nat -> nth i (upd l i x) d = x.
Proof.
  induction l as [|y l IH]; intros i x d H; simpl in H; [lia|].
  destruct i; simpl; [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_upd_neq : forall {A} (l: list A) i j x d, i <> j -> nth j (upd l i x) d = nth j l d.
Proof.
  induction l as [|y l IH]; intros i j x d H; [reflexivity|].
  destruct i, j; simpl; try reflexivity; [congruence|]. apply IH. lia.
Qed.

(* a store of v at cell i >= 0 of the destination: cell i holds v, the others and litExtraBuffer are kept *)
Lemma dcell_wr : forall m i v, 0 <= i ->
  exists m', xm_wr m R_dst i v = Some m' /\ xm_lxb m' = xm_lxb m /\
    (forall p, 0 <= p -> dcell m' p = if p =? i then Some v else dcell m p).
Proof.
  intros m i v Hi. unfold xm_wr.
  destruct (i <? 0) eqn:E0; [lia|].
  eexists; split; [reflexivity|]. split; [reflexivity|].
  intros p Hp. unfold dcell; simpl.
  destruct (i <? Zlength (xm_dst m)) eqn:E; rewrite Zlength_correct in *; [apply Z.ltb_lt in E|apply Z.ltb_ge in E].
  - destruct (Z.eqb_spec p i).
    + subst. apply nth_upd_eq. lia.
    + apply nth_upd_neq. lia.
  - destruct (Z.eqb_spec p i).
    + subst. rewrite app_nth2 by lia. rewrite app_nth2 by (rewrite repeat_length; lia).
      rewrite repeat_length.
      replace (Z.to_nat i - length (xm_dst m) - Z.to_nat (i - Z.of_nat (length (xm_dst m))))%nat
        with 0%nat by lia. reflexivity.
    + destruct (Nat.lt_ge_cases (Z.to_nat p) (length (xm_dst m))).
      * rewrite app_nth1 by lia. reflexivity.
      * rewrite app_nth2 by lia. rewrite (nth_overflow (xm_dst m)) by lia.
        set (j := (Z.to_nat p - length (xm_dst m))%nat).
        set (n0 := Z.to_nat (i - Z.of_nat (length (xm_dst m)))).
        assert (j <> n0) by (unfold j, n0; lia).
        destruct (Nat.lt_ge_cases j n0).
        -- rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
        -- rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
           apply nth_overflow. simpl. lia.
Qed.

(* m' differs from m only in destination cells below h *)
Definition Fr (m m': xmem) (h: Z) : Prop :=
  xm_lxb m' = xm_lxb m /\ forall p, 0 <= p -> h <= p -> dcell m' p = dcell m p.

Lemma Fr_refl : forall m h, Fr m m h.
Proof. intros m h. split; reflexivity. Qed.

Lemma Fr_mono : forall m m' h h', Fr m m' h -> h <= h' -> Fr m m' h'.
Proof. intros m m' h h' [H1 H2] Hh. split; [exact H1|]. intros p Hp Hp'. apply H2; lia. Qed.

Lemma Fr_trans : forall m1 m2 m3 h1 h2 h, Fr m1 m2 h1 -> Fr m2 m3 h2 -> h1 <= h -> h2 <= h -> Fr m1 m3 h.
Proof.
  intros m1 m2 m3 h1 h2 h [A1 B1] [A2 B2] H1 H2. split; [congruence|].
  intros p Hp Hp'. rewrite B2 by lia. apply B1; lia.
Qed.

(* ---------- the pattern a match copy writes ---------- *)

Section Pattern.
Variable outl : list Z.
Variable off : Z.
Let L := Zlength outl.
Variable Hoff : 1 <= off <= L.

(* the cell p of the output after a match of offset off behind outl: outl itself below L, then outl's last
   off bytes repeated *)
Definition pidx (p: Z) : Z := if p <? L then p else L - off + (p - L) mod off.
Definition X (p: Z) : Z := byte_at outl (pidx p).

Lemma X_per : forall s t, L - off <= s -> 0 <= t -> X (s + t * off) = X s.
Proof.
  intros s t Hs Ht. unfold X, pidx. f_equal.
  destruct (s <? L) eqn:E1.
  - destruct (Z.eq_dec t 0) as [->|Hn].
    + rewrite Z.mul_0_l, Z.add_0_r, E1. reflexivity.
    + destruct (s + t * off <? L) eqn:E2; [nia|].
      replace (s + t * off - L) with ((s - L + off) + (t - 1) * off) by ring.
      rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
  - destruct (s + t * off <? L) eqn:E2; [nia|].
    replace (s + t * off - L) with ((s - L) + t * off) by ring.
    rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma X_dist : forall s d, L - off <= s <= d -> (d - s) mod off = 0 -> X d = X s.
Proof.
  intros s d Hs Hm.
  assert (Hd: d = s + ((d - s) / off) * off).
  { pose proof (Z.div_mod (d - s) off ltac:(lia)) as H. rewrite Hm in H. nia. }
  rewrite Hd. apply X_per; [lia|]. apply Z.div_pos; lia.
Qed.

(* the format model's match: its output is the pattern X *)
Lemma lz_copy_X : forall n out, L <= Zlength out ->
  (forall p, 0 <= p < Zlength out -> byte_at out p = X p) ->
  Zlength (lz_copy nil out off n) = Zlength out + Z.of_nat n /\
  forall p, 0 <= p < Zlength out + Z.of_nat n -> byte_at (lz_copy nil out off n) p = X p.
Proof.
  induction n as [|n IH]; intros out HL Hout; cbn [lz_copy app].
  - split; [lia|]. intros p Hp. apply Hout. lia.
  - change (Zlength (@nil Z)) with 0. rewrite Z.add_0_l. rewrite Nat2Z.inj_succ.
    set (b := byte_at out (Zlength out - off)).
    assert (Hb: b = X (Zlength out)).
    { unfold b. rewrite Hout by lia.
      symmetry. apply X_dist; [lia|]. replace (Zlength out - (Zlength out - off)) with (1 * off) by ring.
      apply Z_mod_mult. }
    assert (Hlen: Zlength (out ++ [b]) = Zlength out + 1).
    { rewrite !Zlength_correct, app_length. simpl. lia. }
    destruct (IH (out ++ [b])) as [IH1 IH2]; [lia| |].
    + intros p Hp. rewrite Hlen in Hp. unfold byte_at.
      destruct (Z.eq_dec p (Zlength out)) as [->|Hn].
      * rewrite app_nth2 by (rewrite Zlength_correct in *; lia).
        rewrite Zlength_correct, Nat2Z.id, Nat.sub_diag. rewrite <- Zlength_correct. exact Hb.
      * rewrite app_nth1 by (rewrite Zlength_correct in *; lia). apply Hout. lia.
    + rewrite Hlen in IH1, IH2. split; [lia|]. intros p Hp. apply IH2. lia.
Qed.

(* ---------- copies under the pattern invariant ---------- *)

(* the destination's cells [0, w) hold the pattern *)
Definition Inv (m: xmem) (w: Z) : Prop := forall p, 0 <= p < w -> dcell m p = Some (X p).
Lemma Inv_mono : forall m w w', Inv m w -> w' <= w -> Inv m w'.
Proof. intros m w w' H Hw p Hp. apply H. lia. Qed.

(* storing X d at a cell d within or just after the pattern prefix *)
Lemma wr_ok : forall m w d, Inv m w -> 0 <= d <= w ->
  exists m', xm_wr m R_dst d (X d) = Some m' /\ Inv m' (Z.max w (d + 1)) /\ Fr m m' (d + 1).
Proof.
  intros m w d HI Hd. destruct (dcell_wr m d (X d)) as (m' & E & Hl & Hc); [lia|].
  exists m'. split; [exact E|]. split.
  - intros p Hp. rewrite Hc by lia. destruct (Z.eqb_spec p d) as [->|Hn]; [reflexivity|]. apply HI. lia.
  - split; [exact Hl|]. intros p Hp Hp'. rewrite Hc by lia. destruct (Z.eqb_spec p d); [lia|reflexivity].
Qed.

Lemma rd_ok : forall src m w s, Inv m w -> 0 <= s < w -> xm_rd src m R_dst s = Some (X s).
Proof.
  intros src m w s HI Hs. unfold xm_rd. destruct (s <? 0) eqn:E; [lia|]. apply HI. lia.
Qed.

(* a source s behind the destination d at a multiple of off, at or above L - off *)
Definition G (d s: Z) : Prop := L - off <= s < d /\ (d - s) mod off = 0.

Lemma G_shift : forall d s i, G d s -> 0 <= i -> G (d + i) (s + i).
Proof.
  intros d s i [H1 H2] Hi. split; [lia|]. replace (d + i - (s + i)) with (d - s) by ring. exact H2.
Qed.

Lemma fwd_ok : forall src k m w d s, Inv m w -> G d s -> d <= w ->
  exists m', xm_fwd src k m R_dst d R_dst s = Some m' /\
    Inv m' (Z.max w (d + Z.of_nat k)) /\ Fr m m' (d + Z.of_nat k).
Proof.
  intros src k. induction k as [|k IH]; intros m w d s HI HG Hd; simpl.
  - exists m. split; [reflexivity|]. split; [eapply Inv_mono; [exact HI|lia]|]. apply Fr_refl.
  - destruct HG as [Hs Hm] eqn:HG0.
    rewrite (rd_ok src m w s) by (auto; lia).
    rewrite <- (X_dist s d) by (auto; lia).
    destruct (wr_ok m w d) as (m1 & E1 & HI1 & HF1); [auto|lia|].
    rewrite E1.
    destruct (IH m1 (Z.max w (d + 1)) (d + 1) (s + 1)) as (m2 & E2 & HI2 & HF2).
    + exact HI1.
    + apply G_shift; [exact HG|lia].
    + lia.
    + exists m2. split; [exact E2|]. split.
      * eapply Inv_mono; [exact HI2|lia].
      * eapply Fr_trans; [exact HF1|exact HF2|lia|lia].
Qed.

Fixpoint zseq (s: Z) (k: nat) : list Z := match k with O => nil | S k => s :: zseq (s + 1) k end.

Lemma rdn_ok : forall src k m w s, Inv m w -> 0 <= s -> s + Z.of_nat k <= w ->
  xm_rdn src k m R_dst s = Some (map X (zseq s k)).
Proof.
  intros src k. induction k as [|k IH]; intros m w s HI Hs Hk; simpl; [reflexivity|].
  rewrite (rd_ok src m w s) by (auto; lia). rewrite (IH m w (s + 1)) by (auto; lia). reflexivity.
Qed.

Lemma map_X_shift : forall k d s, G d s -> map X (zseq s k) = map X (zseq d k).
Proof.
  induction k as [|k IH]; intros d s HG; simpl; [reflexivity|].
  destruct HG as [H1 H2] eqn:HG0. rewrite (X_dist s d) by (auto; lia). f_equal.
  apply IH. apply G_shift; [exact HG|lia].
Qed.

Lemma wrn_ok : forall k m w d, Inv m w -> 0 <= d <= w ->
  exists m', xm_wrn (map X (zseq d k)) m R_dst d = Some m' /\
    Inv m' (Z.max w (d + Z.of_nat k)) /\ Fr m m' (d + Z.of_nat k).
Proof.
  intros k. induction k as [|k IH]; intros m w d HI Hd; simpl.
  - exists m. split; [reflexivity|]. split; [eapply Inv_mono; [exact HI|lia]|]. apply Fr_refl.
  - destruct (wr_ok m w d) as (m1 & E1 & HI1 & HF1); [auto|lia|].
    rewrite E1.
    destruct (IH m1 (Z.max w (d + 1)) (d + 1)) as (m2 & E2 & HI2 & HF2); [exact HI1|lia|].
    exists m2. split; [exact E2|]. split.
    + eapply Inv_mono; [exact HI2|lia].
    + eapply Fr_trans; [exact HF1|exact HF2|lia|lia].
Qed.

Lemma move_ok : forall src k m w d s, Inv m w -> G d s -> d <= w -> s + Z.of_nat k <= w ->
  exists m', xm_move src k m R_dst d R_dst s = Some m' /\
    Inv m' (Z.max w (d + Z.of_nat k)) /\ Fr m m' (d + Z.of_nat k).
Proof.
  intros src k m w d s HI HG Hd Hk. unfold xm_move.
  destruct HG as [H1 H2] eqn:HG0.
  rewrite (rdn_ok src k m w s) by (auto; lia). rewrite (map_X_shift k d s HG).
  apply wrn_ok; [exact HI|lia].
Qed.

Lemma chunks_ok : forall src k m w d s, Inv m w -> G d s -> s + 16 <= d <= w ->
  exists m', xm_chunks16 src k m d R_dst s = Some m' /\
    Inv m' (Z.max w (d + 16 * Z.of_nat k)) /\ Fr m m' (d + 16 * Z.of_nat k).
Proof.
  intros src k. induction k as [|k IH]; intros m w d s HI HG Hd; simpl.
  - exists m. split; [reflexivity|]. split; [eapply Inv_mono; [exact HI|lia]|]. apply Fr_refl.
  - destruct (move_ok src 16 m w d s) as (m1 & E1 & HI1 & HF1); [auto|auto|lia|simpl; lia|].
    rewrite E1.
    destruct (IH m1 (Z.max w (d + 16)) (d + 16) (s + 16)) as (m2 & E2 & HI2 & HF2).
    + exact HI1.
    + apply G_shift; [exact HG|lia].
    + lia.
    + exists m2. split; [exact E2|]. split.
      * eapply Inv_mono; [exact HI2|lia].
      * eapply Fr_trans; [exact HF1|exact HF2|lia|lia].
Qed.

(* ZSTD_wildcopy of len bytes at d: the pattern up to d + len, stores below d + len + 32 *)
Lemma wild_ok : forall src m w d s len b, Inv m w -> G d s -> d <= w -> 0 <= len ->
  (b = false -> s + 16 <= d) ->
  exists m', xm_wild src m d R_dst s len b = Some m' /\ Inv m' (Z.max w (d + len)) /\
    Fr m m' (d + len + XWILDCOPY).
Proof.
  intros src m w d s len b HI HG Hd Hlen Hb. unfold xm_wild, XWILDCOPY.
  assert (Hq: 0 <= (len + 7) / 8) by (apply Z.div_pos; lia).
  assert (Hq1: len <= 8 * ((len + 7) / 8) <= len + 7).
  { pose proof (Z.div_mod (len + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)). lia. }
  destruct (andb b (d - s <? 16)) eqn:E.
  - destruct (fwd_ok src (Z.to_nat (8 * Z.max 1 ((len + 7) / 8))) m w d s) as (m' & E' & HI' & HF');
      [auto|auto|auto|].
    exists m'. split; [exact E'|]. rewrite Z2Nat.id in HI', HF' by lia. split.
    + eapply Inv_mono; [exact HI'|lia].
    + eapply Fr_mono; [exact HF'|lia].
  - assert (Hs16: s + 16 <= d).
    { destruct b; [|auto]. simpl in E. lia. }
    set (nch := if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32)).
    assert (Hn: 0 <= nch /\ len <= 16 * nch <= len + 32).
    { unfold nch. destruct (len <=? 16) eqn:E2; [lia|].
      pose proof (Z.div_mod (len - 16 + 31) 32 ltac:(lia)).
      pose proof (Z.mod_pos_bound (len - 16 + 31) 32 ltac:(lia)).
      assert (0 <= (len - 16 + 31) / 32) by (apply Z.div_pos; lia). lia. }
    destruct (chunks_ok src (Z.to_nat nch) m w d s) as (m' & E' & HI' & HF'); [auto|auto|lia|].
    exists m'. split; [exact E'|]. rewrite Z2Nat.id in HI', HF' by lia. split.
    + eapply Inv_mono; [exact HI'|lia].
    + eapply Fr_mono; [exact HF'|lia].
Qed.

(* ZSTD_overlapCopy8 for an offset below 8: the distance of the second 4-byte copy and the distance left
   behind are multiples of the offset, the latter at least 8 *)
Lemma ov8_dists : forall o, 1 <= o < 8 ->
  0 <= xdec32 o /\ 0 < o + 4 - xdec32 o /\ (o + 4 - xdec32 o) mod o = 0 /\
  8 <= o - xdec32 o + xdec64 o <= o + 8 /\ (o - xdec32 o + xdec64 o) mod o = 0.
Proof.
  intros o Ho.
  assert (o = 1 \/ o = 2 \/ o = 3 \/ o = 4 \/ o = 5 \/ o = 6 \/ o = 7) as Hc by lia.
  repeat destruct Hc as [->|Hc]; try (rewrite Hc); cbv -[Z.le Z.lt]; lia.
Qed.

(* ZSTD_overlapCopy8 at op (at or above L, within the pattern prefix), from op - off *)
Lemma ov8_ok : forall src m w op, Inv m w -> L <= op <= w ->
  exists m' ip1, xm_ov8 src m op (op - off) off = Some (m', op + 8, ip1) /\
    Inv m' (Z.max w (op + 8)) /\ Fr m m' (op + 8) /\ G (op + 8) ip1 /\ ip1 + 8 <= op + 8.
Proof.
  intros src m w op HI Hop. unfold xm_ov8.
  assert (HG0: G op (op - off)).
  { split; [lia|]. replace (op - (op - off)) with off by ring. apply Z_mod_same_full. }
  destruct (fwd_ok src (if off <? 8 then 4%nat else 8%nat) m w op (op - off)) as (m1 & E1 & HI1 & HF1);
    [auto|auto|lia|].
  destruct (off <? 8) eqn:E.
  - apply Z.ltb_lt in E. rewrite E1.
    destruct (ov8_dists off) as (D1 & D2 & D3 & D4 & D5); [lia|].
    destruct (fwd_ok src 4 m1 (Z.max w (op + 4)) (op + 4) (op - off + xdec32 off)) as (m2 & E2 & HI2 & HF2).
    + exact HI1.
    + split; [lia|]. replace (op + 4 - (op - off + xdec32 off)) with (off + 4 - xdec32 off) by ring. exact D3.
    + lia.
    + rewrite E2. do 2 eexists. split; [reflexivity|]. split; [|split; [|split]].
      * eapply Inv_mono; [exact HI2|lia].
      * eapply Fr_trans; [exact HF1|exact HF2|simpl; lia|simpl; lia].
      * split; [lia|]. replace (op + 8 - (op - off + xdec32 off - xdec64 off + 8))
          with (off - xdec32 off + xdec64 off) by ring. exact D5.
      * lia.
  - apply Z.ltb_ge in E. rewrite E1. do 2 eexists. split; [reflexivity|]. split; [|split; [|split]].
    + eapply Inv_mono; [exact HI1|simpl; lia].
    + exact HF1.
    + replace (op + 8) with (op + Z.of_nat 8) by reflexivity.
      replace (op - off + 8) with (op - off + Z.of_nat 8) by reflexivity.
      apply G_shift; [exact HG0|lia].
    + lia.
Qed.

(* ZSTD_safecopy of a match (source before destination) at op from op - off, with output limit wv: the
   pattern up to op + ml, stores below wv + XWILDCOPY *)
Lemma safecopy_ok : forall src m wv op ml, Inv m op -> L <= op -> 0 <= ml -> op + ml <= wv + XWILDCOPY ->
  exists m', xm_safecopy src m op wv R_dst (op - off) ml true = Some m' /\ Inv m' (op + ml) /\
    Fr m m' (wv + XWILDCOPY).
Proof.
  intros src m wv op ml HI Hop Hml Hw. unfold xm_safecopy, XWILDCOPY in *.
  assert (HG0: G op (op - off)).
  { split; [lia|]. replace (op - (op - off)) with off by ring. apply Z_mod_same_full. }
  destruct (ml <? 8) eqn:E1.
  - destruct (fwd_ok src (Z.to_nat ml) m op op (op - off)) as (m1 & E & HI1 & HF1); [auto|auto|lia|].
    rewrite Z2Nat.id in HI1, HF1 by lia.
    exists m1. split; [exact E|]. split.
    + eapply Inv_mono; [exact HI1|lia].
    + eapply Fr_mono; [exact HF1|lia].
  - apply Z.ltb_ge in E1.
    destruct (ov8_ok src m op op) as (m1 & ip1 & Eo & HI1 & HF1 & HG1 & Hip1); [auto|lia|].
    replace (op - (op - off)) with off by ring. rewrite Eo.
    destruct (wv - (op + ml) >=? 0) eqn:E2.
    + apply Z.geb_le in E2.
      destruct (wild_ok src m1 (Z.max op (op + 8)) (op + 8) ip1 (ml - 8) true) as (m2 & E & HI2 & HF2);
        [auto|auto|lia|lia|discriminate|].
      exists m2. split; [exact E|]. split.
      * eapply Inv_mono; [exact HI2|lia].
      * eapply Fr_trans; [exact HF1|exact HF2|unfold XWILDCOPY; lia|unfold XWILDCOPY; lia].
    + rewrite Z.geb_leb, Z.leb_gt in E2.
      destruct (wv - (op + 8) >=? 0) eqn:E3.
      * apply Z.geb_le in E3.
        destruct (wild_ok src m1 (Z.max op (op + 8)) (op + 8) ip1 (wv - (op + 8)) true)
          as (m2 & E & HI2 & HF2); [auto|auto|lia|lia|discriminate|].
        rewrite E.
        destruct (fwd_ok src (Z.to_nat (op + ml - wv)) m2 (Z.max (Z.max op (op + 8)) (op + 8 + (wv - (op + 8))))
          wv (ip1 + (wv - (op + 8)))) as (m3 & E' & HI3 & HF3).
        -- exact HI2.
        -- replace wv with (op + 8 + (wv - (op + 8))) at 1 by ring. apply G_shift; [exact HG1|lia].
        -- lia.
        -- rewrite Z2Nat.id in HI3, HF3 by lia.
           exists m3. split; [exact E'|]. split.
           ++ eapply Inv_mono; [exact HI3|lia].
           ++ eapply Fr_trans; [eapply (Fr_trans _ _ _ _ _ (wv + XWILDCOPY)); [exact HF1|exact HF2|unfold XWILDCOPY in *; lia|unfold XWILDCOPY in *; lia]|exact HF3|unfold XWILDCOPY in *; lia|unfold XWILDCOPY in *; lia].
      * rewrite Z.geb_leb, Z.leb_gt in E3.
        destruct (fwd_ok src (Z.to_nat (op + ml - (op + 8))) m1 (Z.max op (op + 8)) (op + 8) ip1)
          as (m2 & E & HI2 & HF2); [auto|auto|lia|].
        rewrite Z2Nat.id in HI2, HF2 by lia.
        exists m2. split; [exact E|]. split.
        -- eapply Inv_mono; [exact HI2|lia].
        -- eapply Fr_trans; [exact HF1|exact HF2|lia|lia].
Qed.

End Pattern.

(* the match within the prefix (fast or slow path) at L = |outl|, from L - off: the pattern up to L + ml,
   stores below W *)
Lemma prefix_ok : forall outl off e m ml wo W, 1 <= off <= Zlength outl -> 0 <= ml ->
  Inv outl off m (Zlength outl) ->
  match wo with
  | None => Zlength outl + ml + XWILDCOPY <= W
  | Some w => Zlength outl + ml <= w + XWILDCOPY <= W
  end ->
  exists m', xm_prefix e m (Zlength outl) (Zlength outl - off) ml off wo = Some m' /\
    Inv outl off m' (Zlength outl + ml) /\ Fr m m' W.
Proof.
  intros outl off e m ml wo W Hoff Hml HI Hwo. set (L := Zlength outl) in *. unfold xm_prefix.
  assert (HG0: G outl off L (L - off)).
  { split; [unfold L; lia|]. replace (L - (L - off)) with off by ring. apply Z_mod_same_full. }
  destruct wo as [w|].
  - destruct (safecopy_ok outl off Hoff (xe_src e) m w L ml) as (m' & E & HI' & HF');
      [exact HI|unfold L; lia|exact Hml|lia|].
    exists m'. split; [exact E|]. split; [exact HI'|]. eapply Fr_mono; [exact HF'|lia].
  - unfold XWILDCOPY in Hwo. destruct (off >=? 16) eqn:E16.
    + apply Z.geb_le in E16.
      destruct (wild_ok outl off Hoff (xe_src e) m L L (L - off) ml false) as (m' & E & HI' & HF');
        [exact HI|exact HG0|lia|exact Hml|intros _; lia|].
      exists m'. split; [exact E|]. split.
      * eapply Inv_mono; [exact HI'|lia].
      * eapply Fr_mono; [exact HF'|unfold XWILDCOPY; lia].
    + destruct (ov8_ok outl off Hoff (xe_src e) m L L) as (m1 & ip1 & Eo & HI1 & HF1 & HG1 & Hip1);
        [exact HI|unfold L; lia|].
      rewrite Eo. destruct (ml >? 8) eqn:E8.
      * apply Z.gtb_lt in E8.
        destruct (wild_ok outl off Hoff (xe_src e) m1 (Z.max L (L + 8)) (L + 8) ip1 (ml - 8) true)
          as (m2 & E & HI2 & HF2); [exact HI1|exact HG1|lia|lia|discriminate|].
        exists m2. split; [exact E|]. split.
        -- eapply Inv_mono; [exact HI2|lia].
        -- eapply Fr_trans; [exact HF1|exact HF2|lia|unfold XWILDCOPY; lia].
      * rewrite Z.gtb_ltb, Z.ltb_ge in E8.
        exists m1. split; [reflexivity|]. split.
        -- eapply Inv_mono; [exact HI1|lia].
        -- eapply Fr_mono; [exact HF1|lia].
Qed.

Lemma xm_match_agree : forall (e: xenv) (m: xmem) (oLitEnd ml off: Z) (wo: option Z) (outl: list Z) (W: Z),
  xe_ps e = 0 -> xe_vs e = 0 ->
  Zlength outl = oLitEnd -> dst_has m 0 outl ->
  1 <= off <= oLitEnd -> 0 <= ml ->
  match wo with
  | None => oLitEnd + ml + XWILDCOPY <= W
  | Some w => oLitEnd + ml <= w + XWILDCOPY <= W
  end ->
  exists m', xm_match e m oLitEnd ml off wo = Some m' /\
    dst_has m' 0 (lz_copy nil outl off (Z.to_nat ml)) /\ xm_lxb m' = xm_lxb m /\ dst_same_from m m' W.
Proof.
  intros e m oLitEnd ml off wo outl W Hps Hvs HL Hm Hoff Hml Hwo. subst oLitEnd.
  assert (HI: Inv outl off m (Zlength outl)).
  { intros p Hp. specialize (Hm p Hp). unfold xm_rd in Hm. rewrite Z.add_0_l in Hm.
    destruct (p <? 0) eqn:E; [lia|]. unfold dcell. rewrite Hm. unfold X, pidx.
    destruct (p <? Zlength outl) eqn:E2; [reflexivity|lia]. }
  unfold xm_match. rewrite Hps, Hvs, Z.sub_0_r.
  destruct (off >? Zlength outl) eqn:E; [lia|].
  destruct (prefix_ok outl off e m ml wo W Hoff Hml HI Hwo) as (m' & E' & HI' & [HF1 HF2]).
  exists m'. split; [exact E'|]. split; [|split; [exact HF1|]].
  - destruct (lz_copy_X outl off Hoff (Z.to_nat ml) outl) as [Hlen Hnth]; [lia| |].
    { intros p Hp. unfold X, pidx. destruct (p <? Zlength outl) eqn:E3; [reflexivity|lia]. }
    rewrite Z2Nat.id in Hlen, Hnth by lia.
    intros k Hk. rewrite Hlen in Hk. unfold xm_rd. rewrite Z.add_0_l.
    destruct (k <? 0) eqn:E2; [lia|]. rewrite Hnth by lia. apply HI'. lia.
  - intros p Hp. apply HF2; [|exact Hp]. destruct wo; unfold XWILDCOPY in Hwo; lia.
Qed.
