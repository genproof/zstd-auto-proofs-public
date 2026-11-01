(* The copies of a sequence's literals (ZSTD_copy16 + ZSTD_wildcopy on the fast path, ZSTD_safecopy on the slow
   path, ZSTD_safecopyDstBeforeSrc for the dst part of split literals) write the literals after the output so
   far, from wherever they lie (region lr at li, followed by XWILDCOPY defined cells), without reaching the
   literals not yet read.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Local Open Scope Z_scope.

(* ---------- one store, one read ---------- *)

Lemma nth_upd_any : forall {A} (l: list A) i j x d, (i < length l)%nat ->
  nth j (upd l i x) d = if Nat.eqb j i then x else nth j l d.
Proof.
  induction l as [|y l IH]; intros i j x d Hi; simpl in Hi; [lia|].
  destruct i as [|i]; destruct j as [|j]; simpl; try reflexivity.
  apply IH. lia.
Qed.

Lemma nth_ext_cell : forall (l: list (option Z)) n v j,
  nth j (l ++ repeat None n ++ [Some v]) None =
  if Nat.eqb j (length l + n) then Some v else nth j l None.
Proof.
  intros l n v j.
  destruct (Nat.ltb_spec j (length l)).
  - rewrite app_nth1 by lia. destruct (Nat.eqb_spec j (length l + n)); [lia|reflexivity].
  - rewrite app_nth2 by lia. rewrite (nth_overflow l) by lia.
    destruct (Nat.ltb_spec (j - length l) n).
    + rewrite app_nth1 by (rewrite repeat_length; lia).
      rewrite nth_repeat. destruct (Nat.eqb_spec j (length l + n)); [lia|reflexivity].
    + rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
      destruct (Nat.eqb_spec j (length l + n)).
      * subst j. replace (length l + n - length l - n)%nat with O by lia. reflexivity.
      * destruct (j - length l - n)%nat as [|q] eqn:E; [lia|]. destruct q; reflexivity.
Qed.

(* a store of one destination cell at i >= 0 always succeeds, changes cell i only and not litExtraBuffer *)
Lemma wr_dst : forall m i v, 0 <= i ->
  exists m', xm_wr m R_dst i v = Some m' /\ xm_lxb m' = xm_lxb m /\
    forall p, 0 <= p -> dcell m' p = if p =? i then Some v else dcell m p.
Proof.
  intros m i v Hi. unfold xm_wr.
  destruct (Z.ltb_spec i 0); [lia|].
  eexists; split; [reflexivity|]. split; [reflexivity|].
  intros p Hp. unfold dcell; simpl.
  destruct (Z.ltb_spec i (Zlength (xm_dst m))).
  - rewrite Zlength_correct in H0. rewrite nth_upd_any by lia.
    destruct (Nat.eqb_spec (Z.to_nat p) (Z.to_nat i)); destruct (Z.eqb_spec p i); try reflexivity; lia.
  - rewrite nth_ext_cell. rewrite Zlength_correct in *.
    destruct (Nat.eqb_spec (Z.to_nat p) (length (xm_dst m) + Z.to_nat (i - Z.of_nat (length (xm_dst m)))));
      destruct (Z.eqb_spec p i); try reflexivity; lia.
Qed.

Lemma rd_dst : forall src m j, xm_rd src m R_dst j = if j <? 0 then None else dcell m j.
Proof. reflexivity. Qed.

Lemma rd_dst_src : forall src src' m j, xm_rd src m R_dst j = xm_rd src' m R_dst j.
Proof. reflexivity. Qed.

Lemma rd_other : forall src m m' r j, r <> R_dst -> xm_lxb m' = xm_lxb m ->
  xm_rd src m' r j = xm_rd src m r j.
Proof. intros src m m' r j Hr Hl. destruct r; [congruence| |]; unfold xm_rd; rewrite ?Hl; reflexivity. Qed.

(* ---------- copies whose reads see the original memory ---------- *)

(* m' is m with the n destination cells from d set to the n cells of region r from s, as m holds them;
   litExtraBuffer and every other destination cell unchanged *)
Definition copied (src: list Z) (m m': xmem) (d: Z) (r: xreg) (s n: Z) : Prop :=
  xm_lxb m' = xm_lxb m /\
  (forall p, 0 <= p -> p < d \/ d + n <= p -> dcell m' p = dcell m p) /\
  (forall k, 0 <= k < n -> dcell m' (d + k) = xm_rd src m r (s + k)).

(* the n cells of region r from s are defined *)
Definition rdef (src: list Z) (m: xmem) (r: xreg) (s n: Z) : Prop :=
  forall k, 0 <= k < n -> xm_rd src m r (s + k) <> None.

Lemma copied_refl : forall src m d r s, copied src m m d r s 0.
Proof. intros. split; [reflexivity|]. split; [reflexivity|]. intros; lia. Qed.

(* a read of a cell no store of the copy reached sees the original memory *)
Lemma copied_rd : forall src m m1 d r s n j, copied src m m1 d r s n ->
  (r = R_dst -> j < d \/ d + n <= j) -> xm_rd src m1 r j = xm_rd src m r j.
Proof.
  intros src m m1 d r s n j [Hl [Hf _]] Hj.
  destruct r.
  - rewrite !rd_dst. destruct (Z.ltb_spec j 0); [reflexivity|]. apply Hf; [lia|]. apply Hj; reflexivity.
  - apply rd_other; [discriminate|exact Hl].
  - apply rd_other; [discriminate|exact Hl].
Qed.

Lemma rdef_copied : forall src m m1 d r s n s' n', copied src m m1 d r s n ->
  (r = R_dst -> d + n <= s') -> rdef src m r s' n' -> rdef src m1 r s' n'.
Proof.
  intros src m m1 d r s n s' n' Hc Hr Hd k Hk.
  rewrite (copied_rd _ _ _ _ _ _ _ _ Hc). apply Hd; exact Hk.
  intros E. specialize (Hr E). lia.
Qed.

Lemma rdef_sub : forall src m r s n a n', rdef src m r s n -> 0 <= a -> 0 <= n' -> a + n' <= n ->
  rdef src m r (s + a) n'.
Proof.
  intros src m r s n a n' Hd Ha Hn' Hle k Hk. rewrite <- Z.add_assoc. apply Hd. lia.
Qed.

Lemma rdef_le : forall src m r s n n', rdef src m r s n -> n' <= n -> rdef src m r s n'.
Proof. intros src m r s n n' Hd Hle k Hk. apply Hd. lia. Qed.

(* a second copy at the same distance, from the cells the first did not reach, extends the first *)
Lemma copied_seq : forall src m m1 m2 d r s n1 a d2 s2 n2,
  0 <= d -> 0 <= a <= n1 -> 0 <= n2 -> d2 = d + a -> s2 = s + a -> (r = R_dst -> d + n1 <= s2) ->
  copied src m m1 d r s n1 -> copied src m1 m2 d2 r s2 n2 -> copied src m m2 d r s (Z.max n1 (a + n2)).
Proof.
  intros src m m1 m2 d r s n1 a d2 s2 n2 Hd Ha Hn2 E1 E2 Hr H1 H2. subst d2 s2.
  pose proof H1 as [L1 [F1 C1]]. destruct H2 as [L2 [F2 C2]].
  split; [congruence|]. split.
  - intros p Hp Hpo. rewrite F2 by lia. apply F1; lia.
  - intros k Hk.
    destruct (Z_lt_le_dec k a) as [Hka|Hka]; [|destruct (Z_lt_le_dec k (a + n2)) as [Hkb|Hkb]].
    + rewrite F2 by lia. apply C1. lia.
    + replace (d + k) with (d + a + (k - a)) by lia. rewrite C2 by lia.
      replace (s + a + (k - a)) with (s + k) by lia.
      apply (copied_rd _ _ _ _ _ _ _ _ H1). intros E. specialize (Hr E). lia.
    + rewrite F2 by lia. apply C1. lia.
Qed.

(* ---------- the copy primitives ---------- *)

Lemma copied_one : forall src m m1 d r s v, 0 <= d -> xm_rd src m r s = Some v ->
  xm_lxb m1 = xm_lxb m -> (forall p, 0 <= p -> dcell m1 p = if p =? d then Some v else dcell m p) ->
  copied src m m1 d r s 1.
Proof.
  intros src m m1 d r s v Hd Hv Hl Hc. split; [exact Hl|]. split.
  - intros p Hp Hpo. rewrite Hc by exact Hp. destruct (Z.eqb_spec p d); [lia|reflexivity].
  - intros k Hk. assert (k = 0) by lia. subst k. rewrite !Z.add_0_r, Hc by lia. rewrite Z.eqb_refl. congruence.
Qed.

(* a forward byte copy whose stores stay below its reads (d <= s when the source is the destination) *)
Lemma fwd_copied : forall src r k m d s, 0 <= d -> (r = R_dst -> d <= s) -> rdef src m r s (Z.of_nat k) ->
  exists m', xm_fwd src k m R_dst d r s = Some m' /\ copied src m m' d r s (Z.of_nat k).
Proof.
  intros src r. induction k as [|k IH]; intros m d s Hd Hr Hdef.
  - exists m. split; [reflexivity|apply copied_refl].
  - simpl xm_fwd.
    destruct (xm_rd src m r s) as [v|] eqn:Ev.
    2:{ exfalso. apply (Hdef 0); [lia|]. rewrite Z.add_0_r. exact Ev. }
    destruct (wr_dst m d v Hd) as [m1 [W1 [L1 C1]]]. rewrite W1.
    assert (H1: copied src m m1 d r s 1) by (eapply copied_one; eauto).
    destruct (IH m1 (d + 1) (s + 1)) as [m' [W' C']].
    + lia.
    + intros E; specialize (Hr E); lia.
    + eapply rdef_copied; [exact H1| |].
      * intros E; specialize (Hr E); lia.
      * apply (rdef_sub _ _ _ _ _ 1 _ Hdef); lia.
    + exists m'. split; [exact W'|].
      replace (Z.of_nat (S k)) with (Z.max 1 (1 + Z.of_nat k)) by lia.
      eapply copied_seq; eauto; try lia.
      intros E; specialize (Hr E); lia.
Qed.

Lemma rdn_ok : forall src r k m s, rdef src m r s (Z.of_nat k) ->
  exists vs, xm_rdn src k m r s = Some vs /\ Zlength vs = Z.of_nat k /\
    forall j, 0 <= j < Z.of_nat k -> xm_rd src m r (s + j) = Some (nth (Z.to_nat j) vs 0).
Proof.
  intros src r. induction k as [|k IH]; intros m s Hdef.
  - exists nil. split; [reflexivity|]. split; [reflexivity|]. intros; lia.
  - simpl xm_rdn.
    destruct (xm_rd src m r s) as [v|] eqn:Ev.
    2:{ exfalso. apply (Hdef 0); [lia|]. rewrite Z.add_0_r. exact Ev. }
    destruct (IH m (s + 1)) as [vs [R1 [Len1 C1]]].
    { apply (rdef_sub _ _ _ _ _ 1 _ Hdef); lia. }
    rewrite R1. exists (v :: vs). split; [reflexivity|]. split.
    + rewrite Zlength_cons. lia.
    + intros j Hj. destruct (Z.eq_dec j 0).
      * subst j. rewrite Z.add_0_r. exact Ev.
      * replace (s + j) with (s + 1 + (j - 1)) by lia. rewrite C1 by lia.
        replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. reflexivity.
Qed.

Lemma wrn_ok : forall vs m d, 0 <= d ->
  exists m', xm_wrn vs m R_dst d = Some m' /\ xm_lxb m' = xm_lxb m /\
    (forall p, 0 <= p -> p < d \/ d + Zlength vs <= p -> dcell m' p = dcell m p) /\
    (forall j, 0 <= j < Zlength vs -> dcell m' (d + j) = Some (nth (Z.to_nat j) vs 0)).
Proof.
  induction vs as [|v vs IH]; intros m d Hd.
  - exists m. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. intros j Hj.
    rewrite Zlength_nil in Hj; lia.
  - simpl xm_wrn. pose proof (Zlength_correct vs).
    destruct (wr_dst m d v Hd) as [m1 [W1 [L1 C1]]]. rewrite W1.
    destruct (IH m1 (d + 1)) as [m' [W' [L' [F' C']]]]; [lia|].
    rewrite W'. exists m'. rewrite Zlength_cons. split; [reflexivity|]. split; [congruence|]. split.
    + intros p Hp Hpo. rewrite F', C1 by lia. destruct (Z.eqb_spec p d); [lia|reflexivity].
    + intros j Hj. destruct (Z.eq_dec j 0).
      * subst j. rewrite Z.add_0_r, F', C1 by lia. rewrite Z.eqb_refl. reflexivity.
      * replace (d + j) with (d + 1 + (j - 1)) by lia. rewrite C' by lia.
        replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. reflexivity.
Qed.

(* a move (all reads, then all stores) has no condition on the places *)
Lemma move_copied : forall src r k m d s, 0 <= d -> rdef src m r s (Z.of_nat k) ->
  exists m', xm_move src k m R_dst d r s = Some m' /\ copied src m m' d r s (Z.of_nat k).
Proof.
  intros src r k m d s Hd Hdef. unfold xm_move.
  destruct (rdn_ok src r k m s Hdef) as [vs [R1 [Len1 C1]]]. rewrite R1.
  destruct (wrn_ok vs m d Hd) as [m' [W' [L' [F' C']]]]. rewrite W'.
  exists m'. split; [reflexivity|]. split; [exact L'|]. split.
  - intros p Hp Hpo. apply F'; lia.
  - intros j Hj. rewrite C' by lia. rewrite C1 by lia. reflexivity.
Qed.

Lemma chunks_copied : forall src r k m d s, 0 <= d -> (r = R_dst -> d <= s) ->
  rdef src m r s (16 * Z.of_nat k) ->
  exists m', xm_chunks16 src k m d r s = Some m' /\ copied src m m' d r s (16 * Z.of_nat k).
Proof.
  intros src r. induction k as [|k IH]; intros m d s Hd Hr Hdef.
  - exists m. split; [reflexivity|apply copied_refl].
  - simpl xm_chunks16.
    destruct (move_copied src r 16 m d s Hd) as [m1 [W1 H1]].
    { apply (rdef_le _ _ _ _ _ _ Hdef). lia. }
    rewrite W1.
    destruct (IH m1 (d + 16) (s + 16)) as [m' [W' C']].
    + lia.
    + intros E; specialize (Hr E); lia.
    + eapply rdef_copied; [exact H1| |].
      * intros E; specialize (Hr E); simpl Z.of_nat; lia.
      * apply (rdef_sub _ _ _ _ _ 16 _ Hdef); lia.
    + exists m'. split; [exact W'|].
      replace (16 * Z.of_nat (S k)) with (Z.max (Z.of_nat 16) (16 + 16 * Z.of_nat k)) by lia.
      eapply copied_seq; eauto; simpl Z.of_nat; try lia.
      intros E; specialize (Hr E); lia.
Qed.

(* ZSTD_wildcopy without overlap (chunks of 16) of len >= 0 bytes at d: copies n bytes, at least len, at least 16,
   at most len + 31 *)
Lemma wild_copied : forall src m d r s len, 0 <= d -> (r = R_dst -> d <= s) -> 0 <= len ->
  rdef src m r s (Z.max 16 (len + 31)) ->
  exists m' n, xm_wild src m d r s len false = Some m' /\ copied src m m' d r s n /\
    len <= n /\ 16 <= n /\ n <= Z.max 16 (len + 31).
Proof.
  intros src m d r s len Hd Hr Hlen Hdef. unfold xm_wild. simpl andb. cbv iota.
  set (nch := if len <=? 16 then 1 else 1 + 2 * ((len - 16 + 31) / 32)).
  assert (Hn: 1 <= nch /\ len <= 16 * nch <= Z.max 16 (len + 31)).
  { subst nch. destruct (Z.leb_spec len 16); [lia|].
    pose proof (Z.div_mod (len - 16 + 31) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (len - 16 + 31) 32 ltac:(lia)). lia. }
  destruct (chunks_copied src r (Z.to_nat nch) m d s Hd Hr) as [m' [W' C']].
  { rewrite Z2Nat.id by lia. apply (rdef_le _ _ _ _ _ _ Hdef). lia. }
  rewrite Z2Nat.id in C' by lia.
  exists m', (16 * nch). split; [exact W'|]. split; [exact C'|]. lia.
Qed.

(* ---------- the literals' copies ---------- *)

Lemma byte_at_app : forall a b k, 0 <= k ->
  byte_at (a ++ b) k = if k <? Zlength a then byte_at a k else byte_at b (k - Zlength a).
Proof.
  intros a b k Hk. unfold byte_at. rewrite Zlength_correct.
  destruct (Z.ltb_spec k (Z.of_nat (length a))).
  - apply app_nth1. lia.
  - rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma rdef_has : forall src m r i L, reg_has src m r i L -> rdef src m r i (Zlength L).
Proof. intros src m r i L H k Hk. rewrite H by exact Hk. discriminate. Qed.

Lemma rdef_lits : forall src m r i L n, reg_has src m r i L -> reg_def src m r (i + Zlength L) n ->
  rdef src m r i (Zlength L + n).
Proof.
  intros src m r i L n Hh Hd k Hk.
  destruct (Z_lt_le_dec k (Zlength L)).
  - rewrite Hh by lia. discriminate.
  - destruct (Hd (k - Zlength L)) as [v Hv]; [lia|].
    replace (i + Zlength L + (k - Zlength L)) with (i + k) in Hv by lia. rewrite Hv. discriminate.
Qed.

(* a copy of at least |L| cells of region lr at li, which holds L, to the end op of the output outc *)
Lemma copied_out : forall src m m' op lr li L outc n, copied src m m' op lr li n ->
  Zlength outc = op -> dst_has m 0 outc -> reg_has src m lr li L -> Zlength L <= n ->
  dst_has m' 0 (outc ++ L) /\ xm_lxb m' = xm_lxb m /\
  (forall p, 0 <= p -> p < op \/ op + n <= p -> dcell m' p = dcell m p).
Proof.
  intros src m m' op lr li L outc n [Hl [Hf Hc]] Hop Hout Hreg Hn.
  split; [|split; [exact Hl|exact Hf]].
  intros k Hk. rewrite !Zlength_correct, app_length, Nat2Z.inj_add, <- !Zlength_correct in Hk. rewrite Z.add_0_l, rd_dst.
  destruct (Z.ltb_spec k 0); [lia|]. rewrite byte_at_app by lia. rewrite Hop.
  destruct (Z.ltb_spec k op).
  - rewrite Hf by lia. specialize (Hout k ltac:(lia)). rewrite Z.add_0_l, rd_dst in Hout.
    destruct (Z.ltb_spec k 0); [lia|]. exact Hout.
  - replace k with (op + (k - op)) at 1 by lia. rewrite Hc by lia. apply Hreg. lia.
Qed.

Lemma lit_copies_agree :
  (* fast path (ZSTD_execSequence, ZSTD_execSequenceSplitLitBuffer): stores below op + |L| + 32 *)
  (forall (src: list Z) (m: xmem) (op: Z) (lr: xreg) (li: Z) (L outc: list Z),
     Zlength outc = op -> dst_has m 0 outc -> 0 <= li ->
     reg_has src m lr li L -> reg_def src m lr (li + Zlength L) XWILDCOPY ->
     (lr = R_dst -> op + 16 <= li) ->
     exists m1 m', xm_move src 16 m R_dst op lr li = Some m1 /\
       (if Zlength L >? 16 then xm_wild src m1 (op + 16) lr (li + 16) (Zlength L - 16) false else Some m1) = Some m' /\
       dst_has m' 0 (outc ++ L) /\ xm_lxb m' = xm_lxb m /\ dst_same_from m m' (op + Zlength L + XWILDCOPY)) /\
  (* slow path (ZSTD_execSequenceEnd): ZSTD_safecopy with oend_w = w, stores below w + 32 *)
  (forall (src: list Z) (m: xmem) (op w: Z) (lr: xreg) (li: Z) (L outc: list Z),
     Zlength outc = op -> dst_has m 0 outc -> 0 <= li ->
     reg_has src m lr li L -> reg_def src m lr (li + Zlength L) XWILDCOPY ->
     op + Zlength L <= w + XWILDCOPY -> (lr = R_dst -> w + XWILDCOPY <= li) ->
     exists m', xm_safecopy src m op w lr li (Zlength L) false = Some m' /\
       dst_has m' 0 (outc ++ L) /\ xm_lxb m' = xm_lxb m /\ dst_same_from m m' (w + XWILDCOPY)) /\
  (* the dst part of split literals left over at the transition (ZSTD_safecopyDstBeforeSrc), the output at
     least 32 bytes before them: stores exactly the |L| cells from op *)
  (forall (src: list Z) (m: xmem) (op li: Z) (L outc: list Z),
     Zlength outc = op -> dst_has m 0 outc -> dst_has m li L -> op + XWILDCOPY <= li ->
     exists m', xm_sdbs src m op li (Zlength L) = Some m' /\
       dst_has m' 0 (outc ++ L) /\ xm_lxb m' = xm_lxb m /\
       (forall p, 0 <= p -> p < op \/ op + Zlength L <= p -> dcell m' p = dcell m p)).
Proof.
  split; [|split].
  - (* fast path *)
    intros src m op lr li L outc Hop Hout Hli Hreg Hdef Hr.
    pose proof (Zlength_correct L). pose proof (Zlength_correct outc). unfold XWILDCOPY in *.
    pose proof (rdef_lits _ _ _ _ _ _ Hreg Hdef) as HD.
    destruct (move_copied src lr 16 m op li) as [m1 [W1 H1]]; [lia|apply (rdef_le _ _ _ _ _ _ HD); simpl; lia|].
    simpl Z.of_nat in H1.
    exists m1. destruct (Z.gtb_spec (Zlength L) 16).
    + destruct (wild_copied src m1 (op + 16) lr (li + 16) (Zlength L - 16)) as [m' [n [W' [C' Hn]]]].
      * lia.
      * intros E; specialize (Hr E); lia.
      * lia.
      * eapply rdef_copied; [exact H1| |].
        -- intros E; specialize (Hr E); lia.
        -- apply (rdef_sub _ _ _ _ _ 16 _ HD); lia.
      * assert (Hc: copied src m m' op lr li (Z.max 16 (16 + n))).
        { eapply copied_seq; [| | |reflexivity|reflexivity| |exact H1|exact C']; try lia.
          intros E; specialize (Hr E); lia. }
        destruct (copied_out _ _ _ _ _ _ _ _ _ Hc Hop Hout Hreg) as [A [B C]]; [lia|].
        exists m'. split; [exact W1|]. split; [exact W'|]. split; [exact A|]. split; [exact B|].
        intros p Hp. apply C; lia.
    + destruct (copied_out _ _ _ _ _ _ _ _ _ H1 Hop Hout Hreg) as [A [B C]]; [lia|].
      exists m1. split; [exact W1|]. split; [reflexivity|]. split; [exact A|]. split; [exact B|].
      intros p Hp. apply C; lia.
  - (* slow path *)
    intros src m op w lr li L outc Hop Hout Hli Hreg Hdef Hw Hr.
    pose proof (Zlength_correct L). pose proof (Zlength_correct outc). unfold XWILDCOPY in *.
    pose proof (rdef_lits _ _ _ _ _ _ Hreg Hdef) as HD.
    assert (Hol: lr = R_dst -> op <= li) by (intros E; specialize (Hr E); lia).
    set (len := Zlength L) in *.
    unfold xm_safecopy. destruct (Z.ltb_spec len 8).
    + destruct (fwd_copied src lr (Z.to_nat len) m op li) as [m' [W' C']]; [lia|exact Hol| |].
      { rewrite Z2Nat.id by lia. apply (rdef_le _ _ _ _ _ _ HD); lia. }
      rewrite Z2Nat.id in C' by lia.
      destruct (copied_out _ _ _ _ _ _ _ _ _ C' Hop Hout Hreg) as [A [B C]]; [lia|].
      exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. intros p Hp. apply C; lia.
    + cbv beta iota zeta.
      destruct (Z.geb_spec (w - (op + len)) 0).
      * destruct (wild_copied src m op lr li len) as [m' [n [W' [C' Hn]]]]; [lia|exact Hol|lia| |].
        { apply (rdef_le _ _ _ _ _ _ HD); lia. }
        destruct (copied_out _ _ _ _ _ _ _ _ _ C' Hop Hout Hreg) as [A [B C]]; [lia|].
        exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. intros p Hp. apply C; lia.
      * destruct (Z.geb_spec (w - op) 0).
        -- destruct (wild_copied src m op lr li (w - op)) as [m1 [n1 [W1 [C1 Hn1]]]]; [lia|exact Hol|lia| |].
           { apply (rdef_le _ _ _ _ _ _ HD); lia. }
           rewrite W1.
           destruct (fwd_copied src lr (Z.to_nat (op + len - w)) m1 w (li + (w - op))) as [m' [W' C']].
           ++ lia.
           ++ intros E; specialize (Hr E); lia.
           ++ rewrite Z2Nat.id by lia. eapply rdef_copied; [exact C1| |].
              ** intros E; specialize (Hr E); lia.
              ** apply (rdef_sub _ _ _ _ _ (w - op) _ HD); lia.
           ++ rewrite Z2Nat.id in C' by lia.
              assert (Hc: copied src m m' op lr li (Z.max n1 ((w - op) + (op + len - w)))).
              { eapply copied_seq; [| | | |reflexivity| |exact C1|exact C']; try lia.
                intros E; specialize (Hr E); lia. }
              destruct (copied_out _ _ _ _ _ _ _ _ _ Hc Hop Hout Hreg) as [A [B C]]; [lia|].
              exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. intros p Hp. apply C; lia.
        -- replace (op + len - op) with len by lia.
           destruct (fwd_copied src lr (Z.to_nat len) m op li) as [m' [W' C']]; [lia|exact Hol| |].
           { rewrite Z2Nat.id by lia. apply (rdef_le _ _ _ _ _ _ HD); lia. }
           rewrite Z2Nat.id in C' by lia.
           destruct (copied_out _ _ _ _ _ _ _ _ _ C' Hop Hout Hreg) as [A [B C]]; [lia|].
           exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. intros p Hp. apply C; lia.
  - (* ZSTD_safecopyDstBeforeSrc *)
    intros src m op li L outc Hop Hout Hhas Hli.
    pose proof (Zlength_correct L). pose proof (Zlength_correct outc). unfold XWILDCOPY in *.
    assert (Hreg: reg_has src m R_dst li L) by exact Hhas.
    pose proof (rdef_has _ _ _ _ _ Hreg) as HD.
    assert (Hol: R_dst = R_dst -> op <= li) by (intros _; lia).
    set (len := Zlength L) in *.
    unfold xm_sdbs. cbv zeta.
    destruct (Z.gtb_spec (op - li) (-8)); [lia|]. rewrite Bool.orb_false_r.
    destruct (Z.ltb_spec len 8).
    + destruct (fwd_copied src R_dst (Z.to_nat len) m op li) as [m' [W' C']]; [lia|exact Hol| |].
      { rewrite Z2Nat.id by lia. apply (rdef_le _ _ _ _ _ _ HD); lia. }
      rewrite Z2Nat.id in C' by lia.
      destruct (copied_out _ _ _ _ _ _ _ _ _ C' Hop Hout Hreg) as [A [B C]]; [lia|].
      exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. exact C.
    + destruct (Z.ltb_spec (op - li) (-16)); [|lia]. rewrite Bool.andb_true_r.
      destruct (Z.geb_spec len 32).
      * destruct (wild_copied src m op R_dst li (len - 32)) as [m1 [n1 [W1 [C1 Hn1]]]]; [lia|exact Hol|lia| |].
        { apply (rdef_le _ _ _ _ _ _ HD); lia. }
        rewrite W1. replace (op + len - (op + len - 32)) with 32 by lia.
        destruct (fwd_copied src R_dst (Z.to_nat 32) m1 (op + len - 32) (li + len - 32)) as [m' [W' C']].
        -- lia.
        -- intros _; lia.
        -- eapply rdef_copied; [exact C1| |].
           ++ intros _; lia.
           ++ replace (li + len - 32) with (li + (len - 32)) by lia.
              apply (rdef_sub _ _ _ _ _ (len - 32) _ HD); simpl; lia.
        -- simpl Z.of_nat in C'.
           assert (Hc: copied src m m' op R_dst li (Z.max n1 ((len - 32) + 32))).
           { eapply copied_seq; [| | | | | |exact C1|exact C']; lia. }
           replace (Z.max n1 ((len - 32) + 32)) with len in Hc by lia.
           destruct (copied_out _ _ _ _ _ _ _ _ _ Hc Hop Hout Hreg) as [A [B C]]; [lia|].
           exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. exact C.
      * cbv iota. replace (op + len - op) with len by lia.
        destruct (fwd_copied src R_dst (Z.to_nat len) m op li) as [m' [W' C']]; [lia|exact Hol| |].
        { rewrite Z2Nat.id by lia. apply (rdef_le _ _ _ _ _ _ HD); lia. }
        rewrite Z2Nat.id in C' by lia.
        destruct (copied_out _ _ _ _ _ _ _ _ _ C' Hop Hout Hreg) as [A [B C]]; [lia|].
        exists m'. split; [exact W'|]. split; [exact A|]. split; [exact B|]. exact C.
Qed.
