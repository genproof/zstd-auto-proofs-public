(* A compressed block the exact model decodes (Exact.xblock) wrote all the cells of its content: the written cells
   it returns (x_written, up to the first never-written cell) reach at least op + n, the cells below op are those
   of the history it was given, litExtraBuffer keeps its length, and the size n of the block is at most the capacity:
   the output end its copies are checked against is never past dst + cap.

   The decoder's proofs need it to read the block's content out of the model's result: block_exact (DecIface)
   gives the output array's cells as the returned written cells, and the frame model (ExFrame.x_blocks) takes the
   content as their slice [op, op + n).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Coq.micromega.Lia.
Require Import Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExAgreeBlkDefs Zstd.proof.model.ExAgreeBlkShape.
Require Import Zstd.proof.model.ExAgreeBlkStore Zstd.proof.model.ExAgreeBlkLitCopy Zstd.proof.model.ExAgreeBlkLoop.
Require Import Zstd.proof.model.ExBlockWrittenHuf.
Local Open Scope Z_scope.

(* ---------- the cells a run of stores leaves written ---------- *)

(* the destination cells [0, k) are all written *)
Definition allsome (m: xmem) (k: Z) : Prop := forall p, 0 <= p < k -> dcell m p <> None.

(* m' comes from m by stores into the destination at indices >= d (and stores into litExtraBuffer, which keep
   its length): the cells below d are unchanged, no written cell becomes unwritten, and when the cells below d
   were written, so are those below e afterwards *)
Definition wf (d e: Z) (m m': xmem) : Prop :=
  Zlength (xm_lxb m') = Zlength (xm_lxb m) /\
  (forall p, 0 <= p < d -> dcell m' p = dcell m p) /\
  (forall k, allsome m k -> allsome m' k) /\
  (allsome m d -> allsome m' e).

Lemma allsome_le : forall m k k', allsome m k -> k' <= k -> allsome m k'.
Proof. intros m k k' H Hk p Hp. apply H. lia. Qed.

Lemma wf_refl : forall d e m, e <= d -> wf d e m m.
Proof.
  intros d e m He. split; [reflexivity|]. split; [reflexivity|]. split; [auto|].
  intros H. eapply allsome_le; eauto.
Qed.

Lemma wf_trans : forall d e d' e' m1 m2 m3, wf d e m1 m2 -> wf d' e' m2 m3 -> d <= d' <= e -> wf d e' m1 m3.
Proof.
  intros d e d' e' m1 m2 m3 (L1 & C1 & A1 & V1) (L2 & C2 & A2 & V2) Hd.
  split; [congruence|]. split; [intros p Hp; rewrite C2, C1 by lia; reflexivity|].
  split; [auto|]. intros H. apply V2. eapply allsome_le; [apply V1, H|lia].
Qed.

Lemma wf_weak : forall d e e' m m', wf d e m m' -> e' <= e -> wf d e' m m'.
Proof.
  intros d e e' m m' (L & C & A & V) He. split; [auto|]. split; [auto|]. split; [auto|].
  intros H. eapply allsome_le; [apply V, H|lia].
Qed.

Lemma wf_low : forall d e d' e' m m', wf d e m m' -> d' <= d -> e' <= d' -> wf d' e' m m'.
Proof.
  intros d e d' e' m m' (L & C & A & V) Hd He. split; [auto|]. split; [intros p Hp; apply C; lia|].
  split; [auto|]. intros H. eapply allsome_le; [apply A, H|lia].
Qed.

Lemma wf_same : forall d e m m', xm_dst m' = xm_dst m -> Zlength (xm_lxb m') = Zlength (xm_lxb m) -> e <= d ->
  wf d e m m'.
Proof.
  intros d e m m' Ed L He. split; [auto|]. split; [intros p Hp; unfold dcell; rewrite Ed; reflexivity|].
  split; [intros k H p Hp; unfold dcell; rewrite Ed; apply H; auto|].
  intros H p Hp. unfold dcell. rewrite Ed. apply H. lia.
Qed.

(* ---------- one store ---------- *)

Lemma wr_wf_dst : forall m i v m', xm_wr m R_dst i v = Some m' -> wf i (i + 1) m m'.
Proof.
  intros m i v m' H.
  assert (Hi: 0 <= i) by (unfold xm_wr in H; destruct (Z.ltb_spec i 0); [discriminate|lia]).
  destruct (wr_dst m i v Hi) as (m2 & E & L & C). rewrite H in E. injection E as <-.
  split; [rewrite L; reflexivity|]. split.
  - intros p Hp. rewrite C by lia. destruct (Z.eqb_spec p i); [lia|reflexivity].
  - split.
    + intros k A p Hp. rewrite C by lia. destruct (p =? i); [discriminate|apply A; auto].
    + intros A p Hp. rewrite C by lia. destruct (Z.eqb_spec p i); [discriminate|apply A; lia].
Qed.

Lemma wr_other : forall m r i v m', r <> R_dst -> xm_wr m r i v = Some m' ->
  xm_dst m' = xm_dst m /\ Zlength (xm_lxb m') = Zlength (xm_lxb m).
Proof.
  intros m r i v m' Hr H. split; [|eapply wr_lxb_len; eauto].
  unfold xm_wr in H. destruct (i <? 0); [discriminate|].
  destruct r; [congruence| |discriminate].
  destruct (i <? Zlength (xm_lxb m)); [|discriminate]. inversion H; reflexivity.
Qed.

Lemma xreg_eq_dec : forall a b : xreg, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* a store anywhere at or after a, in the destination or not *)
Lemma wr_low : forall m r i v m' a, (r = R_dst -> a <= i) -> xm_wr m r i v = Some m' -> wf a a m m'.
Proof.
  intros m r i v m' a Ha H. destruct (xreg_eq_dec r R_dst) as [->|Hr].
  - eapply wf_low; [eapply wr_wf_dst; eauto|auto|lia].
  - destruct (wr_other m r i v m' Hr H). apply wf_same; auto; lia.
Qed.

(* ---------- the copy primitives ---------- *)

Section Copies.
Variable src : list Z.

Lemma fwd_wf : forall k m d rs s m', xm_fwd src k m R_dst d rs s = Some m' -> wf d (d + Z.of_nat k) m m'.
Proof.
  induction k as [|k IH]; intros m d rs s m' H; simpl in H.
  - inversion H; subst. apply wf_refl. lia.
  - destruct (xm_rd src m rs s) as [v|]; [|discriminate].
    destruct (xm_wr m R_dst d v) as [m1|] eqn:Ew; [|discriminate].
    eapply wf_weak; [eapply wf_trans; [eapply wr_wf_dst; eauto|eapply IH; eauto|lia]|lia].
Qed.

Lemma fwd_other : forall k m rd d rs s m', rd <> R_dst -> xm_fwd src k m rd d rs s = Some m' ->
  xm_dst m' = xm_dst m /\ Zlength (xm_lxb m') = Zlength (xm_lxb m).
Proof.
  induction k as [|k IH]; intros m rd d rs s m' Hr H; simpl in H.
  - inversion H; subst. auto.
  - destruct (xm_rd src m rs s) as [v|]; [|discriminate].
    destruct (xm_wr m rd d v) as [m1|] eqn:Ew; [|discriminate].
    destruct (wr_other _ _ _ _ _ Hr Ew). destruct (IH _ _ _ _ _ _ Hr H). split; congruence.
Qed.

Lemma fwd_low : forall k m rd d rs s m' a, (rd = R_dst -> a <= d) -> xm_fwd src k m rd d rs s = Some m' ->
  wf a a m m'.
Proof.
  intros k m rd d rs s m' a Ha H. destruct (xreg_eq_dec rd R_dst) as [->|Hr].
  - eapply wf_low; [eapply fwd_wf; eauto|auto|lia].
  - destruct (fwd_other _ _ _ _ _ _ _ Hr H). apply wf_same; auto; lia.
Qed.

Lemma wrn_wf : forall vs m d m', xm_wrn vs m R_dst d = Some m' -> wf d (d + Z.of_nat (length vs)) m m'.
Proof.
  induction vs as [|v vs IH]; intros m d m' H; simpl in H.
  - inversion H; subst. apply wf_refl. simpl. lia.
  - destruct (xm_wr m R_dst d v) as [m1|] eqn:Ew; [|discriminate].
    eapply wf_weak; [eapply wf_trans; [eapply wr_wf_dst; eauto|eapply IH; eauto|lia]|simpl; lia].
Qed.

Lemma wrn_other : forall vs m rd d m', rd <> R_dst -> xm_wrn vs m rd d = Some m' ->
  xm_dst m' = xm_dst m /\ Zlength (xm_lxb m') = Zlength (xm_lxb m).
Proof.
  induction vs as [|v vs IH]; intros m rd d m' Hr H; simpl in H.
  - inversion H; subst. auto.
  - destruct (xm_wr m rd d v) as [m1|] eqn:Ew; [|discriminate].
    destruct (wr_other _ _ _ _ _ Hr Ew). destruct (IH _ _ _ _ Hr H). split; congruence.
Qed.

Lemma wrn_low : forall vs m rd d m' a, (rd = R_dst -> a <= d) -> xm_wrn vs m rd d = Some m' -> wf a a m m'.
Proof.
  intros vs m rd d m' a Ha H. destruct (xreg_eq_dec rd R_dst) as [->|Hr].
  - eapply wf_low; [eapply wrn_wf; eauto|auto|lia].
  - destruct (wrn_other _ _ _ _ _ Hr H). apply wf_same; auto; lia.
Qed.

Lemma rdn_length : forall k m r i vs, xm_rdn src k m r i = Some vs -> length vs = k.
Proof.
  induction k as [|k IH]; intros m r i vs H; simpl in H.
  - inversion H; reflexivity.
  - destruct (xm_rd src m r i); [|discriminate].
    destruct (xm_rdn src k m r (i + 1)) as [vs'|] eqn:E; [|discriminate].
    inversion H; subst. simpl. f_equal. eapply IH; eauto.
Qed.

Lemma move_wf : forall k m d rs s m', xm_move src k m R_dst d rs s = Some m' -> wf d (d + Z.of_nat k) m m'.
Proof.
  intros k m d rs s m' H. unfold xm_move in H.
  destruct (xm_rdn src k m rs s) as [vs|] eqn:E; [|discriminate].
  apply rdn_length in E. subst k. apply wrn_wf; auto.
Qed.

Lemma move_low : forall k m rd d rs s m' a, (rd = R_dst -> a <= d) -> xm_move src k m rd d rs s = Some m' ->
  wf a a m m'.
Proof.
  intros k m rd d rs s m' a Ha H. unfold xm_move in H.
  destruct (xm_rdn src k m rs s) as [vs|]; [|discriminate]. eapply wrn_low; eauto.
Qed.

Lemma chunks_wf : forall k m d rs s m', xm_chunks16 src k m d rs s = Some m' -> wf d (d + 16 * Z.of_nat k) m m'.
Proof.
  induction k as [|k IH]; intros m d rs s m' H; simpl in H.
  - inversion H; subst. apply wf_refl. lia.
  - destruct (xm_move src 16 m R_dst d rs s) as [m1|] eqn:E; [|discriminate].
    eapply wf_weak; [eapply wf_trans; [eapply move_wf; eauto|eapply IH; eauto|simpl; lia]|lia].
Qed.

Lemma wild_wf : forall m d rs s len srcb4 m', xm_wild src m d rs s len srcb4 = Some m' -> wf d (d + len) m m'.
Proof.
  intros m d rs s len srcb4 m' H. unfold xm_wild in H.
  destruct (srcb4 && (d - s <? 16))%bool.
  - apply fwd_wf in H. eapply wf_weak; [exact H|].
    rewrite Z2Nat.id by lia. assert (len <= 8 * ((len + 7) / 8)) by (Z.div_mod_to_equations; lia). lia.
  - apply chunks_wf in H. eapply wf_weak; [exact H|].
    destruct (Z.leb_spec len 16).
    + simpl. lia.
    + assert (len - 16 <= 32 * ((len - 16 + 31) / 32)) by (Z.div_mod_to_equations; lia).
      assert (0 <= (len - 16 + 31) / 32) by (apply Z.div_pos; lia).
      rewrite Z2Nat.id by lia. lia.
Qed.

Lemma ov8_wf : forall m op ip off m' op' ip', xm_ov8 src m op ip off = Some (m', op', ip') ->
  op' = op + 8 /\ wf op (op + 8) m m'.
Proof.
  intros m op ip off m' op' ip' H. unfold xm_ov8 in H.
  destruct (off <? 8).
  - destruct (xm_fwd src 4 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_fwd src 4 m1 R_dst (op + 4) R_dst _) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. split; [reflexivity|].
    apply fwd_wf in E1. apply fwd_wf in E2. simpl in E1, E2.
    eapply wf_weak; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
  - destruct (xm_fwd src 8 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    inversion H; subst. split; [reflexivity|]. apply fwd_wf in E1. exact E1.
Qed.

Lemma fwd_wf' : forall n m d rs s m', xm_fwd src (Z.to_nat n) m R_dst d rs s = Some m' -> wf d (d + n) m m'.
Proof.
  intros n m d rs s m' H. apply fwd_wf in H. eapply wf_weak; [exact H|]. lia.
Qed.

Lemma safecopy_wf : forall m op oend_w rs ip len srcb4 m',
  xm_safecopy src m op oend_w rs ip len srcb4 = Some m' -> wf op (op + len) m m'.
Proof.
  intros m op oend_w rs ip len srcb4 m' H. unfold xm_safecopy in H.
  destruct (Z.ltb_spec len 8) as [Hl|Hl]; [apply fwd_wf' in H; exact H|].
  assert (Hp: exists m1 op1 ip1, (if srcb4 then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) = Some (m1, op1, ip1)
              /\ wf op op1 m m1 /\ op1 + (if srcb4 then len - 8 else len) = op + len /\ op <= op1 <= op + len).
  { destruct srcb4.
    - destruct (xm_ov8 src m op ip (op - ip)) as [[[m1 op1] ip1]|] eqn:E; [|discriminate].
      apply ov8_wf in E. destruct E as [-> W]. exists m1, (op + 8), ip1. refine (conj eq_refl (conj W _)). lia.
    - exists m, op, ip. refine (conj eq_refl (conj (wf_refl _ _ _ (Z.le_refl _)) _)). lia. }
  destruct Hp as (m1 & op1 & ip1 & E & W1 & Hs & Ho). rewrite E in H.
  set (len1 := if srcb4 then len - 8 else len) in *. clearbody len1.
  destruct (oend_w - (op + len) >=? 0).
  - apply wild_wf in H. eapply wf_weak; [eapply wf_trans; [exact W1|exact H|lia]|lia].
  - destruct (Z.geb_spec (oend_w - op1) 0) as [Hw|Hw].
    + destruct (xm_wild src m1 op1 rs ip1 (oend_w - op1) srcb4) as [m2|] eqn:E2; [|discriminate].
      apply wild_wf in E2. apply fwd_wf' in H.
      eapply wf_weak; [eapply wf_trans; [eapply wf_trans; [exact W1|exact E2|lia]|exact H|lia]|lia].
    + apply fwd_wf' in H. eapply wf_weak; [eapply wf_trans; [exact W1|exact H|lia]|lia].
Qed.

Lemma sdbs_wf : forall m op ip len m', xm_sdbs src m op ip len = Some m' -> wf op (op + len) m m'.
Proof.
  intros m op ip len m' H. unfold xm_sdbs in H.
  destruct ((len <? 8) || (op - ip >? -8))%bool; [apply fwd_wf' in H; exact H|].
  destruct ((len >=? 32) && (op - ip <? -16))%bool eqn:Ec.
  - apply andb_prop in Ec. destruct Ec as [E1 _]. apply Z.geb_le in E1.
    destruct (xm_wild src m op R_dst ip (len - 32) false) as [m1|] eqn:E2; [|discriminate].
    apply wild_wf in E2. apply fwd_wf' in H.
    eapply wf_weak; [eapply wf_trans; [exact E2|exact H|lia]|lia].
  - apply fwd_wf' in H. eapply wf_weak; [exact H|lia].
Qed.
End Copies.

(* ---------- one sequence ---------- *)

Lemma prefix_wf : forall e m op mt ml off wo m', xm_prefix e m op mt ml off wo = Some m' -> wf op (op + ml) m m'.
Proof.
  intros e m op mt ml off wo m' H. unfold xm_prefix in H. destruct wo as [w|].
  - eapply safecopy_wf; eauto.
  - destruct (off >=? 16); [eapply wild_wf; eauto|].
    destruct (xm_ov8 (xe_src e) m op mt off) as [[[m1 op1] mt1]|] eqn:E; [|discriminate].
    apply ov8_wf in E. destruct E as [-> W].
    destruct (Z.gtb_spec ml 8).
    + apply wild_wf in H. eapply wf_weak; [eapply wf_trans; [exact W|exact H|lia]|lia].
    + inversion H; subst. eapply wf_weak; [exact W|lia].
Qed.

Lemma match_wf : forall e m oLitEnd ml off wo m', xm_match e m oLitEnd ml off wo = Some m' ->
  wf oLitEnd (oLitEnd + ml) m m'.
Proof.
  intros e m oLitEnd ml off wo m' H. unfold xm_match in H.
  destruct (Z.gtb_spec off (oLitEnd - xe_ps e)) as [Ho|Ho]; [|eapply prefix_wf; eauto].
  destruct (off >? oLitEnd - xe_vs e); [discriminate|].
  destruct (Z.geb_spec (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e))) ml).
  - apply move_wf in H. eapply wf_weak; [exact H|lia].
  - destruct (xm_move (xe_src e) (Z.to_nat (xe_de e - (xe_de e + (oLitEnd - off - xe_ps e)))) m R_dst oLitEnd R_dst _)
      as [m1|] eqn:E; [|discriminate].
    apply move_wf in E. apply prefix_wf in H. rewrite Z2Nat.id in E by lia.
    eapply wf_weak; [eapply wf_trans; [exact E|exact H|lia]|lia].
Qed.

Lemma exec_wf : forall e m op lr li llim ll ml off m' op' li', 0 <= ll ->
  x_exec e m op lr li llim ll ml off = Some (m', op', li') ->
  wf op (op + ll + ml) m m' /\ op' = op + ll + ml /\ li' = li + ll /\ li' <= llim.
Proof.
  intros e m op lr li llim ll ml off m' op' li' Hll H. unfold x_exec in H. cbv zeta in H.
  destruct (Z.ltb_spec (llim - li) ll) as [Hc|Hc]; cbn [orb] in H.
  - (* slow path *)
    destruct (ll + ml >? xe_oend e - op); [discriminate|].
    destruct (Z.gtb_spec ll (llim - li)); [discriminate|].
    destruct (xm_safecopy (xe_src e) m op (xe_oend e - XWILDCOPY) lr li ll false) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. apply safecopy_wf in E1. apply match_wf in E2.
    split; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
  - destruct (xe_oend e - XWILDCOPY - op <? ll + ml); cbn [orb] in H.
    + (* slow path *)
      destruct (ll + ml >? xe_oend e - op); [discriminate|].
      destruct (Z.gtb_spec ll (llim - li)); [discriminate|].
      destruct (xm_safecopy (xe_src e) m op (xe_oend e - XWILDCOPY) lr li ll false) as [m1|] eqn:E1; [|discriminate].
      destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
      inversion H; subst. apply safecopy_wf in E1. apply match_wf in E2.
      split; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
    + (* fast path *)
      destruct (xm_move (xe_src e) 16 m R_dst op lr li) as [m1|] eqn:E1; [|discriminate].
      destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) lr (li + 16) (ll - 16) false else Some m1)
        as [m2|] eqn:E2; [|discriminate].
      assert (W2: wf op (op + ll) m m2).
      { apply move_wf in E1. destruct (Z.gtb_spec ll 16).
        - apply wild_wf in E2. eapply wf_weak; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
        - inversion E2; subst. eapply wf_weak; [exact E1|lia]. }
      destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:E3; [|discriminate].
      inversion H; subst. apply match_wf in E3. split; [eapply wf_trans; [exact W2|exact E3|lia]|lia].
Qed.

Lemma exec_split_wf : forall e m op li llim ll ml off m' op' li', 0 <= ll ->
  x_exec_split e m op li llim ll ml off = Some (m', op', li') ->
  wf op (op + ll + ml) m m' /\ op' = op + ll + ml /\ li' = li + ll /\ li' <= llim.
Proof.
  intros e m op li llim ll ml off m' op' li' Hll H. unfold x_exec_split in H. cbv zeta in H.
  destruct (Z.ltb_spec (llim - li) ll) as [Hc|Hc]; cbn [orb] in H.
  - (* slow path *)
    destruct (ll + ml >? xe_oend e - op); [discriminate|].
    destruct (Z.gtb_spec ll (llim - li)); [discriminate|].
    destruct ((op >? li) && (op <? li + ll))%bool; [discriminate|].
    destruct (xm_sdbs (xe_src e) m op li ll) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. apply sdbs_wf in E1. apply match_wf in E2.
    split; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
  - destruct (li + ll - XWILDCOPY - op <? ll + ml); cbn [orb] in H.
    + (* slow path *)
      destruct (ll + ml >? xe_oend e - op); [discriminate|].
      destruct (Z.gtb_spec ll (llim - li)); [discriminate|].
      destruct ((op >? li) && (op <? li + ll))%bool; [discriminate|].
      destruct (xm_sdbs (xe_src e) m op li ll) as [m1|] eqn:E1; [|discriminate].
      destruct (xm_match e m1 (op + ll) ml off _) as [m2|] eqn:E2; [|discriminate].
      inversion H; subst. apply sdbs_wf in E1. apply match_wf in E2.
      split; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
    + (* fast path *)
      destruct (xm_move (xe_src e) 16 m R_dst op R_dst li) as [m1|] eqn:E1; [|discriminate].
      destruct (if ll >? 16 then xm_wild (xe_src e) m1 (op + 16) R_dst (li + 16) (ll - 16) false else Some m1)
        as [m2|] eqn:E2; [|discriminate].
      assert (W2: wf op (op + ll) m m2).
      { apply move_wf in E1. destruct (Z.gtb_spec ll 16).
        - apply wild_wf in E2. eapply wf_weak; [eapply wf_trans; [exact E1|exact E2|lia]|lia].
        - inversion E2; subst. eapply wf_weak; [exact E1|lia]. }
      destruct (xm_match e m2 (op + ll) ml off None) as [m3|] eqn:E3; [|discriminate].
      inversion H; subst. apply match_wf in E3. split; [eapply wf_trans; [exact W2|exact E3|lia]|lia].
Qed.

(* ---------- the sequence loop and the last literals ---------- *)

Lemma step_wf : forall e s ll ml off s', 0 <= ll -> 0 <= ml -> xli s <= xlim s ->
  x_step e s ll ml off = Some s' ->
  wf (xop s) (xop s') (xmm s) (xmm s') /\ xop s <= xop s' /\ xli s' <= xlim s'.
Proof.
  intros e s ll ml off s' Hll Hml Hi H. unfold x_step in H. cbv zeta in H.
  destruct (xsp s).
  - destruct (Z.ltb_spec (xlim s - xli s) ll).
    + destruct (Z.eqb_spec (xlim s - xli s) 0) as [E0|E0].
      * cbv iota beta in H.
        destruct (x_exec e (xmm s) (xop s) R_lxb 0 XLITEXTRA (ll - (xlim s - xli s)) ml off)
          as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
        apply exec_wf in Ex; [|lia]. destruct Ex as (W & -> & -> & Hl).
        inversion H; subst; cbn [xop xmm xli xlim]. split; [eapply wf_weak; [exact W|lia]|lia].
      * destruct (xlim s - xli s >? xe_oend e - xop s); [discriminate|].
        destruct (xm_sdbs (xe_src e) (xmm s) (xop s) (xli s) (xlim s - xli s)) as [m1|] eqn:Es; [|discriminate].
        cbv iota beta in H.
        destruct (x_exec e m1 (xop s + (xlim s - xli s)) R_lxb 0 XLITEXTRA (ll - (xlim s - xli s)) ml off)
          as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
        apply sdbs_wf in Es. apply exec_wf in Ex; [|lia]. destruct Ex as (W & -> & -> & Hl).
        inversion H; subst; cbn [xop xmm xli xlim].
        split; [eapply wf_weak; [eapply wf_trans; [exact Es|exact W|lia]|lia]|lia].
    + destruct (x_exec_split e (xmm s) (xop s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
        [|discriminate].
      apply exec_split_wf in Ex; [|lia]. destruct Ex as (W & -> & -> & Hl).
      inversion H; subst; cbn [xop xmm xli xlim]. split; [eapply wf_weak; [exact W|lia]|lia].
  - destruct (x_exec e (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
      [|discriminate].
    apply exec_wf in Ex; [|lia]. destruct Ex as (W & -> & -> & Hl).
    inversion H; subst; cbn [xop xmm xli xlim]. split; [eapply wf_weak; [exact W|lia]|lia].
Qed.

(* a sequence ZSTD_decodeSequence decodes has nonnegative literal and match lengths, whatever its tables *)
Lemma dseq_nonneg : forall tLL tOF tML V last sLL sOF sML pos sq st pos',
  dseq_one tLL tOF tML V last sLL sOF sML pos = Some (sq, st, pos') -> 0 <= sq_ll sq /\ 0 <= sq_ml sq.
Proof.
  intros tLL tOF tML V last sLL sOF sML pos sq st pos' H. unfold dseq_one in H.
  destruct (rd V pos _) as [[eOF p1]|] eqn:R1; [|discriminate].
  destruct (rd V p1 _) as [[eML p2]|] eqn:R2; [|discriminate].
  destruct (rd V p2 _) as [[eLL p3]|] eqn:R3; [|discriminate].
  apply loop_rd_bounds in R2; [|apply loop_nth_nonneg; unfold ML_bits_tab; repeat (constructor; [lia|]); constructor].
  apply loop_rd_bounds in R3; [|apply loop_nth_nonneg; unfold LL_bits_tab; repeat (constructor; [lia|]); constructor].
  pose proof (loop_LL_base_nonneg (Z.to_nat (fe_sym (fse_cell tLL sLL)))).
  pose proof (loop_ML_base_nonneg (Z.to_nat (fe_sym (fse_cell tML sML)))).
  cbv zeta in H.
  set (bL := nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_base_tab 0) in *.
  set (bM := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0) in *.
  clearbody bL bM.
  destruct last.
  - inversion H; subst; clear H. cbn [sq_ll sq_ml]. lia.
  - destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
    destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
    destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
    inversion H; subst; clear H. cbn [sq_ll sq_ml]. lia.
Qed.

Lemma loop_wf : forall e tLL tOF tML V k st pos rep s s' pos' rep', xli s <= xlim s ->
  x_seq_loop dseq_one c_offset e tLL tOF tML V k st pos rep s = Some (s', pos', rep') ->
  wf (xop s) (xop s') (xmm s) (xmm s') /\ xop s <= xop s' /\ xli s' <= xlim s'.
Proof.
  intros e tLL tOF tML V k. induction k as [|k IH]; intros st pos rep s s' pos' rep' Hi H;
    destruct st as [[sLL sOF] sML]; simpl in H.
  - inversion H; subst. split; [apply wf_refl; lia|lia].
  - destruct (dseq_one tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos) as [[[sq st1] pos1]|] eqn:E1; [|discriminate].
    destruct (c_offset rep (sq_ll sq) (sq_ov sq)) as [off rep1].
    destruct (x_step e s (sq_ll sq) (sq_ml sq) off) as [s1|] eqn:Es; [|discriminate].
    apply dseq_nonneg in E1. destruct E1.
    apply step_wf in Es; auto. destruct Es as (W1 & O1 & I1).
    destruct (IH _ _ _ _ _ _ _ I1 H) as (W2 & O2 & I2).
    split; [eapply wf_trans; [exact W1|exact W2|lia]|lia].
Qed.

Lemma last_wf : forall e s m op', xli s <= xlim s -> x_last e s = Some (m, op') ->
  wf (xop s) op' (xmm s) m /\ xop s <= op' /\ op' <= xe_oend e.
Proof.
  intros e s m op' Hi H. pose proof (x_last_shape _ _ _ _ H) as [Ho Hoe]. unfold xcnt in Ho.
  unfold x_last in H. cbv zeta in H.
  destruct (xsp s) eqn:Esp.
  - destruct (xlim s - xli s >? xe_oend e - xop s); [discriminate|].
    destruct (xm_move (xe_src e) (Z.to_nat (xlim s - xli s)) (xmm s) R_dst (xop s) R_dst (xli s)) as [m1|] eqn:E1;
      [|discriminate].
    cbv iota beta zeta in H.
    destruct (XLITEXTRA - 0 >? _); [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. apply move_wf in E1. apply fwd_wf' in E2. rewrite Z2Nat.id in E1 by lia.
    split; [eapply wf_weak; [eapply wf_trans; [exact E1|exact E2|lia]|lia]|unfold XLITEXTRA in *; lia].
  - cbv iota beta zeta in H. destruct (_ >? _); [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. apply fwd_wf' in E2. split; [eapply wf_weak; [exact E2|lia]|lia].
Qed.

Lemma seqs_wf : forall e tabs rep bits nbSeq s0 m op' rep', xli s0 <= xlim s0 ->
  x_seqs dseq_one c_offset e tabs rep bits nbSeq s0 = Some (m, op', rep') ->
  wf (xop s0) op' (xmm s0) m /\ xop s0 <= op' /\ op' <= xe_oend e.
Proof.
  intros e tabs rep bits nbSeq s0 m op' rep' Hi H. destruct tabs as [[tLL tOF] tML]. unfold x_seqs in H.
  destruct (negb (bs_okb bits)); [discriminate|].
  destruct (rd bits (bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[s1 pos] r]|] eqn:El; [|discriminate].
  destruct (negb (pos =? 0)); [discriminate|].
  destruct (x_last e s1) as [[m1 o1]|] eqn:Ex; [|discriminate].
  inversion H; subst.
  apply loop_wf in El; auto. destruct El as (W1 & O1 & I1). apply last_wf in Ex; auto. destruct Ex as (W2 & O2 & E2).
  split; [eapply wf_trans; [exact W1|exact W2|lia]|lia].
Qed.

(* ---------- the literals section ---------- *)

(* the literals of a section number at most wmax = MIN(blockSizeMax, dstCapacity) (when it is positive) *)
Lemma lits_len : forall h b bsm wmax str lits lused huf,
  x_lits xhuf x_lits_huf h b bsm wmax str = Some (lits, lused, huf) -> Zlength lits <= Z.max 0 wmax.
Proof.
  intros h b bsm wmax str lits lused huf H. unfold x_lits in H. cbv zeta in H.
  revert H. destruct (Zlength b <? 2); [discriminate|].
  destruct (Z.land (byte_at b 0) 3 =? 0).
  - destruct (_ && _)%bool; [discriminate|].
    match goal with |- context [match ?p with pair _ _ => _ end] => destruct p as [lh ls] end.
    destruct (ls >? bsm); [discriminate|]. destruct (Z.ltb_spec wmax ls); [discriminate|].
    destruct (lh + ls >? Zlength b); [discriminate|].
    intros Hx; injection Hx; intros; subst. unfold slice. rewrite Zlength_correct, firstn_length. lia.
  - destruct (Z.land (byte_at b 0) 3 =? 1).
    + destruct (_ && _)%bool; [discriminate|]. destruct (_ && _)%bool; [discriminate|].
      match goal with |- context [match ?p with pair _ _ => _ end] => destruct p as [lh ls] end.
      destruct (ls >? bsm); [discriminate|]. destruct (Z.ltb_spec wmax ls); [discriminate|].
      intros Hx; injection Hx; intros; subst. rewrite Zlength_correct, repeat_length. lia.
    + destruct (_ && _)%bool; [discriminate|]. destruct (Zlength b <? 5); [discriminate|].
      match goal with |- context [match ?p with pair _ _ => _ end] => destruct p as [[[lh ls] cs] single] end.
      destruct (ls >? bsm); [discriminate|]. destruct (_ && _)%bool; [discriminate|].
      destruct (cs + lh >? Zlength b); [discriminate|]. destruct (Z.ltb_spec wmax ls); [discriminate|].
      match goal with |- context [match x_lits_huf ?a ?b ?c ?d ?e with _ => _ end] =>
        destruct (x_lits_huf a b c d e) as [[l t]|] eqn:Eh; [|discriminate] end.
      intros Hx; injection Hx; intros; subst. apply x_lits_huf_len in Eh. lia.
Qed.


(* ---------- the literals' stores ---------- *)

Lemma wf_aa : forall a m1 m2 m3, wf a a m1 m2 -> wf a a m2 m3 -> wf a a m1 m3.
Proof. intros a m1 m2 m3 W1 W2. eapply wf_trans; [exact W1|exact W2|lia]. Qed.

Ltac ls_side := intros ?Hr; try discriminate; unfold x_split_L0, XLITEXTRA, XWILDCOPY in *; lia.

(* one store run (or one condition) of x_lits_store, each run shown to write at or after a *)
Ltac ls_step a :=
  match goal with
  | |- context [match xm_wrn ?vs ?mm ?r ?d with _ => _ end] =>
      let E := fresh "W" in destruct (xm_wrn vs mm r d) as [?|] eqn:E;
      [apply (wrn_low vs mm r d _ a) in E; [|ls_side] | discriminate]
  | |- context [match xm_fwd ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end] =>
      let E := fresh "W" in destruct (xm_fwd sr k mm rd d rs s) as [?|] eqn:E;
      [apply (fwd_low sr k mm rd d rs s _ a) in E; [|ls_side] | discriminate]
  | |- context [match xm_move ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end] =>
      let E := fresh "W" in destruct (xm_move sr k mm rd d rs s) as [?|] eqn:E;
      [apply (move_low sr k mm rd d rs s _ a) in E; [|ls_side] | discriminate]
  | |- context [if ?c then _ else _] => let C := fresh "C" in destruct c eqn:C
  end.

(* The literals section's stores write at or after the block's start op0 (given that a split section, more
   than XLITEXTRA literals, fits the expected write size ews), and leave the literal pointer at or before
   its limit. *)
Lemma lits_store_wf : forall body lits lused m op0 ews bsm cap str m' lr li lim sp,
  0 <= op0 -> 0 <= bsm -> (XLITEXTRA < Zlength lits -> Zlength lits <= ews) ->
  x_lits_store body lits lused m op0 ews bsm cap str = Some (m', lr, li, lim, sp) ->
  wf op0 op0 m m' /\ li <= lim.
Proof.
  intros body lits lused m op0 ews bsm cap str m' lr li lim sp Hop Hb Hl H.
  pose proof (Zlen_nonneg lits) as Hn.
  assert (Hs: x_alloc_loc cap (Zlength lits) bsm str = XL_split -> XLITEXTRA < Zlength lits <= ews).
  { intros Eloc. unfold x_alloc_loc in Eloc. destruct (negb str && _)%bool; [discriminate|].
    destruct (Z.leb_spec (Zlength lits) XLITEXTRA); [discriminate|]. split; [lia|apply Hl; lia]. }
  unfold x_lits_store in H. cbv zeta in H. revert H.
  destruct (x_alloc_loc cap (Zlength lits) bsm str) eqn:Eloc.
  all: try (specialize (Hs eq_refl)).
  all: cbv beta iota delta [xl_is_split].
  all: repeat (ls_step op0; cbv beta iota).
  all: intros Hx; injection Hx; intros; subst; split.
  all: try (repeat (eapply wf_aa; [eassumption|]); apply wf_refl; lia).
  all: try (unfold x_split_L0, XLITEXTRA, XWILDCOPY in *; lia).
  (* the case of literals placed at once (types 0, 1) whose type is neither 0 nor 1 does not arise *)
  all: assert (0 <= Z.land (byte_at body 0) 3) by (apply Z.land_nonneg; right; lia); bool2prop; lia.
Qed.


(* ---------- the block ---------- *)

(* the output end of a block is at most dst + dstCapacity: literals after the block's room are chosen only
   when the capacity exceeds the room *)
Lemma oend_cap : forall b lused litSize bsm cap str op, 0 <= litSize ->
  match x_litloc b lused litSize bsm cap str with XL_in_dst => op + bsm + XWILDCOPY | _ => op + cap end
  <= op + cap.
Proof.
  intros b lused litSize bsm cap str op Hl. unfold x_litloc.
  destruct (_ && _)%bool; [lia|]. unfold x_alloc_loc.
  destruct (negb str && (cap >? bsm + XWILDCOPY + litSize + XWILDCOPY))%bool eqn:E.
  - apply andb_prop in E. destruct E as [_ E]. apply gtb_lt' in E. unfold XWILDCOPY in *. lia.
  - destruct (_ <=? _); lia.
Qed.

(* a list of destination cells whose first k are written has at least k written cells *)
Lemma written_len : forall d k, (forall p, 0 <= p < k -> nth (Z.to_nat p) d None <> None) ->
  k <= Zlength (x_written d).
Proof.
  induction d as [|c d IH]; intros k H.
  - destruct (Z.leb_spec k 0); [simpl; rewrite Zlength_nil; lia|]. exfalso. apply (H 0); [lia|reflexivity].
  - destruct c as [v|].
    + simpl. rewrite Zlength_cons. assert (k - 1 <= Zlength (x_written d)); [|lia]. apply IH.
      intros p Hp. specialize (H (p + 1) ltac:(lia)).
      replace (Z.to_nat (p + 1)) with (S (Z.to_nat p)) in H by lia. exact H.
    + destruct (Z.leb_spec k 0); [simpl; rewrite Zlength_nil; lia|]. exfalso. apply (H 0); [lia|reflexivity].
Qed.

(* the conclusion, from the stores of the whole block: those of the literals section at or after op, then
   the sequences' and last literals' covering [op, op') *)
Lemma block_final : forall mem L op op' m1 m, 0 <= op <= Zlength mem -> op <= op' ->
  wf op op {| xm_dst := map Some mem; xm_lxb := L |} m1 -> wf op op' m1 m ->
  op + (op' - op) <= Zlength (x_written (xm_dst m)) /\
  firstn (Z.to_nat op) (x_written (xm_dst m)) = firstn (Z.to_nat op) mem /\ Zlength (xm_lxb m) = Zlength L.
Proof.
  intros mem L op op' m1 m Hop Ho W1 W2.
  pose proof (wf_trans _ _ _ _ _ _ _ W1 W2 ltac:(lia)) as (L1 & C & A & V).
  assert (Hc: forall k, (k < Z.to_nat op)%nat -> nth k (map Some mem) None = Some (nth k mem 0)).
  { intros k Hk. rewrite (nth_indep _ None (Some 0)) by (rewrite map_length; rewrite Zlength_correct in Hop; lia).
    apply map_nth. }
  assert (A0: allsome {| xm_dst := map Some mem; xm_lxb := L |} op).
  { intros p Hp. unfold dcell. cbn [xm_dst]. rewrite Hc by lia. discriminate. }
  split; [pose proof (written_len (xm_dst m) op' (V A0)); lia|].
  split; [|exact L1].
  assert (Hl: length (firstn (Z.to_nat op) mem) = Z.to_nat op)
    by (rewrite firstn_length; rewrite Zlength_correct in Hop; lia).
  rewrite <- Hl at 1. apply x_written_prefix. intros k Hk. rewrite Hl in Hk.
  specialize (C (Z.of_nat k) ltac:(lia)). unfold dcell in C. rewrite Nat2Z.id in C. rewrite C. cbn [xm_dst].
  rewrite Hc by lia. f_equal.
  rewrite <- (firstn_skipn (Z.to_nat op) mem) at 1. rewrite app_nth1 by lia. reflexivity.
Qed.


(* the same, with the size bounded by the capacity (a size the decoder returns is never read as an error code) *)
Lemma xblock_written_cap (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  0 <= op <= Zlength mem ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  0 <= n <= cap /\ op + n <= Zlength m' /\ firstn (Z.to_nat op) m' = firstn (Z.to_nat op) mem /\
  Zlength (x_lxb xhuf st') = Zlength (x_lxb xhuf st).
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
  apply lits_store_wf in Es; [|lia|pose proof (Zlen_nonneg body); lia|intros; unfold XLITEXTRA in *; lia].
  destruct Es as [W0 I0].
  pose proof (oend_cap body lused (Zlength lits) bsm cap str op (Zlen_nonneg lits)) as Hoe.
  destruct (nbSeq =? 0).
  - match goal with |- context [match x_last ?e ?s with _ => _ end] =>
      destruct (x_last e s) as [[m1 op1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply last_wf in Ex; [|cbn [xli xlim]; lia]. cbn [xop xmm xe_oend] in Ex. destruct Ex as (W & O & E).
    destruct (block_final mem (x_lxb xhuf st) op op1 m m1 Hop O W0 W) as (F1 & F2 & F3).
    cbn [x_lxb]. split; [lia|]. split; [exact F1|]. split; [exact F2|exact F3].
  - destruct tabs as [t|]; [|discriminate].
    match goal with |- context [match x_seqs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 with _ => _ end] =>
      destruct (x_seqs a1 a2 a3 a4 a5 a6 a7 a8) as [[[m1 op1] rep1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply seqs_wf in Ex; [|cbn [xli xlim]; lia]. cbn [xop xmm xe_oend] in Ex. destruct Ex as (W & O & E).
    destruct (block_final mem (x_lxb xhuf st) op op1 m m1 Hop O W0 W) as (F1 & F2 & F3).
    cbn [x_lxb]. split; [lia|]. split; [exact F1|]. split; [exact F2|exact F3].
Qed.

Lemma xblock_written (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z) (str: bool)
    (n: Z) :
  0 <= op <= Zlength mem ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  0 <= n /\ op + n <= Zlength m' /\ firstn (Z.to_nat op) m' = firstn (Z.to_nat op) mem /\
  Zlength (x_lxb xhuf st') = Zlength (x_lxb xhuf st).
Proof.
  intros Hop H. destruct (xblock_written_cap st st' mem m' ps op ds de body bsm cap str n Hop H) as (Hn & R).
  split; [lia|exact R].
Qed.
