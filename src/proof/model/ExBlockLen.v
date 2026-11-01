(* A compressed block decoded in streaming mode (Exact.xblock with streaming = true) into a destination region that
   has its whole capacity after op (op + cap <= |mem|) returns as many written cells as it was given: every store
   of the block lands below op + cap (the literals section stays in litExtraBuffer or, split, below
   op + MIN(bsm, cap); the sequences' copies, wild copies included, stay below the output end op + cap; the last
   literals are checked against it), so no cell is appended to the region and none becomes unwritten.

   The stream model (model/ExStream.v) decodes compressed blocks into its output ring at outStart with the capacity
   outBuffSize - outStart: this is what keeps the ring at outBuffSize cells (ExStreamFacts.zinv).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.ExHuf Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Coq.micromega.Lia.
Require Import Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExCSeq.
Local Open Scope Z_scope.


(* ---------- the destination region keeps its length and stays written ---------- *)

Section Len.
(* the number of cells of the destination region *)
Variable L : Z.

(* the region has exactly L cells, all written: stores below L keep it so (an in-place update) *)
Definition dok (m: xmem) : Prop := Zlength (xm_dst m) = L /\ Forall (fun c => c <> None) (xm_dst m).

Lemma upd_Zlen : forall {A} (l: list A) i x, Zlength (upd l i x) = Zlength l.
Proof.
  intros A l. induction l as [|y l IH]; intros i x; [reflexivity|].
  destruct i; simpl; rewrite !Zlength_cons; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma upd_Forall_some : forall (l: list (option Z)) i v,
  Forall (fun c => c <> None) l -> Forall (fun c => c <> None) (upd l i (Some v)).
Proof.
  induction l as [|y l IH]; intros i v H; [constructor|].
  inversion H; subst. destruct i; simpl; constructor; auto; discriminate.
Qed.

Lemma wr_ok : forall m r i v m', dok m -> xm_wr m r i v = Some m' -> (r = R_dst -> i < L) -> dok m'.
Proof.
  intros m r i v m' [Hl Hf] H Hb. unfold xm_wr in H.
  destruct (i <? 0) eqn:Ei; [discriminate|]. apply Z.ltb_ge in Ei.
  destruct r.
  - specialize (Hb eq_refl). destruct (Z.ltb_spec i (Zlength (xm_dst m))); [|lia].
    inversion H; subst; clear H. split; cbn [xm_dst].
    + rewrite upd_Zlen. exact Hl.
    + apply upd_Forall_some; auto.
  - destruct (i <? Zlength (xm_lxb m)); [|discriminate]. inversion H; subst. split; auto.
  - discriminate.
Qed.

Section Copies.
Variable src : list Z.

Lemma fwd_ok : forall k m rd d rs s m', dok m -> xm_fwd src k m rd d rs s = Some m' ->
  (rd = R_dst -> (0 < k)%nat -> d + Z.of_nat k <= L) -> dok m'.
Proof.
  induction k as [|k IH]; intros m rd d rs s m' Hm H Hb; simpl in H.
  - inversion H; subst; auto.
  - destruct (xm_rd src m rs s) as [v|]; [|discriminate].
    destruct (xm_wr m rd d v) as [m1|] eqn:Ew; [|discriminate].
    eapply IH; [eapply wr_ok; [exact Hm|exact Ew|]|exact H|].
    + intros Hr. specialize (Hb Hr ltac:(lia)). lia.
    + intros Hr Hk. specialize (Hb Hr ltac:(lia)). lia.
Qed.

(* a forward copy of n bytes (n an integer) at d *)
Lemma fwd_ok' : forall n m rd d rs s m', dok m -> xm_fwd src (Z.to_nat n) m rd d rs s = Some m' ->
  (rd = R_dst -> 0 < n -> d + n <= L) -> dok m'.
Proof.
  intros n m rd d rs s m' Hm H Hb. eapply fwd_ok; [exact Hm|exact H|].
  intros Hr Hk. assert (0 < n) by lia. rewrite Z2Nat.id by lia. apply Hb; [exact Hr|lia].
Qed.

Lemma wrn_ok : forall vs m rd d m', dok m -> xm_wrn vs m rd d = Some m' ->
  (rd = R_dst -> (0 < length vs)%nat -> d + Z.of_nat (length vs) <= L) -> dok m'.
Proof.
  induction vs as [|v vs IH]; intros m rd d m' Hm H Hb; simpl in H.
  - inversion H; subst; auto.
  - destruct (xm_wr m rd d v) as [m1|] eqn:Ew; [|discriminate]. simpl in Hb.
    eapply IH; [eapply wr_ok; [exact Hm|exact Ew|]|exact H|].
    + intros Hr. specialize (Hb Hr ltac:(lia)). lia.
    + intros Hr Hk. specialize (Hb Hr ltac:(lia)). lia.
Qed.

Lemma rdn_length : forall k m r i vs, xm_rdn src k m r i = Some vs -> length vs = k.
Proof.
  induction k as [|k IH]; intros m r i vs H; simpl in H.
  - inversion H; reflexivity.
  - destruct (xm_rd src m r i); [|discriminate].
    destruct (xm_rdn src k m r (i + 1)) as [vs'|] eqn:E; [|discriminate].
    inversion H; subst. simpl. f_equal. eapply IH; eauto.
Qed.

Lemma move_ok : forall k m rd d rs s m', dok m -> xm_move src k m rd d rs s = Some m' ->
  (rd = R_dst -> (0 < k)%nat -> d + Z.of_nat k <= L) -> dok m'.
Proof.
  intros k m rd d rs s m' Hm H Hb. unfold xm_move in H.
  destruct (xm_rdn src k m rs s) as [vs|] eqn:E; [|discriminate].
  apply rdn_length in E. subst k. eapply wrn_ok; eauto.
Qed.

Lemma chunks_ok : forall k m d rs s m', dok m -> xm_chunks16 src k m d rs s = Some m' ->
  d + 16 * Z.of_nat k <= L -> dok m'.
Proof.
  induction k as [|k IH]; intros m d rs s m' Hm H Hb; simpl in H.
  - inversion H; subst; auto.
  - destruct (xm_move src 16 m R_dst d rs s) as [m1|] eqn:E; [|discriminate].
    eapply IH; [eapply move_ok; [exact Hm|exact E|]|exact H|]; intros; lia.
Qed.

(* ZSTD_wildcopy writes at most 16 bytes, or len + 31 *)
Lemma wild_ok : forall m d rs s len srcb4 m', dok m -> xm_wild src m d rs s len srcb4 = Some m' ->
  d + Z.max 16 (len + 31) <= L -> dok m'.
Proof.
  intros m d rs s len srcb4 m' Hm H Hb. unfold xm_wild in H.
  destruct (srcb4 && (d - s <? 16))%bool.
  - eapply fwd_ok; [exact Hm|exact H|]. intros _ _.
    rewrite Z2Nat.id by lia.
    assert (8 * ((len + 7) / 8) <= len + 7) by (Z.div_mod_to_equations; lia). lia.
  - eapply chunks_ok; [exact Hm|exact H|].
    destruct (Z.leb_spec len 16).
    + simpl. lia.
    + assert (32 * ((len - 16 + 31) / 32) <= len - 16 + 31) by (Z.div_mod_to_equations; lia).
      assert (0 <= (len - 16 + 31) / 32) by (apply Z.div_pos; lia).
      rewrite Z2Nat.id by lia. lia.
Qed.

Lemma ov8_ok : forall m op ip off m' op' ip', dok m -> xm_ov8 src m op ip off = Some (m', op', ip') ->
  op + 8 <= L -> dok m' /\ op' = op + 8.
Proof.
  intros m op ip off m' op' ip' Hm H Hb. unfold xm_ov8 in H.
  destruct (off <? 8).
  - destruct (xm_fwd src 4 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    destruct (xm_fwd src 4 m1 R_dst (op + 4) R_dst (ip + xdec32 off)) as [m2|] eqn:E2; [|discriminate].
    inversion H; subst. split; [|reflexivity].
    eapply fwd_ok; [eapply fwd_ok; [exact Hm|exact E1|]|exact E2|]; intros; simpl; lia.
  - destruct (xm_fwd src 8 m R_dst op R_dst ip) as [m1|] eqn:E1; [|discriminate].
    inversion H; subst. split; [|reflexivity]. eapply fwd_ok; [exact Hm|exact E1|]; intros; simpl; lia.
Qed.

(* ZSTD_safecopy writes [op, op + len) and, through its wild part, at most up to oend_w + 31 *)
Lemma safecopy_ok : forall m op oend_w rs ip len srcb4 m', dok m ->
  xm_safecopy src m op oend_w rs ip len srcb4 = Some m' -> 0 <= len -> op + len <= L -> oend_w + 32 <= L ->
  dok m'.
Proof.
  intros m op oend_w rs ip len srcb4 m' Hm H Hl Hb Hw. unfold xm_safecopy in H.
  destruct (Z.ltb_spec len 8).
  - eapply fwd_ok'; [exact Hm|exact H|]. intros; lia.
  - destruct (if srcb4 then xm_ov8 src m op ip (op - ip) else Some (m, op, ip)) as [[[m1 op1] ip1]|] eqn:E1;
      [|discriminate].
    assert (Hm1: dok m1 /\ op1 = (if srcb4 then op + 8 else op)).
    { destruct srcb4.
      - apply ov8_ok in E1; auto. lia.
      - inversion E1; subst. auto. }
    destruct Hm1 as [Hm1 Ho1].
    set (len1 := if srcb4 then len - 8 else len) in H.
    assert (Hs: op1 + len1 = op + len /\ op1 + 16 <= op + len + 16 /\ 0 <= len1)
      by (unfold len1; destruct srcb4; cbv iota in Ho1; lia).
    clearbody len1.
    destruct (Z.geb_spec (oend_w - (op + len)) 0).
    + eapply wild_ok; [exact Hm1|exact H|]. lia.
    + destruct (Z.geb_spec (oend_w - op1) 0).
      * destruct (xm_wild src m1 op1 rs ip1 (oend_w - op1) srcb4) as [m2|] eqn:E2; [|discriminate].
        eapply fwd_ok'; [eapply wild_ok; [exact Hm1|exact E2|lia]|exact H|]. intros; lia.
      * eapply fwd_ok'; [exact Hm1|exact H|]. intros; lia.
Qed.

(* ZSTD_safecopyDstBeforeSrc writes [op, op + len) *)
Lemma sdbs_ok : forall m op ip len m', dok m -> xm_sdbs src m op ip len = Some m' ->
  (0 < len -> op + len <= L) -> dok m'.
Proof.
  intros m op ip len m' Hm H Hb. unfold xm_sdbs in H.
  destruct ((len <? 8) || (op - ip >? -8))%bool eqn:Ec.
  - eapply fwd_ok'; [exact Hm|exact H|]. intros; auto.
  - apply Bool.orb_false_iff in Ec as [E1 _]. apply Z.ltb_ge in E1.
    destruct ((len >=? 32) && (op - ip <? -16))%bool eqn:Ec2; cbv beta iota in H.
    + apply andb_prop in Ec2 as [E2 _]. apply Z.geb_le in E2.
      destruct (xm_wild src m op R_dst ip (len - 32) false) as [m1|] eqn:Ew; [|discriminate].
      eapply fwd_ok'; [eapply wild_ok; [exact Hm|exact Ew|]|exact H|]; [|intros]; specialize (Hb ltac:(lia)); lia.
    + eapply fwd_ok'; [exact Hm|exact H|]. intros; specialize (Hb ltac:(lia)); lia.
Qed.

End Copies.

(* boolean comparisons of the hypotheses as propositions *)
Ltac zb := repeat match goal with
  | H: (_ >? _) = _ |- _ => rewrite Z.gtb_ltb in H
  | H: (_ >=? _) = _ |- _ => rewrite Z.geb_leb in H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H: (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H; destruct H
  | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H; destruct H
  | H: (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H: (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in H; destruct H as [H|H]
  end.

(* case on the first test or result H depends on *)
Ltac dh H := match type of H with
  | context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E; cbv beta iota in H; try discriminate H
  end.

Ltac lz := unfold XWILDCOPY, XLITEXTRA in *; lia.

(* ---------- the matches and the sequences ---------- *)

(* a match of ml bytes at op: the fast path (wo = None) may overshoot by 32 bytes, the slow path stays below
   op + ml and its wild part below oend_w + 32 *)
Definition wo_ok (op ml: Z) (wo: option Z) : Prop :=
  match wo with None => op + ml + 32 <= L | Some w => op + ml <= L /\ w + 32 <= L end.

Lemma prefix_ok : forall e m op mt ml off wo m', dok m -> xm_prefix e m op mt ml off wo = Some m' -> 0 <= ml ->
  wo_ok op ml wo -> dok m'.
Proof.
  intros e m op mt ml off wo m' Hm H Hl Hw. unfold xm_prefix in H. destruct wo as [w|]; cbn [wo_ok] in Hw.
  - eapply safecopy_ok; [exact Hm|exact H|lia|lia|lia].
  - dh H; zb.
    + eapply wild_ok; [exact Hm|exact H|lia].
    + destruct (xm_ov8 (xe_src e) m op mt off) as [[[m1 op1] mt1]|] eqn:E1; [|discriminate].
      apply ov8_ok in E1; [|exact Hm|lia]. destruct E1 as [Hm1 ->].
      dh H; zb.
      * eapply wild_ok; [exact Hm1|exact H|lia].
      * inversion H; subst; auto.
Qed.

Lemma match_ok : forall e m oLitEnd ml off wo m', dok m -> xm_match e m oLitEnd ml off wo = Some m' -> 0 <= ml ->
  wo_ok oLitEnd ml wo -> dok m'.
Proof.
  intros e m oLitEnd ml off wo m' Hm H Hl Hw.
  assert (Hb: oLitEnd + ml <= L) by (destruct wo; cbn [wo_ok] in Hw; lia).
  unfold xm_match in H. dh H; zb.
  - dh H; zb. cbv zeta in H. dh H; zb.
    + eapply move_ok; [exact Hm|exact H|]. intros; lia.
    + dh H. eapply prefix_ok; [eapply move_ok; [exact Hm|exact E2|]|exact H|lia|].
      * intros; lia.
      * destruct wo; cbn [wo_ok] in *; lia.
  - eapply prefix_ok; [exact Hm|exact H|lia|exact Hw].
Qed.

(* one sequence: every store below the output end oend *)
Lemma exec_ok : forall e m op lr li llim ll ml off m' op' li', dok m ->
  x_exec e m op lr li llim ll ml off = Some (m', op', li') -> 0 <= ll -> 0 <= ml -> xe_oend e <= L -> dok m'.
Proof.
  intros e m op lr li llim ll ml off m' op' li' Hm H Hll Hml Ho. unfold x_exec in H. cbv zeta in H.
  dh H; zb.
  1-2: dh H; zb; dh H; zb; dh H; dh H; inversion H; subst;
    eapply match_ok; [eapply safecopy_ok; [exact Hm|exact E2|lia|lia|lz]|exact E3|lia|cbn [wo_ok]; lz].
  dh H. dh H. dh H. inversion H; subst.
  eapply move_ok in E; [|exact Hm|intros; simpl; lz].
  assert (Hm2: dok x0).
  { revert E0. destruct (Z.gtb_spec ll 16); intros E0.
    - eapply wild_ok; [exact E|exact E0|lz].
    - inversion E0; subst; auto. }
  eapply match_ok; [exact Hm2|exact E1|lia|cbn [wo_ok]; lz].
Qed.

(* one sequence, literals in dst: every store below the literals' end in dst, llim *)
Lemma exec_split_ok : forall e m op li llim ll ml off m' op' li', dok m ->
  x_exec_split e m op li llim ll ml off = Some (m', op', li') -> 0 <= ll -> 0 <= ml -> xe_oend e <= L ->
  llim <= L -> dok m'.
Proof.
  intros e m op li llim ll ml off m' op' li' Hm H Hll Hml Ho Hlim. unfold x_exec_split in H. cbv zeta in H.
  dh H; zb.
  1-2: dh H; zb; dh H; zb; dh H; zb; dh H; dh H; inversion H; subst.
  1-4: eapply match_ok; [eapply sdbs_ok; [exact Hm|exact E3|intros; lia]|exact E4|lia|cbn [wo_ok]; lz].
  dh H. dh H. dh H. inversion H; subst.
  eapply move_ok in E; [|exact Hm|intros; simpl; lz].
  assert (Hm2: dok x0).
  { revert E0. destruct (Z.gtb_spec ll 16); intros E0.
    - eapply wild_ok; [exact E|exact E0|lz].
    - inversion E0; subst; auto. }
  eapply match_ok; [exact Hm2|exact E1|lia|cbn [wo_ok]; lz].
Qed.

(* an execution state whose memory is whole and, while the literals are split, whose dst literals end within it *)
Definition xok (s: xex) : Prop := dok (xmm s) /\ (xsp s = true -> xlim s <= L).

Lemma step_ok : forall e s ll ml off s', xok s -> x_step e s ll ml off = Some s' -> 0 <= ll -> 0 <= ml ->
  xe_oend e <= L -> xok s'.
Proof.
  intros e s ll ml off s' [Hm Hs] H Hll Hml Ho. unfold x_step in H. cbv zeta in H.
  destruct (xsp s); [specialize (Hs eq_refl)|].
  - dh H; zb.
    + destruct (if xlim s - xli s =? 0 then Some (xmm s, xop s) else _) as [[m1 op1]|] eqn:Emo; [|discriminate].
      assert (Hm1: dok m1).
      { dh Emo; zb.
        - inversion Emo; subst; auto.
        - dh Emo; zb. dh Emo. inversion Emo; subst. eapply sdbs_ok; [exact Hm|exact E2|intros; lia]. }
      destruct (x_exec _ _ _ _ _ _ _ _ _) as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
      inversion H; subst. split; [|cbn; discriminate]. eapply exec_ok; [exact Hm1|exact Ex|lia|lia|lia].
    + destruct (x_exec_split _ _ _ _ _ _ _ _) as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
      inversion H; subst. split; [|cbn; auto]. eapply exec_split_ok; [exact Hm|exact Ex|lia|lia|lia|lia].
  - destruct (x_exec _ _ _ _ _ _ _ _ _) as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
    inversion H; subst. split; [|cbn; discriminate]. eapply exec_ok; [exact Hm|exact Ex|lia|lia|lia].
Qed.


(* a read of nb >= 0 bits gives a nonnegative value *)
Lemma rd_nonneg : forall V pos nb v p, rd V pos nb = Some (v, p) -> 0 <= nb -> 0 <= v.
Proof.
  intros V pos nb v p H Hnb. unfold rd in H. destruct (pos - nb <? 0); [discriminate|].
  inversion H; subst; clear H. unfold bs_peek_s.
  destruct (Z.ltb_spec pos 0); [lia|]. destruct (pos - nb >=? 0).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg.
    + apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    + apply Z.pow_nonneg. lia.
Qed.

Lemma nth_nonneg : forall l n, Forall (fun x => 0 <= x) l -> 0 <= nth n l 0.
Proof.
  induction l as [|x l IH]; intros n H; [destruct n; simpl; lia|].
  inversion H; subst. destruct n; simpl; auto.
Qed.

Ltac tab_nonneg := apply nth_nonneg; repeat (constructor; [lia|]); constructor.

(* a sequence ZSTD_decodeSequence decodes has nonnegative literal and match lengths *)
Lemma dseq_nonneg : forall tLL tOF tML V last sLL sOF sML pos sq st pos',
  dseq_one tLL tOF tML V last sLL sOF sML pos = Some (sq, st, pos') -> 0 <= sq_ll sq /\ 0 <= sq_ml sq.
Proof.
  intros tLL tOF tML V last sLL sOF sML pos sq st pos' H. unfold dseq_one in H.
  destruct (rd V pos _) as [[eOF p1]|] eqn:R1; [|discriminate].
  destruct (rd V p1 _) as [[eML p2]|] eqn:R2; [|discriminate].
  destruct (rd V p2 _) as [[eLL p3]|] eqn:R3; [|discriminate].
  apply rd_nonneg in R2; [|unfold ML_bits_tab; tab_nonneg].
  apply rd_nonneg in R3; [|unfold LL_bits_tab; tab_nonneg].
  assert (0 <= nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_base_tab 0) by (unfold LL_base_tab; tab_nonneg).
  assert (0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0) by (unfold ML_base_tab; tab_nonneg).
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

Lemma loop_ok : forall e tLL tOF tML V k st pos rep s s' pos' rep', xok s -> xe_oend e <= L ->
  x_seq_loop dseq_one c_offset e tLL tOF tML V k st pos rep s = Some (s', pos', rep') -> xok s'.
Proof.
  intros e tLL tOF tML V k. induction k as [|k IH]; intros st pos rep s s' pos' rep' Hs Ho H;
    destruct st as [[sLL sOF] sML]; simpl in H.
  - inversion H; subst. exact Hs.
  - destruct (dseq_one tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos) as [[[sq st1] pos1]|] eqn:E1; [|discriminate].
    destruct (c_offset rep (sq_ll sq) (sq_ov sq)) as [off rep1].
    destruct (x_step e s (sq_ll sq) (sq_ml sq) off) as [s1|] eqn:Es; [|discriminate].
    apply dseq_nonneg in E1. destruct E1.
    eapply IH; [eapply step_ok; [exact Hs|exact Es|lia|lia|exact Ho]|exact Ho|exact H].
Qed.

(* the last literals: checked against oend *)
Lemma last_ok : forall e s m op', xok s -> xe_oend e <= L -> x_last e s = Some (m, op') -> dok m.
Proof.
  intros e s m op' [Hm Hs] Ho H. unfold x_last in H. cbv zeta in H.
  destruct (xsp s); [specialize (Hs eq_refl)|].
  - destruct (Z.gtb_spec (xlim s - xli s) (xe_oend e - xop s)); [discriminate|].
    destruct (xm_move (xe_src e) (Z.to_nat (xlim s - xli s)) (xmm s) R_dst (xop s) R_dst (xli s)) as [m1|] eqn:E1;
      [|discriminate].
    cbv beta iota zeta in H. dh H; zb. dh H. inversion H; subst.
    eapply fwd_ok'; [eapply move_ok; [exact Hm|exact E1|]|exact E0|].
    + intros; lia.
    + intros; lz.
  - cbv beta iota zeta in H. dh H; zb. dh H. inversion H; subst. eapply fwd_ok'; [exact Hm|exact E0|]. intros; lia.
Qed.

Lemma seqs_ok : forall e tabs rep bits nbSeq s0 m op' rep', xok s0 -> xe_oend e <= L ->
  x_seqs dseq_one c_offset e tabs rep bits nbSeq s0 = Some (m, op', rep') -> dok m.
Proof.
  intros e tabs rep bits nbSeq s0 m op' rep' Hs Ho H. destruct tabs as [[tLL tOF] tML]. unfold x_seqs in H.
  destruct (negb (bs_okb bits)); [discriminate|].
  destruct (rd bits (bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[s1 pos] r]|] eqn:El; [|discriminate].
  destruct (negb (pos =? 0)); [discriminate|].
  destruct (x_last e s1) as [[m1 o1]|] eqn:Ex; [|discriminate].
  inversion H; subst.
  eapply last_ok; [eapply loop_ok; [exact Hs|exact Ho|exact El]|exact Ho|exact Ex].
Qed.


(* ---------- the literals' stores ---------- *)

(* (no simpl here: the copies of XLITEXTRA bytes would be unfolded) *)
Ltac ls_side := intros; try discriminate; unfold x_split_L0 in *; rewrite ?repeat_length;
  rewrite ?Zlength_correct in *; unfold XLITEXTRA, XWILDCOPY in *; lia.

(* the memory after each store run of x_lits_store *)
Ltac mok := repeat match goal with
  | Hm: dok ?m, E: xm_fwd ?sr ?k ?m ?rd ?d ?rs ?s = Some ?m1 |- _ =>
      apply (fwd_ok sr k m rd d rs s m1 Hm) in E; [|ls_side]
  | Hm: dok ?m, E: xm_wrn ?vs ?m ?rd ?d = Some ?m1 |- _ =>
      apply (wrn_ok vs m rd d m1 Hm) in E; [|ls_side]
  | Hm: dok ?m, E: xm_move ?sr ?k ?m ?rd ?d ?rs ?s = Some ?m1 |- _ =>
      apply (move_ok sr k m rd d rs s m1 Hm) in E; [|ls_side]
  end.

Lemma ls_extra_ok : forall body lits lused m op0 ews bsm cap m' lr li lim sp, dok m ->
  x_alloc_loc cap (Zlength lits) bsm true = XL_extra ->
  x_lits_store body lits lused m op0 ews bsm cap true = Some (m', lr, li, lim, sp) ->
  dok m' /\ (sp = true -> lim <= L).
Proof.
  intros body lits lused m op0 ews bsm cap m' lr li lim sp Hm Eloc H.
  unfold x_lits_store in H. rewrite Eloc in H. cbv beta iota zeta delta [xl_is_split] in H.
  repeat (dh H; zb); mok; inversion H; subst; split; auto; discriminate.
Qed.
Lemma ls_src_ok : forall body lits lused m op0 ews bsm cap m' lr li lim sp, dok m ->
  x_alloc_loc cap (Zlength lits) bsm true = XL_src ->
  x_lits_store body lits lused m op0 ews bsm cap true = Some (m', lr, li, lim, sp) ->
  dok m' /\ (sp = true -> lim <= L).
Proof.
  intros body lits lused m op0 ews bsm cap m' lr li lim sp Hm Eloc H.
  unfold x_lits_store in H. rewrite Eloc in H. cbv beta iota zeta delta [xl_is_split] in H.
  repeat (dh H; zb); mok; inversion H; subst; split; auto; discriminate.
Qed.

(* one store run (or one condition) of x_lits_store, on the goal *)
Ltac ls_step :=
  match goal with
  | Hm: dok ?mm |- context [match xm_wrn ?vs ?mm ?r ?d with _ => _ end] =>
      let E := fresh "W" in destruct (xm_wrn vs mm r d) as [?|] eqn:E;
      [apply (wrn_ok vs mm r d _ Hm) in E; [|ls_side] | discriminate]
  | Hm: dok ?mm |- context [match xm_fwd ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end] =>
      let E := fresh "W" in destruct (xm_fwd sr k mm rd d rs s) as [?|] eqn:E;
      [apply (fwd_ok sr k mm rd d rs s _ Hm) in E; [|ls_side] | discriminate]
  | Hm: dok ?mm |- context [match xm_move ?sr ?k ?mm ?rd ?d ?rs ?s with _ => _ end] =>
      let E := fresh "W" in destruct (xm_move sr k mm rd d rs s) as [?|] eqn:E;
      [apply (move_ok sr k mm rd d rs s _ Hm) in E; [|ls_side] | discriminate]
  | |- context [if ?c then _ else _] => let C := fresh "C" in destruct c eqn:C
  end.

Lemma ls_split_ok : forall body lits lused m op0 ews bsm cap m' lr li lim sp, dok m -> op0 + ews <= L ->
  x_alloc_loc cap (Zlength lits) bsm true = XL_split ->
  x_lits_store body lits lused m op0 ews bsm cap true = Some (m', lr, li, lim, sp) ->
  dok m' /\ (sp = true -> lim <= L).
Proof.
  intros body lits lused m op0 ews bsm cap m' lr li lim sp Hm Hb Eloc H.
  assert (Hs: XLITEXTRA < Zlength lits).
  { unfold x_alloc_loc in Eloc. cbn [negb andb] in Eloc. destruct (Z.leb_spec (Zlength lits) XLITEXTRA);
      [discriminate|lia]. }
  (* a type of at most 1 is 0 or 1 *)
  assert (0 <= Z.land (byte_at body 0) 3) by (apply Z.land_nonneg; right; lia).
  unfold x_lits_store in H. revert H. rewrite Eloc. cbv beta iota zeta delta [xl_is_split].
  repeat (ls_step; cbv beta iota).
  all: intros Hx; injection Hx; intros; subst; split; auto; try ls_side.
  all: zb; lia.
Qed.


(* In streaming mode the literals go to litExtraBuffer, stay in the block, or are split with their dst part in
   [op0, op0 + ews): every store below op0 + ews, and the dst part's end (the limit) too. *)
Lemma lits_store_ok : forall body lits lused m op0 ews bsm cap m' lr li lim sp, dok m -> op0 + ews <= L ->
  x_lits_store body lits lused m op0 ews bsm cap true = Some (m', lr, li, lim, sp) ->
  dok m' /\ (sp = true -> lim <= L).
Proof.
  intros body lits lused m op0 ews bsm cap m' lr li lim sp Hm Hb H.
  destruct (x_alloc_loc cap (Zlength lits) bsm true) eqn:Eloc.
  - unfold x_alloc_loc in Eloc. cbn [negb andb] in Eloc. destruct (_ <=? _); discriminate.
  - eapply ls_extra_ok; eauto.
  - eapply ls_split_ok; eauto.
  - eapply ls_src_ok; eauto.
Qed.



End Len.


(* ---------- the block ---------- *)

(* streaming never places the literals in dst after the block's room *)
Lemma litloc_stream : forall b lused litSize bsm cap, x_litloc b lused litSize bsm cap true <> XL_in_dst.
Proof.
  intros b lused litSize bsm cap. unfold x_litloc, x_alloc_loc. cbn [negb andb].
  destruct (_ && _)%bool; [discriminate|]. destruct (_ <=? _); discriminate.
Qed.

(* a region whose cells are all written gives all of them *)
Lemma written_all : forall d, Forall (fun c => c <> None) d -> Zlength (x_written d) = Zlength d.
Proof.
  induction d as [|c d IH]; intros H; [reflexivity|].
  inversion H; subst. destruct c as [v|]; [|congruence].
  simpl. rewrite !Zlength_cons. rewrite IH by auto. reflexivity.
Qed.

Lemma dok_init : forall mem lxb, dok (Zlength mem) {| xm_dst := map Some mem; xm_lxb := lxb |}.
Proof.
  intros mem lxb. split; cbn [xm_dst].
  - rewrite !Zlength_correct, map_length. reflexivity.
  - apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (v & <- & _). discriminate.
Qed.

Lemma xblock_len (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap n: Z) :
  0 <= op -> 0 <= cap -> op + cap <= Zlength mem ->
  xblock st mem ps op ds de body bsm cap true = Some (st', m', n) -> Zlength m' = Zlength mem.
Proof.
  intros Hop Hcap Hlen H. unfold xblock, x_block in H. cbv zeta in H.
  destruct (Z.gtb_spec (Zlength body) bsm) as [Hb|Hb]; [discriminate|]. revert H.
  match goal with |- context [match x_lits ?a ?b ?c ?d ?e ?f ?g with _ => _ end] =>
    destruct (x_lits a b c d e f g) as [[[lits lused] huf]|] eqn:El; [|discriminate] end.
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|];
    [|discriminate].
  destruct ((nbSeq >? 0) && (cap =? 0))%bool; [discriminate|].
  destruct (x_lits_store body lits lused {| xm_dst := map Some mem; xm_lxb := x_lxb xhuf st |} op
              (Z.min bsm cap) bsm cap true) as [[[[[m lr] li] lim] sp]|] eqn:Es; [|discriminate].
  apply (lits_store_ok (Zlength mem)) in Es; [|apply dok_init|lia].
  destruct Es as [Hm Hsp].
  assert (Hoe: match x_litloc body lused (Zlength lits) bsm cap true with
               | XL_in_dst => op + bsm + XWILDCOPY | _ => op + cap end <= Zlength mem).
  { pose proof (litloc_stream body lused (Zlength lits) bsm cap).
    destruct (x_litloc body lused (Zlength lits) bsm cap true); [congruence|lia|lia|lia]. }
  destruct (nbSeq =? 0).
  - match goal with |- context [match x_last ?e ?s with _ => _ end] =>
      destruct (x_last e s) as [[m1 op1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply (last_ok (Zlength mem)) in Ex; [|split; cbn [xmm xsp xlim]; auto|exact Hoe].
    destruct Ex as [Hl Hf]. rewrite written_all by exact Hf. exact Hl.
  - destruct tabs as [t|]; [|discriminate].
    match goal with |- context [match x_seqs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 with _ => _ end] =>
      destruct (x_seqs a1 a2 a3 a4 a5 a6 a7 a8) as [[[m1 op1] rep1]|] eqn:Ex; [|discriminate] end.
    intros Hx; injection Hx; intros; subst.
    apply (seqs_ok (Zlength mem)) in Ex; [|split; cbn [xmm xsp xlim]; auto|exact Hoe].
    destruct Ex as [Hl Hf]. rewrite written_all by exact Hf. exact Hl.
Qed.
