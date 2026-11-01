(* The value-free side of the agreement of the exact block model with Block.decode_block: whatever the memory
   holds, a successful execution of the exact model advances op by ll + ml per sequence and then by the
   literals left, and ends at or before its output end; the format model's execution has the matching
   lengths.  So a block the exact model decodes has exactly the format model's content size, which therefore
   fits the capacity (ExAgreeBlock.v, the case where it does not).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.Block Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Local Open Scope Z_scope.

(* destruct every match of hypothesis H on a variable-free scrutinee, innermost first *)
Ltac dmatch H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] =>
      lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
      let E := fresh "E" in destruct x eqn:E
  end.

(* ---------- the exact model ---------- *)

Lemma x_exec_shape : forall e m op lr li llim ll ml off m' op' li',
  x_exec e m op lr li llim ll ml off = Some (m', op', li') -> op' = op + ll + ml /\ li' = li + ll.
Proof.
  intros. unfold x_exec in H. dmatch H; try discriminate; inversion H; subst; lia.
Qed.

Lemma x_exec_split_shape : forall e m op li llim ll ml off m' op' li',
  x_exec_split e m op li llim ll ml off = Some (m', op', li') -> op' = op + ll + ml /\ li' = li + ll.
Proof.
  intros. unfold x_exec_split in H. dmatch H; try discriminate; inversion H; subst; lia.
Qed.

Lemma gtb_le' : forall a b, (a >? b) = false -> a <= b.
Proof. intros a b H. rewrite Z.gtb_ltb in H. apply Z.ltb_ge in H. exact H. Qed.
Lemma gtb_lt' : forall a b, (a >? b) = true -> b < a.
Proof. intros a b H. rewrite Z.gtb_ltb in H. apply Z.ltb_lt in H. exact H. Qed.

(* the boolean comparisons of a hypothesis as propositions, for lia *)
Ltac bool2prop :=
  repeat match goal with
  | E: (_ =? _) = true |- _ => apply Z.eqb_eq in E
  | E: (_ =? _) = false |- _ => apply Z.eqb_neq in E
  | E: (_ <? _) = true |- _ => apply Z.ltb_lt in E
  | E: (_ <? _) = false |- _ => apply Z.ltb_ge in E
  | E: (_ >? _) = true |- _ => apply gtb_lt' in E
  | E: (_ >? _) = false |- _ => apply gtb_le' in E
  end.

Lemma x_step_shape : forall e s ll ml off s',
  x_step e s ll ml off = Some s' -> xop s' = xop s + ll + ml /\ xcnt s' = xcnt s - ll.
Proof.
  intros e s ll ml off s' H. unfold x_step in H. cbv zeta in H. unfold xcnt.
  destruct (xsp s) eqn:Esp.
  - destruct (xlim s - xli s <? ll) eqn:Elt.
    + destruct (xlim s - xli s =? 0) eqn:E0.
      * cbv iota beta in H.
        destruct (x_exec e (xmm s) (xop s) R_lxb 0 XLITEXTRA (ll - (xlim s - xli s)) ml off)
          as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
        apply x_exec_shape in Ex. injection H; intros; subst s'. cbn [xop xsp xli xlim].
        apply Z.eqb_eq in E0. unfold XLITEXTRA in *. lia.
      * destruct (xlim s - xli s >? xe_oend e - xop s); [discriminate|].
        destruct (xm_sdbs (xe_src e) (xmm s) (xop s) (xli s) (xlim s - xli s)) as [m1|]; [|discriminate].
        cbv iota beta in H.
        destruct (x_exec e m1 (xop s + (xlim s - xli s)) R_lxb 0 XLITEXTRA (ll - (xlim s - xli s)) ml off)
          as [[[m2 op2] li2]|] eqn:Ex; [|discriminate].
        apply x_exec_shape in Ex. injection H; intros; subst s'. cbn [xop xsp xli xlim].
        unfold XLITEXTRA in *. lia.
    + destruct (x_exec_split e (xmm s) (xop s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
        [|discriminate].
      apply x_exec_split_shape in Ex. injection H; intros; subst s'. cbn [xop xsp xli xlim]. lia.
  - destruct (x_exec e (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off) as [[[m2 op2] li2]|] eqn:Ex;
      [|discriminate].
    apply x_exec_shape in Ex. injection H; intros; subst s'. cbn [xop xsp xli xlim]. lia.
Qed.

Lemma x_last_shape : forall e s m op',
  x_last e s = Some (m, op') -> op' = xop s + xcnt s /\ op' <= xe_oend e.
Proof.
  intros e s m op' H. unfold x_last in H. cbv zeta in H. unfold xcnt.
  destruct (xsp s) eqn:Esp.
  - destruct (xlim s - xli s >? xe_oend e - xop s) eqn:E1; [discriminate|].
    destruct (xm_move (xe_src e) (Z.to_nat (xlim s - xli s)) (xmm s) R_dst (xop s) R_dst (xli s)) as [m1|];
      [|discriminate].
    cbv iota beta zeta in H.
    destruct (XLITEXTRA - 0 >? xe_oend e - (xop s + (xlim s - xli s))) eqn:E2; [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|]; [|discriminate].
    injection H; intros; subst. apply gtb_le' in E1. apply gtb_le' in E2. unfold XLITEXTRA in *. lia.
  - cbv iota beta zeta in H.
    destruct (xlim s - xli s >? xe_oend e - xop s) eqn:E2; [discriminate|].
    destruct (xm_fwd _ _ _ _ _ _ _) as [m2|]; [|discriminate].
    injection H; intros; subst. apply gtb_le' in E2. lia.
Qed.

Lemma x_seq_loop_shape : forall e tLL tOF tML V k sLL sOF sML pos l p rep s s' pos' rep',
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  x_seq_loop dseq_one c_offset e tLL tOF tML V k (sLL, sOF, sML) pos rep s = Some (s', pos', rep') ->
  xop s' = xop s + sum_ll l + sum_ml l /\ xcnt s' = xcnt s - sum_ll l.
Proof.
  intros e tLL tOF tML V k. induction k as [|k IH]; intros sLL sOF sML pos l p rep s s' pos' rep' Hd Hx.
  - simpl in Hd, Hx. inversion Hd; inversion Hx; subst. simpl. lia.
  - apply decode_seqs_step in Hd. destruct Hd as (sq & nLL & nOF & nML & pos1 & l' & E1 & -> & E2).
    simpl in Hx. rewrite E1 in Hx.
    destruct (c_offset rep (sq_ll sq) (sq_ov sq)) as [off rep1].
    destruct (x_step e s (sq_ll sq) (sq_ml sq) off) as [s1|] eqn:Es; [|discriminate].
    apply x_step_shape in Es. destruct (IH _ _ _ _ _ _ _ _ _ _ _ E2 Hx) as [H1 H2].
    simpl. lia.
Qed.

Lemma x_seqs_shape : forall e tLL tOF tML rep bits nbSeq s0 seqs m op' rep',
  decode_seq_stream tLL tOF tML bits nbSeq = Some seqs ->
  x_seqs dseq_one c_offset e (tLL, tOF, tML) rep bits nbSeq s0 = Some (m, op', rep') ->
  op' = xop s0 + xcnt s0 + sum_ml seqs /\ op' <= xe_oend e.
Proof.
  intros. unfold decode_seq_stream in H. unfold x_seqs in H0.
  destruct (negb (bs_okb bits)); [discriminate|].
  destruct (rd bits (bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l p]|] eqn:Ed; [|discriminate].
  destruct p; try discriminate. inversion H; subst.
  destruct (x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[s1 pos] r]|] eqn:El; [|discriminate].
  destruct (negb (pos =? 0)); [discriminate|].
  destruct (x_last e s1) as [[m1 o1]|] eqn:Ex; [|discriminate].
  inversion H0; subst.
  apply x_last_shape in Ex. destruct (x_seq_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ed El). lia.
Qed.

Lemma x_lits_store_shape : forall body lits lused m op0 ews bsm cap streaming m' lr li lim sp,
  x_lits_store body lits lused m op0 ews bsm cap streaming = Some (m', lr, li, lim, sp) ->
  xcnt {| xmm := m'; xop := op0; xlr := lr; xli := li; xlim := lim; xsp := sp |} = Zlength lits.
Proof.
  intros. assert (Hty: 0 <= Z.land (byte_at body 0) 3) by (apply Z.land_nonneg; right; lia).
  unfold x_lits_store in H. cbv zeta in H. unfold xcnt. cbn [xsp xli xlim].
  destruct (x_alloc_loc cap (Zlength lits) bsm streaming); cbv iota beta zeta in H;
    dmatch H; try discriminate; injection H; intros; subst; cbv iota beta;
    unfold x_split_L0, XLITEXTRA, XWILDCOPY; bool2prop; lia.
Qed.

(* ---------- the format model ---------- *)

Lemma Zlength_app' : forall (a b: list Z), Zlength (a ++ b) = Zlength a + Zlength b.
Proof. intros. rewrite !Zlength_correct, app_length. lia. Qed.

Lemma lz_copy_app : forall hist out offset n, exists t,
  lz_copy hist out offset n = out ++ t /\ Zlength t = Z.of_nat n.
Proof.
  intros hist out offset n. revert out. induction n as [|n IH]; intros out.
  - exists nil. simpl. rewrite app_nil_r. split; reflexivity.
  - simpl. destruct (IH (out ++ [byte_at (hist ++ out) (Zlength hist + Zlength out - offset)])) as [t [E L]].
    rewrite E. eexists. rewrite <- app_assoc. split; [reflexivity|].
    rewrite Zlength_app', L, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma exec_seqs_shape : forall wsize rep hist lits out seqs out' lits' rep',
  Forall (fun sq => 0 <= sq_ll sq /\ 0 <= sq_ml sq) seqs ->
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  (exists t, out' = out ++ t) /\
  Zlength out' = Zlength out + sum_ll seqs + sum_ml seqs /\ Zlength lits' = Zlength lits - sum_ll seqs.
Proof.
  intros wsize rep hist lits out seqs. revert rep lits out.
  induction seqs as [|sq seqs IH]; intros rep lits out out' lits' rep' Hf H.
  - simpl in H. inversion H; subst. simpl. split; [exists nil; rewrite app_nil_r; reflexivity|lia].
  - inversion Hf as [|? ? [Hll Hml] Hf']; subst. simpl in H.
    destruct (sq_ll sq >? Zlength lits) eqn:Eg; [discriminate|]. apply gtb_le' in Eg.
    destruct (resolve_offset _ _ _) as [[offset rep1]|]; [|discriminate].
    destruct (_ >? _); [discriminate|]. destruct (_ >? _); [discriminate|].
    destruct (lz_copy_app hist (out ++ firstn (Z.to_nat (sq_ll sq)) lits) offset (Z.to_nat (sq_ml sq)))
      as [t [Et Lt]].
    rewrite Et in H. destruct (IH _ _ _ _ _ _ Hf' H) as [[t2 E2] [L1 L2]].
    assert (Lf: Zlength (firstn (Z.to_nat (sq_ll sq)) lits) = sq_ll sq).
    { rewrite Zlength_correct, firstn_length. rewrite Zlength_correct in Eg. lia. }
    assert (Ls: Zlength (skipn (Z.to_nat (sq_ll sq)) lits) = Zlength lits - sq_ll sq).
    { rewrite !Zlength_correct, skipn_length. rewrite Zlength_correct in Eg. lia. }
    split.
    + exists (firstn (Z.to_nat (sq_ll sq)) lits ++ t ++ t2). rewrite E2. rewrite !app_assoc. reflexivity.
    + simpl. rewrite L1, L2, Ls, !Zlength_app', Lf, Lt. lia.
Qed.

Lemma nth_forall_def : forall {A} (P: A -> Prop) (l: list A) (d: A) (n: nat),
  Forall P l -> P d -> P (nth n l d).
Proof.
  intros A P l d n Hl Hd. destruct (Nat.lt_ge_cases n (length l)) as [Hlt|Hge].
  - rewrite Forall_forall in Hl. apply Hl. apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. exact Hd.
Qed.

Lemma rd_nonneg : forall V pos nb v pos', 0 <= nb -> rd V pos nb = Some (v, pos') -> 0 <= v.
Proof.
  intros V pos nb v pos' Hnb H. unfold rd in H. destruct (pos - nb <? 0); [discriminate|].
  inversion H; subst. unfold bs_peek_s. destruct (pos <? 0) eqn:Ep; [lia|].
  apply Z.ltb_ge in Ep. destruct (pos - nb >=? 0).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg.
    + apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    + destruct (Z.neg_nonneg_cases (- (pos - nb))); [rewrite Z.pow_neg_r by assumption; lia|].
      apply Z.pow_nonneg; lia.
Qed.

(* every sequence of a block has ll >= 0 and ml >= 3 (the ML codes are at most MaxML) *)
Lemma decode_seqs_bounds : forall tLL tOF tML V k sLL sOF sML pos l p,
  of_ok (Some (tLL, tOF, tML)) ->
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  Forall (fun sq => 0 <= sq_ll sq /\ 3 <= sq_ml sq) l.
Proof.
  intros tLL tOF tML V k. induction k as [|k IH]; intros sLL sOF sML pos l p Hok Hd.
  - simpl in Hd. inversion Hd; subst. constructor.
  - destruct Hok as [HLL [HOF HML]].
    pose proof Hd as Hd0. apply decode_seqs_step in Hd. destruct Hd as (sq & nLL & nOF & nML & pos1 & l' & E1 & -> & E2).
    constructor; [|eapply IH; [split; [exact HLL|split; [exact HOF|exact HML]]|exact E2]].
    unfold dseq_one in E1.
    destruct (rd V pos _) as [[eOF p1]|] eqn:R1; [|discriminate].
    destruct (rd V p1 _) as [[eML p2]|] eqn:R2; [|discriminate].
    destruct (rd V p2 _) as [[eLL p3]|] eqn:R3; [|discriminate].
    assert (Hsq: sq = {| sq_ll := nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_base_tab 0 + eLL;
                         sq_ml := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0 + eML;
                         sq_ov := 2 ^ fe_sym (fse_cell tOF sOF) + eOF |}).
    { destruct (Nat.eqb k 0); [inversion E1; reflexivity|].
      dmatch E1; try discriminate; inversion E1; reflexivity. }
    subst sq. cbn [sq_ll sq_ml].
    assert (HbM: 0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0).
    { apply (nth_forall_def (fun x => 0 <= x)); [repeat constructor; cbv; discriminate|lia]. }
    assert (HbL: 0 <= nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_bits_tab 0).
    { apply (nth_forall_def (fun x => 0 <= x)); [repeat constructor; cbv; discriminate|lia]. }
    apply rd_nonneg in R2; [|exact HbM]. apply rd_nonneg in R3; [|exact HbL].
    assert (HL: 0 <= nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_base_tab 0).
    { apply (nth_forall_def (fun x => 0 <= x)); [repeat constructor; cbv; discriminate|lia]. }
    assert (HM: 0 <= fe_sym (fse_cell tML sML) <= MaxML).
    { unfold fse_cell. apply (nth_forall_def (fun e => 0 <= fe_sym e <= MaxML)); [exact HML|simpl; unfold MaxML; lia]. }
    assert (HM3: 3 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0).
    { assert (Hn: (Z.to_nat (fe_sym (fse_cell tML sML)) < length ML_base_tab)%nat)
        by (simpl; unfold MaxML in HM; lia).
      assert (HF: Forall (fun x => 3 <= x) ML_base_tab) by (repeat constructor; cbv; discriminate).
      rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hn. }
    lia.
Qed.

(* the written cells of a destination whose first cells hold l start with l *)
Lemma x_written_prefix : forall (d: list (option Z)) (l: list Z),
  (forall k, (k < length l)%nat -> nth k d None = Some (nth k l 0)) -> firstn (length l) (x_written d) = l.
Proof.
  intros d l. revert d. induction l as [|a l IH]; intros d H; [reflexivity|].
  destruct d as [|x d]; [specialize (H O ltac:(simpl; lia)); discriminate|].
  pose proof (H O ltac:(simpl; lia)) as H0. simpl in H0. subst x. simpl. f_equal.
  apply IH. intros k Hk. apply (H (S k)). simpl. lia.
Qed.

Lemma x_written_has : forall (m: xmem) (l: list Z),
  dst_has m 0 l -> firstn (length l) (x_written (xm_dst m)) = l.
Proof.
  intros m l H. apply x_written_prefix. intros k Hk.
  assert (Hk': 0 <= Z.of_nat k < Zlength l) by (rewrite Zlength_correct; lia).
  specialize (H _ Hk'). unfold xm_rd in H. rewrite Z.add_0_l in H.
  destruct (Z.of_nat k <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite Nat2Z.id in H. rewrite H. unfold byte_at. rewrite Nat2Z.id. reflexivity.
Qed.
