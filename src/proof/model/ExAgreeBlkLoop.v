(* The sequence loop of the exact model (ExBlock.x_seq_loop: decode one sequence with the C-exact
   ZSTD_decodeSequence, resolve its offset on size_t repeat offsets, execute it) against the format model's
   decode-then-execute (Block.decode_seqs, Block.exec_seqs).  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.BitsFast Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Huffman Zstd.proof.model.Block.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkDefs.
Require Import Zstd.proof.model.ExAgreeBlkExec.
Local Open Scope Z_scope.

(* ---------- the values of one decoded sequence ---------- *)

(* a read of nb >= 0 bits gives a value of nb bits *)
Lemma loop_rd_bounds : forall V pos nb v pos',
  0 <= nb -> rd V pos nb = Some (v, pos') -> 0 <= v < 2 ^ nb /\ pos' = pos - nb.
Proof.
  intros V pos nb v pos' Hn H. unfold rd in H.
  destruct (pos - nb <? 0) eqn:E; [discriminate|]. inversion H; subst; clear H.
  apply Z.ltb_ge in E. unfold bs_peek_s.
  assert (0 < 2 ^ nb) by (apply Z.pow_pos_nonneg; lia).
  destruct (pos <? 0) eqn:E1; [lia|].
  destruct (pos - nb >=? 0) eqn:E2; [|rewrite Z.geb_leb in E2; apply Z.leb_gt in E2; lia].
  pose proof (Z.mod_pos_bound (le_value (slice V ((pos - nb) / 8) 5) / 2 ^ ((pos - nb) mod 8)) (2 ^ nb) H).
  lia.
Qed.

(* the base tables of the literal and match lengths are nonnegative *)
Lemma loop_nth_nonneg : forall (l: list Z) n, Forall (fun x => 0 <= x) l -> 0 <= nth n l 0.
Proof.
  intros l n H. destruct (Nat.lt_ge_cases n (length l)) as [Hn|Hn].
  - rewrite Forall_forall in H. apply H. apply nth_In; exact Hn.
  - rewrite nth_overflow by exact Hn. lia.
Qed.

Lemma loop_LL_base_nonneg : forall n, 0 <= nth n LL_base_tab 0.
Proof.
  intro n. apply loop_nth_nonneg. unfold LL_base_tab. repeat (constructor; [lia|]). constructor.
Qed.

Lemma loop_ML_base_nonneg : forall n, 0 <= nth n ML_base_tab 0.
Proof.
  intro n. apply loop_nth_nonneg. unfold ML_base_tab. repeat (constructor; [lia|]). constructor.
Qed.

(* a symbol of a table whose cells are bounded by B is bounded by B (the default cell has symbol 0) *)
Lemma loop_fse_sym_bound : forall t st B,
  Forall (fun e => 0 <= fe_sym e <= B) (ft_cells t) -> 0 <= B -> 0 <= fe_sym (fse_cell t st) <= B.
Proof.
  intros t st B H HB. unfold fse_cell.
  destruct (Nat.lt_ge_cases (Z.to_nat st) (length (ft_cells t))) as [Hn|Hn].
  - rewrite Forall_forall in H. apply H. apply nth_In; exact Hn.
  - rewrite nth_overflow by exact Hn. simpl. lia.
Qed.

(* One sequence as ZSTD_decodeSequence decodes it: nonnegative literal and match lengths, and (the offset
   codes being at most MaxOff = 31) an offset value of at most 32 bits. *)
Lemma loop_dseq_bounds : forall tLL tOF tML V last sLL sOF sML pos sq st pos',
  Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells tOF) ->
  dseq_one tLL tOF tML V last sLL sOF sML pos = Some (sq, st, pos') ->
  0 <= sq_ll sq /\ 0 <= sq_ml sq /\ 0 <= sq_ov sq < 2 ^ 32.
Proof.
  intros tLL tOF tML V last sLL sOF sML pos sq st pos' HOF H. unfold dseq_one in H.
  destruct (rd V pos _) as [[eOF p1]|] eqn:R1; [|discriminate].
  destruct (rd V p1 _) as [[eML p2]|] eqn:R2; [|discriminate].
  destruct (rd V p2 _) as [[eLL p3]|] eqn:R3; [|discriminate].
  pose proof (loop_fse_sym_bound tOF sOF MaxOff HOF ltac:(unfold MaxOff; lia)) as HC.
  apply loop_rd_bounds in R1; [|lia].
  apply loop_rd_bounds in R2; [|apply loop_nth_nonneg; unfold ML_bits_tab; repeat (constructor; [lia|]); constructor].
  apply loop_rd_bounds in R3; [|apply loop_nth_nonneg; unfold LL_bits_tab; repeat (constructor; [lia|]); constructor].
  assert (Hsq: 0 <= nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_base_tab 0 + eLL /\
               0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0 + eML /\
               0 <= 2 ^ fe_sym (fse_cell tOF sOF) + eOF < 2 ^ 32).
  { pose proof (loop_LL_base_nonneg (Z.to_nat (fe_sym (fse_cell tLL sLL)))).
    pose proof (loop_ML_base_nonneg (Z.to_nat (fe_sym (fse_cell tML sML)))).
    unfold MaxOff in HC.
    assert (0 < 2 ^ fe_sym (fse_cell tOF sOF)) by (apply Z.pow_pos_nonneg; lia).
    assert (2 ^ (fe_sym (fse_cell tOF sOF) + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_add_r in H3 by lia.
    lia. }
  destruct last.
  - inversion H; subst; clear H. simpl. exact Hsq.
  - destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
    destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
    destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
    inversion H; subst; clear H. simpl. exact Hsq.
Qed.

(* Every sequence decode_seqs decodes has these bounds. *)
Lemma loop_seqs_bounds : forall tLL tOF tML V k sLL sOF sML pos l p,
  Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells tOF) ->
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  Forall (fun sq => 0 <= sq_ll sq /\ 0 <= sq_ml sq /\ 0 <= sq_ov sq < 2 ^ 32) l.
Proof.
  intros tLL tOF tML V k. induction k as [|k IH]; intros sLL sOF sML pos l p HOF H.
  - simpl in H. inversion H; subst. constructor.
  - apply decode_seqs_step in H. destruct H as (sq & nLL & nOF & nML & pos' & l' & H1 & -> & H2).
    constructor.
    + eapply loop_dseq_bounds; eassumption.
    + eapply IH; eassumption.
Qed.

Lemma loop_sum_ml_nonneg : forall l,
  Forall (fun sq => 0 <= sq_ll sq /\ 0 <= sq_ml sq /\ 0 <= sq_ov sq < 2 ^ 32) l -> 0 <= sum_ml l.
Proof.
  induction l as [|sq l IH]; intros H; simpl; [lia|]. inversion H; subst. specialize (IH H3). lia.
Qed.

(* ---------- the offsets ---------- *)

(* On repeat offsets in [1, 2^32) and an offset value of at most 32 bits, zstd's offset resolution on size_t
   values (`temp -= !temp`) is the format's whenever the format accepts the offset: the offset is at least 1
   and the new repeat offsets are again in [1, 2^32). *)
Lemma loop_c_offset_agree : forall rep ll ov o rep2,
  reps_ok rep -> 0 <= ov < 2 ^ 32 -> resolve_offset rep ll ov = Some (o, rep2) ->
  c_offset rep ll ov = (o, rep2) /\ 1 <= o /\ reps_ok rep2.
Proof.
  intros [[r1 r2] r3] ll ov o rep2 Hr Hov H. unfold reps_ok in Hr. unfold resolve_offset in H.
  unfold c_offset.
  destruct (ov >? 3) eqn:E0.
  { apply Z.gtb_lt in E0. inversion H; subst. split; [reflexivity|]. unfold reps_ok. lia. }
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1).
  { inversion H; subst. split; [reflexivity|]. unfold reps_ok. lia. }
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2).
  { inversion H; subst. split; [reflexivity|]. unfold reps_ok. lia. }
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3).
  { inversion H; subst. split; [reflexivity|]. unfold reps_ok. lia. }
  destruct (r1 - 1 <=? 0) eqn:E1; [discriminate|]. apply Z.leb_gt in E1.
  inversion H; subst; clear H.
  rewrite Z.mod_small by lia.
  destruct (r1 - 1 =? 0) eqn:E2; [apply Z.eqb_eq in E2; lia|].
  split; [reflexivity|]. unfold reps_ok. lia.
Qed.

Lemma x_seq_loop_agree : forall (e: xenv) (tLL tOF tML: fse_table) (V: list Z) (k: nat) (sLL sOF sML pos: Z)
    (l: list sequence) (p wsize: Z) (rep: Z * Z * Z) (outc lits: list Z) (s: xex)
    (out' lits': list Z) (rep': Z * Z * Z),
  of_ok (Some (tLL, tOF, tML)) -> reps_ok rep ->
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  exec_seqs wsize rep nil lits outc l = Some (out', lits', rep') ->
  ex_inv e s outc lits (sum_ml l) ->
  exists s', x_seq_loop dseq_one c_offset e tLL tOF tML V k (sLL, sOF, sML) pos rep s = Some (s', p, rep') /\
    ex_inv e s' out' lits' 0 /\ xm_lxb (xmm s') = xm_lxb (xmm s) /\ reps_ok rep'.
Proof.
  intros e tLL tOF tML V k. induction k as [|k IH];
    intros sLL sOF sML pos l p wsize rep outc lits s out' lits' rep' Hof Hrep Hdec Hexec Hinv.
  - simpl in Hdec. inversion Hdec; subst; clear Hdec. simpl in Hexec. inversion Hexec; subst; clear Hexec.
    exists s. split; [reflexivity|]. split; [exact Hinv|]. split; [reflexivity|exact Hrep].
  - pose proof Hof as (HLL & HOF & HML).
    pose proof (loop_seqs_bounds _ _ _ _ _ _ _ _ _ _ _ HOF Hdec) as Hb.
    apply decode_seqs_step in Hdec. destruct Hdec as (sq & nLL & nOF & nML & pos' & l' & H1 & -> & H2).
    inversion Hb as [|? ? Hsq Hb']; subst. destruct Hsq as (Hll & Hml & Hov).
    pose proof (loop_sum_ml_nonneg l' Hb') as Hsum.
    cbn [exec_seqs] in Hexec.
    destruct (sq_ll sq >? Zlength lits) eqn:E1; [discriminate|].
    rewrite Z.gtb_ltb in E1; apply Z.ltb_ge in E1.
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[o rep2]|] eqn:Eo; [|discriminate].
    destruct (o >? Zlength (@nil Z) + Zlength (outc ++ firstn (Z.to_nat (sq_ll sq)) lits)) eqn:E2;
      [discriminate|].
    rewrite Z.gtb_ltb in E2; apply Z.ltb_ge in E2.
    destruct (o >? wsize + Zlength (@nil Z)) eqn:E3; [discriminate|].
    destruct (loop_c_offset_agree _ _ _ _ _ Hrep Hov Eo) as (Hc & Ho & Hrep2).
    assert (Hfl: Zlength (outc ++ firstn (Z.to_nat (sq_ll sq)) lits) = Zlength outc + sq_ll sq).
    { rewrite !Zlength_correct in *. rewrite app_length, firstn_length. lia. }
    rewrite Hfl in E2. change (Zlength (@nil Z)) with 0 in E2.
    cbn [sum_ml fold_right] in Hinv. fold (sum_ml l') in Hinv.
    destruct (x_step_agree e s outc lits (sq_ml sq + sum_ml l') (sq_ll sq) (sq_ml sq) o Hinv
                ltac:(lia) ltac:(lia) ltac:(lia)) as (s1 & Hs1 & Hinv1 & Hlxb1).
    replace (sq_ml sq + sum_ml l' - sq_ml sq) with (sum_ml l') in Hinv1 by lia.
    destruct (IH nLL nOF nML pos' l' p wsize rep2 _ _ s1 out' lits' rep' Hof Hrep2 H2 Hexec Hinv1)
      as (s2 & Hl & Hinv2 & Hlxb2 & Hrep').
    exists s2. cbn [x_seq_loop]. rewrite H1, Hc, Hs1.
    split; [exact Hl|]. split; [exact Hinv2|]. split; [congruence|exact Hrep'].
Qed.
