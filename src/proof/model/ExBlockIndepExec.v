(* The execution of a block's sequences and last literals (ExBlock.x_exec, x_exec_split, x_step, x_seq_loop,
   x_last, x_seqs) on two related memories (ExBlockIndepMem.rel), one-shot without dictionary
   (prefixStart = virtualStart = 0), with repeat offsets >= 1: both runs fail, or both succeed at the same
   positions, and the output so far stays clean.

   The invariant (xinv) has two phases:
   - while the literals lie in the destination or the block's input, or are split with the cursor in their
     destination part, nothing reads litExtraBuffer's stale cells: the whole destination is clean (and, split,
     the part of the literals in litExtraBuffer, which the block wrote);
   - once the literals are read from litExtraBuffer (all of them, or past the split transition), the output so
     far [0, op) is clean and so are litExtraBuffer's cells below the literals' end, which the block wrote.
   Every offset is >= 1 (c_offset keeps the repeat offsets >= 1), so a match reads the clean output so far or
   cells it wrote itself.  Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Fse Zstd.proof.model.Block Zstd.proof.model.ExCSeq.
Require Import Zstd.proof.model.ExBlock.
Require Import Zstd.proof.model.ExAgreeBlkDefs Zstd.proof.model.ExBlockIndepMem Zstd.proof.model.ExBlockIndepCopy.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* two optional (memory, op, li) results: both fail, or the same op and li and memories related by R op *)
Definition orel3 (R: Z -> xmem -> xmem -> Prop) (o1 o2: option (xmem * Z * Z)) : Prop :=
  orel (fun a b => let '(m1, x1, y1) := a in let '(m2, x2, y2) := b in x1 = x2 /\ y1 = y2 /\ R x1 m1 m2) o1 o2.

(* litExtraBuffer keeps its clean cells and [0, P) is clean *)
Definition RB (c: creg) (P: Z) (m1 m2: xmem) : Prop :=
  exists c', rel c' m1 m2 /\ (forall x, c R_lxb x -> c' R_lxb x) /\ PC c' P.

Section Exec.
Variable e : xenv.
Hypothesis Hps : xe_ps e = 0.
Hypothesis Hvs : xe_vs e = 0.

(* ZSTD_execSequence with the literals in the destination or the input, the destination all clean *)
Lemma exec_A : forall c m1 m2 op lr li llim ll ml off, rel c m1 m2 -> Aall c -> lr <> R_lxb -> 1 <= off ->
  orel3 (fun _ => RC c) (x_exec e m1 op lr li llim ll ml off) (x_exec e m2 op lr li llim ll ml off).
Proof.
  intros c m1 m2 op lr li llim ll ml off HR HA Hlr Hoff.
  assert (Hrs: forall c', Aall c' -> lr = R_src \/ (lr = R_dst /\ Aall c')) by (destruct lr; auto; congruence).
  unfold x_exec. cbv beta zeta.
  destruct ((llim - li <? ll) || (xe_oend e - XWILDCOPY - op <? ll + ml)).
  - destruct (ll + ml >? xe_oend e - op); [exact I|].
    destruct (ll >? llim - li); [exact I|].
    pose proof (safecopy_A (xe_src e) c m1 m2 op (xe_oend e - XWILDCOPY) lr li ll HR HA Hlr) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hc1).
    pose proof (match_M e c1 ma mb (op + ll) ml off (Some (xe_oend e - XWILDCOPY)) Hps Hvs K1
                  (fun x _ => RC_A c c1 HA Hc1 x) Hoff) as K2.
    odest K2. destruct K2 as (c2 & K2 & Hc2 & _).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c2. split; auto. eapply cle_trans; eauto.
  - pose proof (move_A (xe_src e) 16 c m1 m2 op lr li HR (Hrs c HA)) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hc1).
    assert (Hw: orel (RC c) (if ll >? 16 then xm_wild (xe_src e) ma (op + 16) lr (li + 16) (ll - 16) false else Some ma)
                            (if ll >? 16 then xm_wild (xe_src e) mb (op + 16) lr (li + 16) (ll - 16) false else Some mb)).
    { destruct (ll >? 16).
      - eapply RC_cle; [exact Hc1|]. apply wild_A; auto. apply Hrs. eapply RC_A; eauto.
      - exists c1; auto. }
    odest Hw. destruct Hw as (c2 & K2 & Hc2).
    pose proof (match_M e c2 ma0 mb0 (op + ll) ml off None Hps Hvs K2
                  (fun x _ => RC_A c c2 HA Hc2 x) Hoff) as K3.
    odest K3. destruct K3 as (c3 & K3 & Hc3 & _).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c3. split; auto. eapply cle_trans; eauto.
Qed.

(* ZSTD_execSequence with the literals in litExtraBuffer, its cells [0, llim) clean, the output [0, op) clean *)
Lemma exec_B : forall c m1 m2 op li llim ll ml off, rel c m1 m2 -> PC c op ->
  (forall j, 0 <= j < llim -> c R_lxb j) -> 1 <= off ->
  orel3 (fun o => RB c o) (x_exec e m1 op R_lxb li llim ll ml off) (x_exec e m2 op R_lxb li llim ll ml off).
Proof.
  intros c m1 m2 op li llim ll ml off HR HP HL Hoff.
  assert (Hsrc: forall c' n, (forall x, c R_lxb x -> c' R_lxb x) -> li + n <= llim ->
            forall j, 0 <= j < n -> li + j < 0 \/ c' R_lxb (li + j)).
  { intros c' n Hc' Hn j Hj. destruct (Z.lt_ge_cases (li + j) 0); [left; auto|right; apply Hc', HL; lia]. }
  unfold x_exec. cbv beta zeta.
  destruct (Z.ltb_spec (llim - li) ll); [|destruct (Z.ltb_spec (xe_oend e - XWILDCOPY - op) (ll + ml))]; cbn [orb].
  - destruct (ll + ml >? xe_oend e - op); [exact I|].
    destruct (Z.gtb_spec ll (llim - li)); [exact I|lia].
  - destruct (ll + ml >? xe_oend e - op); [exact I|].
    destruct (Z.gtb_spec ll (llim - li)); [exact I|].
    pose proof (safecopy_L (xe_src e) c m1 m2 op (xe_oend e - XWILDCOPY) li ll HR) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hl1 & Hb1 & Hr1).
    assert (HP1: PC c1 (op + ll)).
    { intros x Hx. destruct (Z.lt_ge_cases x op); [apply Hb1; auto; apply HP; lia|].
      apply Hr1; [|lia]. apply Hsrc; auto. lia. }
    pose proof (match_M e c1 ma mb (op + ll) ml off (Some (xe_oend e - XWILDCOPY)) Hps Hvs K1 HP1 Hoff) as K2.
    odest K2. destruct K2 as (c2 & K2 & Hc2 & HP2).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c2. split; auto.
  - pose proof (move_L (xe_src e) 16 c m1 m2 op li (Z.min ll 16) HR ltac:(simpl; lia)) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hl1 & Hb1 & Hr1).
    specialize (Hr1 ltac:(apply Hsrc; auto; lia)).
    assert (Hw: orel (RB c (op + ll))
                  (if ll >? 16 then xm_wild (xe_src e) ma (op + 16) R_lxb (li + 16) (ll - 16) false else Some ma)
                  (if ll >? 16 then xm_wild (xe_src e) mb (op + 16) R_lxb (li + 16) (ll - 16) false else Some mb)).
    { destruct (Z.gtb_spec ll 16).
      - pose proof (wild_L (xe_src e) c1 ma mb (op + 16) (li + 16) (ll - 16) K1) as K2.
        eapply orel_mono; [|exact K2]. intros a b (c2 & K2' & Hl2 & Hb2 & Hr2).
        exists c2. split; auto. split; [auto|].
        intros x Hx. destruct (Z.lt_ge_cases x (op + 16)).
        + apply Hb2; auto. destruct (Z.lt_ge_cases x op); [apply Hb1; auto; apply HP; lia|apply Hr1; lia].
        + apply Hr2; [|lia]. intros j Hj.
          destruct (Hsrc c1 ll Hl1 ltac:(lia) (16 + j) ltac:(lia)) as [?|?]; [left; lia|right].
          replace (li + 16 + j) with (li + (16 + j)) by lia. auto.
      - exists c1. split; auto. split; auto.
        intros x Hx. destruct (Z.lt_ge_cases x op); [apply Hb1; auto; apply HP; lia|apply Hr1; lia]. }
    odest Hw. destruct Hw as (c2 & K2 & Hl2 & HP2).
    pose proof (match_M e c2 ma0 mb0 (op + ll) ml off None Hps Hvs K2 HP2 Hoff) as K3.
    odest K3. destruct K3 as (c3 & K3 & Hc3 & HP3).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c3. split; auto.
Qed.

(* ZSTD_execSequenceSplitLitBuffer, the destination all clean *)
Lemma exec_split_A : forall c m1 m2 op li llim ll ml off, rel c m1 m2 -> Aall c -> 1 <= off ->
  orel3 (fun _ => RC c) (x_exec_split e m1 op li llim ll ml off) (x_exec_split e m2 op li llim ll ml off).
Proof.
  intros c m1 m2 op li llim ll ml off HR HA Hoff.
  unfold x_exec_split. cbv beta zeta.
  destruct ((llim - li <? ll) || (li + ll - XWILDCOPY - op <? ll + ml)).
  - destruct (ll + ml >? xe_oend e - op); [exact I|].
    destruct (ll >? llim - li); [exact I|].
    destruct ((op >? li) && (op <? li + ll)); [exact I|].
    pose proof (sdbs_A (xe_src e) c m1 m2 op li ll HR HA) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hc1).
    pose proof (match_M e c1 ma mb (op + ll) ml off (Some (li + ll - XWILDCOPY)) Hps Hvs K1
                  (fun x _ => RC_A c c1 HA Hc1 x) Hoff) as K2.
    odest K2. destruct K2 as (c2 & K2 & Hc2 & _).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c2. split; auto. eapply cle_trans; eauto.
  - pose proof (move_A (xe_src e) 16 c m1 m2 op R_dst li HR (or_intror (conj eq_refl HA))) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hc1).
    assert (Hw: orel (RC c) (if ll >? 16 then xm_wild (xe_src e) ma (op + 16) R_dst (li + 16) (ll - 16) false else Some ma)
                            (if ll >? 16 then xm_wild (xe_src e) mb (op + 16) R_dst (li + 16) (ll - 16) false else Some mb)).
    { destruct (ll >? 16).
      - eapply RC_cle; [exact Hc1|]. apply wild_A; auto. right; split; auto. eapply RC_A; eauto.
      - exists c1; auto. }
    odest Hw. destruct Hw as (c2 & K2 & Hc2).
    pose proof (match_M e c2 ma0 mb0 (op + ll) ml off None Hps Hvs K2
                  (fun x _ => RC_A c c2 HA Hc2 x) Hoff) as K3.
    odest K3. destruct K3 as (c3 & K3 & Hc3 & _).
    cbn. split; [reflexivity|split; [reflexivity|]]. exists c3. split; auto. eapply cle_trans; eauto.
Qed.

(* the two-phase invariant of the execution states *)
Definition xinv (s1 s2: xex) : Prop :=
  xop s1 = xop s2 /\ xlr s1 = xlr s2 /\ xli s1 = xli s2 /\ xlim s1 = xlim s2 /\ xsp s1 = xsp s2 /\
  exists c, rel c (xmm s1) (xmm s2) /\
    (if xsp s1 then Aall c /\ (forall j, 0 <= j < XLITEXTRA -> c R_lxb j)
     else match xlr s1 with
          | R_lxb => PC c (xop s1) /\ (forall j, 0 <= j < xlim s1 -> c R_lxb j)
          | _ => Aall c
          end).

Lemma step_inv : forall s1 s2 ll ml off, xinv s1 s2 -> 1 <= off ->
  orel xinv (x_step e s1 ll ml off) (x_step e s2 ll ml off).
Proof.
  intros [m1 op lr li lim sp] [m2 op2 lr2 li2 lim2 sp2] ll ml off
    (Eop & Elr & Eli & Elim & Esp & c & HR & Hph) Hoff.
  simpl in Eop, Elr, Eli, Elim, Esp, HR, Hph. subst op2 lr2 li2 lim2 sp2.
  unfold x_step. cbn [xmm xop xlr xli xlim xsp]. cbv zeta.
  destruct sp.
  - destruct Hph as (HA & HL).
    destruct (Z.ltb_spec (lim - li) ll).
    + assert (Hmo: orel (fun a b => let '(m1', o1) := a in let '(m2', o2) := b in
                          o1 = o2 /\ exists c', rel c' m1' m2' /\ cle c c')
                  (if lim - li =? 0 then Some (m1, op) else
                   if lim - li >? xe_oend e - op then None else
                   match xm_sdbs (xe_src e) m1 op li (lim - li) with Some m => Some (m, op + (lim - li)) | None => None end)
                  (if lim - li =? 0 then Some (m2, op) else
                   if lim - li >? xe_oend e - op then None else
                   match xm_sdbs (xe_src e) m2 op li (lim - li) with Some m => Some (m, op + (lim - li)) | None => None end)).
      { destruct (lim - li =? 0); [cbn; split; [reflexivity|exists c; split; auto; apply cle_refl]|].
        destruct (lim - li >? xe_oend e - op); [exact I|].
        pose proof (sdbs_A (xe_src e) c m1 m2 op li (lim - li) HR HA) as K1.
        odest K1. destruct K1 as (c1 & K1 & Hc1). cbn. split; [reflexivity|exists c1; auto]. }
      destruct (if lim - li =? 0 then Some (m1, op) else _) as [[ma oa]|];
        destruct (if lim - li =? 0 then Some (m2, op) else _) as [[mb ob]|]; cbn [orel] in Hmo;
        try contradiction; [|exact I].
      destruct Hmo as (<- & c1 & K1 & Hc1).
      pose proof (exec_B c1 ma mb oa 0 XLITEXTRA (ll - (lim - li)) ml off K1
                    (fun x _ => RC_A c c1 HA Hc1 x) (fun j Hj => Hc1 _ _ (HL j Hj)) Hoff) as K2.
      unfold orel3 in K2.
      destruct (x_exec e ma oa R_lxb 0 XLITEXTRA (ll - (lim - li)) ml off) as [[[ma' o1] l1]|];
        destruct (x_exec e mb oa R_lxb 0 XLITEXTRA (ll - (lim - li)) ml off) as [[[mb' o2] l2]|];
        cbn [orel] in K2; try contradiction; [|exact I].
      destruct K2 as (<- & <- & c2 & K2 & Hl2 & HP2).
      cbn. repeat (split; [reflexivity|]). exists c2. split; auto. split; [auto|intros j Hj; apply Hl2, Hc1, HL; exact Hj].
    + pose proof (exec_split_A c m1 m2 op li lim ll ml off HR HA Hoff) as K2.
      unfold orel3 in K2.
      destruct (x_exec_split e m1 op li lim ll ml off) as [[[ma' o1] l1]|];
        destruct (x_exec_split e m2 op li lim ll ml off) as [[[mb' o2] l2]|];
        cbn [orel] in K2; try contradiction; [|exact I].
      destruct K2 as (<- & <- & c2 & K2 & Hc2).
      cbn. repeat (split; [reflexivity|]). exists c2. split; auto. split; [eapply RC_A; eauto|intros j Hj; apply Hc2, HL; exact Hj].
  - destruct lr.
    + pose proof (exec_A c m1 m2 op R_dst li lim ll ml off HR Hph ltac:(discriminate) Hoff) as K2.
      unfold orel3 in K2.
      destruct (x_exec e m1 op R_dst li lim ll ml off) as [[[ma' o1] l1]|];
        destruct (x_exec e m2 op R_dst li lim ll ml off) as [[[mb' o2] l2]|];
        cbn [orel] in K2; try contradiction; [|exact I].
      destruct K2 as (<- & <- & c2 & K2 & Hc2).
      cbn. repeat (split; [reflexivity|]). exists c2. split; auto. eapply RC_A; eauto.
    + destruct Hph as (HP & HL).
      pose proof (exec_B c m1 m2 op li lim ll ml off HR HP HL Hoff) as K2.
      unfold orel3 in K2.
      destruct (x_exec e m1 op R_lxb li lim ll ml off) as [[[ma' o1] l1]|];
        destruct (x_exec e m2 op R_lxb li lim ll ml off) as [[[mb' o2] l2]|];
        cbn [orel] in K2; try contradiction; [|exact I].
      destruct K2 as (<- & <- & c2 & K2 & Hl2 & HP2).
      cbn. repeat (split; [reflexivity|]). exists c2. split; auto. split; auto.
    + pose proof (exec_A c m1 m2 op R_src li lim ll ml off HR Hph ltac:(discriminate) Hoff) as K2.
      unfold orel3 in K2.
      destruct (x_exec e m1 op R_src li lim ll ml off) as [[[ma' o1] l1]|];
        destruct (x_exec e m2 op R_src li lim ll ml off) as [[[mb' o2] l2]|];
        cbn [orel] in K2; try contradiction; [|exact I].
      destruct K2 as (<- & <- & c2 & K2 & Hc2).
      cbn. repeat (split; [reflexivity|]). exists c2. split; auto. eapply RC_A; eauto.
Qed.

(* the last literals *)
Lemma last_inv : forall s1 s2, xinv s1 s2 ->
  orel (fun a b => let '(m1', o1) := a in let '(m2', o2) := b in o1 = o2 /\ exists c, rel c m1' m2' /\ PC c o1)
       (x_last e s1) (x_last e s2).
Proof.
  intros [m1 op lr li lim sp] [m2 op2 lr2 li2 lim2 sp2]
    (Eop & Elr & Eli & Elim & Esp & c & HR & Hph).
  simpl in Eop, Elr, Eli, Elim, Esp, HR, Hph. subst op2 lr2 li2 lim2 sp2.
  unfold x_last. cbn [xmm xop xlr xli xlim xsp]. cbv zeta.
  destruct sp.
  - destruct Hph as (HA & HL).
    destruct (lim - li >? xe_oend e - op); [exact I|].
    pose proof (move_A (xe_src e) (Z.to_nat (lim - li)) c m1 m2 op R_dst li HR (or_intror (conj eq_refl HA))) as K1.
    odest K1. destruct K1 as (c1 & K1 & Hc1).
    cbv beta iota.
    destruct (XLITEXTRA - 0 >? xe_oend e - (op + (lim - li))); [exact I|].
    pose proof (fwd_L (xe_src e) (Z.to_nat (XLITEXTRA - 0)) c1 ma mb (op + (lim - li)) 0 (XLITEXTRA - 0) K1
                  ltac:(unfold XLITEXTRA; lia)) as K2.
    odest K2. destruct K2 as (c2 & K2 & Hl2 & Hb2 & Hr2).
    cbn. split; [reflexivity|]. exists c2. split; auto.
    intros x Hx. destruct (Z.lt_ge_cases x (op + (lim - li))).
    + apply Hb2; [lia|apply Hc1, HA].
    + apply Hr2; [|lia]. intros j Hj. right. rewrite Z.add_0_l. apply Hc1, HL. unfold XLITEXTRA in *; lia.
  - destruct (lim - li >? xe_oend e - op); [exact I|].
    destruct lr.
    + pose proof (fwd_A (xe_src e) (Z.to_nat (lim - li)) c m1 m2 op R_dst li HR (or_intror (conj eq_refl Hph))) as K1.
      odest K1. destruct K1 as (c1 & K1 & Hc1).
      cbn. split; [reflexivity|]. exists c1. split; auto. intros x _. apply Hc1, Hph.
    + destruct Hph as (HP & HL).
      pose proof (fwd_L (xe_src e) (Z.to_nat (lim - li)) c m1 m2 op li (lim - li) HR ltac:(lia)) as K1.
      odest K1. destruct K1 as (c1 & K1 & Hl1 & Hb1 & Hr1).
      cbn. split; [reflexivity|]. exists c1. split; auto.
      intros x Hx. destruct (Z.lt_ge_cases x op).
      * apply Hb1; [lia|apply HP; lia].
      * apply Hr1; [|lia]. intros j Hj.
        destruct (Z.lt_ge_cases (li + j) 0); [left; auto|right; apply HL; lia].
    + pose proof (fwd_A (xe_src e) (Z.to_nat (lim - li)) c m1 m2 op R_src li HR (or_introl eq_refl)) as K1.
      odest K1. destruct K1 as (c1 & K1 & Hc1).
      cbn. split; [reflexivity|]. exists c1. split; auto. intros x _. apply Hc1, Hph.
Qed.

(* the repeat offsets stay >= 1, and so does every offset *)
Definition reps_pos (rep: Z * Z * Z) : Prop := let '(r1, r2, r3) := rep in 1 <= r1 /\ 1 <= r2 /\ 1 <= r3.

Lemma c_offset_pos : forall rep ll ov, reps_pos rep ->
  1 <= fst (c_offset rep ll ov) /\ reps_pos (snd (c_offset rep ll ov)).
Proof.
  intros [[r1 r2] r3] ll ov (H1 & H2 & H3). unfold c_offset.
  destruct (Z.gtb_spec ov 3); [simpl; lia|].
  destruct (_ =? 1); [simpl; lia|].
  destruct (_ =? 2); [simpl; lia|].
  destruct (_ =? 3); [simpl; lia|].
  pose proof (Z.mod_pos_bound (r1 - 1) (2 ^ 64) ltac:(lia)).
  destruct (Z.eqb_spec ((r1 - 1) mod 2 ^ 64) 0); simpl; unfold SIZE_MAX; lia.
Qed.

Lemma loop_inv : forall dseq tLL tOF tML V k st pos rep s1 s2, reps_pos rep -> xinv s1 s2 ->
  orel (fun a b => let '(s1', p1, r1) := a in let '(s2', p2, r2) := b in p1 = p2 /\ r1 = r2 /\ xinv s1' s2')
       (x_seq_loop dseq c_offset e tLL tOF tML V k st pos rep s1)
       (x_seq_loop dseq c_offset e tLL tOF tML V k st pos rep s2).
Proof.
  intros dseq tLL tOF tML V k. induction k as [|k IH]; intros [[sLL sOF] sML] pos rep s1 s2 Hrep Hinv;
    cbn [x_seq_loop].
  - cbn. auto.
  - destruct (dseq tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos) as [[[sq st'] pos']|]; [|exact I].
    pose proof (c_offset_pos rep (sq_ll sq) (sq_ov sq) Hrep) as (Hoff & Hrep').
    destruct (c_offset rep (sq_ll sq) (sq_ov sq)) as [off rep'].
    simpl in Hoff, Hrep'.
    pose proof (step_inv s1 s2 (sq_ll sq) (sq_ml sq) off Hinv Hoff) as K1.
    destruct (x_step e s1 (sq_ll sq) (sq_ml sq) off) as [t1|];
      destruct (x_step e s2 (sq_ll sq) (sq_ml sq) off) as [t2|]; cbn [orel] in K1; try contradiction; [|exact I].
    apply IH; auto.
Qed.

(* the sequences and the last literals of a block *)
Lemma seqs_inv : forall dseq tabs rep bits nbSeq s1 s2, reps_pos rep -> xinv s1 s2 ->
  orel (fun a b => let '(m1', o1, r1) := a in let '(m2', o2, r2) := b in
                   o1 = o2 /\ r1 = r2 /\ exists c, rel c m1' m2' /\ PC c o1)
       (x_seqs dseq c_offset e tabs rep bits nbSeq s1) (x_seqs dseq c_offset e tabs rep bits nbSeq s2).
Proof.
  intros dseq [[tLL tOF] tML] rep bits nbSeq s1 s2 Hrep Hinv. unfold x_seqs.
  destruct (negb (bs_okb bits)); [exact I|].
  destruct (rd bits (bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|exact I].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|exact I].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|exact I].
  pose proof (loop_inv dseq tLL tOF tML bits (Z.to_nat nbSeq) (sLL, sOF, sML) p3 rep s1 s2 Hrep Hinv) as K1.
  destruct (x_seq_loop dseq c_offset e tLL tOF tML bits (Z.to_nat nbSeq) (sLL, sOF, sML) p3 rep s1)
    as [[[t1 q1] r1]|];
  destruct (x_seq_loop dseq c_offset e tLL tOF tML bits (Z.to_nat nbSeq) (sLL, sOF, sML) p3 rep s2)
    as [[[t2 q2] r2]|]; cbn [orel] in K1; try contradiction; [|exact I].
  destruct K1 as (<- & <- & K1).
  destruct (negb (q1 =? 0)); [exact I|].
  pose proof (last_inv t1 t2 K1) as K2.
  destruct (x_last e t1) as [[ma oa]|]; destruct (x_last e t2) as [[mb ob]|]; cbn [orel] in K2;
    try contradiction; [|exact I].
  destruct K2 as (<- & K2). cbn. auto.
Qed.

End Exec.
