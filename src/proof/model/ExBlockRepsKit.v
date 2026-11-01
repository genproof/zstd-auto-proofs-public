(* The repeat offsets and the sequence tables a compressed block of the exact model (Exact.xblock) leaves, on a
   block of bytes: the repeat offsets stay in [1, 2^32) and the tables' codes within MaxLL, MaxOff, MaxML
   (ExAgreeDefs.reps_ok, of_ok).

   Within the sequence loop the repeat offsets are size_t values: a new offset is below 2^32 (its OF code is at
   most MaxOff), and the only other new value is r1 - 1 (`temp -= !temp`: 0 becomes (size_t)-1).  Starting
   from [1, 2^32), a repeat offset is thus either in [1, 2^32) or (size_t)-1 decremented fewer times than there
   were sequences; a block has fewer than 2^17 sequences, so its U32 truncation (x_rep32) is never 0.
   Plain Coq. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Import ListNotations.
Require Import Zstd.proof.model.Bytes Zstd.proof.model.Bitstream Zstd.proof.model.Fse.
Require Import Zstd.proof.model.NCount Zstd.proof.model.Block Zstd.proof.model.EntC.
Require Import Zstd.proof.model.ExHuf Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock Zstd.proof.model.Exact.
Require Import Zstd.proof.model.ExAgreeDefs Zstd.proof.model.ExAgreeBlkHdr Zstd.proof.model.ExAgreeBlkLoop.
Require Import Zstd.proof.model.Refuse.
Local Open Scope Z_scope.

(* ---------- the tables of a sequences header ---------- *)

(* FSE_readNCount (both windows) returns at most maxsv + 1 normalized counts *)
Lemma xr_ncount_len (s: list Z) (maxsv: Z) norm log size :
  x_ncount ncount_c s maxsv = Some (norm, log, size) -> Zlength norm <= maxsv + 1.
Proof.
  assert (Hc : forall s', ncount_c s' maxsv = Some (norm, log, size) -> Zlength norm <= maxsv + 1).
  { intros s' H. unfold ncount_c in H.
    destruct (_ >? FSE_TABLELOG_ABSOLUTE_MAX); [discriminate|].
    match type of H with context [match ?m with _ => _ end] => destruct m as [[[n r] p]|] end; [|discriminate].
    destruct (negb (r =? 1)); [discriminate|].
    destruct (Zlength n >? maxsv + 1) eqn:E; [discriminate|].
    destruct (_ >? Zlength s'); [discriminate|].
    inversion H; subst. lia. }
  unfold x_ncount. destruct (Zlength s <? 8).
  - destruct (ncount_c _ maxsv) as [[[n l] z]|] eqn:E; [|discriminate].
    destruct (z >? Zlength s); [discriminate|]. intros H; inversion H; subst. eapply Hc; exact E.
  - apply Hc.
Qed.

(* one table of ZSTD_buildSeqTable on bytes has its codes within max *)
Lemma xr_seq_table_syms (mode: Z) (predef: fse_table) (prev: option fse_table) (max maxLog: Z) (b: list Z) t k :
  0 <= max -> bytes_ok b ->
  Forall (fun e => 0 <= fe_sym e <= max) (ft_cells predef) ->
  (forall p, prev = Some p -> Forall (fun e => 0 <= fe_sym e <= max) (ft_cells p)) ->
  x_seq_table ncount_c mode predef prev max maxLog b = Some (t, k) ->
  Forall (fun e => 0 <= fe_sym e <= max) (ft_cells t).
Proof.
  intros Hmax Hb Hpre Hprev H. unfold x_seq_table in H.
  destruct (mode =? 0); [inversion H; subst; auto|].
  destruct (mode =? 1).
  { destruct (Zlength b <? 1); [discriminate|].
    destruct (byte_at b 0 >? max) eqn:E; [discriminate|].
    inversion H; subst. rewrite Z.gtb_ltb, Z.ltb_ge in E.
    unfold fse_rle; simpl. constructor; [simpl; pose proof (byte_at_nonneg b 0 Hb); lia | constructor]. }
  destruct (mode =? 3).
  { destruct prev as [p|]; [|discriminate]. inversion H; subst. auto. }
  destruct (x_ncount ncount_c b max) as [[[norm log] size]|] eqn:E; [|discriminate].
  destruct (log >? maxLog); [discriminate|]. inversion H; subst.
  apply fse_build_syms; [lia|]. eapply xr_ncount_len; exact E.
Qed.

(* ZSTD_decodeSeqHeaders on bytes: the tables have the format's codes, and there are fewer than 2^17
   sequences *)
Lemma xr_seq_header (prev: option seq_tabs) (b: list Z) (nbSeq: Z) (tabs: option seq_tabs) (hused: Z) :
  bytes_ok b -> of_ok prev -> x_seq_header ncount_c prev b = Some (nbSeq, tabs, hused) ->
  of_ok tabs /\ 0 <= nbSeq < 2 ^ 17.
Proof.
  intros Hb Hprev H. unfold x_seq_header in H.
  destruct (Zlength b <? 1); [discriminate|].
  assert (Hnb : forall nb pos ok,
    (if byte_at b 0 <=? 127 then (byte_at b 0, 1, true)
     else if byte_at b 0 =? 255 then (le_field b 1 2 + LONGNBSEQ, 3, 3 <=? Zlength b)
     else ((byte_at b 0 - 128) * 256 + byte_at b 1, 2, 2 <=? Zlength b)) = (nb, pos, ok) ->
    0 <= nb < 2 ^ 17).
  { intros nb pos ok E.
    pose proof (byte_at_nonneg b 0 Hb) as H0. pose proof (byte_at_nonneg b 1 Hb) as H1.
    assert (H0' : byte_at b 0 < 256).
    { unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat 0) (length b)) as [Hl|Hl].
      - assert (Hin := nth_In b 0 Hl). unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
        apply Hb in Hin. unfold is_byte in Hin. lia.
      - rewrite nth_overflow by exact Hl. lia. }
    assert (H1' : byte_at b 1 < 256).
    { unfold byte_at. destruct (Nat.lt_ge_cases (Z.to_nat 1) (length b)) as [Hl|Hl].
      - assert (Hin := nth_In b 0 Hl). unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
        apply Hb in Hin. unfold is_byte in Hin. lia.
      - rewrite nth_overflow by exact Hl. lia. }
    pose proof (rf_le_field_range b 1 2 Hb ltac:(lia)) as HF. unfold LONGNBSEQ in E.
    destruct (byte_at b 0 <=? 127) eqn:E1; [inversion E; subst; lia|].
    destruct (byte_at b 0 =? 255) eqn:E2; inversion E; subst.
    - change (2 ^ (8 * 2)) with 65536 in HF. lia.
    - apply Z.leb_gt in E1. lia. }
  match type of H with context [match ?e with pair _ _ => _ end] => destruct e as [[nb pos] ok] eqn:Enb end.
  specialize (Hnb _ _ _ eq_refl).
  destruct (negb ok); [discriminate|].
  destruct (nb =? 0).
  { destruct (pos =? Zlength b); [|discriminate]. inversion H; subst. split; [exact Hprev|lia]. }
  destruct (pos + 1 >? Zlength b); [discriminate|].
  destruct (negb (Z.land (byte_at b pos) 3 =? 0)); [discriminate|].
  assert (HpLL : forall p, option_map (fun '(l, _, _) => l) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxLL) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  assert (HpOF : forall p, option_map (fun '(_, o, _) => o) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  assert (HpML : forall p, option_map (fun '(_, _, m) => m) prev = Some p ->
            Forall (fun e => 0 <= fe_sym e <= MaxML) (ft_cells p)).
  { intros p Hp. destruct prev as [[[l o] m]|]; inversion Hp; subst. apply Hprev. }
  destruct (x_seq_table ncount_c (Z.shiftr (byte_at b pos) 6) LL_predef _ MaxLL LLFSELog _) as [[tLL k1]|] eqn:E1;
    [|discriminate].
  apply xr_seq_table_syms in E1; auto;
    [|unfold MaxLL; lia | apply Forall_skipn'; exact Hb | exact LL_predef_syms].
  destruct (x_seq_table ncount_c (Z.land (Z.shiftr (byte_at b pos) 4) 3) OF_predef _ MaxOff OffFSELog _)
    as [[tOF k2]|] eqn:E2; [|discriminate].
  apply xr_seq_table_syms in E2; auto;
    [|unfold MaxOff; lia | apply Forall_skipn'; exact Hb | exact OF_predef_syms].
  destruct (x_seq_table ncount_c (Z.land (Z.shiftr (byte_at b pos) 2) 3) ML_predef _ MaxML MLFSELog _)
    as [[tML k3]|] eqn:E3; [|discriminate].
  apply xr_seq_table_syms in E3; auto;
    [|unfold MaxML; lia | apply Forall_skipn'; exact Hb | exact ML_predef_syms].
  inversion H; subst. split; [simpl; auto|lia].
Qed.

(* ---------- the size_t repeat offsets in the sequence loop ---------- *)

(* a size_t repeat offset with k sequences left: in [1, 2^32), or (size_t)-1 decremented fewer than
   2^32 - 1 - k times *)
Definition rgood (k r: Z) : Prop := (1 <= r < 2 ^ 32) \/ (2 ^ 64 - 2 ^ 32 + k < r < 2 ^ 64).

Definition rgood3 (k: Z) (rep: Z * Z * Z) : Prop :=
  let '(r1, r2, r3) := rep in rgood k r1 /\ rgood k r2 /\ rgood k r3.

Lemma xr_rgood_mono (k k' r: Z) : k' <= k -> rgood k r -> rgood k' r.
Proof. unfold rgood. intros Hk [H|H]; [left; exact H|right; lia]. Qed.

Lemma xr_rgood_new (k v: Z) : 1 <= v < 2 ^ 32 -> rgood k v.
Proof. intros H. left. exact H. Qed.

(* `temp -= !temp` on (r1 - 1) mod 2^64 *)
Lemma xr_rgood_dec (k r: Z) : 0 <= k -> k + 1 <= 2 ^ 32 - 1 -> rgood (k + 1) r ->
  rgood k (let t := (r - 1) mod 2 ^ 64 in if t =? 0 then SIZE_MAX else t).
Proof.
  unfold rgood, SIZE_MAX. cbv zeta.
  change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  intros Hk Hk1 [H|H].
  - rewrite Z.mod_small by lia.
    destruct (r - 1 =? 0) eqn:E; [right; lia|]. apply Z.eqb_neq in E. left; lia.
  - rewrite Z.mod_small by lia.
    destruct (r - 1 =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]. right; lia.
Qed.

(* one offset resolution (ZSTD_decodeSequence) on an offset value of at most 32 bits *)
Lemma xr_c_offset (k: Z) rep ll ov :
  0 <= k -> k + 1 <= 2 ^ 32 - 1 -> 0 <= ov < 2 ^ 32 -> rgood3 (k + 1) rep -> rgood3 k (snd (c_offset rep ll ov)).
Proof.
  intros Hk Hk1 Hov. destruct rep as [[r1 r2] r3]. unfold rgood3. intros (H1 & H2 & H3).
  assert (M : forall r, rgood (k + 1) r -> rgood k r) by (intros r; apply xr_rgood_mono; lia).
  unfold c_offset.
  destruct (ov >? 3) eqn:E0.
  { apply Z.gtb_lt in E0. cbn [snd]. split; [apply xr_rgood_new; lia|auto]. }
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [cbn [snd]; auto|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [cbn [snd]; auto|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [cbn [snd]; auto|].
  cbn [snd]. split; [apply xr_rgood_dec; auto|auto].
Qed.

Lemma xr_seq_loop (e: xenv) (tLL tOF tML: fse_table) (V: list Z) (k: nat) (st: Z * Z * Z) (pos: Z)
    (rep: Z * Z * Z) (s: xex) s' pos' rep' :
  Forall (fun e => 0 <= fe_sym e <= MaxOff) (ft_cells tOF) ->
  Z.of_nat k <= 2 ^ 32 - 1 -> rgood3 (Z.of_nat k) rep ->
  x_seq_loop dseq_one c_offset e tLL tOF tML V k st pos rep s = Some (s', pos', rep') ->
  rgood3 0 rep'.
Proof.
  intros HOF. revert st pos rep s. induction k as [|k IH]; intros st pos rep s Hk Hr H.
  - simpl in H. inversion H; subst. exact Hr.
  - simpl in H. destruct st as [[sLL sOF] sML].
    destruct (dseq_one tLL tOF tML V (Nat.eqb k 0) sLL sOF sML pos) as [[[sq st2] pos2]|] eqn:D; [|discriminate].
    destruct (c_offset rep (sq_ll sq) (sq_ov sq)) as [off rep2] eqn:C.
    destruct (x_step _ _ _ _ _) as [s2|]; [|discriminate].
    apply loop_dseq_bounds in D as (_ & _ & Hov); [|exact HOF].
    eapply IH; [lia| |exact H].
    change rep2 with (snd (off, rep2)). rewrite <- C.
    apply xr_c_offset; [lia|lia|exact Hov|]. rewrite Nat2Z.inj_succ in Hr. exact Hr.
Qed.

(* the U32 truncation of such offsets after the loop is in [1, 2^32) *)
Lemma xr_rep32 (rep: Z * Z * Z) : rgood3 0 rep -> reps_ok (x_rep32 rep).
Proof.
  destruct rep as [[r1 r2] r3]. unfold rgood3, rgood, reps_ok, x_rep32. intros (H1 & H2 & H3).
  assert (Hm : forall r, (1 <= r < 2 ^ 32) \/ (2 ^ 64 - 2 ^ 32 + 0 < r < 2 ^ 64) -> 1 <= r mod 2 ^ 32 < 2 ^ 32).
  { change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
    intros r [Hr|Hr].
    - rewrite Z.mod_small; lia.
    - rewrite <- (Z.mod_unique r 4294967296 4294967295 (r - 18446744069414584320)); lia. }
  auto.
Qed.

Lemma xr_reps_rgood (k: Z) (rep: Z * Z * Z) : reps_ok rep -> rgood3 k rep.
Proof.
  destruct rep as [[r1 r2] r3]. unfold reps_ok, rgood3. intros (H1 & H2 & H3).
  repeat split; apply xr_rgood_new; assumption.
Qed.

(* the sequences of a block keep the repeat offsets in [1, 2^32) *)
Lemma xr_seqs (e: xenv) (tabs: seq_tabs) (rep: Z * Z * Z) (bits: list Z) (nbSeq: Z) (s0: xex) m op rep' :
  of_ok (Some tabs) -> reps_ok rep -> nbSeq < 2 ^ 17 ->
  x_seqs dseq_one c_offset e tabs rep bits nbSeq s0 = Some (m, op, rep') ->
  reps_ok rep'.
Proof.
  intros Hof Hr Hn H. destruct tabs as [[tLL tOF] tML]. unfold x_seqs in H. destruct Hof as (_ & HOF & _).
  destruct (negb (bs_okb bits)); [discriminate|].
  destruct (rd bits (bs_total bits) (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd bits p1 (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd bits p2 (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (x_seq_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[s p] r2]|] eqn:L; [|discriminate].
  destruct (negb (p =? 0)); [discriminate|].
  destruct (x_last _ _) as [[m2 op2]|]; [|discriminate].
  inversion H; subst. apply xr_rep32.
  assert (Hk : Z.of_nat (Z.to_nat nbSeq) <= 2 ^ 32 - 1).
  { lia. }
  eapply xr_seq_loop; [exact HOF|exact Hk| apply xr_reps_rgood, Hr | exact L].
Qed.

(* ---------- the block ---------- *)

Lemma xblock_reps_bytes (st st': xstate) (mem m': list Z) (ps op ds de: Z) (body: list Z) (bsm cap: Z)
    (str: bool) (n: Z) :
  bytes_ok body -> reps_ok (x_rep xhuf st) -> of_ok (x_seq xhuf st) ->
  xblock st mem ps op ds de body bsm cap str = Some (st', m', n) ->
  reps_ok (x_rep xhuf st') /\ of_ok (x_seq xhuf st').
Proof.
  intros Hb Hr Hof H. unfold xblock, x_block in H.
  destruct (Zlength body >? bsm); [discriminate|].
  destruct (x_lits _ _ _ _ _ _ _) as [[[lits lused] huf]|]; [|discriminate].
  destruct (x_seq_header ncount_c (x_seq xhuf st) (skipn (Z.to_nat lused) body)) as [[[nbSeq tabs] hused]|] eqn:Hh;
    [|discriminate].
  apply xr_seq_header in Hh as [Htabs Hnb]; [|apply Forall_skipn'; exact Hb|exact Hof].
  destruct (andb (nbSeq >? 0) (cap =? 0)); [discriminate|].
  destruct (x_lits_store _ _ _ _ _ _ _ _ _) as [[[[[m lr] li] lim] sp]|]; [|discriminate].
  match type of H with context [match ?r with Some _ => _ | None => None end] =>
    destruct r as [[[m2 op2] rep]|] eqn:R end; [|discriminate].
  inversion H; subst; clear H. cbn [x_rep x_seq]. split; [|exact Htabs].
  destruct (nbSeq =? 0).
  - destruct (x_last _ _); [|discriminate]. destruct p. inversion R; subst. exact Hr.
  - destruct tabs as [t|]; [|discriminate]. refine (xr_seqs _ _ _ _ nbSeq _ _ _ _ Htabs Hr _ R). lia.
Qed.
