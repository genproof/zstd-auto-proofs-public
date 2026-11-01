(* LOOP (the three sequence loops): the plain-Coq steps of the loop invariant,
   shared by the three loop bodies (BlkSeqLoopShort / BlkSeqLoopSplit / BlkSeqLoopLong).

   The invariant (model part, assumed only when the model succeeds: decode_seq_stream ... = Some seqs and
   exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep2)):
   - decoding: after id sequences decoded, the C states / position are the model's:
       decode_seqs tLL tOF tML s (Z.to_nat (nbSeq - id)) sLL sOF sML pos = Some (skipn id seqs, 0),
     with bs_ready pos lo (loop_init_model, then loop_dec_step);
   - executing: after ie sequences executed (blk = the block bytes so far, at [d, d + |blk|); lr = the
     literals left), the rest of the model is
       exec_seqs wsize crep hist lr (out ++ blk) (skipn ie seqs) = Some (out', lits', rep2)
     (loop_exec_step: one sequence; its first lo literals may already be written, the split loop's
     leftover copy);
   - the end: BIT_endOfDStream sees (lo, pos) = (0, 0) after the last sequence (loop_end_lo). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqDecModel Zstd.proof.dec.B.blk.BlkSeqEXEC.
Require Import Zstd.proof.dec.B.blk.BlkSeqDEC.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* ---------- decoding ---------- *)

(* the container invariant the initial reads keep *)
Definition lim_inv (pos lo: Z) : Prop := 0 <= lo /\ lo mod 8 = 0 /\ pos <= lo + 64 /\ bs_ready pos lo.

Lemma lim_reload_pos (p lo: Z) :
  0 <= lo -> lo mod 8 = 0 -> lo <= p -> p <= lo + 64 -> p <= snd (bs_reload p lo) + 64.
Proof.
  intros H0 H8 H1 H2. unfold bs_reload.
  destruct (p <? lo) eqn:E; [apply Z.ltb_lt in E; lia|].
  pose proof (Z.div_mod (lo + 64 - p) 8 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (lo + 64 - p) 8 ltac:(lia)) as Hm.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Hl. rewrite H8 in Hl.
  destruct (8 <=? lo / 8); [cbn [snd]; lia|].
  destruct (lo / 8 =? 0); [cbn [snd]; lia|].
  destruct (lo / 8 <? (lo + 64 - p) / 8) eqn:E3; cbn [snd]; [apply Z.ltb_lt in E3; lia | lia].
Qed.

Lemma lim_step (pos lo nb: Z) :
  lim_inv pos lo -> 0 <= nb <= 9 -> 0 <= pos - nb ->
  lo <= pos - nb /\ lim_inv (pos - nb) (snd (bs_reload (pos - nb) lo)).
Proof.
  intros (H0 & H8 & H64 & Hr) Hnb Hp.
  assert (Hle: lo <= pos - nb) by (destruct Hr; lia).
  split; [exact Hle|].
  pose proof (bs_reload_lo (pos - nb) lo H0 ltac:(lia)).
  split; [lia|]. split; [apply dce_reload_mod8, H8|]. split.
  - apply lim_reload_pos; lia.
  - apply bs_reload_ready; auto.
Qed.

Lemma lim_init (s: list Z) :
  bytes_ok s -> bs_wf s = true -> lim_inv (bs_total s) (8 * Z.max 0 (Zlength s - 8)).
Proof.
  intros Hb Hwf. split; [lia|]. split.
  { rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
  split; [|apply bs_init_ready; auto].
  unfold bs_total. rewrite <- Zlength_correct.
  assert (Hlast: highbit (last s 0) <= 7).
  { assert (Hl: 0 <= last s 0 < 256).
    { destruct s as [|b r] using rev_ind; [cbn; lia|]. rewrite last_last.
      unfold bytes_ok in Hb. apply Forall_app in Hb as [_ Hb]. inversion Hb; subst. exact H1. }
    unfold highbit. destruct (Z.eq_dec (last s 0) 0) as [->|Hn]; [cbn; lia|].
    assert (Z.log2 (last s 0) < 8); [|lia]. apply Z.log2_lt_pow2; [lia|]. cbn; lia. }
  lia.
Qed.

Lemma lim_peek (s: list Z) (pos lo nb: Z) (v: Z) :
  bytes_ok s -> 0 <= nb <= 9 -> nb <= pos -> (lo <= pos - nb -> v = bs_peek (bs_value s) pos nb) ->
  lo <= pos - nb -> v = bs_peek_s s pos nb.
Proof.
  intros Hb Hnb Hp Hv Hlo. rewrite (Hv Hlo). symmetry. apply bs_peek_s_eq; auto; lia.
Qed.

(* the three initial states (BIT_initDStream, then ZSTD_initFseState for LL, OF, ML: each reads ft_log bits
   (exact when they are in the container), then reloads) are the model's, and the container is ready *)
Lemma loop_init_model (tLL tOF tML: fse_table) (s: list Z) (nbSeq: Z) (seqs: list sequence) (v1 v2 v3: Z) :
  bytes_ok s -> bs_wf s = true -> fse_ok KLL tLL -> fse_ok KOF tOF -> fse_ok KML tML ->
  let pos0 := bs_total s in let lo0 := 8 * Z.max 0 (Zlength s - 8) in
  let pos1 := pos0 - ft_log tLL in let lo1 := snd (bs_reload pos1 lo0) in
  let pos2 := pos1 - ft_log tOF in let lo2 := snd (bs_reload pos2 lo1) in
  let pos3 := pos2 - ft_log tML in let lo3 := snd (bs_reload pos3 lo2) in
  (lo0 <= pos1 -> v1 = bs_peek (bs_value s) pos0 (ft_log tLL)) ->
  (lo1 <= pos2 -> v2 = bs_peek (bs_value s) pos1 (ft_log tOF)) ->
  (lo2 <= pos3 -> v3 = bs_peek (bs_value s) pos2 (ft_log tML)) ->
  decode_seq_stream tLL tOF tML s nbSeq = Some seqs ->
  bs_ready pos3 lo3 /\ decode_seqs tLL tOF tML s (Z.to_nat nbSeq) v1 v2 v3 pos3 = Some (seqs, 0).
Proof.
  intros Hb Hwf HLL HOF HML. cbv zeta. intros H1 H2 H3 Hd.
  destruct HLL as [HlLL _]. destruct HOF as [HlOF _]. destruct HML as [HlML _].
  cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
  unfold decode_seq_stream in Hd.
  destruct (negb (bs_okb s)); [discriminate|].
  unfold rd in Hd.
  destruct (bs_total s - ft_log tLL <? 0) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  destruct (bs_total s - ft_log tLL - ft_log tOF <? 0) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
  destruct (bs_total s - ft_log tLL - ft_log tOF - ft_log tML <? 0) eqn:E3; [discriminate|].
  apply Z.ltb_ge in E3.
  pose proof (lim_init s Hb Hwf) as I0.
  destruct (lim_step _ _ (ft_log tLL) I0 ltac:(lia) ltac:(lia)) as [L1 I1].
  destruct (lim_step _ _ (ft_log tOF) I1 ltac:(lia) ltac:(lia)) as [L2 I2].
  destruct (lim_step _ _ (ft_log tML) I2 ltac:(lia) ltac:(lia)) as [L3 I3].
  set (lo0 := 8 * Z.max 0 (Zlength s - 8)) in *.
  set (p1 := bs_total s - ft_log tLL) in *. set (l1 := snd (bs_reload p1 lo0)) in *.
  set (p2 := p1 - ft_log tOF) in *. set (l2 := snd (bs_reload p2 l1)) in *.
  rewrite <- (lim_peek s (bs_total s) lo0 (ft_log tLL) v1 Hb ltac:(lia) ltac:(lia) H1 L1) in Hd.
  rewrite <- (lim_peek s p1 l1 (ft_log tOF) v2 Hb ltac:(lia) ltac:(lia) H2 L2) in Hd.
  rewrite <- (lim_peek s p2 l2 (ft_log tML) v3 Hb ltac:(lia) ltac:(lia) H3 L3) in Hd.
  split; [apply I3|].
  destruct (decode_seqs tLL tOF tML s (Z.to_nat nbSeq) v1 v2 v3 _) as [[l p]|]; [|discriminate].
  destruct p as [|p|p]; try discriminate. injection Hd as ->. reflexivity.
Qed.

(* one decode step: the model's next sequence is dseq_one's (isLast iff it is the last), the rest follows *)
Lemma loop_dec_step (tLL tOF tML: fse_table) (s: list Z) (k: nat) (sLL sOF sML pos: Z) (l: list sequence) :
  decode_seqs tLL tOF tML s (S k) sLL sOF sML pos = Some (l, 0) ->
  exists sq a b c pn rest,
    l = sq :: rest /\
    dseq_one tLL tOF tML s (Nat.eqb k 0) sLL sOF sML pos = Some (sq, (a, b, c), pn) /\
    decode_seqs tLL tOF tML s k a b c pn = Some (rest, 0) /\
    (k = O -> rest = nil /\ pn = 0).
Proof.
  intros H. rewrite decode_seqs_S in H.
  destruct (dseq_one tLL tOF tML s (Nat.eqb k 0) sLL sOF sML pos) as [[[sq [[a b] c]] pn]|] eqn:E;
    [|discriminate].
  destruct k as [|k'].
  - injection H as <- Hp. exists sq, a, b, c, pn, nil. subst pn.
    split; [reflexivity|]. split; [first [exact E | reflexivity]|]. split; [reflexivity|]. auto.
  - destruct (decode_seqs tLL tOF tML s (S k') a b c pn) as [[l' p']|] eqn:E2; [|discriminate].
    injection H as <- ->. exists sq, a, b, c, pn, l'.
    split; [reflexivity|]. split; [first [exact E | reflexivity]|]. split; [first [exact E2 | reflexivity]|]. discriminate.
Qed.

(* after the model's last sequence (position 0) from a ready container, the container is the last one:
   BIT_endOfDStream returns 1 (lo' = 0: the reloads of ZSTD_decodeSequence only lower lo) *)
Lemma loop_end_lo (tLL tOF tML: fse_table) (s: list Z) (sLL sOF sML pos lo lo': Z) (sq: sequence)
    (stn: Z * Z * Z) :
  fse_ok KLL tLL -> fse_ok KOF tOF -> fse_ok KML tML ->
  0 <= sLL < 2 ^ ft_log tLL -> 0 <= sOF < 2 ^ ft_log tOF -> 0 <= sML < 2 ^ ft_log tML ->
  0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 -> bs_ready pos lo -> 0 <= lo' <= lo ->
  dseq_one tLL tOF tML s true sLL sOF sML pos = Some (sq, stn, 0) ->
  lo' = 0.
Proof.
  intros _ HOF _ _ _ _ H0 H8 Hpos Hrdy Hlo' Hone.
  unfold dseq_one, rd in Hone. cbv zeta in Hone.
  pose proof (dce_ml_bits (Z.to_nat (fe_sym (fse_cell tML sML)))) as HmlB.
  pose proof (dce_ll_bits (Z.to_nat (fe_sym (fse_cell tLL sLL)))) as HllB.
  assert (HofB: fe_sym (fse_cell tOF sOF) <= 31).
  { destruct HOF as (_ & _ & HF). unfold fse_cell.
    destruct (Nat.lt_ge_cases (Z.to_nat sOF) (length (ft_cells tOF))) as [Hl|Hl].
    - rewrite Forall_forall in HF. specialize (HF _ (nth_In _ {| fe_sym := 0; fe_nb := 0; fe_base := 0 |} Hl)).
      cbn [sk_max] in HF. unfold MaxOff in HF. lia.
    - rewrite nth_overflow by exact Hl. cbn. lia. }
  set (mlB := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0) in *.
  set (llB := nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_bits_tab 0) in *.
  set (ofB := fe_sym (fse_cell tOF sOF)) in *.
  destruct (pos - ofB <? 0); [discriminate|].
  destruct (pos - ofB - mlB <? 0); [discriminate|].
  destruct (pos - ofB - mlB - llB <? 0); [discriminate|].
  clearbody mlB llB ofB.
  injection Hone as _ _ Hp.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Hd. rewrite H8 in Hd.
  destruct Hrdy as [->|Hr]; [lia|].
  assert (lo = 0) by lia. lia.
Qed.

(* ---------- executing ---------- *)

(* the extDict lies inside its array (DecIface.layout_ok gives it) *)
Definition ext_in_bounds (e: ext_seg) (N: Z) : Prop :=
  match e with
  | ExtNone => True
  | ExtIn e1 elen => e1 <= N /\ 0 <= e1 - elen
  | ExtSep _ _ en ec e1 elen => Zlength ec = en /\ e1 <= en /\ 0 <= e1 - elen
  end.

(* ---------- helpers of loop_exec_step ---------- *)

Lemma les_rep_ok (crep: Z * Z * Z) (ll ov off: Z) (crep': Z * Z * Z) :
  rep_ok crep -> 1 <= ov < 2 ^ 32 -> resolve_offset crep ll ov = Some (off, crep') ->
  1 <= off /\ rep_ok crep'.
Proof.
  destruct crep as [[r1 r2] r3]. unfold rep_ok, resolve_offset. intros (H1 & H2 & H3) Hov H.
  destruct (ov >? 3) eqn:E; [apply Z.gtb_lt in E; inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 1); [inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 2); [inversion H; subst; lia|].
  destruct ((if ll =? 0 then ov + 1 else ov) =? 3); [inversion H; subst; lia|].
  destruct (r1 - 1 <=? 0) eqn:E4; [discriminate|]. apply Z.leb_gt in E4. inversion H; subst; lia.
Qed.

Lemma les_rep64 (crep: Z * Z * Z) : rep_ok crep -> rep64_ok crep.
Proof. destruct crep as [[r1 r2] r3]. unfold rep_ok, rep64_ok, SIZE_MAX. lia. Qed.

(* the history the model sees is unchanged in the current array *)
Lemma les_hist_view (c0 c: list val) (d ps cap bsm: Z) (e: ext_seg) (hist out: list Z) (wsize: Z) :
  0 <= ps <= d -> 0 <= cap -> d + cap <= Zlength c -> Zlength c0 = Zlength c -> 0 <= bsm ->
  hist_view c0 d ps e hist out wsize -> ext_clear d ps cap bsm e hist out wsize ->
  ext_in_bounds e (Zlength c) ->
  unchanged_outside c0 c d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)) ->
  hist_view c d ps e hist out wsize.
Proof.
  intros Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hu k Hk.
  destruct (Hhv k Hk) as [Hle Hch]. split; [exact Hle|]. rewrite <- Hch. unfold chist.
  assert (Hk1: 1 <= k) by lia.
  destruct (k <=? d - ps) eqn:E.
  - apply Z.leb_le in E. apply Hu; lia.
  - apply Z.leb_gt in E. destruct e as [|e1 elen|sh eb en ec e1 elen]; try reflexivity.
    simpl in Hcl, Hb. specialize (Hcl k ltac:(lia)).
    assert (0 <= Z.min cap (bsm + WILDCOPY_OVERLENGTH)) by (unfold WILDCOPY_OVERLENGTH; lia).
    apply Hu; lia.
Qed.

(* the offset is in the C's history *)
Lemma les_off (c0: list val) (d ps: Z) (e: ext_seg) (hist out: list Z) (wsize off nb ll: Z) :
  0 <= ps <= d -> 0 <= ext_len e -> 0 <= nb -> 0 <= ll ->
  hist_view c0 d ps e hist out wsize ->
  1 <= off -> off <= Zlength hist + Zlength out + nb + ll -> off <= wsize + Zlength hist ->
  off <= d + nb + ll - ps + ext_len e.
Proof.
  intros Hps He Hnb Hll Hhv Ho1 Ho2 Ho3.
  assert (Hho: Zlength (hist ++ out) = Zlength hist + Zlength out) by apply Zlength_app.
  destruct (Z_le_gt_dec off (Zlength hist + Zlength out)) as [Hle|Hgt].
  - destruct (Hhv off) as [H _]; [rewrite Hho; lia|]. lia.
  - destruct (Z_le_gt_dec 1 (Zlength hist + Zlength out)) as [H1|H1]; [|lia].
    destruct (Hhv (Zlength hist + Zlength out)) as [H _]; [rewrite Hho; lia|]. lia.
Qed.

Lemma les_ext_read (e: ext_seg) (d ps cap bsm: Z) (hist out: list Z) (wsize off nb ll lo ml E: Z) :
  ext_clear d ps cap bsm e hist out wsize ->
  0 <= nb -> 0 <= ll -> nb + ll <= bsm -> E <= d + cap ->
  off <= Zlength hist + Zlength out + nb + ll -> off <= wsize + Zlength hist ->
  ext_read_ok e (d + nb + lo) E (ll - lo) ml off ps.
Proof.
  intros Hcl Hnb Hll Hb HE Ho1 Ho2.
  destruct e as [|e1 elen|sh eb en ec e1 elen]; try exact I. unfold ext_read_ok. simpl in Hcl.
  replace (d + nb + lo + (ll - lo)) with (d + nb + ll) by lia.
  destruct (Z_le_gt_dec off (d + nb + ll - ps)) as [H|H]; [left; exact H|right; left].
  rewrite Zlength_app in Hcl. specialize (Hcl (off - nb - ll) ltac:(lia)).
  unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

Lemma les_lz_bytes (hist out: list Z) (off: Z) (ml: nat) :
  bytes_ok hist -> bytes_ok out -> bytes_ok (lz_copy hist out off ml).
Proof.
  revert out. induction ml as [|m IH]; intros out Hh Ho; simpl; [exact Ho|].
  apply IH; [exact Hh|]. unfold bytes_ok in *. apply Forall_app. split; [exact Ho|].
  constructor; [|constructor]. unfold byte_at.
  assert (Hb: Forall is_byte (hist ++ out)) by (apply Forall_app; auto).
  set (i := Z.to_nat _). destruct (Nat.lt_ge_cases i (length (hist ++ out))) as [Hi|Hi].
  - rewrite Forall_forall in Hb. apply Hb, nth_In, Hi.
  - rewrite nth_overflow by exact Hi. unfold is_byte. lia.
Qed.

(* loop_exec_step without bytes_ok mb; mb is the match copy's tail *)
Lemma loop_exec_step_core (c0 c: list val) (d ps cap bsm: Z) (e: ext_seg) (hist out: list Z) (wsize: Z)
    (blk lr: list Z) (lo: Z) (sq: sequence) (rest: list sequence) (crep: Z * Z * Z)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  0 <= ps <= d -> 0 <= cap -> d + cap <= Zlength c -> Zlength c0 = Zlength c -> 0 <= bsm ->
  hist_view c0 d ps e hist out wsize -> ext_clear d ps cap bsm e hist out wsize ->
  ext_in_bounds e (Zlength c) -> 0 <= ext_len e ->
  unchanged_outside c0 c d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)) ->
  bytes_ok lr -> rep_ok crep ->
  exec_seqs wsize crep hist lr (out ++ blk) (sq :: rest) = Some (out', lits', rep2) ->
  Zlength out' - Zlength out + Zlength lits' <= bsm ->
  0 <= lo <= sq_ll sq -> 0 <= sq_ml sq -> 1 <= sq_ov sq < 2 ^ 32 ->
  sublist d (d + Zlength blk + lo) c = zbytes (blk ++ firstn (Z.to_nat lo) lr) ->
  let ll := sq_ll sq in let ml := sq_ml sq in
  let k := d + Zlength blk in
  let L := firstn (Z.to_nat ll) lr in
  exists off crep' mb,
    c_offset crep ll (sq_ov sq) = (off, crep') /\ rep_ok crep' /\
    ll <= Zlength lr /\
    k + ll + ml <= d + (Zlength out' - Zlength out + Zlength lits') /\
    1 <= off <= k + ll - ps + ext_len e /\
    Zlength mb = ml /\ lz_copy hist (out ++ blk ++ L) off (Z.to_nat ml) = out ++ blk ++ L ++ mb /\
    (k + ll + ml <= d + cap ->
     (forall E, E <= d + cap -> ext_read_ok e (k + lo) E (ll - lo) ml off ps) /\
     sublist (k + lo) (k + ll + ml) (exec_c c (k + lo) (zbytes (skipn (Z.to_nat lo) L)) ml off ps e) =
       zbytes (skipn (Z.to_nat lo) L ++ mb)) /\
    exec_seqs wsize crep' hist (skipn (Z.to_nat ll) lr) (out ++ blk ++ L ++ mb) rest =
      Some (out', lits', rep2).
Proof.
  intros Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hel Hu Hlr Hrep Hex Hcnt Hlo Hml Hov Hblk.
  cbv zeta.
  cbn [exec_seqs] in Hex.
  destruct (sq_ll sq >? Zlength lr) eqn:Ell; [discriminate|]. rewrite Z.gtb_ltb in Ell; apply Z.ltb_ge in Ell.
  destruct (resolve_offset crep (sq_ll sq) (sq_ov sq)) as [[off crep']|] eqn:Er; [|discriminate].
  destruct (off >? _) eqn:Eo1 in Hex; [discriminate|]. rewrite Z.gtb_ltb in Eo1; apply Z.ltb_ge in Eo1.
  destruct (off >? _) eqn:Eo2 in Hex; [discriminate|]. rewrite Z.gtb_ltb in Eo2; apply Z.ltb_ge in Eo2.
  set (ll := sq_ll sq) in *. set (ml := sq_ml sq) in *.
  set (L := firstn (Z.to_nat ll) lr) in *.
  rewrite <- app_assoc in Eo1, Hex.
  destruct (les_rep_ok crep ll (sq_ov sq) off crep' Hrep Hov Er) as [Hoff1 Hrep'].
  destruct (lz_copy_app hist (out ++ blk ++ L) off (Z.to_nat ml)) as [mb [Hmb Hmbl]].
  assert (HmbZ: Zlength mb = ml) by (rewrite Zlength_correct, Hmbl; lia).
  assert (HLZ: Zlength L = ll).
  { unfold L. rewrite Zlength_correct, length_firstn. rewrite Zlength_correct in Ell. lia. }
  rewrite Hmb, <- !app_assoc in Hex.
  pose proof (Zlength_nonneg blk) as Hb0. pose proof (Zlength_nonneg lits') as Hl0.
  assert (Hend: d + Zlength blk + ll + ml <= d + (Zlength out' - Zlength out + Zlength lits')).
  { destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid].
    assert (Zlength out' = Zlength out + Zlength blk + ll + ml + Zlength mid)
      by (rewrite Hmid, !Zlength_app; lia).
    pose proof (Zlength_nonneg mid). lia. }
  rewrite !Zlength_app in Eo1.
  exists off, crep', mb.
  split; [apply c_offset_resolve; [apply les_rep64|]; assumption|].
  split; [exact Hrep'|]. split; [exact Ell|]. split; [exact Hend|].
  split; [split; [exact Hoff1|]; apply (les_off c0 d ps e hist out wsize); auto; lia|].
  split; [exact HmbZ|]. split; [rewrite Hmb, <- !app_assoc; reflexivity|].
  split; [|exact Hex].
  intros Hfit. split.
  - intros E HE. apply (les_ext_read e d ps cap bsm hist out wsize); auto; lia.
  - set (B := d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)).
    assert (HLsplit: firstn (Z.to_nat lo) lr ++ skipn (Z.to_nat lo) L = L).
    { replace (firstn (Z.to_nat lo) lr) with (firstn (Z.to_nat lo) L) by
        (unfold L; rewrite firstn_firstn; f_equal; lia).
      apply firstn_skipn. }
    assert (HsZ: Zlength (skipn (Z.to_nat lo) L) = ll - lo).
    { rewrite Zlength_correct, length_skipn. rewrite Zlength_correct in HLZ. lia. }
    assert (Hfl: Zlength (firstn (Z.to_nat lo) lr) = lo).
    { rewrite Zlength_correct, length_firstn. rewrite Zlength_correct in Ell. lia. }
    destruct (exec_c_lz c d (d + Zlength blk + lo) ps B e hist out (blk ++ firstn (Z.to_nat lo) lr)
                (skipn (Z.to_nat lo) L) wsize ml off) as [_ Hx].
    + exact Hps.
    + rewrite Zlength_app, Hfl. lia.
    + exact Hml.
    + unfold B, WILDCOPY_OVERLENGTH. lia.
    + unfold B. lia.
    + unfold L. apply Forall_skipn, Forall_firstn, Hlr.
    + exact Hblk.
    + apply (les_hist_view c0 c d ps cap bsm); auto.
    + destruct e as [|e1 elen|sh eb en ec e1 elen]; simpl in Hb |- *; auto.
      split; [lia|]. split; [lia|]. exact Hcl.
    + exact Hel.
    + exact Hoff1.
    + rewrite <- !app_assoc, HLsplit, !Zlength_app. lia.
    + exact Eo2.
    + rewrite HsZ in Hx. replace (d + Zlength blk + lo + (ll - lo) + ml) with (d + Zlength blk + ll + ml) in Hx
        by lia.
      rewrite Hx. f_equal.
      rewrite <- !app_assoc, HLsplit, Hmb.
      replace ((out ++ blk ++ L) ++ mb) with ((out ++ blk ++ firstn (Z.to_nat lo) lr) ++ (skipn (Z.to_nat lo) L ++ mb)).
      * apply ecl_skipn_app.
      * rewrite (app_assoc (out ++ blk ++ firstn (Z.to_nat lo) lr) (skipn (Z.to_nat lo) L) mb). f_equal.
        rewrite <- !app_assoc, HLsplit. reflexivity.
Qed.

(* One sequence sq of the model, executed by the C at op = d + |blk| + lo of the output array c, after the
   block bytes blk and the first lo literals of sq (already written: the split loop's leftover copy;
   lo = 0 otherwise); lr = the literals left before sq.  c0 = the output array at the block's start, of
   which the history (hist_view, ext_clear) is the model's; the C has written only in
   [d, d + min(cap, bsm + 32)).  When the rest of the model succeeds and the block's content
   cnt (|cnt| = |out'| - |out| + |lits'|) is at most bsm:
   - the C offset (c_offset) is the model's, the new repeat offsets are rep_ok;
   - ll literals are left, the offset is in the C's history (no literal / offset error of execSequence);
   - the sequence ends within the content (k + ll + ml <= d + |cnt|): a capacity error of execSequence
     (oend - op < ll + ml with oend = d + cap) means cap < |cnt|;
   - when it fits the capacity: ext_read_ok holds (any oend E <= d + cap) and the bytes execSequence writes
     for the rest of sq (exec_c, at k + lo, the ll - lo remaining literals) are the model's: the
     literals, then the match bytes mb;
   - the rest of the model continues from the new block bytes blk ++ L ++ mb. *)
Lemma loop_exec_step (c0 c: list val) (d ps cap bsm: Z) (e: ext_seg) (hist out: list Z) (wsize: Z)
    (blk lr: list Z) (lo: Z) (sq: sequence) (rest: list sequence) (crep: Z * Z * Z)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  0 <= ps <= d -> 0 <= cap -> d + cap <= Zlength c -> Zlength c0 = Zlength c -> 0 <= bsm ->
  hist_view c0 d ps e hist out wsize -> ext_clear d ps cap bsm e hist out wsize ->
  ext_in_bounds e (Zlength c) -> 0 <= ext_len e ->
  unchanged_outside c0 c d (d + Z.min cap (bsm + WILDCOPY_OVERLENGTH)) ->
  bytes_ok lr -> rep_ok crep ->
  exec_seqs wsize crep hist lr (out ++ blk) (sq :: rest) = Some (out', lits', rep2) ->
  Zlength out' - Zlength out + Zlength lits' <= bsm ->
  0 <= lo <= sq_ll sq -> 0 <= sq_ml sq -> 1 <= sq_ov sq < 2 ^ 32 ->
  sublist d (d + Zlength blk + lo) c = zbytes (blk ++ firstn (Z.to_nat lo) lr) ->
  let ll := sq_ll sq in let ml := sq_ml sq in
  let k := d + Zlength blk in
  let L := firstn (Z.to_nat ll) lr in
  exists off crep' mb,
    c_offset crep ll (sq_ov sq) = (off, crep') /\ rep_ok crep' /\
    ll <= Zlength lr /\
    k + ll + ml <= d + (Zlength out' - Zlength out + Zlength lits') /\
    1 <= off <= k + ll - ps + ext_len e /\
    Zlength mb = ml /\
    (k + ll + ml <= d + cap ->
     (forall E, E <= d + cap -> ext_read_ok e (k + lo) E (ll - lo) ml off ps) /\
     sublist (k + lo) (k + ll + ml) (exec_c c (k + lo) (zbytes (skipn (Z.to_nat lo) L)) ml off ps e) =
       zbytes (skipn (Z.to_nat lo) L ++ mb)) /\
    exec_seqs wsize crep' hist (skipn (Z.to_nat ll) lr) (out ++ blk ++ L ++ mb) rest =
      Some (out', lits', rep2).
Proof.
  intros Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hel Hu Hlr Hrep Hex Hcnt Hlo Hml Hov Hblk.
  destruct (loop_exec_step_core c0 c d ps cap bsm e hist out wsize blk lr lo sq rest crep out' lits' rep2
              Hps Hcap Hc Hc0 Hbsm Hhv Hcl Hb Hel Hu Hlr Hrep Hex Hcnt Hlo Hml Hov Hblk)
    as (off & crep' & mb & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  exists off, crep', mb. tauto.
Qed.
