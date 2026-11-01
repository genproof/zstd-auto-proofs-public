(* Sub-group DEC of CORE: the FSE sequence machine.

     ZSTD_initFseState, ZSTD_updateFseStateWithDInfo, ZSTD_decodeSequence

   The interface (seqState_t representation, the three funspecs) is CORE's (BlkSeqCORE.v); DEC_ok proves
   the three bodies.  The model side (one step dseq_one of Block.decode_seqs,
   the C offset resolution c_offset, the ready container bs_ready) is BlkSeqDecModel.v.

   seqState_t at p: the bit stream DStream (Spec_bits BIT_DStream_rep over the sequences bitstream s), the
   three ZSTD_fseState {state; table = dt + 1} for LL, OF (stateOffb), ML, and prevOffset[3] = the repeat
   offsets as size_t values.  The tables are seqtab_at_fm (BRep) wherever they live (context, DDict,
   globals); they are only read. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqDecModel.
Local Open Scope logic.

Definition t_seqstate : type := Tstruct ___gp_seqState_t noattr.
Definition t_fsestate : type := Tstruct ___gp_ZSTD_fseState noattr.
Definition t_bitd : type := Tstruct ___gp_BIT_DStream_t noattr.

(* an fseState: the state, the table pointer dt + 1 (the cells after the header) *)
Definition fse_val (st: Z) (dt: val) : reptype t_fsestate := (Vlong (Int64.repr st), offset_val 8 dt).

Definition rep64_vals (rep: Z * Z * Z) : list val :=
  let '(r1, r2, r3) := rep in [Vlong (Int64.repr r1); Vlong (Int64.repr r2); Vlong (Int64.repr r3)].

(* the three tables (LL, OF, ML) at tp = (pLL, pOF, pML), any shares and fastMode words *)
Definition seqtabs_at (sh: share * share * share) (t: fse_table * fse_table * fse_table) (fm: Z * Z * Z)
    (tp: val * val * val) : mpred :=
  let '(shLL, shOF, shML) := sh in let '(tLL, tOF, tML) := t in
  let '(fLL, fOF, fML) := fm in let '(pLL, pOF, pML) := tp in
  seqtab_at_fm shLL KLL tLL fLL pLL * seqtab_at_fm shOF KOF tOF fOF pOF * seqtab_at_fm shML KML tML fML pML.

Definition seqtabs_sh_ok (sh: share * share * share) : Prop :=
  let '(a, b, c) := sh in readable_share a /\ readable_share b /\ readable_share c.

(* the states are states of their tables *)
Definition states_ok (t: fse_table * fse_table * fse_table) (st: Z * Z * Z) : Prop :=
  let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
  0 <= sLL < 2 ^ ft_log tLL /\ 0 <= sOF < 2 ^ ft_log tOF /\ 0 <= sML < 2 ^ ft_log tML.

(* seqState_t at p: stream s at start, position pos / window lo (Spec_bits), states st = (LL, OF, ML) over
   the tables at tp, repeat offsets rep *)
Definition seqstate_at (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z)
    (tp: val * val * val) (rep: Z * Z * Z) (p: val) : mpred :=
  let '(sLL, sOF, sML) := st in let '(pLL, pOF, pML) := tp in
  BIT_DStream_rep sh gv s start pos lo (field_address t_seqstate (DOT _DStream) p) *
  field_at sh t_seqstate (DOT _stateLL) (fse_val sLL pLL) p *
  field_at sh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) p *
  field_at sh t_seqstate (DOT _stateML) (fse_val sML pML) p *
  field_at sh t_seqstate (DOT _prevOffset) (rep64_vals rep) p.

(* the largest literal / match length a code gives: base + (2^bits - 1) *)
Definition LL_VMAX : Z := 65536 + 65535.
Definition ML_VMAX : Z := 65539 + 65535.

(* the most bits one ZSTD_decodeSequence reads: offset 31, match 16, literal 16, states 9 + 9 + 8 *)
Definition DSEQ_BITS : Z := 89.

(* The model's reads (Block.rd: BitsFast.bs_peek_s, a 5-byte window) are the stream value's bits
   (Bitstream.bs_peek, what the BIT_* specs return) for reads of at most 32 bits inside the stream.
   (Needed by the decodeSequence body; part of DEC's work.) *)
Section bpse.
Local Open Scope Z_scope.

Lemma bpse_bytes_ok_skipn (k: nat) (l: list Z) : bytes_ok l -> bytes_ok (skipn k l).
Proof.
  revert l; induction k as [|k IH]; intros l Hl; simpl; auto.
  destruct l as [|b l]; auto. inversion Hl; subst. auto.
Qed.

Lemma bpse_le_value_skipn (k: nat) (l: list Z) :
  bytes_ok l -> le_value (skipn k l) = le_value l / 2 ^ (8 * Z.of_nat k).
Proof.
  revert l; induction k as [|k IH]; intros l Hl.
  - cbn [skipn]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - destruct l as [|b l]; cbn [skipn le_value].
    + rewrite ?Zdiv_0_l; reflexivity.
    + inversion Hl as [|? ? Hb Hl']; subst. unfold is_byte in Hb. rewrite IH by exact Hl'.
      replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by (rewrite Nat2Z.inj_succ; lia).
      rewrite Z.pow_add_r by lia. rewrite <- Z.div_div by (try lia; apply Z.pow_pos_nonneg; lia).
      f_equal. change (2 ^ 8) with 256.
      rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma bpse_le_value_firstn (m: nat) (l: list Z) :
  bytes_ok l -> le_value (firstn m l) = le_value l mod 2 ^ (8 * Z.of_nat m).
Proof.
  revert l; induction m as [|m IH]; intros l Hl.
  - cbn [firstn le_value]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.mod_1_r. reflexivity.
  - destruct l as [|b l]; cbn [firstn le_value].
    + rewrite ?Zmod_0_l; reflexivity.
    + inversion Hl as [|? ? Hb Hl']; subst. unfold is_byte in Hb. rewrite IH by exact Hl'.
      replace (8 * Z.of_nat (S m)) with (8 + 8 * Z.of_nat m) by (rewrite Nat2Z.inj_succ; lia).
      rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
      rewrite Z.rem_mul_r by (try lia; apply Z.pow_pos_nonneg; lia).
      rewrite (Z.mul_comm 256 (le_value l)), Z_mod_plus_full, Z.div_add by lia.
      rewrite (Z.mod_small b) by lia. rewrite (Z.div_small b) by lia. f_equal; f_equal; lia.
Qed.

End bpse.

Lemma bs_peek_s_eq (s: list Z) (pos nb: Z) :
  bytes_ok s -> 0 <= nb <= 32 -> nb <= pos -> bs_peek_s s pos nb = bs_peek (bs_value s) pos nb.
Proof.
  intros Hs Hnb Hpos. unfold bs_peek_s, bs_peek, bs_value.
  destruct (pos <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (pos - nb >=? 0) eqn:E2; [|rewrite Z.geb_leb in E2; apply Z.leb_gt in E2; lia].
  set (lo := pos - nb).
  assert (Hlo: 0 <= lo) by (unfold lo; lia).
  set (V := le_value s).
  unfold slice. rewrite bpse_le_value_firstn by (apply bpse_bytes_ok_skipn; auto).
  rewrite bpse_le_value_skipn by auto. fold V.
  rewrite !Z2Nat.id by (try apply Z.div_pos; lia).
  replace (2 ^ pos) with (2 ^ lo * 2 ^ nb)%Z at 2
    by (rewrite <- Z.pow_add_r by lia; f_equal; unfold lo; lia).
  rewrite Z.div_mul_cancel_r by (apply Z.pow_nonzero; lia).
  pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as Hr.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Hd.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.testbit_mod_pow2 by lia.
  rewrite Z.div_pow2_bits by lia.
  rewrite Z.div_pow2_bits by lia.
  rewrite Z.testbit_mod_pow2 by lia.
  rewrite Z.testbit_mod_pow2 by lia.
  rewrite Z.div_pow2_bits by lia.
  destruct (i <? nb) eqn:Ei.
  - apply Z.ltb_lt in Ei.
    replace (i + lo mod 8 <? 8 * 5) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (i + lo <? pos) with true by (symmetry; apply Z.ltb_lt; unfold lo in *; lia).
    cbn [andb]. f_equal. lia.
  - apply Z.ltb_ge in Ei.
    replace (i + lo <? pos) with false by (symmetry; apply Z.ltb_ge; unfold lo in *; lia).
    reflexivity.
Qed.

Lemma dce_forall_nth (l: list Z) (i: nat) :
  Forall (fun x => 0 <= x <= 16) l -> 0 <= nth i l 0 <= 16.
Proof.
  intros H. revert i. induction H as [|x l Hx Hl IH]; intros [|i]; cbn; try lia; auto.
Qed.

Lemma dce_ml_bits (i: nat) : 0 <= nth i ML_bits_tab 0 <= 16.
Proof. apply dce_forall_nth. unfold ML_bits_tab. repeat constructor; lia. Qed.

Lemma dce_ll_bits (i: nat) : 0 <= nth i LL_bits_tab 0 <= 16.
Proof. apply dce_forall_nth. unfold LL_bits_tab. repeat constructor; lia. Qed.

Lemma dce_peek0 (s: list Z) (p: Z) : 0 <= p -> bs_peek_s s p 0 = 0.
Proof.
  intros H. unfold bs_peek_s.
  destruct (p <? 0) eqn:E; [reflexivity|].
  replace (p - 0) with p by lia.
  destruct (p >=? 0) eqn:E2; [apply Z.mod_1_r|rewrite Z.geb_leb, Z.leb_gt in E2; lia].
Qed.

Lemma dce_reload_mod8 (p lo: Z) : lo mod 8 = 0 -> snd (bs_reload p lo) mod 8 = 0.
Proof.
  intros H. unfold bs_reload.
  destruct (p <? lo); [exact H|].
  destruct (8 <=? lo / 8); [cbn [snd]; rewrite Zminus_mod, H, Z.mul_comm, Z_mod_mult; reflexivity|].
  destruct (lo / 8 =? 0); [exact H|].
  destruct (lo / 8 <? (lo + 64 - p) / 8); [reflexivity|].
  cbn [snd]; rewrite Zminus_mod, H, Z.mul_comm, Z_mod_mult; reflexivity.
Qed.

(* The C reads of one ZSTD_decodeSequence are the model step's (dseq_one) when the container is ready.
   r*: the extra bits read (0 when none), u*: the state bits; each C read is known to be the model's
   read (bs_peek_s) when it lies above the window (lo <= the position after the read). *)
Lemma dseq_c_exact (tLL tOF tML: fse_table) (s: list Z) (last: bool) (sLL sOF sML pos lo: Z)
    (rOF rML rLL uLL uML uOF: Z) (sq: sequence) (stn: Z * Z * Z) (pn: Z) :
  let eLL := fse_cell tLL sLL in let eOF := fse_cell tOF sOF in let eML := fse_cell tML sML in
  let ofB := fe_sym eOF in
  let mlB := nth (Z.to_nat (fe_sym eML)) ML_bits_tab 0 in
  let llB := nth (Z.to_nat (fe_sym eLL)) LL_bits_tab 0 in
  let p1 := pos - ofB in let p2 := p1 - mlB in
  let lo2 := if 31 <=? ofB + mlB + llB then snd (bs_reload p2 lo) else lo in
  let p3 := p2 - llB in
  let p4 := p3 - fe_nb eLL in let p5 := p4 - fe_nb eML in let p6 := p5 - fe_nb eOF in
  0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 -> bs_ready pos lo ->
  0 <= ofB <= 31 ->
  0 <= fe_nb eLL <= 9 -> 0 <= fe_nb eML <= 9 -> 0 <= fe_nb eOF <= 8 ->
  (ofB = 0 -> rOF = 0) -> (0 < ofB -> lo <= p1 -> rOF = bs_peek_s s pos ofB) ->
  (mlB = 0 -> rML = 0) -> (0 < mlB -> lo <= p2 -> rML = bs_peek_s s p1 mlB) ->
  (llB = 0 -> rLL = 0) -> (0 < llB -> lo2 <= p3 -> rLL = bs_peek_s s p2 llB) ->
  (last = false -> lo2 <= p4 -> uLL = bs_peek_s s p3 (fe_nb eLL)) ->
  (last = false -> lo2 <= p5 -> uML = bs_peek_s s p4 (fe_nb eML)) ->
  (last = false -> lo2 <= p6 -> uOF = bs_peek_s s p5 (fe_nb eOF)) ->
  dseq_one tLL tOF tML s last sLL sOF sML pos = Some (sq, stn, pn) ->
  sq_ll sq = nth (Z.to_nat (fe_sym eLL)) LL_base_tab 0 + rLL /\
  sq_ml sq = nth (Z.to_nat (fe_sym eML)) ML_base_tab 0 + rML /\
  sq_ov sq = 2 ^ ofB + rOF /\
  pn = (if last then p3 else p6) /\
  (last = false -> stn = (fe_base eLL + uLL, fe_base eOF + uOF, fe_base eML + uML) /\
                   bs_ready p6 (snd (bs_reload p6 lo2))).
Proof.
  cbv zeta.
  intros H0 H8 Hpos Hrdy HofB HnLL HnML HnOF HrOF0 HrOF HrML0 HrML HrLL0 HrLL HuLL HuML HuOF Hone.
  pose proof (dce_ml_bits (Z.to_nat (fe_sym (fse_cell tML sML)))) as HmlB.
  pose proof (dce_ll_bits (Z.to_nat (fe_sym (fse_cell tLL sLL)))) as HllB.
  unfold dseq_one, rd in Hone; cbv zeta in Hone.
  set (ofB := fe_sym (fse_cell tOF sOF)) in *.
  set (mlB := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0) in *.
  set (llB := nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_bits_tab 0) in *.
  set (lo2 := if 31 <=? ofB + mlB + llB then snd (bs_reload (pos - ofB - mlB) lo) else lo) in *.
  set (nLL := fe_nb (fse_cell tLL sLL)) in *.
  set (nML := fe_nb (fse_cell tML sML)) in *.
  set (nOF := fe_nb (fse_cell tOF sOF)) in *.
  assert (Hlo1: lo = 0 \/ lo + 9 <= pos - ofB - mlB).
  { destruct Hrdy as [Hr|Hr]; [left; exact Hr|right; lia]. }
  assert (Hlo2: 0 <= lo2 /\ lo2 mod 8 = 0 /\ (lo2 = 0 \/ lo2 + 26 <= pos - ofB - mlB - llB)).
  { subst lo2. destruct (31 <=? ofB + mlB + llB) eqn:Et.
    - pose proof (bs_reload_lo (pos - ofB - mlB) lo H0 ltac:(lia)).
      pose proof (dce_reload_mod8 (pos - ofB - mlB) lo H8).
      destruct Hlo1 as [Hl|Hl].
      + subst lo. split; [lia|]. split; [assumption|]. left; lia.
      + pose proof (bs_reload_ready (pos - ofB - mlB) lo H0 H8 ltac:(lia)) as Hr.
        unfold bs_ready in Hr. split; [lia|]. split; [assumption|]. lia.
    - apply Z.leb_gt in Et. split; [lia|]. split; [assumption|].
      destruct Hrdy; [left; assumption|right; lia]. }
  destruct (pos - ofB <? 0) eqn:E1; [discriminate|]. apply Z.ltb_ge in E1.
  destruct (pos - ofB - mlB <? 0) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
  destruct (pos - ofB - mlB - llB <? 0) eqn:E3; [discriminate|]. apply Z.ltb_ge in E3.
  assert (XOF: bs_peek_s s pos ofB = rOF).
  { destruct (Z.eq_dec ofB 0) as [Hz|Hz].
    - rewrite HrOF0 by exact Hz. rewrite Hz. apply dce_peek0. lia.
    - symmetry. apply HrOF; lia. }
  assert (XML: bs_peek_s s (pos - ofB) mlB = rML).
  { destruct (Z.eq_dec mlB 0) as [Hz|Hz].
    - rewrite HrML0 by exact Hz. rewrite Hz. apply dce_peek0. lia.
    - symmetry. apply HrML; lia. }
  assert (XLL: bs_peek_s s (pos - ofB - mlB) llB = rLL).
  { destruct (Z.eq_dec llB 0) as [Hz|Hz].
    - rewrite HrLL0 by exact Hz. rewrite Hz. apply dce_peek0. lia.
    - symmetry. apply HrLL; lia. }
  rewrite XOF, XML, XLL in Hone.
  destruct last.
  - injection Hone as <- <- <-. cbn [sq_ll sq_ml sq_ov]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. discriminate.
  - destruct (pos - ofB - mlB - llB - nLL <? 0) eqn:E4; [discriminate|]. apply Z.ltb_ge in E4.
    destruct (pos - ofB - mlB - llB - nLL - nML <? 0) eqn:E5; [discriminate|]. apply Z.ltb_ge in E5.
    destruct (pos - ofB - mlB - llB - nLL - nML - nOF <? 0) eqn:E6; [discriminate|].
    apply Z.ltb_ge in E6.
    assert (Hw: lo2 <= pos - ofB - mlB - llB - nLL - nML - nOF) by lia.
    rewrite <- (HuLL eq_refl ltac:(lia)), <- (HuML eq_refl ltac:(lia)), <- (HuOF eq_refl ltac:(lia)) in Hone.
    injection Hone as <- <- <-. cbn [sq_ll sq_ml sq_ov]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. intros _. split; [reflexivity|].
    apply bs_reload_ready; [apply Hlo2|apply Hlo2|exact Hw].
Qed.

(* ------------------------------------------------------------------ *)
(* ZSTD_initFseState(&st, &bitD, dt): reads tableLog bits (the header cell of the table at dt), reloads,
   sets st = {the bits read; dt + 1}.  Exact when the bits are in the container (lo <= pos - log). *)
Definition ZSTD_initFseState_spec : ident * funspec :=
  DECLARE _ZSTD_initFseState
  WITH sh: share, pst: val, shb: share, pb: val, gv: globals, s: list Z, start: val, pos: Z, lo: Z,
       shs: share, bp: val, buf: list Z, off: Z, sht: share, k: seqkind, t: fse_table, fm: Z, dt: val
  PRE [ tptr t_fsestate, tptr t_bitd, tptr t_seqSymbol ]
    PROP (writable_share sh; writable_share shb; readable_share shs; readable_share sht;
          bit_src_ok s start bp buf off; bcons pos lo + ft_log t <= Int.max_unsigned)
    PARAMS (pst; pb; dt) GLOBALS (gv)
    SEP (data_at_ sh t_fsestate pst; BIT_DStream_rep shb gv s start pos lo pb; bit_src shs bp buf;
         seqtab_at_fm sht k t fm dt)
  POST [ tvoid ]
    EX v: Z,
    PROP (0 <= v < 2 ^ ft_log t; lo <= pos - ft_log t -> v = bs_peek (bs_value s) pos (ft_log t))
    RETURN ()
    SEP (data_at sh t_fsestate (fse_val v dt) pst;
         BIT_DStream_rep shb gv s start (pos - ft_log t) (snd (bs_reload (pos - ft_log t) lo)) pb;
         bit_src shs bp buf; seqtab_at_fm sht k t fm dt).

(* ZSTD_updateFseStateWithDInfo(&st, &bitD, nextState, nbBits): st.state := nextState + readBits(nbBits);
   no reload. *)
Definition ZSTD_updateFseStateWithDInfo_spec : ident * funspec :=
  DECLARE _ZSTD_updateFseStateWithDInfo
  WITH sh: share, pst: val, st0: val, tbl: val, shb: share, pb: val, gv: globals, s: list Z, start: val,
       pos: Z, lo: Z, ns: Z, nb: Z
  PRE [ tptr t_fsestate, tptr t_bitd, tushort, tuint ]
    PROP (writable_share sh; writable_share shb; 0 <= ns < 2 ^ 16; 0 <= nb <= 32;
          bcons pos lo + nb <= Int.max_unsigned)
    PARAMS (pst; pb; Vint (Int.repr ns); Vint (Int.repr nb))
    SEP (data_at sh t_fsestate (st0, tbl) pst; BIT_DStream_rep shb gv s start pos lo pb)
  POST [ tvoid ]
    EX v: Z,
    PROP (0 <= v < 2 ^ nb; lo <= pos - nb -> v = bs_peek (bs_value s) pos nb)
    RETURN ()
    SEP (data_at sh t_fsestate (Vlong (Int64.repr (ns + v)), tbl) pst;
         BIT_DStream_rep shb gv s start (pos - nb) lo pb).

(* ZSTD_decodeSequence(&seq, &seqState, longOffsets, isLastSeq) (64-bit, non-aarch64 path): one sequence.
   Always: the sequence (ll, ml, offset) has code-range lengths and the C offset resolution of some offset
   value ov (c_offset; ll0 = (LL baseValue == 0) iff ll = 0), the states stay states of their tables
   (unchanged when last), at most DSEQ_BITS bits are read, reloads only lower the window.  When the
   container is ready (bs_ready) and the model's step dseq_one succeeds: exactly its sequence (ll, ml,
   ov), its position, and (not last) its next states, with the container ready again. *)
Definition ZSTD_decodeSequence_spec : ident * funspec :=
  DECLARE _ZSTD_decodeSequence
  WITH gv: globals, shq: share, q: val, sh: share, p: val, s: list Z, start: val, pos: Z, lo: Z,
       st: Z * Z * Z, t: fse_table * fse_table * fse_table, tp: val * val * val,
       sht: share * share * share, fm: Z * Z * Z, rep: Z * Z * Z,
       shs: share, bp: val, buf: list Z, off: Z, lof: Z, last: bool
  PRE [ tptr t_seq, tptr t_seqstate, tint, tint ]
    PROP (writable_share shq; writable_share sh; readable_share shs; seqtabs_sh_ok sht;
          bit_src_ok s start bp buf off; states_ok t st; rep64_ok rep;
          bcons pos lo + DSEQ_BITS <= Int.max_unsigned; lof = 0 \/ lof = 1)
    PARAMS (q; p; Vint (Int.repr lof); Vint (Int.repr (if last then 1 else 0))) GLOBALS (gv)
    SEP (data_at_ shq t_seq q; seqstate_at sh gv s start pos lo st tp rep p; seqtabs_at sht t fm tp;
         bit_src shs bp buf)
  POST [ tvoid ]
    EX ll: Z, EX ml: Z, EX ov: Z, EX st': Z * Z * Z, EX pos': Z, EX lo': Z,
    PROP (0 <= ll <= LL_VMAX; 3 <= ml <= ML_VMAX; 1 <= ov < 2 ^ 32;
          states_ok t st'; pos - DSEQ_BITS <= pos' <= pos; 0 <= lo' <= lo;
          last = true -> st' = st;
          bs_ready pos lo ->
          forall sq stn pn,
            (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
             dseq_one tLL tOF tML s last sLL sOF sML pos) = Some (sq, stn, pn) ->
            ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
            (last = false -> st' = stn /\ bs_ready pos' lo');
          (* the overflow regime: when a read of the model's step goes below the start of the stream, so does
             the C's position (it reads the same numbers of bits), and it stays there (positions only decrease):
             the final BIT_endOfDStream check fails *)
          (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
           dseq_one tLL tOF tML s last sLL sOF sML pos) = None -> pos' < 0)
    RETURN ()
    SEP (data_at shq t_seq (seqrep ll ml (fst (c_offset rep ll ov))) q;
         seqstate_at sh gv s start pos' lo' st' tp (snd (c_offset rep ll ov)) p;
         seqtabs_at sht t fm tp; bit_src shs bp buf).

(* ================= sub-group DEC ================= *)
Definition DEC_ids : list ident :=
  [ _ZSTD_initFseState; _ZSTD_updateFseStateWithDInfo; _ZSTD_decodeSequence ].
Definition DEC_exports : funspecs :=
  [ ZSTD_initFseState_spec; ZSTD_updateFseStateWithDInfo_spec; ZSTD_decodeSequence_spec ].
Definition DEC_imports : funspecs := [ ZSTD_seqCopy_spec ].
Definition DEC_obligation : Prop := subtree_ok DEC_ids DEC_exports (G_BLK ++ DEC_imports).

Definition DEC_G : funspecs := G_BLK ++ DEC_imports ++ DEC_exports.

Lemma body_ZSTD_updateFseStateWithDInfo :
  semax_body Vprog DEC_G f_ZSTD_updateFseStateWithDInfo ZSTD_updateFseStateWithDInfo_spec.
Proof.
  start_function.
  unfold bcons in *.
  forward_call (shb, pb, gv, s, start, pos, lo, nb).
  Intros v.
  forward.
  Exists v. entailer!. apply derives_refl.
Qed.

(* for (;;break) {} (DEBUGLOG): a no-op *)
Lemma dec_skipbreak_seq : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros Espec cs Delta P c R H.
apply semax_seq with P; [|exact H].
apply semax_loop with P.
2: { eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
     apply andp_left2, derives_refl. }
eapply semax_post; [| | | | apply semax_skip].
all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
- intros rho; simpl; apply andp_left2, derives_refl.
- intros rho; simpl; apply andp_left2, FF_left.
- intros rho; simpl; apply andp_left2, FF_left.
- intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

Lemma sk_maxlog_le (k: seqkind) : sk_maxlog k <= 9.
Proof. destruct k; cbv; discriminate. Qed.

Lemma body_ZSTD_initFseState :
  semax_body Vprog DEC_G f_ZSTD_initFseState ZSTD_initFseState_spec.
Proof.
  start_function.
  unfold bcons in *.
  unfold seqtab_at_fm. Intros.
  assert (Hlog: 0 <= ft_log t <= 9).
  { destruct H1 as [[? ?] _]. pose proof (sk_maxlog_le k). lia. }
  forward. forward. forward.
  forward_call (shb, pb, gv, s, start, pos, lo, ft_log t).
  Intros v.
  forward.
  apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
  forward_call (shb, pb, gv, s, start, pos - ft_log t, lo, shs, bp, buf, off).
  forward.
  Exists v. entailer!. unfold seqtab_at_fm, fse_val. entailer!.
Qed.

(* one cell of a sequence table apart *)
Lemma seqarr_split (sh: share) (n v: Z) (c: list (val * (val * (val * val)))) (dt: val) :
  0 <= v < n -> Zlength c = n -> field_compatible (tarray t_seqSymbol n) [] dt ->
  data_at sh (tarray t_seqSymbol n) c dt =
  data_at sh (tarray t_seqSymbol v) (sublist 0 v c) dt *
  data_at sh t_seqSymbol (Znth v c) (offset_val (8 * v) dt) *
  data_at sh (tarray t_seqSymbol (n - (v + 1))) (sublist (v + 1) n c) (offset_val (8 * (v + 1)) dt).
Proof.
  intros Hv Hn FC.
  rewrite (@split3_data_at_Tarray CompSpecs sh t_seqSymbol n v (v + 1) c c (sublist 0 v c) (sublist v (v + 1) c) (sublist (v + 1) n c)).
  2: (unfold naturally_aligned; simpl; auto).
  2: lia.
  2: (split; [lia|]; apply Z.eq_le_incl; exact (eq_sym Hn)).
  2: (symmetry; apply sublist_same; [reflexivity | exact (eq_sym Hn)]).
  2-4: reflexivity.
  change (Tarray t_seqSymbol n noattr) with (tarray t_seqSymbol n).
  rewrite !arr_field_address0 by (auto; lia).
  replace (v + 1 - v) with 1 by lia.
  rewrite (sublist_len_1 v c) by lia.
  rewrite (@data_at_singleton_array_eq CompSpecs sh t_seqSymbol (Znth v c)) by reflexivity.
  simpl sizeof. reflexivity.
Qed.

Lemma seqcell_Znth (k: seqkind) (t: fse_table) (i: Z) :
  0 <= i < Zlength (ft_cells t) ->
  Znth i (map (seqcell k) (ft_cells t)) = seqcell k (fse_cell t i).
Proof.
  intros Hi. unfold Znth. destruct (Z_lt_dec i 0); [lia|].
  unfold fse_cell.
  rewrite (nth_indep _ _ (seqcell k {| fe_sym := 0; fe_nb := 0; fe_base := 0 |})).
  2: { rewrite length_map. rewrite Zlength_correct in Hi. lia. }
  apply map_nth.
Qed.

Lemma BIT_rep_inv (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (p: val) :
  BIT_DStream_rep sh gv s start pos lo p |-- !! bit_inv s pos lo.
Proof. unfold BIT_DStream_rep. Intros ptr lim. entailer!. Qed.

Lemma add_cell_ptr (d: val) (i: Z) :
  isptr d -> 0 <= i <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr t_seqSymbol) tulong d (Vlong (Int64.repr i))) =
  offset_val (8 * i) d.
Proof.
  intros Hd Hi. destruct d; try contradiction. simpl. unfold sem_add_ptr_long. simpl. do 2 f_equal.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia. unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8) by (cbv; split; discriminate). apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_mult; [apply Ptrofs.eqm_refl | apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr].
Qed.

Lemma cell_forall (t: fse_table) (P: fse_entry -> Prop) (i: Z) :
  Forall P (ft_cells t) -> 0 <= i < Zlength (ft_cells t) -> P (fse_cell t i).
Proof.
  intros HF Hi. unfold fse_cell. rewrite Forall_forall in HF. apply HF.
  apply nth_In. rewrite Zlength_correct in Hi. lia.
Qed.

Lemma ll_tab_facts (c: Z) : 0 <= c <= 35 ->
  0 <= sk_bits KLL c <= 16 /\ 0 <= sk_base KLL c /\ sk_base KLL c + 2 ^ sk_bits KLL c - 1 <= LL_VMAX /\
  (sk_base KLL c = 0 -> sk_bits KLL c = 0).
Proof.
  intros Hc. assert (E: c = Z.of_nat (Z.to_nat c)) by lia. remember (Z.to_nat c) as n.
  assert (Hn: (n < 36)%nat) by lia. rewrite E. clear Heqn E Hc.
  do 36 (destruct n as [|n]; [cbv - [Z.le Z.lt]; lia|]). lia.
Qed.

Lemma ml_tab_facts (c: Z) : 0 <= c <= 52 ->
  0 <= sk_bits KML c <= 16 /\ 3 <= sk_base KML c /\ sk_base KML c + 2 ^ sk_bits KML c - 1 <= ML_VMAX.
Proof.
  intros Hc. assert (E: c = Z.of_nat (Z.to_nat c)) by lia. remember (Z.to_nat c) as n.
  assert (Hn: (n < 53)%nat) by lia. rewrite E. clear Heqn E Hc.
  do 53 (destruct n as [|n]; [cbv - [Z.le Z.lt]; lia|]). lia.
Qed.

Lemma of_tab_facts (c: Z) : 0 <= c <= 31 ->
  sk_bits KOF c = c /\ sk_base KOF c = (if c <? 2 then c else 2 ^ c - 3).
Proof.
  intros Hc. assert (E: c = Z.of_nat (Z.to_nat c)) by lia. remember (Z.to_nat c) as n.
  assert (Hn: (n < 32)%nat) by lia. rewrite E. clear Heqn E Hc.
  do 32 (destruct n as [|n]; [vm_compute; split; reflexivity|]). lia.
Qed.

Lemma zext8_repr (x: Z) : 0 <= x < 256 -> Int.zero_ext 8 (Int.repr x) = Int.repr x.
Proof.
  intros Hx. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia. f_equal.
  rewrite Zbits.Zzero_ext_mod by lia. apply Z.mod_small. cbv - [Z.le Z.lt]; lia.
Qed.

Lemma c_offset_ll (rep: Z * Z * Z) (ll ll' ov: Z) :
  (ll =? 0) = (ll' =? 0) -> c_offset rep ll ov = c_offset rep ll' ov.
Proof. intros E. destruct rep as [[r1 r2] r3]. unfold c_offset. rewrite E. reflexivity. Qed.

Lemma c_offset_big (r1 r2 r3 ll ov: Z) : 4 <= ov -> c_offset (r1, r2, r3) ll ov = (ov - 3, (ov - 3, r1, r2)).
Proof. intros H. unfold c_offset. replace (ov >? 3) with true by lia. reflexivity. Qed.

Section dpo.
Local Open Scope Z_scope.
Lemma dpo_reload_le (p lo: Z) :
  0 <= lo -> lo mod 8 = 0 -> p <= lo + 64 -> p <= snd (bs_reload p lo) + 64.
Proof.
  intros H0 H8 H. unfold bs_reload.
  assert (Hk: 8 * (lo / 8) = lo) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
  assert (Hnb: 8 * ((lo + 64 - p) / 8) <= lo + 64 - p /\ lo + 64 - p < 8 * ((lo + 64 - p) / 8) + 8).
  { pose proof (Z.div_mod (lo + 64 - p) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lo + 64 - p) 8 ltac:(lia)). lia. }
  destruct (p <? lo) eqn:E; [cbn [snd]; lia|].
  destruct (8 <=? lo / 8); [cbn [snd]; lia|].
  destruct (lo / 8 =? 0); [cbn [snd]; lia|].
  destruct (lo / 8 <? (lo + 64 - p) / 8) eqn:E3; [apply Z.ltb_lt in E3; cbn [snd]; lia|].
  cbn [snd]; lia.
Qed.
End dpo.

(* hides hypotheses from lia *)
Definition dpo_hide (P: Prop) : Prop := P.

(* The pure part of ZSTD_decodeSequence's postcondition, from the facts the C body establishes:
   r* = the extra bits read (BIT_readBitsFast posts; 0 when none), u* = the state bits (not last), the
   window lo2 after the optional reload (totalBits >= 31) and lo' after the final reload. *)
Lemma dec_post_ok (tLL tOF tML: fse_table) (s: list Z) (last: bool) (sLL sOF sML pos lo: Z)
    (rOF rML rLL uLL uML uOF: Z) :
  let eLL := fse_cell tLL sLL in let eOF := fse_cell tOF sOF in let eML := fse_cell tML sML in
  let cOF := fe_sym eOF in
  let xML := sk_bits KML (fe_sym eML) in let xLL := sk_bits KLL (fe_sym eLL) in
  let bML := sk_base KML (fe_sym eML) in let bLL := sk_base KLL (fe_sym eLL) in
  let p1 := pos - cOF in let p2 := p1 - xML in
  let lo2 := if 31 <=? xLL + xML + cOF then snd (bs_reload p2 lo) else lo in
  let p3 := p2 - xLL in
  let p4 := p3 - fe_nb eLL in let p5 := p4 - fe_nb eML in let p6 := p5 - fe_nb eOF in
  let st' := if last then (sLL, sOF, sML) else (fe_base eLL + uLL, fe_base eOF + uOF, fe_base eML + uML) in
  let pos' := if last then p3 else p6 in
  let lo' := if last then lo2 else snd (bs_reload p6 lo2) in
  let ll := bLL + rLL in let ml := bML + rML in let ov := 2 ^ cOF + rOF in
  bit_inv s pos lo -> bcons pos lo + DSEQ_BITS <= Int.max_unsigned ->
  fse_ok KLL tLL -> fse_ok KOF tOF -> fse_ok KML tML -> states_ok (tLL, tOF, tML) (sLL, sOF, sML) ->
  0 <= rOF < 2 ^ cOF -> (cOF = 0 -> rOF = 0) ->
  (0 < cOF -> lo <= p1 \/ (lo = 0 /\ 0 < pos) -> rOF = bs_peek (bs_value s) pos cOF) ->
  0 <= rML < 2 ^ xML -> (xML = 0 -> rML = 0) ->
  (0 < xML -> lo <= p2 \/ (lo = 0 /\ 0 < p1) -> rML = bs_peek (bs_value s) p1 xML) ->
  0 <= rLL < 2 ^ xLL -> (xLL = 0 -> rLL = 0) ->
  (0 < xLL -> lo2 <= p3 \/ (lo2 = 0 /\ 0 < p2) -> rLL = bs_peek (bs_value s) p2 xLL) ->
  (last = false -> 0 <= uLL < 2 ^ fe_nb eLL /\ (lo2 <= p4 -> uLL = bs_peek (bs_value s) p3 (fe_nb eLL))) ->
  (last = false -> 0 <= uML < 2 ^ fe_nb eML /\ (lo2 <= p5 -> uML = bs_peek (bs_value s) p4 (fe_nb eML))) ->
  (last = false -> 0 <= uOF < 2 ^ fe_nb eOF /\ (lo2 <= p6 -> uOF = bs_peek (bs_value s) p5 (fe_nb eOF))) ->
  (ll =? 0) = (bLL =? 0) /\
  0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= ov < 2 ^ 32 /\
  states_ok (tLL, tOF, tML) st' /\ pos - DSEQ_BITS <= pos' <= pos /\ 0 <= lo' <= lo /\
  (last = true -> st' = (sLL, sOF, sML)) /\
  (bs_ready pos lo ->
   forall sq stn pn,
     dseq_one tLL tOF tML s last sLL sOF sML pos = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     (last = false -> st' = stn /\ bs_ready pos' lo')).
Proof.
  cbv zeta.
  intros Hinv Hbc HokLL HokOF HokML Hst HrOFb HrOF0 HrOF HrMLb HrML0 HrML HrLLb HrLL0 HrLL HuLL HuML HuOF.
  let T1 := type of HrOF in let T2 := type of HrML in let T3 := type of HrLL in
  let T4 := type of HuLL in let T5 := type of HuML in let T6 := type of HuOF in
  assert (PACK: dpo_hide (T1 /\ T2 /\ T3 /\ T4 /\ T5 /\ T6)) by (unfold dpo_hide; tauto).
  clear HrOF HrML HrLL HuLL HuML HuOF.
  destruct Hinv as (Hbytes & Hlen & Hlo0 & Hlo8 & Hlok & Hposlo & Hcons).
  destruct Hst as (HsLL & HsOF & HsML).
  destruct HokLL as (HlogLL & HzLL & HfLL).
  destruct HokOF as (HlogOF & HzOF & HfOF).
  destruct HokML as (HlogML & HzML & HfML).
  pose proof (cell_forall _ _ sLL HfLL ltac:(lia)) as CLL. cbv beta in CLL.
  pose proof (cell_forall _ _ sOF HfOF ltac:(lia)) as COF. cbv beta in COF.
  pose proof (cell_forall _ _ sML HfML ltac:(lia)) as CML. cbv beta in CML.
  unfold sk_max, sk_maxlog, MaxLL, MaxML, MaxOff, LLFSELog, MLFSELog, OffFSELog in *.
  set (eLL := fse_cell tLL sLL) in *. set (eOF := fse_cell tOF sOF) in *. set (eML := fse_cell tML sML) in *.
  destruct CLL as (CsLL & CnLL & CbLL & CpLL).
  destruct COF as (CsOF & CnOF & CbOF & CpOF).
  destruct CML as (CsML & CnML & CbML & CpML).
  pose proof (ll_tab_facts (fe_sym eLL) ltac:(lia)) as TLL.
  pose proof (ml_tab_facts (fe_sym eML) ltac:(lia)) as TML.
  set (cOF := fe_sym eOF) in *.
  set (xML := sk_bits KML (fe_sym eML)) in *. set (xLL := sk_bits KLL (fe_sym eLL)) in *.
  set (bML := sk_base KML (fe_sym eML)) in *. set (bLL := sk_base KLL (fe_sym eLL)) in *.
  assert (P2LL: 2 ^ fe_nb eLL <= 2 ^ ft_log tLL) by lia.
  assert (HpOF: 0 < 2 ^ cOF <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
  assert (H232: 2 ^ 32 = (2 * 2 ^ 31)%Z) by reflexivity.
  assert (HpML: 0 < 2 ^ xML) by (apply Z.pow_pos_nonneg; lia).
  assert (HpLL: 0 < 2 ^ xLL) by (apply Z.pow_pos_nonneg; lia).
  set (lo2 := if 31 <=? xLL + xML + cOF then snd (bs_reload (pos - cOF - xML) lo) else lo) in *.
  assert (Hlo2: 0 <= lo2 <= lo /\ lo2 mod 8 = 0 /\ pos - cOF - xML <= lo2 + 64).
  { subst lo2. destruct (31 <=? xLL + xML + cOF).
    - pose proof (bs_reload_lo (pos - cOF - xML) lo Hlo0 ltac:(lia)).
      pose proof (dce_reload_mod8 (pos - cOF - xML) lo Hlo8).
      pose proof (dpo_reload_le (pos - cOF - xML) lo Hlo0 Hlo8 ltac:(lia)). lia.
    - lia. }
  assert (Hlo': 0 <= (if last then lo2 else snd (bs_reload (pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML - fe_nb eOF) lo2)) <= lo).
  { destruct last; [lia|].
    pose proof (bs_reload_lo (pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML - fe_nb eOF) lo2 ltac:(lia) ltac:(lia)). lia. }
  split.
  { destruct (Z.eq_dec bLL 0) as [Hz|Hz].
    - rewrite (HrLL0 (proj2 (proj2 (proj2 TLL)) Hz)), Hz. reflexivity.
    - replace (bLL + rLL =? 0) with false by lia. replace (bLL =? 0) with false by lia. reflexivity. }
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { destruct last; [repeat split; lia|].
    unfold dpo_hide in PACK. destruct PACK as (_ & _ & _ & HuLL & HuML & HuOF).
    destruct (HuLL eq_refl) as [HuLLb _]. destruct (HuML eq_refl) as [HuMLb _].
    destruct (HuOF eq_refl) as [HuOFb _]. clear HuLL HuML HuOF. repeat split; lia. }
  split; [unfold DSEQ_BITS; destruct last; lia|].
  split; [exact Hlo'|].
  split; [destruct last; [reflexivity|discriminate]|].
  intros Hrdy sq stn pn Hone.
  unfold dpo_hide in PACK. destruct PACK as (HrOF & HrML & HrLL & HuLL & HuML & HuOF).
  pose proof (dseq_c_exact tLL tOF tML s last sLL sOF sML pos lo rOF rML rLL uLL uML uOF sq stn pn) as X.
  cbv zeta in X. fold eLL eOF eML cOF in X.
  change (nth (Z.to_nat (fe_sym eML)) ML_bits_tab 0) with xML in X.
  change (nth (Z.to_nat (fe_sym eLL)) LL_bits_tab 0) with xLL in X.
  change (nth (Z.to_nat (fe_sym eML)) ML_base_tab 0) with bML in X.
  change (nth (Z.to_nat (fe_sym eLL)) LL_base_tab 0) with bLL in X.
  replace (cOF + xML + xLL) with (xLL + xML + cOF) in X by lia.
  fold lo2 in X.
  assert (Hpk: forall p nb, 0 <= nb <= 32 -> nb <= p -> bs_peek (bs_value s) p nb = bs_peek_s s p nb)
    by (intros; symmetry; apply bs_peek_s_eq; auto).
  specialize (X Hlo0 Hlo8 Hposlo Hrdy ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HrOF0).
  specialize (X ltac:(intros Hc Hl; rewrite <- Hpk by lia; apply HrOF; auto) HrML0).
  specialize (X ltac:(intros Hc Hl; rewrite <- Hpk by lia; apply HrML; auto) HrLL0).
  specialize (X ltac:(intros Hc Hl; rewrite <- Hpk by lia; apply HrLL; auto)).
  specialize (X ltac:(intros Hl Hw; destruct (HuLL Hl) as [_ Hu]; rewrite <- Hpk by lia; apply Hu; auto)).
  specialize (X ltac:(intros Hl Hw; destruct (HuML Hl) as [_ Hu]; rewrite <- Hpk by lia; apply Hu; auto)).
  specialize (X ltac:(intros Hl Hw; destruct (HuOF Hl) as [_ Hu]; rewrite <- Hpk by lia; apply Hu; auto)).
  destruct (X Hone) as (E1 & E2 & E3 & E4 & E5).
  split; [symmetry; exact E1|]. split; [symmetry; exact E2|]. split; [symmetry; exact E3|]. split; [rewrite E4; reflexivity|].
  intros Hl; subst last. destruct (E5 eq_refl) as [-> Hr]. split; [reflexivity|exact Hr].
Qed.

(* The overflow regime of one step: the model's step fails only when one of its reads goes below the start
   of the stream (Block.rd); the C reads the same numbers of bits (all nonnegative), so its final position,
   the sum of all the counts below pos, is negative too. *)
Lemma dseq_none_neg (tLL tOF tML: fse_table) (s: list Z) (last: bool) (sLL sOF sML pos: Z) :
  let eLL := fse_cell tLL sLL in let eOF := fse_cell tOF sOF in let eML := fse_cell tML sML in
  let ofB := fe_sym eOF in
  let mlB := nth (Z.to_nat (fe_sym eML)) ML_bits_tab 0 in
  let llB := nth (Z.to_nat (fe_sym eLL)) LL_bits_tab 0 in
  let p3 := pos - ofB - mlB - llB in
  let p6 := p3 - fe_nb eLL - fe_nb eML - fe_nb eOF in
  0 <= ofB -> 0 <= fe_nb eLL -> 0 <= fe_nb eML -> 0 <= fe_nb eOF ->
  dseq_one tLL tOF tML s last sLL sOF sML pos = None ->
  (if last then p3 else p6) < 0.
Proof.
  cbv zeta. intros HofB HnLL HnML HnOF Hone.
  pose proof (dce_ml_bits (Z.to_nat (fe_sym (fse_cell tML sML)))) as HmlB.
  pose proof (dce_ll_bits (Z.to_nat (fe_sym (fse_cell tLL sLL)))) as HllB.
  unfold dseq_one, rd in Hone; cbv zeta in Hone.
  set (ofB := fe_sym (fse_cell tOF sOF)) in *.
  set (mlB := nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0) in *.
  set (llB := nth (Z.to_nat (fe_sym (fse_cell tLL sLL))) LL_bits_tab 0) in *.
  set (nLL := fe_nb (fse_cell tLL sLL)) in *.
  set (nML := fe_nb (fse_cell tML sML)) in *.
  set (nOF := fe_nb (fse_cell tOF sOF)) in *.
  destruct (pos - ofB <? 0) eqn:E1; [apply Z.ltb_lt in E1; destruct last; lia|]. apply Z.ltb_ge in E1.
  destruct (pos - ofB - mlB <? 0) eqn:E2; [apply Z.ltb_lt in E2; destruct last; lia|]. apply Z.ltb_ge in E2.
  destruct (pos - ofB - mlB - llB <? 0) eqn:E3; [apply Z.ltb_lt in E3; destruct last; lia|].
  apply Z.ltb_ge in E3.
  destruct last; [discriminate|].
  destruct (pos - ofB - mlB - llB - nLL <? 0) eqn:E4; [apply Z.ltb_lt in E4; lia|]. apply Z.ltb_ge in E4.
  destruct (pos - ofB - mlB - llB - nLL - nML <? 0) eqn:E5; [apply Z.ltb_lt in E5; lia|].
  apply Z.ltb_ge in E5.
  destruct (pos - ofB - mlB - llB - nLL - nML - nOF <? 0) eqn:E6; [apply Z.ltb_lt in E6; lia|].
  discriminate.
Qed.

(* dseq_none_neg with the cells' bounds from the tables' invariants, in the counts of dec_post_ok *)
Lemma dec_none_c (tLL tOF tML: fse_table) (s: list Z) (last: bool) (sLL sOF sML pos: Z) :
  fse_ok KLL tLL -> fse_ok KOF tOF -> fse_ok KML tML -> states_ok (tLL, tOF, tML) (sLL, sOF, sML) ->
  dseq_one tLL tOF tML s last sLL sOF sML pos = None ->
  (if last then pos - fe_sym (fse_cell tOF sOF) - sk_bits KML (fe_sym (fse_cell tML sML))
                - sk_bits KLL (fe_sym (fse_cell tLL sLL))
   else pos - fe_sym (fse_cell tOF sOF) - sk_bits KML (fe_sym (fse_cell tML sML))
        - sk_bits KLL (fe_sym (fse_cell tLL sLL)) - fe_nb (fse_cell tLL sLL) - fe_nb (fse_cell tML sML)
        - fe_nb (fse_cell tOF sOF)) < 0.
Proof.
  intros HokLL HokOF HokML Hst Hone.
  destruct Hst as (HsLL & HsOF & HsML).
  destruct HokLL as (HlogLL & HzLL & HfLL).
  destruct HokOF as (HlogOF & HzOF & HfOF).
  destruct HokML as (HlogML & HzML & HfML).
  pose proof (cell_forall _ _ sLL HfLL ltac:(lia)) as CLL. cbv beta in CLL.
  pose proof (cell_forall _ _ sOF HfOF ltac:(lia)) as COF. cbv beta in COF.
  pose proof (cell_forall _ _ sML HfML ltac:(lia)) as CML. cbv beta in CML.
  destruct CLL as (_ & CnLL & _). destruct COF as (CsOF & CnOF & _). destruct CML as (_ & CnML & _).
  exact (dseq_none_neg tLL tOF tML s last sLL sOF sML pos ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hone).
Qed.

(* dec_post_ok with the overflow regime (dseq_none_neg) *)
Lemma dec_post_ok_x (tLL tOF tML: fse_table) (s: list Z) (last: bool) (sLL sOF sML pos lo: Z)
    (rOF rML rLL uLL uML uOF: Z) :
  let eLL := fse_cell tLL sLL in let eOF := fse_cell tOF sOF in let eML := fse_cell tML sML in
  let cOF := fe_sym eOF in
  let xML := sk_bits KML (fe_sym eML) in let xLL := sk_bits KLL (fe_sym eLL) in
  let bML := sk_base KML (fe_sym eML) in let bLL := sk_base KLL (fe_sym eLL) in
  let p1 := pos - cOF in let p2 := p1 - xML in
  let lo2 := if 31 <=? xLL + xML + cOF then snd (bs_reload p2 lo) else lo in
  let p3 := p2 - xLL in
  let p4 := p3 - fe_nb eLL in let p5 := p4 - fe_nb eML in let p6 := p5 - fe_nb eOF in
  let st' := if last then (sLL, sOF, sML) else (fe_base eLL + uLL, fe_base eOF + uOF, fe_base eML + uML) in
  let pos' := if last then p3 else p6 in
  let lo' := if last then lo2 else snd (bs_reload p6 lo2) in
  let ll := bLL + rLL in let ml := bML + rML in let ov := 2 ^ cOF + rOF in
  bit_inv s pos lo -> bcons pos lo + DSEQ_BITS <= Int.max_unsigned ->
  fse_ok KLL tLL -> fse_ok KOF tOF -> fse_ok KML tML -> states_ok (tLL, tOF, tML) (sLL, sOF, sML) ->
  0 <= rOF < 2 ^ cOF -> (cOF = 0 -> rOF = 0) ->
  (0 < cOF -> lo <= p1 \/ (lo = 0 /\ 0 < pos) -> rOF = bs_peek (bs_value s) pos cOF) ->
  0 <= rML < 2 ^ xML -> (xML = 0 -> rML = 0) ->
  (0 < xML -> lo <= p2 \/ (lo = 0 /\ 0 < p1) -> rML = bs_peek (bs_value s) p1 xML) ->
  0 <= rLL < 2 ^ xLL -> (xLL = 0 -> rLL = 0) ->
  (0 < xLL -> lo2 <= p3 \/ (lo2 = 0 /\ 0 < p2) -> rLL = bs_peek (bs_value s) p2 xLL) ->
  (last = false -> 0 <= uLL < 2 ^ fe_nb eLL /\ (lo2 <= p4 -> uLL = bs_peek (bs_value s) p3 (fe_nb eLL))) ->
  (last = false -> 0 <= uML < 2 ^ fe_nb eML /\ (lo2 <= p5 -> uML = bs_peek (bs_value s) p4 (fe_nb eML))) ->
  (last = false -> 0 <= uOF < 2 ^ fe_nb eOF /\ (lo2 <= p6 -> uOF = bs_peek (bs_value s) p5 (fe_nb eOF))) ->
  (ll =? 0) = (bLL =? 0) /\
  0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= ov < 2 ^ 32 /\
  states_ok (tLL, tOF, tML) st' /\ pos - DSEQ_BITS <= pos' <= pos /\ 0 <= lo' <= lo /\
  (last = true -> st' = (sLL, sOF, sML)) /\
  (bs_ready pos lo ->
   forall sq stn pn,
     dseq_one tLL tOF tML s last sLL sOF sML pos = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     (last = false -> st' = stn /\ bs_ready pos' lo')) /\
  (dseq_one tLL tOF tML s last sLL sOF sML pos = None -> pos' < 0).
Proof.
  cbv zeta.
  intros Hinv Hbc HokLL HokOF HokML Hst HrOFb HrOF0 HrOF HrMLb HrML0 HrML HrLLb HrLL0 HrLL HuLL HuML HuOF.
  destruct (dec_post_ok tLL tOF tML s last sLL sOF sML pos lo rOF rML rLL uLL uML uOF
      Hinv Hbc HokLL HokOF HokML Hst HrOFb HrOF0 HrOF HrMLb HrML0 HrML HrLLb HrLL0 HrLL HuLL HuML HuOF)
    as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  refine (conj A0 (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 _))))))))).
  exact (dec_none_c tLL tOF tML s last sLL sOF sML pos HokLL HokOF HokML Hst).
Qed.

(* an if on a constant 0 condition (MEM_32bits()): only the else branch *)
Ltac dead_if := apply semax_if_seq; forward_if;
  [exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end | ].

(* temp -= !temp on size_t *)
Lemma tmz (x: int64) :
  Int64.sub x (Int64.repr (Int.signed (Int.repr (Z.b2z (negb (negb (Int64.eq x Int64.zero))))))) =
  if Int64.eq x Int64.zero then Int64.repr (-1) else x.
Proof.
  destruct (Int64.eq x Int64.zero) eqn:E.
  - apply Int64.same_if_eq in E. subst. reflexivity.
  - change (Int64.repr (Int.signed (Int.repr (Z.b2z (negb (negb false)))))) with Int64.zero.
    apply Int64.sub_zero_l.
Qed.

Lemma rep_nz (r: Z) : 1 <= r <= SIZE_MAX -> Int64.eq (Int64.repr r) Int64.zero = false.
Proof.
  intros H. apply Int64.eq_false. intro E. apply (f_equal Int64.unsigned) in E.
  rewrite Int64.unsigned_repr in E by (unfold SIZE_MAX in H; rep_lia).
  rewrite Int64.unsigned_zero in E. lia.
Qed.

Lemma tmz_r1 (r1: Z) : 1 <= r1 <= SIZE_MAX ->
  (if Int64.eq (Int64.sub (Int64.repr r1) (Int64.repr (Int.signed (Int.repr 1)))) Int64.zero
   then Int64.repr (-1) else Int64.sub (Int64.repr r1) (Int64.repr (Int.signed (Int.repr 1)))) =
  Int64.repr (if (r1 - 1) mod 2 ^ 64 =? 0 then SIZE_MAX else (r1 - 1) mod 2 ^ 64).
Proof.
  intros H. unfold SIZE_MAX in *. change (Int.signed (Int.repr 1)) with 1.
  assert (E: Int64.sub (Int64.repr r1) (Int64.repr 1) = Int64.repr (r1 - 1)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
  rewrite E. rewrite Z.mod_small by lia.
  destruct (Z.eq_dec r1 1) as [->|N].
  - simpl. apply Int64.eqm_samerepr. exists (-1). reflexivity.
  - rewrite rep_nz by (unfold SIZE_MAX; lia). replace (r1 - 1 =? 0) with false by lia. reflexivity.
Qed.

Lemma off3 (a b c: Z) : 0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= c <= 1 ->
  Int64.add (Int64.repr (Int.unsigned (Int.add (Int.repr a) (Int.repr b)))) (Int64.repr c) = Int64.repr (a + b + c).
Proof.
  intros. rewrite Int.add_unsigned, !(Int.unsigned_repr a), (Int.unsigned_repr b), Int.unsigned_repr by rep_lia.
  rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma tmz_nz (r: Z) : 1 <= r <= SIZE_MAX ->
  Int64.sub (Int64.repr r) (Int64.repr (Int.signed (Int.repr (Z.b2z (negb (negb (Int64.eq (Int64.repr r) Int64.zero))))))) =
  Int64.repr r.
Proof. intros H. rewrite tmz, rep_nz by exact H. reflexivity. Qed.

Ltac dead_br := exfalso; first
  [ match goal with H: Int64.eq _ _ = true |- _ => vm_compute in H; discriminate H end
  | match goal with H: ?a <> ?a |- _ => apply H; reflexivity end
  | match goal with H: Int64.eq _ _ = false |- _ => vm_compute in H; discriminate H end ].
(* an if on a concrete condition: both branches, the dead one closed *)
Ltac cif := first [apply semax_if_seq | apply -> seq_assoc; apply semax_if_seq]; forward_if; try solve [dead_br].

(* an equation entailer! does not substitute *)
Definition dec_eq {A: Type} (a b: A) : Prop := a = b.
Ltac hide_eq H := match type of H with @eq ?T ?a ?b => change (@dec_eq T a b) in H end.

(* rejoin a table split by seqarr_split, the cell given by its value *)
Lemma seqtab_rejoin (sh: share) (k: seqkind) (t: fse_table) (fm: Z) (dt: val) (i: Z)
    (c: val * (val * (val * val))) :
  fse_ok k t -> 0 <= fm <= Int.max_unsigned -> 0 <= i < 2 ^ ft_log t ->
  field_compatible (tarray t_seqSymbol (2 ^ ft_log t)) [] (offset_val 8 dt) ->
  c = seqcell k (fse_cell t i) ->
  data_at sh t_seqhdr (Vint (Int.repr fm), Vint (Int.repr (ft_log t))) dt *
  data_at sh (tarray t_seqSymbol i) (sublist 0 i (map (seqcell k) (ft_cells t))) (offset_val 8 dt) *
  data_at sh t_seqSymbol c (offset_val (8 * i) (offset_val 8 dt)) *
  data_at sh (tarray t_seqSymbol (2 ^ ft_log t - (i + 1)))
    (sublist (i + 1) (2 ^ ft_log t) (map (seqcell k) (ft_cells t))) (offset_val (8 * (i + 1)) (offset_val 8 dt))
  |-- seqtab_at_fm sh k t fm dt.
Proof.
  intros Hok Hfm Hi FC ->. unfold seqtab_at_fm.
  assert (Hz: Zlength (ft_cells t) = 2 ^ ft_log t) by (destruct Hok as (_ & H & _); exact H).
  rewrite (seqarr_split sh (2 ^ ft_log t) i (map (seqcell k) (ft_cells t))) by (rewrite ?Zlength_map; auto).
  rewrite seqcell_Znth by lia. entailer!.
Qed.

Lemma fse_field_LL (sh: share) (v: val * val) (p: val) :
  data_at sh t_fsestate v (field_address t_seqstate (DOT _stateLL) p) |-- field_at sh t_seqstate (DOT _stateLL) v p.
Proof. rewrite field_at_data_at. apply derives_refl. Qed.
Lemma fse_field_ML (sh: share) (v: val * val) (p: val) :
  data_at sh t_fsestate v (field_address t_seqstate (DOT _stateML) p) |-- field_at sh t_seqstate (DOT _stateML) v p.
Proof. rewrite field_at_data_at. apply derives_refl. Qed.
Lemma fse_field_OF (sh: share) (v: val * val) (p: val) :
  data_at sh t_fsestate v (field_address t_seqstate (DOT _stateOffb) p) |-- field_at sh t_seqstate (DOT _stateOffb) v p.
Proof. rewrite field_at_data_at. apply derives_refl. Qed.

(* the offset value ov = 2^cOF + bits of ZSTD_decodeSequence is in [1, 2^32) (proved apart: lia in the
   body's context is slow) *)
Lemma ov_rng (c r: Z) : 0 <= c <= 31 -> 0 <= r < 2 ^ c -> (1 <= 2 ^ c + r < 2 ^ 32)%Z.
Proof.
  intros Hc Hr.
  assert (1 <= 2 ^ c)%Z by (change 1%Z with (2 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
  assert (2 ^ c <= 2 ^ 31)%Z by (apply Z.pow_le_mono_r; lia).
  assert (E31: (2 ^ 31 = 2147483648)%Z) by reflexivity. assert (E32: (2 ^ 32 = 4294967296)%Z) by reflexivity. lia.
Qed.

Lemma body_ZSTD_decodeSequence :
  semax_body Vprog DEC_G f_ZSTD_decodeSequence ZSTD_decodeSequence_spec.
Proof.
  start_function.
  destruct st as [[sLL sOF] sML]; destruct t as [[tLL tOF] tML]; destruct tp as [[pLL pOF] pML];
  destruct sht as [[shLL shOF] shML]; destruct fm as [[fLL fOF] fML]; destruct rep as [[r1 r2] r3].
  unfold seqstate_at, seqtabs_at, seqtab_at_fm. Intros.
  destruct H1 as (HsLL & HsOF & HsML).
  destruct H7 as (HlLL & HzLL & HfLL). destruct H9 as (HlOF & HzOF & HfOF). destruct H5 as (HlML & HzML & HfML).
  assert_PROP (field_compatible (tarray t_seqSymbol (2 ^ ft_log tLL)) [] (offset_val 8 pLL)) as FCLL by entailer!.
  assert_PROP (field_compatible (tarray t_seqSymbol (2 ^ ft_log tOF)) [] (offset_val 8 pOF)) as FCOF by entailer!.
  assert_PROP (field_compatible (tarray t_seqSymbol (2 ^ ft_log tML)) [] (offset_val 8 pML)) as FCML by entailer!.
  rewrite (seqarr_split shLL (2 ^ ft_log tLL) sLL) by (rewrite ?Zlength_map; auto).
  rewrite (seqarr_split shOF (2 ^ ft_log tOF) sOF) by (rewrite ?Zlength_map; auto).
  rewrite (seqarr_split shML (2 ^ ft_log tML) sML) by (rewrite ?Zlength_map; auto).
  rewrite !seqcell_Znth by lia. Intros.
  assert_PROP (field_compatible t_seqstate (DOT _prevOffset) p) as FCp by entailer!.
  assert (FCd: field_compatible t_seqstate (DOT _DStream) p).
  { clear - FCp. destruct FCp as (? & ? & ? & ? & ?). repeat split; auto. all: simpl; auto. all: left; reflexivity. }
  freeze [7;8;10;11;12;14;15;16;18] FT.
  unfold fse_val.
  pose proof (cell_forall tLL _ sLL HfLL ltac:(lia)) as CLL; cbv beta in CLL.
  pose proof (cell_forall tOF _ sOF HfOF ltac:(lia)) as COF; cbv beta in COF.
  pose proof (cell_forall tML _ sML HfML ltac:(lia)) as CML; cbv beta in CML.
  remember (fse_cell tLL sLL) as eLL eqn:EeLL. remember (fse_cell tOF sOF) as eOF eqn:EeOF.
  remember (fse_cell tML sML) as eML eqn:EeML.
  assert (Hlog: ft_log tLL <= 9 /\ ft_log tOF <= 8 /\ ft_log tML <= 9) by (cbv [sk_maxlog LLFSELog OffFSELog MLFSELog] in *; lia).
  assert (Hp: isptr pLL /\ isptr pOF /\ isptr pML).
  { destruct FCLL as [A _]; destruct FCOF as [B _]; destruct FCML as [C _].
    destruct pLL, pOF, pML; try contradiction; simpl; auto. }
  assert (Hb512: 2 ^ ft_log tLL <= 512 /\ 2 ^ ft_log tOF <= 256 /\ 2 ^ ft_log tML <= 512).
  { split; [|split]; [change 512 with (2 ^ 9) | change 256 with (2 ^ 8) | change 512 with (2 ^ 9)];
    apply Z.pow_le_mono_r; lia. }
  unfold seqcell.
  forward. forward. forward. rewrite add_cell_ptr by (auto; rep_lia).
  forward. forward. forward. rewrite add_cell_ptr by (auto; rep_lia).
  forward. forward. forward. rewrite add_cell_ptr by (auto; rep_lia).
  destruct H as (RLL & ROF & RML).
  destruct CLL as (HcLL & HnLL & HbLL0 & HbLL1). destruct COF as (HcOF & HnOF & HbOF0 & HbOF1).
  destruct CML as (HcML & HnML & HbML0 & HbML1).
  cbv [sk_max MaxLL MaxOff MaxML] in HcLL, HcOF, HcML.
  destruct (ll_tab_facts (fe_sym eLL) HcLL) as (HxLL & HbLL & HvLL & HzLL0).
  destruct (ml_tab_facts (fe_sym eML) HcML) as (HxML & HbML & HvML).
  destruct (of_tab_facts (fe_sym eOF) HcOF) as (HxOF & HbOF). rewrite HxOF.
  remember (sk_bits KLL (fe_sym eLL)) as xLL eqn:ExLL. remember (sk_base KLL (fe_sym eLL)) as bLL eqn:EbLL.
  remember (sk_bits KML (fe_sym eML)) as xML eqn:ExML. remember (sk_base KML (fe_sym eML)) as bML eqn:EbML.
  remember (sk_base KOF (fe_sym eOF)) as bOF eqn:EbOF. remember (fe_sym eOF) as cOF eqn:EcOF.
  hide_eq EeLL. hide_eq EeOF. hide_eq EeML. hide_eq ExLL. hide_eq EbLL. hide_eq ExML. hide_eq EbML.
  hide_eq EbOF. hide_eq EcOF.
  rename H6 into HfmML, H8 into HfmLL, H10 into HfmOF.
  assert (H2xLL: 1 <= 2 ^ xLL) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (H2xML: 1 <= 2 ^ xML) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  unfold LL_VMAX, ML_VMAX in HvLL, HvML.
  change (data_at_ Tsh (Tstruct ___gp_seq_t noattr) v_seq) with (data_at Tsh t_seq (Vundef, (Vundef, Vundef)) v_seq).
  forward. forward. forward. forward. forward.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  forward. { entailer!. rep_lia. } forward.
  forward.
  rewrite !zext8_repr by lia. rewrite !add_repr. rewrite zext8_repr by lia.
  rewrite !Int.unsigned_repr by rep_lia.
  assert_PROP (bit_inv s pos lo) as BI0.
  { go_lower. sep_apply (BIT_rep_inv sh gv s start pos lo (field_address t_seqstate (DOT _DStream) p)). entailer!. }
  freeze [0;1;2;4;5;6;9;10;11] FR1.
  forward_if (EX rOF: Z,
    PROP (0 <= rOF < 2 ^ cOF; cOF = 0 -> rOF = 0;
          0 < cOF -> lo <= pos - cOF \/ (lo = 0 /\ 0 < pos) -> rOF = bs_peek (bs_value s) pos cOF)
    LOCAL (temp _offset (Vlong (Int64.repr (fst (c_offset (r1, r2, r3) bLL (2 ^ cOF + rOF)))));
           temp _totalBits (Vint (Int.repr (xLL + xML + cOF)));
           temp _mlBits (Vint (Int.repr xML)); temp _llBits (Vint (Int.repr xLL));
           temp _ofDInfo (offset_val (8 * sOF) (offset_val 8 pOF));
           temp _mlDInfo (offset_val (8 * sML) (offset_val 8 pML));
           temp _llDInfo (offset_val (8 * sLL) (offset_val 8 pLL));
           lvar _seq (Tstruct ___gp_seq_t noattr) v_seq; gvars gv; temp _gp_seq q; temp _seqState p;
           temp _isLastSeq (Vint (Int.repr (if last then 1 else 0))))
    SEP (FRZL FR1;
         BIT_DStream_rep sh gv s start (pos - cOF) lo (field_address t_seqstate (DOT _DStream) p);
         field_at sh t_seqstate (DOT _prevOffset) (rep64_vals (snd (c_offset (r1, r2, r3) bLL (2 ^ cOF + rOF)))) p;
         data_at shLL t_seqSymbol
           (Vint (Int.repr (fe_base eLL)), (Vint (Int.repr xLL), (Vint (Int.repr (fe_nb eLL)), Vint (Int.repr bLL))))
           (offset_val (8 * sLL) (offset_val 8 pLL))))%assert.
  { (* ofBits > 1 *)
    forward_call tt. dead_if. forward. dead_if. forward. dead_if.
    unfold bcons, DSEQ_BITS in H3.
    forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos, lo, cOF).
    { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    Intros rOF.
    forward. forward_call tt. dead_if.
    unfold rep64_vals.
    forward. forward. forward. forward. forward.
    Exists rOF.
    assert (Hc4: 4 <= 2 ^ cOF) by (change 4 with (2^2); apply Z.pow_le_mono_r; lia).
    assert (Hc31: 2 ^ cOF <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    assert (HbOF': bOF = 2 ^ cOF - 3) by (rewrite HbOF; destruct (cOF <? 2) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]).
    clear HbOF. rewrite c_offset_big by lia. cbn [fst snd].
    entailer!.
    all: try rewrite Int.unsigned_repr by rep_lia.
    { repeat split; intros; try lia; auto. f_equal. f_equal. lia. }
    unfold rep64_vals. replace (2 ^ cOF + rOF - 3) with (2 ^ cOF - 3 + rOF) by lia. apply derives_refl'. f_equal. }
  { (* ofBits <= 1 *)
    forward. forward.
    unfold rep64_vals. destruct H2 as (Hr1 & Hr2 & Hr3).
    destruct (zeq bLL 0) as [EL0|NL0]; cbn [Z.b2z proj_sumbool].
    - forward_if.
      + (* ofBits = 0, ll0 = 1 *)
        assert (cOF = 0) by lia. subst cOF.
        forward.
        assert (Enot: Z.b2z (negb (negb (Int.eq (Int.repr 1) Int.zero))) = 0) by reflexivity.
        forward. rewrite Enot. forward. forward.
        Exists 0. assert (C1: c_offset (r1,r2,r3) bLL (2^0+0) = (r2,(r2,r1,r3))) by (rewrite EL0; reflexivity).
        rewrite C1. cbn [fst snd]. rewrite Z.sub_0_r. entailer!.
      + (* ofBits = 1, ll0 = 1 *)
        assert (cOF = 1) by lia. subst cOF.
        assert (HbOF1': bOF = 1) by (rewrite HbOF; reflexivity). clear HbOF. subst bOF.
        unfold bcons, DSEQ_BITS in H3.
        forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos, lo, 1).
        { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
        Intros rOF. forward.
        assert (rOF = 0 \/ rOF = 1) as [-> | ->] by (simpl in *; lia).
        * rewrite (off3 1 1 0) by lia. cif; try discriminate. forward. forward. forward. forward.
          rewrite tmz_nz by (unfold SIZE_MAX in *; lia).
          cif; try discriminate. forward. forward. forward. forward. forward. forward. forward.
          Exists 0. assert (C: c_offset (r1,r2,r3) bLL (2^1+0) = (r3,(r3,r1,r2))) by (unfold c_offset; rewrite EL0; reflexivity).
          rewrite C. cbn [fst snd]. entailer!.
        * rewrite (off3 1 1 1) by lia. cif; try discriminate. forward. forward. forward. forward.
          rewrite tmz, tmz_r1 by (unfold SIZE_MAX in *; lia).
          cif; try discriminate. forward. forward. forward. forward. forward. forward. forward.
          Exists 1.
          assert (C: c_offset (r1,r2,r3) bLL (2^1+1) =
            ((if (r1 - 1) mod 2 ^ 64 =? 0 then SIZE_MAX else (r1 - 1) mod 2 ^ 64),
             ((if (r1 - 1) mod 2 ^ 64 =? 0 then SIZE_MAX else (r1 - 1) mod 2 ^ 64), r1, r2)))
            by (unfold c_offset; rewrite EL0; reflexivity).
          rewrite C. cbn [fst snd]. entailer!.
    - forward_if.
      + (* ofBits = 0, ll0 = 0 *)
        assert (cOF = 0) by lia. subst cOF.
        forward.
        assert (Enot: Z.b2z (negb (negb (Int.eq (Int.repr 0) Int.zero))) = 1) by reflexivity.
        forward. rewrite Enot. forward. forward.
        Exists 0.
        assert (C1: c_offset (r1,r2,r3) bLL (2^0+0) = (r1,(r1,r2,r3)))
          by (unfold c_offset; rewrite (proj2 (Z.eqb_neq bLL 0) NL0); reflexivity).
        rewrite C1. cbn [fst snd]. rewrite Z.sub_0_r. entailer!.
      + (* ofBits = 1, ll0 = 0 *)
        assert (cOF = 1) by lia. subst cOF.
        assert (HbOF1': bOF = 1) by (rewrite HbOF; reflexivity). clear HbOF. subst bOF.
        unfold bcons, DSEQ_BITS in H3.
        forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos, lo, 1).
        { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
        Intros rOF. forward.
        assert (rOF = 0 \/ rOF = 1) as [-> | ->] by (simpl in *; lia).
        * rewrite (off3 1 0 0) by lia. cif; try discriminate. forward. forward. forward. forward.
          rewrite tmz_nz by (unfold SIZE_MAX in *; lia).
          cif; try discriminate. forward. forward. forward. forward. forward.
          Exists 0.
          assert (C: c_offset (r1,r2,r3) bLL (2^1+0) = (r2,(r2,r1,r3)))
            by (unfold c_offset; rewrite (proj2 (Z.eqb_neq bLL 0) NL0); reflexivity).
          rewrite C. cbn [fst snd]. entailer!.
        * rewrite (off3 1 0 1) by lia. cif; try discriminate. forward. forward. forward. forward.
          rewrite tmz_nz by (unfold SIZE_MAX in *; lia).
          cif; try discriminate. forward. forward. forward. forward. forward. forward. forward.
          Exists 1.
          assert (C: c_offset (r1,r2,r3) bLL (2^1+1) = (r3,(r3,r1,r2)))
            by (unfold c_offset; rewrite (proj2 (Z.eqb_neq bLL 0) NL0); reflexivity).
          rewrite C. cbn [fst snd]. entailer!. }
  Intros rOF.
  assert (Hov: 1 <= 2 ^ cOF + rOF < 2 ^ 32) by (apply ov_rng; [lia | assumption]).
  remember (c_offset (r1, r2, r3) bLL (2 ^ cOF + rOF)) as CO eqn:ECO. hide_eq ECO.
  thaw FR1.
  forward.
  freeze [0;2;3;4;5;6;7;10;11] FR2.
  destruct BI0 as (Bb & Bl & Blo & Bm8 & Bk & Bpos & Bc).
  unfold bcons, DSEQ_BITS in H3.
  forward_if (EX rML: Z,
    PROP (0 <= rML < 2 ^ xML; xML = 0 -> rML = 0;
          0 < xML -> lo <= pos - cOF - xML \/ (lo = 0 /\ 0 < pos - cOF) -> rML = bs_peek (bs_value s) (pos - cOF) xML)
    LOCAL (temp _totalBits (Vint (Int.repr (xLL + xML + cOF)));
           temp _llBits (Vint (Int.repr xLL));
           temp _ofDInfo (offset_val (8 * sOF) (offset_val 8 pOF));
           temp _mlDInfo (offset_val (8 * sML) (offset_val 8 pML));
           temp _llDInfo (offset_val (8 * sLL) (offset_val 8 pLL));
           lvar _seq (Tstruct ___gp_seq_t noattr) v_seq; gvars gv; temp _gp_seq q; temp _seqState p;
           temp _isLastSeq (Vint (Int.repr (if last then 1 else 0))))
    SEP (FRZL FR2;
         data_at Tsh t_seq (Vlong (Int64.repr bLL), (Vlong (Int64.repr (bML + rML)), Vlong (Int64.repr (fst CO)))) v_seq;
         bit_src shs bp buf;
         BIT_DStream_rep sh gv s start (pos - cOF - xML) lo (field_address t_seqstate (DOT _DStream) p)))%assert.
  { forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF, lo, xML).
    { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    Intros rML. forward. forward. Exists rML. entailer!. }
  { forward. Exists 0. assert (Hx0: xML = 0) by lia. rewrite Hx0, Z.sub_0_r, Z.add_0_r. entailer!. apply derives_refl. }
  Intros rML.
  forward_call tt. cif; try discriminate. forward. cif; try discriminate.
  forward_call tt. cif; try discriminate. forward.
  forward_if (PROP ()
    LOCAL (temp _llBits (Vint (Int.repr xLL));
           temp _ofDInfo (offset_val (8 * sOF) (offset_val 8 pOF));
           temp _mlDInfo (offset_val (8 * sML) (offset_val 8 pML));
           temp _llDInfo (offset_val (8 * sLL) (offset_val 8 pLL));
           lvar _seq (Tstruct ___gp_seq_t noattr) v_seq; gvars gv; temp _gp_seq q; temp _seqState p;
           temp _isLastSeq (Vint (Int.repr (if last then 1 else 0))))
    SEP (FRZL FR2;
         data_at Tsh t_seq (Vlong (Int64.repr bLL), (Vlong (Int64.repr (bML + rML)), Vlong (Int64.repr (fst CO)))) v_seq;
         bit_src shs bp buf;
         BIT_DStream_rep sh gv s start (pos - cOF - xML)
           (if 31 <=? xLL + xML + cOF then snd (bs_reload (pos - cOF - xML) lo) else lo)
           (field_address t_seqstate (DOT _DStream) p))).
  { forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF - xML, lo, shs, bp, buf, off).
    { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    assert (Hge: 31 <= xLL + xML + cOF).
    { match goal with H: proj_sumbool (zlt _ _) = false |- _ => destruct (zlt _ _) in H; [discriminate | lia] end. }
    rewrite (proj2 (Z.leb_le _ _) Hge). entailer!. }
  { forward.
    assert (Hlt: xLL + xML + cOF < 31).
    { match goal with H: proj_sumbool (zlt _ _) = true |- _ => destruct (zlt _ _) in H; [lia | discriminate] end. }
    rewrite (proj2 (Z.leb_gt _ _) Hlt). entailer!. }
  assert (Hlo2: 0 <= (if 31 <=? xLL + xML + cOF then snd (bs_reload (pos - cOF - xML) lo) else lo) <= lo).
  { destruct (31 <=? xLL + xML + cOF); [apply bs_reload_lo; lia | lia]. }
  remember (if 31 <=? xLL + xML + cOF then snd (bs_reload (pos - cOF - xML) lo) else lo) as lo2 eqn:Elo2.
  hide_eq Elo2.
  forward_if (EX rLL: Z,
    PROP (0 <= rLL < 2 ^ xLL; xLL = 0 -> rLL = 0;
          0 < xLL -> lo2 <= pos - cOF - xML - xLL \/ (lo2 = 0 /\ 0 < pos - cOF - xML) ->
            rLL = bs_peek (bs_value s) (pos - cOF - xML) xLL)
    LOCAL (temp _ofDInfo (offset_val (8 * sOF) (offset_val 8 pOF));
           temp _mlDInfo (offset_val (8 * sML) (offset_val 8 pML));
           temp _llDInfo (offset_val (8 * sLL) (offset_val 8 pLL));
           lvar _seq (Tstruct ___gp_seq_t noattr) v_seq; gvars gv; temp _gp_seq q; temp _seqState p;
           temp _isLastSeq (Vint (Int.repr (if last then 1 else 0))))
    SEP (FRZL FR2;
         data_at Tsh t_seq (Vlong (Int64.repr (bLL + rLL)), (Vlong (Int64.repr (bML + rML)), Vlong (Int64.repr (fst CO)))) v_seq;
         bit_src shs bp buf;
         BIT_DStream_rep sh gv s start (pos - cOF - xML - xLL) lo2 (field_address t_seqstate (DOT _DStream) p)))%assert.
  { forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF - xML, lo2, xLL).
    { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    Intros rLL. forward. forward. Exists rLL. entailer!. }
  { forward. Exists 0. assert (Hx0: xLL = 0) by lia. rewrite Hx0, Z.sub_0_r, Z.add_0_r. entailer!. all: try apply derives_refl. }
  Intros rLL.
  forward_call tt. cif; try discriminate.
  apply -> seq_assoc. apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
  thaw FR2.
  assert (Hp2LL: 0 < 2 ^ fe_nb eLL) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2ML: 0 < 2 ^ fe_nb eML) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2OF: 0 < 2 ^ fe_nb eOF) by (apply Z.pow_pos_nonneg; lia).
  (* the seq_t field bounds, before the branches (rep_lia in the not-last branch's larger context stalls) *)
  assert (Bll: 0 <= bLL + rLL <= Int64.max_unsigned) by rep_lia.
  assert (Bml: 0 <= bML + rML <= Int64.max_unsigned) by rep_lia.
  assert (Bof: 0 <= fst CO <= Int64.max_unsigned).
  { destruct (c_offset_ok (r1, r2, r3) bLL (2 ^ cOF + rOF)) as [HCOa _]; [exact H2 | exact Hov |].
    unfold dec_eq in ECO. rewrite <- ECO in HCOa. unfold SIZE_MAX in HCOa. rep_lia. }
  destruct last.
  - cif; try discriminate.
    all: try solve [exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end].
    unfold dec_eq in ECO. destruct (c_offset_ok (r1, r2, r3) bLL (2 ^ cOF + rOF)) as [HCO1 HCO2]; [exact H2 | |].
    { exact Hov. }
    rewrite <- ECO in HCO1, HCO2.
    freeze [0;2;3;4;5;6;7;8;10;11] FR3.
    forward_call (Tsh, v_seq, bLL + rLL, bML + rML, fst CO, shq, q).
    pose proof (dec_post_ok_x tLL tOF tML s true sLL sOF sML pos lo rOF rML rLL 0 0 0) as DP. cbv zeta in DP.
    unfold dec_eq in EeLL, EeOF, EeML, ExLL, EbLL, ExML, EbML, EcOF, Elo2, EbOF.
    rewrite <- EeLL, <- EeOF, <- EeML in DP. rewrite <- EcOF in DP. rewrite <- ExLL, <- ExML, <- EbLL, <- EbML in DP.
    rewrite <- Elo2 in DP.
    edestruct DP as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
    all: try assumption.
    { unfold bit_inv; repeat split; assumption. }
    { exact (conj HlLL (conj HzLL HfLL)). }
    { exact (conj HlOF (conj HzOF HfOF)). }
    { exact (conj HlML (conj HzML HfML)). }
    { exact (conj HsLL (conj HsOF HsML)). }
    all: try (intros; discriminate).
    clear DP.
    thaw FR3. thaw FT.
    sep_apply (seqtab_rejoin shLL KLL tLL fLL pLL sLL
      (Vint (Int.repr (fe_base eLL)), (Vint (Int.repr xLL), (Vint (Int.repr (fe_nb eLL)), Vint (Int.repr bLL))))).
    all: try solve [exact (conj HlLL (conj HzLL HfLL)) | assumption | lia | rewrite <- EeLL; unfold seqcell; rewrite <- ExLL, <- EbLL; reflexivity].

    sep_apply (seqtab_rejoin shOF KOF tOF fOF pOF sOF
      (Vint (Int.repr (fe_base eOF)), (Vint (Int.repr cOF), (Vint (Int.repr (fe_nb eOF)), Vint (Int.repr bOF))))).
    all: try solve [exact (conj HlOF (conj HzOF HfOF)) | assumption | lia | rewrite <- EeOF; unfold seqcell; rewrite <- EcOF, HxOF, <- EbOF; reflexivity].

    sep_apply (seqtab_rejoin shML KML tML fML pML sML
      (Vint (Int.repr (fe_base eML)), (Vint (Int.repr xML), (Vint (Int.repr (fe_nb eML)), Vint (Int.repr bML))))).
    all: try solve [exact (conj HlML (conj HzML HfML)) | assumption | lia | rewrite <- EeML; unfold seqcell; rewrite <- ExML, <- EbML; reflexivity].

    Exists (bLL + rLL) (bML + rML) (2 ^ cOF + rOF) (sLL, sOF, sML) (pos - cOF - xML - xLL) lo2.
    rewrite (c_offset_ll (r1, r2, r3) (bLL + rLL) bLL) by exact D0. rewrite <- ECO.
    unfold seqstate_at, seqtabs_at, fse_val. cbv beta iota.
    entailer!.
  - cif; try discriminate.
    all: try solve [exfalso; match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end].
    rewrite (field_at_data_at sh t_seqstate (DOT _stateLL)), (field_at_data_at sh t_seqstate (DOT _stateML)),
      (field_at_data_at sh t_seqstate (DOT _stateOffb)).
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    assert (FCs: field_compatible t_seqstate (DOT _stateLL) p /\ field_compatible t_seqstate (DOT _stateML) p /\
                 field_compatible t_seqstate (DOT _stateOffb) p).
    { clear - FCp. destruct FCp as (? & ? & ? & ? & ?). repeat split; auto. all: simpl; auto.
      all: unfold in_members; simpl; tauto. }
    destruct FCs as (FCsLL & FCsML & FCsOF).
    assert (Z16: forall x, 0 <= x < 65536 -> Int.zero_ext 16 (Int.repr x) = Int.repr x).
    { intros x Hx. unfold Int.zero_ext. rewrite Int.unsigned_repr by rep_lia. f_equal.
      rewrite Zbits.Zzero_ext_mod by lia. apply Z.mod_small. cbv - [Z.le Z.lt]; lia. }
    forward_call (sh, field_address t_seqstate (DOT _stateLL) p, Vlong (Int64.repr sLL), offset_val 8 pLL, sh,
      field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF - xML - xLL, lo2, fe_base eLL, fe_nb eLL).
    { entailer!. simpl. unfold eval_field. simpl. rewrite !field_compatible_field_address by auto.
      rewrite Z16 by lia. reflexivity. }
    { unfold bcons; lia. }
    Intros uLL.
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    forward_call (sh, field_address t_seqstate (DOT _stateML) p, Vlong (Int64.repr sML), offset_val 8 pML, sh,
      field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF - xML - xLL - fe_nb eLL, lo2,
      fe_base eML, fe_nb eML).
    { entailer!. simpl. unfold eval_field. simpl. rewrite !field_compatible_field_address by auto.
      rewrite Z16 by lia. reflexivity. }
    { unfold bcons; lia. }
    Intros uML.
    forward_call tt. cif; try discriminate.
    forward. { entailer!. rep_lia. }
    forward. { entailer!. rep_lia. }
    forward_call (sh, field_address t_seqstate (DOT _stateOffb) p, Vlong (Int64.repr sOF), offset_val 8 pOF, sh,
      field_address t_seqstate (DOT _DStream) p, gv, s, start, pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML, lo2,
      fe_base eOF, fe_nb eOF).
    { entailer!. simpl. unfold eval_field. simpl. rewrite !field_compatible_field_address by auto.
      rewrite Z16 by lia. reflexivity. }
    { unfold bcons; lia. }
    Intros uOF.
    forward_call (sh, field_address t_seqstate (DOT _DStream) p, gv, s, start,
      pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML - fe_nb eOF, lo2, shs, bp, buf, off).
    { entailer!. simpl. unfold eval_field. simpl. rewrite field_compatible_field_address by auto. reflexivity. }
    unfold dec_eq in ECO. destruct (c_offset_ok (r1, r2, r3) bLL (2 ^ cOF + rOF)) as [HCO1 HCO2]; [exact H2 | |].
    { exact Hov. }
    rewrite <- ECO in HCO1, HCO2.
    freeze [0;1;2;3;4;5;7;8;9;10] FR3.
    forward_call (Tsh, v_seq, bLL + rLL, bML + rML, fst CO, shq, q).
    pose proof (dec_post_ok_x tLL tOF tML s false sLL sOF sML pos lo rOF rML rLL uLL uML uOF) as DP. cbv zeta in DP.
    unfold dec_eq in EeLL, EeOF, EeML, ExLL, EbLL, ExML, EbML, EcOF, Elo2, EbOF.
    rewrite <- EeLL, <- EeOF, <- EeML in DP. rewrite <- EcOF in DP. rewrite <- ExLL, <- ExML, <- EbLL, <- EbML in DP.
    rewrite <- Elo2 in DP.
    edestruct DP as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
    all: try assumption.
    { unfold bit_inv; repeat split; assumption. }
    { exact (conj HlLL (conj HzLL HfLL)). }
    { exact (conj HlOF (conj HzOF HfOF)). }
    { exact (conj HlML (conj HzML HfML)). }
    { exact (conj HsLL (conj HsOF HsML)). }
    all: try (intros _; split; assumption).
    clear DP.
    thaw FR3. thaw FT.
    sep_apply (seqtab_rejoin shLL KLL tLL fLL pLL sLL
      (Vint (Int.repr (fe_base eLL)), (Vint (Int.repr xLL), (Vint (Int.repr (fe_nb eLL)), Vint (Int.repr bLL))))).
    all: try solve [exact (conj HlLL (conj HzLL HfLL)) | assumption | lia | rewrite <- EeLL; unfold seqcell; rewrite <- ExLL, <- EbLL; reflexivity].

    sep_apply (seqtab_rejoin shOF KOF tOF fOF pOF sOF
      (Vint (Int.repr (fe_base eOF)), (Vint (Int.repr cOF), (Vint (Int.repr (fe_nb eOF)), Vint (Int.repr bOF))))).
    all: try solve [exact (conj HlOF (conj HzOF HfOF)) | assumption | lia | rewrite <- EeOF; unfold seqcell; rewrite <- EcOF, HxOF, <- EbOF; reflexivity].

    sep_apply (seqtab_rejoin shML KML tML fML pML sML
      (Vint (Int.repr (fe_base eML)), (Vint (Int.repr xML), (Vint (Int.repr (fe_nb eML)), Vint (Int.repr bML))))).
    all: try solve [exact (conj HlML (conj HzML HfML)) | assumption | lia | rewrite <- EeML; unfold seqcell; rewrite <- ExML, <- EbML; reflexivity].

    sep_apply (fse_field_LL sh (Vlong (Int64.repr (fe_base eLL + uLL)), offset_val 8 pLL) p).
    sep_apply (fse_field_ML sh (Vlong (Int64.repr (fe_base eML + uML)), offset_val 8 pML) p).
    sep_apply (fse_field_OF sh (Vlong (Int64.repr (fe_base eOF + uOF)), offset_val 8 pOF) p).
    Exists (bLL + rLL) (bML + rML) (2 ^ cOF + rOF) (fe_base eLL + uLL, fe_base eOF + uOF, fe_base eML + uML)
      (pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML - fe_nb eOF)
      (snd (bs_reload (pos - cOF - xML - xLL - fe_nb eLL - fe_nb eML - fe_nb eOF) lo2)).
    rewrite (c_offset_ll (r1, r2, r3) (bLL + rLL) bLL) by exact D0. rewrite <- ECO.
    unfold seqstate_at, seqtabs_at, fse_val. cbv beta iota.
    entailer!.
Qed.

Lemma DEC_ok : DEC_obligation.
Proof.
  unfold DEC_obligation, subtree_ok.
  exists DEC_exports. split; [reflexivity | split; [apply incl_refl | ]].
  rewrite <- app_assoc. fold DEC_G.
  repeat constructor.
  - exists f_ZSTD_initFseState. split; [reflexivity | split; [reflexivity | apply body_ZSTD_initFseState]].
  - exists f_ZSTD_updateFseStateWithDInfo.
    split; [reflexivity | split; [reflexivity | apply body_ZSTD_updateFseStateWithDInfo]].
  - exists f_ZSTD_decodeSequence. split; [reflexivity | split; [reflexivity | apply body_ZSTD_decodeSequence]].
Qed.
