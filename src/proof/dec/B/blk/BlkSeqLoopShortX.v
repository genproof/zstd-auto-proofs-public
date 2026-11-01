(* The short loop (ZSTD_decompressSequences_body, literals not split) against the exact block model
   (model/ExBlock.v): the plain-Coq steps of its last clause BlkIface.seqs_exact.  BlkSeqLoopShort's VST
   proof carries the predicates below in its invariants and discharges each step with one lemma here.

   seqs_exact quantifies over the model's region (rb, m), the block body (body at bo) and the literal pointer
   (lr, li, lim, sp) satisfying its hypotheses (xs_hyp); for each choice the model's outcome is xs_X.  The C's
   state (op = d + K, j literals used, its output array c, its repeat offsets crep, its bitstream position
   pos / container lo, its FSE states st) is related to a model state s (xs_rel): op = rb + xop s, the
   literal index li + j, every written cell of the model's region is the array's (dst_rel), the history and
   the literals are written (xh_ok, xl_ok: then the model fails exactly when the C does, BlkSeqXKitD).

   The loop invariant (xs_inv) is a continuation equality: xs_X is what the model computes from the state
   s for the sequences left (xs_cont: x_seq_loop, the end check pos = 0, x_last, x_rep32) -- or the
   bitstream has overflowed (pos < 0: the model failed on a read below the stream's start, the C keeps
   decoding from an overflowed container and its final BIT_endOfDStream check fails) and xs_X = None.

   Steps: xs_init_err / xs_init (BIT_initDStream, the three ZSTD_initFseState), xs_dec_step (one
   ZSTD_decodeSequence), xs_exec_step (one ZSTD_execSequence), xs_end (BIT_endOfDStream, the repeat
   offsets), xs_aft_nb0 (no sequences), xs_epi (the last literals), xs_exact_none / xs_exact_some (the
   clause itself). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Section ShortX.
(* the specification's variables (seqs_spec) and litExtraBuffer's bytes *)
Variables (fs: fstate) (os: option seq_tabs) (rep: Z * Z * Z) (l: litloc) (lits lxb: list Z) (nbSeq: Z)
  (o: outarr) (i: inwin) (h: hctx).

(* the facts of the precondition the steps use *)
Definition xs_ctx : Prop :=
  outarr_ok o /\ inwin_ok i /\ not_split l /\ lits_at l (oa_c o) (oa_d o) (oa_cap o) i lits /\
  0 <= nbSeq /\ (nbSeq > 0 -> os <> None /\ 0 < oa_cap o) /\ seqs_ok os /\ rep_ok rep /\
  (0 < oa_cap o -> layout_ok fs (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h)) /\
  Zlength lxb = LITEXTRA_N /\ bytes_ok lxb /\
  (l = LExtra -> sublist 0 (Zlength lits) lxb = lits).

(* the C's places (offsets in their arrays): oend, the first literal, the literals' array as a source of
   BlkSeqXMem's copies (cl: litExtraBuffer's cells) and as a list *)
Definition xs_oend : Z := match l with LDst lb => lb | _ => oa_d o + oa_cap o end.
Definition xs_li0 : Z := match l with LIn off => off | LExtra => 0 | LDst lb => lb | LSplit lb => lb end.
Definition xs_lsrc : lsrc := match l with LIn _ => LS (iw_c i) | LExtra => LS (zbytes lxb) | _ => LW end.
Definition xs_larr (c: list val) : list val :=
  match l with LIn _ => iw_c i | LExtra => zbytes lxb | _ => c end.

(* the hypotheses of seqs_exact for one choice of the region, the body and the literal pointer *)
Definition xs_hyp (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de: Z) : Prop :=
  hc_region h rb = Some (ps, ds, de) /\ 0 <= rb <= oa_d o /\
  dst_rel (oa_c o) rb m /\
  (forall j, ps <= j < oa_d o - rb \/ ds <= j < de -> nth (Z.to_nat j) m None <> None) /\
  0 <= bo /\ bo + Zlength body <= iw_N i /\ sublist bo (bo + Zlength body) (iw_c i) = zbytes body /\
  litloc_rel l rb bo (Zlength lits) lr li lim sp /\
  0 <= ps /\ 0 <= ds /\ 0 <= li /\
  (lr = R_dst -> forall j, li <= j < lim + WILDCOPY_OVERLENGTH -> nth (Z.to_nat j) m None <> None) /\
  (lr = R_src -> lim + WILDCOPY_OVERLENGTH <= Zlength body).

Definition xs_env (rb: Z) (body: list Z) (ps ds de: Z) : xenv :=
  {| xe_src := body; xe_ps := ps; xe_vs := ps - (de - ds); xe_de := de; xe_oend := seq_oend l rb o |}.

Definition xs_s0 (rb: Z) (m: list (option Z)) (lr: xreg) (li lim: Z) (sp: bool) : xex :=
  {| xmm := {| xm_dst := m; xm_lxb := lxb |}; xop := oa_d o - rb; xlr := lr; xli := li; xlim := lim;
     xsp := sp |}.

(* the model's outcome *)
Definition xs_X (rb: Z) (m: list (option Z)) (body: list Z) (lr: xreg) (li lim: Z) (sp: bool) (ps ds de: Z)
    : option (xmem * Z * (Z * Z * Z)) :=
  x_seq_section (xs_env rb body ps ds de) os rep (iw_s i) nbSeq (xs_s0 rb m lr li lim sp).

(* the model fails on every choice *)
Definition xs_none : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    xs_X rb m body lr li lim sp ps ds de = None.

(* the C's state (K bytes written, j literals used, the output array c) and the model's state s, without
   the history *)
Definition xs_rel (e: xenv) (rb: Z) (lr: xreg) (li lim: Z) (c: list val) (K j: Z) (s: xex) : Prop :=
  xop s = oa_d o + K - rb /\ xlr s = lr /\ xli s = li + j /\ xlim s = lim /\ xsp s = false /\
  xm_lxb (xmm s) = lxb /\ dst_rel c rb (xm_dst (xmm s)) /\ xl_ok e (xmm s) lr (li + j) lim.

(* what the model computes from s with k sequences left (FSE states st, position pos, repeat offsets crep) *)
Definition xs_cont (e: xenv) (t: seq_tabs) (k: nat) (st: Z * Z * Z) (pos: Z) (crep: Z * Z * Z) (s: xex)
    : option (xmem * Z * (Z * Z * Z)) :=
  let '(tLL, tOF, tML) := t in
  match x_seq_loop dseq_one c_offset e tLL tOF tML (iw_s i) k st pos crep s with
  | None => None
  | Some (s', pos', rep') =>
      if negb (pos' =? 0) then None else
      match x_last e s' with Some (m', op') => Some (m', op', x_rep32 rep') | None => None end
  end.

(* the loop invariant after id sequences (tables t; the C's bitstream at (pos, lo), states st, repeat offsets
   crep) *)
Definition xs_inv (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z)
    : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    let e := xs_env rb body ps ds de in
    (exists s, xs_rel e rb lr li lim c K j s /\ xh_ok e (xmm s) (xop s) /\
       (id < nbSeq -> bs_ready pos lo) /\ (id = nbSeq -> pos = 0 -> lo = 0) /\
       xs_X rb m body lr li lim sp ps ds de = xs_cont e t (Z.to_nat (nbSeq - id)) st pos crep s) \/
    (pos < 0 /\ xs_X rb m body lr li lim sp ps ds de = None).

(* after the id-th decode (the sequence (ll, ml, ov); pos, lo, st already the C's next ones), before its
   execution *)
Definition xs_mid (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z)
    (ll ml ov: Z) : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    let e := xs_env rb body ps ds de in
    (exists s, xs_rel e rb lr li lim c K j s /\ xh_ok e (xmm s) (xop s) /\
       (id + 1 < nbSeq -> bs_ready pos lo) /\ (id + 1 = nbSeq -> pos = 0 -> lo = 0) /\
       xs_X rb m body lr li lim sp ps ds de =
         match x_step e s ll ml (fst (c_offset crep ll ov)) with
         | None => None
         | Some s' => xs_cont e t (Z.to_nat (nbSeq - (id + 1))) st pos (snd (c_offset crep ll ov)) s'
         end) \/
    (pos < 0 /\ xs_X rb m body lr li lim sp ps ds de = None).

(* after the sequences (the bitstream consumed, the repeat offsets crep saved): the last literals are left *)
Definition xs_aft (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    let e := xs_env rb body ps ds de in
    exists s, xs_rel e rb lr li lim c K j s /\
      xs_X rb m body lr li lim sp ps ds de =
        match x_last e s with Some (m', op') => Some (m', op', crep) | None => None end.

(* ---------- the steps ---------- *)

(* BIT_initDStream fails (bs_wf: BlkSeqDEC's BIT_initDStream_spec): the model fails *)
Lemma xs_okb_wf (s: list Z) : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. rewrite !andb_true_iff. intros [[_ H1] H2].
  rewrite Zlength_correct. split; [|exact H2].
  rewrite negb_true_iff in *. apply Z.eqb_neq. apply Nat.eqb_neq in H1. lia.
Qed.

Lemma xs_init_err (t: seq_tabs) :
  xs_ctx -> os = Some t -> 0 < nbSeq -> bs_wf (iw_s i) = false -> xs_none.
Proof.
  intros _ Hos Hnb Hwf rb m body bo lr li lim sp ps ds de _.
  unfold xs_X, x_seq_section. rewrite Hos.
  replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold xb_seqs, x_seqs. destruct t as [[tLL tOF] tML].
  destruct (bs_okb (iw_s i)) eqn:E; [rewrite (xs_okb_wf _ E) in Hwf; discriminate | reflexivity].
Qed.

(* the stream test of x_seqs is BIT_initDStream's (bs_wf) on bytes *)
Lemma xs_okb (s: list Z) : bytes_ok s -> bs_wf s = true -> bs_okb s = true.
Proof.
  intros Hs Hw. rewrite <- Hw. unfold bs_okb, bs_wf.
  replace (forallb (fun b => andb (0 <=? b) (b <? 256)) s) with true.
  2:{ symmetry. apply forallb_forall. intros x Hx. unfold bytes_ok in Hs. rewrite Forall_forall in Hs.
      apply Hs in Hx. unfold is_byte in Hx. lia. }
  rewrite Zlength_correct. cbn [andb]. destruct (length s); reflexivity.
Qed.


(* after BIT_initDStream and the three ZSTD_initFseState (each reads ft_log bits, exactly when they are in the
   container, then reloads: BlkSeqLoopModel.loop_init_model's hypotheses), at 0 sequences *)
Lemma xs_init (tLL tOF tML: fse_table) (v1 v2 v3: Z) :
  xs_ctx -> os = Some (tLL, tOF, tML) -> 0 < nbSeq -> bs_wf (iw_s i) = true ->
  let s := iw_s i in
  let pos0 := bs_total s in let lo0 := 8 * Z.max 0 (Zlength s - 8) in
  let pos1 := pos0 - ft_log tLL in let lo1 := snd (bs_reload pos1 lo0) in
  let pos2 := pos1 - ft_log tOF in let lo2 := snd (bs_reload pos2 lo1) in
  let pos3 := pos2 - ft_log tML in let lo3 := snd (bs_reload pos3 lo2) in
  (lo0 <= pos1 -> v1 = bs_peek (bs_value s) pos0 (ft_log tLL)) ->
  (lo1 <= pos2 -> v2 = bs_peek (bs_value s) pos1 (ft_log tOF)) ->
  (lo2 <= pos3 -> v3 = bs_peek (bs_value s) pos2 (ft_log tML)) ->
  xs_inv (tLL, tOF, tML) 0 0 (oa_c o) rep 0 pos3 lo3 (v1, v2, v3).
Proof.
  intros Hctx Hos Hnb Hwf. cbv zeta. intros H1 H2 H3.
  destruct Hctx as (Ho & Hi & Hns & Hla & Hnb0 & Hcap & Hsq & Hrep & Hlay & HlxbN & Hlxb & Hlx).
  rewrite Hos in Hsq. destruct Hsq as (HLL & HOF & HML).
  destruct HLL as [HlLL _]. destruct HOF as [HlOF _]. destruct HML as [HlML _].
  cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
  assert (Hb: bytes_ok (iw_s i)) by (destruct Hi as (_&_&_&_&_&_&Hb&_); exact Hb).
  intros rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
  unfold xs_X, x_seq_section. rewrite Hos.
  replace (nbSeq =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold xb_seqs, x_seqs. rewrite (xs_okb _ Hb Hwf). cbn [negb].
  pose proof (lim_init (iw_s i) Hb Hwf) as I0.
  destruct (bs_total (iw_s i) - ft_log tLL <? 0) eqn:E1.
  { right. unfold rd; rewrite E1. apply Z.ltb_lt in E1. split; [lia|reflexivity]. }
  replace (rd (iw_s i) (bs_total (iw_s i)) (ft_log tLL)) with
    (Some (bs_peek_s (iw_s i) (bs_total (iw_s i)) (ft_log tLL), bs_total (iw_s i) - ft_log tLL)) by (unfold rd; rewrite E1; reflexivity).
  apply Z.ltb_ge in E1.
  destruct (lim_step _ _ (ft_log tLL) I0 ltac:(lia) ltac:(lia)) as [L1 I1].
  rewrite <- (lim_peek (iw_s i) (bs_total (iw_s i)) (8 * Z.max 0 (Zlength (iw_s i) - 8)) (ft_log tLL) v1 Hb ltac:(lia) ltac:(lia) H1 L1).
  destruct (bs_total (iw_s i) - ft_log tLL - ft_log tOF <? 0) eqn:E2.
  { right. unfold rd; rewrite E2. apply Z.ltb_lt in E2. split; [lia|reflexivity]. }
  replace (rd (iw_s i) (bs_total (iw_s i) - ft_log tLL) (ft_log tOF)) with
    (Some (bs_peek_s (iw_s i) (bs_total (iw_s i) - ft_log tLL) (ft_log tOF), bs_total (iw_s i) - ft_log tLL - ft_log tOF)) by (unfold rd; rewrite E2; reflexivity).
  apply Z.ltb_ge in E2.
  destruct (lim_step _ _ (ft_log tOF) I1 ltac:(lia) ltac:(lia)) as [L2 I2].
  rewrite <- (lim_peek (iw_s i) (bs_total (iw_s i) - ft_log tLL) (snd (bs_reload (bs_total (iw_s i) - ft_log tLL) (8 * Z.max 0 (Zlength (iw_s i) - 8)))) (ft_log tOF) v2 Hb ltac:(lia) ltac:(lia) H2 L2).
  destruct (bs_total (iw_s i) - ft_log tLL - ft_log tOF - ft_log tML <? 0) eqn:E3.
  { right. unfold rd; rewrite E3. apply Z.ltb_lt in E3. split; [lia|reflexivity]. }
  replace (rd (iw_s i) (bs_total (iw_s i) - ft_log tLL - ft_log tOF) (ft_log tML)) with
    (Some (bs_peek_s (iw_s i) (bs_total (iw_s i) - ft_log tLL - ft_log tOF) (ft_log tML), bs_total (iw_s i) - ft_log tLL - ft_log tOF - ft_log tML)) by (unfold rd; rewrite E3; reflexivity).
  apply Z.ltb_ge in E3.
  destruct (lim_step _ _ (ft_log tML) I2 ltac:(lia) ltac:(lia)) as [L3 I3].
  rewrite <- (lim_peek (iw_s i) (bs_total (iw_s i) - ft_log tLL - ft_log tOF) (snd (bs_reload (bs_total (iw_s i) - ft_log tLL - ft_log tOF) (snd (bs_reload (bs_total (iw_s i) - ft_log tLL) (8 * Z.max 0 (Zlength (iw_s i) - 8)))))) (ft_log tML) v3 Hb ltac:(lia) ltac:(lia) H3 L3).
  left. exists (xs_s0 rb m lr li lim sp).
  destruct Hh as (Hreg & Hrb & Hdst & Hwr & Hbo & Hbn & Hbs & Hlr & Hps & Hds & Hli & Hrd & Hrs).
  split; [|split; [|split; [|split]]].
  - (* the C's state is the model's start *)
    assert (Hsp: sp = false /\ (0 <= li <= lim) /\ (lr = R_lxb -> lim + WILDCOPY_OVERLENGTH <= LITEXTRA_N)).
    { pose proof (Zlength_nonneg lits).
      destruct l as [off| |lb|lb]; cbn in Hlr, Hns, Hla.
      - destruct Hlr as (-> & _ & -> & ->). split; [reflexivity|]. split; [lia|discriminate].
      - destruct Hlr as (-> & -> & -> & ->). split; [reflexivity|]. split; [lia|].
        intros _. destruct Hla as (_ & _ & Hn). unfold LITEXTRA_N, LITBUFFEREXTRASIZE in *. lia.
      - destruct Hlr as (-> & _ & -> & ->). split; [reflexivity|]. split; [lia|discriminate].
      - contradiction. }
    destruct Hsp as (-> & Hlil & Hlx').
    unfold xs_rel, xs_s0; cbn [xop xlr xli xlim xsp xmm xm_lxb xm_dst].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Hdst|].
    unfold xl_ok; cbn [xm_lxb]. split; [lia|].
    destruct lr;
      first [ intros j Hj; split; [lia|]; cbn [xm_dst]; apply Hrd; [reflexivity|lia]
            | cbn [xe_src xs_env]; apply Hrs; reflexivity
            | rewrite HlxbN; apply Hlx'; reflexivity ].
  - (* the history is written *)
    assert (Hc: 0 < oa_cap o) by (apply Hcap; lia).
    destruct (Hlay Hc) as (Hpsd & _ & _ & Hel & Hext).
    unfold xh_ok, xs_env, xs_s0; cbn [xe_ps xe_vs xe_de xop xmm].
    unfold hc_region in Hreg.
    destruct (hc_ext h) as [|e1 elen|] eqn:Ex; cbn [ext_len] in Hel;
      [injection Hreg as <- <- <- | injection Hreg as <- <- <- | discriminate].
    + split; [lia|]. split; [lia|]. split; [lia|]. split.
      * intros j Hj. split; [lia|]. apply Hwr; lia.
      * intros j Hj. lia.
    + split; [lia|]. split; [lia|]. split; [lia|]. split.
      * intros j Hj. split; [lia|]. apply Hwr; lia.
      * intros j Hj. split; [lia|]. apply Hwr; right; lia.
  - (* the container holds a whole sequence *)
    intros _. apply I3.
  - intros Hn. lia.
  - (* the rest is the loop *)
    unfold xs_cont. rewrite Z.sub_0_r. reflexivity.
Qed.

(* one ZSTD_decodeSequence (isLast iff nbSeq - id = 1): BlkSeqDEC's ZSTD_decodeSequence_spec's
   postcondition, the container facts of seqstate_at (bit_inv) *)
Lemma xs_dec_step (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z)
    (pos' lo': Z) (st': Z * Z * Z) (ll ml ov: Z) :
  seqs_ok (Some t) -> states_ok t st -> 0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
  0 <= id < nbSeq -> 0 <= lo' <= lo -> pos - DSEQ_BITS <= pos' <= pos ->
  ((nbSeq - id =? 1) = true -> st' = st) ->
  (bs_ready pos lo ->
   forall sq stn pn,
     (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
      dseq_one tLL tOF tML (iw_s i) (nbSeq - id =? 1) sLL sOF sML pos) = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     ((nbSeq - id =? 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
  ((let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
    dseq_one tLL tOF tML (iw_s i) (nbSeq - id =? 1) sLL sOF sML pos) = None -> pos' < 0) ->
  xs_inv t id K c crep j pos lo st ->
  xs_mid t id K c crep j pos' lo' st' ll ml ov.
Proof.
  intros Hso Hst H0lo H8 Hplo Hid Hlo' Hpos' Hlast Hspec Hnone Hinv.
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML]; destruct st' as [[sLL' sOF'] sML'].
  pose proof Hso as (HfLL & HfOF & HfML). pose proof Hst as (HsLL & HsOF & HsML).
  cbv beta iota zeta in Hspec, Hnone.
  intros rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
  destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hr & Hxh & Hrdy & _ & HX) | (Hp & HX)].
  2: { right. split; [lia | exact HX]. }
  specialize (Hrdy (proj2 Hid)).
  assert (Hk: Z.to_nat (nbSeq - id) = S (Z.to_nat (nbSeq - (id + 1)))) by lia.
  assert (Hle: Nat.eqb (Z.to_nat (nbSeq - (id + 1))) 0 = (nbSeq - id =? 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (nbSeq - (id + 1))) 0); destruct (Z.eqb_spec (nbSeq - id) 1); lia. }
  rewrite Hk in HX. unfold xs_cont in HX |- *. cbn [x_seq_loop] in HX. rewrite Hle in HX.
  destruct (dseq_one tLL tOF tML (iw_s i) (nbSeq - id =? 1) sLL sOF sML pos) as [[[sq stn] pn]|] eqn:Ed.
  2: { right. split; [apply Hnone; reflexivity | exact HX]. }
  destruct (Hspec Hrdy sq stn pn eq_refl) as (Hll & Hml & Hov & Hpn & Hnl). subst ll ml ov pos'.
  left. exists s. split; [exact Hr|]. split; [exact Hxh|].
  destruct (c_offset crep (sq_ll sq) (sq_ov sq)) as [off rep'] eqn:Ec. cbn [fst snd].
  destruct (nbSeq - id =? 1) eqn:EL.
  - apply Z.eqb_eq in EL.
    specialize (Hlast eq_refl). injection Hlast as -> -> ->.
    split; [intros; lia|].
    split.
    { intros _ Hp0. subst pn.
      exact (loop_end_lo tLL tOF tML (iw_s i) sLL sOF sML pos lo lo' sq stn HfLL HfOF HfML HsLL HsOF HsML
               H0lo H8 Hplo Hrdy Hlo' Ed). }
    rewrite HX. replace (Z.to_nat (nbSeq - (id + 1))) with O by lia.
    destruct (x_step _ s _ _ off); reflexivity.
  - apply Z.eqb_neq in EL. destruct (Hnl eq_refl) as [Hst' Hrd]. rewrite Hst'.
    split; [intros; exact Hrd|]. split; [intros; lia|].
    rewrite HX. destruct (x_step _ s _ _ off); reflexivity.
Qed.

(* lexec reads dictEnd only for a match reaching into the extDict (offset beyond oLitEnd - prefixStart):
   otherwise its value does not matter (without an extDict the region's dictEnd is prefixStart, the C's
   ext_end is 0) *)
Lemma lexec_de_irr (ps vs de1 de2 oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) :
  off <= op + ll - ps ->
  lexec ps vs de1 oend c op s li llim ll ml off = lexec ps vs de2 oend c op s li llim ll ml off.
Proof.
  intros H. unfold lexec, lmatch. cbv zeta.
  replace (off >? op + ll - ps) with false by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* the C's error condition of ZSTD_execSequence (array offsets) is the model's (region coordinates) *)
Lemma xs_exec_err_eq (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de K j ll ml off: Z) :
  xs_ctx -> xs_hyp rb m body bo lr li lim sp ps ds de ->
  exec_err (oa_d o + K) xs_oend (xs_li0 + j) (xs_li0 + Zlength lits) ll ml off (hc_ps h) (ext_len (hc_ext h)) =
  xexec_err (xs_env rb body ps ds de) (oa_d o + K - rb) (li + j) lim ll ml off.
Proof.
  intros Hc (Hr & _ & _ & _ & _ & _ & _ & Hl & _).
  destruct Hc as (_ & _ & Hns & _).
  unfold exec_err, xexec_err, xs_env, xs_oend, xs_li0, seq_oend; cbn [xe_oend xe_vs].
  unfold hc_region in Hr.
  destruct (hc_ext h); inversion Hr; subst; cbn [ext_len];
  destruct l; cbn in Hl, Hns; try contradiction; decompose record Hl; subst;
  match goal with |- ((?a <? _) || (?c <? _) || (?e <? _))%bool = ((?a' <? _) || (?c' <? _) || (?e' <? _))%bool =>
    replace a with a' by lia; replace c with c' by lia; replace e with e' by lia; reflexivity end.
Qed.

(* on success, the C's stores (lexec in array offsets, the history and literal places of h and l) hold the
   model's new written cells (x_exec_l in region coordinates) *)
Lemma xs_exec_dst (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de K j ll ml off: Z) (mm m': xmem) (op' li': Z) (c: list val) :
  xs_ctx -> xs_hyp rb m body bo lr li lim sp ps ds de -> Zlength c = oa_N o -> 0 <= ll -> 0 <= ml ->
  x_exec (xs_env rb body ps ds de) mm (oa_d o + K - rb) lr (li + j) lim ll ml off = Some (m', op', li') ->
  dst_rel c rb (xm_dst mm) -> xm_lxb mm = lxb ->
  xexec_err (xs_env rb body ps ds de) (oa_d o + K - rb) (li + j) lim ll ml off = false ->
  dst_rel (lexec (hc_ps h) (hc_ps h - ext_len (hc_ext h)) (ext_end (hc_ext h)) xs_oend c (oa_d o + K) xs_lsrc
             (xs_li0 + j) (xs_li0 + Zlength lits) ll ml off) rb (xm_dst m').
Proof.
  intros Hc Hh Hlc Hll Hml Hx Hd Hlx Herr.
  pose proof Hh as (Hr & Hrb & _ & _ & Hbo & Hbn & Hbs & Hl & _).
  pose proof Hc as ((_ & Hoc & _ & Hd0 & Hcap & HN) & (_ & _ & _ & _ & Hic & _) & Hns & Hla & _).
  assert (Hs: src_rel (xe_src (xs_env rb body ps ds de)) (xm_lxb mm) (iw_c i) bo (zbytes lxb)).
  { rewrite Hlx. cbn [xe_src xs_env]. unfold src_rel. repeat split; auto; lia. }
  assert (Hoe: rb + xe_oend (xs_env rb body ps ds de) = xs_oend).
  { cbn [xe_oend xs_env]. unfold seq_oend, xs_oend. destruct l; lia. }
  assert (Hoe2: rb + xe_oend (xs_env rb body ps ds de) <= Zlength c).
  { rewrite Hoe, Hlc. unfold xs_oend. destruct l; cbn in Hla |- *; try lia.
    unfold lits_at in Hla. decompose record Hla. unfold WILDCOPY_OVERLENGTH in *. lia. }
  destruct (x_exec_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Hd Hs Hll Hml ltac:(lia) Hoe2) as [_ HD].
  rewrite Hoe in HD.
  replace (rb + (oa_d o + K - rb)) with (oa_d o + K) in HD by lia.
  revert Herr HD. unfold xexec_err, xs_env; cbn [xe_ps xe_vs xe_de xe_oend].
  unfold hc_region in Hr.
  destruct (hc_ext h) eqn:Ex; inversion Hr; subst; cbn [ext_len ext_end];
  destruct l eqn:El; cbn in Hl, Hns; try contradiction; decompose record Hl; subst;
  unfold xs_lsrc, xs_li0; cbn [reg_l reg_o]; intros Herr HD.
  all: rewrite El; cbv beta iota.
  all: apply orb_false_iff in Herr as [_ Hoff]; apply Z.ltb_ge in Hoff.
  all: first [ rewrite (lexec_de_irr _ _ 0 (rb + (hc_ps h - rb))) by lia | idtac ].
  all: match goal with HD: dst_rel ?A _ _ |- dst_rel ?B _ _ => replace B with A; [exact HD|] end;
    f_equal; lia.
Qed.

(* one ZSTD_execSequence (BlkSeqEXEC's exec_spec: its error iff exec_err, its stores lexec), the sequence
   (ll, ml, off = fst (c_offset crep ll ov)) at op = d + K, the literals at xs_li0 + j *)
Lemma xs_exec_step (t: seq_tabs) (id K: Z) (c c': list val) (crep: Z * Z * Z) (j pos lo: Z)
    (st: Z * Z * Z) (ll ml ov r: Z) :
  xs_ctx -> 0 <= id < nbSeq -> 0 <= K -> oa_d o + K <= xs_oend -> 0 <= j <= Zlength lits ->
  Zlength c = oa_N o -> 0 <= ll -> 1 <= ml -> 1 <= fst (c_offset crep ll ov) ->
  xs_mid t id K c crep j pos lo st ll ml ov ->
  is_error_code r = exec_err (oa_d o + K) xs_oend (xs_li0 + j) (xs_li0 + Zlength lits) ll ml
                      (fst (c_offset crep ll ov)) (hc_ps h) (ext_len (hc_ext h)) ->
  match hc_ext h with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec (hc_ps h) (hc_ps h - ext_len (hc_ext h)) (ext_end (hc_ext h)) xs_oend c (oa_d o + K) xs_lsrc
                (xs_li0 + j) (xs_li0 + Zlength lits) ll ml (fst (c_offset crep ll ov))
  end ->
  (is_error_code r = true -> xs_none) /\
  (is_error_code r = false ->
   xs_inv t (id + 1) (K + (ll + ml)) c' (snd (c_offset crep ll ov)) (j + ll) pos lo st).
Proof.
  intros Hctx Hid HK HKo Hj Hlc Hll Hml Hoff Hmid Herr Hc'.
  set (off := fst (c_offset crep ll ov)) in *.
  (* one choice of the region: the model's step fails iff the C errs, else the relation holds after it *)
  assert (Hstep: forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    forall s, xs_rel (xs_env rb body ps ds de) rb lr li lim c K j s ->
      xh_ok (xs_env rb body ps ds de) (xmm s) (xop s) ->
      match x_step (xs_env rb body ps ds de) s ll ml off with
      | None => is_error_code r = true
      | Some s' => is_error_code r = false /\
          xs_rel (xs_env rb body ps ds de) rb lr li lim c' (K + (ll + ml)) (j + ll) s' /\
          xh_ok (xs_env rb body ps ds de) (xmm s') (xop s')
      end).
  { intros rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk.
    destruct Hrel as (Hop & Hlr & Hli & Hlim & Hsp & Hlx & Hd & Hl).
    unfold x_step. rewrite Hsp, Hop, Hlr, Hli, Hlim.
    rewrite Hop in Hhk.
    pose proof (x_exec_def _ _ _ _ _ _ _ _ _ Hhk Hl Hll Hml Hoff) as D.
    rewrite (xs_exec_err_eq rb m body bo lr li lim sp ps ds de K j ll ml off Hctx Hh) in Herr.
    destruct (x_exec _ _ _ _ _ _ _ _ _) as [[[m' op'] li']|] eqn:Ex; [|congruence].
    destruct D as (He & Hop' & Hli' & Hle & Hw).
    assert (Hr: is_error_code r = false) by congruence.
    split; [exact Hr|].
    assert (Hc2: c' = lexec (hc_ps h) (hc_ps h - ext_len (hc_ext h)) (ext_end (hc_ext h)) xs_oend c (oa_d o + K)
                        xs_lsrc (xs_li0 + j) (xs_li0 + Zlength lits) ll ml off).
    { destruct Hh as (Hreg & _). unfold hc_region in Hreg.
      destruct (hc_ext h); try discriminate; exact (Hc' Hr). }
    pose proof He as He'.
    unfold xexec_err in He'. apply orb_false_iff in He' as [He' He3]. apply orb_false_iff in He' as [He1 He2].
    apply Z.ltb_ge in He1, He2, He3.
    destruct Hle as (Hle & Hlx').
    split.
    - unfold xs_rel; cbn [xmm xop xlr xli xlim xsp].
      split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [congruence|].
      split; [rewrite Hc2; exact (xs_exec_dst rb m body bo lr li lim sp ps ds de K j ll ml off (xmm s) m' op' li' c
                                    Hctx Hh Hlc Hll ltac:(lia) Ex Hd Hlx He)|].
      unfold xl_ok in Hl |- *. destruct Hl as (Hl1 & Hl2). split; [lia|].
      destruct lr; [| rewrite Hlx'; exact Hl2 | exact Hl2].
      intros k Hk. apply Hle, Hl2. lia.
    - unfold xh_ok in Hhk |- *. cbn [xmm xop].
      destruct Hhk as (Hh1 & Hh2 & Hh3 & Hh4 & Hh5).
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      + intros k Hk. destruct (Z.lt_ge_cases k (oa_d o + K - rb)).
        * apply Hle, Hh4. lia.
        * apply Hw. lia.
      + intros k Hk. apply Hle, Hh5. lia. }
  split.
  - intros Hr rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hmid rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & Hhk & _ & _ & HX)|(_ & HX)];
      [|exact HX].
    rewrite HX. specialize (Hstep rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk).
    destruct (x_step _ _ _ _ _) as [s'|]; [destruct Hstep; congruence | reflexivity].
  - intros Hr rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
    destruct (Hmid rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & Hhk & Hb1 & Hb2 & HX)|(Hp & HX)];
      [|right; auto].
    specialize (Hstep rb m body bo lr li lim sp ps ds de Hh s Hrel Hhk).
    rewrite HX. destruct (x_step _ _ _ _ _) as [s'|]; [|congruence].
    destruct Hstep as (_ & Hrel' & Hhk').
    left. exists s'. auto.
Qed.

(* BIT_endOfDStream (success iff lo = 0 and pos = 0), then the repeat offsets saved ((U32) prevOffset: they
   fit 32 bits, rep_ok) *)
Lemma xs_end (t: seq_tabs) (K: Z) (c: list val) (crep: Z * Z * Z) (j pos lo: Z) (st: Z * Z * Z) :
  xs_ctx -> os = Some t -> 0 < nbSeq -> xs_inv t nbSeq K c crep j pos lo st ->
  (~ (lo = 0 /\ pos = 0) -> xs_none) /\
  (lo = 0 -> pos = 0 -> rep_ok crep -> xs_aft K c crep j).
Proof.
  intros _ _ _ Hinv. split.
  - intros Hn rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & _ & _ & _ & Hend & HX)|(_ & HX)]; [|exact HX].
    rewrite HX. unfold xs_cont. destruct t as [[tLL tOF] tML].
    replace (Z.to_nat (nbSeq - nbSeq)) with O by lia. cbn [x_seq_loop].
    destruct (Z.eqb_spec pos 0) as [E|E]; [|reflexivity].
    exfalso. apply Hn. split; [apply Hend; auto | exact E].
  - intros Hlo Hpos Hrep rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & _ & _ & _ & HX)|(Hneg & _)]; [|lia].
    exists s. split; [exact Hrel|]. rewrite HX. unfold xs_cont. destruct t as [[tLL tOF] tML].
    replace (Z.to_nat (nbSeq - nbSeq)) with O by lia. cbn [x_seq_loop]. subst pos. cbn [Z.eqb negb].
    assert (Hr: x_rep32 crep = crep).
    { destruct crep as [[r1 r2] r3]. unfold rep_ok in Hrep. unfold x_rep32.
      rewrite !Z.mod_small by lia. reflexivity. }
    rewrite Hr. reflexivity.
Qed.

(* no sequences: nothing before the last literals, the repeat offsets unchanged *)
Lemma xs_aft_nb0 : xs_ctx -> nbSeq = 0 -> xs_aft 0 (oa_c o) rep 0.
Proof.
  intros HC Hnb rb m body bo lr li lim sp ps ds de Hh.
  destruct HC as (_ & Hi & Hns & Hla & _ & _ & _ & _ & _ & Hlx & _ & _).
  destruct Hh as (_ & Hrb & Hdr & _ & _ & _ & _ & Hlr & _ & _ & Hli & Hwd & Hws).
  destruct Hla as (_ & Hn & Hloc).
  exists (xs_s0 rb m lr li lim sp). cbv zeta.
  assert (Hsp: sp = false /\ lim = li + Zlength lits).
  { unfold litloc_rel in Hlr. destruct l; simpl in Hns; try contradiction; destruct Hlr as (_ & ? & ? & ?); (split; [assumption | lia]). }
  destruct Hsp as [-> Hlim].
  split.
  - unfold xs_rel, xs_s0. cbn [xop xlr xli xlim xsp xmm xm_lxb xm_dst].
    split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact Hdr|].
    unfold xl_ok. rewrite Z.add_0_r. pose proof (Zlength_nonneg lits).
    split; [lia|].
    destruct lr.
    + intros q Hq. split; [lia|]. apply Hwd; [reflexivity | lia].
    + cbn [xm_lxb]. rewrite Hlx. unfold litloc_rel in Hlr.
      destruct l; simpl in Hns; try contradiction; try (destruct Hlr as (Hlr & _); discriminate).
      destruct Hlr as (_ & -> & -> & _). simpl in Hloc.
      unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia.
    + apply Hws; reflexivity.
  - unfold xs_X, x_seq_section. rewrite Hnb. reflexivity.
Qed.

(* memcpy of k bytes from a separate array cs (literals read in place, litExtraBuffer): the cells
   [a, a + k) of c become the cells [s, s + k) of cs *)
Lemma lfwd_LS (k: nat) (c cs: list val) (a s: Z) :
  0 <= a -> a + Z.of_nat k <= Zlength c -> 0 <= s -> s + Z.of_nat k <= Zlength cs ->
  lfwd k c a (LS cs) s = sublist 0 a c ++ sublist s (s + Z.of_nat k) cs ++ sublist (a + Z.of_nat k) (Zlength c) c.
Proof.
  revert c a s. induction k as [|k IH]; intros c a s Ha Hc Hs Hcs; cbn [lfwd lrd].
  - rewrite !Z.add_0_r, sublist_nil, app_nil_l, <- sublist_split, sublist_same; auto; lia.
  - rewrite Nat2Z.inj_succ in *.
    rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite Zlength_upd_Znth.
    replace (a + 1 + Z.of_nat k) with (a + Z.succ (Z.of_nat k)) by lia.
    replace (s + 1 + Z.of_nat k) with (s + Z.succ (Z.of_nat k)) by lia.
    list_solve.
Qed.

(* memcpy of k bytes within the output array, the source at or after the end of the destination: the
   cells [a, a + k) of c become the cells [s, s + k) of c *)
Lemma lfwd_LW_after (k: nat) (c: list val) (a s: Z) :
  0 <= a -> a + Z.of_nat k <= s -> s + Z.of_nat k <= Zlength c ->
  lfwd k c a LW s = sublist 0 a c ++ sublist s (s + Z.of_nat k) c ++ sublist (a + Z.of_nat k) (Zlength c) c.
Proof.
  revert c a s. induction k as [|k IH]; intros c a s Ha Has Hc; cbn [lfwd lrd].
  - rewrite !Z.add_0_r, sublist_nil, app_nil_l, <- sublist_split, sublist_same; auto; lia.
  - rewrite Nat2Z.inj_succ in *.
    rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite Zlength_upd_Znth.
    replace (a + 1 + Z.of_nat k) with (a + Z.succ (Z.of_nat k)) by lia.
    replace (s + 1 + Z.of_nat k) with (s + Z.succ (Z.of_nat k)) by lia.
    list_solve.
Qed.

(* the last literals (lastLLSize = |lits| - j): the capacity error, else memcpy of the literals left to
   op = d + K (which the C has, at xs_li0 + j of their array) *)
Lemma xs_epi (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) :
  xs_ctx -> 0 <= K -> oa_d o + K <= xs_oend -> 0 <= j <= Zlength lits -> Zlength c = oa_N o ->
  sublist (xs_li0 + j) (xs_li0 + Zlength lits) (xs_larr c) = zbytes (skipn (Z.to_nat j) lits) ->
  xs_aft K c crep j ->
  (xs_oend - (oa_d o + K) < Zlength lits - j -> xs_none) /\
  (Zlength lits - j <= xs_oend - (oa_d o + K) ->
   forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
     match xs_X rb m body lr li lim sp ps ds de with
     | None => False
     | Some (mm, op', rep2) =>
         K + (Zlength lits - j) = op' - (oa_d o - rb) /\
         dst_rel (sublist 0 (oa_d o + K) c ++ zbytes (skipn (Z.to_nat j) lits) ++
                  sublist (oa_d o + K + (Zlength lits - j)) (Zlength c) c) rb (xm_dst mm) /\
         rep2 = crep
     end).
Proof.
  intros Hctx HK Hoe Hj Hc Hsub Haft.
  destruct Hctx as (Hoa & Hiw & Hns & Hla & _).
  assert (Hcom: forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
    exists s, xs_rel (xs_env rb body ps ds de) rb lr li lim c K j s /\
      xlim s - xli s = Zlength lits - j /\
      xe_oend (xs_env rb body ps ds de) - xop s = xs_oend - (oa_d o + K) /\
      xs_X rb m body lr li lim sp ps ds de =
        match xm_fwd body (Z.to_nat (Zlength lits - j)) (xmm s) R_dst (xop s) (xlr s) (xli s) with
        | Some m' => if Zlength lits - j >? xs_oend - (oa_d o + K) then None
                     else Some (m', xop s + (Zlength lits - j), crep)
        | None => if Zlength lits - j >? xs_oend - (oa_d o + K) then None else None
        end).
  { intros rb m body bo lr li lim sp ps ds de Hh.
    destruct (Haft rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & HX).
    exists s. pose proof Hrel as (Hop & Hlr & Hli & Hlim & Hsp & _).
    destruct Hh as (_ & _ & _ & _ & _ & _ & _ & Hll & _).
    assert (Hn: xlim s - xli s = Zlength lits - j)
      by (destruct l; cbn in Hns, Hll; intuition lia).
    assert (Hoe': xe_oend (xs_env rb body ps ds de) - xop s = xs_oend - (oa_d o + K))
      by (unfold xs_env, xs_oend, seq_oend; cbn [xe_oend]; destruct l; lia).
    split; [exact Hrel|]. split; [exact Hn|]. split; [exact Hoe'|].
    rewrite HX. unfold x_last. rewrite Hsp. cbv zeta. rewrite Hn, Hoe'.
    destruct (Zlength lits - j >? xs_oend - (oa_d o + K));
      cbn [xe_src xs_env]; destruct (xm_fwd _ _ _ _ _ _ _); reflexivity. }
  split.
  - intros Hcap rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & _ & _ & _ & ->).
    replace (Zlength lits - j >? xs_oend - (oa_d o + K)) with true by lia.
    destruct (xm_fwd _ _ _ _ _ _ _); reflexivity.
  - intros Hcap rb m body bo lr li lim sp ps ds de Hh.
    destruct (Hcom rb m body bo lr li lim sp ps ds de Hh) as (s & Hrel & Hn & Hoe' & ->).
    replace (Zlength lits - j >? xs_oend - (oa_d o + K)) with false by lia.
    destruct Hrel as (Hop & Hlr & Hli & Hlim & Hsp & Hlxb & Hdr & Hxl).
    destruct Hh as (_ & Hrb & _ & _ & Hbo & Hbn & Hbs & Hll & _).
    pose proof Hoa as (_ & HoN & _ & Hd0 & Hcap0 & HdN).
    pose proof Hiw as (_ & _ & _ & _ & HiN & _).
    destruct Hla as (_ & Hn0 & Hla).
    assert (Hoend: xs_oend <= oa_d o + oa_cap o)
      by (unfold xs_oend; destruct l; try lia; destruct Hla as (? & ? & _); unfold WILDCOPY_OVERLENGTH in *; lia).
    set (n := Zlength lits - j) in *.
    assert (Hnn: Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
    destruct Hxl as (Hl0 & Hxl).
    assert (HW: WILDCOPY_OVERLENGTH = 32) by reflexivity.
    destruct (xm_fwd_def body (Z.to_nat n) (xmm s) (xop s) (xlr s) (xli s)) as (m' & Hf & _ & _).
    { lia. }
    { lia. }
    { rewrite Hnn, Hlr. destruct lr.
      - intros t Ht. apply Hxl. destruct (_ <? _); lia.
      - rewrite Hlxb in Hxl |- *. lia.
      - cbn [xe_src xs_env] in Hxl. lia. }
    rewrite Hf. split; [lia|]. split; [|reflexivity].
    destruct (xm_fwd_l body (Z.to_nat n) (xmm s) m' (xop s) (xlr s) (xli s) c (iw_c i) (zbytes lxb) rb bo)
      as (_ & Hd); auto.
    { rewrite Hlxb. unfold src_rel. repeat split; auto; lia. }
    { lia. }
    { lia. }
    replace (rb + xop s) with (oa_d o + K) in Hd by lia.
    rewrite Hlr, Hli in Hd.
    unfold xs_li0, xs_larr, xs_oend in *.
    destruct l as [off| |lb|lb]; cbn in Hns, Hll; [| | |contradiction].
    + destruct Hll as (-> & -> & -> & _).
      cbn [reg_l reg_o] in Hd. rewrite lfwd_LS in Hd by (try rewrite Zlength_map; lia).
      replace (bo + (li + j) + Z.of_nat (Z.to_nat n)) with (bo + li + Zlength lits) in Hd by lia.
      replace (bo + (li + j)) with (bo + li + j) in Hd by lia.
      rewrite Hsub, Hnn in Hd. exact Hd.
    + destruct Hll as (-> & -> & -> & _).
      cbn [reg_l reg_o] in Hd. cbn [xe_src xs_env] in Hxl. rewrite Hlxb in Hxl.
      rewrite lfwd_LS in Hd by (rewrite ?Zlength_map; lia).
      replace (0 + (0 + j) + Z.of_nat (Z.to_nat n)) with (0 + Zlength lits) in Hd by lia.
      replace (0 + (0 + j)) with (0 + j) in Hd by lia.
      rewrite Hsub, Hnn in Hd. exact Hd.
    + destruct Hll as (-> & -> & -> & _).
      cbn [reg_l reg_o] in Hd. rewrite lfwd_LW_after in Hd by lia.
      replace (rb + (li + j) + Z.of_nat (Z.to_nat n)) with (rb + li + Zlength lits) in Hd by lia.
      replace (rb + (li + j)) with (rb + li + j) in Hd by lia.
      rewrite Hsub, Hnn in Hd. exact Hd.
Qed.

(* ---------- the clause ---------- *)

Lemma xs_exact_none (r: Z) (oc': list val) (rep': Z * Z * Z) :
  is_error_code r = true -> xs_none -> seqs_exact os rep l lits lxb nbSeq o i h r oc' rep'.
Proof.
  intros Hr Hn rb m body bo lr li lim sp ps ds de H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  cbv zeta.
  pose proof (Hn rb m body bo lr li lim sp ps ds de ltac:(unfold xs_hyp; repeat (split; [assumption|]); assumption)) as E.
  unfold xs_X, xs_env, xs_s0 in E. rewrite E. exact Hr.
Qed.

Lemma xs_exact_some (r: Z) (oc': list val) (rep': Z * Z * Z) :
  is_error_code r = false ->
  (forall rb m body bo lr li lim sp ps ds de, xs_hyp rb m body bo lr li lim sp ps ds de ->
     match xs_X rb m body lr li lim sp ps ds de with
     | None => False
     | Some (mm, op', rep2) => r = op' - (oa_d o - rb) /\ dst_rel oc' rb (xm_dst mm) /\ rep' = rep2
     end) ->
  seqs_exact os rep l lits lxb nbSeq o i h r oc' rep'.
Proof.
  intros Hr Hs rb m body bo lr li lim sp ps ds de H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  cbv zeta.
  specialize (Hs rb m body bo lr li lim sp ps ds de ltac:(unfold xs_hyp; repeat (split; [assumption|]); assumption)).
  unfold xs_X, xs_env, xs_s0 in Hs.
  destruct (x_seq_section _ _ _ _ _ _) as [[[mm op'] rep2]|]; [|contradiction].
  destruct Hs as (A & B & C). auto.
Qed.

End ShortX.
