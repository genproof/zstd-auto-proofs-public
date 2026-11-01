(* The long loop against the exact block model: the decoder's steps (BIT_initDStream, the three ZSTD_initFseState, one ZSTD_decodeSequence, BIT_endOfDStream), the repeat offsets, no sequences (BlkSeqLoopLongX: the predicates). Plain Coq. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopLongX.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* ---------- helpers ---------- *)

(* the stream test of x_seqs implies BIT_initDStream's (bs_wf) *)
Lemma xl_okb_wf (s: list Z) : bs_okb s = true -> bs_wf s = true.
Proof.
  unfold bs_okb, bs_wf. rewrite !andb_true_iff. intros [[_ H1] H2].
  rewrite Zlength_correct. split; [|exact H2].
  rewrite negb_true_iff in *. apply Z.eqb_neq. apply Nat.eqb_neq in H1. lia.
Qed.

(* on bytes, the stream test of x_seqs is BIT_initDStream's (bs_wf) *)
Lemma xl_okb (s: list Z) : bytes_ok s -> bs_wf s = true -> bs_okb s = true.
Proof.
  intros Hs Hw. rewrite <- Hw. unfold bs_okb, bs_wf.
  replace (forallb (fun b => andb (0 <=? b) (b <? 256)) s) with true.
  2:{ symmetry. apply forallb_forall. intros x Hx. unfold bytes_ok in Hs. rewrite Forall_forall in Hs.
      apply Hs in Hx. unfold is_byte in Hx. lia. }
  rewrite Zlength_correct. cbn [andb]. destruct (length s); reflexivity.
Qed.

(* executing a queue q ++ q' is executing q, then q' *)
Lemma x_steps_app (e: xenv) (s: xex) (q q': list (Z * Z * Z)) :
  x_steps e s (q ++ q') = match x_steps e s q with Some s1 => x_steps e s1 q' | None => None end.
Proof.
  revert s. induction q as [|[[ll ml] off] q IH]; intros s; cbn [app x_steps]; [reflexivity|].
  destruct (x_step e s ll ml off); [apply IH | reflexivity].
Qed.

(* the model's initial literal pointer: 0 <= li <= lim, not split unless the literals are, the 32 cells after
   litExtraBuffer's literals inside it *)
Lemma xl_litptr (a: la) (rb bo: Z) (lr: xreg) (li lim: Z) (sp: bool) :
  xl_ctx a -> litloc_rel (a_l a) rb bo (Zlength (a_lits a)) lr li lim sp -> 0 <= li ->
  li <= lim /\ (lr = R_lxb -> lim + WILDCOPY_OVERLENGTH <= LITEXTRA_N).
Proof.
  intros Hctx Hlr Hli.
  destruct Hctx as (_ & _ & Hla & _).
  destruct Hla as (_ & Hn & Hloc).
  destruct (a_l a) as [off| |lb|lb]; cbn in Hlr, Hloc.
  - destruct Hlr as (-> & _ & -> & _). split; [lia|discriminate].
  - destruct Hlr as (-> & -> & -> & _). split; [lia|].
    intros _. unfold LITEXTRA_N, LITBUFFEREXTRASIZE in *. lia.
  - destruct Hlr as (-> & _ & -> & _). split; [lia|discriminate].
  - destruct Hlr as (-> & _ & -> & _). split; [lia|discriminate].
Qed.

(* the model's start relates to the C's start (nothing written, no literal used, not switched) *)
Lemma xl_rel_s0 (a: la) (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de: Z) :
  xl_ctx a -> xl_hyp a rb m body bo lr li lim sp ps ds de ->
  xl_rel a (xl_env a rb body ps ds de) rb lr li lim sp (oa_c (a_o a)) 0 0 false (xl_s0 a rb m lr li lim sp).
Proof.
  intros Hctx Hh.
  destruct Hh as (Hreg & Hrb & Hdst & Hwr & Hbo & Hbn & Hbs & Hlr & Hps & Hds & Hli & Hrd & Hrs).
  destruct (xl_litptr a rb bo lr li lim sp Hctx Hlr Hli) as (Hlil & Hlx').
  pose proof Hctx as (_ & _ & _ & _ & _ & _ & _ & _ & (HlxbN & _)).
  unfold xl_rel, xl_s0, a_d; cbn [xop xlr xli xlim xsp xmm xm_lxb xm_dst].
  split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hdst|].
  unfold xl_ok; cbn [xm_lxb]. split; [lia|].
  destruct lr;
    first [ intros j Hj; split; [lia|]; cbn [xm_dst]; apply Hrd; [reflexivity|lia]
          | cbn [xe_src xl_env]; apply Hrs; reflexivity
          | rewrite HlxbN; apply Hlx'; reflexivity ].
Qed.

(* BIT_initDStream fails (bs_wf: Spec_bits' BIT_initDStream_spec): the model fails *)
Lemma xl_init_err (a: la) (t: seq_tabs) :
  xl_ctx a -> a_os a = Some t -> 0 < a_nb a -> bs_wf (iw_s (a_i a)) = false -> xl_none a.
Proof.
  intros _ Hos Hnb Hwf rb m body bo lr li lim sp ps ds de _.
  unfold xl_X, x_seq_section. rewrite Hos.
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold xb_seqs, x_seqs. destruct t as [[tLL tOF] tML].
  destruct (bs_okb (iw_s (a_i a))) eqn:E; [rewrite (xl_okb_wf _ E) in Hwf; discriminate | reflexivity].
Qed.

(* after BIT_initDStream and the three ZSTD_initFseState (each reads ft_log bits, exactly when they are in the
   container, then reloads: BlkSeqLoopModel.loop_init_model's hypotheses), at 0 sequences *)
Lemma xl_init (a: la) (tLL tOF tML: fse_table) (v1 v2 v3: Z) :
  xl_ctx a -> a_os a = Some (tLL, tOF, tML) -> 0 < a_nb a -> bs_wf (iw_s (a_i a)) = true ->
  let s := iw_s (a_i a) in
  let pos0 := bs_total s in let lo0 := 8 * Z.max 0 (Zlength s - 8) in
  let pos1 := pos0 - ft_log tLL in let lo1 := snd (bs_reload pos1 lo0) in
  let pos2 := pos1 - ft_log tOF in let lo2 := snd (bs_reload pos2 lo1) in
  let pos3 := pos2 - ft_log tML in let lo3 := snd (bs_reload pos3 lo2) in
  (lo0 <= pos1 -> v1 = bs_peek (bs_value s) pos0 (ft_log tLL)) ->
  (lo1 <= pos2 -> v2 = bs_peek (bs_value s) pos1 (ft_log tOF)) ->
  (lo2 <= pos3 -> v3 = bs_peek (bs_value s) pos2 (ft_log tML)) ->
  xl_inv a (tLL, tOF, tML) 0 0 (oa_c (a_o a)) (a_rep a) 0 false pos3 lo3 (v1, v2, v3) nil.
Proof.
  intros Hctx Hos Hnb Hwf. cbv zeta. intros H1 H2 H3.
  pose proof Hctx as (Ho & Hi & Hla & Hnb0 & Hcap & Hsq & Hrep & Hlay & Hlxb).
  rewrite Hos in Hsq. destruct Hsq as (HLL & HOF & HML).
  destruct HLL as [HlLL _]. destruct HOF as [HlOF _]. destruct HML as [HlML _].
  cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
  assert (Hb: bytes_ok (iw_s (a_i a))) by (destruct Hi as (_&_&_&_&_&_&Hb&_); exact Hb).
  intros rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
  unfold xl_X, x_seq_section. rewrite Hos.
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold xb_seqs, x_seqs. rewrite (xl_okb _ Hb Hwf). cbn [negb].
  set (S0 := iw_s (a_i a)) in *.
  pose proof (lim_init S0 Hb Hwf) as I0.
  destruct (bs_total S0 - ft_log tLL <? 0) eqn:E1.
  { right. unfold rd; rewrite E1. apply Z.ltb_lt in E1. split; [lia|reflexivity]. }
  replace (rd S0 (bs_total S0) (ft_log tLL)) with
    (Some (bs_peek_s S0 (bs_total S0) (ft_log tLL), bs_total S0 - ft_log tLL)) by (unfold rd; rewrite E1; reflexivity).
  apply Z.ltb_ge in E1.
  destruct (lim_step _ _ (ft_log tLL) I0 ltac:(lia) ltac:(lia)) as [L1 I1].
  rewrite <- (lim_peek S0 (bs_total S0) (8 * Z.max 0 (Zlength S0 - 8)) (ft_log tLL) v1 Hb ltac:(lia) ltac:(lia) H1 L1).
  destruct (bs_total S0 - ft_log tLL - ft_log tOF <? 0) eqn:E2.
  { right. unfold rd; rewrite E2. apply Z.ltb_lt in E2. split; [lia|reflexivity]. }
  replace (rd S0 (bs_total S0 - ft_log tLL) (ft_log tOF)) with
    (Some (bs_peek_s S0 (bs_total S0 - ft_log tLL) (ft_log tOF), bs_total S0 - ft_log tLL - ft_log tOF)) by (unfold rd; rewrite E2; reflexivity).
  apply Z.ltb_ge in E2.
  destruct (lim_step _ _ (ft_log tOF) I1 ltac:(lia) ltac:(lia)) as [L2 I2].
  rewrite <- (lim_peek S0 (bs_total S0 - ft_log tLL) (snd (bs_reload (bs_total S0 - ft_log tLL) (8 * Z.max 0 (Zlength S0 - 8)))) (ft_log tOF) v2 Hb ltac:(lia) ltac:(lia) H2 L2).
  destruct (bs_total S0 - ft_log tLL - ft_log tOF - ft_log tML <? 0) eqn:E3.
  { right. unfold rd; rewrite E3. apply Z.ltb_lt in E3. split; [lia|reflexivity]. }
  replace (rd S0 (bs_total S0 - ft_log tLL - ft_log tOF) (ft_log tML)) with
    (Some (bs_peek_s S0 (bs_total S0 - ft_log tLL - ft_log tOF) (ft_log tML), bs_total S0 - ft_log tLL - ft_log tOF - ft_log tML)) by (unfold rd; rewrite E3; reflexivity).
  apply Z.ltb_ge in E3.
  destruct (lim_step _ _ (ft_log tML) I2 ltac:(lia) ltac:(lia)) as [L3 I3].
  rewrite <- (lim_peek S0 (bs_total S0 - ft_log tLL - ft_log tOF) (snd (bs_reload (bs_total S0 - ft_log tLL - ft_log tOF) (snd (bs_reload (bs_total S0 - ft_log tLL) (8 * Z.max 0 (Zlength S0 - 8)))))) (ft_log tML) v3 Hb ltac:(lia) ltac:(lia) H3 L3).
  left. exists (xl_s0 a rb m lr li lim sp).
  split; [exact (xl_rel_s0 a rb m body bo lr li lim sp ps ds de Hctx Hh)|].
  destruct Hh as (Hreg & Hrb & Hdst & Hwr & Hbo & Hbn & Hbs & Hlr & Hps & Hds & Hli & Hrd & Hrs).
  split; [|split; [|split]].
  - (* the history is written *)
    assert (Hc: 0 < oa_cap (a_o a)) by (apply Hcap; lia).
    destruct (Hlay Hc) as (Hpsd & _ & _ & Hel & Hext).
    unfold xh_ok, xl_env, xl_s0; cbn [xe_ps xe_vs xe_de xop xmm].
    unfold hc_region in Hreg.
    destruct (hc_ext (a_h a)) as [|e1 elen|] eqn:Ex; cbn [ext_len] in Hel;
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
    unfold xl_cont. cbn [x_steps]. rewrite Z.sub_0_r. reflexivity.
Qed.

(* one ZSTD_decodeSequence (isLast iff id = nbSeq - 1): BlkSeqDEC's ZSTD_decodeSequence_spec's
   postcondition, the container facts of seqstate_at (bit_inv); the decoded sequence joins the queue *)
Lemma xl_dec_step (a: la) (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool)
    (pos lo: Z) (st: Z * Z * Z) (q: list (Z * Z * Z)) (pos' lo': Z) (st': Z * Z * Z) (ll ml ov: Z) :
  seqs_ok (Some t) -> states_ok t st -> 0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
  0 <= id < a_nb a -> 0 <= lo' <= lo -> pos - DSEQ_BITS <= pos' <= pos ->
  ((id =? a_nb a - 1) = true -> st' = st) ->
  (bs_ready pos lo ->
   forall sq stn pn,
     (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
      dseq_one tLL tOF tML (iw_s (a_i a)) (id =? a_nb a - 1) sLL sOF sML pos) = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     ((id =? a_nb a - 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
  ((let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
    dseq_one tLL tOF tML (iw_s (a_i a)) (id =? a_nb a - 1) sLL sOF sML pos) = None -> pos' < 0) ->
  xl_inv a t id K c crep j sw pos lo st q ->
  xl_inv a t (id + 1) K c (snd (c_offset crep ll ov)) j sw pos' lo' st'
    (q ++ [(ll, ml, fst (c_offset crep ll ov))]).
Proof.
  intros Hso Hst H0lo H8 Hplo Hid Hlo' Hpos' Hlast Hspec Hnone Hinv.
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML]; destruct st' as [[sLL' sOF'] sML'].
  pose proof Hso as (HfLL & HfOF & HfML). pose proof Hst as (HsLL & HsOF & HsML).
  cbv beta iota zeta in Hspec, Hnone.
  intros rb m body bo lr li lim sp ps ds de Hh. cbv zeta.
  destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hr & Hxh & Hrdy & _ & HX) | (Hp & HX)].
  2: { right. split; [lia | exact HX]. }
  specialize (Hrdy (proj2 Hid)).
  assert (Hk: Z.to_nat (a_nb a - id) = S (Z.to_nat (a_nb a - (id + 1)))) by lia.
  assert (Hle: Nat.eqb (Z.to_nat (a_nb a - (id + 1))) 0 = (id =? a_nb a - 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (a_nb a - (id + 1))) 0); destruct (Z.eqb_spec id (a_nb a - 1)); lia. }
  rewrite Hk in HX. unfold xl_cont in HX |- *. cbn [x_seq_loop] in HX. rewrite Hle in HX.
  destruct (dseq_one tLL tOF tML (iw_s (a_i a)) (id =? a_nb a - 1) sLL sOF sML pos) as [[[sq stn] pn]|] eqn:Ed.
  2: { right. split; [apply Hnone; reflexivity|].
       rewrite HX. destruct (x_steps _ s q); reflexivity. }
  destruct (Hspec Hrdy sq stn pn eq_refl) as (Hll & Hml & Hov & Hpn & Hnl). subst ll ml ov pos'.
  left. exists s. split; [exact Hr|]. split; [exact Hxh|].
  rewrite x_steps_app.
  destruct (c_offset crep (sq_ll sq) (sq_ov sq)) as [off rep'] eqn:Ec. cbn [fst snd].
  destruct (id =? a_nb a - 1) eqn:EL.
  - apply Z.eqb_eq in EL.
    specialize (Hlast eq_refl). injection Hlast as -> -> ->.
    split; [intros; lia|].
    split.
    { intros _ Hp0. subst pn.
      exact (loop_end_lo tLL tOF tML (iw_s (a_i a)) sLL sOF sML pos lo lo' sq stn HfLL HfOF HfML HsLL HsOF HsML
               H0lo H8 Hplo Hrdy Hlo' Ed). }
    rewrite HX. replace (Z.to_nat (a_nb a - (id + 1))) with O by lia.
    destruct (x_steps _ s q) as [s1|]; [|reflexivity]. cbn [x_steps x_seq_loop].
    destruct (x_step _ s1 _ _ off); reflexivity.
  - apply Z.eqb_neq in EL. destruct (Hnl eq_refl) as [Hst' Hrd]. rewrite Hst'.
    split; [intros; exact Hrd|]. split; [intros; lia|].
    rewrite HX. destruct (x_steps _ s q) as [s1|]; [|reflexivity]. cbn [x_steps].
    destruct (x_step _ s1 _ _ off); reflexivity.
Qed.

(* BIT_endOfDStream (success iff lo = 0 and pos = 0), after the last decode *)
Lemma xl_end (a: la) (t: seq_tabs) (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool) (pos lo: Z)
    (st: Z * Z * Z) (q: list (Z * Z * Z)) :
  xl_inv a t (a_nb a) K c crep j sw pos lo st q -> ~ (lo = 0 /\ pos = 0) -> xl_none a.
Proof.
  intros Hinv Hn rb m body bo lr li lim sp ps ds de Hh.
  destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & _ & _ & _ & Hend & HX)|(_ & HX)]; [|exact HX].
  rewrite HX. unfold xl_cont. destruct t as [[tLL tOF] tML].
  replace (Z.to_nat (a_nb a - a_nb a)) with O by lia.
  destruct (x_steps _ s q) as [s1|]; [|reflexivity]. cbn [x_seq_loop].
  destruct (Z.eqb_spec pos 0) as [E|E]; [|reflexivity].
  exfalso. apply Hn. split; [apply Hend; auto | exact E].
Qed.

(* the queue executed, the bitstream consumed: the repeat offsets saved ((U32) prevOffset), the last literals
   are left *)
Lemma xl_reps (a: la) (t: seq_tabs) (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool) (lo: Z)
    (st: Z * Z * Z) :
  xl_inv a t (a_nb a) K c crep j sw 0 lo st nil -> xl_aft a K c (x_rep32 crep) j sw.
Proof.
  intros Hinv rb m body bo lr li lim sp ps ds de Hh.
  destruct (Hinv rb m body bo lr li lim sp ps ds de Hh) as [(s & Hrel & _ & _ & _ & HX)|(Hneg & _)]; [|lia].
  exists s. split; [exact Hrel|]. rewrite HX. unfold xl_cont. destruct t as [[tLL tOF] tML].
  replace (Z.to_nat (a_nb a - a_nb a)) with O by lia. reflexivity.
Qed.

(* no sequences: nothing before the last literals, the repeat offsets unchanged *)
Lemma xl_aft_nb0 (a: la) : xl_ctx a -> a_nb a = 0 -> xl_aft a 0 (oa_c (a_o a)) (a_rep a) 0 false.
Proof.
  intros Hctx Hnb rb m body bo lr li lim sp ps ds de Hh.
  exists (xl_s0 a rb m lr li lim sp). cbv zeta.
  split; [exact (xl_rel_s0 a rb m body bo lr li lim sp ps ds de Hctx Hh)|].
  unfold xl_X, x_seq_section. rewrite Hnb. reflexivity.
Qed.

