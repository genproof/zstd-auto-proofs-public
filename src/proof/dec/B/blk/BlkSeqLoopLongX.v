(* The long loop (ZSTD_decompressSequencesLong_body, any literals) against the exact block model
   (model/ExBlock.v): the plain-Coq steps of its last clause BlkIface.seqs_exact.  BlkSeqLoopLong's VST proof
   (BlkSeqLoopLongDefs: LI, XI) carries the predicates below in its invariants and discharges each step with
   one lemma here.

   seqs_exact quantifies over the model's region (rb, m), the block body (body at bo) and the literal pointer
   (lr, li, lim, sp) satisfying its hypotheses (xl_hyp); for each choice the model's outcome is xl_X.  The
   long loop decodes up to 8 sequences ahead of the one it executes: its state is the executor's (op = d + K,
   j literals used, sw: split literals switched to litExtraBuffer, the output array c), the decoder's (FSE
   states st, bitstream position pos / container lo, repeat offsets crep, after id sequences) and the queue q
   of the sequences decoded and not yet executed (their C values (ll, ml, offset)).  The executor's state is
   related to a model state s (xl_rel): op = rb + xop s, the literal pointer, every written cell of the
   model's region is the array's (dst_rel), the literals are written (xl_ok: then the model fails exactly
   when the C does, BlkSeqXKitD).  Decoding never touches memory, so the model, which decodes and executes
   one sequence after the other (x_seq_loop), is the same as executing the queue first (x_steps) and then
   continuing from the decoder's state (xl_cont).

   The loop invariant (xl_inv) is this continuation equality -- or the bitstream has overflowed (pos < 0:
   the model failed on a read below the stream's start, the C keeps decoding from an overflowed container and
   its BIT_endOfDStream check, before the last sequences are executed, fails) and xl_X = None.

   Steps (BlkSeqLoopLongXD / XE / XP): xl_init_err / xl_init (BIT_initDStream, the three ZSTD_initFseState), xl_dec_step (one
   ZSTD_decodeSequence), xl_exec_N / xl_exec_S / xl_exec_X1 (the queue head: ZSTD_execSequence,
   ZSTD_execSequenceSplitLitBuffer, the switch of split literals to litExtraBuffer), xl_end (BIT_endOfDStream),
   xl_reps (the repeat offsets saved), xl_aft_nb0 (no sequences), xl_epi_head / xl_epi_last (the last
   literals), xl_exact_none / xl_exact_some (the clause itself). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Zstd.proof.model.ExCSeq Zstd.proof.model.ExBlock.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

(* ===================== the arguments ===================== *)

(* the WITH of seqs_spec (lxb: litExtraBuffer's bytes) and the addresses of the body's five locals *)
Record la := mk_la {
  a_gv: globals; a_p: val; a_fs: fstate; a_ox: option ddx; a_os: option (fse_table * fse_table * fse_table);
  a_fe: Z; a_rep: Z * Z * Z; a_l: litloc; a_lits: list Z; a_lxb: list Z; a_nb: Z; a_bsm: Z;
  a_W: list ptr_witness; a_o: outarr; a_i: inwin; a_h: hctx;
  a_vlp: val; a_vsqs: val; a_vss: val; a_vs: val; a_vs1: val }.

Definition a_n (a: la) : Z := Zlength (a_lits a).
Definition a_ob (a: la) : val := oa_base (a_o a).
Definition a_d (a: la) : Z := oa_d (a_o a).
Definition a_cap (a: la) : Z := oa_cap (a_o a).
Definition a_ps (a: la) : Z := hc_ps (a_h a).
Definition a_x (a: la) : ext_seg := hc_ext (a_h a).
Definition a_start (a: la) : val := offset_val (iw_off (a_i a)) (iw_base (a_i a)).
(* oend = ostart + E: litBuffer for literals in dst, else dst + capacity *)
Definition a_E (a: la) : Z := match a_l a with LDst lb => lb | _ => a_d a + a_cap a end.
Definition a_adv (a: la) : Z := Z.min (a_nb a) 8.

(* the literals: litPtr = lit_base + lit_li (j literals consumed), litBufferEnd = lit_base + lit_lim;
   sw: LSplit after the switch to litExtraBuffer *)
Definition lit_base (a: la) (sw: bool) : val :=
  match a_l a with
  | LIn _ => iw_base (a_i a)
  | LExtra => lit_extra (a_p a)
  | LDst _ => a_ob a
  | LSplit _ => if sw then lit_extra (a_p a) else a_ob a
  end.
Definition lit_li (a: la) (sw: bool) (j: Z) : Z :=
  match a_l a with
  | LIn off => off + j
  | LExtra => j
  | LDst lb => lb + j
  | LSplit lb => if sw then j - (a_n a - LITBUFFEREXTRASIZE) else lb + j
  end.
Definition lit_lim (a: la) (sw: bool) : Z :=
  match a_l a with
  | LIn off => off + a_n a
  | LExtra => a_n a
  | LDst lb => lb + a_n a
  | LSplit lb => if sw then LITBUFFEREXTRASIZE else lb + (a_n a - LITBUFFEREXTRASIZE)
  end.

(* ===================== the model's side ===================== *)

(* the literals' array as a source of BlkSeqXMem's copies (litExtraBuffer holds lxb), and as a list *)
Definition xl_lsrc (a: la) (sw: bool) : lsrc :=
  match a_l a with
  | LIn _ => LS (iw_c (a_i a))
  | LExtra => LS (zbytes (a_lxb a))
  | LDst _ => LW
  | LSplit _ => if sw then LS (zbytes (a_lxb a)) else LW
  end.
Definition xl_larr (a: la) (sw: bool) (c: list val) : list val :=
  match a_l a with
  | LIn _ => iw_c (a_i a)
  | LExtra => zbytes (a_lxb a)
  | LDst _ => c
  | LSplit _ => if sw then zbytes (a_lxb a) else c
  end.

(* litExtraBuffer's bytes (BlkIface.litfields): the literals (LExtra), the last 65536 of them (LSplit) *)
Definition xl_lxb_ok (a: la) : Prop :=
  let lits := a_lits a in let lxb := a_lxb a in
  Zlength lxb = LITEXTRA_N /\ bytes_ok lxb /\
  match a_l a with
  | LExtra => sublist 0 (Zlength lits) lxb = lits
  | LSplit _ => sublist 0 LITBUFFEREXTRASIZE lxb = sublist (Zlength lits - LITBUFFEREXTRASIZE) (Zlength lits) lits
  | _ => True
  end.

(* the facts of the precondition the steps use *)
Definition xl_ctx (a: la) : Prop :=
  let o := a_o a in let h := a_h a in
  outarr_ok o /\ inwin_ok (a_i a) /\ lits_at (a_l a) (oa_c o) (oa_d o) (oa_cap o) (a_i a) (a_lits a) /\
  0 <= a_nb a /\ (a_nb a > 0 -> a_os a <> None /\ 0 < oa_cap o) /\ seqs_ok (a_os a) /\ rep_ok (a_rep a) /\
  (0 < oa_cap o -> layout_ok (a_fs a) (oa_base o) (oa_N o) (oa_d o) (hc_ps h) (hc_ext h)) /\
  xl_lxb_ok a.

(* the executor's position facts (BlkSeqLoopLongDefs.ex_safe's): op in [d, oend], the literal position in
   range, sw only for split literals, after their part in dst *)
Definition xl_pos (a: la) (K j: Z) (sw: bool) (c: list val) : Prop :=
  0 <= K /\ a_d a + K <= a_E a /\ 0 <= j <= a_n a /\
  match a_l a with
  | LSplit _ => if sw then a_n a - LITBUFFEREXTRASIZE <= j else j <= a_n a - LITBUFFEREXTRASIZE
  | _ => sw = false
  end /\
  Zlength c = oa_N (a_o a).

(* the hypotheses of seqs_exact for one choice of the region, the body and the literal pointer *)
Definition xl_hyp (a: la) (rb: Z) (m: list (option Z)) (body: list Z) (bo: Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de: Z) : Prop :=
  let o := a_o a in let i := a_i a in
  hc_region (a_h a) rb = Some (ps, ds, de) /\ 0 <= rb <= oa_d o /\
  dst_rel (oa_c o) rb m /\
  (forall j, ps <= j < oa_d o - rb \/ ds <= j < de -> nth (Z.to_nat j) m None <> None) /\
  0 <= bo /\ bo + Zlength body <= iw_N i /\ sublist bo (bo + Zlength body) (iw_c i) = zbytes body /\
  litloc_rel (a_l a) rb bo (Zlength (a_lits a)) lr li lim sp /\
  0 <= ps /\ 0 <= ds /\ 0 <= li /\
  (lr = R_dst -> forall j, li <= j < lim + WILDCOPY_OVERLENGTH -> nth (Z.to_nat j) m None <> None) /\
  (lr = R_src -> lim + WILDCOPY_OVERLENGTH <= Zlength body).

Definition xl_env (a: la) (rb: Z) (body: list Z) (ps ds de: Z) : xenv :=
  {| xe_src := body; xe_ps := ps; xe_vs := ps - (de - ds); xe_de := de; xe_oend := seq_oend (a_l a) rb (a_o a) |}.

Definition xl_s0 (a: la) (rb: Z) (m: list (option Z)) (lr: xreg) (li lim: Z) (sp: bool) : xex :=
  {| xmm := {| xm_dst := m; xm_lxb := a_lxb a |}; xop := oa_d (a_o a) - rb; xlr := lr; xli := li; xlim := lim;
     xsp := sp |}.

(* the model's outcome *)
Definition xl_X (a: la) (rb: Z) (m: list (option Z)) (body: list Z) (lr: xreg) (li lim: Z) (sp: bool)
    (ps ds de: Z) : option (xmem * Z * (Z * Z * Z)) :=
  x_seq_section (xl_env a rb body ps ds de) (a_os a) (a_rep a) (iw_s (a_i a)) (a_nb a) (xl_s0 a rb m lr li lim sp).

(* the model fails on every choice *)
Definition xl_none (a: la) : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
    xl_X a rb m body lr li lim sp ps ds de = None.

(* the C's executor state (K bytes written, j literals used, sw, the output array c) and the model's state s,
   without the history; (lr, li, lim, sp) the model's initial literal pointer *)
Definition xl_rel (a: la) (e: xenv) (rb: Z) (lr: xreg) (li lim: Z) (sp: bool) (c: list val) (K j: Z) (sw: bool)
    (s: xex) : Prop :=
  xop s = a_d a + K - rb /\
  xlr s = (if sw then R_lxb else lr) /\
  xli s = (if sw then j - (a_n a - LITBUFFEREXTRASIZE) else li + j) /\
  xlim s = (if sw then LITBUFFEREXTRASIZE else lim) /\
  xsp s = (if sw then false else sp) /\
  xm_lxb (xmm s) = a_lxb a /\ dst_rel c rb (xm_dst (xmm s)) /\ xl_ok e (xmm s) (xlr s) (xli s) (xlim s).

(* the queue q executed from s *)
Fixpoint x_steps (e: xenv) (s: xex) (q: list (Z * Z * Z)) : option xex :=
  match q with
  | nil => Some s
  | (ll, ml, off) :: q' => match x_step e s ll ml off with Some s' => x_steps e s' q' | None => None end
  end.

(* what the model computes from s with k sequences left after the queue q (FSE states st, position pos,
   repeat offsets crep) *)
Definition xl_cont (a: la) (e: xenv) (t: seq_tabs) (q: list (Z * Z * Z)) (k: nat) (st: Z * Z * Z) (pos: Z)
    (crep: Z * Z * Z) (s: xex) : option (xmem * Z * (Z * Z * Z)) :=
  let '(tLL, tOF, tML) := t in
  match x_steps e s q with
  | None => None
  | Some s1 =>
      match x_seq_loop dseq_one c_offset e tLL tOF tML (iw_s (a_i a)) k st pos crep s1 with
      | None => None
      | Some (s', pos', rep') =>
          if negb (pos' =? 0) then None else
          match x_last e s' with Some (m', op') => Some (m', op', x_rep32 rep') | None => None end
      end
  end.

(* the loop invariant: executor (K, c, j, sw), decoder after id sequences (tables t; repeat offsets crep,
   bitstream at (pos, lo), states st), the queue q *)
Definition xl_inv (a: la) (t: seq_tabs) (id K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool) (pos lo: Z)
    (st: Z * Z * Z) (q: list (Z * Z * Z)) : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
    let e := xl_env a rb body ps ds de in
    (exists s, xl_rel a e rb lr li lim sp c K j sw s /\ xh_ok e (xmm s) (xop s) /\
       (id < a_nb a -> bs_ready pos lo) /\ (id = a_nb a -> pos = 0 -> lo = 0) /\
       xl_X a rb m body lr li lim sp ps ds de = xl_cont a e t q (Z.to_nat (a_nb a - id)) st pos crep s) \/
    (pos < 0 /\ xl_X a rb m body lr li lim sp ps ds de = None).

(* after the sequences (the bitstream consumed, the repeat offsets crep saved): the last literals are left *)
Definition xl_aft (a: la) (K: Z) (c: list val) (crep: Z * Z * Z) (j: Z) (sw: bool) : Prop :=
  forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
    let e := xl_env a rb body ps ds de in
    exists s, xl_rel a e rb lr li lim sp c K j sw s /\
      xl_X a rb m body lr li lim sp ps ds de =
        match x_last e s with Some (m', op') => Some (m', op', crep) | None => None end.

(* the array vd after a copy of the bytes bs to di (memmove's result) *)
Definition xl_put (vd: list val) (di: Z) (bs: list val) : list val :=
  sublist 0 di vd ++ bs ++ sublist (di + Zlength bs) (Zlength vd) vd.

(* ===================== the clause ===================== *)

Lemma xl_exact_none (a: la) (r: Z) (oc': list val) (rep': Z * Z * Z) :
  is_error_code r = true -> xl_none a ->
  seqs_exact (a_os a) (a_rep a) (a_l a) (a_lits a) (a_lxb a) (a_nb a) (a_o a) (a_i a) (a_h a) r oc' rep'.
Proof.
  intros Hr Hn rb m body bo lr li lim sp ps ds de H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  cbv zeta.
  pose proof (Hn rb m body bo lr li lim sp ps ds de ltac:(unfold xl_hyp; repeat (split; [assumption|]); assumption)) as E.
  unfold xl_X, xl_env, xl_s0 in E. rewrite E. exact Hr.
Qed.

Lemma xl_exact_some (a: la) (r: Z) (oc': list val) (rep': Z * Z * Z) :
  is_error_code r = false ->
  (forall rb m body bo lr li lim sp ps ds de, xl_hyp a rb m body bo lr li lim sp ps ds de ->
     match xl_X a rb m body lr li lim sp ps ds de with
     | None => False
     | Some (mm, op', rep2) => r = op' - (oa_d (a_o a) - rb) /\ dst_rel oc' rb (xm_dst mm) /\ rep' = rep2
     end) ->
  seqs_exact (a_os a) (a_rep a) (a_l a) (a_lits a) (a_lxb a) (a_nb a) (a_o a) (a_i a) (a_h a) r oc' rep'.
Proof.
  intros Hr Hs rb m body bo lr li lim sp ps ds de H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
  cbv zeta.
  specialize (Hs rb m body bo lr li lim sp ps ds de ltac:(unfold xl_hyp; repeat (split; [assumption|]); assumption)).
  unfold xl_X, xl_env, xl_s0 in Hs.
  destruct (x_seq_section _ _ _ _ _ _) as [[[mm op'] rep2]|]; [|contradiction].
  destruct Hs as (A & B & C). auto.
Qed.
