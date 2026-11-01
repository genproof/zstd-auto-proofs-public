(* LOOP, the split-literal loop (BlkSeqLoopSplit): its plain-Coq part.  The arguments of the call (sa), the ghosts the
   prologue fixes (sg), the loop state (sw), the loop invariants of the old clauses of seqs_spec (sinv, spend, slast)
   and of its exact clause (BlkIface.seqs_exact: xinv, xpend, xlast), and the exact steps: each piece of the body of
   ZSTD_decompressSequences_bodySplitLitBuffer keeps the exact invariant, or proves the exact clause when it returns.
   The model is model/ExBlock.v's x_seq_section (x_seqs: x_seq_loop's x_step, x_last); the C's stores are the
   mirrors of BlkSeqXMem (the exact clauses of COPY and EXEC), related to the model by the kits BlkSeqXKitL / D. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopCommon.
Require Import Coq.micromega.Lia.
Require Import Zstd.proof.model.ExBlock Zstd.proof.model.ExCSeq.
Local Open Scope logic.

(* the arguments of the call (the WITH of seqs_spec, l = LSplit lb; a_lxb: litExtraBuffer's bytes) and the four local
   variables *)
Record sa := {
  a_gv: globals; a_p: val; a_fs: fstate; a_ox: option ddx; a_os: option (fse_table * fse_table * fse_table);
  a_fe: Z; a_rep: Z * Z * Z; a_lb: Z; a_lits: list Z; a_nb: Z; a_bsm: Z; a_W: list ptr_witness;
  a_o: outarr; a_i: inwin; a_h: hctx; a_lxb: list Z;
  a_vlp: val; a_vss: val; a_vsq: val; a_vsq1: val }.

Section Derived.
Local Open Scope Z_scope.
Variable a: sa.
Definition sp_ob : val := oa_base (a_o a).
Definition sp_d : Z := oa_d (a_o a).
Definition sp_cap : Z := oa_cap (a_o a).
Definition sp_N : Z := oa_N (a_o a).
Definition sp_c0 : list val := oa_c (a_o a).
Definition sp_n : Z := Zlength (a_lits a).
(* the end of the head (the literals in the output array), = litBufferEnd while split *)
Definition sp_lim : Z := a_lb a + (sp_n - LITBUFFEREXTRASIZE).
(* the last 65536 literals, in litExtraBuffer *)
Definition sp_tail : list Z := sublist (sp_n - LITBUFFEREXTRASIZE) sp_n (a_lits a).
Definition sp_ps : Z := hc_ps (a_h a).
Definition sp_x : ext_seg := hc_ext (a_h a).
Definition sp_s : list Z := iw_s (a_i a).
(* the sequences bitstream (seqStart) *)
Definition sp_sst : val := offset_val (iw_off (a_i a)) (iw_base (a_i a)).
(* the model's history and window *)
Definition sp_hist : list Z := hc_hist (a_h a).
Definition sp_out : list Z := hc_out (a_h a).
Definition sp_ws : Z := hc_wsize (a_h a).

(* the precondition of seqs_spec is_split *)
Definition sa_ok : Prop :=
  outarr_ok (a_o a) /\ inwin_ok (a_i a) /\ lits_at (LSplit (a_lb a)) sp_c0 sp_d sp_cap (a_i a) (a_lits a) /\
  0 <= a_bsm a <= ZSTD_BLOCKSIZE_MAX /\ sp_n <= a_bsm a /\
  0 <= a_nb a <= LONGNBSEQ + 65535 /\ (a_nb a > 0 -> a_os a <> None /\ 0 < sp_cap) /\
  seqs_ok (a_os a) /\ rep_ok (a_rep a) /\ (a_fe a = 0 \/ a_fe a = 1) /\
  (sp_cap = 0 -> (pws_pred (a_W a) |-- weak_valid_pointer (offset_val sp_d sp_ob))) /\
  (0 < sp_cap -> layout_ok (a_fs a) sp_ob sp_N sp_d sp_ps sp_x) /\
  hist_ptrs_ok (a_fs a) (a_o a) sp_x /\ lit_pos (LSplit (a_lb a)) sp_d sp_cap (a_bsm a) sp_n /\
  ext0_ok (a_W a) (a_fs a) sp_x.

(* the definedness facts of seqs_spec's precondition: the history, the 32 cells after the head *)
Definition sa_dok : Prop := hist_def sp_c0 sp_d sp_ps sp_x /\ lit_slack_def (LSplit (a_lb a)) sp_c0 sp_n.

(* consequences of the PRE (lit_pos, hist_ptrs_ok; sp_pending_ok): the head literals are far enough ahead of the
   output; dictEnd is a pointer or NULL *)
Definition sp_pending : Prop :=
  sp_d + Z.min (a_bsm a) sp_cap - sp_n + WILDCOPY_OVERLENGTH <= a_lb a /\ is_pointer_or_null (fs_dictEnd (a_fs a)).
End Derived.

(* the ghosts the prologue fixes: the tables t (a_os = Some t), their pointers, shares and fastMode words, the
   two shares of the input array (a readable copy, the bitstream), the 32 bytes after the tail in litExtraBuffer *)
Record sg := {
  g_t: fse_table * fse_table * fse_table; g_tp: val * val * val; g_sht: share * share * share; g_fm: Z * Z * Z;
  g_sh1: share; g_sh2: share; g_xr: list val }.

(* what the prologue's borrowing gives: Q = the tables' resources outside zstd_globals (with the DDict's), which,
   with zstd_globals, lend the three tables (seqtabs_at) for decodeSequence and give tabs_seq back; Rin = the rest
   of the input array *)
Definition bfacts (a: sa) (g: sg) (Q Rin: mpred) : Prop :=
  let gv := a_gv a in let p := a_p a in
  a_os a = Some (g_t g) /\ seqtabs_sh_ok (g_sht g) /\
  (forall fe': Z,
     field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p (g_tp g) * Q * zstd_globals gv
     |-- tabs_seq gv p (a_ox a) (a_os a) fe' * dent_of dent_def gv (a_ox a) * zstd_globals gv) /\
  (exists R': mpred,
     (Q * zstd_globals gv |-- seqtabs_at (g_sht g) (g_t g) (g_fm g) (g_tp g) * R') /\
     (seqtabs_at (g_sht g) (g_t g) (g_fm g) (g_tp g) * R' |-- Q * zstd_globals gv)) /\
  readable_share (g_sh1 g) /\ readable_share (g_sh2 g) /\
  data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) =
    data_at (g_sh1 g) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
    bit_src (g_sh2 g) (sp_sst a) (sp_s a) * Rin /\
  Zlength (g_xr g) = WILDCOPY_OVERLENGTH /\ byte_cells (g_xr g).

(* the loop state: id sequences decoded and executed (PEND: id executed, one more decoded), the bitstream
   (pos, lo), the FSE states, the C repeat offsets (PEND: before the pending sequence), op = d + K, j literals
   consumed (litPtr = lb + j in the output array while split, else litExtraBuffer + (j - (n - 65536))), the
   output array c *)
Record sw := { w_id: Z; w_pos: Z; w_lo: Z; w_st: Z * Z * Z; w_crep: Z * Z * Z; w_K: Z; w_j: Z; w_c: list val }.

Section Inv.
Local Open Scope Z_scope.
Variable a: sa.

(* the model's success, as the model clause of seqs_spec assumes it (0 < cap here) *)
Definition model_hyp (t: fse_table * fse_table * fse_table) (seqs: list sequence) (out' lits': list Z)
    (rep2: Z * Z * Z) : Prop :=
  let '(tLL, tOF, tML) := t in
  hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
  ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
  decode_seq_stream tLL tOF tML (sp_s a) (a_nb a) = Some seqs /\
  exec_seqs (sp_ws a) (a_rep a) (sp_hist a) (a_lits a) (sp_out a) seqs = Some (out', lits', rep2) /\
  Zlength out' - Zlength (sp_out a) + Zlength lits' <= a_bsm a.

(* the block's content length when the model succeeds *)
Definition cntlen (out' lits': list Z) : Z := Zlength out' - Zlength (sp_out a) + Zlength lits'.

(* what the executors read is defined (memcpy and memmove are libc.c's byte loops): the history before dst,
   the extDict, the head of the literals with the 32 cells after it; and the bytes written so far *)
Definition sp_dfd (K: Z) (c: list val) : Prop :=
  Forall is_byte_val (sublist (sp_d a) (sp_d a + K) c) /\ Forall is_byte_val (sublist (sp_ps a) (sp_d a) c) /\
  ext_def (sp_x a) c /\ Forall is_byte_val (sublist (a_lb a) (sp_lim a + WILDCOPY_OVERLENGTH) c).

(* model-free facts of the output: op within the capacity; what was written; the written bytes and what the
   executors read are defined.  While split (ph = true) nothing at or after max(op, litPtr) was written. *)
Definition sp_outok (ph: bool) (K j: Z) (c: list val) : Prop :=
  0 <= K <= sp_cap a /\ Zlength c = sp_N a /\
  (if ph
   then 0 <= j <= sp_n a - LITBUFFEREXTRASIZE /\
        unchanged_outside (sp_c0 a) c (sp_d a)
          (Z.min (sp_d a + Z.min (sp_cap a) (K + WILDCOPY_OVERLENGTH)) (Z.max (sp_d a + K) (a_lb a + j)))
   else sp_n a - LITBUFFEREXTRASIZE <= j <= sp_n a /\
        unchanged_outside (sp_c0 a) c (sp_d a) (sp_d a + Z.min (sp_cap a) (K + WILDCOPY_OVERLENGTH))) /\
  sp_dfd K c /\
  (byte_cells (sp_c0 a) -> byte_cells (iw_c (a_i a)) -> ext_bytes (sp_x a) -> byte_cells c).

(* the model part at a loop head: the C decodes the model's remaining sequences; the model executes the
   remaining sequences from the C's repeat offsets, after the block bytes blk (|blk| = K), which are the
   output's when the content fits the capacity *)
Definition sp_minv (t: fse_table * fse_table * fse_table) (w: sw) : Prop :=
  forall seqs out' lits' rep2, model_hyp t seqs out' lits' rep2 ->
    (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := w_st w in
     decode_seqs tLL tOF tML (sp_s a) (Z.to_nat (a_nb a - w_id w)) sLL sOF sML (w_pos w) =
       Some (skipn (Z.to_nat (w_id w)) seqs, 0)) /\
    (w_id w < a_nb a -> bs_ready (w_pos w) (w_lo w)) /\ (w_id w = a_nb a -> w_lo w = 0) /\
    exists blk, Zlength blk = w_K w /\
      exec_seqs (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
        (skipn (Z.to_nat (w_id w)) seqs) = Some (out', lits', rep2) /\
      (cntlen out' lits' <= sp_cap a -> sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk).

(* the loop invariant (ph: still split) *)
Definition sinv (t: fse_table * fse_table * fse_table) (ph: bool) (w: sw) : Prop :=
  0 <= w_id w <= a_nb a /\ (ph = false -> 1 <= w_id w) /\
  0 <= w_lo w /\ bcons (w_pos w) (w_lo w) + DSEQ_BITS * (a_nb a - w_id w) <= Int.max_unsigned /\
  states_ok t (w_st w) /\ rep_ok (w_crep w) /\
  sp_outok ph (w_K w) (w_j w) (w_c w) /\ sp_minv t w.

(* after decoding sequence number id (ll, ml, ov): the new bitstream state and FSE states are in w; w_crep is
   still the repeat offsets before it *)
Definition spend (t: fse_table * fse_table * fse_table) (ph: bool) (w: sw) (ll ml ov: Z) : Prop :=
  0 <= w_id w < a_nb a /\ (ph = false -> 1 <= w_id w) /\
  0 <= w_lo w /\ bcons (w_pos w) (w_lo w) + DSEQ_BITS * (a_nb a - w_id w - 1) <= Int.max_unsigned /\
  states_ok t (w_st w) /\ rep_ok (w_crep w) /\
  0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= ov < 2 ^ 32 /\
  sp_outok ph (w_K w) (w_j w) (w_c w) /\
  forall seqs out' lits' rep2, model_hyp t seqs out' lits' rep2 ->
    exists sq,
      skipn (Z.to_nat (w_id w)) seqs = sq :: skipn (Z.to_nat (w_id w + 1)) seqs /\
      sq_ll sq = ll /\ sq_ml sq = ml /\ sq_ov sq = ov /\
      (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := w_st w in
       decode_seqs tLL tOF tML (sp_s a) (Z.to_nat (a_nb a - w_id w - 1)) sLL sOF sML (w_pos w) =
         Some (skipn (Z.to_nat (w_id w + 1)) seqs, 0)) /\
      (w_id w + 1 < a_nb a -> bs_ready (w_pos w) (w_lo w)) /\ (w_id w + 1 = a_nb a -> w_lo w = 0) /\
      exists blk, Zlength blk = w_K w /\
        exec_seqs (sp_ws a) (w_crep w) (sp_hist a) (skipn (Z.to_nat (w_j w)) (a_lits a)) (sp_out a ++ blk)
          (skipn (Z.to_nat (w_id w)) seqs) = Some (out', lits', rep2) /\
        (cntlen out' lits' <= sp_cap a -> sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk).

(* before the last literals: rep' are the repeat offsets saved in the context *)
Definition slast (ph: bool) (w: sw) (rep': Z * Z * Z) : Prop :=
  rep_ok rep' /\ sp_outok ph (w_K w) (w_j w) (w_c w) /\ (a_nb a = 0 -> rep' = a_rep a) /\
  (sp_cap a = 0 \/
   (hist_view (sp_c0 a) (sp_d a) (sp_ps a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a) /\
    ext_clear (sp_d a) (sp_ps a) (sp_cap a) (a_bsm a) (sp_x a) (sp_hist a) (sp_out a) (sp_ws a)) ->
   forall cnt rep2,
     seqs_model (a_os a) (sp_s a) (a_nb a) (a_rep a) (sp_hist a) (sp_out a) (a_lits a) (sp_ws a) = Some (cnt, rep2) ->
     Zlength cnt <= a_bsm a ->
     exists blk, Zlength blk = w_K w /\ cnt = blk ++ skipn (Z.to_nat (w_j w)) (a_lits a) /\ rep2 = rep' /\
       (Zlength cnt <= sp_cap a -> sublist (sp_d a) (sp_d a + w_K w) (w_c w) = zbytes blk)).

(* litPtr and litBufferEnd *)
Definition sp_lp (ph: bool) (j: Z) : val :=
  if ph then offset_val (a_lb a + j) (sp_ob a)
  else offset_val (j - (sp_n a - LITBUFFEREXTRASIZE)) (lit_extra (a_p a)).
Definition sp_lbe (ph: bool) : val :=
  if ph then offset_val (sp_lim a) (sp_ob a) else offset_val LITBUFFEREXTRASIZE (lit_extra (a_p a)).
Definition sp_loc (ph: bool) : Z := if ph then LOC_SPLIT else LOC_NOT_IN_DST.
End Inv.

(* ===================================================================== *)
(* the exact outcome (BlkIface.seqs_exact): the model of model/ExBlock.v (x_seq_section) followed forwards.
   For each region m of the output array at rb and block body at bo that seqs_exact quantifies over (xhyp), the
   loop states carry a model state s (xex) related to the C's (xrel) and the model's outcome is the
   continuation of the model from s (xcont); or the bitstream has overflowed (position below 0: the model has
   failed and BIT_endOfDStream will fail). *)
Section Exact.
Local Open Scope Z_scope.
Variable a: sa.

(* seqs_exact's hypotheses for the split literals at lb (litloc_rel: R_dst, li = lb - rb, lim = sp_lim - rb) *)
Definition xhyp (rb: Z) (m: list (option Z)) (body: list Z) (bo ps ds de: Z) : Prop :=
  hc_region (a_h a) rb = Some (ps, ds, de) /\ 0 <= rb <= sp_d a /\ dst_rel (sp_c0 a) rb m /\
  (forall j, ps <= j < sp_d a - rb \/ ds <= j < de -> nth (Z.to_nat j) m None <> None) /\
  0 <= bo /\ bo + Zlength body <= iw_N (a_i a) /\ sublist bo (bo + Zlength body) (iw_c (a_i a)) = zbytes body /\
  0 <= ps /\ 0 <= ds /\ 0 <= a_lb a - rb /\
  (forall j, a_lb a - rb <= j < sp_lim a - rb + WILDCOPY_OVERLENGTH -> nth (Z.to_nat j) m None <> None).

(* seqs_exact's environment and initial state *)
Definition xenv_a (rb: Z) (body: list Z) (ps ds de: Z) : xenv :=
  {| xe_src := body; xe_ps := ps; xe_vs := ps - (de - ds); xe_de := de; xe_oend := sp_d a + sp_cap a - rb |}.
Definition xs0_a (rb: Z) (m: list (option Z)) : xex :=
  {| xmm := {| xm_dst := m; xm_lxb := a_lxb a |}; xop := sp_d a - rb; xlr := R_dst; xli := a_lb a - rb;
     xlim := sp_lim a - rb; xsp := true |}.

(* the model's outcome *)
Definition xres_a (rb: Z) (m: list (option Z)) (body: list Z) (ps ds de: Z) : option (xmem * Z * (Z * Z * Z)) :=
  x_seq_section (xenv_a rb body ps ds de) (a_os a) (a_rep a) (sp_s a) (a_nb a) (xs0_a rb m).

(* the rest of x_seqs from the loop state (k sequences left, FSE states st, position pos, repeat offsets rep,
   execution state s) *)
Definition xcont (e: xenv) (t: seq_tabs) (k: nat) (st: Z * Z * Z) (pos: Z) (rep: Z * Z * Z) (s: xex)
    : option (xmem * Z * (Z * Z * Z)) :=
  let '(tLL, tOF, tML) := t in
  match x_seq_loop dseq_one c_offset e tLL tOF tML (sp_s a) k st pos rep s with
  | None => None
  | Some (s', pos', rep') =>
      if negb (pos' =? 0) then None else
      match x_last e s' with Some (mm, op) => Some (mm, op, x_rep32 rep') | None => None end
  end.

(* the model's execution state s is the C's at op = d + K with j literals consumed (ph: still split, the literal
   pointer in the head in dst; else in litExtraBuffer); the written cells of its region are the C's output array's,
   the history and the literals it reads are written *)
Definition xrel (e: xenv) (rb: Z) (ph: bool) (w: sw) (s: xex) : Prop :=
  xop s = sp_d a - rb + w_K w /\
  (if ph then xlr s = R_dst /\ xli s = a_lb a - rb + w_j w /\ xlim s = sp_lim a - rb /\ xsp s = true
   else xlr s = R_lxb /\ xli s = w_j w - (sp_n a - LITBUFFEREXTRASIZE) /\ xlim s = LITBUFFEREXTRASIZE /\
        xsp s = false) /\
  xm_lxb (xmm s) = a_lxb a /\ dst_rel (w_c w) rb (xm_dst (xmm s)) /\
  xh_ok e (xmm s) (xop s) /\ xl_ok e (xmm s) (xlr s) (xli s) (xlim s).

(* at a loop head (cl: the cells of litExtraBuffer) *)
Definition xinv (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) : Prop :=
  cl = zbytes (a_lxb a) /\ Zlength (a_lxb a) = LITEXTRA_N /\
  forall rb m body bo ps ds de, xhyp rb m body bo ps ds de ->
    let e := xenv_a rb body ps ds de in
    (exists s, xres_a rb m body ps ds de = xcont e t (Z.to_nat (a_nb a - w_id w)) (w_st w) (w_pos w) (w_crep w) s /\
       xrel e rb ph w s /\ (w_id w < a_nb a -> bs_ready (w_pos w) (w_lo w)) /\
       (w_id w = a_nb a -> w_pos w = 0 -> w_lo w = 0)) \/
    (w_pos w < 0 /\ xres_a rb m body ps ds de = None).

(* after the decode of sequence number id (ll, ml, ov), before its execution (w: the new bitstream position and
   states, w_crep still the repeat offsets before it) *)
Definition xpend (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) (ll ml ov: Z) : Prop :=
  cl = zbytes (a_lxb a) /\ Zlength (a_lxb a) = LITEXTRA_N /\
  forall rb m body bo ps ds de, xhyp rb m body bo ps ds de ->
    let e := xenv_a rb body ps ds de in
    (exists s, xres_a rb m body ps ds de =
         match x_step e s ll ml (fst (c_offset (w_crep w) ll ov)) with
         | None => None
         | Some s' => xcont e t (Z.to_nat (a_nb a - w_id w - 1)) (w_st w) (w_pos w) (snd (c_offset (w_crep w) ll ov)) s'
         end /\
       xrel e rb ph w s /\ (w_id w + 1 < a_nb a -> bs_ready (w_pos w) (w_lo w)) /\
       (w_id w + 1 = a_nb a -> w_pos w = 0 -> w_lo w = 0)) \/
    (w_pos w < 0 /\ xres_a rb m body ps ds de = None).

(* before the last literals: rep' the repeat offsets saved *)
Definition xlast (cl: list val) (ph: bool) (w: sw) (rep': Z * Z * Z) : Prop :=
  cl = zbytes (a_lxb a) /\ Zlength (a_lxb a) = LITEXTRA_N /\
  forall rb m body bo ps ds de, xhyp rb m body bo ps ds de ->
    let e := xenv_a rb body ps ds de in
    exists s, xres_a rb m body ps ds de = match x_last e s with Some (mm, op) => Some (mm, op, rep') | None => None end /\
      xrel e rb ph w s.

(* the exact clause of the postcondition *)
Definition xpost (r: Z) (oc': list val) (rep': Z * Z * Z) : Prop :=
  seqs_exact (a_os a) (a_rep a) (LSplit (a_lb a)) (a_lits a) (a_lxb a) (a_nb a) (a_o a) (a_i a) (a_h a) r oc' rep'.
End Exact.

(* ===================================================================== *)
(* the exact steps (plain Coq): each piece of the body keeps the exact invariant, or proves the exact clause of the
   postcondition (xpost) when it returns *)
Section XSteps.
Local Open Scope Z_scope.

(* the postcondition's exact clause from its instance for each region *)
Lemma xpost_intro (a: sa) (r: Z) (oc': list val) (rep': Z * Z * Z) :
  (forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de ->
     match xres_a a rb m body ps ds de with
     | None => is_error_code r = true
     | Some (mm, op', rep2) =>
         is_error_code r = false /\ r = op' - (sp_d a - rb) /\ dst_rel oc' rb (xm_dst mm) /\ rep' = rep2
     end) ->
  xpost a r oc' rep'.
Proof.
  intros H. unfold xpost, seqs_exact. intros rb m body bo lr li lim sp ps ds de Hreg Hrb Hdr Hhw Hbo Hbn Hbs Hll Hps Hds Hli Hlw Hsrc.
  cbn [litloc_rel] in Hll. destruct Hll as (-> & Hlb & Hlim & ->).
  assert (Hx: xhyp a rb m body bo ps ds de).
  { unfold xhyp. unfold sp_d, sp_c0, sp_lim, sp_n. repeat split; auto; try lia.
    intros j Hj. apply (Hlw eq_refl). lia. }
  specialize (H _ _ _ _ _ _ _ Hx). unfold xres_a, xenv_a, xs0_a in H.
  replace (a_lb a - rb) with li in H by lia.
  replace (sp_lim a - rb) with lim in H by (unfold sp_lim, sp_n; lia).
  exact H.
Qed.

(* an error return where the model fails *)
Lemma xpost_err (a: sa) (r: Z) (oc': list val) (rep': Z * Z * Z) :
  is_error_code r = true ->
  (forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None) ->
  xpost a r oc' rep'.
Proof.
  intros Her H. apply xpost_intro. intros rb m body bo ps ds de Hx. rewrite (H _ _ _ _ _ _ _ Hx). exact Her.
Qed.

(* the initial state of the model is the C's before the first sequence (op = dst, the literal pointer at the head
   of the literals in dst): the history it reads is written (prefixStart <= dst and the extDict, layout_ok, which
   holds since the split literals give a positive capacity), and so are the head literals with their 32 cells *)
Lemma xrel0 (a: sa) (w: sw) (rb: Z) (m: list (option Z)) (body: list Z) (bo ps ds de: Z) :
  sa_ok a -> xhyp a rb m body bo ps ds de -> w_K w = 0 -> w_j w = 0 -> w_c w = sp_c0 a ->
  xrel a (xenv_a a rb body ps ds de) rb true w (xs0_a a rb m).
Proof.
  intros Hok Hx HK Hj Hc.
  destruct Hok as (_ & _ & Hlits & _ & _ & _ & _ & _ & _ & _ & _ & Hlay & _).
  unfold lits_at in Hlits. cbv zeta in Hlits.
  destruct Hlits as (_ & _ & Hn & Hdlb & Hlbc & _).
  assert (Hcap: 0 < sp_cap a) by (unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  specialize (Hlay Hcap). destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Hx as (Hreg & Hrb & Hdr & Hhw & _ & _ & _ & Hps0 & Hds0 & Hli & Hlw).
  unfold xrel, xenv_a, xs0_a. cbn [xop xlr xli xlim xsp xmm xm_lxb xm_dst].
  rewrite HK, Hj, Hc.
  assert (Hde: ds <= de /\ ps = sp_ps a - rb).
  { unfold hc_region in Hreg. unfold sp_ps, sp_x in *.
    destruct (hc_ext (a_h a)) as [|e1 elen|sh eb en ec e1 elen]; inversion Hreg; subst; cbn [ext_len] in *; lia. }
  split; [lia|]. split; [repeat split; lia|]. split; [reflexivity|]. split; [exact Hdr|]. split.
  - unfold xh_ok. cbn [xe_ps xe_vs xe_de]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    + intros j Hj'. split; [lia|]. apply Hhw. lia.
    + intros j Hj'. split; [lia|]. apply Hhw. lia.
  - unfold xl_ok. unfold sp_lim, sp_n. split; [unfold LITBUFFEREXTRASIZE in *; lia|].
    intros j Hj'. split; [lia|]. apply Hlw. unfold sp_lim, sp_n. lia.
Qed.

(* BIT_initDStream fails (no well-formed stream): so does the model *)
Lemma xinit_err (a: sa) (t: seq_tabs) :
  a_os a = Some t -> 0 < a_nb a -> bs_wf (sp_s a) = false ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros Hos Hnb Hwf rb m body bo ps ds de _.
  unfold xres_a, x_seq_section. rewrite (proj2 (Z.eqb_neq (a_nb a) 0) ltac:(lia)), Hos.
  destruct t as [[tLL tOF] tML]. unfold xb_seqs, x_seqs.
  assert (Hok: bs_okb (sp_s a) = false).
  { unfold bs_wf in Hwf. unfold bs_okb.
    apply andb_false_iff in Hwf as [Hz | Hl].
    - apply negb_false_iff, Z.eqb_eq in Hz. rewrite Zlength_correct in Hz.
      assert (length (sp_s a) = 0%nat) as -> by lia. rewrite andb_false_r. reflexivity.
    - rewrite Hl, andb_false_r. reflexivity. }
  rewrite Hok. reflexivity.
Qed.

(* BIT_initDStream and the three ZSTD_initFseState: the model's first reads (Block.rd), or a position below 0 *)
Lemma xinit (a: sa) (t: seq_tabs) (cl: list val) (v1 v2 v3: Z) :
  sa_ok a -> a_os a = Some t -> 0 < a_nb a -> bs_wf (sp_s a) = true ->
  cl = zbytes (a_lxb a) -> Zlength (a_lxb a) = LITEXTRA_N ->
  let '(tLL, tOF, tML) := t in
  let pos0 := bs_total (sp_s a) in let lo0 := 8 * Z.max 0 (Zlength (sp_s a) - 8) in
  let pos1 := pos0 - ft_log tLL in let lo1 := snd (bs_reload pos1 lo0) in
  let pos2 := pos1 - ft_log tOF in let lo2 := snd (bs_reload pos2 lo1) in
  let pos3 := pos2 - ft_log tML in let lo3 := snd (bs_reload pos3 lo2) in
  (lo0 <= pos1 -> v1 = bs_peek (bs_value (sp_s a)) pos0 (ft_log tLL)) ->
  (lo1 <= pos2 -> v2 = bs_peek (bs_value (sp_s a)) pos1 (ft_log tOF)) ->
  (lo2 <= pos3 -> v3 = bs_peek (bs_value (sp_s a)) pos2 (ft_log tML)) ->
  xinv a t cl true {| w_id := 0; w_pos := pos3; w_lo := lo3; w_st := (v1, v2, v3); w_crep := a_rep a; w_K := 0;
                      w_j := 0; w_c := sp_c0 a |}.
Proof.
  intros Hok Hos Hnb Hwf Hcl Hlx.
  destruct t as [[tLL tOF] tML]. cbv zeta. intros H1 H2 H3.
  assert (Hb: bytes_ok (sp_s a)).
  { destruct Hok as (_ & Hi & _). destruct Hi as (_ & _ & _ & _ & _ & _ & Hb & _). exact Hb. }
  assert (Hts: fse_ok KLL tLL /\ fse_ok KOF tOF /\ fse_ok KML tML).
  { destruct Hok as (_ & _ & _ & _ & _ & _ & _ & Hs & _). rewrite Hos in Hs. exact Hs. }
  destruct Hts as ([HlLL _] & [HlOF _] & [HlML _]).
  cbn [sk_maxlog] in HlLL, HlOF, HlML. unfold LLFSELog, OffFSELog, MLFSELog in *.
  assert (Hokb: bs_okb (sp_s a) = true).
  { revert Hwf. unfold bs_okb, bs_wf.
    replace (forallb (fun b => andb (0 <=? b) (b <? 256)) (sp_s a)) with true.
    2:{ symmetry. apply forallb_forall. intros x Hx. unfold bytes_ok in Hb. rewrite Forall_forall in Hb.
        apply Hb in Hx. unfold is_byte in Hx. lia. }
    rewrite Zlength_correct. destruct (length (sp_s a)); cbn; auto. }
  split; [exact Hcl|]. split; [exact Hlx|].
  intros rb m body bo ps ds de Hx. cbv zeta.
  cbn [w_id w_pos w_lo w_st w_crep].
  rewrite Z.sub_0_r.
  assert (Hres: xres_a a rb m body ps ds de =
    let e := xenv_a a rb body ps ds de in
    match rd (sp_s a) (bs_total (sp_s a)) (ft_log tLL) with None => None | Some (sLL, pos) =>
    match rd (sp_s a) pos (ft_log tOF) with None => None | Some (sOF, pos) =>
    match rd (sp_s a) pos (ft_log tML) with None => None | Some (sML, pos) =>
      xcont a e (tLL, tOF, tML) (Z.to_nat (a_nb a)) (sLL, sOF, sML) pos (a_rep a) (xs0_a a rb m)
    end end end).
  { unfold xres_a, x_seq_section. rewrite (proj2 (Z.eqb_neq (a_nb a) 0) ltac:(lia)), Hos.
    unfold xb_seqs, x_seqs. rewrite Hokb. cbn [negb]. reflexivity. }
  rewrite Hres. clear Hres. cbv zeta. unfold rd.
  destruct (Z_lt_le_dec (bs_total (sp_s a) - ft_log tLL - ft_log tOF - ft_log tML) 0) as [Hneg|Hpos].
  - right. split; [exact Hneg|].
    destruct (bs_total (sp_s a) - ft_log tLL <? 0); [reflexivity|].
    destruct (bs_total (sp_s a) - ft_log tLL - ft_log tOF <? 0); [reflexivity|].
    rewrite (proj2 (Z.ltb_lt _ 0) Hneg). reflexivity.
  - left. exists (xs0_a a rb m).
    rewrite (proj2 (Z.ltb_ge (bs_total (sp_s a) - ft_log tLL) 0) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge (bs_total (sp_s a) - ft_log tLL - ft_log tOF) 0) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge (bs_total (sp_s a) - ft_log tLL - ft_log tOF - ft_log tML) 0) ltac:(lia)).
    pose proof (lim_init (sp_s a) Hb Hwf) as I0.
    destruct (lim_step _ _ (ft_log tLL) I0 ltac:(lia) ltac:(lia)) as [L1 I1].
    destruct (lim_step _ _ (ft_log tOF) I1 ltac:(lia) ltac:(lia)) as [L2 I2].
    destruct (lim_step _ _ (ft_log tML) I2 ltac:(lia) ltac:(lia)) as [L3 I3].
    rewrite <- (lim_peek (sp_s a) (bs_total (sp_s a)) _ (ft_log tLL) v1 Hb ltac:(lia) ltac:(lia) H1 L1).
    rewrite <- (lim_peek (sp_s a) (bs_total (sp_s a) - ft_log tLL) _ (ft_log tOF) v2 Hb ltac:(lia) ltac:(lia) H2 L2).
    rewrite <- (lim_peek (sp_s a) (bs_total (sp_s a) - ft_log tLL - ft_log tOF) _ (ft_log tML) v3 Hb ltac:(lia) ltac:(lia) H3 L3).
    split; [reflexivity|]. split.
    + apply xrel0 with (bo := bo); auto.
    + split; [intros _; apply I3 | intros Hz; lia].
Qed.

(* ZSTD_decodeSequence (DEC's clauses: exact when the model's step succeeds, the position below 0 when it fails) *)
Lemma xdec (a: sa) (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) (pos' lo': Z) (st': Z * Z * Z)
    (ll ml ov: Z) :
  seqs_ok (Some t) -> sinv a t ph w -> xinv a t cl ph w -> w_id w < a_nb a ->
  w_lo w mod 8 = 0 -> w_pos w <= w_lo w + 64 ->
  w_pos w - DSEQ_BITS <= pos' <= w_pos w -> 0 <= lo' <= w_lo w ->
  ((a_nb a - w_id w =? 1) = true -> st' = w_st w) ->
  (bs_ready (w_pos w) (w_lo w) ->
   forall sq stn pn,
     (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := w_st w in
      dseq_one tLL tOF tML (sp_s a) (a_nb a - w_id w =? 1) sLL sOF sML (w_pos w)) = Some (sq, stn, pn) ->
     ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
     ((a_nb a - w_id w =? 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
  ((let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := w_st w in
    dseq_one tLL tOF tML (sp_s a) (a_nb a - w_id w =? 1) sLL sOF sML (w_pos w)) = None -> pos' < 0) ->
  xpend a t cl ph (Build_sw (w_id w) pos' lo' st' (w_crep w) (w_K w) (w_j w) (w_c w)) ll ml ov.
Proof.
  destruct w as [id pos lo st crep K j c]. cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c].
  intros Hso Hinv Hx Hid H8 Hplo Hpos' Hlo' Hlast Hspec Hnone.
  destruct Hinv as (Hid0 & Hph & H0lo & Hbc & Hst & Hrep & Hout & Hminv).
  cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in *.
  destruct Hx as (Hcl & Hlen & Hx). unfold xpend. split; [exact Hcl|]. split; [exact Hlen|].
  intros rb m body bo ps ds de Hh. cbv zeta.
  destruct (Hx rb m body bo ps ds de Hh) as [(s & Hres & Hrel & Hrdy & _) | (Hneg & Hres)];
    cbn [w_id w_pos w_lo w_st w_crep w_K w_j w_c] in *.
  2:{ right. split; [lia | exact Hres]. }
  specialize (Hrdy Hid).
  destruct t as [[tLL tOF] tML]; destruct st as [[sLL sOF] sML].
  destruct Hso as (HfLL & HfOF & HfML). destruct Hst as (HsLL & HsOF & HsML).
  cbv beta iota zeta in Hspec, Hnone.
  assert (Hk: Z.to_nat (a_nb a - id) = S (Z.to_nat (a_nb a - id - 1))) by lia.
  assert (Hle: Nat.eqb (Z.to_nat (a_nb a - id - 1)) 0 = (a_nb a - id =? 1)).
  { destruct (Nat.eqb_spec (Z.to_nat (a_nb a - id - 1)) 0); destruct (Z.eqb_spec (a_nb a - id) 1); lia. }
  unfold xcont in Hres |- *. rewrite Hk in Hres. cbn [x_seq_loop] in Hres. rewrite Hle in Hres.
  destruct (dseq_one tLL tOF tML (sp_s a) (a_nb a - id =? 1) sLL sOF sML pos) as [[[sq stn] pn]|] eqn:Hone.
  2:{ right. split; [apply Hnone; reflexivity | exact Hres]. }
  destruct (Hspec Hrdy sq stn pn eq_refl) as (-> & -> & -> & -> & Hnl).
  left. exists s. split.
  - rewrite Hres. destruct (c_offset crep (sq_ll sq) (sq_ov sq)) as [off rep'] eqn:Hco. cbn [fst snd].
    destruct (x_step _ s (sq_ll sq) (sq_ml sq) off) as [s'|]; [|reflexivity].
    destruct (a_nb a - id =? 1) eqn:EL.
    + apply Z.eqb_eq in EL. replace (Z.to_nat (a_nb a - id - 1)) with O by lia. reflexivity.
    + destruct (Hnl eq_refl) as [-> _]. reflexivity.
  - split; [exact Hrel|]. split.
    + intros Hlt. assert (EL: (a_nb a - id =? 1) = false) by (apply Z.eqb_neq; lia).
      exact (proj2 (Hnl EL)).
    + intros Heq Hp0. subst pn. assert (EL: (a_nb a - id =? 1) = true) by (apply Z.eqb_eq; lia).
      rewrite EL in Hone.
      eapply (loop_end_lo tLL tOF tML (sp_s a) sLL sOF sML pos lo lo' sq stn); eauto.
Qed.

(* ---------- the execution steps: helpers ----------
   The model's region is the output array from rb: the model's positions are the C's minus rb.  Its prefixStart
   and virtualStart are the C's (hc_region); its dictEnd is the C's except without an extDict, where the model
   takes prefixStart and the C's mirror functions take 0 (ext_end): no match reads it then, an offset beyond
   oLitEnd - prefixStart being an error.  A separate extDict has no region (xhyp fails). *)

(* two comparisons at the same distance *)
Lemma xs_ltb_shift (x y x' y': Z) : x' - x = y' - y -> (x <? y) = (x' <? y').
Proof. intros H. destruct (Z.ltb_spec x y), (Z.ltb_spec x' y'); auto; lia. Qed.

Lemma xs_coords (a: sa) rb m body bo ps ds de :
  xhyp a rb m body bo ps ds de ->
  rb + ps = sp_ps a /\ rb + (ps - (de - ds)) = sp_ps a - ext_len (sp_x a) /\
  (rb + de = ext_end (sp_x a) \/ ext_len (sp_x a) = 0).
Proof.
  intros [H _]. unfold hc_region in H. unfold sp_ps, sp_x.
  destruct (hc_ext (a_h a)); inversion H; subst; cbn [ext_len ext_end].
  - split; [lia|]. split; [lia|]. right; reflexivity.
  - split; [lia|]. split; [lia|]. left; lia.
Qed.

(* the C's case analysis on the extDict, in a region *)
Lemma xs_notsep (a: sa) rb m body bo ps ds de (P Q: Prop) :
  xhyp a rb m body bo ps ds de -> match sp_x a with ExtSep _ _ _ _ _ _ => P | _ => Q end -> Q.
Proof.
  intros [H _]. unfold hc_region in H. unfold sp_x. destruct (hc_ext (a_h a)); auto. discriminate.
Qed.

(* the bounds the steps need: the region inside the output array, the head of the literals ends 32 bytes before
   the output end, the input array's length *)
Lemma xs_facts (a: sa) rb m body bo ps ds de :
  sa_ok a -> xhyp a rb m body bo ps ds de ->
  0 <= rb <= sp_d a /\ sp_d a + sp_cap a <= sp_N a /\ sp_lim a + WILDCOPY_OVERLENGTH <= sp_d a + sp_cap a /\
  Zlength (iw_c (a_i a)) = iw_N (a_i a).
Proof.
  intros (Ho & Hi & Hla & _) Hx. destruct Hx as (_ & Hrb & _).
  destruct Ho as (_ & _ & _ & Hd & Hc & HN). unfold inwin_ok, win_ok in Hi. destruct Hi as (_ & _ & _ & _ & HcN & _).
  unfold lits_at in Hla. destruct Hla as (_ & _ & _ & _ & Hlb & _).
  unfold sp_lim, sp_n, sp_d, sp_cap, sp_N in *. lia.
Qed.

(* the error conditions of the executors in the model's coordinates are the C's *)
Lemma xs_split_err_eq (a: sa) rb m body bo ps ds de (op li k lic ll ml off: Z) :
  xhyp a rb m body bo ps ds de -> rb + op = k -> rb + li = lic ->
  xsplit_err (xenv_a a rb body ps ds de) op li ll ml off =
  exec_split_err k (sp_d a + sp_cap a) lic ll ml off (sp_ps a) (ext_len (sp_x a)).
Proof.
  intros Hx Hk Hl. destruct (xs_coords a rb m body bo ps ds de Hx) as (E1 & E2 & _).
  unfold xsplit_err, exec_split_err, xenv_a. cbn [xe_oend xe_vs].
  apply f_equal2; [apply f_equal2; [|apply f_equal2]|]; apply xs_ltb_shift; lia.
Qed.

Lemma xs_exec_err_eq (a: sa) rb m body bo ps ds de (op k li llim li' llim' ll ml off: Z) :
  xhyp a rb m body bo ps ds de -> rb + op = k -> llim - li = llim' - li' ->
  xexec_err (xenv_a a rb body ps ds de) op li llim ll ml off =
  exec_err k (sp_d a + sp_cap a) li' llim' ll ml off (sp_ps a) (ext_len (sp_x a)).
Proof.
  intros Hx Hk Hl. destruct (xs_coords a rb m body bo ps ds de Hx) as (E1 & E2 & _).
  unfold xexec_err, exec_err, xenv_a. cbn [xe_oend xe_vs].
  apply f_equal2; [apply f_equal2|]; apply xs_ltb_shift; lia.
Qed.

Lemma xs_split_err_off (k e li ll ml off ps elen: Z) :
  exec_split_err k e li ll ml off ps elen = false -> off <= k + ll - ps + elen.
Proof. unfold exec_split_err. intros H. apply orb_false_iff in H as [_ H]. apply Z.ltb_ge in H. lia. Qed.

Lemma xs_exec_err_ok (k e li lim ll ml off ps elen: Z) :
  exec_err k e li lim ll ml off ps elen = false -> ll + ml <= e - k /\ ll <= lim - li /\ off <= k + ll - ps + elen.
Proof.
  unfold exec_err. intros H. apply orb_false_iff in H as [H H3]. apply orb_false_iff in H as [H1 H2].
  apply Z.ltb_ge in H1, H2, H3. lia.
Qed.

(* the match does not read dictEnd when the offset stays within the prefix *)
Lemma xs_lmatch_de (ps vs de de' oLitEnd ml off: Z) (c: list val) (wo: option Z) :
  off <= oLitEnd - ps -> lmatch ps vs de c oLitEnd ml off wo = lmatch ps vs de' c oLitEnd ml off wo.
Proof. intros H. unfold lmatch. destruct (Z.gtb_spec off (oLitEnd - ps)); [lia|reflexivity]. Qed.

Lemma xs_lexec_de (ps vs de de' oend: Z) (c: list val) (op: Z) (s: lsrc) (li llim ll ml off: Z) :
  off <= op + ll - ps -> lexec ps vs de oend c op s li llim ll ml off = lexec ps vs de' oend c op s li llim ll ml off.
Proof. intros H. unfold lexec. destruct ((_ || _)%bool); apply xs_lmatch_de; lia. Qed.

Lemma xs_lexec_split_de (ps vs de de' oend: Z) (c: list val) (op li llim ll ml off: Z) :
  off <= op + ll - ps ->
  lexec_split ps vs de oend c op li llim ll ml off = lexec_split ps vs de' oend c op li llim ll ml off.
Proof. intros H. unfold lexec_split. destruct ((_ || _)%bool); apply xs_lmatch_de; lia. Qed.

(* the mirrors of the kits (region coordinates) are the C's stores (array offsets) *)
Lemma xs_lexec_eq (a: sa) rb m body bo ps ds de (c: list val) (op k: Z) (s: lsrc) (li llim ll ml off: Z) :
  xhyp a rb m body bo ps ds de -> rb + op = k -> off <= k + ll - sp_ps a + ext_len (sp_x a) ->
  let e := xenv_a a rb body ps ds de in
  lexec (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + op) s li llim ll ml off =
  lexec (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) c k s li llim ll ml off.
Proof.
  intros Hx Hk Ho. destruct (xs_coords a rb m body bo ps ds de Hx) as (E1 & E2 & E3).
  cbv zeta. unfold xenv_a. cbn [xe_ps xe_vs xe_de xe_oend]. rewrite E1, E2, Hk.
  replace (rb + (sp_d a + sp_cap a - rb)) with (sp_d a + sp_cap a) by lia.
  destruct E3 as [E3|E3]; [rewrite E3; reflexivity|]. apply xs_lexec_de. lia.
Qed.

Lemma xs_lexec_split_eq (a: sa) rb m body bo ps ds de (c: list val) (op k li llim ll ml off: Z) :
  xhyp a rb m body bo ps ds de -> rb + op = k -> off <= k + ll - sp_ps a + ext_len (sp_x a) ->
  let e := xenv_a a rb body ps ds de in
  lexec_split (rb + xe_ps e) (rb + xe_vs e) (rb + xe_de e) (rb + xe_oend e) c (rb + op) li llim ll ml off =
  lexec_split (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) c k li llim ll ml off.
Proof.
  intros Hx Hk Ho. destruct (xs_coords a rb m body bo ps ds de Hx) as (E1 & E2 & E3).
  cbv zeta. unfold xenv_a. cbn [xe_ps xe_vs xe_de xe_oend]. rewrite E1, E2, Hk.
  replace (rb + (sp_d a + sp_cap a - rb)) with (sp_d a + sp_cap a) by lia.
  destruct E3 as [E3|E3]; [rewrite E3; reflexivity|]. apply xs_lexec_split_de. lia.
Qed.

(* the readable history and literals stay readable as the output grows and the literal cursor advances *)
Lemma xs_xh_ext (e: xenv) (m m': xmem) (op op': Z) :
  xh_ok e m op -> xm_le m m' -> op <= op' -> xwr_rng m' op op' -> xh_ok e m' op'.
Proof.
  intros (H1 & H2 & H3 & H4 & H5) Hle Hop Hw. unfold xh_ok. split; [lia|]. split; [lia|]. split; [lia|].
  split; [eapply xwr_rng_app; [eapply xwr_rng_le; eauto | exact Hw] | eapply xwr_rng_le; eauto].
Qed.

Lemma xs_xl_ext (e: xenv) (m m': xmem) (lr: xreg) (li li' lim: Z) :
  xl_ok e m lr li lim -> xm_le m m' -> li <= li' <= lim -> xl_ok e m' lr li' lim.
Proof.
  intros (H1 & H2) [Hw Hlx] Hl. split; [lia|]. destruct lr.
  - intros j Hj. apply Hw, H2. lia.
  - rewrite Hlx. exact H2.
  - exact H2.
Qed.

(* the facts of the pending sequence the steps use *)
Lemma xs_spend (a: sa) (t: seq_tabs) (ph: bool) (w: sw) (ll ml ov: Z) :
  spend a t ph w ll ml ov ->
  0 <= ll /\ 3 <= ml /\ 1 <= fst (c_offset (w_crep w) ll ov) /\ sp_outok a ph (w_K w) (w_j w) (w_c w).
Proof.
  intros (_ & _ & _ & _ & _ & Hr & Hll & Hml & Hov & Ho & _). split; [lia|]. split; [lia|]. split; [|exact Ho].
  destruct (w_crep w) as [[r1 r2] r3]. apply c_offset_ok; [|exact Hov]. unfold rep_ok in Hr. unfold rep64_ok, SIZE_MAX. lia.
Qed.

(* the leftover of the head (ZSTD_safecopyDstBeforeSrc, nothing when there is none): the model's copy, the C's *)
Lemma xs_left_copy (src: list Z) (m: xmem) (op li lo oend: Z) (c: list val) (rb: Z) :
  0 <= op -> 0 <= li -> 0 <= lo -> lo <= oend - op -> xwr_rng m li (li + lo) -> dst_rel c rb (xm_dst m) -> 0 <= rb ->
  rb + op + lo <= Zlength c ->
  exists m1,
    (if lo =? 0 then Some (m, op) else
     if lo >? oend - op then None else
     match xm_sdbs src m op li lo with Some m => Some (m, op + lo) | None => None end) = Some (m1, op + lo) /\
    xm_le m m1 /\ xwr_rng m1 op (op + lo) /\ xm_lxb m1 = xm_lxb m /\
    dst_rel (if lo =? 0 then c else lsdbs c (rb + op) (rb + li) lo) rb (xm_dst m1).
Proof.
  intros Hop Hli Hlo Hoe Hw Hdr Hrb Hc.
  destruct (Z.eqb_spec lo 0) as [->|Hn].
  - exists m. rewrite Z.add_0_r. split; [reflexivity|]. split; [apply xm_le_refl|].
    split; [intros j Hj; lia|]. auto.
  - destruct (Z.gtb_spec lo (oend - op)); [lia|].
    destruct (xm_sdbs_def src m op li lo Hop Hli Hlo Hw) as (m1 & E & Hle & Hw1).
    rewrite E. exists m1. destruct (xm_sdbs_l src m m1 op li lo c rb E Hdr Hrb Hc) as (Hx & Hd).
    split; [reflexivity|]. split; [exact Hle|]. split; [exact Hw1|]. split; [exact Hx|exact Hd].
Qed.

(* from xpend to the next xinv: the model's step from each region's state succeeds with a related state *)
Lemma xs_inv_step (a: sa) (t: seq_tabs) (cl: list val) (ph ph': bool) (w w': sw) (ll ml ov: Z) :
  xpend a t cl ph w ll ml ov ->
  w_id w' = w_id w + 1 -> w_pos w' = w_pos w -> w_lo w' = w_lo w -> w_st w' = w_st w ->
  w_crep w' = snd (c_offset (w_crep w) ll ov) ->
  (forall rb m body bo ps ds de s, xhyp a rb m body bo ps ds de -> xrel a (xenv_a a rb body ps ds de) rb ph w s ->
     exists s', x_step (xenv_a a rb body ps ds de) s ll ml (fst (c_offset (w_crep w) ll ov)) = Some s' /\
       xrel a (xenv_a a rb body ps ds de) rb ph' w' s') ->
  xinv a t cl ph' w'.
Proof.
  intros (Hcl & Hlen & H) Hid Hpos Hlo Hst Hrep Hstep. split; [exact Hcl|]. split; [exact Hlen|].
  intros rb m body bo ps ds de Hx. cbv zeta.
  destruct (H rb m body bo ps ds de Hx) as [(s & Hres & Hrel & Hb1 & Hb2) | (Hp & Hres)].
  - destruct (Hstep rb m body bo ps ds de s Hx Hrel) as (s' & Hs & Hrel').
    left. exists s'. rewrite Hs in Hres. rewrite Hres, Hid, Hpos, Hlo, Hst, Hrep.
    replace (a_nb a - (w_id w + 1)) with (a_nb a - w_id w - 1) by lia.
    split; [reflexivity|]. split; [exact Hrel'|]. split; [exact Hb1|exact Hb2].
  - right. rewrite Hpos. auto.
Qed.

(* ... or the model's step fails from every related state *)
Lemma xs_step_none (a: sa) (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) (ll ml ov: Z) :
  xpend a t cl ph w ll ml ov ->
  (forall rb m body bo ps ds de s, xhyp a rb m body bo ps ds de -> xrel a (xenv_a a rb body ps ds de) rb ph w s ->
     x_step (xenv_a a rb body ps ds de) s ll ml (fst (c_offset (w_crep w) ll ov)) = None) ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros (_ & _ & H) Hn rb m body bo ps ds de Hx.
  destruct (H rb m body bo ps ds de Hx) as [(s & Hres & Hrel & _) | (_ & Hres)]; [|exact Hres].
  rewrite (Hn rb m body bo ps ds de s Hx Hrel) in Hres. exact Hres.
Qed.

(* phase 1 in a region: the model's ZSTD_execSequenceSplitLitBuffer fails exactly on the C's error conditions;
   on success the C's stores (lexec_split) hold the new region and the next state is related *)
Lemma xs_x1 (a: sa) rb m body bo ps ds de (w w': sw) (s: xex) (ll ml off: Z) :
  sa_ok a -> xhyp a rb m body bo ps ds de -> xrel a (xenv_a a rb body ps ds de) rb true w s ->
  Zlength (w_c w) = sp_N a -> 0 <= ll -> 1 <= ml -> 1 <= off -> ll <= sp_lim a - (a_lb a + w_j w) ->
  match x_step (xenv_a a rb body ps ds de) s ll ml off with
  | None => exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml off (sp_ps a)
              (ext_len (sp_x a)) = true
  | Some s' =>
      exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml off (sp_ps a)
        (ext_len (sp_x a)) = false /\
      (w_K w' = w_K w + (ll + ml) -> w_j w' = w_j w + ll ->
       w_c w' = lexec_split (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) (w_c w)
                  (sp_d a + w_K w) (a_lb a + w_j w) (sp_lim a) ll ml off ->
       xrel a (xenv_a a rb body ps ds de) rb true w' s')
  end.
Proof.
  intros Ha Hx Hr HN Hll Hml Hoff Hj.
  destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & Hlxb & Hdr & Hh & Hl).
  destruct (xs_facts a rb m body bo ps ds de Ha Hx) as (Hrb & HdN & Hlbe & HiN).
  assert (Hoe: xlim s + WILDCOPY_OVERLENGTH <= xe_oend (xenv_a a rb body ps ds de)).
  { rewrite Hlim. unfold xenv_a. cbn [xe_oend]. lia. }
  rewrite Hlr in Hl. unfold x_step. rewrite Hsp. cbv zeta.
  replace (xlim s - xli s <? ll) with false by (symmetry; apply Z.ltb_ge; lia).
  pose proof (x_exec_split_def (xenv_a a rb body ps ds de) (xmm s) (xop s) (xli s) (xlim s) ll ml off Hh Hl
                ltac:(lia) Hoe Hll Hml Hoff) as D.
  rewrite (xs_split_err_eq a rb m body bo ps ds de (xop s) (xli s) (sp_d a + w_K w) (a_lb a + w_j w) ll ml off Hx
             ltac:(lia) ltac:(lia)) in D.
  revert D. destruct (x_exec_split (xenv_a a rb body ps ds de) (xmm s) (xop s) (xli s) (xlim s) ll ml off)
    as [[[m' op'] li']|] eqn:E; intros D; [|exact D].
  destruct D as (Herr & Hop' & Hli' & Hle & Hw). split; [exact Herr|]. intros HK HJ HC.
  pose proof (xs_split_err_off _ _ _ _ _ _ _ _ Herr) as He.
  destruct (x_exec_split_l (xenv_a a rb body ps ds de) (xmm s) m' (xop s) (xli s) (xlim s) ll ml off op' li' (w_c w) rb
              E Hdr Hll ltac:(lia) ltac:(lia) ltac:(unfold xenv_a; cbn [xe_oend]; lia) Hoe) as (Hlx & Hdr').
  rewrite (xs_lexec_split_eq a rb m body bo ps ds de (w_c w) (xop s) (sp_d a + w_K w) _ _ ll ml off Hx
             ltac:(lia) ltac:(lia)) in Hdr'.
  replace (rb + xli s) with (a_lb a + w_j w) in Hdr' by lia.
  replace (rb + xlim s) with (sp_lim a) in Hdr' by lia.
  unfold xrel. cbn [xop xlr xli xlim xsp xmm].
  split; [lia|]. split; [split; [reflexivity|]; split; [lia|]; split; [lia|reflexivity]|].
  split; [rewrite Hlx; exact Hlxb|]. split; [rewrite HC; exact Hdr'|].
  split; [eapply xs_xh_ext; [exact Hh|exact Hle|lia|exact Hw]|].
  eapply xs_xl_ext; [exact Hl|exact Hle|lia].
Qed.

(* the leftover in a region: the model's copy of the head's rest (none when lo = 0), then its ZSTD_execSequence
   from litExtraBuffer, fail exactly on the C's error conditions; on success the C's stores hold the new region
   and the next state (literals in litExtraBuffer) is related *)
Lemma xs_left (a: sa) rb m body bo ps ds de (w w': sw) (s: xex) (cl: list val) (lo ll ml off: Z) :
  lo = sp_lim a - (a_lb a + w_j w) ->
  sa_ok a -> xhyp a rb m body bo ps ds de -> xrel a (xenv_a a rb body ps ds de) rb true w s ->
  cl = zbytes (a_lxb a) -> Zlength (a_lxb a) = LITEXTRA_N ->
  Zlength (w_c w) = sp_N a -> 1 <= ml -> 1 <= off -> lo < ll -> w_K w + lo <= sp_cap a ->
  match x_step (xenv_a a rb body ps ds de) s ll ml off with
  | None => exec_err (sp_d a + w_K w + lo) (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml off (sp_ps a)
              (ext_len (sp_x a)) = true
  | Some s' =>
      exec_err (sp_d a + w_K w + lo) (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml off (sp_ps a)
        (ext_len (sp_x a)) = false /\
      (w_K w' = w_K w + ll + ml -> w_j w' = w_j w + ll ->
       w_c w' = lexec (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a)
                  (if lo =? 0 then w_c w else lsdbs (w_c w) (sp_d a + w_K w) (a_lb a + w_j w) lo)
                  (sp_d a + w_K w + lo) (LS cl) 0 LITBUFFEREXTRASIZE (ll - lo) ml off ->
       xrel a (xenv_a a rb body ps ds de) rb false w' s')
  end.
Proof.
  intros Hlo Ha Hx Hr Hcl HL HN Hml Hoff Hll HK.
  destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & Hlxb & Hdr & Hh & Hl).
  destruct (xs_facts a rb m body bo ps ds de Ha Hx) as (Hrb & HdN & Hlbe & HiN).
  pose proof Hx as Hx'. destruct Hx' as (_ & _ & _ & _ & Hbo & Hbn & Hbs & _).
  assert (Hoe: xe_oend (xenv_a a rb body ps ds de) = sp_d a + sp_cap a - rb) by reflexivity.
  pose proof Hl as (Hl0 & Hlw). rewrite Hlr in Hlw. unfold WILDCOPY_OVERLENGTH in Hlw.
  pose proof Hh as (Hh0 & _).
  unfold x_step. rewrite Hsp. cbv zeta.
  replace (xlim s - xli s) with lo by lia.
  destruct (Z.ltb_spec lo ll) as [_|]; [|lia].
  assert (Hw0: xwr_rng (xmm s) (xli s) (xli s + lo)) by (eapply xwr_rng_sub; [| |exact Hlw]; lia).
  destruct (xs_left_copy (xe_src (xenv_a a rb body ps ds de)) (xmm s) (xop s) (xli s) lo
              (xe_oend (xenv_a a rb body ps ds de)) (w_c w) rb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hw0 Hdr
              ltac:(lia) ltac:(lia)) as (m1 & Hmo & Hle1 & Hw1 & Hlx1 & Hdr1).
  rewrite Hmo. cbv beta iota.
  assert (Hh1: xh_ok (xenv_a a rb body ps ds de) m1 (xop s + lo))
    by (eapply xs_xh_ext; [exact Hh|exact Hle1|lia|exact Hw1]).
  assert (Hl1: xl_ok (xenv_a a rb body ps ds de) m1 R_lxb 0 XLITEXTRA).
  { split; [unfold XLITEXTRA; lia|]. rewrite Hlx1, Hlxb, HL.
    unfold LITEXTRA_N, XLITEXTRA, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH. lia. }
  pose proof (x_exec_def (xenv_a a rb body ps ds de) m1 (xop s + lo) R_lxb 0 XLITEXTRA (ll - lo) ml off Hh1 Hl1
                ltac:(lia) Hml Hoff) as D.
  rewrite (xs_exec_err_eq a rb m body bo ps ds de (xop s + lo) (sp_d a + w_K w + lo) 0 XLITEXTRA 0
             LITBUFFEREXTRASIZE (ll - lo) ml off Hx ltac:(lia) ltac:(reflexivity)) in D.
  revert D. destruct (x_exec (xenv_a a rb body ps ds de) m1 (xop s + lo) R_lxb 0 XLITEXTRA (ll - lo) ml off)
    as [[[m2 op2] li2]|] eqn:E; intros D; cbv beta iota; [|exact D].
  destruct D as (Herr & Hop2 & Hli2 & Hle2 & Hw2). split; [exact Herr|]. intros HK' HJ' HC.
  destruct (xs_exec_err_ok _ _ _ _ _ _ _ _ _ Herr) as (He1 & He2 & He3).
  assert (Hsrc: src_rel (xe_src (xenv_a a rb body ps ds de)) (xm_lxb m1) (iw_c (a_i a)) bo cl).
  { change (xe_src (xenv_a a rb body ps ds de)) with body. unfold src_rel. rewrite Hlx1, Hlxb.
    split; [lia|]. split; [lia|]. split; [exact Hbs|exact Hcl]. }
  assert (HL1: Zlength (if lo =? 0 then w_c w else lsdbs (w_c w) (rb + xop s) (rb + xli s) lo) = Zlength (w_c w))
    by (destruct (lo =? 0); [reflexivity|apply lsdbs_len]).
  destruct (x_exec_l (xenv_a a rb body ps ds de) m1 m2 (xop s + lo) R_lxb 0 XLITEXTRA (ll - lo) ml off op2 li2 _
              (iw_c (a_i a)) cl rb bo E Hdr1 Hsrc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Hlx2 & Hdr2).
  cbn [reg_l reg_o] in Hdr2.
  rewrite (xs_lexec_eq a rb m body bo ps ds de _ (xop s + lo) (sp_d a + w_K w + lo) (LS cl) _ _ (ll - lo) ml off Hx
             ltac:(lia) ltac:(lia)) in Hdr2.
  change (0 + 0) with 0 in Hdr2. change (0 + XLITEXTRA) with LITBUFFEREXTRASIZE in Hdr2.
  replace (rb + xop s) with (sp_d a + w_K w) in Hdr2 by lia.
  replace (rb + xli s) with (a_lb a + w_j w) in Hdr2 by lia.
  unfold xrel. cbn [xop xlr xli xlim xsp xmm].
  split; [lia|].
  split; [split; [reflexivity|]; split; [unfold sp_lim in Hlo; lia|]; split; reflexivity|].
  split; [rewrite Hlx2, Hlx1; exact Hlxb|]. split; [rewrite HC; exact Hdr2|].
  split; [eapply xs_xh_ext; [exact Hh1|exact Hle2|lia|exact Hw2]|].
  eapply xs_xl_ext; [exact Hl1|exact Hle2|unfold XLITEXTRA, LITBUFFEREXTRASIZE in *; lia].
Qed.

(* phase 2 in a region: the model's ZSTD_execSequence from litExtraBuffer *)
Lemma xs_x2 (a: sa) rb m body bo ps ds de (w w': sw) (s: xex) (cl: list val) (ll ml off: Z) :
  sa_ok a -> xhyp a rb m body bo ps ds de -> xrel a (xenv_a a rb body ps ds de) rb false w s ->
  cl = zbytes (a_lxb a) -> Zlength (w_c w) = sp_N a -> 0 <= ll -> 1 <= ml -> 1 <= off ->
  match x_step (xenv_a a rb body ps ds de) s ll ml off with
  | None => exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE
              ll ml off (sp_ps a) (ext_len (sp_x a)) = true
  | Some s' =>
      exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE
        ll ml off (sp_ps a) (ext_len (sp_x a)) = false /\
      (w_K w' = w_K w + (ll + ml) -> w_j w' = w_j w + ll ->
       w_c w' = lexec (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) (w_c w)
                  (sp_d a + w_K w) (LS cl) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml off ->
       xrel a (xenv_a a rb body ps ds de) rb false w' s')
  end.
Proof.
  intros Ha Hx Hr Hcl HN Hll Hml Hoff.
  destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & Hlxb & Hdr & Hh & Hl).
  destruct (xs_facts a rb m body bo ps ds de Ha Hx) as (Hrb & HdN & Hlbe & HiN).
  pose proof Hx as Hx'. destruct Hx' as (_ & _ & _ & _ & Hbo & Hbn & Hbs & _).
  assert (Hoe: xe_oend (xenv_a a rb body ps ds de) = sp_d a + sp_cap a - rb) by reflexivity.
  unfold x_step. rewrite Hsp. cbv zeta.
  pose proof (x_exec_def (xenv_a a rb body ps ds de) (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off Hh Hl
                Hll Hml Hoff) as D.
  rewrite (xs_exec_err_eq a rb m body bo ps ds de (xop s) (sp_d a + w_K w) (xli s) (xlim s)
             (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml off Hx ltac:(lia) ltac:(lia)) in D.
  revert D. destruct (x_exec (xenv_a a rb body ps ds de) (xmm s) (xop s) (xlr s) (xli s) (xlim s) ll ml off)
    as [[[m' op'] li']|] eqn:E; intros D; [|exact D].
  destruct D as (Herr & Hop' & Hli' & Hle & Hw). split; [exact Herr|]. intros HK HJ HC.
  destruct (xs_exec_err_ok _ _ _ _ _ _ _ _ _ Herr) as (He1 & He2 & He3).
  assert (Hsrc: src_rel (xe_src (xenv_a a rb body ps ds de)) (xm_lxb (xmm s)) (iw_c (a_i a)) bo cl).
  { change (xe_src (xenv_a a rb body ps ds de)) with body. unfold src_rel. rewrite Hlxb.
    split; [lia|]. split; [lia|]. split; [exact Hbs|exact Hcl]. }
  destruct (x_exec_l (xenv_a a rb body ps ds de) (xmm s) m' (xop s) (xlr s) (xli s) (xlim s) ll ml off op' li'
              (w_c w) (iw_c (a_i a)) cl rb bo E Hdr Hsrc Hll ltac:(lia) ltac:(lia) ltac:(lia)) as (Hlx & Hdr').
  rewrite (xs_lexec_eq a rb m body bo ps ds de (w_c w) (xop s) (sp_d a + w_K w) _ _ _ ll ml off Hx
             ltac:(lia) ltac:(lia)) in Hdr'.
  rewrite Hlr in Hdr'. cbn [reg_l reg_o] in Hdr'. rewrite Hli, Hlim in Hdr'. rewrite !Z.add_0_l in Hdr'.
  unfold xrel. cbn [xop xlr xli xlim xsp xmm].
  split; [lia|]. split; [split; [exact Hlr|]; split; [lia|]; split; [exact Hlim|reflexivity]|].
  split; [rewrite (proj2 Hle); exact Hlxb|]. split; [rewrite HC; exact Hdr'|].
  split; [eapply xs_xh_ext; [exact Hh|exact Hle|lia|exact Hw]|].
  eapply xs_xl_ext; [exact Hl|exact Hle|lia].
Qed.

(* phase 1, ZSTD_execSequenceSplitLitBuffer: an error iff the model fails *)
Lemma xx1_err (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> xpend a t cl true w ll ml ov ->
  ll <= sp_lim a - (a_lb a + w_j w) ->
  exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml (fst (c_offset (w_crep w) ll ov))
    (sp_ps a) (ext_len (sp_x a)) = true ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros Ha Hp Hs Hx Hj Herr. destruct (xs_spend a t true w ll ml ov Hs) as (Hll & Hml & Hoff & Ho).
  destruct Ho as (_ & HN & _).
  apply (xs_step_none a t cl true w ll ml ov Hx). intros rb m body bo ps ds de s Hh Hr.
  pose proof (xs_x1 a rb m body bo ps ds de w w s ll ml (fst (c_offset (w_crep w) ll ov)) Ha Hh Hr HN Hll
                ltac:(lia) Hoff Hj) as D.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|reflexivity].
  destruct D as [D _]. congruence.
Qed.

(* phase 1, its success: the C's stores are the model's (EXEC's lexec_split, XKitL.x_exec_split_l) *)
Lemma xx1 (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov r: Z) (c': list val) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> xpend a t cl true w ll ml ov ->
  ll <= sp_lim a - (a_lb a + w_j w) -> Zlength c' = Zlength (w_c w) ->
  exec_split_err (sp_d a + w_K w) (sp_d a + sp_cap a) (a_lb a + w_j w) ll ml (fst (c_offset (w_crep w) ll ov))
    (sp_ps a) (ext_len (sp_x a)) = false ->
  is_error_code r = false ->
  match sp_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec_split (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) (w_c w)
                (sp_d a + w_K w) (a_lb a + w_j w) (sp_lim a) ll ml (fst (c_offset (w_crep w) ll ov))
  end ->
  xinv a t cl true {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                      w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                      w_c := c' |}.
Proof.
  intros Ha Hp Hs Hx Hj HL Herr Hr Hc. destruct (xs_spend a t true w ll ml ov Hs) as (Hll & Hml & Hoff & Ho).
  destruct Ho as (_ & HN & _).
  apply (xs_inv_step a t cl true true w _ ll ml ov Hx); try reflexivity. intros rb m body bo ps ds de s Hh Hrl.
  match goal with |- exists s', _ /\ xrel _ _ _ _ ?w' s' =>
    pose proof (xs_x1 a rb m body bo ps ds de w w' s ll ml (fst (c_offset (w_crep w) ll ov)) Ha Hh Hrl HN Hll
                  ltac:(lia) Hoff Hj) as D end.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|congruence].
  destruct D as [_ D]. exists s'. split; [reflexivity|]. apply D; [reflexivity|reflexivity|].
  cbn [w_c]. exact (xs_notsep a rb m body bo ps ds de _ _ Hh Hc Hr).
Qed.

(* the leftover check (leftoverLit > oend - op): the model fails *)
Lemma xleft_lerr (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> xpend a t cl true w ll ml ov ->
  sp_lim a - (a_lb a + w_j w) < ll -> 0 < sp_lim a - (a_lb a + w_j w) ->
  sp_cap a - w_K w < sp_lim a - (a_lb a + w_j w) ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros Ha Hp Hs Hx Hl0 Hl1 Hl2.
  apply (xs_step_none a t cl true w ll ml ov Hx). intros rb m body bo ps ds de s Hh Hrl.
  destruct Hrl as (Hop & (Hlr & Hli & Hlim & Hsp) & _).
  unfold x_step. rewrite Hsp. cbv zeta.
  destruct (Z.ltb_spec (xlim s - xli s) ll); [|lia].
  destruct (Z.eqb_spec (xlim s - xli s) 0); [lia|].
  match goal with |- context [?x >? ?y] => destruct (Z.gtb_spec x y) end; [reflexivity|].
  unfold xenv_a in *. cbn [xe_oend] in *. lia.
Qed.

(* the leftover copy (ZSTD_safecopyDstBeforeSrc, COPY's lsdbs; nothing when there is none), then ZSTD_execSequence
   from litExtraBuffer: an error iff the model fails *)
Lemma xleft_xerr (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov: Z) (c1: list val) :
  let lo := sp_lim a - (a_lb a + w_j w) in
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> xpend a t cl true w ll ml ov ->
  lo < ll -> w_K w + lo <= sp_cap a ->
  c1 = (if lo =? 0 then w_c w else lsdbs (w_c w) (sp_d a + w_K w) (a_lb a + w_j w) lo) ->
  exec_err (sp_d a + w_K w + lo) (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = true ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros lo Ha Hp Hs Hx Hl0 HK Hc1 Herr.
  assert (Hlo: lo = sp_lim a - (a_lb a + w_j w)) by reflexivity. clearbody lo.
  destruct (xs_spend a t true w ll ml ov Hs) as (Hll & Hml & Hoff & Ho). destruct Ho as (_ & HN & _).
  pose proof Hx as (Hcl & HL & _).
  apply (xs_step_none a t cl true w ll ml ov Hx). intros rb m body bo ps ds de s Hh Hrl.
  pose proof (xs_left a rb m body bo ps ds de w w s cl lo ll ml (fst (c_offset (w_crep w) ll ov)) Hlo Ha Hh Hrl
                Hcl HL HN ltac:(lia) Hoff Hl0 HK) as D.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|reflexivity].
  destruct D as [D _]. congruence.
Qed.

(* ... and its success: the invariant of phase 2 *)
Lemma xleft_ok (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov r: Z) (c1 c': list val) :
  let lo := sp_lim a - (a_lb a + w_j w) in
  sa_ok a -> sp_pending a -> spend a t true w ll ml ov -> xpend a t cl true w ll ml ov ->
  lo < ll -> w_K w + lo <= sp_cap a ->
  c1 = (if lo =? 0 then w_c w else lsdbs (w_c w) (sp_d a + w_K w) (a_lb a + w_j w) lo) ->
  Zlength c1 = Zlength (w_c w) -> Zlength c' = Zlength c1 ->
  exec_err (sp_d a + w_K w + lo) (sp_d a + sp_cap a) 0 LITBUFFEREXTRASIZE (ll - lo) ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = false ->
  is_error_code r = false ->
  match sp_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) c1
                (sp_d a + w_K w + lo) (LS cl) 0 LITBUFFEREXTRASIZE (ll - lo) ml (fst (c_offset (w_crep w) ll ov))
  end ->
  xinv a t cl false {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                       w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + ll + ml; w_j := w_j w + ll;
                       w_c := c' |}.
Proof.
  intros lo Ha Hp Hs Hx Hl0 HK Hc1 HL1 HL2 Herr Hr Hc.
  assert (Hlo: lo = sp_lim a - (a_lb a + w_j w)) by reflexivity. clearbody lo.
  destruct (xs_spend a t true w ll ml ov Hs) as (Hll & Hml & Hoff & Ho). destruct Ho as (_ & HN & _).
  pose proof Hx as (Hcl & HL & _).
  apply (xs_inv_step a t cl true false w _ ll ml ov Hx); try reflexivity. intros rb m body bo ps ds de s Hh Hrl.
  match goal with |- exists s', _ /\ xrel _ _ _ _ ?w' s' =>
    pose proof (xs_left a rb m body bo ps ds de w w' s cl lo ll ml (fst (c_offset (w_crep w) ll ov)) Hlo Ha Hh Hrl
                  Hcl HL HN ltac:(lia) Hoff Hl0 HK) as D end.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|congruence].
  destruct D as [_ D]. exists s'. split; [reflexivity|]. apply D; [reflexivity|reflexivity|].
  cbn [w_c]. rewrite <- Hc1. exact (xs_notsep a rb m body bo ps ds de _ _ Hh Hc Hr).
Qed.

(* phase 2, ZSTD_execSequence from litExtraBuffer: an error iff the model fails *)
Lemma xx2_err (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov: Z) :
  sa_ok a -> sp_pending a -> spend a t false w ll ml ov -> xpend a t cl false w ll ml ov ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = true ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros Ha Hp Hs Hx Herr. destruct (xs_spend a t false w ll ml ov Hs) as (Hll & Hml & Hoff & Ho).
  destruct Ho as (_ & HN & _). pose proof Hx as (Hcl & HL & _).
  apply (xs_step_none a t cl false w ll ml ov Hx). intros rb m body bo ps ds de s Hh Hr.
  pose proof (xs_x2 a rb m body bo ps ds de w w s cl ll ml (fst (c_offset (w_crep w) ll ov)) Ha Hh Hr Hcl HN Hll
                ltac:(lia) Hoff) as D.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|reflexivity].
  destruct D as [D _]. congruence.
Qed.

(* ... and its success *)
Lemma xx2 (a: sa) (t: seq_tabs) (cl: list val) (w: sw) (ll ml ov r: Z) (c': list val) :
  sa_ok a -> sp_pending a -> spend a t false w ll ml ov -> xpend a t cl false w ll ml ov ->
  Zlength c' = Zlength (w_c w) ->
  exec_err (sp_d a + w_K w) (sp_d a + sp_cap a) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
    (fst (c_offset (w_crep w) ll ov)) (sp_ps a) (ext_len (sp_x a)) = false ->
  is_error_code r = false ->
  match sp_x a with
  | ExtSep _ _ _ _ _ _ => True
  | _ => is_error_code r = false ->
         c' = lexec (sp_ps a) (sp_ps a - ext_len (sp_x a)) (ext_end (sp_x a)) (sp_d a + sp_cap a) (w_c w)
                (sp_d a + w_K w) (LS cl) (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE ll ml
                (fst (c_offset (w_crep w) ll ov))
  end ->
  xinv a t cl false {| w_id := w_id w + 1; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w;
                       w_crep := snd (c_offset (w_crep w) ll ov); w_K := w_K w + (ll + ml); w_j := w_j w + ll;
                       w_c := c' |}.
Proof.
  intros Ha Hp Hs Hx HL1 Herr Hr Hc. destruct (xs_spend a t false w ll ml ov Hs) as (Hll & Hml & Hoff & Ho).
  destruct Ho as (_ & HN & _). pose proof Hx as (Hcl & HL & _).
  apply (xs_inv_step a t cl false false w _ ll ml ov Hx); try reflexivity. intros rb m body bo ps ds de s Hh Hrl.
  match goal with |- exists s', _ /\ xrel _ _ _ _ ?w' s' =>
    pose proof (xs_x2 a rb m body bo ps ds de w w' s cl ll ml (fst (c_offset (w_crep w) ll ov)) Ha Hh Hrl Hcl HN Hll
                  ltac:(lia) Hoff) as D end.
  revert D. destruct (x_step _ s ll ml _) as [s'|]; intros D; [|congruence].
  destruct D as [_ D]. exists s'. split; [reflexivity|]. apply D; [reflexivity|reflexivity|].
  cbn [w_c]. exact (xs_notsep a rb m body bo ps ds de _ _ Hh Hc Hr).
Qed.

(* the end of the sequences: BIT_endOfDStream fails (not lo = 0 and pos = 0): so does the model *)
Lemma xend_err (a: sa) (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) :
  sinv a t ph w -> xinv a t cl ph w -> w_id w = a_nb a -> ~ (w_lo w = 0 /\ w_pos w = 0) ->
  forall rb m body bo ps ds de, xhyp a rb m body bo ps ds de -> xres_a a rb m body ps ds de = None.
Proof.
  intros _ (_ & _ & Hx) Hid Hne rb m body bo ps ds de Hh.
  destruct (Hx rb m body bo ps ds de Hh) as [(s & Hres & _ & _ & Hend) | (_ & Hres)]; [|exact Hres].
  rewrite Hres. rewrite Hid, Z.sub_diag. unfold xcont. destruct t as [[tLL tOF] tML]. cbn [Z.to_nat x_seq_loop].
  destruct (Z.eqb_spec (w_pos w) 0) as [Hp0|Hp0]; [|reflexivity].
  exfalso. apply Hne. split; [apply Hend|]; assumption.
Qed.

(* ... it succeeds: the last literals remain, the repeat offsets are the C's (x_rep32 of size_t values below 2^32) *)
Lemma xend_ok (a: sa) (t: seq_tabs) (cl: list val) (ph: bool) (w: sw) :
  sinv a t ph w -> xinv a t cl ph w -> w_id w = a_nb a -> w_lo w = 0 -> w_pos w = 0 ->
  xlast a cl ph w (w_crep w).
Proof.
  intros (_ & _ & _ & _ & _ & Hrep & _) (Hcl & Hlen & Hx) Hid Hlo Hpos.
  split; [exact Hcl|]. split; [exact Hlen|]. intros rb m body bo ps ds de Hh. cbv zeta.
  destruct (Hx rb m body bo ps ds de Hh) as [(s & Hres & Hrel & _) | (Hneg & _)]; [|lia].
  exists s. split; [|exact Hrel].
  rewrite Hres, Hid, Z.sub_diag. unfold xcont. destruct t as [[tLL tOF] tML]. cbn [Z.to_nat x_seq_loop].
  rewrite Hpos. cbn [Z.eqb negb].
  assert (Hr: x_rep32 (w_crep w) = w_crep w).
  { destruct (w_crep w) as [[r1 r2] r3]. destruct Hrep as (H1 & H2 & H3). unfold x_rep32.
    rewrite !Z.mod_small by lia. reflexivity. }
  rewrite Hr. reflexivity.
Qed.

(* no sequences: only the last literals (the repeat offsets unchanged) *)
Lemma xlast0 (a: sa) (cl: list val) (st: Z * Z * Z) :
  sa_ok a -> a_nb a = 0 -> cl = zbytes (a_lxb a) -> Zlength (a_lxb a) = LITEXTRA_N ->
  xlast a cl true {| w_id := 0; w_pos := 0; w_lo := 0; w_st := st; w_crep := a_rep a; w_K := 0; w_j := 0;
                     w_c := sp_c0 a |} (a_rep a).
Proof.
  intros Hok Hnb Hcl Hlx. split; [exact Hcl|]. split; [exact Hlx|].
  intros rb m body bo ps ds de Hx. cbv zeta. exists (xs0_a a rb m). split.
  - unfold xres_a, x_seq_section. rewrite Hnb. reflexivity.
  - apply xrel0 with (bo := bo); auto.
Qed.

(* the facts of the precondition the last literals use: the output array's bounds, more literals than
   litExtraBuffer holds *)
Lemma xfin_ctx (a: sa) : sa_ok a ->
  0 <= sp_d a /\ 0 <= sp_cap a /\ sp_d a + sp_cap a <= sp_N a /\ sp_N a <= 2 ^ 63 - 1 /\
  LITBUFFEREXTRASIZE < sp_n a /\ sp_lim a + WILDCOPY_OVERLENGTH <= sp_d a + sp_cap a.
Proof.
  intros (Ho & _ & Hl & _). destruct Ho as (_ & _ & HN & Hd & Hcap & HdN).
  destruct Hl as (_ & _ & Hgt & _ & Hend & _). unfold sp_lim, sp_d, sp_cap, sp_N, sp_n in *. repeat split; lia.
Qed.

(* reading k cells of the output array in order gives its sublist *)
Lemma xfin_lrdn (k: nat) (c: list val) (i: Z) :
  0 <= i -> i + Z.of_nat k <= Zlength c -> lrdn k c LW i = sublist i (i + Z.of_nat k) c.
Proof.
  revert i. induction k as [|k IH]; intros i Hi Hk.
  - cbn. rewrite sublist_nil' by lia. reflexivity.
  - cbn [lrdn lrd]. rewrite IH by lia.
    rewrite (sublist_split i (i + 1) (i + Z.of_nat (S k))) by lia. rewrite (sublist_one i (i + 1)) by lia.
    cbn [app]. f_equal. f_equal. lia.
Qed.

(* the stores of a run of values at d replace the cells [d, d + |vs|) *)
Lemma xfin_lwrn (vs c: list val) (d: Z) :
  0 <= d -> d + Zlength vs <= Zlength c -> lwrn vs c d = put c d vs.
Proof.
  revert c d. induction vs as [|v vs IH]; intros c d Hd Hb.
  - cbn [lwrn]. unfold put. list_solve.
  - rewrite Zlength_cons in Hb. pose proof (Zlength_nonneg vs).
    cbn [lwrn]. rewrite IH; [|lia|list_solve]. unfold put. list_solve.
Qed.

(* a move within the output array (all read, then all stored): the cells [d, d + k) take the old [i, i + k) *)
Lemma xfin_lmove (k: nat) (c: list val) (d i: Z) :
  0 <= d -> 0 <= i -> i + Z.of_nat k <= Zlength c -> d + Z.of_nat k <= Zlength c ->
  lmove k c d LW i = put c d (sublist i (i + Z.of_nat k) c).
Proof.
  intros. unfold lmove. rewrite xfin_lrdn by lia. apply xfin_lwrn; [lia|]. rewrite Zlength_sublist by lia. lia.
Qed.

(* a forward copy from a separate array: the cells [d, d + k) take the source's [i, i + k) *)
Lemma xfin_lfwd (k: nat) (c cs: list val) (d i: Z) :
  0 <= d -> 0 <= i -> i + Z.of_nat k <= Zlength cs -> d + Z.of_nat k <= Zlength c ->
  lfwd k c d (LS cs) i = put c d (sublist i (i + Z.of_nat k) cs).
Proof.
  intros Hd Hi Hs Hc. rewrite <- xfin_lwrn by (rewrite ?Zlength_sublist; lia).
  revert c d i Hd Hi Hs Hc. induction k as [|k IH]; intros c d i Hd Hi Hs Hc.
  - cbn. rewrite sublist_nil' by lia. reflexivity.
  - cbn [lfwd lrd]. rewrite IH by (rewrite ?Zlength_upd_Znth; lia).
    rewrite (sublist_split i (i + 1) (i + Z.of_nat (S k))) by lia. rewrite (sublist_one i (i + 1)) by lia.
    cbn [app lwrn]. f_equal. f_equal. lia.
Qed.

(* an error code *)
Lemma xfin_err70 : is_error_code (err_code 70) = true.
Proof. reflexivity. Qed.

(* litExtraBuffer from the literal cursor to its end holds the literals left *)
Lemma xfin_tail (a: sa) (j: Z) :
  sa_ok a -> Zlength (a_lxb a) = LITEXTRA_N -> sublist 0 LITBUFFEREXTRASIZE (a_lxb a) = sp_tail a ->
  sp_n a - LITBUFFEREXTRASIZE <= j <= sp_n a ->
  sublist (j - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE (a_lxb a) = skipn (Z.to_nat j) (a_lits a).
Proof.
  intros Hsa HL Ht Hj. destruct (xfin_ctx a Hsa) as (_ & _ & _ & _ & Hgt & _).
  unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in HL.
  transitivity (sublist (j - (sp_n a - LITBUFFEREXTRASIZE)) LITBUFFEREXTRASIZE
                  (sublist 0 LITBUFFEREXTRASIZE (a_lxb a))).
  { rewrite sublist_sublist by (unfold sp_n, LITBUFFEREXTRASIZE in *; lia). f_equal; lia. }
  rewrite Ht. unfold sp_tail, sp_n in *.
  rewrite sublist_sublist by lia. rewrite <- sublist_skip by lia. f_equal; lia.
Qed.

(* the last literals still split, the head's rest does not fit (lastLLSize > oend - op): the model fails *)
Lemma xfin_herr (a: sa) (cl: list val) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> slast a true w rep' -> xlast a cl true w rep' ->
  sp_cap a - w_K w < sp_lim a - (a_lb a + w_j w) ->
  xpost a (err_code 70) (w_c w) rep'.
Proof.
  intros Hsa _ (_ & _ & Hx) Hlt.
  apply xpost_err; [apply xfin_err70|].
  intros rb m body bo ps ds de Hh. destruct (Hx _ _ _ _ _ _ _ Hh) as (s & Hres & Hr).
  rewrite Hres. destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & _).
  unfold x_last. rewrite Hsp.
  assert (E: (xlim s - xli s >? xe_oend (xenv_a a rb body ps ds de) - xop s) = true)
    by (apply Z.gtb_lt; cbn [xenv_a xe_oend]; lia).
  rewrite E. reflexivity.
Qed.

(* ... it fits: the memmove of the head's rest (lmove), the literals continue in litExtraBuffer *)
Lemma xfin_switch (a: sa) (cl: list val) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> sp_pending a -> slast a true w rep' -> xlast a cl true w rep' ->
  w_K w + (sp_lim a - (a_lb a + w_j w)) <= sp_cap a ->
  xlast a cl false
    {| w_id := w_id w; w_pos := w_pos w; w_lo := w_lo w; w_st := w_st w; w_crep := w_crep w;
       w_K := w_K w + (sp_lim a - (a_lb a + w_j w)); w_j := sp_n a - LITBUFFEREXTRASIZE;
       w_c := put (w_c w) (sp_d a + w_K w) (sublist (a_lb a + w_j w) (sp_lim a) (w_c w)) |} rep'.
Proof.
  intros Hsa _ (_ & (HK & HcN & _) & _) (Hcl & HL & Hx) Hfit.
  destruct (xfin_ctx a Hsa) as (Hd & Hcap & HdN & _ & _ & Hend).
  split; [exact Hcl|]. split; [exact HL|].
  intros rb m body bo ps ds de Hh. destruct (Hx _ _ _ _ _ _ _ Hh) as (s & Hres & Hr).
  destruct Hh as (_ & Hrb & _).
  destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & Hlxb & Hdr & Hho & Hlo).
  set (n1 := sp_lim a - (a_lb a + w_j w)).
  assert (Hn1: xlim s - xli s = n1) by (unfold n1; lia).
  destruct Hlo as (Hli0 & Hlw). rewrite Hlr in Hlw.
  destruct (xm_move_def body (Z.to_nat n1) (xmm s) (xop s) R_dst (xli s)) as (m' & Hmv & Hle & Hw); [lia|lia| |].
  { cbn. rewrite Z2Nat.id by lia. intros q Hq. apply Hlw. unfold WILDCOPY_OVERLENGTH. lia. }
  rewrite Z2Nat.id in Hw by lia.
  exists {| xmm := m'; xop := xop s + n1; xlr := R_lxb; xli := 0; xlim := XLITEXTRA; xsp := false |}.
  split.
  - rewrite Hres. unfold x_last at 1. rewrite Hsp, Hn1.
    assert (E: (n1 >? xe_oend (xenv_a a rb body ps ds de) - xop s) = false)
      by (rewrite Z.gtb_ltb; apply Z.ltb_ge; cbn [xenv_a xe_oend]; lia).
    rewrite E. cbn [xenv_a xe_src]. rewrite Hmv. reflexivity.
  - unfold xrel. cbn [xop xlr xli xlim xsp xmm w_K w_j w_c].
    destruct (xm_move_l body (Z.to_nat n1) (xmm s) m' (xop s) R_dst (xli s) (w_c w) (zbytes body)
      (zbytes (xm_lxb (xmm s))) rb 0 Hmv Hdr (xk_src_rel_any _ _) ltac:(lia)) as [Hlx' Hdr'].
    { rewrite Z2Nat.id by lia. unfold sp_N in *. lia. }
    cbn [reg_l reg_o] in Hdr'.
    rewrite xfin_lmove, Z2Nat.id in Hdr' by (rewrite ?Z2Nat.id; unfold sp_N, WILDCOPY_OVERLENGTH in *; lia).
    replace (rb + xop s) with (sp_d a + w_K w) in Hdr' by lia.
    replace (rb + xli s) with (a_lb a + w_j w) in Hdr' by lia.
    replace (a_lb a + w_j w + n1) with (sp_lim a) in Hdr' by (unfold n1; lia).
    split; [lia|]. split; [unfold XLITEXTRA, LITBUFFEREXTRASIZE; repeat split; lia|].
    split; [congruence|]. split; [exact Hdr'|]. split.
    + destruct Hho as (H1 & H2 & H3 & H4 & H5). unfold xh_ok.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [|eapply xwr_rng_le; eauto].
      intros q Hq. destruct (Z.ltb_spec q (xop s)); [apply (proj1 Hle), H4; lia|apply Hw; lia].
    + unfold xl_ok. split; [unfold XLITEXTRA; lia|]. rewrite Hlx', Hlxb, HL.
      unfold XLITEXTRA, LITEXTRA_N, LITBUFFEREXTRASIZE. lia.
Qed.

(* the last literals from litExtraBuffer do not fit: the model fails *)
Lemma xfin_terr (a: sa) (cl: list val) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> slast a false w rep' -> xlast a cl false w rep' ->
  sp_cap a < w_K w + (sp_n a - w_j w) ->
  xpost a (err_code 70) (w_c w) rep'.
Proof.
  intros Hsa _ (_ & _ & Hx) Hlt.
  apply xpost_err; [apply xfin_err70|].
  intros rb m body bo ps ds de Hh. destruct (Hx _ _ _ _ _ _ _ Hh) as (s & Hres & Hr).
  rewrite Hres. destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & _).
  unfold x_last. rewrite Hsp.
  assert (E: (xlim s - xli s >? xe_oend (xenv_a a rb body ps ds de) - xop s) = true)
    by (apply Z.gtb_lt; cbn [xenv_a xe_oend]; unfold LITBUFFEREXTRASIZE in *; lia).
  rewrite E. reflexivity.
Qed.

(* ... they fit: the memcpy (lfwd from litExtraBuffer), the model's outcome *)
Lemma xfin_ok (a: sa) (cl: list val) (w: sw) (rep': Z * Z * Z) :
  sa_ok a -> sublist 0 LITBUFFEREXTRASIZE (a_lxb a) = sp_tail a -> slast a false w rep' -> xlast a cl false w rep' ->
  w_K w + (sp_n a - w_j w) <= sp_cap a ->
  xpost a (w_K w + (sp_n a - w_j w))
    (put (w_c w) (sp_d a + w_K w) (zbytes (skipn (Z.to_nat (w_j w)) (a_lits a)))) rep'.
Proof.
  intros Hsa Htail (_ & (HK & HcN & (Hj & _) & _) & _) (Hcl & HL & Hx) Hfit.
  destruct (xfin_ctx a Hsa) as (Hd & Hcap & HdN & HN & Hgt & _).
  apply xpost_intro. intros rb m body bo ps ds de Hh.
  destruct (Hx _ _ _ _ _ _ _ Hh) as (s & Hres & Hr).
  destruct Hh as (_ & Hrb & _).
  destruct Hr as (Hop & (Hlr & Hli & Hlim & Hsp) & Hlxb & Hdr & _ & Hlo).
  destruct Hlo as (Hli0 & _).
  set (n := sp_n a - w_j w).
  assert (Hn: xlim s - xli s = n) by (unfold n; lia).
  destruct (xm_fwd_def body (Z.to_nat n) (xmm s) (xop s) R_lxb (xli s)) as (m' & Hfw & Hle & Hw); [lia|lia| |].
  { cbn. rewrite Z2Nat.id, Hlxb, HL by lia. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia. }
  rewrite Hres. unfold x_last at 1. rewrite Hsp. cbv beta iota zeta. rewrite Hn.
  assert (E: (n >? xe_oend (xenv_a a rb body ps ds de) - xop s) = false)
    by (rewrite Z.gtb_ltb; apply Z.ltb_ge; cbn [xenv_a xe_oend]; lia).
  rewrite E, Hlr. cbn [xenv_a xe_src]. rewrite Hfw. cbv beta iota.
  destruct (xm_fwd_l body (Z.to_nat n) (xmm s) m' (xop s) R_lxb (xli s) (w_c w) (zbytes body)
    (zbytes (xm_lxb (xmm s))) rb 0 Hfw Hdr (xk_src_rel_any _ _) ltac:(lia)) as [_ Hdr'].
  { rewrite Z2Nat.id by lia. unfold sp_N in *. lia. }
  cbn [reg_l reg_o] in Hdr'.
  rewrite xfin_lfwd, Z2Nat.id in Hdr'
    by (rewrite ?Z2Nat.id, ?Zlength_map, ?Hlxb, ?HL by lia;
        unfold sp_N, LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  rewrite sublist_map, Hlxb in Hdr'.
  replace (0 + xli s) with (w_j w - (sp_n a - LITBUFFEREXTRASIZE)) in Hdr' by lia.
  replace (w_j w - (sp_n a - LITBUFFEREXTRASIZE) + n) with LITBUFFEREXTRASIZE in Hdr' by (unfold n; lia).
  rewrite xfin_tail in Hdr' by (auto; lia).
  replace (rb + xop s) with (sp_d a + w_K w) in Hdr' by lia.
  split; [unfold is_error_code; apply Z.ltb_ge; unfold n in *; lia|].
  split; [unfold n in *; lia|]. split; [exact Hdr'|reflexivity].
Qed.
End XSteps.
