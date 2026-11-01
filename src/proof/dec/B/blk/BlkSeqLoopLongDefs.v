(* LOOP / long loop: ZSTD_decompressSequencesLong_body cut in segments.
    The body (BlkSeqLoopLongCode.lg_body_eq) is
     lg_pro (if (nbSeq) lg_init (seqNb = 0; ADV loop; MAIN loop; lg_end; seqNb -= seqAdvance; FIN loop; lg_reps);
             lg_epi)
   - la: the arguments (the WITH of seqs_spec and the addresses of the five locals);
   - lfx: what is fixed once the sequences start (the tables t and their pointers tp, the input array split
     into a readable copy sh1 (literals LIn) + the bitstream bit_src sh2 + Ri, litExtraBuffer's contents xc);
   - lst: the loop state (decoder: id decoded, pos/lo/states/repeat offsets; ring sequences[8] holding the
     queue q of the decoded, not yet executed sequences ie..id-1 at slot k mod 8; executor: op = d + K,
     j literals consumed, sw = the split literals switched to litExtraBuffer, c the output array;
     prefetchPos pp);
   - LI: the loop invariant (PROP / LOCAL / SEP lists), the same in the three loops (ADV: ie = 0; MAIN:
     ie = id - min(nbSeq, 8); FIN: id = nbSeq);
   - XI: the epilogue's precondition (exec part only; shared by nbSeq = 0 and nbSeq > 0);
   - the segment statements (SEG_PRO .. SEG_EPI : Prop) and the pure decode step DSTEP, each proved separately.
   la_pend: facts the glue derives from seqs_spec's PRE (hist_ptrs_ok, lit_pos, ext0_ok). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopLongX Zstd.proof.dec.B.blk.BlkSeqLoopLongCode.
Require Import Zstd.proof.model.ExBlock.
Local Open Scope logic.

(* ===================== the arguments ===================== *)

(* la, its accessors and the literal places lit_base / lit_li / lit_lim: BlkSeqLoopLongX *)

(* the precondition's PROPs (seqs_spec) *)
Definition la_ok (a: la) : Prop :=
  let o := a_o a in
  outarr_ok o /\ inwin_ok (a_i a) /\ lits_at (a_l a) (oa_c o) (oa_d o) (oa_cap o) (a_i a) (a_lits a) /\
  0 <= a_bsm a <= ZSTD_BLOCKSIZE_MAX /\ a_n a <= a_bsm a /\ 0 <= a_nb a <= LONGNBSEQ + 65535 /\
  (a_nb a > 0 -> a_os a <> None /\ 0 < oa_cap o) /\ seqs_ok (a_os a) /\ rep_ok (a_rep a) /\
  (a_fe a = 0 \/ a_fe a = 1) /\
  (oa_cap o = 0 -> (pws_pred (a_W a) |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)))) /\
  (0 < oa_cap o -> layout_ok (a_fs a) (oa_base o) (oa_N o) (oa_d o) (a_ps a) (a_x a)).

(* What the glue derives from seqs_spec's PRE (hist_ptrs_ok, lit_pos, ext0_ok via
   BlkSeqLoopCommon.dictend_ok_split): the history pointers, dictEnd either NULL / in the output array /
   inside a non-empty separate dictionary (la_dictend_ok = Common's dictend_ok_ne), or weakly valid in the
   caller's witnesses W; and where in-dst literals lie (they must not be overwritten before they are read). *)
Definition la_dictend_ok (fs: fstate) (o: outarr) (e: ext_seg) : Prop :=
  fs_dictEnd fs = nullval \/
  (exists k, 0 <= k <= oa_N o /\ fs_dictEnd fs = offset_val k (oa_base o)) \/
  (match e with ExtSep _ eb en _ e1 _ => fs_dictEnd fs = offset_val e1 eb /\ 0 <= e1 <= en /\ 0 < en | _ => False end).
Definition la_pend (a: la) : Prop :=
  (is_pointer_or_null (fs_prefixStart (a_fs a)) /\ is_pointer_or_null (fs_virtualStart (a_fs a)) /\
   (la_dictend_ok (a_fs a) (a_o a) (a_x a) \/
    (pws_pred (a_W a) |-- weak_valid_pointer (fs_dictEnd (a_fs a))))) /\
  match a_l a with
  | LDst lb => a_d a + a_bsm a <= lb
  | LSplit lb => a_d a + Z.min (a_bsm a) (a_cap a) - a_n a + WILDCOPY_OVERLENGTH <= lb
  | _ => True
  end.

(* the definedness facts of seqs_spec's precondition: the history, the 32 cells after literals in dst *)
Definition la_dok (a: la) : Prop :=
  hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) /\ lit_slack_def (a_l a) (oa_c (a_o a)) (a_n a).

(* the postcondition (seqs_spec (fun _ => True)) *)
Definition la_post (a: la) : environ -> mpred :=
  let gv := a_gv a in let p := a_p a in let o := a_o a in let i := a_i a in let h := a_h a in
  (EX r: Z, EX oc': list val, EX rep': Z * Z * Z,
   PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = oa_N o; rep_ok rep';
         unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o);
         is_error_code r = false ->
           r <= oa_cap o /\
           unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
           (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
            (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= a_bsm a /\ ext_far (oa_d o) (oa_cap o) (a_bsm a) (hc_ext h))) ->
              exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt);
         oa_cap o = 0 \/
         (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
          ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
         match seqs_model (a_os a) (iw_s i) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
         | Some (cnt, rep2) =>
             Zlength cnt <= a_bsm a ->
             (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
              rep' = rep2) \/
             (is_error_code r = true /\ oa_cap o < Zlength cnt)
         | None => True
         end;
         is_error_code r = true -> dec_err r;
         byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc';
         seqs_exact (a_os a) (a_rep a) (a_l a) (a_lits a) (a_lxb a) (a_nb a) o i h r oc' rep')
   RETURN (Vlong (Int64.repr r))
   SEP (zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a);
        tabs_seq gv p (a_ox a) (a_os a) (if a_nb a =? 0 then a_fe a else 1); dent_of dent_def gv (a_ox a);
        field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p; lit_scratch_x p (a_lxb a);
        data_at (oa_sh o) (tarray tuchar (oa_N o)) oc' (oa_base o);
        data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext h)))%argsassert.

Definition lg_Delta : tycontext := func_tycontext f_ZSTD_decompressSequencesLong_body Vprog LOOP_GB nil.
Definition lg_R (a: la) : ret_assert :=
  frame_ret_assert (function_body_ret_assert tulong (la_post a)) (stackframe_of f_ZSTD_decompressSequencesLong_body).

(* ===================== the tables, with their pointers fixed ===================== *)

(* BlkSeqLoopCommon.seqtabs_borrow puts zstd_globals in the borrowed rest, but the executors and BIT_*
   need zstd_globals between two decodeSequence calls; re-borrowing would lose the pointers the seqState
   holds.  Hence tabs_seq with the three pointers fixed (tp), borrowed around each table use. *)
Definition seq_where_tp (gv: globals) (p: val) (ox: option ddx) (k: seqkind) (t: fse_table) (tp: val) : mpred :=
  EX w: tloc,
  seq_ptr_at p k tp *
  match w with
  | TCtx => !! (tp = ctx_seq k p) && seqspace_at Ews k (Some t) (ctx_seq k p)
  | TDict => !! (ox_seq k ox = Some t /\ tp = dd_seq k (ox_q ox)) && seqspace_at Ews k None (ctx_seq k p)
  | TGlob => !! (t = sk_predef k /\ tp = gv (sk_gdefault k)) && seqspace_at Ews k None (ctx_seq k p)
  end.

Definition tabs_seq_tp (gv: globals) (p: val) (ox: option ddx) (t: fse_table * fse_table * fse_table) (fe: Z)
    (tp: val * val * val) : mpred :=
  let '(a, b, c) := t in let '(pa, pb, pc) := tp in
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p *
  seq_where_tp gv p ox KLL a pa * seq_where_tp gv p ox KOF b pb * seq_where_tp gv p ox KML c pc.

(* TABS (proved separately): *)
Definition TABS_INTRO : Prop :=
  forall gv p ox t fe, tabs_seq gv p ox (Some t) fe |-- EX tp, tabs_seq_tp gv p ox t fe tp.
Definition TABS_ELIM : Prop :=
  forall gv p ox t fe tp, tabs_seq_tp gv p ox t fe tp |-- tabs_seq gv p ox (Some t) fe.
Definition TABS_BORROW : Prop :=
  GLOBALS_obligation ->
  forall gv p ox t fe tp,
  tabs_seq_tp gv p ox t fe tp * dent_of dent_def gv ox * zstd_globals gv |--
  EX sht: share * share * share, EX fm: Z * Z * Z, EX R: mpred,
    !! (seqtabs_sh_ok sht /\
        forall fe': Z,
          field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe')) p * seq_ptrs p tp * seqtabs_at sht t fm tp * R
          |-- tabs_seq_tp gv p ox t fe' tp * dent_of dent_def gv ox * zstd_globals gv) &&
    (field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr fe)) p * seq_ptrs p tp * seqtabs_at sht t fm tp * R).

(* ===================== what is fixed in the sequence phase ===================== *)

Record lfx := mk_lfx {
  x_t: fse_table * fse_table * fse_table; x_tp: val * val * val;
  x_sh1: share; x_sh2: share; x_Ri: mpred; x_xc: list val }.

(* litExtraBuffer's contents (always bytes): the literals (LExtra), the last 65536 of them (LSplit) *)
Definition xc_ok (l: litloc) (lits: list Z) (xc: list val) : Prop :=
  Zlength xc = LITEXTRA_N /\ byte_cells xc /\
  match l with
  | LExtra => sublist 0 (Zlength lits) xc = zbytes lits
  | LSplit _ => sublist 0 LITBUFFEREXTRASIZE xc =
                zbytes (sublist (Zlength lits - LITBUFFEREXTRASIZE) (Zlength lits) lits)
  | _ => True
  end.

Definition lfx_ok (a: la) (x: lfx) : Prop :=
  let i := a_i a in
  a_os a = Some (x_t x) /\ readable_share (x_sh1 x) /\ readable_share (x_sh2 x) /\
  data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) =
    data_at (x_sh1 x) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) *
    bit_src (x_sh2 x) (a_start a) (iw_s i) * x_Ri x /\
  xc_ok (a_l a) (a_lits a) (x_xc x).

(* litExtraBuffer holds lxb (BlkIface.litfields), for the exact model *)
Definition lfx_x (a: la) (x: lfx) : Prop := x_xc x = zbytes (a_lxb a) /\ xl_lxb_ok a.

(* the facts of the precondition the exact steps (BlkSeqLoopLongX) use *)
Lemma xl_ctx_of (a: la) : la_ok a -> xl_lxb_ok a -> xl_ctx a.
Proof.
  intros (H1 & H2 & H3 & _ & _ & H6 & H7 & H8 & H9 & _ & _ & H12) H.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj H7 (conj H8 (conj H9 (conj H12 H)))))))). lia.
Qed.

(* ===================== the literals ===================== *)

Definition lit_code (a: la) (sw: bool) : Z := if sw then LOC_NOT_IN_DST else loc_code (a_l a).

(* the literal fields the loop never writes (as litfields), the location (written at the switch),
   litExtraBuffer as a byte array *)
Definition lit_fix (a: la) : mpred :=
  let p := a_p a in let ob := a_ob a in let ib := iw_base (a_i a) in let n := a_n a in
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr n)) p *
  match a_l a with
  | LIn off =>
      field_at Ews t_dctx (DOT _litPtr) (offset_val off ib) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (off + n) ib) p *
      field_at_ Ews t_dctx (DOT _litBuffer) p
  | LExtra =>
      field_at Ews t_dctx (DOT _litPtr) (lit_extra p) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val n (lit_extra p)) p *
      field_at Ews t_dctx (DOT _litBuffer) (lit_extra p) p
  | LDst lb =>
      field_at Ews t_dctx (DOT _litPtr) (offset_val lb ob) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + n) ob) p *
      field_at Ews t_dctx (DOT _litBuffer) (offset_val lb ob) p
  | LSplit lb =>
      field_at Ews t_dctx (DOT _litPtr) (offset_val lb ob) p *
      field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + (n - LITBUFFEREXTRASIZE)) ob) p *
      field_at Ews t_dctx (DOT _litBuffer) (offset_val lb ob) p
  end.
Definition lit_now (a: la) (xc: list val) (sw: bool) : mpred :=
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a sw))) (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)).

(* ===================== the executor's state (K, j, sw, c) ===================== *)

(* always: op inside [d, oend], the literal position in range, writes only in [d, min(oend, op + 32)), and
   bytes in, bytes out (the output array holds bytes when the arrays it reads do) *)
Definition ex_safe (a: la) (K j: Z) (sw: bool) (c: list val) : Prop :=
  let n := a_n a in
  0 <= K /\ a_d a + K <= a_E a /\ 0 <= j <= n /\
  match a_l a with
  | LSplit _ => if sw then n - LITBUFFEREXTRASIZE <= j else j <= n - LITBUFFEREXTRASIZE
  | _ => sw = false
  end /\
  Zlength c = oa_N (a_o a) /\
  unchanged_outside (oa_c (a_o a)) c (a_d a) (Z.min (a_E a) (a_d a + K + WILDCOPY_OVERLENGTH)) /\
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells c).

(* the cells of the output array the executors read as literals (literals in dst, the split head), with the
   32 cells after them *)
Definition lit_dst_rd (a: la) (c: list val) : Prop :=
  match a_l a with
  | LDst lb => Forall is_byte_val (sublist lb (lb + a_n a + WILDCOPY_OVERLENGTH) c)
  | LSplit lb => Forall is_byte_val (sublist lb (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) c)
  | _ => True
  end.

(* the bytes written so far are defined, and (with a capacity, so with sequences to execute) what the
   executors read: the history before dst, the extDict, the literals in dst (memcpy and memmove are libc.c's
   byte loops).  Literals elsewhere are in arrays the loop does not write (lits_at, litExtraBuffer). *)
Definition ex_def (a: la) (K j: Z) (sw: bool) (c: list val) : Prop :=
  Forall is_byte_val (sublist (a_d a) (a_d a + K) c) /\
  (0 < a_cap a -> Forall is_byte_val (sublist (a_ps a) (a_d a) c) /\ ext_def (a_x a) c /\ lit_dst_rd a c).

(* zbytes are defined bytes *)
Lemma sh_release_zbytes' (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof. induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity]. Qed.

(* the place of the literals in the output array *)
Lemma ex_lits_place (a: la) :
  la_ok a ->
  match a_l a with
  | LDst lb => a_d a <= lb /\ lb + a_n a + WILDCOPY_OVERLENGTH <= a_d a + a_cap a
  | LSplit lb => a_d a <= lb /\ lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH <= a_d a + a_cap a /\
                 LITBUFFEREXTRASIZE < a_n a
  | _ => True
  end.
Proof.
  intros (_ & _ & (_ & _ & Hl) & _). unfold a_d, a_cap, a_n.
  destruct (a_l a) eqn:El; rewrite ?El in *; auto.
  - destruct Hl as (? & ? & _); auto.
  - destruct Hl as (? & ? & ? & _); auto.
Qed.

(* the extDict lies in its array *)
Lemma ex_ext_ok (a: la) (c: list val) :
  la_ok a -> 0 < a_cap a -> Zlength c = oa_N (a_o a) -> exec_ext_ok (a_x a) c.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay) Hcap Hc.
  destruct (Hlay Hcap) as (_ & _ & _ & Hel & Hext). unfold exec_ext_ok, a_x in *. split; [lia|].
  destruct (hc_ext (a_h a)); simpl in *; try tauto; lia.
Qed.

(* at the start: from seqs_spec's hist_def, lits_at and lit_slack_def *)
Lemma ex_def0 (a: la) : la_ok a -> la_dok a -> ex_def a 0 0 false (oa_c (a_o a)).
Proof.
  intros Hok [Hhd Hsl]. split; [rewrite Z.add_0_r, sublist_nil; constructor|]. intros Hcap.
  pose proof (ex_ext_ok a (oa_c (a_o a)) Hok Hcap) as Hxo.
  pose proof (ex_lits_place a Hok) as Hpl.
  destruct Hok as (Ho & _ & (Hlb & _ & Hl) & _ & _ & _ & _ & _ & _ & _ & _ & Hlay).
  destruct (Hlay Hcap) as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & _ & Hod & Hocap & Hodc).
  specialize (Hxo Hoc).
  unfold a_d, a_cap, a_ps, a_x, a_n in *. pose proof (Zlength_nonneg (a_lits a)) as Hzl.
  split; [apply (hist_def_prefix _ _ _ _ Hhd); lia|]. split; [apply (hist_def_ext _ (oa_d (a_o a)) (hc_ps (a_h a))); auto; lia|].
  unfold lit_dst_rd, a_n. destruct (a_l a) as [off| |lb|lb] eqn:El; rewrite ?El in *; auto; simpl in Hsl, Hl.
  - destruct Hl as (_ & _ & Hsub).
    apply (Forall_def_join _ lb (lb + Zlength (a_lits a))); try (unfold WILDCOPY_OVERLENGTH in *; lia); [| exact Hsl].
    rewrite Hsub. apply sh_release_zbytes'. exact Hlb.
  - destruct Hl as (_ & _ & _ & Hsub).
    apply (Forall_def_join _ lb (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE)));
      try (unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia); [| exact Hsl].
    rewrite Hsub. apply sh_release_zbytes'. unfold bytes_ok in *. apply Forall_sublist. exact Hlb.
Qed.

(* a step keeps it: every cell unchanged or a defined byte, the r bytes written defined *)
Lemma ex_def_step (a: la) (K r j j': Z) (sw sw': bool) (c c': list val) :
  la_ok a -> 0 <= K -> 0 <= r -> a_d a + K + r <= Zlength c -> Zlength c = oa_N (a_o a) -> Zlength c' = Zlength c ->
  ex_def a K j sw c -> xd_ub c c' -> Forall is_byte_val (sublist (a_d a + K) (a_d a + K + r) c') ->
  ex_def a (K + r) j' sw' c'.
Proof.
  intros Hok HK Hr Hend Hc Hc' (Hw & Hrd) Hu Hnew.
  assert (Hd0: 0 <= a_d a) by (destruct Hok as ((_ & _ & _ & Hd & _) & _); exact Hd).
  split.
  - replace (a_d a + (K + r)) with (a_d a + K + r) by lia.
    apply (Forall_def_join _ (a_d a) (a_d a + K)); try lia; [| exact Hnew].
    apply (Forall_def_ub c); auto; lia.
  - intros Hcap. destruct (Hrd Hcap) as (Hh & He & Hl).
    pose proof (ex_ext_ok a c Hok Hcap Hc) as Hxo. pose proof (ex_lits_place a Hok) as Hpl.
    assert (HdN: a_d a + a_cap a <= Zlength c) by (destruct Hok as ((_ & Hoc & _ & _ & _ & Hdc) & _); unfold a_d, a_cap; lia).
    assert (Hps: 0 <= a_ps a <= a_d a).
    { destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay). apply (Hlay Hcap). }
    split; [| split].
    + apply (Forall_def_ub c); auto; lia.
    + apply (ext_def_ub _ c); auto.
    + unfold lit_dst_rd in *. destruct (a_l a) eqn:El; rewrite ?El in *; auto; apply (Forall_def_ub c); auto;
        unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia.
Qed.

(* what an execution at op = d + K reads: the history and the extDict *)
Lemma ex_def_hist (a: la) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> 0 < a_cap a -> 0 <= K -> a_d a + K <= Zlength c -> ex_def a K j sw c ->
  Forall is_byte_val (sublist (a_ps a) (a_d a + K) c) /\ ext_def (a_x a) c.
Proof.
  intros Hok Hcap HK Hb (Hw & Hrd). destruct (Hrd Hcap) as (Hh & He & _). split; [| exact He].
  assert (Hps: 0 <= a_ps a <= a_d a).
  { destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay). apply (Hlay Hcap). }
  apply (Forall_def_join _ (a_ps a) (a_d a)); auto; lia.
Qed.

(* ... and the literals, wherever they are; the split head from litPtr on *)
Lemma ex_def_lits (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> xc_ok (a_l a) (a_lits a) xc -> 0 < a_cap a -> 0 <= j <= a_n a -> Zlength c = oa_N (a_o a) ->
  ex_def a K j sw c ->
  match a_l a with
  | LIn off => Forall is_byte_val (sublist (off + j) (off + a_n a + WILDCOPY_OVERLENGTH) (iw_c (a_i a)))
  | LExtra => Forall is_byte_val (sublist j (a_n a + WILDCOPY_OVERLENGTH) xc)
  | LDst lb => Forall is_byte_val (sublist (lb + j) (lb + a_n a + WILDCOPY_OVERLENGTH) c)
  | LSplit lb =>
      (j <= a_n a - LITBUFFEREXTRASIZE ->
       Forall is_byte_val (sublist (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) c)) /\
      (a_n a - LITBUFFEREXTRASIZE <= j ->
       Forall is_byte_val (sublist (j - (a_n a - LITBUFFEREXTRASIZE)) (LITBUFFEREXTRASIZE + WILDCOPY_OVERLENGTH) xc))
  end.
Proof.
  intros Hok (Hxl & Hxb & _) Hcap Hj Hc (_ & Hrd). destruct (Hrd Hcap) as (_ & _ & Hl).
  pose proof (ex_lits_place a Hok) as Hpl.
  assert (HdN: a_d a + a_cap a <= Zlength c) by (destruct Hok as ((_ & Hoc & _ & _ & _ & Hdc) & _); unfold a_d, a_cap; lia).
  assert (Hd0: 0 <= a_d a) by (destruct Hok as ((_ & _ & _ & Hod & _) & _); unfold a_d; lia).
  destruct Hok as (_ & Hi & (Hlb & Hn & Hll) & _). pose proof (Zlength_nonneg (a_lits a)) as Hzl.
  unfold lit_dst_rd, a_n in *. destruct (a_l a) as [off| |lb|lb] eqn:El; rewrite ?El in *.
  - destruct Hll as (Hoff & HoN & Hsub & Hsl). destruct Hi as (_ & _ & _ & _ & HiN & _).
    apply (xd_sub _ off (off + Zlength (a_lits a) + WILDCOPY_OVERLENGTH)); try (unfold WILDCOPY_OVERLENGTH in *; lia).
    apply (Forall_def_join _ off (off + Zlength (a_lits a))); try (unfold WILDCOPY_OVERLENGTH in *; lia); [| exact Hsl].
    rewrite Hsub. apply sh_release_zbytes'. exact Hlb.
  - apply Forall_sublist. exact Hxb.
  - apply (xd_sub _ lb (lb + Zlength (a_lits a) + WILDCOPY_OVERLENGTH)); auto; unfold WILDCOPY_OVERLENGTH in *; lia.
  - split; intros Hj'.
    + apply (xd_sub _ lb (lb + (Zlength (a_lits a) - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH)); auto;
        unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; lia.
    + apply Forall_sublist. exact Hxb.
Qed.

(* the literal precondition of ZSTD_execSequence (literals not the split head), for its literal array ls *)
Lemma ex_def_lit_N (a: la) (xc: list val) (ls: litsrc) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> xc_ok (a_l a) (a_lits a) xc -> 0 < a_cap a -> ex_safe a K j sw c -> ex_def a K j sw c ->
  (match a_l a with LSplit _ => sw = true | _ => True end) ->
  lit_arr ls c = (match a_l a with LIn _ => iw_c (a_i a) | LDst _ => c | _ => xc end) ->
  Forall is_byte_val (sublist (lit_li a sw j) (lit_lim a sw + WILDCOPY_OVERLENGTH) (lit_arr ls c)).
Proof.
  intros Hok Hxc Hcap Hs Hd Hns Hla.
  pose proof Hs as (HK & HKE & Hj & Hsw & Hc & _).
  pose proof (ex_def_lits a xc K j sw c Hok Hxc Hcap Hj Hc Hd) as Hl.
  rewrite Hla. unfold lit_li, lit_lim. destruct (a_l a) eqn:El; rewrite ?El in *; auto.
  subst sw. destruct Hl as (_ & Hl2). apply Hl2. exact Hsw.
Qed.

(* ... and of ZSTD_execSequenceSplitLitBuffer (the split head) *)
Lemma ex_def_lit_S (a: la) (xc: list val) (lb K j: Z) (c: list val) :
  la_ok a -> xc_ok (a_l a) (a_lits a) xc -> 0 < a_cap a -> a_l a = LSplit lb -> ex_safe a K j false c ->
  ex_def a K j false c ->
  Forall is_byte_val (sublist (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) c).
Proof.
  intros Hok Hxc Hcap Hl Hs Hd.
  pose proof Hs as (HK & HKE & Hj & Hsw & Hc & _). rewrite Hl in Hsw.
  pose proof (ex_def_lits a xc K j false c Hok Hxc Hcap Hj Hc Hd) as Hs2. rewrite Hl in Hs2.
  destruct Hs2 as (Hs2 & _). exact (Hs2 Hsw).
Qed.

(* the split literals not yet read are still there *)
Definition lit_intact (a: la) (j: Z) (sw: bool) (c: list val) : Prop :=
  match a_l a with
  | LSplit lb => sw = false ->
      sublist (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE)) c =
      zbytes (sublist j (a_n a - LITBUFFEREXTRASIZE) (a_lits a))
  | _ => True
  end.

(* ===================== the model ===================== *)

#[export] Instance Inhabitant_sequence : Inhabitant sequence := {| sq_ll := 0; sq_ml := 0; sq_ov := 0 |}.

Fixpoint rep_chain (r: Z * Z * Z) (l: list sequence) : Z * Z * Z :=
  match l with nil => r | sq :: t => rep_chain (snd (c_offset r (sq_ll sq) (sq_ov sq))) t end.
(* the C values (ll, ml, offset) of the sequences l, decoded with the repeat offsets r *)
Fixpoint q_of (r: Z * Z * Z) (l: list sequence) : list (Z * Z * Z) :=
  match l with
  | nil => nil
  | sq :: t => (sq_ll sq, sq_ml sq, fst (c_offset r (sq_ll sq) (sq_ov sq))) :: q_of (snd (c_offset r (sq_ll sq) (sq_ov sq))) t
  end.
Definition sum_ll (l: list sequence) : Z := fold_right (fun sq z => sq_ll sq + z) 0 l.
Definition sum_llml (l: list sequence) : Z := fold_right (fun sq z => sq_ll sq + sq_ml sq + z) 0 l.

(* the model decodes the bitstream (the tables t) into seqs *)
Definition DM (a: la) (t: fse_table * fse_table * fse_table) (seqs: list sequence) : Prop :=
  let '(tLL, tOF, tML) := t in decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a) = Some seqs.
(* ... executes them (content |cnt| = cnt_len <= bsm), and the history zstd sees is the model's *)
Definition cnt_len (a: la) (out' lits': list Z) : Z := Zlength out' - Zlength (hc_out (a_h a)) + Zlength lits'.
Definition EM (a: la) (seqs: list sequence) (out' lits': list Z) (rep2: Z * Z * Z) : Prop :=
  let h := a_h a in let o := a_o a in
  exec_seqs (hc_wsize h) (a_rep a) (hc_hist h) (a_lits a) (hc_out h) seqs = Some (out', lits', rep2) /\
  cnt_len a out' lits' <= a_bsm a /\
  hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
  ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h).

(* after ie sequences executed: positions (always), content (when it fits the capacity) *)
Definition ex_model (a: la) (seqs: list sequence) (ie K j: Z) (sw: bool) (c: list val) : Prop :=
  K = sum_llml (sublist 0 ie seqs) /\ j = sum_ll (sublist 0 ie seqs) /\
  forall out' lits' rep2, EM a seqs out' lits' rep2 -> cnt_len a out' lits' <= a_cap a ->
    rep_ok (rep_chain (a_rep a) (sublist 0 ie seqs)) /\
    exists blk, Zlength blk = K /\ sublist (a_d a) (a_d a + K) c = zbytes blk /\
      exec_seqs (hc_wsize (a_h a)) (rep_chain (a_rep a) (sublist 0 ie seqs)) (hc_hist (a_h a))
        (sublist j (a_n a) (a_lits a)) (hc_out (a_h a) ++ blk) (sublist ie (a_nb a) seqs)
        = Some (out', lits', rep2) /\
      lit_intact a j sw c.

(* ===================== the decoder's state ===================== *)

(* a repeat offset after k decodes: a 32-bit value, or (size_t)-1 lowered at most k times (so its U32
   truncation is never 0) *)
Definition rc1 (k v: Z) : Prop := (1 <= v < 2 ^ 32) \/ (SIZE_MAX - k <= v <= SIZE_MAX).
Definition rep_c_ok (k: Z) (r: Z * Z * Z) : Prop := let '(r1, r2, r3) := r in rc1 k r1 /\ rc1 k r2 /\ rc1 k r3.

Definition dec_safe (t: fse_table * fse_table * fse_table) (id pos lo: Z) (st drep: Z * Z * Z) : Prop :=
  states_ok t st /\ rep_c_ok id drep /\ bcons pos lo <= 91 + DSEQ_BITS * id.

(* after id sequences decoded: the model's rest, a ready container; at the end the stream is consumed *)
Definition dec_model (a: la) (t: fse_table * fse_table * fse_table) (seqs: list sequence) (id pos lo: Z)
    (st drep: Z * Z * Z) : Prop :=
  (let '(tLL, tOF, tML) := t in let '(sLL, sOF, sML) := st in
   id < a_nb a ->
   decode_seqs tLL tOF tML (iw_s (a_i a)) (Z.to_nat (a_nb a - id)) sLL sOF sML pos = Some (sublist id (a_nb a) seqs, 0) /\
   bs_ready pos lo) /\
  (id = a_nb a -> pos = 0 /\ lo = 0) /\
  drep = rep_chain (a_rep a) (sublist 0 id seqs).

(* ===================== the ring ===================== *)

#[export] Instance Inhabitant_q3 : Inhabitant (option (Z * Z * Z)) := None.

(* the C cell of a ring slot (plain val tuples: a list of reptype t_seq elaborates very slowly);
   Some e = seqrep3 e, None = default_val t_seq (never written) *)
Definition seqrep3 (e: Z * Z * Z) : val * (val * val) :=
  let '(ll, ml, off) := e in (Vlong (Int64.repr ll), (Vlong (Int64.repr ml), Vlong (Int64.repr off))).
Definition ring_cell (o: option (Z * Z * Z)) : val * (val * val) :=
  match o with Some e => seqrep3 e | None => (Vundef, (Vundef, Vundef)) end.
Definition ring_vals (r: list (option (Z * Z * Z))) : list (val * (val * val)) := map ring_cell r.
(* the queue q (sequences ie, ie+1, ...) at the slots (ie + k) mod 8 *)
Definition ring_ok (ie: Z) (ring: list (option (Z * Z * Z))) (q: list (Z * Z * Z)) : Prop :=
  Zlength ring = 8 /\ forall k, 0 <= k < Zlength q -> Znth ((ie + k) mod 8) ring = Some (Znth k q).
Definition q_safe (q: list (Z * Z * Z)) : Prop :=
  Forall (fun e => let '(ll, ml, off) := e in 0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= off <= SIZE_MAX) q.

(* ===================== the loop state and invariant ===================== *)

Record lst := mk_lst {
  w_id: Z; w_ie: Z;
  w_pos: Z; w_lo: Z; w_st: Z * Z * Z; w_drep: Z * Z * Z;
  w_ring: list (option (Z * Z * Z)); w_q: list (Z * Z * Z);
  w_K: Z; w_j: Z; w_sw: bool; w_c: list val;
  w_pp: Z }.

Definition LI_P (a: la) (x: lfx) (w: lst) : list Prop :=
  [0 <= w_ie w <= w_id w; w_id w <= a_nb a; w_id w - w_ie w <= 8; Zlength (w_q w) = w_id w - w_ie w;
   ring_ok (w_ie w) (w_ring w) (w_q w); q_safe (w_q w);
   dec_safe (x_t x) (w_id w) (w_pos w) (w_lo w) (w_st w) (w_drep w);
   0 <= w_pp w <= 2 ^ 63 - 1 + 2 ^ 19 * w_id w;
   ex_safe a (w_K w) (w_j w) (w_sw w) (w_c w); ex_def a (w_K w) (w_j w) (w_sw w) (w_c w);
   forall seqs, DM a (x_t x) seqs ->
     Zlength seqs = a_nb a /\
     dec_model a (x_t x) seqs (w_id w) (w_pos w) (w_lo w) (w_st w) (w_drep w) /\
     w_q w = q_of (rep_chain (a_rep a) (sublist 0 (w_ie w) seqs)) (sublist (w_ie w) (w_id w) seqs) /\
     ex_model a seqs (w_ie w) (w_K w) (w_j w) (w_sw w) (w_c w);
   (* the exact model (BlkSeqLoopLongX) *)
   xl_inv a (x_t x) (w_id w) (w_K w) (w_c w) (w_drep w) (w_j w) (w_sw w) (w_pos w) (w_lo w) (w_st w) (w_q w)].

(* the locals every segment has *)
Definition L_base (a: la) : list localdef :=
  let o := a_o a in let fs := a_fs a in
  [lvar _sequence__1 t_seq (a_vs1 a); lvar _sequence t_seq (a_vs a);
   lvar _seqState t_seqstate (a_vss a); lvar _sequences (tarray t_seq 8) (a_vsqs a);
   lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a);
   temp _dctx (a_p a); temp _dst (offset_val (oa_d o) (oa_base o));
   temp _maxDstSize (Vlong (Int64.repr (oa_cap o)));
   temp _seqStart (a_start a); temp _seqSize (Vlong (Int64.repr (Zlength (iw_s (a_i a)))));
   temp _nbSeq (Vint (Int.repr (a_nb a))); temp _isLongOffset (Vint (Int.repr 0));
   temp _ostart (offset_val (oa_d o) (oa_base o)); temp _oend (offset_val (a_E a) (oa_base o));
   temp _prefixStart (fs_prefixStart fs); temp _dictStart (fs_virtualStart fs); temp _dictEnd (fs_dictEnd fs)].
(* op and litBufferEnd *)
Definition L_ex (a: la) (K: Z) (sw: bool) : list localdef :=
  [temp _op (offset_val (a_d a + K) (a_ob a)); temp _litBufferEnd (offset_val (lit_lim a sw) (lit_base a sw))].
(* the sequence phase *)
Definition L_seq (a: la) (pp seqNb: Z) : list localdef :=
  [temp _seqAdvance (Vint (Int.repr (a_adv a))); temp _seqNb (Vint (Int.repr seqNb));
   temp _prefetchPos (Vlong (Int64.repr pp))].

Definition LI_L (a: la) (w: lst) (seqNb: Z) : list localdef :=
  L_seq a (w_pp w) seqNb ++ L_ex a (w_K w) (w_sw w) ++ L_base a.

(* the resources that do not change in the sequence phase *)
Definition S_fix (a: la) (x: lfx) : list mpred :=
  let gv := a_gv a in let p := a_p a in let i := a_i a in
  [zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a); dent_of dent_def gv (a_ox a);
   field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (a_rep a)) p;
   data_at (x_sh1 x) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); bit_src (x_sh2 x) (a_start a) (iw_s i);
   x_Ri x; ext_res (a_x a)].

Definition LI_S (a: la) (x: lfx) (w: lst) : list mpred :=
  [data_at Tsh (tptr tuchar) (offset_val (lit_li a (w_sw w) (w_j w)) (lit_base a (w_sw w))) (a_vlp a);
   data_at Tsh (tarray t_seq 8) (ring_vals (w_ring w)) (a_vsqs a);
   seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) (w_pos w) (w_lo w) (w_st w) (x_tp x) (w_drep w) (a_vss a);
   data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seq (a_vs1 a);
   tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x);
   lit_now a (x_xc x) (w_sw w);
   data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) (w_c w) (a_ob a)] ++ S_fix a x.

Definition LI (a: la) (x: lfx) (w: lst) (seqNb: Z) : environ -> mpred :=
  PROPx (LI_P a x w) (LOCALx (LI_L a w seqNb) (SEPx (LI_S a x w))).

(* the phases *)
Definition adv_ph (a: la) (w: lst) : Prop :=
  w_ie w = 0 /\ w_K w = 0 /\ w_j w = 0 /\ w_sw w = false /\ w_c w = oa_c (a_o a).
Definition main_ph (a: la) (w: lst) : Prop := w_ie w = w_id w - a_adv a.
(* FIN: all decoded, and BIT_endOfDStream has seen the stream consumed *)
Definition fin_ph (a: la) (w: lst) : Prop := w_id w = a_nb a /\ w_pos w = 0.

(* LI_P as one Prop *)
Definition LIP (a: la) (x: lfx) (w: lst) : Prop := fold_right and True (LI_P a x w).

(* ===================== the epilogue's precondition ===================== *)

(* the model's sequences (seqs_model's first part) *)
Definition DMg (a: la) (seqs: list sequence) : Prop :=
  (if a_nb a =? 0 then Some nil else
   match a_os a with
   | Some (tLL, tOF, tML) => decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)
   | None => None
   end) = Some seqs.

(* all sequences executed: positions; when the content fits, the bytes so far, the literals left, the
   repeat offsets rep' (the context's field) *)
Definition XM (a: la) (K j: Z) (sw: bool) (c: list val) (rep': Z * Z * Z) : Prop :=
  let h := a_h a in let o := a_o a in
  forall seqs, DMg a seqs ->
    K = sum_llml seqs /\ j = sum_ll seqs /\
    forall out' lits' rep2,
      exec_seqs (hc_wsize h) (a_rep a) (hc_hist h) (a_lits a) (hc_out h) seqs = Some (out', lits', rep2) ->
      cnt_len a out' lits' <= a_bsm a ->
      (oa_cap o = 0 \/
       (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
        ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h))) ->
      cnt_len a out' lits' <= oa_cap o ->
      rep' = rep2 /\
      exists blk, Zlength blk = K /\ sublist (a_d a) (a_d a + K) c = zbytes blk /\
        out' = hc_out h ++ blk /\ lits' = sublist j (a_n a) (a_lits a) /\ lit_intact a j sw c.

Definition XI_P (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val) (rep': Z * Z * Z) : list Prop :=
  [xc_ok (a_l a) (a_lits a) xc; ex_safe a K j sw c; ex_def a K j sw c; rep_ok rep'; XM a K j sw c rep';
   xc = zbytes (a_lxb a); xl_lxb_ok a; xl_aft a K c rep' j sw].

Definition XI_S (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val) (fe': Z) (rep': Z * Z * Z)
    : list mpred :=
  let gv := a_gv a in let p := a_p a in let i := a_i a in
  [data_at Tsh (tptr tuchar) (offset_val (lit_li a sw j) (lit_base a sw)) (a_vlp a);
   data_at_ Tsh (tarray t_seq 8) (a_vsqs a); data_at_ Tsh t_seqstate (a_vss a);
   data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seq (a_vs1 a);
   zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a); tabs_seq gv p (a_ox a) (a_os a) fe';
   dent_of dent_def gv (a_ox a); field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p;
   lit_now a xc sw; data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a);
   data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (a_x a)].

Definition XI (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val) (fe': Z) (rep': Z * Z * Z)
    : environ -> mpred :=
  PROPx (XI_P a xc K j sw c rep') (LOCALx (L_ex a K sw ++ L_base a) (SEPx (XI_S a xc K j sw c fe' rep'))).

(* the U32 truncation of the decoder's repeat offsets (saved into the context) *)
Definition rep_trunc (r: Z * Z * Z) : Z * Z * Z :=
  let '(r1, r2, r3) := r in (r1 mod 2 ^ 32, r2 mod 2 ^ 32, r3 mod 2 ^ 32).

(* ===================== the precondition after start_function ===================== *)

Definition L_pre (a: la) : list localdef :=
  let o := a_o a in
  [lvar _sequence__1 t_seq (a_vs1 a); lvar _sequence t_seq (a_vs a);
   lvar _seqState t_seqstate (a_vss a); lvar _sequences (tarray t_seq 8) (a_vsqs a);
   lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a);
   temp _dctx (a_p a); temp _dst (offset_val (oa_d o) (oa_base o));
   temp _maxDstSize (Vlong (Int64.repr (oa_cap o)));
   temp _seqStart (offset_val (iw_off (a_i a)) (iw_base (a_i a)));
   temp _seqSize (Vlong (Int64.repr (Zlength (iw_s (a_i a)))));
   temp _nbSeq (Vint (Int.repr (a_nb a))); temp _isLongOffset (Vint (Int.repr 0))].

Definition S_pre (a: la) : list mpred :=
  let gv := a_gv a in let p := a_p a in let o := a_o a in let i := a_i a in
  [data_at_ Tsh t_seq (a_vs1 a); data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seqstate (a_vss a);
   data_at_ Tsh (tarray t_seq 8) (a_vsqs a); data_at_ Tsh (tptr tuchar) (a_vlp a);
   zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a); tabs_seq gv p (a_ox a) (a_os a) (a_fe a);
   dent_of dent_def gv (a_ox a); field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (a_rep a)) p;
   litfields p (oa_base o) (iw_base i) (a_l a) (a_lits a) (a_lxb a);
   data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o);
   data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (hc_ext (a_h a))].

(* the state when the sequences start (after the prologue, tables and input split) *)
Definition S_init (a: la) (x: lfx) : list mpred :=
  [data_at Tsh (tptr tuchar) (offset_val (lit_li a false 0) (lit_base a false)) (a_vlp a);
   data_at_ Tsh (tarray t_seq 8) (a_vsqs a); data_at_ Tsh t_seqstate (a_vss a);
   data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seq (a_vs1 a);
   tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) (a_fe a) (x_tp x);
   lit_now a (x_xc x) false;
   data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) (oa_c (a_o a)) (a_ob a)] ++ S_fix a x.

(* ===================== the decode step (pure; proved separately) ===================== *)

(* one ZSTD_decodeSequence (last iff id = nbSeq - 1) from a decoder state of the invariant: the new state
   is the invariant's at id + 1, the offset a size_t value, and under the model the sequence is the model's
   sequence id (the queue grows by its C values) *)
Definition DSTEP : Prop :=
  forall (a: la) (x: lfx) (id pos lo: Z) (st drep: Z * Z * Z) (ll ml ov pos' lo': Z) (st': Z * Z * Z),
    la_ok a -> lfx_ok a x -> 0 <= id < a_nb a ->
    dec_safe (x_t x) id pos lo st drep ->
    (forall seqs, DM a (x_t x) seqs -> Zlength seqs = a_nb a /\ dec_model a (x_t x) seqs id pos lo st drep) ->
    0 <= lo -> lo mod 8 = 0 -> pos <= lo + 64 ->
    (* ZSTD_decodeSequence's postcondition *)
    0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= ov < 2 ^ 32 -> states_ok (x_t x) st' ->
    pos - DSEQ_BITS <= pos' <= pos -> 0 <= lo' <= lo -> (id = a_nb a - 1 -> st' = st) ->
    (bs_ready pos lo ->
     forall sq stn pn,
       (let '(tLL, tOF, tML) := x_t x in let '(sLL, sOF, sML) := st in
        dseq_one tLL tOF tML (iw_s (a_i a)) (id =? a_nb a - 1) sLL sOF sML pos) = Some (sq, stn, pn) ->
       ll = sq_ll sq /\ ml = sq_ml sq /\ ov = sq_ov sq /\ pos' = pn /\
       ((id =? a_nb a - 1) = false -> st' = stn /\ bs_ready pos' lo')) ->
    1 <= fst (c_offset drep ll ov) <= SIZE_MAX /\
    dec_safe (x_t x) (id + 1) pos' lo' st' (snd (c_offset drep ll ov)) /\
    forall seqs, DM a (x_t x) seqs ->
      dec_model a (x_t x) seqs (id + 1) pos' lo' st' (snd (c_offset drep ll ov)) /\
      sq_ll (Znth id seqs) = ll /\ sq_ml (Znth id seqs) = ml /\ sq_ov (Znth id seqs) = ov /\
      forall ie, 0 <= ie <= id ->
        q_of (rep_chain (a_rep a) (sublist 0 ie seqs)) (sublist ie (id + 1) seqs) =
        q_of (rep_chain (a_rep a) (sublist 0 ie seqs)) (sublist ie id seqs) ++ [(ll, ml, fst (c_offset drep ll ov))].

(* ===================== the segments (each proved separately) ===================== *)

(* PRO: lg_pro, from the precondition to the locals set (litPtr, oend, ...); litExtraBuffer as bytes *)
Definition SEG_PRO : Prop :=
  forall (Espec: OracleKind) (a: la) (REST: statement),
    la_ok a -> la_pend a ->
    (forall xc, xc_ok (a_l a) (a_lits a) xc -> xc = zbytes (a_lxb a) -> xl_lxb_ok a ->
       semax lg_Delta (PROPx [] (LOCALx (L_ex a 0 false ++ L_base a)
                                   (SEPx (XI_S a xc 0 0 false (oa_c (a_o a)) (a_fe a) (a_rep a)))))
         REST (lg_R a)) ->
    semax lg_Delta (PROPx [] (LOCALx (L_pre a) (SEPx (S_pre a)))) (lg_pro REST) (lg_R a).

(* INIT: lg_init (nbSeq > 0): seqAdvance, prefetchPos, fseEntropy = 1, prevOffset, BIT_initDStream
   (an error returns), the three initFseState; then REST (seqNb = 0; the loops ...) from LI with id = 0 *)
Definition SEG_INIT : Prop :=
  TABS_ELIM -> TABS_BORROW ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (REST: statement) (R: ret_assert),
    GLOBALS_obligation -> la_ok a -> la_pend a -> la_dok a -> lfx_ok a x -> lfx_x a x -> 0 < a_nb a ->
    RA_return R = RA_return (lg_R a) ->
    (forall w, LIP a x w -> adv_ph a w -> w_id w = 0 ->
       semax lg_Delta
         (PROPx [] (LOCALx ([temp _seqAdvance (Vint (Int.repr (a_adv a)));
                             temp _prefetchPos (Vlong (Int64.repr (w_pp w)))] ++ L_ex a 0 false ++ L_base a)
                     (SEPx (LI_S a x w))))
         REST R) ->
    semax lg_Delta (PROPx [] (LOCALx (L_ex a 0 false ++ L_base a) (SEPx (S_init a x)))) (lg_init REST) R.

(* ADV: one iteration of the prepare loop (decode, prefetch, store at sequences[seqNb]) *)
Definition SEG_ADV : Prop :=
  TABS_BORROW -> DSTEP ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> adv_ph a w -> w_id w < a_adv a ->
    semax lg_Delta (LI a x w (w_id w)) lg_adv_body
      (normal_ret_assert
         (EX w': lst, PROPx (LI_P a x w' ++ [adv_ph a w'; w_id w' = w_id w + 1])
                        (LOCALx (LI_L a w' (w_id w)) (SEPx (LI_S a x w'))))).

(* MAIN: one iteration of the main loop: decode sequence id, execute sequence ie = id - 8 (the split
   handling), prefetch, store; an error returns *)
Definition SEG_MAIN : Prop :=
  TABS_ELIM -> TABS_BORROW -> DSTEP ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst) (R: ret_assert),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> main_ph a w -> w_id w < a_nb a ->
    RA_normal R = (EX w': lst, PROPx (LI_P a x w' ++ [main_ph a w'; w_id w' = w_id w + 1])
                                 (LOCALx (LI_L a w' (w_id w)) (SEPx (LI_S a x w')))) ->
    RA_return R = RA_return (lg_R a) ->
    semax lg_Delta (LI a x w (w_id w))
      (Ssequence lg_main_dec (Ssequence lg_main_chk (Sifthenelse (Etempvar _t'17 tint) lg_main_x1 lg_main_x2))) R.

(* END: BIT_endOfDStream after the main loop (an error returns) *)
Definition SEG_END : Prop :=
  TABS_ELIM ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> main_ph a w -> w_id w = a_nb a -> 0 < a_nb a ->
    semax lg_Delta (LI a x w (a_nb a)) lg_end
      (overridePost (PROPx (LI_P a x w ++ [w_pos w = 0]) (LOCALx (LI_L a w (a_nb a)) (SEPx (LI_S a x w)))) (lg_R a)).

(* FIN: one iteration of the queue loop: execute sequence ie (the split handling); an error returns *)
Definition SEG_FIN : Prop :=
  TABS_ELIM ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst) (R: ret_assert),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> fin_ph a w -> w_ie w < a_nb a ->
    RA_normal R = (EX w': lst, PROPx (LI_P a x w' ++ [fin_ph a w'; w_ie w' = w_ie w + 1])
                                 (LOCALx (LI_L a w' (w_ie w)) (SEPx (LI_S a x w')))) ->
    RA_return R = RA_return (lg_R a) ->
    semax lg_Delta (LI a x w (w_ie w))
      (Ssequence lg_fin_pre (Ssequence lg_fin_chk (Sifthenelse (Etempvar _t'27 tint) lg_fin_x1 lg_fin_x2))) R.

(* REPS: save the repeat offsets; give back the tables and the input array: the epilogue's XI *)
Definition SEG_REPS : Prop :=
  TABS_ELIM ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> fin_ph a w -> w_ie w = a_nb a -> 0 < a_nb a ->
    semax lg_Delta (LI a x w (a_nb a)) lg_reps
      (normal_ret_assert (XI a (x_xc x) (w_K w) (w_j w) (w_sw w) (w_c w) 1 (rep_trunc (w_drep w)))).

(* EPI: the last literals (split: the rest in dst, then litExtraBuffer), the result *)
Definition SEG_EPI : Prop :=
  forall (Espec: OracleKind) (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val) (rep': Z * Z * Z),
    la_ok a -> la_pend a ->
    semax lg_Delta (XI a xc K j sw c (if a_nb a =? 0 then a_fe a else 1) rep') lg_epi (lg_R a).
