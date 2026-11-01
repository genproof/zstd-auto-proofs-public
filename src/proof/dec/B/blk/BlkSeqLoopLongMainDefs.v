(* LOOP / long loop, part MAIN:
   one iteration of the main loop cut in parts, each a Prop proved in its own file, assembled in
   BlkSeqLoopLongMain.v (lg_main_ok : SEG_MAIN).

   MAIN body = lg_main_dec; lg_main_chk; if (t'17) lg_main_x1 else lg_main_x2:
   - P_DEC  (BlkSeqLoopLongMainDec.v): ZSTD_decodeSequence(&sequence__1): LI -> MD (decoder at id + 1, the
     new sequence e in sequence__1; the queue q of 8 still in the ring);
   - lg_main_chk: t'17 = location == split && litBufferEnd - litPtr < head.litLength (lg_cut);
   - P_X1 / P_X2 (BlkSeqLoopLongMainX1.v / X2.v): execute the queue head (sequence ie, ring slot ie mod 8)
     from MD, error returns, then P_TAIL;
   - P_TAIL (BlkSeqLoopLongMainTail.v): prefetchMatch(&sequence__1), seqCopy into slot id mod 8, op += r:
     XS -> the next LI (w_next);
   - the pure executor steps XSTEP (BlkSeqLoopLongXstep.v, shared with FIN): from XP (the executor facts of
     LI_P with the head e0) and the executor's postcondition to XQ (the executor facts at ie + 1) or XERR
     (the facts of la_post for an error return);
   - P_INV (BlkSeqLoopLongMainInv.v): XP from LI_P (lg_xp_of) and LI_P of w_next from MD + XQ.
   All parts are proved in lg_Delta (with the final COPY / EXEC specs, Defs v3 with bytes in / bytes out,
   dec_err, ext_far). *)
Require Export Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs.
Local Open Scope logic.

(* ===================== after the decode (P_DEC) ===================== *)

(* the decoder after decoding sequence id (= w_id w): position, container, states, repeat offsets;
   the decoded sequence e = (ll, ml, off) (C values) *)
Record ldec := mk_ldec { d_pos: Z; d_lo: Z; d_st: Z * Z * Z; d_rep: Z * Z * Z; d_ll: Z; d_ml: Z; d_off: Z }.
Definition d_e (dd: ldec) : Z * Z * Z := (d_ll dd, d_ml dd, d_off dd).

Definition MD_P (a: la) (x: lfx) (w: lst) (dd: ldec) : list Prop :=
  LI_P a x w ++
  [main_ph a w; w_id w < a_nb a;
   dec_safe (x_t x) (w_id w + 1) (d_pos dd) (d_lo dd) (d_st dd) (d_rep dd);
   q_safe [d_e dd];
   forall seqs, DM a (x_t x) seqs ->
     dec_model a (x_t x) seqs (w_id w + 1) (d_pos dd) (d_lo dd) (d_st dd) (d_rep dd) /\
     w_q w ++ [d_e dd] = q_of (rep_chain (a_rep a) (sublist 0 (w_ie w) seqs)) (sublist (w_ie w) (w_id w + 1) seqs);
   (* the exact model: the decoded sequence joins the queue (BlkSeqLoopLongX.xl_dec_step) *)
   xl_inv a (x_t x) (w_id w + 1) (w_K w) (w_c w) (d_rep dd) (w_j w) (w_sw w) (d_pos dd) (d_lo dd) (d_st dd)
     (w_q w ++ [d_e dd])].

Definition MD_S (a: la) (x: lfx) (w: lst) (dd: ldec) : list mpred :=
  [data_at Tsh (tptr tuchar) (offset_val (lit_li a (w_sw w) (w_j w)) (lit_base a (w_sw w))) (a_vlp a);
   data_at Tsh (tarray t_seq 8) (ring_vals (w_ring w)) (a_vsqs a);
   seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) (d_pos dd) (d_lo dd) (d_st dd) (x_tp x) (d_rep dd) (a_vss a);
   data_at_ Tsh t_seq (a_vs a); data_at Tsh t_seq (seqrep (d_ll dd) (d_ml dd) (d_off dd)) (a_vs1 a);
   tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x);
   lit_now a (x_xc x) (w_sw w);
   data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) (w_c w) (a_ob a)] ++ S_fix a x.

Definition MD (a: la) (x: lfx) (w: lst) (dd: ldec) : environ -> mpred :=
  PROPx (MD_P a x w dd) (LOCALx (LI_L a w (w_id w)) (SEPx (MD_S a x w dd))).

Definition P_DEC : Prop :=
  TABS_BORROW -> DSTEP ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> LIP a x w -> main_ph a w -> w_id w < a_nb a ->
    semax lg_Delta (LI a x w (w_id w)) lg_main_dec (normal_ret_assert (EX dd: ldec, MD a x w dd)).

(* ===================== the branch (lg_main_chk) ===================== *)

(* t'17: the split literals are switched to litExtraBuffer before the head (ll of ring slot ie mod 8) *)
Definition lg_cut (a: la) (w: lst) : Prop :=
  match a_l a with
  | LSplit _ => w_sw w = false /\ lit_lim a false - lit_li a false (w_j w) < fst (fst (Znth 0 (w_q w)))
  | _ => False
  end.

(* ===================== after the execution (P_TAIL) ===================== *)

(* the next state: decoder dd, sequence e stored at slot id mod 8, queue tl q ++ [e], executor (K', j', sw', c'),
   prefetchPos advanced by e's ll + ml *)
Definition w_next (w: lst) (dd: ldec) (K' j': Z) (sw': bool) (c': list val) : lst :=
  mk_lst (w_id w + 1) (w_ie w + 1) (d_pos dd) (d_lo dd) (d_st dd) (d_rep dd)
    (upd_Znth (w_id w mod 8) (w_ring w) (Some (d_e dd))) (tl (w_q w) ++ [d_e dd])
    K' j' sw' c' (w_pp w + d_ll dd + d_ml dd).

(* the tail of both branches (x1: tq = _t'11, osz = _oneSeqSize; x2: _t'16, _oneSeqSize__1):
   prefetchPos = ZSTD_prefetchMatch(prefetchPos, &sequence__1, prefixStart, dictEnd);
   ZSTD_seqCopy(&sequences[seqNb & 7], &sequence__1); op += oneSeqSize *)
Definition lg_tail (tq osz: ident) : statement :=
  Ssequence
    (Ssequence
       (Scall (Some tq)
          (Evar _ZSTD_prefetchMatch
             (Tfunction (tulong :: tptr t_seq :: tptr tuchar :: tptr tuchar :: nil) tulong cc_default))
          (Etempvar _prefetchPos tulong :: Eaddrof (Evar _sequence__1 t_seq) (tptr t_seq) ::
           Etempvar _prefixStart (tptr tuchar) :: Etempvar _dictEnd (tptr tuchar) :: nil))
       (Sset _prefetchPos (Etempvar tq tulong)))
    (Ssequence
       (Scall None
          (Evar _ZSTD_seqCopy (Tfunction (tptr t_seq :: tptr t_seq :: nil) tvoid cc_default))
          (Ebinop Oadd (Evar _sequences (tarray t_seq 8))
             (Ebinop Oand (Etempvar _seqNb tint)
                (Ebinop Osub (Econst_int (Int.repr 8) tint) (Econst_int (Int.repr 1) tint) tint) tint)
             (tptr t_seq) ::
           Eaddrof (Evar _sequence__1 t_seq) (tptr t_seq) :: nil))
       (Sset _op (Ebinop Oadd (Etempvar _op (tptr tuchar)) (Etempvar osz tulong) (tptr tuchar)))).

Definition tail_ids (tq osz: ident) : Prop := (tq, osz) = (_t'11, _oneSeqSize) \/ (tq, osz) = (_t'16, _oneSeqSize__1).

(* after a successful execution: op = d + Kop, oneSeqSize = r (Kop + r = K'), the executor at (K', j', sw', c'),
   the pure facts of the next state; ring slot id mod 8 (the executed head) is free *)
Definition XS (a: la) (x: lfx) (w: lst) (dd: ldec) (K' j': Z) (sw': bool) (c': list val) (Kop r: Z) (osz: ident)
    : environ -> mpred :=
  let w' := w_next w dd K' j' sw' c' in
  PROPx (LI_P a x w' ++ [main_ph a w; w_id w < a_nb a; Kop + r = K'; 0 <= r <= Int64.max_unsigned;
                         0 <= w_pp w <= 2 ^ 63 - 1 + 2 ^ 19 * w_id w; q_safe [d_e dd]])
  (LOCALx (temp osz (Vlong (Int64.repr r)) :: temp _op (offset_val (a_d a + Kop) (a_ob a)) ::
           L_seq a (w_pp w) (w_id w) ++
           [temp _litBufferEnd (offset_val (lit_lim a sw') (lit_base a sw'))] ++ L_base a)
  (SEPx ([data_at Tsh (tptr tuchar) (offset_val (lit_li a sw' j') (lit_base a sw')) (a_vlp a);
          data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth (w_id w mod 8) (w_ring w) None)) (a_vsqs a);
          seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) (d_pos dd) (d_lo dd) (d_st dd) (x_tp x) (d_rep dd)
            (a_vss a);
          data_at_ Tsh t_seq (a_vs a); data_at Tsh t_seq (seqrep (d_ll dd) (d_ml dd) (d_off dd)) (a_vs1 a);
          tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x);
          lit_now a (x_xc x) sw';
          data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c' (a_ob a)] ++ S_fix a x))).

Definition P_TAIL : Prop :=
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst) (dd: ldec) (K' j': Z) (sw': bool) (c': list val)
         (Kop r: Z) (tq osz: ident),
    la_ok a -> la_pend a -> lfx_ok a x -> tail_ids tq osz ->
    semax lg_Delta (XS a x w dd K' j' sw' c' Kop r osz) (lg_tail tq osz)
      (normal_ret_assert
         (EX w': lst, PROPx (LI_P a x w' ++ [main_ph a w'; w_id w' = w_id w + 1])
                        (LOCALx (LI_L a w' (w_id w)) (SEPx (LI_S a x w'))))).

(* ===================== the executor's steps (XSTEP, pure; shared with FIN) ===================== *)

(* the executor's facts before executing the queue head e0 = (ll, ml, off) = sequence ie *)
Definition XP (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (e0: Z * Z * Z) : Prop :=
  let '(ll, ml, off) := e0 in
  0 <= ie < a_nb a /\ ex_safe a K j sw c /\ ex_def a K j sw c /\
  0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= off <= SIZE_MAX /\
  forall seqs, DM a (x_t x) seqs ->
    Zlength seqs = a_nb a /\ 1 <= sq_ov (Znth ie seqs) < 2 ^ 32 /\
    ll = sq_ll (Znth ie seqs) /\ ml = sq_ml (Znth ie seqs) /\
    off = fst (c_offset (rep_chain (a_rep a) (sublist 0 ie seqs)) ll (sq_ov (Znth ie seqs))) /\
    ex_model a seqs ie K j sw c.

(* ... after it (ie the index of the next sequence) *)
Definition XQ (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) : Prop :=
  ex_safe a K j sw c /\ ex_def a K j sw c /\ forall seqs, DM a (x_t x) seqs -> ex_model a seqs ie K j sw c.

(* an error return with the output array c: la_post's facts *)
Definition XERR (a: la) (c: list val) : Prop :=
  let o := a_o a in let h := a_h a in
  unchanged_outside (oa_c o) c (oa_d o) (oa_d o + oa_cap o) /\
  (oa_cap o = 0 \/
   (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
    ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
   match seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
   | Some (cnt, _) => Zlength cnt <= a_bsm a -> oa_cap o < Zlength cnt
   | None => True
   end) /\
  (byte_cells (oa_c o) -> byte_cells (iw_c (a_i a)) -> ext_bytes (hc_ext h) -> byte_cells c).

(* where execSequence reads the literals when they are not the split head (LSplit: switched) *)
Definition lsrc (a: la) (x: lfx) : litsrc :=
  match a_l a with
  | LIn _ => LitSep (x_sh1 x) (iw_base (a_i a)) (iw_c (a_i a))
  | LDst _ => LitIn
  | _ => LitSep Ews (lit_extra (a_p a)) (x_xc x)
  end.

(* not the split head: not LSplit, or switched *)
Definition nosplit (a: la) (sw: bool) : Prop := match a_l a with LSplit _ => sw = true | _ => True end.

(* the leftover copy's result: c1 = c with [k, k + lo) := the split literals [li, li + lo) (safecopyDstBeforeSrc's POST) *)
Definition copied (c c1: list val) (k li lo: Z) : Prop :=
  Zlength c1 = Zlength c /\
  (lo < WILDCOPY_OVERLENGTH \/ li - k <= WILDCOPY_VECLEN \/ WILDCOPY_OVERLENGTH <= li - k ->
     sublist k (k + lo) c1 = sublist k (k + lo) (listcopy c li k (Z.to_nat lo))) /\
  (Forall is_byte_val (sublist li (li + lo) c) -> Forall is_byte_val (sublist k (k + lo) c1)) /\
  unchanged_outside c c1 k (k + lo).

Definition XSTEP : Prop :=
  forall (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z),
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (* (N) ZSTD_execSequence on the head, literals not the split head *)
  (nosplit a sw ->
   let li := lit_li a sw j in let lim := lit_lim a sw in let ls := lsrc a x in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_err k E li lim ll ml off ps elen = true -> unchanged_outside c c' k E -> XERR a c') /\
   (exec_err k E li lim ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       sublist k (k + (ll + ml)) c' =
         sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c')) /\
  (* (S) ZSTD_execSequenceSplitLitBuffer: the split head holds the literals *)
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_li a false j + ll <= lit_lim a false ->
   let li := lit_li a false j in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_split_err k E li ll ml off ps elen = true -> unchanged_outside c c' k E -> XERR a c') /\
   (exec_split_err k E li ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       (lit_exact_split k li ll ->
          sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps xs)) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) false c')) /\
  (* (X1) the split head ends before the head's literals: the leftover lo, switch, execSequence on litExtraBuffer *)
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_lim a false - lit_li a false j < ll ->
   let li := lit_li a false j in let lo := lit_lim a false - li in
   (0 < lo -> E - k < lo -> XERR a c) /\
   forall c1, (lo = 0 -> c1 = c) -> (0 < lo -> lo <= E - k /\ copied c c1 k li lo) ->
   let k1 := k + lo in let ls := lsrc a x in let li1 := lit_li a true (j + lo) in let lim1 := lit_lim a true in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c1 -> byte_cells (lit_arr ls c1) -> ext_bytes xs -> byte_cells c') -> xd_ub c1 c' ->
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = true -> unchanged_outside c1 c' k1 E -> XERR a c') /\
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = false ->
    unchanged_outside c1 c' k1 (Z.min E (k1 + (ll - lo + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c') ->
    (ext_read_ok xs k1 E (ll - lo) ml off ps ->
       sublist k1 (k1 + (ll - lo + ml)) c' =
         sublist k1 (k1 + (ll - lo + ml)) (exec_c c1 k1 (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k1 c1) -> Forall is_byte_val (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ->
        ext_def xs c1 -> Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c'))) ->
    XQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c')).

(* ===================== the invariant's plumbing (P_INV, pure) ===================== *)

Definition P_INV : Prop :=
  forall (a: la) (x: lfx) (w: lst) (dd: ldec),
    la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> fold_right and True (MD_P a x w dd) ->
    XP a x (w_ie w) (w_K w) (w_j w) (w_sw w) (w_c w) (Znth 0 (w_q w)) /\
    w_ie w mod 8 = w_id w mod 8 /\ Znth (w_id w mod 8) (w_ring w) = Some (Znth 0 (w_q w)) /\
    (* the exact model with the queue head apart *)
    xl_ctx a /\ xl_pos a (w_K w) (w_j w) (w_sw w) (w_c w) /\
    xl_inv a (x_t x) (w_id w + 1) (w_K w) (w_c w) (d_rep dd) (w_j w) (w_sw w) (d_pos dd) (d_lo dd) (d_st dd)
      (Znth 0 (w_q w) :: (tl (w_q w) ++ [d_e dd])) /\
    forall K' j' sw' c',
      XQ a x (w_ie w + 1) K' j' sw' c' ->
      xl_inv a (x_t x) (w_id w + 1) K' c' (d_rep dd) j' sw' (d_pos dd) (d_lo dd) (d_st dd) (tl (w_q w) ++ [d_e dd]) ->
      LIP a x (w_next w dd K' j' sw' c').

(* ===================== the two branches ===================== *)

Definition P_X1 : Prop :=
  TABS_ELIM -> XSTEP -> P_INV -> P_TAIL ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst) (dd: ldec) (R: ret_assert),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> lg_cut a w ->
    RA_normal R = (EX w': lst, PROPx (LI_P a x w' ++ [main_ph a w'; w_id w' = w_id w + 1])
                                 (LOCALx (LI_L a w' (w_id w)) (SEPx (LI_S a x w')))) ->
    RA_return R = RA_return (lg_R a) ->
    semax lg_Delta (MD a x w dd) lg_main_x1 R.

Definition P_X2 : Prop :=
  TABS_ELIM -> XSTEP -> P_INV -> P_TAIL ->
  forall (Espec: OracleKind) (a: la) (x: lfx) (w: lst) (dd: ldec) (R: ret_assert),
    GLOBALS_obligation -> la_ok a -> la_pend a -> lfx_ok a x -> lfx_x a x -> ~ lg_cut a w ->
    RA_normal R = (EX w': lst, PROPx (LI_P a x w' ++ [main_ph a w'; w_id w' = w_id w + 1])
                                 (LOCALx (LI_L a w' (w_id w)) (SEPx (LI_S a x w')))) ->
    RA_return R = RA_return (lg_R a) ->
    semax lg_Delta (MD a x w dd) lg_main_x2 R.

(* the tails of the two branches are lg_tail *)
Lemma lg_x1_tail :
  match lg_main_x1 with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ T)))))) =>
      T = lg_tail _t'11 _oneSeqSize
  | _ => False
  end.
Proof. reflexivity. Qed.

Lemma lg_x2_tail :
  match lg_main_x2 with Ssequence _ (Ssequence _ T) => T = lg_tail _t'16 _oneSeqSize__1 | _ => False end.
Proof. reflexivity. Qed.

(* the branches' R made concrete: normal = R's, the rest lg_R's (forward on a return then sees the function's
   postcondition with the stack frame) *)
Lemma lg_R_concrete {Espec: OracleKind} (a: la) (P: environ -> mpred) (c: statement) (R: ret_assert) :
  RA_return R = RA_return (lg_R a) ->
  semax lg_Delta P c (overridePost (RA_normal R) (lg_R a)) -> semax lg_Delta P c R.
Proof.
  intros HR H. eapply semax_post; [| | | | exact H].
  - destruct R; simpl. intro rho. apply andp_left2. apply derives_refl.
  - unfold lg_R, frame_ret_assert, function_body_ret_assert, overridePost. simpl.
    intro rho. apply andp_left2. simpl. normalize.
  - unfold lg_R, frame_ret_assert, function_body_ret_assert, overridePost. simpl.
    intro rho. apply andp_left2. simpl. normalize.
  - intro vl. rewrite HR. destruct (lg_R a); simpl. intro rho. apply andp_left2. apply derives_refl.
Qed.
