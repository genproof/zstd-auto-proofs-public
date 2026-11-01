(* LOOP / long loop, part MAIN: branch !t'17 (execSequenceSplitLitBuffer or execSequence).
   The exact model (BlkSeqLoopLongX.xl_inv) follows by BlkSeqLoopLongXE.xl_exec_S / xl_exec_N from EXEC's exact
   stores (lexec_split, lexec); error returns give seqs_exact by xl_exact_none. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Require Zstd.proof.dec.B.blk.BlkSeqLoopLongXE.
Local Open Scope logic.

(* after the executor: its result r, the output c', litPtr lp; ring slot id mod 8 (the head) freed *)
Definition x2_Q (a: la) (x: lfx) (w: lst) (dd: ldec) (ll ml: Z) : environ -> mpred :=
  (EX r: Z, EX c': list val, EX lp: val,
  PROPx [0 <= r <= Int64.max_unsigned; Zlength c' = Zlength (w_c w);
         is_error_code r = true -> XERR a c' /\ dec_err r /\ xl_none a;
         is_error_code r = false ->
           r = ll + ml /\ lp = offset_val (lit_li a (w_sw w) (w_j w + ll)) (lit_base a (w_sw w)) /\
           XQ a x (w_ie w + 1) (w_K w + (ll + ml)) (w_j w + ll) (w_sw w) c' /\
           xl_inv a (x_t x) (w_id w + 1) (w_K w + (ll + ml)) c' (d_rep dd) (w_j w + ll) (w_sw w) (d_pos dd)
             (d_lo dd) (d_st dd) (tl (w_q w) ++ [d_e dd])]
  (LOCALx (temp _t'12 (Vlong (Int64.repr r)) :: L_seq a (w_pp w) (w_id w) ++ L_ex a (w_K w) (w_sw w) ++ L_base a)
  (SEPx ([data_at Tsh (tptr tuchar) lp (a_vlp a);
          data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth (w_id w mod 8) (w_ring w) None)) (a_vsqs a);
          seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) (d_pos dd) (d_lo dd) (d_st dd) (x_tp x) (d_rep dd)
            (a_vss a);
          data_at_ Tsh t_seq (a_vs a); data_at Tsh t_seq (seqrep (d_ll dd) (d_ml dd) (d_off dd)) (a_vs1 a);
          tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x);
          lit_fix a; field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a (w_sw w)))) (a_p a);
          data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a));
          data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c' (a_ob a)] ++ S_fix a x))))%assert.

Lemma x2_id8 (a: la) (w: lst) : main_ph a w -> 0 <= w_ie w -> w_id w < a_nb a -> 8 <= w_id w.
Proof. unfold main_ph, a_adv. lia. Qed.

Lemma x2_code2 (a: la) (sw: bool) :
  Int.repr (lit_code a sw) = Int.repr 2 -> sw = false /\ exists lb, a_l a = LSplit lb.
Proof.
  unfold lit_code, loc_code, LOC_NOT_IN_DST, LOC_IN_DST, LOC_SPLIT.
  destruct sw, (a_l a); intros H; eauto;
  apply (f_equal Int.unsigned) in H; rewrite !Int.unsigned_repr in H by rep_lia; lia.
Qed.

Lemma x2_code_not2 (a: la) (sw: bool) :
  Int.repr (lit_code a sw) <> Int.repr 2 -> nosplit a sw.
Proof.
  unfold lit_code, loc_code, LOC_NOT_IN_DST, LOC_IN_DST, LOC_SPLIT, nosplit.
  destruct sw, (a_l a); intros H; auto.
Qed.

Lemma x2_land (id: Z) : Z.land (id - 8) (8 - 1) = id mod 8.
Proof.
  change (8 - 1) with (Z.ones 3). rewrite Z.land_ones by lia.
  replace (id - 8) with (id + (-1) * 8) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

(* the ring cell of the head *)
Lemma x2_ring_vals {d: Inhabitant (val * (val * val))} (r: list (option (Z * Z * Z))) (k: Z) (e: Z * Z * Z) :
  0 <= k < Zlength r -> Znth k r = Some e -> @Znth _ d k (ring_vals r) = seqrep3 e.
Proof. intros Hk He. unfold ring_vals. rewrite Znth_map by exact Hk. rewrite He. reflexivity. Qed.

(* ring slot k borrowed for the executor; given back free *)
Lemma x2_ring_take (r: list (option (Z * Z * Z))) (k: Z) (p: val) (e: Z * Z * Z) :
  0 <= k < 8 -> Zlength r = 8 -> Znth k r = Some e ->
  data_at Tsh (tarray t_seq 8) (ring_vals r) p |--
  data_at Tsh t_seq (seqrep3 e) (offset_val (24 * k) p) *
  (data_at_ Tsh t_seq (offset_val (24 * k) p) -*
   data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r None)) p).
Proof.
  intros Hk Hr He. assert_PROP (field_compatible (tarray t_seq 8) [] p) as Hfc by entailer!.
  eapply derives_trans; [apply (@SingletonHole.array_with_hole_intro CompSpecs Tsh t_seq k 8 (ring_vals r) p); lia|].
  rewrite arr_field_address by (auto; lia). change (sizeof t_seq) with 24.
  unfold ring_vals at 1. rewrite Znth_map by lia. rewrite He.
  apply sepcon_derives; [apply derives_refl|].
  unfold SingletonHole.array_with_hole. apply (allp_left _ (Vundef, (Vundef, Vundef))).
  rewrite arr_field_address by (auto; lia). change (sizeof t_seq) with 24.
  change (Vundef, (Vundef, Vundef)) with (ring_cell None).
  unfold ring_vals. rewrite upd_Znth_map. unfold data_at_. apply derives_refl.
Qed.

Lemma x2_ring_give (r: list (option (Z * Z * Z))) (k: Z) (p: val) (v: reptype t_seq) :
  data_at Tsh t_seq v (offset_val (24 * k) p) *
  (data_at_ Tsh t_seq (offset_val (24 * k) p) -*
   data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r None)) p) |--
  data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r None)) p.
Proof.
  sep_apply (data_at_data_at_ Tsh t_seq v (offset_val (24 * k) p)). apply modus_ponens_wand.
Qed.

(* the dictEnd argument for the executors *)
Definition x2_dE (a: la) : val := match a_x a with ExtNone => fs_dictEnd (a_fs a) | _ => nullval end.

Lemma x2_wvp (v: val) : weak_valid_pointer v |-- !! is_pointer_or_null v.
Proof.
  unfold weak_valid_pointer. destruct v; try (apply prop_right; simpl; auto; fail); simpl;
  change predicates_hered.orp with (@orp mpred _); change predicates_hered.FF with (@FF mpred _);
  try change predicates_hered.prop with (@prop mpred _); apply orp_left; first [apply FF_left | apply prop_derives; auto].
Qed.

Lemma x2_dE_pn (a: la) : la_pend a -> isptr (a_ob a) -> pws_pred (a_W a) |-- !! is_pointer_or_null (x2_dE a).
Proof.
  intros ((_ & _ & Hde) & _) Hob. unfold x2_dE, a_ob in *.
  destruct (a_x a); try (apply prop_right; simpl; auto; fail).
  destruct Hde as [Hde | Hw].
  - unfold la_dictend_ok in Hde. apply prop_right.
    destruct Hde as [-> | [(k & _ & ->) | []]]; simpl; auto.
  - eapply derives_trans; [exact Hw | apply x2_wvp].
Qed.

(* the executors' common preconditions *)
Lemma x2_pre (a: la) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> la_pend a -> 0 < a_nb a -> isptr (a_ob a) -> ex_safe a K j sw c ->
  0 < a_cap a /\ Zlength c <= 2 ^ 63 - 1 /\ 0 <= a_ps a <= a_d a + K /\ a_d a + K <= a_E a /\
  a_E a <= a_d a + a_cap a /\ a_d a + a_cap a <= Zlength c /\
  exec_ext_ok (a_x a) c /\
  fs_prefixStart (a_fs a) = offset_val (a_ps a) (a_ob a) /\
  fs_virtualStart (a_fs a) = offset_val (a_ps a - ext_len (a_x a)) (a_ob a) /\
  dict_end (a_x a) (a_ob a) (x2_dE a) = fs_dictEnd (a_fs a).
Proof.
  intros Hla Hpd Hnb Hob (HK & HKE & Hj & Hsw & Hc & Hun).
  destruct Hla as (Ho & Hi & Hlt & Hbsm & Hn & Hnbr & Hnc & _ & _ & _ & _ & Hlay).
  destruct (Hnc ltac:(lia)) as [_ Hcap].
  specialize (Hlay Hcap). destruct Hlay as (Hps & Hfps & Hfvs & Hel & Hext).
  destruct Ho as (Hosh & Hoc & HoN & Hod & Hocap & Hodc).
  assert (HE: a_E a <= a_d a + a_cap a).
  { unfold a_E, a_d, a_cap. destruct Hlt as (_ & _ & Hll). destruct (a_l a); try lia.
    destruct Hll as (? & ? & _). pose proof (Zlength_nonneg (a_lits a)). unfold WILDCOPY_OVERLENGTH in *. lia. }
  unfold x2_dE, a_d, a_cap, a_ps, a_ob, a_x in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold exec_ext_ok. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia. }
  split; [auto|]. split; [auto|].
  destruct (hc_ext (a_h a)); simpl in *; try tauto; symmetry; tauto.
Qed.

(* the split head: XSTEP (S) on execSequenceSplitLitBuffer's postcondition *)
Lemma x2_post_S (HXS: XSTEP) (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off lb r: Z)
    (c': list val) (lp: val) :
  sw = false -> la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) ->
  a_l a = LSplit lb -> lb + j + ll <= lb + (a_n a - LITBUFFEREXTRASIZE) ->
  Zlength c' = Zlength c ->
  (byte_cells c -> ext_bytes (a_x a) -> byte_cells c') ->
  is_error_code r = exec_split_err (a_d a + K) (a_E a) (lb + j) ll ml off (a_ps a) (ext_len (a_x a)) ->
  (is_error_code r = true -> unchanged_outside c c' (a_d a + K) (a_E a) /\ dec_err r) ->
  (is_error_code r = false ->
     r = ll + ml /\ lp = offset_val (lb + j + ll) (a_ob a) /\
     unchanged_outside c c' (a_d a + K)
       (Z.min (Z.min (a_E a) (a_d a + K + r + WILDCOPY_OVERLENGTH)) (Z.max (a_d a + K + r) (lb + j + ll))) /\
     (ext_read_ok (a_x a) (a_d a + K) (a_E a) ll ml off (a_ps a) ->
        (lit_exact_split (a_d a + K) (lb + j) ll ->
           sublist (a_d a + K) (a_d a + K + r) c' =
           sublist (a_d a + K) (a_d a + K + r) (exec_c c (a_d a + K) (sublist (lb + j) (lb + j + ll) c) ml off (a_ps a) (a_x a))) /\
        (Forall is_byte_val (sublist (a_ps a) (a_d a + K) c) -> Forall is_byte_val (sublist (lb + j) (lb + j + ll) c) ->
         ext_def (a_x a) c -> Forall is_byte_val (sublist (a_d a + K) (a_d a + K + r) c')))) ->
  xd_ub c c' -> (is_error_code r = false -> Forall is_byte_val (sublist (a_d a + K) (a_d a + K + r) c')) ->
  (is_error_code r = true -> XERR a c' /\ dec_err r) /\
  (is_error_code r = false ->
     r = ll + ml /\ lp = offset_val (lit_li a sw (j + ll)) (lit_base a sw) /\
     XQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c').
Proof.
  intros -> Hla Hpd Hlfx HXP Hl Hlim Hlen Hby Herr Hun Hok Hxu Hxf.
  assert (Eli: lit_li a false j = lb + j) by (unfold lit_li; rewrite Hl; reflexivity).
  assert (Elim: lit_lim a false = lb + (a_n a - LITBUFFEREXTRASIZE)) by (unfold lit_lim; rewrite Hl; reflexivity).
  destruct (HXS a x ie K j false c ll ml off Hla Hpd Hlfx HXP) as (_ & HS & _).
  specialize (HS lb Hl eq_refl ltac:(rewrite Eli, Elim; lia) c' Hlen Hby Hxu). cbv zeta in HS. rewrite Eli in HS.
  destruct HS as [HSe HSo]. split.
  - intros Hr. destruct (Hun Hr) as [Hu Hd]. split; [apply HSe; [congruence | exact Hu] | exact Hd].
  - intros Hr. destruct (Hok Hr) as (-> & Hlp & Hu & Hb). split; [reflexivity|]. split.
    + rewrite Hlp. unfold lit_li, lit_base. rewrite Hl. f_equal. lia.
    + apply HSo; auto. congruence.
Qed.

(* the literals are not the split head: lsrc *)
Lemma x2_lsrc_base (a: la) (x: lfx) (sw: bool) :
  nosplit a sw -> BlkSeqEXEC.lit_base (lsrc a x) (a_ob a) = lit_base a sw.
Proof. unfold nosplit, lsrc, BlkSeqEXEC.lit_base, lit_base. destruct (a_l a); intros; subst; reflexivity. Qed.

Lemma x2_lit_li_add (a: la) (sw: bool) (j ll: Z) : lit_li a sw (j + ll) = lit_li a sw j + ll.
Proof. unfold lit_li. destruct (a_l a); try destruct sw; lia. Qed.

Lemma x2_post_N (HXS: XSTEP) (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off r: Z)
    (c': list val) (lp: val) :
  la_ok a -> la_pend a -> lfx_ok a x -> XP a x ie K j sw c (ll, ml, off) -> nosplit a sw ->
  Zlength c' = Zlength c ->
  (byte_cells c -> byte_cells (lit_arr (lsrc a x) c) -> ext_bytes (a_x a) -> byte_cells c') ->
  is_error_code r = exec_err (a_d a + K) (a_E a) (lit_li a sw j) (lit_lim a sw) ll ml off (a_ps a) (ext_len (a_x a)) ->
  (is_error_code r = true -> unchanged_outside c c' (a_d a + K) (a_E a) /\ dec_err r) ->
  (is_error_code r = false ->
     r = ll + ml /\ lp = offset_val (lit_li a sw j + ll) (BlkSeqEXEC.lit_base (lsrc a x) (a_ob a)) /\
     unchanged_outside c c' (a_d a + K) (Z.min (a_E a) (a_d a + K + r + WILDCOPY_OVERLENGTH)) /\
     (ext_read_ok (a_x a) (a_d a + K) (a_E a) ll ml off (a_ps a) ->
        sublist (a_d a + K) (a_d a + K + r) c' =
        sublist (a_d a + K) (a_d a + K + r)
          (exec_c c (a_d a + K) (sublist (lit_li a sw j) (lit_li a sw j + ll) (lit_arr (lsrc a x) c)) ml off
             (a_ps a) (a_x a)) /\
        (Forall is_byte_val (sublist (a_ps a) (a_d a + K) c) ->
         Forall is_byte_val (sublist (lit_li a sw j) (lit_li a sw j + ll) (lit_arr (lsrc a x) c)) ->
         ext_def (a_x a) c -> Forall is_byte_val (sublist (a_d a + K) (a_d a + K + r) c')))) ->
  xd_ub c c' -> (is_error_code r = false -> Forall is_byte_val (sublist (a_d a + K) (a_d a + K + r) c')) ->
  (is_error_code r = true -> XERR a c' /\ dec_err r) /\
  (is_error_code r = false ->
     r = ll + ml /\ lp = offset_val (lit_li a sw (j + ll)) (lit_base a sw) /\
     XQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c').
Proof.
  intros Hla Hpd Hlfx HXP Hns Hlen Hby Herr Hun Hok Hxu Hxf.
  destruct (HXS a x ie K j sw c ll ml off Hla Hpd Hlfx HXP) as (HN & _ & _).
  specialize (HN Hns c' Hlen Hby Hxu). cbv zeta in HN.
  destruct HN as [HNe HNo]. split.
  - intros Hr. destruct (Hun Hr) as [Hu Hd]. split; [apply HNe; [congruence | exact Hu] | exact Hd].
  - intros Hr. destruct (Hok Hr) as (-> & Hlp & Hu & Hb). split; [reflexivity|]. split.
    + rewrite Hlp, x2_lit_li_add, (x2_lsrc_base a x sw Hns). reflexivity.
    + apply HNo; auto. congruence.
Qed.

(* the literal arrays: lit_res of lsrc and the rest *)
Definition x2_lrest (a: la) (x: lfx) : mpred :=
  match a_l a with
  | LIn _ => data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a))
  | LDst _ => data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)) *
              data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))
  | _ => data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))
  end.

Lemma x2_lit_split (a: la) (x: lfx) :
  la_ok a -> lfx_ok a x ->
  data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)) *
  data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) =
  lit_res (lsrc a x) * x2_lrest a x.
Proof.
  intros (_ & Hi & _) (_ & _ & _ & _ & (Hxc & _)).
  assert (HiN: Zlength (iw_c (a_i a)) = iw_N (a_i a)) by (destruct Hi as (_ & _ & _ & _ & ? & _); auto).
  unfold lsrc, lit_res, x2_lrest. destruct (a_l a).
  - rewrite HiN, sepcon_comm. reflexivity.
  - rewrite Hxc. reflexivity.
  - rewrite emp_sepcon. reflexivity.
  - rewrite Hxc. reflexivity.
Qed.

(* execSequence's literal precondition *)
Lemma x2_ls_ok (a: la) (x: lfx) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> lfx_ok a x -> nosplit a sw -> ex_safe a K j sw c ->
  match lsrc a x with
  | LitSep shl _ cl => readable_share shl /\ 0 <= lit_li a sw j <= lit_lim a sw /\
                       lit_lim a sw + WILDCOPY_OVERLENGTH <= Zlength cl
  | LitIn => a_E a <= lit_li a sw j <= lit_lim a sw /\ lit_lim a sw + WILDCOPY_OVERLENGTH <= Zlength c
  end.
Proof.
  intros (Ho & Hi & Hlt & _) (_ & Hsh1 & _ & _ & (Hxc & _)) Hns (HK & HKE & Hj & Hsw & Hc & _).
  destruct Hlt as (_ & Hn & Hll). destruct Ho as (_ & _ & _ & Hod & Hocap & Hodc).
  assert (HiN: Zlength (iw_c (a_i a)) = iw_N (a_i a)) by (destruct Hi as (_ & _ & _ & _ & ? & _); auto).
  unfold nosplit, lsrc, lit_li, lit_lim, a_E, a_n, a_d, a_cap in *. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
  destruct (a_l a).
  - subst sw. destruct Hll as (? & ? & _). split; [auto|]. lia.
  - subst sw. split; [auto|]. rewrite Hxc. lia.
  - subst sw. destruct Hll as (? & ? & _). lia.
  - subst sw. split; [auto|]. rewrite Hxc. lia.
Qed.

(* error returns: the seqState_t local and the literal fields back (as BlkSeqLoopLongEnd) *)
Lemma x2_ss_split (v: val) :
  data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v =
  data_at_ Tsh t_bitd (field_address t_seqstate (DOT _DStream) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateLL) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateOffb) v) *
  data_at_ Tsh t_fsestate (field_address t_seqstate (DOT _stateML) v) *
  field_at_ Tsh t_seqstate (DOT _prevOffset) v.
Proof.
  unfold_data_at (data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v).
  rewrite !field_at_data_at. rewrite <- !sepcon_assoc. unfold field_at_. rewrite field_at_data_at. reflexivity.
Qed.

Lemma x2_ss (gv0: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv0 s start pos lo st tp r v |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite (x2_ss_split v). unfold seqstate_at, BIT_DStream_rep.
  destruct st as [[a b] c]; destruct tp as [[x y] z]. Intros ptr lim.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at.
  repeat (sep_apply data_at_data_at_). cancel.
Qed.

Lemma x2_lit_release (a: la) (xc: list val) (v: val) :
  byte_cells xc ->
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) v (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) |-- lit_scratch (a_p a).
Proof.
  intros Hxc. unfold lit_fix, lit_scratch, lit_extra, lit_extra_bytes.
  change (data_at Ews (tarray tuchar LITEXTRA_N) xc (field_address t_dctx (DOT _litExtraBuffer) (a_p a)))
    with (data_at Ews (nested_field_type t_dctx (DOT _litExtraBuffer)) xc (field_address t_dctx (DOT _litExtraBuffer) (a_p a))).
  rewrite <- (field_at_data_at Ews t_dctx (DOT _litExtraBuffer)).
  destruct (a_l a); Intros;
  repeat match goal with |- context [field_at Ews t_dctx ?g ?v (a_p a)] =>
    tryif constr_eq g (StructField _litExtraBuffer :: nil) then fail else sep_apply (field_at_field_at_ Ews t_dctx g v (a_p a)) end;
  Exists xc; entailer!.
Qed.

(* error returns, the exact model: the literal fields back with litExtraBuffer still holding lxb
   (la_post's lit_scratch_x) *)
Lemma x2_lit_release_x (a: la) (v: val) :
  Zlength (a_lxb a) = LITEXTRA_N /\ bytes_ok (a_lxb a) ->
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) v (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes (a_lxb a)) (lit_extra (a_p a)) |--
  lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros Hx. unfold lit_fix, lit_scratch_x, lit_extra_at. rewrite <- litextra_data_at.
  destruct (a_l a);
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd));
    try sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation));
    entailer!; apply Hx.
Qed.

(* execSequence's literal array (lsrc) is the exact model's (xl_lsrc) when litExtraBuffer holds lxb *)
Lemma x2_ls_l (a: la) (x: lfx) (sw: bool) :
  nosplit a sw -> x_xc x = zbytes (a_lxb a) -> ls_l (lsrc a x) = xl_lsrc a sw.
Proof.
  unfold nosplit, lsrc, xl_lsrc, ls_l. intros Hns Hxc. destruct (a_l a); try subst sw; rewrite ?Hxc; reflexivity.
Qed.

Lemma x2_prop_app (Delta: tycontext) (P: environ -> mpred) (L1 L2: list Prop) (Q: list localdef) (R: list mpred) :
  fold_right and True L1 -> fold_right and True L2 ->
  ENTAIL Delta, P |-- PROPx [] (LOCALx Q (SEPx R)) ->
  ENTAIL Delta, P |-- PROPx (L1 ++ L2) (LOCALx Q (SEPx R)).
Proof.
  intros H1 H2 H. eapply derives_trans; [exact H|]. unfold PROPx.
  apply andp_derives; [|apply derives_refl]. apply prop_derives. intros _. clear - H1 H2.
  induction L1 as [|p L1 IH]; simpl in *; [exact H2|]. destruct H1; split; auto.
Qed.

Lemma x2_sub32 (i: ptrofs) (n: Z) :
  Ptrofs.sub (Ptrofs.add i (Ptrofs.repr n)) (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 32))) =
  Ptrofs.add i (Ptrofs.repr (n - WILDCOPY_OVERLENGTH)).
Proof.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, <- Ptrofs.sub_add_opp. f_equal.
  unfold Ptrofs.sub, WILDCOPY_OVERLENGTH. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_sub;
  apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

(* the literals left before litLimit are at most the block's literals: litLimit - litPtr does not wrap as a
   ptrdiff_t (exec_spec's precondition) *)
Lemma x2_lit_span (a: la) (sw: bool) (j: Z) :
  la_ok a -> 0 <= j -> lit_lim a sw - lit_li a sw j <= Int64.max_signed.
Proof.
  intros (_ & _ & (_ & Hn & _) & _) Hj.
  assert (lit_lim a sw - lit_li a sw j <= Zlength (a_lits a))
    by (unfold lit_lim, lit_li, a_n, LITBUFFEREXTRASIZE; destruct (a_l a); try destruct sw; lia).
  unfold ZSTD_BLOCKSIZE_MAX in Hn. rep_lia.
Qed.

Lemma lg_main_x2_ok : P_X2.
Proof.
  intros HTE HXS HINV HTAIL Espec a x w dd R HG Hla Hpd Hlfx Hlx Hcut HRn HRr.
  apply (lg_R_concrete a); [exact HRr|]. rewrite HRn.
  unfold MD, MD_P, LI_P. cbv [app]. Intros.
  assert (HMD: fold_right and True (MD_P a x w dd)).
  { unfold MD_P, LI_P. cbv [app fold_right]. repeat (apply conj; [assumption|]). exact I. }
  destruct (HINV a x w dd Hla Hpd Hlfx Hlx HMD) as (HXP & Hslot & Hring & Hctx & Hpos & Hinv0 & HLI').
  unfold MD_S, LI_L, S_fix, L_seq, L_ex, L_base, lg_main_x2, lit_now. cbv [app]. repeat flatten_sepcon_in_SEP.
  forward.
  pose proof (x2_id8 a w H11 ltac:(lia) H12) as Hid8.
  destruct (Znth 0 (w_q w)) as [[ll ml] off] eqn:He0.
  assert_PROP (isptr (a_ob a)) as Hob by entailer!.
  pose proof (x2_land (w_id w)) as Hland.
  assert (Hland7: Z.land (w_id w - 8) 7 = w_id w mod 8) by exact Hland.
  assert (Hk8: 0 <= w_id w mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hnbr: a_nb a <= 32512 + 65535) by (destruct Hla as (_ & _ & _ & _ & _ & ? & _); unfold LONGNBSEQ in *; lia).
  assert (Hr8: Zlength (w_ring w) = 8) by (destruct H3; auto).
  pose proof (fun d => @x2_ring_vals d (w_ring w) (w_id w mod 8) (ll, ml, off) ltac:(lia) Hring) as Hrv.
  destruct (x2_pre a (w_K w) (w_j w) (w_sw w) (w_c w) Hla Hpd ltac:(lia) Hob H7)
    as (Hcap & Hc32 & Hps & HkE & HEd & HdN & Hext & Hfps & Hfvs & Hfde).
  assert_PROP (is_pointer_or_null (x2_dE a)) as Hdep by (sep_apply (x2_dE_pn a Hpd Hob); entailer!).
  assert (HcN: Zlength (w_c w) = oa_N (a_o a)) by (destruct H7 as (_ & _ & _ & _ & ? & _); auto).
  assert (HXP' := HXP). destruct HXP' as (Hie & Xsf & Xdf & Hll & Hml & Hoff & _).
  assert (Xxc: xc_ok (a_l a) (a_lits a) (x_xc x)) by (destruct Hlfx as (_ & _ & _ & _ & Hxc); exact Hxc).
  destruct (ex_def_hist a (w_K w) (w_j w) (w_sw w) (w_c w) Hla Hcap ltac:(destruct Xsf; lia) ltac:(lia) Xdf)
    as (Xdh & Xde).
  forward_if (x2_Q a x w dd ll ml).
  - destruct (x2_code2 a (w_sw w) H17) as (Hsw & lb & Hl).
    assert (Eli: forall j, lit_li a (w_sw w) j = lb + j) by (intros; unfold lit_li; rewrite Hsw, Hl; reflexivity).
    assert (Elim: lit_lim a (w_sw w) = lb + (a_n a - LITBUFFEREXTRASIZE)) by (unfold lit_lim; rewrite Hsw, Hl; reflexivity).
    assert (Eb: lit_base a (w_sw w) = a_ob a) by (unfold lit_base; rewrite Hsw, Hl; reflexivity).
    rewrite !Eli, Elim, Eb.
    forward. forward.
    { entailer!. rewrite Hland7, Hrv. simpl. auto. }
    rewrite Hland, Hrv. cbn [seqrep3].
    sep_apply (x2_ring_take (w_ring w) (w_id w mod 8) (a_vsqs a) (ll, ml, off) Hk8 Hr8 Hring).
    flatten_sepcon_in_SEP.
    assert (Hlcut: lb + w_j w + ll <= lb + (a_n a - LITBUFFEREXTRASIZE)).
    { unfold lg_cut, lit_lim, lit_li in Hcut. rewrite Hl, He0 in Hcut. rewrite Hsw in Hcut. simpl in Hcut. lia. }
    assert (Hlim32: lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH <= a_E a /\ 0 <= lb).
    { destruct Hla as ((_ & _ & _ & Hd0 & _) & _ & (_ & _ & Hll') & _). rewrite Hl in Hll'.
      unfold a_E, a_d, a_cap, a_n. rewrite Hl. lia. }
    change (seqrep3 (ll, ml, off)) with (seqrep ll ml off).
    assert (Xdl: Forall is_byte_val (sublist (lb + w_j w) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) (w_c w)))
      by (apply (ex_def_lit_S a (x_xc x) lb (w_K w)); auto; rewrite <- Hsw; auto).
    rewrite <- HcN, Hfps, Hfvs, <- Hfde.
    forward_call (a_gv a, oa_sh (a_o a), a_ob a, w_c w, a_d a + w_K w, a_E a, Tsh,
                  offset_val (24 * (w_id w mod 8)) (a_vsqs a), ll, ml, off, Tsh, a_vlp a, lb + w_j w,
                  lb + (a_n a - LITBUFFEREXTRASIZE), a_ps a, a_x a, x2_dE a).
    { entailer!. rewrite Hland. change (sizeof (Tstruct ___gp_seq_t noattr)) with 24.
      unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction. simpl. rewrite x2_sub32. reflexivity. }
    { split; [destruct Hla as ((? & _) & _); auto|].
      destruct H7 as (_ & _ & Hj & _). unfold LL_VMAX, ML_VMAX, SIZE_MAX in *.
      split; [rep_lia|]. split; [rep_lia|]. split; [lia|].
      (* the split literal buffer lies within the last block-size bytes of dst (la_pend) *)
      destruct Hpd as [_ Hp]. rewrite Hl in Hp. unfold a_E. rewrite Hl.
      destruct Hla as ((_ & _ & _ & Hd0 & _) & _ & _ & Hbs & Hnb & _). unfold a_n, a_d, a_cap, ZSTD_BLOCKSIZE_MAX in *.
      destruct (Z.min_spec (a_bsm a) (oa_cap (a_o a))) as [[? E]|[? E]]; rewrite E in Hp;
        unfold WILDCOPY_OVERLENGTH in *; lia. }
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *. Intros.
    forward.
    sep_apply (x2_ring_give (w_ring w) (w_id w mod 8) (a_vsqs a) (seqrep ll ml off)).
    edestruct (x2_post_S HXS a x (w_ie w) (w_K w) (w_j w) (w_sw w) (w_c w) ll ml off lb r c' lp Hsw Hla Hpd Hlfx HXP Hl Hlcut)
      as [Hpe Hpo]; try eassumption.
    (* the exact model: BlkSeqLoopLongXE.xl_exec_S on the executor's exact stores *)
    assert (Hinv0' := Hinv0). rewrite Hsw in Hinv0', Hpos.
    destruct (BlkSeqLoopLongXE.xl_exec_S a (x_t x) (w_id w + 1) (w_K w) (w_c w) c' (d_rep dd) (w_j w) lb (d_pos dd) (d_lo dd)
                (d_st dd) (tl (w_q w) ++ [d_e dd]) ll ml off r Hctx Hpos Hl
                ltac:(unfold lit_li, lit_lim; rewrite Hl; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hinv0'
                ltac:(unfold lit_li; rewrite Hl; assumption) ltac:(unfold lit_li, lit_lim; rewrite Hl; assumption))
      as [Xe Xo].
    assert (Hpe': is_error_code r = true -> XERR a c' /\ dec_err r /\ xl_none a)
      by (intros Hr; destruct (Hpe Hr); auto).
    assert (Hpo': is_error_code r = false ->
              r = ll + ml /\ lp = offset_val (lit_li a (w_sw w) (w_j w + ll)) (lit_base a (w_sw w)) /\
              XQ a x (w_ie w + 1) (w_K w + (ll + ml)) (w_j w + ll) (w_sw w) c' /\
              xl_inv a (x_t x) (w_id w + 1) (w_K w + (ll + ml)) c' (d_rep dd) (w_j w + ll) (w_sw w) (d_pos dd)
                (d_lo dd) (d_st dd) (tl (w_q w) ++ [d_e dd]))
      by (intros Hr; destruct (Hpo Hr) as (A & B & C); rewrite Hsw; rewrite Hsw in B, C; auto).
    clear Hpe Hpo.
    unfold x2_Q. Exists r c' lp. unfold L_seq, L_ex, L_base, S_fix. cbv [app].
    rewrite Elim, Eb, Hfps, Hfvs, <- Hfde, <- HcN. rewrite Eb in Hpo'.
    entailer!.
  - pose proof (x2_code_not2 a (w_sw w) H17) as Hns.
    sep_apply (x2_ring_take (w_ring w) (w_id w mod 8) (a_vsqs a) (ll, ml, off) Hk8 Hr8 Hring).
    flatten_sepcon_in_SEP.
    change (seqrep3 (ll, ml, off)) with (seqrep ll ml off).
    gather_SEP (data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)))
               (data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))).
    rewrite (x2_lit_split a x Hla Hlfx). flatten_sepcon_in_SEP.
    rewrite <- HcN, Hfps, Hfvs, <- Hfde, <- (x2_lsrc_base a x (w_sw w) Hns).
    pose proof (x2_ls_ok a x (w_K w) (w_j w) (w_sw w) (w_c w) Hla Hlfx Hns H7) as Hls.
    assert (Xdl: Forall is_byte_val (sublist (lit_li a (w_sw w) (w_j w)) (lit_lim a (w_sw w) + WILDCOPY_OVERLENGTH)
                                       (lit_arr (lsrc a x) (w_c w)))).
    { apply (ex_def_lit_N a (x_xc x) (lsrc a x) (w_K w)); auto.
      unfold lsrc. destruct (a_l a); reflexivity. }
    forward_call (a_gv a, oa_sh (a_o a), a_ob a, w_c w, a_d a + w_K w, a_E a, Tsh,
                  offset_val (24 * (w_id w mod 8)) (a_vsqs a), ll, ml, off, Tsh, a_vlp a, lsrc a x,
                  lit_li a (w_sw w) (w_j w), lit_lim a (w_sw w), a_ps a, a_x a, x2_dE a).
    { pose proof (x2_lit_span a (w_sw w) (w_j w) Hla ltac:(destruct Xsf as (_ & _ & ? & _); lia)).
      split; [destruct Hla as ((? & _) & _); auto|]. unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. rep_lia. }
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *. Intros.
    forward.
    sep_apply (x2_ring_give (w_ring w) (w_id w mod 8) (a_vsqs a) (seqrep ll ml off)).
    gather_SEP (lit_res (lsrc a x)) (x2_lrest a x).
    rewrite <- (x2_lit_split a x Hla Hlfx). flatten_sepcon_in_SEP.
    edestruct (x2_post_N HXS a x (w_ie w) (w_K w) (w_j w) (w_sw w) (w_c w) ll ml off r c' lp Hla Hpd Hlfx HXP Hns)
      as [Hpe Hpo]; try eassumption.
    (* the exact model: BlkSeqLoopLongXE.xl_exec_N on the executor's exact stores *)
    destruct (BlkSeqLoopLongXE.xl_exec_N a (x_t x) (w_id w + 1) (w_K w) (w_c w) c' (d_rep dd) (w_j w) (w_sw w)
                (d_pos dd) (d_lo dd) (d_st dd) (tl (w_q w) ++ [d_e dd]) ll ml off r Hctx Hpos Hns
                ltac:(lia) ltac:(lia) ltac:(lia) Hinv0 ltac:(assumption)
                ltac:(rewrite <- (x2_ls_l a x (w_sw w) Hns (proj1 Hlx)); assumption))
      as [Xe Xo].
    assert (Hpe': is_error_code r = true -> XERR a c' /\ dec_err r /\ xl_none a)
      by (intros Hr; destruct (Hpe Hr); auto).
    assert (Hpo': is_error_code r = false ->
              r = ll + ml /\ lp = offset_val (lit_li a (w_sw w) (w_j w + ll)) (lit_base a (w_sw w)) /\
              XQ a x (w_ie w + 1) (w_K w + (ll + ml)) (w_j w + ll) (w_sw w) c' /\
              xl_inv a (x_t x) (w_id w + 1) (w_K w + (ll + ml)) c' (d_rep dd) (w_j w + ll) (w_sw w) (d_pos dd)
                (d_lo dd) (d_st dd) (tl (w_q w) ++ [d_e dd]))
      by (intros Hr; destruct (Hpo Hr) as (A & B & C); auto).
    clear Hpe Hpo.
    unfold x2_Q. Exists r c' lp. unfold L_seq, L_ex, L_base, S_fix. cbv [app].
    rewrite Hfps, Hfvs, <- Hfde, <- HcN, <- (x2_lsrc_base a x (w_sw w) Hns).
    rewrite <- (x2_lsrc_base a x (w_sw w) Hns) in Hpo'.
    entailer!.
  - unfold x2_Q. Intros r c' lp. unfold L_seq, L_ex, L_base, S_fix. cbv [app].
    forward.
    forward_call r.
    destruct (is_error_code r) eqn:Er.
    + forward_if (PROP (False) LOCAL () SEP ()).
      * unfold POSTCONDITION, abbreviate, lg_R, la_post. forward.
        match goal with Hx: true = true -> XERR a c' /\ _ |- _ => destruct (Hx eq_refl) as (HXE & HDE & HXN) end.
        assert (Hlf' := Hlfx). destruct Hlf' as (Hos & _ & _ & Heq & (_ & Hxcb & _)).
        Exists r c' (a_rep a).
        sep_apply (x2_ss (a_gv a) (iw_s (a_i a)) (a_start a) (d_pos dd) (d_lo dd) (d_st dd) (x_tp x) (d_rep dd) (a_vss a)).
        destruct Hlx as [Hxz Hxl]. rewrite Hxz.
        sep_apply (x2_lit_release_x a (Vint (Int.repr (lit_code a (w_sw w))))
                     ltac:(destruct Hxl as (? & ? & _); split; assumption)).
        sep_apply (derives_refl' _ _ (eq_sym Heq)).
        sep_apply (HTE (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x)).
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) lp (a_vlp a)).
        sep_apply (data_at_data_at_ Tsh (tarray t_seq 8) (ring_vals (upd_Znth (w_id w mod 8) (w_ring w) None)) (a_vsqs a)).
        sep_apply (data_at_data_at_ Tsh t_seq (seqrep (d_ll dd) (d_ml dd) (d_off dd)) (a_vs1 a)).
        rewrite <- Hos. replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        apply andp_right; [apply prop_right | unfold a_x, a_ob; cancel].
        destruct HXE as (HXu & HXm & HXb).
        split; [auto|]. split; [congruence|]. split; [destruct Hla as (_ & _ & _ & _ & _ & _ & _ & _ & ? & _); auto|].
        split; [exact HXu|]. split; [congruence|]. split; [|split; [intros; exact HDE | split; [exact HXb | split; [apply xl_exact_none; [exact Er | exact HXN] | reflexivity]]]].
        intros Hv. specialize (HXm Hv).
        destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; auto.
      * exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in Hz; rewrite Int.unsigned_repr in Hz by rep_lia;
          rewrite Int.unsigned_zero in Hz; lia end.
    + forward_if.
      { exfalso. match goal with Hz: Int.repr 0 <> Int.zero |- _ => apply Hz; reflexivity end. }
      match goal with Hx: false = false -> _ |- _ => destruct (Hx eq_refl) as (Hr & Hlp & HXQ & HXI) end.
      subst r lp.
      eapply semax_pre; [| exact (HTAIL Espec a x w dd (w_K w + (ll + ml)) (w_j w + ll) (w_sw w) c' (w_K w) (ll + ml)
                                   _t'16 _oneSeqSize__1 Hla Hpd Hlfx (or_intror eq_refl))].
      pose proof (HLI' _ _ _ _ HXQ HXI) as HLIP'.
      unfold XS. cbv zeta.
      apply x2_prop_app; [exact HLIP' | simpl; unfold LL_VMAX, ML_VMAX in *; repeat split; auto; lia |].
      unfold L_seq, L_base, S_fix, lit_now. cbv [app].
      entailer!.
Qed.
