(* LOOP / long loop: one iteration of the queue-finishing loop (SEG_FIN),
   after BIT_endOfDStream: execute the queue head.  Besides the old facts (FIN_INV, FXSTEP), the exact model's
   invariant xl_inv is carried through the executor steps of BlkSeqLoopLongXE (xl_exec_N / xl_exec_S /
   xl_exec_X1); an error return gives seqs_exact by BlkSeqLoopLongX.xl_exact_none. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXE.
Local Open Scope logic.


(* ===================== error returns (as in BlkSeqLoopLongEnd.v) ===================== *)

(* the literal fields back to la_post's lit_scratch_x, litExtraBuffer holding exactly lxb *)
Lemma lgf_lit_release_x (a: la) (lxb: list Z) (sw: bool) :
  Zlength lxb = LITEXTRA_N -> bytes_ok lxb -> lit_now a (zbytes lxb) sw |-- lit_scratch_x (a_p a) lxb.
Proof.
  intros Hl Hb. unfold lit_now, lit_fix, lit_scratch_x, lit_extra_at.
  rewrite <- (litextra_data_at (a_p a) (zbytes lxb)).
  destruct (a_l a); Intros;
  repeat match goal with |- context [field_at Ews t_dctx ?g ?v (a_p a)] =>
    lazymatch g with (StructField _litExtraBuffer :: nil) => fail
    | _ => sep_apply (field_at_field_at_ Ews t_dctx g v (a_p a)) end end;
  entailer!.
Qed.

(* the seqState_t local back to data_at_ (as BlkSeqLoopShort.sh_end_ok_ss) *)
Lemma lgf_ss_split (v: val) :
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

Lemma lgf_ss (gv: globals) (s: list Z) (start: val) (pos lo sLL sOF sML: Z) (pLL pOF pML: val) (r: Z * Z * Z)
    (v: val) :
  BIT_DStream_rep Tsh gv s start pos lo (field_address t_seqstate (DOT _DStream) v) *
  field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) v *
  field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) v *
  field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) v *
  field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v
  |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite lgf_ss_split. unfold BIT_DStream_rep. Intros ptr lim.
  sep_apply (field_at_field_at_ Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v).
  rewrite !field_at_data_at.
  sep_apply (data_at_data_at_ Tsh t_bitd
    (Vlong (Int64.repr (bit_C s lo)), (Vint (Int.repr (lo + 64 - pos)), (ptr, (start, lim))))
    (field_address t_seqstate (DOT _DStream) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sLL pLL) (field_address t_seqstate (DOT _stateLL) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sOF pOF) (field_address t_seqstate (DOT _stateOffb) v)).
  sep_apply (data_at_data_at_ Tsh t_fsestate (fse_val sML pML) (field_address t_seqstate (DOT _stateML) v)).
  cancel.
Qed.

(* oend <= dst + capacity *)
Lemma lgf_E_le (a: la) : la_ok a -> a_E a <= a_d a + a_cap a.
Proof.
  intros (_ & _ & Hlits & _). unfold a_E, a_d, a_cap.
  destruct Hlits as (_ & Hn & Hl). destruct (a_l a); try lia.
  destruct Hl as (? & ? & _). unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

Lemma lgf_unch (a: la) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> ex_safe a K j sw c ->
  unchanged_outside (oa_c (a_o a)) c (oa_d (a_o a)) (oa_d (a_o a) + oa_cap (a_o a)).
Proof.
  intros Hla (HK & HKE & _ & _ & _ & Hu). pose proof (lgf_E_le a Hla) as HE.
  unfold a_d, a_cap in *. intros k Hk Hn. apply Hu; [exact Hk|]. intros Hk'. apply Hn. lia.
Qed.

(* the model decodes when seqs_model is defined *)
Lemma lgf_DM (a: la) (t: fse_table * fse_table * fse_table) (rep: Z * Z * Z) (hist out lits: list Z)
    (wsize: Z) (r: list Z * (Z * Z * Z)) :
  a_os a = Some t -> 0 < a_nb a ->
  seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) rep hist out lits wsize = Some r ->
  exists seqs, DM a t seqs /\ exec_seqs wsize rep hist lits out seqs <> None.
Proof.
  intros Hos Hnb Hm. unfold seqs_model in Hm. rewrite Hos in Hm.
  replace (a_nb a =? 0) with false in Hm by (symmetry; apply Z.eqb_neq; lia).
  destruct t as [[tLL tOF] tML].
  destruct (decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)) as [seqs|] eqn:Hd; [|discriminate].
  exists seqs. split; [exact Hd|].
  destruct (exec_seqs wsize rep hist lits out seqs); [discriminate|discriminate].
Qed.

(* ===================== the ring: one cell out of sequences[8] ===================== *)

Definition ring_hole (sh: share) (k: Z) (rv: list (val * (val * val))) (v: val) : mpred :=
  !! field_compatible (tarray t_seq 8) [] v &&
  (data_at sh (tarray t_seq k) (sublist 0 k rv) v *
   data_at sh (tarray t_seq (8 - (k + 1))) (sublist (k + 1) 8 rv) (offset_val (24 * (k + 1)) v)).

Lemma ring_join (sh: share) (rv: list (val * (val * val))) (k: Z) (cell: val * (val * val)) (v: val) :
  0 <= k < 8 -> Zlength rv = 8 ->
  data_at sh (tarray t_seq 8) (upd_Znth k rv cell) v =
  data_at sh t_seq cell (offset_val (24 * k) v) * ring_hole sh k rv v.
Proof.
  intros Hk Hl. unfold ring_hole.
  set (u := upd_Znth k rv cell).
  assert (Hu: Zlength u = 8) by (unfold u; rewrite Zlength_upd_Znth; lia).
  assert (E1: data_at sh (tarray t_seq 8) u v =
              data_at sh (tarray t_seq k) (sublist 0 k u) v *
              data_at sh (tarray t_seq (k + 1 - k)) (sublist k (k + 1) u)
                (field_address0 (tarray t_seq 8) (SUB k) v) *
              data_at sh (tarray t_seq (8 - (k + 1))) (sublist (k + 1) 8 u)
                (field_address0 (tarray t_seq 8) (SUB (k + 1)) v)).
  { refine (@split3_data_at_Tarray CompSpecs sh t_seq 8 k (k + 1) u u (sublist 0 k u) (sublist k (k + 1) u)
              (sublist (k + 1) 8 u) v _ _ _ _ _ _ _); try reflexivity; try lia.
    - split; reflexivity.
    - assert (E: k + 1 <= 8 <= Zlength u) by lia. exact E.
    - assert (E: u = sublist 0 8 u) by (rewrite sublist_same by lia; reflexivity). exact E. }
  assert (E2: sublist k (k + 1) u = [cell]).
  { unfold u. rewrite sublist_upd_Znth_lr by lia. replace (k - k) with 0 by lia.
    rewrite sublist_len_1 by lia. rewrite upd_Znth0. reflexivity. }
  assert (E3: sublist 0 k u = sublist 0 k rv) by (unfold u; apply sublist_upd_Znth_l; lia).
  assert (E4: sublist (k + 1) 8 u = sublist (k + 1) 8 rv) by (unfold u; apply sublist_upd_Znth_r; lia).
  replace (k + 1 - k) with 1 in E1 by lia.
  rewrite E2, E3, E4 in E1.
  assert (E5: forall q, data_at sh (tarray t_seq 1) [cell] q = data_at sh t_seq cell q).
  { intros q. refine (@data_at_singleton_array_eq CompSpecs sh t_seq cell [cell] q eq_refl). }
  rewrite E5 in E1. rewrite E1.
  apply pred_ext.
  - assert_PROP (isptr (field_address0 (tarray t_seq 8) (SUB k) v)) as Hp.
    { sep_apply (data_at_local_facts sh t_seq cell (field_address0 (tarray t_seq 8) (SUB k) v)). entailer!. }
    unfold field_address0 in Hp.
    destruct (field_compatible0_dec (tarray t_seq 8) (SUB k) v) as [Hfc0|]; [|contradiction].
    assert (Hfc: field_compatible (tarray t_seq 8) [] v).
    { destruct Hfc0 as (H1 & H2 & H3 & H4 & H5 & H6). repeat split; auto. }
    rewrite !arr_field_address0 by (auto; lia).
    change (sizeof t_seq) with 24. Intros. entailer!.
  - Intros. rewrite !arr_field_address0 by (auto; lia).
    change (sizeof t_seq) with 24. entailer!.
Qed.

(* the head's cell back into the ring (unchanged, or rewritten) *)
Lemma ring_back_upd (sh: share) (ring: list (option (Z * Z * Z))) (k: Z) (e: Z * Z * Z) (v: val) :
  0 <= k < 8 -> Zlength ring = 8 ->
  data_at sh t_seq (seqrep3 e) (offset_val (24 * k) v) * ring_hole sh k (ring_vals ring) v =
  data_at sh (tarray t_seq 8) (ring_vals (upd_Znth k ring (Some e))) v.
Proof.
  intros Hk Hl. unfold ring_vals at 2. rewrite <- upd_Znth_map.
  change (map ring_cell ring) with (ring_vals ring). change (ring_cell (Some e)) with (seqrep3 e).
  rewrite ring_join by (unfold ring_vals; rewrite ?Zlength_map; lia). reflexivity.
Qed.

Lemma ring_back (sh: share) (ring: list (option (Z * Z * Z))) (k: Z) (e: Z * Z * Z) (v: val) :
  0 <= k < 8 -> Zlength ring = 8 -> Znth k ring = Some e ->
  data_at sh t_seq (seqrep3 e) (offset_val (24 * k) v) * ring_hole sh k (ring_vals ring) v =
  data_at sh (tarray t_seq 8) (ring_vals ring) v.
Proof.
  intros Hk Hl He. rewrite ring_back_upd by auto. rewrite upd_Znth_triv by (auto; lia). reflexivity.
Qed.

Lemma fin_ss (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv s start pos lo st tp r v |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  unfold seqstate_at. destruct st as [[sLL sOF] sML]; destruct tp as [[pLL pOF] pML].
  apply lgf_ss.
Qed.

(* everything of the loop back to the function's frame and la_post's resources (an error return) *)
Lemma fin_ret_sep (HTE: TABS_ELIM) (a: la) (x: lfx) (sw: bool) (cl cm co: Z) (k8: Z)
    (ring: list (option (Z * Z * Z))) (lp: val) (pos lo: Z) (st drep: Z * Z * Z) :
  lfx_ok a x -> lfx_x a x -> 0 < a_nb a -> 0 <= k8 < 8 -> Zlength ring = 8 ->
  data_at Tsh t_seq (seqrep cl cm co) (offset_val (24 * k8) (a_vsqs a)) *
  ring_hole Tsh k8 (ring_vals ring) (a_vsqs a) *
  data_at Tsh (tptr tuchar) lp (a_vlp a) *
  seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) pos lo st (x_tp x) drep (a_vss a) *
  tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x) *
  lit_now a (x_xc x) sw *
  data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
  bit_src (x_sh2 x) (a_start a) (iw_s (a_i a)) * x_Ri x
  |-- tabs_seq (a_gv a) (a_p a) (a_ox a) (a_os a) (if a_nb a =? 0 then a_fe a else 1) * lit_scratch_x (a_p a) (a_lxb a) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
      data_at_ Tsh (tptr tuchar) (a_vlp a) * data_at_ Tsh (tarray (Tstruct ___gp_seq_t noattr) 8) (a_vsqs a) *
      data_at_ Tsh (Tstruct ___gp_seqState_t noattr) (a_vss a).
Proof.
  intros (Hos & _ & _ & Heq & _) (Hxx & Hxl & Hxb & _) Hnb Hk Hl.
  change (seqrep cl cm co) with (seqrep3 (cl, cm, co)).
  rewrite (ring_back_upd Tsh ring k8 (cl, cm, co) (a_vsqs a) Hk Hl).
  sep_apply (data_at_data_at_ Tsh (tarray t_seq 8) (ring_vals (upd_Znth k8 ring (Some (cl, cm, co)))) (a_vsqs a)).
  sep_apply (fin_ss (a_gv a) (iw_s (a_i a)) (a_start a) pos lo st (x_tp x) drep (a_vss a)).
  rewrite Hxx. sep_apply (lgf_lit_release_x a (a_lxb a) sw Hxl Hxb).
  sep_apply (HTE (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x)).
  sep_apply (data_at_data_at_ Tsh (tptr tuchar) lp (a_vlp a)).
  rewrite Heq, <- Hos. replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cancel.
Qed.

(* the condition of the leftover branch: split literals not switched yet, fewer left in dst than ll *)
Definition fin_b (a: la) (sw: bool) (j ll: Z) : bool :=
  match a_l a with LSplit _ => negb sw && (a_n a - LITBUFFEREXTRASIZE - j <? ll) | _ => false end.

Lemma fin_b_false (a: la) (sw: bool) (j ll: Z) :
  Int.repr (lit_code a sw) <> Int.repr 2 -> fin_b a sw j ll = false.
Proof.
  unfold fin_b, lit_code, loc_code. destruct sw, (a_l a); simpl; auto; intros H; contradiction.
Qed.

Lemma lit_code_split (a: la) (sw: bool) :
  Int.repr (lit_code a sw) = Int.repr 2 -> sw = false /\ exists lb, a_l a = LSplit lb.
Proof.
  unfold lit_code, loc_code, LOC_NOT_IN_DST, LOC_IN_DST, LOC_SPLIT.
  destruct sw, (a_l a); intros H; try (apply repr_inj_unsigned in H; rep_lia); eauto.
Qed.

Lemma lit_fix_split (a: la) (lb: Z) :
  a_l a = LSplit lb ->
  lit_fix a =
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (a_n a))) (a_p a) *
  (field_at Ews t_dctx (DOT _litPtr) (offset_val lb (a_ob a)) (a_p a) *
   field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a)) (a_p a) *
   field_at Ews t_dctx (DOT _litBuffer) (offset_val lb (a_ob a)) (a_p a)).
Proof. intros E. unfold lit_fix. rewrite E. reflexivity. Qed.

(* (size_t)(p + A - (p + B)) < ll *)
Lemma fin_chk_val (b: val) (A B ll: Z) :
  isptr b -> 0 <= B <= A -> A <= Ptrofs.max_unsigned -> 0 <= ll <= Int64.max_unsigned ->
  force_val (sem_cast tint tbool (eval_binop Olt tulong tulong
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val A b) (offset_val B b)))
    (Vlong (Int64.repr ll)))) = Val.of_bool (A - B <? ll).
Proof.
  intros Hb HAB HA Hll. destruct b; try contradiction.
  simpl. unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr A)) (Ptrofs.add i (Ptrofs.repr B)) = Ptrofs.repr (A - B)).
  { rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted. apply ptrofs_sub_repr. }
  rewrite E. rewrite Ptrofs.divs_one by (compute; congruence).
  unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  unfold Val.of_bool.
  destruct (zlt (A - B) ll), (A - B <? ll) eqn:Q; simpl; auto;
    try (apply Z.ltb_lt in Q; lia); try (apply Z.ltb_ge in Q; lia).
Qed.

(* the literals of the executors: LIn the input array (its readable copy), LExtra / switched LSplit
   litExtraBuffer, LDst in the output array *)
Definition fin_ls (a: la) (x: lfx) : litsrc :=
  match a_l a with
  | LIn _ => LitSep (x_sh1 x) (iw_base (a_i a)) (iw_c (a_i a))
  | LDst _ => LitIn
  | _ => LitSep Ews (lit_extra (a_p a)) (x_xc x)
  end.
Definition fin_lother (a: la) (x: lfx) : mpred :=
  let i := a_i a in
  match a_l a with
  | LIn _ => data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a))
  | LDst _ => data_at (x_sh1 x) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) *
              data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a))
  | _ => data_at (x_sh1 x) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i)
  end.

Lemma fin_lres (a: la) (x: lfx) :
  Zlength (iw_c (a_i a)) = iw_N (a_i a) -> Zlength (x_xc x) = LITEXTRA_N ->
  data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
  data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)) =
  BlkSeqEXEC.lit_res (fin_ls a x) * fin_lother a x.
Proof.
  intros H1 H2. unfold fin_ls, fin_lother, BlkSeqEXEC.lit_res.
  destruct (a_l a); rewrite ?H1, ?H2, ?emp_sepcon; try reflexivity; apply sepcon_comm.
Qed.

Lemma fin_lres_back (a: la) (x: lfx) :
  Zlength (iw_c (a_i a)) = iw_N (a_i a) -> Zlength (x_xc x) = LITEXTRA_N ->
  BlkSeqEXEC.lit_res (fin_ls a x) * fin_lother a x |--
  data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
  data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)).
Proof. intros H1 H2. rewrite (fin_lres a x H1 H2). apply derives_refl. Qed.

Lemma fin_lit_now_eq (a: la) (xc: list val) (sw: bool) :
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a sw))) (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) = lit_now a xc sw.
Proof. reflexivity. Qed.

Lemma lit_li_add (a: la) (sw: bool) (j l: Z) : lit_li a sw (j + l) = lit_li a sw j + l.
Proof. unfold lit_li. destruct (a_l a); try destruct sw; lia. Qed.

(* litPtr + ll - 32 *)
Lemma fin_sub32 (b: val) (A: Z) :
  isptr b -> force_val (sem_sub_pi tuchar Signed (offset_val A b) (Vint (Int.repr 32))) = offset_val (A - 32) b.
Proof.
  intros Hb. destruct b; try contradiction. simpl. unfold sem_sub_pi. simpl. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc. f_equal. rewrite Ptrofs.neg_repr, ptrofs_add_repr.
  f_equal; lia.
Qed.

(* op += r *)
Lemma fin_add (b: val) (A n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val A b) (Vlong (Int64.repr n))) =
  offset_val (A + n) b.
Proof.
  intros Hb Hn. destruct b; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma fin_lit_now_fold (a: la) (xc: list val) (sw: bool) :
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a sw))) (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) |-- lit_now a xc sw.
Proof. unfold lit_now. apply derives_refl. Qed.

Lemma fin_nsplit (a: la) (sw: bool) :
  Int.repr (lit_code a sw) <> Int.repr 2 -> match a_l a with LSplit _ => sw = true | _ => True end.
Proof.
  unfold lit_code, loc_code. destruct (a_l a), sw; auto; intros H; contradiction.
Qed.

(* the executors' literal source is the exact model's (litExtraBuffer holds lxb) *)
Lemma fin_lsrc (a: la) (x: lfx) (sw: bool) :
  (match a_l a with LSplit _ => sw = true | _ => True end) -> x_xc x = zbytes (a_lxb a) ->
  ls_l (fin_ls a x) = xl_lsrc a sw.
Proof.
  intros H Hx. unfold fin_ls, xl_lsrc, ls_l. destruct (a_l a); rewrite ?Hx; auto. subst sw. reflexivity.
Qed.

Lemma fin_ls_base (a: la) (x: lfx) (sw: bool) :
  (match a_l a with LSplit _ => sw = true | _ => True end) ->
  BlkSeqEXEC.lit_base (fin_ls a x) (a_ob a) = lit_base a sw.
Proof.
  intros H. unfold fin_ls, lit_base, BlkSeqEXEC.lit_base. destruct (a_l a); auto. subst sw. reflexivity.
Qed.

(* the history facts of the executors' preconditions *)
Lemma fin_hist_pre (a: la) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> ex_safe a K j sw c -> 0 < a_nb a ->
  Zlength c <= 2 ^ 63 - 1 /\ 0 <= a_ps a <= a_d a + K /\ a_d a + K <= a_E a <= Zlength c /\
  a_E a <= a_d a + a_cap a /\ a_d a + a_cap a <= Zlength c /\
  exec_ext_ok (a_x a) c /\
  fs_prefixStart (a_fs a) = offset_val (a_ps a) (a_ob a) /\
  fs_virtualStart (a_fs a) = offset_val (a_ps a - ext_len (a_x a)) (a_ob a) /\
  dict_end (a_x a) (a_ob a) (fs_dictEnd (a_fs a)) = fs_dictEnd (a_fs a).
Proof.
  intros Hla Hes Hnb.
  pose proof (lgf_E_le a Hla) as HE.
  destruct Hla as ((Hosh & HoN & HoN32 & Hod & Hocap & HodN) & Hiw & Hlits & Hbsm & Hnbsm & Hnbr & Hnb0 &
                   Hso & Hrep & Hfe & Hc0 & Hlay).
  destruct (Hnb0 ltac:(lia)) as [_ Hcap].
  destruct (Hlay Hcap) as (Hps & Hfps & Hfvs & Hel & Hext).
  destruct Hes as (HK0 & HKE & Hj & Hjsw & Hcl & Hun).
  unfold a_E in *. unfold a_d, a_cap, a_ps, a_x, a_ob in *.
  assert (HcN: Zlength c <= 2 ^ 63 - 1) by lia.
  split; [lia|]. split; [lia|]. split; [destruct (a_l a); lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold exec_ext_ok. split; [lia|]. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia. }
  split; [exact Hfps|]. split; [exact Hfvs|].
  destruct (hc_ext (a_h a)); simpl in *; try reflexivity; symmetry; tauto.
Qed.

(* the facts of exec_spec's precondition (literals not split in dst) and the history pointers *)
Lemma fin_exec_pre (a: la) (x: lfx) (K j: Z) (sw: bool) (c: list val) :
  la_ok a -> lfx_ok a x -> ex_safe a K j sw c -> 0 < a_nb a ->
  match a_l a with LSplit _ => sw = true | _ => True end ->
  Zlength c <= 2 ^ 63 - 1 /\ 0 <= a_ps a <= a_d a + K /\ a_d a + K <= a_E a <= Zlength c /\
  a_E a <= a_d a + a_cap a /\
  match fin_ls a x with
  | LitSep shl _ cl => readable_share shl /\ 0 <= lit_li a sw j <= lit_lim a sw /\
                       lit_lim a sw + WILDCOPY_OVERLENGTH <= Zlength cl
  | LitIn => a_E a <= lit_li a sw j <= lit_lim a sw /\ lit_lim a sw + WILDCOPY_OVERLENGTH <= Zlength c
  end /\
  lit_lim a sw - lit_li a sw j = a_n a - j /\
  exec_ext_ok (a_x a) c /\
  fs_prefixStart (a_fs a) = offset_val (a_ps a) (a_ob a) /\
  fs_virtualStart (a_fs a) = offset_val (a_ps a - ext_len (a_x a)) (a_ob a) /\
  dict_end (a_x a) (a_ob a) (fs_dictEnd (a_fs a)) = fs_dictEnd (a_fs a).
Proof.
  intros Hla Hlx Hes Hnb Hsw.
  pose proof (lgf_E_le a Hla) as HE.
  destruct Hla as ((Hosh & HoN & HoN32 & Hod & Hocap & HodN) & Hiw & Hlits & Hbsm & Hnbsm & Hnbr & Hnb0 &
                   Hso & Hrep & Hfe & Hc0 & Hlay).
  destruct (Hnb0 ltac:(lia)) as [_ Hcap].
  destruct (Hlay Hcap) as (Hps & Hfps & Hfvs & Hel & Hext).
  destruct Hlx as (Hos & Hsh1 & Hsh2 & Heq & Hxc).
  destruct Hes as (HK0 & HKE & Hj & Hjsw & Hcl & Hun).
  destruct Hxc as (Hxl & Hxc).
  destruct Hiw as (_ & Hoff & Hon & HN32 & HiN & _).
  destruct Hlits as (_ & Hn & Hll).
  unfold a_E, lit_li, lit_lim, fin_ls in *. unfold a_d, a_cap, a_ps, a_x, a_n, a_ob in *.
  assert (HcN: Zlength c <= 2 ^ 63 - 1) by lia.
  split; [lia|]. split; [lia|]. split; [destruct (a_l a); lia|]. split; [lia|].
  split.
  { destruct (a_l a) as [off| |lb|lb].
    - destruct Hll as (? & ? & _). split; [auto|]. rewrite HiN. lia.
    - split; [auto|]. rewrite Hxl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia.
    - destruct Hll as (? & ? & _). unfold WILDCOPY_OVERLENGTH in *. lia.
    - subst sw. split; [auto|]. rewrite Hxl. unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. lia. }
  split; [destruct (a_l a); try subst sw; lia|].
  split.
  { unfold exec_ext_ok. split; [lia|]. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia. }
  split; [exact Hfps|]. split; [exact Hfvs|].
  destruct (hc_ext (a_h a)); simpl in *; try reflexivity; symmetry; tauto.
Qed.

(* ===================== the iteration's states ===================== *)

(* the iteration's starting point: queue head (ll, ml, off), the rest q' *)
Definition fin_pre (a: la) (x: lfx) (w: lst) (ll ml off: Z) (q': list (Z * Z * Z)) : Prop :=
  la_ok a /\ la_pend a /\ lfx_ok a x /\ LIP a x w /\ fin_ph a w /\ w_ie w < a_nb a /\
  w_q w = (ll, ml, off) :: q'.

(* the state after the iteration *)
Definition fin_next (w: lst) (q': list (Z * Z * Z)) (ring': list (option (Z * Z * Z))) (K' j': Z) (sw': bool)
    (c': list val) : lst :=
  mk_lst (w_id w) (w_ie w + 1) (w_pos w) (w_lo w) (w_st w) (w_drep w) ring' q' K' j' sw' c' (w_pp w).

(* la_post's PROP for an error return r with output array oc' (rep' = rep) *)
Definition fin_errP (a: la) (r: Z) (oc': list val) : Prop :=
  let o := a_o a in let h := a_h a in let i := a_i a in
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = oa_N o /\ rep_ok (a_rep a) /\
  unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + oa_cap o) /\
  (is_error_code r = false ->
     r <= oa_cap o /\
     unchanged_outside (oa_c o) oc' (oa_d o) (oa_d o + Z.min (oa_cap o) (r + WILDCOPY_OVERLENGTH)) /\
     (hist_def (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) ->
      (ext_clean (oa_d o) (oa_cap o) (hc_ext h) \/ (r <= a_bsm a /\ ext_far (oa_d o) (oa_cap o) (a_bsm a) (hc_ext h))) ->
        exists cnt, sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\ bytes_ok cnt)) /\
  (oa_cap o = 0 \/
   (hist_view (oa_c o) (oa_d o) (hc_ps h) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h) /\
    ext_clear (oa_d o) (hc_ps h) (oa_cap o) (a_bsm a) (hc_ext h) (hc_hist h) (hc_out h) (hc_wsize h)) ->
   match seqs_model (a_os a) (iw_s i) (a_nb a) (a_rep a) (hc_hist h) (hc_out h) (a_lits a) (hc_wsize h) with
   | Some (cnt, rep2) =>
       Zlength cnt <= a_bsm a ->
       (is_error_code r = false /\ r = Zlength cnt /\ sublist (oa_d o) (oa_d o + r) oc' = zbytes cnt /\
        a_rep a = rep2) \/
       (is_error_code r = true /\ oa_cap o < Zlength cnt)
   | None => True
   end) /\
  (is_error_code r = true -> dec_err r) /\
  (byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc') /\
  seqs_exact (a_os a) (a_rep a) (a_l a) (a_lits a) (a_lxb a) (a_nb a) o i h r oc' (a_rep a).

(* ===================== the executor's steps (FXSTEP, pure; a copy of MainDefs' XSTEP) ===================== *)

(* the executor's facts before executing the queue head e0 = (ll, ml, off) = sequence ie *)
Definition FXP (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (e0: Z * Z * Z) : Prop :=
  let '(ll, ml, off) := e0 in
  0 <= ie < a_nb a /\ ex_safe a K j sw c /\ ex_def a K j sw c /\
  0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= off <= SIZE_MAX /\
  forall seqs, DM a (x_t x) seqs ->
    Zlength seqs = a_nb a /\ 1 <= sq_ov (Znth ie seqs) < 2 ^ 32 /\
    ll = sq_ll (Znth ie seqs) /\ ml = sq_ml (Znth ie seqs) /\
    off = fst (c_offset (rep_chain (a_rep a) (sublist 0 ie seqs)) ll (sq_ov (Znth ie seqs))) /\
    ex_model a seqs ie K j sw c.

(* ... after it (ie the index of the next sequence) *)
Definition FXQ (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) : Prop :=
  ex_safe a K j sw c /\ ex_def a K j sw c /\ forall seqs, DM a (x_t x) seqs -> ex_model a seqs ie K j sw c.

(* an error return with the output array c: la_post's facts *)
Definition FXERR (a: la) (c: list val) : Prop :=
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

(* not the split head: not LSplit, or switched *)
Definition fnosplit (a: la) (sw: bool) : Prop := match a_l a with LSplit _ => sw = true | _ => True end.

(* the leftover copy's result: c1 = c with [k, k + lo) := the split literals [li, li + lo) (safecopyDstBeforeSrc's POST) *)
Definition fcopied (c c1: list val) (k li lo: Z) : Prop :=
  Zlength c1 = Zlength c /\
  (lo < WILDCOPY_OVERLENGTH \/ li - k <= WILDCOPY_VECLEN \/ WILDCOPY_OVERLENGTH <= li - k ->
     sublist k (k + lo) c1 = sublist k (k + lo) (listcopy c li k (Z.to_nat lo))) /\
  (Forall is_byte_val (sublist li (li + lo) c) -> Forall is_byte_val (sublist k (k + lo) c1)) /\
  unchanged_outside c c1 k (k + lo).

Definition FXSTEP : Prop :=
  forall (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z),
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (* (N) ZSTD_execSequence on the head, literals not the split head *)
  (fnosplit a sw ->
   let li := lit_li a sw j in let lim := lit_lim a sw in let ls := fin_ls a x in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_err k E li lim ll ml off ps elen = true -> unchanged_outside c c' k E -> FXERR a c') /\
   (exec_err k E li lim ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       sublist k (k + (ll + ml)) c' =
         sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c')) /\
  (* (S) ZSTD_execSequenceSplitLitBuffer: the split head holds the literals *)
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_li a false j + ll <= lit_lim a false ->
   let li := lit_li a false j in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_split_err k E li ll ml off ps elen = true -> unchanged_outside c c' k E -> FXERR a c') /\
   (exec_split_err k E li ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       (lit_exact_split k li ll ->
          sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps xs)) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) false c')) /\
  (* (X1) the split head ends before the head's literals: the leftover lo, switch, execSequence on litExtraBuffer *)
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_lim a false - lit_li a false j < ll ->
   let li := lit_li a false j in let lo := lit_lim a false - li in
   (0 < lo -> E - k < lo -> FXERR a c) /\
   forall c1, (lo = 0 -> c1 = c) -> (0 < lo -> lo <= E - k /\ fcopied c c1 k li lo) ->
   let k1 := k + lo in let ls := fin_ls a x in let li1 := lit_li a true (j + lo) in let lim1 := lit_lim a true in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c1 -> byte_cells (lit_arr ls c1) -> ext_bytes xs -> byte_cells c') -> xd_ub c1 c' ->
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = true -> unchanged_outside c1 c' k1 E -> FXERR a c') /\
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = false ->
    unchanged_outside c1 c' k1 (Z.min E (k1 + (ll - lo + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c') ->
    (ext_read_ok xs k1 E (ll - lo) ml off ps ->
       sublist k1 (k1 + (ll - lo + ml)) c' =
         sublist k1 (k1 + (ll - lo + ml)) (exec_c c1 k1 (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k1 c1) -> Forall is_byte_val (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ->
        ext_def xs c1 -> Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c')).

(* ===================== FIN_INV's helpers ===================== *)

Lemma fi_rd_range (s: list Z) (pos nb v pos': Z) :
  0 <= nb -> rd s pos nb = Some (v, pos') -> 0 <= v < 2 ^ nb.
Proof.
  intros Hnb H. unfold rd in H. destruct (pos - nb <? 0) eqn:E; [discriminate|].
  inversion H; subst. apply Z.ltb_ge in E. unfold bs_peek_s.
  destruct (pos <? 0) eqn:E1; [apply Z.ltb_lt in E1; lia|].
  destruct (pos - nb >=? 0) eqn:E2; [|rewrite Z.geb_leb, Z.leb_gt in E2; lia].
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma fi_cell_sym (t: fse_table) (s: Z) : fse_ok KOF t -> 0 <= fe_sym (fse_cell t s) <= MaxOff.
Proof.
  intros (_ & _ & HF). unfold fse_cell.
  destruct (Nat.lt_ge_cases (Z.to_nat s) (length (ft_cells t))) as [Hl|Hl].
  - rewrite Forall_forall in HF. apply (HF _ (nth_In _ _ Hl)).
  - rewrite nth_overflow by exact Hl. simpl. unfold MaxOff. lia.
Qed.

Lemma fi_ov_range (c e: Z) : 0 <= c <= MaxOff -> 0 <= e < 2 ^ c -> 1 <= 2 ^ c + e < 2 ^ 32.
Proof.
  intros Hc He. unfold MaxOff in Hc.
  assert (2 ^ c <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  assert (1 <= 2 ^ c) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  change (2 ^ 32) with (2 ^ 31 + 2 ^ 31). lia.
Qed.

Lemma fi_decode_seqs_ov (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  fse_ok KOF tOF ->
  forall (sLL sOF sML pos: Z) (l: list sequence) (p: Z),
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) ->
  Forall (fun sq => 1 <= sq_ov sq < 2 ^ 32) l.
Proof.
  intros HOF. induction k as [|k IH]; intros sLL sOF sML pos l p H.
  - simpl in H. inversion H; subst. constructor.
  - simpl decode_seqs in H.
    destruct (rd V pos _) as [[eOF p1]|] eqn:R1; [|discriminate].
    destruct (rd V p1 _) as [[eML p2]|]; [|discriminate].
    destruct (rd V p2 _) as [[eLL p3]|]; [|discriminate].
    pose proof (fi_cell_sym tOF sOF HOF) as Hc.
    assert (Hov: 1 <= 2 ^ fe_sym (fse_cell tOF sOF) + eOF < 2 ^ 32).
    { apply fi_ov_range; [exact Hc|]. eapply fi_rd_range; [lia|exact R1]. }
    destruct k as [|k'].
    + inversion H; subst. constructor; [exact Hov|constructor].
    + destruct (rd V p3 _) as [[uLL p4]|]; [|discriminate].
      destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
      destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
      destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l' p']|] eqn:D; [|discriminate].
      inversion H; subst. constructor; [exact Hov|]. eapply IH; exact D.
Qed.

Lemma fi_DM_ov (a: la) (x: lfx) (seqs: list sequence) :
  la_ok a -> lfx_ok a x -> DM a (x_t x) seqs -> Forall (fun sq => 1 <= sq_ov sq < 2 ^ 32) seqs.
Proof.
  intros Ha Hx HD. destruct Hx as [Hos _].
  destruct Ha as (_ & _ & _ & _ & _ & _ & _ & Hsq & _).
  rewrite Hos in Hsq. unfold DM in HD. destruct (x_t x) as [[tLL tOF] tML].
  destruct Hsq as (_ & HOF & _). unfold decode_seq_stream in HD.
  destruct (negb (bs_okb _)); [discriminate|].
  destruct (rd _ _ (ft_log tLL)) as [[sLL p1]|]; [|discriminate].
  destruct (rd _ _ (ft_log tOF)) as [[sOF p2]|]; [|discriminate].
  destruct (rd _ _ (ft_log tML)) as [[sML p3]|]; [|discriminate].
  destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l p]|] eqn:D; [|discriminate].
  destruct p; try discriminate. inversion HD; subst.
  eapply fi_decode_seqs_ov; [exact HOF|exact D].
Qed.

Lemma fi_rep_chain_app (r: Z * Z * Z) (l1 l2: list sequence) :
  rep_chain r (l1 ++ l2) = rep_chain (rep_chain r l1) l2.
Proof. revert r. induction l1 as [|s l1 IH]; intros r; simpl; [reflexivity|apply IH]. Qed.

Lemma fi_ring_next (ie: Z) (ring ring': list (option (Z * Z * Z))) (e: Z * Z * Z) (q': list (Z * Z * Z)) :
  0 <= ie -> Zlength (e :: q') <= 8 -> ring_ok ie ring (e :: q') ->
  (ring' = ring \/ exists v, ring' = upd_Znth (ie mod 8) ring v) ->
  ring_ok (ie + 1) ring' q'.
Proof.
  intros Hie Hlen (HL & HR) Hr'. rewrite Zlength_cons in Hlen.
  assert (Hq: forall k, 0 <= k < Zlength q' -> Znth ((ie + 1 + k) mod 8) ring = Some (Znth k q')).
  { intros k Hk. specialize (HR (k + 1) ltac:(rewrite Zlength_cons; lia)).
    rewrite Znth_pos_cons in HR by lia. replace (k + 1 - 1) with k in HR by lia.
    replace (ie + 1 + k) with (ie + (k + 1)) by lia. exact HR. }
  destruct Hr' as [-> | [v ->]].
  - split; [exact HL|exact Hq].
  - split; [rewrite Zlength_upd_Znth; exact HL|].
    intros k Hk. rewrite upd_Znth_diff.
    + apply Hq; exact Hk.
    + rewrite HL. apply Z.mod_pos_bound; lia.
    + rewrite HL. apply Z.mod_pos_bound; lia.
    + intros E. assert (Hm: (ie + 1 + k - ie) mod 8 = 0).
      { rewrite Zminus_mod, E, Z.sub_diag. reflexivity. }
      replace (ie + 1 + k - ie) with (k + 1) in Hm by lia.
      rewrite Z.mod_small in Hm by lia. lia.
Qed.

(* ===================== the invariant's plumbing for FIN ===================== *)

(* from LI_P at the queue head to the executor's facts; from the executor's facts after it to LI_P at ie + 1
   (the ring unchanged, or the head's slot rewritten: the leftover branch's litLength -= lo); an executor error
   to la_post's PROP *)
Definition FIN_INV : Prop :=
  forall (a: la) (x: lfx) (w: lst) (ll ml off: Z) (q': list (Z * Z * Z)),
  fin_pre a x w ll ml off q' ->
  FXP a x (w_ie w) (w_K w) (w_j w) (w_sw w) (w_c w) (ll, ml, off) /\
  (forall (ring': list (option (Z * Z * Z))) (K' j': Z) (sw': bool) (c': list val),
     (ring' = w_ring w \/ exists v, ring' = upd_Znth (w_ie w mod 8) (w_ring w) v) ->
     FXQ a x (w_ie w + 1) K' j' sw' c' ->
     xl_inv a (x_t x) (w_id w) K' c' (w_drep w) j' sw' (w_pos w) (w_lo w) (w_st w) q' ->
     LIP a x (fin_next w q' ring' K' j' sw' c')) /\
  (forall (r: Z) (c': list val),
     FXERR a c' -> 0 <= r <= Int64.max_unsigned -> is_error_code r = true -> dec_err r ->
     Zlength c' = oa_N (a_o a) -> xl_none a -> fin_errP a r c') /\
  (* the exact model at the queue head (BlkSeqLoopLongXE's steps) *)
  xl_pos a (w_K w) (w_j w) (w_sw w) (w_c w) /\
  xl_inv a (x_t x) (w_id w) (w_K w) (w_c w) (w_drep w) (w_j w) (w_sw w) (w_pos w) (w_lo w) (w_st w)
    ((ll, ml, off) :: q').

Lemma fin_inv_ok : FIN_INV.
Proof.
  intros a x w ll ml off q' (Ha & Hp & Hx & HL & Hph & Hlt & Hq).
  unfold LIP, LI_P, fold_right in HL.
  destruct HL as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _).
  unfold fin_ph in Hph. destruct Hph as [Hph Hpos]. rewrite Hq in H4, H5, H6, H11, H12.
  pose proof (Forall_inv H6) as He. cbv beta iota in He.
  pose proof (Forall_inv_tail H6) as Hq'.
  rewrite Zlength_cons in H4.
  assert (Hsq: forall seqs, DM a (x_t x) seqs ->
            Zlength seqs = a_nb a /\
            ll = sq_ll (Znth (w_ie w) seqs) /\ ml = sq_ml (Znth (w_ie w) seqs) /\
            off = fst (c_offset (rep_chain (a_rep a) (sublist 0 (w_ie w) seqs)) (sq_ll (Znth (w_ie w) seqs))
                                (sq_ov (Znth (w_ie w) seqs))) /\
            q' = q_of (rep_chain (a_rep a) (sublist 0 (w_ie w + 1) seqs)) (sublist (w_ie w + 1) (w_id w) seqs)).
  { intros seqs HD. destruct (H11 seqs HD) as (Hlen & _ & HQ & _).
    rewrite Hph in HQ |- *. rewrite (sublist_next (w_ie w) (a_nb a)) in HQ by lia.
    cbn [q_of] in HQ. injection HQ as E1 E2 E3 E4.
    split; [exact Hlen|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
    rewrite E4, (sublist_last_1 0 (w_ie w)) by lia. rewrite fi_rep_chain_app. reflexivity. }
  split; [|split; [|split; [|split]]].
  - unfold FXP. destruct He as (Hll & Hml & Hoff).
    split; [lia|]. split; [exact H9|]. split; [exact H10|].
    split; [exact Hll|]. split; [exact Hml|]. split; [exact Hoff|].
    intros seqs HD. destruct (Hsq seqs HD) as (Hlen & E1 & E2 & E3 & _).
    destruct (H11 seqs HD) as (_ & _ & _ & HM).
    pose proof (fi_DM_ov a x seqs Ha Hx HD) as Hov. rewrite Forall_Znth in Hov.
    split; [exact Hlen|]. split; [apply Hov; lia|].
    split; [exact E1|]. split; [exact E2|]. split; [rewrite E1; exact E3|]. exact HM.
  - intros ring' K' j' sw' c' Hr (Q1 & Q2 & Q3) Hxl.
    unfold LIP, LI_P, fin_next.
    cbn [fold_right w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp].
    split; [lia|]. split; [exact H2|]. split; [lia|]. split; [lia|].
    split; [eapply fi_ring_next; [lia| rewrite Zlength_cons; lia | exact H5 | exact Hr]|].
    split; [exact Hq'|]. split; [exact H7|]. split; [exact H8|]. split; [exact Q1|]. split; [exact Q2|].
    split; [|split; [exact Hxl | exact I]].
    intros seqs HD. destruct (H11 seqs HD) as (Hlen & Hdm & _ & _).
    destruct (Hsq seqs HD) as (_ & _ & _ & _ & E4).
    split; [exact Hlen|]. split; [exact Hdm|]. split; [exact E4|]. apply Q3; exact HD.
  - intros r c' (U & M & B) Hr Herr Hde Hlen Hxn. unfold fin_errP.
    split; [exact Hr|]. split; [exact Hlen|].
    split; [destruct Ha as (_ & _ & _ & _ & _ & _ & _ & _ & Hrep & _); exact Hrep|].
    split; [exact U|]. split; [intros E; congruence|].
    split; [|split; [intros _; exact Hde | split; [exact B | exact (xl_exact_none a r c' (a_rep a) Herr Hxn)]]].
    intros Hv. specialize (M Hv).
    destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; [|exact I].
    intros Hc. right. split; [exact Herr|apply M; exact Hc].
  - destruct H9 as (X1 & X2 & X3 & X4 & X5 & _). unfold xl_pos. auto.
  - exact H12.
Qed.

(* ===================== FXSTEP: BlkSeqLoopLongXstep.v's proof, renamed ===================== *)

(* ===================== list helpers ===================== *)

Lemma xs_Forall_sub (l: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l ->
  (Forall is_byte_val (sublist a b l) <-> forall q, a <= q < b -> is_byte_val (Znth q l)).
Proof.
  intros Hab Hb. rewrite VST.zlist.list_solver.Forall_Znth. rewrite Zlength_sublist by lia. split.
  - intros H q Hq. specialize (H (q - a) ltac:(lia)). rewrite Znth_sublist in H by lia.
    replace (q - a + a) with q in H by lia. exact H.
  - intros H q Hq. rewrite Znth_sublist by lia. apply H; lia.
Qed.

Lemma xs_zbytes_def (l0: list Z) : bytes_ok l0 -> Forall is_byte_val (zbytes l0).
Proof.
  induction 1; simpl; constructor; auto. exists x. unfold is_byte in H. split; [lia|reflexivity].
Qed.

Lemma xs_sublist_ext (l1 l2: list val) (a b: Z) :
  0 <= a <= b -> b <= Zlength l1 -> Zlength l2 = Zlength l1 ->
  (forall q, a <= q < b -> Znth q l2 = Znth q l1) -> sublist a b l2 = sublist a b l1.
Proof.
  intros Hab Hb Hl H. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia. apply H; lia.
Qed.

(* the forward copy from ahead (di < si) reads only bytes not yet written *)
Lemma xs_listcopy_ahead (c: list val) (si di: Z) (n: nat) :
  0 <= di < si -> si + Z.of_nat n <= Zlength c ->
  forall t, 0 <= t < Z.of_nat n -> Znth (di + t) (listcopy c si di n) = Znth (si + t) c.
Proof.
  revert c si di. induction n as [|m IH]; intros c si di Hd Hn t Ht; [simpl in Ht; lia|].
  rewrite Nat2Z.inj_succ in *. simpl.
  assert (Hu: Zlength (upd_Znth di c (Znth si c)) = Zlength c) by (apply Zlength_upd_Znth).
  destruct (Z.eq_dec t 0) as [->|Ht0].
  - rewrite listcopy_outside by (rewrite ?Hu; lia). rewrite Z.add_0_r, upd_Znth_same by lia.
    rewrite Z.add_0_r. reflexivity.
  - replace (di + t) with ((di + 1) + (t - 1)) by lia.
    rewrite IH by (rewrite ?Hu; lia). rewrite upd_Znth_diff by lia. f_equal; lia.
Qed.

Lemma xs_listcopy_ahead_sub (c: list val) (si di n: Z) :
  0 <= di < si -> 0 <= n -> si + n <= Zlength c ->
  sublist di (di + n) (listcopy c si di (Z.to_nat n)) = sublist si (si + n) c.
Proof.
  intros Hd Hn Hs. assert (Hl: Zlength (listcopy c si di (Z.to_nat n)) = Zlength c)
    by (apply listcopy_Zlength; lia).
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros q Hq. rewrite Zlength_sublist in Hq by lia. rewrite !Znth_sublist by lia.
  replace (q + di) with (di + q) by lia. rewrite xs_listcopy_ahead by lia. f_equal; lia.
Qed.

(* ===================== model helpers ===================== *)

Lemma xs_exec_len (wsize: Z) (rep: Z * Z * Z) (hist lits out: list Z) (seqs: list sequence)
    (out' lits': list Z) (rep': Z * Z * Z) :
  exec_seqs wsize rep hist lits out seqs = Some (out', lits', rep') ->
  Zlength out + Zlength lits <= Zlength out' + Zlength lits'.
Proof.
  revert rep lits out. induction seqs as [|sq rest IH]; intros rep lits out H.
  - simpl in H. inversion H; subst. lia.
  - simpl in H.
    destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep2]|] eqn:E2; [|discriminate].
    destruct (offset >? Zlength hist + Zlength (out ++ firstn (Z.to_nat (sq_ll sq)) lits)); [discriminate|].
    destruct (offset >? wsize + Zlength hist); [discriminate|].
    specialize (IH _ _ _ H).
    rewrite lz_copy_length, Zlength_app in IH. repeat rewrite Zlength_correct in IH. repeat rewrite Zlength_correct.
    pose proof (firstn_skipn (Z.to_nat (sq_ll sq)) lits) as Hfs.
    apply (f_equal (@length Z)) in Hfs. rewrite app_length in Hfs. lia.
Qed.

Lemma xs_sum_llml_app (l1 l2: list sequence) : sum_llml (l1 ++ l2) = sum_llml l1 + sum_llml l2.
Proof. induction l1 as [|sq l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma xs_sum_ll_app (l1 l2: list sequence) : sum_ll (l1 ++ l2) = sum_ll l1 + sum_ll l2.
Proof. induction l1 as [|sq l IH]; simpl; [reflexivity|]. rewrite IH. lia. Qed.

Lemma xs_rep_chain_app (r: Z * Z * Z) (l1 l2: list sequence) :
  rep_chain r (l1 ++ l2) = rep_chain (rep_chain r l1) l2.
Proof. revert r; induction l1 as [|sq l1 IH]; intros r; simpl; [reflexivity | apply IH]. Qed.

Lemma xs_sub_snoc (seqs: list sequence) (ie: Z) :
  0 <= ie < Zlength seqs -> sublist 0 (ie + 1) seqs = sublist 0 ie seqs ++ [Znth ie seqs].
Proof.
  intros H. rewrite (sublist_split 0 ie (ie + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma xs_sub_cons (seqs: list sequence) (ie nb: Z) :
  0 <= ie < nb -> nb <= Zlength seqs -> sublist ie nb seqs = Znth ie seqs :: sublist (ie + 1) nb seqs.
Proof.
  intros H Hn. rewrite (sublist_split ie (ie + 1) nb) by lia. rewrite sublist_len_1 by lia. reflexivity.
Qed.

Lemma xs_firstn_sub {A} {IA: Inhabitant A} (l: list A) (j n t: Z) :
  0 <= j -> 0 <= t -> j + t <= n -> n <= Zlength l ->
  firstn (Z.to_nat t) (sublist j n l) = sublist j (j + t) l.
Proof.
  intros. rewrite <- sublist_firstn. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

Lemma xs_skipn_sub {A} {IA: Inhabitant A} (l: list A) (j n t: Z) :
  0 <= j -> 0 <= t -> j + t <= n -> n <= Zlength l ->
  skipn (Z.to_nat t) (sublist j n l) = sublist (j + t) n l.
Proof.
  intros. rewrite <- sublist_skip by lia. rewrite Zlength_sublist by lia.
  rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* ===================== the context ===================== *)

Ltac xs_fold := change (oa_d (a_o ?a)) with (a_d a) in *; change (oa_cap (a_o ?a)) with (a_cap a) in *;
  change (hc_ps (a_h ?a)) with (a_ps a) in *; change (hc_ext (a_h ?a)) with (a_x a) in *;
  change (Zlength (a_lits ?a)) with (a_n a) in *.

Lemma xs_basic (a: la) (x: lfx) :
  la_ok a -> la_pend a -> lfx_ok a x -> 0 < a_nb a ->
  Zlength (oa_c (a_o a)) = oa_N (a_o a) /\ oa_N (a_o a) <= 2 ^ 63 - 1 /\ 0 <= a_d a /\ 0 < a_cap a /\
  a_d a + a_cap a <= oa_N (a_o a) /\
  0 <= a_ps a <= a_d a /\ 0 <= ext_len (a_x a) <= 2 ^ 63 - 1 /\ ext_in_bounds (a_x a) (oa_N (a_o a)) /\
  bytes_ok (a_lits a) /\ 0 <= a_n a <= a_bsm a /\ a_bsm a <= ZSTD_BLOCKSIZE_MAX /\ rep_ok (a_rep a) /\
  a_d a <= a_E a <= a_d a + a_cap a /\ a_os a = Some (x_t x).
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & Hnb & Hcap & Hso & Hrep & Hfe & Hc0 & Hlay) Hpend (Hos & _) Hnb0.
  destruct (Hcap ltac:(lia)) as [_ Hcap0]. specialize (Hlay Hcap0).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Hla as (Hlb & Hln & Hl).
  xs_fold. unfold a_n.
  repeat split; try lia; auto.
  - unfold ext_in_bounds. destruct (a_x a); simpl in *; tauto || lia.
  - pose proof (Zlength_nonneg (a_lits a)). lia.
  - unfold a_E. revert Hl. unfold WILDCOPY_OVERLENGTH. destruct (a_l a); lia.
  - unfold a_E. revert Hl. unfold WILDCOPY_OVERLENGTH. destruct (a_l a); lia.
Qed.

(* ext_read_ok from ext_clean (or ext_far while the literals end within bsm) and the offset in the history *)
Lemma xs_ext_read (a: la) (k E' ll ml off: Z) :
  la_ok a -> 0 < a_cap a ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/
   (k + ll <= a_d a + a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  a_d a <= k -> E' <= a_d a + a_cap a -> 0 <= ll -> 0 <= ml ->
  off <= k + ll - a_ps a + ext_len (a_x a) ->
  ext_read_ok (a_x a) k E' ll ml off (a_ps a).
Proof.
  intros Hok Hcap Hcl Hk HE Hll Hml Hoff.
  unfold ext_read_ok. destruct (a_x a) as [|e1 elen|sh eb en ec e1 elen] eqn:Hx; auto.
  simpl in Hoff. unfold ext_clean, ext_far in Hcl. unfold WILDCOPY_OVERLENGTH in *.
  destruct (Z_le_gt_dec off (k + ll - a_ps a)) as [H|H]; [left; exact H|right].
  destruct Hcl as [[Hc|Hc]|[Hb Hc]]; [right; lia|left; lia|left; lia].
Qed.

(* the clean / far premise is monotone in K *)
Lemma xs_cl_mono (a: la) (K K': Z) :
  K <= K' ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K' <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))).
Proof. intros H [H1|[H2 H3]]; [left; exact H1|right; split; [lia|exact H3]]. Qed.

Lemma xs_cl_k (a: la) (K' k ll: Z) :
  k + ll <= a_d a + K' ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K' <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (k + ll <= a_d a + a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))).
Proof. intros H [H1|[H2 H3]]; [left; exact H1|right; split; [lia|exact H3]]. Qed.

(* the prefix [ps, d) is defined when the history is *)
Lemma xs_prefix_def (a: la) (cc: list val) :
  0 <= a_ps a <= a_d a -> 0 <= ext_len (a_x a) -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  Zlength cc = Zlength (oa_c (a_o a)) -> a_d a <= Zlength cc ->
  (forall q, 0 <= q < a_d a -> Znth q cc = Znth q (oa_c (a_o a))) ->
  Forall is_byte_val (sublist (a_ps a) (a_d a) cc).
Proof.
  intros Hps Hel Hhd Hl Hd Hu. rewrite xs_Forall_sub by lia. intros q Hq.
  rewrite Hu by lia. specialize (Hhd (a_d a - q) ltac:(lia)). unfold chist in Hhd.
  rewrite (proj2 (Z.leb_le _ _)) in Hhd by lia. replace (a_d a - (a_d a - q)) with q in Hhd by lia. exact Hhd.
Qed.

(* the extDict is defined when the history is and the array is unchanged outside [d, d + cap) *)
Lemma xs_ext_def_hi (a: la) (cc: list val) (hi: Z) :
  la_ok a -> 0 < a_cap a -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  match a_x a with ExtIn e1 elen => e1 <= a_d a \/ hi <= e1 - elen | _ => True end ->
  Zlength cc = Zlength (oa_c (a_o a)) ->
  unchanged_outside (oa_c (a_o a)) cc (a_d a) hi ->
  ext_def (a_x a) cc.
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & Hnb & Hcap & Hso & Hrep & Hfe & Hc0 & Hlay) Hcap0 Hhd Hcl Hl Hu.
  specialize (Hlay Hcap0). destruct Hlay as (Hps & _ & _ & Hel & Hext).
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc). xs_fold.
  unfold ext_def. destruct (a_x a) as [|e1 elen|sh eb en ec e1 elen] eqn:Hx; auto.
  - destruct Hext as (_ & He1 & He2). simpl in Hel.
    rewrite xs_Forall_sub by lia. intros q Hq.
    rewrite Hu by lia.
    specialize (Hhd (a_d a - a_ps a + (e1 - q))). simpl in Hhd.
    specialize (Hhd ltac:(lia)). unfold chist in Hhd.
    rewrite (proj2 (Z.leb_gt _ _)) in Hhd by lia.
    replace (e1 - (a_d a - a_ps a + (e1 - q) - (a_d a - a_ps a))) with q in Hhd by lia. exact Hhd.
  - destruct Hext as (_ & _ & Hen & He1 & He2). simpl in Hel.
    rewrite xs_Forall_sub by lia. intros q Hq.
    specialize (Hhd (a_d a - a_ps a + (e1 - q))). simpl in Hhd.
    specialize (Hhd ltac:(lia)). unfold chist in Hhd.
    rewrite (proj2 (Z.leb_gt _ _)) in Hhd by lia.
    replace (e1 - (a_d a - a_ps a + (e1 - q) - (a_d a - a_ps a))) with q in Hhd by lia. exact Hhd.
Qed.

(* ... under the clean / far premise, the array unchanged outside [d, min(oend, d + Kb + 32)) *)
Lemma xs_ext_def (a: la) (cc: list val) (Kb: Z) :
  la_ok a -> 0 < a_cap a -> hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (Kb <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  a_E a <= a_d a + a_cap a -> 0 <= Kb ->
  Zlength cc = Zlength (oa_c (a_o a)) ->
  unchanged_outside (oa_c (a_o a)) cc (a_d a) (Z.min (a_E a) (a_d a + Kb + WILDCOPY_OVERLENGTH)) ->
  ext_def (a_x a) cc.
Proof.
  intros Hok Hcap Hhd Hcl HE HKb Hl Hu. unfold WILDCOPY_OVERLENGTH in *.
  destruct Hcl as [Hcl|[Hkb Hfar]].
  - apply (xs_ext_def_hi a cc (a_d a + a_cap a)); auto.
    + unfold ext_clean in Hcl. destruct (a_x a); auto; unfold WILDCOPY_OVERLENGTH in Hcl; lia.
    + intros q Hq Hnq. apply Hu; [exact Hq|]. lia.
  - apply (xs_ext_def_hi a cc (a_d a + Z.min (a_cap a) (a_bsm a + 32))); auto.
    + unfold ext_far in Hfar. destruct (a_x a); auto; unfold WILDCOPY_OVERLENGTH in Hfar; lia.
    + intros q Hq Hnq. apply Hu; [exact Hq|]. lia.
Qed.

(* ===================== the model step ===================== *)

(* under the model, with the content within the capacity: the executed bytes so far, the head's step
   (BlkSeqLoopModel.loop_exec_step), the model at ie + 1; the bytes of the step from any leftover lo already
   in place *)
Lemma xs_m0 (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) (seqs: list sequence)
    (out' lits': list Z) (rep2: Z * Z * Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c (ll, ml, off) -> DM a (x_t x) seqs ->
  EM a seqs out' lits' rep2 -> cnt_len a out' lits' <= a_cap a ->
  exists blk crep' mb,
    Zlength blk = K /\ sublist (a_d a) (a_d a + K) c = zbytes blk /\ lit_intact a j sw c /\
    ll <= a_n a - j /\ K + ll + ml + (a_n a - (j + ll)) <= cnt_len a out' lits' /\
    cnt_len a out' lits' <= a_bsm a /\
    off <= a_d a + K + ll - a_ps a + ext_len (a_x a) /\ Zlength mb = ml /\ rep_ok crep' /\
    K + ll + ml = sum_llml (sublist 0 (ie + 1) seqs) /\ j + ll = sum_ll (sublist 0 (ie + 1) seqs) /\
    rep_chain (a_rep a) (sublist 0 (ie + 1) seqs) = crep' /\
    exec_seqs (hc_wsize (a_h a)) crep' (hc_hist (a_h a)) (sublist (j + ll) (a_n a) (a_lits a))
      (hc_out (a_h a) ++ (blk ++ sublist j (j + ll) (a_lits a) ++ mb)) (sublist (ie + 1) (a_nb a) seqs)
      = Some (out', lits', rep2) /\
    (forall lo cc, 0 <= lo <= ll -> Zlength cc = oa_N (a_o a) ->
       unchanged_outside (oa_c (a_o a)) cc (a_d a) (a_d a + Z.min (a_cap a) (a_bsm a + WILDCOPY_OVERLENGTH)) ->
       sublist (a_d a) (a_d a + K + lo) cc = zbytes (blk ++ sublist j (j + lo) (a_lits a)) ->
       (forall E', E' <= a_d a + a_cap a -> ext_read_ok (a_x a) (a_d a + K + lo) E' (ll - lo) ml off (a_ps a)) /\
       sublist (a_d a + K + lo) (a_d a + K + ll + ml)
         (exec_c cc (a_d a + K + lo) (zbytes (sublist (j + lo) (j + ll) (a_lits a))) ml off (a_ps a) (a_x a)) =
       zbytes (sublist (j + lo) (j + ll) (a_lits a) ++ mb)).
Proof.
  intros Hok Hpend Hfx HXP HDM HEM Hcnt.
  destruct HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (Hm seqs HDM) as (Hlen & Hov & Hll' & Hml' & Hoff' & HK & Hj & Hexm).
  destruct (Hexm out' lits' rep2 HEM Hcnt) as (Hrep & blk & Hblk & Hsub & Hexb & Hli).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  destruct Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof HEM as (Hex & Hcb & Hhv & Hecl).
  rewrite (xs_sub_cons seqs ie (a_nb a)) in Hexb by lia.
  pose proof (xs_exec_len _ _ _ _ _ _ _ _ _ Hexb) as Hlen0.
  rewrite Zlength_app, Zlength_sublist in Hlen0 by (unfold a_n in *; lia).
  unfold cnt_len in Hcnt, Hcb. xs_fold.
  set (crep := rep_chain (a_rep a) (sublist 0 ie seqs)) in *.
  set (lr := sublist j (a_n a) (a_lits a)) in *.
  assert (Hlrb: bytes_ok lr) by (apply Forall_sublist; exact Hlb).
  assert (Hlrl: Zlength lr = a_n a - j) by (unfold lr, a_n in *; rewrite Zlength_sublist; lia).
  assert (Hstep: forall lo cc, 0 <= lo <= ll -> Zlength cc = oa_N (a_o a) ->
       unchanged_outside (oa_c (a_o a)) cc (a_d a) (a_d a + Z.min (a_cap a) (a_bsm a + WILDCOPY_OVERLENGTH)) ->
       sublist (a_d a) (a_d a + Zlength blk + lo) cc = zbytes (blk ++ firstn (Z.to_nat lo) lr) ->
       exists off0 crep' mb,
         c_offset crep ll (sq_ov (Znth ie seqs)) = (off0, crep') /\ rep_ok crep' /\
         ll <= Zlength lr /\
         a_d a + Zlength blk + ll + ml <= a_d a + cnt_len a out' lits' /\
         1 <= off0 <= a_d a + Zlength blk + ll - a_ps a + ext_len (a_x a) /\
         Zlength mb = ml /\ lz_copy (hc_hist (a_h a)) (hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr) off0 (Z.to_nat ml) =
           hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr ++ mb /\
         (a_d a + Zlength blk + ll + ml <= a_d a + a_cap a ->
          (forall E, E <= a_d a + a_cap a -> ext_read_ok (a_x a) (a_d a + Zlength blk + lo) E (ll - lo) ml off0 (a_ps a)) /\
          sublist (a_d a + Zlength blk + lo) (a_d a + Zlength blk + ll + ml)
            (exec_c cc (a_d a + Zlength blk + lo) (zbytes (skipn (Z.to_nat lo) (firstn (Z.to_nat ll) lr))) ml off0 (a_ps a) (a_x a)) =
          zbytes (skipn (Z.to_nat lo) (firstn (Z.to_nat ll) lr) ++ mb)) /\
         exec_seqs (hc_wsize (a_h a)) crep' (hc_hist (a_h a)) (skipn (Z.to_nat ll) lr)
           (hc_out (a_h a) ++ blk ++ firstn (Z.to_nat ll) lr ++ mb) (sublist (ie + 1) (a_nb a) seqs) = Some (out', lits', rep2)).
  { intros lo cc Hlo Hcc Hucc Hscc.
    rewrite Hll', Hml'. unfold cnt_len.
    apply (loop_exec_step_core (oa_c (a_o a)) cc (a_d a) (a_ps a) (a_cap a) (a_bsm a) (a_x a)); try lia;
      try assumption.
    all: first [ rewrite Hcc, Hoc; reflexivity | rewrite Hcc; exact Hib | unfold cnt_len; lia
               | rewrite <- Hll'; exact Hlo | rewrite <- Hml'; lia ]. }
  destruct (Hstep 0 c ltac:(lia) Hc) as (off0 & crep' & mb & Hco & Hrep' & Hllr & Hend & Hoff0 & Hmb & Hlz & Hfit & Hexr).
  { intros q Hq Hnq. apply Hu; [lia|]. intros Hq2. apply Hnq. unfold WILDCOPY_OVERLENGTH in *. lia. }
  { rewrite Z.add_0_r, Hblk. simpl. rewrite app_nil_r. exact Hsub. }
  assert (Hoo: off = off0) by (rewrite Hoff', Hco; reflexivity). subst off0.
  rewrite Hblk in *. unfold lr in *.
  rewrite (xs_firstn_sub (a_lits a) j (a_n a) ll) in * by (unfold a_n in *; lia).
  rewrite (xs_skipn_sub (a_lits a) j (a_n a) ll) in * by (unfold a_n in *; lia).
  pose proof (xs_exec_len _ _ _ _ _ _ _ _ _ Hexr) as Hlen1.
  rewrite !Zlength_app, !Zlength_sublist in Hlen1 by (unfold a_n in *; lia).
  exists blk, crep', mb.
  split; [exact Hblk|]. split; [exact Hsub|]. split; [exact Hli|].
  split; [lia|]. split; [unfold cnt_len; lia|]. split; [unfold cnt_len; lia|].
  split; [lia|]. split; [exact Hmb|]. split; [exact Hrep'|].
  rewrite (xs_sub_snoc seqs ie) by lia.
  rewrite xs_sum_llml_app, xs_sum_ll_app, xs_rep_chain_app, <- HK, <- Hj. cbn [rep_chain].
  rewrite <- Hll'. fold crep. rewrite Hco. cbn [snd].
  split; [simpl; lia|]. split; [simpl; lia|]. split; [reflexivity|]. split; [exact Hexr|].
  intros lo cc Hlo Hcc Hucc Hscc.
  destruct (Hstep lo cc Hlo Hcc Hucc) as (off2 & crep2 & mb2 & Hco2 & _ & _ & _ & _ & Hmb2 & Hlz2 & Hfit2 & _).
  { rewrite (xs_firstn_sub (a_lits a) j (a_n a) lo) by (unfold a_n in *; lia). exact Hscc. }
  rewrite Hco in Hco2. inversion Hco2; subst off2 crep2.
  rewrite Hlz in Hlz2. rewrite !app_assoc in Hlz2. apply app_inv_head in Hlz2. subst mb2.
  rewrite (xs_skipn_sub (a_lits a) j (j + ll) lo) in Hfit2
    by (unfold a_n in *; lia).
  apply Hfit2. unfold cnt_len in Hend. lia.
Qed.

(* ===================== bytes in, bytes out ===================== *)

(* the literal array execSequence reads holds bytes *)
Lemma xs_lit_bytes (a: la) (x: lfx) (c: list val) :
  lfx_ok a x -> byte_cells (iw_c (a_i a)) -> byte_cells c -> byte_cells (lit_arr (fin_ls a x) c).
Proof.
  intros (_ & _ & _ & _ & (_ & Hxb & _)) Hi Hc. unfold fin_ls. destruct (a_l a); simpl; auto.
Qed.

(* a copy of bytes into a byte array *)
Lemma xs_bytes_patch (c c1: list val) (lo hi: Z) :
  byte_cells c -> Zlength c1 = Zlength c -> unchanged_outside c c1 lo hi -> 0 <= lo <= hi -> hi <= Zlength c ->
  Forall is_byte_val (sublist lo hi c1) -> byte_cells c1.
Proof.
  intros Hc Hl Hu Hlh Hh Hs. unfold byte_cells.
  apply VST.zlist.list_solver.Forall_Znth. intros q Hq.
  destruct (Z_lt_le_dec q lo) as [H1|H1]; [|destruct (Z_lt_le_dec q hi) as [H2|H2]].
  - rewrite Hu by lia. unfold byte_cells in Hc. rewrite VST.zlist.list_solver.Forall_Znth in Hc. apply Hc. lia.
  - rewrite xs_Forall_sub in Hs by lia. apply Hs. lia.
  - rewrite Hu by lia. unfold byte_cells in Hc. rewrite VST.zlist.list_solver.Forall_Znth in Hc. apply Hc. lia.
Qed.

Lemma xs_bytes_sub (c: list val) (lo hi: Z) : byte_cells c -> Forall is_byte_val (sublist lo hi c).
Proof. intros H. apply Forall_sublist. exact H. Qed.

(* ===================== the error return ===================== *)

Lemma xs_err (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c c': list val) (e0: Z * Z * Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c e0 ->
  Zlength c' = Zlength c -> unchanged_outside c c' (a_d a) (a_d a + a_cap a) ->
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells c') ->
  (forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
     cnt_len a out' lits' <= a_cap a -> False) ->
  FXERR a c'.
Proof.
  intros Hok Hpend Hfx HXP Hl' Hu' Hb' Hno.
  assert (Hie: 0 <= ie < a_nb a) by (destruct e0 as [[? ?] ?]; apply HXP).
  assert (Hsafe: ex_safe a K j sw c) by (destruct e0 as [[? ?] ?]; apply HXP).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  destruct Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  unfold FXERR. xs_fold. split.
  { intros q Hq Hnq. rewrite Hu' by lia. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH. lia. }
  split; [|exact Hb'].
  intros [Hc0|(Hhv & Hecl)]; [lia|].
  unfold seqs_model. rewrite Hos.
  replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  destruct (x_t x) as [[tLL tOF] tML] eqn:Ht.
  destruct (decode_seq_stream tLL tOF tML (iw_s (a_i a)) (a_nb a)) as [seqs|] eqn:Hds; [|exact I].
  destruct (exec_seqs (hc_wsize (a_h a)) (a_rep a) (hc_hist (a_h a)) (a_lits a) (hc_out (a_h a)) seqs)
    as [[[out' lits'] rep2]|] eqn:Hex; [|exact I].
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ Hex) as [mid Hmid].
  assert (Hlen: Zlength (skipn (length (hc_out (a_h a))) (out' ++ lits')) = cnt_len a out' lits').
  { unfold cnt_len. rewrite Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl.
    rewrite !Zlength_app. lia. }
  rewrite Hlen. intros Hcb.
  destruct (Z_lt_le_dec (a_cap a) (cnt_len a out' lits')) as [H|H]; [exact H|].
  exfalso. apply (Hno seqs out' lits' rep2).
  - unfold DM. exact Hds.
  - unfold EM. xs_fold. refine (conj Hex (conj Hcb (conj Hhv Hecl))).
  - exact H.
Qed.

(* ===================== literal and capacity facts ===================== *)

Lemma xs_sub_in {A} {IA: Inhabitant A} (l L: list A) (lo hi p q: Z) :
  sublist lo hi l = L -> 0 <= lo -> hi <= Zlength l -> lo <= p -> p <= q -> q <= hi ->
  sublist p q l = sublist (p - lo) (q - lo) L.
Proof. intros H H1 H2 H3 H4 H5. rewrite <- H. rewrite sublist_sublist by lia. f_equal; lia. Qed.

Lemma xs_lim_N (a: la) (sw: bool) (j: Z) :
  fnosplit a sw -> lit_lim a sw - lit_li a sw j = a_n a - j.
Proof. unfold fnosplit, lit_lim, lit_li. destruct (a_l a); intros; try subst sw; lia. Qed.

(* the literals execSequence reads (not the split head) *)
Lemma xs_lits_N (a: la) (x: lfx) (K j: Z) (sw: bool) (c: list val) (ll: Z) :
  la_ok a -> lfx_ok a x -> ex_safe a K j sw c -> fnosplit a sw -> 0 <= ll -> j + ll <= a_n a ->
  sublist (lit_li a sw j) (lit_li a sw j + ll) (lit_arr (fin_ls a x) c) = zbytes (sublist j (j + ll) (a_lits a)).
Proof.
  intros (Ho & Hi & Hla & Hbsm & Hn & _) (_ & _ & _ & _ & Hxc) (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0) Hns Hll Hjl.
  destruct Ho as (_ & Hoc & HoN & Hod & Hocap & Hodc).
  destruct Hla as (Hlb & Hln & Hl). destruct Hxc as (Hxl & Hxbc & Hxc).
  unfold lit_li, fin_ls, lit_arr, fnosplit, a_E, a_n, a_d, a_cap in *.
  destruct (a_l a) as [off| |lb|lb] eqn:Hloc.
  - destruct Hl as (Hoff & HoffN & Hs & _). destruct Hi as (_ & _ & _ & _ & HiN & _).
    rewrite (xs_sub_in _ _ _ _ _ _ Hs) by (unfold WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - destruct Hl as (Hlb0 & HlbE & Hs).
    rewrite (xs_sublist_ext (oa_c (a_o a)) c) by (unfold WILDCOPY_OVERLENGTH in *; first [lia | intros q Hq; apply Hu; lia]).
    rewrite (xs_sub_in _ _ _ _ _ _ Hs) by (unfold WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. f_equal; f_equal; lia.
  - subst sw. destruct Hl as (Hbig & Hlb0 & HlbE & Hs).
    rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    rewrite sublist_map. rewrite sublist_sublist by (unfold a_n in *; lia). f_equal; f_equal; lia.
Qed.

(* oend is beyond the content within min(cap, bsm) *)
Lemma xs_E_big (a: la) : la_pend a -> a_d a + Z.min (a_cap a) (a_bsm a) <= a_E a.
Proof. intros (_ & Hp). unfold a_E. destruct (a_l a); lia. Qed.

(* the positions of the model after the head *)
Lemma xs_sums (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) (seqs: list sequence) :
  FXP a x ie K j sw c (ll, ml, off) -> DM a (x_t x) seqs ->
  K + (ll + ml) = sum_llml (sublist 0 (ie + 1) seqs) /\ j + ll = sum_ll (sublist 0 (ie + 1) seqs).
Proof.
  intros (Hie & _ & _ & _ & _ & _ & Hm) HDM.
  destruct (Hm seqs HDM) as (Hlen & _ & Hll' & Hml' & _ & HK & Hj & _).
  rewrite (xs_sub_snoc seqs ie) by lia. rewrite xs_sum_llml_app, xs_sum_ll_app, <- HK, <- Hj.
  simpl. lia.
Qed.

(* ===================== (N) execSequence, literals not the split head ===================== *)

Lemma xs_case_N (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (fnosplit a sw ->
   let li := lit_li a sw j in let lim := lit_lim a sw in let ls := fin_ls a x in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> byte_cells (lit_arr ls c) -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_err k E li lim ll ml off ps elen = true -> unchanged_outside c c' k E -> FXERR a c') /\
   (exec_err k E li lim ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       sublist k (k + (ll + ml)) c' =
         sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) (lit_arr ls c)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) (lit_arr ls c)) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen Hns li lim ls c' Hl' Hbyc' Hxu.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  assert (Hlim: lim - li = a_n a - j) by apply xs_lim_N, Hns.
  pose proof (xs_E_big a Hpend) as HEb.
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j sw c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. apply Hu'; [lia|]. unfold k, E in *. lia.
    + intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | apply xs_lit_bytes; auto; apply Hbc0; auto | exact Hb3].
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j sw c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
      unfold k, E, ps, elen in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_err in Hnerr. rewrite !orb_false_iff, !Z.ltb_ge in Hnerr.
    destruct Hnerr as ((H1 & H2) & H3).
    assert (Hlits: sublist li (li + ll) (lit_arr ls c) = zbytes (sublist j (j + ll) (a_lits a)))
      by (apply xs_lits_N with (K := K); auto; lia).
    assert (Hu0: unchanged_outside (oa_c (a_o a)) c (a_d a) (a_d a + a_cap a)).
    { intros q Hq Hnq. apply Hu; [lia|]. lia. }
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. unfold k. lia. }
    split; [|split].
    + unfold ex_safe. split; [lia|]. split; [unfold k, E in *; lia|]. split; [lia|].
      split; [revert Hsw Hns; clear - Hll; unfold fnosplit; destruct (a_l a); auto; intros; subst; lia|].
      split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k, E in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | apply xs_lit_bytes; auto; apply Hbc0; auto | exact Hb3].
    + apply (ex_def_step a K (ll + ml) j (j + ll) sw sw c c'); unfold k, E in *; auto; try lia.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j sw c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      destruct (xs_m0 a x ie K j sw c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (Hstep 0 c) as (Hro0 & Hb0).
      { lia. }
      { exact Hc. }
      { intros q Hq Hnq. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite !Z.add_0_r, sublist_nil, app_nil_r. exact Hsub. }
      rewrite !Z.add_0_r, !Z.sub_0_r in Hro0. rewrite !Z.add_0_r in Hb0.
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        replace (a_d a + (K + (ll + ml))) with (k + (ll + ml)) by (unfold k; lia).
        change (a_d a + K) with k. rewrite (proj1 (Hby (Hro0 E ltac:(unfold E; lia)))). rewrite Hlits.
        replace (k + (ll + ml)) with (a_d a + K + ll + ml) by (unfold k; lia). exact Hb0.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. revert Hns. unfold fnosplit. destruct (a_l a); auto. intros -> ?. discriminate.
Qed.

(* ===================== (S) execSequenceSplitLitBuffer ===================== *)

(* the split literals still in place, cut at j + t *)
Lemma xs_split_lits (a: la) (lb j t: Z) (c: list val) :
  a_l a = LSplit lb -> lit_intact a j false c -> 0 <= lb -> 0 <= j -> 0 <= t ->
  j + t <= a_n a - LITBUFFEREXTRASIZE -> lb + (a_n a - LITBUFFEREXTRASIZE) <= Zlength c ->
  sublist (lb + j) (lb + j + t) c = zbytes (sublist j (j + t) (a_lits a)) /\
  sublist (lb + j + t) (lb + (a_n a - LITBUFFEREXTRASIZE)) c =
    zbytes (sublist (j + t) (a_n a - LITBUFFEREXTRASIZE) (a_lits a)).
Proof.
  intros Hl Hli Hlb Hj Ht Hjt Hc. unfold lit_intact in Hli. rewrite Hl in Hli. specialize (Hli eq_refl).
  assert (Hn: a_n a = Zlength (a_lits a)) by reflexivity.
  split.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hli) by lia. rewrite sublist_map, sublist_sublist by lia.
    f_equal; f_equal; lia.
  - rewrite (xs_sub_in _ _ _ _ _ _ Hli) by lia. rewrite sublist_map, sublist_sublist by lia.
    f_equal; f_equal; lia.
Qed.

Lemma xs_case_S (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_li a false j + ll <= lit_lim a false ->
   let li := lit_li a false j in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c -> ext_bytes xs -> byte_cells c') -> xd_ub c c' ->
   (exec_split_err k E li ll ml off ps elen = true -> unchanged_outside c c' k E -> FXERR a c') /\
   (exec_split_err k E li ll ml off ps elen = false ->
    unchanged_outside c c' k (Z.min (Z.min E (k + (ll + ml) + WILDCOPY_OVERLENGTH)) (Z.max (k + (ll + ml)) (li + ll))) ->
    Forall is_byte_val (sublist k (k + (ll + ml)) c') ->
    (ext_read_ok xs k E ll ml off ps ->
       (lit_exact_split k li ll ->
          sublist k (k + (ll + ml)) c' = sublist k (k + (ll + ml)) (exec_c c k (sublist li (li + ll) c) ml off ps xs)) /\
       (Forall is_byte_val (sublist ps k c) -> Forall is_byte_val (sublist li (li + ll) c) ->
        ext_def xs c -> Forall is_byte_val (sublist k (k + (ll + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) false c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen lb Hl Hsw0 Hlil li c' Hl' Hbyc' Hxu. subst sw.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof Hok as (_ & _ & (_ & _ & Hla) & _). rewrite Hl in Hla.
  destruct Hla as (Hbig & Hlb0 & HlbE & Hlbs).
  pose proof Hpend as (_ & Hpl). rewrite Hl in Hpl, Hsw.
  assert (HEe: E = a_d a + a_cap a) by (unfold E, a_E; rewrite Hl; reflexivity).
  assert (HEa: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite Hl; reflexivity).
  rewrite HEa in *.
  assert (Hlie: li = lb + j) by (unfold li, lit_li; rewrite Hl; reflexivity).
  clearbody E li. subst E li.
  unfold lit_li, lit_lim in Hlil. rewrite Hl in Hlil.
  xs_fold. unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *.
  (* under the model: the literals are far ahead of op *)
  assert (Hfar: forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
            cnt_len a out' lits' <= a_cap a -> k + ml + 32 <= lb + j).
  { intros seqs out' lits' rep2 HDM HEM Hcnt.
    destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
      as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
    unfold k. lia. }
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j false c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. apply Hu'; [lia|]. unfold k in *. lia.
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_split_err in Herr. rewrite !orb_true_iff, !andb_true_iff, !Z.ltb_lt in Herr.
      unfold k, ps, elen in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_split_err in Hnerr.
    rewrite !orb_false_iff, !Z.ltb_ge in Hnerr. destruct Hnerr as ((H1 & H2) & H3).
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. unfold k. lia. }
    split; [|split].
    + unfold ex_safe. rewrite Hl, HEa. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *. split; [lia|]. split; [unfold k in *; lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hbc0; auto | exact Hb3].
    + apply (ex_def_step a K (ll + ml) j (j + ll) false false c c'); unfold k in *; auto; try lia.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j false c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (Hstep 0 c) as (Hro0 & Hb0).
      { lia. }
      { exact Hc. }
      { intros q Hq Hnq. apply Hu; [lia|]. unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite !Z.add_0_r, sublist_nil, app_nil_r. exact Hsub. }
      rewrite !Z.add_0_r, !Z.sub_0_r in Hro0. rewrite !Z.add_0_r in Hb0.
      destruct (xs_split_lits a lb j ll c Hl Hli ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold LITBUFFEREXTRASIZE; lia) ltac:(unfold LITBUFFEREXTRASIZE; lia)) as (HL1 & HL2).
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        replace (a_d a + (K + (ll + ml))) with (k + (ll + ml)) by (unfold k; lia).
        change (a_d a + K) with k.
        rewrite (proj1 (Hby (Hro0 (a_d a + a_cap a) ltac:(lia)))) by (unfold lit_exact_split; right; right; lia).
        rewrite HL1.
        replace (k + (ll + ml)) with (a_d a + K + ll + ml) by (unfold k; lia). exact Hb0.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. rewrite Hl. intros _. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
        rewrite <- HL2. replace (lb + (j + ll)) with (lb + j + ll) by lia.
        apply xs_sublist_ext; try lia. intros q Hq. apply Hu'; [lia|]. lia.
Qed.

(* ===================== (X1) leftover, switch, execSequence on litExtraBuffer ===================== *)

(* litExtraBuffer holds the last 65536 literals *)
Lemma xs_xc_lits (a: la) (x: lfx) (lb s t: Z) :
  la_ok a -> lfx_ok a x -> a_l a = LSplit lb -> 0 <= s -> 0 <= t -> s + t <= LITBUFFEREXTRASIZE ->
  sublist s (s + t) (x_xc x) =
    zbytes (sublist (a_n a - LITBUFFEREXTRASIZE + s) (a_n a - LITBUFFEREXTRASIZE + s + t) (a_lits a)).
Proof.
  intros (_ & _ & (_ & _ & Hla) & _) (_ & _ & _ & _ & (Hxl & _ & Hxc)) Hl Hs Ht Hst.
  rewrite Hl in Hla, Hxc. destruct Hla as (Hbig & _).
  assert (Hn: a_n a = Zlength (a_lits a)) by reflexivity.
  rewrite (xs_sub_in _ _ _ _ _ _ Hxc) by (unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  rewrite sublist_map, sublist_sublist by lia. f_equal; f_equal; lia.
Qed.

Lemma xs_case_X1 (a: la) (x: lfx) (ie K j: Z) (sw: bool) (c: list val) (ll ml off: Z) :
  la_ok a -> la_pend a -> lfx_ok a x -> FXP a x ie K j sw c (ll, ml, off) ->
  let k := a_d a + K in let E := a_E a in let ps := a_ps a in let xs := a_x a in let elen := ext_len (a_x a) in
  (forall lb, a_l a = LSplit lb -> sw = false -> lit_lim a false - lit_li a false j < ll ->
   let li := lit_li a false j in let lo := lit_lim a false - li in
   (0 < lo -> E - k < lo -> FXERR a c) /\
   forall c1, (lo = 0 -> c1 = c) -> (0 < lo -> lo <= E - k /\ fcopied c c1 k li lo) ->
   let k1 := k + lo in let ls := fin_ls a x in let li1 := lit_li a true (j + lo) in let lim1 := lit_lim a true in
   forall c', Zlength c' = Zlength c ->
   (byte_cells c1 -> byte_cells (lit_arr ls c1) -> ext_bytes xs -> byte_cells c') -> xd_ub c1 c' ->
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = true -> unchanged_outside c1 c' k1 E -> FXERR a c') /\
   (exec_err k1 E li1 lim1 (ll - lo) ml off ps elen = false ->
    unchanged_outside c1 c' k1 (Z.min E (k1 + (ll - lo + ml) + WILDCOPY_OVERLENGTH)) ->
    Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c') ->
    (ext_read_ok xs k1 E (ll - lo) ml off ps ->
       sublist k1 (k1 + (ll - lo + ml)) c' =
         sublist k1 (k1 + (ll - lo + ml)) (exec_c c1 k1 (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ml off ps xs) /\
       (Forall is_byte_val (sublist ps k1 c1) -> Forall is_byte_val (sublist li1 (li1 + (ll - lo)) (lit_arr ls c1)) ->
        ext_def xs c1 -> Forall is_byte_val (sublist k1 (k1 + (ll - lo + ml)) c'))) ->
    FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c')).
Proof.
  intros Hok Hpend Hfx HXP k E ps xs elen lb Hl Hsw0 Hlil li lo. subst sw.
  pose proof HXP as (Hie & Hsafe & Hdef & Hll & Hml & Hoff & Hm).
  destruct (xs_basic a x Hok Hpend Hfx ltac:(lia))
    as (Hoc & HoN & Hod & Hcap & Hodc & Hps & Hel & Hib & Hlb & Hn & Hbsm & Hrep0 & HE & Hos).
  pose proof Hsafe as (HK0 & HKE & Hj0 & Hsw & Hc & Hu & Hbc0).
  pose proof Hok as (_ & _ & (_ & _ & Hla) & _). rewrite Hl in Hla.
  destruct Hla as (Hbig & Hlb0 & HlbE & Hlbs).
  pose proof Hpend as (_ & Hpl). rewrite Hl in Hpl, Hsw.
  assert (HEe: E = a_d a + a_cap a) by (unfold E, a_E; rewrite Hl; reflexivity).
  assert (HEa: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite Hl; reflexivity).
  rewrite HEa in *.
  assert (Hlie: li = lb + j) by (unfold li, lit_li; rewrite Hl; reflexivity).
  assert (Hloe: lo = a_n a - LITBUFFEREXTRASIZE - j) by (unfold lo, lit_lim; rewrite Hl, Hlie; lia).
  clearbody E li lo. subst E li.
  unfold lit_li, lit_lim in Hlil. rewrite Hl in Hlil.
  xs_fold. unfold WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *.
  assert (Hlo0: 0 <= lo < ll) by lia.
  split.
  { intros Hlo Hbad. apply (xs_err a x ie K j false c c (ll, ml, off)); auto.
    - intros q Hq Hnq. reflexivity.
    - intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
      unfold k in *. lia. }
  intros c1 Hc1z Hc1p c' Hl' Hbyc' Hxu.
  assert (Hli1: lit_li a true (j + lo) = 0) by (unfold lit_li; rewrite Hl; unfold LITBUFFEREXTRASIZE; lia).
  assert (Hlim1: lit_lim a true = LITBUFFEREXTRASIZE) by (unfold lit_lim; rewrite Hl; reflexivity).
  assert (Hls: lit_arr (fin_ls a x) c1 = x_xc x) by (unfold fin_ls; rewrite Hl; reflexivity).
  rewrite Hli1, Hlim1, Hls. set (k1 := k + lo) in *.
  (* the leftover copy *)
  assert (Hc1: Zlength c1 = Zlength c /\ k + lo <= a_d a + a_cap a /\
               unchanged_outside c c1 k (k + lo) /\
               (Forall is_byte_val (sublist (lb + j) (lb + j + lo) c) -> Forall is_byte_val (sublist k (k + lo) c1)) /\
               (k + 32 <= lb + j -> sublist k (k + lo) c1 = sublist (lb + j) (lb + j + lo) c) /\
               (byte_cells c -> byte_cells c1)).
  { destruct (Z.eq_dec lo 0) as [H0|H0].
    - rewrite (Hc1z H0). rewrite H0, Z.add_0_r, !sublist_nil. unfold k.
      repeat split; auto; try lia. intros _. rewrite Z.add_0_r, sublist_nil. reflexivity.
    - destruct (Hc1p ltac:(lia)) as (Hloe' & Hcl & Hcd & Hcb & Hcu).
      split; [exact Hcl|]. split; [lia|]. split; [exact Hcu|]. split; [exact Hcb|].
      split.
      + intros Hfar. rewrite Hcd by (unfold WILDCOPY_VECLEN, WILDCOPY_OVERLENGTH; lia).
        apply xs_listcopy_ahead_sub; unfold k in *; lia.
      + intros Hb. apply (xs_bytes_patch c c1 k (k + lo)); auto; unfold k in *; try lia.
        apply Hcb, xs_bytes_sub, Hb. }
  destruct Hc1 as (Hc1l & Hk1E & Hc1u & Hc1b & Hc1e & Hc1y).
  assert (Hxcb: byte_cells (x_xc x)) by (destruct Hfx as (_ & _ & _ & _ & (_ & Hxb & _)); exact Hxb).
  assert (Hc1o: unchanged_outside (oa_c (a_o a)) c1 (a_d a) (a_d a + a_cap a)).
  { intros q Hq Hnq. rewrite Hc1u by (unfold k in *; lia). apply Hu; lia. }
  (* under the model: the literals are far ahead of op *)
  assert (Hfar: forall seqs out' lits' rep2, DM a (x_t x) seqs -> EM a seqs out' lits' rep2 ->
            cnt_len a out' lits' <= a_cap a -> k + ml + 32 <= lb + j).
  { intros seqs out' lits' rep2 HDM HEM Hcnt.
    destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
      as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & _).
    unfold k. lia. }
  split.
  - intros Herr Hu'. apply (xs_err a x ie K j false c c' (ll, ml, off)); auto.
    + intros q Hq Hnq. rewrite Hu' by (unfold k1, k in *; lia). apply Hc1u; unfold k in *; lia.
    + intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hc1y, Hbc0; auto | rewrite Hls; exact Hxcb | exact Hb3].
    + intros seqs out' lits' rep2 HDM HEM Hcnt.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & _).
      unfold exec_err in Herr. rewrite !orb_true_iff, !Z.ltb_lt in Herr.
      unfold k1, k, ps, elen, LITBUFFEREXTRASIZE in *. lia.
  - intros Hnerr Hu' Hxf Hby. unfold exec_err in Hnerr. rewrite !orb_false_iff, !Z.ltb_ge in Hnerr.
    destruct Hnerr as ((H1 & H2) & H3). unfold LITBUFFEREXTRASIZE in H2.
    assert (Hc'd: sublist (a_d a) (a_d a + K) c' = sublist (a_d a) (a_d a + K) c).
    { apply xs_sublist_ext; try lia. intros q Hq.
      rewrite Hu' by (unfold k1, k in *; lia). apply Hc1u; unfold k in *; lia. }
    assert (Hc'k: sublist k k1 c' = sublist k (k + lo) c1).
    { unfold k1. apply xs_sublist_ext; unfold k in *; try lia. intros q Hq. apply Hu'; lia. }
    split; [|split].
    + unfold ex_safe. rewrite Hl, HEa. unfold LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *.
      split; [lia|]. split; [unfold k1, k in *; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros q Hq Hnq; rewrite Hu' by (unfold k1, k in *; lia);
              rewrite Hc1u by (unfold k in *; lia); apply Hu; [lia|]; lia|].
      intros Hb1 Hb2 Hb3. apply Hbyc'; [apply Hc1y, Hbc0; auto | rewrite Hls; exact Hxcb | exact Hb3].
    + assert (Hsrc: Forall is_byte_val (sublist (lb + j) (lb + j + lo) c)).
      { pose proof (ex_def_lits a (x_xc x) K j false c Hok ltac:(destruct Hfx as (_ & _ & _ & _ & Hxc); exact Hxc)
                      Hcap ltac:(unfold a_n in *; lia) Hc Hdef) as Hs.
        rewrite Hl in Hs. destruct Hs as (Hs1 & _).
        specialize (Hs1 ltac:(unfold a_n, LITBUFFEREXTRASIZE in *; lia)).
        apply (xd_sub _ (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH)); auto;
          unfold a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia. }
      assert (Hc1d: ex_def a (K + lo) j false c1).
      { destruct (Z.eq_dec lo 0) as [H0|H0].
        - rewrite (Hc1z H0), H0, Z.add_0_r. exact Hdef.
        - apply (ex_def_step a K lo j j false false c c1); unfold k in *; auto; try lia;
            first [ apply (xd_ub_frame c c1 (a_d a + K) (a_d a + K + lo));
                      [exact Hc1u | apply xd_Forall_rng; [lia | lia | apply Hc1b; exact Hsrc]]
                  | apply Hc1b; exact Hsrc ]. }
      replace (K + (ll + ml)) with (K + lo + (ll - lo + ml)) by lia.
      apply (ex_def_step a (K + lo) (ll - lo + ml) j (j + ll) false true c1 c'); unfold k1, k in *; auto; try lia.
      all: replace (a_d a + (K + lo)) with (a_d a + K + lo) by lia; exact Hxf.
    + intros seqs HDM.
      destruct (xs_sums a x ie K j false c ll ml off seqs HXP HDM) as (Hs1 & Hs2).
      unfold ex_model. split; [exact Hs1|]. split; [exact Hs2|].
      intros out' lits' rep2 HEM Hcnt.
      pose proof (Hfar seqs out' lits' rep2 HDM HEM Hcnt) as Hf.
      destruct (xs_m0 a x ie K j false c ll ml off seqs out' lits' rep2 Hok Hpend Hfx HXP HDM HEM Hcnt)
        as (blk & crep' & mb & Hblk & Hsub & Hli & Hlln & Hcntb & Hcb & Hoffb & Hmb & Hrep' & _ & _ & Hrc &
            Hexr & Hstep).
      split; [rewrite Hrc; exact Hrep'|].
      destruct (xs_split_lits a lb j lo c Hl Hli ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold LITBUFFEREXTRASIZE; lia) ltac:(unfold LITBUFFEREXTRASIZE; lia)) as (HL1 & _).
      assert (Hlo1: sublist k (k + lo) c1 = zbytes (sublist j (j + lo) (a_lits a)))
        by (rewrite Hc1e by lia; exact HL1).
      destruct (Hstep lo c1) as (Hro1 & Hb1).
      { lia. }
      { lia. }
      { intros q Hq Hnq. unfold WILDCOPY_OVERLENGTH in *. rewrite Hc1u by (unfold k in *; lia). apply Hu; [lia|].
        unfold WILDCOPY_OVERLENGTH in *. lia. }
      { rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + K + lo)) by lia.
        rewrite map_app. f_equal; [|exact Hlo1].
        rewrite (xs_sublist_ext c c1) by (try lia; intros q Hq; apply Hc1u; unfold k; lia). exact Hsub. }
      exists (blk ++ sublist j (j + ll) (a_lits a) ++ mb).
      split; [rewrite !Zlength_app, Zlength_sublist by (unfold a_n in *; lia); lia|].
      split.
      * rewrite (sublist_split (a_d a) (a_d a + K) (a_d a + (K + (ll + ml)))) by lia.
        rewrite map_app. f_equal; [rewrite Hc'd; exact Hsub|].
        change (a_d a + K) with k.
        rewrite (sublist_split k k1 (a_d a + (K + (ll + ml)))) by (unfold k1, k in *; lia).
        rewrite (sublist_split j (j + lo) (j + ll)) by (unfold a_n in *; lia).
        rewrite <- app_assoc, !map_app. f_equal; [rewrite Hc'k; exact Hlo1|].
        replace (a_d a + (K + (ll + ml))) with (k1 + (ll - lo + ml)) by (unfold k1, k; lia).
        rewrite (proj1 (Hby (Hro1 (a_d a + a_cap a) ltac:(lia)))).
        rewrite (xs_xc_lits a x lb 0 (ll - lo)) by (auto; unfold LITBUFFEREXTRASIZE; lia).
        replace (a_n a - LITBUFFEREXTRASIZE + 0) with (j + lo) by (unfold LITBUFFEREXTRASIZE; lia).
        replace (j + lo + (ll - lo)) with (j + ll) by lia.
        replace (k1 + (ll - lo + ml)) with (a_d a + K + ll + ml) by (unfold k1, k; lia). rewrite <- map_app. exact Hb1.
      * split; [rewrite Hrc; exact Hexr|].
        unfold lit_intact. rewrite Hl. intros; discriminate.
Qed.

Lemma fin_xstep_ok : FXSTEP.
Proof.
  unfold FXSTEP. intros a x ie K j sw c ll ml off Hok Hpend Hfx HXP.
  pose proof (xs_case_N a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HN.
  pose proof (xs_case_S a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HS.
  pose proof (xs_case_X1 a x ie K j sw c ll ml off Hok Hpend Hfx HXP) as HX.
  cbv zeta in HN, HS, HX |- *. exact (conj HN (conj HS HX)).
Qed.




(* (p + A) - (p + B) *)
Lemma lgf_sub (b: val) (A B: Z) :
  isptr b -> 0 <= B <= A -> A <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val A b) (offset_val B b)) =
  Vlong (Int64.repr (A - B)).
Proof.
  intros Hb HAB HA. destruct b; try contradiction.
  simpl. unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr A)) (Ptrofs.add i (Ptrofs.repr B)) = Ptrofs.repr (A - B)).
  { rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted. apply ptrofs_sub_repr. }
  rewrite E. rewrite Ptrofs.divs_one by (compute; congruence).
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* leftoverLit > (size_t)(oend - op) *)
Lemma lgf_gt (b: val) (E k lo: Z) :
  isptr b -> 0 <= k <= E -> E <= Ptrofs.max_unsigned -> 0 <= lo <= Int64.max_unsigned ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1)))
      sem_cast_pointer sem_cast_pointer (Vlong (Int64.repr lo))
      (force_val (sem_sub_pp tuchar (offset_val E b) (offset_val k b))) with
  | Some v' => v' | None => Vundef end = Val.of_bool (E - k <? lo).
Proof.
  intros Hb HkE HE Hlo. destruct b; try contradiction.
  unfold sem_sub_pp. simpl. rewrite peq_true. simpl.
  assert (Q: Ptrofs.sub (Ptrofs.add i (Ptrofs.repr E)) (Ptrofs.add i (Ptrofs.repr k)) = Ptrofs.repr (E - k)).
  { rewrite !(Ptrofs.add_commut i). rewrite Ptrofs.sub_shifted. apply ptrofs_sub_repr. }
  rewrite Q. rewrite Ptrofs.divs_one by (compute; congruence).
  unfold Vptrofs. simpl. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (E - k) lo), (E - k <? lo) eqn:W; simpl; auto;
    try (apply Z.ltb_lt in W; lia); try (apply Z.ltb_ge in W; lia).
Qed.

Lemma lgf_sub64 (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. intros. unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

(* litExtraBuffer + 65536 *)
Lemma lgf_extra_end (p: val) :
  isptr p ->
  force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
    (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer p) (Vint (Int.repr 65536))) =
  offset_val 65536 (offset_val 30380 p).
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
Qed.

(* do { body } while (0) *)
Lemma lgf_do0 {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P: environ -> mpred) (body: statement)
    (R: ret_assert) :
  semax Delta P body (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop body Sbreak) R.
Proof.
  intros H. apply semax_loop with (RA_normal R); [exact H|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

(* the literal fields back together (the split head) *)
Lemma fin_lit_fold (a: la) (lb: Z) (xc: list val) (sw: bool) (vl: val) :
  a_l a = LSplit lb -> vl = Vint (Int.repr (lit_code a sw)) ->
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (a_n a))) (a_p a) *
  field_at Ews t_dctx (DOT _litPtr) (offset_val lb (a_ob a)) (a_p a) *
  field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a)) (a_p a) *
  field_at Ews t_dctx (DOT _litBuffer) (offset_val lb (a_ob a)) (a_p a) *
  field_at Ews t_dctx (DOT _litBufferLocation) vl (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) |-- lit_now a xc sw.
Proof.
  intros El ->. unfold lit_now. rewrite (lit_fix_split a lb El). cancel.
Qed.

(* the facts of exec_spec's precondition (the array, the history pointers) *)
Lemma lgf_exec_pre (a: la) (K: Z) (c: list val) :
  la_ok a -> 0 < a_nb a -> 0 <= K -> a_d a + K <= a_E a -> Zlength c = oa_N (a_o a) ->
  Zlength c <= 2 ^ 63 - 1 /\ 0 <= a_ps a <= a_d a + K /\ a_E a <= Zlength c /\
  exec_ext_ok (a_x a) c /\
  fs_prefixStart (a_fs a) = offset_val (a_ps a) (a_ob a) /\
  fs_virtualStart (a_fs a) = offset_val (a_ps a - ext_len (a_x a)) (a_ob a) /\
  dict_end (a_x a) (a_ob a) (fs_dictEnd (a_fs a)) = fs_dictEnd (a_fs a).
Proof.
  intros Hla Hnb HK HKE Hcl.
  pose proof (lgf_E_le a Hla) as HE.
  destruct Hla as ((Hosh & HoN & HoN32 & Hod & Hocap & HodN) & Hiw & Hlits & Hbsm & Hnbsm & Hnbr & Hnb0 &
                   Hso & Hrep & Hfe & Hc0 & Hlay).
  destruct (Hnb0 ltac:(lia)) as [_ Hcap].
  destruct (Hlay Hcap) as (Hps & Hfps & Hfvs & Hel & Hext).
  unfold a_d, a_cap, a_ps, a_x, a_ob in *.
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold exec_ext_ok. split; [lia|]. destruct (hc_ext (a_h a)); simpl in *; try tauto; lia. }
  split; [exact Hfps|]. split; [exact Hfvs|].
  destruct (hc_ext (a_h a)); simpl in *; try reflexivity; symmetry; tauto.
Qed.

(* &sequences[seqNb & 7] *)
Lemma fin_slot_addr (v: val) (ie: Z) :
  isptr v -> 0 <= ie <= Int.max_signed ->
  force_val (sem_binary_operation' Oadd (tarray t_seq 8) tint v
    (eval_binop Oand tint tint (Vint (Int.repr ie)) (eval_binop Osub tint tint (Vint (Int.repr 8)) (Vint (Int.repr 1)))))
  = offset_val (24 * (ie mod 8)) v.
Proof.
  intros Hv Hie. destruct v; try contradiction.
  simpl. unfold sem_add_ptr_int. simpl.
  assert (E: Int.and (Int.repr ie) (Int.sub (Int.repr 8) (Int.repr 1)) = Int.repr (ie mod 8)).
  { unfold Int.and. change (Int.sub (Int.repr 8) (Int.repr 1)) with (Int.repr 7).
    rewrite !Int.unsigned_repr by rep_lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. unfold Ptrofs.of_ints. pose proof (Z.mod_pos_bound ie 8 ltac:(lia)).
  rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

(* the literals left before litLimit are at most the block's literals: litLimit - litPtr does not wrap as a
   ptrdiff_t (exec_spec's precondition) *)
Lemma lgf_lit_span (a: la) (sw: bool) (j: Z) :
  la_ok a -> 0 <= j -> lit_lim a sw - lit_li a sw j <= Int64.max_signed.
Proof.
  intros (_ & _ & (_ & Hn & _) & _) Hj.
  assert (lit_lim a sw - lit_li a sw j <= Zlength (a_lits a))
    by (unfold lit_lim, lit_li, a_n, LITBUFFEREXTRASIZE; destruct (a_l a); try destruct sw; lia).
  unfold ZSTD_BLOCKSIZE_MAX in Hn. rep_lia.
Qed.

Lemma lg_fin_ok : SEG_FIN.
Proof.
  intros HTE Espec a x w R HG Hla Hpend Hlfx Hlfxx HLIP Hfin Hie HRn HRr.
  destruct w as [id ie pos lo st drep ring q K j sw c pp];
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in *.
  unfold fin_ph in Hfin; cbn [w_id w_pos] in Hfin. destruct Hfin as [Hid Hpos0]. subst id.
  (* pos = 0 as a boolean equation: the branches' subst keeps it *)
  apply Z.eqb_eq in Hpos0.
  destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_return] in HRn, HRr; subst Rn Rr.
  match goal with |- semax _ _ _ {| RA_normal := ?N |} => apply (semax_post (overridePost N (lg_R a))) end.
  { apply ENTAIL_refl. }
  { unfold lg_R, frame_ret_assert, function_body_ret_assert. cbn [RA_break].
    apply andp_left2. rewrite FF_sepcon. apply FF_left. }
  { unfold lg_R, frame_ret_assert, function_body_ret_assert. cbn [RA_continue].
    apply andp_left2. rewrite FF_sepcon. apply FF_left. }
  { intros vl. apply andp_left2. apply derives_refl. }
  unfold lg_R.
  unfold LI, LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base, lg_fin_pre;
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
  Intros. rename H10 into Hxl0.
  assert_PROP (isptr (a_vsqs a)) as Hvsqs by entailer!.
  assert_PROP (isptr (a_ob a)) as Hob by entailer!.
  assert_PROP (is_pointer_or_null (fs_dictEnd (a_fs a))) as Hpde by entailer!.
  assert (Hla' := Hla).
  destruct Hla' as (Hoa & Hiw & Hlits & Hbsm & Hnbsm & Hnbr & Hnb0 & Hso & Hrep & Hfe & Hc0 & Hlay).
  assert (Hoa' := Hoa). destruct Hoa' as (Hosh & HoN & HoN32 & Hod & Hocap & HodN).
  assert (Hes := H7). destruct Hes as (HK0 & HKE & Hj & Hjsw & Hcl & Hun).
  assert (Hnb: a_nb a <= LONGNBSEQ + 65535) by (destruct Hla as (_ & _ & _ & _ & _ & ? & _); lia).
  forward.
  rewrite fin_slot_addr by (auto; unfold LONGNBSEQ in *; rep_lia).
  set (k8 := ie mod 8).
  assert (Hk8: 0 <= k8 < 8) by (apply Z.mod_pos_bound; lia).
  destruct q as [|[[ll ml] off] q']; [rewrite Zlength_nil in H2; lia|].
  assert (Hcell: Znth k8 ring = Some (ll, ml, off)).
  { destruct H3 as (_ & Hr). specialize (Hr 0). rewrite Z.add_0_r, Znth_0_cons in Hr. apply Hr.
    rewrite Zlength_cons. pose proof (Zlength_nonneg q'). lia. }
  assert (Hrl: Zlength (ring_vals ring) = 8) by (unfold ring_vals; rewrite Zlength_map; apply H3).
  assert (Hrl8: Zlength ring = 8) by apply H3.
  rewrite <- (ring_back Tsh ring k8 (ll, ml, off) (a_vsqs a) Hk8 Hrl8 Hcell).
  unfold lit_now. Intros.
  unfold lg_fin_chk.
  forward.
  forward_if (PROP () LOCAL (temp _t'27 (Val.of_bool (fin_b a sw j ll));
      temp _sequence__2 (offset_val (24 * k8) (a_vsqs a));
      temp _seqAdvance (Vint (Int.repr (a_adv a))); temp _seqNb (Vint (Int.repr ie));
      temp _prefetchPos (Vlong (Int64.repr pp));
      temp _op (offset_val (a_d a + K) (a_ob a));
      temp _litBufferEnd (offset_val (lit_lim a sw) (lit_base a sw));
      lvar _sequence__1 t_seq (a_vs1 a); lvar _sequence t_seq (a_vs a);
      lvar _seqState t_seqstate (a_vss a); lvar _sequences (tarray t_seq 8) (a_vsqs a);
      lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a); temp _dctx (a_p a);
      temp _dst (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
      temp _maxDstSize (Vlong (Int64.repr (oa_cap (a_o a))));
      temp _seqStart (a_start a); temp _seqSize (Vlong (Int64.repr (Zlength (iw_s (a_i a)))));
      temp _nbSeq (Vint (Int.repr (a_nb a))); temp _isLongOffset (Vint (Int.repr 0));
      temp _ostart (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
      temp _oend (offset_val (a_E a) (oa_base (a_o a)));
      temp _prefixStart (fs_prefixStart (a_fs a)); temp _dictStart (fs_virtualStart (a_fs a));
      temp _dictEnd (fs_dictEnd (a_fs a)))
     SEP (data_at Tsh (tptr tuchar) (offset_val (lit_li a sw j) (lit_base a sw)) (a_vlp a);
      data_at Tsh t_seq (seqrep3 (ll, ml, off)) (offset_val (24 * k8) (a_vsqs a));
      ring_hole Tsh k8 (ring_vals ring) (a_vsqs a);
      seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) pos lo st (x_tp x) drep (a_vss a);
      data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seq (a_vs1 a);
      tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x); lit_fix a;
      field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a sw))) (a_p a);
      data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a));
      data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a);
      zstd_globals (a_gv a); pws_pred (a_W a); frame_fields (a_p a) (a_fs a);
      dent_of dent_def (a_gv a) (a_ox a);
      field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals (a_rep a)) (a_p a);
      data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a));
      bit_src (x_sh2 x) (a_start a) (iw_s (a_i a)); x_Ri x; ext_res (a_x a))).
  - destruct (lit_code_split a sw H10) as [-> [lb El]].
    rewrite (lit_fix_split a lb El). Intros.
    assert (Eli: lit_li a false j = lb + j) by (unfold lit_li; rewrite El; reflexivity).
    assert (Elb: lit_base a false = a_ob a) by (unfold lit_base; rewrite El; reflexivity).
    rewrite Eli, Elb.
    forward. forward. forward.
    cbn [seqrep3 fst].
    assert (Hn: a_n a - LITBUFFEREXTRASIZE <= a_n a) by (unfold LITBUFFEREXTRASIZE; lia).
    rewrite El in Hlits, Hjsw. destruct Hlits as (_ & Hn0 & Hn1 & Hdlb & Hlbe & _).
    assert (Hll: 0 <= ll <= LL_VMAX) by (inversion H4 as [|? ? Hq]; destruct Hq as (? & _); lia).
    forward.
    + entailer!. destruct (a_ob a); try contradiction. simpl. unfold sameblock. destruct peq; auto; congruence.
    + rewrite (lit_fix_split a lb El), Eli, Elb.
      rewrite fin_chk_val by (auto; unfold a_n, LITBUFFEREXTRASIZE, LL_VMAX, WILDCOPY_OVERLENGTH in *; rep_lia).
      replace (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j) <? ll) with (fin_b a false j ll)
        by (unfold fin_b; rewrite El; simpl; f_equal; lia).
      entailer!.
  - forward. entailer!. rewrite fin_b_false by auto. reflexivity.
  - destruct (fin_b a sw j ll) eqn:Eb; forward_if;
      try solve [contradiction | match goal with H: _ = Int.zero |- _ => inversion H end].
    + (* x1 *)
      assert (Hx1: exists lb, a_l a = LSplit lb /\ sw = false /\ a_n a - LITBUFFEREXTRASIZE - j < ll).
      { unfold fin_b in Eb. destruct (a_l a) eqn:?; try discriminate. destruct sw; try discriminate.
        simpl in Eb. apply Z.ltb_lt in Eb. eauto. }
      destruct Hx1 as (lb & El & -> & Hcut).
      assert (Hnb1: 0 < a_nb a) by lia.
      assert (Eli: lit_li a false j = lb + j) by (unfold lit_li; rewrite El; reflexivity).
      assert (Elb: lit_base a false = a_ob a) by (unfold lit_base; rewrite El; reflexivity).
      assert (Elim: lit_lim a false = lb + (a_n a - LITBUFFEREXTRASIZE)) by (unfold lit_lim; rewrite El; reflexivity).
      assert (HEd: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
      assert (Hlits' := Hlits). rewrite El in Hlits', Hjsw. destruct Hlits' as (_ & Hn0 & Hn1 & Hdlb & Hlbe & _).
      assert (Hq := H4). inversion Hq as [|? ? Hq1 Hq2]; subst. destruct Hq1 as (Hll & Hml & Hoff).
      set (w0 := mk_lst (a_nb a) ie pos lo st drep ring ((ll, ml, off) :: q') K j false c pp).
      assert (Hpre: fin_pre a x w0 ll ml off q')
        by exact (conj Hla (conj Hpend (conj Hlfx (conj HLIP (conj (conj eq_refl (proj1 (Z.eqb_eq _ _) Hpos0)) (conj Hie eq_refl)))))).
      destruct (fin_inv_ok a x w0 ll ml off q' Hpre) as (HXP & HNX & HER & Hxpos & Hxinv0).
      destruct (fin_xstep_ok a x ie K j false c ll ml off Hla Hpend Hlfx HXP) as (_ & _ & HX1).
      pose proof (xl_exec_X1 a (x_t x) (a_nb a) K c drep j lb pos lo st q' ll ml off (xl_ctx_of a Hla (proj2 Hlfxx))
                    Hxpos El ltac:(rewrite Eli, Elim; unfold a_n, LITBUFFEREXTRASIZE in *; lia)
                    ltac:(lia) ltac:(lia) ltac:(lia) Hxinv0) as HXX.
      cbv zeta in HXX. rewrite Eli, Elim in HXX.
      specialize (HX1 lb El eq_refl ltac:(rewrite Eli, Elim; unfold a_n, LITBUFFEREXTRASIZE in *; lia)).
      cbv zeta in HX1. rewrite Eli, Elim in HX1.
      rewrite (lit_fix_split a lb El). Intros.
      rewrite Eli, Elb, Elim.
      unfold lg_fin_x1.
      forward. forward. forward.
      { entailer!. clear - Hob. destruct (a_ob a); try contradiction. simpl.
        apply prop_right. destruct (peq b b); [reflexivity | congruence]. }
      rewrite lgf_sub by (auto; unfold a_n, a_d, a_cap, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia).
      set (lo0 := lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j)) in *.
      assert (Hlo0: 0 <= lo0) by (unfold lo0; lia).
      assert (Hloj: j + lo0 = a_n a - LITBUFFEREXTRASIZE) by (unfold lo0; lia).
      assert (Hlol: lo0 < ll) by (unfold lo0; lia).
      assert (Xcap: 0 < a_cap a) by (unfold a_d, a_cap, a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
      assert (Xsrc: Forall is_byte_val (sublist (lb + j) (lb + j + lo0) c)).
      { apply (xd_sub _ (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH));
          try (unfold lo0, a_d, a_cap, a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
        apply (ex_def_lit_S a (x_xc x) lb K j c); auto.
        destruct Hlfx as (_ & _ & _ & _ & Hxc); exact Hxc. }
      freeze [2;3;4;5;6;7;8;9;10;15;16;17;18;19;20;21] FR.
      forward_if (EX c1: list val,
        PROP (Zlength c1 = Zlength c; lo0 = 0 -> c1 = c;
              0 < lo0 -> lo0 <= a_E a - (a_d a + K) /\ fcopied c c1 (a_d a + K) (lb + j) lo0;
              0 < lo0 -> c1 = lsdbs c (a_d a + K) (lb + j) lo0)
        LOCAL (temp _leftoverLit__1 (Vlong (Int64.repr lo0));
         temp _sequence__2 (offset_val (24 * k8) (a_vsqs a));
         temp _seqAdvance (Vint (Int.repr (a_adv a))); temp _seqNb (Vint (Int.repr ie));
         temp _prefetchPos (Vlong (Int64.repr pp));
         temp _op (offset_val (a_d a + K + lo0) (a_ob a));
         temp _litBufferEnd (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a));
         lvar _sequence__1 t_seq (a_vs1 a); lvar _sequence t_seq (a_vs a);
         lvar _seqState t_seqstate (a_vss a); lvar _sequences (tarray t_seq 8) (a_vsqs a);
         lvar _litPtr (tptr tuchar) (a_vlp a); gvars (a_gv a); temp _dctx (a_p a);
         temp _dst (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
         temp _maxDstSize (Vlong (Int64.repr (oa_cap (a_o a))));
         temp _seqStart (a_start a); temp _seqSize (Vlong (Int64.repr (Zlength (iw_s (a_i a)))));
         temp _nbSeq (Vint (Int.repr (a_nb a))); temp _isLongOffset (Vint (Int.repr 0));
         temp _ostart (offset_val (oa_d (a_o a)) (oa_base (a_o a)));
         temp _oend (offset_val (a_E a) (oa_base (a_o a)));
         temp _prefixStart (fs_prefixStart (a_fs a)); temp _dictStart (fs_virtualStart (a_fs a));
         temp _dictEnd (fs_dictEnd (a_fs a)))
        SEP (FRZL FR; data_at Tsh (tptr tuchar) (offset_val (lb + j) (a_ob a)) (a_vlp a);
         data_at Tsh t_seq (seqrep3 (ll - lo0, ml, off)) (offset_val (24 * k8) (a_vsqs a));
         field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a false))) (a_p a);
         data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a));
         data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c1 (a_ob a);
         zstd_globals (a_gv a); ext_res (a_x a)))%assert.
      * assert (Hlp: 0 < lo0).
        { destruct (Z.eq_dec lo0 0) as [Hz|]; [|lia]. exfalso.
          match goal with H: Int64.repr lo0 <> Int64.zero |- _ => rewrite Hz in H; apply H; reflexivity end. }
        destruct (Z_lt_ge_dec (a_E a - (a_d a + K)) lo0) as [Herr|Hok].
        -- eapply semax_seq; [| apply semax_ff].
           apply lgf_do0. forward_if.
           { apply prop_right. clear - Hob. unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction.
             simpl. destruct (peq b b); [reflexivity | congruence]. }
           { apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
             match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
             ++ apply ENTAIL_refl.
             ++ forward_if True. { contradiction. } { forward. entailer!. }
                forward. Intros. apply ENTAIL_refl.
             ++ apply dec_skipbreak_seq. apply dec_skipbreak_seq.
                unfold la_post in POSTCONDITION. forward.
                assert (HXE: FXERR a c) by (destruct HX1 as [HX1' _]; exact (HX1' Hlp Herr)).
                assert (Hxn: xl_none a) by exact (proj1 HXX Hlp Herr).
                assert (Hd: dec_err (Int64.unsigned (Int64.repr (-70)))).
                { unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
                  rewrite Int64.unsigned_repr_eq. split; [reflexivity|]. split; vm_compute; congruence. }
                assert (HP: fin_errP a (Int64.unsigned (Int64.repr (-70))) c)
                  by (apply HER; auto; first [apply Int64.unsigned_range_2 | reflexivity | lia]).
                Exists (Int64.unsigned (Int64.repr (-70))) c (a_rep a).
                rewrite Int64.repr_unsigned.
                thaw FR.
                sep_apply (fin_lit_fold a lb (x_xc x) false _ El eq_refl).
                change (seqrep3 (ll, ml, off)) with (seqrep ll ml off).
                sep_apply (fin_ret_sep HTE a x false ll ml off k8 ring (offset_val (lb + j) (a_ob a)) pos lo st drep
                             Hlfx Hlfxx Hnb1 Hk8 Hrl8).
                destruct HP as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6 & HP7 & HP8 & HP9).
                apply andp_right;
                  [apply prop_right;
                   exact (conj HP1 (conj HP2 (conj HP3 (conj HP4 (conj HP5 (conj HP6 (conj HP7 (conj HP8 (conj HP9 eq_refl)))))))))
                  | unfold a_x, a_ob; cancel]. }
           { exfalso. match goal with H: typed_false tint _ |- _ =>
               change (oa_base (a_o a)) with (a_ob a) in H;
               rewrite lgf_gt in H by (auto; unfold a_n, a_d, a_cap, a_E, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia);
               replace (a_E a - (a_d a + K) <? lo0) with true in H by (symmetry; apply Z.ltb_lt; lia);
               discriminate H end. }
        -- match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
           ++ apply lgf_do0. forward_if.
              { apply prop_right. clear - Hob. unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction.
                simpl. destruct (peq b b); [reflexivity | congruence]. }
              { exfalso. match goal with H: typed_true tint _ |- _ =>
                  change (oa_base (a_o a)) with (a_ob a) in H;
                  rewrite lgf_gt in H by (auto; unfold a_n, a_d, a_cap, a_E, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia);
                  replace (a_E a - (a_d a + K) <? lo0) with false in H by (symmetry; apply Z.ltb_ge; lia);
                  discriminate H end. }
              { forward. entailer!. }
           ++ abbreviate_semax. forward.
              rewrite <- Hcl.
              assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] (a_ob a)) as Hfc by entailer!.
              assert (Hb1: a_d a + K + lo0 <= Zlength c /\ lb + j + lo0 + WILDCOPY_OVERLENGTH <= Zlength c).
              { unfold lo0. unfold a_d, a_cap, a_n, WILDCOPY_OVERLENGTH in *. lia. }
              assert (Hfa1: field_address0 (tarray tuchar (Zlength c)) (SUB (a_d a + K)) (a_ob a) =
                            offset_val (a_d a + K) (a_ob a)).
              { rewrite arr_field_address0 by (auto; unfold a_d in *; lia). change (sizeof tuchar) with 1. f_equal; lia. }
              assert (Hfa2: field_address0 (tarray tuchar (Zlength c)) (SUB (lb + j)) (a_ob a) =
                            offset_val (lb + j) (a_ob a)).
              { rewrite arr_field_address0 by (auto; unfold WILDCOPY_OVERLENGTH in *; lia). change (sizeof tuchar) with 1. f_equal; lia. }
              forward_call (a_gv a, oa_sh (a_o a), a_ob a, c, lb + j, a_d a + K, lo0).
              { unfold lo0 in *. unfold a_d, a_cap, a_n, WILDCOPY_OVERLENGTH in *. rep_lia. }
              Intros c1.
              forward.
              cbn [seqrep3 fst].
              forward.
              rewrite lgf_sub64 by (unfold lo0, a_n, LITBUFFEREXTRASIZE, LL_VMAX, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
              forward.
              rewrite fin_add by (auto; unfold lo0, a_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
              Exists c1. rewrite Hcl. entailer!.
              split; [lia|]. unfold fcopied, unchanged_outside. repeat split; auto.
      * assert (Hz: lo0 = 0).
        { match goal with H: Int64.repr lo0 = Int64.zero |- _ =>
            apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by
              (unfold lo0, a_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia); exact H end. }
        forward. Exists c.
        replace (ll - lo0) with ll by lia. replace (a_d a + K + lo0) with (a_d a + K) by lia.
        entailer!; intros; lia.
      * Intros c1.
        forward.
        assert_PROP (isptr (lit_extra (a_p a))) as Hxp by entailer!.
        assert (Hle: lit_extra (a_p a) = offset_val 30380 (a_p a)).
        { revert Hxp. unfold lit_extra, field_address. destruct (field_compatible_dec _ _ _); [reflexivity | intros []]. }
        rewrite <- Hle.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
          forward_if (PROPx P (LOCALx (temp _t'19 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
        { forward. entailer!. }
        { exfalso. match goal with H: Int.lt _ _ = false |- _ => revert H; vm_compute; intros Hc; discriminate Hc end. }
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
          forward_if (PROPx P (LOCALx (temp _t'20 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
        { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc; discriminate Hc end]. }
        { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
            forward_if (PROPx P (LOCALx (temp _t'20 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
          { forward. forward. entailer!. }
          { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc; discriminate Hc end]. } }
        forward. forward.
        assert (Hlbe2: force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
                         (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer (a_p a)) (Vint (Int.repr 65536))) =
                       offset_val 65536 (lit_extra (a_p a))).
        { clear - Hle Hxp. rewrite Hle in *. apply lgf_extra_end.
          destruct (a_p a); try contradiction; simpl; auto. }
        rewrite Hlbe2.
        assert (Hk1: 0 <= K + lo0 /\ a_d a + (K + lo0) <= a_E a).
        { destruct (Z.eq_dec lo0 0) as [Hz|Hz]; [rewrite Hz; lia|].
          match goal with H: 0 < lo0 -> _ |- _ => destruct (H ltac:(lia)) as [Hle1 _] end. lia. }
        assert (Hc1: Zlength c1 = oa_N (a_o a)) by lia.
        destruct (lgf_exec_pre a (K + lo0) c1 Hla Hnb1 (proj1 Hk1) (proj2 Hk1) Hc1)
          as (Hc32 & Hps & HEc & Hext & Hfps & Hfvs & Hfde).
        rewrite Hfps, Hfvs. rewrite <- Hfde.
        (* what execSequence reads: the history and the leftover copy, the extDict, litExtraBuffer *)
        assert (Xc1c: lo0 = 0 -> c1 = c) by assumption.
        assert (Xc1f: 0 < lo0 -> lo0 <= a_E a - (a_d a + K) /\ fcopied c c1 (a_d a + K) (lb + j) lo0) by assumption.
        assert (Xd1: ex_def a (K + lo0) (j + lo0) true c1).
        { destruct (Z.eq_dec lo0 0) as [Hz|Hz].
          - rewrite (Xc1c Hz), Hz, Z.add_0_r. match goal with H: ex_def a K j false c |- _ => exact H end.
          - destruct (Xc1f ltac:(lia)) as (_ & (Hcl1 & _ & Hcb1 & Hcu1)).
        assert (Hd0: 0 <= a_d a) by (destruct Hla as ((_ & _ & _ & Hd & _) & _); exact Hd).
        apply (ex_def_step a K lo0 j (j + lo0) false true c c1); try lia; auto.
        all: try (apply Hcb1; exact Xsrc).
        apply (xd_ub_frame c c1 (a_d a + K) (a_d a + K + lo0)); [exact Hcu1 |].
        apply xd_Forall_rng; [lia | lia | apply Hcb1; exact Xsrc]. }
        destruct (ex_def_hist a (K + lo0) (j + lo0) true c1 Hla Xcap ltac:(lia) ltac:(lia) Xd1) as (Xdh1 & Xde1).
        replace (a_d a + (K + lo0)) with (a_d a + K + lo0) in Xdh1 by lia.
        assert (Xdl1: Forall is_byte_val (sublist 0 (65536 + WILDCOPY_OVERLENGTH) (x_xc x)))
          by (apply Forall_sublist; destruct Hlfx as (_ & _ & _ & _ & (_ & Hxb & _)); exact Hxb).
        change (seqrep3 (ll - lo0, ml, off)) with (seqrep (ll - lo0) ml off).
        assert (Hxl: Zlength (x_xc x) = LITEXTRA_N) by (destruct Hlfx as (_ & _ & _ & _ & (Hx & _)); exact Hx).
        rewrite <- Hxl.
        change (data_at Ews (tarray tuchar (Zlength (x_xc x))) (x_xc x) (lit_extra (a_p a)))
          with (BlkSeqEXEC.lit_res (LitSep Ews (lit_extra (a_p a)) (x_xc x))).
        rewrite <- Hc1.
        assert (Hlp0: data_at Tsh (tptr tuchar) (lit_extra (a_p a)) (a_vlp a) =
                      data_at Tsh (tptr tuchar) (offset_val 0 (lit_extra (a_p a))) (a_vlp a))
          by (rewrite isptr_offset_val_zero by exact Hxp; reflexivity).
        rewrite Hlp0.
        forward_call (a_gv a, oa_sh (a_o a), a_ob a, c1, a_d a + K + lo0, a_E a, Tsh, offset_val (24 * k8) (a_vsqs a),
                      ll - lo0, ml, off, Tsh, a_vlp a, LitSep Ews (lit_extra (a_p a)) (x_xc x), 0, 65536, a_ps a, a_x a,
                      fs_dictEnd (a_fs a)).
        { rewrite Hxl. unfold LL_VMAX, ML_VMAX, SIZE_MAX in Hll, Hml, Hoff.
          unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
          repeat split; try rep_lia; auto. }
        Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
        assert (Eli1: lit_li a true (j + lo0) = 0) by (unfold lit_li; rewrite El; lia).
        assert (Elim1: lit_lim a true = 65536) by (unfold lit_lim; rewrite El; reflexivity).
        assert (Els: fin_ls a x = LitSep Ews (lit_extra (a_p a)) (x_xc x)) by (unfold fin_ls; rewrite El; reflexivity).
        destruct HX1 as [_ HX1'].
        assert (Hc1c: lo0 = 0 -> c1 = c) by assumption.
        assert (Hc1f: 0 < lo0 -> lo0 <= a_E a - (a_d a + K) /\ fcopied c c1 (a_d a + K) (lb + j) lo0) by assumption.
        specialize (HX1' c1 Hc1c Hc1f c'). cbv zeta in HX1'.
        rewrite Eli1, Elim1, Els in HX1'.
        assert (Hc'l: Zlength c' = Zlength c)
          by (match goal with H: Zlength c' = Zlength c1 |- _ => rewrite H end; lia).
        assert (Hb': byte_cells c1 -> byte_cells (lit_arr (LitSep Ews (lit_extra (a_p a)) (x_xc x)) c1) ->
                     ext_bytes (a_x a) -> byte_cells c') by assumption.
        assert (Hxu': xd_ub c1 c') by assumption.
        destruct (HX1' Hc'l Hb' Hxu') as (HXe & HXs). clear HX1'.
        (* the exact model: the leftover copy is lsdbs, execSequence's stores lexec *)
        assert (Hc1x: 0 < lo0 -> c1 = lsdbs c (a_d a + K) (lb + j) lo0) by assumption.
        destruct HXX as [_ HXX].
        specialize (HXX c1 Hc1c (fun H => conj (proj1 (Hc1f H)) (Hc1x H)) r c').
        cbv zeta in HXX. rewrite Eli1, Elim1 in HXX.
        rewrite <- (fin_lsrc a x true ltac:(rewrite El; reflexivity) (proj1 Hlfxx)), Els in HXX.
        destruct (HXX ltac:(assumption) ltac:(assumption)) as (HXXe & HXXs). clear HXX.
        forward_call r.
        unfold POSTCONDITION, abbreviate, la_post.
        destruct (is_error_code r) eqn:Er.
        -- forward_if (PROP (False) LOCAL () SEP ()).
           { forward.
             match goal with H: true = true -> _ /\ dec_err r |- _ => destruct (H eq_refl) as (Hun1 & Hde) end.
             assert (HE: FXERR a c') by (apply HXe; [congruence | exact Hun1]).
             assert (Hxn: xl_none a) by exact (HXXe eq_refl).
             assert (HP: fin_errP a r c') by (apply HER; auto; lia).
             Exists r c' (a_rep a).
             thaw FR.
             unfold BlkSeqEXEC.lit_res. rewrite Hxl.
             sep_apply (fin_lit_fold a lb (x_xc x) true _ El eq_refl).
             sep_apply (fin_ret_sep HTE a x true (ll - lo0) ml off k8 ring lp pos lo st drep Hlfx Hlfxx Hnb1 Hk8 Hrl8).
             rewrite Hc1. destruct HP as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6 & HP7 & HP8 & HP9).
             apply andp_right;
               [apply prop_right;
                exact (conj HP1 (conj HP2 (conj HP3 (conj HP4 (conj HP5 (conj HP6 (conj HP7 (conj HP8 (conj HP9 eq_refl)))))))))
               | unfold a_x, a_ob; cancel]. }
           all: try solve [match goal with H: _ = Int.zero |- _ => inversion H end].
        -- match goal with H: false = false -> _ |- _ => destruct (H eq_refl) as (Hr & Hlp & Hun' & Hbytes) end.
           match goal with H: false = exec_err _ _ _ _ _ _ _ _ _ |- _ => rename H into Hee end.
           subst r lp.
           assert (HQ: FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c').
           { apply HXs; [congruence | exact Hun' | | exact Hbytes].
             match goal with H: false = false -> Forall _ _ |- _ => exact (H eq_refl) end. }
           assert (HL: LIP a x (fin_next w0 q' (upd_Znth k8 ring (Some (ll - lo0, ml, off)))
                                  (K + (ll + ml)) (j + ll) true c'))
             by (apply HNX; [right; eexists; reflexivity | exact HQ | exact (HXXs eq_refl)]).
           apply semax_if_seq. forward_if.
           { exfalso. match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
           forward.
           Exists (fin_next w0 q' (upd_Znth k8 ring (Some (ll - lo0, ml, off))) (K + (ll + ml)) (j + ll) true c').
           thaw FR.
           unfold fin_next in *; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp w0] in *.
           unfold LIP, LI_P in HL; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp fold_right] in HL.
           destruct HL as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & HL7 & HL8 & HL9 & HL10 & HL11 & HL12 & _).
           rewrite fin_add by (auto; unfold lo0, a_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX, LL_VMAX, ML_VMAX in *; rep_lia).
           rewrite <- Hfps, <- Hfvs, Hfde.
           assert (Eli2: lit_li a true (j + ll) = 0 + (ll - lo0)) by (unfold lit_li; rewrite El; lia).
           assert (Elb2: lit_base a true = lit_extra (a_p a)) by (unfold lit_base; rewrite El; reflexivity).
           rewrite Eli2, Elb2, Elim1. unfold BlkSeqEXEC.lit_base.
           replace (a_d a + K + lo0 + (ll - lo0 + ml)) with (a_d a + (K + (ll + ml))) by lia.
           rewrite Hc1. unfold fin_ph. cbn [w_id]. apply Z.eqb_eq in Hpos0.
           unfold BlkSeqEXEC.lit_res. rewrite Hxl.
           entailer!.
           change (seqrep (ll - lo0) ml off) with (seqrep3 (ll - lo0, ml, off)).
           rewrite <- (ring_back_upd Tsh ring k8 (ll - lo0, ml, off) (a_vsqs a) Hk8 Hrl8).
           sep_apply (fin_lit_fold a lb (x_xc x) true _ El eq_refl).
           cancel.
    + (* x2 *)
      unfold lg_fin_x2. forward.
      apply semax_if_seq.
      destruct (Int.eq_dec (Int.repr (lit_code a sw)) (Int.repr 2)) as [Hsp|Hns]; forward_if;
        try contradiction.
      * (* split *)
        destruct (lit_code_split a sw Hsp) as [-> [lb El]].
        assert (Hnb1: 0 < a_nb a) by lia.
        destruct (fin_hist_pre a K j false c Hla H7 Hnb1)
          as (Hc32 & Hps & HkE & HEcap & HcapN & Hext & Hfps & Hfvs & Hfde).
        assert (Hq := H4). inversion Hq as [|? ? Hq1 Hq2]; subst. destruct Hq1 as (Hll & Hml & Hoff).
        assert (Eli: lit_li a false j = lb + j) by (unfold lit_li; rewrite El; reflexivity).
        assert (Elb: lit_base a false = a_ob a) by (unfold lit_base; rewrite El; reflexivity).
        assert (Elim: lit_lim a false = lb + (a_n a - LITBUFFEREXTRASIZE)) by (unfold lit_lim; rewrite El; reflexivity).
        assert (HEd: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
        assert (Hlits' := Hlits). rewrite El in Hlits', Hjsw. destruct Hlits' as (_ & Hn0 & Hn1 & Hdlb & Hlbe & _).
        assert (Hjl: lb + j + ll <= lb + (a_n a - LITBUFFEREXTRASIZE)).
        { unfold fin_b in Eb. rewrite El in Eb. simpl in Eb. apply Z.ltb_ge in Eb. lia. }
        (* what execSequenceSplitLitBuffer reads *)
        assert (Xcap: 0 < a_cap a) by (unfold a_d, a_cap, a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
        assert (Xdf: ex_def a K j false c) by assumption.
        destruct (ex_def_hist a K j false c Hla Xcap ltac:(lia) ltac:(lia) Xdf) as (Xdh & Xde).
        assert (Xdl: Forall is_byte_val (sublist (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH) c)).
        { apply (ex_def_lit_S a (x_xc x) lb K j c); auto. destruct Hlfx as (_ & _ & _ & _ & Hxc); exact Hxc. }
        rewrite Hfps, Hfvs, Eli, Elb, Elim.
        forward. forward.
        cbn [seqrep3 fst].
        rewrite <- Hcl.
        forward_call (a_gv a, oa_sh (a_o a), a_ob a, c, a_d a + K, a_E a, Tsh,
                      offset_val (24 * k8) (a_vsqs a), ll, ml, off, Tsh, a_vlp a, lb + j,
                      lb + (a_n a - LITBUFFEREXTRASIZE), a_ps a, a_x a, fs_dictEnd (a_fs a)).
        { entailer!. rewrite Hfde. simpl. rewrite fin_sub32 by auto. reflexivity. }
        { (* the split literal buffer lies near the end of dst (la_pend) *)
          pose proof Hpend as (_ & Hp). rewrite El in Hp.
          destruct (Z.min_spec (a_bsm a) (a_cap a)) as [[? E]|[? E]]; rewrite E in Hp;
          rewrite HEd; unfold a_d, a_cap, a_n, LL_VMAX, ML_VMAX, SIZE_MAX, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX,
            LITBUFFEREXTRASIZE in *; repeat split; rep_lia. }
        Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
        set (w0 := mk_lst (a_nb a) ie pos lo st drep ring ((ll, ml, off) :: q') K j false c pp).
        assert (Hpre: fin_pre a x w0 ll ml off q')
          by exact (conj Hla (conj Hpend (conj Hlfx (conj HLIP (conj (conj eq_refl (proj1 (Z.eqb_eq _ _) Hpos0)) (conj Hie eq_refl)))))).
        destruct (fin_inv_ok a x w0 ll ml off q' Hpre) as (HXP & HNX & HER & Hxpos & Hxinv0).
        destruct (fin_xstep_ok a x ie K j false c ll ml off Hla Hpend Hlfx HXP) as (_ & HXS & _).
        cbv zeta in HXS.
        assert (Hc'l: Zlength c' = Zlength c) by assumption.
        assert (Hb': byte_cells c -> ext_bytes (a_x a) -> byte_cells c') by assumption.
        assert (Hxu': xd_ub c c') by assumption.
        destruct (HXS lb El eq_refl ltac:(rewrite Eli, Elim; lia) c' Hc'l Hb' Hxu') as (HXSe & HXSs).
        rewrite Eli in HXSe, HXSs.
        assert (HXX: (is_error_code r = true -> xl_none a) /\
                     (is_error_code r = false -> xl_inv a (x_t x) (a_nb a) (K + (ll + ml)) c' drep (j + ll) false pos lo st q')).
        { apply (xl_exec_S a (x_t x) (a_nb a) K c c' drep j lb pos lo st q' ll ml off r (xl_ctx_of a Hla (proj2 Hlfxx))
                   Hxpos El); try lia; try exact Hxinv0; rewrite ?Eli, ?Elim; first [assumption | lia]. }
        destruct HXX as (HXXe & HXXs).
        forward. forward. forward_call r.
        unfold POSTCONDITION, abbreviate, la_post.
        destruct (is_error_code r) eqn:Er.
        -- forward_if (PROP (False) LOCAL () SEP ()).
           { forward.
             match goal with H: true = true -> _ /\ dec_err r |- _ => destruct (H eq_refl) as (Hun1 & Hde) end.
             assert (HE: FXERR a c') by (apply HXSe; [congruence | exact Hun1]).
             assert (Hxn: xl_none a) by exact (HXXe eq_refl).
             assert (HP: fin_errP a r c') by (apply HER; auto; lia).
             Exists r c' (a_rep a).
             sep_apply (fin_lit_now_fold a (x_xc x) false).
             sep_apply (fin_ret_sep HTE a x false ll ml off k8 ring lp pos lo st drep Hlfx Hlfxx Hnb1 Hk8 Hrl8).
             rewrite Hcl. destruct HP as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6 & HP7 & HP8 & HP9).
             apply andp_right;
               [apply prop_right;
                exact (conj HP1 (conj HP2 (conj HP3 (conj HP4 (conj HP5 (conj HP6 (conj HP7 (conj HP8 (conj HP9 eq_refl)))))))))
               | unfold a_x, a_ob; cancel]. }
           all: try solve [match goal with H: _ = Int.zero |- _ => inversion H end].
        -- match goal with H: false = false -> _ |- _ => destruct (H eq_refl) as (Hr & Hlp & Hun' & Hdef') end.
           subst r lp.
           assert (HQ: FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) false c').
           { apply HXSs; [congruence | exact Hun' | | exact Hdef'].
             match goal with H: false = false -> Forall _ _ |- _ => exact (H eq_refl) end. }
           assert (HL: LIP a x (fin_next w0 q' ring (K + (ll + ml)) (j + ll) false c'))
             by (apply HNX; [auto | exact HQ | exact (HXXs eq_refl)]).
           apply semax_if_seq. forward_if.
           { exfalso. match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
           forward.
           Exists (fin_next w0 q' ring (K + (ll + ml)) (j + ll) false c').
           unfold fin_next in *; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp w0] in *.
           unfold LIP, LI_P in HL; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp fold_right] in HL.
           destruct HL as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & HL7 & HL8 & HL9 & HL10 & HL11 & HL12 & _).
           rewrite fin_add by (auto; unfold LL_VMAX, ML_VMAX in *; rep_lia).
           rewrite <- Hfps, <- Hfvs. rewrite lit_li_add, Eli, Elim, Elb.
           replace (a_d a + K + (ll + ml)) with (a_d a + (K + (ll + ml))) by lia.
           replace (lb + j + ll) with (lb + (j + ll)) by lia.
           rewrite Hcl. unfold fin_ph. cbn [w_id]. apply Z.eqb_eq in Hpos0.
           entailer!.
           rewrite <- (ring_back Tsh ring k8 (ll, ml, off) (a_vsqs a) Hk8 Hrl8 Hcell).
           unfold lit_now. change (seqrep ll ml off) with (seqrep3 (ll, ml, off)).
           cancel.
      * (* not split *)
        assert (Hsw := fin_nsplit a sw Hns).
        assert (Hnb1: 0 < a_nb a) by lia.
        destruct (fin_exec_pre a x K j sw c Hla Hlfx H7 Hnb1 Hsw)
          as (Hc32 & Hps & HkE & HEcap & Hls & Hlim & Hext & Hfps & Hfvs & Hfde).
        assert (Hq := H4). inversion Hq as [|? ? Hq1 Hq2]; subst. destruct Hq1 as (Hll & Hml & Hoff).
        (* what execSequence reads *)
        assert (Xcap: 0 < a_cap a) by (destruct (Hnb0 ltac:(lia)) as [_ Xc0]; exact Xc0).
        assert (Xdf: ex_def a K j sw c) by assumption.
        destruct (ex_def_hist a K j sw c Hla Xcap ltac:(lia) ltac:(lia) Xdf) as (Xdh & Xde).
        assert (Xdl: Forall is_byte_val (sublist (lit_li a sw j) (lit_lim a sw + WILDCOPY_OVERLENGTH) (lit_arr (fin_ls a x) c))).
        { apply (ex_def_lit_N a (x_xc x) (fin_ls a x) K j sw c); auto.
          - destruct Hlfx as (_ & _ & _ & _ & Hxc); exact Hxc.
          - unfold fin_ls. destruct (a_l a); reflexivity. }
        rewrite Hfps, Hfvs.
        rewrite <- (fin_ls_base a x sw Hsw).
        assert (HiN: Zlength (iw_c (a_i a)) = iw_N (a_i a)) by (destruct Hiw as (_ & _ & _ & _ & ? & _); auto).
        assert (Hxl: Zlength (x_xc x) = LITEXTRA_N) by (destruct Hlfx as (_ & _ & _ & _ & ? & _); auto).
        gather_SEP (data_at (x_sh1 x) _ _ _) (data_at Ews (tarray tuchar LITEXTRA_N) _ _).
        rewrite (fin_lres a x HiN Hxl).
        rewrite <- Hcl.
        forward_call (a_gv a, oa_sh (a_o a), a_ob a, c, a_d a + K, a_E a, Tsh, offset_val (24 * k8) (a_vsqs a),
                      ll, ml, off, Tsh, a_vlp a, fin_ls a x, lit_li a sw j, lit_lim a sw, a_ps a, a_x a,
                      fs_dictEnd (a_fs a)).
        { cancel. }
        { pose proof (lgf_lit_span a sw j Hla
            ltac:(match goal with H: ex_safe a K j sw c |- _ => destruct H as (_ & _ & ? & _); lia end)).
          unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. repeat split; auto; rep_lia. }
        Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
        set (w0 := mk_lst (a_nb a) ie pos lo st drep ring ((ll, ml, off) :: q') K j sw c pp).
        assert (Hpre: fin_pre a x w0 ll ml off q')
          by exact (conj Hla (conj Hpend (conj Hlfx (conj HLIP (conj (conj eq_refl (proj1 (Z.eqb_eq _ _) Hpos0)) (conj Hie eq_refl)))))).
        destruct (fin_inv_ok a x w0 ll ml off q' Hpre) as (HXP & HNX & HER & Hxpos & Hxinv0).
        destruct (fin_xstep_ok a x ie K j sw c ll ml off Hla Hpend Hlfx HXP) as (HXN & _ & _).
        assert (Hc'l: Zlength c' = Zlength c) by assumption.
        assert (Hb': byte_cells c -> byte_cells (lit_arr (fin_ls a x) c) -> ext_bytes (a_x a) -> byte_cells c')
          by assumption.
        assert (Hxu': xd_ub c c') by assumption.
        destruct (HXN Hsw c' Hc'l Hb' Hxu') as (HXNe & HXNs).
        assert (HXX: (is_error_code r = true -> xl_none a) /\
                     (is_error_code r = false -> xl_inv a (x_t x) (a_nb a) (K + (ll + ml)) c' drep (j + ll) sw pos lo st q')).
        { pose proof (fin_lsrc a x sw Hsw (proj1 Hlfxx)) as Els.
          apply (xl_exec_N a (x_t x) (a_nb a) K c c' drep j sw pos lo st q' ll ml off r (xl_ctx_of a Hla (proj2 Hlfxx))
                   Hxpos Hsw); [lia | lia | lia | exact Hxinv0 | |].
          - match goal with H: is_error_code r = exec_err _ _ _ _ _ _ _ _ _ |- _ => exact H end.
          - match goal with H: match a_x a with ExtSep _ _ _ _ _ _ => True | _ => _ end |- _ =>
              rewrite Els in H; exact H end. }
        destruct HXX as (HXXe & HXXs).
        forward. forward_call r.
        unfold POSTCONDITION, abbreviate, la_post.
        destruct (is_error_code r) eqn:Er.
        -- forward_if (PROP (False) LOCAL () SEP ()).
           { forward.
             match goal with H: true = true -> _ /\ dec_err r |- _ => destruct (H eq_refl) as (Hun1 & Hde) end.
             assert (HE: FXERR a c') by (apply HXNe; [congruence | exact Hun1]).
             assert (Hxn: xl_none a) by exact (HXXe eq_refl).
             assert (HP: fin_errP a r c') by (apply HER; auto; lia).
             Exists r c' (a_rep a).
             sep_apply (fin_lres_back a x HiN Hxl).
             sep_apply (fin_lit_now_fold a (x_xc x) sw).
             sep_apply (fin_ret_sep HTE a x sw ll ml off k8 ring lp pos lo st drep Hlfx Hlfxx Hnb1 Hk8 Hrl8).
             rewrite Hcl. destruct HP as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6 & HP7 & HP8 & HP9).
             apply andp_right;
               [apply prop_right;
                exact (conj HP1 (conj HP2 (conj HP3 (conj HP4 (conj HP5 (conj HP6 (conj HP7 (conj HP8 (conj HP9 eq_refl)))))))))
               | unfold a_x, a_ob; cancel]. }
           all: try solve [match goal with H: _ = Int.zero |- _ => inversion H end].
        -- match goal with H: false = false -> _ |- _ => destruct (H eq_refl) as (Hr & Hlp & Hun' & Hbytes) end.
           match goal with H: false = exec_err _ _ _ _ _ _ _ _ _ |- _ => rename H into Hee end.
           subst r lp.
           assert (HQ: FXQ a x (ie + 1) (K + (ll + ml)) (j + ll) sw c').
           { apply HXNs; [congruence | exact Hun' | | exact Hbytes].
             match goal with H: false = false -> Forall _ _ |- _ => exact (H eq_refl) end. }
           assert (HL: LIP a x (fin_next w0 q' ring (K + (ll + ml)) (j + ll) sw c'))
             by (apply HNX; [auto | exact HQ | exact (HXXs eq_refl)]).
           apply semax_if_seq. forward_if.
           { exfalso. match goal with H: _ <> Int.zero |- _ => apply H; reflexivity end. }
           forward.
           Exists (fin_next w0 q' ring (K + (ll + ml)) (j + ll) sw c').
           unfold fin_next in *; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp w0] in *.
           unfold LIP, LI_P in HL; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp fold_right] in HL.
           destruct HL as (HL1 & HL2 & HL3 & HL4 & HL5 & HL6 & HL7 & HL8 & HL9 & HL10 & HL11 & HL12 & _).
           rewrite fin_add by (auto; unfold LL_VMAX, ML_VMAX in *; rep_lia).
           rewrite (fin_ls_base a x sw Hsw). rewrite <- Hfps, <- Hfvs. rewrite <- lit_li_add.
           replace (a_d a + K + (ll + ml)) with (a_d a + (K + (ll + ml))) by lia.
           rewrite Hcl. unfold fin_ph. cbn [w_id]. apply Z.eqb_eq in Hpos0.
           entailer!.
           sep_apply (fin_lres_back a x HiN Hxl).
           rewrite <- (ring_back Tsh ring k8 (ll, ml, off) (a_vsqs a) Hk8 Hrl8 Hcell).
           unfold lit_now. change (seqrep ll ml off) with (seqrep3 (ll, ml, off)).
           cancel.
Qed.
