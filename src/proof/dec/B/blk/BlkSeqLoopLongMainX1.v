(* LOOP / long loop, part MAIN: branch t'17 (leftover copy, switch, execSequence).
   The exact model (BlkSeqLoopLongX.xl_inv) follows by BlkSeqLoopLongXE.xl_exec_X1 from COPY's and EXEC's exact
   stores (lsdbs, lexec); error returns give seqs_exact by xl_exact_none. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Require Zstd.proof.dec.B.blk.BlkSeqLoopLongXE.
Local Open Scope logic.

(* ===================== helpers: error returns (as in BlkSeqLoopLongEnd.v), the ring ===================== *)

(* the seqState_t local back to data_at_ (as BlkSeqLoopShort.sh_end_ok_ss) *)
Lemma lgx_ss_split (v: val) :
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

Lemma lgx_ss (gv: globals) (s: list Z) (start: val) (pos lo sLL sOF sML: Z) (pLL pOF pML: val) (r: Z * Z * Z)
    (v: val) :
  BIT_DStream_rep Tsh gv s start pos lo (field_address t_seqstate (DOT _DStream) v) *
  field_at Tsh t_seqstate (DOT _stateLL) (fse_val sLL pLL) v *
  field_at Tsh t_seqstate (DOT _stateOffb) (fse_val sOF pOF) v *
  field_at Tsh t_seqstate (DOT _stateML) (fse_val sML pML) v *
  field_at Tsh t_seqstate (DOT _prevOffset) (rep64_vals r) v
  |-- data_at_ Tsh (Tstruct ___gp_seqState_t noattr) v.
Proof.
  rewrite lgx_ss_split. unfold BIT_DStream_rep. Intros ptr lim.
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
Lemma lgx_E_le (a: la) : la_ok a -> a_E a <= a_d a + a_cap a.
Proof.
  intros (_ & _ & Hlits & _). unfold a_E, a_d, a_cap.
  destruct Hlits as (_ & Hn & Hl). destruct (a_l a); try lia.
  destruct Hl as (? & ? & _). unfold WILDCOPY_OVERLENGTH in *. lia.
Qed.

(* the model decodes when seqs_model is defined *)
Lemma lgx_DM (a: la) (t: fse_table * fse_table * fse_table) (rep: Z * Z * Z) (hist out lits: list Z)
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

Definition lgx_ring_hole (sh: share) (k: Z) (rv: list (val * (val * val))) (v: val) : mpred :=
  !! field_compatible (tarray t_seq 8) [] v &&
  (data_at sh (tarray t_seq k) (sublist 0 k rv) v *
   data_at sh (tarray t_seq (8 - (k + 1))) (sublist (k + 1) 8 rv) (offset_val (24 * (k + 1)) v)).

Lemma lgx_ring_join (sh: share) (rv: list (val * (val * val))) (k: Z) (cell: val * (val * val)) (v: val) :
  0 <= k < 8 -> Zlength rv = 8 ->
  data_at sh (tarray t_seq 8) (upd_Znth k rv cell) v =
  data_at sh t_seq cell (offset_val (24 * k) v) * lgx_ring_hole sh k rv v.
Proof.
  intros Hk Hl. unfold lgx_ring_hole.
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

(* the PROP list as one Prop *)
Lemma lgx_prop1 (P: list Prop) (Q: list localdef) (R: list mpred) :
  PROPx P (LOCALx Q (SEPx R)) = PROPx [fold_right and True P] (LOCALx Q (SEPx R)).
Proof.
  unfold PROPx. f_equal. extensionality rho. simpl.
  replace (fold_right and True P /\ True) with (fold_right and True P); [reflexivity|].
  apply prop_ext; tauto.
Qed.

(* the split literals: litPtr, litBufferEnd in the output array *)
Lemma lgx_lit_fix_split (a: la) (lb: Z) :
  a_l a = LSplit lb ->
  lit_fix a =
  field_at Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (a_n a))) (a_p a) *
  (field_at Ews t_dctx (DOT _litPtr) (offset_val lb (a_ob a)) (a_p a) *
   field_at Ews t_dctx (DOT _litBufferEnd) (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a)) (a_p a) *
   field_at Ews t_dctx (DOT _litBuffer) (offset_val lb (a_ob a)) (a_p a)).
Proof. intros E. unfold lit_fix. rewrite E. reflexivity. Qed.

(* (p + A) - (p + B) *)
Lemma lgx_sub (b: val) (A B: Z) :
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
Lemma lgx_gt (b: val) (E k lo: Z) :
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

(* op += n *)
Lemma lgx_add (b: val) (a n: Z) :
  isptr b -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong (offset_val a b) (Vlong (Int64.repr n))) =
  offset_val (a + n) b.
Proof.
  intros Hb Hn. destruct b; try contradiction. simpl.
  unfold sem_add_ptr_long. simpl. f_equal.
  rewrite Ptrofs.add_assoc. f_equal.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
  rewrite Ptrofs.add_unsigned. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma lgx_sub64 (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. intros. unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

(* the facts of exec_spec's precondition (the array, the history pointers) *)
Lemma lgx_exec_pre (a: la) (K: Z) (c: list val) :
  la_ok a -> 0 < a_nb a -> 0 <= K -> a_d a + K <= a_E a -> Zlength c = oa_N (a_o a) ->
  Zlength c <= 2 ^ 63 - 1 /\ 0 <= a_ps a <= a_d a + K /\ a_E a <= Zlength c /\
  exec_ext_ok (a_x a) c /\
  fs_prefixStart (a_fs a) = offset_val (a_ps a) (a_ob a) /\
  fs_virtualStart (a_fs a) = offset_val (a_ps a - ext_len (a_x a)) (a_ob a) /\
  dict_end (a_x a) (a_ob a) (fs_dictEnd (a_fs a)) = fs_dictEnd (a_fs a).
Proof.
  intros Hla Hnb HK HKE Hcl.
  pose proof (lgx_E_le a Hla) as HE.
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

(* litExtraBuffer + 65536 *)
Lemma lgx_extra_end (p: val) :
  isptr p ->
  force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
    (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer p) (Vint (Int.repr 65536))) =
  offset_val 65536 (offset_val 30380 p).
Proof.
  intros Hp. destruct p; try contradiction. simpl. f_equal.
Qed.

(* &sequences[k] *)
Lemma lgx_addp (v: val) (k: Z) :
  isptr v -> 0 <= k < 8 ->
  force_val (sem_add_ptr_int (Tstruct ___gp_seq_t noattr) Signed v (Vint (Int.repr k))) = offset_val (24 * k) v.
Proof.
  intros Hv Hk. destruct v; try contradiction. simpl. unfold sem_add_ptr_int. simpl.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

Lemma lgx_cast (v: val) (t1 t2: type) : is_pointer_or_null v -> eval_cast (tptr t1) (tptr t2) v = v.
Proof. intros H. destruct v; simpl in *; try contradiction; auto. Qed.

(* the head's cell back as a free ring slot *)
Lemma lgx_ring_none (r: list (option (Z * Z * Z))) (k: Z) (cell: reptype t_seq) (v: val) :
  0 <= k < 8 -> Zlength r = 8 ->
  data_at Tsh t_seq cell (offset_val (24 * k) v) * lgx_ring_hole Tsh k (ring_vals r) v |--
  data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r None)) v.
Proof.
  intros Hk Hr. unfold ring_vals at 2. rewrite <- upd_Znth_map. fold (ring_vals r).
  rewrite lgx_ring_join by (auto; unfold ring_vals; rewrite Zlength_map; lia).
  cancel.
Qed.

Lemma lgx_fr_app (l1 l2: list Prop) :
  fold_right and True l1 -> fold_right and True l2 -> fold_right and True (l1 ++ l2).
Proof. induction l1 as [|p l1 IH]; simpl; auto. intros [Hp H1] H2. split; auto. Qed.

Lemma lgx_ent_prop (P: Prop) (A: environ -> mpred) (Q: list localdef) (R: list mpred) :
  P -> A |-- PROPx [] (LOCALx Q (SEPx R)) -> A |-- PROPx [P] (LOCALx Q (SEPx R)).
Proof.
  intros HP H. eapply derives_trans; [exact H|]. unfold PROPx. intro rho. simpl.
  apply andp_derives; [apply prop_derives; tauto | apply derives_refl].
Qed.

(* ===== error returns: the resources of la_post and the stack frame ===== *)

Lemma lgx_ss2 (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z) (tp: val * val * val)
    (r: Z * Z * Z) (v: val) :
  seqstate_at Tsh gv s start pos lo st tp r v |-- data_at_ Tsh t_seqstate v.
Proof.
  unfold seqstate_at. destruct st as [[sLL sOF] sML], tp as [[pLL pOF] pML]. apply lgx_ss.
Qed.

(* the literal fields back as scratch, litExtraBuffer still holding lxb (la_post's lit_scratch_x) *)
Lemma lgx_lit_rel (p: val) (v1 v2 v3 v4 v5: val) (lxb: list Z) :
  Zlength lxb = LITEXTRA_N -> bytes_ok lxb ->
  field_at Ews t_dctx (DOT _litSize) v1 p * field_at Ews t_dctx (DOT _litPtr) v2 p *
  field_at Ews t_dctx (DOT _litBufferEnd) v3 p * field_at Ews t_dctx (DOT _litBuffer) v4 p *
  field_at Ews t_dctx (DOT _litBufferLocation) v5 p *
  data_at Ews (tarray tuchar LITEXTRA_N) (zbytes lxb) (lit_extra p)
  |-- lit_scratch_x p lxb.
Proof.
  intros Hl Hb. unfold lit_scratch_x, lit_extra_at, lit_extra.
  rewrite (field_at_data_at Ews t_dctx (DOT _litExtraBuffer)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize) v1 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr) v2 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd) v3 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer) v4 p).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation) v5 p).
  entailer!.
Qed.

Lemma lgx_rel (HTE: TABS_ELIM) (a: la) (x: lfx) (lpv: val) (rv: list (val * (val * val)))
    (dpos dlo: Z) (dst drp: Z * Z * Z) (s1: reptype t_seq) (v1 v2 v3 v4 v5: val) :
  lfx_ok a x -> lfx_x a x ->
  data_at Tsh (tptr tuchar) lpv (a_vlp a) * data_at Tsh (tarray t_seq 8) rv (a_vsqs a) *
  seqstate_at Tsh (a_gv a) (iw_s (a_i a)) (a_start a) dpos dlo dst (x_tp x) drp (a_vss a) *
  data_at_ Tsh t_seq (a_vs a) * data_at Tsh t_seq s1 (a_vs1 a) *
  tabs_seq_tp (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x) *
  field_at Ews t_dctx (DOT _litSize) v1 (a_p a) * field_at Ews t_dctx (DOT _litPtr) v2 (a_p a) *
  field_at Ews t_dctx (DOT _litBufferEnd) v3 (a_p a) * field_at Ews t_dctx (DOT _litBuffer) v4 (a_p a) *
  field_at Ews t_dctx (DOT _litBufferLocation) v5 (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a)) *
  data_at (x_sh1 x) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
  bit_src (x_sh2 x) (a_start a) (iw_s (a_i a)) * x_Ri x
  |-- tabs_seq (a_gv a) (a_p a) (a_ox a) (a_os a) 1 * lit_scratch_x (a_p a) (a_lxb a) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a)) *
      data_at_ Tsh (tptr tuchar) (a_vlp a) * data_at_ Tsh (tarray t_seq 8) (a_vsqs a) *
      data_at_ Tsh t_seqstate (a_vss a) * data_at_ Tsh t_seq (a_vs a) * data_at_ Tsh t_seq (a_vs1 a).
Proof.
  intros (Hos & _ & _ & Heq & _) (Hxz & Hxl & Hxb & _). rewrite Heq, Hos, Hxz.
  sep_apply (lgx_lit_rel (a_p a) v1 v2 v3 v4 v5 (a_lxb a) Hxl Hxb).
  sep_apply (lgx_ss2 (a_gv a) (iw_s (a_i a)) (a_start a) dpos dlo dst (x_tp x) drp (a_vss a)).
  sep_apply (HTE (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x)).
  sep_apply (data_at_data_at_ Tsh (tptr tuchar) lpv (a_vlp a)).
  sep_apply (data_at_data_at_ Tsh (tarray t_seq 8) rv (a_vsqs a)).
  sep_apply (data_at_data_at_ Tsh t_seq s1 (a_vs1 a)).
  cancel.
Qed.

(* do { body } while (0) *)
Lemma lgx_do0 {Espec: OracleKind} {cs: compspecs} (Delta: tycontext) (P: environ -> mpred) (body: statement)
    (R: ret_assert) :
  semax Delta P body (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop body Sbreak) R.
Proof.
  intros H. apply semax_loop with (RA_normal R); [exact H|].
  eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert. cbv beta iota.
  apply andp_left2, derives_refl.
Qed.

Lemma lgx_upd_same {A} {d: Inhabitant A} (l: list A) (i: Z) :
  0 <= i < Zlength l -> upd_Znth i l (Znth i l) = l.
Proof.
  intros Hi. apply Znth_eq_ext; [rewrite upd_Znth_Zlength; lia|].
  intros k Hk. rewrite upd_Znth_Zlength in Hk by lia.
  destruct (Z.eq_dec k i) as [->|Hne]; [rewrite upd_Znth_same by lia; reflexivity|].
  rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma lgx_err70 : dec_err (Int64.unsigned (Int64.repr (-70))).
Proof.
  unfold dec_err. split; [reflexivity|].
  unfold ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; compute; congruence.
Qed.

Lemma lg_main_x1_ok : P_X1.
Proof.
  intros HTE HXS HINV HTAIL Espec a x w dd R HG Hla Hpend Hlfx Hlx Hcut HRn HRr.
  apply (lg_R_concrete a); [exact HRr|]. rewrite HRn. unfold lg_R.
  unfold MD. rewrite lgx_prop1. Intros.
  rename H into HMD.
  destruct (HINV a x w dd Hla Hpend Hlfx Hlx HMD) as (HXP & Hk8 & Hslot & Hctx & Hpos & Hinv0 & HLI').
  destruct w as [id ie pos blo st drep ring q K j sw c pp];
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in *.
  destruct dd as [dpos dlo dst drp dll dml doff].
  unfold lg_cut in Hcut; cbn [w_sw w_j w_q] in Hcut.
  destruct (a_l a) as [| |lb0|lb] eqn:El; try contradiction.
  destruct Hcut as [-> Hcut].
  destruct (Znth 0 q) as [[ll ml] off] eqn:Eq0. cbn [fst] in Hcut.
  assert (HMD' := HMD).
  unfold MD_P, LI_P in HMD'; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp
     d_pos d_lo d_st d_rep d_ll d_ml d_off d_e fold_right app] in HMD'.
  destruct HMD' as (Hie0 & Hidnb & Hq8 & Hql & Hring & Hqs & Hds & Hpp & Hes & Hed & Hmdl & Hxi & Hmain & Hid &
                    Hds' & Hqs1 & Hmdl' & Hxi' & _).
  assert (HXP' := HXP). destruct HXP' as (Hie & _ & _ & Hll & Hml & Hoff & _).
  destruct (HXS a x ie K j false c ll ml off Hla Hpend Hlfx HXP) as (_ & _ & HX1).
  specialize (HX1 lb El eq_refl Hcut).
  (* the exact model: BlkSeqLoopLongXE.xl_exec_X1 (leftover check, lsdbs, execSequence on litExtraBuffer) *)
  pose proof (BlkSeqLoopLongXE.xl_exec_X1 a (x_t x) (id + 1) K c drp j lb dpos dlo dst
                (tl q ++ [(dll, dml, doff)]) ll ml off Hctx Hpos El Hcut ltac:(lia) ltac:(lia) ltac:(lia) Hinv0)
    as HXX.
  cbv zeta in HXX.
  unfold LI_L, MD_S, S_fix, L_seq, L_ex, L_base, lit_now;
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp
         d_pos d_lo d_st d_rep d_ll d_ml d_off app].
  rewrite (lgx_lit_fix_split a lb El).
  assert (Eli: lit_li a false j = lb + j) by (unfold lit_li; rewrite El; reflexivity).
  assert (Elim: lit_lim a false = lb + (a_n a - LITBUFFEREXTRASIZE)) by (unfold lit_lim; rewrite El; reflexivity).
  assert (Elb: lit_base a false = a_ob a) by (unfold lit_base; rewrite El; reflexivity).
  rewrite Eli, Elim, Elb in *.
  Intros.
  unfold lg_main_x1.
  assert (Hla' := Hla).
  destruct Hla' as ((Hosh & HoN & HoN32 & Hod & Hocap & HodN) & Hiw & Hlits & Hbsm & Hnbsm & Hnbr & Hnb0 &
                    Hso & Hrep & Hfe & Hc0 & Hlay).
  rewrite El in Hlits. destruct Hlits as (_ & Hn & Hn65 & Hdlb & Hlbe & Hlsub).
  assert (Hes' := Hes). destruct Hes' as (HK0 & HKE & Hj & Hjsw & Hcl & Hun). rewrite El in Hjsw.
  pose proof (lgx_E_le a Hla) as HEle.
  destruct Hring as [Hr8 _].
  clear HXS HINV HMD Hmdl Hmdl' Hds Hds' Hxi Hxi' Hinv0.
  assert_PROP (isptr (a_ob a)) as Hob by entailer!.
  assert_PROP (is_pointer_or_null (fs_dictEnd (a_fs a))) as Hpde by entailer!.
  forward. forward. forward.
  { entailer!. clear - Hob. destruct (a_ob a); try contradiction. simpl.
    apply prop_right. destruct (peq b b); [reflexivity | congruence]. }
  rewrite lgx_sub by (auto; unfold a_n, a_d, a_cap, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia).
  set (lo := lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j)) in *.
  set (k8 := id mod 8).
  assert (Hk8r: 0 <= k8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hlo0: 0 <= lo) by (unfold lo; lia).
  assert (Hloj: j + lo = a_n a - LITBUFFEREXTRASIZE) by (unfold lo; lia).
  assert (Hrl: Zlength (ring_vals ring) = 8)
    by (unfold ring_vals; rewrite Zlength_map; exact Hr8).
  assert (Hland: Z.land (id - 8) (8 - 1) = k8).
  { change (8 - 1) with (Z.ones 3). rewrite Z.land_ones by lia. unfold k8.
    replace (id - 8) with (id + (-1) * 2 ^ 3) by lia. rewrite Z.mod_add by lia. reflexivity. }
  assert (Hland': 0 <= Z.land (id - 8) (8 - 1) < 8) by (rewrite Hland; lia).
  (* the leftover literals are defined (ex_def) *)
  assert (Xcap: 0 < a_cap a) by (unfold a_d, a_cap, a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
  assert (Xsrc: Forall is_byte_val (sublist (lb + j) (lb + j + lo) c)).
  { apply (xd_sub _ (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH));
      try (unfold lo, a_d, a_cap, a_n, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; lia).
    apply (ex_def_lit_S a (x_xc x) lb K j c); auto.
    destruct Hlfx as (_ & _ & _ & _ & Hxc); exact Hxc. }
  freeze [2;3;4;5;6;7;8;9;14;15;16;17;18;19;20] FR.
  forward_if (EX c1: list val,
    PROP (Zlength c1 = Zlength c; lo = 0 -> c1 = c;
          0 < lo -> lo <= a_E a - (a_d a + K) /\ copied c c1 (a_d a + K) (lb + j) lo;
          0 < lo -> c1 = lsdbs c (a_d a + K) (lb + j) lo)
    LOCAL (temp _leftoverLit (Vlong (Int64.repr lo));
     temp _seqAdvance (Vint (Int.repr (a_adv a))); temp _seqNb (Vint (Int.repr id));
     temp _prefetchPos (Vlong (Int64.repr pp));
     temp _op (offset_val (a_d a + K + lo) (a_ob a));
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
     data_at Tsh (tarray t_seq 8) (upd_Znth k8 (ring_vals ring) (seqrep3 (ll - lo, ml, off))) (a_vsqs a);
     field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (lit_code a false))) (a_p a);
     data_at Ews (tarray tuchar LITEXTRA_N) (x_xc x) (lit_extra (a_p a));
     data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c1 (a_ob a);
     zstd_globals (a_gv a); ext_res (a_x a)))%assert.
  - assert (Hlp: 0 < lo).
    { destruct (Z.eq_dec lo 0) as [Hz|]; [|lia]. exfalso.
      match goal with H: Int64.repr lo <> Int64.zero |- _ => rewrite Hz in H; apply H; reflexivity end. }
    destruct (Z_lt_ge_dec (a_E a - (a_d a + K)) lo) as [Herr|Hok].
    + eapply semax_seq; [| apply semax_ff].
      apply lgx_do0. forward_if.
      { apply prop_right. clear - Hob. unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction.
        simpl. destruct (peq b b); [reflexivity | congruence]. }
      { apply dec_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
        match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
        * apply ENTAIL_refl.
        * forward_if True. { contradiction. } { forward. entailer!. }
          forward. Intros. apply ENTAIL_refl.
        * apply dec_skipbreak_seq. apply dec_skipbreak_seq.
          unfold la_post in POSTCONDITION. forward.
          assert (HXE: XERR a c) by (destruct HX1 as [HX1' _]; exact (HX1' Hlp Herr)).
          Exists (Int64.unsigned (Int64.repr (-70))) c (a_rep a).
          rewrite Int64.repr_unsigned.
          thaw FR.
          sep_apply (lgx_rel HTE a x (offset_val (lb + j) (a_ob a)) (ring_vals ring) dpos dlo dst drp
                       (seqrep dll dml doff) (Vlong (Int64.repr (a_n a))) (offset_val lb (a_ob a))
                       (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a)) (offset_val lb (a_ob a))
                       (Vint (Int.repr (lit_code a false))) Hlfx Hlx).
          replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
          apply andp_right; [apply prop_right | unfold a_x, a_ob; cancel].
          assert (HE: is_error_code (Int64.unsigned (Int64.repr (-70))) = true) by reflexivity.
          split; [apply Int64.unsigned_range_2|]. split; [lia|]. split; [exact Hrep|].
          destruct HXE as [Hu [Hm Hb]]. split; [exact Hu|]. rewrite HE. split; [discriminate|].
          split; [intros Hv; specialize (Hm Hv); destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; auto|].
          split; [intros _; apply lgx_err70|]. split; [exact Hb|].
          split; [apply xl_exact_none; [exact HE | exact (proj1 HXX Hlp Herr)]|]. reflexivity. }
      { exfalso. match goal with H: typed_false tint _ |- _ =>
          change (oa_base (a_o a)) with (a_ob a) in H;
          rewrite lgx_gt in H by (auto; unfold a_n, a_d, a_cap, a_E, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia);
          replace (a_E a - (a_d a + K) <? lo) with true in H by (symmetry; apply Z.ltb_lt; lia);
          discriminate H end. }
    + match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
      * apply lgx_do0. forward_if.
        { apply prop_right. clear - Hob. unfold a_ob in *. destruct (oa_base (a_o a)); try contradiction.
          simpl. destruct (peq b b); [reflexivity | congruence]. }
        { exfalso. match goal with H: typed_true tint _ |- _ =>
            change (oa_base (a_o a)) with (a_ob a) in H;
            rewrite lgx_gt in H by (auto; unfold a_n, a_d, a_cap, a_E, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH in *; rep_lia);
            replace (a_E a - (a_d a + K) <? lo) with false in H by (symmetry; apply Z.ltb_ge; lia);
            discriminate H end. }
        { forward. entailer!. }
      * abbreviate_semax. forward.
        rewrite <- Hcl.
        assert_PROP (field_compatible (tarray tuchar (Zlength c)) [] (a_ob a)) as Hfc by entailer!.
        assert (Hb1: a_d a + K + lo <= Zlength c /\ lb + j + lo + WILDCOPY_OVERLENGTH <= Zlength c).
        { unfold lo. unfold a_d, a_cap, a_n, WILDCOPY_OVERLENGTH in *. lia. }
        assert (Hfa1: field_address0 (tarray tuchar (Zlength c)) (SUB (a_d a + K)) (a_ob a) =
                      offset_val (a_d a + K) (a_ob a)).
        { rewrite arr_field_address0 by (auto; unfold a_d in *; lia). change (sizeof tuchar) with 1. f_equal; lia. }
        assert (Hfa2: field_address0 (tarray tuchar (Zlength c)) (SUB (lb + j)) (a_ob a) =
                      offset_val (lb + j) (a_ob a)).
        { rewrite arr_field_address0 by (auto; unfold WILDCOPY_OVERLENGTH in *; lia). change (sizeof tuchar) with 1. f_equal; lia. }
        forward_call (a_gv a, oa_sh (a_o a), a_ob a, c, lb + j, a_d a + K, lo).
        { clear HX1 HLI' HRn. unfold lo in *. unfold a_d, a_cap, a_n, WILDCOPY_OVERLENGTH in *. lia. }
        Intros c1.
        assert (Hzk: forall d, @Znth _ d k8 (ring_vals ring) = seqrep3 (ll, ml, off)).
        { intros d. unfold ring_vals. rewrite Znth_map by lia. unfold k8. rewrite Hslot. reflexivity. }
        forward.
        { rewrite Hland, Hzk. entailer!. }
        { entailer!. rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia). unfold LONGNBSEQ in *; rep_lia. }
        rewrite Hland, Hzk.
        change (let (x0, _) := seqrep3 (ll, ml, off) in x0) with (Vlong (Int64.repr ll)).
        forward.
        { entailer!. rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia). unfold LONGNBSEQ in *; rep_lia. }
        rewrite Hland, Hzk.
        rewrite lgx_sub64 by (unfold lo, a_n, LITBUFFEREXTRASIZE, LL_VMAX, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
        change (Vlong (Int64.repr (ll - lo)), snd (seqrep3 (ll, ml, off))) with (seqrep3 (ll - lo, ml, off)).
        forward.
        rewrite lgx_add by (auto; unfold lo, a_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia).
        Exists c1. rewrite Hcl. entailer!.
        split; [lia|]. unfold copied. repeat split; auto.
  - assert (Hz: lo = 0).
    { match goal with H: Int64.repr lo = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by
          (unfold lo, a_n, LITBUFFEREXTRASIZE, ZSTD_BLOCKSIZE_MAX in *; rep_lia); exact H end. }
    forward. Exists c.
    assert (Hu: upd_Znth k8 (ring_vals ring) (seqrep3 (ll - lo, ml, off)) = ring_vals ring).
    { rewrite Hz, Z.sub_0_r.
      replace (seqrep3 (ll, ml, off)) with (Znth k8 (ring_vals ring))
        by (unfold ring_vals; rewrite Znth_map by lia; unfold k8; rewrite Hslot; reflexivity).
      apply lgx_upd_same; lia. }
    rewrite Hu. entailer!.
    first [f_equal; lia | split; [intros; lia | f_equal; lia]].
  - Intros c1. rename H2 into Hc1x.
    assert (Hid8: 8 <= id /\ ie = id - 8).
    { unfold main_ph, a_adv in Hmain. cbn [w_id w_ie] in Hmain. lia. }
    forward.
    assert_PROP (isptr (lit_extra (a_p a))) as Hxp by entailer!.
    assert (Hle: lit_extra (a_p a) = offset_val 30380 (a_p a)).
    { revert Hxp. unfold lit_extra, field_address. destruct (field_compatible_dec _ _ _); [reflexivity | intros []]. }
    rewrite <- Hle.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'7 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
    { forward. entailer!. }
    { exfalso. match goal with H: Int.lt _ _ = false |- _ => revert H; vm_compute; intros Hc; discriminate Hc end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'8 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
    { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc; discriminate Hc end]. }
    { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'8 (Vint (Int.repr 65536)) :: L) (SEPx S))) end.
      { forward. forward. entailer!. }
      { exfalso. first [lia | match goal with H: Int.lt _ _ = _ |- _ => revert H; vm_compute; intros Hc; discriminate Hc end]. } }
    forward. forward.
    assert (Hlbe2: force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
                     (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer (a_p a)) (Vint (Int.repr 65536))) =
                   offset_val 65536 (lit_extra (a_p a))).
    { clear - Hle Hxp. rewrite Hle in *. apply lgx_extra_end.
      destruct (a_p a); try contradiction; simpl; auto. }
    rewrite Hlbe2.
    assert (Hnb': 0 < a_nb a) by lia.
    assert (Hk1: 0 <= K + lo /\ a_d a + (K + lo) <= a_E a).
    { destruct (Z.eq_dec lo 0) as [Hz|Hz]; [rewrite Hz; lia|]. destruct (H1 ltac:(lia)) as [Hle1 _]. lia. }
    destruct (lgx_exec_pre a (K + lo) c1 Hla Hnb' (proj1 Hk1) (proj2 Hk1) ltac:(lia))
      as (Hc32 & Hps & HEc & Hext & Hfps & Hfvs & Hfde).
    (* what execSequence reads: the history and the leftover copy, the extDict, litExtraBuffer *)
    assert (Xd1: ex_def a (K + lo) (j + lo) true c1).
    { destruct (Z.eq_dec lo 0) as [Hz|Hz].
      - rewrite (H0 Hz), Hz, Z.add_0_r. exact Hed.
      - destruct (H1 ltac:(lia)) as (_ & (Hcl1 & _ & Hcb1 & Hcu1)).
        assert (Hd0: 0 <= a_d a) by (destruct Hla as ((_ & _ & _ & Hd & _) & _); exact Hd).
        apply (ex_def_step a K lo j (j + lo) false true c c1); try lia; auto.
        all: try (apply Hcb1; exact Xsrc).
        apply (xd_ub_frame c c1 (a_d a + K) (a_d a + K + lo)); [exact Hcu1 |].
        apply xd_Forall_rng; [lia | lia | apply Hcb1; exact Xsrc]. }
    destruct (ex_def_hist a (K + lo) (j + lo) true c1 Hla ltac:(lia) ltac:(lia) ltac:(lia) Xd1) as (Xdh1 & Xde1).
    replace (a_d a + (K + lo)) with (a_d a + K + lo) in Xdh1 by lia.
    assert (Xdl1: Forall is_byte_val (sublist 0 (65536 + WILDCOPY_OVERLENGTH) (x_xc x)))
      by (apply Forall_sublist; destruct Hlfx as (_ & _ & _ & _ & (_ & Hxb & _)); exact Hxb).
    rewrite Hfps, Hfvs. rewrite <- Hfde.
    rewrite (lgx_ring_join Tsh (ring_vals ring) k8 (seqrep3 (ll - lo, ml, off)) (a_vsqs a)) by lia.
    Intros.
    change (seqrep3 (ll - lo, ml, off)) with (seqrep (ll - lo) ml off).
    assert (Hxl: Zlength (x_xc x) = LITEXTRA_N) by (destruct Hlfx as (_ & _ & _ & _ & (Hx & _)); exact Hx).
    rewrite <- Hxl.
    change (data_at Ews (tarray tuchar (Zlength (x_xc x))) (x_xc x) (lit_extra (a_p a)))
      with (BlkSeqEXEC.lit_res (LitSep Ews (lit_extra (a_p a)) (x_xc x))).
    replace (oa_N (a_o a)) with (Zlength c1) by lia.
    assert (Hlp0: data_at Tsh (tptr tuchar) (lit_extra (a_p a)) (a_vlp a) =
                  data_at Tsh (tptr tuchar) (offset_val 0 (lit_extra (a_p a))) (a_vlp a))
      by (rewrite isptr_offset_val_zero by exact Hxp; reflexivity).
    rewrite Hlp0.
    forward_call (a_gv a, oa_sh (a_o a), a_ob a, c1, a_d a + K + lo, a_E a, Tsh, offset_val (24 * k8) (a_vsqs a),
                  ll - lo, ml, off, Tsh, a_vlp a, LitSep Ews (lit_extra (a_p a)) (x_xc x), 0, 65536, a_ps a, a_x a,
                  fs_dictEnd (a_fs a)).
    { rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia). unfold LONGNBSEQ in *; rep_lia. }
    { rewrite Hxl. unfold LL_VMAX, ML_VMAX, SIZE_MAX in Hll, Hml, Hoff.
      unfold LITEXTRA_N, LITBUFFEREXTRASIZE, WILDCOPY_OVERLENGTH.
      repeat split; try rep_lia; auto. }
    Intros vret. destruct vret as [[r c'] lp]. cbn [fst snd] in *.
    forward_call r.
    (* the exact model: the switch and execSequence on litExtraBuffer (BlkSeqLoopLongXE.xl_exec_X1) *)
    assert (Eli1x: lit_li a true (j + lo) = 0) by (unfold lit_li; rewrite El; lia).
    assert (Elim1x: lit_lim a true = 65536) by (unfold lit_lim; rewrite El; reflexivity).
    assert (Elsx: xl_lsrc a true = ls_l (LitSep Ews (lit_extra (a_p a)) (x_xc x)))
      by (unfold xl_lsrc; rewrite El; cbn [ls_l]; rewrite (proj1 Hlx); reflexivity).
    destruct HXX as [_ HXX]. rewrite Eli1x, Elim1x, Elsx in HXX.
    destruct (HXX c1 H0 (fun h => conj (proj1 (H1 h)) (Hc1x h)) r c' H5 H10) as [Xe Xo].
    destruct (is_error_code r) eqn:Er.
    + forward_if (PROP (False) LOCAL () SEP ()).
      * unfold la_post in POSTCONDITION. forward.
        assert (HXE: XERR a c').
        { destruct HX1 as [_ HX1'].
          specialize (HX1' c1 H0 H1 c' ltac:(lia)). cbv zeta in HX1'.
          assert (Els: lsrc a x = LitSep Ews (lit_extra (a_p a)) (x_xc x)) by (unfold lsrc; rewrite El; reflexivity).
          rewrite Els in HX1'. specialize (HX1' H4 H8).
          change (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j)) with lo in HX1'.
          assert (Eli1: lit_li a true (j + lo) = 0) by (unfold lit_li; rewrite El; lia).
          assert (Elim1: lit_lim a true = 65536) by (unfold lit_lim; rewrite El; reflexivity).
          rewrite Eli1, Elim1 in HX1'.
          destruct HX1' as [HX1' _]. apply HX1'; [symmetry; exact H5 | exact (proj1 (H6 eq_refl))]. }
        Exists r c' (a_rep a).
        thaw FR.
        unfold BlkSeqEXEC.lit_res. rewrite Hxl.
        sep_apply (lgx_ring_none ring (id mod 8) (seqrep (ll - lo) ml off) (a_vsqs a) Hk8r Hr8).
        sep_apply (lgx_rel HTE a x lp (ring_vals (upd_Znth (id mod 8) ring None)) dpos dlo dst drp
                     (seqrep dll dml doff) (Vlong (Int64.repr (a_n a))) (offset_val lb (a_ob a))
                     (offset_val (lb + (a_n a - LITBUFFEREXTRASIZE)) (a_ob a)) (offset_val lb (a_ob a))
                     (Vint (Int.repr 0)) Hlfx Hlx).
        replace (a_nb a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite H, Hcl.
        apply andp_right; [apply prop_right | unfold a_x, a_ob; cancel].
        split; [lia|]. split; [lia|]. split; [exact Hrep|].
        destruct HXE as [Hu [Hm Hb]]. split; [exact Hu|]. rewrite Er. split; [discriminate|].
        split; [intros Hv; specialize (Hm Hv); destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|]; auto|].
        split; [intros _; exact (proj2 (H6 eq_refl))|]. split; [exact Hb|].
        split; [apply xl_exact_none; [exact Er | exact (Xe eq_refl)]|]. reflexivity.
      * exfalso. match goal with H: Int.repr _ = Int.zero |- _ =>
          apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia;
          rewrite Int.unsigned_zero in H; lia end.
    + forward_if.
      { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
      assert (HXQ: XQ a x (ie + 1) (K + (ll + ml)) (j + ll) true c').
      { destruct HX1 as [_ HX1'].
        specialize (HX1' c1 H0 H1 c' ltac:(lia)). cbv zeta in HX1'.
        change (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j)) with lo in HX1'.
        assert (Eli1: lit_li a true (j + lo) = 0) by (unfold lit_li; rewrite El; lia).
        assert (Els: lsrc a x = LitSep Ews (lit_extra (a_p a)) (x_xc x)) by (unfold lsrc; rewrite El; reflexivity).
        assert (Elim1: lit_lim a true = 65536) by (unfold lit_lim; rewrite El; reflexivity).
        rewrite Eli1, Els, Elim1 in HX1'. specialize (HX1' H4 H8).
        destruct HX1' as [_ HX1'].
        destruct (H7 eq_refl) as (Hr & Hlp & Hu & Hrd).
        pose proof (H9 eq_refl) as Hxf. rewrite Hr in Hxf.
        apply HX1'.
        - symmetry. exact H5.
        - rewrite Hr in Hu. exact Hu.
        - exact Hxf.
        - rewrite Hr in Hrd. exact Hrd. }
      pose proof (HLI' _ _ _ _ HXQ (Xo eq_refl)) as HLIw.
      destruct (H7 eq_refl) as (Hr & Hlp & _). subst r lp.
      clear HX1 HLI' H4 H5 H6 H7 HXP.
      rewrite <- Hfps, <- Hfvs, Hfde.
      thaw FR.
      eapply semax_pre; [| apply (HTAIL Espec a x
        {| w_id := id; w_ie := ie; w_pos := pos; w_lo := blo; w_st := st; w_drep := drep; w_ring := ring;
           w_q := q; w_K := K; w_j := j; w_sw := false; w_c := c; w_pp := pp |}
        {| d_pos := dpos; d_lo := dlo; d_st := dst; d_rep := drp; d_ll := dll; d_ml := dml; d_off := doff |}
        (K + (ll + ml)) (j + ll) true c' (K + lo) (ll - lo + ml) _t'11 _oneSeqSize Hla Hpend Hlfx
        (or_introl eq_refl))].
      unfold XS. cbv zeta. rewrite (lgx_prop1 (LI_P _ _ _ ++ _)).
      apply lgx_ent_prop.
      { apply lgx_fr_app; [exact HLIw|].
        cbn [fold_right w_id w_pp]. repeat split; auto; lia. }
      sep_apply (lgx_ring_none ring k8 (seqrep (ll - lo) ml off) (a_vsqs a) Hk8r Hr8).
      unfold BlkSeqEXEC.lit_res, BlkSeqEXEC.lit_base. rewrite Hxl.
      rewrite H, Hcl.
      unfold lit_now, lit_fix, lit_li, lit_lim, lit_base, lit_code, L_seq, L_base, S_fix.
      rewrite El. cbn [w_id w_pp w_ring d_pos d_lo d_st d_rep d_ll d_ml d_off]. cbv [app].
      replace (j + ll - (a_n a - LITBUFFEREXTRASIZE)) with (0 + (ll - lo)) by lia.
      replace (a_d a + (K + lo)) with (a_d a + K + lo) by lia.
      unfold LOC_NOT_IN_DST, LITBUFFEREXTRASIZE.
      entailer!.
Qed.
