(* LOOP / long loop: the last literals and the result. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXP.
Local Open Scope logic.

(* the last copy (from `lastLLSize = litBufferEnd - litPtr` to the return) *)
Definition epi_last : statement := match lg_epi with Ssequence _ s => s | _ => Sskip end.

(* the state before the last copy: op = ostart + K', litPtr = lpv, litBufferEnd = lbe *)
Definition epi_mid (a: la) (K': Z) (lpv lbe: val) (code: Z) (xc c: list val) (fe': Z) (rep': Z * Z * Z)
    : environ -> mpred :=
  let gv := a_gv a in let p := a_p a in let i := a_i a in
  PROPx [] (LOCALx (temp _op (offset_val (a_d a + K') (a_ob a)) :: temp _litBufferEnd lbe :: L_base a)
   (SEPx [data_at Tsh (tptr tuchar) lpv (a_vlp a);
   data_at_ Tsh (tarray t_seq 8) (a_vsqs a); data_at_ Tsh t_seqstate (a_vss a);
   data_at_ Tsh t_seq (a_vs a); data_at_ Tsh t_seq (a_vs1 a);
   zstd_globals gv; pws_pred (a_W a); frame_fields p (a_fs a); tabs_seq gv p (a_ox a) (a_os a) fe';
   dent_of dent_def gv (a_ox a); field_at Ews t_dctx (DOT _entropy DOT _rep) (rep_vals rep') p;
   lit_fix a; field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr code)) p;
   data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra p);
   data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a);
   data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i); ext_res (a_x a)])).

Lemma epi_sub_ptr (b: block) (o: ptrofs) (si L: Z) :
  0 <= L <= Ptrofs.max_signed ->
  force_val (sem_binary_operation' Osub (tptr tuchar) (tptr tuchar) (offset_val (si + L) (Vptr b o))
               (offset_val si (Vptr b o))) = Vlong (Int64.repr L).
Proof.
  intros HL. simpl. unfold sem_sub_pp. rewrite if_true by auto. simpl.
  assert (E: Ptrofs.sub (Ptrofs.add o (Ptrofs.repr (si + L))) (Ptrofs.add o (Ptrofs.repr si)) = Ptrofs.repr L).
  { rewrite (Ptrofs.add_commut o), (Ptrofs.add_commut o (Ptrofs.repr si)), Ptrofs.sub_shifted.
    unfold Ptrofs.sub. apply Ptrofs.eqm_samerepr.
    replace L with ((si + L) - si) at 2 by lia.
    apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr. }
  rewrite E. unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia.
  rewrite Ptrofs.signed_repr by rep_lia. rewrite Z.quot_1_r.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma epi_sub_pp (b: block) (o: ptrofs) (x y: Z) :
  0 <= y - x <= Ptrofs.max_signed ->
  sem_sub_pp tuchar (Vptr b (Ptrofs.add o (Ptrofs.repr y))) (Vptr b (Ptrofs.add o (Ptrofs.repr x))) =
  Some (Vlong (Int64.repr (y - x))).
Proof.
  intros H. pose proof (epi_sub_ptr b o x (y - x) H) as E.
  replace (x + (y - x)) with y in E by lia. simpl in E.
  destruct (sem_sub_pp tuchar _ _); simpl in E; [congruence|discriminate].
Qed.

Lemma epi_ltu (b: block) (o: ptrofs) (E dK L: Z) :
  0 <= E - dK <= 2 ^ 63 - 1 -> 0 <= L <= 2 ^ 63 - 1 ->
  match both_long (fun n1 n2 : int64 => Some (bool2val (Int64.ltu n2 n1))) sem_cast_pointer sem_cast_pointer
          (Vlong (Int64.repr L))
          (force_val (sem_sub_pp tuchar (Vptr b (Ptrofs.add o (Ptrofs.repr E)))
                        (Vptr b (Ptrofs.add o (Ptrofs.repr dK))))) with
  | Some v' => v' | None => Vundef end = Vint (if E - dK <? L then Int.one else Int.zero).
Proof.
  intros H1 H2. rewrite epi_sub_pp by (unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus,
    Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; simpl; lia). simpl. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (E - dK) L), (E - dK <? L) eqn:Eb; try reflexivity; lia.
Qed.

(* for (;;break) { if (0) ...; } (the error-message macro): a no-op *)
Lemma epi_ifzero_seq {Espec: OracleKind} (P: list Prop) (Q: list localdef) (R: list mpred) (s c: statement)
    (R': ret_assert) :
  semax lg_Delta (PROPx P (LOCALx Q (SEPx R))) c R' ->
  semax lg_Delta (PROPx P (LOCALx Q (SEPx R)))
    (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) R'.
Proof.
  intros H. apply semax_seq with (PROPx P (LOCALx Q (SEPx R))); [|exact H].
  apply semax_loop with (PROPx P (LOCALx Q (SEPx R))).
  2: { eapply semax_pre; [|apply semax_break]. destruct R'; unfold loop2_ret_assert, overridePost. cbv beta iota.
       apply andp_left2, derives_refl. }
  apply semax_pre with (P' := |> PROPx P (LOCALx Q (SEPx R))).
  { apply andp_left2, now_later. }
  apply (semax_ifthenelse_PQR' _ (Vint Int.zero)).
  - reflexivity.
  - apply andp_left2. intro rho. unfold tc_expr. simpl. apply TT_right.
  - apply andp_left2. intro rho. unfold local, lift1. simpl. apply prop_right. reflexivity.
  - apply semax_extract_PROP. intros Ht. inv Ht.
  - apply semax_extract_PROP. intros _.
    eapply semax_post; [| | | | apply semax_skip].
    all: destruct R'; unfold normal_ret_assert, loop1_ret_assert, overridePost.
    + intros rho; simpl; apply andp_left2, derives_refl.
    + intros rho; simpl; apply andp_left2, FF_left.
    + intros rho; simpl; apply andp_left2, FF_left.
    + intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

(* la_post's PROP part *)
Definition epi_pp (a: la) (r: Z) (oc': list val) (rep': Z * Z * Z) : Prop :=
  let o := a_o a in let i := a_i a in let h := a_h a in
  0 <= r <= Int64.max_unsigned /\ Zlength oc' = oa_N o /\ rep_ok rep' /\
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
        rep' = rep2) \/
       (is_error_code r = true /\ oa_cap o < Zlength cnt)
   | None => True
   end) /\
  (is_error_code r = true -> dec_err r) /\
  (byte_cells (oa_c o) -> byte_cells (iw_c i) -> ext_bytes (hc_ext h) -> byte_cells oc').

Lemma epi_dec_err70 : dec_err (Int64.modulus - 70).
Proof.
  unfold dec_err, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [reflexivity|]. rewrite Int64.modulus_power. unfold Int64.zwordsize, Int64.wordsize, Wordsize_64.wordsize.
  simpl. lia.
Qed.

(* the literal fields back to scratch, litExtraBuffer still holding lxb (la_post's lit_scratch_x) *)
Lemma epi_scratch_x (a: la) (code: Z) (xc: list val) :
  xc = zbytes (a_lxb a) -> xl_lxb_ok a ->
  lit_fix a * field_at Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr code)) (a_p a) *
  data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) |-- lit_scratch_x (a_p a) (a_lxb a).
Proof.
  intros -> (Hn & Hb & _). unfold lit_fix, lit_scratch_x, lit_extra_at. rewrite <- litextra_data_at.
  rewrite prop_true_andp by (split; assumption).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferLocation) (Vint (Int.repr (code))) (a_p a)).
  sep_apply (field_at_field_at_ Ews t_dctx (DOT _litSize) (Vlong (Int64.repr (a_n a))) (a_p a)).
  destruct (a_l a).
  - sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)). sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
    cancel.
  - sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)). sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
    sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)). cancel.
  - sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)). sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
    sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)). cancel.
  - sep_apply (field_at_field_at_ Ews t_dctx (DOT _litPtr)). sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBufferEnd)).
    sep_apply (field_at_field_at_ Ews t_dctx (DOT _litBuffer)). cancel.
Qed.

(* la_post's last PROP: the exact clause of seqs_spec for the result r, the array oc' and the offsets rep' *)
Definition epi_x (a: la) (r: Z) (oc': list val) (rep': Z * Z * Z) : Prop :=
  seqs_exact (a_os a) (a_rep a) (a_l a) (a_lits a) (a_lxb a) (a_nb a) (a_o a) (a_i a) (a_h a) r oc' rep'.

Lemma epi_wvp (a: la) (K': Z) (c: list val) (R: mpred) :
  la_ok a -> 0 <= K' <= a_cap a ->
  data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a) * pws_pred (a_W a) * R |--
  weak_valid_pointer (offset_val (a_d a + K') (a_ob a)).
Proof.
  intros Hok HK. destruct Hok as ((Hsh & Hlen & HN & Hd & Hcap & HdN) & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  unfold a_cap, a_d, a_ob in *.
  destruct (Z.eq_dec (oa_cap (a_o a)) 0) as [E|E].
  - replace K' with 0 by lia. rewrite Z.add_0_r.
    apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. exact (H0 E).
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1.
    eapply derives_trans; [apply data_at_memory_block|].
    apply memory_block_weak_valid_pointer; [ | | auto]; rewrite sizeof_tarray_tuchar by lia; lia.
Qed.

Lemma epi_ptr_add (o: ptrofs) (x L: Z) :
  0 <= L <= Int64.max_unsigned ->
  Ptrofs.add (Ptrofs.add o (Ptrofs.repr x))
    (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tuchar)) (Ptrofs.of_int64 (Int64.repr L))) =
  Ptrofs.add o (Ptrofs.repr (x + L)).
Proof.
  intros HL. simpl Ctypes.sizeof. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

Lemma epi_ret (b: block) (o: ptrofs) (d K L: Z) :
  0 <= K -> 0 <= L <= Int.max_unsigned -> K + L <= 2 ^ 63 - 1 ->
  force_val (sem_sub_pp tuchar
    (Vptr b (Ptrofs.add (Ptrofs.add o (Ptrofs.repr (d + K)))
               (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tuchar)) (Ptrofs.of_int64 (Int64.repr L)))))
    (offset_val d (Vptr b o))) = Vlong (Int64.repr (K + L)).
Proof.
  intros HK HL HKL.
  assert (E: Ptrofs.add (Ptrofs.add o (Ptrofs.repr (d + K)))
               (Ptrofs.mul (Ptrofs.repr (Ctypes.sizeof tuchar)) (Ptrofs.of_int64 (Int64.repr L))) =
             Ptrofs.add o (Ptrofs.repr (d + (K + L)))).
  { simpl Ctypes.sizeof. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
    unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
    rewrite Ptrofs.add_assoc, ptrofs_add_repr. f_equal. f_equal. lia. }
  rewrite E. simpl offset_val. rewrite epi_sub_pp.
  - replace (d + (K + L) - d) with (K + L) by lia. reflexivity.
  - unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
    simpl. lia.
Qed.

Lemma epi_tc_null (a: la) (K': Z) (c: list val) (b: block) (o: ptrofs) (P: mpred) :
  la_ok a -> 0 <= K' <= a_cap a -> oa_base (a_o a) = Vptr b o ->
  (P |-- data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (Vptr b o) * pws_pred (a_W a) * TT) ->
  P |-- denote_tc_test_eq (Vptr b (Ptrofs.add o (Ptrofs.repr (a_d a + K')))) (Vlong (Int64.repr 0)).
Proof.
  intros Hok HK Hb HP.
  change (denote_tc_test_eq (Vptr b (Ptrofs.add o (Ptrofs.repr (a_d a + K')))) (Vlong (Int64.repr 0))) with
    (!! (Int64.repr 0 = Int64.zero) && weak_valid_pointer (Vptr b (Ptrofs.add o (Ptrofs.repr (a_d a + K'))))).
  apply andp_right; [apply prop_right; reflexivity |].
  eapply derives_trans; [exact HP|].
  pose proof (epi_wvp a K' c TT Hok HK) as W. unfold a_ob in W. rewrite Hb in W. exact W.
Qed.

Lemma epi_last_ok (Espec: OracleKind) (a: la) (K' si L: Z) (sb: val) (code: Z) (xc c: list val)
    (rep': Z * Z * Z) :
  la_ok a -> byte_cells xc -> xc = zbytes (a_lxb a) -> xl_lxb_ok a ->
  isptr sb -> 0 <= K' -> a_d a + K' <= a_E a -> a_E a <= a_d a + a_cap a ->
  0 <= L <= Int.max_unsigned ->
  (a_E a - (a_d a + K') < L -> epi_pp a (Int64.modulus - 70) c rep') ->
  (a_E a - (a_d a + K') < L -> xl_none a) ->
  (L <= a_E a - (a_d a + K') ->
   exists (ma: memmove_args) (F: mpred) (c': list val),
     mm_ok ma /\ mm_dst ma = offset_val (a_d a + K') (a_ob a) /\ mm_src ma = offset_val si sb /\ mm_len ma = L /\
     (data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a) *
      data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))
      |-- mm_pre ma * F) /\
     (mm_post ma * F |--
      data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c' (a_ob a) *
      data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))) /\
     epi_pp a (K' + L) c' rep' /\ epi_x a (K' + L) c' rep') ->
  semax lg_Delta (epi_mid a K' (offset_val si sb) (offset_val (si + L) sb) code xc c
                    (if a_nb a =? 0 then a_fe a else 1) rep') epi_last (lg_R a).
Proof.
  intros Hok Hxb Hxz Hxl Hsb HK HKE HEc HL Herr Hxn Hsucc. (* kept as a conjunction: VST's forward would substitute xc away *)
  assert (Hxz': xc = zbytes (a_lxb a) /\ True) by (split; [exact Hxz | exact I]); clear Hxz.
  assert (HN: a_d a + a_cap a <= oa_N (a_o a) /\ oa_N (a_o a) <= 2 ^ 63 - 1 /\ 0 <= a_d a).
  { destruct Hok as ((_ & _ & HN & Hd & _ & HdN) & _). unfold a_d, a_cap. lia. }
  destruct sb as [| | | | |bsb osb]; try contradiction.
  unfold epi_mid, L_base. cbv zeta. cbv beta iota delta [epi_last lg_epi]. unfold a_ob, lg_R, la_post in *.
  assert_PROP (isptr (oa_base (a_o a))) as Hobp. { entailer!. }
  destruct (oa_base (a_o a)) as [| | | | |bo bof] eqn:Hob; try contradiction.
  abbreviate_semax.
  forward.
  forward.
  { entailer!. simpl. destruct (peq bsb bsb); [reflexivity | contradiction]. }
  rewrite epi_sub_ptr by rep_lia.
  destruct (Z_lt_le_dec (a_E a - (a_d a + K')) L) as [Hlt|Hle].
  - lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
    + apply ENTAIL_refl.
    + forward_if.
      { apply prop_right. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
      * rewrite <- seq_assoc. apply dec_skipbreak_seq. rewrite <- seq_assoc. apply epi_ifzero_seq.
        rewrite <- seq_assoc. apply dec_skipbreak_seq. rewrite <- seq_assoc. apply dec_skipbreak_seq.
        forward.
        Exists (Int64.modulus - 70) c rep'.
        specialize (Herr Hlt). unfold epi_pp in Herr; cbv zeta in Herr.
        pose proof (xl_exact_none a (Int64.modulus - 70) c rep' eq_refl (Hxn Hlt)) as Hx.
        apply andp_right.
        { apply prop_right. destruct Herr as (A1&A2&A3&A4&A5&A6&A7&A8).
          refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj Hx _))))))))).
          f_equal. apply Int64.eqm_samerepr. exists (-1). unfold Int64.modulus. lia. }
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val si (Vptr bsb osb)) (a_vlp a)).
        sep_apply (epi_scratch_x a code xc (proj1 Hxz') Hxl).
        unfold a_x. cancel.
      * exfalso. rewrite epi_ltu in H by (unfold a_d, a_cap in *; rep_lia).
        destruct (_ <? _) eqn:Eb; [inv H|]. lia.
  - destruct (Hsucc Hle) as (ma & F & c' & Hmm & Hdst & Hsrc & Hlen & Hpre & Hpost & Hpp & Hx).
    lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + apply ENTAIL_refl.
    + forward_if.
      { apply prop_right. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
      * exfalso. rewrite epi_ltu in H by (unfold a_d, a_cap in *; rep_lia).
        destruct (_ <? _) eqn:Eb; [|inv H]. apply Z.ltb_lt in Eb. lia.
      * forward. apply ENTAIL_refl.
    + apply semax_if_seq. forward_if.
      { apply (epi_tc_null a K' c bo bof); auto. { unfold a_d, a_E, a_cap in *. lia. } cancel. }
      * forward.
        gather_SEP 14 13 15. replace_SEP 0 (mm_pre ma * F).
        { go_lower. eapply derives_trans; [|exact Hpre]. cancel. }
        Intros.
        forward_call ma.
        { apply prop_right. rewrite Hdst, Hsrc, Hlen. reflexivity. }
        gather_SEP 0 1.
        replace_SEP 0 (data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c' (Vptr bo bof) *
          data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
          data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))).
        { go_lower. eapply derives_trans; [|exact Hpost]. cancel. }
        Intros.
        forward.
        forward.
        { apply prop_right. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
        Exists (K' + mm_len ma) c' rep'.
        unfold epi_pp in Hpp; cbv zeta in Hpp.
        apply andp_right.
        { apply prop_right. destruct Hpp as (A1&A2&A3&A4&A5&A6&A7&A8).
          refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj Hx _))))))))).
          apply epi_ret; unfold a_d, a_E, a_cap in *; rep_lia. }
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val si (Vptr bsb osb)) (a_vlp a)).
        sep_apply (epi_scratch_x a code xc (proj1 Hxz') Hxl).
        unfold a_x. cancel.
      * inv H.
Qed.

Definition epi_head : statement := match lg_epi with Ssequence s _ => s | _ => Sskip end.
Lemma epi_split : lg_epi = Ssequence epi_head epi_last.
Proof. reflexivity. Qed.

(* not split (or switched already): the head is skipped *)
Lemma epi_nohead (Espec: OracleKind) (a: la) (xc: list val) (K j: Z) (sw: bool) (c: list val)
    (rep': Z * Z * Z) :
  la_ok a -> byte_cells xc -> xc = zbytes (a_lxb a) -> xl_lxb_ok a ->
  lit_code a sw <> LOC_SPLIT -> isptr (lit_base a sw) ->
  let L := lit_lim a sw - lit_li a sw j in
  0 <= K -> a_d a + K <= a_E a -> a_E a <= a_d a + a_cap a -> 0 <= L <= Int.max_unsigned ->
  (a_E a - (a_d a + K) < L -> epi_pp a (Int64.modulus - 70) c rep') ->
  (a_E a - (a_d a + K) < L -> xl_none a) ->
  (L <= a_E a - (a_d a + K) ->
   exists (ma: memmove_args) (F: mpred) (c': list val),
     mm_ok ma /\ mm_dst ma = offset_val (a_d a + K) (a_ob a) /\
     mm_src ma = offset_val (lit_li a sw j) (lit_base a sw) /\ mm_len ma = L /\
     (data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a) *
      data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))
      |-- mm_pre ma * F) /\
     (mm_post ma * F |--
      data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c' (a_ob a) *
      data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
      data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))) /\
     epi_pp a (K + L) c' rep' /\ epi_x a (K + L) c' rep') ->
  semax lg_Delta
    (PROPx [] (LOCALx (L_ex a K sw ++ L_base a) (SEPx (XI_S a xc K j sw c (if a_nb a =? 0 then a_fe a else 1) rep'))))
    lg_epi (lg_R a).
Proof.
  intros Hok Hxb Hxz Hxl Hcode Hb L HK HKE HEc HL Herr Hxn Hsucc.
  rewrite epi_split.
  apply semax_seq with (epi_mid a K (offset_val (lit_li a sw j) (lit_base a sw))
                          (offset_val (lit_li a sw j + L) (lit_base a sw)) (lit_code a sw) xc c
                          (if a_nb a =? 0 then a_fe a else 1) rep').
  2: { apply epi_last_ok; auto. }
  unfold XI_S, L_ex, L_base, lit_now, epi_head, epi_mid. cbv zeta. cbv beta iota delta [lg_epi]. cbn [app].
  Intros.
  abbreviate_semax.
  forward.
  forward_if.
  { exfalso. apply Hcode. unfold LOC_SPLIT.
    apply repr_inj_unsigned in H; auto;
    unfold lit_code, loc_code, LOC_NOT_IN_DST, LOC_IN_DST, LOC_SPLIT; destruct sw, (a_l a); rep_lia. }
  forward.
  destruct (lg_R a). cbn [tycontext.RA_normal]. unfold L_base. cbv zeta. subst L.
  replace (lit_li a sw j + (lit_lim a sw - lit_li a sw j)) with (lit_lim a sw) by lia.
  entailer!.
Qed.

Lemma epi_lit_extra (p: val) :
  field_compatible t_dctx (DOT _litBufferLocation) p ->
  isptr p /\ lit_extra p = offset_val (nested_field_offset t_dctx (DOT _litExtraBuffer)) p.
Proof.
  intros H. split; [destruct H; auto|].
  unfold lit_extra, field_address. rewrite if_true; [reflexivity|].
  destruct H as (H1 & H2 & H3 & H4 & H5). repeat split; auto.
  simpl. unfold in_members. simpl. repeat (first [left; reflexivity | right]).
Qed.

Lemma epi_lbe (p: val) :
  isptr p ->
  force_val (sem_binary_operation' Oadd (tarray tuchar 65568) tint
     (eval_field (Tstruct _ZSTD_DCtx_s noattr) _litExtraBuffer p) (Vint (Int.shl (Int.repr 1) (Int.repr 16)))) =
  offset_val LITBUFFEREXTRASIZE (offset_val (nested_field_offset t_dctx (DOT _litExtraBuffer)) p).
Proof.
  intros Hp. destruct p; try contradiction. reflexivity.
Qed.

(* split, not switched: the rest of the in-dst part first, then litExtraBuffer *)
Lemma epi_splithead (Espec: OracleKind) (a: la) (lb: Z) (xc: list val) (K j: Z) (c: list val)
    (rep': Z * Z * Z) :
  la_ok a -> byte_cells xc -> xc = zbytes (a_lxb a) -> xl_lxb_ok a -> a_l a = LSplit lb ->
  let L1 := lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j) in
  0 <= K -> a_d a + K <= a_E a -> a_E a = a_d a + a_cap a -> 0 <= L1 -> 0 <= lb + j -> lb + j + L1 <= oa_N (a_o a) ->
  Forall is_byte_val (sublist (lb + j) (lb + j + L1) c) ->
  (a_E a - (a_d a + K) < L1 -> epi_pp a (Int64.modulus - 70) c rep') ->
  (a_E a - (a_d a + K) < L1 -> xl_none a) ->
  (L1 <= a_E a - (a_d a + K) ->
   semax lg_Delta
     (epi_mid a (K + L1) (lit_extra (a_p a)) (offset_val LITBUFFEREXTRASIZE (lit_extra (a_p a))) LOC_SPLIT xc
        (mm_result c (oa_N (a_o a)) (lb + j) (a_d a + K) L1) (if a_nb a =? 0 then a_fe a else 1) rep')
     epi_last (lg_R a)) ->
  semax lg_Delta
    (PROPx [] (LOCALx (L_ex a K false ++ L_base a)
                 (SEPx (XI_S a xc K j false c (if a_nb a =? 0 then a_fe a else 1) rep'))))
    lg_epi (lg_R a).
Proof.
  intros Hok Hxb Hxz Hxl El L1 HK HKE HEc HL1 Hs1 Hs2 Hsrc Herr Hxn Hcont. (* kept as a conjunction: VST's forward would substitute xc away *)
  assert (Hxz': xc = zbytes (a_lxb a) /\ True) by (split; [exact Hxz | exact I]); clear Hxz.
  rewrite epi_split.
  unfold XI_S, L_ex, L_base, lit_now, lit_li, lit_lim, lit_base, lit_code, epi_head.
  rewrite El. cbv zeta. cbv beta iota delta [lg_epi]. cbn [app]. simpl loc_code.
  unfold a_ob, lg_R, la_post in *.
  Intros.
  assert_PROP (isptr (oa_base (a_o a))) as Hobp. { entailer!. }
  destruct (oa_base (a_o a)) as [| | | | |bo bof] eqn:Hob; try contradiction.
  abbreviate_semax.
  forward.
  apply semax_if_seq. forward_if.
  2: { exfalso. apply H. reflexivity. }
  clear H.
  forward.
  forward.
  { entailer!. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
  replace (lb + (a_n a - LITBUFFEREXTRASIZE)) with ((lb + j) + L1) by (unfold L1; lia).
  assert (HN: a_d a + a_cap a <= oa_N (a_o a) /\ oa_N (a_o a) <= 2 ^ 63 - 1 /\ 0 <= a_d a /\
              writable_share (oa_sh (a_o a)) /\ Zlength (oa_c (a_o a)) = oa_N (a_o a)).
  { destruct Hok as ((Hsh & Hlen & HN & Hd & _ & HdN) & _). unfold a_d, a_cap.
    split; [lia|]. split; [lia|]. split; [lia|]. split; assumption. }
  rewrite epi_sub_ptr by (unfold a_d, a_cap in *; rep_lia).
  destruct (Z_lt_le_dec (a_E a - (a_d a + K)) L1) as [Hlt|Hle].
  - lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
    + apply ENTAIL_refl.
    + forward_if.
      { apply prop_right. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
      * rewrite <- seq_assoc. apply dec_skipbreak_seq. rewrite <- seq_assoc. apply epi_ifzero_seq.
        rewrite <- seq_assoc. apply dec_skipbreak_seq. rewrite <- seq_assoc. apply dec_skipbreak_seq.
        forward.
        Exists (Int64.modulus - 70) c rep'.
        specialize (Herr Hlt). unfold epi_pp in Herr; cbv zeta in Herr.
        pose proof (xl_exact_none a (Int64.modulus - 70) c rep' eq_refl (Hxn Hlt)) as Hx.
        apply andp_right.
        { apply prop_right. destruct Herr as (A1&A2&A3&A4&A5&A6&A7&A8).
          refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj Hx _))))))))).
          f_equal. apply Int64.eqm_samerepr. exists (-1). unfold Int64.modulus. lia. }
        sep_apply (data_at_data_at_ Tsh (tptr tuchar) (offset_val (lb + j) (Vptr bo bof)) (a_vlp a)).
        sep_apply (epi_scratch_x a LOC_SPLIT xc (proj1 Hxz') Hxl).
        unfold a_x. cancel.
      * exfalso. rewrite epi_ltu in H by (unfold a_d, a_cap in *; rep_lia).
        destruct (_ <? _) eqn:Eb; [inv H|]. apply Z.ltb_ge in Eb. lia.
  - lazymatch goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    + apply ENTAIL_refl.
    + forward_if.
      { apply prop_right. simpl. destruct (peq bo bo); [reflexivity | contradiction]. }
      * exfalso. rewrite epi_ltu in H by (unfold a_d, a_cap in *; rep_lia).
        destruct (_ <? _) eqn:Eb; [|inv H]. apply Z.ltb_lt in Eb. lia.
      * forward. apply ENTAIL_refl.
    + rewrite <- seq_assoc. apply semax_if_seq. forward_if.
      { apply (epi_tc_null a K c bo bof); auto. { unfold a_d, a_E, a_cap in *. lia. } cancel. }
      * forward.
        assert_PROP (Zlength c = oa_N (a_o a)) as Hlc. { entailer!. }
        forward_call (mm_within (oa_sh (a_o a)) (Vptr bo bof) (oa_N (a_o a)) c (lb + j) (a_d a + K) L1).
        { unfold mm_ok. destruct HN as (HN1&HN2&HN3&Hsh&_). refine (conj Hsh (conj Hlc _)).
          clear Hcont Herr. repeat split; try rep_lia. apply xd_bv. exact Hsrc. }
        forward.
        forward.
        clear Herr.
        repeat rewrite <- seq_assoc. apply semax_if_seq. forward_if.
        2: { exfalso. revert H0. vm_compute. discriminate. }
        forward. repeat rewrite <- seq_assoc. apply semax_if_seq. forward_if.
        { exfalso. revert H1. vm_compute. discriminate. }
        repeat rewrite <- seq_assoc. apply semax_if_seq. forward_if.
        2: { exfalso. revert H2. vm_compute. discriminate. }
        forward. forward. forward.
        assert_PROP (field_compatible t_dctx (DOT _litBufferLocation) (a_p a)) as Hfc. { entailer!. }
        destruct (epi_lit_extra _ Hfc) as [Hpp Hxe].
        rewrite epi_lbe by auto.
        change 30380 with (nested_field_offset t_dctx (DOT _litExtraBuffer)).
        rewrite <- Hxe.
        rewrite epi_ptr_add by (unfold L1 in *; rep_lia).
        eapply semax_pre; [| apply (Hcont Hle)].
        unfold epi_mid, L_base, mm_post, a_ob. cbv zeta. rewrite Hob.
        replace (a_d a + (K + L1)) with (a_d a + K + L1) by lia.
        clear Hcont. entailer!.
      * inv H.
Qed.

(* ===================== byte arrays: carving a range, a disjoint memmove ===================== *)

Lemma epi_split3 (sh: share) (n a L: Z) (v: list val) (p: val) :
  field_compatible (tarray tuchar n) [] p -> 0 <= a -> 0 <= L -> a + L <= n -> Zlength v = n ->
  data_at sh (tarray tuchar n) v p =
  data_at sh (tarray tuchar a) (sublist 0 a v) p *
  data_at sh (tarray tuchar L) (sublist a (a + L) v) (offset_val a p) *
  data_at sh (tarray tuchar (n - (a + L))) (sublist (a + L) n v) (offset_val (a + L) p).
Proof.
  intros Hfc Ha HL HaL Hv.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar sh n a (a + L) v p) by lia.
  replace (a + L - a) with L by lia.
  rewrite !field_address0_offset.
  - simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l. reflexivity.
  - apply field_compatible0_cons. split; [simpl; lia|]. first [exact Hfc | apply field_compatible_field_compatible0, Hfc].
  - apply field_compatible0_cons. split; [simpl; lia|]. first [exact Hfc | apply field_compatible_field_compatible0, Hfc].
Qed.

(* the array after a disjoint copy of L bytes to offset di *)
Definition epi_put (vd: list val) (di: Z) (bs: list val) : list val :=
  sublist 0 di vd ++ bs ++ sublist (di + Zlength bs) (Zlength vd) vd.

Lemma epi_mm_disj (shs shd: share) (Ns: Z) (vs: list val) (ps: val) (si: Z) (Nd: Z) (vd: list val) (pd: val)
    (di L: Z) :
  readable_share shs -> writable_share shd ->
  field_compatible (tarray tuchar Ns) [] ps -> field_compatible (tarray tuchar Nd) [] pd ->
  0 <= si -> 0 <= L -> si + L <= Ns -> Zlength vs = Ns -> 0 <= di -> di + L <= Nd -> Zlength vd = Nd ->
  L <= Int64.max_unsigned -> Forall is_byte_val (sublist si (si + L) vs) ->
  exists F: mpred,
    mm_ok (mm_disjoint shs shd (offset_val si ps) (offset_val di pd) L (sublist si (si + L) vs)) /\
    (data_at shs (tarray tuchar Ns) vs ps * data_at shd (tarray tuchar Nd) vd pd |--
     mm_pre (mm_disjoint shs shd (offset_val si ps) (offset_val di pd) L (sublist si (si + L) vs)) * F) /\
    (mm_post (mm_disjoint shs shd (offset_val si ps) (offset_val di pd) L (sublist si (si + L) vs)) * F |--
     data_at shs (tarray tuchar Ns) vs ps *
     data_at shd (tarray tuchar Nd) (epi_put vd di (sublist si (si + L) vs)) pd).
Proof.
  intros Hrs Hws Hfs Hfd Hsi HL HsL Hvs Hdi HdL Hvd HLm Hbv.
  exists (data_at shs (tarray tuchar si) (sublist 0 si vs) ps *
          data_at shs (tarray tuchar (Ns - (si + L))) (sublist (si + L) Ns vs) (offset_val (si + L) ps) *
          data_at shd (tarray tuchar di) (sublist 0 di vd) pd *
          data_at shd (tarray tuchar (Nd - (di + L))) (sublist (di + L) Nd vd) (offset_val (di + L) pd)).
  assert (Hb: Zlength (sublist si (si + L) vs) = L) by (rewrite Zlength_sublist; lia).
  split; [exact (conj Hrs (conj Hws (conj Hb (conj HLm (xd_bv _ Hbv)))))|]. split.
  - unfold mm_pre. rewrite (epi_split3 shs Ns si L vs ps), (epi_split3 shd Nd di L vd pd) by auto.
    sep_apply (data_at_data_at_ shd (tarray tuchar L) (sublist di (di + L) vd) (offset_val di pd)).
    cancel.
  - unfold mm_post.
    assert (Hpl: Zlength (epi_put vd di (sublist si (si + L) vs)) = Nd).
    { unfold epi_put. rewrite !Zlength_app, !Zlength_sublist by lia. lia. }
    rewrite (epi_split3 shs Ns si L vs ps) by auto.
    rewrite (epi_split3 shd Nd di L (epi_put vd di (sublist si (si + L) vs)) pd) by auto.
    unfold epi_put. rewrite Hb, Hvd.
    replace (sublist 0 di (sublist 0 di vd ++ sublist si (si + L) vs ++ sublist (di + L) Nd vd))
      with (sublist 0 di vd) by list_solve.
    replace (sublist di (di + L) (sublist 0 di vd ++ sublist si (si + L) vs ++ sublist (di + L) Nd vd))
      with (sublist si (si + L) vs) by list_solve.
    replace (sublist (di + L) Nd (sublist 0 di vd ++ sublist si (si + L) vs ++ sublist (di + L) Nd vd))
      with (sublist (di + L) Nd vd) by list_solve.
    cancel.
Qed.

Lemma epi_put_len (vd bs: list val) (di: Z) :
  0 <= di -> di + Zlength bs <= Zlength vd -> Zlength (epi_put vd di bs) = Zlength vd.
Proof. intros. unfold epi_put. list_solve. Qed.

Lemma epi_put_mid (vd bs: list val) (di: Z) :
  0 <= di -> di + Zlength bs <= Zlength vd -> sublist di (di + Zlength bs) (epi_put vd di bs) = bs.
Proof. intros. unfold epi_put. list_solve. Qed.

Lemma epi_put_out (vd bs: list val) (di: Z) :
  0 <= di -> di + Zlength bs <= Zlength vd -> unchanged_outside vd (epi_put vd di bs) di (di + Zlength bs).
Proof.
  intros H1 H2 i Hi Hn. unfold epi_put.
  destruct (Z_lt_le_dec i di).
  - rewrite Znth_app1 by list_solve. list_solve.
  - rewrite Znth_app2 by list_solve. rewrite Znth_app2 by list_solve. list_solve.
Qed.

Lemma epi_put_pre (vd bs: list val) (di lo hi: Z) :
  0 <= lo <= hi -> hi <= di -> di + Zlength bs <= Zlength vd -> sublist lo hi (epi_put vd di bs) = sublist lo hi vd.
Proof. intros. unfold epi_put. list_solve. Qed.

Lemma epi_mm_result (c: list val) (N si di n: Z) :
  Zlength c = N -> 0 <= si -> 0 <= n -> si + n <= N ->
  mm_result c N si di n = epi_put c di (sublist si (si + n) c).
Proof. intros. unfold mm_result, epi_put. rewrite Zlength_sublist by lia. f_equal. f_equal. f_equal; lia. Qed.

Lemma epi_zb_byte (l: list Z) : bytes_ok l -> Forall is_byte_val (zbytes l).
Proof.
  intros H. induction H; constructor; auto. exists x. split; [exact H | reflexivity].
Qed.

Lemma epi_zb_sub (l: list Z) (lo hi: Z) : sublist lo hi (zbytes l) = zbytes (sublist lo hi l).
Proof. rewrite sublist_map. reflexivity. Qed.

Lemma epi_bytes_sub (l: list Z) (lo hi: Z) : bytes_ok l -> bytes_ok (sublist lo hi l).
Proof. unfold bytes_ok. intros H. apply Forall_sublist, H. Qed.

Lemma epi_bc_sub (l: list val) (lo hi: Z) : byte_cells l -> byte_cells (sublist lo hi l).
Proof. unfold byte_cells. intros H. apply Forall_sublist, H. Qed.

Lemma epi_put_bytes (vd bs: list val) (di: Z) : byte_cells vd -> byte_cells bs -> byte_cells (epi_put vd di bs).
Proof.
  intros H1 H2. unfold epi_put, byte_cells in *.
  apply Forall_app. split; [apply Forall_sublist, H1|]. apply Forall_app. split; [exact H2 | apply Forall_sublist, H1].
Qed.

Lemma epi_ext_mono (a: la) (K T: Z) :
  K <= T ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (T <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
  (ext_clean (a_d a) (a_cap a) (a_x a) \/ (K <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))).
Proof. intros HKT [H|[H1 H2]]; [left; exact H | right; split; [lia | exact H2]]. Qed.

(* ===================== pure facts for the postcondition ===================== *)

Lemma epi_bytes (l: list val) : Forall is_byte_val l -> exists cnt, l = zbytes cnt /\ bytes_ok cnt.
Proof.
  induction l as [|v l IH]; intros H.
  - exists nil. split; [reflexivity | constructor].
  - inv H. destruct H2 as (z & Hz & ->). destruct (IH H3) as (cnt & -> & Hb).
    exists (z :: cnt). split; [reflexivity | constructor; auto].
Qed.

Lemma epi_peek_nonneg (s: list Z) (pos nb: Z) : 0 <= nb -> 0 <= bs_peek_s s pos nb.
Proof.
  intros Hnb. unfold bs_peek_s.
  destruct (pos <? 0) eqn:E1; [lia|]. apply Z.ltb_ge in E1.
  destruct (pos - nb >=? 0).
  - apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
  - apply Z.mul_nonneg_nonneg; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | apply Z.pow_nonneg; lia].
Qed.

Lemma epi_rd_nonneg (V: list Z) (pos nb e p: Z) : rd V pos nb = Some (e, p) -> 0 <= nb -> 0 <= e.
Proof.
  intros H Hnb. unfold rd in H. destruct (pos - nb <? 0); [discriminate|].
  injection H as <- _. apply epi_peek_nonneg, Hnb.
Qed.

Lemma epi_nth_nonneg (l: list Z) (i: nat) : Forall (fun x => 0 <= x) l -> 0 <= nth i l 0.
Proof.
  intros H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - rewrite Forall_forall in H. apply H, nth_In, Hi.
  - rewrite nth_overflow by exact Hi. lia.
Qed.

Lemma epi_dseqs_ml (tLL tOF tML: fse_table) (V: list Z) (k: nat) :
  forall sLL sOF sML pos l p,
  decode_seqs tLL tOF tML V k sLL sOF sML pos = Some (l, p) -> Forall (fun sq => 0 <= sq_ml sq) l.
Proof.
  assert (HB: Forall (fun x => 0 <= x) ML_base_tab) by (repeat constructor; lia).
  assert (HN: Forall (fun x => 0 <= x) ML_bits_tab) by (repeat constructor; lia).
  induction k as [|k IH]; intros sLL sOF sML pos l p H; cbn [decode_seqs] in H.
  - inv H. constructor.
  - destruct (rd V pos _) as [[eOF pos1]|] eqn:R1; [|discriminate].
    destruct (rd V pos1 (nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_bits_tab 0)) as [[eML pos2]|] eqn:R2;
      [|discriminate].
    assert (HeML: 0 <= eML) by (eapply epi_rd_nonneg; [exact R2 | apply epi_nth_nonneg, HN]).
    assert (Hml: 0 <= nth (Z.to_nat (fe_sym (fse_cell tML sML))) ML_base_tab 0 + eML).
    { pose proof (epi_nth_nonneg _ (Z.to_nat (fe_sym (fse_cell tML sML))) HB). lia. }
    destruct (rd V pos2 _) as [[eLL pos3]|] eqn:R3; [|discriminate].
    destruct k as [|k'].
    + inv H. constructor; [exact Hml | constructor].
    + destruct (rd V pos3 _) as [[uLL p4]|]; [|discriminate].
      destruct (rd V p4 _) as [[uML p5]|]; [|discriminate].
      destruct (rd V p5 _) as [[uOF p6]|]; [|discriminate].
      destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l' p']|] eqn:R7; [|discriminate].
      inv H. constructor; [exact Hml | eapply IH; exact R7].
Qed.

Lemma epi_exec_len (w: Z) (rep: Z * Z * Z) (hist: list Z) (seqs: list sequence) :
  forall lits out out' lits' rep2,
  exec_seqs w rep hist lits out seqs = Some (out', lits', rep2) -> Forall (fun sq => 0 <= sq_ml sq) seqs ->
  Zlength out' + Zlength lits' = Zlength out + Zlength lits + (sum_llml seqs - sum_ll seqs).
Proof.
  revert rep. induction seqs as [|sq rest IH]; intros rep lits out out' lits' rep2 H Hml.
  - simpl in H. inv H. simpl. lia.
  - simpl in H. inv Hml.
    destruct (sq_ll sq >? Zlength lits) eqn:Ell; [discriminate|].
    destruct (resolve_offset rep (sq_ll sq) (sq_ov sq)) as [[offset rep3]|]; [|discriminate].
    destruct (offset >? _); [discriminate|]. destruct (offset >? _); [discriminate|].
    specialize (IH _ _ _ _ _ _ H H3). rewrite IH. rewrite lz_copy_length.
    rewrite Z.gtb_ltb in Ell. apply Z.ltb_ge in Ell.
    rewrite Zlength_app, !Zlength_correct, firstn_length, skipn_length.
    simpl sum_llml. simpl sum_ll. rewrite !Zlength_correct in Ell. lia.
Qed.

(* the model's sequences (seqs_model's first part = DMg) execute to a content of K + (n - j) bytes *)
Lemma epi_cnt (a: la) (K j: Z) (sw: bool) (c: list val) (rep' rep2: Z * Z * Z) (cnt: list Z) :
  XM a K j sw c rep' ->
  seqs_model (a_os a) (iw_s (a_i a)) (a_nb a) (a_rep a) (hc_hist (a_h a)) (hc_out (a_h a)) (a_lits a)
    (hc_wsize (a_h a)) = Some (cnt, rep2) ->
  exists seqs out' lits', DMg a seqs /\
    exec_seqs (hc_wsize (a_h a)) (a_rep a) (hc_hist (a_h a)) (a_lits a) (hc_out (a_h a)) seqs =
      Some (out', lits', rep2) /\
    cnt = skipn (length (hc_out (a_h a))) (out' ++ lits') /\
    Zlength cnt = cnt_len a out' lits' /\ Zlength cnt = K + (a_n a - j).
Proof.
  intros HX Hm. unfold seqs_model in Hm.
  destruct (if a_nb a =? 0 then Some nil else _) as [seqs|] eqn:Hs; [|discriminate].
  destruct (exec_seqs _ _ _ _ _ seqs) as [[[out' lits'] rep3]|] eqn:He; [|discriminate].
  inv Hm. exists seqs, out', lits'.
  assert (HD: DMg a seqs) by exact Hs.
  assert (Hml: Forall (fun sq => 0 <= sq_ml sq) seqs).
  { destruct (a_nb a =? 0); [inv Hs; constructor|].
    destruct (a_os a) as [[[tLL tOF] tML]|]; [|discriminate].
    unfold decode_seq_stream in Hs.
    destruct (negb _); [discriminate|].
    destruct (rd _ _ _) as [[? ?]|]; [|discriminate].
    destruct (rd _ _ _) as [[? ?]|]; [|discriminate].
    destruct (rd _ _ _) as [[? ?]|]; [|discriminate].
    destruct (decode_seqs _ _ _ _ _ _ _ _ _) as [[l p]|] eqn:Hd; [|discriminate].
    destruct p; [|discriminate..]. inv Hs. eapply epi_dseqs_ml; exact Hd. }
  destruct (HX seqs HD) as (HK & Hj & _).
  pose proof (epi_exec_len _ _ _ _ _ _ _ _ _ He Hml) as HL.
  destruct (exec_seqs_app _ _ _ _ _ _ _ _ _ He) as [mid Hmid].
  assert (Hc: Zlength (skipn (length (hc_out (a_h a))) (out' ++ lits')) = Zlength mid + Zlength lits').
  { rewrite Hmid, <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O. simpl. apply Zlength_app. }
  assert (Hmid': Zlength out' = Zlength (hc_out (a_h a)) + Zlength mid) by (rewrite Hmid; apply Zlength_app).
  unfold cnt_len, a_n in *. repeat split; auto; lia.
Qed.

Lemma epi_pp_err (a: la) (K j: Z) (sw: bool) (c c': list val) (rep': Z * Z * Z) :
  la_ok a -> la_pend a -> XM a K j sw c rep' -> rep_ok rep' ->
  Zlength c' = oa_N (a_o a) -> unchanged_outside (oa_c (a_o a)) c' (a_d a) (a_d a + a_cap a) ->
  a_E a < a_d a + K + (a_n a - j) ->
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells c') ->
  epi_pp a (Int64.modulus - 70) c' rep'.
Proof.
  intros Hok Hpend HX Hrep Hlen Hun HE Hcb. unfold epi_pp. cbv zeta.
  assert (Herr: is_error_code (Int64.modulus - 70) = true) by reflexivity.
  refine (conj _ (conj Hlen (conj Hrep (conj Hun (conj _ (conj _ (conj (fun _ => epi_dec_err70) Hcb))))))).
  - unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. lia.
  - rewrite Herr. discriminate.
  - intros _. destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hm; [|exact I].
    intros Hb. right. split; [exact Herr|].
    destruct (epi_cnt a K j sw c rep' rep2 cnt HX Hm) as (sq & o' & l' & _ & _ & _ & _ & Hc).
    destruct Hpend as (_ & Hl). unfold a_E, a_d, a_cap in *.
    destruct (a_l a); lia.
Qed.

Ltac elia := unfold WILDCOPY_OVERLENGTH in *; lia.

Lemma epi_pp_ok (a: la) (K j: Z) (sw: bool) (c c': list val) (rep': Z * Z * Z) :
  la_ok a -> ex_safe a K j sw c -> ex_def a K j sw c -> rep_ok rep' -> XM a K j sw c rep' ->
  let T := K + (a_n a - j) in
  a_d a + T <= a_E a -> a_E a <= a_d a + a_cap a ->
  Zlength c' = oa_N (a_o a) ->
  unchanged_outside c c' (a_d a + K) (a_d a + T) ->
  (hist_def (oa_c (a_o a)) (a_d a) (a_ps a) (a_x a) ->
   (ext_clean (a_d a) (a_cap a) (a_x a) \/ (T <= a_bsm a /\ ext_far (a_d a) (a_cap a) (a_bsm a) (a_x a))) ->
     Forall is_byte_val (sublist (a_d a + K) (a_d a + T) c')) ->
  (lit_intact a j sw c -> sublist (a_d a + K) (a_d a + T) c' = zbytes (sublist j (a_n a) (a_lits a))) ->
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells c') ->
  epi_pp a T c' rep'.
Proof.
  intros Hok Hs Hd Hrep HX T HT HEc Hlen Hun Hdef Hmod Hcb'.
  assert (HKT: K <= T) by (destruct Hs as (_ & _ & Hj' & _); unfold T; lia).
  pose proof (epi_ext_mono a K T HKT) as Hmono.
  destruct Hs as (HK & HKE & Hj & _ & Hlc & Hun0 & _).
  destruct Hok as ((_ & Hl0 & HN & Hd0 & Hcap & HdN) & _).
  unfold a_E, a_d, a_cap, a_n, a_ps, a_x in *.
  assert (HTd: T = K + (Zlength (a_lits a) - j)) by reflexivity. clearbody T.
  assert (HT0: 0 <= T) by elia.
  assert (HTe: is_error_code T = false).
  { unfold is_error_code. apply Z.ltb_ge. elia. }
  (* the bytes [d, d+K) are c's *)
  assert (Hpre: sublist (oa_d (a_o a)) (oa_d (a_o a) + K) c' = sublist (oa_d (a_o a)) (oa_d (a_o a) + K) c).
  { apply Znth_eq_ext; [rewrite !Zlength_sublist; elia|]. intros i Hi.
    rewrite Zlength_sublist in Hi by elia. rewrite !Znth_sublist by elia.
    rewrite Hun; [reflexivity | elia | elia]. }
  assert (Hsplit: sublist (oa_d (a_o a)) (oa_d (a_o a) + T) c' =
                  sublist (oa_d (a_o a)) (oa_d (a_o a) + K) c ++ sublist (oa_d (a_o a) + K) (oa_d (a_o a) + T) c').
  { rewrite <- Hpre. rewrite <- sublist_split by elia. reflexivity. }
  assert (Hun1: forall lo hi, lo <= oa_d (a_o a) -> Z.min (match a_l a with LDst lb => lb | _ => oa_d (a_o a) + oa_cap (a_o a) end)
                  (oa_d (a_o a) + K + WILDCOPY_OVERLENGTH) <= hi -> oa_d (a_o a) + T <= hi ->
                  unchanged_outside (oa_c (a_o a)) c' lo hi).
  { intros lo hi H1 H2 H3 i Hi Hn. rewrite Hl0 in Hi.
    rewrite Hun by (try elia). apply Hun0; elia. }
  unfold epi_pp. cbv zeta.
  refine (conj _ (conj Hlen (conj Hrep (conj _ (conj _ (conj _ (conj _ Hcb'))))))).
  - unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. elia.
  - apply Hun1; elia.
  - intros _. split; [elia|]. split.
    + apply Hun1; elia.
    + intros Hh He. apply epi_bytes. rewrite Hsplit. apply Forall_app. split.
      * exact (proj1 Hd).
      * apply (Hdef Hh He).
  - intros Hv. destruct (seqs_model _ _ _ _ _ _ _ _) as [[cnt rep2]|] eqn:Hm; [|exact I].
    intros Hb. left.
    destruct (epi_cnt a K j sw c rep' rep2 cnt HX Hm) as (seqs & out' & lits' & HD & He & Hc & Hcl & HcT).
    unfold a_n in HcT.
    destruct (HX seqs HD) as (_ & _ & HX2).
    destruct (HX2 out' lits' rep2 He ltac:(rewrite <- Hcl; exact Hb) Hv ltac:(rewrite <- Hcl; elia))
      as (-> & blk & Hblk & Hsb & -> & -> & Hli).
    unfold a_d, a_n in Hsb.
    split; [exact HTe|]. split; [elia|]. split; [|reflexivity].
    rewrite Hc, Hsplit, Hsb, (Hmod Hli), <- app_assoc, skipn_app, skipn_all, Nat.sub_diag, skipn_O.
    simpl. rewrite map_app. reflexivity.
  - intros He. rewrite HTe in He. discriminate.
Qed.

(* not split: the literals left, copied as one block bs *)
Lemma epi_ok_put (a: la) (K j: Z) (sw: bool) (c bs: list val) (rep': Z * Z * Z) :
  la_ok a -> ex_safe a K j sw c -> ex_def a K j sw c -> rep_ok rep' -> XM a K j sw c rep' ->
  a_d a + K + (a_n a - j) <= a_E a -> a_E a <= a_d a + a_cap a ->
  Zlength bs = a_n a - j -> bs = zbytes (sublist j (a_n a) (a_lits a)) -> bytes_ok (a_lits a) ->
  (byte_cells (oa_c (a_o a)) -> byte_cells (iw_c (a_i a)) -> ext_bytes (a_x a) -> byte_cells bs) ->
  epi_pp a (K + (a_n a - j)) (epi_put c (a_d a + K) bs) rep'.
Proof.
  intros Hok Hs Hd Hrep HX HT HEc Hbl Hbs Hb Hbb.
  pose proof Hs as (HK & HKE & Hj & _ & Hcl & _ & Hcb).
  pose proof Hok as ((_ & _ & _ & Hd0 & _ & HdN) & _).
  assert (Hput: sublist (a_d a + K) (a_d a + K + (a_n a - j)) (epi_put c (a_d a + K) bs) = bs).
  { rewrite <- Hbl. apply epi_put_mid; unfold a_d, a_cap, a_E in *; lia. }
  apply epi_pp_ok with (sw := sw) (c := c); auto.
  - replace (a_d a + (K + (a_n a - j))) with (a_d a + K + (a_n a - j)) by lia. exact HT.
  - rewrite epi_put_len; [lia | unfold a_d in *; lia | rewrite Hbl; unfold a_d, a_cap, a_E in *; lia].
  - replace (a_d a + (K + (a_n a - j))) with (a_d a + K + Zlength bs) by lia.
    apply epi_put_out; unfold a_d, a_cap, a_E in *; lia.
  - intros _ _. replace (a_d a + (K + (a_n a - j))) with (a_d a + K + (a_n a - j)) by lia.
    rewrite Hput, Hbs. apply epi_zb_byte, epi_bytes_sub, Hb.
  - intros _. replace (a_d a + (K + (a_n a - j))) with (a_d a + K + (a_n a - j)) by lia.
    rewrite Hput, Hbs. reflexivity.
  - intros H1 H2 H3. apply epi_put_bytes; auto.
Qed.

Lemma epi_unch_sub (c0 c: list val) (lo hi x y: Z) :
  unchanged_outside c0 c lo hi -> Zlength c0 = Zlength c -> hi <= x -> 0 <= x <= y -> y <= Zlength c0 ->
  sublist x y c = sublist x y c0.
Proof.
  intros H Hl Hx Hxy Hy. apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros i Hi. rewrite Zlength_sublist in Hi by lia. rewrite !Znth_sublist by lia. apply H; lia.
Qed.

(* ===================== the exact clause (BlkSeqLoopLongXP) ===================== *)

Lemma epi_noerr (T: Z) : T <= 2 ^ 63 -> is_error_code T = false.
Proof. intros H. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

(* the last copy fails its capacity check: the model fails *)
Lemma epi_none_last (a: la) (K j: Z) (sw: bool) (c: list val) (rep': Z * Z * Z) (n: Z) :
  xl_ctx a -> xl_pos a K j sw c -> match a_l a with LSplit _ => sw = true | _ => True end ->
  xl_aft a K c rep' j sw -> n = lit_lim a sw - lit_li a sw j -> a_E a - (a_d a + K) < n -> xl_none a.
Proof.
  intros Hc Hp Hsw Ha Hn Hlt. pose proof (xl_epi_last a K c rep' j sw Hc Hp Hsw Ha) as Hl. cbv zeta in Hl.
  apply (proj1 Hl). subst n. exact Hlt.
Qed.

(* the last copy (the n literals left, bs, to op = d + K): the result K + n, the array after the copy *)
Lemma epi_exact_last (a: la) (K j: Z) (sw: bool) (c bs: list val) (rep': Z * Z * Z) (n: Z) :
  xl_ctx a -> xl_pos a K j sw c -> match a_l a with LSplit _ => sw = true | _ => True end ->
  xl_aft a K c rep' j sw -> n = lit_lim a sw - lit_li a sw j -> a_d a + K + n <= a_E a ->
  bs = sublist (lit_li a sw j) (lit_lim a sw) (xl_larr a sw c) -> is_error_code (K + n) = false ->
  epi_x a (K + n) (epi_put c (a_d a + K) bs) rep'.
Proof.
  intros Hc Hp Hsw Ha Hn HE Hbs Herr.
  pose proof (xl_epi_last a K c rep' j sw Hc Hp Hsw Ha) as Hl. cbv zeta in Hl. destruct Hl as [_ Hs].
  apply xl_exact_some; [exact Herr|].
  intros rb m body bo lr li lim sp ps ds de Hh.
  specialize (Hs ltac:(lia) rb m body bo lr li lim sp ps ds de Hh).
  destruct (xl_X a rb m body lr li lim sp ps ds de) as [[[mm op'] rep2]|]; [|exact Hs].
  destruct Hs as (A & B & C). subst bs n. split; [lia|]. split; [exact B | congruence].
Qed.

Ltac eal := unfold LITEXTRA_N, a_n, a_d, a_cap, WILDCOPY_OVERLENGTH, LITBUFFEREXTRASIZE in *; rep_lia.

Lemma lg_epi_ok : SEG_EPI.
Proof.
  intros Espec a xc K j sw c rep' Hok Hpend.
  unfold XI, XI_P.
  apply semax_extract_PROP; intros Hxc. apply semax_extract_PROP; intros Hs.
  apply semax_extract_PROP; intros Hd. apply semax_extract_PROP; intros Hrep.
  apply semax_extract_PROP; intros HX. apply semax_extract_PROP; intros Hxz.
  apply semax_extract_PROP; intros Hlxb. apply semax_extract_PROP; intros Haft.
  (* the exact steps' facts *)
  pose proof (xl_ctx_of a Hok Hlxb) as Hctx.
  assert (Hpos: xl_pos a K j sw c) by (destruct Hs as (A1 & A2 & A3 & A4 & A5 & _); exact (conj A1 (conj A2 (conj A3 (conj A4 A5))))).
  assert_PROP (field_compatible (tarray tuchar (oa_N (a_o a))) [] (a_ob a) /\
               field_compatible (tarray tuchar LITEXTRA_N) [] (lit_extra (a_p a)) /\
               field_compatible (tarray tuchar (iw_N (a_i a))) [] (iw_base (a_i a))) as Hfc.
  { unfold XI_S, lit_now, L_ex, L_base. cbv zeta. cbn [app]. entailer!. }
  destruct Hfc as (Hfo & Hfx & Hfi).
  pose proof Hok as Hok'.
  destruct Hok' as ((Hosh & Hol & HoN & Hod & Hocap & HodN) & (Hish & Hioff & HiN1 & HiN & Hil & _) & Hla & _).
  pose proof Hs as Hs'. destruct Hs' as (HK & HKE & Hj & Hsw & Hcl & Hun0 & Hcb).
  pose proof Hxc as Hxc'. destruct Hxc' as (Hxl & Hxb & Hxm).
  destruct Hla as (Hlb & Hn & Hlm). unfold ZSTD_BLOCKSIZE_MAX in Hn.
  destruct (a_l a) as [off| |lb|lb] eqn:El.
  - (* literals in the input array *)
    subst sw.
    assert (HE: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
    assert (HL: lit_lim a false - lit_li a false j = a_n a - j) by (unfold lit_lim, lit_li; rewrite El; lia).
    destruct Hlm as (Ho1 & Ho2 & Ho3 & Ho4).
    apply epi_nohead; auto.
    + unfold lit_code, LOC_SPLIT. rewrite El. discriminate.
    + unfold lit_base. rewrite El. apply Hfi.
    + lia.
    + rewrite HL. eal.
    + rewrite HL. intros Hlt. eapply epi_pp_err; eauto.
      * intros i Hi Hi2. apply Hun0; auto. eal.
      * lia.
    + rewrite HL. intros Hlt.
      exact (epi_none_last a K j _ c rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft
               (eq_sym HL) Hlt).
    + rewrite HL. intros Hle.
      destruct (epi_mm_disj (iw_sh (a_i a)) (oa_sh (a_o a)) (iw_N (a_i a)) (iw_c (a_i a)) (iw_base (a_i a))
                  (off + j) (oa_N (a_o a)) c (a_ob a) (a_d a + K) (a_n a - j))
        as (F & Hmm & Hpre & Hpost); auto; try eal.
      { apply (xd_sub _ off (off + a_n a)); try eal. unfold a_n. rewrite Ho3. apply epi_zb_byte, Hlb. }
      exists (mm_disjoint (iw_sh (a_i a)) (oa_sh (a_o a)) (offset_val (off + j) (iw_base (a_i a)))
                (offset_val (a_d a + K) (a_ob a)) (a_n a - j)
                (sublist (off + j) (off + j + (a_n a - j)) (iw_c (a_i a)))),
             (F * data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a))),
             (epi_put c (a_d a + K) (sublist (off + j) (off + j + (a_n a - j)) (iw_c (a_i a)))).
      split; [exact Hmm|]. split; [reflexivity|].
      split; [unfold lit_li, lit_base; rewrite El; reflexivity|]. split; [reflexivity|].
      split; [|split; [|split]].
      * rewrite <- sepcon_assoc.
        eapply derives_trans; [|apply sepcon_derives; [exact Hpre | apply derives_refl]]. cancel.
      * rewrite <- sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives; [exact Hpost | apply derives_refl]|]. cancel.
      * apply epi_ok_put with (sw := false); auto; try eal; try (rewrite Zlength_sublist; eal).
        -- unfold a_n in *.
           replace (off + j + (Zlength (a_lits a) - j)) with (Zlength (a_lits a) + off) by lia.
           replace (off + j) with (j + off) by lia.
           rewrite <- (sublist_sublist (Zlength (a_lits a)) (off + Zlength (a_lits a)) j off) by eal.
           rewrite Ho3. apply epi_zb_sub.
        -- intros _ Hib _. apply epi_bc_sub, Hib.
      * apply (epi_exact_last a K j _ c _ rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft (eq_sym HL)).
        -- lia.
        -- unfold lit_li, lit_lim, xl_larr; rewrite El; cbv beta iota; try rewrite Hxz; try unfold m in *.
           f_equal; unfold a_n in *; lia.
        -- apply epi_noerr; try unfold m in *; eal.
  - (* literals in litExtraBuffer *)
    subst sw.
    assert (HE: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
    assert (HL: lit_lim a false - lit_li a false j = a_n a - j) by (unfold lit_lim, lit_li; rewrite El; lia).
    apply epi_nohead; auto.
    + unfold lit_code, LOC_SPLIT. rewrite El. discriminate.
    + unfold lit_base. rewrite El. apply Hfx.
    + lia.
    + rewrite HL. eal.
    + rewrite HL. intros Hlt. eapply epi_pp_err; eauto.
      * intros i Hi Hi2. apply Hun0; auto. eal.
      * lia.
    + rewrite HL. intros Hlt.
      exact (epi_none_last a K j _ c rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft
               (eq_sym HL) Hlt).
    + rewrite HL. intros Hle.
      destruct (epi_mm_disj Ews (oa_sh (a_o a)) LITEXTRA_N xc (lit_extra (a_p a))
                  j (oa_N (a_o a)) c (a_ob a) (a_d a + K) (a_n a - j))
        as (F & Hmm & Hpre & Hpost); auto; try eal.
      all: try (apply writable_readable, writable_Ews).
      all: try (apply Forall_sublist; exact Hxb).
      exists (mm_disjoint Ews (oa_sh (a_o a)) (offset_val j (lit_extra (a_p a)))
                (offset_val (a_d a + K) (a_ob a)) (a_n a - j) (sublist j (j + (a_n a - j)) xc)),
             (F * data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))),
             (epi_put c (a_d a + K) (sublist j (j + (a_n a - j)) xc)).
      split; [exact Hmm|]. split; [reflexivity|].
      split; [unfold lit_li, lit_base; rewrite El; reflexivity|]. split; [reflexivity|].
      split; [|split; [|split]].
      * rewrite <- sepcon_assoc.
        eapply derives_trans; [|apply sepcon_derives; [exact Hpre | apply derives_refl]]. cancel.
      * rewrite <- sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives; [exact Hpost | apply derives_refl]|]. cancel.
      * apply epi_ok_put with (sw := false); auto; try eal; try (rewrite Zlength_sublist; eal).
        -- unfold a_n in *.
           replace (j + (Zlength (a_lits a) - j)) with (Zlength (a_lits a) + 0) by lia.
           replace j with (j + 0) at 1 by lia.
           rewrite <- (sublist_sublist (Zlength (a_lits a)) (Zlength (a_lits a)) j 0) by eal.
           rewrite Hxm. apply epi_zb_sub.
        -- intros _ _ _. apply epi_bc_sub, Hxb.
      * apply (epi_exact_last a K j _ c _ rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft (eq_sym HL)).
        -- lia.
        -- unfold lit_li, lit_lim, xl_larr; rewrite El; cbv beta iota; try rewrite Hxz; try unfold m in *.
           f_equal; unfold a_n in *; lia.
        -- apply epi_noerr; try unfold m in *; eal.
  - (* literals in dst *)
    subst sw.
    destruct Hlm as (Hl1 & Hl2 & Hl3).
    assert (HE: a_E a = lb) by (unfold a_E; rewrite El; reflexivity).
    assert (HL: lit_lim a false - lit_li a false j = a_n a - j) by (unfold lit_lim, lit_li; rewrite El; lia).
    apply epi_nohead; auto.
    + unfold lit_code, LOC_SPLIT, LOC_IN_DST. rewrite El. discriminate.
    + unfold lit_base. rewrite El. apply Hfo.
    + eal.
    + rewrite HL. eal.
    + rewrite HL. intros Hlt. eapply epi_pp_err; eauto.
      * intros i Hi Hi2. apply Hun0; auto. eal.
      * lia.
    + rewrite HL. intros Hlt.
      exact (epi_none_last a K j _ c rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft
               (eq_sym HL) Hlt).
    + rewrite HL. intros Hle.
      assert (Hbs: sublist (lb + j) (lb + j + (a_n a - j)) c = zbytes (sublist j (a_n a) (a_lits a))).
      { rewrite (epi_unch_sub (oa_c (a_o a)) c (a_d a) (Z.min (a_E a) (a_d a + K + WILDCOPY_OVERLENGTH)))
          by (auto; try lia; eal).
        unfold a_n in *.
        replace (lb + j + (Zlength (a_lits a) - j)) with (Zlength (a_lits a) + lb) by lia.
        replace (lb + j) with (j + lb) by lia.
        rewrite <- (sublist_sublist (Zlength (a_lits a)) (lb + Zlength (a_lits a)) j lb) by eal.
        rewrite Hl3. apply epi_zb_sub. }
      exists (mm_within (oa_sh (a_o a)) (a_ob a) (oa_N (a_o a)) c (lb + j) (a_d a + K) (a_n a - j)),
             (data_at Ews (tarray tuchar LITEXTRA_N) xc (lit_extra (a_p a)) *
              data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))),
             (epi_put c (a_d a + K) (sublist (lb + j) (lb + j + (a_n a - j)) c)).
      split; [unfold mm_ok; refine (conj Hosh (conj Hcl _)); repeat split; try eal;
              apply xd_bv; rewrite Hbs; apply epi_zb_byte, epi_bytes_sub, Hlb|].
      split; [reflexivity|].
      split; [unfold lit_li, lit_base; rewrite El; reflexivity|]. split; [reflexivity|].
      split; [|split; [|split]].
      * unfold mm_pre. cancel.
      * unfold mm_post. rewrite epi_mm_result by eal. cancel.
      * apply epi_ok_put with (sw := false); auto; try eal; try (rewrite Zlength_sublist; eal).
        intros H1 H2 H3. apply epi_bc_sub, Hcb; auto.
      * apply (epi_exact_last a K j _ c _ rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft (eq_sym HL)).
        -- lia.
        -- unfold lit_li, lit_lim, xl_larr; rewrite El; cbv beta iota; try rewrite Hxz; try unfold m in *.
           f_equal; unfold a_n in *; lia.
        -- apply epi_noerr; try unfold m in *; eal.
  - (* split *)
    destruct sw.
    + (* switched to litExtraBuffer *)
      assert (HE: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
      assert (HL: lit_lim a true - lit_li a true j = a_n a - j) by (unfold lit_lim, lit_li; rewrite El; lia).
      assert (Hjs: a_n a - LITBUFFEREXTRASIZE <= j) by exact Hsw.
      apply epi_nohead; auto.
      * unfold lit_code, LOC_SPLIT, LOC_NOT_IN_DST. discriminate.
      * unfold lit_base. rewrite El. apply Hfx.
      * lia.
      * rewrite HL. eal.
      * rewrite HL. intros Hlt. eapply epi_pp_err; eauto.
        -- intros i Hi Hi2. apply Hun0; auto. eal.
        -- lia.
      * rewrite HL. intros Hlt.
        exact (epi_none_last a K j true c rep' _ Hctx Hpos ltac:(rewrite El; reflexivity) Haft (eq_sym HL) Hlt).
      * rewrite HL. intros Hle.
        destruct Hlm as (Hl0 & Hl1 & Hl2 & Hl3).
        set (m := a_n a - LITBUFFEREXTRASIZE) in *.
        destruct (epi_mm_disj Ews (oa_sh (a_o a)) LITEXTRA_N xc (lit_extra (a_p a))
                    (j - m) (oa_N (a_o a)) c (a_ob a) (a_d a + K) (a_n a - j))
          as (F & Hmm & Hpre & Hpost); auto; try (unfold m in *; eal).
        all: try (apply writable_readable, writable_Ews).
        all: try (apply Forall_sublist; exact Hxb).
        exists (mm_disjoint Ews (oa_sh (a_o a)) (offset_val (j - m) (lit_extra (a_p a)))
                  (offset_val (a_d a + K) (a_ob a)) (a_n a - j) (sublist (j - m) (j - m + (a_n a - j)) xc)),
               (F * data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))),
               (epi_put c (a_d a + K) (sublist (j - m) (j - m + (a_n a - j)) xc)).
        split; [exact Hmm|]. split; [reflexivity|].
        split; [unfold lit_li, lit_base; rewrite El; reflexivity|]. split; [reflexivity|].
        split; [|split; [|split]].
        -- rewrite <- sepcon_assoc.
           eapply derives_trans; [|apply sepcon_derives; [exact Hpre | apply derives_refl]]. cancel.
        -- rewrite <- sepcon_assoc.
           eapply derives_trans; [apply sepcon_derives; [exact Hpost | apply derives_refl]|]. cancel.
        -- apply epi_ok_put with (sw := true); auto; try (unfold m in *; eal); try (rewrite Zlength_sublist; unfold m in *; eal).
           ++ unfold m, a_n in *.
              replace (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE) + (Zlength (a_lits a) - j))
                with (LITBUFFEREXTRASIZE + 0) by lia.
              replace (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE))
                with (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE) + 0) by lia.
              rewrite <- (sublist_sublist LITBUFFEREXTRASIZE LITBUFFEREXTRASIZE
                            (j - (Zlength (a_lits a) - LITBUFFEREXTRASIZE)) 0) by eal.
              rewrite Hxm, epi_zb_sub, sublist_sublist by eal. f_equal. f_equal; lia.
           ++ intros _ _ _. apply epi_bc_sub, Hxb.
        -- apply (epi_exact_last a K j _ c _ rep' _ Hctx Hpos ltac:(rewrite El; first [exact I | reflexivity]) Haft (eq_sym HL)).
          ++ lia.
          ++ unfold lit_li, lit_lim, xl_larr; rewrite El; cbv beta iota; try rewrite Hxz; try unfold m in *.
             f_equal; unfold a_n in *; lia.
          ++ apply epi_noerr; try unfold m in *; eal.
    + (* the head in dst, then litExtraBuffer *)
      destruct Hlm as (Hl0 & Hl1 & Hl2 & Hl3).
      assert (HE: a_E a = a_d a + a_cap a) by (unfold a_E; rewrite El; reflexivity).
      assert (Hjs: j <= a_n a - LITBUFFEREXTRASIZE) by exact Hsw.
      assert (Hxp: isptr (lit_extra (a_p a))) by (destruct Hfx; auto).
      assert (Xsrc: Forall is_byte_val (sublist (lb + j) (lb + j + (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j))) c)).
      { assert (Hcap0: 0 < a_cap a) by (unfold a_cap, a_d in *; eal).
        pose proof (ex_def_lits a xc K j false c Hok ltac:(rewrite El; exact Hxc) Hcap0 ltac:(eal) Hcl Hd) as Hs2. rewrite El in Hs2.
        destruct Hs2 as (Hs2 & _). specialize (Hs2 Hjs).
        apply (xd_sub _ (lb + j) (lb + (a_n a - LITBUFFEREXTRASIZE) + WILDCOPY_OVERLENGTH)); auto; eal. }
      apply epi_splithead with (lb := lb); auto; try eal.
      * intros Hlt. eapply epi_pp_err; eauto.
        -- intros i Hi Hi2. apply Hun0; auto. eal.
        -- eal.
      * intros Hlt. pose proof (xl_epi_head a K c rep' j lb Hctx Hpos El Haft) as Hh. cbv zeta in Hh.
        apply (proj1 Hh). unfold lit_lim, lit_li. rewrite El. cbv beta iota. lia.
      * intros Hle.
        set (L1 := lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + j)) in *.
        set (bs1 := sublist (lb + j) (lb + j + L1) c).
        set (c1 := epi_put c (a_d a + K) bs1).
        assert (Hbs1: Zlength bs1 = L1) by (unfold bs1; rewrite Zlength_sublist; unfold L1 in *; eal).
        assert (Hc1: mm_result c (oa_N (a_o a)) (lb + j) (a_d a + K) L1 = c1)
          by (unfold c1, bs1; apply epi_mm_result; unfold L1 in *; eal).
        rewrite Hc1.
        assert (Hc1l: Zlength c1 = oa_N (a_o a)) by (unfold c1; rewrite epi_put_len; unfold L1 in *; eal).
        assert (Hc1u: unchanged_outside c c1 (a_d a + K) (a_d a + K + L1))
          by (unfold c1; rewrite <- Hbs1; apply epi_put_out; unfold L1 in *; eal).
        (* the exact model after the split head (BlkSeqLoopLongXP.xl_epi_head) *)
        assert (Hpos1: xl_pos a (K + L1) (j + L1) true c1).
        { unfold xl_pos. rewrite El. cbv beta iota. unfold L1 in *. repeat split; try exact Hc1l; eal. }
        assert (HnL: LITBUFFEREXTRASIZE = lit_lim a true - lit_li a true (j + L1)).
        { unfold lit_lim, lit_li. rewrite El. cbv beta iota. unfold L1, a_n in *. lia. }
        assert (Haft1: xl_aft a (K + L1) c1 rep' (j + L1) true).
        { pose proof (xl_epi_head a K c rep' j lb Hctx Hpos El Haft) as Hh. cbv zeta in Hh. destruct Hh as [_ Hh].
          assert (E1: lit_lim a false - lit_li a false j = L1)
            by (unfold lit_lim, lit_li; rewrite El; cbv beta iota; unfold L1; lia).
          assert (E2: sublist (lit_li a false j) (lit_lim a false) c = bs1)
            by (unfold bs1, lit_li, lit_lim; rewrite El; cbv beta iota; f_equal; unfold L1; lia).
          rewrite E1, E2 in Hh. exact (Hh Hle). }
        eapply semax_pre;
          [| apply (epi_last_ok Espec a (K + L1) 0 LITBUFFEREXTRASIZE (lit_extra (a_p a)) LOC_SPLIT xc c1 rep')].
        { rewrite isptr_offset_val_zero by exact Hxp. rewrite Z.add_0_l. apply ENTAIL_refl. }
        all: auto; try (unfold L1 in *; eal).
        -- intros Hlt. eapply epi_pp_err; eauto.
           ++ intros i Hi Hi2. rewrite Hc1u by (try lia; unfold L1 in *; eal).
              apply Hun0; [lia|]. unfold L1 in *; eal.
           ++ unfold L1 in *; eal.
           ++ intros H1 H2 H3. unfold c1. apply epi_put_bytes; [apply Hcb; auto | unfold bs1; apply epi_bc_sub, Hcb; auto].
        -- intros Hlt.
           exact (epi_none_last a (K + L1) (j + L1) true c1 rep' _ Hctx Hpos1 ltac:(rewrite El; reflexivity) Haft1 HnL Hlt).
        -- intros Hle2.
           destruct (epi_mm_disj Ews (oa_sh (a_o a)) LITEXTRA_N xc (lit_extra (a_p a)) 0 (oa_N (a_o a)) c1
                       (a_ob a) (a_d a + (K + L1)) LITBUFFEREXTRASIZE)
             as (F & Hmm & Hpre & Hpost); auto; try (unfold L1 in *; eal).
           all: try (apply writable_readable, writable_Ews).
           all: try (apply Forall_sublist; exact Hxb).
           set (bs2 := sublist 0 (0 + LITBUFFEREXTRASIZE) xc) in *.
           exists (mm_disjoint Ews (oa_sh (a_o a)) (offset_val 0 (lit_extra (a_p a)))
                     (offset_val (a_d a + (K + L1)) (a_ob a)) LITBUFFEREXTRASIZE bs2),
                  (F * data_at (iw_sh (a_i a)) (tarray tuchar (iw_N (a_i a))) (iw_c (a_i a)) (iw_base (a_i a))),
                  (epi_put c1 (a_d a + (K + L1)) bs2).
           split; [exact Hmm|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [|split; [|split]].
           ++ rewrite <- sepcon_assoc.
              eapply derives_trans; [|apply sepcon_derives; [exact Hpre | apply derives_refl]]. cancel.
           ++ rewrite <- sepcon_assoc.
              eapply derives_trans; [apply sepcon_derives; [exact Hpost | apply derives_refl]|]. cancel.
           ++ assert (Hbs2: bs2 = zbytes (sublist (a_n a - LITBUFFEREXTRASIZE) (a_n a) (a_lits a)))
                by (unfold bs2; rewrite Z.add_0_l; exact Hxm).
              assert (Hbs2l: Zlength bs2 = LITBUFFEREXTRASIZE)
                by (unfold bs2; rewrite Zlength_sublist; eal).
              set (c2 := epi_put c1 (a_d a + (K + L1)) bs2).
              assert (HL1: L1 = a_n a - LITBUFFEREXTRASIZE - j) by (unfold L1; lia).
              assert (Hs1: sublist (a_d a + K) (a_d a + K + L1) c2 = bs1).
              { unfold c2. rewrite epi_put_pre by (try lia; eal).
                unfold c1. rewrite <- Hbs1. apply epi_put_mid; eal. }
              assert (Hs2: sublist (a_d a + K + L1) (a_d a + K + (a_n a - j)) c2 = bs2).
              { unfold c2. replace (a_d a + K + L1) with (a_d a + (K + L1)) by lia.
                replace (a_d a + K + (a_n a - j)) with (a_d a + (K + L1) + Zlength bs2) by lia.
                apply epi_put_mid; eal. }
              assert (Hc2l: Zlength c2 = oa_N (a_o a)) by (unfold c2; rewrite epi_put_len; eal).
              replace (K + L1 + LITBUFFEREXTRASIZE) with (K + (a_n a - j)) by lia.
              apply epi_pp_ok with (sw := false) (c := c); auto; try eal.
              ** intros i Hi Hn2. transitivity (Znth i c1).
                 --- unfold c2. apply epi_put_out; eal.
                 --- apply Hc1u; eal.
              ** intros Hh Hc. replace (a_d a + (K + (a_n a - j))) with (a_d a + K + (a_n a - j)) by lia.
                 rewrite (sublist_split (a_d a + K) (a_d a + K + L1) (a_d a + K + (a_n a - j))) by eal.
                 rewrite Hs1, Hs2. apply Forall_app. split.
                 --- unfold bs1. exact Xsrc.
                 --- rewrite Hbs2. apply epi_zb_byte, epi_bytes_sub, Hlb.
              ** intros Hli. replace (a_d a + (K + (a_n a - j))) with (a_d a + K + (a_n a - j)) by lia.
                 rewrite (sublist_split (a_d a + K) (a_d a + K + L1) (a_d a + K + (a_n a - j))) by eal.
                 rewrite Hs1, Hs2. unfold lit_intact in Hli. rewrite El in Hli. specialize (Hli eq_refl).
                 unfold bs1. replace (lb + j + L1) with (lb + (a_n a - LITBUFFEREXTRASIZE)) by lia.
                 rewrite Hli, Hbs2, <- map_app, <- sublist_split by eal. reflexivity.
              ** intros H1 H2 H3. unfold c2, c1.
                 apply epi_put_bytes; [apply epi_put_bytes; [apply Hcb; auto | unfold bs1; apply epi_bc_sub, Hcb; auto] |].
                 unfold bs2. apply epi_bc_sub, Hxb.
           ++ apply (epi_exact_last a (K + L1) (j + L1) true c1 bs2 rep' _ Hctx Hpos1 ltac:(rewrite El; reflexivity)
                       Haft1 HnL).
              ** lia.
              ** unfold bs2, lit_li, lit_lim, xl_larr. rewrite El. cbv beta iota. rewrite Hxz.
                 f_equal; unfold L1, a_n in *; lia.
              ** apply epi_noerr. unfold L1 in *; eal.
Qed.
