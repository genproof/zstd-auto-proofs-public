(* LOOP / long loop, part MAIN: the tail of both branches (prefetchMatch, seqCopy, op += r). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Local Open Scope logic.

(* the pointer witnesses of ZSTD_prefetchMatch: the output array (contents c) and a separate extDict
   (as BlkSeqLoopLongAdv.adv_W, for any contents) *)
Definition mt_W (a: la) (c: list val) : list ptr_witness :=
  pw_bytes (oa_sh (a_o a)) (oa_N (a_o a)) c (a_ob a) ::
  match a_x a with ExtSep sh eb en ec _ _ => [pw_bytes sh en ec eb] | _ => [] end.

Lemma mt_W_eq (a: la) (c: list val) :
  pws_pred (mt_W a c) = data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a) * ext_res (a_x a).
Proof.
  unfold mt_W, pws_pred, ext_res. destruct (a_x a); simpl; rewrite ?sepcon_emp; reflexivity.
Qed.

Lemma mt_arr_wvp (sh: share) (n: Z) (c: list val) (b: val) (k: Z) :
  readable_share sh -> 0 <= k <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c b |-- weak_valid_pointer (offset_val k b).
Proof.
  intros Hsh Hk Hn. sep_apply (data_at_memory_block sh (tarray tuchar n) c b).
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  apply memory_block_weak_valid_pointer; auto using readable_nonidentity.
Qed.

Lemma mt_pws_app (l1 l2: list ptr_witness) : pws_pred (l1 ++ l2) = pws_pred l1 * pws_pred l2.
Proof.
  induction l1 as [|w l IH]; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. reflexivity.
  - unfold pws_pred in *. simpl. rewrite IH, sepcon_assoc. reflexivity.
Qed.

(* ... and the caller's witnesses W (dictEnd may be weakly valid only there) *)
Definition mt_W2 (a: la) (c: list val) : list ptr_witness := mt_W a c ++ a_W a.

Lemma mt_W2_eq (a: la) (c: list val) :
  pws_pred (mt_W2 a c) =
  data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) c (a_ob a) * (ext_res (a_x a) * pws_pred (a_W a)).
Proof. unfold mt_W2. rewrite mt_pws_app, mt_W_eq, sepcon_assoc. reflexivity. Qed.

Lemma mt_W_ps (a: la) (c: list val) :
  la_ok a -> 0 < oa_cap (a_o a) -> pws_pred (mt_W2 a c) |-- weak_valid_pointer (fs_prefixStart (a_fs a)).
Proof.
  intros Hla Hc. destruct Hla as ((Hw & HN & _ & Hd & _ & Hdc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay).
  destruct (Hlay Hc) as (Hps & Heq & _). rewrite Heq, mt_W2_eq.
  apply sepcon_weak_valid_pointer1. apply mt_arr_wvp; [apply writable_readable; auto | lia | lia].
Qed.

Lemma mt_W_de (a: la) (c: list val) :
  la_ok a -> la_pend a -> 0 < oa_cap (a_o a) -> isptr (a_ob a) ->
  match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end ->
  is_pointer_or_null (fs_dictEnd (a_fs a)) ->
  fs_dictEnd (a_fs a) = nullval \/
  (isptr (fs_dictEnd (a_fs a)) /\ (pws_pred (mt_W2 a c) |-- weak_valid_pointer (fs_dictEnd (a_fs a)))).
Proof.
  intros Hla Hpe Hc Hob Heb Hpn.
  destruct Hla as ((Hw & HN & _ & Hd & _ & Hdc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay).
  destruct Hpe as ((_ & _ & Hde) & _). specialize (Hlay Hc).
  destruct Hde as [[Hn | [(k & Hk & Heq) | Hx]] | HW]; [left; auto | right | right | ].
  - rewrite Heq. split; [unfold a_ob in Hob; destruct (oa_base (a_o a)); try contradiction; simpl; auto|].
    rewrite mt_W2_eq. apply sepcon_weak_valid_pointer1.
    apply mt_arr_wvp; [apply writable_readable; auto | lia | unfold a_d in *; lia].
  - unfold layout_ok in Hlay. rewrite mt_W2_eq. unfold ext_res.
    destruct (a_x a) as [| |sh eb en ec e1 elen]; try contradiction.
    destruct Hx as (Heq & He1 & Hen). destruct Hlay as (_ & _ & _ & _ & _ & Hsh & _).
    rewrite Heq. split; [destruct eb; try contradiction; simpl; auto|].
    apply sepcon_weak_valid_pointer2. apply sepcon_weak_valid_pointer1. apply mt_arr_wvp; auto.
  - destruct (fs_dictEnd (a_fs a)) eqn:E; try contradiction; [left; simpl in Hpn; subst; reflexivity|].
    right. split; [simpl; auto|]. rewrite mt_W2_eq.
    apply sepcon_weak_valid_pointer2. apply sepcon_weak_valid_pointer2. exact HW.
Qed.

Lemma mt_W_facts (a: la) (c: list val) (R: mpred) :
  pws_pred (mt_W2 a c) * R |--
  !! (isptr (a_ob a) /\ match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end).
Proof.
  rewrite mt_W2_eq. unfold ext_res. destruct (a_x a); entailer!.
Qed.

(* the ring slot k of sequences[8], borrowed for a store (as adv_ring_borrow / adv_ring_back) *)
Lemma mt_ring_borrow (r: list (option (Z * Z * Z))) (k: Z) (p: val) :
  0 <= k < 8 -> Zlength r = 8 ->
  data_at Tsh (tarray t_seq 8) (ring_vals r) p |--
  data_at_ Tsh t_seq (offset_val (24 * k) p) *
  (ALL e: Z * Z * Z, data_at Tsh t_seq (seqrep3 e) (offset_val (24 * k) p) -*
                     data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r (Some e))) p).
Proof.
  intros Hk Hr. assert_PROP (field_compatible (tarray t_seq 8) [] p) as Hfc by entailer!.
  eapply derives_trans; [apply (@SingletonHole.array_with_hole_intro CompSpecs Tsh t_seq k 8 (ring_vals r) p); lia|].
  rewrite arr_field_address by (auto; lia). change (sizeof t_seq) with 24.
  apply sepcon_derives; [apply data_at_data_at_|].
  unfold SingletonHole.array_with_hole. apply allp_right; intro e. apply (allp_left _ (seqrep3 e)).
  rewrite arr_field_address by (auto; lia). change (sizeof t_seq) with 24.
  unfold ring_vals. rewrite <- upd_Znth_map. apply derives_refl.
Qed.

Lemma mt_ring_back (r: list (option (Z * Z * Z))) (k: Z) (p: val) (ll ml off: Z) :
  data_at Tsh t_seq (seqrep ll ml off) (offset_val (24 * k) p) *
  (ALL e: Z * Z * Z, data_at Tsh t_seq (seqrep3 e) (offset_val (24 * k) p) -*
                     data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r (Some e))) p) |--
  data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r (Some (ll, ml, off)))) p.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_left _ (ll, ml, off)); apply derives_refl]|].
  apply modus_ponens_wand.
Qed.

Lemma mt_upd_upd {A} {d: Inhabitant A} (l: list A) (k: Z) (u v: A) :
  0 <= k < Zlength l -> upd_Znth k (upd_Znth k l u) v = upd_Znth k l v.
Proof.
  intros Hk. apply Znth_eq_ext; [rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia|].
  intros i Hi. rewrite !upd_Znth_Zlength in Hi by (rewrite ?upd_Znth_Zlength; lia).
  destruct (Z.eq_dec i k) as [->|Hne].
  - rewrite !upd_Znth_same by (rewrite ?upd_Znth_Zlength; lia). reflexivity.
  - rewrite !upd_Znth_diff by (rewrite ?upd_Znth_Zlength; lia). reflexivity.
Qed.

(* &sequences[seqNb & 7] *)
Lemma mt_slot (p: val) (id: Z) :
  isptr p ->
  force_val (sem_add_ptr_int t_seq Signed p (Vint (Int.repr (Z.land id (8 - 1))))) = offset_val (24 * (id mod 8)) p.
Proof.
  intros Hp. destruct p; try contradiction.
  change (8 - 1) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  assert (Hm: 0 <= id mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold sem_add_ptr_int. simpl. f_equal. f_equal.
  unfold Ptrofs.of_ints. rewrite Int.signed_repr by rep_lia. rewrite ptrofs_mul_repr. reflexivity.
Qed.

(* op += oneSeqSize *)
Lemma mt_add (b: val) (a n: Z) :
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

Lemma lg_main_tail_ok : P_TAIL.
Proof.
  intros Espec a x w dd K' j' sw' c' Kop r tq osz Hla Hpend Hlfx Htid.
  destruct Htid as [E|E]; injection E as -> ->.
  - destruct w as [id ie pos lo st drep ring q K j sw c pp].
    destruct dd as [dpos dlo dst drp ll ml off].
    unfold XS, w_next, d_e; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp
                                 d_pos d_lo d_st d_rep d_ll d_ml d_off].
    unfold main_ph; cbn [w_id w_ie].
    unfold LI_P at 1. cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
    Intros.
    assert (Hr8: Zlength ring = 8).
    { destruct H3 as [Hl _]. rewrite Zlength_upd_Znth in Hl; auto. }
    assert (Hq1: Zlength (tl q ++ [(ll, ml, off)]) >= 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. pose proof (Zlength_nonneg (tl q)). lia. }
    assert (Hm8: 0 <= id mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hla' := Hla).
    destruct Hla' as (Hoa & Hiw & _ & _ & _ & Hnb & Hnb0 & _ & _ & _ & _ & Hlay).
    assert (Hadv: a_adv a = Z.min (a_nb a) 8) by reflexivity.
    destruct (Hnb0 ltac:(lia)) as [_ Hcap].
    unfold S_fix, L_seq, L_base. cbn [app].
    gather_SEP 7 16 9. rewrite <- mt_W2_eq.
    assert_PROP (isptr (a_ob a) /\ match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) as HobE.
    { unfold PROPx, LOCALx, SEPx. apply andp_left2. apply andp_left2. apply andp_left2.
      change (fold_right_sepcon (?A :: ?B)) with (A * fold_right_sepcon B). intro rho. apply mt_W_facts. }
    destruct HobE as [Hob Heb].
    assert_PROP (is_pointer_or_null (fs_dictEnd (a_fs a))) as Hdpn by entailer!.
    pose proof (mt_W_ps a c' Hla Hcap) as Hwps.
    pose proof (mt_W_de a c' Hla Hpend Hcap Hob Heb Hdpn) as Hwde.
    assert (Hpsp: isptr (fs_prefixStart (a_fs a))).
    { destruct (Hlay Hcap) as (_ & -> & _). unfold a_ob in Hob. destruct (oa_base (a_o a)); try contradiction; simpl; auto. }
    assert (Hq: 0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= off <= SIZE_MAX)
      by (unfold q_safe in H16; apply Forall_inv in H16; exact H16).
    destruct Hq as (Hll & Hml & Hoff).
    unfold lg_tail.
    remember (mt_W2 a c') as WW eqn:HWW.
    apply -> seq_assoc.
    forward_call (Tsh, a_vs1 a, ll, ml, off, pp, fs_prefixStart (a_fs a), fs_dictEnd (a_fs a), WW).
    { unfold LL_VMAX, ML_VMAX, SIZE_MAX, LONGNBSEQ in *. rep_lia. }
    forward.
    assert (Hr8': Zlength (upd_Znth (id mod 8) ring None) = 8) by (rewrite Zlength_upd_Znth; auto).
    sep_apply (mt_ring_borrow (upd_Znth (id mod 8) ring None) (id mod 8) (a_vsqs a) Hm8 Hr8').
    flatten_sepcon_in_SEP.
    forward_call (Tsh, a_vs1 a, ll, ml, off, Tsh, offset_val (24 * (id mod 8)) (a_vsqs a)).
    { entailer!. rewrite mt_slot by auto. reflexivity. }
    { unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. rep_lia. }
    sep_apply (mt_ring_back (upd_Znth (id mod 8) ring None) (id mod 8) (a_vsqs a) ll ml off).
    rewrite mt_upd_upd by (rewrite Hr8; lia).
    forward.
    rewrite mt_add by auto.
    subst WW. rewrite mt_W2_eq. flatten_sepcon_in_SEP.
    Exists (mk_lst (id + 1) (ie + 1) dpos dlo dst drp (upd_Znth (id mod 8) ring (Some (ll, ml, off)))
                   (tl q ++ [(ll, ml, off)]) K' j' sw' c' (pp + ll + ml)).
    unfold LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base.
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
    entailer!.
    f_equal. lia.
  - destruct w as [id ie pos lo st drep ring q K j sw c pp].
    destruct dd as [dpos dlo dst drp ll ml off].
    unfold XS, w_next, d_e; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp
                                 d_pos d_lo d_st d_rep d_ll d_ml d_off].
    unfold main_ph; cbn [w_id w_ie].
    unfold LI_P at 1. cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
    Intros.
    assert (Hr8: Zlength ring = 8).
    { destruct H3 as [Hl _]. rewrite Zlength_upd_Znth in Hl; auto. }
    assert (Hq1: Zlength (tl q ++ [(ll, ml, off)]) >= 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. pose proof (Zlength_nonneg (tl q)). lia. }
    assert (Hm8: 0 <= id mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hla' := Hla).
    destruct Hla' as (Hoa & Hiw & _ & _ & _ & Hnb & Hnb0 & _ & _ & _ & _ & Hlay).
    assert (Hadv: a_adv a = Z.min (a_nb a) 8) by reflexivity.
    destruct (Hnb0 ltac:(lia)) as [_ Hcap].
    unfold S_fix, L_seq, L_base. cbn [app].
    gather_SEP 7 16 9. rewrite <- mt_W2_eq.
    assert_PROP (isptr (a_ob a) /\ match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) as HobE.
    { unfold PROPx, LOCALx, SEPx. apply andp_left2. apply andp_left2. apply andp_left2.
      change (fold_right_sepcon (?A :: ?B)) with (A * fold_right_sepcon B). intro rho. apply mt_W_facts. }
    destruct HobE as [Hob Heb].
    assert_PROP (is_pointer_or_null (fs_dictEnd (a_fs a))) as Hdpn by entailer!.
    pose proof (mt_W_ps a c' Hla Hcap) as Hwps.
    pose proof (mt_W_de a c' Hla Hpend Hcap Hob Heb Hdpn) as Hwde.
    assert (Hpsp: isptr (fs_prefixStart (a_fs a))).
    { destruct (Hlay Hcap) as (_ & -> & _). unfold a_ob in Hob. destruct (oa_base (a_o a)); try contradiction; simpl; auto. }
    assert (Hq: 0 <= ll <= LL_VMAX /\ 3 <= ml <= ML_VMAX /\ 1 <= off <= SIZE_MAX)
      by (unfold q_safe in H16; apply Forall_inv in H16; exact H16).
    destruct Hq as (Hll & Hml & Hoff).
    unfold lg_tail.
    remember (mt_W2 a c') as WW eqn:HWW.
    apply -> seq_assoc.
    forward_call (Tsh, a_vs1 a, ll, ml, off, pp, fs_prefixStart (a_fs a), fs_dictEnd (a_fs a), WW).
    { unfold LL_VMAX, ML_VMAX, SIZE_MAX, LONGNBSEQ in *. rep_lia. }
    forward.
    assert (Hr8': Zlength (upd_Znth (id mod 8) ring None) = 8) by (rewrite Zlength_upd_Znth; auto).
    sep_apply (mt_ring_borrow (upd_Znth (id mod 8) ring None) (id mod 8) (a_vsqs a) Hm8 Hr8').
    flatten_sepcon_in_SEP.
    forward_call (Tsh, a_vs1 a, ll, ml, off, Tsh, offset_val (24 * (id mod 8)) (a_vsqs a)).
    { entailer!. rewrite mt_slot by auto. reflexivity. }
    { unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. rep_lia. }
    sep_apply (mt_ring_back (upd_Znth (id mod 8) ring None) (id mod 8) (a_vsqs a) ll ml off).
    rewrite mt_upd_upd by (rewrite Hr8; lia).
    forward.
    rewrite mt_add by auto.
    subst WW. rewrite mt_W2_eq. flatten_sepcon_in_SEP.
    Exists (mk_lst (id + 1) (ie + 1) dpos dlo dst drp (upd_Znth (id mod 8) ring (Some (ll, ml, off)))
                   (tl q ++ [(ll, ml, off)]) K' j' sw' c' (pp + ll + ml)).
    unfold LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base.
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
    entailer!.
    f_equal. lia.
Qed.
