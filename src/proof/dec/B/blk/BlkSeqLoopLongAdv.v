(* The long loop (ZSTD_decompressSequencesLong_body, cut in segments by BlkSeqLoopLongDefs): one iteration of the
   prepare loop (one ZSTD_decodeSequence, the sequence queued; the exact model's invariant by BlkSeqLoopLongXD.xl_dec_step). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXD.
Local Open Scope logic.

Lemma adv_bit (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z)
    (tp: val * val * val) (r: Z * Z * Z) (q: val) :
  seqstate_at sh gv s start pos lo st tp r q |-- !! bit_inv s pos lo.
Proof.
  unfold seqstate_at, BIT_DStream_rep. destruct st as [[a b] c0]; destruct tp as [[x y] z].
  Intros ptr lim. entailer!.
Qed.

(* the pointer witnesses of ZSTD_prefetchMatch: the output array, a separate extDict, the caller's W *)
Definition adv_ext (e: ext_seg) : list ptr_witness :=
  match e with ExtSep sh eb en ec _ _ => [pw_bytes sh en ec eb] | _ => [] end.
Definition adv_W (a: la) : list ptr_witness :=
  pw_bytes (oa_sh (a_o a)) (oa_N (a_o a)) (oa_c (a_o a)) (a_ob a) :: adv_ext (a_x a) ++ a_W a.

Lemma adv_pws_app (l1 l2: list ptr_witness) : pws_pred (l1 ++ l2) = pws_pred l1 * pws_pred l2.
Proof.
  induction l1 as [|w l IH]; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. reflexivity.
  - unfold pws_pred in *. simpl. rewrite IH, sepcon_assoc. reflexivity.
Qed.

Lemma adv_W_eq (a: la) :
  pws_pred (adv_W a) =
  data_at (oa_sh (a_o a)) (tarray tuchar (oa_N (a_o a))) (oa_c (a_o a)) (a_ob a) * ext_res (a_x a) *
  pws_pred (a_W a).
Proof.
  unfold adv_W. change (pws_pred (?w :: ?l)) with (pw_pred w * pws_pred l).
  rewrite adv_pws_app, <- sepcon_assoc. f_equal. f_equal.
  unfold adv_ext, pws_pred, ext_res. destruct (a_x a); simpl; rewrite ?sepcon_emp; reflexivity.
Qed.

Lemma adv_arr_wvp (sh: share) (n: Z) (c: list val) (b: val) (k: Z) :
  readable_share sh -> 0 <= k <= n -> 0 < n ->
  data_at sh (tarray tuchar n) c b |-- weak_valid_pointer (offset_val k b).
Proof.
  intros Hsh Hk Hn. sep_apply (data_at_memory_block sh (tarray tuchar n) c b).
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  apply memory_block_weak_valid_pointer; auto using readable_nonidentity.
Qed.

Lemma adv_W_ps (a: la) :
  la_ok a -> 0 < oa_cap (a_o a) -> pws_pred (adv_W a) |-- weak_valid_pointer (fs_prefixStart (a_fs a)).
Proof.
  intros Hla Hc. destruct Hla as ((Hw & HN & _ & Hd & _ & Hdc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay).
  destruct (Hlay Hc) as (Hps & Heq & _). rewrite Heq, adv_W_eq.
  apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer1.
  apply adv_arr_wvp; [apply writable_readable; auto | lia | lia].
Qed.

Lemma adv_W_de (a: la) :
  la_ok a -> la_pend a -> 0 < oa_cap (a_o a) -> isptr (a_ob a) ->
  match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end ->
  is_pointer_or_null (fs_dictEnd (a_fs a)) ->
  fs_dictEnd (a_fs a) = nullval \/
  (isptr (fs_dictEnd (a_fs a)) /\ (pws_pred (adv_W a) |-- weak_valid_pointer (fs_dictEnd (a_fs a)))).
Proof.
  intros Hla Hpe Hc Hob Heb Hpn.
  destruct Hla as ((Hw & HN & _ & Hd & _ & Hdc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlay).
  destruct Hpe as ((_ & _ & Hde) & _). specialize (Hlay Hc).
  destruct Hde as [[Hn | [(k & Hk & Heq) | Hx]] | HW]; [left; auto | right | right | ].
  - rewrite Heq. split; [unfold a_ob in Hob; destruct (oa_base (a_o a)); try contradiction; simpl; auto|].
    rewrite adv_W_eq. apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer1.
    apply adv_arr_wvp; [apply writable_readable; auto | lia | unfold a_d in *; lia].
  - unfold layout_ok in Hlay. rewrite adv_W_eq. unfold ext_res.
    destruct (a_x a) as [| |sh eb en ec e1 elen]; try contradiction.
    destruct Hx as (Heq & He1 & Hen). destruct Hlay as (_ & _ & _ & _ & _ & Hsh & _).
    rewrite Heq. split; [destruct eb; try contradiction; simpl; auto|].
    apply sepcon_weak_valid_pointer1. apply sepcon_weak_valid_pointer2. apply adv_arr_wvp; auto.
  - destruct (fs_dictEnd (a_fs a)) eqn:E; try contradiction; [left; simpl in Hpn; subst; reflexivity|].
    right. split; [simpl; auto|]. rewrite adv_W_eq. apply sepcon_weak_valid_pointer2. exact HW.
Qed.

(* the ring slot k of sequences[8], borrowed for a store *)
Lemma adv_ring_borrow (r: list (option (Z * Z * Z))) (k: Z) (p: val) :
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

Lemma adv_ring_back (r: list (option (Z * Z * Z))) (k: Z) (p: val) (ll ml off: Z) :
  data_at Tsh t_seq (seqrep ll ml off) (offset_val (24 * k) p) *
  (ALL e: Z * Z * Z, data_at Tsh t_seq (seqrep3 e) (offset_val (24 * k) p) -*
                     data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r (Some e))) p) |--
  data_at Tsh (tarray t_seq 8) (ring_vals (upd_Znth k r (Some (ll, ml, off)))) p.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_left _ (ll, ml, off)); apply derives_refl]|].
  apply modus_ponens_wand.
Qed.

(* the pure part of the new invariant *)
Lemma adv_ring_ok (id: Z) (ring: list (option (Z * Z * Z))) (q: list (Z * Z * Z)) (e: Z * Z * Z) :
  0 <= id < 8 -> Zlength q = id -> ring_ok 0 ring q -> ring_ok 0 (upd_Znth id ring (Some e)) (q ++ [e]).
Proof.
  intros Hid Hq [Hl Hk]. split; [rewrite upd_Znth_Zlength; lia|].
  intros k Hk'. rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk'.
  rewrite Z.add_0_l, Z.mod_small by lia.
  destruct (Z.eq_dec k id) as [->|Hne].
  - rewrite upd_Znth_same by lia. rewrite Znth_app2 by lia. replace (id - Zlength q) with 0 by lia. reflexivity.
  - rewrite upd_Znth_diff by lia. rewrite Znth_app1 by lia.
    specialize (Hk k ltac:(lia)). rewrite Z.add_0_l, Z.mod_small in Hk by lia. exact Hk.
Qed.

Lemma adv_q_safe (q: list (Z * Z * Z)) (ll ml off: Z) :
  q_safe q -> 0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= off <= SIZE_MAX -> q_safe (q ++ [(ll, ml, off)]).
Proof.
  intros Hq H1 H2 H3. unfold q_safe in *. rewrite Forall_app. split; auto.
Qed.

Lemma lg_adv_ok : SEG_ADV.
Proof.
  intros HTB HDS Espec a x w HG Hla Hpend Hlfx Hlfxx HLIP Hadv Hid.
  destruct w as [id ie pos lo st drep ring q K j sw c pp]; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in *.
  unfold adv_ph in Hadv; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in Hadv.
  destruct Hadv as (Hie & HK & Hj & Hsw & Hc). subst ie K j sw c.
  unfold LI, LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base, lg_adv_body; cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
  unfold lg_Delta; simplify_func_tycontext.
  Intros.
  match goal with H: xl_inv _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hxinv end.
  assert_PROP (bit_inv (iw_s (a_i a)) pos lo) as HBI.
  { apply andp_left2. unfold PROPx, LOCALx. apply andp_left2. apply andp_left2. unfold SEPx. intro rho.
    simpl fold_right_sepcon.
    sep_apply (adv_bit Tsh (a_gv a) (iw_s (a_i a)) (a_start a) pos lo st (x_tp x) drep (a_vss a)).
    Intros. simpl. apply prop_right; auto. }
  sep_apply (HTB HG (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x)).
  Intros sht fm Rt.
  assert (Hla' := Hla).
  destruct Hla' as (Hoa & Hiw & _ & _ & _ & Hnb & Hnb0 & _ & _ & _ & _ & Hlay).
  assert (Hlf' := Hlfx). destruct Hlf' as (Hos & _ & Hsh2 & _ & _).
  assert (Hadv: a_adv a = Z.min (a_nb a) 8) by reflexivity.
  assert (Hidn: 0 <= id < a_nb a) by lia.
  destruct (Hnb0 ltac:(lia)) as [_ Hcap].
  assert_PROP (isptr (a_start a)) as Hsp.
  { unfold bit_src. entailer!. }
  assert (HD5 := H5). destruct HD5 as (Hstok & Hrc & Hbc).
  forward_call (a_gv a, Tsh, a_vs a, Tsh, a_vss a, iw_s (a_i a), a_start a, pos, lo, st, x_t x,
                x_tp x, sht, fm, drep, x_sh2 x, a_start a, iw_s (a_i a), 0, 0, (id =? a_nb a - 1)).
  { rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia); unfold LONGNBSEQ in *; rep_lia. }
  { go_lower. apply prop_right. simpl. unfold Int.eq, Int.sub. change (Int.unsigned (Int.repr 1)) with 1.
    rewrite (Int.unsigned_repr (a_nb a)) by (unfold LONGNBSEQ in *; rep_lia).
    rewrite (Int.unsigned_repr (a_nb a - 1)) by (unfold LONGNBSEQ in *; rep_lia).
    rewrite (Int.unsigned_repr id) by (unfold LONGNBSEQ in *; rep_lia).
    destruct (Z.eqb_spec id (a_nb a - 1)); destruct (zeq id (a_nb a - 1)); try lia; reflexivity. }
  { split; [|split].
    - unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
      split; [reflexivity|]. split; [lia|]. rewrite Z.add_0_l, sublist_same by lia. split; [lia|reflexivity].
    - destruct drep as [[r1 r2] r3]. unfold rep_c_ok, rc1, rep64_ok, SIZE_MAX in *. lia.
    - unfold bcons, DSEQ_BITS, LONGNBSEQ in *. rep_lia. }
  Intros vret. destruct vret as [[[[[ll ml] ov] st'] pos'] lo']. Intros. cbn [fst snd] in *.
  sep_apply (H11 1).
  destruct HBI as (_ & _ & H0lo & H8lo & _ & Hplo & _).
  edestruct (HDS a x id pos lo st drep ll ml ov pos' lo' st') as (Hoff & Hds' & Hmdl); eauto.
  { intros seqs Hd. destruct (H9 seqs Hd) as (? & ? & _); auto. }
  { intros E. apply H18. apply Z.eqb_eq. auto. }
  assert (Hring := adv_ring_ok id ring q (ll, ml, fst (c_offset drep ll ov)) ltac:(lia) ltac:(lia) H3).
  assert (Hqs := adv_q_safe q ll ml (fst (c_offset drep ll ov)) H4 H12 H13 Hoff).
  assert (Hmd': forall seqs, DM a (x_t x) seqs ->
     Zlength seqs = a_nb a /\
     dec_model a (x_t x) seqs (id + 1) pos' lo' st' (snd (c_offset drep ll ov)) /\
     q ++ [(ll, ml, fst (c_offset drep ll ov))] =
       q_of (rep_chain (a_rep a) (sublist 0 0 seqs)) (sublist 0 (id + 1) seqs) /\
     ex_model a seqs 0 0 0 false (oa_c (a_o a))).
  { intros seqs Hd. destruct (H9 seqs Hd) as (Hz & _ & Hq & Hex). destruct (Hmdl seqs Hd) as (Hdm & _ & _ & _ & Hqq).
    split; [auto|]. split; [auto|]. split; [|auto]. rewrite Hqq by lia. rewrite <- Hq. reflexivity. }
  (* the exact model: the decoded sequence joins the queue *)
  pose proof Hla as (_ & _ & _ & _ & _ & _ & _ & Hso & _).
  pose proof (xl_dec_step a (x_t x) id 0 (oa_c (a_o a)) drep 0 false pos lo st q pos' lo' st' ll ml ov
    (eq_ind _ seqs_ok Hso _ Hos) Hstok H0lo H8lo Hplo Hidn H17 H16 H18 H19 H20 Hxinv) as Hxinv'.
  clear Hmdl H9 H19 H18 H20 Hxinv HLIP.
  Intros.
  assert_PROP (isptr (a_ob a) /\ is_pointer_or_null (fs_dictEnd (a_fs a))) as Hobd by entailer!.
  destruct Hobd as [Hob Hdpn].
  assert_PROP (match a_x a with ExtSep _ eb _ _ _ _ => isptr eb | _ => True end) as Heb.
  { unfold ext_res. destruct (a_x a); entailer!. }
  pose proof (adv_W_ps a Hla Hcap) as Hwps.
  pose proof (adv_W_de a Hla Hpend Hcap Hob Heb Hdpn) as Hwde.
  assert (Hpsp: isptr (fs_prefixStart (a_fs a))).
  { destruct (Hlay Hcap) as (_ & -> & _). unfold a_ob in Hob. destruct (oa_base (a_o a)); try contradiction; simpl; auto. }
  gather_SEP 10 16 11. rewrite <- sepcon_assoc, <- adv_W_eq.
  remember (adv_W a) as WW eqn:HWW.
  apply seq_assoc.
  forward_call (Tsh, a_vs a, ll, ml, fst (c_offset drep ll ov), pp, fs_prefixStart (a_fs a), fs_dictEnd (a_fs a), WW).
  { unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. rep_lia. }
  forward.
  assert (Hr8: Zlength ring = 8) by (destruct H3; auto).
  sep_apply (adv_ring_borrow ring id (a_vsqs a) ltac:(lia) Hr8).
  Intros.
  forward_call (Tsh, a_vs a, ll, ml, fst (c_offset drep ll ov), Tsh, offset_val (24 * id) (a_vsqs a)).
  { unfold LL_VMAX, ML_VMAX, SIZE_MAX in *. rep_lia. }
  sep_apply (adv_ring_back ring id (a_vsqs a) ll ml (fst (c_offset drep ll ov))).
  sep_apply (data_at_data_at_ Tsh t_seq (seqrep ll ml (fst (c_offset drep ll ov))) (a_vs a)).
  subst WW. rewrite adv_W_eq.
  assert (Hpp: 0 <= pp + ll + ml <= 2 ^ 63 - 1 + 2 ^ 19 * (id + 1)) by (unfold LL_VMAX, ML_VMAX in *; lia).
  assert (Hzq: Zlength (q ++ [(ll, ml, fst (c_offset drep ll ov))]) = id + 1 - 0)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hph: adv_ph a (mk_lst (id + 1) 0 pos' lo' st' (snd (c_offset drep ll ov))
             (upd_Znth id ring (Some (ll, ml, fst (c_offset drep ll ov))))
             (q ++ [(ll, ml, fst (c_offset drep ll ov))]) 0 0 false (oa_c (a_o a)) (pp + ll + ml)))
    by (unfold adv_ph; cbn; auto).
  Exists (mk_lst (id + 1) 0 pos' lo' st' (snd (c_offset drep ll ov))
             (upd_Znth id ring (Some (ll, ml, fst (c_offset drep ll ov))))
             (q ++ [(ll, ml, fst (c_offset drep ll ov))]) 0 0 false (oa_c (a_o a)) (pp + ll + ml)).
  cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp].
  entailer!.
Qed.
