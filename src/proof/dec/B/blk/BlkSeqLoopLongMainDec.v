(* LOOP / long loop, part MAIN: the decode (ZSTD_decodeSequence into sequence__1). *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs Zstd.proof.dec.B.blk.BlkSeqLoopLongXD.
Local Open Scope logic.

Lemma lgmd_bit (sh: share) (gv: globals) (s: list Z) (start: val) (pos lo: Z) (st: Z * Z * Z)
    (tp: val * val * val) (r: Z * Z * Z) (q: val) :
  seqstate_at sh gv s start pos lo st tp r q |-- !! bit_inv s pos lo.
Proof.
  unfold seqstate_at, BIT_DStream_rep. destruct st as [[a b] c0]; destruct tp as [[x y] z].
  Intros ptr lim. entailer!.
Qed.

Lemma lgmd_q_safe1 (ll ml off: Z) :
  0 <= ll <= LL_VMAX -> 3 <= ml <= ML_VMAX -> 1 <= off <= SIZE_MAX -> q_safe [(ll, ml, off)].
Proof. intros H1 H2 H3. unfold q_safe. constructor; auto. Qed.

Lemma lg_main_dec_ok : P_DEC.
Proof.
  intros HTB HDS Espec a x w HG Hla Hpend Hlfx Hlx HLIP Hmain Hid.
  destruct w as [id ie pos lo st drep ring q K j sw c pp];
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp] in *.
  unfold LI, LI_P, LI_L, LI_S, S_fix, L_seq, L_ex, L_base, lg_main_dec;
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp app].
  Intros.
  assert_PROP (bit_inv (iw_s (a_i a)) pos lo) as HBI.
  { apply andp_left2. unfold PROPx, LOCALx. apply andp_left2. apply andp_left2. unfold SEPx. intro rho.
    simpl fold_right_sepcon.
    sep_apply (lgmd_bit Tsh (a_gv a) (iw_s (a_i a)) (a_start a) pos lo st (x_tp x) drep (a_vss a)).
    Intros. simpl. apply prop_right; auto. }
  sep_apply (HTB HG (a_gv a) (a_p a) (a_ox a) (x_t x) 1 (x_tp x)).
  Intros sht fm Rt.
  assert (Hla' := Hla).
  destruct Hla' as (Hoa & Hiw & _ & _ & _ & Hnb & Hnb0 & _ & _ & _ & _ & Hlay).
  assert (Hlf' := Hlfx). destruct Hlf' as (Hos & _ & Hsh2 & _ & _).
  assert (Hidn: 0 <= id < a_nb a) by lia.
  assert_PROP (isptr (a_start a)) as Hsp.
  { unfold bit_src. entailer!. }
  assert (HD5 := H5). destruct HD5 as (Hstok & Hrc & Hbc).
  forward_call (a_gv a, Tsh, a_vs1 a, Tsh, a_vss a, iw_s (a_i a), a_start a, pos, lo, st, x_t x,
                x_tp x, sht, fm, drep, x_sh2 x, a_start a, iw_s (a_i a), 0, 0, (id =? a_nb a - 1)).
  { rewrite !Int.signed_repr by (unfold LONGNBSEQ in *; rep_lia); unfold LONGNBSEQ in *; rep_lia. }
  { go_lower. apply prop_right. simpl. unfold Int.eq, Int.sub. change (Int.unsigned (Int.repr 1)) with 1.
    rewrite (Int.unsigned_repr (a_nb a)) by (unfold LONGNBSEQ in *; rep_lia).
    rewrite (Int.unsigned_repr (a_nb a - 1)) by (unfold LONGNBSEQ in *; rep_lia).
    rewrite (Int.unsigned_repr id) by (unfold LONGNBSEQ in *; rep_lia).
    destruct (Z.eqb_spec id (a_nb a - 1)); destruct (zeq id (a_nb a - 1)); try lia; reflexivity. }
  { split; [|split].
    - unfold bit_src_ok. rewrite isptr_offset_val_zero by auto.
      split; [reflexivity|]. split; [lia|]. split; [lia|]. rewrite Z.add_0_l; apply sublist_same; lia.
    - destruct drep as [[r1 r2] r3]. unfold rep_c_ok, rc1, rep64_ok, SIZE_MAX, LONGNBSEQ in *. lia.
    - unfold bcons, DSEQ_BITS, LONGNBSEQ in *. rep_lia. }
  Intros vret. destruct vret as [[[[[ll ml] ov] st'] pos'] lo']. Intros. cbn [fst snd] in *.
  sep_apply (H12 1).
  destruct HBI as (_ & _ & H0lo & H8lo & _ & Hplo & _).
  edestruct (HDS a x id pos lo st drep ll ml ov pos' lo' st') as (Hoff & Hds' & Hmdl); eauto.
  { intros seqs Hd. destruct (H9 seqs Hd) as (? & ? & _); auto. }
  { intros E. apply H19. apply Z.eqb_eq. auto. }
  (* the exact model: the decoded sequence joins the queue *)
  assert (Hxl: xl_inv a (x_t x) (id + 1) K c (snd (c_offset drep ll ov)) j sw pos' lo' st'
                 (q ++ [(ll, ml, fst (c_offset drep ll ov))])).
  { destruct Hla as (_ & _ & _ & _ & _ & _ & _ & Hsok & _). rewrite Hos in Hsok.
    apply (xl_dec_step a (x_t x) id K c drep j sw pos lo st q pos' lo' st' ll ml ov); auto; lia. }
  Exists (mk_ldec pos' lo' st' (snd (c_offset drep ll ov)) ll ml (fst (c_offset drep ll ov))).
  unfold MD, MD_P, MD_S, LI_P, LI_L, S_fix, L_seq, L_ex, L_base, d_e;
    cbn [w_id w_ie w_pos w_lo w_st w_drep w_ring w_q w_K w_j w_sw w_c w_pp d_pos d_lo d_st d_rep d_ll d_ml d_off app].
  entailer!.
  split; [apply lgmd_q_safe1; auto|].
  intros seqs Hd. destruct (Hmdl seqs Hd) as (Hdm & _ & _ & _ & Hqq). destruct (H9 seqs Hd) as (_ & _ & Hq & _).
  split; [exact Hdm|]. rewrite Hqq by lia. rewrite <- Hq. reflexivity.
Qed.
