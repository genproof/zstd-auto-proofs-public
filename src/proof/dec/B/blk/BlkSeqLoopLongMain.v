(* LOOP / long loop: one iteration of the main loop (decode one, execute the one 8 behind).
   Assembly of the parts of BlkSeqLoopLongMainDefs (P_DEC, P_X1, P_X2, P_TAIL, P_INV, XSTEP),
   all in lg_Delta. *)
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongDefs.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDefs.
Require Import Zstd.proof.dec.B.blk.BlkSeqLoopLongMainDec Zstd.proof.dec.B.blk.BlkSeqLoopLongMainTail Zstd.proof.dec.B.blk.BlkSeqLoopLongMainInv Zstd.proof.dec.B.blk.BlkSeqLoopLongMainX1 Zstd.proof.dec.B.blk.BlkSeqLoopLongMainX2 Zstd.proof.dec.B.blk.BlkSeqLoopLongXstep.
Local Open Scope logic.

(* ---------- t'17 ---------- *)

(* pointer differences within one object *)
Lemma lgm_sub_ptr (b: block) (o: ptrofs) (si L: Z) :
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

Lemma lgm_t17 (b: block) (o: ptrofs) (i1 li ll: Z) :
  0 <= i1 - li <= 2 ^ 40 -> 0 <= ll <= 2 ^ 40 ->
  force_val (sem_cast tint tbool
    (eval_binop Olt tulong tulong
       (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar)
          (offset_val i1 (Vptr b o)) (offset_val li (Vptr b o))))
       (Vlong (Int64.repr ll)))) = Vint (Int.repr (if i1 - li <? ll then 1 else 0)).
Proof.
  intros HL Hll. set (L := i1 - li) in *. replace i1 with (li + L) by (unfold L; lia). clearbody L.
  assert (E: eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val (li + L) (Vptr b o)) (offset_val li (Vptr b o))
             = Vlong (Int64.repr L)).
  { rewrite <- (lgm_sub_ptr b o li L). reflexivity.
    unfold Ptrofs.max_signed, Ptrofs.half_modulus, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize.
    simpl. lia. }
  rewrite E. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt L ll), (L <? ll) eqn:Eb; try (apply Z.ltb_lt in Eb || apply Z.ltb_ge in Eb); try lia; reflexivity.
Qed.

Definition lgm_chk_post (a: la) (x: lfx) (w: lst) (dd: ldec) : environ -> mpred :=
  EX b: bool,
    PROPx ((b = true <-> lg_cut a w) :: MD_P a x w dd)
    (LOCALx (temp _t'17 (Vint (Int.repr (if b then 1 else 0))) :: LI_L a w (w_id w)) (SEPx (MD_S a x w dd))).

Lemma lgm_chk {Espec: OracleKind} (a: la) (x: lfx) (w: lst) (dd: ldec) :
  la_ok a -> lfx_ok a x ->
  semax lg_Delta (MD a x w dd) lg_main_chk (normal_ret_assert (lgm_chk_post a x w dd)).
Proof.
  intros Hla Hlfx.
  unfold MD, MD_P, MD_S, LI_P, LI_L, L_seq, L_ex, L_base, lg_main_chk. cbn [app].
  Intros.
  assert (Hadv: a_adv a = 8) by (unfold main_ph, a_adv in *; lia).
  assert (Hie: w_ie w = w_id w - 8) by (unfold main_ph in H11; lia).
  destruct (Znth 0 (w_q w)) as [[ll0 ml0] off0] eqn:Eq0.
  assert (Hcell: Znth (w_id w mod 8) (w_ring w) = Some (ll0, ml0, off0)).
  { destruct H3 as [_ Hr]. rewrite <- Eq0. replace (w_id w mod 8) with ((w_ie w + 0) mod 8). apply Hr. lia.
    rewrite Hie. replace (w_id w - 8 + 0) with (w_id w + (-1) * 8) by lia. apply Z_mod_plus_full. }
  unfold S_fix, lit_now, lit_code. cbn [app]. Intros.
  forward.
  forward_if (lgm_chk_post a x w dd).
  - assert (Hs: exists lb, a_l a = LSplit lb /\ w_sw w = false).
    { apply (f_equal Int.unsigned) in H17.
      destruct (w_sw w), (a_l a) eqn:El; unfold LOC_NOT_IN_DST, loc_code, LOC_IN_DST, LOC_SPLIT in H17;
        rewrite ?Int.unsigned_repr in H17 by rep_lia. all: try discriminate. all: eauto. }
    destruct Hs as (lb & El & Esw).
    unfold lit_fix. rewrite El. Intros.
    rewrite Esw in *. unfold lit_li, lit_base, lit_lim in *. rewrite El in *.
    forward. forward.
    assert (Hland: Z.land (w_id w - 8) (8 - 1) = w_id w mod 8).
    { change (8 - 1) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
      replace (w_id w - 8) with (w_id w + (-1) * 8) by lia. apply Z_mod_plus_full. }
    assert (Hm8: 0 <= w_id w mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hrl: Zlength (w_ring w) = 8) by (destruct H3; auto).
    assert (Hcv: Znth (Z.land (w_id w - 8) (8 - 1)) (ring_vals (w_ring w)) =
                 (Vlong (Int64.repr ll0), (Vlong (Int64.repr ml0), Vlong (Int64.repr off0)))).
    { rewrite Hland. unfold ring_vals. rewrite Znth_map by lia. rewrite Hcell. reflexivity. }
    forward.
    { entailer!. replace (Z.land (w_id w - 8) 7) with (w_id w mod 8) by (rewrite <- Hland; reflexivity).
      unfold ring_vals. rewrite Znth_map by lia. rewrite Hcell. simpl. auto. }
    { entailer!. destruct Hla as (_ & _ & _ & _ & _ & Hnb & _). unfold LONGNBSEQ in Hnb.
      rewrite !Int.signed_repr by rep_lia. rep_lia. }
    replace (Z.land (w_id w - 8) (8 - 1)) with (w_id w mod 8) by (rewrite <- Hland; reflexivity).
    unfold ring_vals at 1. rewrite Znth_map by lia. rewrite Hcell. simpl ring_cell. cbv beta iota zeta.
    assert_PROP (isptr (a_ob a)) as Hob by entailer!.
    destruct (a_ob a) as [ | ? | ? | ? | ? | bob ofo] eqn:Eob; try contradiction.
    forward.
    { entailer!. unfold sameblock. destruct (peq bob bob); [reflexivity | contradiction]. }
    pose proof H7 as H7c. destruct H7c as (HK0 & HKE & Hjn & Hjs & Hcl & Hun). rewrite El in Hjs. cbv beta iota in Hjs.
    assert (Hll0: 0 <= ll0 <= LL_VMAX).
    { unfold q_safe in H4. rewrite Forall_forall in H4.
      assert (Hin: In (Znth 0 (w_q w)) (w_q w)) by (apply Znth_In; lia).
      specialize (H4 _ Hin). rewrite Eq0 in H4. tauto. }
    assert (Hn: a_n a <= ZSTD_BLOCKSIZE_MAX) by (destruct Hla as (_ & _ & (_ & Hn & _) & _); exact (proj2 Hn)).
    rewrite lgm_t17 by (unfold LL_VMAX, ZSTD_BLOCKSIZE_MAX, LITBUFFEREXTRASIZE in *; lia).
    unfold lgm_chk_post. Exists (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + w_j w) <? ll0).
    unfold MD_P, MD_S, LI_P, LI_L, L_seq, L_ex, L_base, S_fix, lit_now, lit_fix, lit_code, lit_li, lit_base, lit_lim.
    cbn [app]. rewrite El, Esw, Eob.
    assert (Hcut: (lb + (a_n a - LITBUFFEREXTRASIZE) - (lb + w_j w) <? ll0) = true <-> lg_cut a w).
    { unfold lg_cut. rewrite El, Eq0, Esw. unfold lit_lim, lit_li. rewrite El. simpl. rewrite Z.ltb_lt. tauto. }
    entailer!.
  - forward. unfold lgm_chk_post. Exists false.
    assert (Hcut: false = true <-> lg_cut a w).
    { split; [discriminate|]. unfold lg_cut. intro Hc. destruct (a_l a) eqn:El; try contradiction.
      destruct Hc as [Esw _]. rewrite Esw in H17. exfalso. apply H17. reflexivity. }
    unfold MD_P, MD_S, LI_P, LI_L, L_seq, L_ex, L_base, S_fix, lit_now, lit_code. cbn [app]. entailer!.
Qed.

Lemma lgm_drop (Delta: tycontext) (P: list Prop) (q: localdef) (L: list localdef) (S: list mpred) :
  ENTAIL Delta, PROPx P (LOCALx (q :: L) (SEPx S)) |-- PROPx P (LOCALx L (SEPx S)).
Proof.
  apply andp_left2. unfold PROPx. apply andp_derives; [apply derives_refl|].
  unfold LOCALx. apply andp_derives; [|apply derives_refl].
  intro rho. unfold local, lift1. simpl. apply prop_derives. intros [_ Hl]. exact Hl.
Qed.

Lemma lg_main_ok : SEG_MAIN.
Proof.
  intros TE TB DS Espec a x w R HG Hla Hpe Hlfx Hlx HLIP Hmain Hid HRn HRr.
  destruct R as [Rn Rb Rc Rr]. cbn [RA_normal RA_return] in HRn, HRr.
  apply semax_seq with (Q := EX dd: ldec, MD a x w dd).
  { eapply semax_post; [| | | | apply (lg_main_dec_ok TB DS Espec a x w HG Hla Hpe Hlfx Hlx HLIP Hmain Hid)].
    all: intros; apply andp_left2; first [apply derives_refl | apply FF_left | (intro rho; simpl; normalize)]. }
  Intros dd.
  apply semax_seq with (Q := lgm_chk_post a x w dd).
  { eapply semax_post; [| | | | apply (lgm_chk a x w dd Hla Hlfx)].
    all: intros; apply andp_left2; first [apply derives_refl | apply FF_left | (intro rho; simpl; normalize)]. }
  unfold lgm_chk_post. Intros b. Intros.
  eapply semax_pre; [apply andp_left2, now_later|].
  apply semax_ifthenelse_PQR' with (v := Vint (Int.repr (if b then 1 else 0))).
  { reflexivity. }
  { unfold MD_P, MD_S, LI_P, LI_L, L_seq, L_ex, L_base, S_fix. cbn [app]. entailer!. }
  { unfold MD_P, MD_S, LI_P, LI_L, L_seq, L_ex, L_base, S_fix. cbn [app]. entailer!. }
  - Intros. destruct b.
    + assert (Hc: lg_cut a w) by (apply H; reflexivity).
      eapply semax_pre; [apply lgm_drop |].
      apply (lg_main_x1_ok TE lg_xstep_ok lg_main_inv_ok lg_main_tail_ok Espec a x w dd
               {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |} HG Hla Hpe Hlfx Hlx Hc HRn HRr).
    + exfalso; first [apply H0; reflexivity | revert H0; cbv; discriminate].
  - Intros. destruct b.
    + exfalso; first [apply H0; reflexivity | revert H0; cbv; discriminate].
    + assert (Hc: ~ lg_cut a w) by (intro Hc; apply H in Hc; discriminate).
      eapply semax_pre; [apply lgm_drop |].
      apply (lg_main_x2_ok TE lg_xstep_ok lg_main_inv_ok lg_main_tail_ok Espec a x w dd
               {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |} HG Hla Hpe Hlfx Hlx Hc HRn HRr).
Qed.
