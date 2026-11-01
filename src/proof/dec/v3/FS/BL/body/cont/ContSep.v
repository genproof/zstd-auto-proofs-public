(* FS3-bl BODY, BLCont: ZSTD_checkContinuity's pointer comparisons, from the arrays of the witness list
   [the output array; the dictionary's bytes; W]. *)
Require Import Zstd.proof.dec.v3.FS.BL.body.cont.ContPure.
Local Open Scope logic.

Section CM_ContSep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bc_arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma bc_arr_vp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d < N ->
  data_at sh (tarray tuchar N) c p |-- valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma bc_pws3 shd osz oc ob shk od W :
  pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W) =
  data_at shd (tarray tuchar osz) oc ob * (bd_res shk od * pws_pred W).
Proof. unfold pws_pred. simpl map. simpl fold_right. rewrite bd_pw_res. reflexivity. Qed.

Lemma bc_teq_same (P: mpred) v : isptr v -> (P |-- weak_valid_pointer v) -> P |-- denote_tc_test_eq v v.
Proof.
  intros Hv H. destruct v; try contradiction. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  unfold test_eq_ptrs, sameblock. destruct (peq b b); [simpl | congruence]. apply andp_right; auto.
Qed.

Lemma bc_teq_pn (P: mpred) v : isptr v -> (P |-- weak_valid_pointer v) -> P |-- denote_tc_test_eq v nullval.
Proof.
  intros Hv H. destruct v; try contradiction. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma bc_teq_np (P: mpred) v : isptr v -> (P |-- weak_valid_pointer v) -> P |-- denote_tc_test_eq nullval v.
Proof.
  intros Hv H. destruct v; try contradiction. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma bc_teq_nn (P: mpred) : P |-- denote_tc_test_eq nullval nullval.
Proof. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl. apply andp_right; apply prop_right; auto. Qed.

Lemma bc_teq_pp (P: mpred) v w : isptr v -> isptr w ->
  (P |-- valid_pointer v) -> (P |-- valid_pointer w) -> P |-- denote_tc_test_eq v w.
Proof.
  intros Hv Hw H1 H2. destruct v, w; try contradiction. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  unfold test_eq_ptrs. destruct (sameblock _ _); apply andp_right; auto;
    eapply derives_trans; try apply valid_pointer_weak; auto.
Qed.

Lemma bc_teq_sb (P: mpred) v w : sameblock v w = true ->
  (P |-- weak_valid_pointer v) -> (P |-- weak_valid_pointer w) -> P |-- denote_tc_test_eq v w.
Proof.
  intros Hs H1 H2. destruct v, w; try discriminate. Transparent denote_tc_test_eq. unfold denote_tc_test_eq; simpl.
  unfold test_eq_ptrs. rewrite Hs. apply andp_right; auto.
Qed.

(* the dictionary's end is weakly valid when ZSTD_checkContinuity moves away from it *)
Lemma bc_dict_end_wvp W d shk shd cap dst :
  bd_wf (Some d) -> readable_share shk -> bd_buf_ok W shk (Some d) shd cap dst ->
  bd_res shk (Some d) * pws_pred W |-- weak_valid_pointer (bd_end (Some d)).
Proof.
  intros Hwf Hk Hbd. destruct Hwf as [(Hds & Hb & _ & Heb & _ & Hg & _) | (Hn & _)].
  2:{ simpl bd_end. rewrite Hn. simpl. apply sepcon_weak_valid_pointer2.
      eapply derives_trans; [apply valid_pointer_null | apply valid_pointer_weak]. }
  simpl bd_end. rewrite bd_off_ptr by exact Heb.
  assert (Hr: bd_res shk (Some d) = data_at shk (tarray tuchar (Zlength (bd_b d))) (zbytes (bd_b d)) (bd_eb d))
    by (apply bytes_at_ptr; exact Heb).
  rewrite Hr.
  destruct (Z.eq_dec (Zlength (bd_b d)) 0) as [H0 | H0].
  - assert (Hg1: bd_g0 d = 0) by (destruct Hg as [? | (? & ?)]; auto; lia).
    destruct (Hbd Hg1 Heb) as [(_ & _ & Hbuf) | (_ & Hv & _)].
    + rewrite sepcon_comm.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply data_at_data_at_] |].
      eapply derives_trans; [exact Hbuf |]. apply andp_left2, derives_refl.
    + rewrite H0. destruct (bd_eb d); try contradiction. simpl offset_val. rewrite Ptrofs.add_zero.
      apply sepcon_weak_valid_pointer2. eapply derives_trans; [exact Hv | apply valid_pointer_weak].
  - apply sepcon_weak_valid_pointer1. apply bc_arr_wvp.
    + apply readable_nonidentity; auto.
    + pose proof (Zlength_nonneg (bd_b d)). lia.
    + pose proof (Zlength_nonneg (bd_b d)). lia.
Qed.

(* part 2: dst != previousDstEnd is defined (made when the capacity is > 0 and gpDictCopy = 0) *)
Lemma bc_teq W od osz0 ba fs shk shd ob osz opos oc :
  bl_hist_ok ba ob opos oc -> (ba_out ba <> None -> osz = osz0) ->
  bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob) -> writable_share shd -> readable_share shk ->
  0 <= opos -> 0 < osz - opos -> bd_wf od -> field_compatible (tarray tuchar osz) nil ob ->
  bl_lay od osz0 ba fs -> fs_gpDictCopy fs = Vint (Int.repr 0) ->
  pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W) |--
    denote_tc_test_eq (offset_val opos ob) (fs_previousDstEnd fs).
Proof.
  intros Hh Ho Hbd Hwd Hrk Hp Hc Hwf Fob Hl Hg0. rewrite bc_pws3.
  destruct (bc_fc_arr _ _ Fob ltac:(lia)) as (B & o & Eob & Hob). subst ob.
  assert (Nd: sepalg.nonidentity shd) by (apply readable_nonidentity; auto).
  assert (Wd: data_at shd (tarray tuchar osz) oc (Vptr B o) |-- weak_valid_pointer (offset_val opos (Vptr B o)))
    by (apply bc_arr_wvp; auto; lia).
  unfold bl_hist_ok in Hh.
  destruct Hl as [(Hpe & Hps & Hvs & Hde & Hg & Hout) |
                  [(ob' & f0 & Eo & Hf0 & Hpe & Hps & Hvs & Hde & Hg) |
                   (ob' & f0 & pe & Eo & Hisp & Hf & Hpe0 & Hpe & Hps & Hvs & Hde & Hg)]].
  - rewrite Hpe. destruct od as [d|].
    + destruct Hwf as [Hwf | (Hn & _)].
      2:{ simpl bd_end. rewrite Hn. cbn [bd_off]. apply bc_teq_pn; [exact I |]. apply sepcon_weak_valid_pointer1; exact Wd. }
      assert (Hg1: bd_g0 d = 0).
      { rewrite Hg0 in Hg. simpl bd_g0o in Hg. destruct Hwf as (_ & _ & _ & _ & _ & [Hd | (Hd & _)] & _); auto.
        rewrite Hd in Hg. inversion Hg. }
      destruct Hwf as (Hds & Hb & _ & Heb & _).
      assert (Hr: bd_res shk (Some d) = data_at shk (tarray tuchar (Zlength (bd_b d))) (zbytes (bd_b d)) (bd_eb d))
        by (apply bytes_at_ptr; exact Heb).
      rewrite Hr. simpl bd_end. rewrite bd_off_ptr by exact Heb.
      destruct (Hbd Hg1 Heb) as [(Hsb & Hoff & Hbuf) | (H0 & Hv & _)].
      * apply bc_teq_sb.
        { destruct (bd_eb d); try contradiction. exact Hsb. }
        { apply sepcon_weak_valid_pointer1; exact Wd. }
        { apply sepcon_weak_valid_pointer2. rewrite sepcon_comm.
          eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply data_at_data_at_] |].
          eapply derives_trans; [exact Hbuf |]. apply andp_left2, derives_refl. }
      * rewrite H0. destruct (bd_eb d) eqn:Eb; try contradiction.
        simpl offset_val at 2. rewrite Ptrofs.add_zero.
        apply bc_teq_pp; [exact I | exact I | |].
        { apply sepcon_valid_pointer1. apply bc_arr_vp; auto. lia. }
        { apply sepcon_valid_pointer2, sepcon_valid_pointer2. exact Hv. }
    + simpl bd_end. apply bc_teq_pn; [exact I |]. apply sepcon_weak_valid_pointer1; exact Wd.
  - exfalso. rewrite Eo in Hh. destruct Hh as (E1 & E2 & _ & _). subst ob' f0.
    assert (osz = osz0) by (apply Ho; congruence). lia.
  - rewrite Eo in Hh. destruct Hh as (E1 & E2 & _ & _). subst ob' pe. rewrite Hpe.
    apply bc_teq_same; [exact I |]. apply sepcon_weak_valid_pointer1; exact Wd.
Qed.

(* part 3: when the output starts a new segment *)
Lemma bc_mv W od osz0 ba fs shk shd ob osz opos oc :
  bl_hist_ok ba ob opos oc -> (ba_out ba <> None -> osz = osz0) ->
  bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob) -> readable_share shk ->
  0 <= opos <= osz -> bd_wf od -> field_compatible (tarray tuchar osz) nil ob ->
  bl_lay od osz0 ba fs -> cont_moves fs (offset_val opos ob) (osz - opos) = true ->
  isptr (offset_val opos ob) /\
  (pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W) |-- denote_tc_test_eq (fs_previousDstEnd fs) nullval) /\
  (fs_previousDstEnd fs <> nullval -> sameblock (fs_previousDstEnd fs) (fs_prefixStart fs) = true).
Proof.
  intros Hh Ho Hbd Hrk Hp Hwf Fob Hl Hm. rewrite bc_pws3.
  destruct (bc_fc_arr _ _ Fob ltac:(lia)) as (B & o & Eob & Hob). subst ob.
  split; [exact I |].
  unfold bl_hist_ok in Hh.
  destruct Hl as [(Hpe & Hps & Hvs & Hde & Hg & Hout) |
                  [(ob' & f0 & Eo & Hf0 & Hpe & Hps & Hvs & Hde & Hg) |
                   (ob' & f0 & pe & Eo & Hisp & Hf & Hpe0 & Hpe & Hps & Hvs & Hde & Hg)]].
  - rewrite Hpe, Hps. destruct od as [d|].
    + destruct Hwf as [Hwf1 | (Hn & _)].
      2:{ simpl bd_end. rewrite Hn. cbn [bd_off]. split; [apply bc_teq_nn | intros Hc; exfalso; apply Hc; reflexivity]. }
      pose proof Hwf1 as (Hds & Hb & _ & Heb & _). split.
      * apply bc_teq_pn; [simpl; destruct (bd_eb d); try contradiction; exact I |].
        apply sepcon_weak_valid_pointer2. eapply bc_dict_end_wvp; eauto. left; exact Hwf1.
      * intros _. simpl. destruct (bd_eb d); try contradiction. unfold sameblock; simpl.
        destruct (peq b b); auto.
    + split; [apply bc_teq_nn | simpl; congruence].
  - exfalso. rewrite Eo in Hh. destruct Hh as (E1 & E2 & _ & _). subst ob' f0.
    assert (osz = osz0) by (apply Ho; congruence). subst osz0.
    replace (osz - opos) with 0 in Hm by lia. discriminate Hm.
  - exfalso. rewrite Eo in Hh. destruct Hh as (E1 & E2 & _ & _). subst ob' pe.
    unfold cont_moves in Hm. rewrite Hg, Hpe, !bc_veqb_refl in Hm. simpl in Hm.
    rewrite andb_false_r in Hm. discriminate Hm.
Qed.

(* bl_cont_ok, given the dictionary array's field_compatible and D12 *)
Lemma bc_all W md od osz0 ba fs hb v shk shd ob osz opos oc shs src c :
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c -> bl_cinv md od osz0 ba fs hb v ->
  field_compatible (tarray tuchar osz) nil ob -> bc_fc od ->
  (forall d, od = Some d -> bd_de0 d = nullval -> isptr (bd_eb d) -> 0 < Zlength (bd_b d)) ->
  (fs_gpDictCopy fs = Vint (Int.repr 0) \/ fs_gpDictCopy fs = Vint (Int.repr 1)) /\
  (0 < osz - opos -> fs_gpDictCopy fs = Vint (Int.repr 0) ->
     (pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W)
        |-- denote_tc_test_eq (offset_val opos ob) (fs_previousDstEnd fs))) /\
  (cont_moves fs (offset_val opos ob) (osz - opos) = true ->
     isptr (offset_val opos ob) /\
     (pws_pred (pw_bytes shd osz oc ob :: bd_pw shk od :: W) |-- denote_tc_test_eq (fs_previousDstEnd fs) nullval) /\
     (fs_previousDstEnd fs <> nullval -> sameblock (fs_previousDstEnd fs) (fs_prefixStart fs) = true)) /\
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)).
Proof.
  intros Hpre Hci Fob Hfc D12.
  destruct Hpre as (_ & Hh & Ho & _ & _ & Hbd & Hwd & _ & Hrk & Hp & _).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwf & _ & Hl).
  split; [eapply bc_g01; eauto |].
  split; [intros; eapply bc_teq; eauto; lia |].
  split; [intros; eapply bc_mv; eauto |].
  eapply bc_lay; eauto.
Qed.

End CM_ContSep_1.
