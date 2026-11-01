(* FS3-bl BODY, stages 3/4, raw block: the output window [d, d + cap) as a separate array (copied from
   v2's body_stream_continue.v: mid_o, side_W, out_split, out_join, mid_wvp). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Local Open Scope logic.

Section CM_RawHelp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma rh_fc_arr N base :
  field_compatible (tarray tuchar N) [] base -> 0 <= N ->
  exists b ofs, base = Vptr b ofs /\ Ptrofs.unsigned ofs + N < Ptrofs.modulus.
Proof.
  intros (Hp & _ & Hs & _) HN. destruct base; try contradiction. exists b, i. split; auto.
  red in Hs. simpl in Hs. rewrite Z.max_r in Hs by lia. lia.
Qed.

Lemma rh_arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma rh_fa0_sub N p k :
  field_compatible (tarray tuchar N) [] p -> 0 <= k <= N ->
  field_address0 (Tarray tuchar N noattr) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Definition mid_o (o: outarr) : outarr :=
  {| oa_sh := oa_sh o; oa_base := offset_val (oa_d o) (oa_base o); oa_N := oa_cap o;
     oa_c := sublist (oa_d o) (oa_d o + oa_cap o) (oa_c o); oa_d := 0; oa_cap := oa_cap o |}.

Definition side_W (o: outarr) : list ptr_witness :=
  [pw_bytes (oa_sh o) (oa_d o) (sublist 0 (oa_d o) (oa_c o)) (oa_base o);
   pw_bytes (oa_sh o) (oa_N o - (oa_d o + oa_cap o)) (sublist (oa_d o + oa_cap o) (oa_N o) (oa_c o))
     (offset_val (oa_d o + oa_cap o) (oa_base o))].

Lemma mid_ok o : outarr_ok o -> outarr_ok (mid_o o).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc). unfold mid_o, outarr_ok; cbn.
  split; [auto |]. split; [rewrite Zlength_sublist; lia |]. repeat split; lia.
Qed.

Lemma pws_app W1 W2 : pws_pred (W1 ++ W2) = (pws_pred W1 * pws_pred W2)%logic.
Proof.
  induction W1; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. auto.
  - unfold pws_pred in *. simpl. rewrite IHW1. rewrite sepcon_assoc. auto.
Qed.

Lemma pws_app_fold W1 W2 : pws_pred W1 * pws_pred W2 |-- pws_pred (W1 ++ W2).
Proof. rewrite pws_app. apply derives_refl. Qed.

Lemma pws_app_unfold W1 W2 : pws_pred (W1 ++ W2) |-- pws_pred W1 * pws_pred W2.
Proof. rewrite pws_app. apply derives_refl. Qed.

Lemma out_split o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o) =
  (pws_pred (side_W o) *
   data_at (oa_sh (mid_o o)) (tarray tuchar (oa_N (mid_o o))) (oa_c (mid_o o)) (offset_val (oa_d o) (oa_base o)))%logic.
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc. unfold side_W, mid_o, pws_pred; cbn.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar (oa_sh o) (oa_N o) (oa_d o) (oa_d o + oa_cap o)) by lia.
  rewrite !rh_fa0_sub by (auto; lia). replace (oa_d o + oa_cap o - oa_d o) with (oa_cap o) by lia.
  rewrite sepcon_emp. apply pred_ext; cancel.
Qed.

Lemma out_unsplit o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  pws_pred (side_W o) * data_at (oa_sh o) (tarray tuchar (oa_cap o)) (oa_c (mid_o o)) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o).
Proof. intros. rewrite (out_split o) by auto. apply derives_refl. Qed.

Lemma out_join o (bs: list Z) :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> Zlength bs <= oa_cap o ->
  pws_pred (side_W o) *
  data_at (oa_sh o) (tarray tuchar (oa_cap o)) (put_bytes (oa_c (mid_o o)) 0 bs) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o).
Proof.
  intros Ho Fc Hb. pose proof Ho as (Hs & Hc & HN & Hd & Hcap & Hdc). pose proof (Zlength_nonneg bs).
  assert (Hz: Zlength (zbytes bs) = Zlength bs) by apply Zlength_map.
  assert (Lp: Zlength (put_bytes (oa_c o) (oa_d o) bs) = oa_N o)
    by (unfold put_bytes; rewrite !Zlength_app, Hz, !Zlength_sublist by lia; lia).
  set (o2 := {| oa_sh := oa_sh o; oa_base := oa_base o; oa_N := oa_N o;
      oa_c := put_bytes (oa_c o) (oa_d o) bs; oa_d := oa_d o; oa_cap := oa_cap o |}).
  change (data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o))
    with (data_at (oa_sh o2) (tarray tuchar (oa_N o2)) (oa_c o2) (oa_base o2)).
  rewrite (out_split o2) by (subst o2; first [assumption | split; [exact Hs |]; split; [exact Lp |]; cbn; repeat split; lia]).
  subst o2.
  unfold side_W, mid_o, pws_pred; cbn [map fold_right oa_sh oa_base oa_N oa_c oa_d oa_cap pw_pred].
  rewrite !sepcon_emp. unfold put_bytes.
  apply sepcon_derives; [apply sepcon_derives |]; apply derives_refl'; f_equal; list_solve.
Qed.

Lemma mid_wvp o W :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> oa_cap o = 0 ->
  (oa_N o = 0 -> (pws_pred W |-- weak_valid_pointer (oa_base o))) ->
  pws_pred (W ++ side_W o) |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc H0 HW. rewrite pws_app.
  assert (Hni: sepalg.nonidentity (oa_sh o)) by (apply readable_nonidentity, writable_readable; auto).
  destruct (zlt 0 (oa_d o)).
  - apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer1.
    apply rh_arr_wvp; auto; lia.
  - destruct (zlt 0 (oa_N o)).
    + apply sepcon_weak_valid_pointer2. unfold side_W, pws_pred; simpl. apply sepcon_weak_valid_pointer2.
      apply sepcon_weak_valid_pointer1. rewrite H0, Z.add_0_r.
      destruct (rh_fc_arr _ _ Fc ltac:(lia)) as (bb & ofs & -> & _).
      rewrite <- (isptr_offset_val_zero (offset_val (oa_d o) (Vptr bb ofs))) at 2 by exact I.
      apply rh_arr_wvp; auto; lia.
    + apply sepcon_weak_valid_pointer1.
      replace (oa_d o) with 0 by lia. rewrite isptr_offset_val_zero by (destruct Fc; auto).
      apply HW; lia.
Qed.

(* osz = 0: buf_ok gives the weak validity of ob from W alone *)
Lemma buf0_wvp W sh ob :
  buf_ok W sh 0 ob -> field_compatible (tarray tuchar 0) [] ob -> pws_pred W |-- weak_valid_pointer ob.
Proof.
  intros Hb Fc. eapply derives_trans; [| eapply derives_trans; [apply Hb | apply andp_left1, derives_refl]].
  rewrite <- (sepcon_emp (pws_pred W)) at 1. apply sepcon_derives; [apply derives_refl |].
  rewrite data_at__eq. rewrite data_at_zero_array_eq; auto.
Qed.

End CM_RawHelp_1.
