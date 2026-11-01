(* FS3 load3: the DDicts of a context's set, as the caller holds them (Spec_api6 dict_res + set_res), lend the
   dictIDs zstd's hash set reads (set_ids), and are distinct from any other DDict the caller holds *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_Load3Set_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition load3_set_facts : Prop :=
  (forall DENT gv sh st, set_cur_ok st -> NoDup (map fst (dc_set st)) ->
     dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st) |--
     set_ids (dc_set st) *
     (set_ids (dc_set st) -* (dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st)))) /\
  (forall DENT gv sh st q dd,
     DD3x DENT gv q dd * dict_res (DD3x DENT) gv sh (dc_dict st) * set_res (DD3x DENT) gv sh (dc_set st) (dc_dict st) |--
     !! (~ In q (map fst (dc_set st)))).

(* P lends Q: P holds Q and gets P back from it *)
Definition l3s_borrow (P Q: mpred) : Prop := P |-- Q * (Q -* P).

Lemma l3s_borrow_intro: forall P Q R, P |-- Q * R -> Q * R |-- P -> l3s_borrow P Q.
Proof.
  intros. unfold l3s_borrow. eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. auto.
Qed.

Lemma l3s_borrow_emp: l3s_borrow emp emp.
Proof.
  apply (l3s_borrow_intro _ _ emp); rewrite sepcon_emp; auto.
Qed.

Lemma l3s_borrow_sep: forall P1 Q1 P2 Q2, l3s_borrow P1 Q1 -> l3s_borrow P2 Q2 -> l3s_borrow (P1 * P2) (Q1 * Q2).
Proof.
  unfold l3s_borrow; intros.
  eapply derives_trans; [apply sepcon_derives; [apply H|apply H0]|].
  eapply derives_trans; [|apply sepcon_derives; [apply derives_refl|apply wand_frame_hor]].
  rewrite <- !sepcon_assoc. apply sepcon_derives; [|apply derives_refl].
  rewrite (sepcon_comm (Q1 * _) Q2), <- sepcon_assoc, (sepcon_comm Q2 Q1). auto.
Qed.

Lemma l3s_borrow_emp_l: forall P, l3s_borrow P emp.
Proof.
  intros. unfold l3s_borrow. rewrite emp_sepcon. apply wand_sepcon_adjoint. rewrite sepcon_emp; auto.
Qed.

Lemma l3s_borrow_frame: forall P Q R, l3s_borrow P Q -> l3s_borrow (P * R) Q.
Proof.
  intros. rewrite <- (sepcon_emp Q). apply l3s_borrow_sep; auto. apply l3s_borrow_emp_l.
Qed.


Lemma l3s_borrow_list: forall {A} (P Q: A -> mpred) (l: list A),
  (forall e, In e l -> l3s_borrow (P e) (Q e)) ->
  l3s_borrow (fold_right sepcon emp (map P l)) (fold_right sepcon emp (map Q l)).
Proof.
  induction l; simpl; intros.
  - apply l3s_borrow_emp.
  - apply l3s_borrow_sep; auto.
Qed.

Lemma l3s_fold_app: forall (l1 l2: list mpred),
  fold_right sepcon emp (l1 ++ l2) = fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros. rewrite emp_sepcon; auto. rewrite IHl1, sepcon_assoc; auto.
Qed.

Lemma l3s_intro': forall A B R C, A |-- B * R -> R * B |-- C -> A |-- B * (B -* C).
Proof.
  intros. eapply derives_trans; [apply H|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. auto.
Qed.

Lemma l3s_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| b l IH]; intros Hb; simpl; [lia |].
  inversion Hb as [| ? ? Hb1 Hb2]; subst. specialize (IH Hb2). unfold is_byte in Hb1.
  rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma l3s_le_field_4_range: forall l i, bytes_ok l -> 0 <= le_field l i 4 <= Int.max_unsigned.
Proof.
  intros. unfold le_field, slice.
  assert (Hok: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn. auto. }
  pose proof (l3s_le_value_range _ Hok).
  assert (Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 256 ^ 4)
    by (apply Z.pow_le_mono_r; [lia | auto]).
  rep_lia.
Qed.

Lemma l3s_dict_id_of_range: forall b, bytes_ok b -> 0 <= dict_id_of b <= Int.max_unsigned.
Proof.
  intros. unfold dict_id_of. destruct (Zlength b <? 8); [rep_lia |].
  destruct (negb _); [rep_lia | apply l3s_le_field_4_range; auto].
Qed.

(* the dictBuffer field of DD3_of's ddx is ddb *)
Lemma l3s_dd_x_buf q dd : (if ddx_copied (dd_x q dd) then dd_buf dd else nullval) = ddb dd.
Proof. unfold ddx_copied, dd_x, ddb; simpl. destruct (dd_xref dd); reflexivity. Qed.

Lemma l3s_ddid_valid q id db : ddid q id db |-- valid_pointer q.
Proof. unfold ddid. Intros. apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; reflexivity. Qed.

(* one DDict lends its dictBuffer and dictID fields *)
Lemma l3s_dd_borrow: forall DENT gv q dd, l3s_borrow (DD3x DENT gv q dd) (ddid q (dd_id dd) (ddb dd)).
Proof.
  intros. unfold l3s_borrow, DD3x, DD3_of, ddict_rep_at, ddict_struct.
  Intros. rewrite !l3s_dd_x_buf.
  assert (Hr: 0 <= dd_id dd <= Int.max_unsigned) by (apply l3s_dict_id_of_range; auto).
  change (dx_raw (dd_x q dd)) with false. change (dx_bytes (dd_x q dd)) with (dd_bytes dd). change (dx_q (dd_x q dd)) with q.
  cbv iota. change (dict_id_of (dd_bytes dd)) with (dd_id dd).
  match goal with |- (?Fb * ?Fc * ?Fs * ?Fid * ?Fe * ?Fm) * ?D * ?M * ?P |-- _ =>
    apply (l3s_intro' _ _ (Fc * Fs * Fe * Fm * D * M * P)) end.
  - unfold ddid, t_ddict. rewrite prop_true_andp by auto. cancel.
  - unfold ddid, t_ddict. Intros. rewrite prop_true_andp by (repeat split; auto). cancel.
Qed.

Lemma l3s_dd_valid DENT gv q dd : DD3x DENT gv q dd |-- valid_pointer q.
Proof.
  eapply derives_trans; [apply l3s_dd_borrow |]. apply sepcon_valid_pointer1. apply l3s_ddid_valid.
Qed.

Lemma l3s_ddv_borrow: forall DENT gv q dd,
  l3s_borrow (DD3x DENT gv q dd && valid_pointer q) (ddid q (dd_id dd) (ddb dd)).
Proof.
  intros. unfold l3s_borrow. eapply derives_trans; [apply andp_left1, l3s_dd_borrow |].
  apply sepcon_derives; [apply derives_refl |]. apply wand_derives; [apply derives_refl |].
  apply andp_right; [apply derives_refl | apply l3s_dd_valid].
Qed.

Lemma l3s_ddres_borrow: forall DENT gv sh q dd,
  l3s_borrow (ddict_res (DD3x DENT) gv sh q dd) (ddid q (dd_id dd) (ddb dd)).
Proof.
  intros. unfold ddict_res. apply l3s_borrow_frame. apply l3s_ddv_borrow.
Qed.

Lemma l3s_set_res_nocur: forall DD gv sh l d,
  (forall e, In e l -> cur_ddict d <> Some (fst e)) ->
  set_res DD gv sh l d = fold_right sepcon emp (map (fun e => ddict_res DD gv sh (fst e) (snd e)) l).
Proof.
  intros. unfold set_res. f_equal. apply map_ext_in. intros e He.
  destruct (cur_ddict d) as [q0|] eqn:Hc; auto.
  destruct (Val.eq (fst e) q0); auto. subst q0. exfalso; apply (H e He); auto.
Qed.

Lemma l3s_res_borrow: forall DENT gv sh d l,
  (forall dr q dd dd', d = Some dr -> dr_src dr = DSDDict q dd -> In (q, dd') l -> dd' = dd) ->
  NoDup (map fst l) ->
  l3s_borrow (dict_res (DD3x DENT) gv sh d * set_res (DD3x DENT) gv sh l d) (set_ids l).
Proof.
  intros DENT gv sh d l Hcur Hnd.
  assert (Hall: (forall e, In e l -> cur_ddict d <> Some (fst e)) ->
     l3s_borrow (dict_res (DD3x DENT) gv sh d * set_res (DD3x DENT) gv sh l d) (set_ids l)).
  { intros H. rewrite l3s_set_res_nocur by auto. rewrite sepcon_comm. apply l3s_borrow_frame.
    unfold set_ids. apply l3s_borrow_list. intros. apply l3s_ddres_borrow. }
  destruct (in_dec Val.eq (match cur_ddict d with Some q0 => q0 | None => Vundef end) (map fst l)) as [Hin|Hnin].
  2:{ apply Hall. intros e He Hc. rewrite Hc in Hnin. apply Hnin. apply in_map; auto. }
  destruct (cur_ddict d) as [q0|] eqn:Hc.
  2:{ apply Hall. intros e He Hc'. discriminate. }
  destruct d as [dr|]; [|discriminate]. simpl in Hc.
  destruct (dr_src dr) as [| |q1 dd1] eqn:Hs; try discriminate. inv Hc.
  apply in_map_iff in Hin. destruct Hin as [[q0' dd0] [Hq Hin]]. simpl in Hq. subst q0'.
  pose proof (Hcur dr q0 dd1 dd0 eq_refl Hs Hin) as Hdd.
  apply in_split in Hin. destruct Hin as [l1 [l2 Hl]]. subst l.
  rewrite map_app in Hnd. simpl in Hnd.
  assert (H1: ~ In q0 (map fst l1)).
  { intro. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app; auto. }
  assert (H2: ~ In q0 (map fst l2)).
  { intro. apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app; auto. }
  assert (Hr: forall l', ~ In q0 (map fst l') ->
     set_res (DD3x DENT) gv sh l' (Some dr) =
     fold_right sepcon emp (map (fun e => ddict_res (DD3x DENT) gv sh (fst e) (snd e)) l')).
  { intros. apply l3s_set_res_nocur. intros e He Hc. simpl in Hc. rewrite Hs in Hc. inv Hc.
    apply H. apply in_map; auto. }
  assert (Hsplit: set_res (DD3x DENT) gv sh (l1 ++ (q0, dd0) :: l2) (Some dr) =
     set_res (DD3x DENT) gv sh l1 (Some dr) * set_res (DD3x DENT) gv sh l2 (Some dr)).
  { unfold set_res at 1. rewrite map_app, l3s_fold_app. simpl.
    rewrite Hs. destruct (Val.eq q0 q0); [|congruence]. rewrite emp_sepcon. unfold set_res; simpl; rewrite Hs; reflexivity. }
  rewrite Hsplit, (Hr l1 H1), (Hr l2 H2).
  unfold set_ids. rewrite map_app, l3s_fold_app. simpl.
  unfold dict_res. rewrite Hs. subst dd0. simpl.
  match goal with |- l3s_borrow (?X * (?F1 * ?F2)) (?I1 * (?I * ?I2)) =>
    replace (X * (F1 * F2)) with (F1 * (X * F2)) by (apply pred_ext; cancel) end.
  apply l3s_borrow_sep; [apply l3s_borrow_list; intros; apply l3s_ddres_borrow|].
  apply l3s_borrow_sep; [apply l3s_ddres_borrow | apply l3s_borrow_list; intros; apply l3s_ddres_borrow].
Qed.

(* two DDicts at one address conflict on the dictID field *)
Lemma l3s_dd_dd: forall DENT gv q dd dd', DD3x DENT gv q dd * DD3x DENT gv q dd' |-- FF.
Proof.
  intros.
  assert (Hd: forall dd0, DD3x DENT gv q dd0 |-- ddid q (dd_id dd0) (ddb dd0) * TT).
  { intros. eapply derives_trans; [apply l3s_dd_borrow|]. apply sepcon_derives; auto. }
  eapply derives_trans; [apply sepcon_derives; apply Hd|].
  unfold ddid. Intros.
  match goal with |- ?A * ?B * ?T * (?A' * ?B' * ?T') |-- _ =>
    eapply derives_trans with (Q := (A * A') * (B * B' * T * T')); [cancel|] end.
  eapply derives_trans; [apply sepcon_derives; [apply field_at_conflict|apply derives_refl]|].
  - apply readable_nonidentity; auto.
  - simpl. lia.
  - rewrite FF_sepcon. auto.
Qed.

Lemma l3s_held: forall DENT gv sh d l q, In q (map fst l) ->
  dict_res (DD3x DENT) gv sh d * set_res (DD3x DENT) gv sh l d |-- EX dd, DD3x DENT gv q dd * TT.
Proof.
  intros. destruct (cur_ddict d) as [q0|] eqn:Hc.
  - destruct (Val.eq q q0).
    + subst q0. destruct d as [dr|]; [|discriminate]. simpl in Hc.
      destruct (dr_src dr) as [| |q1 dd1] eqn:Hs; try discriminate. inv Hc.
      unfold dict_res. rewrite Hs. unfold ddict_res. Exists dd1.
      eapply derives_trans with ((DD3x DENT gv q dd1 && valid_pointer q) * TT); [cancel |].
      apply sepcon_derives; [apply andp_left1, derives_refl | auto].
    + apply in_map_iff in H. destruct H as [[q' dd] [Hq Hin]]. simpl in Hq. subst q'.
      apply in_split in Hin. destruct Hin as [l1 [l2 Hl]]. subst l.
      unfold set_res. rewrite map_app, l3s_fold_app. simpl. rewrite Hc.
      destruct (Val.eq q q0); [congruence|]. unfold ddict_res. Exists dd.
      eapply derives_trans with ((DD3x DENT gv q dd && valid_pointer q) * TT); [cancel |].
      apply sepcon_derives; [apply andp_left1, derives_refl | auto].
  - apply in_map_iff in H. destruct H as [[q' dd] [Hq Hin]]. simpl in Hq. subst q'.
    apply in_split in Hin. destruct Hin as [l1 [l2 Hl]]. subst l.
    unfold set_res. rewrite map_app, l3s_fold_app. simpl. rewrite Hc.
    unfold ddict_res. Exists dd.
    eapply derives_trans with ((DD3x DENT gv q dd && valid_pointer q) * TT); [cancel |].
    apply sepcon_derives; [apply andp_left1, derives_refl | auto].
Qed.

Lemma load3_set_ok : load3_set_facts.
Proof.
  split.
  - intros DENT gv sh st Hcur Hnd. apply l3s_res_borrow; auto.
  - intros DENT gv sh st q dd.
    destruct (in_dec Val.eq q (map fst (dc_set st))) as [Hin|Hnin].
    + rewrite sepcon_assoc. eapply derives_trans; [apply sepcon_derives; [apply derives_refl|apply (l3s_held DENT gv sh _ _ q Hin)]|].
      Intros dd'. rewrite <- sepcon_assoc. eapply derives_trans; [apply sepcon_derives; [apply l3s_dd_dd|apply derives_refl]|].
      rewrite FF_sepcon. apply FF_left.
    + apply prop_right; auto.
Qed.

End CM_Load3Set_1.
