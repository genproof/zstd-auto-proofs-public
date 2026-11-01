(* FS3: ZSTD_DCtx_selectFrameDDict. *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

Section CM_body3_select_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* for (;;break) {} (DEBUGLOG): a no-op *)
Lemma sel_skipbreak_seq : forall {Espec: OracleKind} {cs: compspecs} Delta (P: environ -> mpred) c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros Espec cs Delta P c R H.
apply semax_seq with P; [|exact H].
apply semax_loop with P.
2: { eapply semax_pre; [|apply semax_break]. destruct R; unfold loop2_ret_assert, overridePost. cbv beta iota.
     apply andp_left2, derives_refl. }
eapply semax_post; [| | | | apply semax_skip].
all: destruct R; unfold normal_ret_assert, loop1_ret_assert, overridePost.
- intros rho; simpl; apply andp_left2, derives_refl.
- intros rho; simpl; apply andp_left2, FF_left.
- intros rho; simpl; apply andp_left2, FF_left.
- intros vl rho; simpl; apply andp_left2, FF_left.
Qed.

Transparent denote_tc_test_eq.
Lemma sel_test_eq_null_weak: forall P x, isptr x -> P |-- weak_valid_pointer x -> P |-- denote_tc_test_eq x nullval.
Proof.
  intros P x Hx H. destruct x; try contradiction. unfold denote_tc_test_eq, nullval. simpl.
  apply andp_right; [apply prop_right; auto | auto].
Qed.

Lemma sel_test_eq_null_null: forall P, P |-- denote_tc_test_eq nullval nullval.
Proof. intros. unfold denote_tc_test_eq, nullval. simpl. apply andp_right; apply prop_right; auto. Qed.
Opaque denote_tc_test_eq.

Lemma sel_ddict_rep_at_valid (DENT: dent_pred) gv x buf :
  ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  unfold ddict_rep_at, ddict_struct. Intros.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
  entailer!.
Qed.

Lemma sel_ddict_any_valid (q: val) : ddict_any q |-- valid_pointer q.
Proof.
  unfold ddict_any, ddict_failed. Intros n db.
  sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) db q); auto.
  repeat apply sepcon_valid_pointer1; apply derives_refl.
Qed.

Lemma sel_local_valid (DENT: dent_pred) gv q lx :
  q <> nullval -> local_rep DENT gv q lx |-- valid_pointer q.
Proof.
  intros Hq. unfold local_rep. rewrite if_false by auto.
  destruct lx as [[x buf]|].
  - Intros. subst q. apply sel_ddict_rep_at_valid.
  - apply sel_ddict_any_valid.
Qed.

Lemma sel_local_isptr (DENT: dent_pred) gv q lx :
  q <> nullval -> local_rep DENT gv q lx |-- !! isptr q.
Proof.
  intros Hq. unfold local_rep. rewrite if_false by auto.
  destruct lx as [[x buf]|].
  - Intros. subst q. unfold ddict_rep_at, ddict_struct. Intros. entailer!.
  - unfold ddict_any, ddict_failed. Intros n db. entailer!.
Qed.

(* the dictBuffer field (offset 0) of a DDict gives the weak validity zstd's NULL tests need *)
Lemma sel_db_wvp (q v: val) : field_at Ews t_ddict (DOT _dictBuffer) v q |-- weak_valid_pointer q.
Proof.
  eapply derives_trans; [| apply valid_pointer_weak].
  apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
  simpl; lia.
Qed.

Lemma sel_set_wvp l q :
  In q (map fst l) -> set_ids l |-- weak_valid_pointer q.
Proof.
  induction l as [|[q0 dd] l IH]; simpl; intros Hin; [contradiction|].
  unfold set_ids; simpl. destruct Hin as [<-|Hin].
  - unfold ddid. apply sepcon_weak_valid_pointer1. Intros. apply sepcon_weak_valid_pointer1. apply sel_db_wvp.
  - apply sepcon_weak_valid_pointer2. apply IH; auto.
Qed.

Lemma sel_probe_f_in l tbl id : hs_inv l tbl ->
  forall fuel j, 0 <= j < Zlength tbl ->
  hs_probe_f fuel l tbl j (Zlength tbl) id = nullval \/ In (hs_probe_f fuel l tbl j (Zlength tbl) id) (map fst l).
Proof.
  intros Hinv. destruct Hinv as (_ & _ & _ & _ & _ & _ & Hperm & _).
  induction fuel as [|f IH]; intros j Hj; simpl; [left; reflexivity|].
  destruct (EqDec_val (Znth j tbl) nullval) as [E|E]; [left; reflexivity|].
  destruct (orb _ _).
  - right. eapply Permutation_in; [exact Hperm|]. apply filter_In. split.
    + apply Znth_In; auto.
    + unfold veqb. destruct (Val.eq (Znth j tbl) nullval); [contradiction | reflexivity].
  - apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma sel_probe_in l tbl id : hs_inv l tbl ->
  hs_probe l tbl id = nullval \/ In (hs_probe l tbl id) (map fst l).
Proof.
  intros Hinv. unfold hs_probe. apply sel_probe_f_in; auto.
  destruct Hinv as ((k & Hk & Hn) & _).
  unfold hs_home. rewrite Hn.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma sel_in_isptr l tbl q : hs_inv l tbl -> In q (map fst l) -> isptr q.
Proof.
  intros Hinv Hin. destruct Hinv as (_ & _ & _ & _ & _ & Hp & _).
  apply list_in_map_inv in Hin. destruct Hin as [e [-> He]].
  rewrite Forall_forall in Hp. apply Hp; auto.
Qed.

Lemma sel_dgroup_fold (DENT: dent_pred) gv p d :
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p * field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p * local_rep DENT gv (df_local d) (df_lx d)
  |-- dgroup DENT gv p d.
Proof. unfold dgroup. cancel. Qed.

Lemma sel_cur_wvp (DENT: dent_pred) gv d l xq :
  df_ddict d <> nullval ->
  (df_ddict d = nullval \/ df_ddict d = df_local d \/ In (df_ddict d) (map fst l) \/ exists v, xq = Some (df_ddict d, v)) ->
  local_rep DENT gv (df_local d) (df_lx d) * set_ids l * opt_token xq |-- weak_valid_pointer (df_ddict d).
Proof.
  intros N [E|[E|[E|E]]]; [contradiction | | |].
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer1. rewrite E.
    eapply derives_trans; [apply sel_local_valid; congruence | apply valid_pointer_weak].
  - apply sepcon_weak_valid_pointer1, sepcon_weak_valid_pointer2. apply sel_set_wvp; auto.
  - apply sepcon_weak_valid_pointer2. destruct E as [v E]. rewrite E. unfold opt_token. apply sel_db_wvp.
Qed.

Lemma sel_wvp_frame (P Q: mpred) x : P |-- weak_valid_pointer x -> P * Q |-- weak_valid_pointer x.
Proof. apply sepcon_weak_valid_pointer1. Qed.

Lemma bodies_select3_gap :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_selectFrameDDict_spec DENT).
Proof.
  intros DENT TABS SR BR HD HT.
  exists f_ZSTD_DCtx_selectFrameDDict; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  rename H3 into Hlm, H4 into Hcm, H5 into Hhb.
  apply sel_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
  assert_PROP (hs_inv l tbl) as Hinv by (unfold hset_tbl; Intros tp; entailer!).
  unfold dgroup. Intros.
  assert (Hcur := H2). destruct H2 as [Huses Hc].
  assert_PROP (df_ddict d <> nullval -> isptr (df_ddict d)) as Hptr.
  { destruct Hc as [E|[E|[E|E]]].
    - entailer!; intros C; contradiction.
    - rewrite E. destruct (eq_dec (df_local d) nullval) as [N|N]; [entailer!; intros C; contradiction|].
      sep_apply (sel_local_isptr DENT gv (df_local d) (df_lx d) N). entailer!.
    - entailer!; try intros _. eapply sel_in_isptr; eauto.
    - destruct E as [v E]. rewrite E. unfold opt_token. entailer!. }
  forward.
  { entailer!. destruct (eq_dec (df_ddict d) nullval) as [N|N]; [rewrite N; simpl; auto|]. apply Hptr in N.
    destruct (df_ddict d); try contradiction; exact I. }
  forward_if.
  { destruct (eq_dec (df_ddict d) nullval) as [N|N]; [rewrite N; apply sel_test_eq_null_null|].
    apply sel_test_eq_null_weak; auto.
    apply derives_trans with (local_rep DENT gv (df_local d) (df_lx d) * set_ids l * opt_token xq * TT);
      [cancel | apply sel_wvp_frame, sel_cur_wvp; auto]. }
  { (* a current DDict: look the frame's ID up *)
    assert (Hp: isptr (df_ddict d)) by exact H2. clear H2.
    assert (N: df_ddict d <> nullval) by (intros E; rewrite E in Hp; exact Hp).
    forward.
    { unfold hset_tbl. Intros tp. entailer!. }
    unfold frame_fields. Intros. forward.
    match goal with |- context [tc_val tuint ?v] => change v with (fp_dictID (fs_fParams fs)) end.
    rewrite H. entailer!.
    match goal with |- context [temp _t'5 ?v] => change v with (fp_dictID (fs_fParams fs)) end.
    rewrite H. forward_call (sp, l, tbl, id, am).
    assert (Hrin := sel_probe_in l tbl id Hinv).
    remember (hs_probe l tbl id) as r eqn:Er.
    assert (Hr: r = nullval \/ isptr r).
    { destruct Hrin as [E|E]; [left; auto | right; eapply sel_in_isptr; eauto]. }
    forward.
    forward_if.
    { destruct Hrin as [E|E]; [rewrite E; apply sel_test_eq_null_null|].
      apply sel_test_eq_null_weak; [eapply sel_in_isptr; eauto|].
      apply derives_trans with (set_ids l * TT); [cancel | apply sel_wvp_frame, sel_set_wvp; auto]. }
    { (* found: clear the dictionary, reference the set's DDict *)
      assert (Nr: r <> nullval) by (intros E; rewrite E in H2; exact H2).
      apply sel_skipbreak_seq. unfold MORE_COMMANDS, abbreviate.
      sep_apply (sel_dgroup_fold DENT gv p d).
      forward_call (gv, p, d, am, hb).
      unfold dgroup, df_none, local_rep. cbn [df_local df_ddict df_uses df_lx].
      rewrite if_true by auto. Intros.
      forward.
      match goal with |- context [tc_val tuint ?v] => change v with (fp_dictID (fs_fParams fs)) end.
      rewrite H. entailer!.
      match goal with |- context [temp _t'3 ?v] => change v with (fp_dictID (fs_fParams fs)) end.
      rewrite H.
      forward. forward. forward.
      replace (sel_r d l tbl id) with r by (unfold sel_r; rewrite if_false by auto; auto).
      rewrite (if_false (r = nullval)) by auto.
      replace (sel_dict d r) with (switch_fields r) by (unfold sel_dict; rewrite if_false by auto; auto).
      assert (E0: local_held (switch_fields r) = 0)
        by (unfold local_held, switch_fields; simpl; destruct (eq_dec nullval nullval); [reflexivity | contradiction]).
      rewrite E0, Z.add_0_r.
      unfold switch_fields; cbn [df_local df_ddict df_uses df_lx].
      rewrite if_true by auto.
      unfold frame_fields, fsu_dictID; cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart
        fs_dictEnd fs_expected fs_fParams fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize
        fs_validateChecksum fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
      entailer!. }
    { (* not found: nothing changes *)
      assert (Er0: r = nullval) by (destruct Hr as [E|E]; auto; destruct r; try contradiction; discriminate).
      forward.
      replace (sel_r d l tbl id) with nullval by (unfold sel_r; rewrite if_false by auto; congruence).
      rewrite if_true by auto. unfold sel_dict. rewrite if_true by auto.
      unfold dgroup, frame_fields. entailer!. } }
  { (* no current DDict: nothing changes *)
    assert (E: df_ddict d = nullval) by exact H2.
    forward.
    replace (sel_r d l tbl id) with nullval by (unfold sel_r; rewrite if_true by auto; auto).
    rewrite if_true by auto. unfold sel_dict. rewrite if_true by auto.
    unfold dgroup. entailer!. }
Qed.

Lemma bodies_select3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_selectFrameDDict_spec DENT).
Proof. exact bodies_select3_gap. Qed.

End CM_body3_select_1.
