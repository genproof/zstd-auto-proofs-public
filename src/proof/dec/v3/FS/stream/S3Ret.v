(* FS3 streaming: the error returns RET3 (S3RetStmts; template v2 StreamRet.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3RetStmts.
Local Open Scope logic.

Section CM_S3Ret_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ret3_prefix_app_l : forall (p q s: list Z), is_prefix (p ++ q) s -> is_prefix p s.
Proof.
unfold is_prefix; intros p q s H.
pose proof (firstn_skipn (length (p ++ q)) s) as E. rewrite H in E. rewrite <- E, <- app_assoc.
rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity.
Qed.

Lemma ret3_err_post : forall (a: dsa) (oc': list val) (r ip: Z),
  dsa_ok a -> start_ok a -> err_why a r ->
  (ip = a_ipos a \/ (ip = a_isz a /\ ss_ahead (dc_ss (a_st a)) = 0)) ->
  Zlength oc' = a_osz a -> sublist 0 (a_opos a) oc' = sublist 0 (a_opos a) (a_oc a) ->
  stream_post (a_st a) (ret_st a r ip) r (a_obf a) (a_osz a) (a_opos a) (a_opos a) (a_oc a) oc' (a_ibs a)
    (a_isz a) (a_ipos a) ip.
Proof.
intros a oc' r ip Hok Hst Hwhy Hip Hoc Hpre.
destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hopos & _ & _ & Hipos & _ & Hlen & _).
destruct Hst as (Hcont & Hah & Hahlen & _).
destruct Hwhy as [Hde Hwhy]. pose proof Hde as (Herr & Hn80 & Hn82).
assert (Hr0: r <> 0) by (intro; subst r; discriminate Herr).
assert (Hall: ss_in (dc_ss (a_st a)) ++
          sublist (a_ipos a + ss_ahead (dc_ss (a_st a))) (ip + ss_ahead (dc_ss (a_st a))) (a_ibs a) ++
          sublist (ip + ss_ahead (dc_ss (a_st a))) (a_isz a) (a_ibs a) = a_all a).
{ unfold a_all. f_equal. destruct Hip as [-> | [-> H0]].
  - rewrite sublist_nil. reflexivity.
  - rewrite H0, !Z.add_0_r. apply sublist_rejoin; lia. }
unfold stream_post.
exists nil, (ss_stall (dc_ss (a_st a))), (ss_ahead (dc_ss (a_st a))).
cbv zeta.
repeat split; try lia; try assumption.
all: try (intros H; rewrite Herr in H; discriminate).
all: try (intros _ H; rewrite Herr in H; discriminate).
all: try (rewrite sublist_nil; reflexivity).
all: try apply Forall_nil.
all: try (destruct Hip as [-> | [-> ?]]; lia).
all: try (unfold stall_ok; intros [H|H]; contradiction).
all: try (intros _ _; rewrite Z.sub_diag; unfold ZSTD_BLOCKSIZE_MAX; lia).
all: try (unfold ret_st; rewrite ?app_nil_r; reflexivity).
all: try (destruct Hip as [-> | [-> H0]]; [right; reflexivity | left; lia]).
all: try (match goal with H: is_error_code _ = false |- _ => rewrite Herr in H; discriminate end).
all: try (intros Ht; rewrite app_nil_r; apply Hcont; auto;
          match goal with Hp: is_prefix (_ ++ _) _ |- _ => eapply ret3_prefix_app_l; exact Hp end).
all: try (intros _ Hf0; rewrite Herr in Hf0; discriminate).
all: try (match goal with Hb: bytes_ok ?s |- _ =>
  intros Hsall Ht _ e He; rewrite <- app_assoc, Hall in Hsall;
  destruct Hwhy as [Hm | [Hf | (Hstab & Hsm)]];
  [ left; unfold ZSTD_error_memory_allocation in *; lia
  | exfalso; exact (Hf s Hb Hsall Ht)
  | right; right; right; exists (a_osz a); rewrite Hstab; split; auto ] end).
all: try (rewrite Zlength_nil; lia).
all: try (match goal with Hsm: forall s0, _ -> _ -> _ -> _ < _ |- _ => apply Hsm; auto end).
(* stream_zero_ref: an error is not 0 *)
all: try (intros ? _ _ _ H0; contradiction (Hr0 H0)).
Qed.

Lemma ret3_err_base : forall (a: dsa) (k: cst3) (r ip: Z),
  dsa_ok a -> is_error_code r = true -> base_call (a_st a) k -> base_rel3 (ret_st a r ip) k.
Proof.
intros a k r ip Hok Herr Hb.
pose proof (dsa_ok_mem a Hok) as Hm.
destruct Hok as (_ & _ & _ & _ & _ & _ & _ & Hdict & _).
destruct Hdict as (_ & _ & Hbl).
destruct Hb as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
unfold base_rel3, ret_st; simpl.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split.
- split; [intros Hs; simpl in Hs; congruence |]. intros H. unfold ss_init in H. inversion H. congruence.
- split; [intros H; contradiction | mem_call_tac].
Qed.

Lemma ret3_ctx_valid : forall DENT TABS (gv: globals) (p: val) (k: cst3),
  TABS_OK TABS -> ctx_rep3 DENT TABS gv p k |-- valid_pointer p.
Proof.
intros DENT TABS gv p k HT. unfold ctx_rep3, ctx_body3, fgroup3, tabs_rep. normalize.
assert (V: field_at_ Ews t_dctx (DOT _LLTptr) p |-- valid_pointer p)
  by (apply field_at_valid_ptr0; auto; reflexivity).
destruct (c3_tabs k) as [lxb | ox ts].
- unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
- sep_apply (HT gv p ox ts). unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

(* a failed stream: any stream relation holds (ss_err) *)
Lemma ret3_err_DC : forall DENT TABS (SR: srel3) BR (gv: globals) (p: val) (k: cst3) (st: dctx_st),
  TABS_OK TABS -> base_rel3 st k -> ss_err (dc_ss st) = true -> dc_bl st = None ->
  ctx_rep3 DENT TABS gv p k |-- DC3x DENT TABS SR BR gv p st && valid_pointer p.
Proof.
intros DENT TABS SR BR gv p k st HT Hb He Hbl.
apply andp_right; [| apply ret3_ctx_valid; auto].
unfold DC3x, DC3_of. Exists k. apply andp_right; [| apply derives_refl].
apply prop_right. split; [exact Hb|]. split; [| split].
- intros _ H; congruence.
- intros ba H; congruence.
- apply ex_on3_err; exact He.
Qed.

Lemma ret3_err_gen : forall DENT TABS BR (a: dsa) (w: lw) (r ip: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a ->
  (ip = a_ipos a \/ (ip = a_isz a /\ ss_ahead (dc_ss (a_st a)) = 0)) ->
  base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_S_ip DENT TABS a w ip))) |--
    RA_return (ds_R DENT TABS BR a) (Some (Vlong (Int64.repr r))).
Proof.
intros DENT TABS BR a w r ip HT Hok Hst Hip Hbc Hoc Hpre Hr Hwhy.
assert (Herr: is_error_code r = true) by (destruct Hwhy as [[? _] _]; auto).
pose proof (ret3_err_post a (w_oc w) r ip Hok Hst Hwhy Hip Hoc Hpre) as Hpost.
pose proof (ret3_err_base a (w_k w) r ip Hok Herr Hbc) as Hbase.
assert (Hprog: stream_progress (a_st a) (ret_st a r ip) r (a_osz a) (a_opos a) (a_opos a) (a_isz a) (a_ipos a) ip
                 (a_ibs a))
  by (unfold stream_progress, stream_progress_m; intros H; rewrite Herr in H; discriminate).
assert (Hun: stream_untouched (a_st a) r (a_osz a) (a_opos a) (a_oc a) (w_oc w))
  by (intros _ H; rewrite Herr in H; discriminate).
assert (Hse: ss_err (dc_ss (ret_st a r ip)) = true) by exact Herr.
assert (Hbl: dc_bl (ret_st a r ip) = None)
  by (destruct Hok as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hbl) & _); exact Hbl).
unfold ds_R, RA_return, frame_ret_assert, function_body_ret_assert.
unfold ds_LI_L, ds_S_ip, ds_post, stackframe_of; simpl fn_vars.
go_lowerx.
sep_apply (ret3_err_DC DENT TABS SR3r BR (a_gv a) (a_d a) (w_k w) (ret_st a r ip) HT Hbase Hse Hbl).
unfold liftx, lift; simpl.
Exists r (a_opos a) ip (w_oc w) (ret_st a r ip).
unfold var_block, eval_lvar; simpl.
unfold lvar_denote in H0.
destruct (Map.get (ve_of rho) _op) as [[b t]|] eqn:E; [|contradiction].
destruct H0 as [<- ->].
unfold liftx, lift; simpl. rewrite E. simpl.
sep_apply (data_at_data_at_ Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (Vptr b Ptrofs.zero)).
rewrite data_at__memory_block. entailer!.
apply derives_refl.
Qed.

Lemma ret3_err_gen_x : forall DENT TABS BR (a: dsa) (w: lw) (r ip: Z),
  TABS_OK TABS -> dsa_ok a -> start_ok a ->
  (ip = a_ipos a \/ (ip = a_isz a /\ ss_ahead (dc_ss (a_st a)) = 0)) ->
  base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r -> ex_err a r ->
  PROPx [] (LOCALx (ds_LI_L a w) (SEPx (ds_S_ip DENT TABS a w ip))) |--
    RA_return (ds_R_x DENT TABS BR a) (Some (Vlong (Int64.repr r))).
Proof.
intros DENT TABS BR a w r ip HT Hok Hst Hip Hbc Hoc Hpre Hr Hwhy Hex.
assert (Herr: is_error_code r = true) by (destruct Hwhy as [[? _] _]; auto).
pose proof (ret3_err_post a (w_oc w) r ip Hok Hst Hwhy Hip Hoc Hpre) as Hpost.
pose proof (ret3_err_base a (w_k w) r ip Hok Herr Hbc) as Hbase.
assert (Hprog: stream_progress (a_st a) (ret_st a r ip) r (a_osz a) (a_opos a) (a_opos a) (a_isz a) (a_ipos a) ip
                 (a_ibs a))
  by (unfold stream_progress, stream_progress_m; intros H; rewrite Herr in H; discriminate).
assert (Hun: stream_untouched (a_st a) r (a_osz a) (a_opos a) (a_oc a) (w_oc w))
  by (intros _ H; rewrite Herr in H; discriminate).
assert (Hexa: stream_exact (a_st a) (ret_st a r ip) r (a_osz a) (a_opos a) (a_opos a) (w_oc w) (a_ibs a)
                 (a_isz a) (a_ipos a) ip).
{ intros Hf. destruct (Hex Hf) as [Hm | Hn]; [left; exact Hm | right]. cbv zeta.
  unfold a_xin, a_xroom in Hn. rewrite Hn. exact Herr. }
assert (Hse: ss_err (dc_ss (ret_st a r ip)) = true) by exact Herr.
assert (Hbl: dc_bl (ret_st a r ip) = None)
  by (destruct Hok as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hbl) & _); exact Hbl).
unfold ds_R_x, RA_return, frame_ret_assert, function_body_ret_assert.
unfold ds_LI_L, ds_S_ip, ds_post_x, stackframe_of; simpl fn_vars.
go_lowerx.
sep_apply (ret3_err_DC DENT TABS SR3 BR (a_gv a) (a_d a) (w_k w) (ret_st a r ip) HT Hbase Hse Hbl).
unfold liftx, lift; simpl.
Exists r (a_opos a) ip (w_oc w) (ret_st a r ip).
unfold var_block, eval_lvar; simpl.
unfold lvar_denote in H0.
destruct (Map.get (ve_of rho) _op) as [[b t]|] eqn:E; [|contradiction].
destruct H0 as [<- ->].
unfold liftx, lift; simpl. rewrite E. simpl.
sep_apply (data_at_data_at_ Tsh (tptr tschar) (offset_val (w_opc w) (a_ob a)) (Vptr b Ptrofs.zero)).
rewrite data_at__memory_block. entailer!.
apply derives_refl.
Qed.

Lemma RET3_ok : RET3.
Proof.
split.
- intros DENT TABS BR a w r HT Hok Hst Hbc Hoc Hpre Hr Hwhy.
  change (ds_LI_S DENT TABS a w) with (ds_S_ip DENT TABS a w (a_ipos a)).
  apply ret3_err_gen; auto.
- intros DENT TABS BR a w r HT Hok Hst H0 Hbc Hoc Hpre Hr Hwhy.
  apply ret3_err_gen; auto.
Qed.

Lemma RET3x_ok : RET3x.
Proof.
split.
- intros DENT TABS BR a w r HT Hok Hst Hbc Hoc Hpre Hr Hwhy Hex.
  change (ds_LI_S DENT TABS a w) with (ds_S_ip DENT TABS a w (a_ipos a)).
  apply ret3_err_gen_x; auto.
- intros DENT TABS BR a w r HT Hok Hst H0 Hbc Hoc Hpre Hr Hwhy Hex.
  apply ret3_err_gen_x; auto.
Qed.

End CM_S3Ret_1.
