(* valid_params main, segment D1 (see the header of VPMain.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPMain.
Require Import Zstd.proof.harness.valid_params.VPMem2.
Require Import Zstd.proof.harness.valid_params.VPMem3.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

(* ---------- the model: one-shot decoding of the series zstd sees ---------- *)

Lemma VPD1_model md ws' : vp_written md ws' ->
  decode_series_m md sel_none (Some no_dict) no_wlim (ws_bytes ws') =
  if all_ok no_wlim (ws_frames ws') then SOk (ws_content ws') else SDet.
Proof.
  intros Hw. destruct (all_ok no_wlim (ws_frames ws')) eqn:E.
  - apply VPS_oneshot; auto.
  - pose proof Hw as (_ & _ & _ & _ & Hs). unfold decode_series_m. rewrite Hs, E. reflexivity.
Qed.

Lemma VPD1_success wsr ws' p base wlim cap r out : VP_dfacts wsr ws' p base wlim ->
  oneshot_ok (dmode_of p) (Some no_dict) (ws_bytes ws') cap r out -> is_error_code r = false ->
  r = Zlength (ws_content wsr) /\ sublist 0 r out = zbytes (ws_content wsr).
Proof.
  intros (Hw & Hc & _) [_ Ho] Er. rewrite (VPD1_model _ _ Hw) in Ho.
  destruct (all_ok no_wlim (ws_frames ws')); [| congruence].
  rewrite <- Hc. destruct Ho as [Ho _]. apply Ho, Er.
Qed.

Lemma VPD1_error wsr ws' p base wlim cap r out : VP_dfacts wsr ws' p base wlim ->
  oneshot_ok (dmode_of p) (Some no_dict) (ws_bytes ws') cap r out -> is_error_code r = true ->
  Zlength (ws_content wsr) <= cap -> within_oneshot_b (ws_frames wsr) = true ->
  error_of r = ZSTD_error_memory_allocation.
Proof.
  intros Hd [_ Ho] Er Hcap Hwi. pose proof Hd as (Hw & Hc & _).
  assert (Ha: all_ok no_wlim (ws_frames ws') = true) by (apply Hd; exact Hwi).
  rewrite (VPD1_model _ _ Hw), Ha in Ho.
  destruct Ho as [_ Ho]. destruct (Ho Er) as [Hlt | ->]; [rewrite Hc in Hlt; lia |].
  reflexivity.
Qed.

Lemma VPD1_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs, Znth_map by lia. reflexivity.
Qed.

Lemma VPD1_content_at (c: list Z) i : 0 <= i < Zlength c -> Zlength c <= 2 ^ 18 ->
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength c)) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi Hc. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

(* ---------- buffers: the API's compspecs, dst = malloc(max(1, cap)) ---------- *)

Definition VPD1_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VPD1_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VPD1_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VPD1_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VPD1_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

(* the witness lent to ZSTD_decompressDCtx: the unused byte of dst = malloc(1) when cap = 0 *)
Definition VPD1_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma VPD1_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

Lemma VPD1_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma VPD1_split ib il :  0 <= il ->
  @data_at_ HCS Ews (tarray tuchar (Z.max 1 il)) ib |--
  !!(buf_ok (VPD1_W il ib) Ews il ib) && (@data_at_ ZCS Ews (tarray tuchar il) ib * pws_pred (VPD1_W il ib)).
Proof.
  intros Hil. rewrite <- VPD1_arr_. destruct (zeq il 0) as [->|Hn].
  - unfold VPD1_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply VPD1_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Z.max 1 0) with 1.
    rewrite <- (emp_sepcon (@data_at_ ZCS Ews (tarray tuchar 1) ib)) at 1.
    apply sepcon_derives; [| apply derives_refl].
    unfold data_at_, field_at_. apply data_at_zero_array; auto.
  - unfold VPD1_W. rewrite if_false by auto. rewrite Z.max_r by lia.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply VPD1_buf_ok_pos; lia | apply derives_refl].
Qed.

Lemma VPD1_join ib il v : 0 <= il ->
  @data_at ZCS Ews (tarray tuchar il) v ib * pws_pred (VPD1_W il ib) |-- @data_at_ HCS Ews (tarray tuchar (Z.max 1 il)) ib.
Proof.
  intros Hil. rewrite <- VPD1_arr_. destruct (zeq il 0) as [->|Hn].
  - unfold VPD1_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (v = []) by (entailer!; apply Zlength_nil_inv; auto). subst v.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
  - unfold VPD1_W. rewrite if_false by auto. rewrite Z.max_r by lia. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
Qed.

Lemma VPD1_res_i (DD0: globals -> val -> ddict_st -> mpred) gv sh p :
  emp |-- dict_res DD0 gv sh (dc_dict (set_par dctx_init p)) * set_res DD0 gv sh (dc_set (set_par dctx_init p)) (dc_dict (set_par dctx_init p)).
Proof. unfold dict_res, set_res. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma VPD1_res_e (DD0: globals -> val -> ddict_st -> mpred) gv sh p :
  dict_res DD0 gv sh (dc_dict (set_par dctx_init p)) * set_res DD0 gv sh (dc_set (set_par dctx_init p)) (dc_dict (set_par dctx_init p)) |-- emp.
Proof. unfold dict_res, set_res. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma VPD1_oneshot p s cap r out :
  oneshot_dctx (set_par dctx_init p) s cap r out ->
  oneshot_ok (dmode_of p) (Some no_dict) s cap r out.
Proof. exact (fun H => H). Qed.

Lemma VPD1_bytes_ok md ws' : vp_written md ws' -> bytes_ok (ws_bytes ws').
Proof. intros (H & _). exact H. Qed.

Lemma VPD1_content_borrow_w (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  VP_Rc V p |--
  @data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) *
  (@data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) -* VP_Rc V p).
Proof. unfold VP_Rc. apply VP_content_borrow. Qed.

Lemma VPD1_src_ok W n src : 0 < n -> buf_ok W Ews n src.
Proof. apply VPD1_buf_ok_pos. Qed.

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

(* D1: the one-shot branch of s16 *)
Lemma VP_segD1 (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base wlim: Z) (src dctx: val) :
  semax Delta (VP_SD0 DC WG gv vz vi vo wsr ws' p base wlim src dctx) VP_oneshot_s
    (normal_ret_assert (EX st: dctx_st, VP_SD1 DC WG gv vz vi vo wsr ws' src dctx st)).
Proof.
  unfold VP_SD0, VP_oneshot_s.
  Intros. rename H into Hd.
  pose proof Hd as (Hw & Hc & Hb & Hbase & Hn & Hbok & Hcok & Hnb & Hnc & Hnf & Hwf & Hfr & Hwl & Hwo & _).
  assert (Hnb': Zlength (ws_bytes ws') <= 2 ^ 19).
  { rewrite Hb. destruct (zle base (Zlength (ws_bytes wsr)));
      [rewrite Zlength_sublist by lia; lia | rewrite sublist_nil_gen by lia; rewrite Zlength_nil; lia]. }
  sep_apply (VP_sr_unfold7w wsr (gv _x_valid_params__sr)). Intros.
  repeat apply -> seq_assoc. unfold VP_Delta. simplify_func_tycontext.
  unfold VP_Rcn. forward. fold (VP_Rcn (vl (Zlength (ws_content wsr))) (gv _x_valid_params__sr)).
  forward_call (0, Zlength (ws_content wsr) + 16).
  Intros cap. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_params__t'39 (Vlong (Int64.repr (Z.max 1 cap))) :: L) (SEPx R))) end.
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. rewrite Z.max_r by (simpl in *; lia). reflexivity. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. simpl in *. rewrite Z.max_l by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 cap), gv).
  { simpl. rep_lia. }
  Intros dst. forward.
  destruct (eq_dec dst nullval) as [Hd0|Hd0].
  { subst dst. forward_if.
    { exfalso; congruence. }
    forward. Exists (set_par dctx_init p). unfold VP_SD1.
    sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)). entailer!. }
  Intros.
  forward_if; [| exfalso; contradiction].
  sep_apply (VPD1_split dst cap ltac:(lia)). Intros.
  rewrite <- (VPD1_arr Ews (Zlength (ws_bytes ws')) (zbytes (ws_bytes ws')) src).
  sep_apply (VPD1_res_i DD gv Ews p).
  forward_call (VPD1_W cap dst, gv, dctx, set_par dctx_init p, Ews, Ews, dst, cap, Ews, src, ws_bytes ws').
  { sep_apply (data_at__mbuf Ews cap dst). cancel. }
  { split; [apply VPD1_src_ok; lia | apply (VPD1_bytes_ok _ _ Hw)]. }
  Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
  unfold mbuf; rewrite if_false by auto.
  match goal with Ho: oneshot_dctx _ _ _ _ _ |- _ => apply VPD1_oneshot in Ho; rename Ho into Hos end.
  sep_apply (VPD1_res_e DD gv Ews p).
  rewrite (VPD1_arr Ews cap out dst).
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  { (* a success: the content *)
    assert (Er: is_error_code r = false) by (destruct (is_error_code r); [discriminate | reflexivity]).
    destruct (VPD1_success wsr ws' p base wlim cap r out Hd Hos Er) as [Hr Hout]. subst r.
    unfold VP_Rcn. forward. fold (VP_Rcn (vl (Zlength (ws_content wsr))) (gv _x_valid_params__sr)).
    forward_call Int.one.
    1: (entailer!; unfold vl; simpl; rewrite Int64.eq_true; reflexivity).
    assert (Hfit: Zlength (ws_content wsr) <= cap) by (destruct Hos as [Hf _]; apply Hf, Er).
    remember (zbytes (ws_content wsr) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content wsr))) as CV eqn:ECV.
    assert (HCV: Zlength CV = 2 ^ 18) by (subst CV; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_for_simple_bound (Zlength (ws_content wsr)) (EX i:Z, PROPx P (LOCALx L (SEPx R))) end.
    1: entailer!.
    { assert (Ho: Znth i out = Vint (Int.repr (Znth i (ws_content wsr))))
        by (apply VPD1_out_at with (r := Zlength (ws_content wsr)); auto).
      assert (Hbi: is_byte (Znth i (ws_content wsr))) by (apply Forall_Znth; auto).
      unfold is_byte in Hbi.
      forward.
      1: (entailer!; change (@Znth val Vundef i out) with (@Znth val Inhabitant_val i out); rewrite Ho; simpl;
          rewrite Int.unsigned_repr by rep_lia; rep_lia).
      change (@Znth val Vundef i out) with (@Znth val Inhabitant_val i out). rewrite Ho.
      sep_apply (VPD1_content_borrow_w CV (gv _x_valid_params__sr) i ltac:(lia) HCV).
      replace (Znth i CV) with (Vint (Int.repr (Znth i (ws_content wsr))))
        by (match goal with Hi: 0 <= i < Zlength (ws_content wsr) |- _ => clear - ECV Hi Hnc end; subst CV; symmetry; apply VPD1_content_at; lia).
      Intros.
      assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_params__sr)) (Vlong (Int64.repr i))) =
                   field_address tuchar [] (offset_val (524296 + i) (gv _x_valid_params__sr))).
      { entailer!. rewrite field_address_offset by auto. simpl. normalize. }
      forward.
      forward_call Int.one.
      { entailer!. simpl. rewrite Int.eq_true. reflexivity. }
      sep_apply (wand_frame_elim (data_at Ews tuchar (Vint (Int.repr (Znth i (ws_content wsr))))
                                    (offset_val (524296 + i) (gv _x_valid_params__sr)))).
      entailer!. }
    subst CV.
    rewrite <- (VPD1_arr Ews cap out dst).
    sep_apply (VPD1_join dst cap out ltac:(lia)).
    forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
    { rewrite if_false by auto. cancel. }
    Exists st'. unfold VP_SD1.
    rewrite (VPD1_arr Ews (Zlength (ws_bytes ws')) (zbytes (ws_bytes ws')) src).
    sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)).
    entailer!. }
  { (* an error: with room for the content and a series within zstd's range, memory *)
    assert (Er: is_error_code r = true) by (destruct (is_error_code r); [reflexivity | contradiction]).
    unfold VP_Rcn. forward. fold (VP_Rcn (vl (Zlength (ws_content wsr))) (gv _x_valid_params__sr)).
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if.
    - sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)).
      apply -> seq_assoc.
      forward_call (Ews, gv _x_valid_params__sr, wsr).
      destruct (within_oneshot_b (ws_frames wsr)) eqn:Ew.
      + forward. apply semax_if_seq. forward_if.
        2: (exfalso; apply Int.one_not_zero; assumption).
        forward_call r.
        forward_call Int.one.
        { go_lower. apply prop_right.
          rewrite (VPD1_error wsr ws' p base wlim cap r out Hd Hos Er ltac:(lia) Ew). reflexivity. }
        rewrite <- (VPD1_arr Ews cap out dst).
        sep_apply (VPD1_join dst cap out ltac:(lia)).
        forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
        { rewrite if_false by auto. cancel. }
        Exists st'. unfold VP_SD1.
        rewrite (VPD1_arr Ews (Zlength (ws_bytes ws')) (zbytes (ws_bytes ws')) src).
        entailer!.
      + forward. apply semax_if_seq. forward_if.
        1: (exfalso; auto).
        rewrite <- (VPD1_arr Ews cap out dst).
        sep_apply (VPD1_join dst cap out ltac:(lia)).
        forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
        { rewrite if_false by auto. cancel. }
        Exists st'. unfold VP_SD1.
        rewrite (VPD1_arr Ews (Zlength (ws_bytes ws')) (zbytes (ws_bytes ws')) src).
        entailer!.
    - forward. apply semax_if_seq. forward_if.
      1: (exfalso; auto).
      sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)).
      rewrite <- (VPD1_arr Ews cap out dst).
      sep_apply (VPD1_join dst cap out ltac:(lia)).
      forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
      { rewrite if_false by auto. cancel. }
      Exists st'. unfold VP_SD1.
      rewrite (VPD1_arr Ews (Zlength (ws_bytes ws')) (zbytes (ws_bytes ws')) src).
      entailer!. }
Qed.

End Seg.
