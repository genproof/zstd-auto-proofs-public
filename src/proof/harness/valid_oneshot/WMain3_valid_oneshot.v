(* MainOK of the unit valid_oneshot: the main of valid_oneshot adapted to API v3 from its v2 proof. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_oneshot.WTopSpecs_valid_oneshot.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.ApiBridge.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_oneshot.HOK_valid_oneshot.CompSpecs.

(* ---------- main's precondition: the decoder's tables, the writer's statics, sr ---------- *)

Lemma WD_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma WD_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma WD_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_oneshot.whole_prog))
  = wvardefs.
Proof.
  rewrite WD_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof WD_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. exact (H i E).
Qed.

Lemma WD_InitGPred_in x l gv : In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  intros Hin. apply in_split in Hin as [l1 [l2 ->]].
  rewrite InitGPred_middleD. rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma WD_sr_in :
  In (_x_valid_oneshot__sr, Gvar v_x_valid_oneshot__sr)
    (filter (fun ig => negb (id_in_list (fst ig) wvar_ids))
      (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_oneshot.whole_prog))).
Proof.
  rewrite !filter_In. split; [split|].
  - unfold Vardefs. apply filter_In. split; [|reflexivity].
    apply Maps.PTree.elements_correct. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma WD_sr_zero gv :
  globs2pred gv (_x_valid_oneshot__sr, Gvar v_x_valid_oneshot__sr) |-- data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_oneshot__sr).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 786936 with (@sizeof HCS t_wseries).
  apply mapsto_zero_data_at_zero.
  - auto.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    hnf. rewrite Ptrofs.unsigned_zero. apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

Lemma WD_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_oneshot.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_oneshot__sr) * TT)).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_oneshot.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 11 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite WD_wvardefs. apply sepcon_derives; [apply HWG|].
    eapply derives_trans; [apply WD_InitGPred_in, WD_sr_in|].
    apply sepcon_derives; [apply WD_sr_zero | apply derives_refl].
Qed.

(* ---------- compspecs: the API's (decoder) and main's (this unit) ---------- *)

Definition WD_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma WD_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (WD_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma WD_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (WD_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma WD_Externals : Externals = [nondet_u32_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma WD_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* ---------- the series' bytes, split off sr for exact_copy ---------- *)

Lemma VO_bytes_split sh (bs: list Z) p : Zlength bs <= 2 ^ 19 ->
  field_at sh t_wseries (DOT _bytes) (zbytes bs ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs)) p =
  (data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) (field_address t_wseries (DOT _bytes) p) *
   data_at sh (tarray tuchar (2 ^ 19 - Zlength bs)) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength bs))
     (field_address0 (tarray tuchar (2 ^ 19)) (SUB (Zlength bs)) (field_address t_wseries (DOT _bytes) p)))%logic.
Proof.
  intros Hn. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _bytes)) with (tarray tuchar (2 ^ 19)).
  apply split2_data_at_Tarray_app.
  - rewrite Zlength_map. reflexivity.
  - rewrite Zlength_Zrepeat; [reflexivity|]. pose proof (Zlength_nonneg bs). lia.
Qed.

(* ---------- the model: what one-shot decoding of a written series gives ---------- *)

Lemma VO_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto.
  intros E. apply andb_prop in E as [E1 E2]. destruct (wi_rejected wl f); [discriminate|].
  rewrite IH by exact E2. reflexivity.
Qed.

Lemma VO_model ws : series_facts no_dict ws -> wseries_wf ws ->
  decode_series no_dict no_wlim (ws_bytes ws) =
  if within_oneshot_b (ws_frames ws) then SOk (ws_content ws) else SDet.
Proof.
  intros Hf Hw. unfold decode_series. rewrite (series_frames_written no_dict ws no_wlim Hf).
  rewrite (within_oneshot_all_ok ws Hw).
  destruct (all_ok no_wlim (ws_frames ws)) eqn:E; [|reflexivity].
  rewrite (VO_ok_prefix_all _ _ E). f_equal. apply (written_content no_dict ws Hf).
Qed.

(* a success is the content; an error with room for the content and a series within zstd's range is memory *)
Lemma VO_success ws cap r out : series_facts no_dict ws -> wseries_wf ws ->
  oneshot_ok md_dflt (Some no_dict) (ws_bytes ws) cap r out -> is_error_code r = false ->
  r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws).
Proof.
  intros Hf Hw Hos Er. apply oneshot_ok_dflt in Hos. destruct Hos as [_ Ho]. rewrite (VO_model ws Hf Hw) in Ho.
  destruct (within_oneshot_b (ws_frames ws)); [| congruence].
  destruct Ho as [Ho _]. apply Ho, Er.
Qed.

Lemma VO_error ws cap r out : series_facts no_dict ws -> wseries_wf ws ->
  oneshot_ok md_dflt (Some no_dict) (ws_bytes ws) cap r out -> is_error_code r = true ->
  Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
  error_of r = ZSTD_error_memory_allocation.
Proof.
  intros Hf Hw Hos Er Hc Hwi. apply oneshot_ok_dflt in Hos. destruct Hos as [_ Ho]. rewrite (VO_model ws Hf Hw), Hwi in Ho.
  destruct Ho as [_ Ho]. destruct (Ho Er) as [Hlt | ->]; [lia |].
  reflexivity.
Qed.

(* ---------- buffers of max(1, n) bytes: n bytes for the API, the rest lent as a witness ---------- *)

Definition VO_tail (n: Z) (p: val) : val := @field_address0 ZCS (tarray tuchar (Z.max 1 n)) (SUB n) p.

Lemma VO_split sh n (v1 v2: list val) p : 0 <= n -> Zlength v1 = n -> Zlength v2 = Z.max 1 n - n ->
  @data_at ZCS sh (tarray tuchar (Z.max 1 n)) (v1 ++ v2) p =
  (@data_at ZCS sh (tarray tuchar n) v1 p * @data_at ZCS sh (tarray tuchar (Z.max 1 n - n)) v2 (VO_tail n p))%logic.
Proof. intros. unfold VO_tail. apply split2_data_at_Tarray_app; auto. Qed.

Lemma VO_split_ sh n p : 0 <= n ->
  @data_at_ ZCS sh (tarray tuchar (Z.max 1 n)) p =
  (@data_at_ ZCS sh (tarray tuchar n) p *
   @data_at ZCS sh (tarray tuchar (Z.max 1 n - n)) (Zrepeat Vundef (Z.max 1 n - n)) (VO_tail n p))%logic.
Proof.
  intros Hn. unfold data_at_, field_at_.
  change (@field_at ZCS sh (tarray tuchar (Z.max 1 n)) [] (default_val (nested_field_type (tarray tuchar (Z.max 1 n)) [])) p)
    with (@data_at ZCS sh (tarray tuchar (Z.max 1 n)) (Zrepeat Vundef (Z.max 1 n)) p).
  change (@field_at ZCS sh (tarray tuchar n) [] (default_val (nested_field_type (tarray tuchar n) [])) p)
    with (@data_at ZCS sh (tarray tuchar n) (Zrepeat Vundef n) p).
  replace (Zrepeat Vundef (Z.max 1 n)) with (Zrepeat Vundef n ++ Zrepeat Vundef (Z.max 1 n - n))
    by (rewrite Zrepeat_app by lia; f_equal; lia).
  apply VO_split; [lia | rewrite Zlength_Zrepeat; lia | rewrite Zlength_Zrepeat; lia].
Qed.

Lemma VO_pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma VO_buf_ok W sh n p v : readable_share sh -> 0 <= n ->
  In (pw_bytes Ews (Z.max 1 n - n) v (VO_tail n p)) W -> buf_ok W sh n p.
Proof.
  intros Hsh Hn Hin. unfold buf_ok.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block ZCS). normalize.
    match goal with H: field_compatible _ _ p |- _ => destruct H as [Hp _] end.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n.
    eapply derives_trans; [apply sepcon_derives; [apply (VO_pws_in W _ Hin) | apply derives_refl] |].
    simpl pw_pred. unfold VO_tail. change (Z.max 1 0 - 0) with 1. change (Z.max 1 0) with 1.
    saturate_local.
    match goal with H: field_compatible _ [] (field_address0 _ _ p) |- _ => destruct H as [Hfa _] end.
    unfold field_address0 in *.
    destruct (@field_compatible0_dec ZCS (tarray tuchar 1) (SUB 0) p) as [Hfc|]; [| contradiction].
    assert (Hp: isptr p) by (destruct Hfc; auto).
    change (nested_field_offset (tarray tuchar 1) (SUB 0)) with 0.
    rewrite !isptr_offset_val_zero by exact Hp.
    assert (Hv: @data_at ZCS Ews (tarray tuchar 1) v p |-- weak_valid_pointer p).
    { eapply derives_trans; [apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia] |].
      apply valid_pointer_weak. }
    apply andp_right; apply sepcon_weak_valid_pointer1; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

(* ---------- free ---------- *)

Lemma VO_cmp_null_t p : isptr p ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr (Tstruct _ZSTD_DCtx_s noattr)) (tptr tvoid) p
    (eval_cast tint (tptr tvoid) (Vint (Int.repr 0))))) = Vint Int.zero.
Proof. destruct p; try contradiction. reflexivity. Qed.

Lemma VO_isptr p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma VO_cmp_null p : isptr p ->
  force_val (sem_cast tint tbool (eval_binop Oeq (tptr tuchar) (tptr tvoid) p
    (eval_cast tint (tptr tvoid) (Vint (Int.repr 0))))) = Vint Int.zero.
Proof. destruct p; try contradiction. reflexivity. Qed.

Lemma VO_free_nn_ {cs: compspecs} t p : p <> nullval ->
  (malloc_token Ews t p * data_at_ Ews t p) |--
  (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by auto. cancel. Qed.

(* the two tails lent to a call *)
Lemma VO_pws_fold sh1 n1 c1 b1 sh2 n2 c2 b2 :
  (@data_at ZCS sh1 (tarray tuchar n1) c1 b1 * @data_at ZCS sh2 (tarray tuchar n2) c2 b2) |--
  pws_pred [pw_bytes sh1 n1 c1 b1; pw_bytes sh2 n2 c2 b2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma VO_pws_unfold sh1 n1 c1 b1 sh2 n2 c2 b2 :
  pws_pred [pw_bytes sh1 n1 c1 b1; pw_bytes sh2 n2 c2 b2] |--
  (@data_at ZCS sh1 (tarray tuchar n1) c1 b1 * @data_at ZCS sh2 (tarray tuchar n2) c2 b2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

(* a buffer back in one piece, at main's compspecs, for free *)
Lemma VO_join sh n (v1 v2: list val) p : 0 <= n -> Zlength v1 = n -> Zlength v2 = Z.max 1 n - n ->
  (@data_at ZCS sh (tarray tuchar n) v1 p * @data_at ZCS sh (tarray tuchar (Z.max 1 n - n)) v2 (VO_tail n p)) |--
  @data_at_ HCS sh (tarray tuchar (Z.max 1 n)) p.
Proof.
  intros. rewrite <- VO_split by auto. rewrite <- WD_arr_. apply data_at_data_at_.
Qed.

Lemma VO_dict_none_i (DD0: globals -> val -> ddict_st -> mpred) gv sh : emp |-- dict_res DD0 gv sh (dc_dict dctx_init).
Proof. apply derives_refl. Qed.



Lemma VO_free_null {cs: compspecs} t :
  emp |-- (if eq_dec nullval nullval then emp else (malloc_token Ews t nullval * data_at_ Ews t nullval)).
Proof. rewrite if_true by auto. apply derives_refl. Qed.

Lemma VO_free_nn {cs: compspecs} t v p : p <> nullval ->
  (malloc_token Ews t p * data_at Ews t v p) |--
  (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by auto. cancel. Qed.

Lemma VO_join_ sh n p : 0 <= n ->
  (@data_at_ ZCS sh (tarray tuchar n) p *
   @data_at ZCS sh (tarray tuchar (Z.max 1 n - n)) (Zrepeat Vundef (Z.max 1 n - n)) (VO_tail n p)) |--
  @data_at_ HCS sh (tarray tuchar (Z.max 1 n)) p.
Proof. intros. rewrite <- VO_split_ by auto. rewrite <- WD_arr_. apply derives_refl. Qed.

Lemma VO_dres_i (DD0: globals -> val -> ddict_st -> mpred) gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. change (set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init)) with (@emp mpred _ _). rewrite sepcon_emp. apply derives_refl. Qed.

Lemma VO_dres_e (DD0: globals -> val -> ddict_st -> mpred) gv sh :
  dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init) |-- emp.
Proof. change (set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init)) with (@emp mpred _ _). rewrite sepcon_emp. apply derives_refl. Qed.

Lemma VO_dict_none_e (DD0: globals -> val -> ddict_st -> mpred) gv sh : dict_res DD0 gv sh (dc_dict dctx_init) |-- emp.
Proof. apply derives_refl. Qed.

(* a decoding leaves a new context as it was, except dc_ex (cleared: the stream may read what it left behind) *)
Lemma VO_after_init st' : after_decode (after_use dctx_init) st' (dc_dict dctx_init) -> st' = set_ex dctx_init false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma VO_after_init2 st' :
  after_decode (after_use (set_ex dctx_init false)) st' (dc_dict (set_ex dctx_init false)) ->
  st' = set_ex dctx_init false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma VO_dres_i2 (DD0: globals -> val -> ddict_st -> mpred) gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict (set_ex dctx_init false)) *
          set_res DD0 gv sh (dc_set (set_ex dctx_init false)) (dc_dict (set_ex dctx_init false)).
Proof. apply VO_dres_i. Qed.

Lemma VO_dres_e2 (DD0: globals -> val -> ddict_st -> mpred) gv sh :
  dict_res DD0 gv sh (dc_dict (set_ex dctx_init false)) *
  set_res DD0 gv sh (dc_set (set_ex dctx_init false)) (dc_dict (set_ex dctx_init false)) |-- emp.
Proof. apply VO_dres_e. Qed.

Lemma VO_drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

Lemma VO_bytes_ok (l: list Z) : Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. intros H. eapply Forall_impl; [|exact H]. intros a Ha. unfold is_byte. rep_lia. Qed.

(* ---------- sr back in one piece for within_oneshot ---------- *)

Lemma VO_ws_fold sh ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  (@data_at HCS sh (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS sh (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS sh t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS sh t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS sh t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
   @field_at HCS sh t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS sh t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer sh 786932 786936 p) |--
  @data_at HCS sh t_wseries (wseries_val ws) p.
Proof.
  intros Hn. rewrite <- VO_bytes_split by exact Hn.
  unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val]. rewrite !sepcon_assoc. apply derives_refl.
Qed.

Lemma VO_ws_unfold sh ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  @data_at HCS sh t_wseries (wseries_val ws) p |--
  (@data_at HCS sh (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (@field_address HCS t_wseries (DOT _bytes) p) *
   @data_at HCS sh (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (@field_address0 HCS (tarray tuchar (2 ^ 19)) (SUB (Zlength (ws_bytes ws))) (@field_address HCS t_wseries (DOT _bytes) p)) *
   @field_at HCS sh t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
   @field_at HCS sh t_wseries (DOT _content)
     (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
   @field_at HCS sh t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p *
   @field_at HCS sh t_wseries (DOT _f)
     (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) p *
   @field_at HCS sh t_wseries (DOT _nframes) (vu (Zlength (ws_frames ws))) p *
   spacer sh 786932 786936 p).
Proof.
  intros Hn. unfold_data_at (data_at _ _ _ p). cbn [fst snd wseries_val].
  rewrite (VO_bytes_split sh (ws_bytes ws) p Hn). rewrite !sepcon_assoc. apply derives_refl.
Qed.

(* the bytes delivered and the content, at index i *)
Lemma VO_out_at (c: list Z) r out i : sublist 0 r out = zbytes c -> r = Zlength c -> 0 <= i < r ->
  Znth i out = Vint (Int.repr (Znth i c)).
Proof.
  intros Hs Hr Hi. replace (Znth i out) with (Znth (i + 0) out) by (rewrite Z.add_0_r; reflexivity).
  rewrite <- (Znth_sublist 0 i r out) by lia. rewrite Hs, Znth_map by lia. reflexivity.
Qed.

Lemma VO_content_at (c: list Z) i : 0 <= i < Zlength c -> Zlength c <= 2 ^ 18 ->
  Znth i (zbytes c ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength c)) = Vint (Int.repr (Znth i c)).
Proof.
  intros Hi Hc. rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

Ltac VO_kill :=
  exfalso; first [ assumption | discriminate | solve [auto] | congruence ].

Theorem main_ok3_valid_oneshot : MainOK.
Proof.
intros DC DD WG WDS HWG.
unfold G0. rewrite WD_Externals.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred
          (sepcon (zstd_globals gv) (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_oneshot__sr)) TT)))
          _ _ _ Zstd.contracts.x_valid_oneshot.whole_prog).
4: idtac.
- intros. apply WD_pre; auto.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply WD_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g). split; [reflexivity | exact Hin].
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize.
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward.
  forward_call (gv, Ews, gv _x_valid_oneshot__sr, nullval, @None (wdict * share)).
  { unfold wdict_arg. entailer!. }
  Intros ws.
  unfold wdict_arg, wdict_model in *.
  Intros.
  unfold_data_at (data_at _ t_wseries _ _). cbn [fst snd wseries_val].
  pose proof H as Hfacts. destruct H as (Hbok & Hcok & Hnb & Hnc & Hnf & _).
  forward.
  forward_call (0, Zlength (ws_content ws) + 16).
  Intros cap. forward. forward.
  rewrite (VO_bytes_split Ews (ws_bytes ws)) by lia.
  Intros.
  forward_call (gv, Ews, field_address t_wseries (DOT _bytes) (gv _x_valid_oneshot__sr), ws_bytes ws).
  { entailer!.
    match goal with H: field_compatible _ [] (field_address t_wseries (DOT _bytes) ?p) |- _ =>
      unfold field_address in *; destruct (field_compatible_dec t_wseries (DOT _bytes) p) as [Hfc|Hfc];
      [| destruct H as [Hx _]; contradiction] end.
    simpl. destruct (gv _x_valid_oneshot__sr); try contradiction. reflexivity. }
  Intros src. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_oneshot__t'3 (Vlong (Int64.repr (Z.max 1 cap))) :: L) (SEPx R))) end.
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. rewrite Z.max_r by (simpl in *; lia). reflexivity. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. simpl in *. rewrite Z.max_l by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 cap), gv).
  { simpl. rep_lia. }
  Intros dst. forward.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec src nullval) as [Hs0|Hs0].
  { subst src. forward_if; [| exfalso; auto].
    forward. forward_if; [| VO_kill].
    sep_apply (VO_free_null (tarray tuchar 1)).
    forward_call (tarray tuchar 1, nullval, gv).
    forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
    forward. }
  Intros.
  destruct (eq_dec dst nullval) as [Hd0|Hd0].
  { subst dst. forward_if; [VO_kill |].
    forward. forward_if; [| VO_kill].
    sep_apply (VO_free_nn (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))))
      (zbytes (ws_bytes ws) ++ Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src Hs0).
    forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv).
    sep_apply (VO_free_null (tarray tuchar (Z.max 1 cap))).
    forward_call (tarray tuchar (Z.max 1 cap), nullval, gv).
    forward. }
  Intros.
  forward_if; [VO_kill |].
  forward. assert_PROP (isptr dst) as Hpd by entailer!. rewrite (VO_cmp_null dst Hpd).
  forward_if; [VO_kill |].
  assert_PROP (isptr src) as Hps by entailer!.
  (* the buffers at the API's compspecs, each split into the bytes passed and its tail *)
  rewrite <- (WD_arr Ews (Z.max 1 (Zlength (ws_bytes ws)))).
  rewrite (VO_split Ews (Zlength (ws_bytes ws)))
    by first [apply Zlength_nonneg | rewrite Zlength_map; reflexivity | rewrite Zlength_Zrepeat; [reflexivity | lia]].
  rewrite <- (WD_arr_ Ews (Z.max 1 cap)).
  rewrite (VO_split_ Ews cap) by lia.
  Intros.
  forward_call 2.
  Intros k.
  freeze [4; 8; 9; 11; 12; 13; 14; 15] FR.
  forward_if (EX r: Z, EX out: list val, EX dc: val, EX ost: option dctx_st,
    PROP (0 <= r <= Int64.max_unsigned; Zlength out = cap; oneshot_ok md_dflt (Some no_dict) (ws_bytes ws) cap r out;
          match ost with None => dc = nullval | Some _ => True end)
    LOCAL (temp _r (Vlong (Int64.repr r)); temp _dctx dc; temp _dst dst; temp _src src;
           temp _cap (Vlong (Int64.repr cap)); gvars gv)
    SEP (FRZL FR; mem_mgr gv; zstd_globals gv; match ost with None => emp | Some st => DC gv dc st end;
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 cap)) dst; @data_at ZCS Ews (tarray tuchar cap) out dst;
         @data_at ZCS Ews (tarray tuchar (Z.max 1 cap - cap)) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst);
         @malloc_token HCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src;
         @data_at ZCS Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src;
         @data_at ZCS Ews (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (VO_tail (Zlength (ws_bytes ws)) src);
         @field_at HCS Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_oneshot__sr); TT; has_ext tt)).
  { (* ZSTD_decompress *)
    forward.
    sep_apply (VO_pws_fold Ews (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws))) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (VO_tail (Zlength (ws_bytes ws)) src)
                           Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)).
    forward_call ([pw_bytes Ews (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws))) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (VO_tail (Zlength (ws_bytes ws)) src); pw_bytes Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)], gv, Ews, dst, cap, Ews, src, ws_bytes ws).
    { unfold mbuf; rewrite if_false by auto. cancel. }
    { split; (eapply VO_buf_ok; [auto | rep_lia | simpl; tauto]). }
    Intros vret. destruct vret as [r out]. cbn [fst snd] in *.
    unfold mbuf; rewrite if_false by auto.
    sep_apply VO_pws_unfold. Intros.
    forward.
    Exists r out nullval (@None dctx_st). entailer!. }
  { (* ZSTD_decompressDCtx on a context used before *)
    forward_call (0, 4096). Intros m.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_oneshot__t'8 (Vlong (Int64.repr (Z.max 1 m))) :: L) (SEPx R))) end.
    { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. rewrite Z.max_r by lia. reflexivity. }
    { forward. entailer!. rewrite !Int64.unsigned_repr in * by rep_lia. simpl in *. rewrite Z.max_l by lia. reflexivity. }
    forward_call (tarray tuchar (Z.max 1 m), gv). { simpl. rep_lia. }
    Intros other. forward.
    forward_call gv.
    Intros dc.
    repeat apply -> seq_assoc. apply semax_if_seq.
    destruct (eq_dec dc nullval) as [Hc0|Hc0].
    { (* no context *)
      subst dc. destruct (eq_dec other nullval) as [Ho0|Ho0].
      { subst other. forward_if; [| VO_kill]. forward. forward_if; [| VO_kill].
        forward_call (gv, nullval, @None dctx_st).
        sep_apply (VO_free_null (tarray tuchar 1)).
        forward_call (tarray tuchar 1, nullval, gv).
        sep_apply (VO_join_ Ews (Zlength (ws_bytes ws)) src ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0).
      forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv).
      sep_apply (VO_join_ Ews cap dst ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0).
      forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
      forward. }
      Intros. forward_if; [VO_kill |].
      forward. forward_if; [| VO_kill].
      forward_call (gv, nullval, @None dctx_st).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 m)) other Ho0).
      forward_call (tarray tuchar (Z.max 1 m), other, gv).
      sep_apply (VO_join_ Ews (Zlength (ws_bytes ws)) src ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0).
      forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv).
      sep_apply (VO_join_ Ews cap dst ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0).
      forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
      forward. }
    Intros.
    destruct (eq_dec other nullval) as [Ho0|Ho0].
    { subst other. forward_if; [| VO_kill]. forward. forward_if; [| VO_kill].
      sep_apply (VO_drop_vp (DC gv dc dctx_init) dc).
      forward_call (gv, dc, Some dctx_init).
      sep_apply (VO_free_null (tarray tuchar 1)).
      forward_call (tarray tuchar 1, nullval, gv).
      sep_apply (VO_join_ Ews (Zlength (ws_bytes ws)) src ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0).
      forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv).
      sep_apply (VO_join_ Ews cap dst ltac:(rep_lia)).
      sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0).
      forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
      forward. }
    Intros. forward_if; [VO_kill |].
    assert (Hpc: isptr dc) by (apply VO_isptr; auto).
    forward.
    rewrite (VO_cmp_null_t dc Hpc). forward_if; [VO_kill |].
    sep_apply (VO_drop_vp (DC gv dc dctx_init) dc).
    (* the earlier use: m nondet bytes *)
    rewrite <- (WD_arr_ Ews (Z.max 1 m) other). rewrite (VO_split_ Ews m other) by lia. Intros.
    rewrite (WD_arr_ Ews m other).
    forward_call (other, m, Ews). Intros obs.
    rewrite <- (WD_arr Ews m (map (fun b => Vint (Int.repr b)) obs) other).
    subst m.
    sep_apply (VO_pws_fold Ews (Z.max 1 (Zlength obs) - (Zlength obs)) (Zrepeat Vundef (Z.max 1 (Zlength obs) - (Zlength obs))) (VO_tail (Zlength obs) other)
                           Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)).
    sep_apply (VO_dres_i DD gv Ews).
    forward_call ([pw_bytes Ews (Z.max 1 (Zlength obs) - (Zlength obs)) (Zrepeat Vundef (Z.max 1 (Zlength obs) - (Zlength obs))) (VO_tail (Zlength obs) other); pw_bytes Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)], gv, dc, dctx_init, Ews, Ews, dst, cap, Ews, other, obs).
    { unfold mbuf; rewrite if_false by auto. cancel. }
    1: split; [|split]; [eapply VO_buf_ok; [auto | rep_lia | simpl; tauto] |
                         eapply VO_buf_ok; [auto | rep_lia | simpl; tauto] | apply VO_bytes_ok; auto].
    Intros vret. destruct vret as [[r1 out1] st1].
    unfold mbuf; rewrite if_false by auto.
    api_init; match goal with Ha: after_decode _ _ _ |- _ => apply VO_after_init in Ha; cbn [fst snd] in Ha; subst st1 end.
    cbn [fst snd] in *.
    sep_apply (VO_dres_e DD gv Ews). sep_apply VO_pws_unfold. Intros.
    sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out1 dst).
    sep_apply (VO_join Ews (Zlength obs) (zbytes obs) (Zrepeat Vundef (Z.max 1 (Zlength obs) - (Zlength obs))) other
      ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia])).
    sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength obs))) other Ho0).
    forward_call (tarray tuchar (Z.max 1 (Zlength obs)), other, gv).
    (* the series *)
    forward.
    sep_apply (VO_pws_fold Ews (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws))) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (VO_tail (Zlength (ws_bytes ws)) src)
                           Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)).
    sep_apply (VO_dres_i2 DD gv Ews).
    forward_call ([pw_bytes Ews (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws))) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - (Zlength (ws_bytes ws)))) (VO_tail (Zlength (ws_bytes ws)) src); pw_bytes Ews (Z.max 1 cap - cap) (Zrepeat Vundef (Z.max 1 cap - cap)) (VO_tail cap dst)], gv, dc, set_ex dctx_init false, Ews, Ews, dst, cap, Ews, src, ws_bytes ws).
    { unfold mbuf; rewrite if_false by auto. cancel. }
    1: split; eapply VO_buf_ok; [auto | rep_lia | simpl; tauto | auto | rep_lia | simpl; tauto].
    Intros vret. destruct vret as [[r out] st2].
    unfold mbuf; rewrite if_false by auto.
    api_init; match goal with Ha: after_decode _ _ _ |- _ => apply VO_after_init2 in Ha; cbn [fst snd] in Ha; subst st2 end.
    cbn [fst snd] in *.
    match goal with Ho: oneshot_dctx _ _ _ _ _ |- _ => apply oneshot_dctx_nil in Ho; [change (oneshot_ok md_dflt (Some no_dict) (ws_bytes ws) cap r out) in Ho | reflexivity] end.
    sep_apply (VO_dres_e2 DD gv Ews). sep_apply VO_pws_unfold. Intros.
    forward.
    Exists r out dc (Some (set_ex dctx_init false)). entailer!. all: rewrite ?WD_arr; cancel. }
  Intros r out dc ost. thaw FR. rewrite (WD_arr Ews cap out dst).
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  { (* a success: the content *)
    assert (Er: is_error_code r = false) by (destruct (is_error_code r); [discriminate | reflexivity]).
    destruct (VO_success ws cap r out Hfacts H0 H6 Er) as [Hr Hout]. subst r.
    assert (Hfit: Zlength (ws_content ws) <= cap) by (destruct H6 as [Hf _]; apply Hf, Er).
    forward.
    forward_call Int.one.
    1: (entailer!; unfold vl; simpl; rewrite Int64.eq_true; reflexivity).
    rewrite (field_at_data_at Ews t_wseries (DOT _content)).
    change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar (2^18)).
    rewrite (split2_data_at_Tarray_app (Zlength (ws_content ws)) (2^18)) by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
    Intros.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_for_simple_bound (Zlength (ws_content ws)) (EX i:Z, PROPx P (LOCALx L (SEPx R))) end.
    1: entailer!.
    2: (forward_call (gv, dc, ost);
        sep_apply (VO_join Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src
            ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
        sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0);
        forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv);
        rewrite <- (WD_arr Ews cap out dst);
        sep_apply (VO_join Ews cap out (Zrepeat Vundef (Z.max 1 cap - cap)) dst
            ltac:(rep_lia) ltac:(assumption) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
        sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0);
        forward_call (tarray tuchar (Z.max 1 cap), dst, gv);
        forward).
    assert (Ho: Znth i out = Vint (Int.repr (Znth i (ws_content ws))))
      by (apply VO_out_at with (r := Zlength (ws_content ws)); auto).
    assert (Hb: is_byte (Znth i (ws_content ws))) by (apply Forall_Znth; auto).
    unfold is_byte in Hb.
    forward.
    1: (entailer!; change (@Znth val Vundef i out) with (@Znth val Inhabitant_val i out); rewrite Ho; simpl;
        rewrite Int.unsigned_repr by rep_lia; rep_lia).
    change (@Znth val Vundef i out) with (@Znth val Inhabitant_val i out). rewrite Ho.
    assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_oneshot__sr)) (Vlong (Int64.repr i))) =
      field_address (tarray tuchar (Zlength (ws_content ws))) (SUB i)
        (field_address t_wseries (DOT _content) (gv _x_valid_oneshot__sr))) as Ha.
    1: entailer!.
    1: rewrite arr_field_address by (auto; lia).
    1: (unfold field_address;
        match goal with |- context [@field_compatible_dec ?cs ?t ?g ?p] =>
          destruct (@field_compatible_dec cs t g p) as [Hf|Hf] end;
        [rewrite offset_offset_val; f_equal; simpl; lia
        | exfalso; destruct H17 as [Hx _]; unfold field_address in Hx; rewrite if_false in Hx by exact Hf; exact Hx]).
    forward.
    forward_call Int.one.
    1: (entailer!; simpl; rewrite Int.eq_true; reflexivity).
    entailer!. }
  { (* an error: with room for the content and a series within zstd's range, memory *)
    assert (Er: is_error_code r = true) by (destruct (is_error_code r); [reflexivity | contradiction]).
    forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if.
    - sep_apply (VO_ws_fold Ews ws (gv _x_valid_oneshot__sr) Hnb).
      apply -> seq_assoc.
      forward_call (Ews, gv _x_valid_oneshot__sr, ws).
      sep_apply (VO_ws_unfold Ews ws (gv _x_valid_oneshot__sr) Hnb). Intros.
      destruct (within_oneshot_b (ws_frames ws)) eqn:Ew.
      + forward. apply semax_if_seq. forward_if.
        2: (exfalso; apply Int.one_not_zero; assumption).
        forward_call r.
        forward_call Int.one.
        1: (entailer!; rewrite (VO_error ws _ r out Hfacts H0 H6 Er ltac:(lia) Ew); reflexivity).
        (forward_call (gv, dc, ost);
          sep_apply (VO_join Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src
              ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
          sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0);
          forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv);
          rewrite <- (WD_arr Ews cap out dst);
          sep_apply (VO_join Ews cap out (Zrepeat Vundef (Z.max 1 cap - cap)) dst
              ltac:(rep_lia) ltac:(assumption) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
          sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0);
          forward_call (tarray tuchar (Z.max 1 cap), dst, gv);
          forward).
      + forward. apply semax_if_seq. forward_if.
        1: VO_kill.
        (forward_call (gv, dc, ost);
          sep_apply (VO_join Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src
              ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
          sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0);
          forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv);
          rewrite <- (WD_arr Ews cap out dst);
          sep_apply (VO_join Ews cap out (Zrepeat Vundef (Z.max 1 cap - cap)) dst
              ltac:(rep_lia) ltac:(assumption) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
          sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0);
          forward_call (tarray tuchar (Z.max 1 cap), dst, gv);
          forward).
    - forward. apply semax_if_seq. forward_if.
      1: VO_kill.
      (forward_call (gv, dc, ost);
        sep_apply (VO_join Ews (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws)) (Zrepeat Vundef (Z.max 1 (Zlength (ws_bytes ws)) - Zlength (ws_bytes ws))) src
            ltac:(rep_lia) ltac:(rewrite Zlength_map; reflexivity) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
        sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws)))) src Hs0);
        forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv);
        rewrite <- (WD_arr Ews cap out dst);
        sep_apply (VO_join Ews cap out (Zrepeat Vundef (Z.max 1 cap - cap)) dst
            ltac:(rep_lia) ltac:(assumption) ltac:(rewrite Zlength_Zrepeat; [reflexivity | lia]));
        sep_apply (@VO_free_nn_ HCS (tarray tuchar (Z.max 1 cap)) dst Hd0);
        forward_call (tarray tuchar (Z.max 1 cap), dst, gv);
        forward). }
Unshelve. all: apply WD_cce.
Qed.
