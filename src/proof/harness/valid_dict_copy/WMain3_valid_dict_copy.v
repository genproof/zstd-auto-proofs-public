(* MainOK of the unit valid_dict_copy: the main of valid_dict_copy adapted to API v3 from its v2 proof; proved in the small context G1,
   then lifted to G0. *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_copy.WTopSpecs_valid_dict_copy.

Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.writer.SeriesLemmas.
Require Import Zstd.proof.harness.valid_dict_copy.VDC32Lemmas.
Require Import Zstd.proof.zstd.NullBuf.
Require Import Zstd.proof.harness.ApiAfterKit.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.CompSpecs.

Lemma pws_two w1 w2 : pws_pred [w1; w2] = (pw_pred w1 * pw_pred w2)%logic.
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma ddict_res_nr (DD: globals -> val -> ddict_st -> mpred) gv sh q ddv : dd_ref ddv = None ->
  ddict_res DD gv sh q ddv = (DD gv q ddv && valid_pointer q).
Proof. intros H. unfold ddict_res. rewrite H. apply sepcon_emp. Qed.

Definition dr_own (b: list Z) : dictref := {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |}.

Lemma load_facts st1 r1 b : dict_auto b <> None -> load_result dctx_init st1 r1 (dr_own b) ->
  dc_ss st1 = ss_init /\ dc_last st1 = None /\ (is_error_code r1 = false -> dc_dict st1 = Some (dr_own b)) /\
  (is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation) /\
  dc_par st1 = dparams_dflt /\ dc_set st1 = nil /\ dc_bl st1 = None.
Proof.
  intros Hd H. destruct H as [[-> ->] | (He & -> & [[_ Hn] | ->])].
  - simpl. repeat split; auto. intros E. vm_compute in E. discriminate.
  - cbn in Hn. congruence.
  - simpl. repeat split; auto. intros E. congruence.
Qed.

Lemma dr_of_2 dd ddv : dr_of 2 dd ddv = dr_own (dd_bytes ddv).
Proof. unfold dr_of. destruct (Z.eq_dec 2 2); [reflexivity | lia]. Qed.

Lemma last_ok_dr st api dd b : (dc_last st = None \/ dc_last st = Some (dr_of api dd b)) ->
  (api <> 2 -> dc_last st = None) -> last_ok st (dr_of api dd b).
Proof.
  intros [E|E] H; unfold last_ok; [left; exact E|].
  destruct (Z.eq_dec api 2) as [->|n]; [|left; auto].
  right. rewrite dr_of_2 in *. split; [exact E | exact Logic.I].
Qed.

Lemma dr_of_n2 api dd b : api <> 2 -> dr_of api dd b = ddict_ref dd b.
Proof. intros. unfold dr_of. destruct (Z.eq_dec api 2); [lia | reflexivity]. Qed.

Lemma dict_res_dr (DD: globals -> val -> ddict_st -> mpred) gv sh api dd ddv :
  (api = 2 -> dd = nullval) -> (api <> 2 -> dd <> nullval) -> dd_ref ddv = None ->
  dict_res DD gv sh (Some (dr_of api dd ddv)) = (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd)).
Proof.
  intros H1 H2 H3. unfold dict_res, dr_of. destruct (Z.eq_dec api 2).
  - rewrite if_true by auto. reflexivity.
  - rewrite if_false by auto. simpl. apply ddict_res_nr; auto.
Qed.

Lemma dict_buf_ok_dr W sh api dd b shd cap dst : dd_ref b = None -> dict_buf_ok W sh (Some (dr_of api dd b)) shd cap dst.
Proof. intros H. unfold dict_buf_ok, dr_of. destruct (Z.eq_dec api 2); simpl; auto. rewrite H. auto. Qed.

Lemma dictref_model_dr api dd b : dictref_model (Some (dr_of api dd b)) = dict_auto (dd_bytes b).
Proof. unfold dr_of. destruct (Z.eq_dec api 2); reflexivity. Qed.

Lemma after_use_dr st api dd b : dc_dict st = Some (dr_of api dd b) -> after_use st = st.
Proof. intros E. unfold after_use. rewrite E. unfold dr_of. destruct (Z.eq_dec api 2); reflexivity. Qed.

Lemma after_decode_facts3 st st' l : after_decode st st' l ->
  dc_par st' = dc_par st /\ dc_set st' = dc_set st /\ dc_bl st' = dc_bl st.
Proof. intros [-> | ->]; simpl; auto. Qed.

Lemma refdd_init st' r q dd : refddict_result dctx_init st' r q dd ->
  r = 0 /\ st' = set_dict dctx_init (Some (ddict_ref q dd)).
Proof. unfold refddict_result. intros [[-> ->]|[H _]]; [split; reflexivity | discriminate H]. Qed.

Lemma dres_init_emp (DD: globals -> val -> ddict_st -> mpred) gv sh : dict_res DD gv sh (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Lemma sres_init_emp (DD: globals -> val -> ddict_st -> mpred) gv sh : set_res DD gv sh (dc_set dctx_init) (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Lemma set_res_intro (DD: globals -> val -> ddict_st -> mpred) gv sh st (P: mpred) :
  dc_set st = nil -> P |-- P * set_res DD gv sh (dc_set st) (dc_dict st).
Proof. intros H. rewrite H, set_res_nil, sepcon_emp. apply derives_refl. Qed.

Lemma err64 : is_error_code (err_code ZSTD_error_memory_allocation) = true /\
  error_of (err_code ZSTD_error_memory_allocation) = ZSTD_error_memory_allocation.
Proof. split; reflexivity. Qed.

Lemma content_split ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p =
  (data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
   data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p)))%logic.
Proof.
  intros Hn Hfc. rewrite field_at_data_at.
  change (nested_field_type t_wseries (DOT _content)) with (tarray tuchar 262144).
  apply split2_data_at_Tarray_app; rewrite ?Zlength_map, ?Zlength_Zrepeat; rep_lia.
Qed.

Lemma content_fold ws p : Zlength (ws_content ws) <= 2 ^ 18 -> field_compatible t_wseries (DOT _content) p ->
  data_at Ews (tarray tuchar (Zlength (ws_content ws))) (zbytes (ws_content ws)) (field_address t_wseries (DOT _content) p) *
  data_at Ews (tarray tuchar (262144 - Zlength (ws_content ws))) (Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
     (field_address0 (tarray tuchar 262144) (SUB (Zlength (ws_content ws))) (field_address t_wseries (DOT _content) p))
  |-- field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p.
Proof. intros Hn Hfc. rewrite (content_split ws p Hn Hfc). apply derives_refl. Qed.

(* ---------- the context main is proved in first: only what it calls ---------- *)

Section Body.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Variable HWG : forall gv, InitGPred wvardefs gv |-- WG gv.

Definition G1 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDDict_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD;
   ZSTD_DCtx_loadDictionary_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
   gp_assert_spec;
   choose_spec; choose_in_spec; exact_copy_spec; within_oneshot_spec; w_dict_spec WG WDS; w_series_spec WG WDS].

Lemma body_main_G1 : semax_body Vprog G1 f_main main_spec.
Proof.
  change (semax_body Vprog G1 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_valid_dict_copy.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict_copy__sr) *
    data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict_copy__wd) * TT)))%logic).
  { intros Hgv. apply VDC_pre; auto. }
  { reflexivity. }
  { apply vars_in_tycontext. }
  eapply semax_pre with (P' := PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv; WG gv;
    data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict_copy__sr);
    data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict_copy__wd); TT)).
  { change (stackframe_of f_main) with (fun _ : environ => @emp mpred _ _).
    rewrite sepcon_emp_fun_VDC. entailer!. sep_apply (create_mem_mgr gv). cancel. }
  abbreviate_semax.
  forward_call 3. Intros a.
  forward. forward.
  forward_call (gv, Ews, gv _x_valid_dict_copy__wd).
  Intros wd.
  forward_call (gv, Ews, gv _x_valid_dict_copy__sr, gv _x_valid_dict_copy__wd, Some (wd, Ews)).
  { unfold wdict_arg. entailer!. }
  Intros ws.
  unfold wdict_arg, wdict_rep. Intros stv.
  pose proof H2 as (Hsb & Hsc & Hlb & Hlc & Hnf & _).
  pose proof H0 as (Hdb & Hdl & Hda & _).
  sep_apply (wd_take wd (gv _x_valid_dict_copy__wd) stv ltac:(lia)).
  destruct (sr_unfold ws (gv _x_valid_dict_copy__sr)) as [Rs Es]. rewrite Es.
  Intros.
  forward.
  forward_call (0, Zlength (ws_content ws) + 16).
  Intros cap.
  forward.
  forward.
  sep_apply (sr_bytes_borrow ws (gv _x_valid_dict_copy__sr) ltac:(lia)).
  forward_call (gv, Ews, gv _x_valid_dict_copy__sr, ws_bytes ws).
  { cancel. }
  Intros src.
  forward.
  sep_apply (modus_ponens_wand (data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) (gv _x_valid_dict_copy__sr))).
  sep_apply (copy_buf src (ws_bytes ws)).
  forward.
  forward_call (gv, Ews, gv _x_valid_dict_copy__wd, wd_bytes wd).
  Intros dict.
  forward.
  sep_apply (copy_buf dict (wd_bytes wd)).
  if_set_post (Vlong (Int64.repr (Z.max 1 cap))).
  { forward. entailer!. norm. do 2 f_equal; lia. }
  { forward. entailer!. norm. do 2 f_equal; lia. }
  forward_call (tarray tuchar (Z.max 1 cap), gv).
  { simpl. rep_lia. }
  Intros dst. forward.
  assert_PROP (is_pointer_or_null dst) as PNdst by (destruct (eq_dec dst nullval); entailer!).
  sep_apply (malloc_buf dst cap); [lia|].
  forward_call gv.
  Intros dctx.
  rewrite add_repr.
  assert (Hapi: 1 <= 1 + a <= 3) by lia.
  forget (1 + a) as api.
  set (R0 := if eq_dec src nullval then 0 else if eq_dec dict nullval then 0 else if eq_dec dst nullval then 0 else
             if eq_dec dctx nullval then 0 else if Z.eq_dec api 2 then 2 else 1).
  apply -> seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Ql (SEPx ?Rl))) (Ssequence _ _) _ =>
    apply semax_seq with (Q := PROPx P (LOCALx (temp _rounds (Vint (Int.repr R0)) :: Ql) (SEPx Rl))) end.
  { abbreviate_semax. subst R0.
    destruct (eq_dec src nullval) as [Es0|Ns].
    { subst src. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNsrc Ns). destruct src; try contradiction.
    destruct (eq_dec dict nullval) as [Ei|Ni].
    { subst dict. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdict Ni). destruct dict; try contradiction.
    destruct (eq_dec dst nullval) as [Ed|Nd].
    { subst dst. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdst Nd). destruct dst; try contradiction.
    destruct (eq_dec dctx nullval) as [Ec|Nc].
    { subst dctx. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdctx Nc). destruct dctx; try contradiction.
    destruct (Z.eq_dec api 2).
    { repeat blk_step. all: entailer!. }
    { repeat blk_step. all: entailer!. } }
  assert (HR0: 0 <= R0 <= 2 /\ (R0 <> 0 -> src <> nullval /\ dict <> nullval /\ dst <> nullval /\ dctx <> nullval /\
             R0 = if Z.eq_dec api 2 then 2 else 1)).
  { subst R0. repeat destruct (eq_dec _ _); destruct (Z.eq_dec api 2); split; try lia; intros; repeat split; auto; lia. }
  clearbody R0.
  set (T13 := if Z.eq_dec R0 0 then 0 else if Z.eq_dec api 2 then 0 else 1).
  if_set_post (Vint (Int.repr T13)).
  { forward. entailer!. subst T13. repeat destruct (Z.eq_dec _ _); repeat destruct (zeq _ _); try lia; reflexivity. }
  { forward. entailer!. norm. subst T13. repeat destruct (Z.eq_dec _ _); try lia; reflexivity. }
  rewrite <- (field_at_data_at Ews t_wseries (DOT _bytes)).
  sep_apply (if_drop_vp dctx (DC gv dctx dctx_init)).
  forward_if (EX R: Z, EX dd: val, EX ddv: ddict_st,
    PROP (0 <= R <= 2; R <> 0 -> src <> nullval /\ dict <> nullval /\ dst <> nullval /\ dctx <> nullval /\
            R = (if Z.eq_dec api 2 then 2 else 1) /\ (api <> 2 -> dd <> nullval);
          api = 2 -> dd = nullval; is_pointer_or_null dd; dd_bytes ddv = wd_bytes wd /\ dd_ref ddv = None)
    LOCAL (temp _rounds (Vint (Int.repr R)); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx dctx_init);
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap (Zrepeat Vundef cap); buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
  { (* createDDict *)
    assert (HT: R0 <> 0 /\ api <> 2) by (subst T13; repeat destruct (Z.eq_dec _ _); try (exfalso; apply H7; reflexivity); split; auto).
    destruct HT as [HR0n Hap].
    destruct HR0 as [_ HR0]. destruct (HR0 HR0n) as (Ns & Ni & Nd & Nc & ER).
    forward.
    rewrite (buf_res_nn dict) by auto. Intros.
    rewrite <- (pws_one (rest_w dict (Zlength (wd_bytes wd)))).
    rewrite <- (bytes_at_ptr Ews (wd_bytes wd) dict) by (apply ptr_nn; auto).
    forward_call ([rest_w dict (Zlength (wd_bytes wd))], gv, Ews, dict, wd_bytes wd).
    { try (split; [intro; contradiction |]). try intros _. apply (buf_ok_of [] []); auto; rep_lia. }
    Intros vret. destruct vret as [q ddv]. cbn [fst snd] in *. rewrite pws_one.
    rewrite bytes_at_ptr by (apply ptr_nn; auto). forward.
    match goal with H: dd_ref ddv = _ |- _ => rewrite if_false in H by auto end.
    match goal with H: dd_ref ddv = _ |- _ => replace (Zlength (wd_bytes wd) =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia); rename H into Hddr end.
    match goal with H: dd_bytes ddv = _ |- _ => rename H into Hddb end.
    destruct (eq_dec q nullval) as [Eq|Nq].
    { subst q. forward_if.
      { forward. Exists 0 nullval ddv. rewrite (buf_res_nn dict) by auto. entailer!. }
      { norm2. } }
    { match goal with H: is_pointer_or_null q |- _ => pose proof (ptr_nn _ H Nq) end. destruct q; try contradiction.
      forward_if.
      { norm2. }
      { forward. Exists R0 (Vptr b i) ddv. rewrite (buf_res_nn dict) by auto.
        destruct (eq_dec (Vptr b i) nullval); [discriminate|].
        entailer!. split; [destruct (Z.eq_dec api 2); lia | intros; repeat split; auto]. } } }
  { forward. Exists R0 nullval (dd0 wd). entailer!.
    destruct HR0 as [_ HR0]. destruct (HR0 H22) as (?&?&?&?&?). repeat split; auto.
    intros Hn. exfalso. subst T13. destruct (Z.eq_dec R0 0); [contradiction|].
    destruct (Z.eq_dec api 2); [contradiction|].
    apply (f_equal Int.unsigned) in H7. rewrite Int.unsigned_repr in H7 by rep_lia. discriminate. }
  Intros R1 dd ddv.
  repeat match goal with H: dd_bytes ddv = _ /\ dd_ref ddv = _ |- _ => destruct H end.
  match goal with H: dd_bytes ddv = _ |- _ => rename H into Hddb end. match goal with H: dd_ref ddv = _ |- _ => rename H into Hddr end.
  forward.
  forward_loop (EX k: Z, EX R: Z, EX st: dctx_st, EX out: list val,
    PROP (0 <= k <= R; R <= 2; is_pointer_or_null dd; api = 2 -> dd = nullval;
          R <> 0 -> src <> nullval /\ dict <> nullval /\ dst <> nullval /\ dctx <> nullval /\ (api <> 2 -> dd <> nullval);
          api <> 2 -> R <= 1;
          Zlength out = cap; dc_ss st = ss_init; k = 0 -> st = dctx_init;
          0 < k < R -> dc_dict st = Some (dr_of api dd ddv);
          dc_last st = None \/ dc_last st = Some (dr_of api dd ddv); dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_bl st = None)
    LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st);
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert
    break: (EX st: dctx_st, EX out: list val,
    PROP (is_pointer_or_null dd; api = 2 -> dd = nullval; Zlength out = cap)
    LOCAL (temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st);
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
  { Exists 0 R1 dctx_init (Zrepeat Vundef cap). entailer!.
    split; [intros Hr; destruct (H8 Hr) as (?&?&?&?&?&?); auto | split; [intros Hn; destruct (Z.eq_dec R1 0) as [|Hr]; [lia|]; destruct (H8 Hr) as (_&_&_&_&E&_); rewrite E; destruct (Z.eq_dec api 2); lia | rewrite Zlength_Zrepeat; lia]]. }
  { Intros k R st out.
    match goal with H: dc_par st = _ |- _ => rename H into Hpar end. match goal with H: dc_set st = _ |- _ => rename H into Hset end. match goal with H: dc_bl st = _ |- _ => rename H into Hbl end.
    forward_if.
    2: { forward. Exists st out. entailer!. }
    destruct (H12 ltac:(lia)) as (Ns & Ni & Nd & Nc & Ndd).
    rewrite (if_false (dctx = nullval)) by auto.
    clear R0 HR0 T13 R1 H7 H8.
    forward_if (EX r: Z, EX R': Z, EX st': dctx_st, EX out': list val,
    PROP (0 <= r <= Int64.max_unsigned; k + 1 <= R' <= R; Zlength out' = cap; dc_ss st' = ss_init;
          0 < k + 1 < R' -> dc_dict st' = Some (dr_of api dd ddv);
          dc_last st' = None \/ dc_last st' = Some (dr_of api dd ddv);
          is_error_code r = false -> r <= cap;
          is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out' = zbytes (ws_content ws);
          is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
            r = err_code ZSTD_error_memory_allocation; dc_par st' = dparams_dflt /\ dc_set st' = nil /\ dc_bl st' = None)
    LOCAL (temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
    { (* api 1: ZSTD_decompress_usingDDict *)
      forward.
      rewrite (buf_res_nn dst) by auto. rewrite (buf_res_nn src) by auto.
      rewrite (if_false (dd = nullval)) by (apply Ndd; lia). Intros.
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
      forward_call ([rest_w dst cap; rest_w src (Zlength (ws_bytes ws))], gv, dctx, st, Ews, dst, cap, Ews, src, ws_bytes ws, Ews, dd, ddv).
      { rewrite pws_two, (ddict_res_nr DD gv Ews dd ddv Hddr). cancel. }
      { split; [apply (buf_ok_of [] [rest_w src (Zlength (ws_bytes ws))]); auto; lia |].
        split; [apply (buf_ok_of [rest_w dst cap] []); auto; rep_lia |].
        unfold ddict_buf_ok; rewrite Hddr; exact Logic.I. }
      Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *.
      api_init; match goal with H: after_decode _ _ _ |- _ => pose proof (after_decode_facts3 _ _ _ H) as (Hpar' & Hset' & Hbl'); apply after_decode_facts in H; destruct H as (Hss & Hdi & Hla) end.
      match goal with H: oneshot_ok _ _ _ _ _ _ |- _ => rewrite Hpar, dmode_of_dflt, Hddb in H; pose proof (proj1 H) as Hle; apply (VDC_oneshot wd ws cap r out' H0 H2 H3) in H; destruct H as [Hok Herr] end.
      rewrite pws_two, (ddict_res_nr DD gv Ews dd ddv Hddr). Intros.
      forward.
      Exists r R st' out'.
      rewrite (buf_res_nn dst) by auto. rewrite (buf_res_nn src) by auto.
      rewrite (if_false (dctx = nullval)) by auto. rewrite (if_false (dd = nullval)) by (apply Ndd; lia).
      entailer!.
      destruct Hla as [E|E]; rewrite E; [exact H18 | right; unfold dr_of; destruct (Z.eq_dec 1 2); [lia | reflexivity]]. }
    { (* api 2, 3 *)
      forward.
      forward_if (EX r1: Z, EX R': Z, EX st1: dctx_st,
    PROP (0 <= r1 <= Int64.max_unsigned; k + 1 <= R' <= R; dc_ss st1 = ss_init;
          dc_last st1 = None \/ dc_last st1 = Some (dr_of api dd ddv); api <> 2 -> dc_last st1 = None;
          is_error_code r1 = false -> dc_dict st1 = Some (dr_of api dd ddv);
          is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation /\ R' = (k + 1)%Z; dc_par st1 = dparams_dflt /\ dc_set st1 = nil /\ dc_bl st1 = None)
    LOCAL (temp _r (Vlong (Int64.repr r1)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st1);
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
      { (* k = 0: the dictionary *)
        assert (Hk0: k = 0) by (norm2; lia). rewrite (H16 Hk0).
        forward_if (EX r1: Z, EX st1: dctx_st,
    PROP (0 <= r1 <= Int64.max_unsigned; dc_ss st1 = ss_init; dc_last st1 = None;
          is_error_code r1 = false -> dc_dict st1 = Some (dr_of api dd ddv);
          is_error_code r1 = true -> r1 = err_code ZSTD_error_memory_allocation; dc_par st1 = dparams_dflt /\ dc_set st1 = nil /\ dc_bl st1 = None)
    LOCAL (temp _x_valid_dict_copy__t'15 (Vlong (Int64.repr r1)); temp _r (Vlong (Int64.repr 0)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R)); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st1);
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
        { (* api 2: ZSTD_DCtx_loadDictionary *)
          subst api. forward.
          rewrite (buf_res_nn dict) by auto. Intros.
          rewrite <- (pws_one (rest_w dict (Zlength (wd_bytes wd)))).
          forward_call ([rest_w dict (Zlength (wd_bytes wd))], gv, dctx, dctx_init, Ews, dict, wd_bytes wd).
          { apply (buf_ok_of [] []); auto; rep_lia. }
          Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *. rewrite pws_one.
          api_init; match goal with H: load_result _ _ _ _ |- _ => apply (load_facts _ _ _ Hda) in H; destruct H as (Hs1 & Hl1 & Hd1 & He1 & Hp1 & Hst1 & Hb1) end.
          forward.
          Exists r1 st1.
          rewrite (buf_res_nn dict) by auto. rewrite dr_of_2, Hddb.
          rewrite (if_false (dctx = nullval)) by auto.
          entailer!. }
        { (* api 3: ZSTD_DCtx_refDDict *)
          assert (Hd: dd <> nullval) by (apply Ndd; lia).
          rewrite (if_false (dd = nullval)) by auto.
          sep_apply (andp_drop_vp (DD gv dd ddv) dd).
          match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
            apply semax_pre with (PROPx P (LOCALx Q (SEPx (dict_res DD gv Ews (dc_dict dctx_init) ::
              set_res DD gv Ews (dc_set dctx_init) (dc_dict dctx_init) :: R))));
            [rewrite dres_init_emp, sres_init_emp; entailer! |] end.
          forward_call (gv, dctx, dctx_init, dd, ddv, Ews).
          { rewrite (if_false (dd = nullval)) by auto. cancel. }
          Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *.
          api_init. rewrite (if_false (dd = nullval)) by auto.
          match goal with H: refddict_result _ _ _ _ _ |- _ => apply refdd_init in H; destruct H as [-> ->] end.
          rewrite dres_init_emp, sres_init_emp.
          forward.
          Exists 0 (set_dict dctx_init (Some (dr_of api dd ddv))).
          rewrite (dr_of_n2 api) by lia.
          rewrite (if_false (dctx = nullval)) by auto. rewrite (if_false (dd = nullval)) by auto.
          entailer!.
          all: try (match goal with H: is_error_code 0 = true |- _ => vm_compute in H; discriminate end).
          all: try apply derives_refl. }
        Intros r1 st1.
        forward.
        forward_call r1.
        forward_if.
        { forward. Exists r1 1 st1. entailer!. }
        { forward. Exists r1 R st1. entailer!.
          match goal with H: Int.repr (if is_error_code r1 then 1 else 0) = Int.zero, H': is_error_code r1 = true |- _ =>
            rewrite H' in H; apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr in H by rep_lia; discriminate end. } }
      { (* k > 0 *)
        forward. Exists 0 R st. rewrite (if_false (dctx = nullval)) by auto. entailer!.
        split; [intros _; apply H17; lia | intros E; vm_compute in E; discriminate]. }
      Intros r1 R' st1.
      match goal with H: dc_par st1 = _ |- _ => rename H into Hpar1 end. match goal with H: dc_set st1 = _ |- _ => rename H into Hset1 end. match goal with H: dc_bl st1 = _ |- _ => rename H into Hbl1 end.
      forward_call r1.
      forward_if.
      { (* ZSTD_decompressDCtx *)
        assert (He: is_error_code r1 = false) by (destruct (is_error_code r1); auto; discriminate).
        match goal with H: is_error_code r1 = false -> dc_dict st1 = _ |- _ => specialize (H He); rename H into Hd1 end.
        forward.
        rewrite (buf_res_nn dst) by auto. rewrite (buf_res_nn src) by auto. Intros.
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
        sep_apply (data_at__mbuf Ews cap dst).
        rewrite (if_false (dctx = nullval)) by auto.
        rewrite <- (dict_res_dr DD gv Ews api dd ddv) by auto.
        rewrite <- Hd1.
        sep_apply (set_res_intro DD gv Ews st1 (mem_mgr gv) Hset1).
        forward_call ([rest_w dst cap; rest_w src (Zlength (ws_bytes ws))], gv, dctx, st1, Ews, Ews, dst, cap, Ews, src, ws_bytes ws).
        { rewrite pws_two. cancel. }
        { split; [apply (buf_ok_of [] [rest_w src (Zlength (ws_bytes ws))]); auto; lia |].
          split; [apply (buf_ok_of [rest_w dst cap] []); auto; rep_lia |].
          rewrite Hd1. split; [apply dict_buf_ok_dr; exact Hddr |].
          rewrite Hset1; constructor. }
        Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
        match goal with H: oneshot_dctx _ _ _ _ _ |- _ => apply (oneshot_dctx_nil st1 _ _ _ _ Hset1) in H; rewrite Hpar1, dmode_of_dflt in H end.
        api_init.
        rewrite Hd1, dictref_model_dr, Hddb, (after_use_dr st1 api dd ddv Hd1) in *.
        match goal with H: after_decode _ _ _ |- _ => pose proof (after_decode_facts3 _ _ _ H) as (Hpar' & Hset' & Hbl'); apply after_decode_facts in H; destruct H as (Hss & Hdi & Hla) end.
        match goal with H: oneshot_ok _ _ _ _ _ _ |- _ => pose proof (proj1 H) as Hle; apply (VDC_oneshot wd ws cap r out' H0 H2 H3) in H; destruct H as [Hok Herr] end.
        rewrite pws_two, (dict_res_dr DD gv Ews api dd ddv) by auto. rewrite Hset1, set_res_nil. Intros.
        forward.
        Exists r R' st' out'.
        rewrite (buf_res_nn dst) by auto. rewrite (buf_res_nn src) by auto.
        rewrite (if_false (dctx = nullval)) by auto.
        entailer!.
        destruct Hla as [E|E]; rewrite E; auto. }
      { assert (He: is_error_code r1 = true)
          by (destruct (is_error_code r1); auto; match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end).
        match goal with H: is_error_code r1 = true -> _ |- _ => destruct (H He) as [Er ER] end.
        forward. Exists r1 R' st1 out. entailer!. } }
    Intros r R' st' out'.
    forward_call r.
    forward_if (PROP () LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv) SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
    { (* success: the content *)
      assert (He: is_error_code r = false) by (destruct (is_error_code r); auto; discriminate).
      match goal with H: is_error_code r = false -> _ /\ _ |- _ => destruct (H He) as [Er Esub] end.
      match goal with H: is_error_code r = false -> r <= cap |- _ => specialize (H He) as Hrcap end.
      forward.
      forward_call (Int.one).
      { entailer!. rewrite Int64.eq_true. reflexivity. }
      forward.
      forward_loop (EX i: Z, PROP (0 <= i <= r) LOCAL (temp _i (Vlong (Int64.repr i)); temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv) SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert
        break: (PROP () LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv) SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
      { Exists 0. entailer!. }
      { Intros i.
        forward_if.
        2: { forward. entailer!. }
        norm.
        assert (Hi1: Znth i out' = Vint (Int.repr (Znth i (ws_content ws)))).
        { replace (Znth i out') with (Znth (i + 0) out') by (f_equal; lia). rewrite <- (Znth_sublist 0 i r out') by lia. rewrite Esub, Znth_map by lia. reflexivity. }
        assert (Hi2: Znth i (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) =
                     Vint (Int.repr (Znth i (ws_content ws)))).
        { rewrite app_Znth1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
        assert (Hb: 0 <= Znth i (ws_content ws) <= Byte.max_unsigned).
        { pose proof (proj1 (Forall_Znth _ _) Hsc i ltac:(lia)) as Hz. unfold is_byte in Hz. rep_lia. }
        rewrite (buf_res_nn dst) by auto. Intros.
        rewrite (vdc_data_at_cs ZCS HCS Ews cap out' dst).
        forward.
        1: { entailer!. replace (@Znth val Vundef i out') with (Vint (Int.repr (Znth i (ws_content ws)))) by (rewrite <- Hi1; reflexivity).
             simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        assert_PROP (field_compatible t_wseries (DOT _content) (gv _x_valid_dict_copy__sr)) as Hfcc by entailer!.
        rewrite (content_split ws (gv _x_valid_dict_copy__sr) Hlc Hfcc). Intros.
        assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_dict_copy__sr)) (Vlong (Int64.repr i))) =
          field_address (tarray tuchar (Zlength (ws_content ws))) (SUB i) (field_address t_wseries (DOT _content) (gv _x_valid_dict_copy__sr))) as Ea.
        { entailer!. rewrite (field_address_offset t_wseries) by auto.
          rewrite arr_field_address by (auto; try lia; rewrite field_address_offset in *; auto).
          simpl; rewrite offset_offset_val; f_equal; lia. }
        forward.
        1: { entailer!. apply Hb. }
        sep_apply (content_fold ws (gv _x_valid_dict_copy__sr) Hlc Hfcc).
        forward_call (Int.one).
        { entailer!. replace (@Znth val Vundef i out') with (Vint (Int.repr (Znth i (ws_content ws)))) by (rewrite <- Hi1; reflexivity).
          simpl. rewrite Int.eq_true. reflexivity. }
        forward.
        Exists (i + 1). rewrite ?(vdc_data_at_cs ZCS HCS Ews cap out' dst).
        entailer!. }
      }
    { (* an error: memory_allocation when the capacity holds the content and the frames are within range *)
      assert (He: is_error_code r = true)
        by (destruct (is_error_code r); auto; match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end).
      forward.
      forward_if (PROP () LOCAL (temp _x_valid_dict_copy__t'22 (Vint (Int.repr (if andb (Zlength (ws_content ws) <=? cap) (within_oneshot_b (ws_frames ws)) then 1 else 0))); temp _r (Vlong (Int64.repr r)); temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv) SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
      { (* within_oneshot *)
        norm.
        assert (Hfold: (field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr) *
          field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr) *
          field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr) *
          field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr) * Rs)
          |-- data_at Ews t_wseries (wseries_val ws) (gv _x_valid_dict_copy__sr)) by (rewrite Es; apply derives_refl).
        sep_apply Hfold.
        forward_call (Ews, gv _x_valid_dict_copy__sr, ws).
        forward.
        rewrite Es. Intros.
        entailer!. rewrite (proj2 (Z.leb_le _ _)) by lia. destruct (within_oneshot_b _); reflexivity. }
      { norm. forward. entailer!. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
      forward_if (PROP () LOCAL (temp _k (Vint (Int.repr k)); temp _rounds (Vint (Int.repr R')); temp _ddict dd; temp _dctx dctx; temp _dst dst; temp _dict dict;
           temp _src src; temp _cap (Vlong (Int64.repr cap)); temp _api (Vint (Int.repr api)); gvars gv) SEP (mem_mgr gv; zstd_globals gv; (if eq_dec dctx nullval then emp else DC gv dctx st');
         (if eq_dec dd nullval then emp else (DD gv dd ddv && valid_pointer dd));
         buf_res dst cap out'; buf_res dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd));
         buf_res src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws));
         field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr);
         field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) (gv _x_valid_dict_copy__sr); Rs;
         field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) (gv _x_valid_dict_copy__wd); TT))%assert.
      { assert (Hw: Zlength (ws_content ws) <= cap /\ within_oneshot_b (ws_frames ws) = true).
        { match goal with H: Int.repr (if (?b1 && ?b2)%bool then 1 else 0) <> Int.zero |- _ =>
            destruct (b1 && b2)%bool eqn:Eb; [|contradiction H; reflexivity] end.
          apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. auto. }
        destruct Hw as [Hw1 Hw2].
        match goal with H: is_error_code r = true -> _ -> _ -> r = _ |- _ => specialize (H He Hw1 Hw2) as Er end.
        forward_call r.
        forward_call (Int.one).
        { entailer!. }
        entailer!. }
      { forward. entailer!. }
      }
    forward.
    Exists (k + 1) R' st' out'.
    entailer!. }
  (* after the loop: free everything *)
  Intros st out.
  sep_apply (if_drop_vp dd (DD gv dd ddv)).
  replace (if eq_dec dd nullval then emp else DD gv dd ddv)
    with (match (if eq_dec dd nullval then None else Some ddv) with None => emp | Some x => DD gv dd x end)
    by (destruct (eq_dec dd nullval); reflexivity).
  forward_call (gv, dd, if eq_dec dd nullval then None else Some ddv).
  { destruct (eq_dec dd nullval); auto. }
  replace (if eq_dec dctx nullval then emp else DC gv dctx st)
    with (match (if eq_dec dctx nullval then None else Some st) with None => emp | Some x => DC gv dctx x end)
    by (destruct (eq_dec dctx nullval); reflexivity).
  forward_call (gv, dctx, if eq_dec dctx nullval then None else Some st).
  { destruct (eq_dec dctx nullval); auto. }
  sep_apply (buf_free src (Zlength (ws_bytes ws)) (zbytes (ws_bytes ws))); [rep_lia|].
  forward_call (tarray tuchar (Z.max 1 (Zlength (ws_bytes ws))), src, gv).
  sep_apply (buf_free dict (Zlength (wd_bytes wd)) (zbytes (wd_bytes wd))); [rep_lia|].
  forward_call (tarray tuchar (Z.max 1 (Zlength (wd_bytes wd))), dict, gv).
  sep_apply (buf_free dst cap out); [rep_lia|].
  forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
  forward.
Qed.

End Body.

(* ---------- from G1 to G0 (Specs_api DC DD) WG WDS: every entry of G1 is found there unchanged ---------- *)

Lemma VDC_Externals_eq : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma VDC_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VDC_G1_in DC DD WG WDS i fs : initial_world.find_id i (G1 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompressDCtx;
     _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_freeDCtx; _ZSTD_createDDict; _ZSTD_freeDDict;
     _ZSTD_DCtx_loadDictionary; _ZSTD_DCtx_refDDict; _gp_assert;
     _choose; _choose_in; _exact_copy; _within_oneshot; _w_dict; _w_series]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VDC_Externals_eq.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Definition VDC_fun_ids : list ident :=
  [_quickproof_malloc; _quickproof_free;
   _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompress; _ZSTD_decompressDCtx; _ZSTD_decompress_usingDict;
   _ZSTD_decompress_usingDDict; _ZSTD_createDCtx; _ZSTD_createDStream; _ZSTD_freeDCtx; _ZSTD_freeDStream;
   _ZSTD_DCtx_reset; _ZSTD_initDStream; _ZSTD_DCtx_setParameter; _ZSTD_DStreamOutSize;
   _ZSTD_createDDict; _ZSTD_createDDict_byReference; _ZSTD_freeDDict;
   _ZSTD_getDictID_fromDDict; _ZSTD_getDictID_fromDict;
   _ZSTD_DCtx_loadDictionary_byReference; _ZSTD_DCtx_loadDictionary;
   _ZSTD_DCtx_refPrefix; _ZSTD_DCtx_refDDict;
   _ZSTD_decompressStream;
   _ZSTD_findFrameCompressedSize; _ZSTD_getFrameContentSize; _ZSTD_findDecompressedSize;
   _ZSTD_decompressBound; _ZSTD_frameHeaderSize; _ZSTD_getDictID_fromFrame;
   _ZSTD_isFrame; _ZSTD_isSkippableFrame; _ZSTD_getFrameHeader; _ZSTD_readSkippableFrame;
   _ZSTD_DCtx_setFormat; _ZSTD_DCtx_setMaxWindowSize; _ZSTD_resetDStream;
   _ZSTD_DCtx_loadDictionary_advanced; _ZSTD_DCtx_refPrefix_advanced;
   _ZSTD_initDStream_usingDict; _ZSTD_initDStream_usingDDict;
   _ZSTD_getDecompressedSize; _ZSTD_getFrameHeader_advanced;
   _ZSTD_decompressBegin; _ZSTD_decompressBegin_usingDict; _ZSTD_decompressBegin_usingDDict;
   _ZSTD_nextSrcSizeToDecompress; _ZSTD_nextInputType; _ZSTD_decompressContinue;
   _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_estimateDStreamSize;
   _nondet_u32; _gp_assert; _gp_assume;
   _choose; _choose_in; _exact_copy; _within_oneshot; _w_dict; _w_series].

Lemma VDC_G0_ids DC DD WG WDS : map fst (G0 (Specs_api DC DD) WG WDS) = VDC_fun_ids.
Proof. unfold G0, Imports. rewrite VDC_Externals_eq. reflexivity. Qed.

Lemma VDC_vars_funs_b : forallb (fun i => negb (id_in_list i VDC_fun_ids)) (map fst Vprog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VDC_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VDC_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VDC_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = None.
Proof.
  intros H. apply VDC_tyc_g_nil_in in H. apply VDC_find_id_not_in. rewrite VDC_G0_ids.
  pose proof VDC_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

Theorem main_ok3_valid_dict_copy : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (body_main_G1 DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VDC_make_tycontext_g_find Vprog (G1 DC DD WG WDS) i).
    destruct (initial_world.find_id i (G1 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VDC_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) WG WDS) i).
      rewrite (VDC_G1_in DC DD WG WDS i fs E). apply sub_option_refl.
    * (* a plain [rewrite] would also try the left [PTree.get], unfolding [G0] against [nil] *)
      refine (eq_ind_r (fun b => tycontext.sub_option _ b) _
        (VDC_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) WG WDS) i)).
      destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
      rewrite (VDC_var_not_fun DC DD WG WDS i t EV). reflexivity.
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (G1 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VDC_G1_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

