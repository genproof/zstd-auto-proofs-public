(* MainOK of the unit valid_stream: the main of valid_stream adapted to API v3 from its v2 proof. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import Zstd.proof.harness.valid_stream.WTopSpecs_valid_stream.
Require Import Zstd.proof.harness.valid_stream.VSPre.
Require Import Zstd.proof.harness.valid_stream.VSModel.
Require Import Zstd.proof.harness.valid_stream.VSMem.
Require Import Zstd.proof.harness.valid_stream.VSFacts.
Require Import Zstd.proof.harness.valid_stream.VSMem2.
Require Import Zstd.proof.harness.valid_stream.VSMem3.
Require Import Zstd.proof.harness.valid_stream.VSModel2.
Require Import Zstd.proof.model.ParamsDflt Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsW.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_stream.HOK_valid_stream.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Lemma VS_Externals_eq : Externals = [nondet_u32_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Definition VS_G0 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) (WG: globals -> mpred)
    (WDS: wdict -> reptype t_wstate -> Prop) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_createDStream_spec DC; ZSTD_freeDStream_spec DC;
   ZSTD_decompressStream_spec DC DD; gp_assert_spec;
   exact_copy_spec; within_stream_spec; stall_error_spec; chunk_spec; w_series_spec WG WDS].

Lemma VS_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

(* The change_composite_env instance of any two compspecs, without computing it. *)
Definition VS_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma VS_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VS_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma VS_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VS_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma VS_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (VS_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma VS_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.





Ltac VS_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Lemma VS_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

Lemma VS_S_byte: forall bs k, Forall (fun b => 0 <= b <= Byte.max_unsigned) bs -> 0 <= k < Zlength bs ->
  is_int I8 Unsigned (Znth k (map (fun b => Vint (Int.repr b)) bs)).
Proof.
  intros. rewrite Znth_map by lia.
  pose proof (proj1 (Forall_Znth _ _) H k H0). simpl.
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma VS_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (VS_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

(* the witnesses lent to ZSTD_decompressStream: the unused byte of ib = malloc(1) when ilen = 0 *)
Definition VS_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma VS_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
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

Lemma VS_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma VS_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  !!(buf_ok (VS_W il ib) Ews il ib) && (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (VS_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold VS_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply VS_buf_ok_pos; lia | apply derives_refl].
  - apply Zlength_nil_inv in HA. subst A. unfold VS_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply VS_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef]. change (Zrepeat Vundef 1) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma VS_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (VS_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold VS_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold VS_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

Lemma VS_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

Lemma VS_free_prep {cs: compspecs} sh t v p :
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at sh t v p) |--
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at_ sh t p).
Proof. destruct (eq_dec p nullval); [auto|]. apply sepcon_derives; [auto | apply data_at_data_at_]. Qed.

Lemma VS_wdict_null WDS : emp |-- wdict_arg WDS nullval None.
Proof. unfold wdict_arg. entailer!. Qed.

Lemma VSF_frame (fs: list winfo) k : 0 <= k < Zlength fs ->
  Znth k (map winfo_val fs ++ Zrepeat (winfo_val winfo0) (4 - Zlength fs)) = winfo_val (Znth k fs).
Proof.
  intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity.
Qed.

(* main's view of the stream's read bytes: zstd has read ss_ahead (0 or 1) bytes beyond main's ipos *)
Definition VS_in_ok (ss: sstate) (ipos: Z) (bs: list Z) : Prop :=
  0 <= ss_ahead ss <= 1 /\ ipos + ss_ahead ss <= Zlength bs /\ ss_in ss = sublist 0 (ipos + ss_ahead ss) bs.

(* API v3: a context from dctx_init driven by decompressStream alone keeps the default parameters, no DDict set
   and no buffer-less frame *)
Definition VS3 (st: dctx_st) : Prop := dc_par st = dparams_dflt /\ dc_set st = nil /\ dc_bl st = None.

Lemma VS_DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh :
  dc_dict st = None -> dc_set st = nil ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma VS_stream_dict_ok W st : dc_dict st = None -> VS3 st -> stream_dict_ok W st.
Proof. intros Hd (_ & Hs & Hb). unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

Lemma VS_alive_w (sin: list Z) :
  stream_alive_m (dmode_w md_dflt) sel_none (Some no_dict) sin <-> stream_alive sin.
Proof.
  rewrite <- stream_alive_m_dflt. unfold stream_alive_m.
  split; intros [s0 [H1 [H2 H3]]]; exists s0; repeat split; auto;
  try rewrite Zstd.proof.model.ParamsW.series_frames_m_w_nodict in H3; try rewrite Zstd.proof.model.ParamsW.series_frames_m_w_nodict; auto.
Qed.

Lemma VS_claims_w (sin0 sout0 sin sall sout: list Z) (a1: Z) (ocap: option Z) (r: Z) :
  stream_claims_m (dmode_w md_dflt) sel_none (Some no_dict) stream_wlim sin0 sout0 sin sall sout a1 ocap r <->
  stream_claims sin0 sout0 sin sall sout a1 ocap r.
Proof.
  rewrite <- stream_claims_m_dflt. unfold stream_claims_m.
  split; intros H s0 Hb Hpre; specialize (H s0 Hb Hpre);
  rewrite ?Zstd.proof.model.ParamsW.series_frames_m_w_nodict in *; exact H.
Qed.

(* stream_post, unpacked, with both facts on the hostage byte (zstd returns 1 while it holds the last byte of
   a frame; a 0 return has released it) *)
Lemma VS_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' :
  dc_dict st = None -> VS3 st ->
  stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' ->
  exists dl stall' a',
   (opos <= opos' <= osz /\ ipos <= ipos' <= isz /\ Zlength oc' = osz /\
    sublist 0 opos oc' = sublist 0 opos oc /\
    Zlength dl = opos' - opos /\
    (dc_stable st = true \/ stream_alive (ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs) ->
       sublist opos opos' oc' = zbytes dl /\ bytes_ok dl) /\
    0 <= a' <= 1 /\ ipos + ss_ahead (dc_ss st) <= ipos' + a' /\
    (ipos' + a' <= isz \/ ipos' + a' = ipos + ss_ahead (dc_ss st)) /\ (r = 0 -> a' = 0) /\
    st' = set_last
            (set_ss st {| ss_in := ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs;
                          ss_out := ss_out (dc_ss st) ++ dl;
                          ss_stall := stall'; ss_err := is_error_code r;
                          ss_obuf := if dc_stable st then Some (ob, osz) else None; ss_ahead := a';
                          ss_calls := ss_calls (dc_ss st) ++ [(sublist ipos isz ibs, osz - opos)] |})
            (Some stream_mark) /\
    (is_error_code r = false -> (ipos' <> ipos \/ opos' <> opos) -> stall' = 0) /\
    (is_error_code r = false -> ipos' = ipos -> opos' = opos -> 0 <= stall' <= ss_stall (dc_ss st) + 1) /\
    (dc_stable st = false -> ipos = isz -> opos' - opos <= ZSTD_BLOCKSIZE_MAX) /\
    stall_ok r (ss_stall (dc_ss st)) ipos ipos' isz opos opos' osz /\
    stream_claims (sublist 0 (Zlength (ss_in (dc_ss st)) - ss_ahead (dc_ss st)) (ss_in (dc_ss st))) (ss_out (dc_ss st))
      (ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs)
      ((ss_in (dc_ss st) ++ sublist (ipos + ss_ahead (dc_ss st)) (ipos' + a') ibs) ++ sublist (ipos' + a') isz ibs)
      (ss_out (dc_ss st) ++ dl) a' (if dc_stable st then Some osz else None) r) /\
   (a' = 1 -> is_error_code r = false -> r = 1).
Proof.
  intros Hd (Hp & Hs & _) H. unfold stream_post in H. rewrite (st_sel_nil st Hs), Hd, Hp in H.
  change (dmode_of dparams_dflt) with md_dflt in H. change (dictref_model None) with (Some no_dict) in H.
  change (dp_wmax dparams_dflt) with stream_wlim in H. simpl fst in H; simpl snd in H.
  destruct H as (dl & stall' & a' & H). cbv zeta in H.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & Hh & A10 & A11 & A12 & A13 & A14 & A15 & _).
  rewrite VS_alive_w in A6. rewrite VS_claims_w in A15.
  exists dl, stall', a'. split; [|exact Hh].
  do 9 (split; [assumption|]). split; [exact (stream_hostage_zero a' r Hh A7)|].
  repeat (split; [assumption|]). exact A15.
Qed.


(* the bytes the caller saw consumed before the call *)
Lemma VS_sin0 (l: list Z) ipos a : 0 <= ipos -> 0 <= a -> ipos + a <= Zlength l ->
  sublist 0 (Zlength (sublist 0 (ipos + a) l) - a) (sublist 0 (ipos + a) l) = sublist 0 ipos l.
Proof.
  intros. rewrite Zlength_sublist by lia. rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* the bytes read are a prefix of the series, whose walk ends (TEnd) or stops at a rejected header (TDetHdr) *)
Lemma VS_alive ws sin : series_facts no_dict ws -> is_prefix sin (ws_bytes ws) -> stream_alive sin.
Proof.
  intros Hsf Hp. exists (ws_bytes ws). split; [exact (proj1 Hsf)|]. split; [exact Hp|].
  rewrite (VSP_written _ _ no_wlim Hsf). simpl. destruct (all_ok no_wlim (ws_frames ws)); auto.
Qed.

(* sr.content[k], lent out of its wrapper *)
Lemma VS_content_borrow_w (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  VS_Rc V p |--
  @data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) *
  (@data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) -* VS_Rc V p).
Proof. unfold VS_Rc. apply VS_content_borrow. Qed.

Ltac VS_fold :=
  eapply derives_trans; [|apply sepcon_derives; [apply VS_sr_fold | apply derives_refl]];
  unfold VS_fields; simpl fold_right_sepcon; cancel.

Lemma VS_body DC DD WG WDS : (forall gv, InitGPred wvardefs gv |-- WG gv) ->
  semax_body Vprog (VS_G0 DC DD WG WDS) f_main main_spec.
Proof.
intros HWG.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred (sepcon (Zstd.proof.zstd.Globals.zstd_globals gv)
          (sepcon (WG gv) (sepcon (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_stream__sr)) TT))) _ _ _
          Zstd.contracts.x_valid_stream.whole_prog).
4: idtac.
- intros Hgv. eapply derives_trans; [apply (VS_pre gv Hgv) |].
  sep_apply (HWG gv). cancel.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply VS_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, g); auto.
- process_stackframe_of.
  repeat rewrite <- data_at__offset_zero.
  try simple apply start_function_aux1.
  match goal with |- semax ?D ?P ?c (frame_ret_assert (function_body_ret_assert ?t _) ?F) =>
    apply (semax_post (frame_ret_assert (function_body_ret_assert t (PROP () LOCAL () (SEP (TT)))) F))
  end.
  1,2,3: intros; simpl; normalize.
  1: intros [v|]; simpl; unfold bind_ret; simpl; normalize;
       intros x; apply andp_left2; apply sepcon_derives; [unfold_lift; apply TT_right | auto].
  abbreviate_semax.
  sep_apply (create_mem_mgr gv).
  forward. forward. forward.
  sep_apply (VS_wdict_null WDS).
  forward_call (gv, Ews, gv _x_valid_stream__sr, nullval, @None (wdict * share)).
  Intros ws.
  forward_call gv.
  Intros ds.
  destruct (eq_dec ds nullval) as [Hds|Hds].
  { subst ds. forward_if. forward. entailer!. exfalso; auto. }
  forward_if. contradiction.
  sep_apply (andp_left1 (DC gv ds dctx_init) (valid_pointer ds) (DC gv ds dctx_init) (derives_refl _)).
  simpl wdict_model in *.
  match goal with H: series_facts no_dict ws |- _ => rename H into Hsf end.
  pose proof Hsf as (Hbok & Hcok & Hn & Hcn & Hnf & _).
  assert (HN0: 0 < Zlength (ws_bytes ws)).
  { pose proof (VSP_frames_bounds _ _ Hsf) as Hfb. destruct (ws_frames ws) as [|f0 fs0]; [simpl in Hnf; lia|].
    inversion Hfb as [|? ? (A & B & C & _) _]; subst. unfold wi_end in C. lia. }
  forward.
  forward_loop
    (EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st: dctx_st,
     PROP (0 <= calls <= 4096; 0 <= ipos <= Zlength (ws_bytes ws); 0 <= got <= Zlength (ws_content ws);
           0 <= stalled <= calls;
           dc_dict st = None; dc_stable st = false; ss_err (dc_ss st) = false;
           VS_in_ok (dc_ss st) ipos (ws_bytes ws); ss_out (dc_ss st) = sublist 0 got (ws_content ws);
           0 <= ss_stall (dc_ss st) <= stalled;
           ipos < Zlength (ws_bytes ws) \/ got < Zlength (ws_content ws); VS3 st)
     LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _stalled (Vlong (Int64.repr stalled)); temp _ds ds;
            lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st; WG gv;
          data_at Ews t_wseries (wseries_val ws) (gv _x_valid_stream__sr);
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt))
  continue:
    (EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st: dctx_st,
     PROP (0 <= calls < 4096; 0 <= ipos <= Zlength (ws_bytes ws); 0 <= got <= Zlength (ws_content ws);
           0 <= stalled <= calls + 1;
           dc_dict st = None; dc_stable st = false; ss_err (dc_ss st) = false;
           VS_in_ok (dc_ss st) ipos (ws_bytes ws); ss_out (dc_ss st) = sublist 0 got (ws_content ws);
           0 <= ss_stall (dc_ss st) <= stalled;
           ipos < Zlength (ws_bytes ws) \/ got < Zlength (ws_content ws); VS3 st)
     LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _stalled (Vlong (Int64.repr stalled)); temp _ds ds;
            lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st; WG gv;
          data_at Ews t_wseries (wseries_val ws) (gv _x_valid_stream__sr);
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt))
  break:
    (EX st: dctx_st,
     PROP ()
     LOCAL (temp _ds ds; lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st; WG gv;
          data_at Ews t_wseries (wseries_val ws) (gv _x_valid_stream__sr);
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { Exists 0 0 0 0 dctx_init. entailer!. split; [|split; [simpl; lia | unfold VS3; simpl; auto]].
    unfold VS_in_ok; simpl; repeat split; try lia; apply Zlength_nonneg. }
  2: { Intros calls ipos got stalled st. forward. Exists (calls + 1) ipos got stalled st. entailer!. }
  2: { Intros st. forward_call (gv, ds, Some st). forward. cancel. }
  Intros calls ipos got stalled st.
  match goal with H: VS3 st |- _ => rename H into Hv3 end.
  match goal with H: ipos < Zlength (ws_bytes ws) \/ got < _ |- _ => rename H into Hinv end.
  forward_if.
  2: { forward. Exists st. entailer!. }
  sep_apply (VS_sr_unfold7w ws (gv _x_valid_stream__sr)). Intros.
  unfold VS_Rn. forward. fold (VS_Rn (vl (Zlength (ws_bytes ws))) (gv _x_valid_stream__sr)).
  forward_call (Zlength (ws_bytes ws) - ipos).
  Intros ilen. forward.
  forward_call (2 ^ 18).
  Intros olen0. forward.
  sep_apply (VS_bytes_borrow_w ws (gv _x_valid_stream__sr) ipos ilen); [lia..|].
  forward_call (gv, Ews, offset_val ipos (gv _x_valid_stream__sr), sublist ipos (ipos + ilen) (ws_bytes ws)).
  { entailer!. simpl. rewrite Zlength_sublist by lia. do 4 f_equal; lia. }
  { cancel. }
  { rewrite Zlength_sublist by lia. split; [rep_lia|].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  Intros ib.
  sep_apply (wand_frame_elim (@data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws))))
     (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos (gv _x_valid_stream__sr)))).
  rewrite Zlength_sublist by lia. replace (ipos + ilen - ipos) with ilen by lia.
  change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr.
  forward_call (tarray tuchar (1 + olen0), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ob.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'6 (Vint (Int.repr
        (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
  end.
  { VS_tc_null_test ib. }
  { forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
  { forward.
    { entailer!; VS_tc_null_test ob. }
    destruct (eq_dec ib nullval); [contradiction|].
    destruct (eq_dec ob nullval); entailer!;
      try reflexivity; destruct ob; try contradiction; reflexivity. }
  forward_if.
  { sep_apply (VS_free_prep Ews (tarray tuchar (Z.max 1 ilen))
      (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws)) ++ Zrepeat Vundef (Z.max 1 ilen - ilen)) ib).
    forward_call (tarray tuchar (Z.max 1 ilen), ib, gv).
    forward_call (tarray tuchar (1 + olen0), ob, gv).
    forward. sep_apply (VS_sr_fold7w ws (gv _x_valid_stream__sr)). Exists st. entailer!. }
  match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht6 end.
  change (EqDec_val ib nullval) with (eq_dec ib nullval) in Ht6.
  change (EqDec_val ob nullval) with (eq_dec ob nullval) in Ht6.
  destruct (eq_dec ib nullval) as [|Hib]; [now apply VS_repr1_neq0 in Ht6|].
  destruct (eq_dec ob nullval) as [|Hob]; [now apply VS_repr1_neq0 in Ht6|].
  clear Ht6. Intros.
  assert (Hm: (0 < ilen /\ Z.max 1 ilen = ilen) \/ (ilen = 0 /\ Z.max 1 ilen = 1)) by lia.
  set (m := Z.max 1 ilen) in *. clearbody m.
  forward. forward. forward. forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  assert (HA: Zlength (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) = ilen)
    by (rewrite Zlength_map, Zlength_sublist by lia; lia).
  rewrite <- (VS_arr Ews m _ ib).
  sep_apply (VS_ib_split ib ilen m _ HA Hm). Intros.
  rewrite <- (VS_arr_ Ews (1 + olen0) ob), <- VS_out, <- VS_in.
  rewrite (@data_at__eq ZCS).
  assert (Hbytes: bytes_ok (sublist ipos (ipos + ilen) (ws_bytes ws))).
  { unfold bytes_ok in *. apply Forall_sublist. auto. }
  assert (Hdn: dc_dict st = None) by assumption.
  rewrite (VS_DC_res DC DD gv ds st Ews Hdn (proj1 (proj2 Hv3))). do 2 try flatten_sepcon_in_SEP.
  (* both buffers are allocated: they are the API's mbuf *)
  assert_PROP (isptr ob /\ isptr ib) as Hp.
  { entailer. apply prop_right. split.
    - destruct ob; simpl in *; try contradiction; auto; elim Hob; subst; reflexivity.
    - destruct ib; simpl in *; try contradiction; auto; elim Hib; subst; reflexivity. }
  destruct Hp as [Hpo Hpi].
  rewrite <- (mbuf_isptr Ews (1 + olen0) _ ob Hpo), <- (mbuf_isptr Ews ilen _ ib Hpi).
  forward_call (VS_W ilen ib, gv, ds, st, v_out, v_in, Tsh, Tsh, Ews, ob, 1 + olen0, 0,
                @default_val ZCS (tarray tuchar (1 + olen0)), Ews, ib, ilen, 0, sublist ipos (ipos + ilen) (ws_bytes ws)).
  { split; [apply VS_buf_ok_pos; lia|]. split; [apply VS_stream_dict_ok; auto|].
    split; [apply Zlength_default_val_Tarray_tuchar; lia|].
    rewrite Zlength_sublist by lia. lia. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
  rewrite (mbuf_isptr _ _ _ ob Hpo), (mbuf_isptr _ _ _ ib Hpi).
  rewrite Hdn, (proj1 (proj2 Hv3)). change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  sep_apply (andp_left1 (DC gv ds st') (valid_pointer ds) (DC gv ds st') (derives_refl _)).
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct (VS_post _ _ _ _ _ _ _ _ _ _ _ _ _ Hdn Hv3 H) as (dl & stall' & a' & (Hop & Hip & Hoc & Hpre & Hdlen0 & Hcells &
      Ha' & Hia & Hia2 & Hr0a & Hst' & Hs1 & Hs2 & Hbm & Hstall & Hcl) & Hhost); clear H end.
  sep_apply (VS_ib_join ib ilen m (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) Hm).
  rewrite VS_out, VS_in, (VS_arr_ Ews m ib), (VS_arr Ews (1 + olen0) oc' ob).
  pose proof H8 as (Ha0 & Ha1 & Ha2).
  destruct (VSF_read (ws_bytes ws) ipos ilen (ss_ahead (dc_ss st)) ipos' a') as [Hsin Hlen']; try lia.
  rewrite Ha2, Hsin in Hst', Hcl, Hcells. rewrite H9, H6 in Hcl.
  rewrite VS_sin0 in Hcl by lia.
  assert (Hsall: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws) ++
                   sublist (ipos' + a') ilen (sublist ipos (ipos + ilen) (ws_bytes ws))) (ws_bytes ws))
    by (apply VSF_sall; lia).
  destruct (Hcells (or_intror (VS_alive ws _ Hsf (VSF_is_prefix_sublist (ws_bytes ws) (ipos + ipos' + a') ltac:(lia)))))
    as [Hdl Hbo]. clear Hcells.
  assert (Hdlen: Zlength dl = opos') by lia.
  subst opos'.
  pose proof (VSP_content ws _ _ _ _ _ _ _ _ Hsf (VSF_is_prefix_sublist (ws_bytes ws) (ipos + ipos' + a') ltac:(lia)) Hcl) as Hpre'.
  apply VSF_prefix_app in Hpre'; [|lia]. destruct Hpre' as [Hgot' Hdl'].
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite VS_ltu64_false by rep_lia. reflexivity. }
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite VS_ltu64_false by rep_lia. reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx R)))
  end.
  { forward. forward_call Int.one.
    { entailer!.
      try match goal with H: Int64.repr ilen = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
        change (Int64.unsigned Int64.zero) with 0 in H end.
      assert (Hb: Zlength dl <= ZSTD_BLOCKSIZE_MAX) by (specialize (Hbm H6 ltac:(lia)); lia).
      unfold ZSTD_BLOCKSIZE_MAX in Hb.
      change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072.
      rewrite VS_ltu64_false by rep_lia. reflexivity. }
    entailer!. }
  { forward. entailer!. }
  unfold VS_Rcn.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?R))) _ _ =>
    forward_loop (EX j: Z, PROPx ((0 <= j <= Zlength dl) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
      continue: (EX j: Z, PROPx ((0 <= j < Zlength dl) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
      break: (PROPx P (LOCALx L (SEPx R)))
  end.
  { Exists 0. entailer!. }
  { Intros j. forward. forward_if.
    2: { forward. entailer!. }
    try match goal with H: Int64.ltu _ _ = true |- _ => rewrite VS_ltu_Z in H by rep_lia; apply Z.ltb_lt in H end.
    forward.
    forward_call Int.one.
    { entailer!. try rewrite add64_repr; rewrite VS_ltu_Z by rep_lia.
      destruct (got + j <? Zlength (ws_content ws)) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia. }
    assert (Ej: Znth j oc' = Vint (Int.repr (Znth j dl))) by (apply VSF_oc with (Zlength dl); auto; lia).
    assert (Ec: Znth (got + j) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
                = Vint (Int.repr (Znth j dl))).
    { rewrite VSF_zb by lia. rewrite (VSF_dl (ws_content ws) dl got j) by (first [exact Hdl' | lia]). reflexivity. }
    assert (Hbj: 0 <= Znth j dl <= 255).
    { unfold bytes_ok in Hbo. pose proof (proj1 (Forall_Znth _ _) Hbo j ltac:(lia)) as Hb. cbv beta in Hb.
      unfold is_byte in Hb. lia. }
    forward.
    { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    remember (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) as CV eqn:ECV.
    assert (HCV: Zlength CV = 2 ^ 18) by (subst CV; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
    sep_apply (VS_content_borrow_w CV (gv _x_valid_stream__sr) (got + j) ltac:(lia) HCV).
    replace (Znth (got + j) CV) with (Vint (Int.repr (Znth j dl))) by (clear - Ec ECV; subst CV; symmetry; exact Ec).
    Intros.
    assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_stream__sr))
                   (Vlong (Int64.add (Int64.repr got) (Int64.repr j)))) =
                 field_address tuchar [] (offset_val (524296 + (got + j)) (gv _x_valid_stream__sr))).
    { entailer!. rewrite field_address_offset by auto. simpl. normalize. }
    forward.
    { entailer!. rep_lia. }
    forward_call Int.one.
    { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity).
      simpl. rewrite Int.eq_true. reflexivity. }
    sep_apply (wand_frame_elim (data_at Ews tuchar (Vint (Int.repr (Znth j dl)))
                                  (offset_val (524296 + (got + j)) (gv _x_valid_stream__sr)))).
    Exists j. clear Ec HCV. entailer!. }
  { Intros j. forward. Exists (j + 1). entailer!. }
  fold (VS_Rcn (vl (Zlength (ws_content ws))) (gv _x_valid_stream__sr)).
  forward. forward. forward. forward.
  forward_call (tarray tuchar m, ib, gv).
  { rewrite if_false by auto. cancel. }
  forward_call (tarray tuchar (1 + olen0), ob, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (1 + olen0)) oc' ob). cancel. }
  forward_call r.
  forward_if.
  { match goal with H: Int.repr (if is_error_code r then 1 else 0) <> Int.zero |- _ => rename H into Herr end.
    destruct (is_error_code r) eqn:Er; [|contradiction Herr; reflexivity]. clear Herr.
    sep_apply (VS_sr_fold7w ws (gv _x_valid_stream__sr)).
    forward_call (Ews, gv _x_valid_stream__sr, ws).
    assert (He: r = 2 ^ 64 - error_of r) by (unfold error_of; rewrite Er; lia).
    assert (Hpin: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws)) (ws_bytes ws))
      by (apply VSF_is_prefix_sublist; lia).
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX v9: int, PROPx ((v9 = Int.zero -> within_stream_b (ws_frames ws) = true /\ error_of r <> 64) :: P)
                   (LOCALx (temp _x_valid_stream__t'9 (Vint v9) :: L) (SEPx R)))
    end.
    { forward. Exists Int.one. entailer!. exfalso; apply Int.one_not_zero; assumption. }
    { forward_call r. forward.
      Exists (if Int.eq (Int.repr (error_of r)) (Int.repr 64) then Int.one else Int.zero). entailer!.
      split.
      { intro X. destruct (within_stream_b (ws_frames ws)); [|contradiction H16; reflexivity].
        split; auto. intro E. rewrite E, Int.eq_true in X. exfalso; apply Int.one_not_zero; exact X. }
      destruct (Int.eq _ _); reflexivity. }
    Intros v9.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX v11: int, PROPx ((v11 <> Int.zero) :: P)
                   (LOCALx (temp _x_valid_stream__t'11 (Vint v11) :: L) (SEPx R)))
    end.
    { forward. Exists Int.one. entailer!. }
    { match goal with H: v9 = Int.zero -> _ |- _ => rename H into Hv9 end.
      destruct (Hv9 ltac:(assumption)) as [Hws He64].
      assert (Hst: stall_error_b (error_of r) stalled ipos' ilen (Zlength dl) (1 + olen0) 0 = true).
      { apply (VSF_stall r (error_of r) (ss_stall (dc_ss st))); auto; try lia.
        destruct (VSP_err ws _ _ _ _ _ _ r Hsf H0 Hws Hpin Hsall Hcl Er (error_of r) He) as [X | X]; [contradiction | exact X]. }
      forward_call r.
      forward_call (error_of r, stalled, Tsh, v_in, ib, ilen, ipos', Tsh, v_out, ob, 1 + olen0, Zlength dl, 0).
      { unfold error_of; rewrite Er. unfold is_error_code in Er. apply Z.ltb_lt in Er. rep_lia. }
      forward. Exists Int.one. rewrite Hst. entailer!. }
    Intros v11. forward_call v11. forward.
    Exists st'. entailer!. }
  match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rename H into Herr end.
  destruct (is_error_code r) eqn:Er; [exfalso; apply VS_repr1_neq0; exact Herr|]. clear Herr.
  rewrite !add64_repr.
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'15
      (Vint (if andb (ipos' =? 0) (Zlength dl =? 0) then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!.
    match goal with H: Int64.repr ipos' = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
      change (Int64.unsigned Int64.zero) with 0 in H; subst ipos' end.
    unfold Int64.cmpu. destruct (Z.eqb_spec (Zlength dl) 0) as [E|E]; [rewrite E; reflexivity|].
    rewrite Int64.eq_false; [reflexivity|]. intro X. apply (f_equal Int64.unsigned) in X.
    rewrite !Int64.unsigned_repr in X by rep_lia. lia. }
  { forward. entailer!.
    destruct (Z.eqb_spec ipos' 0); [subst; contradiction|]. reflexivity. }
  set (b0 := andb (ipos' =? 0) (Zlength dl =? 0)).
  assert (Hst2: 0 <= stall' <= (if b0 then stalled + 1 else 0)).
  { subst b0. destruct (Z.eqb_spec ipos' 0), (Z.eqb_spec (Zlength dl) 0); simpl.
    - specialize (Hs2 eq_refl ltac:(assumption) ltac:(assumption)). lia.
    - rewrite (Hs1 eq_refl ltac:(right; assumption)). lia.
    - rewrite (Hs1 eq_refl ltac:(left; assumption)). lia.
    - rewrite (Hs1 eq_refl ltac:(left; assumption)). lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'16
      (Vlong (Int64.repr (if b0 then stalled + 1 else 0))) :: L) (SEPx R)))
  end.
  { forward. entailer!. destruct b0; [|contradiction]. try rewrite add64_repr. reflexivity. }
  { forward. entailer!. destruct b0; [discriminate|]. reflexivity. }
  forward.
  subst st'.
  match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: DC gv ds ?s :: _)))) _ _ => set (st2 := s) end.
  assert (Hcalls: calls < 4096) by (rewrite !Int64.unsigned_repr in H11 by rep_lia; lia).
  assert (Hin2: VS_in_ok (dc_ss st2) (ipos + ipos') (ws_bytes ws))
    by (subst st2; unfold VS_in_ok; simpl; split; [lia | split; [lia | reflexivity]]).
  assert (Hout2: ss_out (dc_ss st2) = sublist 0 (got + Zlength dl) (ws_content ws))
    by (subst st2; simpl; rewrite H9; apply VSF_out_app; auto; lia).
  assert (Hd2: dc_dict st2 = None /\ dc_stable st2 = false /\ ss_err (dc_ss st2) = false /\
               0 <= ss_stall (dc_ss st2) <= (if b0 then stalled + 1 else 0))
    by (subst st2; simpl; auto).
  assert (Hsl: 0 <= (if b0 then stalled + 1 else 0) <= calls + 1) by (destruct b0; lia).
  assert (Hpin: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws)) (ws_bytes ws))
    by (apply VSF_is_prefix_sublist; lia).
  assert (Hlin: Zlength (sublist 0 (ipos + ipos' + a') (ws_bytes ws)) = ipos + ipos' + a')
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hlout: Zlength (sublist 0 got (ws_content ws) ++ dl) = got + Zlength dl)
    by (rewrite Zlength_app, Zlength_sublist by lia; lia).
  assert (Hv32: VS3 st2) by (subst st2; exact Hv3).
  clearbody st2.
  forward_if.
  { match goal with H: Int64.repr r = Int64.zero |- _ =>
      apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
      change (Int64.unsigned Int64.zero) with 0 in H; subst r end.
    pose proof (VSP_zero ws _ _ _ _ _ _ _ 0 Hsf Hpin Hcl eq_refl) as Hz. rewrite Hlin, Hlout in Hz.
    rewrite (Hr0a eq_refl), Z.add_0_r in Hz.
    assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
    assert (EQ64: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
                    Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b)).
    { intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
      destruct (zeq a b); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto. }
    unfold VS_Rf, VS_Rnf.
    forward. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?R))) _ _ =>
      forward_loop (EX k: Z, PROPx ((0 <= k <= Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
           temp _at_end (Vint (Int.repr (if VSF_at (ws_frames ws) (ipos + ipos') (got + Zlength dl) k then 1 else 0))) :: L) (SEPx R)))
       continue: (EX k: Z, PROPx ((0 <= k < Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
           temp _at_end (Vint (Int.repr (if VSF_at (ws_frames ws) (ipos + ipos') (got + Zlength dl) (k + 1) then 1 else 0))) :: L) (SEPx R)))
       break: (PROPx P (LOCALx (temp _at_end (Vint (Int.repr 1)) :: L) (SEPx R)))
    end.
    { Exists 0. entailer!. }
    { Intros k. forward. forward_if.
      2: { forward. entailer!.
           try match goal with H: Int.unsigned (Int.repr k) >= _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
           replace k with (Zlength (ws_frames ws)) by lia. rewrite VSF_at_all, Hz. reflexivity. }
      try match goal with H: Int.unsigned (Int.repr k) < _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
      assert (Fk: forall d, @Znth (reptype t_winfo) d k (map winfo_val (ws_frames ws) ++
                Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) = winfo_val (Znth k (ws_frames ws))).
      { intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
      pose proof (proj1 (Forall_Znth _ _) (VSP_frames_bounds _ _ Hsf) k ltac:(lia)) as Bf. cbv beta in Bf.
      forward.
      { entailer!. rewrite Fk. exact I. }
      forward.
      { entailer!. rewrite Fk. exact I. }
      rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
      set (f := Znth k (ws_frames ws)) in *.
      unfold wi_end in Bf |- *.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'17 (Vint (if andb (wi_start f + wi_size f =? ipos + ipos')
          (got + Zlength dl =? wi_cstart f + wi_csize f) then Int.one else Int.zero)) :: L) (SEPx R)))
      end.
      { match goal with H: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H; rewrite add64_repr in H;
          apply (f_equal Int64.unsigned) in H; rewrite !Int64.unsigned_repr in H by rep_lia; rename H into Hend end.
        forward.
        { entailer!. rewrite Fk. exact I. }
        forward.
        { entailer!. rewrite Fk. exact I. }
        rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
        forward. entailer!.
        rewrite (proj2 (Z.eqb_eq _ _) Hend). simpl andb.
        unfold Int64.cmpu. rewrite EQ64 by rep_lia. unfold bool2val.
        destruct (got + Zlength dl =? wi_cstart f + wi_csize f); reflexivity. }
      { forward. entailer!.
        try match goal with H: Int64.add _ _ <> _ |- _ => rewrite add64_repr in H end.
        destruct (Z.eqb_spec (wi_start f + wi_size f) (ipos + ipos')) as [E|E]; [rewrite E in *; contradiction|].
        reflexivity. }
      forward_if.
      { forward. Exists k. entailer!.
        rewrite VSF_at_step by lia. fold f.
        unfold wi_end.
        destruct (andb (wi_start f + wi_size f =? ipos + ipos') (got + Zlength dl =? wi_cstart f + wi_csize f));
          [rewrite orb_true_r; reflexivity | exfalso; match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end]. }
      { forward. Exists k. entailer!.
        rewrite VSF_at_step by lia. fold f.
        unfold wi_end.
        destruct (andb (wi_start f + wi_size f =? ipos + ipos') (got + Zlength dl =? wi_cstart f + wi_csize f));
          [exfalso; apply Int.one_not_zero; assumption | rewrite orb_false_r; reflexivity]. } }
    { Intros k. forward. Exists (k + 1). entailer!. }
    forward_call Int.one. unfold VS_Rn. forward.
    fold (VS_Rn (vl (Zlength (ws_bytes ws))) (gv _x_valid_stream__sr)). fold (VS_Rnf (vu (Zlength (ws_frames ws))) (gv _x_valid_stream__sr)). fold (VS_Rf (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) (gv _x_valid_stream__sr)).
    sep_apply (VS_sr_fold7w ws (gv _x_valid_stream__sr)).
    forward_if.
    { forward. Exists st2. entailer!. }
    { forward. Exists calls (ipos + ipos') (got + Zlength dl) (if b0 then stalled + 1 else 0) st2.
      destruct Hd2 as (Hd2a & Hd2b & Hd2c & Hd2d). entailer!.
      match goal with H: Int64.repr (ipos + ipos') <> _ |- _ =>
        assert (ipos + ipos' <> Zlength (ws_bytes ws)) by (intro X; apply H; rewrite X; reflexivity) end.
      lia. } }
  { assert (Hr0: r <> 0) by (intro; subst r; match goal with H: Int64.repr 0 <> _ |- _ => apply H; reflexivity end).
    assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
    assert (EQ64: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
                    Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b)).
    { intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
      destruct (zeq a b); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto. }
    set (ip2 := ipos + ipos') in *. set (got2 := got + Zlength dl) in *.
    unfold VS_Rn, VS_Rf, VS_Rnf.
    forward. forward.
    match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?R))) _ _ =>
      forward_loop (EX k: Z, PROPx ((0 <= k <= Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
           temp _end (Vlong (Int64.repr (h_end (skipn (Z.to_nat k) (ws_frames ws)) ip2 got2 (Zlength (ws_bytes ws))))) :: L) (SEPx R)))
       continue: (EX k: Z, PROPx ((0 < k <= Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
           temp _end (Vlong (Int64.repr (h_end (skipn (Z.to_nat (k - 1)) (ws_frames ws)) ip2 got2 (Zlength (ws_bytes ws))))) :: L) (SEPx R)))
       break: (PROPx P (LOCALx (temp _end (Vlong (Int64.repr (h_end (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws))))) :: L) (SEPx R)))
    end.
    { Exists (Zlength (ws_frames ws)). entailer!. rewrite skipn_all2 by (rewrite <- ZtoNat_Zlength; lia). reflexivity. }
    { Intros k. forward_if.
      2: { forward. entailer!. replace k with 0 by lia. reflexivity. }
      assert (Fk: forall d, @Znth (reptype t_winfo) d (k - 1) (map winfo_val (ws_frames ws) ++
                Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) = winfo_val (Znth (k - 1) (ws_frames ws))).
      { intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
      pose proof (proj1 (Forall_Znth _ _) (VSP_frames_bounds _ _ Hsf) (k - 1) ltac:(lia)) as Bf. cbv beta in Bf.
      forward.
      { entailer!. rewrite Fk. exact I. }
      forward.
      { entailer!. rewrite Fk. exact I. }
      rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
      set (f := Znth (k - 1) (ws_frames ws)) in *.
      unfold wi_end in Bf.
      forward. rewrite add64_repr.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'18 (Vint (if orb (wi_start f + wi_size f >? ip2)
          (andb (wi_start f + wi_size f =? ip2) (got2 <? wi_cstart f + wi_csize f)) then Int.one else Int.zero)) :: L) (SEPx R)))
      end.
      { forward.
        match goal with H: ip2 < wi_start f + wi_size f |- _ => rewrite (proj2 (Z.gtb_lt _ _) H) end. entailer!. }
      { match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
          forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'18 (Vint (if orb (wi_start f + wi_size f >? ip2)
            (andb (wi_start f + wi_size f =? ip2) (got2 <? wi_cstart f + wi_csize f)) then Int.one else Int.zero)) :: L) (SEPx R)))
        end.
        { forward.
          { entailer!. rewrite Fk. exact I. }
          forward.
          { entailer!. rewrite Fk. exact I. }
          rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
          forward. forward.
          match goal with H: Int64.eq _ _ = true |- _ =>
            rewrite EQ64 in H by rep_lia; apply Z.eqb_eq in H; rename H into Hee end.
          rewrite Hee. rewrite Z.gtb_ltb, Z.ltb_irrefl, Z.eqb_refl. simpl orb; simpl andb.
          rewrite add64_repr. unfold Int64.cmpu. rewrite VS_ltu_Z by rep_lia. entailer!.
          unfold bool2val. destruct (got + Zlength dl <? wi_cstart f + wi_csize f); reflexivity. }
        { forward.
          assert (Hne: wi_start f + wi_size f <> ip2)
            by (intro X; match goal with H: Int64.repr _ <> Int64.repr _ |- _ => apply H; rewrite X; reflexivity end).
          rewrite Z.gtb_ltb. rewrite (proj2 (Z.ltb_ge ip2 (wi_start f + wi_size f))) by lia.
          rewrite (proj2 (Z.eqb_neq _ _) Hne). simpl orb. simpl andb. entailer!. } }
      forward_if.
      { forward. Exists k.
        rewrite (VSF_h_end_step (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws)) k) by lia. fold f. unfold wi_end.
        match goal with H: (if ?c then _ else _) <> Int.zero |- _ =>
          destruct c; [|exfalso; apply H; reflexivity] end.
        entailer!. }
      { forward. Exists k.
        rewrite (VSF_h_end_step (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws)) k) by lia. fold f. unfold wi_end.
        match goal with H: (if ?c then _ else _) = Int.zero |- _ =>
          destruct c; [exfalso; apply Int.one_not_zero; exact H|] end.
        entailer!. } }
    { Intros k. forward. Exists (k - 1). entailer!. }
    assert (Hhe1: ip2 <= h_end (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws))) by (apply VS_h_end_ge; unfold ip2; lia).
    assert (Hle: forall d a b l, Forall (fun f => wi_end f <= d) l -> h_end l a b d <= d).
    { clear. intros d a b l. induction l as [|g l IH]; intros FB; simpl; [lia|]. inversion FB; subst.
      destruct (_ || _)%bool; [assumption | apply IH; assumption]. }
    assert (Hhe2: h_end (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws)) <= Zlength (ws_bytes ws)).
    { apply Hle. eapply Forall_impl; [|apply (VSP_frames_bounds _ _ Hsf)]. simpl. intros g Hg.
      destruct Hg as (_ & _ & Hg & _). exact Hg. }
    assert (Hh: r <= Z.max 1 (h_end (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws)) - ip2) /\
                (ip2 < Zlength (ws_bytes ws) \/ got2 < Zlength (ws_content ws))).
    { destruct (Z.eq_dec a' 0) as [Ea | Ea].
      - subst a'. rewrite Z.add_0_r in Hcl.
        pose proof (VSP_hint ws ipos got ip2 (sublist 0 got (ws_content ws) ++ dl) _ 0 None r Hsf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      Hinv Hcl Er ltac:(lia)) as Hh.
        rewrite Hlout in Hh. split; [exact Hh|].
        destruct (Z.eq_dec ip2 (Zlength (ws_bytes ws))) as [E1|E1]; [|lia].
        destruct (Z.eq_dec got2 (Zlength (ws_content ws))) as [E2|E2]; [|lia].
        exfalso. rewrite E1, (sublist_same 0 (Zlength (ws_bytes ws)) (ws_bytes ws)) in Hcl by lia.
        exact (VSP_hint_end ws ipos got (sublist 0 got (ws_content ws) ++ dl) _ None r Hsf ltac:(lia) ltac:(lia) ltac:(lia) Hinv Hcl Er ltac:(lia)).
      - split; [|left; lia].
        rewrite (Hhost ltac:(lia) ltac:(first [exact Er | reflexivity])). apply Z.le_max_l. }
    destruct Hh as [Hh Hinv2].
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_stream__t'19 (Vlong (Int64.repr
        (Z.max 1 (h_end (ws_frames ws) ip2 got2 (Zlength (ws_bytes ws)) - ip2)))) :: L) (SEPx R)))
    end.
    { forward. entailer!.
      match goal with H: Int64.unsigned (Int64.repr 0) < _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      rewrite Z.max_r by lia. reflexivity. }
    { forward. entailer!.
      match goal with H: Int64.unsigned (Int64.repr 0) >= _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      rewrite Z.max_l by lia. reflexivity. }
    forward_call Int.one.
    { entailer!. rewrite VS_ltu64_false by rep_lia. reflexivity. }
    fold (VS_Rn (vl (Zlength (ws_bytes ws))) (gv _x_valid_stream__sr)). fold (VS_Rnf (vu (Zlength (ws_frames ws))) (gv _x_valid_stream__sr)). fold (VS_Rf (map winfo_val (ws_frames ws) ++ Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) (gv _x_valid_stream__sr)).
    sep_apply (VS_sr_fold7w ws (gv _x_valid_stream__sr)).
    Exists calls ip2 got2 (if b0 then stalled + 1 else 0) st2.
    destruct Hd2 as (Hd2a & Hd2b & Hd2c & Hd2d). entailer!. }
Qed.

Lemma VS_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma VS_G0_in DC DD WG WDS i fs : initial_world.find_id i (VS_G0 DC DD WG WDS) = Some fs ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_createDStream;
     _ZSTD_freeDStream; _ZSTD_decompressStream; _gp_assert; _exact_copy; _within_stream; _stall_error;
     _chunk; _w_series]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold G0, Imports. rewrite VS_Externals_eq.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Definition VS_fun_ids : list ident :=
  Eval lazy in map fst (G0 (Specs_api (fun _ _ _ => emp) (fun _ _ _ => emp)) (fun _ => emp) (fun _ _ => True)).

Lemma VS_G0_ids DC DD WG WDS : map fst (G0 (Specs_api DC DD) WG WDS) = VS_fun_ids.
Proof. unfold G0, Imports. rewrite VS_Externals_eq. reflexivity. Qed.

Lemma VS_vars_funs_b : forallb (fun i => negb (id_in_list i VS_fun_ids)) (map fst Vprog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VS_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma VS_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma VS_var_not_fun DC DD WG WDS i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (G0 (Specs_api DC DD) WG WDS) = None.
Proof.
  intros H. apply VS_tyc_g_nil_in in H. apply VS_find_id_not_in. rewrite VS_G0_ids.
  pose proof VS_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

(* A name that is not a function of G keeps its type of the global variables: stated for an abstract G, so that
   the rewriting never compares the concrete function list with the empty one (which unfolds the specifications). *)
Lemma VS_sub_none (V: varspecs) (G: funspecs) i :
  (forall t, Maps.PTree.get i (make_tycontext_g V nil) = Some t -> initial_world.find_id i G = None) ->
  tycontext.sub_option (Maps.PTree.get i (make_tycontext_g V nil)) (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. rewrite (VS_make_tycontext_g_find V G i).
  destruct (Maps.PTree.get i (make_tycontext_g V nil)) as [t|] eqn:EV; [|exact Logic.I].
  rewrite (H t eq_refl). reflexivity.
Qed.

Theorem main_ok3_valid_stream : MainOK.
Proof.
  intros DC DD WG WDS HWG.
  eapply semax_body_subsumption; [apply (VS_body DC DD WG WDS HWG) |].
  apply tycontext_sub_i99. split; intro i.
  + rewrite (VS_make_tycontext_g_find Vprog (VS_G0 DC DD WG WDS) i).
    destruct (initial_world.find_id i (VS_G0 DC DD WG WDS)) as [fs|] eqn:E.
    * rewrite (VS_make_tycontext_g_find Vprog (G0 (Specs_api DC DD) WG WDS) i).
      rewrite (VS_G0_in DC DD WG WDS i fs E). apply sub_option_refl.
    * apply VS_sub_none. intros t EV. exact (VS_var_not_fun DC DD WG WDS i t EV).
  + rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i (VS_G0 DC DD WG WDS)) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (VS_G0_in DC DD WG WDS i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

