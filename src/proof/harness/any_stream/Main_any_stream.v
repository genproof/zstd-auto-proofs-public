(* The harness obligation of harness/any_stream.c under the decoder's API v3:
   for ANY predicates DC, DD of the decoder's API (Spec_api6), specifications of the harness's helpers such that
   every helper and main satisfy them. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_stream.HOK_any_stream.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.any_stream.HOK_any_stream.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

(* The change_composite_env instance of any two compspecs, without computing it. *)
Definition AS_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma AS_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (AS_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma AS_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (AS_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma AS_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (AS_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma AS_Externals_eq : Externals = [nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma AS_api_ids DC DD : map fst (Specs_api DC DD) =
  [_ZSTD_isError; _ZSTD_getErrorCode; _ZSTD_decompress; _ZSTD_decompressDCtx; _ZSTD_decompress_usingDict;
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
   _ZSTD_createDCtx_advancedP; _ZSTD_estimateDCtxSize; _ZSTD_estimateDStreamSize].
Proof. reflexivity. Qed.

(* main's calls: malloc/free, the decoder's stream API, the environment *)
Definition AS_G0 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_createDStream_spec DC; ZSTD_freeDStream_spec DC;
   ZSTD_DCtx_reset_spec DC; ZSTD_initDStream_spec DC; ZSTD_DStreamOutSize_spec;
   ZSTD_decompressStream_spec DC DD;
   nondet_u32_spec; nondet_size_spec; @nondet_bytes_nn_spec HCS; gp_assert_spec; gp_assume_spec].

Lemma AS_tyc_g_isSome: forall (V: varspecs) G i, In i (map fst V) ->
  isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros. unfold make_tycontext_g. induction G as [|[j f] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); simpl; auto.
    apply IHV. destruct H; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); simpl; auto.
Qed.

Lemma AS_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma AS_chunk_in u : 0 <= u <= Int.max_unsigned ->
  Int.unsigned (Int.modu (Int.repr u) (Int.add (Int.repr 256) (Int.repr 1))) = u mod 257.
Proof.
  intros. change (Int.add (Int.repr 256) (Int.repr 1)) with (Int.repr 257).
  pose proof (Z.mod_pos_bound u 257 ltac:(lia)).
  unfold Int.modu. rewrite (Int.unsigned_repr u) by rep_lia.
  rewrite (Int.unsigned_repr 257) by rep_lia. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma AS_chunk_out u : 0 <= u <= Int.max_unsigned ->
  Int.unsigned (Int.add (Int.modu (Int.repr u) (Int.repr 256)) (Int.repr 1)) = u mod 256 + 1.
Proof.
  intros. pose proof (Z.mod_pos_bound u 256 ltac:(lia)).
  unfold Int.modu, Int.add.
  rewrite (Int.unsigned_repr u) by rep_lia.
  rewrite (Int.unsigned_repr 256) by rep_lia.
  rewrite (Int.unsigned_repr (u mod 256)) by rep_lia.
  rewrite (Int.unsigned_repr 1) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Ltac AS_tc_null_test p :=
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

Lemma AS_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

Lemma AS_S_byte: forall bs k, Forall (fun b => 0 <= b <= Byte.max_unsigned) bs -> 0 <= k < Zlength bs ->
  is_int I8 Unsigned (Znth k (map (fun b => Vint (Int.repr b)) bs)).
Proof.
  intros. rewrite Znth_map by lia.
  pose proof (proj1 (Forall_Znth _ _) H k H0). simpl.
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

Lemma AS_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (AS_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

(* the witnesses lent to ZSTD_decompressStream: the unused byte of ib = malloc(1) when ilen = 0 *)
Definition AS_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma AS_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
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

Lemma AS_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma AS_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  !!(buf_ok (AS_W il ib) Ews il ib) && (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (AS_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold AS_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply AS_buf_ok_pos; lia | apply derives_refl].
  - apply Zlength_nil_inv in HA. subst A. unfold AS_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply AS_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef]. change (Zrepeat Vundef 1) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma AS_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (AS_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold AS_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold AS_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

Lemma AS_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

(* a stream without dictionary or DDict set: the dictionary resources of ZSTD_decompressStream are emp *)
Lemma AS_DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh : dc_dict st = None -> dc_set st = nil ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma AS_stream_dict_ok W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

Lemma AS_body_main (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) : semax_body Vprog (AS_G0 DC DD) f_main main_spec.
Proof.
unfold main_spec, QPmain_spec_ext', NDmk_funspec.
split3; [reflexivity | reflexivity |].
intros Espec DTL gv.
simpl fn_body; simpl fn_params; simpl fn_return.
change (map fst []) with (@nil ident).
eapply (main_pre_InitGpred (sepcon (Zstd.proof.zstd.Globals.zstd_globals gv) TT) _ _ _
          Zstd.contracts.x_any_stream.whole_prog).
4: idtac.
- intros. eapply derives_trans.
  + apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_any_stream.whole_prog); [|exact H].
    unfold Zstd.proof.top.MainPre6.all_progs. do 4 right; left; reflexivity.
  + cancel.
- reflexivity.
- apply Forall_forall; intros [i g] Hin; simpl fst.
  apply AS_tyc_g_isSome. unfold Vprog, QPvarspecs. rewrite map_map.
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
  forward_call tt. Intros n.
  forward. forward.
  forward_call (if Int64.ltu (Int64.repr 4096) (Int64.repr n) then Int.zero else Int.one).
  { entailer!. simpl. destruct (Int64.ltu _ _); reflexivity. }
  Intros. match goal with H: (if _ then _ else _) <> _ |- _ => rename H into Ha end.
  assert (Hn: n <= 4096).
  { destruct (Int64.ltu (Int64.repr 4096) (Int64.repr n)) eqn:E; [exfalso; apply Ha; reflexivity|].
    rewrite AS_ltu_Z in E by rep_lia. apply Z.ltb_ge in E. lia. }
  clear Ha.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros src.
  destruct (eq_dec src nullval) as [Hsrc|Hsrc].
  { subst src. forward_if. forward. entailer!. exfalso. auto. }
  Intros. forward_if. contradiction.
  forward_call (src, n, Ews).
  Intros bs.
  forward_call tt.
  Intros cap.
  forward_call (if Int64.ltu (Int64.repr 65536) (Int64.repr cap) then Int.zero else Int.one).
  { entailer!. simpl. destruct (Int64.ltu _ _); reflexivity. }
  Intros. match goal with H: (if _ then _ else _) <> _ |- _ => rename H into Ha end.
  assert (Hcap: cap <= 65536).
  { destruct (Int64.ltu (Int64.repr 65536) (Int64.repr cap)) eqn:E; [exfalso; apply Ha; reflexivity|].
    rewrite AS_ltu_Z in E by rep_lia. apply Z.ltb_ge in E. lia. }
  clear Ha.
  forward_call tt.
  forward_call Int.one.
  forward_call gv.
  Intros ds.
  destruct (eq_dec ds nullval) as [Hds|Hds].
  { subst ds. forward_if.
    - forward_call (tarray tuchar n, src, gv).
      { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes bs) src). cancel. }
      forward. entailer!.
    - exfalso; auto. }
  forward_if. contradiction.
  sep_apply (andp_left1 (DC gv ds dctx_init) (valid_pointer ds) (DC gv ds dctx_init) (derives_refl _)).
  forward.
  forward_loop
    (EX calls: Z, EX got: Z, EX ipos: Z, EX st: dctx_st,
     PROP (0 <= calls <= 512; 0 <= ipos <= n; 0 <= got <= cap + 256;
           dc_dict st = None; dc_set st = nil; dc_bl st = None; dc_stable st = false; ss_err (dc_ss st) = false)
     LOCAL (temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _ds ds; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st;
          data_at Ews (tarray tuchar n) (zbytes bs) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt))
  continue:
    (EX calls: Z, EX got: Z, EX ipos: Z, EX st: dctx_st,
     PROP (0 <= calls < 512; 0 <= ipos <= n; 0 <= got <= cap + 256;
           dc_dict st = None; dc_set st = nil; dc_bl st = None; dc_stable st = false; ss_err (dc_ss st) = false)
     LOCAL (temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _ds ds; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st;
          data_at Ews (tarray tuchar n) (zbytes bs) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt))
  break:
    (EX st: dctx_st,
     PROP ()
     LOCAL (temp _ds ds; temp _src src; lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st;
          data_at Ews (tarray tuchar n) (zbytes bs) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { Exists 0 0 0 dctx_init. entailer!. }
  2: { Intros calls got ipos st. forward. Exists (calls + 1) got ipos st. entailer!. }
  2: { Intros st. forward_call (gv, ds, Some st). forward_call (gv, nullval, @None dctx_st). cancel.
       forward_call (tarray tuchar n, src, gv).
       { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes bs) src). cancel. }
       forward. cancel. }
  Intros calls got ipos st.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((b = true -> calls < 512 /\ got <= cap) :: P)
                 (LOCALx (temp _t'6 (Vint (if b then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { forward. Exists (negb (Int64.ltu (Int64.repr cap) (Int64.repr got))). entailer!.
    split.
    { rewrite AS_ltu_Z by rep_lia. intro E. destruct (cap <? got) eqn:E2; simpl in E; [discriminate|].
      apply Z.ltb_ge in E2. lia. }
    unfold Int64.cmpu. destruct (Int64.ltu _ _); reflexivity. }
  { forward. Exists false. entailer!. }
  Intros b. forward_if.
  2: { forward. Exists st. entailer!. }
  destruct b; [|exfalso; apply H14; reflexivity].
  destruct (H13 eq_refl) as [Hcalls Hgot]. clear H13 H14.
  forward_call tt. Intros u1. forward.
  forward_call tt. Intros u2. forward.
  rewrite (AS_chunk_in u1), (AS_chunk_out u2) by lia.
  pose proof (Z.mod_pos_bound u1 257 ltac:(lia)). pose proof (Z.mod_pos_bound u2 256 ltac:(lia)).
  set (a1 := u1 mod 257) in *. set (ol := u2 mod 256 + 1).
  assert (Ha1: 0 <= a1 <= 256) by (subst a1; lia). assert (Hol: 1 <= ol <= 256) by (subst ol; lia).
  clearbody a1 ol.
  forward_if
    (PROP ()
     LOCAL (temp _ilen (Vlong (Int64.repr (Z.min a1 (n - ipos)))); temp _olen (Vlong (Int64.repr ol));
            temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _ds ds; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st;
          data_at Ews (tarray tuchar n) (zbytes bs) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { forward. entailer!.
    match goal with H: Int64.ltu _ _ = true |- _ => try rewrite sub64_repr in H; rewrite AS_ltu_Z in H by rep_lia; apply Z.ltb_lt in H end.
    rewrite Z.min_r by lia. reflexivity. }
  { forward. entailer!.
    match goal with H: Int64.ltu _ _ = false |- _ => try rewrite sub64_repr in H; rewrite AS_ltu_Z in H by rep_lia; apply Z.ltb_ge in H end.
    rewrite Z.min_l by lia. reflexivity. }
  assert (Hil: 0 <= Z.min a1 (n - ipos) <= 256 /\ Z.min a1 (n - ipos) <= n - ipos) by lia.
  set (il := Z.min a1 (n - ipos)) in *. clearbody il. destruct Hil as [Hil1 Hil2].
  forward_if
    (PROP ()
     LOCAL (temp _t'9 (Vlong (Int64.repr (Z.max 1 il)));
            temp _ilen (Vlong (Int64.repr il)); temp _olen (Vlong (Int64.repr ol));
            temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _ds ds; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv ds st;
          data_at Ews (tarray tuchar n) (zbytes bs) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { forward. entailer!.
    match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    rewrite Z.max_r by lia. reflexivity. }
  { forward. entailer!.
    match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    replace il with 0 by lia. reflexivity. }
  forward_call (tarray tuchar (Z.max 1 il), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ib. forward.
  forward_call (tarray tuchar ol, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ob.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'12 (Vint (Int.repr
        (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
  end.
  { AS_tc_null_test ib. }
  { forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
  { forward.
    { entailer!; AS_tc_null_test ob. }
    destruct (eq_dec ib nullval); [contradiction|].
    destruct (eq_dec ob nullval); entailer!;
      try reflexivity; destruct ob; try contradiction; reflexivity. }
  forward_if.
  { forward_call (tarray tuchar (Z.max 1 il), ib, gv).
    forward_call (tarray tuchar ol, ob, gv).
    forward. Exists st. entailer!. }
  match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht12 end.
  change (EqDec_val ib nullval) with (eq_dec ib nullval) in Ht12.
  change (EqDec_val ob nullval) with (eq_dec ob nullval) in Ht12.
  destruct (eq_dec ib nullval) as [|Hib]; [now apply AS_repr1_neq0 in Ht12|].
  destruct (eq_dec ob nullval) as [|Hob]; [now apply AS_repr1_neq0 in Ht12|].
  clear Ht12. Intros.
  try rewrite (if_false (ib = nullval)) by auto. try rewrite (if_false (ob = nullval)) by auto.
  Intros.
  assert (Hm: (0 < il /\ Z.max 1 il = il) \/ (il = 0 /\ Z.max 1 il = 1)) by lia.
  set (m := Z.max 1 il) in *. clearbody m.
  forward.
  forward_loop
    (EX i: Z,
     PROP (0 <= i <= il)
     LOCAL (temp _j (Vlong (Int64.repr i)); temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il));
            temp _olen (Vlong (Int64.repr ol)); temp _calls (Vint (Int.repr calls));
            temp _ipos (Vlong (Int64.repr ipos)); temp _got (Vlong (Int64.repr got));
            temp _ds ds; temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _n (Vlong (Int64.repr n));
            lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
          malloc_token Ews (tarray tuchar m) ib;
          data_at Ews (tarray tuchar m) (sublist ipos (ipos + i) (zbytes bs) ++ Zrepeat Vundef (m - i)) ib;
          zstd_globals gv; DC gv ds st; data_at Ews (tarray tuchar n) (zbytes bs) src;
          malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
          TT; has_ext tt))
  continue:
    (EX i: Z,
     PROP (0 <= i < il)
     LOCAL (temp _j (Vlong (Int64.repr i)); temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il));
            temp _olen (Vlong (Int64.repr ol)); temp _calls (Vint (Int.repr calls));
            temp _ipos (Vlong (Int64.repr ipos)); temp _got (Vlong (Int64.repr got));
            temp _ds ds; temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _n (Vlong (Int64.repr n));
            lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
          malloc_token Ews (tarray tuchar m) ib;
          data_at Ews (tarray tuchar m) (sublist ipos (ipos + (i + 1)) (zbytes bs) ++ Zrepeat Vundef (m - (i + 1))) ib;
          zstd_globals gv; DC gv ds st; data_at Ews (tarray tuchar n) (zbytes bs) src;
          malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
          TT; has_ext tt))
  break:
    (PROP ()
     LOCAL (temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il));
            temp _olen (Vlong (Int64.repr ol)); temp _calls (Vint (Int.repr calls));
            temp _ipos (Vlong (Int64.repr ipos)); temp _got (Vlong (Int64.repr got));
            temp _ds ds; temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _n (Vlong (Int64.repr n));
            lvar _out tout v_out; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
          malloc_token Ews (tarray tuchar m) ib;
          data_at Ews (tarray tuchar m) (sublist ipos (ipos + il) (zbytes bs) ++ Zrepeat Vundef (m - il)) ib;
          zstd_globals gv; DC gv ds st; data_at Ews (tarray tuchar n) (zbytes bs) src;
          malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
          TT; has_ext tt)).
  { Exists 0. entailer!. rewrite sublist_nil, app_nil_l. cancel. }
  { Intros i. forward_if.
    2: { forward. entailer!. replace i with il by lia. cancel. }
    forward.
    { entailer!.
      match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) bs |- _ =>
        pose proof (proj1 (Forall_Znth _ _) Hf (ipos + i) ltac:(lia)) as Hb end.
      cbv beta in Hb. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    forward.
    Exists i. entailer!.
    match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) bs |- _ =>
      pose proof (proj1 (Forall_Znth _ _) Hf (ipos + i) ltac:(lia)) as Hb end.
    cbv beta in Hb.
    try rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
    replace (Vint (Int.repr (Znth (ipos + i) bs))) with (Znth (ipos + i) (zbytes bs))
      by (rewrite Znth_map by lia; reflexivity).
    replace (upd_Znth i (sublist ipos (ipos + i) (zbytes bs) ++ Zrepeat Vundef (m - i)) (Znth (ipos + i) (zbytes bs)))
      with (sublist ipos (ipos + (i + 1)) (zbytes bs) ++ Zrepeat Vundef (m - (i + 1))); [cancel|].
    list_solve. }
  { Intros i. forward. Exists (i + 1). entailer!. }
  forward. forward. forward. forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  replace (sublist ipos (ipos + il) (zbytes bs)) with (zbytes (sublist ipos (ipos + il) bs))
    by (rewrite sublist_map; auto).
  assert (HA: Zlength (zbytes (sublist ipos (ipos + il) bs)) = il)
    by (rewrite Zlength_map, Zlength_sublist by lia; lia).
  rewrite <- (AS_arr Ews m _ ib).
  sep_apply (AS_ib_split ib il m _ HA Hm). Intros.
  rewrite <- (AS_arr_ Ews ol ob), <- AS_out, <- AS_in.
  rewrite (@data_at__eq ZCS).
  assert (Hbytes: bytes_ok (sublist ipos (ipos + il) bs)).
  { unfold bytes_ok, is_byte. apply Forall_sublist. eapply Forall_impl; [|eassumption]. intros; simpl in *; rep_lia. }
  match goal with Hd: dc_dict st = None, Hs: dc_set st = nil |- _ =>
    rewrite (AS_DC_res DC DD gv ds st Ews Hd Hs) end. do 2 try flatten_sepcon_in_SEP.
  assert_PROP (isptr ib /\ isptr ob) as Pio.
  { entailer!. match goal with A: field_compatible _ _ ib, B: field_compatible _ _ ob |- _ =>
      split; [apply (proj1 A) | apply (proj1 B)] end. }
  destruct Pio as [Pib Pob].
  sep_apply (data_at_mbuf Ews il (zbytes (sublist ipos (ipos + il) bs)) ib).
  sep_apply (data_at_mbuf Ews ol (@default_val ZCS (tarray tuchar ol)) ob).
  forward_call (AS_W il ib, gv, ds, st, v_out, v_in, Tsh, Tsh, Ews, ob, ol, 0,
                @default_val ZCS (tarray tuchar ol), Ews, ib, il, 0, sublist ipos (ipos + il) bs).
  { split; [apply AS_buf_ok_pos; lia|]. split; [apply AS_stream_dict_ok; auto|].
    split; [apply Zlength_default_val_Tarray_tuchar; lia|].
    rewrite Zlength_sublist by lia. lia. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
  rewrite !mbuf_isptr by auto.
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor & Hr0 & Hst' & Hs1 & Hs2 & Hbm & Hstall & Hcl & _) end.
  sep_apply (andp_left1 (DC gv ds st') (valid_pointer ds) (DC gv ds st') (derives_refl _)).
  match goal with Hd: dc_dict st = None, Hs: dc_set st = nil |- _ =>
    rewrite Hd, Hs; change (dict_res DD gv Ews None) with emp; change (set_res DD gv Ews nil None) with emp end.
  sep_apply (AS_ib_join ib il m (zbytes (sublist ipos (ipos + il) bs)) Hm).
  rewrite AS_out, AS_in, (AS_arr_ Ews m ib), (AS_arr Ews ol oc' ob).
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite AS_ltu64_false by rep_lia. reflexivity. }
  forward. forward.
  forward_call Int.one.
  { entailer!. rewrite AS_ltu64_false by rep_lia. reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx R)))
  end.
  { forward. forward_call Int.one.
    { entailer!.
      match goal with H: Int64.repr il = Int64.zero |- _ =>
        apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
        change (Int64.unsigned Int64.zero) with 0 in H end.
      assert (Hb: opos' <= ZSTD_BLOCKSIZE_MAX) by (specialize (Hbm ltac:(assumption) ltac:(lia)); lia).
      unfold ZSTD_BLOCKSIZE_MAX in Hb.
      change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072.
      rewrite AS_ltu64_false by rep_lia. reflexivity. }
    entailer!. }
  { forward. entailer!. }
  forward. forward. forward. forward.
  forward_call (tarray tuchar m, ib, gv).
  { rewrite if_false by auto. cancel. }
  forward_call (tarray tuchar ol, ob, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar ol) oc' ob). cancel. }
  forward_call r.
  subst st'.
  match goal with |- context [DC gv ds (set_last (set_ss st ?x) _)] => set (s2 := x) end.
  set (st2 := set_last (set_ss st s2) (Some stream_mark)).
  forward_if.
  { forward_call tt. Intros u3.
    forward_if.
    { forward_call (gv, ds, st2, ZSTD_reset_session_only).
      Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
      match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [-> ->]; clear H end.
      Exists calls (got + opos') (ipos + ipos') (set_ex (set_ss st2 ss_init) false). subst st2 s2. entailer!. }
    { forward_call (gv, ds, st2).
      Exists calls (got + opos') (ipos + ipos') (set_ex (set_ss (set_dict st2 None) ss_init) false).
      subst st2 s2. entailer!. } }
  match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rename H into Herr end.
  destruct (is_error_code r) eqn:Er; [discriminate|]. clear Herr.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX v: int, PROPx P (LOCALx (temp _t'15 (Vint v) :: L) (SEPx R)))
  end.
  { forward_if.
    { forward. Exists Int.one. entailer!. }
    { forward. forward.
      Exists (if Int64.cmpu Ceq (Int64.repr il) (Int64.repr 0) then Int.one else Int.zero). entailer!.
      destruct (Int64.cmpu _ _ _); reflexivity. } }
  { forward. Exists Int.zero. entailer!. }
  Intros v15.
  forward_if.
  { forward. Exists st2. subst st2 s2. entailer!. }
  { forward. Exists calls (got + opos') (ipos + ipos') st2. subst st2 s2. entailer!. }
Qed.

Lemma AS_make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma AS_G0_in_Gprog DC DD i fs : initial_world.find_id i (AS_G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
Proof.
  intros Hi.
  assert (Hin: In i [_quickproof_malloc; _quickproof_free; _ZSTD_isError; _ZSTD_createDStream; _ZSTD_freeDStream;
     _ZSTD_DCtx_reset; _ZSTD_initDStream; _ZSTD_DStreamOutSize; _ZSTD_decompressStream;
     _nondet_u32; _nondet_size; _nondet_bytes; _gp_assert; _gp_assume]).
  { apply initial_world.find_id_e in Hi. apply (in_map fst) in Hi. exact Hi. }
  unfold Gprog, Imports. rewrite AS_Externals_eq.
  repeat destruct Hin as [<-|Hin]; try contradiction; rewrite <- Hi; reflexivity.
Qed.

Definition AS_fun_ids : list ident :=
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
   _nondet_u32; _nondet_size; _nondet_bytes; _gp_assert; _gp_assume; _main].

Lemma AS_Gprog_ids DC DD : map fst (Gprog (Specs_api DC DD) []) = AS_fun_ids.
Proof. unfold Gprog. rewrite AS_Externals_eq. reflexivity. Qed.

Lemma AS_vars_funs_b : forallb (fun i => negb (id_in_list i AS_fun_ids)) (map fst Vprog) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma AS_find_id_not_in {A} i (l: list (ident * A)) : ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j x] l IH]; simpl; intros H; auto.
  rewrite if_false by (intro; subst; tauto). apply IH; tauto.
Qed.

Lemma AS_tyc_g_nil_in (V: varspecs) i t : Maps.PTree.get i (make_tycontext_g V nil) = Some t -> In i (map fst V).
Proof.
  unfold make_tycontext_g. simpl. induction V as [|[k u] V IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); auto.
Qed.

Lemma AS_var_not_fun DC DD i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = None.
Proof.
  intros H. apply AS_tyc_g_nil_in in H. apply AS_find_id_not_in. rewrite AS_Gprog_ids.
  pose proof AS_vars_funs_b as B. rewrite forallb_forall in B. specialize (B i H).
  intro Hin. apply Zstd.proof.top.MainPre6.MP_id_in_list_true_i in Hin. rewrite Hin in B. discriminate.
Qed.

(* API v3.2: the proof uses no streaming claim (stream_claims_m / stream_alive_m under dmode_w), so it is
   unchanged from v3; ApiBridge.stream_claims_v3_dflt gives the v2 forms if ever needed. *)
Theorem any_stream_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (AS_body_main DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (AS_make_tycontext_g_find Vprog (AS_G0 DC DD) i).
      destruct (initial_world.find_id i (AS_G0 DC DD)) as [fs|] eqn:E.
      * remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (AS_make_tycontext_g_find Vprog GP i). subst GP.
        rewrite (AS_G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (AS_make_tycontext_g_find Vprog GP i). subst GP.
        destruct (Maps.PTree.get i (make_tycontext_g Vprog [])) as [t|] eqn:EV; [|exact Logic.I].
        rewrite (AS_var_not_fun DC DD i t EV). reflexivity.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (AS_G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (AS_G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
