(* The harness obligation of api_untouched_output (harness/api_untouched_output.c): for ANY predicates DC, DD of
   the decoder's API (Spec_api6), the helpers of laws_common.h (upto, any_bytes, copy_of, bytes_eq, proved once in
   the frames kit) and main satisfy their specifications.

   main's loop keeps one stream without dictionary in buffered mode and without a pending error (an error is
   followed by ZSTD_DCtx_reset, which gives a new stream).  Each call's check: the output cells before the
   position given are unchanged (stream_post: sublist 0 opos oc' = sublist 0 opos oc), and after a call that
   returns no error the cells after the returned position are unchanged (stream_untouched).  The buffers have
   any size up to PTRDIFF_MAX: the streaming specification with sizes up to 2 ^ 63 - 1. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_untouched_output.HOK_api_untouched_output.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

Local Notation ZCS := Zstd.units.Zstd.CS.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Lemma make_tycontext_g_isSome (V: varspecs) (G: funspecs) i :
  In i (map fst V) -> isSome (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros Hi. unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction V as [|[k t] V IHV]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact Logic.I|]. apply IHV. destruct Hi; [congruence|auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact Logic.I|]. exact IH.
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.api_untouched_output.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_untouched_output.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_untouched_output.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays, tokens and the buffer structs between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at ZCS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs ZCS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at ZCS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs ZCS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token ZCS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma tok_of_Z sh n p :
  @malloc_token ZCS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Definition cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma out_Z sh (a b c: val) p :
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at CompSpecs sh tout (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite ZCS CompSpecs (cce ZCS CompSpecs) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma in_Z sh (a b c: val) p :
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at CompSpecs sh tin (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite ZCS CompSpecs (cce ZCS CompSpecs) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

(* ---------- the buffer witnesses of a call: the malloc_tokens of its two buffers ---------- *)

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token ZCS Ews t1 p1 * @malloc_token ZCS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token ZCS Ews t1 p1 * @malloc_token ZCS Ews t2 p2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* a malloc'ed buffer (also of 0 bytes) is weakly valid at both ends, given its token *)
Lemma buf_ok_tok W sh n p : In (pw_token Ews (tarray tuchar n) p) W -> readable_share sh -> 0 <= n -> isptr p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold buf_ok.
  eapply derives_trans; [apply sepcon_derives; [apply (pws_in W _ Hin) | apply derives_refl] |].
  simpl pw_pred.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block ZCS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token ZCS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
      by (eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]).
    apply andp_right; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* a stream without dictionary or DDict set: the dictionary resources of ZSTD_decompressStream are emp *)
Lemma res_none (DD: globals -> val -> ddict_st -> mpred) gv st sh : dc_dict st = None -> dc_set st = nil ->
  emp = (dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv d st sh :
  dc_dict st = None -> dc_set st = nil ->
  DC gv d st = (DC gv d st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma stream_dict_ok_none W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

(* a byte array cut at k: [0, k) at p and [k, m) at p + k *)
Lemma split_arr {cs: compspecs} sh m k (v: list val) p : 0 <= k <= m -> Zlength v = m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) v p =
  (data_at sh (tarray tuchar k) (sublist 0 k v) p * data_at sh (tarray tuchar (m - k)) (sublist k m v) (offset_val k p))%logic.
Proof.
  intros Hk Hv Hf. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh m k v p Hk Hv).
  rewrite field_address0_offset by auto with field_compatible. simpl. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
Qed.

(* ... and cut at a and b: [0, a) at p, [a, b) at p + a, [b, m) at p + b *)
Lemma split3_arr {cs: compspecs} sh m a b (v: list val) p : 0 <= a <= b -> b <= m -> Zlength v = m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) v p =
  (data_at sh (tarray tuchar a) (sublist 0 a v) p * data_at sh (tarray tuchar (b - a)) (sublist a b v) (offset_val a p) *
   data_at sh (tarray tuchar (m - b)) (sublist b m v) (offset_val b p))%logic.
Proof.
  intros Hab Hbm Hv Hf.
  rewrite (split_arr sh m b v p) by (auto; lia).
  rewrite (split_arr sh b a (sublist 0 b v) p).
  - rewrite sublist_sublist00 by lia. rewrite sublist_sublist by lia. rewrite !Z.add_0_r. reflexivity.
  - lia.
  - rewrite Zlength_sublist by lia. lia.
  - eapply field_compatible_array_smaller0; [exact Hf | lia].
Qed.

Lemma data_at__Zrepeat {cs: compspecs} sh c p :
  data_at_ sh (tarray tuchar c) p = data_at sh (tarray tuchar c) (Zrepeat Vundef c) p.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

(* the three parts of a byte array, any contents, joined again *)
Lemma join3_ {cs: compspecs} sh m a b p : 0 <= a <= b -> b <= m -> field_compatible (tarray tuchar m) [] p ->
  (data_at_ sh (tarray tuchar a) p * data_at_ sh (tarray tuchar (b - a)) (offset_val a p) *
   data_at_ sh (tarray tuchar (m - b)) (offset_val b p))%logic |-- data_at_ sh (tarray tuchar m) p.
Proof.
  intros Hab Hbm Hf. rewrite !data_at__Zrepeat.
  rewrite (split3_arr sh m a b (Zrepeat Vundef m) p) by (rewrite ?Zlength_Zrepeat; auto; lia).
  rewrite !sublist_Zrepeat by lia. rewrite Z.sub_0_r. apply derives_refl.
Qed.

Lemma bytes_eq_refl (la: list Z) : (if list_eq_dec Z.eq_dec la la then Int.one else Int.zero) = Int.one.
Proof. destruct (list_eq_dec Z.eq_dec la la); [reflexivity | contradiction]. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.


(* ---------- buffers that malloc may return as NULL when empty ---------- *)

(* the token of a buffer lent to ZSTD_decompressStream (none for NULL) *)
Definition wtok (n: Z) (p: val) : list ptr_witness :=
  if eq_dec p nullval then [] else [pw_token Ews (tarray tuchar n) p].

Lemma pws_app_fold W1 W2 : (pws_pred W1 * pws_pred W2)%logic |-- pws_pred (W1 ++ W2).
Proof.
  unfold pws_pred. rewrite map_app. induction (map pw_pred W1) as [|a w IH]; simpl.
  - rewrite emp_sepcon. apply derives_refl.
  - rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | exact IH].
Qed.

Lemma pws_app_unfold W1 W2 : pws_pred (W1 ++ W2) |-- (pws_pred W1 * pws_pred W2)%logic.
Proof.
  unfold pws_pred. rewrite map_app. induction (map pw_pred W1) as [|a w IH]; simpl.
  - rewrite emp_sepcon. apply derives_refl.
  - rewrite sepcon_assoc. apply sepcon_derives; [apply derives_refl | exact IH].
Qed.

(* NULL is no object: buf_ok holds for it at once *)
Lemma buf_ok_null W sh n : buf_ok W sh n nullval.
Proof.
  unfold buf_ok. rewrite (@data_at__isptr ZCS). normalize.
Qed.

Lemma buf_ok_w W n p : (p <> nullval -> In (pw_token Ews (tarray tuchar n) p) W /\ isptr p) -> 0 <= n ->
  buf_ok W Ews n p.
Proof.
  intros H Hn. destruct (eq_dec p nullval) as [->|Hp]; [apply buf_ok_null |].
  destruct (H Hp). apply buf_ok_tok; auto.
Qed.

Lemma mbytes_isptr n l p : FSpecs.mbytes n l p |-- !!(p <> nullval -> isptr p).
Proof.
  unfold FSpecs.mbytes. destruct (eq_dec p nullval) as [->|Hp].
  - apply prop_right. intro; contradiction.
  - entailer!.
Qed.

Lemma mbytes_vp n l p : 0 <= n -> FSpecs.mbytes n l p |-- valid_pointer p.
Proof.
  intros Hn. unfold FSpecs.mbytes. destruct (eq_dec p nullval) as [->|Hp]; [apply valid_pointer_null |].
  destruct (zlt 0 n).
  - apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; lia].
  - apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia.
Qed.

(* the object of an input piece or of the output, lent to ZSTD_decompressStream and back *)
Lemma to_call n l p : (p = nullval -> n = 0) -> Zlength l = n ->
  FSpecs.mbytes n l p |-- (pws_pred (wtok n p) * mbuf Ews n (zbytes l) p)%logic.
Proof.
  intros Hn Hl. unfold FSpecs.mbytes, wtok, mbuf. destruct (eq_dec p nullval) as [->|Hp].
  - specialize (Hn eq_refl). subst n. apply Zlength_nil_inv in Hl. subst l.
    unfold pws_pred. simpl. rewrite emp_sepcon. apply andp_right; [apply prop_right; auto | apply derives_refl].
  - unfold pws_pred. simpl. rewrite sepcon_emp.
    apply sepcon_derives; [apply tok_to_Z | apply to_Z].
Qed.

Lemma of_call n l p : (pws_pred (wtok n p) * mbuf Ews n (zbytes l) p)%logic |-- FSpecs.mbytes n l p.
Proof.
  unfold FSpecs.mbytes, wtok, mbuf. destruct (eq_dec p nullval) as [->|Hp].
  - unfold pws_pred. simpl. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
  - unfold pws_pred. simpl. rewrite sepcon_emp.
    apply sepcon_derives; [apply tok_of_Z | apply of_Z].
Qed.

Lemma offset_nn p k : isptr p -> offset_val k p <> nullval.
Proof. intros Hp. destruct p; try contradiction. simpl. discriminate. Qed.

Lemma pws_one t p : pws_pred [pw_token Ews t p] = @malloc_token ZCS Ews t p.
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma mbytes_nn n l p : p <> nullval ->
  FSpecs.mbytes n l p = (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (zbytes l) p)%logic.
Proof. intros. unfold FSpecs.mbytes. rewrite if_false by auto. reflexivity. Qed.

(* what free(p) takes for an object of n bytes (nothing for NULL) *)
Definition ofree (n: Z) (p: val) : mpred :=
  if eq_dec p nullval then emp else (malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)%logic.

Lemma mbytes_ofree n l p : FSpecs.mbytes n l p |-- ofree n p.
Proof.
  unfold FSpecs.mbytes, ofree. destruct (eq_dec p nullval); [apply derives_refl |].
  apply sepcon_derives; [apply derives_refl | apply data_at_data_at_].
Qed.

(* the output after a call, as what free takes *)
Lemma out_ofree n c p : (pws_pred (wtok n p) * mbuf Ews n c p)%logic |-- ofree n p.
Proof.
  unfold wtok, mbuf, ofree. destruct (eq_dec p nullval).
  - unfold pws_pred. simpl. rewrite emp_sepcon. apply andp_left2. apply derives_refl.
  - unfold pws_pred. simpl. rewrite sepcon_emp. apply sepcon_derives; [apply tok_of_Z |].
    eapply derives_trans; [apply of_Z | apply data_at_data_at_].
Qed.

(* the three parts of a byte array, any contents, as what free takes *)
Lemma join3_any {cs: compspecs} sh m a b p v1 v2 v3 : 0 <= a <= b -> b <= m -> field_compatible (tarray tuchar m) [] p ->
  (data_at sh (tarray tuchar a) v1 p * data_at sh (tarray tuchar (b - a)) v2 (offset_val a p) *
   data_at sh (tarray tuchar (m - b)) v3 (offset_val b p))%logic |-- data_at_ sh (tarray tuchar m) p.
Proof.
  intros Hab Hbm Hf. eapply derives_trans; [| apply (join3_ sh m a b p Hab Hbm Hf)].
  repeat apply sepcon_derives; apply data_at_data_at_.
Qed.

(* the value of `k != 0` (k a size_t) as the bool negb (k =? 0), and what k =? 0 = true says *)
Ltac ne0_tac k :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- negb (?j =? 0) = false -> _ =>
      let E := fresh in intros E; destruct (Z.eqb_spec j 0); [| discriminate]; repeat split; auto
  | |- Vint (if negb (?j =? 0) then _ else _) = bool2val _ =>
      destruct (Z.eqb_spec j 0) as [->|?]; simpl;
      [reflexivity |
       unfold Int64.cmpu, Int64.eq; rewrite !Int64.unsigned_repr by rep_lia; rewrite zeq_false by lia; reflexivity]
  end.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_createDStream_spec DC; ZSTD_freeDStream_spec DC; ZSTD_DCtx_reset_spec DC;
   ZSTD_decompressStream_spec DC DD;
   nondet_u8_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs; @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs].

(* the stream between two calls: no dictionary, buffered mode, no pending error *)
Definition sok (st: dctx_st) : Prop :=
  dc_dict st = None /\ dc_set st = nil /\ dc_bl st = None /\ dc_stable st = false /\ ss_err (dc_ss st) = false.

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_untouched_output.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call 9223372036854775807.
  Intros n.
  forward.
  forward_call (gv, n).
  Intros vret. destruct vret as [input l]. cbn [fst snd] in *.
  forward_call gv.
  Intros zds.
  unfold FSpecs.mbytes.
  repeat apply -> seq_assoc.
  (* input or the stream NULL: the run ends *)
  destruct (eq_dec input nullval) as [Hin|Hin].
  { subst input. apply semax_if_seq. forward_if; [| contradiction]. forward.
    forward_if; [forward; cancel | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { subst zds. Intros. apply semax_if_seq. forward_if; [contradiction |]. forward.
    change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
    forward_if; [forward; cancel | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  Intros.
  assert_PROP (isptr input) as Hinp by entailer!.
  apply semax_if_seq. forward_if; [contradiction |].
  pose proof (isptr_of zds PNzds Hz) as Hzp.
  destruct zds as [| | | | | bz iz]; try contradiction. forward.
  forward_if; [discriminate |].
  set (zds := Vptr bz iz) in *.
  sep_apply (drop_vp (DC gv zds dctx_init) zds).
  forward_loop
    (EX read: Z, EX st: dctx_st,
     PROP (0 <= read <= n; sok st)
     LOCAL (temp _zds zds; temp _input input; temp _read (Vlong (Int64.repr read)); temp _n (Vlong (Int64.repr n));
            lvar _output tout v_output; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st;
          malloc_token Ews (tarray tuchar n) input; data_at Ews (tarray tuchar n) (zbytes l) input;
          data_at_ Tsh tout v_output; data_at_ Tsh tin v_in; TT; has_ext tt))
    break:
    (EX st: dctx_st,
     PROP ()
     LOCAL (temp _zds zds; lvar _output tout v_output; lvar _in tin v_in; gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st;
          data_at_ Tsh tout v_output; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { Exists 0 dctx_init. entailer!. unfold sok; simpl; auto. }
  2: { Intros st. forward_call (gv, zds, Some st). forward. cancel. }
  Intros read st.
  match goal with H: sok st |- _ => destruct H as (Hsd & Hss & Hsb & Hsst & Hse) end.
  forward_call (n - read).
  Intros take.
  forward_call 9223372036854775807.
  Intros room.
  (* the piece: input[read, read + take) *)
  assert_PROP (field_compatible (tarray tuchar n) [] input) as Hfi by entailer!.
  rewrite (split3_arr Ews n read (read + take) (zbytes l) input) by (rewrite ?Zlength_map; auto; lia).
  replace (read + take - read) with take by lia.
  replace (sublist read (read + take) (zbytes l)) with (zbytes (sublist read (read + take) l))
    by (rewrite sublist_map; reflexivity).
  Intros.
  forward_call (gv, Ews, offset_val read input, sublist read (read + take) l).
  { entailer!. rewrite Zlength_sublist by lia. replace (read + take - read) with take by lia. reflexivity. }
  { rewrite Zlength_sublist by lia. replace (read + take - read) with take by lia. cancel. }
  { apply Forall_sublist. exact H1. }
  Intros piece.
  replace (Zlength (sublist read (read + take) l)) with take by (rewrite Zlength_sublist; lia).
  sep_apply (mbytes_isptr take (sublist read (read + take) l) piece). Intros. rename H6 into Hpp.
  forward_call (gv, room).
  Intros vret. destruct vret as [out lo]. cbn [fst snd] in *.
  match goal with H: Zlength lo = room |- _ => rename H into Hlo end.
  match goal with H: bytes_ok lo |- _ => rename H into Hblo end.
  sep_apply (mbytes_isptr room lo out). Intros. rename H6 into Hop.
  (* before = out == NULL ? NULL : copy_of(out, room) *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX q: val, PROPx ((out = nullval -> q = nullval) :: P)
                             (LOCALx (temp _t'10 q :: L) (SEPx (FSpecs.mbytes room lo q :: R)))) end.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    match goal with |- context [FSpecs.mbytes ?k ?m out] => apply derives_trans with (FSpecs.mbytes k m out * TT)%logic; [cancel | apply sepcon_valid_pointer1; apply mbytes_vp; rep_lia] end. }
  { forward. Exists nullval. entailer!; unfold FSpecs.mbytes; rewrite if_true by auto; cancel. }
  { unfold FSpecs.mbytes at 1. rewrite if_false by auto. Intros.
    forward_call (gv, Ews, out, lo).
    { entailer!. }
    { rewrite Hlo. cancel. }
    Intros q. rewrite Hlo. forward. Exists q. entailer!; unfold FSpecs.mbytes; rewrite if_false by auto; cancel. }
  Intros before. forward.
  match goal with H: out = nullval -> before = nullval |- _ => rename H into Hob end.
  sep_apply (mbytes_isptr room lo before). Intros. rename H6 into Hbp.
  (* the run ends on a NULL piece of some bytes or a NULL copy of some bytes *)
  repeat apply -> seq_assoc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX b12: bool, PROPx ((b12 = false -> piece = nullval -> take = 0) :: P)
                 (LOCALx (temp _t'12 (Vint (if b12 then Int.one else Int.zero)) :: L) (SEPx R))) end.
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    match goal with |- context [FSpecs.mbytes ?k ?m piece] => apply derives_trans with (FSpecs.mbytes k m piece * TT)%logic; [cancel | apply sepcon_valid_pointer1; apply mbytes_vp; rep_lia] end. }
  { forward. Exists (negb (Z.eqb take 0)). entailer!; ne0_tac take. }
  { forward. Exists false. entailer!. }
  Intros b12.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX b13: bool, PROPx ((b13 = false -> (piece = nullval -> take = 0) /\ (before = nullval -> room = 0)) :: P)
                 (LOCALx (temp _t'13 (Vint (if b13 then Int.one else Int.zero)) :: L) (SEPx R))) end.
  { forward. Exists true. entailer!. }
  { destruct b12; [exfalso; exact (Int.one_not_zero ltac:(assumption)) |].
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX b13: bool, PROPx ((b13 = false -> (piece = nullval -> take = 0) /\ (before = nullval -> room = 0)) :: P)
                   (LOCALx (temp _t'13 (Vint (if b13 then Int.one else Int.zero)) :: L) (SEPx R))) end.
    { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      match goal with |- context [FSpecs.mbytes ?k ?m before] => apply derives_trans with (FSpecs.mbytes k m before * TT)%logic; [cancel | apply sepcon_valid_pointer1; apply mbytes_vp; rep_lia] end. }
    { forward. forward.
      match goal with |- context [temp _room (Vlong (Int64.repr ?k))] =>
        Exists (negb (Z.eqb k 0)); entailer!; ne0_tac k end. }
    { forward. Exists false. entailer!. split; [auto | intro E; subst; contradiction]. } }
  Intros b13.
  forward_if.
  { destruct b13; [| exfalso; auto]. forward. cancel. }
  destruct b13; [exfalso; exact (Int.one_not_zero ltac:(assumption)) |].
  match goal with H: false = false -> _ /\ _ |- _ => destruct (H eq_refl) as [Hpt Hbr]; clear H end.
  assert (Hor: out = nullval -> room = 0) by (intro E; apply Hbr, Hob, E).
  forward. forward. forward. forward. forward.
  forward_call room. Intros start.
  forward. forward.
  (* the call, at the decoder's compspecs; a buffer may be NULL when it is empty *)
  change (Int.signed (Int.repr 0)) with 0.
  rewrite <- out_Z, <- in_Z.
  sep_apply (to_call take (sublist read (read + take) l) piece Hpt ltac:(rewrite Zlength_sublist; lia)).
  sep_apply (to_call room lo out Hor Hlo).
  sep_apply (pws_app_fold (wtok take piece) (wtok room out)).
  rewrite (DC_res DC DD gv zds st Ews Hsd Hss). do 2 try flatten_sepcon_in_SEP.
  forward_call (wtok take piece ++ wtok room out,
                gv, zds, st, v_output, v_in, Tsh, Tsh, Ews, out, room, start, zbytes lo,
                Ews, piece, take, 0, sublist read (read + take) l).
  { split; [apply buf_ok_w; [intro Hn; split; [apply in_or_app; right; unfold wtok; rewrite if_false by auto; simpl; auto | auto] | lia] |].
    split; [apply buf_ok_w; [intro Hn; split; [apply in_or_app; left; unfold wtok; rewrite if_false by auto; simpl; auto | auto] | lia] |].
    split; [apply stream_dict_ok_none; auto |].
    split; [rewrite Zlength_map; auto |].
    split; [rewrite Zlength_sublist by lia; lia |].
    apply Forall_sublist; auto. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *.
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl & stall' & a' & Hop' & Hip' & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor' & Hr0 & Hst' & Hs1 & Hs2 & Hbm & Hstall & Hcl) end.
  match goal with H: stream_untouched _ _ _ _ _ _ |- _ => rename H into Hunt end.
  rewrite Hsd, Hss. change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  sep_apply (drop_vp (DC gv zds st') zds).
  sep_apply (pws_app_unfold (wtok take piece) (wtok room out)).
  rewrite out_Z, in_Z.
  sep_apply (of_call take (sublist read (read + take) l) piece).
  subst room.
  (* the check, made for an output space of some bytes; the output and its copy are then objects *)
  forward_if (PROP ()
    LOCAL (temp _result (Vlong (Int64.repr r)); temp _before before; temp _out out;
           temp _piece piece; temp _room (Vlong (Int64.repr (Zlength lo))); temp _take (Vlong (Int64.repr take));
           temp _zds zds; temp _input input; temp _read (Vlong (Int64.repr read)); temp _n (Vlong (Int64.repr n));
           lvar _output tout v_output; lvar _in tin v_in; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds st';
         data_at Tsh tout (out, (Vlong (Int64.repr (Zlength lo)), Vlong (Int64.repr opos'))) v_output;
         data_at Tsh tin (piece, (Vlong (Int64.repr take), Vlong (Int64.repr ipos'))) v_in;
         ofree (Zlength lo) out; ofree (Zlength lo) before; FSpecs.mbytes take (sublist read (read + take) l) piece;
         data_at Ews (tarray tuchar take) (zbytes (sublist read (read + take) l)) (offset_val read input);
         malloc_token Ews (tarray tuchar n) input;
         data_at Ews (tarray tuchar read) (sublist 0 read (zbytes l)) input;
         data_at Ews (tarray tuchar (n - (read + take))) (sublist (read + take) n (zbytes l)) (offset_val (read + take) input);
         TT; has_ext tt)).
  { (* room <> 0 *)
    assert (Hrz: Zlength lo <> 0).
    { intro E. match goal with H: Int64.repr (Zlength lo) <> Int64.repr 0 |- _ => apply H; rewrite E; reflexivity end. }
    assert (Hbn: before <> nullval) by (intro E; apply Hrz, Hbr, E).
    assert (Hon: out <> nullval) by (intro E; apply Hbn, Hob, E).
    unfold wtok, mbuf. rewrite !if_false by auto. rewrite pws_one.
    rewrite (mbytes_nn (Zlength lo) lo before Hbn).
    sep_apply (of_Z Ews (Zlength lo) oc' out).
    sep_apply (tok_of_Z Ews (Zlength lo) out).
    Intros.
    assert_PROP (field_compatible (tarray tuchar (Zlength lo)) [] out) as Hfo by entailer!.
    assert_PROP (field_compatible (tarray tuchar (Zlength lo)) [] before) as Hfb by entailer!.
    rewrite (split3_arr Ews (Zlength lo) start opos' oc' out) by (auto; lia).
    rewrite (split3_arr Ews (Zlength lo) start opos' (zbytes lo) before) by (rewrite ?Zlength_map; auto; lia).
    assert (Epre: sublist 0 start oc' = zbytes (sublist 0 start lo)) by (rewrite Hpre, sublist_map; reflexivity).
    assert (Elo: forall a b, sublist a b (zbytes lo) = zbytes (sublist a b lo)) by (intros; apply sublist_map).
    rewrite Epre, !Elo.
    forward_call (Ews, out, sublist 0 start lo, Ews, before, sublist 0 start lo).
    { entailer!. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. reflexivity. }
    { rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. cancel. }
    { repeat split; try apply Forall_sublist; auto. }
    rewrite bytes_eq_refl. rewrite Zlength_sublist, Z.sub_0_r by lia.
    (* before start always; after the returned position when no error *)
    forward_if (PROP ()
      LOCAL (temp _t'17 (Vint Int.one); temp _result (Vlong (Int64.repr r)); temp _before before; temp _out out;
             temp _piece piece; temp _room (Vlong (Int64.repr (Zlength lo))); temp _take (Vlong (Int64.repr take));
             temp _zds zds; temp _input input; temp _read (Vlong (Int64.repr read)); temp _n (Vlong (Int64.repr n));
             lvar _output tout v_output; lvar _in tin v_in; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv zds st';
           data_at Tsh tout (out, (Vlong (Int64.repr (Zlength lo)), Vlong (Int64.repr opos'))) v_output;
           data_at Tsh tin (piece, (Vlong (Int64.repr take), Vlong (Int64.repr ipos'))) v_in;
           ofree (Zlength lo) out; ofree (Zlength lo) before; FSpecs.mbytes take (sublist read (read + take) l) piece;
           data_at Ews (tarray tuchar take) (zbytes (sublist read (read + take) l)) (offset_val read input);
           malloc_token Ews (tarray tuchar n) input;
           data_at Ews (tarray tuchar read) (sublist 0 read (zbytes l)) input;
           data_at Ews (tarray tuchar (n - (read + take))) (sublist (read + take) n (zbytes l)) (offset_val (read + take) input);
           TT; has_ext tt)).
    + forward_call r.
      destruct (is_error_code r) eqn:Er.
      * forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
        sep_apply (join3_any Ews (Zlength lo) start opos' out (zbytes (sublist 0 start lo)) (sublist start opos' oc')
                     (sublist opos' (Zlength lo) oc') ltac:(lia) ltac:(lia) Hfo).
        sep_apply (join3_any Ews (Zlength lo) start opos' before (zbytes (sublist 0 start lo)) (zbytes (sublist start opos' lo))
                     (zbytes (sublist opos' (Zlength lo) lo)) ltac:(lia) ltac:(lia) Hfb).
        forward. unfold ofree. rewrite !if_false by auto. entailer!.
      * forward_if; [exfalso; auto |].
        forward. forward. forward.
        assert (Eun: sublist opos' (Zlength lo) oc' = zbytes (sublist opos' (Zlength lo) lo))
          by (rewrite (Hunt Hsst Er); apply sublist_map).
        rewrite Eun.
        forward_call (Ews, offset_val opos' out, sublist opos' (Zlength lo) lo, Ews, offset_val opos' before, sublist opos' (Zlength lo) lo).
        { entailer!. rewrite Zlength_sublist by lia. simpl. rewrite <- sub64_repr. normalize. }
        { rewrite Zlength_sublist by lia. cancel. }
        { split; apply Forall_sublist; auto. }
        rewrite bytes_eq_refl. rewrite Zlength_sublist by lia.
        sep_apply (join3_any Ews (Zlength lo) start opos' out (zbytes (sublist 0 start lo)) (sublist start opos' oc')
                     (zbytes (sublist opos' (Zlength lo) lo)) ltac:(lia) ltac:(lia) Hfo).
        sep_apply (join3_any Ews (Zlength lo) start opos' before (zbytes (sublist 0 start lo)) (zbytes (sublist start opos' lo))
                     (zbytes (sublist opos' (Zlength lo) lo)) ltac:(lia) ltac:(lia) Hfb).
        forward. forward. unfold ofree. rewrite !if_false by auto. entailer!.
    + exfalso; exact (Int.one_not_zero ltac:(assumption)).
    + forward_call Int.one. entailer!. }
  { (* room = 0: no check *)
    forward.
    sep_apply (out_ofree (Zlength lo) oc' out). sep_apply (mbytes_ofree (Zlength lo) lo before). entailer!. }
  forward. forward.
  (* free the piece, the output and its copy *)
  sep_apply (mbytes_ofree take (sublist read (read + take) l) piece).
  unfold ofree.
  forward_call (tarray tuchar take, piece, gv).
  forward_call (tarray tuchar (Zlength lo), out, gv).
  forward_call (tarray tuchar (Zlength lo), before, gv).
  (* after an error, a reset *)
  forward_call r.
  forward_if ((EX st2: dctx_st,
    PROP (sok st2)
    LOCAL (temp _zds zds; temp _input input; temp _read (Vlong (Int64.repr (read + ipos')));
           temp _n (Vlong (Int64.repr n)); lvar _output tout v_output; lvar _in tin v_in; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds st2;
         data_at Tsh tout (out, (Vlong (Int64.repr (Zlength lo)), Vlong (Int64.repr opos'))) v_output;
         data_at Tsh tin (piece, (Vlong (Int64.repr take), Vlong (Int64.repr ipos'))) v_in;
         data_at Ews (tarray tuchar take) (zbytes (sublist read (read + take) l)) (offset_val read input);
         malloc_token Ews (tarray tuchar n) input;
         data_at Ews (tarray tuchar read) (sublist 0 read (zbytes l)) input;
         data_at Ews (tarray tuchar (n - (read + take))) (sublist (read + take) n (zbytes l)) (offset_val (read + take) input);
         TT; has_ext tt))%assert).
  { forward_call (gv, zds, st', ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st2]. cbn [fst snd] in *.
    match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [_ ->] end.
    Exists (set_ex (set_ss st' ss_init) false). entailer!.
    try subst st'. unfold sok. simpl. auto. }
  { forward. Exists st'. entailer!.
    destruct (is_error_code r) eqn:Er; [discriminate |].
    try subst st'. unfold sok. simpl. try rewrite Er. auto. }
  Intros st2.
  (* do ... while (nondet_u8() != 0) *)
  forward_call tt. Intros u.
  forward_if.
  { forward. Exists (read + ipos') st2. entailer!.
    rewrite (split3_arr Ews (Zlength l) read (read + take) (zbytes l) input) by (rewrite ?Zlength_map; auto; lia).
    replace (read + take - read) with take by lia. rewrite !sublist_map. cancel. }
  { forward. Exists st2. entailer!. }
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's copy_of, any_bytes,
   upto and bytes_eq (laws_common.h) *)
Definition Hs : funspecs :=
  [@Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma find_cons {A} i (a: ident * A) l :
  initial_world.find_id i (a :: l) = if Pos.eqb i (fst a) then Some (snd a) else initial_world.find_id i l.
Proof.
  destruct a as [j x]. simpl. destruct (Memory.EqDec_ident i j) as [E|Hne].
  - subst. rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec i j); [contradiction | reflexivity].
Qed.

Ltac find_steps :=
  repeat (rewrite find_cons;
          match goal with |- context [Pos.eqb ?i (fst ?a)] =>
            let b := eval lazy in (Pos.eqb i (fst a)) in change (Pos.eqb i (fst a)) with b end;
          cbv beta iota).

Lemma Gprog_cons DC DD : Gprog (Specs_api DC DD) Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
                       @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs;
                       @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
                       Zstd.proof.harness.frames.FSpecs.upto_spec;
                       @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Specs_api. cbn [app].
  repeat destruct Hi as [E|Hi];
    try match type of E with ?a = (i, fs) =>
      replace i with (fst a) by (rewrite E; reflexivity);
      replace fs with (snd a) by (rewrite E; reflexivity) end;
    try contradiction;
    find_steps; reflexivity.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma mtg_none (V: varspecs) i : ~ In i (map fst V) -> Maps.PTree.get i (make_tycontext_g V []) = None.
Proof.
  unfold make_tycontext_g. induction V as [|[k t] V IH]; simpl; intros Hn.
  - apply Maps.PTree.gempty.
  - rewrite Maps.PTree.gsspec. destruct (peq i k); [subst; tauto |]. apply IH. tauto.
Qed.

(* no function name of Gprog is a global variable of the program *)
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (Specs_api DC DD) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (Specs_api DC DD) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem api_untouched_output_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
    + (* copy_of *)
      exists f_copy_of. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_copy_of = Zstd.proof.harness.frames.FSpecs.f_copy_of) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_copy_of).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* any_bytes *)
      exists f_any_bytes. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_any_bytes = Zstd.proof.harness.frames.FSpecs.f_any_bytes) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ (@Zstd.proof.harness.frames.FSpecs.G_any_bytes CompSpecs)).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* upto *)
      exists f_upto. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_upto = Zstd.proof.harness.frames.FSpecs.f_upto) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_upto).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* bytes_eq *)
      exists f_bytes_eq. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_bytes_eq = Zstd.proof.harness.frames.FSpecs.f_bytes_eq) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_bytes_eq).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq CompSpecs).
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
        remember (Gprog (Specs_api DC DD) Hs) as GP eqn:HGP. (* abstract while rewriting: no comparison with [] by computation *)
        rewrite (make_tycontext_g_find Vprog GP i). subst GP.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (Specs_api DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
