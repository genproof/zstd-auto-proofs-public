(* The harness of the law api_reset (harness/api_reset.c): main and the harness's helpers satisfy their
   specifications against the decoder's API (Spec_api6).

   Phase 1 (any use of `used`) needs only the relational specifications: one-shot and streaming decoding,
   ZSTD_DCtx_reset(session_only), ZSTD_DCtx_loadDictionary of any length, ZSTD_DCtx_setParameter after any
   use.  ZSTD_DCtx_reset(session_and_parameters) then puts `used` in dctx_init (reset_post 3, reset_both_init:
   the law never references a DDict), the state ZSTD_createDCtx gives `fresh`.  Phase 2 makes the same calls
   on both contexts from that one abstract state: oneshot_exact and stream_exact (Spec_api6) determine the
   results, positions, bytes and next states from the state and the arguments, so the two runs agree, up to
   a memory-allocation error, which ends the run.  The proof never unfolds os_res or zs_call
   (model/Exact.v). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_reset.HOK_api_reset.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.api_reset.HOK_api_reset.CompSpecs.
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
    (QPprog_vars Zstd.contracts.api_reset.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_reset.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_reset.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- memory between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at HCS sh (tarray tuchar n) v p |-- @data_at ZCS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ HCS sh (tarray tuchar n) p |-- @data_at_ ZCS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token HCS sh (tarray tuchar n) p |-- @malloc_token ZCS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any HCS ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Definition cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma out_Z: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma in_Z: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

(* ---------- a prefix of a byte object, and its buffer witnesses ---------- *)

(* the object of n cells at p as its first k cells and the rest *)
Lemma arr_split sh n k (v: list val) p : @field_compatible ZCS (tarray tuchar n) [] p -> 0 <= k <= n -> Zlength v = n ->
  @data_at ZCS sh (tarray tuchar n) v p =
  (@data_at ZCS sh (tarray tuchar k) (sublist 0 k v) p *
   @data_at ZCS sh (tarray tuchar (n - k)) (sublist k n v) (offset_val k p))%logic.
Proof.
  intros Hf Hk Hv. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n k) by auto.
  change (Tarray tuchar n noattr) with (tarray tuchar n). rewrite arr_field_address0; [| exact Hf | lia].
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma arr_join sh n k (v1 v2: list val) p : @field_compatible ZCS (tarray tuchar n) [] p -> 0 <= k <= n ->
  Zlength v1 = k -> Zlength v2 = n - k ->
  (@data_at ZCS sh (tarray tuchar k) v1 p * @data_at ZCS sh (tarray tuchar (n - k)) v2 (offset_val k p))%logic |--
  @data_at ZCS sh (tarray tuchar n) (v1 ++ v2) p.
Proof.
  intros Hf Hk H1 H2. rewrite (arr_split sh n k (v1 ++ v2) p Hf Hk) by (rewrite Zlength_app; lia).
  rewrite sublist0_app1 by lia. rewrite sublist_same by lia.
  rewrite sublist_app2 by lia. rewrite sublist_same by lia. replace (k - Zlength v1) with 0 by lia.
  apply derives_refl.
Qed.

Lemma pws_in W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* the first k bytes of a malloc'ed object of n bytes are weakly valid at both ends, given the rest of the
   object and its token (an empty prefix of an empty object: the token) *)
Lemma buf_ok_pre W sh n k c p :
  In (pw_bytes Ews (n - k) c (offset_val k p)) W -> In (pw_token Ews (tarray tuchar n) p) W ->
  0 <= k <= n -> isptr p -> readable_share sh -> buf_ok W sh k p.
Proof.
  intros Hb Ht Hk Hp Hsh. unfold buf_ok.
  destruct (zlt 0 k) as [Hpos|Hz].
  - rewrite (@data_at__memory_block ZCS). normalize.
    replace (sizeof (tarray tuchar k)) with k by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (k = 0) by lia. subst k. rewrite isptr_offset_val_zero by exact Hp.
    assert (Hv: pws_pred W |-- valid_pointer p).
    { destruct (zlt 0 n) as [Hn|Hn].
      - eapply derives_trans; [apply (pws_in W _ Hb) |]. simpl pw_pred.
        rewrite isptr_offset_val_zero by exact Hp.
        apply sepcon_valid_pointer1. apply data_at_valid_ptr; [apply readable_nonidentity; auto | simpl; lia].
      - eapply derives_trans; [apply (pws_in W _ Ht) |]. simpl pw_pred.
        apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. simpl. lia. }
    apply andp_right; apply sepcon_weak_valid_pointer1;
      (eapply derives_trans; [exact Hv | apply valid_pointer_weak]).
Qed.

(* the witnesses of a call: the rest and the token of the input object, then of the output object *)
Definition wits (n isz: Z) (r: list val) (src: val) (cap osz: Z) (r': list val) (dst: val) : list ptr_witness :=
  [pw_bytes Ews (n - isz) r (offset_val isz src); pw_token Ews (tarray tuchar n) src;
   pw_bytes Ews (cap - osz) r' (offset_val osz dst); pw_token Ews (tarray tuchar cap) dst].

Lemma wits_fold n isz r src cap osz r' dst :
  (@data_at ZCS Ews (tarray tuchar (n - isz)) r (offset_val isz src) *
   @malloc_token ZCS Ews (tarray tuchar n) src *
   @data_at ZCS Ews (tarray tuchar (cap - osz)) r' (offset_val osz dst) *
   @malloc_token ZCS Ews (tarray tuchar cap) dst)%logic |--
  pws_pred (wits n isz r src cap osz r' dst).
Proof. unfold pws_pred, wits. simpl. rewrite sepcon_emp, !sepcon_assoc. apply derives_refl. Qed.

Lemma wits_unfold n isz r src cap osz r' dst :
  pws_pred (wits n isz r src cap osz r' dst) |--
  (@data_at ZCS Ews (tarray tuchar (n - isz)) r (offset_val isz src) *
   @malloc_token ZCS Ews (tarray tuchar n) src *
   @data_at ZCS Ews (tarray tuchar (cap - osz)) r' (offset_val osz dst) *
   @malloc_token ZCS Ews (tarray tuchar cap) dst)%logic.
Proof. unfold pws_pred, wits. simpl. rewrite sepcon_emp, !sepcon_assoc. apply derives_refl. Qed.

(* ---------- small facts ---------- *)

Lemma ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* a stream without dictionary or DDict set: the dictionary resources of ZSTD_decompressStream are emp *)
Lemma DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh :
  dc_dict st = None -> dc_set st = nil ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma stream_dict_ok_none W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

Lemma bytes_ok_sublist (l: list Z) i j : bytes_ok l -> bytes_ok (sublist i j l).
Proof. unfold bytes_ok. apply Forall_sublist. Qed.

Lemma repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

(* the impossible branch of a test whose value is known *)
Ltac bad := first [contradiction | exfalso; eapply repr1_neq0; eassumption | discriminate |
  exfalso; apply Int.one_not_zero; assumption |
  exfalso; match goal with H: ?x <> ?x |- _ => apply H; reflexivity end].

(* an entry of the witnesses of a call *)
Ltac in_wits := unfold wits; simpl; repeat first [left; reflexivity | right].

(* ---------- one-shot buffer witnesses: the malloc_tokens of the two buffers ---------- *)

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token ZCS Ews t1 p1 * @malloc_token ZCS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token ZCS Ews t1 p1 * @malloc_token ZCS Ews t2 p2).
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws1_fold t1 p1 : @malloc_token ZCS Ews t1 p1 |-- pws_pred [pw_token Ews t1 p1].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws1_unfold t1 p1 : pws_pred [pw_token Ews t1 p1] |-- @malloc_token ZCS Ews t1 p1.
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

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

Lemma of_Z sh n v p :
  @data_at ZCS sh (tarray tuchar n) v p |-- @data_at HCS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ ZCS sh (tarray tuchar n) p |-- @data_at_ HCS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token ZCS sh (tarray tuchar n) p |-- @malloc_token HCS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any HCS ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.

(* ---------- the contexts of the first phase ---------- *)

(* the dictionary of a context of the first phase: none, or one loaded by copy (zstd's own, sticky) *)
Definition own_dict (d: option dictref) : Prop :=
  match d with None => True | Some r => dr_src r = DSOwn /\ dr_once r = false end.

(* the state of `used` between two calls of the first phase: no DDict set, no buffer-less frame, the default
   allocator, buffered output, its own dictionary or none *)
Definition p1_ok (st: dctx_st) : Prop :=
  dc_set st = nil /\ dc_bl st = None /\ dc_mem st = None /\ dc_stable st = false /\ own_dict (dc_dict st).

Lemma own_res (DD: globals -> val -> ddict_st -> mpred) gv sh d : own_dict d -> dict_res DD gv sh d = emp.
Proof. destruct d as [r|]; simpl; [intros [E _]; rewrite E |]; reflexivity. Qed.

Lemma DC_res1 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh :
  p1_ok st ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof.
  intros (Hs & _ & _ & _ & Hd). rewrite (own_res DD gv sh _ Hd), Hs. unfold set_res. simpl. rewrite !sepcon_emp.
  reflexivity.
Qed.

Lemma stream_dict_ok_p1 W st : p1_ok st -> stream_dict_ok W st.
Proof.
  intros (Hs & Hb & _ & _ & Hd). unfold stream_dict_ok. rewrite Hs, Hb. split; [| auto].
  destruct (dc_dict st) as [r|]; [| exact Logic.I]. destruct Hd as [E1 E2]. rewrite E1. auto.
Qed.

Lemma dict_buf_ok_p1 W sh st shd cap dst : p1_ok st -> dict_buf_ok W sh (dc_dict st) shd cap dst.
Proof.
  intros (_ & _ & _ & _ & Hd). unfold dict_buf_ok.
  destruct (dc_dict st) as [r|]; [| exact Logic.I]. destruct Hd as [E1 _]. rewrite E1. exact Logic.I.
Qed.

Lemma p1_set_ss st ss : p1_ok st -> p1_ok (set_ss st ss).
Proof. intros (? & ? & Hm & ? & ?). unfold p1_ok, set_ss; simpl. rewrite Hm. auto. Qed.

Lemma p1_set_last st l : p1_ok st -> p1_ok (set_last st l).
Proof. intros H. exact H. Qed.

(* p1_ok says nothing of dc_ex: a session reset or a one-shot decoding of the first phase may clear it *)
Lemma p1_set_ex st b : p1_ok st -> p1_ok (set_ex st b).
Proof. intros H. exact H. Qed.

Lemma p1_after_use st : p1_ok st -> p1_ok (after_use st).
Proof.
  intros H. unfold after_use. destruct (dc_dict st) as [r|] eqn:E; [| exact H].
  pose proof H as (_ & _ & _ & _ & Hd). rewrite E in Hd. destruct Hd as [_ Ho]. rewrite Ho. exact H.
Qed.

Lemma p1_after_decode st st' l : p1_ok st -> after_decode (after_use st) st' l -> p1_ok st'.
Proof. intros H [-> | ->]; [| apply p1_set_last]; apply p1_set_ex, p1_after_use; exact H. Qed.

Lemma ss_after_decode st st' l : after_decode (after_use st) st' l -> dc_ss st' = dc_ss st.
Proof.
  intros [-> | ->]; unfold after_use; destruct (dc_dict st) as [r|]; try destruct (dr_once r); reflexivity.
Qed.

(* ZSTD_DCtx_loadDictionary (by copy) keeps a context of the first phase in it, before a stream *)
Lemma p1_load st st' r b : p1_ok st ->
  load_result st st' r {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |} ->
  p1_ok st' /\ dc_ss st' = dc_ss st.
Proof.
  intros (? & ? & ? & ? & _) [[_ ->] | (_ & -> & _)]; unfold p1_ok, set_dict; simpl; tauto.
Qed.

(* ... as ZSTD_DCtx_loadDictionary's postcondition states it, for a context in any streaming state with any
   allocator: before a stream and with the default allocator, it is the case above *)
Lemma p1_load_stage st st' r b : p1_ok st -> dc_ss st = ss_init ->
  after_stage (fun st0 r0 st1 => exists om, cm_raised (dc_mem st0) om /\
    load_result (set_mem st0 om) st1 r0 {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |})
    st r st' ->
  p1_ok st' /\ dc_ss st' = ss_init.
Proof.
  intros H Hs Ha. apply after_stage_init in Ha; [| exact Hs]. destruct Ha as [om [Hc Hl]].
  pose proof H as (_ & _ & Hm & _). rewrite Hm in Hc. destruct om as [m|]; [destruct Hc |].
  assert (H': p1_ok (set_mem st None)) by (destruct H as (? & ? & _ & ? & ?); unfold p1_ok, set_mem; simpl; auto).
  destruct (p1_load _ _ _ _ H' Hl) as [P E]. split; [exact P |]. rewrite E. exact Hs.
Qed.

(* ZSTD_DCtx_setParameter(ZSTD_d_windowLogMax, v) before a stream: the parameters change or nothing does *)
Lemma p1_setpar st st' r v : p1_ok st -> dc_ss st = ss_init ->
  after_stage (setpar_res ZSTD_d_windowLogMax v) st r st' -> p1_ok st' /\ dc_ss st' = ss_init.
Proof.
  intros H Hs Ha. apply after_stage_init in Ha; [| exact Hs]. unfold setpar_res in Ha. simpl in Ha.
  destruct (param_set (dc_par st) ZSTD_d_windowLogMax v) as [p'|].
  - destruct Ha as [_ ->]. exact (conj H Hs).
  - destruct Ha as [_ ->]. exact (conj H Hs).
Qed.

Lemma p1_init : p1_ok dctx_init.
Proof. unfold p1_ok; simpl; auto. Qed.

(* ---------- small facts of the second phase ---------- *)

(* a new context has no dictionary resources *)
Lemma res_none_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_none_e DD0 gv sh :
  dict_res DD0 gv sh (dc_dict dctx_init) * set_res DD0 gv sh (dc_set dctx_init) (dc_dict dctx_init) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

(* the state of a new context is in the configuration of oneshot_exact / stream_exact *)
Lemma fresh_init : fresh_cfg dctx_init.
Proof. unfold fresh_cfg; simpl; auto. Qed.

(* a stream call from the configuration of a new context keeps it (set_last, set_ss change neither the dictionary,
   the parameters, the DDict set nor the output mode) *)
Lemma fresh_after st ss l : fresh_cfg st -> fresh_cfg (set_last (set_ss st ss) l).
Proof. unfold fresh_cfg, set_last, set_ss; simpl. tauto. Qed.

(* the two contexts of phase 2 have one abstract state but for zstd's noForwardProgress count (ss_stall), which
   stream_exact leaves open: the state st with the stall count z *)
Definition with_stall (st: dctx_st) (z: Z) : dctx_st :=
  {| dc_dict := dc_dict st; dc_stable := dc_stable st;
     dc_ss := {| ss_in := ss_in (dc_ss st); ss_out := ss_out (dc_ss st); ss_stall := z; ss_err := ss_err (dc_ss st);
                 ss_obuf := ss_obuf (dc_ss st); ss_ahead := ss_ahead (dc_ss st); ss_calls := ss_calls (dc_ss st) |};
     dc_last := dc_last st; dc_par := dc_par st; dc_set := dc_set st; dc_bl := dc_bl st; dc_mem := dc_mem st;
     dc_ex := dc_ex st |}.

(* a context's state is st up to its stall count (kept opaque in the loop, so that no tactic unfolds it) *)
Definition stall_of (st0 st: dctx_st) (z: Z) : Prop := st0 = with_stall st z.

Lemma with_stall_init : with_stall dctx_init 0 = dctx_init.
Proof. reflexivity. Qed.

(* the state stream_exact gives after a call does not depend on the stall count before it *)
Lemma with_stall_after st z inp room r k dl s a l :
  set_last (set_ss (with_stall st z) (ss_after (dc_ss (with_stall st z)) inp room r k dl s a)) l =
  with_stall (set_last (set_ss st (ss_after (dc_ss st) inp room r k dl 0 a)) l) s.
Proof. reflexivity. Qed.

(* what the calls need of a context's state holds of st up to the stall count *)
Lemma stall_of_facts st0 st z : stall_of st0 st z -> fresh_cfg st -> dc_bl st = None -> ss_err (dc_ss st) = false ->
  fresh_cfg st0 /\ dc_dict st0 = None /\ dc_set st0 = nil /\ dc_bl st0 = None /\ ss_err (dc_ss st0) = false /\
  ss_calls (dc_ss st0) = ss_calls (dc_ss st).
Proof. intros -> F B E. unfold fresh_cfg in *. cbn. tauto. Qed.

(* the output delivered so far grows by the bytes of a call *)
Lemma prefix_grow (oc' rest: list val) (O dl: list Z) opos opos' :
  0 <= opos <= opos' -> opos' <= Zlength oc' ->
  sublist 0 opos oc' = zbytes O -> sublist opos opos' oc' = zbytes dl ->
  sublist 0 opos' (oc' ++ rest) = zbytes (O ++ dl).
Proof.
  intros H1 H2 E1 E2. rewrite sublist0_app1 by lia.
  rewrite (sublist_split 0 opos opos') by lia. rewrite E1, E2. clear E1 E2.
  induction O as [|x O IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(* a one-shot result that is not an error fits the capacity (oneshot_ok's first conjunct) *)
Lemma oneshot_le st s cap r out : dc_set st = nil -> oneshot_dctx st s cap r out -> is_error_code r = false -> r <= cap.
Proof. unfold oneshot_dctx. intros E. rewrite E. intros [H _]. exact H. Qed.

(* out_of_memory(r) = 0: r is not the memory-allocation error *)
Lemma not_oom r : Zstd.proof.zstd.Spec_util.error_of r <> 64 -> r <> err_code ZSTD_error_memory_allocation.
Proof.
  intros H E. apply H. subst r. unfold Zstd.proof.zstd.Spec_util.error_of, err_code, ZSTD_error_memory_allocation.
  reflexivity.
Qed.

(* the cells of a tuchar array are bytes: any list of Z shown there is a list of bytes, up to Int.repr *)
Definition bnorm (l: list Z) : list Z := map (fun x => Int.unsigned (Int.repr x)) l.

Lemma bnorm_zbytes l : zbytes (bnorm l) = zbytes l.
Proof.
  unfold bnorm. induction l as [|x l IH]; [reflexivity|]. simpl. rewrite Int.repr_unsigned. f_equal. exact IH.
Qed.

Lemma bnorm_ok {cs: compspecs} l : Forall (value_fits tuchar) (zbytes l) -> bytes_ok (bnorm l).
Proof.
  intros Hv. unfold bytes_ok, bnorm. induction l as [|x l IH]; [constructor|]. simpl in Hv.
  inversion Hv as [|? ? Hx Hr]; subst. constructor; [| apply IH; exact Hr].
  rewrite value_fits_eq in Hx. simpl in Hx. specialize (Hx ltac:(discriminate)). unfold is_byte. simpl in Hx.
  pose proof (Int.unsigned_range (Int.repr x)). change Byte.max_unsigned with 255 in Hx. lia.
Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_createDCtx_spec DC; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompressStream_spec DC DD;
   ZSTD_DCtx_reset_spec DC; ZSTD_DCtx_loadDictionary_spec DC; ZSTD_DCtx_setParameter_spec DC;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.out_of_memory_spec].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_reset.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call gv.
  Intros used.
  forward_call gv.
  Intros fresh.
  (* used or fresh NULL: the run ends *)
  destruct (eq_dec used nullval) as [Hu|Hu].
  { subst used. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  pose proof (isptr_of used PNused Hu) as Hup.
  destruct used as [| | | | | bu ou]; try contradiction.
  destruct (eq_dec fresh nullval) as [Hf|Hf].
  { subst fresh. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  pose proof (isptr_of fresh PNfresh Hf) as Hfp.
  destruct fresh as [| | | | | bf of]; try contradiction.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
  forward_if; [bad |].
  set (used := Vptr bu ou) in *. set (fresh := Vptr bf of) in *.
  sep_apply (drop_vp (DC gv used dctx_init) used).
  sep_apply (drop_vp (DC gv fresh dctx_init) fresh).
  (* ---------- phase 1: any use of `used` ---------- *)
  forward_loop
    (EX st: dctx_st,
     PROP (p1_ok st; dc_ss st = ss_init)
     LOCAL (temp _fresh fresh; temp _used used; lvar _out2 tout v_out2; lvar _out tout v_out;
            lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
     SEP (DC gv fresh dctx_init; DC gv used st; mem_mgr gv; zstd_globals gv; data_at_ Tsh tout v_out2;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in; TT))%assert
    break:
    (EX st: dctx_st,
     PROP (p1_ok st)
     LOCAL (temp _fresh fresh; temp _used used; lvar _out2 tout v_out2; lvar _out tout v_out;
            lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
     SEP (DC gv fresh dctx_init; DC gv used st; mem_mgr gv; zstd_globals gv; data_at_ Tsh tout v_out2;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in; TT))%assert.
  { Exists dctx_init. entailer!. exact p1_init. }
  { Intros st.
    forward_call 9223372036854775807.
    Intros n.
    forward_call (gv, n).
    Intros vret. destruct vret as [src s]. cbn [fst snd] in *.
    forward_call 9223372036854775807.
    Intros cap.
    forward_call (tarray tuchar cap, gv).
    { simpl. rep_lia. }
    Intros dst.
    unfold FSpecs.mbytes.
    repeat apply -> seq_assoc.
    (* src or dst NULL: the run ends *)
    destruct (eq_dec src nullval) as [Hs|Hs].
    { subst src. Intros. apply semax_if_seq. forward_if; [| bad]. forward.
      forward_if; [forward; cancel | bad]. }
    destruct (eq_dec dst nullval) as [Hd|Hd].
    { subst dst. Intros. apply semax_if_seq. forward_if; [bad |]. forward.
      forward_if; [forward; cancel | bad]. }
    Intros.
    assert_PROP (isptr dst) as Hdp by entailer!.
    assert_PROP (isptr src) as Hsp by entailer!.
    apply semax_if_seq. forward_if; [bad |].
    destruct dst as [| | | | | bd od]; try contradiction. forward.
    forward_if; [bad |].
    set (dst := Vptr bd od) in *. subst n.
    forward. forward. forward. forward. forward. forward.
    change (Int.signed (Int.repr 0)) with 0.
    sep_apply (to_Z Ews (Zlength s) (zbytes s) src). sep_apply (tok_to_Z Ews (Zlength s) src).
    sep_apply (to_Z_ Ews cap dst). sep_apply (tok_to_Z Ews cap dst).
    forward_call tt. Intros u.
    forward_if (EX st1: dctx_st,
      PROP (p1_ok st1)
      LOCAL (temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _src src;
             temp _n (Vlong (Int64.repr (Zlength s))); temp _fresh fresh; temp _used used;
             lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
      SEP (mem_mgr gv; @malloc_token ZCS Ews (tarray tuchar cap) dst; @data_at_ ZCS Ews (tarray tuchar cap) dst;
           @malloc_token ZCS Ews (tarray tuchar (Zlength s)) src;
           @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
           DC gv fresh dctx_init; DC gv used st1; zstd_globals gv;
           data_at_ Tsh tout v_out2; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in;
           TT))%assert.
    - (* one-shot *)
      rewrite (DC_res1 DC DD gv used st Ews) by auto. Intros.
      sep_apply (pws_fold (tarray tuchar (Zlength s)) src (tarray tuchar cap) dst).
      forward_call ([pw_token Ews (tarray tuchar (Zlength s)) src; pw_token Ews (tarray tuchar cap) dst],
                    gv, used, st, Ews, Ews, dst, cap, Ews, src, s).
      { split; [apply buf_ok_tok; [simpl; tauto | auto | lia | auto] |].
        split; [apply buf_ok_tok; [simpl; tauto | auto | rep_lia | auto] |].
        split; [apply dict_buf_ok_p1; exact H1 |].
        destruct H1 as (Hs1 & Hb1 & _). rewrite Hs1. split; [constructor | exact Hb1]. }
      Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
      sep_apply pws_unfold.
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
      pose proof H1 as (Hs1 & _ & _ & _ & Hd1).
      rewrite (own_res DD gv Ews (dc_dict st) Hd1), Hs1. unfold set_res. simpl fold_right.
      Exists st'. entailer!. eapply p1_after_decode; [eassumption | apply oneshot_after_init; eassumption].
    - (* streaming: any pieces, any room, until an error or the run stops *)
      rewrite (@data_at__eq ZCS).
      forward_loop
        (EX st1: dctx_st, EX isz: Z, EX ipos: Z, EX opos: Z, EX osv: val, EX oc: list val,
         PROP (0 <= ipos <= isz; isz <= Zlength s; 0 <= opos <= cap; Zlength oc = cap; p1_ok st1;
               ss_err (dc_ss st1) = false)
         LOCAL (temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _src src;
                temp _n (Vlong (Int64.repr (Zlength s))); temp _fresh fresh; temp _used used;
                lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
         SEP (mem_mgr gv; @malloc_token ZCS Ews (tarray tuchar cap) dst; @data_at ZCS Ews (tarray tuchar cap) oc dst;
              @malloc_token ZCS Ews (tarray tuchar (Zlength s)) src;
              @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
              DC gv fresh dctx_init; DC gv used st1; zstd_globals gv;
              data_at_ Tsh tout v_out2; data_at Tsh tout (dst, (osv, Vlong (Int64.repr opos))) v_out;
              data_at_ Tsh tin v_in2; data_at Tsh tin (src, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos))) v_in;
              TT))%assert
        break:
        (EX st1: dctx_st,
         PROP (p1_ok st1)
         LOCAL (temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _src src;
                temp _n (Vlong (Int64.repr (Zlength s))); temp _fresh fresh; temp _used used;
                lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
         SEP (mem_mgr gv; @malloc_token ZCS Ews (tarray tuchar cap) dst; @data_at_ ZCS Ews (tarray tuchar cap) dst;
              @malloc_token ZCS Ews (tarray tuchar (Zlength s)) src;
              @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
              DC gv fresh dctx_init; DC gv used st1; zstd_globals gv;
              data_at_ Tsh tout v_out2; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in;
              TT))%assert.
      { Exists st 0 0 0 (fst (snd (default_val tout))) (@default_val ZCS (tarray tuchar cap)).
        entailer!. rewrite H2. reflexivity. }
      Intros st1 isz ipos opos osv oc.
      (* in.size += upto(n - in.size); out.size = out.pos + upto(cap - out.pos) *)
      forward. forward_call (Zlength s - isz). Intros v. forward. forward.
      forward. forward_call (cap - opos). Intros w. forward. forward.
      rewrite !add64_repr.
      (* the call sees the first isz + v bytes of src and the first opos + w cells of dst *)
      assert_PROP (@field_compatible ZCS (tarray tuchar (Zlength s)) [] src) as Fs by entailer!.
      assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] dst) as Fd by entailer!.
      rewrite (arr_split Ews (Zlength s) (isz + v) (zbytes s) src Fs) by (try rewrite Zlength_map; lia).
      rewrite (arr_split Ews cap (opos + w) oc dst Fd) by lia.
      rewrite !sublist_map.
      Intros.
      sep_apply (wits_fold (Zlength s) (isz + v) (zbytes (sublist (isz + v) (Zlength s) s)) src cap (opos + w)
                   (sublist (opos + w) cap oc) dst).
      rewrite <- out_Z, <- in_Z.
      rewrite (DC_res1 DC DD gv used st1 Ews) by auto.
      Intros.
      forward_call (wits (Zlength s) (isz + v) (zbytes (sublist (isz + v) (Zlength s) s)) src cap (opos + w)
                      (sublist (opos + w) cap oc) dst,
        gv, used, st1, v_out, v_in, Tsh, Tsh, Ews, dst, opos + w, opos, sublist 0 (opos + w) oc, Ews, src, isz + v,
        ipos, sublist 0 (isz + v) s).
      { unfold mbuf; rewrite ?if_false by auto. cancel. }
      { split; [apply (buf_ok_pre _ Ews cap (opos + w) (sublist (opos + w) cap oc) dst);
                [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
        split; [apply (buf_ok_pre _ Ews (Zlength s) (isz + v) (zbytes (sublist (isz + v) (Zlength s) s)) src);
                [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
        pose proof H14 as (_ & _ & _ & Hk1 & _). rewrite Hk1.
        split; [discriminate |]. split; [discriminate |].
        split; [apply stream_dict_ok_p1; auto |].
        split; [rewrite Zlength_sublist; lia |]. split; [rewrite Zlength_sublist; lia |].
        apply bytes_ok_sublist; auto. }
      Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
      match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        destruct H as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor & Hr0 & Hst' & _) end.
      sep_apply (drop_vp (DC gv used st') used).
      pose proof H14 as (Hs1 & _ & _ & _ & Hd1).
      rewrite (own_res DD gv Ews (dc_dict st1) Hd1), Hs1. unfold set_res. simpl fold_right.
      (* the two objects again *)
      sep_apply (wits_unfold (Zlength s) (isz + v) (zbytes (sublist (isz + v) (Zlength s) s)) src cap (opos + w)
                   (sublist (opos + w) cap oc) dst).
      sep_apply (arr_join Ews cap (opos + w) oc' (sublist (opos + w) cap oc) dst Fd);
        try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
      sep_apply (arr_join Ews (Zlength s) (isz + v) (zbytes (sublist 0 (isz + v) s))
                   (zbytes (sublist (isz + v) (Zlength s) s)) src Fs);
        try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
      replace (zbytes (sublist 0 (isz + v) s) ++ zbytes (sublist (isz + v) (Zlength s) s)) with (zbytes s)
        by (rewrite <- map_app, <- sublist_split by lia; rewrite sublist_same by lia; reflexivity).
      rewrite out_Z, in_Z.
      assert (P': p1_ok st' /\ ss_err (dc_ss st') = is_error_code r)
        by (rewrite Hst'; split; [apply p1_set_last, p1_set_ss; auto | reflexivity]).
      destruct P' as [P' E'].
      forward_call r.
      apply semax_if_seq. forward_if.
      + forward_call tt. Intros u2. forward.
        forward_if.
        * forward.
          destruct (is_error_code r) eqn:Er; [bad |].
          Exists st' (isz + v) ipos' opos' (Vlong (Int64.repr (opos + w))) (oc' ++ sublist (opos + w) cap oc).
          entailer!.
        * sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) (oc' ++ sublist (opos + w) cap oc) dst).
          forward. Exists st'. entailer!.
      + forward. forward_if; [bad |].
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) (oc' ++ sublist (opos + w) cap oc) dst).
        forward. Exists st'. entailer!.
    - Intros st1.
      forward_call (gv, used, st1, ZSTD_reset_session_only).
      Intros vret. destruct vret as [r1 st2]. cbn [fst snd] in *.
      match goal with H: reset_post _ _ _ _ |- _ => apply reset_post_session in H; destruct H as [_ Hst2] end.
      assert (P2: p1_ok st2 /\ dc_ss st2 = ss_init) by (subst st2; split; [apply p1_set_ex, p1_set_ss; auto | reflexivity]).
      clear Hst2. destruct P2 as [P2 S2].
      forward_call tt. Intros u1.
      forward_if (EX st3: dctx_st,
        PROP (p1_ok st3; dc_ss st3 = ss_init)
        LOCAL (temp _dst dst; temp _src src; temp _fresh fresh; temp _used used;
               lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
        SEP (mem_mgr gv; @malloc_token ZCS Ews (tarray tuchar cap) dst; @data_at_ ZCS Ews (tarray tuchar cap) dst;
             @malloc_token ZCS Ews (tarray tuchar (Zlength s)) src;
             @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
             DC gv fresh dctx_init; DC gv used st3; zstd_globals gv;
             data_at_ Tsh tout v_out2; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in;
             TT))%assert.
      + sep_apply (pws1_fold (tarray tuchar (Zlength s)) src).
        forward_call ([pw_token Ews (tarray tuchar (Zlength s)) src], gv, used, st2, Ews, src, s).
        { pose proof P2 as (_ & Hb2 & Hm2 & _).
          split; [apply buf_ok_tok; [simpl; tauto | auto | rep_lia | auto] |].
          repeat split; auto; rep_lia. }
        Intros vret. destruct vret as [r2 st3]. cbn [fst snd] in *.
        sep_apply pws1_unfold.
        match goal with H: after_stage _ _ _ _ |- _ => destruct (p1_load_stage _ _ _ _ P2 S2 H) as [P3 S3] end.
        Exists st3. entailer!.
      + forward. Exists st2. entailer!.
      + Intros st3.
        match goal with H: p1_ok st3 |- _ => rename H into P3 end.
        match goal with H: dc_ss st3 = ss_init |- _ => rename H into S3 end.
        forward_call tt. Intros w.
        forward_call (gv, used, st3, ZSTD_d_windowLogMax, Int.signed (Int.repr w)).
        { rewrite Int.repr_signed. entailer!. }
        { split; [simpl; auto | destruct P3 as (_ & Hb3 & _); exact Hb3]. }
        Intros vret. destruct vret as [r3 st4]. cbn [fst snd] in *.
        match goal with H: after_stage _ _ _ _ |- _ => destruct (p1_setpar _ _ _ _ P3 S3 H) as [P4 S4] end.
        (* free the two buffers *)
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src).
        sep_apply (of_Z_ Ews (Zlength s) src).
        sep_apply (tok_of_Z Ews (Zlength s) src).
        sep_apply (@free_pre HCS (tarray tuchar (Zlength s)) src Hsp).
        forward_call (tarray tuchar (Zlength s), src, gv).
        sep_apply (of_Z_ Ews cap dst).
        sep_apply (tok_of_Z Ews cap dst).
        sep_apply (@free_pre HCS (tarray tuchar cap) dst Hdp).
        forward_call (tarray tuchar cap, dst, gv).
        (* do ... while (nondet_u8() != 0) *)
        forward_call tt. Intros u2.
        forward_if.
        * forward. Exists st4. entailer!.
        * forward. Exists st4. entailer!. }
  (* ---------- ZSTD_DCtx_reset(session_and_parameters): `used` is a new context ---------- *)
  Intros st.
  match goal with H: p1_ok st |- _ => rename H into P end.
  forward_call (gv, used, st, ZSTD_reset_session_and_parameters).
  Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
  match goal with H: reset_post _ _ _ _ |- _ => apply reset_post_both in H; destruct H as [Er0 Hst0] end.
  pose proof P as (Ps & _ & Pm & _).
  rewrite (reset_both_init st Ps Pm) in Hst0. subst st0 r0.
  forward_call 0.
  forward_if; [forward; cancel |].
  (* ---------- phase 2: the same calls on both ---------- *)
  forward_call 9223372036854775807.
  Intros n.
  forward_call (gv, n).
  Intros vret. destruct vret as [src s]. cbn [fst snd] in *.
  forward_call 9223372036854775807.
  Intros cap.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros dst.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros oth.
  unfold FSpecs.mbytes.
  (* src, dst or other NULL: the run ends *)
  repeat apply -> seq_assoc.
  destruct (eq_dec src nullval) as [Hs|Hs].
  { subst src. Intros. apply semax_if_seq. forward_if; [| bad]. forward.
    apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  assert_PROP (isptr src) as Hsp by entailer!.
  destruct (eq_dec dst nullval) as [Hd|Hd].
  { subst dst. Intros. apply semax_if_seq. forward_if; [bad |]. forward.
    apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  assert_PROP (isptr dst) as Hdp by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  destruct (eq_dec oth nullval) as [Ho|Ho].
  { subst oth. Intros. apply semax_if_seq. forward_if; [bad |]. forward.
    apply semax_if_seq. forward_if; [bad |]. forward.
    forward_if; [forward; cancel | bad]. }
  Intros.
  assert_PROP (isptr oth) as Hop by entailer!.
  destruct oth as [| | | | | bo po]; try contradiction.
  apply semax_if_seq. forward_if; [bad |]. forward.
  apply semax_if_seq. forward_if; [bad |]. forward.
  forward_if; [bad |].
  set (dst := Vptr bd od) in *. set (oth := Vptr bo po) in *. subst n.
  sep_apply (to_Z Ews (Zlength s) (zbytes s) src). sep_apply (tok_to_Z Ews (Zlength s) src).
  sep_apply (to_Z_ Ews cap dst). sep_apply (tok_to_Z Ews cap dst).
  sep_apply (to_Z_ Ews cap oth). sep_apply (tok_to_Z Ews cap oth).
  forward_call tt. Intros u.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx R))) end.
  { (* one-shot on both contexts *)
    sep_apply (res_none_i DD gv Ews).
    sep_apply (pws_fold (tarray tuchar (Zlength s)) src (tarray tuchar cap) dst).
    forward_call ([pw_token Ews (tarray tuchar (Zlength s)) src; pw_token Ews (tarray tuchar cap) dst],
                  gv, used, dctx_init, Ews, Ews, dst, cap, Ews, src, s).
    { cancel. }
    { split; (apply buf_ok_tok; [simpl; tauto | auto | rep_lia | auto]). }
    Intros vret. destruct vret as [[r1 out1] st1]. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
    sep_apply pws_unfold. sep_apply (res_none_e DD gv Ews).
    sep_apply (pws_fold (tarray tuchar (Zlength s)) src (tarray tuchar cap) oth).
    sep_apply (res_none_i DD gv Ews).
    forward_call ([pw_token Ews (tarray tuchar (Zlength s)) src; pw_token Ews (tarray tuchar cap) oth],
                  gv, fresh, dctx_init, Ews, Ews, oth, cap, Ews, src, s).
    { cancel. }
    { split; (apply buf_ok_tok; [simpl; tauto | auto | rep_lia | auto]). }
    Intros vret. destruct vret as [[r2 out2] st2]. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
    sep_apply pws_unfold. sep_apply (res_none_e DD gv Ews).
    clear H14 H15 H20 H21.
    pose proof (H16 fresh_init) as X1. pose proof (H22 fresh_init) as X2. clear H16 H22.
    (* out_of_memory(result) || out_of_memory(expected): the run ends *)
    forward_call r1.
    destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r1) 64) as [M1|M1].
    { apply semax_if_seq. forward_if; [| bad]. forward. forward_if; [forward; cancel | bad]. }
    apply semax_if_seq. forward_if; [bad |].
    (* the call alone (VST's call-with-cast rule does not take the cast int -> _Bool) *)
    apply -> seq_assoc.
    forward_call r2.
    destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r2) 64) as [M2|M2].
    { forward. forward_if; [forward; cancel | bad]. }
    forward. forward_if; [bad |].
    destruct X1 as [X1 | X1]; [exfalso; exact (not_oom r1 M1 X1) |].
    destruct X2 as [X2 | X2]; [exfalso; exact (not_oom r2 M2 X2) |].
    (* the check: both contexts give the same outcome *)
    revert X1 X2. destruct (os_res s cap) as [c|]; intros X1 X2.
    - destruct X1 as [Er1 Eb1], X2 as [Er2 Eb2].
      subst r1 r2.
      destruct (is_error_code (Zlength c)) eqn:Ec.
      + forward_call (Zlength c). rewrite Ec.
        apply semax_if_seq. forward_if; [| bad].
        forward_call (Zlength c). rewrite Ec.
        forward_call (Int.repr 1).
        forward. cancel.
      + pose proof (oneshot_le dctx_init _ _ _ _ eq_refl H13 Ec) as Hle.
        forward_call (Zlength c). rewrite Ec.
        apply semax_if_seq. forward_if; [bad |].
        apply semax_if_seq. forward_if; [| bad].
        assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] dst) as Fd by entailer!.
        assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] oth) as Fo by entailer!.
        rewrite (arr_split Ews cap (Zlength c) out1 dst Fd) by lia.
        rewrite (arr_split Ews cap (Zlength c) out2 oth Fo) by lia.
        rewrite Eb1, Eb2.
        assert_PROP (@Forall val (@value_fits ZCS tuchar) (zbytes c)) as VF by entailer!.
        pose proof (bnorm_ok _ VF) as Bc.
        rewrite <- (bnorm_zbytes c).
        assert (Lc: Zlength (bnorm c) = Zlength c) by (unfold bnorm; rewrite Zlength_map; lia).
        rewrite <- Lc.
        sep_apply (of_Z Ews (Zlength (bnorm c)) (zbytes (bnorm c)) dst).
        sep_apply (of_Z Ews (Zlength (bnorm c)) (zbytes (bnorm c)) oth).
        repeat apply -> seq_assoc.
        forward_call (Ews, dst, bnorm c, Ews, oth, bnorm c).
        destruct (list_eq_dec Z.eq_dec (bnorm c) (bnorm c)) as [_|NE]; [| congruence].
        forward. forward.
        forward_call Int.one.
        forward. cancel.
    - forward_call r1. rewrite X1.
      apply semax_if_seq. forward_if; [| bad].
      forward_call r2. rewrite X2.
      forward_call (Int.repr 1).
      forward. cancel. }
  { forward. entailer!. }
  (* ---------- the same streaming calls on both: one abstract state, the same delivered bytes ---------- *)
  forward. forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  rewrite (@data_at__eq ZCS Ews (tarray tuchar cap) dst), (@data_at__eq ZCS Ews (tarray tuchar cap) oth).
  forward_loop
    (EX st: dctx_st, EX z1: Z, EX z2: Z, EX ipos: Z, EX opos: Z, EX vi1: val, EX vi2: val, EX vo1: val, EX vo2: val,
     EX oc1: list val, EX oc2: list val, EX O: list Z,
     PROP (0 <= ipos <= Zlength s; 0 <= opos <= cap; Zlength oc1 = cap; Zlength oc2 = cap;
           sublist 0 opos oc1 = zbytes O; sublist 0 opos oc2 = zbytes O;
           fresh_cfg st; dc_bl st = None; ss_err (dc_ss st) = false)
     LOCAL (temp _other oth; temp _dst dst; temp _cap (Vlong (Int64.repr cap)); temp _src src;
            temp _n (Vlong (Int64.repr (Zlength s))); temp _fresh fresh; temp _used used;
            lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in; gvars gv)
     SEP (@malloc_token ZCS Ews (tarray tuchar cap) oth; @data_at ZCS Ews (tarray tuchar cap) oc2 oth;
          @malloc_token ZCS Ews (tarray tuchar cap) dst; @data_at ZCS Ews (tarray tuchar cap) oc1 dst;
          @malloc_token ZCS Ews (tarray tuchar (Zlength s)) src;
          @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
          mem_mgr gv; zstd_globals gv; DC gv used (with_stall st z1); DC gv fresh (with_stall st z2);
          data_at Tsh tout (oth, (vo2, Vlong (Int64.repr opos))) v_out2;
          data_at Tsh tout (dst, (vo1, Vlong (Int64.repr opos))) v_out;
          data_at Tsh tin (src, (vi2, Vlong (Int64.repr ipos))) v_in2;
          data_at Tsh tin (src, (vi1, Vlong (Int64.repr ipos))) v_in; TT))%assert
    break: (PROP () LOCAL (lvar _out2 tout v_out2; lvar _out tout v_out; lvar _in2 tin v_in2; lvar _in tin v_in;
                            gvars gv)
            SEP (data_at_ Tsh tout v_out2; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in2; data_at_ Tsh tin v_in;
                 TT))%assert.
  { rewrite <- with_stall_init.
    Exists dctx_init 0 0 0 0 (fst (snd (default_val tin))) (fst (snd (default_val tin)))
      (fst (snd (default_val tout))) (fst (snd (default_val tout)))
      (@default_val ZCS (tarray tuchar cap)) (@default_val ZCS (tarray tuchar cap)) (@nil Z).
    entailer!. exact fresh_init. }
  2: { forward. cancel. }
  clear P Ps Pm st.
  Intros st z1 z2 ipos opos vi1 vi2 vo1 vo2 oc1 oc2 O.
  match goal with H: fresh_cfg st |- _ => rename H into Fst end.
  (* stu, stf: the states of used and fresh *)
  assert (Eu: exists stu, stall_of stu st z1) by (eexists; reflexivity). destruct Eu as [stu Eu].
  assert (Ef: exists stf, stall_of stf st z2) by (eexists; reflexivity). destruct Ef as [stf Ef].
  replace (with_stall st z1) with stu by exact Eu. replace (with_stall st z2) with stf by exact Ef.
  destruct (stall_of_facts stu st z1 Eu Fst ltac:(assumption) ltac:(assumption)) as (Fu & Fdu & Fsu & Bu & Su & Cu).
  destruct (stall_of_facts stf st z2 Ef Fst ltac:(assumption) ltac:(assumption)) as (Ff & Fdf & Fsf & Bf & Sf & Cf).
  pose proof Fu as (_ & _ & _ & Fku & _). pose proof Ff as (_ & _ & _ & Fkf & _).
  (* in.size = in2.size = in.pos + upto(n - in.pos); out.size = out2.size = out.pos + upto(cap - out.pos) *)
  forward. forward_call (Zlength s - ipos). Intros v. forward. forward. forward. forward.
  forward. forward_call (cap - opos). Intros w. forward. forward. forward. forward.
  rewrite !add64_repr.
  assert_PROP (@field_compatible ZCS (tarray tuchar (Zlength s)) [] src) as Fs by entailer!.
  assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] dst) as Fd by entailer!.
  assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] oth) as Fo by entailer!.
  assert (Ls: Zlength (zbytes s) = Zlength s) by (rewrite Zlength_map; reflexivity).
  (* the first call: used, out, in; it sees the first ipos + v bytes of src and opos + w cells of dst *)
  rewrite (arr_split Ews (Zlength s) (ipos + v) (zbytes s) src Fs) by lia.
  rewrite (arr_split Ews cap (opos + w) oc1 dst Fd) by lia.
  rewrite !sublist_map.
  Intros.
  sep_apply (wits_fold (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
               (sublist (opos + w) cap oc1) dst).
  rewrite <- (out_Z Tsh dst _ _ v_out), <- (in_Z Tsh src _ _ v_in).
  rewrite (DC_res DC DD gv used stu Ews) by auto.
  Intros.
  forward_call (wits (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
                  (sublist (opos + w) cap oc1) dst,
    gv, used, stu, v_out, v_in, Tsh, Tsh, Ews, dst, opos + w, opos, sublist 0 (opos + w) oc1, Ews, src, ipos + v,
    ipos, sublist 0 (ipos + v) s).
  { unfold mbuf; rewrite ?if_false by auto. cancel. }
  { split; [apply (buf_ok_pre _ Ews cap (opos + w) (sublist (opos + w) cap oc1) dst);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply (buf_ok_pre _ Ews (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply stream_dict_ok_none; auto |].
    split; [rewrite Zlength_sublist; lia |]. split; [rewrite Zlength_sublist; lia |].
    apply bytes_ok_sublist; auto. }
  Intros vret. destruct vret as [[[[r1 opos1] ipos1] oc1'] st1]. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl1 & stall1 & a1 & Hop1 & Hip1 & Hoc1 & Hpre1 & _) end.
  match goal with H: stream_exact stu _ r1 _ _ _ _ _ _ _ _ |- _ => pose proof (H Fu) as X1; clear H end.
  sep_apply (drop_vp (DC gv used st1) used).
  rewrite Fdu, Fsu. change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  sep_apply (wits_unfold (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
               (sublist (opos + w) cap oc1) dst).
  sep_apply (arr_join Ews cap (opos + w) oc1' (sublist (opos + w) cap oc1) dst Fd);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  sep_apply (arr_join Ews (Zlength s) (ipos + v) (zbytes (sublist 0 (ipos + v) s))
               (zbytes (sublist (ipos + v) (Zlength s) s)) src Fs);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  replace (zbytes (sublist 0 (ipos + v) s) ++ zbytes (sublist (ipos + v) (Zlength s) s)) with (zbytes s)
    by (rewrite <- map_app, <- sublist_split by lia; rewrite sublist_same by lia; reflexivity).
  rewrite (out_Z Tsh dst), (in_Z Tsh src).
  (* the second call: fresh, out2, in2, the same bytes and room *)
  rewrite (arr_split Ews (Zlength s) (ipos + v) (zbytes s) src Fs) by lia.
  rewrite (arr_split Ews cap (opos + w) oc2 oth Fo) by lia.
  rewrite !sublist_map.
  Intros.
  sep_apply (wits_fold (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
               (sublist (opos + w) cap oc2) oth).
  rewrite <- (out_Z Tsh oth _ _ v_out2), <- (in_Z Tsh src _ _ v_in2).
  rewrite (DC_res DC DD gv fresh stf Ews) by auto.
  Intros.
  forward_call (wits (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
                  (sublist (opos + w) cap oc2) oth,
    gv, fresh, stf, v_out2, v_in2, Tsh, Tsh, Ews, oth, opos + w, opos, sublist 0 (opos + w) oc2, Ews, src, ipos + v,
    ipos, sublist 0 (ipos + v) s).
  { unfold mbuf; rewrite ?if_false by auto. cancel. }
  { split; [apply (buf_ok_pre _ Ews cap (opos + w) (sublist (opos + w) cap oc2) oth);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply (buf_ok_pre _ Ews (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src);
            [in_wits | in_wits | lia | auto | apply writable_readable, writable_Ews] |].
    split; [apply stream_dict_ok_none; auto |].
    split; [rewrite Zlength_sublist; lia |]. split; [rewrite Zlength_sublist; lia |].
    apply bytes_ok_sublist; auto. }
  Intros vret. destruct vret as [[[[r2 opos2] ipos2] oc2'] st2]. cbn [fst snd] in *. unfold mbuf; rewrite ?if_false by auto.
  match goal with H: stream_post stf _ r2 _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl2 & stall2 & a2 & Hop2 & Hip2 & Hoc2 & Hpre2 & _) end.
  match goal with H: stream_exact stf _ r2 _ _ _ _ _ _ _ _ |- _ => pose proof (H Ff) as X2; clear H end.
  sep_apply (drop_vp (DC gv fresh st2) fresh).
  rewrite Fdf, Fsf. change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  sep_apply (wits_unfold (Zlength s) (ipos + v) (zbytes (sublist (ipos + v) (Zlength s) s)) src cap (opos + w)
               (sublist (opos + w) cap oc2) oth).
  sep_apply (arr_join Ews cap (opos + w) oc2' (sublist (opos + w) cap oc2) oth Fo);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  sep_apply (arr_join Ews (Zlength s) (ipos + v) (zbytes (sublist 0 (ipos + v) s))
               (zbytes (sublist (ipos + v) (Zlength s) s)) src Fs);
    try (rewrite ?Zlength_map; rewrite ?Zlength_sublist by lia; lia).
  replace (zbytes (sublist 0 (ipos + v) s) ++ zbytes (sublist (ipos + v) (Zlength s) s)) with (zbytes s)
    by (rewrite <- map_app, <- sublist_split by lia; rewrite sublist_same by lia; reflexivity).
  rewrite (out_Z Tsh oth), (in_Z Tsh src).
  clear H22 H23 H25 H26.
  (* out_of_memory(result) || out_of_memory(expected): the run ends *)
  forward_call r1.
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r1) 64) as [M1|M1].
  { apply semax_if_seq. forward_if; [| bad]. forward. forward_if; [forward; cancel | bad]. }
  apply semax_if_seq. forward_if; [bad |].
  apply -> seq_assoc.
  forward_call r2.
  destruct (Z.eq_dec (Zstd.proof.zstd.Spec_util.error_of r2) 64) as [M2|M2].
  { forward. forward_if; [forward; cancel | bad]. }
  forward. forward_if; [bad |].
  destruct X1 as [X1 | X1]; [exfalso; exact (not_oom r1 M1 X1) |].
  destruct X2 as [X2 | X2]; [exfalso; exact (not_oom r2 M2 X2) |].
  cbv zeta in X1, X2. rewrite Cu in X1. rewrite Cf in X2.
  (* the check: both calls have the same outcome, both contexts the same next state *)
  revert X1 X2.
  destruct (zs_call (ss_calls (dc_ss st)) (sublist ipos (ipos + v) (sublist 0 (ipos + v) s), opos + w - opos))
    as [[[[[r0 k] dl] stall] a]|]; intros X1 X2.
  - destruct X1 as (Er1 & Ei1 & Eo1 & Eb1 & s1 & Es1), X2 as (Er2 & Ei2 & Eo2 & Eb2 & s2 & Es2).
    subst r1 r2 ipos1 ipos2 opos1 opos2 st1 st2.
    destruct (is_error_code r0) eqn:Ec.
    + (* an error in both: the loop ends *)
      forward_call r0. rewrite Ec.
      apply semax_if_seq. forward_if; [| bad].
      forward_call r0. rewrite Ec.
      forward_call (Int.repr 1).
      forward_call r0. rewrite Ec.
      apply semax_if_seq. forward_if.
      * bad.
      * forward. forward_if; [bad | forward; entailer!].
    + forward_call r0. rewrite Ec.
      apply semax_if_seq. forward_if; [bad |].
      repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| bad].
      forward. forward. forward.
      apply semax_if_seq. forward_if;
        [| match goal with Hz: proj_sumbool (zeq ?x ?x) = false |- _ => rewrite proj_sumbool_is_true in Hz by reflexivity; discriminate Hz end].
      forward. forward. forward.
      apply semax_if_seq. forward_if;
        [| match goal with Hz: proj_sumbool (zeq ?x ?x) = false |- _ => rewrite proj_sumbool_is_true in Hz by reflexivity; discriminate Hz end].
      (* bytes_eq(dst, other, out.pos): the first opos + |dl| cells of both are the bytes delivered so far *)
      forward.
      assert (E1: sublist 0 (opos + Zlength dl) (oc1' ++ sublist (opos + w) cap oc1) = zbytes (O ++ dl)).
      { apply (prefix_grow _ _ _ _ opos); try lia; [| exact Eb1]. rewrite Hpre1, sublist_sublist00 by lia. exact H14. }
      assert (E2: sublist 0 (opos + Zlength dl) (oc2' ++ sublist (opos + w) cap oc2) = zbytes (O ++ dl)).
      { apply (prefix_grow _ _ _ _ opos); try lia; [| exact Eb2]. rewrite Hpre2, sublist_sublist00 by lia. exact H15. }
      assert (LO: Zlength O = opos).
      { assert (Z1: Zlength (sublist 0 opos oc1) = opos) by (rewrite Zlength_sublist; lia).
        rewrite H14, Zlength_map in Z1. exact Z1. }
      rewrite (arr_split Ews cap (opos + Zlength dl) (oc1' ++ sublist (opos + w) cap oc1) dst Fd)
        by (try rewrite Zlength_app, Zlength_sublist; lia).
      rewrite (arr_split Ews cap (opos + Zlength dl) (oc2' ++ sublist (opos + w) cap oc2) oth Fo)
        by (try rewrite Zlength_app, Zlength_sublist; lia).
      rewrite E1, E2.
      assert_PROP (@Forall val (@value_fits ZCS tuchar) (zbytes (O ++ dl))) as VF by entailer!.
      pose proof (bnorm_ok _ VF) as Bn.
      rewrite <- (bnorm_zbytes (O ++ dl)).
      assert (LN: Zlength (bnorm (O ++ dl)) = opos + Zlength dl)
        by (unfold bnorm; rewrite Zlength_map, Zlength_app; lia).
      sep_apply (of_Z Ews (opos + Zlength dl) (zbytes (bnorm (O ++ dl))) dst).
      sep_apply (of_Z Ews (opos + Zlength dl) (zbytes (bnorm (O ++ dl))) oth).
      rewrite <- LN.
      repeat apply -> seq_assoc.
      forward_call (Ews, dst, bnorm (O ++ dl), Ews, oth, bnorm (O ++ dl)).
      destruct (list_eq_dec Z.eq_dec (bnorm (O ++ dl)) (bnorm (O ++ dl))) as [_|NE]; [| congruence].
      rewrite LN.
      forward. forward.
      forward_call Int.one.
      (* the two objects again *)
      sep_apply (to_Z Ews (opos + Zlength dl) (zbytes (bnorm (O ++ dl))) dst).
      sep_apply (to_Z Ews (opos + Zlength dl) (zbytes (bnorm (O ++ dl))) oth).
      assert (LR1: Zlength (sublist (opos + Zlength dl) cap (oc1' ++ sublist (opos + w) cap oc1)) =
                   cap - (opos + Zlength dl))
        by (rewrite Zlength_sublist; [lia | lia | rewrite Zlength_app, Zlength_sublist; lia]).
      assert (LR2: Zlength (sublist (opos + Zlength dl) cap (oc2' ++ sublist (opos + w) cap oc2)) =
                   cap - (opos + Zlength dl))
        by (rewrite Zlength_sublist; [lia | lia | rewrite Zlength_app, Zlength_sublist; lia]).
      assert (LZ: Zlength (zbytes (bnorm (O ++ dl))) = opos + Zlength dl) by (rewrite Zlength_map; exact LN).
      sep_apply (arr_join Ews cap (opos + Zlength dl) _ _ dst Fd ltac:(lia) LZ LR1).
      sep_apply (arr_join Ews cap (opos + Zlength dl) _ _ oth Fo ltac:(lia) LZ LR2).
      (* while (!ZSTD_isError(result) && nondet_u8() != 0) *)
      forward_call r0. rewrite Ec.
      apply semax_if_seq. forward_if.
      * forward_call tt. Intros u2. forward. forward_if.
        -- forward.
           unfold stall_of in Eu, Ef. subst stu stf. rewrite !with_stall_after.
           Exists (set_last (set_ss st (ss_after (dc_ss st) (sublist ipos (ipos + v) (sublist 0 (ipos + v) s))
                     (opos + w - opos) r0 k dl 0 a)) (Some stream_mark)) s1 s2
             (ipos + k) (opos + Zlength dl) (Vlong (Int64.repr (ipos + v))) (Vlong (Int64.repr (ipos + v)))
             (Vlong (Int64.repr (opos + w))) (Vlong (Int64.repr (opos + w)))
             (zbytes (bnorm (O ++ dl)) ++ sublist (opos + Zlength dl) cap (oc1' ++ sublist (opos + w) cap oc1))
             (zbytes (bnorm (O ++ dl)) ++ sublist (opos + Zlength dl) cap (oc2' ++ sublist (opos + w) cap oc2))
             (bnorm (O ++ dl)).
           entailer!.
           split; rewrite sublist0_app1 by lia; rewrite sublist_same by lia; reflexivity.
        -- forward. entailer!.
      * first [bad | exfalso; match goal with Hn: _ <> Int.zero |- _ => apply Hn; reflexivity end].

  - (* an error in both: the loop ends *)
    forward_call r1. rewrite X1.
    apply semax_if_seq. forward_if; [| bad].
    forward_call r2. rewrite X2.
    forward_call (Int.repr 1).
    forward_call r1. rewrite X1.
    apply semax_if_seq. forward_if.
    * bad.
    * forward. forward_if; [bad | forward; entailer!].
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's out_of_memory,
   any_bytes, upto and bytes_eq (laws_common.h) *)
Definition Hs : funspecs :=
  [Zstd.proof.harness.frames.FSpecs.out_of_memory_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs].

Lemma Externals_eq :
  Externals = [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
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
  (Specs_api DC DD ++ [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
                       Zstd.proof.harness.frames.FSpecs.out_of_memory_spec;
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

(* main's body, proved with the functions it calls (G0), holds in the context of Gprog: every entry of G0 is one of
   Gprog, and no function of Gprog is a global variable of the program *)
Lemma tsub_G (V: varspecs) (G1 G2: funspecs) f :
  (forall i fs, initial_world.find_id i G1 = Some fs -> initial_world.find_id i G2 = Some fs) ->
  (forall i, In i (map fst G2) -> ~ In i (map fst V)) ->
  tycontext_sub (func_tycontext f V G1 []) (func_tycontext f V G2 []).
Proof.
  intros HG HV. apply tycontext_sub_i99. split; intro i.
  - rewrite (make_tycontext_g_find V G1 i), (make_tycontext_g_find V G2 i).
    destruct (initial_world.find_id i G1) as [fs|] eqn:E.
    + rewrite (HG i fs E). apply sub_option_refl.
    + destruct (initial_world.find_id i G2) as [fs'|] eqn:E'.
      * rewrite mtg_none; [exact Logic.I |].
        apply (HV i). apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
      * apply sub_option_refl.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i G1) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (HG i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

Theorem api_reset_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
    + (* out_of_memory *)
      exists f_out_of_memory. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_out_of_memory = Zstd.proof.harness.frames.FSpecs.f_out_of_memory) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Zstd.proof.harness.frames.FSpecs.G_out_of_memory).
      * exact (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
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
      * apply Zstd.proof.harness.frames.FTransfer.fk_find_all. repeat constructor.
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tsub_G; [apply G0_in_Gprog | apply Gprog_not_var].
Qed.
