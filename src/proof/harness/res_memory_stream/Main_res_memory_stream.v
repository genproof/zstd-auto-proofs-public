(* The harness obligation of res_memory_stream (harness/res_memory_stream.c): for ANY predicates DC, DD of the
   decoder's API (Spec_api6) whose contexts let their own allocator's state be read (dc_cm_ok), the helpers
   count_alloc, count_free (the counting allocator), upto and any_bytes (laws_common.h, proved once in the
   frames kit) and main satisfy their specifications.

   The allocator (CMem): the context gets the struct count of main as its allocator's state, with the ghost
   bound B = ZSTD_estimateDStreamSize(2^windowLogMax) (B0 below; for a window_log zstd refuses the run ends
   before any streaming).  Every allocation of zstd stays within the bound of its context (cm_alloc_spec), the
   counter's peak with it (count_CM), and streaming keeps the bound (set_ss raises it to the estimate of the
   window limit, which it already is).  The check reads count.peak through dc_cm_ok.

   The streaming loop is the one of api_flush_bound: one input object src (n bytes) and one output object dst
   (cap bytes) seen through the same ZSTD_inBuffer / ZSTD_outBuffer; each call sees the prefix in.size of src
   and the prefix out.size of dst, so the two objects are split there for the call and joined after it.  The
   stream stays dictionary-less, in buffered mode, with the parameters set before the loop, and it never
   carries an error into a call (a call that returns an error is followed by ZSTD_DCtx_reset(session_only)). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.res_memory_stream.HOK_res_memory_stream.
Require Zstd.proof.harness.res_memory_stream.Alloc_res_memory_stream.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.

Local Ltac expand_main_pre ::= idtac.

(* the counting allocator of the harness (count_alloc, count_free) as the contexts' allocator *)
Module AL := Zstd.proof.harness.res_memory_stream.Alloc_res_memory_stream.
#[local] Existing Instance AL.count_cm.
Local Notation t_count := AL.t_count.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.res_memory_stream.HOK_res_memory_stream.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).
Local Notation tcm := (Tstruct ___gp_ZSTD_customMem noattr).

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
    (QPprog_vars Zstd.contracts.res_memory_stream.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.res_memory_stream.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.res_memory_stream.whole_prog)).
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

Lemma cm_Z: forall sh (a b c: val) p,
  @data_at ZCS sh tcm (a, (b, c)) p = @data_at HCS sh tcm (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (cce ZCS HCS) sh tcm (a, (b, c)) (a, (b, c))
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

(* a buffer the stream functions are given (Spec_api6.mbuf: NULL allowed for an empty one) at a pointer *)
Lemma mbuf_ptr sh n (c: list val) p : isptr p -> mbuf sh n c p = @data_at ZCS sh (tarray tuchar n) c p.
Proof. intros Hp. unfold mbuf. rewrite if_false; [reflexivity |]. destruct p; try contradiction; discriminate. Qed.

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
  exfalso; match goal with H: ?x <> ?x |- _ => apply H; reflexivity end].

(* ---------- the allocator's bound ---------- *)

(* the window log ZSTD_d_windowLogMax sets (0: the default ZSTD_WINDOWLOG_LIMIT_DEFAULT = 27) *)
Definition wlog (v: Z) : Z := if v =? 0 then 27 else v.

(* the ghost bound of the context's allocator: ZSTD_estimateDStreamSize(2^windowLogMax) (the window log clipped
   to zstd's range, which only matters for a value zstd refuses) *)
Definition B0 (v: Z) : Z := dstream_size (2 ^ Z.max 0 (Z.min 31 (wlog v))).

Lemma B0_range v : dctx_size <= B0 v <= Int64.max_unsigned.
Proof.
  unfold B0, dstream_size, ZSTD_BLOCKSIZE_MAX. rewrite dctx_size_eq.
  assert (0 <= Z.max 0 (Z.min 31 (wlog v)) <= 31) by lia.
  assert (0 < 2 ^ Z.max 0 (Z.min 31 (wlog v)) <= 2 ^ 31).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
  rep_lia.
Qed.

(* the allocator of the context: count_alloc, count_free, the struct count at o, the bound B0 v *)
Definition m0 (gv: globals) (o: val) (v: Z) : cmem :=
  {| cm_alloc := gv _count_alloc; cm_free := gv _count_free; cm_opaque := o; cm_bound := B0 v |}.

(* with the window limit zstd accepted, streaming keeps the allocator as it is *)
Lemma cm_raise_m0 gv o v :
  10 <= wlog v <= 31 -> cm_raise (Some (m0 gv o v)) (2 ^ wlog v) = Some (m0 gv o v).
Proof.
  intros Hw. rewrite cm_raise_bound. unfold m0. simpl. f_equal. f_equal.
  unfold B0. replace (Z.max 0 (Z.min 31 (wlog v))) with (wlog v) by lia. apply Z.max_id.
Qed.

(* main's struct count, both counters 0: the allocator's state with nothing given out *)
Lemma count_init o v :
  data_at Tsh t_count (Vlong (Int64.repr (Int.signed (Int.repr 0))), Vlong (Int64.repr (Int.signed (Int.repr 0)))) o
  |-- CM o (B0 v) 0.
Proof.
  simpl CM. unfold AL.count_CM. Exists 0. pose proof (B0_range v). rewrite dctx_size_eq in H.
  entailer!.
Qed.

(* the allocator's state is main's struct count (what main's return gives back) *)
Lemma CM_count_ o B h : CM o B h |-- data_at_ Tsh t_count o * TT.
Proof. simpl CM. unfold AL.count_CM. Intros peak. sep_apply data_at_data_at_. cancel. Qed.

(* a return of main: the locals back (the allocator's state already as main's struct count) *)
Ltac ret_free :=
  match goal with |- context [data_at Tsh tcm ?x ?p] => sep_apply (data_at_data_at_ Tsh tcm x p) end;
  cancel.

(* ZSTD_d_windowLogMax set on new parameters: the window limit 2^(wlog v), for a v zstd accepts *)
Lemma param_set_wlog v p' : param_set dparams_dflt ZSTD_d_windowLogMax v = Some p' ->
  10 <= wlog v <= 31 /\ dp_wmax p' = 2 ^ wlog v.
Proof.
  unfold param_set. rewrite Z.eqb_refl. fold (wlog v).
  destruct ((10 <=? wlog v) && (wlog v <=? 31))%bool eqn:E; [| discriminate].
  intros Hp. inv Hp. simpl. split; [| reflexivity].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

(* what a stream call keeps of the context and where it leaves the buffers *)
Lemma post_facts st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' :
  stream_post st st' r ob osz opos opos' oc oc' ibs isz ipos ipos' ->
  opos <= opos' <= osz /\ ipos <= ipos' <= isz /\ Zlength oc' = osz /\
  dc_dict st' = dc_dict st /\ dc_set st' = dc_set st /\ dc_bl st' = dc_bl st /\
  dc_stable st' = dc_stable st /\ dc_par st' = dc_par st /\
  dc_mem st' = cm_raise (dc_mem st) (dp_wmax (dc_par st)) /\ ss_err (dc_ss st') = is_error_code r.
Proof.
  unfold stream_post. intros (dl & stall' & a' & HO & HI & HL & _ & _ & _ & _ & _ & _ & _ & Hst & _).
  subst st'. simpl. auto 20.
Qed.

(* ZSTD_DCtx_reset(session_only): a new stream, everything else kept (the allocator's bound raised as by
   any streaming; the flag of a frame decoded before cleared) *)
Lemma reset_facts st :
  dc_dict (set_ex (set_ss st ss_init) false) = dc_dict st /\ dc_set (set_ex (set_ss st ss_init) false) = dc_set st /\
  dc_bl (set_ex (set_ss st ss_init) false) = dc_bl st /\ dc_stable (set_ex (set_ss st ss_init) false) = dc_stable st /\
  dc_par (set_ex (set_ss st ss_init) false) = dc_par st /\
  dc_mem (set_ex (set_ss st ss_init) false) = cm_raise (dc_mem st) (dp_wmax (dc_par st)) /\
  ss_err (dc_ss (set_ex (set_ss st ss_init) false)) = false.
Proof. simpl. auto 10. Qed.

(* the object src again after a call: its prefix of isz bytes and the rest *)
Lemma rejoin_bytes (l: list Z) k : 0 <= k <= Zlength l ->
  zbytes (sublist 0 k l) ++ sublist k (Zlength l) (zbytes l) = zbytes l.
Proof.
  intros Hk. rewrite <- sublist_map. rewrite sublist_rejoin by (rewrite ?Zlength_map; lia).
  apply sublist_same; rewrite ?Zlength_map; lia.
Qed.

(* (size_t) 1 << k *)
Lemma shl_pow k : 0 <= k < 64 -> Int64.shl (Int64.repr 1) (Int64.repr k) = Int64.repr (2 ^ k).
Proof.
  intros Hk. rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia.
  rewrite Int64.mul_commut, Int64.mul_one, two_p_equiv. reflexivity.
Qed.

(* the bound is the estimate of the window limit zstd accepted *)
Lemma B0_wlog v : 10 <= wlog v <= 31 -> B0 v = dstream_size (2 ^ wlog v).
Proof. intros Hw. unfold B0. f_equal. f_equal. lia. Qed.

(* main's struct count again as the allocator's state *)
Lemma CM_fold o B h peak :
  0 <= h -> 0 <= peak <= Int64.max_unsigned -> peak <= B -> (B <= Int64.max_unsigned -> h <= peak) ->
  data_at Tsh t_count (Vlong (Int64.repr h), Vlong (Int64.repr peak)) o * TT |-- CM o B h.
Proof. intros H1 H2 H3 H4. simpl CM. unfold AL.count_CM. Exists peak. entailer!. Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Hypothesis HCM : dc_cm_ok DC.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec');
   ZSTD_isError_spec; ZSTD_createDCtx_advancedP_spec DC; ZSTD_DCtx_setParameter_spec DC;
   ZSTD_decompressStream_spec DC DD; ZSTD_DCtx_reset_spec DC; ZSTD_estimateDStreamSize_spec;
   ZSTD_freeDCtx_spec DC;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec;
   (_count_alloc, cm_alloc_spec); (_count_free, cm_free_spec);
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.res_memory_stream.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward. forward. forward. forward. forward. forward.
  forward_call tt.
  Intros u.
  set (v := Int.signed (Int.repr u)).
  assert_PROP (isptr v_count__1) as Hcp by entailer!.
  make_func_ptr _count_alloc. make_func_ptr _count_free.
  rewrite <- cm_Z.
  sep_apply (count_init v_count__1 v).
  forward_call (gv, Tsh, v_mem, m0 gv v_count__1 v).
  { unfold cm_funs, m0, cmem_val. simpl. entailer!. }
  { simpl. apply B0_range. }
  Intros dctx.
  change (cmem_val (m0 gv v_count__1 v)) with (gv _count_alloc, (gv _count_free, v_count__1)).
  rewrite cm_Z.
  destruct (eq_dec dctx nullval) as [Hn|Hn].
  { subst dctx. Intros.
    repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [| bad].
    change (cm_opaque (m0 gv v_count__1 v)) with v_count__1.
    sep_apply (CM_count_ v_count__1 (cm_bound (m0 gv v_count__1 v)) 0).
    forward. ret_free. }
  pose proof (isptr_of dctx PNdctx Hn) as Hdp.
  destruct dctx as [| | | | | bz oz]; try contradiction.
  set (dctx := Vptr bz oz) in *.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |].
  sep_apply (drop_vp (DC gv dctx (dctx_init_m (m0 gv v_count__1 v))) dctx).
  replace (Vint (Int.repr u)) with (Vint (Int.repr v)) by (unfold v; rewrite Int.repr_signed; reflexivity).
  forward_call (gv, dctx, dctx_init_m (m0 gv v_count__1 v), ZSTD_d_windowLogMax, v).
  { simpl; auto. }
  Intros vret. destruct vret as [r st1]. cbn [fst snd] in *.
  apply after_stage_init in H2; [| reflexivity]. unfold setpar_res in H2.
  change (ZSTD_d_windowLogMax =? ZSTD_d_stableOutBuffer) with false in H2. cbv iota in H2.
  change (dc_par (dctx_init_m (m0 gv v_count__1 v))) with dparams_dflt in H2.
  forward_call r.
  destruct (param_set dparams_dflt ZSTD_d_windowLogMax v) as [p'|] eqn:Ep.
  2: { (* a window log zstd refuses: the run ends *)
    destruct H2 as [He ->]. rewrite He. forward. forward_if; [| bad].
    sep_apply (HCM gv dctx (dctx_init_m (m0 gv v_count__1 v)) (m0 gv v_count__1 v) eq_refl).
    Intros h. change (cm_opaque (m0 gv v_count__1 v)) with v_count__1.
    sep_apply (CM_count_ v_count__1 (cm_bound (m0 gv v_count__1 v)) h).
    forward. ret_free. }
  destruct H2 as [-> ->]. destruct (param_set_wlog v p' Ep) as [Hw Hpw].
  replace (is_error_code 0) with false by reflexivity.
  forward. forward_if; [bad |].
  set (st1 := set_par (dctx_init_m (m0 gv v_count__1 v)) p').
  assert (Hm1: dc_mem st1 = Some (m0 gv v_count__1 v)) by reflexivity.
  forward_call 9223372036854775807.
  Intros n.
  forward_call 9223372036854775807.
  Intros cap.
  forward_call (gv, n).
  Intros vret. destruct vret as [src l]. cbn [fst snd] in *.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros dst.
  unfold FSpecs.mbytes.
  (* src or dst NULL: the run ends *)
  destruct (eq_dec src nullval) as [Hs|Hs].
  { subst src. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| bad]. forward.
    forward_if; [| bad].
    sep_apply (HCM gv dctx st1 (m0 gv v_count__1 v) Hm1).
    Intros h. change (cm_opaque (m0 gv v_count__1 v)) with v_count__1.
    sep_apply (CM_count_ v_count__1 (cm_bound (m0 gv v_count__1 v)) h).
    forward. ret_free. }
  Intros.
  destruct (eq_dec dst nullval) as [Hd|Hd].
  { subst dst. repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
    forward_if; [| bad].
    sep_apply (HCM gv dctx st1 (m0 gv v_count__1 v) Hm1).
    Intros h. change (cm_opaque (m0 gv v_count__1 v)) with v_count__1.
    sep_apply (CM_count_ v_count__1 (cm_bound (m0 gv v_count__1 v)) h).
    forward. ret_free. }
  Intros.
  assert_PROP (isptr dst) as Hdp' by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [bad |]. forward.
  forward_if; [bad |].
  set (dst := Vptr bd od) in *.
  assert_PROP (isptr src) as Hsp by entailer!.
  forward. forward. forward. forward. forward.
  (* the two objects at the decoder's compspecs *)
  sep_apply (to_Z Ews n (zbytes l) src). sep_apply (tok_to_Z Ews n src).
  sep_apply (to_Z_ Ews cap dst). sep_apply (tok_to_Z Ews cap dst).
  rewrite (@data_at__eq ZCS).
  set (m := m0 gv v_count__1 v) in *.
  assert (Hraise: cm_raise (Some m) (2 ^ wlog v) = Some m) by (apply cm_raise_m0; exact Hw).
  forward_loop
    (EX st: dctx_st, EX isz: Z, EX ipos: Z, EX opos: Z, EX osv: val, EX oc: list val,
     PROP (0 <= ipos <= isz; isz <= n; 0 <= opos <= cap; Zlength oc = cap;
           dc_dict st = None; dc_set st = nil; dc_bl st = None; dc_stable st = false; ss_err (dc_ss st) = false;
           dc_par st = p'; dc_mem st = Some m)
     LOCAL (temp _dctx dctx; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
            temp _n (Vlong (Int64.repr n)); temp _window_log (Vint (Int.repr v));
            lvar _out tout v_out; lvar _in tin v_in; lvar _mem tcm v_mem; lvar _count__1 t_count v_count__1;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
          @data_at ZCS Ews (tarray tuchar n) (zbytes l) src; @malloc_token ZCS Ews (tarray tuchar n) src;
          @data_at ZCS Ews (tarray tuchar cap) oc dst; @malloc_token ZCS Ews (tarray tuchar cap) dst;
          data_at Tsh tin (src, (Vlong (Int64.repr isz), Vlong (Int64.repr ipos))) v_in;
          data_at Tsh tout (dst, (osv, Vlong (Int64.repr opos))) v_out;
          data_at Tsh tcm (gv _count_alloc, (gv _count_free, v_count__1)) v_mem; TT))%assert
    break:
    (EX st: dctx_st,
     PROP (dc_par st = p'; dc_mem st = Some m)
     LOCAL (temp _dctx dctx; temp _window_log (Vint (Int.repr v));
            lvar _out tout v_out; lvar _in tin v_in; lvar _mem tcm v_mem; lvar _count__1 t_count v_count__1;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
          data_at Tsh tcm (gv _count_alloc, (gv _count_free, v_count__1)) v_mem;
          data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; TT))%assert.
  { Exists st1 0 0 0 (fst (snd (default_val tout))) (@default_val ZCS (tarray tuchar cap)). entailer!. }
  2: { (* after the loop: the check, then the context freed *)
    Intros st.
    forward_if (PROP () LOCAL (temp _t'17 (Vint (Int.repr (wlog v))); temp _dctx dctx;
                               lvar _out tout v_out; lvar _in tin v_in; lvar _mem tcm v_mem;
                               lvar _count__1 t_count v_count__1; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st;
           data_at Tsh tcm (gv _count_alloc, (gv _count_free, v_count__1)) v_mem;
           data_at_ Tsh tin v_in; data_at_ Tsh tout v_out; TT)).
    { forward. entailer!. rewrite H11. reflexivity. }
    { forward. entailer!. unfold wlog. rewrite (proj2 (Z.eqb_neq _ _) H11). reflexivity. }
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    change (Int.signed (Int.repr 1)) with 1. rewrite Int.unsigned_repr by rep_lia.
    rewrite (shl_pow (wlog v)) by lia.
    forward_call (2 ^ wlog v).
    { split; [apply Z.pow_nonneg; lia | apply Z.pow_le_mono_r; lia]. }
    (* the counter, read through the context *)
    sep_apply (HCM gv dctx st m H10). Intros h.
    change (cm_opaque m) with v_count__1. change (cm_bound m) with (B0 v).
    simpl CM. unfold AL.count_CM. Intros peak.
    change (@data_at AL.CompSpecs) with (@data_at HCS).
    forward.
    pose proof (B0_wlog v Hw) as EB. pose proof (B0_range v) as RB.
    forward_call (Int.one).
    { entailer!. rewrite <- EB. unfold Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
    sep_apply (CM_fold v_count__1 (B0 v) h peak); try assumption.
    sep_apply (wand_frame_elim (CM v_count__1 (B0 v) h) (DC gv dctx st)).
    forward_call (gv, dctx, Some st).
    unfold cm_back. rewrite H10. Intros.
    change (cm_opaque m) with v_count__1.
    sep_apply (CM_count_ v_count__1 (cm_bound m) 0).
    forward. ret_free. }
  Intros st isz ipos opos osv oc.
  (* in.size and out.size of the call *)
  forward. forward_call (n - isz). Intros a. forward. forward.
  forward. forward_call (cap - opos). Intros b. forward. forward.
  replace (Int64.add (Int64.repr isz) (Int64.repr a)) with (Int64.repr (isz + a))
    by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
  replace (Int64.add (Int64.repr opos) (Int64.repr b)) with (Int64.repr (opos + b))
    by (rewrite Int64.add_unsigned, !Int64.unsigned_repr by rep_lia; reflexivity).
  set (isz2 := isz + a). set (osz := opos + b).
  (* the call sees the prefixes; the rests are its buffer witnesses *)
  assert_PROP (@field_compatible ZCS (tarray tuchar n) [] src) as Fs by entailer!.
  assert_PROP (@field_compatible ZCS (tarray tuchar cap) [] dst) as Fd by entailer!.
  rewrite (arr_split Ews n isz2 (zbytes l) src Fs) by (try rewrite Zlength_map; lia).
  rewrite (arr_split Ews cap osz oc dst Fd) by lia.
  rewrite (sublist_map _ 0 isz2 l).
  sep_apply (wits_fold n isz2 (sublist isz2 n (zbytes l)) src cap osz (sublist osz cap oc) dst).
  rewrite <- in_Z, <- out_Z.
  rewrite (DC_res DC DD gv dctx st Ews H13 H14).
  rewrite <- (mbuf_ptr Ews osz (sublist 0 osz oc) dst) by exact Hdp'.
  rewrite <- (mbuf_ptr Ews isz2 (zbytes (sublist 0 isz2 l)) src) by exact Hsp.
  forward_call (wits n isz2 (sublist isz2 n (zbytes l)) src cap osz (sublist osz cap oc) dst,
                gv, dctx, st, v_out, v_in, Tsh, Tsh, Ews, dst, osz, opos, sublist 0 osz oc,
                Ews, src, isz2, ipos, sublist 0 isz2 l).
  { cancel. }
  { split; [| split; [| split; [| split; [| split]]]].
    - apply (buf_ok_pre _ Ews cap osz (sublist osz cap oc) dst); [simpl; tauto | simpl; tauto | lia | auto | auto].
    - apply (buf_ok_pre _ Ews n isz2 (sublist isz2 n (zbytes l)) src); [simpl; tauto | simpl; tauto | lia | auto | auto].
    - apply stream_dict_ok_none; auto.
    - rewrite Zlength_sublist; lia.
    - rewrite Zlength_sublist; lia.
    - apply bytes_ok_sublist; auto. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *.
  destruct (post_facts _ _ _ _ _ _ _ _ _ _ _ _ _ H23)
    as (HO & HI & HL & Ed & Es & Eb & Est & Ep' & Em & Ee).
  rewrite H19, H18, Hpw, Hraise in Em. rewrite H18 in Ep'.
  rewrite H13, H14 in *. rewrite H15 in Eb. rewrite H16 in Est.
  change (dict_res DD gv Ews None) with (@emp mpred _ _).
  change (set_res DD gv Ews [] None) with (@emp mpred _ _).
  sep_apply (drop_vp (DC gv dctx st') dctx).
  rewrite (mbuf_ptr Ews osz oc' dst) by exact Hdp'.
  rewrite (mbuf_ptr Ews isz2 (zbytes (sublist 0 isz2 l)) src) by exact Hsp.
  sep_apply (wits_unfold n isz2 (sublist isz2 n (zbytes l)) src cap osz (sublist osz cap oc) dst).
  sep_apply (arr_join Ews n isz2 (zbytes (sublist 0 isz2 l)) (sublist isz2 n (zbytes l)) src Fs).
  all: match goal with |- Zlength _ = _ => list_solve | |- _ <= _ <= _ => lia | _ => idtac end.
  sep_apply (arr_join Ews cap osz oc' (sublist osz cap oc) dst Fd).
  all: match goal with |- Zlength _ = _ => list_solve | |- _ <= _ <= _ => lia | _ => idtac end.
  replace (zbytes (sublist 0 isz2 l) ++ sublist isz2 n (zbytes l)) with (zbytes l)
    by (subst n; symmetry; apply rejoin_bytes; lia).
  rewrite in_Z, out_Z.
  forward_call r.
  forward_if
    (EX st'': dctx_st,
     PROP (dc_dict st'' = None; dc_set st'' = nil; dc_bl st'' = None; dc_stable st'' = false;
           ss_err (dc_ss st'') = false; dc_par st'' = p'; dc_mem st'' = Some m)
     LOCAL (temp _dctx dctx; temp _dst dst; temp _src src; temp _cap (Vlong (Int64.repr cap));
            temp _n (Vlong (Int64.repr n)); temp _window_log (Vint (Int.repr v));
            lvar _out tout v_out; lvar _in tin v_in; lvar _mem tcm v_mem; lvar _count__1 t_count v_count__1;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st'';
          @data_at ZCS Ews (tarray tuchar n) (zbytes l) src; @malloc_token ZCS Ews (tarray tuchar n) src;
          @data_at ZCS Ews (tarray tuchar cap) (oc' ++ sublist osz cap oc) dst;
          @malloc_token ZCS Ews (tarray tuchar cap) dst;
          data_at Tsh tin (src, (Vlong (Int64.repr isz2), Vlong (Int64.repr ipos'))) v_in;
          data_at Tsh tout (dst, (Vlong (Int64.repr osz), Vlong (Int64.repr opos'))) v_out;
          data_at Tsh tcm (gv _count_alloc, (gv _count_free, v_count__1)) v_mem; TT))%assert.
  { (* an error: a session reset *)
    forward_call (gv, dctx, st', ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [_ ->] end.
    destruct (reset_facts st') as (Rd & Rs & Rb & Rst & Rp & Rm & Re).
    rewrite Em, Ep', Hpw, Hraise in Rm. rewrite Ep' in Rp.
    Exists (set_ex (set_ss st' ss_init) false). entailer!. }
  { forward. Exists st'. entailer!.
    destruct (is_error_code r); [discriminate | auto]. }
  Intros st''.
  forward_call tt. Intros c.
  forward_if.
  { forward. Exists st'' isz2 ipos' opos' (Vlong (Int64.repr osz)) (oc' ++ sublist osz cap oc).
    entailer!. }
  { forward. Exists st''. entailer!. }
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)


(* the harness's own functions besides main (in the order of helper_ids): the counting allocator, and the
   frames kit's any_bytes and upto (laws_common.h) *)
Definition Hs : funspecs :=
  [(_count_alloc, cm_alloc_spec); (_count_free, cm_free_spec);
   @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec].
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
                       (_count_alloc, cm_alloc_spec); (_count_free, cm_free_spec);
                       @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
                       Zstd.proof.harness.frames.FSpecs.upto_spec; main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma sub_in_Gprog DC DD (G: funspecs) :
  Forall (fun ix => initial_world.find_id (fst ix) (Gprog (Specs_api DC DD) Hs) = Some (snd ix)) G ->
  forall i fs, initial_world.find_id i G = Some fs -> initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs.
Proof. apply Zstd.proof.harness.frames.FTransfer.fk_find_all. Qed.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs.
Proof.
  apply sub_in_Gprog. unfold G0. repeat constructor; in_gprog.
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

(* a body proved in a smaller context holds in a larger one whose functions are no global variables *)
Lemma body_sub (V: varspecs) (G1 G2: funspecs) f spec :
  semax_body V G1 f spec ->
  (forall i fs, initial_world.find_id i G1 = Some fs -> initial_world.find_id i G2 = Some fs) ->
  (forall i, In i (map fst G2) -> ~ In i (map fst V)) ->
  semax_body V G2 f spec.
Proof.
  intros B HG HV.
  eapply semax_body_subsumption; [exact B |].
  apply tycontext_sub_i99. split; intro i.
  - rewrite (make_tycontext_g_find V G1 i).
    rewrite (make_tycontext_g_find V G2 i).
    destruct (initial_world.find_id i G1) as [fs|] eqn:E.
    + rewrite (HG i fs E). apply sub_option_refl.
    + destruct (initial_world.find_id i G2) as [fs'|] eqn:E'.
      * rewrite mtg_none; [exact Logic.I |].
        apply (HV i).
        apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
      * apply sub_option_refl.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i G1) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (HG i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

Lemma body_in_Gprog DC DD (G: funspecs) f spec :
  semax_body Vprog G f spec ->
  (forall i fs, initial_world.find_id i G = Some fs -> initial_world.find_id i (Gprog (Specs_api DC DD) Hs) = Some fs) ->
  semax_body Vprog (Gprog (Specs_api DC DD) Hs) f spec.
Proof. intros B HG. exact (body_sub Vprog G _ f spec B HG (Gprog_not_var DC DD)). Qed.

(* the harness's obligation for a decoder whose contexts let their allocator's state be read *)
Theorem res_memory_stream_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    dc_cm_ok DC -> exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD HCM. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]]].
    + (* count_alloc *)
      exists f_count_alloc. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD AL.G_alloc).
      * exact AL.body_count_alloc.
      * apply sub_in_Gprog. repeat constructor; in_gprog.
    + (* count_free *)
      exists f_count_free. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD AL.G_alloc).
      * exact AL.body_count_free.
      * apply sub_in_Gprog. repeat constructor; in_gprog.
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
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      apply (body_in_Gprog DC DD (G0 DC DD)); [apply (body_main_G0 DC DD HCM) | apply G0_in_Gprog].
Qed.
