(* The harness obligation of api_split_invariant (harness/api_split_invariant.c), for ANY predicates DC, DD of the
   decoder's API (Spec_api6.Specs_api, with ZSTD_XXH64_spec: new_frame hashes its content): the helpers of
   laws_common.h and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main sets windowLogMax on a new stream, builds a series of new_frame frames (windows of at most max_window =
   2^windowLogMax, or STREAM_WINDOW for 0) and skippable frames (SI_Model.si_series), and decodes it with one
   ZSTD_decompress call and with stream_all.  SI_Model.si_decode: both models (one-shot, and the stream with the
   context's window limit) decode it to the same content C; ZSTD_decompress then returns |C| with C in its
   output, or an error with cap < |C| or out of memory (oneshot_ok); SI_Stream.si_stream says how the stream
   ends.  Each gp_assert follows. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Pick.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_split_invariant.HOK_api_split_invariant.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
Require Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FStreamSpec.
Require Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FBodyNewFrame.
Require Zstd.proof.harness.frames.FBodyStreamAll.
Require Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.api_split_invariant.SI_Model Zstd.proof.harness.api_split_invariant.SI_Stream.
Local Open Scope logic.

Local Ltac expand_main_pre ::= idtac.

(* Spec_api6 (through FStreamSpec) exports the decoder's Base.Vprog, Base.CompSpecs and Gprog.Gprog, which shadow
   the harness unit's names of HOK_api_split_invariant: those are written H.* below *)
Module H := Zstd.proof.harness.api_split_invariant.HOK_api_split_invariant.
Module C := Zstd.harness.api_split_invariant.code.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := H.CompSpecs.

(* ---------- main's precondition ---------- *)

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
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g H.Vprog G)))
    (QPprog_vars Zstd.contracts.api_split_invariant.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold H.Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of programs has the x_ laws
   only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_split_invariant.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs
                   (Vardefs Zstd.contracts.api_split_invariant.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at HCS sh (tarray tuchar n) v p |-- @data_at ZCS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs HCS ZCS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at ZCS sh (tarray tuchar n) v p |-- @data_at HCS sh (tarray tuchar n) v p.
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

Lemma tok_of_Z sh n p :
  @malloc_token ZCS sh (tarray tuchar n) p |-- @malloc_token HCS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any HCS ZCS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

(* 1 << k in 64 bits *)
Lemma shl1 k : 0 <= k < 64 -> Int64.shl (Int64.repr (Int.signed (Int.repr 1))) (Int64.repr k) = Int64.repr (2 ^ k).
Proof.
  intros Hk. change (Int.signed (Int.repr 1)) with 1.
  rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia. rewrite two_p_equiv.
  rewrite Int64.mul_commut. apply Int64.mul_one.
Qed.

(* ---------- the data array and new_frame's piece data[done .. done + k) ---------- *)

(* a byte array in three parts *)
Lemma split3 {cs: compspecs} sh n a b (l: list Z) p : 0 <= a <= b -> b <= n -> Zlength l = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (zbytes l) p =
  data_at sh (tarray tuchar a) (zbytes (sublist 0 a l)) p *
  data_at sh (tarray tuchar (b - a)) (zbytes (sublist a b l)) (offset_val a p) *
  data_at sh (tarray tuchar (n - b)) (zbytes (sublist b n l)) (offset_val b p).
Proof.
  intros Hab Hb Hl FC. unfold tarray.
  rewrite (split3_data_at_Tarray_tuchar sh n a b) by (try rewrite Zlength_map; lia).
  rewrite !field_address0_offset by auto with field_compatible.
  simpl nested_field_offset. rewrite !Z.add_0_l, !Z.mul_1_l.
  rewrite !sublist_map. reflexivity.
Qed.

(* the witness new_frame gets for its data pointer data + done when the piece is empty: the whole data array
   (n > 0) or the malloc_token of the empty block (n = 0) *)
Definition nf_w (n k: Z) (l: list Z) (data: val) : Zstd.proof.zstd.Spec_xxh.ptr_witness :=
  if zlt 0 k then Zstd.proof.zstd.Spec_xxh.pw_none
  else if zlt 0 n then Zstd.proof.zstd.Spec_xxh.pw_bytes Ews n (zbytes l) data
  else Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar 0) data.

(* the rest of the data array's resources during the call *)
Definition nf_rest (n k done: Z) (l: list Z) (data: val) : mpred :=
  !! field_compatible (tarray tuchar n) [] data &&
  if zlt 0 k then
    @malloc_token HCS Ews (tarray tuchar n) data *
    @data_at HCS Ews (tarray tuchar done) (zbytes (sublist 0 done l)) data *
    @data_at HCS Ews (tarray tuchar (n - (done + k))) (zbytes (sublist (done + k) n l)) (offset_val (done + k) data)
  else if zlt 0 n then @malloc_token HCS Ews (tarray tuchar n) data
  else emp.

Lemma nf_pre n k done l data : 0 <= done -> 0 <= k -> done + k <= n -> Zlength l = n ->
  @malloc_token HCS Ews (tarray tuchar n) data * @data_at HCS Ews (tarray tuchar n) (zbytes l) data |--
  @data_at HCS Ews (tarray tuchar (Zlength (sublist done (done + k) l))) (zbytes (sublist done (done + k) l))
    (offset_val done data) *
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_w n k l data) * nf_rest n k done l data.
Proof.
  intros Hd Hk Hn Hl.
  assert_PROP (field_compatible (tarray tuchar n) [] data) as FC by entailer!.
  assert (Hp: isptr data) by (destruct FC; auto).
  rewrite Zlength_sublist by lia. unfold nf_w, nf_rest.
  rewrite sepcon_andp_prop. apply andp_right; [apply prop_right; exact FC |].
  destruct (zlt 0 k) as [Hk0|Hk0].
  - rewrite (split3 Ews n done (done + k) l data) by (auto; lia).
    replace (done + k - done) with k by lia.
    simpl Zstd.proof.zstd.Spec_xxh.pw_pred. cancel.
  - assert (k = 0) by lia. subst k. rewrite Z.add_0_r, Z.sub_diag, sublist_nil.
    destruct (zlt 0 n) as [Hn0|Hn0].
    + simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
      eapply derives_trans with (@data_at HCS Ews (tarray tuchar 0) (zbytes []) (offset_val done data) *
        (@malloc_token HCS Ews (tarray tuchar n) data * @data_at HCS Ews (tarray tuchar n) (zbytes l) data)).
      { rewrite <- (emp_sepcon (_ * _)) at 1. apply sepcon_derives; [| apply derives_refl].
        apply data_at_tuchar_zero_array. destruct data; try contradiction; exact I. }
      sep_apply (to_Z Ews n (zbytes l) data). cancel.
    + assert (Hl0: l = []) by (apply Zlength_nil_inv; lia). subst l. rewrite Zlength_nil in *.
      assert (n = 0) by lia. subst n. assert (done = 0) by lia. subst done.
      simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
      rewrite isptr_offset_val_zero by exact Hp.
      sep_apply (tok_to_Z Ews 0 data). cancel; apply derives_refl.
Qed.

Lemma nf_post n k done l d' data : 0 <= done -> 0 <= k -> done + k <= n -> Zlength l = n -> Zlength d' = k ->
  @data_at HCS Ews (tarray tuchar (Zlength (sublist done (done + k) l))) (zbytes d') (offset_val done data) *
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_w n k l data) * nf_rest n k done l data |--
  @malloc_token HCS Ews (tarray tuchar n) data *
  @data_at HCS Ews (tarray tuchar n) (zbytes (sublist 0 done l ++ d' ++ sublist (done + k) n l)) data.
Proof.
  intros Hd Hk Hn Hl Hd'.
  rewrite Zlength_sublist by lia. replace (done + k - done) with k by lia. unfold nf_w, nf_rest.
  rewrite sepcon_andp_prop. apply derives_extract_prop. intros FC.
  assert (Hp: isptr data) by (destruct FC; auto).
  set (l' := sublist 0 done l ++ d' ++ sublist (done + k) n l).
  assert (Hl': Zlength l' = n) by (unfold l'; rewrite !Zlength_app, !Zlength_sublist by lia; lia).
  destruct (zlt 0 k) as [Hk0|Hk0].
  - simpl Zstd.proof.zstd.Spec_xxh.pw_pred. rewrite sepcon_emp.
    rewrite (split3 Ews n done (done + k) l' data) by (auto; lia).
    replace (done + k - done) with k by lia.
    assert (E1: sublist 0 done l' = sublist 0 done l) by (unfold l'; list_solve).
    assert (E2: sublist done (done + k) l' = d') by (unfold l'; list_solve).
    assert (E3: sublist (done + k) n l' = sublist (done + k) n l) by (unfold l'; list_solve).
    rewrite E1, E2, E3.
    cancel.
  - assert (Ek: k = 0) by lia. subst k. assert (Hd0: d' = []) by (apply Zlength_nil_inv; lia). subst d'.
    unfold l'. rewrite app_nil_l, Z.add_0_r, sublist_rejoin, sublist_same by lia.
    destruct (zlt 0 n) as [Hn0|Hn0].
    + simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
      sep_apply (data_at_tuchar_zero_array_inv Ews (offset_val done data)). rewrite emp_sepcon.
      sep_apply (of_Z Ews n (zbytes l) data). cancel.
    + assert (Hl0: l = []) by (apply Zlength_nil_inv; lia). subst l. rewrite Zlength_nil in *.
      assert (n = 0) by lia. subst n. assert (done = 0) by lia. subst done.
      simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
      rewrite isptr_offset_val_zero by exact Hp. rewrite sepcon_emp.
      sep_apply (tok_of_Z Ews 0 data). cancel.
Qed.

(* the witness makes data + done weakly valid when the piece is empty *)
Lemma nf_w_valid n k done l data : 0 <= done -> 0 <= k -> done + k <= n -> Zlength l = n -> isptr data ->
  Zlength (sublist done (done + k) l) = 0 ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (nf_w n k l data) |-- weak_valid_pointer (offset_val done data).
Proof.
  intros Hd Hk Hn Hl Hp H0. rewrite Zlength_sublist in H0 by lia. unfold nf_w.
  destruct (zlt 0 k) as [Hk0|Hk0]; [lia |].
  destruct (zlt 0 n) as [Hn0|Hn0].
  - simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    eapply derives_trans; [apply data_at_memory_block |].
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
  - assert (done = 0) by lia. subst done. rewrite isptr_offset_val_zero by exact Hp.
    simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

(* ---------- the buffer witnesses of the decoder's calls: the malloc_tokens of the buffers ---------- *)

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

(* the two size_t cells stream_all writes, between the compspecs *)
Lemma ulong__to_Z sh p : @data_at_ HCS sh tulong p |-- @data_at_ ZCS sh tulong p.
Proof. rewrite (Zstd.proof.harness.frames.FBodyStreamAll.sa_ulong__cs HCS ZCS). apply derives_refl. Qed.

Lemma ulong_of_Z sh v p : @data_at ZCS sh tulong v p |-- @data_at HCS sh tulong v p.
Proof. rewrite (Zstd.proof.harness.frames.FBodyStreamAll.sa_ulong_cs ZCS HCS). apply derives_refl. Qed.

Lemma ulong_of_Z_ sh v p : @data_at ZCS sh tulong v p |-- @data_at_ HCS sh tulong p.
Proof. sep_apply (ulong_of_Z sh v p). apply data_at_data_at_. Qed.

(* error_of of ZSTD_error_memory_allocation's code *)
Lemma error_of_mem : Zstd.proof.zstd.Spec_util.error_of (2 ^ 64 - ZSTD_error_memory_allocation) = 64.
Proof. reflexivity. Qed.

Lemma eq64_false a : 0 <= a <= Int64.max_unsigned -> a <> 0 -> Int64.eq (Int64.repr a) (Int64.repr 0) = false.
Proof.
  intros Ha Hn. apply Int64.eq_false. intro E.
  apply (f_equal Int64.unsigned) in E. rewrite !Int64.unsigned_repr in E by rep_lia. lia.
Qed.

(* the content of a series is made of bytes *)
Lemma si_series_content_ok maxw S C : si_series maxw S C -> bytes_ok C.
Proof.
  induction 1; [constructor | apply Forall_app; split; auto; eapply nf_data_ok; eauto | auto].
Qed.

(* a branch of an if that the values in the context exclude *)
Ltac dead_branch :=
  exfalso;
  first [ exact (Int.one_not_zero ltac:(assumption))
        | match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end
        | match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end
        | discriminate | contradiction ].

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the API of the law *)
Definition API : funspecs := Specs_api DC DD ++ [Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main, in the order of helper_ids *)
Definition Hs : funspecs :=
  [out_of_memory_spec; copy_of_spec; @stream_all_spec CompSpecs DC DD; any_bytes_spec; upto_spec; put_le_spec;
   join_spec; bytes_eq_spec; new_skippable_spec; new_frame_spec].

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec');
   ZSTD_isError_spec; ZSTD_decompress_spec; ZSTD_createDStream_spec DC; ZSTD_DCtx_setParameter_spec DC;
   nondet_u8_spec; nondet_u32_spec; gp_assert_spec;
   out_of_memory_spec; @stream_all_spec CompSpecs DC DD; any_bytes_spec; upto_spec; join_spec; bytes_eq_spec;
   new_skippable_spec; new_frame_spec].

(* a stream without dictionary or DDict set: the dictionary resources of its calls are emp *)
Lemma DC_res_none gv d st0 : dc_dict st0 = None -> dc_set st0 = nil ->
  DC gv d st0 = (DC gv d st0 * dict_res DD gv Ews (dc_dict st0) * set_res DD gv Ews (dc_set st0) (dc_dict st0))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma body_main_G0 (HST: si_stream_stmt) (HDE: si_decode_stmt) : semax_body H.Vprog G0 f_main main_spec.
Proof.
  change (semax_body H.Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_split_invariant.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call tt.
  Intros u32.
  set (wl := Int.signed (Int.repr u32)).
  assert (Ewl: Int.repr u32 = Int.repr wl) by (unfold wl; rewrite Int.repr_signed; reflexivity).
  assert (Rwl: Int.min_signed <= wl <= Int.max_signed) by (apply Int.signed_range).
  rewrite Ewl. clearbody wl.
  forward_call gv.
  Intros zds.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { subst zds. forward_if; [| contradiction]. forward.
    forward_if; [forward; cancel | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  forward_if; [contradiction |].
  Intros.
  sep_apply (andp_left1 (DC gv zds dctx_init) (valid_pointer zds) (DC gv zds dctx_init) (derives_refl _)).
  forward_call (gv, zds, dctx_init, ZSTD_d_windowLogMax, wl).
  { simpl; auto. }
  Intros vret. destruct vret as [r0 st]. cbn [fst snd] in *.
  apply after_stage_init in H2; [| reflexivity]. unfold setpar_res in H2.
  change (ZSTD_d_windowLogMax =? ZSTD_d_stableOutBuffer) with false in H2.
  unfold param_set in H2. change (ZSTD_d_windowLogMax =? ZSTD_d_windowLogMax) with true in H2.
  cbv beta iota zeta in H2.
  set (v' := if wl =? 0 then 27 else wl) in H2.
  forward_call r0.
  destruct ((10 <=? v') && (v' <=? 31))%bool eqn:Acc.
  2: { destruct H2 as [Er ->]. rewrite Er. forward.
       forward_if; [forward; cancel | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  destruct H2 as [-> ->].
  forward.
  forward_if; [exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end |].
  match goal with |- context [DC gv zds ?x] => set (st := x) end.
  assert (Hv': 10 <= v' <= 31) by (apply andb_prop in Acc; destruct Acc as [A1 A2]; apply Z.leb_le in A1, A2; lia).
  forward_if (PROP () LOCAL (temp C._t'6 (Vlong (Int64.repr (2 ^ v'))); temp C._zds zds;
      lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; data_at_ Tsh tulong v_completed;
         data_at_ Tsh tulong v_written; data_at_ Tsh tulong v_len; TT; has_ext tt)).
  { forward. entailer!. }
  { assert (Ev: v' = wl)
      by (match goal with Hx: wl <> 0 |- _ => unfold v'; rewrite (proj2 (Z.eqb_neq _ _) Hx); reflexivity end).
    forward.
    { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    rewrite Int.unsigned_repr by rep_lia. rewrite shl1 by lia. rewrite <- Ev. entailer!. }
  forward.
  forward_call 9223372036854775807.
  Intros n.
  forward. forward.
  forward_call (gv, n).
  Intros vret. destruct vret as [data l]. cbn [fst snd] in *.
  forward.
  destruct (eq_dec data nullval) as [Hdn|Hdn].
  { subst data. forward_if; [forward; cancel | contradiction]. }
  unfold mbytes. rewrite if_false by exact Hdn. Intros.
  assert_PROP (isptr data) as Pdata by entailer!.
  forward_if; [contradiction |].
  set (maxw := 2 ^ v') in *.
  assert (Hmw: 2 ^ 10 <= maxw <= 2 ^ 31) by (unfold maxw; split; apply Z.pow_le_mono_r; lia).
  (* the series loop: the series S built so far, its content Cc, the data array's cells l1 *)
  forward_loop
    (EX done: Z, EX S: list Z, EX Cc: list Z, EX sp: val, EX l1: list Z,
     PROP (si_series maxw S Cc; 0 <= done <= n; Zlength S <= PTRDIFF_MAX; Zlength l1 = n; bytes_ok l1;
           bytes_ok S)
     LOCAL (temp C._done (Vlong (Int64.repr done)); temp C._series_len (Vlong (Int64.repr (Zlength S)));
            temp C._series sp; temp C._data data; temp C._n (Vlong (Int64.repr n));
            temp C._max_window (Vlong (Int64.repr maxw)); temp C._zds zds;
            lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; @mbytes HCS (Zlength S) S sp;
          @malloc_token HCS Ews (tarray tuchar n) data; @data_at HCS Ews (tarray tuchar n) (zbytes l1) data;
          data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; data_at_ Tsh tulong v_len; TT;
          has_ext tt))
  continue:
    (EX done: Z, EX S: list Z, EX Cc: list Z, EX sp: val, EX l1: list Z,
     PROP (si_series maxw S Cc; 0 <= done <= n; Zlength S <= PTRDIFF_MAX; Zlength l1 = n; bytes_ok l1;
           bytes_ok S; S <> []; sp <> nullval)
     LOCAL (temp C._done (Vlong (Int64.repr done)); temp C._series_len (Vlong (Int64.repr (Zlength S)));
            temp C._series sp; temp C._data data; temp C._n (Vlong (Int64.repr n));
            temp C._max_window (Vlong (Int64.repr maxw)); temp C._zds zds;
            lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; @mbytes HCS (Zlength S) S sp;
          @malloc_token HCS Ews (tarray tuchar n) data; @data_at HCS Ews (tarray tuchar n) (zbytes l1) data;
          data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; data_at_ Tsh tulong v_len; TT;
          has_ext tt))
  break:
    (EX done: Z, EX S: list Z, EX Cc: list Z, EX sp: val, EX l1: list Z,
     PROP (si_series maxw S Cc; 0 <= done <= n; Zlength S <= PTRDIFF_MAX; Zlength l1 = n; bytes_ok l1;
           bytes_ok S; S <> []; sp <> nullval)
     LOCAL (temp C._done (Vlong (Int64.repr done)); temp C._series_len (Vlong (Int64.repr (Zlength S)));
            temp C._series sp; temp C._data data; temp C._n (Vlong (Int64.repr n));
            temp C._max_window (Vlong (Int64.repr maxw)); temp C._zds zds;
            lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; @mbytes HCS (Zlength S) S sp;
          @malloc_token HCS Ews (tarray tuchar n) data; @data_at HCS Ews (tarray tuchar n) (zbytes l1) data;
          data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; data_at_ Tsh tulong v_len; TT;
          has_ext tt)).
  { Exists 0 (@nil Z) (@nil Z) nullval l. unfold mbytes. rewrite if_true by reflexivity. entailer!.
    split; [constructor | split; [rewrite Zlength_nil; unfold PTRDIFF_MAX; lia | constructor]]. }
  { (* one iteration: a frame, joined to the series *)
    Intros done S Cc sp l1.
    forward.
    forward_call tt.
    Intros b8.
    forward_if
     (EX piece: Z, EX fp: val, EX F: list Z, EX X: list Z, EX l2: list Z,
      PROP (0 <= piece <= n - done; Zlength l2 = n; bytes_ok l2;
            fp <> nullval -> bytes_ok F /\ Zlength F <= PTRDIFF_MAX /\ si_series maxw (S ++ F) (Cc ++ X) /\ F <> [])
      LOCAL (temp C._frame fp; temp C._piece (Vlong (Int64.repr piece));
             temp C._done (Vlong (Int64.repr done)); temp C._series_len (Vlong (Int64.repr (Zlength S)));
             temp C._series sp; temp C._data data; temp C._n (Vlong (Int64.repr n));
             temp C._max_window (Vlong (Int64.repr maxw)); temp C._zds zds;
             lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len;
             gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; @mbytes HCS (Zlength S) S sp;
           @malloc_token HCS Ews (tarray tuchar n) data; @data_at HCS Ews (tarray tuchar n) (zbytes l2) data;
           data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written;
           if eq_dec fp nullval then data_at_ Tsh tulong v_len
           else data_at Tsh tulong (Vlong (Int64.repr (Zlength F))) v_len * @mbytes HCS (Zlength F) F fp;
           TT; has_ext tt)).
    { (* a skippable frame *)
      forward_call (gv, Tsh, v_len).
      Intros q. forward.
      destruct (eq_dec q nullval) as [Hq|Hq].
      { Exists 0 q (@nil Z) (@nil Z) l1. rewrite !if_true by exact Hq. entailer!. }
      Intros k u.
      Exists 0 q (sk_bytes k u) (@nil Z) l1. rewrite !if_false by exact Hq. entailer!.
      pose proof (sk_bytes_length k u) as Lk. pose proof (Zlength_nonneg u).
      split; [apply sk_bytes_ok; auto |]. split; [unfold PTRDIFF_MAX; lia |].
      split; [rewrite app_nil_r; apply si_skip; auto |].
      intro E. rewrite E, Zlength_nil in Lk. lia. }
    { (* a Zstandard frame of the next k bytes of data *)
      forward_call (n - done).
      Intros k.
      sep_apply (nf_pre n k done l1 data ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      forward_call (gv, Ews, offset_val done data, sublist done (done + k) l1, k, maxw, 0, Tsh, v_len,
                    nf_w n k l1 data).
      { rewrite Zlength_sublist by lia. replace (done + k - done) with k by lia. entailer!. }
      { cancel. }
      { split; [apply Forall_sublist; auto |].
        split; [rewrite Zlength_sublist by lia; rep_lia |].
        intros Z0. apply nf_w_valid; auto; lia. }
      Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
      forward.
      assert (Hdk: Zlength (sublist done (done + k) l1) = k) by (rewrite Zlength_sublist by lia; lia).
      sep_apply (nf_post n k done l1 d' data ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Hl2: Zlength (sublist 0 done l1 ++ d' ++ sublist (done + k) n l1) = n)
        by (rewrite !Zlength_app, !Zlength_sublist by lia; lia).
      assert (Bl2: bytes_ok (sublist 0 done l1 ++ d' ++ sublist (done + k) n l1))
        by (apply Forall_app; split; [apply Forall_sublist; auto | apply Forall_app; split; [auto | apply Forall_sublist; auto]]).
      destruct (eq_dec q nullval) as [Hq|Hq].
      { Exists k q (@nil Z) (@nil Z) (sublist 0 done l1 ++ d' ++ sublist (done + k) n l1).
        rewrite !if_true by exact Hq. entailer!. }
      Intros c.
      Exists k q (nf_bytes (sublist done (done + k) l1) k 0 c) (nf_data (sublist done (done + k) l1) c)
        (sublist 0 done l1 ++ d' ++ sublist (done + k) n l1).
      rewrite !if_false by exact Hq. entailer!.
      set (d := sublist done (done + k) l1) in *.
      assert (Bd: bytes_ok d) by (apply Forall_sublist; auto).
      match goal with Hok: nf_ok _ k maxw 0 c, Hb: Zlength d <= _ |- _ => rename Hok into Hnf, Hb into Hdb end.
      rewrite <- Hdk in Hnf |- *.
      pose proof (nf_bytes_length d (Zlength d) maxw 0 c Hnf) as Lb.
      pose proof (Z.mul_div_le (PTRDIFF_MAX - 26) 4 ltac:(lia)) as Hdiv.
      split; [apply (nf_bytes_ok d (Zlength d) maxw 0 c); auto |].
      split; [unfold PTRDIFF_MAX in *; lia |].
      split; [apply si_frame; auto; unfold PTRDIFF_MAX in Hdb; exact Hdb |].
      intro E. rewrite E, Zlength_nil in Lb. lia. }
    Intros piece fp F X l2.
    repeat apply -> seq_assoc. apply semax_if_seq.
    destruct (eq_dec fp nullval) as [Hf|Hf].
    { (* out of memory *)
      subst fp. try rewrite if_true by reflexivity.
      forward_if; [| contradiction]. forward. forward.
      forward_if; [forward; cancel | contradiction]. }
    try rewrite if_false by exact Hf.
    match goal with Himp: fp <> nullval -> _ |- _ => destruct (Himp Hf) as (BF & LF & SF & NF) end.
    assert (Emb: @mbytes HCS (Zlength F) F fp =
                 @malloc_token HCS Ews (tarray tuchar (Zlength F)) fp *
                 @data_at HCS Ews (tarray tuchar (Zlength F)) (zbytes F) fp)
      by (unfold mbytes; rewrite if_false by exact Hf; reflexivity).
    rewrite Emb.
    forward_if; [contradiction |].
    rewrite <- Emb. Intros.
    forward.
    forward_call (gv, sp, S, fp, F).
    { pose proof (Zlength_nonneg S). pose proof (Zlength_nonneg F). unfold PTRDIFF_MAX in *. rep_lia. }
    Intros q2.
    forward. forward.
    destruct (eq_dec q2 nullval) as [Hq2|Hq2].
    { subst q2. forward_if; [forward; cancel | contradiction]. }
    assert (Emb2: @mbytes HCS (Zlength S + Zlength F) (S ++ F) q2 =
                  @malloc_token HCS Ews (tarray tuchar (Zlength S + Zlength F)) q2 *
                  @data_at HCS Ews (tarray tuchar (Zlength S + Zlength F)) (zbytes (S ++ F)) q2)
      by (unfold mbytes; rewrite if_false by exact Hq2; reflexivity).
    rewrite Emb2.
    forward_if; [contradiction |].
    rewrite <- Emb2. Intros.
    forward. forward. forward.
    match goal with Hj: q2 <> nullval -> _ |- _ => specialize (Hj Hq2 LF) end.
    Exists (done + piece) (S ++ F) (Cc ++ X) q2 l2.
    rewrite Zlength_app. entailer!.
    split; [apply Forall_app; auto | intro E; apply app_eq_nil in E; tauto]. }
  { (* while (done < n || nondet_u8() != 0) *)
    Intros done S Cc sp l1.
    forward_if (EX t: int,
     PROP (si_series maxw S Cc; 0 <= done <= n; Zlength S <= PTRDIFF_MAX; Zlength l1 = n; bytes_ok l1;
           bytes_ok S; S <> []; sp <> nullval)
     LOCAL (temp C._t'9 (Vint t); temp C._done (Vlong (Int64.repr done));
            temp C._series_len (Vlong (Int64.repr (Zlength S)));
            temp C._series sp; temp C._data data; temp C._n (Vlong (Int64.repr n));
            temp C._max_window (Vlong (Int64.repr maxw)); temp C._zds zds;
            lvar C._completed tulong v_completed; lvar C._written tulong v_written; lvar C._len tulong v_len;
            gvars gv)
     SEP (mem_mgr gv; zstd_globals gv; DC gv zds st; @mbytes HCS (Zlength S) S sp;
          @malloc_token HCS Ews (tarray tuchar n) data; @data_at HCS Ews (tarray tuchar n) (zbytes l1) data;
          data_at_ Tsh tulong v_completed; data_at_ Tsh tulong v_written; data_at_ Tsh tulong v_len; TT;
          has_ext tt)).
    { forward. Exists Int.one. entailer!. }
    { forward_call tt. Intros b. forward.
      destruct (zeq b 0); [Exists Int.zero | Exists Int.one]; entailer!. }
    Intros t.
    forward_if.
    { forward. Exists done S Cc sp l1. entailer!. }
    { forward. Exists done S Cc sp l1. entailer!. } }
  (* the series S, its content Cc; one call and the stream *)
  Intros done S Cc sp l1.
  forward_call 9223372036854775807.
  Intros cap.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros one.
  forward_call (tarray tuchar cap, gv).
  { simpl. rep_lia. }
  Intros streamed.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec one nullval) as [Ho|Ho].
  { subst one. forward_if; [| contradiction]. forward.
    forward_if; [forward; cancel | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  try rewrite (if_false (one = nullval)) by exact Ho. Intros.
  forward_if; [contradiction |].
  destruct (eq_dec streamed nullval) as [Hs|Hs].
  { subst streamed. forward.
    forward_if; [forward; cancel | dead_branch]. }
  try rewrite (if_false (streamed = nullval)) by exact Hs. Intros.
  assert_PROP (isptr streamed) as Ps by entailer!.
  destruct streamed as [| | | | | bs is]; try contradiction.
  forward.
  forward_if; [discriminate |].
  set (streamed := Vptr bs is) in *.
  assert (Emb: @mbytes HCS (Zlength S) S sp =
               @malloc_token HCS Ews (tarray tuchar (Zlength S)) sp *
               @data_at HCS Ews (tarray tuchar (Zlength S)) (zbytes S) sp)
    by (unfold mbytes; rewrite if_false by assumption; reflexivity).
  rewrite Emb. Intros.
  assert_PROP (isptr sp) as Psp by entailer!.
  assert_PROP (isptr one) as Pone by entailer!.
  (* ZSTD_decompress(one, cap, series, series_len) *)
  sep_apply (to_Z_ Ews cap one). sep_apply (data_at__mbuf Ews cap one).
  sep_apply (to_Z Ews (Zlength S) (zbytes S) sp).
  sep_apply (tok_to_Z Ews (Zlength S) sp). sep_apply (tok_to_Z Ews cap one).
  sep_apply (pws_fold (tarray tuchar (Zlength S)) sp (tarray tuchar cap) one).
  forward_call ([pw_token Ews (tarray tuchar (Zlength S)) sp; pw_token Ews (tarray tuchar cap) one],
                gv, Ews, one, cap, Ews, sp, S).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | first [lia | apply Zlength_nonneg] | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *. rewrite mbuf_isptr by auto.
  sep_apply pws_unfold. Intros.
  (* stream_all(zds, series, series_len, streamed, cap, &written, &completed) *)
  sep_apply (to_Z_ Ews cap streamed). sep_apply (tok_to_Z Ews cap streamed).
  sep_apply (pws_fold (tarray tuchar (Zlength S)) sp (tarray tuchar cap) streamed).
  sep_apply (ulong__to_Z Tsh v_written). sep_apply (ulong__to_Z Tsh v_completed).
  rewrite (DC_res_none gv zds st eq_refl eq_refl).
  rewrite (@data_at__eq ZCS Ews (tarray tuchar cap) streamed).
  forward_call ([pw_token Ews (tarray tuchar (Zlength S)) sp; pw_token Ews (tarray tuchar cap) streamed],
                gv, zds, st, Ews, sp, S, Ews, streamed, cap, @default_val ZCS (tarray tuchar cap),
                Tsh, v_written, Tsh, v_completed).
  { cancel. }
  { split; [unfold stream_dict_ok, st; simpl; auto |].
    split; [apply buf_ok_tok; [simpl; tauto | auto | apply Zlength_nonneg | auto] |].
    split; [apply buf_ok_tok; [simpl; tauto | auto | lia | auto] |].
    apply Zlength_default_val_Tarray_tuchar; lia. }
  Intros vret. destruct vret as [[r2 y] z]. cbn [fst snd] in *.
  (* the model: both decodings of S give Cc; how the stream ends (SI_Stream); what ZSTD_decompress returned *)
  assert (Hoc: Zlength (@default_val ZCS (tarray tuchar cap)) = cap) by (apply Zlength_default_val_Tarray_tuchar; lia).
  destruct (HDE maxw S Cc md_dflt no_wlim H7 ltac:(lia) eq_refl ltac:(simpl; lia) ltac:(unfold no_wlim; lia))
    as [_ Hd1].
  destruct (HDE maxw S Cc (dmode_w (dmode_of (dc_par st))) no_wlim H7 ltac:(lia) eq_refl ltac:(simpl; lia)
    ltac:(unfold no_wlim; lia)) as [_ Hd2].
  destruct (HDE maxw S Cc (dmode_w (dmode_of (dc_par st))) (dp_wmax (dc_par st)) H7 ltac:(lia) eq_refl
    ltac:(simpl; lia) (Z.le_refl maxw)) as [_ Hd3].
  assert (Hr2: 0 <= r2 <= Int64.max_unsigned)
    by (match goal with Hc: stream_call _ _ _ _ r2 _ |- _ => destruct Hc as (? & ? & ? & _ & _ & ? & _); assumption end).
  match goal with Hr: stream_run _ _ _ _ _, Hc: stream_call _ _ _ _ _ _, Hm: ~ stream_more _ _ _ _ |- _ =>
    pose proof (HST S Cc cap streamed st _ y r2 z eq_refl eq_refl eq_refl eq_refl H12 H13 ltac:(lia) Hoc Hd2 Hd3
                  Hr Hc Hm) as Hres end.
  unfold oneshot_ok in H20. rewrite Hd1 in H20. destruct H20 as [Hle [Hok Herr]].
  sep_apply (ulong_of_Z Tsh (Vlong (Int64.repr (sa_opos z))) v_written).
  sep_apply (ulong_of_Z_ Tsh (Vlong (Int64.repr (sa_done z))) v_completed).
  (* out of memory: the run ends *)
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (Z.eq_dec (error_of r) 64) as [Em|Em].
  { forward_if; [| dead_branch]. forward. forward_if; [| dead_branch]. forward. sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (sa_opos z))) v_written). cancel. }
  forward_if; [dead_branch |].
  repeat apply -> seq_assoc.
  forward_call r2.
  forward.
  destruct (Z.eq_dec (error_of r2) 64) as [Em2|Em2].
  { forward_if; [| dead_branch]. forward. sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (sa_opos z))) v_written). cancel. }
  forward_if; [dead_branch |].
  forward_call r.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (is_error_code r) eqn:Er.
  - (* ZSTD_decompress failed: cap < |Cc|, so the stream's last call did not return 0 *)
    forward_if; [| dead_branch].
    assert (Hcap: cap < Zlength Cc).
    { destruct (Herr eq_refl) as [Hc|Hc]; [exact Hc | exfalso; apply Em; rewrite Hc; reflexivity]. }
    assert (Hn0: r2 <> 0).
    { destruct Hres as [E|[[_ Hc]|(_ & _ & Hc & _)]];
        [exfalso; apply Em2; rewrite E; exact error_of_mem | exact Hc | lia]. }
    forward_call Int.one.
    { entailer!. rewrite eq64_false by auto. reflexivity. }
    forward. sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (sa_opos z))) v_written). cancel.
  - (* ZSTD_decompress returned |Cc| with Cc in one: the stream ended with 0, Cc in streamed *)
    forward_if; [dead_branch |].
    destruct (Hok eq_refl) as [Erc Eout]. specialize (Hle eq_refl).
    destruct Hres as [E|[[Hc _]|(Ez & Eop & Hcl & Esub)]];
      [exfalso; apply Em2; rewrite E; exact error_of_mem | lia |].
    subst r2. subst r.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| dead_branch].
    forward. forward.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if.
    2: { exfalso. destruct (zeq (sa_opos z) (Zlength Cc)); [discriminate | contradiction]. }
    assert (BC: bytes_ok Cc) by (eapply si_series_content_ok; eauto).
    assert_PROP (Zlength (sa_out z) = cap) as Lz by entailer!.
    rewrite (Zstd.proof.harness.frames.FBodyStreamAll.sa_split Ews cap (Zlength Cc) (sa_out z) streamed) by lia.
    rewrite (Zstd.proof.harness.frames.FBodyStreamAll.sa_split Ews cap (Zlength Cc) out one) by lia.
    rewrite Esub, Eout. Intros.
    sep_apply (of_Z Ews (Zlength Cc) (zbytes Cc) streamed). sep_apply (of_Z Ews (Zlength Cc) (zbytes Cc) one).
    repeat apply -> seq_assoc.
    forward_call (Ews, streamed, Cc, Ews, one, Cc).
    destruct (list_eq_dec Z.eq_dec Cc Cc) as [_|NE]; [| contradiction].
    forward.
    forward_call Int.one.
    forward. sep_apply (data_at_data_at_ Tsh tulong (Vlong (Int64.repr (sa_opos z))) v_written). cancel.
Qed.

(* ---------- from G0 to H.Gprog API Hs ---------- *)

Lemma Externals_eq :
  H.Externals = [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
               gp_assume_spec].
Proof.
  unfold H.Externals, present, env_harness, filter.
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

Lemma Gprog_cons : H.Gprog API Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (API ++ [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
           gp_assume_spec] ++ Hs ++ [main_spec]).
Proof. unfold H.Gprog, H.Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry of a body's context found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold API, Hs, Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog i fs : initial_world.find_id i G0 = Some fs -> initial_world.find_id i (H.Gprog API Hs) = Some fs.
Proof.
  apply Zstd.proof.harness.frames.FTransfer.fk_find_all. unfold G0. repeat constructor; in_gprog.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with
  | Some fs => Some (type_of_funspec fs)
  | None => Maps.PTree.get i (make_tycontext_g Vs nil)
  end.
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
Lemma Gprog_not_var i : In i (map fst (H.Gprog API Hs)) -> ~ In i (map fst H.Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst H.Vprog))) (map fst (H.Gprog API Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Lemma body_main (HST: si_stream_stmt) (HDE: si_decode_stmt) : semax_body H.Vprog (H.Gprog API Hs) f_main main_spec.
Proof.
  eapply semax_body_subsumption; [apply (body_main_G0 HST HDE) |].
  apply tycontext_sub_i99. split; intro i.
  - rewrite (make_tycontext_g_find H.Vprog G0 i).
    rewrite (make_tycontext_g_find H.Vprog (H.Gprog API Hs) i).
    destruct (initial_world.find_id i G0) as [fs|] eqn:E.
    + rewrite (G0_in_Gprog i fs E). apply sub_option_refl.
    + destruct (initial_world.find_id i (H.Gprog API Hs)) as [fs'|] eqn:E'.
      * rewrite mtg_none; [exact Logic.I |].
        apply (Gprog_not_var i).
        apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
      * apply sub_option_refl.
  - rewrite !semax_prog.find_id_maketycontext_s.
    destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
    rewrite (G0_in_Gprog i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

(* stream_all's body at the harness's compspecs, for its specification at the decoder's (as in Hs): the kit's
   body at HCS, and the specification at any compspecs is a funspec_sub of the one at any other *)
Lemma body_stream_all_H :
  @semax_body [] (G_stream_all DC DD) HCS FStreamSpec.f_stream_all (@stream_all_spec CompSpecs DC DD).
Proof.
  apply (semax_body_funspec_sub (phi := snd (@stream_all_spec HCS DC DD))).
  - apply (@Zstd.proof.harness.frames.FBodyStreamAll.body_stream_all HCS).
    Zstd.proof.harness.frames.FBodyStreamAll.fs_cspecs_sub.
  - apply Zstd.proof.harness.frames.FBodyStreamAll.stream_all_spec_sub.
  - repeat constructor; simpl; intuition discriminate.
Qed.

(* a helper of the frames kit: the harness's body is the kit's Clight term (the lookup in the harness's
   definitions computes to it), proved once in the kit and moved into Gprog *)
Ltac kit_body fk Gk body :=
  exists fk; split; [vm_compute; reflexivity |]; split; [reflexivity |];
  apply (Zstd.proof.harness.frames.FTransfer.fk_transfer H.Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

(* main's proof uses the facts of SI_Stream and SI_Model (the series' model, how stream_all ends) *)
Theorem api_split_invariant_ok_from : si_stream_stmt -> si_decode_stmt -> si_f5 -> HarnessOK API Hs.
Proof.
  intros HST HDE _.
  split; [vm_compute; reflexivity |].
  repeat apply Forall_cons; try apply Forall_nil.
  - kit_body FSpecs.f_out_of_memory G_out_of_memory
      (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory HCS).
  - kit_body FSpecs.f_copy_of (@G_copy_of HCS)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of HCS).
  - kit_body FStreamSpec.f_stream_all (G_stream_all DC DD) body_stream_all_H.
  - kit_body FSpecs.f_any_bytes (@G_any_bytes HCS)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes HCS).
  - kit_body FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto HCS).
  - kit_body FSpecs.f_put_le G_put_le
      (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le HCS).
  - kit_body FSpecs.f_join (@G_join HCS) (@Zstd.proof.harness.frames.FBodiesSmall.body_join HCS).
  - kit_body FSpecs.f_bytes_eq G_bytes_eq
      (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq HCS).
  - kit_body FSpecs.f_new_skippable (@G_new_skippable HCS)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_new_skippable HCS).
  - kit_body FSpecs.f_new_frame (@G_new_frame HCS)
      (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame HCS).
  - exists f_main. split; [reflexivity |]. split; [reflexivity |]. exact (body_main HST HDE).
Qed.

End Main.
