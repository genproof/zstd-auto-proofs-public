(* The harness obligation of rj_any_stream (harness/rj_any_stream.c): for ANY predicates DC, DD of the decoder's
   API (Spec_api6), the helpers copy_of, any_bytes and upto (laws_common.h, proved once in the frames kit) and
   main satisfy their specifications.

   main's loop keeps one stream without dictionary, in buffered mode and not in error: after a call that returns
   an error the harness resets it (ZSTD_DCtx_reset, session only), and a call that returns no error leaves it out
   of error (stream_post: ss_err is the call's error).  Each call's check is the first two conjuncts of
   stream_post: opos <= opos' <= osz and ipos <= ipos' <= isz; so `read` stays within the input.  The buffers
   have any size up to PTRDIFF_MAX (the streaming specification takes sizes up to 2 ^ 63 - 1).  The input piece
   and the output may be NULL when empty (malloc(0)): the specification takes each buffer as `mbuf` (NULL with
   size 0, or the bytes at a pointer; zstd's fix F9 gives an empty NULL buffer the base ZSTD_emptyBuffer). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rj_any_stream.HOK_rj_any_stream.
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

Lemma Vprog_ids : forallb (fun i => id_in_list i (map fst Vprog))
  (map fst (QPprog_vars Zstd.contracts.rj_any_stream.whole_prog)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.rj_any_stream.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  apply id_in_list_true. apply (in_map fst) in Hin.
  pose proof Vprog_ids as B. rewrite forallb_forall in B. exact (B i Hin).
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rj_any_stream.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rj_any_stream.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays and tokens between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z_ sh n p :
  @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @data_at_ CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs Zstd.units.Zstd.CS CompSpecs). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

(* ---------- the buffer witnesses of a one-shot call: the malloc_tokens of its two buffers ---------- *)

Lemma pws_fold w1 w2 : (pw_pred w1 * pw_pred w2) |-- pws_pred [w1; w2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold w1 w2 : pws_pred [w1; w2] |-- (pw_pred w1 * pw_pred w2).
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
  - rewrite (@data_at__memory_block Zstd.units.Zstd.CS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token Zstd.units.Zstd.CS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
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

Lemma vp_frame (P Q: mpred) p : ((P && valid_pointer p) * Q) |-- valid_pointer p.
Proof. apply sepcon_valid_pointer1. apply andp_left2. apply derives_refl. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

Lemma free_pre {cs: compspecs} t p : isptr p ->
  (malloc_token Ews t p * data_at_ Ews t p) |-- (if eq_dec p nullval then emp else (malloc_token Ews t p * data_at_ Ews t p)).
Proof. intros. rewrite if_false by (intro; subst; contradiction). apply derives_refl. Qed.


(* ---------- the stream's structs between the harness's compspecs and the decoder's ---------- *)

Lemma out_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh tout (a, (b, c)) p = @data_at ZCS sh t_outBuffer (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs ZCS (Zstd.proof.harness.HCsConv.cce_any CompSpecs ZCS)
    sh tout (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  exact (f_equal (fun f => f p) E).
Qed.

Lemma in_to_Z sh (a b c: val) p :
  @data_at CompSpecs sh tin (a, (b, c)) p = @data_at ZCS sh t_inBuffer (a, (b, c)) p.
Proof.
  pose proof (@data_at_change_composite CompSpecs ZCS (Zstd.proof.harness.HCsConv.cce_any CompSpecs ZCS)
    sh tin (a, (b, c)) (a, (b, c)) (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E.
  exact (f_equal (fun f => f p) E).
Qed.

(* ---------- a stream without dictionary ---------- *)

Lemma DC_res (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) gv ds st sh :
  dc_dict st = None -> dc_set st = nil ->
  DC gv ds st = (DC gv ds st * dict_res DD gv sh (dc_dict st) * set_res DD gv sh (dc_set st) (dc_dict st))%logic.
Proof. intros Hd Hs. rewrite Hd, Hs. unfold dict_res, set_res. simpl. rewrite !sepcon_emp. reflexivity. Qed.

Lemma stream_dict_ok_none W st : dc_dict st = None -> dc_set st = nil -> dc_bl st = None -> stream_dict_ok W st.
Proof. intros Hd Hs Hb. unfold stream_dict_ok. rewrite Hd, Hs, Hb. auto. Qed.

(* ---------- the buffers of a call: NULL when empty, or a malloc'ed object lending its token ---------- *)

Definition pw_tok (n: Z) (p: val) : ptr_witness :=
  if eq_dec p nullval then pw_none else pw_token Ews (tarray tuchar n) p.

Lemma buf_ok_mbuf W sh n p : In (pw_tok n p) W -> readable_share sh -> 0 <= n -> is_pointer_or_null p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold pw_tok in Hin. destruct (eq_dec p nullval) as [->|Hne].
  - unfold buf_ok. rewrite (@data_at__eq ZCS). unfold data_at, field_at.
    rewrite sepcon_comm, sepcon_andp_prop'. apply derives_extract_prop. intros [Hfc _].
    destruct Hfc; contradiction.
  - apply buf_ok_tok; auto. apply isptr_of; auto.
Qed.

(* the object of n bytes l that copy_of / malloc returned, as the witness and the buffer of a call *)
Lemma mbytes_to_mbuf n l p : (p = nullval -> n = 0 /\ l = []) ->
  (if eq_dec p nullval then emp else
     (@malloc_token CompSpecs Ews (tarray tuchar n) p * @data_at CompSpecs Ews (tarray tuchar n) (zbytes l) p)) |-- pw_pred (pw_tok n p) * mbuf Ews n (zbytes l) p.
Proof.
  intros H. unfold pw_tok, mbuf. destruct (eq_dec p nullval) as [E|E].
  - destruct (H E) as [-> ->]. simpl. rewrite emp_sepcon. apply andp_right; [apply prop_right; auto | auto].
  - simpl. apply sepcon_derives; [apply tok_to_Z | apply to_Z].
Qed.

Lemma malloc_to_mbuf n p : (p = nullval -> n = 0) ->
  (if eq_dec p nullval then emp else
     (@malloc_token CompSpecs Ews (tarray tuchar n) p * @data_at_ CompSpecs Ews (tarray tuchar n) p)) |--
  pw_pred (pw_tok n p) * mbuf Ews n (Zrepeat Vundef n) p.
Proof.
  intros H. unfold pw_tok, mbuf. destruct (eq_dec p nullval) as [E|E].
  - rewrite (H E). simpl. rewrite emp_sepcon. apply andp_right; [apply prop_right; auto | auto].
  - simpl. apply sepcon_derives; [apply tok_to_Z |].
    eapply derives_trans; [apply to_Z_ |]. rewrite (@data_at__eq ZCS). apply derives_refl.
Qed.

(* after the call: what free takes *)
Lemma mbuf_to_free n c p :
  pw_pred (pw_tok n p) * mbuf Ews n c p |--
  (if eq_dec p nullval then emp else
     (@malloc_token CompSpecs Ews (tarray tuchar n) p * @data_at_ CompSpecs Ews (tarray tuchar n) p)).
Proof.
  unfold pw_tok, mbuf. destruct (eq_dec p nullval) as [E|E].
  - simpl. rewrite emp_sepcon. apply andp_left2. auto.
  - simpl. apply sepcon_derives; [apply tok_of_Z |].
    eapply derives_trans; [apply (@data_at_data_at_ ZCS) | apply of_Z_].
Qed.

(* the n bytes of the input as three parts: before the piece, the piece, after it *)
Lemma input_split sh n l p a b : 0 <= a <= b -> b <= n -> Zlength l = n ->
  @field_compatible CompSpecs (tarray tuchar n) [] p ->
  @data_at CompSpecs sh (tarray tuchar n) (zbytes l) p =
  (@data_at CompSpecs sh (tarray tuchar a) (zbytes (sublist 0 a l)) p *
   @data_at CompSpecs sh (tarray tuchar (b - a)) (zbytes (sublist a b l)) (offset_val a p) *
   @data_at CompSpecs sh (tarray tuchar (n - b)) (zbytes (sublist b n l)) (offset_val b p))%logic.
Proof.
  intros Hab Hb Hl Hfc.
  rewrite (split3_data_at_Tarray_tuchar sh n a b (zbytes l) p) by (try list_solve; lia).
  rewrite !sublist_map.
  rewrite !field_address0_offset.
  - unfold nested_field_offset. simpl. rewrite ?Z.add_0_l, ?Z.mul_1_l. reflexivity.
  - apply field_compatible0_cons. simpl. split; [lia | exact Hfc].
  - apply field_compatible0_cons. simpl. split; [lia | exact Hfc].
Qed.

Lemma input_join sh n l p a k : 0 <= a -> 0 <= k -> a + k <= n -> Zlength l = n ->
  @field_compatible CompSpecs (tarray tuchar n) [] p ->
  (@data_at CompSpecs sh (tarray tuchar a) (zbytes (sublist 0 a l)) p *
   @data_at CompSpecs sh (tarray tuchar k) (zbytes (sublist a (a + k) l)) (offset_val a p) *
   @data_at CompSpecs sh (tarray tuchar (n - (a + k))) (zbytes (sublist (a + k) n l)) (offset_val (a + k) p))%logic
  |-- @data_at CompSpecs sh (tarray tuchar n) (zbytes l) p.
Proof.
  intros. rewrite (input_split sh n l p a (a + k)) by (auto; lia).
  replace (a + k - a) with k by lia. apply derives_refl.
Qed.

Lemma cle_true a b : 0 <= a <= b -> b <= Int64.max_unsigned ->
  Vint Int.one = bool2val (Int64.cmpu Cle (Int64.repr a) (Int64.repr b)).
Proof.
  intros. unfold Int64.cmpu. rewrite ltu_Z by lia.
  replace (b <? a) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* the test p == NULL on a malloc'ed byte array: its token, or (for a non-empty one) its bytes, give a valid p *)
Ltac tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [@malloc_token ?cs ?sh (tarray tuchar ?n) p] =>
    destruct (zlt 0 n);
    [ first
      [ match goal with |- context [@data_at ?cs' ?sh' (tarray tuchar n) ?v p] =>
          apply derives_trans with (@data_at cs' sh' (tarray tuchar n) v p * TT)%logic; [cancel|];
          apply sepcon_valid_pointer1; apply data_at_valid_ptr; [auto | simpl; lia] end
      | match goal with |- context [@data_at_ ?cs' ?sh' (tarray tuchar n) p] =>
          apply derives_trans with (@data_at_ cs' sh' (tarray tuchar n) p * TT)%logic; [cancel|];
          apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | simpl; lia] end ]
    | apply derives_trans with (@malloc_token cs sh (tarray tuchar n) p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; simpl; lia ]
  end.

(* the stream between two calls: no dictionary, buffered output, not in error *)
Definition inv_st (st: dctx_st) : Prop :=
  dc_dict st = None /\ dc_set st = nil /\ dc_bl st = None /\ dc_stable st = false /\ ss_err (dc_ss st) = false.

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
   @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rj_any_stream.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  (* input or zds NULL: the run ends *)
  destruct (eq_dec input nullval) as [Hin|Hin].
  { subst input. Intros. apply semax_if_seq. forward_if; [| contradiction]. forward.
    forward_if; [forward; entailer! | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  destruct (eq_dec zds nullval) as [Hz|Hz].
  { subst zds. Intros. apply semax_if_seq. forward_if; [contradiction |].
    forward.
    change (bool2val (Int64.cmpu Ceq Int64.zero (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
    forward_if; [forward; entailer! | exfalso; exact (Int.one_not_zero ltac:(assumption))]. }
  Intros.
  apply semax_if_seq. forward_if; [contradiction |].
  forward.
  sep_apply (drop_vp (DC gv zds dctx_init) zds).
  pose proof (isptr_of zds PNzds Hz) as Hzp.
  destruct zds as [| | | | | bz iz]; try contradiction.
  forward_if; [exfalso; lia |].
  set (zds := Vptr bz iz) in *.
  forward_loop
    (EX read: Z, EX st: dctx_st,
     PROP (0 <= read <= n; inv_st st)
     LOCAL (temp _read (Vlong (Int64.repr read)); temp _n (Vlong (Int64.repr n)); temp _input input;
            temp _zds zds; lvar _output tout v_output; lvar _in tin v_in; gvars gv)
     SEP (DC gv zds st; mem_mgr gv; zstd_globals gv;
          malloc_token Ews (tarray tuchar n) input; data_at Ews (tarray tuchar n) (zbytes l) input;
          data_at_ Tsh tout v_output; data_at_ Tsh tin v_in; TT; has_ext tt))
    break:
    (EX st: dctx_st,
     PROP ()
     LOCAL (temp _zds zds; lvar _output tout v_output; lvar _in tin v_in; gvars gv)
     SEP (DC gv zds st; mem_mgr gv; zstd_globals gv;
          data_at_ Tsh tout v_output; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { Exists 0 dctx_init. entailer!. all: try (unfold inv_st; repeat split; reflexivity). all: cancel. }
  2: { (* after the loop: free the stream *)
       Intros st. forward_call (gv, zds, Some st). forward. entailer!. }
  (* one call *)
  Intros read st.
  forward_call (n - read).
  Intros take.
  forward_call 9223372036854775807.
  Intros room.
  (* the piece: copy_of(input + read, take) *)
  assert_PROP (@field_compatible CompSpecs (tarray tuchar n) [] input) as Hfc.
  { entailer!. }
  rewrite (input_split Ews n l input read (read + take) ltac:(lia) ltac:(lia) H0 Hfc).
  replace (read + take - read) with take by lia.
  forward_call (gv, Ews, offset_val read input, sublist read (read + take) l).
  { entailer!. rewrite Zlength_sublist by lia. replace (read + take - read) with take by lia. auto. }
  { rewrite Zlength_sublist by lia. replace (read + take - read) with take by lia. cancel. }
  { unfold bytes_ok in *. apply Forall_sublist. auto. }
  rewrite Zlength_sublist by lia. replace (read + take - read) with take by lia.
  Intros piece.
  sep_apply (input_join Ews n l input read take ltac:(lia) ltac:(lia) ltac:(lia) H0 Hfc).
  (* the output: malloc(room) *)
  forward_call (tarray tuchar room, gv).
  { simpl. rep_lia. }
  Intros out.
  unfold FSpecs.mbytes.
  (* the test: (piece == NULL && take != 0) || (out == NULL && room != 0) *)
  set (bp := if eq_dec piece nullval then negb (take =? 0) else false).
  set (bo := if eq_dec out nullval then negb (room =? 0) else false).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'10 (Vint (if bp then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { tc_null_test piece. }
  { forward. entailer!.
    unfold bp. rewrite if_true by auto. unfold Int64.cmpu. destruct (Z.eqb_spec take 0) as [->|Ht]; simpl.
    - reflexivity.
    - rewrite Int64.eq_false; [reflexivity|]. intro E. apply (f_equal Int64.unsigned) in E.
      rewrite !Int64.unsigned_repr in E by rep_lia. contradiction. }
  { forward. entailer!. unfold bp. rewrite if_false by auto. reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'11 (Vint (if (bp || bo)%bool then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { forward. entailer!. destruct bp; [reflexivity | contradiction]. }
  { assert (Hbp: bp = false) by (destruct bp; [discriminate | reflexivity]).
    forward_if.
    { tc_null_test out. }
    { forward. forward. entailer!.
      rewrite Hbp. simpl. unfold bo. rewrite if_true by auto. unfold Int64.cmpu.
      destruct (Z.eqb_spec room 0) as [->|Ht]; simpl.
      - reflexivity.
      - rewrite Int64.eq_false; [reflexivity|]. intro E. apply (f_equal Int64.unsigned) in E.
        rewrite !Int64.unsigned_repr in E by rep_lia. contradiction. }
    { forward. entailer!. rewrite Hbp. simpl. unfold bo. rewrite if_false by auto. reflexivity. } }
  forward_if.
  { forward. entailer!. }
  match goal with H: (if (bp || bo)%bool then _ else _) = Int.zero |- _ => rename H into Ht end.
  destruct (bp || bo)%bool eqn:Eb; [exfalso; exact (Int.one_not_zero Ht) |].
  apply orb_false_iff in Eb. destruct Eb as [Ebp Ebo].
  assert (Hpo: (piece = nullval -> take = 0) /\ (out = nullval -> room = 0)).
  { unfold bp, bo in *. split; intros E.
    - rewrite if_true in Ebp by auto. rewrite negb_false_iff, Z.eqb_eq in Ebp. auto.
    - rewrite if_true in Ebo by auto. rewrite negb_false_iff, Z.eqb_eq in Ebo. auto. }
  clear Ht Ebp Ebo bp bo.
  destruct Hpo as [Hpn Hon].
  (* the buffers of the call *)
  forward. forward.
  forward_call take. Intros ipos.
  forward. forward. forward.
  forward_call room. Intros opos.
  forward. forward. forward.
  (* the call, with the buffers as mbuf and their tokens as witnesses *)
  destruct H5 as (Hd & Hs & Hb & Hstb & He).
  assert_PROP (is_pointer_or_null piece) as PNpiece by entailer!.
  assert_PROP (is_pointer_or_null out) as PNout by entailer!.
  sep_apply (mbytes_to_mbuf take (sublist read (read + take) l) piece).
  { intros E. specialize (Hpn E). subst take. rewrite Z.add_0_r, sublist_nil. auto. }
  sep_apply (malloc_to_mbuf room out Hon).
  sep_apply (pws_fold (pw_tok take piece) (pw_tok room out)).
  rewrite out_to_Z, in_to_Z.
  rewrite (DC_res DC DD gv zds st Ews Hd Hs).
  forward_call ([pw_tok take piece; pw_tok room out], gv, zds, st, v_output, v_in, Tsh, Tsh, Ews, out, room, opos,
                Zrepeat Vundef room, Ews, piece, take, ipos, sublist read (read + take) l).
  { cancel. }
  { split; [apply buf_ok_mbuf; [simpl; auto | auto | lia | auto] |].
    split; [apply buf_ok_mbuf; [simpl; auto | auto | lia | auto] |].
    split; [apply stream_dict_ok_none; auto |].
    split; [rewrite Zlength_Zrepeat; lia |].
    split; [rewrite Zlength_sublist; lia |].
    unfold bytes_ok in *. apply Forall_sublist. auto. }
  Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. cbn [fst snd] in *.
  match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    destruct H as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor & Hr0 & Hst' & Hrest) end.
  sep_apply (drop_vp (DC gv zds st') zds).
  rewrite Hd, Hs. change (dict_res DD gv Ews None) with emp. change (set_res DD gv Ews nil None) with emp.
  rewrite <- out_to_Z, <- in_to_Z.
  (* the check: in_start <= in.pos <= take, out_start <= output.pos <= room *)
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'15 (Vint Int.one) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!. apply cle_true; rep_lia. }
  { exfalso. lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'16 (Vint Int.one) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!. apply cle_true; rep_lia. }
  { exfalso. exact (Int.one_not_zero ltac:(assumption)). }
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'17 (Vint Int.one) :: L) (SEPx R)))
  end.
  { forward. forward. entailer!. apply cle_true; rep_lia. }
  { exfalso. exact (Int.one_not_zero ltac:(assumption)). }
  forward_call Int.one.
  forward. forward.
  (* free the two buffers *)
  sep_apply (pws_unfold (pw_tok take piece) (pw_tok room out)).
  sep_apply (mbuf_to_free take (zbytes (sublist read (read + take) l)) piece).
  forward_call (tarray tuchar take, piece, gv).
  sep_apply (mbuf_to_free room oc' out).
  forward_call (tarray tuchar room, out, gv).
  forward_call r.
  (* a reset after an error; any other time, a reset or not *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX b: bool, PROPx ((is_error_code r = true -> b = true) :: P)
                 (LOCALx (temp _t'19 (Vint (if b then Int.one else Int.zero)) :: L) (SEPx R)))
  end.
  { forward. Exists true. entailer!. }
  { forward_call tt. Intros u. forward.
    Exists (u =? 0). entailer!.
    match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rename H into Herr end.
    split.
    - intros E. rewrite E in Herr. exfalso. exact (Int.one_not_zero Herr).
    - destruct (Z.eqb_spec u 0); destruct (zeq u 0); try lia; reflexivity. }
  Intros b.
  forward_if (EX st3: dctx_st,
     PROP (inv_st st3)
     LOCAL (temp _read (Vlong (Int64.repr (read + ipos'))); temp _n (Vlong (Int64.repr n)); temp _input input;
            temp _zds zds; lvar _output tout v_output; lvar _in tin v_in; gvars gv)
     SEP (DC gv zds st3; mem_mgr gv; zstd_globals gv;
          malloc_token Ews (tarray tuchar n) input; data_at Ews (tarray tuchar n) (zbytes l) input;
          data_at_ Tsh tout v_output; data_at_ Tsh tin v_in; TT; has_ext tt)).
  { forward_call (gv, zds, st', ZSTD_reset_session_only).
    Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
    match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [-> ->]; clear H end.
    Exists (set_ex (set_ss st' ss_init) false). entailer!.
    unfold inv_st; simpl; repeat split; auto. }
  { forward. Exists st'. entailer!.
    destruct b; [exfalso; exact (Int.one_not_zero ltac:(assumption)) |].
    match goal with H: is_error_code r = true -> false = true |- _ => rename H into Hb' end.
    destruct (is_error_code r) eqn:Er; [discriminate (Hb' eq_refl) |].
    unfold inv_st; simpl; repeat split; auto. }
  Intros st3.
  (* do { ... } while (nondet_u8() != 0) *)
  forward_call tt. Intros u2.
  forward_if.
  { forward. Exists (read + ipos') st3. entailer!. }
  { forward. Exists st3. entailer!. }
Qed.

End Main.

(* ---------- from G0 to Gprog (Specs_api DC DD) Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's copy_of, any_bytes
   and upto (laws_common.h) *)
Definition Hs : funspecs :=
  [@Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   Zstd.proof.harness.frames.FSpecs.upto_spec].

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
                       Zstd.proof.harness.frames.FSpecs.upto_spec; main_spec]).
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

Theorem rj_any_stream_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
    + (* copy_of *)
      exists f_copy_of. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_copy_of = Zstd.proof.harness.frames.FSpecs.f_copy_of) by (vm_compute; reflexivity).
      rewrite E. apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ (@Zstd.proof.harness.frames.FSpecs.G_copy_of CompSpecs)).
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
