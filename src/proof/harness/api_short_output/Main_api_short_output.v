(* The harness obligation of api_short_output (harness/api_short_output.c), with the API
   [ZSTD_decompress_spec; ZSTD_getErrorCode_spec; ZSTD_XXH64_spec] (new_frame computes a checksum with
   ZSTD_XXH64): the helpers of laws_common.h and frames.h (proved once in the frames kit) and main satisfy their
   specifications.

   main builds a frame of any data of n >= 1 bytes (new_frame, Frame_Content_Size n or none, no dictionary, a
   window up to ONE_CALL_WINDOW) and gives it to ZSTD_decompress with a capacity cap < n, in an object of cap bytes or,
   for cap = 0, possibly NULL (malloc(0)).  The model decodes the frame to nf_data d c, of n bytes, with Raw and RLE
   blocks only (Facts_api_short_output.nf_series_rr), so the error codes of ZSTD_decompress (Spec_codes.oneshot_codes)
   give ZSTD_error_dstSize_tooSmall or ZSTD_error_memory_allocation; out_of_memory ends the run on the second.
   ZSTD_decompress_spec takes an empty output passed as NULL (Spec_api6.mbuf, fix F9) and gives the error codes; the
   frame has up to 26 + 4 n <= PTRDIFF_MAX bytes, within its size bounds. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_short_output.HOK_api_short_output.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FSpecs.
Require Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FBodyNewFrame.
Require Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.frames.FKit.
Require Import Zstd.proof.harness.api_short_output.Facts_api_short_output.
Local Open Scope logic.

Local Ltac expand_main_pre ::= idtac.

(* the API of the law *)
Definition API : funspecs :=
  [ZSTD_decompress_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main, in the order of helper_ids *)
Definition Hs : funspecs :=
  [out_of_memory_spec; copy_of_spec; any_bytes_spec; upto_spec; put_le_spec; new_frame_spec].

Lemma Hs_ids : map fst Hs = helper_ids.
Proof. vm_compute. reflexivity. Qed.

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
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.api_short_output.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_short_output.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_short_output.whole_prog)).
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
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at__bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

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

Lemma pws_fold t1 p1 t2 p2 :
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2) |--
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

Lemma pws_unfold t1 p1 t2 p2 :
  pws_pred [pw_token Ews t1 p1; pw_token Ews t2 p2] |--
  (@malloc_token Zstd.units.Zstd.CS Ews t1 p1 * @malloc_token Zstd.units.Zstd.CS Ews t2 p2).
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

(* a malloc_token as a witness of the decoder's specifications (Spec_xxh.pw_pred) and back *)
Lemma tok_pw n p : @malloc_token CompSpecs Ews (tarray tuchar n) p |--
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar n) p).
Proof. simpl. apply tok_to_Z. Qed.

Lemma pw_tok n p : Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar n) p) |--
  @malloc_token CompSpecs Ews (tarray tuchar n) p.
Proof. simpl. apply tok_of_Z. Qed.

(* the output buffer of ZSTD_decompress (Spec_api6.mbuf): a malloc'ed object, or NULL for 0 bytes *)
Lemma to_mbuf sh n p : isptr p -> @data_at_ CompSpecs sh (tarray tuchar n) p |-- mbuf sh n (Zrepeat Vundef n) p.
Proof.
  intros Hp. unfold mbuf. rewrite if_false by (intro; subst; contradiction).
  sep_apply (to_Z_ sh n p). rewrite data_at__eq. apply derives_refl.
Qed.

Lemma mbuf_null_intro (P: mpred) sh : P |-- P * mbuf sh 0 (Zrepeat Vundef 0) nullval.
Proof.
  unfold mbuf. rewrite if_true by reflexivity. rewrite prop_true_andp by (split; reflexivity).
  rewrite sepcon_emp. apply derives_refl.
Qed.

(* the condition on the buffers' pointers holds for NULL (data_at_ at NULL is false) *)
Lemma buf_ok_null W sh n : buf_ok W sh n nullval.
Proof. unfold buf_ok. rewrite data_at__isptr. Intros. contradiction. Qed.

Lemma pws_fold1 t1 p1 :
  @malloc_token Zstd.units.Zstd.CS Ews t1 p1 |-- pws_pred [pw_token Ews t1 p1].
Proof. unfold pws_pred. simpl. rewrite sepcon_emp. apply derives_refl. Qed.

(* the witness new_frame and ZSTD_XXH64 need for 0 bytes of data: the data's malloc_token *)
Lemma tok_wvp p : isptr p ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar 0) p) |-- weak_valid_pointer p.
Proof.
  intros Hp. simpl. eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.


(* the if-statement first in a sequence: the rest goes into both branches *)
Ltac ifs := try (match goal with H := @abbreviate statement _ |- _ => unfold abbreviate in H; subst H end);
  repeat apply -> seq_assoc;
  apply semax_if_seq.

(* frame == NULL: the test of the harness returns *)
Ltac end_null :=
  ifs; forward_if; [| contradiction]; forward;
  ifs; forward_if; [| discriminate]; forward;
  ifs; forward_if; [| discriminate]; forward; cancel.

(* n != 0 from the C test *)
Ltac n_pos := match goal with Hn: Int64.repr ?n <> Int64.repr 0 |- _ =>
  assert (n <> 0) by (let E := fresh in intro E; apply Hn; rewrite E; reflexivity) end.

(* a branch whose test is false *)
Ltac nope := exfalso; first [solve [auto] | apply Int.one_not_zero; assumption | discriminate | contradiction].

(* after ZSTD_decompress: the model gives dstSize_tooSmall or a memory error; out_of_memory and the check *)
Ltac check_tail :=
  let vret := fresh "vret" in
  let Hrr := fresh "Hrr" in
  let Hcode := fresh "Hcode" in
  Intros vret; destruct vret as [r out]; cbn [fst snd] in *;
  forward;
  match goal with H5: nf_ok (Zlength ?l) _ _ _ ?c, H1: bytes_ok ?l, Hc: oneshot_codes _ _ _ _ _ _ |- _ =>
    destruct Hc as [_ Hrr];
    assert (Hcode: r = err_code ZSTD_error_dstSize_tooSmall \/ r = err_code ZSTD_error_memory_allocation)
      by (apply (Hrr (nf_data l c));
          [apply nf_series_rr; [exact H5 | exact H1 | rep_lia]
          | rewrite (nf_data_length l (Zlength l) (2 ^ 31) 0 c H5); lia])
  end;
  forward_call r;
  destruct Hcode as [-> | ->];
  [ change (error_of (err_code ZSTD_error_dstSize_tooSmall)) with 70;
    rewrite if_false by lia;
    ifs; forward_if; [nope |];
    forward_call (err_code ZSTD_error_dstSize_tooSmall);
    change (error_of (err_code ZSTD_error_dstSize_tooSmall)) with 70;
    forward_call Int.one;
    forward; cancel
  | change (error_of (err_code ZSTD_error_memory_allocation)) with 64;
    change (if Z.eq_dec 64 64 then Int.one else Int.zero) with Int.one;
    ifs; forward_if; [forward; cancel | nope] ].

(* the context of main's body *)
Definition G : funspecs := Gprog API Hs.

Lemma body_main : semax_body Vprog G f_main main_spec.
Proof.
  change (semax_body Vprog G f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_short_output.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  (* the data: any n bytes *)
  forward_call 9223372036854775807.
  Intros n.
  forward_call (gv, n).
  Intros vret. destruct vret as [p l]. cbn [fst snd] in *.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec p nullval) as [Hp0 | Hp0].
  { (* no data: frame = NULL, the run ends *)
    subst p. forward_if; [| contradiction].
    forward. forward.
    ifs. forward_if.
    - forward. forward.
      forward_call (tarray tuchar 0, gv). { simpl. rep_lia. }
      Intros pd. end_null.
    - n_pos. forward_call (n - 1).
      Intros cap. forward.
      forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
      Intros pd. end_null. }
  (* the frame *)
  subst n. unfold mbytes. rewrite if_false by exact Hp0. Intros.
  assert_PROP (isptr p) as Hp by entailer!.
  forward_if; [contradiction |].
  ifs. forward_if; [discriminate |]. forward.
  sep_apply (tok_pw (Zlength l) p).
  forward_call (gv, Ews, p, l, Zlength l, 2 ^ 31, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) p).
  { match goal with E: Zlength l = 0 |- _ => rewrite E end. apply tok_wvp. exact Hp. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  forward. forward.
  destruct (eq_dec q nullval) as [Hq | Hq].
  { (* out of memory in new_frame: the run ends *)
    subst q. ifs. forward_if.
    - forward. forward.
      forward_call (tarray tuchar 0, gv). { simpl. rep_lia. }
      Intros pd. end_null.
    - n_pos. forward_call (Zlength l - 1).
      Intros cap. forward.
      forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
      Intros pd. end_null. }
  Intros c. set (F := nf_bytes l (Zlength l) 0 c) in *.
  unfold mbytes. rewrite if_false by exact Hq. Intros.
  assert_PROP (isptr q) as Hq' by entailer!.
  ifs. forward_if.
  { (* no data: the run ends *)
    match goal with Hn: Int64.repr (Zlength l) = Int64.zero |- _ =>
      assert (Hl0: Zlength l = 0) by (apply (f_equal Int64.unsigned) in Hn;
        rewrite Int64.unsigned_repr in Hn by rep_lia; exact Hn) end.
    forward. forward.
    forward_call (tarray tuchar 0, gv). { simpl. rep_lia. }
    Intros pd.
    ifs. forward_if; [contradiction |]. forward.
    rewrite Hl0.
    change (bool2val (Int64.cmpu Ceq (Int64.repr 0) (Int64.repr (Int.signed (Int.repr 0))))) with (Vint Int.one).
    ifs. forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))].
    forward. ifs. forward_if; [forward; cancel | discriminate]. }
  (* n >= 1: any capacity below n *)
  n_pos.
  forward_call (Zlength l - 1). Intros cap. forward.
  forward_call (tarray tuchar cap, gv). { simpl. rep_lia. }
  Intros pd.
  ifs. forward_if; [contradiction |]. forward.
  assert (Hn0: Int64.cmpu Ceq (Int64.repr (Zlength l)) (Int64.repr (Int.signed (Int.repr 0))) = false).
  { unfold Int64.cmpu. apply Int64.eq_false. change (Int.signed (Int.repr 0)) with 0. assumption. }
  rewrite Hn0. change (bool2val false) with (Vint Int.zero).
  ifs. forward_if; [exfalso; auto |].
  assert (HF: 9 <= Zlength F <= 26 + 4 * Zlength l) by exact (nf_bytes_length l (Zlength l) (2 ^ 31) 0 c H5).
  assert (Hn': Zlength l <= 2305843009213693945) by exact H7.   (* (PTRDIFF_MAX - 26) / 4 *)
  destruct (eq_dec pd nullval) as [Hpd | Hpd].
  { subst pd. ifs. forward_if; [| contradiction]. forward. forward.
    ifs. forward_if.
    - forward. cancel.
    - (* cap = 0 and malloc(0) returned NULL: ZSTD_decompress(NULL, 0, frame, len), item (N) *)
      match goal with Hc: Int64.repr cap = Int64.zero |- _ =>
        assert (Hc0: cap = 0) by (apply (f_equal Int64.unsigned) in Hc;
          rewrite Int64.unsigned_repr in Hc by rep_lia; exact Hc) end.
      subst cap.
      forward.
      sep_apply (to_Z Ews (Zlength F) (zbytes F) q).
      sep_apply (tok_to_Z Ews (Zlength F) q).
      sep_apply (pws_fold1 (tarray tuchar (Zlength F)) q).
      sep_apply (mbuf_null_intro (mem_mgr gv) Ews).
      forward_call ([pw_token Ews (tarray tuchar (Zlength F)) q], gv, Ews, nullval, 0, Ews, q, F).
      { cancel. }
      { split; [apply buf_ok_null |].
        split; [apply buf_ok_tok; [simpl; tauto | auto | lia | auto] |].
        apply (nf_bytes_ok l (Zlength l) (2 ^ 31) 0 c H5 H1). }
      check_tail. }
  Intros.
  assert_PROP (isptr pd) as Hpd' by entailer!.
  destruct pd as [| | | | | bd od]; try contradiction.
  ifs. forward_if; [discriminate |]. forward.
  ifs. forward_if; [exfalso; auto |].
  set (pd := Vptr bd od) in *.
  (* ZSTD_decompress(dst, cap, frame, len), the buffers at the decoder's compspecs *)
  forward.
  sep_apply (to_Z Ews (Zlength F) (zbytes F) q).
  sep_apply (to_mbuf Ews cap pd Hpd').
  sep_apply (tok_to_Z Ews (Zlength F) q).
  sep_apply (tok_to_Z Ews cap pd).
  sep_apply (pws_fold (tarray tuchar (Zlength F)) q (tarray tuchar cap) pd).
  forward_call ([pw_token Ews (tarray tuchar (Zlength F)) q; pw_token Ews (tarray tuchar cap) pd],
                gv, Ews, pd, cap, Ews, q, F).
  { split; [apply buf_ok_tok; [simpl; tauto | auto | lia | auto] |].
    split; [apply buf_ok_tok; [simpl; tauto | auto | lia | auto] |].
    apply (nf_bytes_ok l (Zlength l) (2 ^ 31) 0 c H5 H1). }
  check_tail.
Qed.

(* ---------- the harness unit's obligation ---------- *)

Lemma Externals_eq :
  Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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

Lemma Gprog_cons : Gprog API Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (API ++ [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
   Hs ++ [main_spec]).
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry of a body's context found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold API, Hs; cbn [app]; find_steps; reflexivity end.

(* a helper of the frames kit: the harness's body is the kit's Clight term (the lookup in the harness's
   definitions computes to it), proved once in the kit and moved into Gprog *)
Ltac kit_body fk Gk body :=
  exists fk; split; [vm_compute; reflexivity |]; split; [reflexivity |];
  apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

Theorem api_short_output_ok : HarnessOK API Hs.
Proof.
  split; [exact Hs_ids |].
  repeat apply Forall_cons; try apply Forall_nil.
  - kit_body FSpecs.f_out_of_memory G_out_of_memory
      Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory.
  - kit_body FSpecs.f_copy_of (@G_copy_of CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
  - kit_body FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
  - kit_body FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
  - kit_body FSpecs.f_put_le G_put_le
      (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
  - kit_body FSpecs.f_new_frame (@G_new_frame CompSpecs)
      (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
  - exists f_main. split; [reflexivity |]. split; [reflexivity |]. exact body_main.
Qed.
