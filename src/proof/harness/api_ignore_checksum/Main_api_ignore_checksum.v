(* The harness obligation of api_ignore_checksum (harness/api_ignore_checksum.c): for ANY predicates DC, DD of
   the decoder's API (Spec_api6, with ZSTD_XXH64's specification, which new_frame calls), the helpers of
   laws_common.h and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main: new_frame's frame with a Content_Checksum (frame[4] & 4) gets any 4 bytes in place of the checksum
   (put_le); ZSTD_DCtx_setParameter(forceIgnoreChecksum, 1) makes the context's mode md_ignore = true, so
   ZSTD_decompressDCtx's claim (oneshot_dctx) is about a series the model decodes to the frame's content
   (Facts_api_ignore_checksum.nf_series_ignore): a result that is not an error is exactly the content, and an
   error is a too small capacity (excluded: cap >= n) or memory_allocation (out_of_memory ends the run).
   The buffers have any size up to PTRDIFF_MAX: this needs the one-shot specifications with sizes up to
   2 ^ 63 - 1 (stage 1 of the size bounds of Spec_api6). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_ignore_checksum.HOK_api_ignore_checksum.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.zstd.Spec_xxh.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame.
Require Import Zstd.proof.harness.api_ignore_checksum.Facts_api_ignore_checksum.

Local Ltac expand_main_pre ::= idtac.
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
    (QPprog_vars Zstd.contracts.api_ignore_checksum.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_ignore_checksum.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_ignore_checksum.whole_prog)).
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


Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

(* the token of the data, lent to new_frame as its pointer witness (for 0 bytes) *)
Lemma tok_pw sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- Spec_xxh.pw_pred (Spec_xxh.pw_token sh (tarray tuchar n) p).
Proof. unfold Spec_xxh.pw_pred. apply tok_to_Z. Qed.

Lemma pw_tok sh n p :
  Spec_xxh.pw_pred (Spec_xxh.pw_token sh (tarray tuchar n) p) |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof. unfold Spec_xxh.pw_pred. apply tok_of_Z. Qed.

Lemma drop_vp (P: mpred) p : (P && valid_pointer p) |-- P.
Proof. apply andp_left1. apply derives_refl. Qed.

(* the harness's test frame[4] & 4: byte 4 is the Frame_Header_Descriptor *)
Lemma frame_byte4 d fcs did c : 4 < Zlength (nf_bytes d fcs did c) ->
  Znth 4 (zbytes (nf_bytes d fcs did c)) = Vint (Int.repr (nh_fhd (nc_hdr c))).
Proof.
  intros H. rewrite Znth_map by lia.
  rewrite <- (nf_byte4 d fcs did c []), app_nil_r. reflexivity.
Qed.

(* frame + len - 4 *)
Lemma frame_end_ptr b o L : 4 <= L <= Int64.max_signed ->
  Vptr b (Ptrofs.sub (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr L)))) (Ptrofs.repr 4)) =
  Vptr b (Ptrofs.add o (Ptrofs.repr (L - 4))).
Proof.
  intros H. f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by rep_lia.
  unfold Ptrofs.sub, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr L), (Ptrofs.unsigned_repr 4), (Ptrofs.unsigned_repr (L - 4)) by rep_lia.
  apply Ptrofs.eqm_samerepr.
  replace (Ptrofs.unsigned o + (L - 4)) with ((Ptrofs.unsigned o + L) - 4) by lia.
  apply Ptrofs.eqm_sub; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr | apply Ptrofs.eqm_refl].
Qed.

(* ---------- the frame after put_le: its last 4 bytes replaced ---------- *)

Lemma put_checksum (F: list Z) v :
  4 <= Zlength F ->
  Spec_util.mem_written (zbytes F) (Zlength F - 4) 4 v =
  zbytes (firstn (Z.to_nat (Zlength F - 4)) F ++ le_bytes 4 v).
Proof.
  intros H. unfold Spec_util.mem_written. rewrite map_app.
  rewrite !Zlength_map. replace (Zlength F - 4 + 4) with (Zlength F) by lia.
  rewrite sublist_nil, app_nil_r. f_equal.
  rewrite sublist_map, sublist_firstn. reflexivity.
Qed.

Lemma put_checksum_length (F: list Z) v :
  4 <= Zlength F -> Zlength (firstn (Z.to_nat (Zlength F - 4)) F ++ le_bytes 4 v) = Zlength F.
Proof.
  intros H. rewrite Zlength_app, Zlength_firstn, ff_le_bytes_Zlength. simpl. lia.
Qed.

Lemma put_checksum_ok (F: list Z) v :
  bytes_ok F -> bytes_ok (firstn (Z.to_nat (Zlength F - 4)) F ++ le_bytes 4 v).
Proof.
  intros H. apply ff_bytes_ok_app; [| apply ff_le_bytes_ok].
  unfold bytes_ok in *. apply Forall_forall. intros x Hx. apply firstn_In in Hx.  
  rewrite Forall_forall in H. auto.
Qed.

(* the parameters after ZSTD_DCtx_setParameter(dctx, ZSTD_d_forceIgnoreChecksum, 1) on a new context *)
Definition par_ign : dparams :=
  {| dp_fmt := 0; dp_ignore := 1; dp_bmax := 0; dp_wmax := dp_wmax_dflt; dp_multi := 0 |}.

Lemma dmode_ign : dmode_of par_ign =
  {| md_magicless := false; md_ignore := true; md_bmax := ZSTD_BLOCKSIZE_MAX; md_dwin := false |}.
Proof. reflexivity. Qed.

(* the context after setParameter has no dictionary resources *)
Lemma res_ign_i DD0 gv sh :
  emp |-- dict_res DD0 gv sh (dc_dict (set_par dctx_init par_ign)) *
          set_res DD0 gv sh (dc_set (set_par dctx_init par_ign)) (dc_dict (set_par dctx_init par_ign)).
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Lemma res_ign_e DD0 gv sh :
  dict_res DD0 gv sh (dc_dict (set_par dctx_init par_ign)) *
  set_res DD0 gv sh (dc_set (set_par dctx_init par_ign)) (dc_dict (set_par dctx_init par_ign)) |-- emp.
Proof. simpl. rewrite emp_sepcon. apply derives_refl. Qed.

Section Main.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

(* the functions main calls *)
Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_createDCtx_spec DC; ZSTD_DCtx_setParameter_spec DC;
   nondet_u32_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.new_frame_spec CompSpecs; @Zstd.proof.harness.frames.FSpecs.put_le_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.out_of_memory_spec].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_ignore_checksum.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  forward_call (gv, n).
  Intros vret. destruct vret as [pdata d]. cbn [fst snd] in *.
  unfold FSpecs.mbytes.
  repeat apply -> seq_assoc.
  destruct (eq_dec pdata nullval) as [Hpn|Hpn].
  { (* no data: frame is NULL and the run ends at the first test *)
    subst pdata. apply semax_if_seq. forward_if; [| contradiction]. forward. forward.
    forward_call (9223372036854775807 - n). Intros u. forward.
    forward_call (tarray tuchar (n + u), gv). { simpl; rep_lia. } Intros pd.
    forward_call gv. Intros dctx.
    repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| contradiction]. forward.
    do 3 (repeat apply -> seq_assoc; apply semax_if_seq;
          forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]; forward).
    forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  Intros. subst n.
  apply semax_if_seq. forward_if; [contradiction |].
  forward_if (temp _t'4 (Vint (Int.repr 31))); [discriminate | forward; entailer! |].
  sep_apply (tok_pw Ews (Zlength d) pdata).
  forward_call (gv, Ews, pdata, d, Zlength d, 2 ^ 31, 0, Tsh, v_len,
                Spec_xxh.pw_token Ews (tarray tuchar (Zlength d)) pdata).
  { simpl Spec_xxh.pw_pred.
    eapply derives_trans; [apply malloc_token_valid_pointer; simpl; rep_lia | apply valid_pointer_weak]. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  sep_apply (pw_tok Ews (Zlength d) pdata).
  forward. forward.
  destruct (eq_dec q nullval) as [Hq|Hq].
  { (* no frame: the run ends at the first test *)
    subst q.
    forward_call (9223372036854775807 - Zlength d). Intros u. forward.
    forward_call (tarray tuchar (Zlength d + u), gv). { simpl; rep_lia. } Intros pd.
    forward_call gv. Intros dctx.
    repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| contradiction]. forward.
    do 3 (repeat apply -> seq_assoc; apply semax_if_seq;
          forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]; forward).
    forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  Intros c. unfold FSpecs.mbytes. rewrite if_false by exact Hq. Intros.
  match goal with H: nf_ok _ _ _ _ _ |- _ => rename H into Hok end.
  match goal with H: d' = nf_data d c |- _ => subst d' end.
  match goal with H: Zlength d <= (FSpecs.PTRDIFF_MAX - 26) / 4 |- _ => rename H into Hn end.
  unfold FSpecs.PTRDIFF_MAX in Hn. simpl in Hn.
  set (F := nf_bytes d (Zlength d) 0 c) in *.
  pose proof (nf_bytes_length _ _ _ _ _ Hok) as HF. fold F in HF.
  forward_call (9223372036854775807 - Zlength d). Intros u. forward.
  forward_call (tarray tuchar (Zlength d + u), gv). { simpl; rep_lia. } Intros pd.
  forward_call gv. Intros dctx.
  assert_PROP (isptr q) as Hq' by entailer!.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [contradiction |].
  destruct (eq_dec pd nullval) as [Hpd|Hpd].
  { subst pd. forward.
    do 3 (repeat apply -> seq_assoc; apply semax_if_seq;
          forward_if; [| first [contradiction | exfalso; exact (Int.one_not_zero ltac:(assumption))]]; forward).
    forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  Intros. assert_PROP (isptr pd) as Hpd' by entailer!.
  destruct pd as [| | | | | bd od]; try contradiction. forward.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [discriminate |].
  destruct (eq_dec dctx nullval) as [Hdn|Hdn].
  { subst dctx. forward.
    do 2 (repeat apply -> seq_assoc; apply semax_if_seq;
          forward_if; [| first [contradiction | exfalso; exact (Int.one_not_zero ltac:(assumption))]]; forward).
    forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  pose proof (isptr_of dctx PNdctx Hdn) as Hdp.
  destruct dctx as [| | | | | bx ox]; try contradiction. forward.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [discriminate |].
  sep_apply (drop_vp (DC gv (Vptr bx ox) dctx_init) (Vptr bx ox)).
  (* frame[4] & 4: the Content_Checksum_flag *)
  assert (H4F: Znth 4 F = nh_fhd (nc_hdr c))
    by (unfold F; rewrite <- (nf_byte4 d (Zlength d) 0 c []), app_nil_r; reflexivity).
  pose proof Hok as [Hh _].
  pose proof Hh as (Hf03 & _ & _ & _ & _ & Hbits & Hd03 & _).
  destruct (ff_fhd_facts _ Hf03 Hbits Hd03) as (Hfb & _).
  forward. { entailer!. rewrite H4F. simpl. rep_lia. }
  rewrite H4F. forward.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
  { (* no Content_Checksum: the run ends *)
    forward. forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  assert (Hck: nh_checksum (nc_hdr c) = true).
  { apply (nf_fhd_checksum _ _ _ _ Hh). intros E.
    match goal with H: Int.and _ _ <> _ |- _ => apply H end.
    unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. rewrite E. reflexivity. }
  (* ZSTD_DCtx_setParameter(dctx, ZSTD_d_forceIgnoreChecksum, 1) *)
  forward_call (gv, Vptr bx ox, dctx_init, ZSTD_d_forceIgnoreChecksum, 1).
  { do 3 right; left; reflexivity. }
  Intros vret. destruct vret as [r0 st1]. cbn [fst snd] in *.
  match goal with H: after_stage _ _ _ _ |- _ =>
    apply after_stage_init in H; [unfold setpar_res in H | reflexivity] end.
  match goal with H: (if _ then _ else _) |- _ =>
    change (param_set (dc_par dctx_init) ZSTD_d_forceIgnoreChecksum 1) with (Some par_ign) in H;
    change (ZSTD_d_forceIgnoreChecksum =? ZSTD_d_stableOutBuffer) with false in H;
    cbv iota in H; destruct H as [-> ->] end.
  forward_call 0.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [contradiction |].
  (* any 4 bytes in place of the Content_Checksum *)
  forward_call tt. Intros v.
  forward.
  destruct q as [| | | | | bq oq]; try contradiction.
  assert (E: data_at Ews (tarray tuchar (Zlength F)) (zbytes F) (Vptr bq oq) =
             data_at Ews (tarray tuchar (Zlength (zbytes F))) (zbytes F) (Vptr bq oq))
    by (rewrite Zlength_map; reflexivity).
  rewrite E. clear E.
  forward_call (Ews, Vptr bq oq, zbytes F, Zlength F - 4, v, 4).
  { entailer!. simpl. rewrite Int.unsigned_repr by rep_lia. rewrite frame_end_ptr by rep_lia. reflexivity. }
  { rewrite Zlength_map. lia. }
  rewrite Zlength_map, put_checksum by lia.
  set (F' := firstn (Z.to_nat (Zlength F - 4)) F ++ le_bytes 4 v).
  assert (HF'l: Zlength F' = Zlength F) by (apply put_checksum_length; lia).
  rewrite <- HF'l.
  assert (HF'ok: bytes_ok F') by (apply put_checksum_ok; eapply nf_bytes_ok; eauto).
  (* the model: with checksums ignored, F' decodes to the frame's content *)
  assert (Hdec: decode_series_m (dmode_of par_ign) sel_none (Some no_dict) no_wlim F' = SOk (nf_data d c)).
  { apply (nf_series_ignore _ _ _ d (Zlength d) (2 ^ 31) 0 c v Hok H1); try reflexivity; auto.
    - change (2 ^ 64) with 18446744073709551616. lia.
    - change (2 ^ 32) with 4294967296. lia.
    - apply (nf_wlog_ok _ _ _ _ Hh). reflexivity.
    - destruct Hh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw). unfold no_wlim.
      change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in Hw. lia. }
  forward.
  rewrite add64_repr.
  sep_apply (to_Z Ews (Zlength F') (zbytes F') (Vptr bq oq)).
  sep_apply (to_Z_ Ews (Zlength d + u) (Vptr bd od)).
  sep_apply (tok_to_Z Ews (Zlength F') (Vptr bq oq)).
  sep_apply (tok_to_Z Ews (Zlength d + u) (Vptr bd od)).
  sep_apply (pws_fold (tarray tuchar (Zlength F')) (Vptr bq oq) (tarray tuchar (Zlength d + u)) (Vptr bd od)).
  sep_apply (res_ign_i DD gv Ews).
  forward_call ([pw_token Ews (tarray tuchar (Zlength F')) (Vptr bq oq); pw_token Ews (tarray tuchar (Zlength d + u)) (Vptr bd od)],
                gv, Vptr bx ox, set_par dctx_init par_ign, Ews, Ews, Vptr bd od, Zlength d + u, Ews, Vptr bq oq, F').
  { cancel. }
  { split; (apply buf_ok_tok; [simpl; tauto | auto | lia | auto]). }
  Intros vret. destruct vret as [[r out] st2]. cbn [fst snd] in *.
  sep_apply (res_ign_e DD gv Ews).
  sep_apply pws_unfold.
  unfold mbuf; rewrite if_false by discriminate.
  sep_apply (of_Z Ews (Zlength d + u) out (Vptr bd od)).
  match goal with Hk: oneshot_dctx _ _ _ _ _ |- _ =>
    unfold oneshot_dctx in Hk; simpl dc_set in Hk; cbv iota in Hk;
    simpl dictref_model in Hk; destruct Hk as [Hle Hm]; simpl dc_par in Hm; rewrite Hdec in Hm;
    destruct Hm as [Hok_r Herr_r] end.
  forward.
  forward_call r.
  destruct (Z.eq_dec (Spec_util.error_of r) 64) as [Hoom|Hoom].
  { (* out of memory: the run ends *)
    forward_if; [| exfalso; exact (Int.one_not_zero ltac:(assumption))]. forward. cancel. }
  forward_if; [contradiction |].
  (* not an error (memory_allocation is excluded, and cap >= n): exactly the content *)
  assert (Er: is_error_code r = false).
  { destruct (is_error_code r) eqn:E; [| reflexivity].
    destruct (Herr_r eq_refl) as [Hc | Hc]; [lia | subst r; exfalso; apply Hoom; reflexivity]. }
  destruct (Hok_r Er) as [Hr Hout]. rewrite H2 in Hr. subst r.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [| contradiction].
  (* bytes_eq(dst, data, n): dst's first n bytes and the data are both the content *)
  set (D := nf_data d c) in *.
  rewrite (split2_data_at_Tarray_tuchar Ews (Zlength d + u) (Zlength d) out (Vptr bd od)) by lia.
  rewrite Hout.
  assert (E1: data_at Ews (Tarray tuchar (Zlength d) noattr) (zbytes D) (Vptr bd od) =
              data_at Ews (tarray tuchar (Zlength D)) (zbytes D) (Vptr bd od)) by (rewrite H2; reflexivity).
  assert (E2: data_at Ews (tarray tuchar (Zlength d)) (zbytes D) pdata =
              data_at Ews (tarray tuchar (Zlength D)) (zbytes D) pdata) by (rewrite H2; reflexivity).
  rewrite E1, E2. clear E1 E2.
  (* the call alone (VST's call-with-cast rule does not take the cast int -> _Bool) *)
  apply -> seq_assoc.
  forward_call (Ews, Vptr bd od, D, Ews, pdata, D).
  { entailer!. rewrite H2. reflexivity. }
  { cancel. }
  destruct (list_eq_dec Z.eq_dec D D) as [_ | Hne]; [| contradiction].
  forward.
  forward_call Int.one.
  forward. cancel.
Qed.

End Main.

(* ---------- from G0 to Gprog (API DC DD) Hs ---------- *)

(* the API the harness imports: the decoder's (Spec_api6) and ZSTD_XXH64, which new_frame calls *)
Definition API (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) : funspecs :=
  Specs_api DC DD ++ [Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's *)
Definition Hs : funspecs :=
  [Zstd.proof.harness.frames.FSpecs.out_of_memory_spec; @Zstd.proof.harness.frames.FSpecs.copy_of_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs; Zstd.proof.harness.frames.FSpecs.upto_spec;
   @Zstd.proof.harness.frames.FSpecs.put_le_spec CompSpecs; @Zstd.proof.harness.frames.FSpecs.bytes_eq_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.new_frame_spec CompSpecs].

Lemma Externals_eq :
  Externals = [nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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

Lemma Gprog_cons DC DD : Gprog (API DC DD) Hs =
  (_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') ::
  (Specs_api DC DD ++ [Spec_xxh.ZSTD_XXH64_spec;
                       nondet_u8_spec; nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec;
                       gp_assume_spec] ++ Hs ++ [main_spec]).
Proof. unfold Gprog, Imports, API. rewrite Externals_eq. cbn [app]. rewrite <- app_assoc. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api, Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (API DC DD) Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Specs_api, Hs. cbn [app].
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (API DC DD) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (API DC DD) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

(* a helper of the frames kit: its body here is the kit's, proved in the kit's context Gk *)
Ltac kit_body f fk Gk body :=
  exists f; split; [vm_compute; reflexivity |]; split; [reflexivity |];
  let E := fresh "E" in
  assert (E: f = fk) by (vm_compute; reflexivity);
  rewrite E; apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [exact body | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog].

Theorem api_ignore_checksum_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (API DC DD) Hs.
Proof.
  intros DC DD. exists Hs. split.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [.. | apply Forall_nil].
    + kit_body f_out_of_memory Zstd.proof.harness.frames.FSpecs.f_out_of_memory
        Zstd.proof.harness.frames.FSpecs.G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body f_copy_of Zstd.proof.harness.frames.FSpecs.f_copy_of
        (@Zstd.proof.harness.frames.FSpecs.G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body f_any_bytes Zstd.proof.harness.frames.FSpecs.f_any_bytes
        (@Zstd.proof.harness.frames.FSpecs.G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body f_upto Zstd.proof.harness.frames.FSpecs.f_upto
        Zstd.proof.harness.frames.FSpecs.G_upto
        (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body f_put_le Zstd.proof.harness.frames.FSpecs.f_put_le
        Zstd.proof.harness.frames.FSpecs.G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body f_bytes_eq Zstd.proof.harness.frames.FSpecs.f_bytes_eq
        Zstd.proof.harness.frames.FSpecs.G_bytes_eq
        (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq CompSpecs).
    + kit_body f_new_frame Zstd.proof.harness.frames.FSpecs.f_new_frame
        (@Zstd.proof.harness.frames.FSpecs.G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
      apply tycontext_sub_i99. split; intro i.
      * (* both lists abstracted, so that the rewriting never compares them with the empty one by computation *)
        remember (G0 DC DD) as GG eqn:HGG. remember (Gprog (API DC DD) Hs) as GP eqn:HGP.
        rewrite (make_tycontext_g_find Vprog GG i), (make_tycontext_g_find Vprog GP i).
        subst GG GP.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (API DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
