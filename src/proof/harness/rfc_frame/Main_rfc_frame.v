(* The harness obligation of rfc_frame (harness/rfc_frame.c): with the API [ZSTD_decompress; ZSTD_getErrorCode;
   ZSTD_XXH64] (the second for out_of_memory, the third for new_frame's checksums), the helpers of laws_common.h
   and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds a frame of new_frame for any data of any length n (content size field n or none, Dictionary_ID 0,
   a window up to ONE_CALL_WINDOW) and decodes it with ZSTD_decompress into a buffer of any capacity cap >= n.
   The model decodes the frame to exactly its content (Facts_rfc_frame), so ZSTD_decompress's specification
   (oneshot_ok) gives either the content (result n, the first n bytes of dst) or the error memory_allocation,
   which out_of_memory recognizes; the check then holds.  The buffers have any size up to PTRDIFF_MAX: this needs
   ZSTD_decompress's specification with sizes up to 2 ^ 63 - 1. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.rfc_frame.HOK_rfc_frame.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame Zstd.proof.harness.frames.FFacts.
Require Import Zstd.proof.harness.rfc_frame.Facts_rfc_frame.
Import Zstd.proof.harness.frames.FSpecs.

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
    (QPprog_vars Zstd.contracts.rfc_frame.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.rfc_frame.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.rfc_frame.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

#[local] Instance CCE_HZ : change_composite_env CompSpecs Zstd.units.Zstd.CS.
Proof. make_cs_preserve CompSpecs Zstd.units.Zstd.CS. Defined.

(* the decoder's specifications are stated at Base.CompSpecs; forward_call moves their frame back to the harness's *)
#[local] Instance CCE_BH : change_composite_env Zstd.proof.zstd.Base.CompSpecs CompSpecs.
Proof. make_cs_preserve Zstd.proof.zstd.Base.CompSpecs CompSpecs. Defined.

Lemma to_Z_ sh n p :
  @data_at_ CompSpecs sh (tarray tuchar n) p |-- @data_at_ Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@data_at__change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p |-- @malloc_token CompSpecs sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ CCE_HZ sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

(* ---------- the pointer witnesses: the malloc_tokens of the buffers ---------- *)

(* a malloc'ed block of 0 bytes: its token shows that its address is valid (new_frame on empty data, ZSTD_decompress
   with cap = 0) *)
Lemma tok_wvp n p : n = 0 ->
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar n) p) |-- weak_valid_pointer p.
Proof.
  intros ->. simpl. eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

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

(* a buffer whose malloc_token is among the witnesses is weakly valid at both ends *)
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

Lemma mbytes_fold {cs: compspecs} n l q : q <> nullval ->
  malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (zbytes l) q |-- mbytes n l q.
Proof. intros Hq. unfold mbytes. rewrite if_false by exact Hq. apply derives_refl. Qed.

Lemma isptr_of p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; auto. subst. contradiction. Qed.

(* the API of the law *)
Definition API : funspecs :=
  [ZSTD_decompress_spec; Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the functions main calls *)
Definition G0 : funspecs :=
  [ZSTD_decompress_spec; (_quickproof_malloc, malloc_spec'); gp_assert_spec;
   upto_spec; any_bytes_spec; new_frame_spec; out_of_memory_spec; bytes_eq_spec].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.rfc_frame.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  Intros vret. destruct vret as [data l]. cbn [fst snd] in *.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec data nullval) as [Hd0|Hd0].
  { (* out of memory: no data, no frame; the run ends *)
    subst data. forward_if; [| contradiction]. forward. forward.
    forward_call (9223372036854775807 - n).
    Intros u. forward.
    forward_call (tarray tuchar (n + u), gv). { simpl. rep_lia. }
    Intros dst.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction]. forward.
    forward_if; [forward; cancel | discriminate]. }
  subst n.
  unfold mbytes at 1. rewrite if_false by exact Hd0. Intros.
  assert_PROP (isptr data) as Hdp by entailer!.
  forward_if; [destruct data; try contradiction; discriminate |].
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if; [discriminate |].
  forward.
  sep_apply (tok_to_Z Ews (Zlength l) data).
  forward_call (gv, Ews, data, l, Zlength l, 2 ^ 31, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength l)) data).
  { simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. cancel. }
  { apply tok_wvp. assumption. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  simpl pw_pred. unfold Zstd.proof.zstd.Base.CompSpecs. sep_apply (tok_of_Z Ews (Zlength l) data).
  forward. forward.
  forward_call (9223372036854775807 - Zlength l).
  Intros u. forward.
  forward_call (tarray tuchar (Zlength l + u), gv). { simpl. rep_lia. }
  Intros dst.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec q nullval) as [Hq0|Hq0].
  { (* out of memory in new_frame: no frame; the run ends *)
    subst q. forward_if; [| contradiction]. forward.
    forward_if; [forward; cancel | discriminate]. }
  Intros c.
  subst d'.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_length l (Zlength l) (2 ^ 31) 0 c H6) as HFl.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_bytes_ok l (Zlength l) (2 ^ 31) 0 c H6 H1) as HFok.
  assert (HnB: 26 + 4 * Zlength l <= 2 ^ 63 - 1).
  { unfold PTRDIFF_MAX in H8. change ((2 ^ 63 - 1 - 26) / 4) with 2305843009213693945 in H8. lia. }
  set (F := nf_bytes l (Zlength l) 0 c) in *.
  unfold mbytes at 1. destruct (eq_dec q nullval) as [C|_]; [contradiction|]. Intros.
  assert_PROP (isptr q) as Hqp by entailer!.
  forward_if; [destruct q; try contradiction; discriminate |].
  destruct (eq_dec dst nullval) as [Hdst|Hdst].
  { (* out of memory for dst; the run ends *)
    subst dst. forward. forward_if; [forward; cancel | ].
    exfalso. match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end. }
  Intros.
  forward.
  assert_PROP (isptr dst) as Hdstp by entailer!.
  destruct dst as [| | | | | bd od]; try contradiction.
  forward_if; [exfalso; lia |].
  forward.
  (* ZSTD_decompress(dst, cap, frame, len), at the decoder's compspecs; the malloc_tokens vouch for the buffers *)
  rewrite add64_repr.
  set (cap := Zlength l + u) in *.
  sep_apply (to_Z Ews (Zlength F) (zbytes F) q).
  sep_apply (to_Z_ Ews cap (Vptr bd od)).
  sep_apply (tok_to_Z Ews (Zlength F) q).
  sep_apply (tok_to_Z Ews cap (Vptr bd od)).
  sep_apply (pws_fold (tarray tuchar (Zlength F)) q (tarray tuchar cap) (Vptr bd od)).
  forward_call ([pw_token Ews (tarray tuchar (Zlength F)) q; pw_token Ews (tarray tuchar cap) (Vptr bd od)],
                gv, Ews, Vptr bd od, cap, Ews, q, F).
  { split; (apply buf_ok_tok; [simpl; tauto | auto | unfold cap; lia | auto]). }
  Intros vret. destruct vret as [r out]. cbn [fst snd] in *.
  unfold mbuf; rewrite if_false by (intro Hn; discriminate Hn).
  match goal with H1: 0 <= r <= _, H2: Zlength out = _, H3: oneshot_ok _ _ _ _ _ _ |- _ =>
    rename H1 into Hr; rename H2 into Hout; rename H3 into Hok1 end.
  sep_apply pws_unfold. Intros.
  forward.
  (* the model: the frame decodes to exactly its content *)
  pose proof (rfc_frame_series l (2 ^ 31) c H6 H1 ltac:(lia) ltac:(lia)) as HS. fold F in HS.
  pose proof (Zstd.proof.harness.frames.FFacts.nf_data_length l (Zlength l) (2 ^ 31) 0 c H6) as HDl.
  destruct Hok1 as [_ Hc]. rewrite HS in Hc. destruct Hc as [Hsucc Herr].
  forward_call r.
  forward_if.
  { forward. entailer!. }
  (* not out of memory: decoding succeeded *)
  assert (Er: is_error_code r = false).
  { destruct (is_error_code r) eqn:E; [| reflexivity].
    destruct (Herr eq_refl) as [Hlt | Hm]; [unfold cap in Hlt; lia |].
    exfalso. subst r. unfold Zstd.proof.zstd.Spec_util.error_of, Zstd.proof.zstd.Spec_util.err_code in *.
    rewrite E in *. simpl in *. apply Int.one_not_zero. assumption. }
  destruct (Hsucc Er) as [Hrn Hsub]. rewrite HDl in Hrn. subst r.
  (* the check: result == n && bytes_eq(dst, data, n) *)
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [| exfalso; match goal with Hx: ?a <> ?a |- _ => apply Hx; reflexivity end].
  rewrite (split2_data_at_Tarray_tuchar Ews cap (Zlength l) out (Vptr bd od)) by (unfold cap; lia).
  rewrite Hsub. Intros.
  sep_apply (of_Z Ews (Zlength l) (zbytes (nf_data l c)) (Vptr bd od)).
  replace (data_at Ews (tarray tuchar (Zlength l)) (zbytes (nf_data l c)))
    with (data_at Ews (tarray tuchar (Zlength (nf_data l c))) (zbytes (nf_data l c))) by (rewrite HDl; reflexivity).
  (* t'12 = bytes_eq(dst, data, n); t'11 = (_Bool) t'12: the call, then the cast as a statement of its own *)
  eapply semax_seq'.
  forward_call (Ews, Vptr bd od, nf_data l c, Ews, data, nf_data l c).
  all: try (entailer!; rewrite HDl; reflexivity).
  destruct (list_eq_dec Z.eq_dec (nf_data l c) (nf_data l c)) as [_|C]; [|contradiction].
  forward. apply andp_left2. apply derives_refl.
  change (Int.eq Int.one Int.zero) with false. cbv iota.
  abbreviate_semax.
  forward_call Int.one.
  forward.
  cancel.
Qed.


(* ---------- from G0 to Gprog API Hs ---------- *)

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers *)
Definition Hs : funspecs :=
  [out_of_memory_spec; @copy_of_spec CompSpecs; @any_bytes_spec CompSpecs; upto_spec; @put_le_spec CompSpecs;
   @bytes_eq_spec CompSpecs; @new_frame_spec CompSpecs].

Lemma Externals_eq : Externals =
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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
  ZSTD_decompress_spec :: Zstd.proof.zstd.Spec_util.ZSTD_getErrorCode_spec :: Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec ::
  [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++
  Hs ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Hs; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog i fs : initial_world.find_id i G0 = Some fs ->
  initial_world.find_id i (Gprog API Hs) = Some fs.
Proof.
  intros Hi. apply initial_world.find_id_e in Hi. unfold G0 in Hi.
  rewrite Gprog_cons. unfold Hs. cbn [app].
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
Lemma Gprog_not_var i : In i (map fst (Gprog API Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog API Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

(* a helper of the frames kit: its body, proved once at any compspecs, in Gprog *)
Ltac kit_body fn fk Gk body :=
  exists fn; split; [vm_compute; reflexivity|]; split; [reflexivity|];
  let E := fresh "E" in
  assert (E: fn = fk) by (vm_compute; reflexivity);
  rewrite E; apply (Zstd.proof.harness.frames.FTransfer.fk_transfer Vprog _ Gk);
  [ exact body
  | apply Zstd.proof.harness.frames.FTransfer.fk_find_all; repeat constructor; in_gprog ].

Theorem rfc_frame_ok : HarnessOK API Hs.
Proof.
  split.
  - vm_compute. reflexivity.
  - constructor; [| constructor; [| constructor; [| constructor; [| constructor; [| constructor;
      [| constructor; [| constructor; [| constructor]]]]]]]].
    + kit_body Zstd.harness.rfc_frame.code.f_out_of_memory FSpecs.f_out_of_memory G_out_of_memory
        (@Zstd.proof.harness.frames.FBodiesSmall.body_out_of_memory CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_copy_of FSpecs.f_copy_of (@G_copy_of CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_any_bytes FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
        (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_upto FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_put_le FSpecs.f_put_le G_put_le
        (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_bytes_eq FSpecs.f_bytes_eq G_bytes_eq
        (@Zstd.proof.harness.frames.FBodiesSmall.body_bytes_eq CompSpecs).
    + kit_body Zstd.harness.rfc_frame.code.f_new_frame FSpecs.f_new_frame (@G_new_frame CompSpecs)
        (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply body_main_G0 |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog G0 i).
        rewrite (make_tycontext_g_find Vprog (Gprog API Hs) i).
        destruct (initial_world.find_id i G0) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog API Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
