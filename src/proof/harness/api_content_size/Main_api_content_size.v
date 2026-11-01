(* The harness obligation of api_content_size (harness/api_content_size.c), with the API
   [ZSTD_getFrameContentSize_spec; ZSTD_XXH64_spec] (new_frame computes a checksum with ZSTD_XXH64): the helpers of
   laws_common.h and frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds an empty frame declaring any content size (new_frame) or a skippable frame (new_skippable), joins
   any bytes after it, and calls ZSTD_getFrameContentSize on the whole input, whose specification returns
   frame_content_size of it.  Facts_api_content_size says what that is: 0 for the skippable frame, otherwise
   ZSTD_CONTENTSIZE_UNKNOWN when the descriptor byte src[4] has neither a Frame_Content_Size_flag nor the
   Single_Segment_flag, and the declared size else: each gp_assert holds.  The input has any size up to
   PTRDIFF_MAX: this uses the frame inspection specifications of Spec_api6 with sources of up to 2 ^ 63 - 1
   bytes (src_spec_pre). *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Pick.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_content_size.HOK_api_content_size.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Import Zstd.proof.harness.frames.FSpecs.
Require Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FBodyNewFrame.
Require Zstd.proof.harness.frames.FTransfer.
Require Import Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.
Require Import Zstd.proof.harness.api_content_size.Facts_api_content_size.
Local Open Scope logic.

Local Ltac expand_main_pre ::= idtac.

(* the API of the law *)
Definition API : funspecs := [ZSTD_getFrameContentSize_spec; Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main, in the order of helper_ids *)
Definition Hs : funspecs :=
  [copy_of_spec; any_bytes_spec; upto_spec; put_le_spec; join_spec; new_skippable_spec; new_frame_spec].

Lemma Hs_ids : map fst Hs = helper_ids.
Proof. vm_compute. reflexivity. Qed.

(* the context of main's body *)
Definition G : funspecs := Gprog API Hs.

(* ---------- main's precondition, local variables ---------- *)

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
    (QPprog_vars Zstd.contracts.api_content_size.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of programs has the x_ laws
   only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_content_size.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_content_size.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* the variable declared as the 8 bytes pick(declared) writes *)
Lemma fc_bytes8 p : field_compatible tulong [] p -> field_compatible (tarray tuchar 8) [] p.
Proof.
  intros (Hp & Hl & Hs & Ha & _). destruct p; try contradiction.
  split; [exact I | split; [reflexivity | split; [| split; [| exact I]]]].
  - simpl in Hs |- *. exact Hs.
  - apply align_compatible_rec_Tarray. intros j Hj.
    eapply align_compatible_rec_by_value; [reflexivity |]. apply Z.divide_1_l.
Qed.

Lemma ulong_bytes p : field_compatible tulong [] p ->
  data_at_ Tsh tulong p |-- data_at_ Tsh (tarray tuchar 8) p.
Proof.
  intros Hfc. rewrite !data_at__memory_block. normalize.
  apply andp_right; [apply prop_right; apply fc_bytes8; exact Hfc | apply derives_refl].
Qed.

(* ---------- byte arrays between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma of_Z sh n v p :
  @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p |-- @data_at CompSpecs sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

(* after new_frame: none[1] is whole again (the empty data array and the witness lent for it) *)
Lemma none_back p :
  @data_at CompSpecs Tsh (tarray tuchar 0) (zbytes []) p *
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] p) |--
  @data_at_ CompSpecs Tsh (tarray tuchar 1) p.
Proof.
  sep_apply (@data_at_zero_array_inv CompSpecs Tsh tuchar (zbytes []) p eq_refl eq_refl).
  rewrite emp_sepcon. simpl Zstd.proof.zstd.Spec_xxh.pw_pred.
  rewrite data_at__eq. change (default_val (tarray tuchar 1)) with [Vundef]. apply of_Z.
Qed.

(* the descriptor byte's tests in C *)
Lemma shr6 x : 0 <= x < 256 -> Int.shr (Int.repr x) (Int.repr 6) = Int.repr (Z.shiftr x 6).
Proof. intros. unfold Int.shr. rewrite Int.signed_repr, Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma and32 x : 0 <= x < 256 -> Int.and (Int.repr x) (Int.repr 32) = Int.repr (Z.land x 32).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

(* none[1] makes the pointer new_frame hashes from weakly valid *)
Lemma none_valid p c : Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 c p) |--
  weak_valid_pointer p.
Proof.
  simpl. eapply derives_trans; [apply data_at_valid_ptr; [apply top_share_nonidentity | simpl; lia] |].
  apply valid_pointer_weak.
Qed.

Lemma body_main : semax_body Vprog G f_main main_spec.
Proof.
  change (semax_body Vprog G f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_content_size.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * TT)%logic).
  { intros _. apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  (* pick(declared) *)
  assert_PROP (field_compatible tulong [] v_declared) as FCd by entailer!.
  sep_apply (ulong_bytes v_declared FCd).
  forward_call (v_declared, 8, Tsh).
  Intros db.
  match goal with H: Zlength db = 8, H': Forall _ db |- _ => sep_apply (pick_tulong Tsh db v_declared H H' FCd) end.
  Intros dv.
  forward_call 9223372036854775807.
  Intros after.
  forward_call tt.
  Intros u8.
  forward.
  repeat apply -> seq_assoc. apply semax_if_seq. forward_if.
  { (* a skippable frame *)
    forward_call (gv, Tsh, v_len).
    Intros q. forward.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    repeat apply -> seq_assoc. apply semax_if_seq.
    destruct (eq_dec q nullval) as [Hq|Hq].
    { subst q. forward_if; [| contradiction]. forward. forward.
      forward_if; [| contradiction]. forward.
      sep_apply (data_at_data_at_ Tsh tulong (Vlong dv) v_declared). cancel. }
    Intros k u.
    assert_PROP (isptr q) as Hq'.
    { unfold mbytes. rewrite if_false by exact Hq. entailer!. }
    forward_if; [unfold mbytes; rewrite if_false by exact Hq; entailer! | contradiction |].
    forward_call (gv, after).
    Intros vret. destruct vret as [p l]. cbn [fst snd] in *.
    subst after.
    forward.
    forward_call (gv, q, sk_bytes k u, p, l).
    { pose proof (Zlength_nonneg l). rewrite sk_bytes_length.
      split; [apply sk_bytes_ok; auto | rep_lia]. }
    Intros src.
    forward.
    forward.
    destruct (eq_dec src nullval) as [Hs|Hs].
    { subst src. forward_if; [| contradiction]. forward. entailer!. }
    assert_PROP (isptr src) as Hs'.
    { unfold mbytes. rewrite if_false by exact Hs. entailer!. }
    forward_if; [unfold mbytes; rewrite if_false by exact Hs; entailer! | contradiction |].
    forward.
    unfold mbytes. rewrite if_false by exact Hs. Intros.
    replace (Zlength (sk_bytes k u) + Zlength l) with (Zlength (sk_bytes k u ++ l))
      by (rewrite Zlength_app; reflexivity).
    sep_apply (to_Z Ews (Zlength (sk_bytes k u ++ l)) (zbytes (sk_bytes k u ++ l)) src).
    specialize (H8 Hs ltac:(unfold PTRDIFF_MAX; lia)).
    forward_call (gv, Ews, src, sk_bytes k u ++ l).
    { entailer!. rewrite Zlength_app. reflexivity. }
    { split; [auto | split; [rewrite Zlength_app, sk_bytes_length in *; unfold PTRDIFF_MAX in *; lia |]].
      apply ff_bytes_ok_app; [apply sk_bytes_ok |]; auto. }
    rewrite acs_skippable by auto.
    forward.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [| contradiction].
    forward_call Int.one.
    forward. entailer!. }
  (* a frame declaring the content size dv *)
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [vm_compute in H4; discriminate |].
  forward. forward.
  assert_PROP (isptr v_none) as Pn by entailer!.
  sep_apply (@data_at_tuchar_zero_array CompSpecs Tsh v_none Pn).
  rewrite <- (Int64.repr_unsigned dv).
  forward_call (gv, Tsh, v_none, @nil Z, Int64.unsigned dv, 2 ^ 31, 0, Tsh, v_len,
                Zstd.proof.zstd.Spec_xxh.pw_bytes Tsh 1 [Vundef] v_none).
  { simpl Zstd.proof.zstd.Spec_xxh.pw_pred. rewrite data_at__eq. change (default_val (tarray tuchar 1)) with [Vundef].
    sep_apply (to_Z Tsh 1 [Vundef] v_none). cancel. }
  { split; [apply Forall_nil | split; [rewrite Zlength_nil; rep_lia | intros _; apply none_valid]]. }
  Intros vret. destruct vret as [q d']. cbn [fst snd] in *.
  rewrite Zlength_nil in *. apply Zlength_nil_inv in H5. subst d'.
  sep_apply (none_back v_none).
  pose proof (Int64.unsigned_range dv) as Hdv.
  set (fcs := Int64.unsigned dv) in *.
  forward. forward.
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  repeat apply -> seq_assoc. apply semax_if_seq.
  destruct (eq_dec q nullval) as [Hq|Hq].
  { subst q. forward_if; [| contradiction]. forward. forward.
    forward_if; [| contradiction]. forward. entailer!. }
  Intros c.
  set (F := nf_bytes [] fcs 0 c) in *.
  assert (HF: 9 <= Zlength F <= 26) by (unfold F; pose proof (nf_bytes_length [] fcs (2 ^ 31) 0 c H5); rewrite Zlength_nil in *; lia).
  assert_PROP (isptr q) as Hq'.
  { unfold mbytes. rewrite if_false by exact Hq. entailer!. }
  forward_if; [unfold mbytes; rewrite if_false by exact Hq; entailer! | contradiction |].
  forward_call (gv, after).
  Intros vret. destruct vret as [p l]. cbn [fst snd] in *.
  subst after.
  forward.
  forward_call (gv, q, F, p, l).
  { apply (nf_bytes_ok [] fcs (2 ^ 31) 0 c); auto. }
  Intros src.
  forward.
  forward.
  destruct (eq_dec src nullval) as [Hs|Hs].
  { subst src. forward_if; [| contradiction]. forward. entailer!. }
  assert_PROP (isptr src) as Hs'.
  { unfold mbytes. rewrite if_false by exact Hs. entailer!. }
  forward_if; [unfold mbytes; rewrite if_false by exact Hs; entailer! | contradiction |].
  forward.
  unfold mbytes. rewrite if_false by exact Hs. Intros.
  replace (Zlength F + Zlength l) with (Zlength (F ++ l)) by (rewrite Zlength_app; reflexivity).
  sep_apply (to_Z Ews (Zlength (F ++ l)) (zbytes (F ++ l)) src).
  match goal with H8: src <> nullval -> _ |- _ => specialize (H8 Hs ltac:(unfold PTRDIFF_MAX; lia)) end.
  forward_call (gv, Ews, src, F ++ l).
  { entailer!. rewrite Zlength_app. reflexivity. }
  { split; [auto | split; [rewrite Zlength_app in *; unfold PTRDIFF_MAX in *; lia |]].
    apply ff_bytes_ok_app; [apply (nf_bytes_ok [] fcs (2 ^ 31) 0 c) |]; auto. }
  sep_apply (of_Z Ews (Zlength (F ++ l)) (zbytes (F ++ l)) src).
  destruct (acs_frame fcs c l H5 ltac:(rep_lia)) as (B4 & Bfhd & Bshr & Band & Bsize).
  fold F in B4, Bsize. rewrite Bsize.
  forward.
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if; [contradiction |].
  assert (Z4: Znth 4 (F ++ l) = nh_fhd (nc_hdr c)) by (rewrite <- B4; reflexivity).
  clearbody F.
  forward; try solve [entailer!; rewrite Zlength_app; lia | entailer!; rewrite Z4; rep_lia].
  rewrite Z4.
  assert (Hfl: 0 <= nh_fcs_flag (nc_hdr c) <= 3) by (destruct H5 as [(Hfl & _) _]; exact Hfl).
  unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
  repeat apply -> seq_assoc. apply semax_if_seq.
  forward_if.
  - (* no Frame_Content_Size_flag *)
    rewrite shr6, Bshr in H14 by exact Bfhd.
    apply repr_inj_unsigned in H14; [| rep_lia | rep_lia].
    forward; try solve [entailer!; rewrite Zlength_app; lia | entailer!; rewrite Z4; rep_lia].
    rewrite Z4.
    forward.
    rewrite and32 by exact Bfhd. rewrite Band.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    repeat apply -> seq_assoc. apply semax_if_seq.
    rewrite H14.
    destruct (nh_single (nc_hdr c)) eqn:Esg.
    + (* Single_Segment: a one-byte Frame_Content_Size field, the declared size *)
      change (32 * zb true) with 32. cbn [andb negb Z.eqb].
      forward_if; [discriminate |].
      forward.
      forward_call (Int.one);
        try solve [entailer!; first [rewrite Int64.eq_true; reflexivity | reflexivity | vm_compute; reflexivity]].
      forward. entailer!.
    + (* no Frame_Content_Size field: UNKNOWN *)
      change (32 * zb false) with 0. cbn [andb negb Z.eqb].
      forward_if; [| discriminate].
      forward_call (Int.one);
        try solve [entailer!; first [rewrite Int64.eq_true; reflexivity | reflexivity | vm_compute; reflexivity]].
      forward. entailer!.
  - (* a Frame_Content_Size_flag: the declared size *)
    rewrite shr6, Bshr in H14 by exact Bfhd.
    assert (Hne: nh_fcs_flag (nc_hdr c) <> 0) by (intro E; apply H14; rewrite E; reflexivity).
    rewrite (proj2 (Z.eqb_neq _ _) Hne). cbn [andb].
    forward.
    unfold abbreviate in MORE_COMMANDS; subst MORE_COMMANDS.
    repeat apply -> seq_assoc. apply semax_if_seq.
    forward_if; [contradiction |].
    forward.
    forward_call (Int.one);
      try solve [entailer!; first [rewrite Int64.eq_true; reflexivity | reflexivity | vm_compute; reflexivity]].
    forward. entailer!.
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

Theorem api_content_size_ok : HarnessOK API Hs.
Proof.
  split; [exact Hs_ids |].
  repeat apply Forall_cons; try apply Forall_nil.
  - kit_body FSpecs.f_copy_of (@G_copy_of CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_copy_of CompSpecs).
  - kit_body FSpecs.f_any_bytes (@G_any_bytes CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_any_bytes CompSpecs).
  - kit_body FSpecs.f_upto G_upto (@Zstd.proof.harness.frames.FBodiesSmall.body_upto CompSpecs).
  - kit_body FSpecs.f_put_le G_put_le
      (@Zstd.proof.harness.frames.FBodiesSmall.body_put_le CompSpecs).
  - kit_body FSpecs.f_join (@G_join CompSpecs) (@Zstd.proof.harness.frames.FBodiesSmall.body_join CompSpecs).
  - kit_body FSpecs.f_new_skippable (@G_new_skippable CompSpecs)
      (@Zstd.proof.harness.frames.FBodiesSmall.body_new_skippable CompSpecs).
  - kit_body FSpecs.f_new_frame (@G_new_frame CompSpecs)
      (@Zstd.proof.harness.frames.FBodyNewFrame.body_new_frame CompSpecs).
  - exists f_main. split; [reflexivity |]. split; [reflexivity |]. exact body_main.
Qed.
