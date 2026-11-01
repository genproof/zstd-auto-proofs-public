(* The harness obligation of api_frame_size (harness/api_frame_size.c): for ANY predicates DC, DD of the decoder's
   API (Spec_api6, with ZSTD_XXH64's specification that new_frame calls), the helpers of laws_common.h and
   frames.h (proved once in the frames kit) and main satisfy their specifications.

   main builds a frame F (new_frame: a Zstandard frame of any data; new_skippable: a skippable frame of up to
   2^32 - 1 bytes of user data), appends any bytes r (join) and checks that ZSTD_findFrameCompressedSize of F ++ r
   is |F|.  The specification of ZSTD_findFrameCompressedSize returns frame_compressed_size of its input; the
   kit's facts give frame_compressed_size (F ++ r) = Some |F| (FFacts.nf_frame_compressed_size,
   FSeries.sk_frame_compressed_size with sk_frame_size_any below).  The input has up to PTRDIFF_MAX bytes and
   the skippable frame up to 2^32 - 1 bytes of user data: this needs the source size bound 2 ^ 63 - 1 of
   src_spec_pre and the model's skippable_frame_size without the 32-bit test (the size bounds of the
   API specifications and fix F5 of patch/GENPROOF-PATCH.md). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.api_frame_size.HOK_api_frame_size.
Require Zstd.proof.top.MainPre6.
Require Zstd.proof.harness.HCsConv.
Require Zstd.proof.harness.frames.FSpecs Zstd.proof.harness.frames.FBodiesSmall Zstd.proof.harness.frames.FTransfer.
Require Zstd.proof.harness.frames.FBodyNewFrame.
Require Zstd.proof.harness.frames.FFacts Zstd.proof.harness.frames.FSeries.

Local Ltac expand_main_pre ::= idtac.

(* ---------- the model: findFrameCompressedSize of the harness's frames ---------- *)

(* a skippable frame of up to 2^32 - 1 bytes of user data: its size is read from its header (F5: no 32-bit test
   on header + user data) *)
Lemma sk_frame_size_any : forall k u rest, Zlength u <= 4294967295 ->
  skippable_frame_size (FModel.sk_bytes k u ++ rest) = Some (8 + Zlength u).
Proof.
  intros k u rest Hu. pose proof (FSeries.sk_bytes_app_length k u rest) as L.
  assert (0 <= Zlength rest /\ 0 <= Zlength u) by (rewrite !Zlength_correct; lia).
  unfold skippable_frame_size. rewrite FSeries.sk_size_field by lia. unfold ZSTD_SKIPPABLEHEADERSIZE.
  replace (Zlength (FModel.sk_bytes k u ++ rest) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Zlength u + 8 >? Zlength (FModel.sk_bytes k u ++ rest)) with false
    by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
  f_equal. lia.
Qed.

(* what main needs of the frame it built: defined bytes, at most PTRDIFF_MAX of them, and
   findFrameCompressedSize finds exactly them in front of any bytes *)
Definition frame_good (F: list Z) : Prop :=
  bytes_ok F /\ Zlength F <= FSpecs.PTRDIFF_MAX /\
  forall rest, frame_compressed_size (F ++ rest) = Some (Zlength F).

Lemma sk_good k u : 0 <= k < 16 -> Zlength u <= 4294967295 -> bytes_ok u -> frame_good (FModel.sk_bytes k u).
Proof.
  intros Hk Hu Hok. pose proof (FSeries.sk_bytes_length k u) as L.
  unfold frame_good. split; [apply FSeries.sk_bytes_ok; auto | split; [unfold FSpecs.PTRDIFF_MAX; lia |]].
  intros rest. rewrite L. apply FSeries.sk_frame_compressed_size; [exact Hk |].
  apply sk_frame_size_any. exact Hu.
Qed.

Lemma nf_good d c : bytes_ok d -> Zlength d <= (FSpecs.PTRDIFF_MAX - 26) / 4 ->
  FModel.nf_ok (Zlength d) (Zlength d) (2 ^ 31) 0 c -> frame_good (FModel.nf_bytes d (Zlength d) 0 c).
Proof.
  intros Hd Hn Hok. pose proof (FFacts.nf_bytes_length _ _ _ _ _ Hok) as L.
  pose proof (Zlength_nonneg d). unfold FSpecs.PTRDIFF_MAX in *. simpl in Hn.
  unfold frame_good. split; [eapply FFacts.nf_bytes_ok; eauto | split; [unfold FSpecs.PTRDIFF_MAX; lia |]].
  intros rest.
  eapply FFacts.nf_frame_compressed_size; [exact Hok | lia | lia |].
  eapply FFacts.nf_wlog_ok; [exact (proj1 Hok) | lia].
Qed.

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
    (QPprog_vars Zstd.contracts.api_frame_size.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. apply make_tycontext_g_isSome.
  unfold Vprog, QPvarspecs. rewrite map_map.
  apply in_map_iff. exists (i, v). split; [reflexivity | exact Hin].
Qed.

(* main's precondition: the decoder's globals, split off as in MainPre6.main_pre_fact6 (whose list of
   programs has the x_ laws only) *)
Lemma pre_globals gv :
  InitGPred (Vardefs Zstd.contracts.api_frame_size.whole_prog) gv |-- zstd_globals gv * TT.
Proof.
  assert (Hincl: incl Zstd.proof.top.MainPre6.zstd_vardefs (Vardefs Zstd.contracts.api_frame_size.whole_prog)).
  { apply Zstd.proof.top.MainPre6.MP_incl_Vardefs; vm_compute; reflexivity. }
  rewrite (Zstd.proof.top.MainPre6.MP_split_zstd _ gv Hincl).
  apply sepcon_derives; [apply Zstd.proof.top.MainPre6.zstd_vardefs_globals | apply TT_right].
Qed.

(* ---------- byte arrays between the harness's compspecs and the decoder's ---------- *)

Lemma to_Z sh n v p :
  @data_at CompSpecs sh (tarray tuchar n) v p |-- @data_at Zstd.units.Zstd.CS sh (tarray tuchar n) v p.
Proof. rewrite (Zstd.proof.harness.HCsConv.data_at_bytes_cs CompSpecs Zstd.units.Zstd.CS). apply derives_refl. Qed.

Lemma tok_to_Z sh n p :
  @malloc_token CompSpecs sh (tarray tuchar n) p |-- @malloc_token Zstd.units.Zstd.CS sh (tarray tuchar n) p.
Proof.
  rewrite (@malloc_token_change_composite _ _ (Zstd.proof.harness.HCsConv.cce_any CompSpecs Zstd.units.Zstd.CS)
    sh (tarray tuchar n)) by reflexivity.
  apply derives_refl.
Qed.

(* new_frame's data lends its malloc_token as ZSTD_XXH64's witness (needed when it has 0 bytes) *)
Lemma tok_pw n p :
  @malloc_token CompSpecs Ews (tarray tuchar n) p |--
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar n) p).
Proof. simpl. apply tok_to_Z. Qed.

Lemma pw_tok_valid p :
  Zstd.proof.zstd.Spec_xxh.pw_pred (Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar 0) p) |--
  weak_valid_pointer p.
Proof.
  simpl. eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak].
Qed.

Lemma mbytes_fold n l p : p <> nullval ->
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (zbytes l) p |-- FSpecs.mbytes n l p.
Proof. intros H. unfold FSpecs.mbytes. rewrite if_false by exact H. apply derives_refl. Qed.

(* the functions main calls *)
Definition G0 : funspecs :=
  [ZSTD_findFrameCompressedSize_spec;
   nondet_u8_spec; gp_assert_spec;
   Zstd.proof.harness.frames.FSpecs.upto_spec; @Zstd.proof.harness.frames.FSpecs.any_bytes_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.new_frame_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.new_skippable_spec CompSpecs;
   @Zstd.proof.harness.frames.FSpecs.join_spec CompSpecs].

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.api_frame_size.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
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
  forward_call 9223372036854775807.
  Intros after.
  forward_call (gv, n).
  Intros vret. destruct vret as [pd d]. cbn [fst snd] in *.
  unfold FSpecs.mbytes.
  destruct (eq_dec pd nullval) as [Hpd|Hpd].
  { subst pd. forward_if; [forward; cancel | congruence]. }
  Intros.
  forward_if; [contradiction |].
  forward_call tt.
  Intros b.
  (* the frame: skippable or not *)
  forward_if (EX fr: val, EX F: list Z,
    PROP (fr <> nullval -> frame_good F)
    LOCAL (temp _frame fr; temp _after (Vlong (Int64.repr after)); lvar _len tulong v_len; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; TT;
         if eq_dec fr nullval then data_at_ Tsh tulong v_len
         else (data_at Tsh tulong (Vlong (Int64.repr (Zlength F))) v_len * FSpecs.mbytes (Zlength F) F fr))).
  - forward_call (gv, Tsh, v_len).
    Intros fr.
    forward.
    destruct (eq_dec fr nullval) as [Hfr|Hfr].
    + Exists fr (@nil Z). rewrite if_true by exact Hfr. entailer!.
    + Intros k u. Exists fr (FModel.sk_bytes k u). rewrite if_false by exact Hfr. entailer!.
      apply sk_good; tauto.
  - forward_if (PROP () LOCAL (temp _t'5 (Vint (Int.repr 31)); temp _data pd; temp _n (Vlong (Int64.repr n));
                              temp _after (Vlong (Int64.repr after)); lvar _len tulong v_len; gvars gv)
      SEP (mem_mgr gv; malloc_token Ews (tarray tuchar n) pd * data_at Ews (tarray tuchar n) (zbytes d) pd;
           data_at_ Tsh tulong v_len; zstd_globals gv; TT)).
    { vm_compute in H6. discriminate H6. }
    { forward. entailer!. }
    subst n.
    sep_apply (tok_pw (Zlength d) pd).
    forward_call (gv, Ews, pd, d, Zlength d, 2 ^ 31, 0, Tsh, v_len,
                  Zstd.proof.zstd.Spec_xxh.pw_token Ews (tarray tuchar (Zlength d)) pd).
    { match goal with Hz: Zlength d = 0 |- _ => rewrite Hz end. apply pw_tok_valid. }
    Intros vret. destruct vret as [fr d']. cbn [fst snd] in *.
    forward.
    destruct (eq_dec fr nullval) as [Hfr|Hfr].
    + Exists fr (@nil Z). rewrite if_true by exact Hfr. entailer!.
    + Intros c. Exists fr (FModel.nf_bytes d (Zlength d) 0 c). rewrite if_false by exact Hfr. entailer!.
      apply nf_good; tauto.
  - Intros fr F.
    repeat apply -> seq_assoc.
    destruct (eq_dec fr nullval) as [Hfr|Hfr].
    { (* no frame: the run ends *)
      subst fr. apply semax_if_seq. forward_if; [| congruence]. forward. forward.
      forward_if; [forward; cancel | congruence]. }
    match goal with Hg: fr <> nullval -> frame_good F |- _ => destruct (Hg Hfr) as (HFok & HFlen & HFcs) end.
    unfold FSpecs.mbytes at 1. rewrite if_false by exact Hfr. Intros.
    apply semax_if_seq. forward_if; [contradiction |].
    (* any bytes r after the frame *)
    forward_call (gv, after).
    Intros vret. destruct vret as [pr r]. cbn [fst snd] in *. subst after.
    forward.
    sep_apply (mbytes_fold (Zlength F) F fr Hfr).
    forward_call (gv, fr, F, pr, r).
    { unfold FSpecs.PTRDIFF_MAX in *. rep_lia. }
    Intros src.
    forward. forward.
    destruct (eq_dec src nullval) as [Hs|Hs].
    { subst src. forward_if; [forward; cancel | congruence]. }
    unfold FSpecs.mbytes at 1. rewrite if_false by exact Hs. Intros.
    forward_if; [contradiction |].
    forward.
    match goal with Hj: src <> nullval -> _ -> _ |- _ =>
      specialize (Hj Hs ltac:(unfold FSpecs.PTRDIFF_MAX in *; lia)) end.
    (* ZSTD_findFrameCompressedSize(F ++ r): frame_compressed_size (F ++ r) = Some |F| *)
    rewrite <- Zlength_app.
    sep_apply (to_Z Ews (Zlength (F ++ r)) (zbytes (F ++ r)) src).
    forward_call (gv, Ews, src, F ++ r).
    { entailer!. rewrite Zlength_app. reflexivity. }
    { split; [auto | split; [rewrite Zlength_app; unfold FSpecs.PTRDIFF_MAX in *; lia |
                             apply FFacts.ff_bytes_ok_app; auto]]. }
    Intros sz.
    forward.
    forward.
    match goal with Hk: match frame_compressed_size (F ++ r) with Some _ => _ | None => _ end |- _ =>
      rewrite HFcs in Hk; subst sz end.
    (* the check *)
    forward_call Int.one.
    { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
    forward.
    cancel.
Qed.


(* ---------- from G0 to Gprog API Hs ---------- *)

(* the decoder's functions the harness reaches: Spec_api6's API and ZSTD_XXH64 (new_frame's checksum; the
   decoder's obligation Zstd6L0.zstd_ok_L0 has it) *)
Definition API (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) : funspecs :=
  Specs_api DC DD ++ [Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec].

(* the harness's own functions besides main (in the order of helper_ids): the frames kit's helpers of
   laws_common.h and frames.h *)
Definition Hs : funspecs :=
  [FSpecs.copy_of_spec; FSpecs.any_bytes_spec; FSpecs.upto_spec; FSpecs.put_le_spec; FSpecs.join_spec;
   FSpecs.new_skippable_spec; FSpecs.new_frame_spec].

Lemma Externals_eq : Externals = [nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
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
  (Specs_api DC DD ++ [Zstd.proof.zstd.Spec_xxh.ZSTD_XXH64_spec;
                       nondet_u8_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec;
                       FSpecs.copy_of_spec; FSpecs.any_bytes_spec; FSpecs.upto_spec; FSpecs.put_le_spec;
                       FSpecs.join_spec; FSpecs.new_skippable_spec; FSpecs.new_frame_spec; main_spec]).
Proof. unfold Gprog, Imports, API. rewrite Externals_eq. cbn [app]. rewrite <- app_assoc. reflexivity. Qed.

(* an entry (i, fs) of a list found in Gprog *)
Ltac in_gprog :=
  match goal with |- initial_world.find_id ?i _ = Some ?fs =>
    rewrite Gprog_cons; unfold Specs_api; cbn [app]; find_steps; reflexivity end.

Lemma G0_in_Gprog DC DD i fs : initial_world.find_id i G0 = Some fs ->
  initial_world.find_id i (Gprog (API DC DD) Hs) = Some fs.
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
Lemma Gprog_not_var DC DD i : In i (map fst (Gprog (API DC DD) Hs)) -> ~ In i (map fst Vprog).
Proof.
  intros Hin Hv.
  assert (Hb: forallb (fun j => negb (id_in_list j (map fst Vprog))) (map fst (Gprog (API DC DD) Hs)) = true).
  { match goal with |- forallb ?f ?l = true => let L := eval lazy in l in change l with L end.
    vm_compute. reflexivity. }
  rewrite forallb_forall in Hb. specialize (Hb i Hin).
  rewrite (Zstd.proof.top.MainPre6.MP_id_in_list_true_i i _ Hv) in Hb. discriminate.
Qed.

Theorem api_frame_size_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    HarnessOK (API DC DD) Hs.
Proof.
  intros DC DD. split.
  - vm_compute. reflexivity.
  - repeat constructor.
    + (* copy_of *)
      exists f_copy_of. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_copy_of = FSpecs.f_copy_of) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ (@FSpecs.G_copy_of CompSpecs)).
      * exact (@FBodiesSmall.body_copy_of CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* any_bytes *)
      exists f_any_bytes. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_any_bytes = FSpecs.f_any_bytes) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ (@FSpecs.G_any_bytes CompSpecs)).
      * exact (@FBodiesSmall.body_any_bytes CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* upto *)
      exists f_upto. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_upto = FSpecs.f_upto) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ FSpecs.G_upto).
      * exact (@FBodiesSmall.body_upto CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* put_le *)
      exists f_put_le. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_put_le = FSpecs.f_put_le) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ FSpecs.G_put_le).
      * exact (@FBodiesSmall.body_put_le CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor.
    + (* join *)
      exists f_join. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_join = FSpecs.f_join) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ (@FSpecs.G_join CompSpecs)).
      * exact (@FBodiesSmall.body_join CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* new_skippable *)
      exists f_new_skippable. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_new_skippable = FSpecs.f_new_skippable) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ (@FSpecs.G_new_skippable CompSpecs)).
      * exact (@FBodiesSmall.body_new_skippable CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* new_frame *)
      exists f_new_frame. split; [vm_compute; reflexivity|]. split; [reflexivity|].
      assert (E: f_new_frame = FSpecs.f_new_frame) by (vm_compute; reflexivity).
      rewrite E. apply (FTransfer.fk_transfer Vprog _ (@FSpecs.G_new_frame CompSpecs)).
      * exact (@FBodyNewFrame.body_new_frame CompSpecs).
      * apply FTransfer.fk_find_all. repeat constructor; in_gprog.
    + (* main *)
      exists f_main. split; [reflexivity|]. split; [reflexivity|].
      eapply semax_body_subsumption; [apply body_main_G0 |].
      apply tycontext_sub_i99. split; intro i.
      * rewrite (make_tycontext_g_find Vprog G0 i).
        rewrite (make_tycontext_g_find Vprog (Gprog (API DC DD) Hs) i).
        destruct (initial_world.find_id i G0) as [fs|] eqn:E.
        -- rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
        -- destruct (initial_world.find_id i (Gprog (API DC DD) Hs)) as [fs'|] eqn:E'.
           ++ rewrite mtg_none; [exact Logic.I |].
              apply (Gprog_not_var DC DD i).
              apply initial_world.find_id_e in E'. apply (in_map fst) in E'. exact E'.
           ++ apply sub_option_refl.
      * rewrite !semax_prog.find_id_maketycontext_s.
        destruct (initial_world.find_id i G0) as [fs|] eqn:E; [|exact Logic.I].
        rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
