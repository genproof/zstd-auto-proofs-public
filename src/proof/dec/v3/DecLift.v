(* API v3: reusing v2 body proofs.  A body proved against a context G stays
   proved against any context G' that gives each function of G a specification at least as strong
   (funspec_sub): VST's tycontext_sub compares glob_specs up to funspec_sub (veric/expr.v subsumespec).
   The v3 exports of H and B are such strengthenings of their v2 versions. *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Export Zstd.proof.dec.v3.H.HAlloc3Sub.

(* G' refines G: every function of G has, in G', a specification that implies its specification in G *)
Definition refines (G' G: funspecs) : Prop :=
  forall i phi, initial_world.find_id i G = Some phi ->
    exists phi', initial_world.find_id i G' = Some phi' /\ funspec_sub phi' phi.

Lemma make_tycontext_g_find_id_lift (V: varspecs) (G: funspecs) (i: ident) :
  Maps.PTree.get i (make_tycontext_g V G) =
  match initial_world.find_id i G with
  | Some phi => Some (type_of_funspec phi)
  | None => initial_world.find_id i V
  end.
Proof.
  induction G as [|[j phi] G IH]; simpl.
  - apply semax_prog.make_tycontext_g_nilG_find_id.
  - rewrite Maps.PTree.gsspec. destruct (Coqlib.peq i j) as [E|E]; subst.
    + destruct (Memory.EqDec_ident j j); [reflexivity | congruence].
    + destruct (Memory.EqDec_ident i j); [congruence | exact IH].
Qed.

Lemma find_id_in_fst_lift {A} (i: ident) (l: list (ident * A)) (x: A) :
  initial_world.find_id i l = Some x -> In i (map fst l).
Proof.
  induction l as [|[j y] l IH]; simpl; [discriminate |].
  destruct (Memory.EqDec_ident i j); [left; congruence | intros H; right; exact (IH H)].
Qed.

Lemma find_id_none_lift {A} (i: ident) (l: list (ident * A)) :
  ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j y] l IH]; simpl; [reflexivity |].
  destruct (Memory.EqDec_ident i j); [intros H; exfalso; apply H; left; congruence |].
  intros H; apply IH; tauto.
Qed.

Lemma NoDup_app_disj_lift {A} (l1 l2: list A) (x: A) :
  NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; simpl; [tauto |].
  intros Hn Hin. inversion Hn as [|y' l' Hy Hl]; subst. destruct Hin as [<-|Hin].
  - intros Hx. apply Hy. apply in_or_app; right; exact Hx.
  - exact (IH Hl Hin).
Qed.

Lemma refines_tycontext_sub (f: function) (G G': funspecs) :
  refines G' G -> NoDup (map fst Vprog ++ map fst G') ->
  tycontext_sub (func_tycontext f Vprog G nil) (func_tycontext f Vprog G' nil).
Proof.
  intros Hr Hnd.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  split; [intro id; destruct (Maps.PTree.get _ _); auto |].
  split; [auto |]. split; [auto |].
  split; [| split; [| intro id; first [exact I | apply Annotation_sub_refl]]].
  - intro id. hnf. rewrite !make_tycontext_g_find_id_lift.
    destruct (initial_world.find_id id G) as [phi|] eqn:E.
    + destruct (Hr id phi E) as [phi' [E' Hs]]. rewrite E'.
      f_equal. apply type_of_funspec_sub; exact Hs.
    + destruct (initial_world.find_id id Vprog) as [t|] eqn:EV; [| exact I].
      assert (N: initial_world.find_id id G' = None).
      { apply find_id_none_lift.
        exact (NoDup_app_disj_lift _ _ _ Hnd (find_id_in_fst_lift _ _ _ EV)). }
      rewrite N. reflexivity.
  - intro id. rewrite !initial_world.make_tycontext_s_find_id.
    destruct (initial_world.find_id id G) as [phi|] eqn:E; [| exact I].
    destruct (Hr id phi E) as [phi' [E' Hs]]. exists phi'. split; [exact E' |].
    apply funspec_sub_sub_si; exact Hs.
Qed.

Lemma body_ok_sub (G G': funspecs) (ix: ident * funspec) :
  body_ok G ix -> refines G' G ->
  NoDup (map fst Vprog ++ map fst G) -> NoDup (map fst Vprog ++ map fst G') ->
  body_ok G' ix.
Proof.
  intros [f [Hf [Hcc Hb]]] Hr _ Hnd'. exists f; split; [exact Hf | split; [exact Hcc |]].
  eapply semax_body_subsumption; [exact Hb |].
  apply refines_tycontext_sub; assumption.
Qed.

Lemma refines_refl (G: funspecs) : refines G G.
Proof. intros i phi H. exists phi. split; [exact H | apply funspec_sub_refl]. Qed.

Lemma find_id_app_split {A} (i: ident) (G1 G2: list (ident * A)) :
  initial_world.find_id i (G1 ++ G2) =
  match initial_world.find_id i G1 with Some x => Some x | None => initial_world.find_id i G2 end.
Proof.
  induction G1 as [|[j x] G1 IH]; simpl; [reflexivity |].
  destruct (Memory.EqDec_ident i j); [reflexivity | exact IH].
Qed.

Lemma find_id_none_iff {A} (i: ident) (G: list (ident * A)) :
  initial_world.find_id i G = None <-> ~ In i (map fst G).
Proof.
  induction G as [|[j x] G IH]; simpl; [tauto |].
  destruct (Memory.EqDec_ident i j) as [E|E]; [subst; split; [discriminate | tauto] |].
  rewrite IH. split; [intros H [H'|H']; [congruence | tauto] | tauto].
Qed.

Lemma refines_app (G1 G2 G1' G2': funspecs) :
  refines G1' G1 -> refines G2' G2 ->
  NoDup (map fst G1 ++ map fst G2) -> NoDup (map fst G1' ++ map fst G2') ->
  (forall i, In i (map fst G1) <-> In i (map fst G1')) ->
  refines (G1' ++ G2') (G1 ++ G2).
Proof.
  intros H1 H2 _ _ Hi i phi H. rewrite find_id_app_split in H |- *.
  destruct (initial_world.find_id i G1) as [x|] eqn:E1.
  - inversion H; subst. destruct (H1 i phi E1) as [phi' [E' Hs]]. rewrite E'. eauto.
  - assert (E1': initial_world.find_id i G1' = None).
    { apply find_id_none_iff. rewrite <- Hi. apply find_id_none_iff. exact E1. }
    rewrite E1'. apply H2. exact H.
Qed.

(* pointwise refinement of two lists with the same names in the same order *)
Lemma refines_pointwise (G' G: funspecs) :
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd a) (snd b)) G' G -> refines G' G.
Proof.
  induction 1 as [|[i' phi'] [j phi] G' G [Ei Hs] _ IH]; intros i psi H; simpl in *; [discriminate|].
  subst i'. destruct (Memory.EqDec_ident i j).
  - inversion H; subst. exists phi'. split; [reflexivity | exact Hs].
  - exact (IH i psi H).
Qed.

Lemma startingInputLength_sub3 :
  funspec_sub (snd ZSTD_startingInputLength_spec3) (snd ZSTD_startingInputLength_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros u [g args]. simpl.
  Exists 0 (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto].
  unfold PROPx; simpl. rewrite !prop_true_andp by auto. auto.
Qed.

Lemma frameHeaderSize_internal_sub3 :
  funspec_sub (snd ZSTD_frameHeaderSize_internal_spec3) (snd ZSTD_frameHeaderSize_internal_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[gv sh] base] N] c] off] s] [g args]. simpl.
  Exists (gv, sh, base, N, c, off, s, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2].
  - unfold PROPx; simpl. apply andp_derives; [apply prop_derives; tauto | auto].
  - Intros r. Exists r. unfold PROPx; simpl. apply andp_derives; [apply prop_derives | auto].
    rewrite ?frame_header_size_zstd1, ?frame_compressed_size_zstd1. tauto.
Qed.

Lemma getFrameHeader_advanced_sub3 :
  funspec_sub (snd ZSTD_getFrameHeader_advanced_spec3) (snd ZSTD_getFrameHeader_advanced_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[[gv shz] zfh] v0] sh] base] N] c] off] s] [g args]. simpl.
  Exists (gv, shz, zfh, v0, sh, base, N, c, off, s, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2].
  - unfold PROPx; simpl. apply andp_derives; [apply prop_derives; tauto | auto].
  - Intros r v. Exists r v. unfold PROPx; simpl. apply andp_derives; [apply prop_derives | auto].
    unfold fh_post_adv, fh_post_m, fh_post. simpl. tauto.
Qed.

Lemma findFrameCompressedSize_advanced_sub3 :
  funspec_sub (snd ZSTD_findFrameCompressedSize_advanced_spec3) (snd ZSTD_findFrameCompressedSize_advanced_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[gv sh] base] N] c] off] s] [g args]. simpl.
  Exists (gv, sh, base, N, c, off, s, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2].
  - unfold PROPx; simpl. apply andp_derives; [apply prop_derives; tauto | auto].
  - Intros r. Exists r. unfold PROPx; simpl. apply andp_derives; [apply prop_derives | auto].
    rewrite ?frame_header_size_zstd1, ?frame_compressed_size_zstd1. tauto.
Qed.

(* for any allocator class: the allocation helpers' specifications imply the default-allocator ones *)
Lemma H_exports3_refines {CMI: cmem_preds} : refines (H_exports3 (CMI:=CMI)) H_exports.
Proof.
  apply refines_pointwise. unfold H_exports3, H_exports.
  repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]).
  - apply startingInputLength_sub3.
  - apply frameHeaderSize_internal_sub3.
  - apply getFrameHeader_advanced_sub3.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
  - apply findFrameCompressedSize_advanced_sub3.
  - apply customMallocP_cm_sub_dflt.
  - apply customCallocP_cm_sub_dflt.
  - apply customFreeP_cm_sub_dflt.
  - apply customMem_copy_cm_sub_dflt.
Qed.

(* H's exports for any class imply those at cmem_none (whose own-allocator cases are vacuous) *)
Lemma H_exports3_refines_none {CMI: cmem_preds} :
  refines (H_exports3 (CMI:=CMI)) (H_exports3 (CMI:=cmem_none)).
Proof.
  apply refines_pointwise. unfold H_exports3.
  repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]);
    try apply funspec_sub_refl.
  - apply customMallocP_cm_sub_none.
  - apply customCallocP_cm_sub_none.
  - apply customFreeP_cm_sub_none.
Qed.

Lemma B_usingDict_sub (DENT: dent_pred) (TABS: tabs_pred) :
  funspec_sub (snd (ZSTD_decompressBegin_usingDict_spec3 TABS)) (snd (ZSTD_decompressBegin_usingDict_spec TABS)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[gv p] fs] W] shk] dk] b] lxb] [g args]. simpl.
  Exists (gv, p, fs, W, shk, dk, b, 0, lxb) (@emp mpred _ _).
  rewrite emp_sepcon. simpl.
  rewrite !fs_begin3_zstd1, cfg_b_split. apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize. rewrite !sepcon_assoc.
    rewrite prop_true_andp by (repeat split; auto; lia). apply derives_refl.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl.
    Intros r ores. Exists r ores. rewrite !sepcon_assoc. apply andp_right; [apply prop_right; tauto |].
    apply andp_derives; [apply derives_refl |].
    repeat (apply sepcon_derives; [apply derives_refl |]). apply sepcon_derives; [| apply derives_refl].
    destruct (usingdict_model dk b ores); [apply derives_refl |].
    apply andp_derives; [apply derives_refl |]. apply exp_derives; intros fs'.
    first [ apply andp_derives; [apply prop_derives; tauto | apply derives_refl]
          | apply sepcon_derives; [apply andp_derives; [apply prop_derives; tauto | apply derives_refl] | apply derives_refl] ].
Qed.

(* a DDict's memory at any class: for the default allocator the same as at cmem_none; for an own allocator its
   tokens are FF at cmem_none (v2's specifications are at cmem_none) *)
Lemma ddict_mem_none_class {CMI: cmem_preds} (x: ddx) (buf: val) :
  dx_mem x = None -> @ddict_mem CMI x buf = @ddict_mem cmem_none x buf.
Proof. intros E. unfold ddict_mem. rewrite E. reflexivity. Qed.

Lemma ddict_mem_some_none (x: ddx) (buf: val) (m: cmem) :
  dx_mem x = Some m -> @ddict_mem cmem_none x buf |-- FF.
Proof. intros E. unfold ddict_mem. rewrite E. simpl. rewrite FF_sepcon. apply derives_refl. Qed.

Lemma B_usingDDict_sub {CMI: cmem_preds} (DENT: dent_pred) (TABS: tabs_pred) :
  funspec_sub (snd (ZSTD_decompressBegin_usingDDict_spec3 (CMI:=CMI) DENT TABS))
              (snd (ZSTD_decompressBegin_usingDDict_spec DENT TABS)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[gv p] fs] W] ox] buf] lxb] [g args]. simpl.
  assert (Hm: match ox with Some x => dx_mem x = None | None => True end \/
              exists x m, ox = Some x /\ dx_mem x = Some m).
  { destruct ox as [x|]; [destruct (dx_mem x) as [m|] eqn:E; [right; eauto | left; reflexivity] | left; exact I]. }
  destruct Hm as [Hm | (x & m & -> & Hm)].
  2: { (* an own allocator's DDict: v2's precondition (at cmem_none) is FF *)
    apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
    sep_apply (ddict_mem_some_none x buf m Hm). rewrite FF_sepcon. apply FF_left. }
  Exists (gv, p, fs, W, ox, buf, 0, lxb) (@emp mpred _ _).
  rewrite emp_sepcon. simpl.
  rewrite !fs_begin3_zstd1, cfg_b_split.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; repeat split; auto; lia |].
    unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
    destruct ox as [x|]; [rewrite (@ddict_mem_none_class CMI x buf Hm) |]; cancel.
  - apply prop_right; intros rho'. rewrite emp_sepcon. unfold PROPx, LOCALx, SEPx; simpl. normalize.
    match goal with Hc: match ox with Some _ => ?c = _ \/ _ | None => _ end |- _ => Exists c end.
    unfold local, lift1; simpl. normalize.
    destruct ox as [y|]; [rewrite (@ddict_mem_none_class CMI y buf Hm) |];
      (apply andp_right; [apply prop_right; split; auto |]); cancel.
Qed.

Lemma B_block_sub (DENT: dent_pred) (TABS: tabs_pred) :
  funspec_sub (snd (ZSTD_decompressBlock_internal_spec3 DENT TABS))
              (snd (ZSTD_decompressBlock_internal_spec DENT TABS)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[[[gv p] fs] ox] ts] bsm] streaming] W] o] i] h] [g args]. simpl.
  Exists (gv, p, fs, ox, ts, bsm, streaming, W, o, i, h) (cfg_fmt p 0).
  simpl.
  rewrite cfg_b_split. apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right; [apply prop_right; tauto |]. unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize. cancel.
  - apply prop_right; intros rho'. unfold PROPx, LOCALx, SEPx; simpl. normalize.
    Exists x x0 x1 x2. normalize. unfold local, lift1; simpl. normalize. cancel.
Qed.

Lemma B_initDDict_sub {CMI: cmem_preds} (DENT: dent_pred) :
  funspec_sub (snd (ZSTD_initDDict_internal_spec3 (CMI:=CMI) DENT)) (snd (ZSTD_initDDict_internal_spec DENT)).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[gv q] W] sh] pk] b] method] ctype] [g args]. simpl.
  (* the default allocator, which has given out nothing *)
  Exists (gv, q, W, sh, pk, b, method, ctype, @None cmem, 0) (@emp mpred _ _).
  rewrite emp_sepcon. simpl.
  match goal with |- ?L |-- _ => assert (Hct: L |-- !! (ctype = 0 \/ ctype = 1)) end.
  { apply andp_left2. unfold PROPx; simpl. normalize. }
  rewrite (add_andp _ _ Hct). clear Hct. rewrite andp_comm. apply derives_extract_prop; intros Hct.
  (* v2's bytes are at a pointer (data_at) *)
  match goal with |- ?L |-- _ => assert (Hpk: L |-- !! isptr pk) end.
  { apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. entailer!. }
  rewrite (add_andp _ _ Hpk). clear Hpk. rewrite andp_comm. apply derives_extract_prop; intros Hpk.
  apply andp_right.
  - apply andp_left2. unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    apply andp_right.
    { apply prop_right; cbn [cm_room cmem_ok]. destruct pk; try contradiction.
      split; [| reflexivity]. split; [auto |]. split; [auto |]. split; [simpl; auto |].
      split; [intros; discriminate |]. split; [intros; auto |]. split; [auto |]. split; [tauto |].
      split; [auto |]. auto. }
    unfold LOCALx, argsassert2assert; simpl. unfold local, lift1; simpl. normalize.
    rewrite (bytes_at_ptr sh b pk Hpk).
    unfold ddict_fresh3, ddict_fresh. cbn [cm_have]. cancel.
  - apply prop_right; intros rho'. rewrite emp_sepcon. apply andp_left2. unfold PROPx, LOCALx, SEPx; simpl.
    Intros r ores. Exists r ores.
    apply andp_right; [apply prop_right |].
    { split; [auto | split; [auto | split; [|auto]]].
      match goal with H1: (r = 0 /\ _) \/ _ |- _ =>
        destruct H1 as [[Hr _]|[He [[Hc Hd]|[[Hc _]|Hm]]]] end.
      + left; auto.
      + right; split; auto. left; split; auto; lia.
      + lia.
      + right; split; auto. }
    rewrite (bytes_at_ptr sh b pk Hpk).
    apply andp_derives; [apply derives_refl |].
    repeat (apply sepcon_derives; [apply derives_refl |]). apply sepcon_derives; [| apply derives_refl].
    rewrite ddx_of3_none. cbn [cm_have blk_tok]. destruct (Z.eq_dec r 0).
    + Intros buf. Exists buf. rewrite sepcon_emp. apply derives_refl.
    + Intros nb. unfold ddict_failed3, ddict_failed. Intros db. Exists db. rewrite sepcon_emp.
      cbn [blk_tok]. apply derives_refl.
Qed.

Lemma B_exports3_refines {CMI: cmem_preds} (DENT: dent_pred) (TABS: tabs_pred) :
  refines (B_exports3 (CMI:=CMI) DENT TABS) (B_exports DENT TABS).
Proof.
  intros i phi H.
  assert (Hin: In (i, phi) (B_exports DENT TABS)).
  { revert H. generalize (B_exports DENT TABS) as l. induction l as [|[j x] l IH]; simpl; [discriminate|].
    destruct (Memory.EqDec_ident i j) as [E|E]; [intros H; inversion H; subst; auto | intros H; auto]. }
  clear H. unfold B_exports in Hin. simpl in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; inversion E; subst; clear E; eexists; (split; [reflexivity|]).
  - apply B_usingDict_sub; auto.
  - apply B_usingDDict_sub.
  - apply B_block_sub.
  - apply B_initDDict_sub.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
Qed.
