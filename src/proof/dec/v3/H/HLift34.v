(* Subtree H, API v3: lifting v2's body proofs (against HSpecs.H_G) to H3_G.
   Local copies (suffix _h) of the proofs of DecLift.body_ok_sub and of the funspec_sub lemmas of
   DecLift.H_exports3_refines, plus findFrameSizeInfo's spec3 against its v2 spec. *)
Require Export Zstd.proof.dec.v3.DecSubtrees3.
Require Export Zstd.proof.dec.v3.H.HSpecs3.
Local Open Scope logic.

(* API v3.4 and the revised usingDict specification: copy of HLift3 without DecLift (whose B part no longer
   checks against it): local copies of
   DecLift.refines and DecLift.find_id_app_split *)
Definition refines (G' G: funspecs) : Prop :=
  forall i phi, initial_world.find_id i G = Some phi ->
    exists phi', initial_world.find_id i G' = Some phi' /\ funspec_sub phi' phi.

Lemma find_id_app_split {A} (i: ident) (G1 G2: list (ident * A)) :
  initial_world.find_id i (G1 ++ G2) =
  match initial_world.find_id i G1 with Some x => Some x | None => initial_world.find_id i G2 end.
Proof.
  induction G1 as [|[j x] G1 IH]; simpl; [reflexivity |].
  destruct (Memory.EqDec_ident i j); [reflexivity | exact IH].
Qed.

(* ---------- body_ok_sub (copy of DecLift's proof) ---------- *)

Lemma make_tycontext_g_find_id_h (V: varspecs) (G: funspecs) (i: ident) :
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

Lemma find_id_in_fst_h {A} (i: ident) (l: list (ident * A)) (x: A) :
  initial_world.find_id i l = Some x -> In i (map fst l).
Proof.
  induction l as [|[j y] l IH]; simpl; [discriminate |].
  destruct (Memory.EqDec_ident i j); [left; congruence | intros H; right; exact (IH H)].
Qed.

Lemma find_id_none_h {A} (i: ident) (l: list (ident * A)) :
  ~ In i (map fst l) -> initial_world.find_id i l = None.
Proof.
  induction l as [|[j y] l IH]; simpl; [reflexivity |].
  destruct (Memory.EqDec_ident i j); [intros H; exfalso; apply H; left; congruence |].
  intros H; apply IH; tauto.
Qed.

Lemma NoDup_app_disj_h {A} (l1 l2: list A) (x: A) :
  NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; simpl; [tauto |].
  intros Hn Hin. inversion Hn as [|y' l' Hy Hl]; subst. destruct Hin as [<-|Hin].
  - intros Hx. apply Hy. apply in_or_app; right; exact Hx.
  - exact (IH Hl Hin).
Qed.

Lemma refines_tycontext_sub_h (f: function) (G G': funspecs) :
  refines G' G -> NoDup (map fst Vprog ++ map fst G') ->
  tycontext_sub (func_tycontext f Vprog G nil) (func_tycontext f Vprog G' nil).
Proof.
  intros Hr Hnd.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  split; [intro id; destruct (Maps.PTree.get _ _); auto |].
  split; [auto |]. split; [auto |].
  split; [| split; [| intro id; first [exact I | apply Annotation_sub_refl]]].
  - intro id. hnf. rewrite !make_tycontext_g_find_id_h.
    destruct (initial_world.find_id id G) as [phi|] eqn:E.
    + destruct (Hr id phi E) as [phi' [E' Hs]]. rewrite E'.
      f_equal. apply type_of_funspec_sub; exact Hs.
    + destruct (initial_world.find_id id Vprog) as [t|] eqn:EV; [| exact I].
      assert (N: initial_world.find_id id G' = None).
      { apply find_id_none_h.
        exact (NoDup_app_disj_h _ _ _ Hnd (find_id_in_fst_h _ _ _ EV)). }
      rewrite N. reflexivity.
  - intro id. rewrite !initial_world.make_tycontext_s_find_id.
    destruct (initial_world.find_id id G) as [phi|] eqn:E; [| exact I].
    destruct (Hr id phi E) as [phi' [E' Hs]]. exists phi'. split; [exact E' |].
    apply funspec_sub_sub_si; exact Hs.
Qed.

Lemma body_ok_sub_h (G G': funspecs) (ix: ident * funspec) :
  body_ok G ix -> refines G' G -> NoDup (map fst Vprog ++ map fst G') -> body_ok G' ix.
Proof.
  intros [f [Hf [Hcc Hb]]] Hr Hnd'. exists f; split; [exact Hf | split; [exact Hcc |]].
  eapply semax_body_subsumption; [exact Hb |].
  apply refines_tycontext_sub_h; assumption.
Qed.

(* ---------- the v3 specs refine the v2 ones (copies of DecLift's proofs) ---------- *)

Lemma refines_pointwise_h (G' G: funspecs) :
  Forall2 (fun a b => fst a = fst b /\ funspec_sub (snd a) (snd b)) G' G -> refines G' G.
Proof.
  induction 1 as [|[i' phi'] [j phi] G' G [Ei Hs] _ IH]; intros i psi H; simpl in *; [discriminate|].
  subst i'. destruct (Memory.EqDec_ident i j).
  - inversion H; subst. exists phi'. split; [reflexivity | exact Hs].
  - exact (IH i psi H).
Qed.

Lemma startingInputLength_sub3_h :
  funspec_sub (snd ZSTD_startingInputLength_spec3) (snd ZSTD_startingInputLength_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros u [g args]. simpl.
  Exists 0 (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2; auto].
  unfold PROPx; simpl. rewrite !prop_true_andp by auto. auto.
Qed.

Lemma frameHeaderSize_internal_sub3_h :
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

Lemma getFrameHeader_advanced_sub3_h :
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

Lemma findFrameCompressedSize_advanced_sub3_h :
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

Lemma findFrameSizeInfo_sub3 :
  funspec_sub (snd ZSTD_findFrameSizeInfo_spec3) (snd ZSTD_findFrameSizeInfo_spec).
Proof.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[gv shf] pf] sh] base] N] c] off] s] [g args]. simpl.
  Exists (gv, shf, pf, sh, base, N, c, off, s, 0) (@emp mpred _ _). rewrite emp_sepcon. simpl.
  apply andp_right; [apply andp_left2 | apply prop_right; intros rho'; rewrite emp_sepcon; apply andp_left2].
  - unfold PROPx; simpl. apply andp_derives; [apply prop_derives; tauto | auto].
  - Intros nb cs db. Exists nb cs db. unfold PROPx; simpl. apply andp_derives; [apply prop_derives | auto].
    rewrite ?frame_size_info_zstd1. tauto.
Qed.

Lemma refines_ext_h (G' G X: funspecs) : refines G' G -> refines (G' ++ X) G.
Proof.
  intros H i phi E. destruct (H i phi E) as [phi' [E' Hs]]. exists phi'.
  rewrite find_id_app_split, E'. auto.
Qed.

Lemma refines_prefix_h (P G' G: funspecs) : refines G' G -> refines (P ++ G') (P ++ G).
Proof.
  intros H i phi E. rewrite find_id_app_split in E |- *.
  destruct (initial_world.find_id i P) as [x|]; [exists phi; split; [exact E | apply funspec_sub_refl] |].
  exact (H i phi E).
Qed.

Lemma H3_specs_refines : refines H3_specs H_specs.
Proof.
  apply refines_ext_h, refines_pointwise_h. unfold H3_core, H_specs.
  repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]);
    first [ apply funspec_sub_refl | apply startingInputLength_sub3_h | apply frameHeaderSize_internal_sub3_h
          | apply getFrameHeader_advanced_sub3_h | apply findFrameSizeInfo_sub3
          | apply findFrameCompressedSize_advanced_sub3_h ].
Qed.

Lemma H3_G_refines : refines H3_G H_G.
Proof. apply refines_prefix_h, H3_specs_refines. Qed.

Lemma H3_nodup : NoDup (map fst Vprog ++ map fst H3_G).
Proof.
  unfold H3_G. rewrite map_app, H3_names.
  apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

(* a v2 body of H holds in the v3 context *)
Lemma lift_H (ix: ident * funspec) : body_ok H_G ix -> body_ok H3_G ix.
Proof. intros H. exact (body_ok_sub_h _ _ _ H H3_G_refines H3_nodup). Qed.

Lemma lift_H_body (ix: ident * funspec) (f: function) :
  zstd_fun (fst ix) f -> fn_callconv f = callingconvention_of_funspec (snd ix) ->
  semax_body Vprog H_G f ix -> body_ok H3_G ix.
Proof. intros Hf Hc Hb. apply lift_H. exists f; auto. Qed.

(* a v3 body proved against H3_G *)
Lemma body_H3 (ix: ident * funspec) (f: function) :
  zstd_fun (fst ix) f -> fn_callconv f = callingconvention_of_funspec (snd ix) ->
  semax_body Vprog H3_G f ix -> body_ok H3_G ix.
Proof. intros Hf Hc Hb. exists f; auto. Qed.
