(* BLift3.v on BSubs34; group DICT with insertDictionary_spec34 (DICT34_G; the bodies proved in BSpecs3's
   DICT3_G lift to it).  Subtree B under API v3, the composition.  Generic lifting of a group's
   subtree_ok from a v2 context to a v3 one (DecLift.body_ok_sub), and the compositions of groups BLK and DICT
   and of the subtree, from the group facts given as hypotheses (BAsm3.v instantiates them). *)
Require Export Zstd.proof.dec.v3.B.BSubs34.
Require Import Zstd.proof.dec.B.BCompose.
Local Open Scope logic.

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

(* the lifting and the compositions for an allocator class (the context's H exports and ZSTD_initDDict_internal
   are those of the class) *)
Section BLift.
Context {CMI: cmem_preds}.

(* ---------- lifting ---------- *)

Lemma refines_app' (G1 G2 G1' G2': funspecs) :
  refines G1' G1 -> refines G2' G2 ->
  (forall i, In i (map fst G1) <-> In i (map fst G1')) ->
  refines (G1' ++ G2') (G1 ++ G2).
Proof.
  intros H1 H2 Hi i phi H. rewrite find_id_app_split in H |- *.
  destruct (initial_world.find_id i G1) as [x|] eqn:E1.
  - inversion H; subst. destruct (H1 i phi E1) as [phi' [E' Hs]]. rewrite E'. eauto.
  - assert (E1': initial_world.find_id i G1' = None).
    { apply find_id_none_iff. rewrite <- Hi. apply find_id_none_iff. exact E1. }
    rewrite E1'. apply H2. exact H.
Qed.

Lemma subtree_ok_lift (ids: list ident) (E G G': funspecs) :
  subtree_ok ids E G -> refines G' G ->
  NoDup (map fst Vprog ++ map fst G ++ ids) -> NoDup (map fst Vprog ++ map fst G' ++ ids) ->
  (forall i, In i (map fst G) <-> In i (map fst G')) ->
  subtree_ok ids E G'.
Proof.
  intros [S [H1 [H2 H3]]] Hr Hn Hn' Hi. exists S. split; [exact H1 | split; [exact H2 |]].
  eapply Forall_impl; [| exact H3]. intros x Hx.
  apply (body_ok_sub_p (G ++ S)); [exact Hx | | |].
  - apply refines_app'; [exact Hr | apply refines_refl | exact Hi].
  - rewrite map_app, H1. exact Hn.
  - rewrite map_app, H1. exact Hn'.
Qed.

(* the v3 context of B's groups refines v2's *)
Definition G_BLK3 : funspecs := G_B03 ++ ENT_exports ++ HUF_exports.

Lemma map_fst_H_exports3 : map fst H_exports3 = map fst H_exports.
Proof. reflexivity. Qed.

Lemma G_B03_refines : refines G_B03 G_B0.
Proof.
  apply refines_app'; [apply refines_refl | apply H_exports3_refines_p | tauto].
Qed.

Lemma G_B03_names (I: funspecs) : forall i, In i (map fst (G_B0 ++ I)) <-> In i (map fst (G_B03 ++ I)).
Proof.
  intros i. unfold G_B0, G_B03. rewrite !map_app, map_fst_H_exports3. tauto.
Qed.

Lemma G_B03_refines_app (I: funspecs) : refines (G_B03 ++ I) (G_B0 ++ I).
Proof.
  apply refines_app'; [apply G_B03_refines | apply refines_refl |].
  intros i. unfold G_B0, G_B03. rewrite !map_app, map_fst_H_exports3. tauto.
Qed.

Lemma nodup_B03 (I: funspecs) (ids: list ident) :
  NoDup (map fst Vprog ++ map fst (G_B0 ++ I) ++ ids) -> NoDup (map fst Vprog ++ map fst (G_B03 ++ I) ++ ids).
Proof. unfold G_B0, G_B03. rewrite !map_app, map_fst_H_exports3. auto. Qed.

(* a group proved against G_B0 ++ I holds against G_B03 ++ I *)
Lemma group_lift (ids: list ident) (E I: funspecs) :
  subtree_ok ids E (G_B0 ++ I) -> NoDup (map fst Vprog ++ map fst (G_B0 ++ I) ++ ids) ->
  subtree_ok ids E (G_B03 ++ I).
Proof.
  intros H Hn. exact (subtree_ok_lift ids E (G_B0 ++ I) (G_B03 ++ I) H (G_B03_refines_app I) Hn
    (nodup_B03 I ids Hn) (G_B03_names I)).
Qed.

(* ---------- group BLK ---------- *)

Lemma blk3_nodup (I: funspecs) (ids: list ident) :
  nodupb (map fst Vprog ++ map fst (G_BLK ++ I) ++ ids) = true ->
  NoDup (map fst Vprog ++ map fst (G_BLK ++ I) ++ ids).
Proof. apply nodupb_ok. Qed.

Definition blk3_groups : list group :=
  [ (ids_LIT, LIT3_exports, LIT_imports); (ids_HDR, HDR_exports, HDR_imports);
    (ids_SEQ, SEQ_exports, SEQ_imports); (ids_TOP, TOP3_exports, TOP3_imports) ].


Lemma BLK3_compose :
  LIT3_obligation -> HDR_obligation -> SEQ_obligation -> TOP3_obligation ->
  subtree_ok ids_BLK TOP3_exports G_BLK3.
Proof.
  intros HL HH HS HT.
  assert (Lift: forall ids E I, subtree_ok ids E (G_BLK ++ I) ->
            nodupb (map fst Vprog ++ map fst (G_BLK ++ I) ++ ids) = true ->
            subtree_ok ids E (G_BLK3 ++ I)).
  { intros ids E I H Hn.
    change G_BLK3 with (G_B03 ++ (ENT_exports ++ HUF_exports)). rewrite <- app_assoc.
    change G_BLK with (G_B0 ++ (ENT_exports ++ HUF_exports)) in H, Hn.
    rewrite <- (app_assoc G_B0) in H, Hn.
    apply group_lift; [exact H | apply nodupb_ok; exact Hn]. }
  apply (subtree_compose G_BLK3 blk3_groups).
  - unfold blk3_groups, g_ids, g_exp, g_imp. cbn [fst snd].
    repeat apply Forall_cons; try apply Forall_nil; apply Lift; try assumption; vm_compute; reflexivity.
  - unfold blk3_groups, g_imp, g_exp. cbn [fst snd map concat app].
    unfold LIT_imports, HDR_imports, SEQ_imports, TOP3_imports,
      LIT3_exports, HDR_exports, SEQ_exports, TOP3_exports. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; intros x Hx; repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. lazy. reflexivity.
  - unfold blk3_groups, g_exp. cbn [fst snd map concat app]. intros x Hx. apply in_or_app. right.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hx.
Qed.

(* ---------- group DICT ---------- *)

Definition DICT3_exports : funspecs :=
  [ ZSTD_decompressBegin_spec3s; ZSTD_decompressBegin_usingDict_spec3 tabs_def;
    ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def; ZSTD_initDDict_internal_spec3 dent_def;
    ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec ].

Lemma DICT34_refines : refines DICT34_G DICT_G.
Proof.
  unfold DICT34_G, DICT_G. apply refines_app'.
  - apply G_B03_refines_app.
  - apply refines_pointwise. unfold DICT34_specs, DICT_specs.
    repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]).
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply loadinto3_sub.
    + apply B_initDDict_sub.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply ins34_sub.
    + apply begin3s_sub.
    + apply B_usingDict_sub; exact dent_def.
    + apply B_usingDDict_sub.
  - intros i. apply G_B03_names.
Qed.

Lemma DICT34_refines3 : refines DICT34_G DICT3_G.
Proof.
  unfold DICT34_G, DICT3_G. apply refines_app'.
  - apply refines_refl.
  - apply refines_pointwise. unfold DICT34_specs, DICT3_specs.
    repeat apply Forall2_cons; try apply Forall2_nil; (split; [reflexivity |]).
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply ins34_sub3.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
    + apply funspec_sub_refl.
  - tauto.
Qed.

Lemma DICT_G_nodup : NoDup (map fst Vprog ++ map fst DICT_G).
Proof. apply nodupb_ok. lazy. reflexivity. Qed.

Lemma DICT3_G_nodup : NoDup (map fst Vprog ++ map fst DICT3_G).
Proof. apply nodupb_ok. lazy. reflexivity. Qed.

Lemma DICT34_G_nodup : NoDup (map fst Vprog ++ map fst DICT34_G).
Proof. apply nodupb_ok. lazy. reflexivity. Qed.

Lemma DICT34_compose :
  body_ok DICT_G ZSTD_DDict_dictContent_spec -> body_ok DICT_G ZSTD_DDict_dictSize_spec ->
  body_ok DICT_G ZSTD_copyDDictParameters_spec -> body_ok DICT_G ZSTD_refDictContent_spec ->
  body_ok DICT_G ZSTD_loadDEntropy_spec ->
  (body_ok DICT34_G ZSTD_decompressBegin_spec3s /\
   body_ok DICT34_G ZSTD_decompress_insertDictionary_spec34 /\
   body_ok DICT34_G (ZSTD_decompressBegin_usingDict_spec3 tabs_def)) ->
  (body_ok DICT3_G ZSTD_loadEntropy_intoDDict_spec3 /\
   body_ok DICT3_G (ZSTD_initDDict_internal_spec3 dent_def)) ->
  body_ok DICT3_G (ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def) ->
  subtree_ok ids_DICT DICT3_exports G_BLK3.
Proof.
  intros Hc Hs Hcp Hr Hl [Hb [Hi Hu]] [Hli Hin] Hd.
  assert (L: forall ix, body_ok DICT_G ix -> body_ok DICT34_G ix).
  { intros ix H. apply (body_ok_sub_p DICT_G); [exact H | exact DICT34_refines | exact DICT_G_nodup | exact DICT34_G_nodup]. }
  assert (L3: forall ix, body_ok DICT3_G ix -> body_ok DICT34_G ix).
  { intros ix H. apply (body_ok_sub_p DICT3_G); [exact H | exact DICT34_refines3 | exact DICT3_G_nodup | exact DICT34_G_nodup]. }
  exists DICT34_specs. split; [exact DICT34_specs_ids | split].
  - unfold DICT3_exports, DICT34_specs. intros x Hx.
    repeat (destruct Hx as [Hx | Hx]; [subst x; simpl; tauto |]). destruct Hx.
  - change (G_BLK3 ++ DICT34_specs) with DICT34_G.
    match goal with |- Forall _ ?l => change l with (ZSTD_DDict_dictContent_spec :: ZSTD_DDict_dictSize_spec :: ZSTD_copyDDictParameters_spec :: ZSTD_loadEntropy_intoDDict_spec3 :: ZSTD_initDDict_internal_spec3 dent_def :: ZSTD_refDictContent_spec :: ZSTD_loadDEntropy_spec :: ZSTD_decompress_insertDictionary_spec34 :: ZSTD_decompressBegin_spec3s :: ZSTD_decompressBegin_usingDict_spec3 tabs_def :: ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def :: nil) end.
    apply Forall_cons; [exact (L _ Hc) |]. apply Forall_cons; [exact (L _ Hs) |].
    apply Forall_cons; [exact (L _ Hcp) |]. apply Forall_cons; [exact (L3 _ Hli) |].
    apply Forall_cons; [exact (L3 _ Hin) |]. apply Forall_cons; [exact (L _ Hr) |].
    apply Forall_cons; [exact (L _ Hl) |]. apply Forall_cons; [exact Hi |].
    apply Forall_cons; [exact Hb |]. apply Forall_cons; [exact Hu |].
    apply Forall_cons; [exact (L3 _ Hd) |]. apply Forall_nil.
Qed.

(* ---------- the subtree ---------- *)

(* B's exports with the decompressBegin specification B proves (it implies DecIface3's: begin3s_api_sub) *)
Definition B_exports3s : funspecs :=
  [ ZSTD_decompressBegin_spec3s; ZSTD_decompressBegin_usingDict_spec3 tabs_def;
    ZSTD_decompressBegin_usingDDict_spec3 dent_def tabs_def;
    ZSTD_decompressBlock_internal_spec3 dent_def tabs_def; ZSTD_initDDict_internal_spec3 dent_def;
    ZSTD_DDict_dictContent_spec; ZSTD_DDict_dictSize_spec ].

Lemma B3_compose :
  ENT_obligation -> HUF_obligation ->
  subtree_ok ids_BLK TOP3_exports G_BLK3 -> subtree_ok ids_DICT DICT3_exports G_BLK3 ->
  subtree_ok ids_B3 B_exports3s (Gprog ++ H_exports3).
Proof.
  intros HE HH HB HD. change (Gprog ++ H_exports3) with G_B03.
  apply subtree_compose with
    (gs := [ (ids_ENT, ENT_exports, []); (ids_HUF, HUF_exports, ENT_exports);
             (ids_BLK, TOP3_exports, ENT_exports ++ HUF_exports);
             (ids_DICT, DICT3_exports, ENT_exports ++ HUF_exports) ]).
  - repeat apply Forall_cons; try apply Forall_nil; unfold g_ids, g_exp, g_imp; simpl fst; simpl snd.
    + rewrite app_nil_r. unfold ENT_obligation in HE.
      pose proof (group_lift ids_ENT ENT_exports [] ltac:(rewrite app_nil_r; exact HE)) as X.
      rewrite app_nil_r in X. apply X. apply nodupb_ok. lazy. reflexivity.
    + apply group_lift; [exact HH |]. apply nodupb_ok. lazy. reflexivity.
    + exact HB.
    + exact HD.
  - repeat apply Forall_cons; try apply Forall_nil; unfold g_ids, g_exp, g_imp; simpl fst; simpl snd;
      intros x Hx; simpl in *; repeat (rewrite in_app_iff in * ); tauto.
  - apply inclb_ok. cbv [concat map g_ids fst]. vm_compute. reflexivity.
  - apply inclb_ok. cbv [concat map g_ids fst]. vm_compute. reflexivity.
  - apply nodupb_ok. cbv [concat map g_ids fst]. vm_compute. reflexivity.
  - apply nodupb_ok. lazy. reflexivity.
  - unfold B_exports3s, TOP3_exports, DICT3_exports. intros x Hx. simpl in *.
    repeat (rewrite in_app_iff in * ). simpl in *. tauto.
Qed.

End BLift.
