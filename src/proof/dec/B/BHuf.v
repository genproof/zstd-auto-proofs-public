(* Group HUF of subtree B (BGroups.v).  Assembled from its five sub-groups
   (huf/HufGroups.v) with BCompose.subtree_compose. *)
Require Export Zstd.proof.dec.B.BGroups.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.huf.HufX1T Zstd.proof.dec.B.huf.HufX2T Zstd.proof.dec.B.huf.HufX1D Zstd.proof.dec.B.huf.HufX2D Zstd.proof.dec.B.huf.HufTop.

Definition huf_groups : list group :=
  [ (ids_X1T, X1T_exports, X1T_imports); (ids_X2T, X2T_exports, X2T_imports);
    (ids_X1D, X1D_exports, X1D_imports); (ids_X2D, X2D_exports, X2D_imports);
    (ids_TOP, TOP_exports, TOP_imports) ].

Lemma huf_nodup : NoDup (map fst Vprog ++ map fst G_HUF ++ ids_HUF).
Proof.
  apply nodupb_ok. lazy. reflexivity.
Qed.

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

Lemma huf_imports_ok :
  Forall (fun g => incl (g_imp g) (concat (map g_exp huf_groups))) huf_groups.
Proof.
  unfold huf_groups, g_imp, g_exp. cbn [fst snd map concat app].
  unfold X1T_imports, X2T_imports, X1D_imports, X2D_imports, TOP_imports,
    X1T_exports, X2T_exports, X1D_exports, X2D_exports, TOP_exports. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; intros x Hx; repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma huf_exports_ok : incl HUF_exports (concat (map g_exp huf_groups)).
Proof.
  unfold huf_groups, g_exp. cbn [fst snd map concat app].
  unfold HUF_exports, X1T_exports, X2T_exports, X1D_exports, X2D_exports, TOP_exports. cbn [app].
  intros x Hx; repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma HUF_ok : HUF_obligation.
Proof.
  unfold HUF_obligation. change (G_B0 ++ ENT_exports) with G_HUF.
  apply (subtree_compose G_HUF huf_groups).
  - unfold huf_groups, g_ids, g_exp, g_imp. cbn [fst snd].
    apply Forall_cons; [exact X1T_ok|]. apply Forall_cons; [exact X2T_ok|].
    apply Forall_cons; [exact X1D_ok|]. apply Forall_cons; [exact X2D_ok|].
    apply Forall_cons; [exact TOP_ok|]. apply Forall_nil.
  - exact huf_imports_ok.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - exact huf_nodup.
  - exact huf_exports_ok.
Qed.
