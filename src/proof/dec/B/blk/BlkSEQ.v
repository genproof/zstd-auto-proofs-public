(* Sub-group SEQ of group BLK (BlkGroups.v): the sequence
   decoders (22 functions, ids_SEQ).  Assembled from two sub-sub-groups with BCompose.subtree_compose
   (pattern: BBlk.v): COPY (the five byte/struct copies, BlkSeqCOPY) and CORE (the FSE machine, the
   executors, the three loops, BlkSeqCORE; it imports COPY and has its own internal interface).
   GLOBALS_obligation (predefined tables in the globals) is proved in BlkGlobals.v and threaded to CORE. *)
Require Export Zstd.proof.dec.B.blk.BlkGroups.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.blk.BlkSeqCOPY Zstd.proof.dec.B.blk.BlkSeqCORE.
Local Open Scope logic.

Definition seq_groups : list group :=
  [ (COPY_ids, COPY_exports, COPY_imports); (ids_CORE, CORE_exports, CORE_imports) ].

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

Lemma seq_imports_ok :
  Forall (fun g => incl (g_imp g) (concat (map g_exp seq_groups))) seq_groups.
Proof.
  unfold seq_groups, g_imp, g_exp. cbn [fst snd map concat app].
  unfold COPY_imports, CORE_imports, COPY_exports, CORE_exports, SEQ_exports. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; intros x Hx;
    repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma seq_exports_ok : incl SEQ_exports (concat (map g_exp seq_groups)).
Proof.
  unfold seq_groups, g_exp. cbn [fst snd map concat app].
  unfold COPY_exports, CORE_exports, SEQ_exports. cbn [app].
  intros x Hx; repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma SEQ_ok : GLOBALS_obligation -> SEQ_obligation.
Proof.
  intro HG. unfold SEQ_obligation.
  change (G_BLK ++ SEQ_imports) with G_BLK.
  apply (subtree_compose G_BLK seq_groups).
  - unfold seq_groups, g_ids, g_exp, g_imp. cbn [fst snd].
    apply Forall_cons; [exact COPY_ok|].
    apply Forall_cons; [exact (CORE_ok HG)|].
    apply Forall_nil.
  - exact seq_imports_ok.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - exact seq_exports_ok.
Qed.
