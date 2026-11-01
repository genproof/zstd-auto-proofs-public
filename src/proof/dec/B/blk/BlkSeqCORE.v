(* Sub-group CORE of SEQ (BlkGroups.ids_SEQ): the 17 sequence functions above the
   byte copies — the FSE state machine (ZSTD_initFseState, ZSTD_updateFseStateWithDInfo, ZSTD_decodeSequence),
   the sequence executors (ZSTD_execSequence{,End}{,SplitLitBuffer}), and the three decode loops with their
   _default wrappers, dispatchers and ZSTD_prefetchMatch.

   Imports the five COPY helpers (BlkSeqCOPY); exports the three dispatchers (SEQ_exports of BlkGroups:
   ZSTD_decompressSequences / ...SplitLitBuffer / ...Long, the fixed `seqs_spec` of BlkIface).  CORE has its
   own internal interface (the seqState_t representation `seqstate_rep`, the one `decode_seqs` step of
   ZSTD_decodeSequence with the C offset resolution = Block.resolve_offset, the one `exec_seqs` step of
   ZSTD_execSequence with the extDict form of patch item 13 (patch/GENPROOF-PATCH.md), the loop invariants)
   and is split into DEC (the 3 FSE functions), EXEC (the 4 executors) and LOOP (the 10 loop/dispatcher
   functions, itself split short / split-literal / long / wrappers).  GLOBALS_obligation (predef tables in the
   globals) is needed where a sequence table is the predefined one (TGlob): the loops split `zstd_globals`. *)
Require Export Zstd.proof.dec.B.blk.BlkSeqCOPY.
Require Import Zstd.proof.dec.B.BCompose.
Require Import Zstd.proof.dec.B.blk.BlkSeqDEC Zstd.proof.dec.B.blk.BlkSeqEXEC Zstd.proof.dec.B.blk.BlkSeqLOOP.
Local Open Scope logic.

Definition ids_CORE : list ident :=
  [ _ZSTD_initFseState; _ZSTD_updateFseStateWithDInfo; _ZSTD_decodeSequence;
    _ZSTD_execSequenceEnd; _ZSTD_execSequenceEndSplitLitBuffer; _ZSTD_execSequence;
    _ZSTD_execSequenceSplitLitBuffer; _ZSTD_decompressSequences_bodySplitLitBuffer;
    _ZSTD_decompressSequences_body; _ZSTD_decompressSequences_default;
    _ZSTD_decompressSequencesSplitLitBuffer_default; _ZSTD_prefetchMatch;
    _ZSTD_decompressSequencesLong_body; _ZSTD_decompressSequencesLong_default;
    _ZSTD_decompressSequences; _ZSTD_decompressSequencesSplitLitBuffer; _ZSTD_decompressSequencesLong ].
Definition CORE_exports : funspecs := SEQ_exports.
Definition CORE_imports : funspecs := COPY_exports.
Definition CORE_obligation : Prop := subtree_ok ids_CORE CORE_exports (G_BLK ++ CORE_imports).

(* the three sub-groups, in the context G_BLK ++ COPY_exports *)
Definition core_groups : list group :=
  [ (DEC_ids, DEC_exports, []); (EXEC_ids, EXEC_exports, []); (LOOP_ids, LOOP_exports, LOOP_imports) ].

Ltac in_spec := solve [repeat (first [left; reflexivity | right])].

Lemma subtree_ok_mono (ids: list ident) (E G G': funspecs) :
  subtree_ok ids E G -> incl G G' -> NoDup (map fst Vprog ++ map fst G' ++ ids) -> subtree_ok ids E G'.
Proof.
  intros [S [H1 [H2 H3]]] Hi Hnd. exists S; split; [exact H1 | split; [exact H2 |]].
  eapply Forall_impl; [|exact H3]. intros x Hx. eapply body_ok_mono; [exact Hx | |].
  - apply incl_app; [apply incl_appl, Hi | apply incl_appr, incl_refl].
  - rewrite map_app, H1. exact Hnd.
Qed.

Lemma core_imports_ok :
  Forall (fun g => incl (g_imp g) (concat (map g_exp core_groups))) core_groups.
Proof.
  unfold core_groups, g_imp, g_exp. cbn [fst snd map concat app].
  unfold LOOP_imports, DEC_exports, EXEC_exports, LOOP_exports, SEQ_exports. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; intros x Hx;
    repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma core_exports_ok : incl CORE_exports (concat (map g_exp core_groups)).
Proof.
  unfold core_groups, g_exp. cbn [fst snd map concat app].
  unfold CORE_exports, DEC_exports, EXEC_exports, LOOP_exports, SEQ_exports. cbn [app].
  intros x Hx; repeat (destruct Hx as [<-|Hx]; [in_spec|]); contradiction.
Qed.

Lemma CORE_ok : GLOBALS_obligation -> CORE_obligation.
Proof.
  intro HG. unfold CORE_obligation, CORE_imports.
  apply (subtree_compose (G_BLK ++ COPY_exports) core_groups).
  - unfold core_groups, g_ids, g_exp, g_imp. cbn [fst snd].
    apply Forall_cons.
    { rewrite app_nil_r. eapply subtree_ok_mono; [exact DEC_ok | |].
      - unfold DEC_imports. apply incl_app; [apply incl_appl, incl_refl|].
        apply incl_appr. unfold COPY_exports. intros x Hx; destruct Hx as [<-|[]]; in_spec.
      - apply nodupb_ok. vm_compute. reflexivity. }
    apply Forall_cons; [rewrite app_nil_r; exact EXEC_ok|].
    apply Forall_cons; [exact (LOOP_ok HG)|].
    apply Forall_nil.
  - exact core_imports_ok.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply inclb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - apply nodupb_ok. vm_compute. reflexivity.
  - exact core_exports_ok.
Qed.
