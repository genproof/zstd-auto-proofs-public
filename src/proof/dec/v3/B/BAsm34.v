(* BAsm3.v on BLift34 and body34_dict_ins (insertDictionary's error branch keeps fParams).  Subtree B under
   API v3: the group facts (v2 proofs of ENT, HUF, HDR, SEQ and
   the unchanged DICT bodies; the v3 re-proofs LIT3, TOP3, DICT3 bodies) composed by BLift3.B3_compose. *)
Require Export Zstd.proof.dec.v3.B.BLift34.
Require Import Zstd.proof.dec.B.BLemmas Zstd.proof.dec.B.BEnt Zstd.proof.dec.B.BHuf Zstd.proof.dec.B.blk.BlkHDR Zstd.proof.dec.B.blk.BlkSEQ Zstd.proof.dec.B.blk.BlkGlobals Zstd.proof.dec.B.dict.body_dict_small Zstd.proof.dec.B.dict.body_dict_load Zstd.proof.dec.B.dict.body_dict_copy Zstd.proof.dec.B.dict.body_dict_ins Zstd.proof.dec.v3.B.BlkLIT3 Zstd.proof.dec.v3.B.BlkTOP3 Zstd.proof.dec.v3.B.body34_dict_ins Zstd.proof.dec.v3.B.body3_dict_init Zstd.proof.dec.v3.B.body3_dict_ddict.

(* for an allocator class: the H exports and ZSTD_initDDict_internal are those of the class *)
Section BAsm.
Context {CMI: cmem_preds}.

Lemma B3_core34 : subtree_ok ids_B3 B_exports3s (Gprog ++ H_exports3 (CMI:=CMI)).
Proof.
  apply B3_compose.
  - exact ENT_ok.
  - exact HUF_ok.
  - apply BLK3_compose.
    + exact LIT3_ok.
    + exact HDR_ok.
    + exact (SEQ_ok BlkGlobals.globals_ok).
    + exact (TOP3_ok BlkGlobals.globals_ok).
  - apply DICT34_compose.
    + exact body_dict_content.
    + exact body_dict_size.
    + exact body_dict_copy.
    + exact body_refDictContent.
    + exact body_dict_load.
    + exact DICT34_ins_ok.
    + exact DICT3_init_ok.
    + exact DICT3_ddict_ok.
Qed.

(* B's exports up to funspec_sub: DecIface3's B_exports3, with B's stronger ZSTD_decompressBegin *)
Lemma B3_exports_sub34 : api_sub (B_exports3 (CMI:=CMI) dent_def tabs_def) B_exports3s.
Proof.
  unfold api_sub, B_exports3, B_exports3s.
  repeat apply Forall_cons; try apply Forall_nil; simpl; eexists; (split; [reflexivity |]).
  - apply begin3s_api_sub.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
  - apply funspec_sub_refl.
Qed.

(* B3_obligation at one class, with subtree_api_ok in place of subtree_ok:
   B's S holds ZSTD_decompressBegin_spec3s, which implies DecIface3's ZSTD_decompressBegin_spec3 *)
Lemma B3_api34 :
  subtree_api_ok ids_B3 (B_exports3 (CMI:=CMI) dent_def tabs_def) (Gprog ++ H_exports3 (CMI:=CMI)).
Proof.
  destruct B3_core34 as [S [H1 [H2 H3]]]. exists S. split; [exact H1 | split; [| exact H3]].
  pose proof B3_exports_sub34 as Hs. unfold api_sub in *. eapply Forall_impl; [| exact Hs].
  intros e [s [Hf Hsub]]. exists s. split; [| exact Hsub].
  assert (Hin: In (fst e, s) B_exports3s).
  { apply initial_world.find_id_e in Hf. exact Hf. }
  apply H2 in Hin. apply initial_world.find_id_i; [exact Hin |].
  apply list_norepet_NoDup. rewrite H1. apply BCompose.nodupb_ok. vm_compute. reflexivity.
Qed.

End BAsm.

(* B3_obligation (DecSubtrees3): B's tables and DDict entropy representations, for every allocator class *)
Lemma B3_ok_api34 :
  exists (DENT: dent_pred) (TABS: tabs_pred),
    DENT_OK DENT /\ TABS_OK TABS /\
    forall {CMI: cmem_preds},
      subtree_api_ok ids_B3 (B_exports3 (CMI:=CMI) DENT TABS) (Gprog ++ H_exports3 (CMI:=CMI)).
Proof.
  exists dent_def, tabs_def. split; [exact dent_def_ok | split; [exact tabs_def_ok |]].
  intros CMI. exact B3_api34.
Qed.
