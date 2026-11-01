(* Subtree FS of the decoder, API v3: the assembly of FS3_obligation from the parts' obligations.
   FS3_S: the 67 specifications in ids_FS3 order: the fixed ones of FSOblig3, decompressFrame's sf (frames part),
   the hash set's internals (set part), decompressContinueStream (streaming part), and for ZSTD_decompressContinue
   the intersection (VST's binary_intersection) of the streaming part's specification and the API one the
   buffer-less part proves. *)
Require Export Zstd.proof.dec.v3.FS.FSLift3.
Require Import Zstd.proof.dec.v3.FS.body3_ddict Zstd.proof.dec.v3.FS.body3_blocks Zstd.proof.dec.v3.FS.body3_small Zstd.proof.dec.v3.FS.body3_life Zstd.proof.dec.v3.FS.body3_ctxops Zstd.proof.dec.v3.FS.body3_load Zstd.proof.dec.v3.FS.body3_dfh Zstd.proof.dec.v3.FS.body3_select Zstd.proof.dec.v3.FS.body3_set Zstd.proof.dec.v3.FS.body3_oneshot Zstd.proof.dec.v3.FS.FS3_frames Zstd.proof.dec.v3.FS.FS3_stream Zstd.proof.dec.v3.FS.FS3_bl.
Require Import Zstd.proof.dec.v3.FS.body3_advp Zstd.proof.dec.v3.FS.body3_estimate Zstd.proof.dec.v3.FS.FSCmOk.
Local Open Scope logic.

Section CM_FSAsm3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the 67 specifications ---------- *)

Section S.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.
Variable SR : srel3.
Variable BR : blrel.
Variables (sf gi ge gx cont ccs: funspec).

Definition FS3_S : funspecs :=
  [ ZSTD_limitCopy_spec;
    ZSTD_createDDict_advancedP_spec3 DENT;
    ZSTD_createDDict_spec (DD3x DENT);
    ZSTD_createDDict_byReference_spec (DD3x DENT);
    ZSTD_freeDDict_int_spec;
    ZSTD_getDictID_fromDDict_int_spec;
    (_ZSTD_DDictHashSet_getIndex, gi);
    (_ZSTD_DDictHashSet_emplaceDDict, ge);
    (_ZSTD_DDictHashSet_expand, gx);
    ZSTD_DDictHashSet_getDDict_spec;
    ZSTD_createDDictHashSet_spec;
    ZSTD_freeDDictHashSet_spec;
    ZSTD_DDictHashSet_addDDict_spec;
    ZSTD_DCtx_resetParameters_spec;
    ZSTD_initDCtx_internal_spec3 DENT TABS;
    ZSTD_createDCtx_internal_spec3 DENT TABS;
    ZSTD_createDCtx_spec (DC3x DENT TABS SR BR);
    ZSTD_clearDict_spec DENT;
    ZSTD_freeDCtx_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_selectFrameDDict_spec DENT;
    ZSTD_decodeFrameHeader_spec3 DENT;
    ZSTD_copyRawBlock_spec;
    ZSTD_setRleBlock_spec;
    ZSTD_DCtx_trace_end_spec;
    (_ZSTD_decompressFrame, sf);
    ZSTD_decompressMultiFrame_spec3 DENT TABS;
    ZSTD_decompress_usingDict_spec (DC3x DENT TABS SR BR);
    ZSTD_getDDict_spec DENT;
    ZSTD_decompressDCtx_spec (DC3x DENT TABS SR BR) (DD3x DENT);
    ZSTD_decompress_spec;
    ZSTD_nextSrcSizeToDecompress_spec;
    ZSTD_nextSrcSizeToDecompressWithInputSize_spec;
    ZSTD_nextInputType_spec;
    ZSTD_isSkipFrame_spec;
    (_ZSTD_decompressContinue, cont);
    ZSTD_decompress_usingDDict_int_spec3 DENT TABS;
    ZSTD_createDStream_spec (DC3x DENT TABS SR BR);
    ZSTD_freeDStream_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS;
    ZSTD_DCtx_loadDictionary_byReference_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_loadDictionary_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS;
    ZSTD_DCtx_refPrefix_spec (DC3x DENT TABS SR BR);
    ZSTD_initDStream_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_refDDict_int_spec3 DENT TABS;
    ZSTD_dParam_getBoundsP_spec3;
    ZSTD_dParam_withinBounds_spec3;
    ZSTD_DCtx_setParameter_spec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_reset_spec (DC3x DENT TABS SR BR);
    ZSTD_decodingBufferSize_internal_spec;
    ZSTD_DCtx_isOverflow_spec;
    ZSTD_DCtx_updateOversizedDuration_spec;
    ZSTD_DCtx_isOversizedTooLong_spec;
    ZSTD_outBuffer_copy_spec;
    ZSTD_checkOutBuffer_spec;
    (_ZSTD_decompressContinueStream, ccs);
    ZSTD_decompressStream_spec (DC3x DENT TABS SR BR) (DD3x DENT);
    ZSTD_checkContinuity_spec;
    ZSTD_initDStream_usingDict_aspec (DC3x DENT TABS SR BR);
    ZSTD_initDStream_usingDDict_aspec (DC3x DENT TABS SR BR) (DD3x DENT);
    ZSTD_resetDStream_aspec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_setMaxWindowSize_aspec (DC3x DENT TABS SR BR);
    ZSTD_DCtx_setFormat_aspec (DC3x DENT TABS SR BR);
    ZSTD_createDCtx_advancedP_spec (DC3x DENT TABS SR BR);
    ZSTD_estimateDCtxSize_spec;
    ZSTD_decodingBufferSize_min_spec;
    ZSTD_estimateDStreamSize_spec ].

End S.

Definition G_FS3 (DENT: dent_pred) (TABS: tabs_pred) : funspecs :=
  Gprog ++ H_exports3 ++ H_api3 ++ B_exports3 DENT TABS.

Lemma FS3_S_names DENT TABS SR BR sf gi ge gx cont ccs :
  map fst (FS3_S DENT TABS SR BR sf gi ge gx cont ccs) = ids_FS3.
Proof. reflexivity. Qed.

Lemma FS3_nodup DENT TABS SR BR sf gi ge gx cont ccs :
  NoDup (map fst Vprog ++ map fst (G_FS3 DENT TABS ++ FS3_S DENT TABS SR BR sf gi ge gx cont ccs)).
Proof.
  rewrite map_app, FS3_S_names.
  apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

End CM_FSAsm3_1.

Ltac in_S := simpl; solve [repeat (first [left; reflexivity | right])].

(* for any allocator class: the parts' obligations hold for it (their files are generic in the class), and the
   contexts DC3_of hold their allocator's state (FSCmOk) *)
Lemma FS3_assemble : FS3_obligation.
Proof.
  intros CMI DENT TABS HD HT.
  destruct (FRAMES3_ok DENT TABS HD HT) as [sf Hf].
  destruct SET3_ok as [_ Hset0]. destruct (Hset0 DENT TABS HD HT) as [sset [Hsm Hss]]. clear Hset0.
  destruct sset as [|[i0 gi] [|[i1 ge] [|[i2 gx] [|]]]]; try discriminate.
  simpl in Hsm. inversion Hsm; subst i0 i1 i2; clear Hsm.
  destruct (STREAM3_ok DENT TABS HD HT) as [SR [sst [Hstm Hst]]].
  destruct sst as [|[j0 c0] [|[j1 ccs] [|]]]; try discriminate.
  simpl in Hstm. inversion Hstm; subst j0 j1; clear Hstm.
  destruct (BL3_ok DENT TABS HD HT) as [BR Hbl]. specialize (Hbl SR). destruct Hbl as (Hcb & Hns & Hnit & Hbapi).
  specialize (Hst BR). specialize (Hf SR BR). specialize (Hss SR BR).
  set (capi := snd (ZSTD_decompressContinue_aspec (DC3x DENT TABS SR BR) (DD3x DENT))).
  rewrite Forall_cons_iff in Hst. destruct Hst as [Hds Hst]. rewrite Forall_cons_iff in Hst.
  destruct Hst as [Hc0 Hst]. rewrite Forall_cons_iff in Hst. destruct Hst as [Hccs _].
  pose proof (inter_some _ _ _ _ _ Hc0 Hcb) as Ei.
  set (chi := inter_of c0 capi) in *.
  set (S := FS3_S DENT TABS SR BR sf gi ge gx chi ccs).
  set (Gfin := G_FS3 DENT TABS ++ S).
  assert (Hnd: NoDup (map fst Vprog ++ map fst Gfin)) by apply FS3_nodup.
  assert (Hnd': NoDup (map fst Gfin)).
  { apply list_norepet_NoDup. apply list_norepet_NoDup in Hnd. apply list_norepet_append_right in Hnd. exact Hnd. }
  assert (Hfix: incl (FS3_fixed DENT TABS SR BR) S).
  { intros x Hx. unfold FS3_fixed in Hx. simpl in Hx.
    repeat (destruct Hx as [<- | Hx]; [unfold S, FS3_S; in_S | ]). contradiction. }
  assert (Hinc: incl (FS3_G DENT TABS SR BR) Gfin).
  { intros x Hx. unfold FS3_G in Hx. unfold Gfin, G_FS3. rewrite !in_app_iff in Hx |- *.
    destruct Hx as [H | [H | [H | [H | H]]]]; try tauto. right. apply Hfix. exact H. }
  assert (Hcin: In (_ZSTD_decompressContinue, chi) Gfin).
  { unfold Gfin. apply in_or_app. right. unfold S, FS3_S. in_S. }
  assert (Href: fs3_refines Gfin (FS3_G DENT TABS SR BR ++ [(_ZSTD_decompressContinue, c0); (_ZSTD_decompressContinueStream, ccs)])).
  { apply (fs3_refines_but _ _ _ chi Hnd' Hcin). intros i phi H. rewrite in_app_iff in H.
    destruct H as [H | [H | [H | []]]].
    - left. apply Hinc. exact H.
    - inversion H; subst. right. split; [reflexivity |]. apply funspec_sub_iff; exact (proj1 (binaryintersection_sub _ _ _ Ei)).
    - inversion H; subst. left. unfold Gfin. apply in_or_app. right. unfold S, FS3_S. in_S. }
  assert (HincF: incl (FS3_G DENT TABS SR BR ++ [(_ZSTD_decompressFrame, sf)]) Gfin).
  { intros x Hx. rewrite in_app_iff in Hx. destruct Hx as [H | [<- | []]]; [apply Hinc; exact H |].
    unfold Gfin. apply in_or_app. right. unfold S, FS3_S. in_S. }
  assert (HincS: incl (FS3_G DENT TABS SR BR ++ [(_ZSTD_DDictHashSet_getIndex, gi);
            (_ZSTD_DDictHashSet_emplaceDDict, ge); (_ZSTD_DDictHashSet_expand, gx)]) Gfin).
  { intros x Hx. rewrite in_app_iff in Hx. destruct Hx as [H | H]; [apply Hinc; exact H |].
    unfold Gfin. apply in_or_app. right. unfold S, FS3_S. simpl in H.
    destruct H as [<- | [<- | [<- | []]]]; in_S. }
  exists (DC3x DENT TABS SR BR), (DD3x DENT). split; [| split; [exact Hbapi | apply DC3_cm_ok]].
  exists S. split; [apply FS3_S_names | split].
  - (* the API specifications, up to funspec_sub *)
    destruct bodies_load3 as (_ & _ & _ & _ & _ & _ & _ & _ & sr & sl & sp).
    destruct bodies_oneshot3 as (_ & _ & _ & _ & su & sfr).
    destruct bodies_ddict3 as (_ & _ & _ & _ & _ & sgd).
    unfold api_sub, FS_api3.
    repeat apply Forall_cons; try apply Forall_nil;
      first
        [ match goal with |- exists s, _ = Some s /\ funspec_sub s (snd ?e) =>
            exists (snd e); split; [reflexivity | apply funspec_sub_refl] end
        | exists (snd (ZSTD_decompress_usingDDict_int_spec3 DENT TABS)); split; [reflexivity | exact (su DENT TABS SR BR HD HT)]
        | exists (snd ZSTD_freeDDict_int_spec); split; [reflexivity | exact (sfr DENT TABS SR BR HD HT)]
        | exists (snd ZSTD_getDictID_fromDDict_int_spec); split; [reflexivity | exact (sgd DENT TABS SR BR HD HT)]
        | exists (snd (ZSTD_DCtx_refDDict_int_spec3 DENT TABS)); split; [reflexivity | exact (sr DENT TABS SR BR HD HT)]
        | exists (snd (ZSTD_DCtx_loadDictionary_advanced_spec3 DENT TABS)); split; [reflexivity | exact (sl DENT TABS SR BR HD HT)]
        | exists (snd (ZSTD_DCtx_refPrefix_advanced_spec3 DENT TABS)); split; [reflexivity | exact (sp DENT TABS SR BR HD HT)]
        | exists (snd ZSTD_nextSrcSizeToDecompress_spec); split; [reflexivity | exact Hns]
        | exists (snd ZSTD_nextInputType_spec); split; [reflexivity | exact Hnit]
        | exists chi; split; [reflexivity | apply funspec_sub_iff; exact (proj2 (binaryintersection_sub _ _ _ Ei))] ].
  - (* the bodies *)
    assert (L: forall x, body_ok (FS3_G DENT TABS SR BR) x -> body_ok Gfin x).
    { intros x Hx. eapply body_ok_mono; [exact Hx | exact Hinc | exact Hnd]. }
    destruct bodies_ddict3 as (d1 & d2 & d3 & d4 & d5 & _).
    destruct bodies_blocks3 as (b1 & b2 & b3 & b4).
    destruct bodies_small3 as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & m9 & m10 & m11).
    destruct bodies_life3 as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9).
    destruct bodies_ctxops3 as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8).
    destruct bodies_load3 as (o1 & o2 & o3 & o4 & o5 & o6 & o7 & o8 & _ & _ & _).
    pose proof bodies_dfh3 as h1. pose proof bodies_select3 as s1.
    pose proof body_createDCtx_advancedP as v1. pose proof body_estimateDCtxSize3 as v2.
    pose proof body_decodingBufferSize_min3 as v3. pose proof body_estimateDStreamSize3 as v4.
    destruct bodies_oneshot3 as (n1 & n2 & n3 & n4 & _ & _).
    repeat match goal with H: FS3_body _ |- _ =>
      let e := fresh "e" in pose proof (L _ (H DENT TABS SR BR HD HT)) as e; cbv beta in e; clear H end.
    pose proof (body_ok_mono _ _ _ (proj1 Hf) HincF Hnd) as f1.
    pose proof (body_ok_mono _ _ _ (proj2 Hf) HincF Hnd) as f2.
    rewrite Forall_app in Hss. destruct Hss as [Hss1 Hss2].
    repeat (rewrite Forall_cons_iff in Hss1; destruct Hss1 as [?s Hss1]).
    repeat (rewrite Forall_cons_iff in Hss2; destruct Hss2 as [?s Hss2]).
    repeat match goal with H: body_ok (FS3_G DENT TABS SR BR ++ [(_ZSTD_DDictHashSet_getIndex, gi); _; _]) ?x |- _ =>
      let e := fresh "e" in pose proof (body_ok_mono _ _ _ H HincS Hnd) as e; clear H end.
    pose proof (fs3_body_ok_sub _ _ _ Hds Href Hnd) as t1.
    pose proof (fs3_body_ok_sub _ _ _ Hccs Href Hnd) as t2.
    pose proof (body_ok_inter _ _ _ _ (fs3_body_ok_sub _ _ _ Hc0 Href Hnd) (L _ Hcb)) as t3.
    fold chi in t3.
    apply Forall_forall. intros x Hx. unfold S, FS3_S in Hx.
    repeat (destruct Hx as [<- | Hx]; [ match goal with H: body_ok _ ?s |- body_ok _ ?s => exact H end | ]).
    contradiction.
Qed.
