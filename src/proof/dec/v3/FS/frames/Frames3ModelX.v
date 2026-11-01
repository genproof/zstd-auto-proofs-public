(* FS3 one-shot frames: the frame model facts of Frames3Model.v for ANY selection (the dictID check of the model
   follows from a decoded or checksum-rejected frame), for ZSTD_decompressFrame_spec3's claims under the
   selection. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3Model.
Local Open Scope Z_scope.

Section CM_Frames3ModelX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* a frame the model decodes passed its dictID check: fr_hdr3 without the selection *)
Lemma fr_hdr3_relax: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s <> FUnk -> fr_hdr3 md false dm s hs h.
Proof.
  intros md sel dm s hs h (Hb & Hl & Ehs & Hh & h0 & Hg & Eh & Hd & Hdw) Hu. subst hs.
  assert (Hm := f3m_magic_need md dm no_wlim s Hu).
  assert (Hg' := Hg). rewrite f3m_prefix in Hg' by f3m_side.
  destruct (f3m_dec_ok md dm s h0 Hdw Hb Hl Hm Hh Hg') as [_ E].
  refine (conj Hb (conj Hl (conj eq_refl (conj Hh _)))). exists h0. split; [exact Hg|]. split; [exact Eh|].
  split; [|exact Hdw]. intros _. unfold f3m_tail in E.
  destruct (andb (negb (fh_dictID h0 =? 0)) (negb (fh_dictID h0 =? dm_id dm))) eqn:D.
  - exfalso. exact (Hu E).
  - apply andb_false_iff in D. destruct D as [D|D]; apply negb_false_iff, Z.eqb_eq in D; auto.
Qed.

Lemma fr_frame_ok3_any: forall md sel dm s hs h c sz,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s = FOk c sz ->
  exists k, fr_DB dm h s hs = Some (c, k) /\
    (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength c = fh_contentSize h) /\
    (if fh_checksumFlag h =? 1
     then hs + k + 4 <= Zlength s /\ (md_ignore md = false -> le_field s (hs + k) 4 = xxh64 c 0 mod 2 ^ 32) /\
          sz = hs + k + 4
     else sz = hs + k).
Proof.
  intros md sel dm s hs h c sz H Hdf. apply fr_frame_ok3; auto.
  eapply fr_hdr3_relax; [exact H | rewrite Hdf; discriminate].
Qed.

Lemma fr_frame_ck3_any: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s = FDetCk ->
  exists c k, fr_DB dm h s hs = Some (c, k) /\ fh_checksumFlag h = 1 /\ md_ignore md = false /\
    (fh_contentSize h = ZSTD_CONTENTSIZE_UNKNOWN \/ Zlength c = fh_contentSize h) /\
    hs + k + 4 <= Zlength s /\ le_field s (hs + k) 4 <> xxh64 c 0 mod 2 ^ 32.
Proof.
  intros md sel dm s hs h H Hdf. apply fr_frame_ck3; auto.
  eapply fr_hdr3_relax; [exact H | rewrite Hdf; discriminate].
Qed.

Lemma fr_frame_hdr3_any: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s <> FDetHdr.
Proof.
  intros md sel dm s hs h (Hb & Hl & Ehs & Hh & h0 & Hg & Eh & Hd & Hdw) Hdf. subst hs.
  assert (Hm := f3m_magic_need md dm no_wlim s ltac:(rewrite Hdf; discriminate)).
  rewrite f3m_prefix in Hg by f3m_side.
  destruct (f3m_dec_ok md dm s h0 Hdw Hb Hl Hm Hh Hg) as [_ E]. rewrite Hdf in E. unfold f3m_tail in E.
  repeat match type of E with context [match ?c with _ => _ end] => destruct c end; discriminate.
Qed.

(* ZSTD_decodeFrameHeader failed, with or without the selection: the model does not decode the frame (the C
   compares the frame's Dictionary_ID with did' = dm_id dm, or with itself after a selection) *)
Lemma hdr_err_model3_any: forall md sel dm s d l tbl fs r fs' d',
  md_dwin md = false -> bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize <= Zlength s ->
  header_size_m (md_magicless md) s + ZSTD_blockHeaderSize <= Zlength s ->
  dfh_post3 md sel d l tbl fs (dm_id dm) 0 (sublist 0 (header_size_m (md_magicless md) s) s) r fs' d' ->
  is_error_code r = true ->
  forall c sz, decode_frame_m md dm no_wlim s = FOk c sz -> False.
Proof.
  intros md sel dm s d l tbl fs r fs' d' Hdw Hb Hl Hh Hd Her c sz Hdf.
  assert (Hm := f3m_magic_need md dm no_wlim s ltac:(rewrite Hdf; discriminate)).
  unfold dfh_post3 in Hd. rewrite f3m_prefix in Hd by f3m_side.
  destruct (get_frame_header_m (md_magicless md) s) as [|k|h] eqn:G.
  1,2: eapply (proj1 (f3m_dec_noh md dm no_wlim s ltac:(intros h0; rewrite G; discriminate))); eauto.
  cbv zeta in Hd. destruct Hd as [_ Hd].
  destruct (f3m_dec_ok md dm s h Hdw Hb Hl Hm Hh G) as [_ E]. rewrite Hdf in E. unfold f3m_tail in E.
  destruct (orb (fh_dictID h =? 0) _) eqn:O.
  - destruct Hd as [-> _]. vm_compute in Her. discriminate.
  - apply orb_false_iff in O. destruct O as [O1 O2].
    destruct (eq_dec (if sel then sel_r d l tbl (fh_dictID h) else nullval) nullval) as [N|N].
    + rewrite O1 in E. rewrite O2 in E. discriminate.
    + rewrite Z.eqb_refl in O2. discriminate.
Qed.

End CM_Frames3ModelX_1.
