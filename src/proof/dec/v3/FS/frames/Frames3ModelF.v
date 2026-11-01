(* FS3 one-shot frames: ZSTD_decompressFrame's bytes are ZSTD_findFrameCompressedSize's (ParamsH.frame_compressed_size_m):
   the header, the blocks the C walks (Frame.blocks_size), the checksum.  Plain Coq. *)
Require Export Zstd.proof.dec.v3.FS.frames.Frames3ModelX Zstd.proof.dec.v3.FS.frames.Frames3Series.
Local Open Scope Z_scope.

Section CM_Frames3ModelF_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma fr_fcs3: forall md sel dm s hs h j nb f,
  fr_hdr3 md sel dm s hs h ->
  blocks_size f (fr_rest s hs) = Some (j, nb) ->
  (md_magicless md = true \/ is_skippable_magic (le_field s 0 4) = false) ->
  (fh_checksumFlag h = 1 -> hs + j + 4 <= Zlength s) ->
  frame_compressed_size_m (md_magicless md) s = Some (hs + j + (if fh_checksumFlag h =? 1 then 4 else 0)).
Proof.
  intros md sel dm s hs h j nb f (Hb & Hl & Ehs & Hh & h0 & Hg & Eh & Hd & Hdw) HB Hns Hck.
  subst hs h.
  assert (Hst: starting_len (md_magicless md) <= Zlength s)
    by (destruct (md_magicless md); cbn [mg_sh starting_len] in *;
        unfold ZSTD_FRAMEHEADERSIZE_MIN, ZSTD_FRAMEHEADERSIZE_PREFIX, ZSTD_blockHeaderSize in *; lia).
  pose proof (hs3_range (md_magicless md) s Hb Hst) as Hr.
  assert (Hm: md_magicless md = false -> le_field s 0 4 = ZSTD_MAGICNUMBER).
  { intros E. destruct (Z.eqb_spec (le_field s 0 4) ZSTD_MAGICNUMBER) as [|N]; auto. exfalso.
    destruct Hns as [Hx | Hx]; [congruence|].
    rewrite E in Hg, Hr. cbn [get_frame_header_m negb mg_sh] in Hg, Hr.
    rewrite sublist_firstn in Hg.
    rewrite gfh_not_magic in Hg; [discriminate | | |].
    - rewrite Zlength_firstn. unfold ZSTD_FRAMEHEADERSIZE_PREFIX in *.
      rewrite E in Hh. unfold ZSTD_blockHeaderSize in *. lia.
    - rewrite frm_le_field_firstn by lia. exact N.
    - rewrite frm_le_field_firstn by lia. exact Hx. }
  rewrite f3m_prefix in Hg by (first [assumption | unfold ZSTD_blockHeaderSize in Hh; lia]).
  destruct (f3m_dec_ok md dm s h0 Hdw Hb Hl Hm Hh Hg) as [Hhs _].
  unfold fr_rest in HB. rewrite frm_sub_end in HB.
  apply bs_fuel in HB; [| apply frm_Forall_skipn; exact Hb].
  assert (Hlen: length (skipn (Z.to_nat (header_size_m (md_magicless md) s)) s) =
                length (skipn (Z.to_nat (fh_headerSize h0)) s)) by (rewrite Hhs; reflexivity).
  cbn [fh_cap fh_checksumFlag] in Hck |- *.
  destruct (md_magicless md) eqn:Emg.
  - unfold frame_compressed_size_m. cbn [negb]. rewrite Hg, Hhs, HB.
    destruct (Z.eqb_spec (fh_checksumFlag h0) 1) as [Ec|Ec].
    + specialize (Hck Ec). destruct (Z.ltb_spec (Zlength s - (header_size_m true s + j)) 4); [lia|].
      all: try reflexivity; try (f_equal; lia).
    + try reflexivity; try (f_equal; lia).
  - unfold frame_compressed_size_m. cbn [negb]. unfold frame_compressed_size.
    destruct Hns as [Hx | Hx]; [discriminate|]. rewrite Hx, andb_false_r.
    cbn [get_frame_header_m negb] in Hg. rewrite Hg, Hhs, HB.
    destruct (Z.eqb_spec (fh_checksumFlag h0) 1) as [Ec|Ec].
    + specialize (Hck Ec). destruct (Z.ltb_spec (Zlength s - (header_size_m false s + j)) 4); [lia|].
      all: try reflexivity; try (f_equal; lia).
    + try reflexivity; try (f_equal; lia).
Qed.

End CM_Frames3ModelF_1.
