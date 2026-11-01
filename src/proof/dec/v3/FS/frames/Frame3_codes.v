(* FS3 one-shot frames: the model facts behind the error codes of ZSTD_decompressFrame (Frames3Spec.frame_codes3), for
   the segment proofs Frame3_*.v.  Plain Coq.

   - an exit where the model's blocks fail (fr_DB) or where the model does not decode the frame at all: no claim
     (fr_codes_noDB, fr_codes_none);
   - a block error at block j: on a frame with only Raw/RLE blocks the failing block is Raw/RLE, which reports
     dstSize_tooSmall (fr_rr_rest, fr_OT_rr); a frame refused by its checksum has its content decoded by the model
     (fr_out_db), which the failing block would overflow: no room for it (fr_codes_blk);
   - ZSTD_decodeFrameHeader failed: the model does not refuse the frame by its checksum (hdr_err_model3_ck). *)
Require Import Zstd.proof.dec.v3.FS.frames.Frames3Defs Zstd.proof.dec.v3.FS.frames.Frames3Model.
Local Open Scope Z_scope.

Section CM_Frame3_codes_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* fr_hdr3's header is the one frame_out_m and frame_rr_m parse; the blocks start at hs *)
Lemma fr_hdr3_gfh: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s <> FUnk ->
  exists h0, get_frame_header_m (md_magicless md) s = FH_ok h0 /\ h = fh_cap md h0 /\ fh_headerSize h0 = hs /\
    md_dwin md = false.
Proof.
  intros md sel dm s hs h (Hb & Hl & Ehs & Hh & h0 & Hg & Eh & _ & Hdw) Hu. subst hs.
  assert (Hm := f3m_magic_need md dm no_wlim s Hu).
  rewrite f3m_prefix in Hg by f3m_side.
  destruct (f3m_dec_ok md dm s h0 Hdw Hb Hl Hm Hh Hg) as [Ehs _].
  exists h0. auto.
Qed.

(* the content frame_out_m is what the model's blocks decode (fr_DB) *)
Lemma fr_out_db: forall md sel dm s hs h c,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s <> FUnk -> frame_out_m md dm s = Some c ->
  exists k, fr_DB dm h s hs = Some (c, k).
Proof.
  intros md sel dm s hs h c Hh Hu Ho.
  destruct (fr_hdr3_gfh md sel dm s hs h Hh Hu) as (h0 & Hg & -> & Ehs & Hdw).
  unfold frame_out_m in Ho. rewrite Hg, Hdw, Ehs in Ho.
  unfold fr_DB, fr_rest. rewrite frm_sub_end. cbn [fh_cap fh_blockSizeMax fh_windowSize].
  destruct (decode_blocks _ _ _ _ _ _ _) as [[o k]|]; [|discriminate].
  injection Ho as ->. exists k. reflexivity.
Qed.

(* a frame with only Raw/RLE blocks: the C's blocks from the header on are Raw/RLE *)
Lemma fr_rr_rest: forall md sel dm s hs h,
  fr_hdr3 md sel dm s hs h -> decode_frame_m md dm no_wlim s <> FUnk -> frame_rr_m md s ->
  blocks_rr (fr_rest s hs).
Proof.
  intros md sel dm s hs h Hh Hu (h1 & Hg1 & Hr).
  destruct (fr_hdr3_gfh md sel dm s hs h Hh Hu) as (h0 & Hg & _ & Ehs & _).
  rewrite Hg in Hg1. injection Hg1 as <-. rewrite Ehs in Hr.
  unfold fr_rest. rewrite frm_sub_end. exact Hr.
Qed.

(* the model decodes neither an Ok frame nor a checksum-refused one: frame_codes3 claims nothing *)
Lemma fr_codes_none: forall md dm s cap r,
  (forall c sz, decode_frame_m md dm no_wlim s = FOk c sz -> False) ->
  decode_frame_m md dm no_wlim s <> FDetCk ->
  frame_codes3 md dm s cap r.
Proof.
  intros md dm s cap r Hok Hck. split.
  - intros c sz Hd. exfalso. exact (Hok c sz Hd).
  - intros Hd. exfalso. exact (Hck Hd).
Qed.

(* the model's blocks fail: no claim *)
Lemma fr_codes_noDB: forall md sel dm s hs h cap r,
  fr_hdr3 md sel dm s hs h -> (forall o k, fr_DB dm h s hs <> Some (o, k)) ->
  frame_codes3 md dm s cap r.
Proof.
  intros md sel dm s hs h cap r Hh Hn. apply fr_codes_none.
  - intros c sz Hd. destruct (fr_frame_ok3_any _ _ _ _ _ _ _ _ Hh Hd) as (k & Hk & _). exact (Hn _ _ Hk).
  - intros Hd. destruct (fr_frame_ck3_any _ _ _ _ _ _ Hh Hd) as (c & k & Hk & _). exact (Hn _ _ Hk).
Qed.

(* a block error at block j (the step of the model, if any, overflows the capacity; a Raw/RLE block reports
   dstSize_tooSmall) *)
Lemma fr_codes_blk: forall md sel dm s hs h j out st c cap r,
  fr_hdr3 md sel dm s hs h -> fr_OT dm h s hs j out st -> 0 <= j -> hs + j <= Zlength s ->
  cblock_size (fr_t s hs j) = Some c -> 0 <= c -> c <= Zlength (fr_t s hs j) - ZSTD_blockHeaderSize ->
  (forall st' out',
     blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h) = Some (st', out') ->
     cap < Zlength out') ->
  (bp_type (block_props_of (fr_t s hs j)) <> 2 -> r = err_code ZSTD_error_dstSize_tooSmall) ->
  frame_codes3 md dm s cap r.
Proof.
  intros md sel dm s hs h j out st c cap r Hh HOT Hj Hhj Hc Hc0 Hct Hov Hrr. split.
  - intros c0 sz Hd Hfr _. apply Hrr.
    assert (Hr := fr_rr_rest md sel dm s hs h Hh ltac:(rewrite Hd; discriminate) Hfr).
    pose proof (fr_OT_rr dm h s hs j out st HOT Hr). lia.
  - intros Hd c0 Ho Hle. exfalso.
    destruct (fr_out_db md sel dm s hs h c0 Hh ltac:(rewrite Hd; discriminate) Ho) as (k & Hk).
    destruct (blk_res st (dm_content dm) out (fr_t s hs j) c (fh_blockSizeMax h) (fh_windowSize h))
      as [[st' out'] | ] eqn:E.
    + pose proof (Hov _ _ eq_refl).
      pose proof (fr_OT_grow dm h s hs j out st c st' out' HOT Hj Hhj Hc Hc0 Hct E c0 k Hk). lia.
    + eapply (fr_OT_none dm h s hs j out st HOT Hj Hhj); [ | exact Hk].
      right; right. exists c; auto.
Qed.

(* ZSTD_decodeFrameHeader failed, with or without the selection: the model does not refuse the frame by its
   checksum (as hdr_err_model3_any for a decoded frame) *)
Lemma hdr_err_model3_ck: forall md sel dm s d l tbl fs r fs' d',
  md_dwin md = false -> bytes_ok s ->
  ZSTD_FRAMEHEADERSIZE_MIN - mg_sh (md_magicless md) + ZSTD_blockHeaderSize <= Zlength s ->
  header_size_m (md_magicless md) s + ZSTD_blockHeaderSize <= Zlength s ->
  dfh_post3 md sel d l tbl fs (dm_id dm) 0 (sublist 0 (header_size_m (md_magicless md) s) s) r fs' d' ->
  is_error_code r = true ->
  decode_frame_m md dm no_wlim s <> FDetCk.
Proof.
  intros md sel dm s d l tbl fs r fs' d' Hdw Hb Hl Hh Hd Her Hdf.
  assert (Hm := f3m_magic_need md dm no_wlim s ltac:(rewrite Hdf; discriminate)).
  unfold dfh_post3 in Hd. rewrite f3m_prefix in Hd by f3m_side.
  destruct (get_frame_header_m (md_magicless md) s) as [|k|h] eqn:G.
  1,2: eapply (proj2 (f3m_dec_noh md dm no_wlim s ltac:(intros h0; rewrite G; discriminate))); eauto.
  cbv zeta in Hd. destruct Hd as [_ Hd].
  destruct (f3m_dec_ok md dm s h Hdw Hb Hl Hm Hh G) as [_ E]. rewrite Hdf in E. unfold f3m_tail in E.
  destruct (orb (fh_dictID h =? 0) _) eqn:O.
  - destruct Hd as [-> _]. vm_compute in Her. discriminate.
  - apply orb_false_iff in O. destruct O as [O1 O2].
    destruct (eq_dec (if sel then sel_r d l tbl (fh_dictID h) else nullval) nullval) as [N|N].
    + rewrite O1 in E. rewrite O2 in E. discriminate.
    + rewrite Z.eqb_refl in O2. discriminate.
Qed.

(* the error codes as constants of the C (RETURN_ERROR's (size_t)-code) *)
Lemma err_code_dst: Int64.unsigned (Int64.repr (-70)) = err_code ZSTD_error_dstSize_tooSmall.
Proof. reflexivity. Qed.

Lemma err_code_ck: Int64.unsigned (Int64.repr (-22)) = err_code ZSTD_error_checksum_wrong.
Proof. reflexivity. Qed.

End CM_Frame3_codes_1.
