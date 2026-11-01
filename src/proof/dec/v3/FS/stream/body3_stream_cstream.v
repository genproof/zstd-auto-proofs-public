(* FS3 streaming: the body of ZSTD_decompressContinueStream (template v2 body_stream_cstream.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Specs.
Local Open Scope logic.

Section CM_body3_stream_cstream_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame stage of a frame in progress: ds_skipFrame exactly for a skippable frame *)
Lemma ccs_stage fs tabs fp l dd :
  c_frame fs tabs fp l dd -> fp_complete fp = false ->
  exists st, fs_stage fs = Vint (Int.repr st) /\ 0 <= st <= 7 /\ (st =? ds_skipFrame) = is_skip fp.
Proof.
  unfold c_frame; intros (_ & _ & _ & _ & _ & HF) Hc; destruct fp as [ | | hdr got | hdr z]; try contradiction.
  - simpl in Hc |- *. destruct HF as (_ & _ & _ & _ & _ & HF). rewrite Hc in HF. destruct HF as [-> _].
    exists ds_skipFrame; unfold ds_skipFrame; split; [reflexivity | split; [lia | reflexivity]].
  - simpl in Hc |- *. destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
    unfold phase_fields in HP. destruct (zp_ph z); try discriminate.
    + destruct HP as [-> _]. exists ds_decodeBlockHeader; unfold ds_decodeBlockHeader; repeat split; lia.
    + destruct HP as (c & _ & -> & _). eexists; split; [reflexivity | ].
      destruct (bp_last _ =? 1); unfold ds_decompressLastBlock, ds_decompressBlock; (split; [lia | reflexivity]).
    + destruct HP as [-> _]. exists ds_checkChecksum; unfold ds_checkChecksum; repeat split; lia.
Qed.

Definition ff_rest (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma ff_split p fs :
  frame_fields p fs = field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * ff_rest p fs.
Proof. unfold frame_fields, ff_rest. apply pred_ext; cancel. Qed.

Lemma ccs_repr_eqm x y : x mod 2^64 = y mod 2^64 -> Int64.repr x = Int64.repr y.
Proof.
  intros E. rewrite <- (Int64.repr_unsigned (Int64.repr x)), <- (Int64.repr_unsigned (Int64.repr y)).
  rewrite !Int64.unsigned_repr_eq. change Int64.modulus with (2^64). congruence.
Qed.

(* oend - op, both in the caller's buffer *)
Lemma ccs_sub_pp b ofs a c :
  force_val (sem_sub_pp tschar (Vptr b (Ptrofs.add ofs (Ptrofs.repr a))) (Vptr b (Ptrofs.add ofs (Ptrofs.repr c))))
  = Vlong (Int64.repr (a - c)).
Proof.
  unfold sem_sub_pp. simpl. rewrite if_true by auto. simpl.
  rewrite (Ptrofs.add_commut ofs (Ptrofs.repr a)), (Ptrofs.add_commut ofs (Ptrofs.repr c)).
  rewrite Ptrofs.sub_shifted. change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.divs_one by reflexivity.
  unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64. apply ccs_repr_eqm.
  unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr_eq. change Ptrofs.modulus with (2^64).
  rewrite Zmod_mod. rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma body3_stream_cstream : stream_body3 (fun DENT TABS BR => ZSTD_decompressContinueStream_spec3 DENT TABS).
Proof.
  intros DENT TABS BR HD HT; exists f_ZSTD_decompressContinueStream; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  destruct (ccs_stage _ _ _ _ _ (proj1 H) (proj1 (proj2 H))) as (st & Hst & Hst7 & Hsk).
  rewrite ff_split, Hst. Intros.
  forward_call (p, st).
  rewrite Hsk, <- Hst.
  gather_SEP (field_at _ _ (DOT _stage) _ _) (ff_rest _ _). rewrite <- ff_split.
  forward.
  assert_PROP (isptr (oa_base o)) as Hpb by entailer!.
  destruct stable.
  - simpl in H0; destruct H0 as (Hcap & -> & ->).
    apply semax_if_seq. forward_if. { discriminate. }
    forward_if (temp _t'6 (Vlong (Int64.repr (oa_cap o)))).
    { forward. destruct (is_skip fp); [ | contradiction]. rewrite Hcap. entailer!. }
    { forward. destruct (is_skip fp) eqn:Es; [ exfalso; match goal with Hx: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hx) end | ].
      destruct (oa_base o) as [| | | | | b ofs] eqn:Eb; try contradiction.
      forward.
      - entailer!. unfold sameblock. destruct (peq b b); [reflexivity | congruence].
      - entailer!. rewrite ccs_sub_pp, Hcap. reflexivity. }
    forward. forward.
    forward_call (gv, p, fs, ts, fp, l, dd, W, o, src, i, n, f).
    Intros vret; destruct vret as [[[r oc'] fs'] tabs']; simpl fst in *; simpl snd in *.
    forward.
    assert (Hr: 0 <= r <= Int64.max_unsigned) by (match goal with Hx: cont_res _ _ _ _ _ _ _ _ _ |- _ => destruct Hx; auto end).
    destruct (is_error_code r) eqn:Er.
    2: { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
         entailer!. forward. forward_call r. rewrite Er.
         forward_if.
         { contradiction. }
         forward. entailer!.
         forward. forward. forward. forward. forward.
         Exists r oc' fs' tabs'. rewrite Er. simpl. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (PROP (False) LOCAL () SEP ()) end.
    entailer!. forward. forward_call r. rewrite Er.
    forward_if; [ | discriminate].
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!.
    { forward_if True. { contradiction. } { forward. entailer!. } forward. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    forward. Exists r oc' fs' tabs'. rewrite Er. entailer!.
  - simpl in H0; destruct H0 as (Hcap & Hb & HN & Hd). subst outBuff outSize ostart.
    apply semax_if_seq. forward_if. 2: { contradiction. }
    forward_if (temp _t'2 (Vlong (Int64.repr (oa_cap o)))).
    { forward. destruct (is_skip fp); [ | contradiction]. rewrite Hcap. entailer!. }
    { forward. forward. forward.
      destruct (is_skip fp) eqn:Es; [ exfalso; match goal with Hx: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hx) end | ].
      entailer!. }
    forward. forward. forward.
    forward_call (gv, p, fs, ts, fp, l, dd, W, o, src, i, n, f).
    { entailer!. destruct (oa_base o); try contradiction.
      simpl. unfold vlong. normalize. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
      unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia. reflexivity. }
    Intros vret; destruct vret as [[[r oc'] fs'] tabs']; simpl fst in *; simpl snd in *.
    forward.
    assert (Hr: 0 <= r <= Int64.max_unsigned) by (match goal with Hx: cont_res _ _ _ _ _ _ _ _ _ |- _ => destruct Hx; auto end).
    destruct (is_error_code r) eqn:Er.
    2: { match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
         entailer!. forward. forward_call r. rewrite Er.
         forward_if.
         { contradiction. }
         forward. entailer!.
         forward_if (temp _t'5 (Vint (Int.repr (if andb (r =? 0) (negb (is_skip fp)) then 1 else 0)))).
         { forward. entailer!.
           match goal with Hx: Int64.repr r = _ |- _ =>
             apply (f_equal Int64.unsigned) in Hx; rewrite Int64.unsigned_repr in Hx by lia; subst r end.
           destruct (is_skip fp); reflexivity. }
         { forward. entailer!.
           assert (Hr0: r <> 0) by (intros ->; match goal with Hx: Int64.repr 0 <> _ |- _ => apply Hx; reflexivity end).
           rewrite (proj2 (Z.eqb_neq r 0) Hr0). reflexivity. }
         destruct (andb (r =? 0) (negb (is_skip fp))) eqn:Ea.
         - apply semax_if_seq. forward_if.
           { forward. forward. Exists r oc' fs' tabs'. rewrite Er, Ea. entailer!. }
           match goal with Hx: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero Hx) end.
         - apply semax_if_seq. forward_if.
           { match goal with Hx: Int.repr 0 <> Int.zero |- _ => exfalso; apply Hx; reflexivity end. }
           forward. forward. forward. forward. Exists r oc' fs' tabs'. rewrite Er, Ea. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (PROP (False) LOCAL () SEP ()) end.
    entailer!. forward. forward_call r. rewrite Er.
    forward_if; [ | discriminate].
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!.
    { forward_if True. { contradiction. } { forward. entailer!. } forward. entailer!. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
    entailer!. forward. entailer!.
    forward. Exists r oc' fs' tabs'. rewrite Er. entailer!.
Qed.

End CM_body3_stream_cstream_1.
