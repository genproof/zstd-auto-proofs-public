(* FS3 bodies, small3: the small streaming helpers (port of v2 body_stream_small.v, specifications unchanged).
   (obligation FSOblig3.FS3_body: for ANY DENT/TABS of B, ANY SR, ANY BR). *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Local Open Scope logic.

(* the arithmetic of the unsigned comparisons of size_t values that are in range *)
Ltac nfin :=
  try change (Int.signed (Int.shl (Int.repr 1) (Int.repr 17))) with 131072 in *;
  unfold ZSTD_BLOCKSIZE_MAX in *; unfold Int64.ltu in *; rewrite ?Int64.unsigned_repr in * by rep_lia;
  repeat match goal with H: context [zlt ?a ?b] |- _ => destruct (zlt a b); try discriminate end;
  unfold vlong; do 2 f_equal; lia.

Section CM_body3_small_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma body_nextSrcSizeToDecompress : FS3_body (fun DENT TABS SR BR => ZSTD_nextSrcSizeToDecompress_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_nextSrcSizeToDecompress; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward.
Qed.

Lemma body_isSkipFrame : FS3_body (fun DENT TABS SR BR => ZSTD_isSkipFrame_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_isSkipFrame; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward.
  entailer!.
  unfold ds_skipFrame; destruct (Z.eqb_spec stage 7); [subst; reflexivity | ].
  rewrite Int.eq_false; [reflexivity | ]. intro Hc; apply repr_inj_signed in Hc; rep_lia.
Qed.

Lemma body_nextInputType : FS3_body (fun DENT TABS SR BR => ZSTD_nextInputType_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_nextInputType; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward_if (PROP (False) LOCAL () SEP ()); [ forward.. | ];
    [ .. | exfalso; rewrite !Int.unsigned_repr in * by rep_lia; lia].
Qed.

Lemma body_isOversizedTooLong : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_isOversizedTooLong_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_DCtx_isOversizedTooLong; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward.
  entailer!.
  unfold vlong; simpl. rewrite Int.signed_repr by rep_lia.
  unfold Int64.ltu; rewrite !Int64.unsigned_repr by rep_lia.
  unfold ZSTD_WORKSPACETOOLARGE_MAXDURATION; destruct (zlt ov 128), (Z.leb_spec 128 ov); try lia; reflexivity.
Qed.

Lemma body_isOverflow : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_isOverflow_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_DCtx_isOverflow; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward.
  forward.
  entailer!.
  unfold vlong; simpl. unfold Int64.ltu, Int64.add.
  rewrite !(Int64.unsigned_repr ins), !(Int64.unsigned_repr outs) by rep_lia.
  rewrite !Int64.unsigned_repr_eq. unfold is_overflow, ZSTD_WORKSPACETOOLARGE_FACTOR.
  change Int64.modulus with (2^64).
  destruct (zlt _ _), (Z.leb_spec ((nin + nout) * 3 mod 2 ^ 64) ((ins + outs) mod 2 ^ 64));
    try lia; reflexivity.
Qed.

Lemma body_updateOversizedDuration : FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_updateOversizedDuration_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_DCtx_updateOversizedDuration; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward_call (p, ins, outs, nin, nout).
  forward_if.
  - forward. forward. entailer!.
    destruct (is_overflow ins outs nin nout); [ | congruence]. unfold vlong.
    rewrite <- (Int64.repr_unsigned (Int64.repr (ov+1))), Int64.unsigned_repr_eq. apply derives_refl.
  - forward. entailer!.
    destruct (is_overflow ins outs nin nout); [ discriminate | apply derives_refl ].
Qed.

Lemma body_outBuffer_copy : FS3_body (fun DENT TABS SR BR => ZSTD_outBuffer_copy_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_outBuffer_copy; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  repeat forward.
  entailer!.
Qed.

Lemma body_nextSrcSizeWithInputSize :
  FS3_body (fun DENT TABS SR BR => ZSTD_nextSrcSizeToDecompressWithInputSize_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_nextSrcSizeToDecompressWithInputSize; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if orb (stage =? 3) (stage =? 4) then 1 else 0)));
                             temp _dctx p; temp _inputSize (Vlong (Int64.repr n)))
              SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p;
                   field_at Ews t_dctx (DOT _bType) bt p;
                   field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p)).
  - forward. entailer!.
  - forward. forward. entailer!.
    destruct (Z.eqb_spec stage 3); [lia|]; destruct (Z.eqb_spec stage 4); [subst; reflexivity|].
    rewrite Int.eq_false; [reflexivity|]; intro Hc; apply repr_inj_signed in Hc; rep_lia.
  - forward_if.
    + forward. forward. entailer!.
      unfold next_size, ds_decompressBlock, ds_decompressLastBlock.
      destruct (stage =? 3), (stage =? 4); try discriminate; reflexivity.
    + assert (Hs: ((stage =? 3) || (stage =? 4))%bool = true)
        by (destruct ((stage =? 3) || (stage =? 4))%bool; [reflexivity | exfalso; apply H3; reflexivity]).
      assert (Hst: stage = 3 \/ stage = 4)
        by (apply orb_true_iff in Hs; destruct Hs as [Hs|Hs]; apply Z.eqb_eq in Hs; auto).
      destruct (H2 Hst) as [b [-> Hb]].
      forward.
      forward_if.
      * forward. forward. entailer!.
        unfold next_size; rewrite (proj2 (Z.eqb_neq b 0) H4), andb_false_r; reflexivity.
      * forward.
        forward_if (PROP () LOCAL (temp _t'2 (vlong (Z.min n e)); temp _dctx p;
                                   temp _inputSize (Vlong (Int64.repr n)))
                    SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p;
                         field_at Ews t_dctx (DOT _bType) (Vint (Int.repr b)) p;
                         field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p)).
        -- forward. entailer!. unfold vlong; repeat f_equal; lia.
        -- forward. forward. entailer!. unfold vlong; repeat f_equal; lia.
        -- forward_if (PROP () LOCAL (temp _t'3 (vlong (Z.max 1 (Z.min n e))); temp _dctx p;
                                      temp _inputSize (Vlong (Int64.repr n)))
                        SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr stage)) p;
                             field_at Ews t_dctx (DOT _bType) (Vint (Int.repr b)) p;
                             field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr e)) p)).
           ++ forward. entailer!. rewrite ?Int64.unsigned_repr in * by rep_lia; unfold vlong; repeat f_equal; lia.
           ++ forward. forward_if.
              ** forward. forward. entailer!. rewrite ?Int64.unsigned_repr in * by rep_lia; unfold vlong; repeat f_equal; lia.
              ** forward. forward. forward. entailer!. rewrite ?Int64.unsigned_repr in * by rep_lia; unfold vlong; repeat f_equal; lia.
           ++ forward. entailer!.
              unfold next_size, ds_decompressBlock, ds_decompressLastBlock; rewrite Hs; reflexivity.
Qed.

Lemma body_decodingBufferSize_internal :
  FS3_body (fun DENT TABS SR BR => ZSTD_decodingBufferSize_internal_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_decodingBufferSize_internal; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (vlong (Z.min ws ZSTD_BLOCKSIZE_MAX));
     temp _windowSize (Vlong (Int64.repr ws)); temp _frameContentSize (Vlong (Int64.repr fcs));
     temp _blockSizeMax (Vlong (Int64.repr bsm))) SEP ()).
  - forward. entailer!; nfin.
  - forward. entailer!; nfin.
  - forward_if (PROP () LOCAL (temp _t'2 (vlong (Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm));
       temp _windowSize (Vlong (Int64.repr ws)); temp _frameContentSize (Vlong (Int64.repr fcs));
       temp _blockSizeMax (Vlong (Int64.repr bsm))) SEP ()).
    + forward_if (PROP () LOCAL (temp _t'3 (vlong (Z.min ws ZSTD_BLOCKSIZE_MAX));
         temp _windowSize (Vlong (Int64.repr ws)); temp _frameContentSize (Vlong (Int64.repr fcs));
         temp _blockSizeMax (Vlong (Int64.repr bsm))) SEP ()).
      * forward. entailer!; nfin.
      * forward. entailer!; nfin.
      * forward. entailer!; nfin.
    + forward. entailer!; nfin.
    + forward. forward.
      set (R := ws + Z.min (Z.min ws ZSTD_BLOCKSIZE_MAX) bsm * 2 + WILDCOPY_OVERLENGTH * 2).
      match goal with |- context [temp _neededRBSize (Vlong ?x)] => replace x with (Int64.repr R) end.
      2:{ unfold R, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX in *.
          change (Int.signed (Int.repr 2)) with 2.
          change (Int.signed (Int.mul (Int.repr 32) (Int.repr 2))) with 64. unfold Int64.add, Int64.mul.
          rewrite (Int64.unsigned_repr ws), (Int64.unsigned_repr 2), (Int64.unsigned_repr (Z.min _ _)),
            (Int64.unsigned_repr (_ * 2)), (Int64.unsigned_repr (ws + _)), (Int64.unsigned_repr 64) by rep_lia.
          f_equal; lia. }
      assert (HR: 0 <= R <= 2 ^ 42) by (unfold R, WILDCOPY_OVERLENGTH, ZSTD_BLOCKSIZE_MAX; lia).
      forward_if (PROP () LOCAL (temp _t'4 (vlong (Z.min fcs R))) SEP ()).
      * forward. entailer!; nfin.
      * forward. entailer!; nfin.
      * forward. forward.
        forward_loop (PROP () LOCAL (temp _minRBSize (vlong (Z.min fcs R)); temp _neededSize (vlong (Z.min fcs R))) SEP ())
          break: (PROP () LOCAL (temp _minRBSize (vlong (Z.min fcs R))) SEP ()).
        -- entailer!.
        -- forward_if (PROP () LOCAL (temp _minRBSize (vlong (Z.min fcs R))) SEP ()).
           ++ exfalso; congruence.
           ++ forward. entailer!.
           ++ forward. entailer!.
        -- forward.
Qed.

Lemma veqb_refl (v: val) : veqb v v = true.
Proof. unfold veqb; destruct (Val.eq v v); congruence. Qed.

Lemma veqb_vlong (a b: Z) :
  0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> veqb (vlong a) (vlong b) = (a =? b).
Proof.
  intros Ha Hb. unfold veqb, vlong. destruct (Val.eq _ _) as [E|E].
  - assert (E1: Int64.repr a = Int64.repr b) by congruence. apply (f_equal Int64.unsigned) in E1.
    rewrite !Int64.unsigned_repr in E1 by lia. subst. symmetry; apply Z.eqb_refl.
  - destruct (Z.eqb_spec a b); subst; congruence.
Qed.

(* comparing a pointer with itself needs only its weak validity *)
Lemma test_eq_self_weak (b: block) (i: ptrofs) :
  weak_valid_pointer (Vptr b i) |-- denote_tc_test_eq (Vptr b i) (Vptr b i).
Proof.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq, test_eq_ptrs, sameblock. simpl.
  destruct (peq b b); [|congruence]. simpl. apply andp_right; apply derives_refl.
  Opaque denote_tc_test_eq.
Qed.

(* comparing NULL with NULL is always defined (an empty output buffer passed as NULL) *)
Lemma test_eq_null_null (P: mpred) : P |-- denote_tc_test_eq nullval nullval.
Proof.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq, nullval. simpl.
  apply andp_right; apply prop_right; auto.
  Opaque denote_tc_test_eq.
Qed.

(* zstd's do { } while (0) blocks: a loop whose increment is break *)
Ltac eref := apply andp_left2, derives_refl.
Ltac skip_loop := match goal with |- semax _ ?P _ _ => forward_loop P break: P; [eref | | ] end.

Lemma body_checkOutBuffer : FS3_body (fun DENT TABS SR BR => ZSTD_checkOutBuffer_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_checkOutBuffer; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  rename H4 into Hobb.
  forward.
  match goal with |- context [temp _expect ?x] =>
    assert_PROP (x = field_address t_dctx (DOT _expectedOutBuffer) p) as Hexp end.
  { entailer!. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  rewrite Hexp; clear Hexp.
  rewrite (field_at_data_at _ _ (DOT _expectedOutBuffer)).
  forward.
  destruct stable.
  2:{ forward_if.
      - forward. entailer!.
      - exfalso; congruence. }
  forward_if.
  { exfalso; congruence. }
  forward.
  forward_if.
  { forward. entailer!. }
  destruct (H3 eq_refl H5) as [esz [epos [-> [Hesz Hepos]]]].
  change (nested_field_type t_dctx (DOT _expectedOutBuffer)) with t_outBuffer.
  set (q := field_address t_dctx (DOT _expectedOutBuffer) p).
  assert_PROP (is_pointer_or_null ob) as Hobp by (destruct Hobb as [-> | ->]; entailer!).
  forward.
  forward.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if andb (veqb ob ob) (veqb (vlong epos) (vlong opos)) then 1 else 0)));
                             temp _expect q; temp _output outp; temp _zds p)
              SEP (field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr 1)) p;
                   field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr stage)) p;
                   data_at Ews t_outBuffer (ob, (vlong esz, vlong epos)) q;
                   data_at sho t_outBuffer (ob, (vlong osz, vlong opos)) outp;
                   pws_pred W; data_at shob (tarray tuchar osz) oc obb)).
  { destruct Hobb as [<- | ->].
    2:{ apply test_eq_null_null. }
    unfold buf_ok in H2. destruct ob; try (destruct H15; contradiction).
    eapply derives_trans; [ | apply test_eq_self_weak].
    eapply derives_trans with (Q := (pws_pred W * data_at shob (tarray tuchar (Zlength oc)) oc (Vptr b i) * TT)%logic);
      [cancel | ].
    apply sepcon_weak_valid_pointer1.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply data_at_data_at_] | ].
    eapply derives_trans; [apply H2 | ]. apply andp_left1, derives_refl. }
  - forward. forward. forward. entailer!.
    rewrite veqb_refl, veqb_vlong by auto; simpl.
    destruct (zeq epos opos), (Z.eqb_spec epos opos); try lia; reflexivity.
  - exfalso; congruence.
  - forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (if andb (andb (veqb ob ob) (veqb (vlong epos) (vlong opos)))
                                                      (veqb (vlong esz) (vlong osz)) then 1 else 0)));
                               temp _expect q; temp _output outp; temp _zds p)
                SEP (field_at Ews t_dctx (DOT _outBufferMode) (Vint (Int.repr 1)) p;
                     field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr stage)) p;
                     data_at Ews t_outBuffer (ob, (vlong esz, vlong epos)) q;
                     data_at sho t_outBuffer (ob, (vlong osz, vlong opos)) outp;
                     pws_pred W; data_at shob (tarray tuchar osz) oc obb)).
    + forward. forward. forward. entailer!.
      rewrite veqb_refl, !veqb_vlong in * by auto; simpl in *.
      destruct (Z.eqb_spec epos opos); [ | simpl in H6'; contradiction].
      destruct (_ =? _) eqn:Eq; simpl; [apply Z.eqb_eq in Eq | apply Z.eqb_neq in Eq];
        destruct (zeq _ _); try contradiction; reflexivity.
    + forward. entailer!.
      rewrite veqb_refl, !veqb_vlong in * by auto; simpl in *.
      destruct (epos =? opos); simpl in *; [discriminate | reflexivity].
    + forward_if.
      * forward. entailer!.
        -- unfold check_out, zdss_init; rewrite (proj2 (Z.eqb_neq _ _) H5); simpl.
           repeat destruct (veqb _ _); simpl in *; try congruence; reflexivity.
        -- unfold q; rewrite (field_at_data_at _ _ (DOT _expectedOutBuffer)); apply derives_refl.
      * match goal with |- semax _ ?P _ _ => forward_loop P break: (PROP (False) LOCAL () SEP ()) end.
        -- entailer!.
        -- skip_loop; [forward; eref | ].
           skip_loop.
           { match goal with |- semax _ ?P _ _ => forward_if P end.
             - exfalso; auto.
             - forward. eref.
             - forward. eref. }
           skip_loop; [forward; eref | ].
           skip_loop; [forward; eref | ].
           forward.
           unfold q; rewrite (field_at_data_at _ _ (DOT _expectedOutBuffer)). entailer!.
           unfold check_out, zdss_init; rewrite (proj2 (Z.eqb_neq _ _) H5); simpl.
           repeat destruct (veqb _ _); simpl in *; try discriminate;
             unfold err_code, ZSTD_error_dstBuffer_wrong; f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity.
        -- Intros; contradiction.
Qed.

Lemma body_limitCopy : FS3_body (fun DENT TABS SR BR => ZSTD_limitCopy_spec).
Proof.
  intros DENT TABS SR BR HD HT; exists f_ZSTD_limitCopy; split; [reflexivity | split; [reflexivity | ]].
  start_function.
  match goal with Hx: byte_cells (sublist os _ cs) |- _ => rename Hx into Hdef end.
  forward_if (PROP () LOCAL (temp _t'1 (Vlong (Int64.repr (Z.min cap n))); temp _dst (offset_val od bd);
                             temp _src (offset_val os bs))
              SEP (data_at shd (tarray tuchar (Zlength cd)) cd bd; data_at shs (tarray tuchar (Zlength cs)) cs bs)).
  - forward. entailer!. nfin.
  - forward. entailer!. nfin.
  - forward.
    set (m := Z.min cap n).
    assert (Hm: 0 <= m <= Int64.max_unsigned) by (unfold m; lia).
    assert (Hdefm: byte_cells (sublist os (os + m) cs)) by exact Hdef.
    forward_if (PROP () LOCAL (temp _length (Vlong (Int64.repr m)))
                SEP (data_at shd (tarray tuchar (Zlength cd)) (copy_cells cd od cs os m) bd;
                     data_at shs (tarray tuchar (Zlength cs)) cs bs)).
    + rewrite !Int64.unsigned_repr in H7 by rep_lia.
      assert (Hdm: od + m <= Zlength cd /\ os + m <= Zlength cs) by (unfold m; lia).
      clearbody m.
      assert_PROP (field_compatible (tarray tuchar (Zlength cd)) [] bd /\
                   field_compatible (tarray tuchar (Zlength cs)) [] bs) as HF by entailer!.
      destruct HF as [Fd Fs].
      rewrite (split3_data_at_Tarray_tuchar shd (Zlength cd) od (od+m) cd bd) by lia.
      rewrite (split3_data_at_Tarray_tuchar shs (Zlength cs) os (os+m) cs bs) by lia.
      replace (od + m - od) with m by lia. replace (os + m - os) with m by lia.
      rewrite !field_address0_offset by auto with field_compatible. simpl nested_field_offset.
      rewrite !Z.add_0_l, !Z.mul_1_l. Intros.
      forward_call (shs, shd, offset_val os bs, offset_val od bd,
                    existT (fun t => reptype t) (tarray tuchar m) (sublist os (os+m) cs)).
      all: simpl projT1 in *; simpl projT2 in *.
      { split; [rewrite sizeof_tarray_tuchar by lia; lia |].
        apply memcpy_ok_bytes; [list_solve | exact Hdefm]. }
      entailer!.
      assert (Hlc: Zlength (copy_cells cd od cs os m) = Zlength cd) by (unfold copy_cells; list_solve).
      rewrite (split3_data_at_Tarray_tuchar shd (Zlength cd) od (od+m) (copy_cells cd od cs os m) bd) by lia.
      rewrite (split3_data_at_Tarray_tuchar shs (Zlength cs) os (os+m) cs bs) by lia.
      replace (od + m - od) with m by lia. replace (os + m - os) with m by lia.
      rewrite !field_address0_offset by auto with field_compatible. simpl nested_field_offset.
      rewrite !Z.add_0_l, !Z.mul_1_l.
      replace (sublist 0 od (copy_cells cd od cs os m)) with (sublist 0 od cd) by (unfold copy_cells; list_solve).
      replace (sublist od (od + m) (copy_cells cd od cs os m)) with (sublist os (os + m) cs)
        by (unfold copy_cells; list_solve).
      replace (sublist (od + m) (Zlength cd) (copy_cells cd od cs os m)) with (sublist (od + m) (Zlength cd) cd)
        by (unfold copy_cells; list_solve).
      cancel.
    + forward. entailer!.
      rewrite !Int64.unsigned_repr in H7 by rep_lia. assert (Hm0: m = 0) by lia.
      replace (copy_cells cd od cs os m) with cd; [apply derives_refl | ].
      unfold copy_cells; rewrite Hm0. list_solve.
    + forward.
Qed.

Lemma bodies_small3 :
  FS3_body (fun DENT TABS SR BR => ZSTD_limitCopy_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_nextSrcSizeToDecompress_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_nextSrcSizeToDecompressWithInputSize_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_nextInputType_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_isSkipFrame_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_decodingBufferSize_internal_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_isOverflow_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_updateOversizedDuration_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_DCtx_isOversizedTooLong_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_outBuffer_copy_spec) /\
  FS3_body (fun DENT TABS SR BR => ZSTD_checkOutBuffer_spec).
Proof.
  exact (conj body_limitCopy (conj body_nextSrcSizeToDecompress (conj body_nextSrcSizeWithInputSize
        (conj body_nextInputType (conj body_isSkipFrame (conj body_decodingBufferSize_internal
        (conj body_isOverflow (conj body_updateOversizedDuration (conj body_isOversizedTooLong
        (conj body_outBuffer_copy body_checkOutBuffer)))))))))).
Qed.

End CM_body3_small_1.
