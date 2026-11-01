(* Bodies of group util: pointer helpers, error codes, small copies, ZSTD_DCtx_get_bmi2. *)
Require Import Zstd.proof.zstd.Gprog.

Lemma body_ZSTD_wrappedPtrAdd : semax_body Vprog Gprog f_ZSTD_wrappedPtrAdd ZSTD_wrappedPtrAdd_spec.
Proof. start_function. forward. Qed.

Lemma body_ZSTD_wrappedPtrSub : semax_body Vprog Gprog f_ZSTD_wrappedPtrSub ZSTD_wrappedPtrSub_spec.
Proof.
  start_function. forward.
  destruct p; try contradiction. entailer!. simpl. f_equal.
  rewrite Ptrofs.sub_add_opp. f_equal. normalize.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Ptrofs.neg_repr. apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_neg.
  rewrite Int64.unsigned_repr_eq. apply Ptrofs.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma body_ZSTD_maybeNullPtrAdd : semax_body Vprog Gprog f_ZSTD_maybeNullPtrAdd ZSTD_maybeNullPtrAdd_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (if 0 <? a then offset_val a p else p)) SEP ()).
  - rewrite !Int64.signed_repr in H2 by rep_lia. assert (isptr p) by auto.
    forward. entailer!. rewrite (proj2 (Z.ltb_lt 0 a)) by lia.
    destruct p; try contradiction. reflexivity.
  - rewrite !Int64.signed_repr in H2 by rep_lia. forward. entailer!.
    replace (0 <? a) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct p; try contradiction; auto.
  - forward.
Qed.

Lemma body_ERR_isError : semax_body Vprog Gprog f_ERR_isError ERR_isError_spec.
Proof.
  start_function. forward.
  entailer!. unfold Int64.ltu, is_error_code. rewrite (Int64.unsigned_repr c) by lia.
  change (Int64.unsigned (Int64.repr (-(120)))) with (2^64 - 120).
  destruct (zlt (2^64-120) c), (2^64-120 <? c) eqn:E; try reflexivity;
    [apply Z.ltb_ge in E | apply Z.ltb_lt in E]; lia.
Qed.

Lemma body_ERR_getErrorCode : semax_body Vprog Gprog f_ERR_getErrorCode ERR_getErrorCode_spec.
Proof.
  start_function. forward_call c.
  destruct (is_error_code c) eqn:E; forward_if.
  - discriminate.
  - forward. entailer!. unfold error_of; rewrite E. rewrite Int64.Z_mod_modulus_eq. do 2 f_equal.
    unfold is_error_code in E; apply Z.ltb_lt in E. change Int64.modulus with (2^64).
    change Int64.max_unsigned with (2^64-1) in H. symmetry. apply Z.mod_unique with (-1); lia.
  - forward. entailer!. unfold error_of; rewrite E. reflexivity.
  - contradiction H0. reflexivity.
Qed.

Lemma body_FSE_isError : semax_body Vprog Gprog f_FSE_isError FSE_isError_spec.
Proof. start_function. forward_call c. forward. Qed.

Lemma body_ZSTD_isError : semax_body Vprog Gprog f_ZSTD_isError ZSTD_isError_spec.
Proof. start_function. forward_call c. forward. Qed.

Lemma body_ZSTD_getErrorCode : semax_body Vprog Gprog f_ZSTD_getErrorCode ZSTD_getErrorCode_spec.
Proof. start_function. forward_call c. forward. Qed.

Lemma body_ZSTD_DCtx_get_bmi2 : semax_body Vprog Gprog f_ZSTD_DCtx_get_bmi2 ZSTD_DCtx_get_bmi2_spec.
Proof. start_function. forward. Qed.

(* The k bytes at offset i of a byte array, as a separate piece between the two others. *)
Ltac split_piece sh n i k c p :=
  rewrite (split3_data_at_Tarray_tuchar sh n i (i + k) c p) by lia;
  replace (i + k - i) with k by lia;
  rewrite !field_address0_offset by auto with field_compatible;
  simpl nested_field_offset; rewrite !Z.mul_1_l, !Z.add_0_l.

Ltac copy_start k :=
  match goal with H: copy_pre _ _ _ _ _ _ _ |- _ => destruct H as (Hs & Hd & ? & ? & ? & ? & Hdef) end;
  match goal with |- context [data_at ?shs (tarray tuchar (Zlength ?cs)) ?cs ?ps] =>
  match goal with |- context [data_at ?shd (tarray tuchar (Zlength ?cd)) ?cd ?pd] =>
  match goal with |- context [temp _dst (offset_val ?id pd)] =>
  match goal with |- context [temp _src (offset_val ?is ps)] =>
    assert_PROP (field_compatible (tarray tuchar (Zlength cs)) [] ps) by entailer!;
    assert_PROP (field_compatible (tarray tuchar (Zlength cd)) [] pd) by entailer!;
    unfold tarray;
    split_piece shs (Zlength cs) is k cs ps;
    split_piece shd (Zlength cd) id k cd pd;
    Intros
  end end end end.

Ltac copy_finish k :=
  match goal with |- context [data_at ?shs (tarray tuchar (Zlength ?cs)) ?cs ?ps] =>
  match goal with |- context [data_at ?shd (tarray tuchar (Zlength ?cd)) (copied ?cs ?cd ?is ?id k) ?pd] =>
    assert (Zlength (copied cs cd is id k) = Zlength cd) by (unfold copied; list_solve);
    unfold tarray;
    split_piece shs (Zlength cs) is k cs ps;
    split_piece shd (Zlength cd) id k (copied cs cd is id k) pd;
    unfold copied; autorewrite with sublist;
    rewrite (Z.add_comm k is); replace (Zlength cd - id - k + (id + k)) with (Zlength cd) by lia;
    cancel
  end end.

Lemma body_ZSTD_copy8 : semax_body Vprog Gprog f_ZSTD_copy8 ZSTD_copy8_spec.
Proof.
  start_function. copy_start 8.
  forward_call (shs, shd, offset_val is ps, offset_val id pd,
                existT (fun t => reptype t) (tarray tuchar 8) (sublist is (is + 8) cs)).
  { simpl projT1; simpl projT2. rewrite sizeof_tarray_tuchar by lia.
    split; [rep_lia | apply memcpy_ok_bytes; [list_solve | exact Hdef]]. }
  simpl projT1; simpl projT2. entailer!. copy_finish 8.
Qed.

Lemma body_ZSTD_copy4 : semax_body Vprog Gprog f_ZSTD_copy4 ZSTD_copy4_spec.
Proof.
  start_function. copy_start 4.
  forward_call (shs, shd, offset_val is ps, offset_val id pd,
                existT (fun t => reptype t) (tarray tuchar 4) (sublist is (is + 4) cs)).
  { simpl projT1; simpl projT2. rewrite sizeof_tarray_tuchar by lia.
    split; [rep_lia | apply memcpy_ok_bytes; [list_solve | exact Hdef]]. }
  simpl projT1; simpl projT2. entailer!. copy_finish 4.
Qed.

Lemma body_ZSTD_copy16 : semax_body Vprog Gprog f_ZSTD_copy16 ZSTD_copy16_spec.
Proof.
  start_function. copy_start 16.
  forward_call (shs, Tsh, offset_val is ps, v_copy16_buf,
                existT (fun t => reptype t) (tarray tuchar 16) (sublist is (is + 16) cs)).
  { simpl projT1; simpl projT2. rewrite sizeof_tarray_tuchar by lia.
    split; [rep_lia | apply memcpy_ok_bytes; [list_solve | exact Hdef]]. }
  simpl projT1; simpl projT2.
  forward_call (Tsh, shd, v_copy16_buf, offset_val id pd,
                existT (fun t => reptype t) (tarray tuchar 16) (sublist is (is + 16) cs)).
  { simpl projT1; simpl projT2. rewrite sizeof_tarray_tuchar by lia.
    split; [rep_lia | apply memcpy_ok_bytes; [list_solve | exact Hdef]]. }
  simpl projT1; simpl projT2. entailer!. copy_finish 16.
Qed.

Lemma bodies_util_misc :
  semax_body Vprog Gprog f_ZSTD_wrappedPtrAdd ZSTD_wrappedPtrAdd_spec /\
  semax_body Vprog Gprog f_ZSTD_wrappedPtrSub ZSTD_wrappedPtrSub_spec /\
  semax_body Vprog Gprog f_ZSTD_maybeNullPtrAdd ZSTD_maybeNullPtrAdd_spec /\
  semax_body Vprog Gprog f_ERR_isError ERR_isError_spec /\
  semax_body Vprog Gprog f_ERR_getErrorCode ERR_getErrorCode_spec /\
  semax_body Vprog Gprog f_FSE_isError FSE_isError_spec /\
  semax_body Vprog Gprog f_ZSTD_copy8 ZSTD_copy8_spec /\
  semax_body Vprog Gprog f_ZSTD_copy16 ZSTD_copy16_spec /\
  semax_body Vprog Gprog f_ZSTD_isError ZSTD_isError_spec /\
  semax_body Vprog Gprog f_ZSTD_getErrorCode ZSTD_getErrorCode_spec /\
  semax_body Vprog Gprog f_ZSTD_DCtx_get_bmi2 ZSTD_DCtx_get_bmi2_spec /\
  semax_body Vprog Gprog f_ZSTD_copy4 ZSTD_copy4_spec.
Proof.
  repeat split.
  all: first [ apply body_ZSTD_wrappedPtrAdd | apply body_ZSTD_wrappedPtrSub
             | apply body_ZSTD_maybeNullPtrAdd | apply body_ERR_isError
             | apply body_ERR_getErrorCode | apply body_FSE_isError
             | apply body_ZSTD_copy8 | apply body_ZSTD_copy16
             | apply body_ZSTD_isError | apply body_ZSTD_getErrorCode
             | apply body_ZSTD_DCtx_get_bmi2 | apply body_ZSTD_copy4 ].
Qed.
