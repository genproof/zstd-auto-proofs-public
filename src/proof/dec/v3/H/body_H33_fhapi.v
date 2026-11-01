(* Subtree H: the API wrappers of the frame header and frame size, against H_G (HSpecs.v).
   API v3.3: src/proof/dec/H/body_H_fhapi.v with the exact error code of fh_post (FH_err => dec_err r /\ r = code). *)
Require Import Zstd.proof.dec.H.HLemmas.
Local Open Scope logic.

Lemma fhapi_fhd_size: forall x, 5 <= fhd_header_size x.
Proof.
  intros x. unfold fhd_header_size.
  assert (Hss: 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { pose proof (Z.land_ones (Z.shiftr x 5) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
    rewrite E. change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2 ltac:(lia)). lia. }
  assert (A: forall n, 0 <= nth n [0; 1; 2; 4] 0) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  assert (B: forall n, 0 <= nth n [0; 2; 4; 8] 0) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  pose proof (A (Z.to_nat (Z.land x 3))). pose proof (B (Z.to_nat (Z.shiftr x 6))).
  destruct (andb _ _); lia.
Qed.

Lemma fhapi_fhd_size_le: forall x, fhd_header_size x <= 20.
Proof.
  intros x. unfold fhd_header_size.
  assert (Hss: 0 <= Z.land (Z.shiftr x 5) 1 <= 1).
  { pose proof (Z.land_ones (Z.shiftr x 5) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
    rewrite E. change (2 ^ 1) with 2. pose proof (Z.mod_pos_bound (Z.shiftr x 5) 2 ltac:(lia)). lia. }
  assert (A: forall n, nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  assert (B: forall n, nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|[|]]]]]; simpl; lia).
  pose proof (A (Z.to_nat (Z.land x 3))). pose proof (B (Z.to_nat (Z.shiftr x 6))).
  destruct (andb _ _); lia.
Qed.

Lemma fhapi_more: forall s k, get_frame_header s = FH_more k -> 5 <= k <= 20.
Proof.
  intros s k H. unfold get_frame_header in H. cbv zeta in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
  inversion H; subst; try (unfold ZSTD_SKIPPABLEHEADERSIZE; lia).
  split; [apply fhapi_fhd_size | apply fhapi_fhd_size_le].
Qed.

Lemma fhapi_ftype: forall s h, get_frame_header s = FH_ok h -> fh_frameType h = 0 \/ fh_frameType h = 1.
Proof.
  intros s h H. unfold get_frame_header in H. cbv zeta in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
  inversion H; subst; simpl; auto.
Qed.

Lemma fhapi_err_nz: forall r, is_error_code r = true -> r <> 0.
Proof. intros r H E. subst. discriminate. Qed.

Lemma body_ZSTD_frameHeaderSize:
  semax_body Vprog H_G f_ZSTD_frameHeaderSize ZSTD_frameHeaderSize_spec.
Proof.
  start_function.
  assert_PROP (isptr src) by entailer!.
  forward_call (gv, sh, src, Zlength s, zbytes s, 0, s).
  { apply win_ok_full; auto. }
  Intros r. forward. Exists r. entailer!.
  destruct (frame_header_size s); [auto | apply dec_err_is_error; auto].
Qed.

Lemma body_ZSTD_findFrameCompressedSize:
  semax_body Vprog H_G f_ZSTD_findFrameCompressedSize ZSTD_findFrameCompressedSize_spec.
Proof.
  start_function.
  assert_PROP (isptr src) by entailer!.
  forward_call (gv, sh, src, Zlength s, zbytes s, 0, s).
  { apply win_ok_full; auto. }
  Intros r. forward. Exists r. entailer!.
Qed.

Lemma body_ZSTD_getFrameHeader:
  semax_body Vprog H_G f_ZSTD_getFrameHeader ZSTD_getFrameHeader_spec.
Proof.
  start_function.
  assert_PROP (isptr src) by entailer!.
  forward_call (gv, shz, pz, v0, sh, src, Zlength s, zbytes s, 0, s).
  { apply win_ok_full; auto. }
  Intros vret. destruct vret as [r v]. unfold fh_post_adv in *. forward. Exists r v. entailer!.
Qed.

(* a return from a function with a local ZSTD_FrameHeader: its value, and the frame header freed *)
Ltac fhapi_ret Efh :=
  apply andp_right;
  [ apply prop_right; unfold frame_content_size, dict_id_from_frame; rewrite Efh;
    try reflexivity; try (f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity)
  | match goal with |- context [data_at Tsh t_fh ?v ?p] =>
      sep_apply (data_at_data_at_ Tsh t_fh v p) end; cancel ].

(* the branch where the call returned 0, for a nonzero r *)
Ltac fhapi_nz :=
  match goal with Hz: Int64.repr _ = _ |- _ =>
    unfold Int64.zero in Hz; apply repr_inj_unsigned64 in Hz; [lia | rep_lia | rep_lia] end.

Lemma body_ZSTD_getFrameContentSize:
  semax_body Vprog H_G f_ZSTD_getFrameContentSize ZSTD_getFrameContentSize_spec.
Proof.
  start_function.
  forward_call (gv, Tsh, v_zfh, default_val t_fh, sh, src, s).
  Intros vret. destruct vret as [r v]. simpl fst in *. simpl snd in *.
  unfold fh_post in *. destruct (get_frame_header s) as [|k|h] eqn:Efh.
  - forward_if.
    + forward. fhapi_ret Efh.
    + destruct H1 as [H1 _]. apply dec_err_is_error, fhapi_err_nz in H1. fhapi_nz.
  - assert (Hk: 5 <= k <= 20) by (eapply fhapi_more; eauto). destruct H1 as [-> _].
    forward_if.
    + forward. fhapi_ret Efh.
    + fhapi_nz.
  - destruct H1 as [-> ->]. pose proof (fhapi_ftype _ _ Efh) as Ht.
    forward_if; [discriminate |].
    forward.
    forward_if.
    + forward. fhapi_ret Efh. rewrite H2. reflexivity.
    + forward. forward. fhapi_ret Efh. destruct (Z.eqb_spec (fh_frameType h) 1); [contradiction | reflexivity].
Qed.

Lemma body_ZSTD_getDictID_fromFrame:
  semax_body Vprog H_G f_ZSTD_getDictID_fromFrame ZSTD_getDictID_fromFrame_spec.
Proof.
  start_function.
  do 9 forward.
  match goal with |- context [data_at Tsh _ ?v0 v_zfp] =>
    replace v0 with (fh_val fh_zero) by reflexivity end.
  forward_call (gv, Tsh, v_zfp, fh_val fh_zero, sh, src, s).
  Intros vret. destruct vret as [r v]. simpl fst in *. simpl snd in *.
  forward_call r.
  unfold fh_post in H1. destruct (get_frame_header s) as [|k|h] eqn:Efh.
  - destruct H1 as [H1 _]. apply dec_err_is_error in H1. rewrite H1. forward_if.
    + forward. fhapi_ret Efh.
    + apply repr_inj_unsigned in H2; rep_lia.
  - destruct H1 as [-> Hv]. assert (Hk: 5 <= k <= 20) by (eapply fhapi_more; eauto).
    assert (Hv': v = fh_val fh_zero) by (rewrite Hv; destruct (_ <? 5); reflexivity).
    clear Hv. subst v.
    replace (is_error_code k) with false
      by (symmetry; unfold is_error_code; apply Z.ltb_ge; lia).
    forward_if; [congruence |].
    forward.
    forward_if; [lia |].
    forward. forward. fhapi_ret Efh.
  - destruct H1 as [-> ->]. pose proof (fhapi_ftype _ _ Efh) as Ht.
    change (is_error_code 0) with false. cbv iota.
    forward_if; [elim H1; reflexivity |].
    forward.
    forward_if.
    + forward. fhapi_ret Efh. rewrite H2. reflexivity.
    + forward. forward. fhapi_ret Efh. destruct (Z.eqb_spec (fh_frameType h) 1); [contradiction | reflexivity].
Qed.

Lemma bodies_H_fhapi :
  semax_body Vprog H_G f_ZSTD_frameHeaderSize ZSTD_frameHeaderSize_spec /\
  semax_body Vprog H_G f_ZSTD_getFrameHeader ZSTD_getFrameHeader_spec /\
  semax_body Vprog H_G f_ZSTD_getFrameContentSize ZSTD_getFrameContentSize_spec /\
  semax_body Vprog H_G f_ZSTD_getDictID_fromFrame ZSTD_getDictID_fromFrame_spec /\
  semax_body Vprog H_G f_ZSTD_findFrameCompressedSize ZSTD_findFrameCompressedSize_spec.
Proof.
  split; [exact body_ZSTD_frameHeaderSize |].
  split; [exact body_ZSTD_getFrameHeader |].
  split; [exact body_ZSTD_getFrameContentSize |].
  split; [exact body_ZSTD_getDictID_fromFrame |].
  exact body_ZSTD_findFrameCompressedSize.
Qed.
