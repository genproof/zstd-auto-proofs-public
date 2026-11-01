(* valid_params main, segment D2: VST helpers of the loop body (from valid_stream's v2 main,
   WMain_valid_stream.v: compspecs conversions, the buffer witnesses, the chunk's block), and the borrow of
   the chunk src[ipos, ipos + ilen). *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_params.VPD2Defs.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Definition D2_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma D2_arr: forall sh n (v: list val) p,
  @data_at ZCS sh (tarray tuchar n) v p = @data_at HCS sh (tarray tuchar n) v p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (D2_cce ZCS HCS) sh (tarray tuchar n) v v
    (JMeq_refl _) ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma D2_arr_: forall sh n p,
  @data_at_ ZCS sh (tarray tuchar n) p = @data_at_ HCS sh (tarray tuchar n) p.
Proof.
  intros. pose proof (@data_at__change_composite ZCS HCS (D2_cce ZCS HCS) sh (tarray tuchar n)
    ltac:(reflexivity)) as E. rewrite E; reflexivity.
Qed.

Lemma D2_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (D2_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma D2_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (D2_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma D2_ltu_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma D2_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

Ltac D2_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Lemma D2_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

(* the witnesses lent to ZSTD_decompressStream: the unused byte of ib = malloc(1) when ilen = 0 *)
Definition D2_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma D2_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

Lemma D2_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma D2_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  !!(buf_ok (D2_W il ib) Ews il ib) && (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (D2_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold D2_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    apply andp_right; [apply prop_right; apply D2_buf_ok_pos; lia | apply derives_refl].
  - apply Zlength_nil_inv in HA. subst A. unfold D2_W. rewrite if_true by auto.
    apply andp_right; [apply prop_right; apply D2_buf_ok_zero|].
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef]. change (Zrepeat Vundef 1) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma D2_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (D2_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold D2_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold D2_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

Lemma D2_free_prep {cs: compspecs} sh t v p :
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at sh t v p) |--
  (if eq_dec p nullval then emp else malloc_token sh t p * data_at_ sh t p).
Proof. destruct (eq_dec p nullval); [auto|]. apply sepcon_derives; [auto | apply data_at_data_at_]. Qed.

(* the chunk src[ipos, ipos + ilen), lent to exact_copy(src + ipos, ilen) *)
Lemma D2_src_borrow (bs: list Z) src ipos ilen :
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength bs ->
  @data_at HCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src |--
  @data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) bs)))
    (zbytes (sublist ipos (ipos + ilen) bs)) (offset_val ipos src) *
  (@data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) bs)))
     (zbytes (sublist ipos (ipos + ilen) bs)) (offset_val ipos src) -*
   @data_at HCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) src).
Proof.
  intros H0 H1 H2.
  assert_PROP (@field_compatible HCS (tarray tuchar (Zlength bs)) nil src) by entailer!.
  assert (HZ: Zlength (sublist ipos (ipos + ilen) bs) = ilen) by list_solve.
  rewrite HZ.
  assert (HL: Zlength (zbytes bs) = Zlength bs) by list_solve.
  rewrite (split3_data_at_Tarray_tuchar Ews (Zlength bs) ipos (ipos + ilen) (zbytes bs)) by lia.
  replace (sublist ipos (ipos + ilen) (zbytes bs)) with (zbytes (sublist ipos (ipos + ilen) bs)) by list_solve.
  replace (ipos + ilen - ipos) with ilen by lia.
  rewrite field_address0_offset by auto with field_compatible.
  replace (offset_val (nested_field_offset (tarray tuchar (Zlength bs)) (SUB ipos)) src)
    with (offset_val ipos src) by (simpl nested_field_offset; f_equal; simpl sizeof; lia).
  match goal with |- sepcon (sepcon ?A ?B) ?C |-- _ =>
    apply derives_trans with (sepcon B (sepcon A C));
    [cancel | apply sepcon_derives; [apply derives_refl | rewrite <- wand_sepcon_adjoint; cancel]] end.
Qed.

(* the facts at D2_tail, and what main's asserts need, from the call's post *)
Lemma D2_post_M2 wsr ws' p base wlim st st' r ob osz opos' oc oc' calls ipos ilen ipos' got stalled :
  VP_dfacts wsr ws' p base wlim ->
  D2_st_ok p ws' (ws_content wsr) st ipos got stalled ->
  0 <= calls < 4096 -> 0 <= stalled <= calls ->
  0 <= ipos -> 0 <= ilen -> ipos + ilen <= Zlength (ws_bytes ws') -> 0 <= got <= Zlength (ws_content wsr) ->
  0 < osz <= 2 ^ 18 + 1 -> 0 <= r <= Int64.max_unsigned ->
  stream_post st st' r ob osz 0 opos' oc oc' (sublist ipos (ipos + ilen) (ws_bytes ws')) ilen 0 ipos' ->
  exists dl,
    (0 <= ipos' <= ilen /\ opos' = Zlength dl /\ Zlength dl <= osz /\ Zlength oc' = osz) /\
    (sublist 0 (Zlength dl) oc' = zbytes dl /\ bytes_ok dl) /\
    (got + Zlength dl <= Zlength (ws_content wsr) /\ dl = sublist got (got + Zlength dl) (ws_content wsr)) /\
    ipos + ipos' <= Zlength (ws_bytes ws') /\
    D2_M2_ok wsr ws' p base wlim calls (ipos + ipos') (got + Zlength dl) stalled ilen ipos' osz (Zlength dl) r st'.
Proof.
  intros Hd Hst Hc Hs Hip Hil Hiln Hg Hosz Hr Hp.
  destruct (D2_post wsr ws' p base wlim st st' r ob osz opos' oc oc' ipos ilen ipos' got stalled Hd Hst Hip Hil Hiln Hg Hp)
    as (dl & a' & stall' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  pose proof Hst as (Hpar & Hdict & Hset & Hbl & Hstab & Herr & _ & _ & Hstl).
  exists dl. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [lia|].
  pose proof H1 as (Q1 & Q2 & Q3 & Q4). pose proof H3 as [Q5 _]. pose proof H4 as [Q6 Q7]. pose proof (Zlength_nonneg dl).
  subst st'. unfold D2_M2_ok, D2_in_ok. cbn [dc_par dc_dict dc_set dc_bl dc_stable dc_ss set_last set_ss
    ss_err ss_in ss_out ss_stall ss_ahead].
  split; [exact Hd|]. do 9 (split; [lia|]).
  do 5 (split; [assumption|]).
  split; [reflexivity|].
  split; [split; [lia | split; [lia | reflexivity]]|].
  split; [reflexivity|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
  intros E. apply H9. exact E.
Qed.

(* sr.content[k], lent out of its wrapper *)
Lemma D2_content_borrow_w (V: list val) p k :
  0 <= k < 2 ^ 18 -> Zlength V = 2 ^ 18 ->
  VP_Rc V p |--
  @data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) *
  (@data_at HCS Ews tuchar (Znth k V) (offset_val (524296 + k) p) -* VP_Rc V p).
Proof. unfold VP_Rc. apply VP_content_borrow. Qed.
