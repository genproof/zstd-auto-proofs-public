(* FS3-bl BODY, stages 3/4, RLE block: helpers (the output window, copied from v2
   body_stream_continue.v; the frame group around rleSize and expected). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Local Open Scope logic.

Section CM_RleHelp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the frame group without rleSize and expected ---------- *)

Definition rl_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma fcore3_split_rl p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr && (field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
                   field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * rl_rest p fs pr).
Proof. unfold fcore3, rl_rest, frame_fields. entailer!. Qed.

Lemma fcore3_join_rl p fs pr v :
  par_ok pr ->
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p * field_at Ews t_dctx (DOT _expected) v p * rl_rest p fs pr
  |-- fcore3 p (fsu_ddictIsCold (fsu_expected fs v) (fs_ddictIsCold fs)) pr nullval.
Proof.
  intros. unfold fcore3, rl_rest, frame_fields, fsu_ddictIsCold, fsu_expected.
  cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
       fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum fs_rleSize
       fs_isFrameDecompression fs_dictID fs_ddictIsCold].
  entailer!.
Qed.

Lemma bl_fs1_rle fs ob osz opos pcs n : fs_rleSize (bl_fs1 fs ob osz opos pcs n) = fs_rleSize fs.
Proof. unfold bl_fs1, continuity. destruct cont_moves; reflexivity. Qed.

Lemma bl_fs1_cold fs ob osz opos pcs n : fs_ddictIsCold (bl_fs1 fs ob osz opos pcs n) = fs_ddictIsCold fs.
Proof. unfold bl_fs1, continuity. destruct cont_moves; reflexivity. Qed.

(* ---------- the output window [d, d + cap) (v2 body_stream_continue.v) ---------- *)

Lemma rl_fc_arr N base :
  field_compatible (tarray tuchar N) [] base -> 0 <= N ->
  exists b ofs, base = Vptr b ofs /\ Ptrofs.unsigned ofs + N < Ptrofs.modulus.
Proof.
  intros (Hp & _ & Hs & _) HN. destruct base; try contradiction. exists b, i. split; auto.
  red in Hs. simpl in Hs. rewrite Z.max_r in Hs by lia. lia.
Qed.

Lemma rl_arr_wvp sh N (c: list val) p d :
  sepalg.nonidentity sh -> 0 <= d <= N -> 0 < N ->
  data_at sh (tarray tuchar N) c p |-- weak_valid_pointer (offset_val d p).
Proof.
  intros. eapply derives_trans; [apply data_at_memory_block |].
  apply memory_block_weak_valid_pointer; auto; simpl; rep_lia.
Qed.

Lemma rl_fa0_sub N p k :
  field_compatible (tarray tuchar N) [] p -> 0 <= k <= N ->
  field_address0 (Tarray tuchar N noattr) (SUB k) p = offset_val k p.
Proof.
  intros. rewrite field_address0_offset by auto with field_compatible. simpl. f_equal. lia.
Qed.

Definition rl_mid (o: outarr) : outarr :=
  {| oa_sh := oa_sh o; oa_base := offset_val (oa_d o) (oa_base o); oa_N := oa_cap o;
     oa_c := sublist (oa_d o) (oa_d o + oa_cap o) (oa_c o); oa_d := 0; oa_cap := oa_cap o |}.

Definition rl_side (o: outarr) : list ptr_witness :=
  [pw_bytes (oa_sh o) (oa_d o) (sublist 0 (oa_d o) (oa_c o)) (oa_base o);
   pw_bytes (oa_sh o) (oa_N o - (oa_d o + oa_cap o)) (sublist (oa_d o + oa_cap o) (oa_N o) (oa_c o))
     (offset_val (oa_d o + oa_cap o) (oa_base o))].

Lemma rl_mid_ok o : outarr_ok o -> outarr_ok (rl_mid o).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc). unfold rl_mid, outarr_ok; cbn.
  split; [auto |]. split; [rewrite Zlength_sublist; lia |]. repeat split; lia.
Qed.

Lemma rl_pws_app W1 W2 : pws_pred (W1 ++ W2) = (pws_pred W1 * pws_pred W2)%logic.
Proof.
  induction W1; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. auto.
  - unfold pws_pred in *. simpl. rewrite IHW1. rewrite sepcon_assoc. auto.
Qed.

Lemma rl_pws_fold W1 W2 : pws_pred W1 * pws_pred W2 |-- pws_pred (W1 ++ W2).
Proof. rewrite rl_pws_app. apply derives_refl. Qed.

Lemma rl_pws_unfold W1 W2 : pws_pred (W1 ++ W2) |-- pws_pred W1 * pws_pred W2.
Proof. rewrite rl_pws_app. apply derives_refl. Qed.

Lemma rl_out_split o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o) =
  (pws_pred (rl_side o) *
   data_at (oa_sh o) (tarray tuchar (oa_cap o)) (oa_c (rl_mid o)) (offset_val (oa_d o) (oa_base o)))%logic.
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc. unfold rl_side, rl_mid, pws_pred; cbn.
  unfold tarray. rewrite (split3_data_at_Tarray_tuchar (oa_sh o) (oa_N o) (oa_d o) (oa_d o + oa_cap o)) by lia.
  rewrite !rl_fa0_sub by (auto; lia). replace (oa_d o + oa_cap o - oa_d o) with (oa_cap o) by lia.
  rewrite sepcon_emp. apply pred_ext; cancel.
Qed.

Lemma rl_out_unsplit o :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) ->
  pws_pred (rl_side o) * data_at (oa_sh o) (tarray tuchar (oa_cap o)) (oa_c (rl_mid o)) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (oa_c o) (oa_base o).
Proof. intros. rewrite (rl_out_split o) by auto. apply derives_refl. Qed.

Lemma rl_out_join o (bs: list Z) :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> Zlength bs <= oa_cap o ->
  pws_pred (rl_side o) *
  data_at (oa_sh o) (tarray tuchar (oa_cap o)) (put_bytes (oa_c (rl_mid o)) 0 bs) (offset_val (oa_d o) (oa_base o))
  |-- data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o).
Proof.
  intros Ho Fc Hb. pose proof Ho as (Hs & Hc & HN & Hd & Hcap & Hdc). pose proof (Zlength_nonneg bs).
  assert (Hz: Zlength (zbytes bs) = Zlength bs) by apply Zlength_map.
  assert (Lp: Zlength (put_bytes (oa_c o) (oa_d o) bs) = oa_N o)
    by (unfold put_bytes; rewrite !Zlength_app, Hz, !Zlength_sublist by lia; lia).
  set (o2 := {| oa_sh := oa_sh o; oa_base := oa_base o; oa_N := oa_N o;
      oa_c := put_bytes (oa_c o) (oa_d o) bs; oa_d := oa_d o; oa_cap := oa_cap o |}).
  change (data_at (oa_sh o) (tarray tuchar (oa_N o)) (put_bytes (oa_c o) (oa_d o) bs) (oa_base o))
    with (data_at (oa_sh o2) (tarray tuchar (oa_N o2)) (oa_c o2) (oa_base o2)).
  rewrite (rl_out_split o2) by (subst o2; first [assumption | split; [exact Hs |]; split; [exact Lp |]; cbn; repeat split; lia]).
  subst o2.
  unfold rl_side, rl_mid, pws_pred; cbn [map fold_right oa_sh oa_base oa_N oa_c oa_d oa_cap pw_pred].
  rewrite !sepcon_emp. unfold put_bytes.
  apply sepcon_derives; [apply sepcon_derives |]; apply derives_refl'; f_equal; list_solve.
Qed.

(* cap = 0: the window's start is weakly valid through W and the two sides (an empty array: buf_ok) *)
Lemma rl_mid_wvp o W :
  outarr_ok o -> field_compatible (tarray tuchar (oa_N o)) [] (oa_base o) -> oa_cap o = 0 ->
  buf_ok W (oa_sh o) (oa_N o) (oa_base o) ->
  pws_pred (W ++ rl_side o) |-- weak_valid_pointer (offset_val (oa_d o) (oa_base o)).
Proof.
  intros (Hs & Hc & HN & Hd & Hcap & Hdc) Fc H0 HW. rewrite rl_pws_app.
  assert (Hni: sepalg.nonidentity (oa_sh o)) by (apply readable_nonidentity, writable_readable; auto).
  destruct (zlt 0 (oa_d o)).
  - apply sepcon_weak_valid_pointer2. unfold rl_side, pws_pred; simpl. apply sepcon_weak_valid_pointer1.
    apply rl_arr_wvp; auto; lia.
  - destruct (zlt 0 (oa_N o)).
    + apply sepcon_weak_valid_pointer2. unfold rl_side, pws_pred; simpl. apply sepcon_weak_valid_pointer2.
      apply sepcon_weak_valid_pointer1. rewrite H0, Z.add_0_r.
      destruct (rl_fc_arr _ _ Fc ltac:(lia)) as (bb & ofs & -> & _).
      rewrite <- (isptr_offset_val_zero (offset_val (oa_d o) (Vptr bb ofs))) at 2 by exact I.
      apply rl_arr_wvp; auto; lia.
    + assert (Hd0: oa_d o = 0) by lia. assert (HN0: oa_N o = 0) by lia.
      rewrite HN0 in HW. unfold rl_side, pws_pred; simpl. rewrite Hd0. rewrite sepcon_emp, <- sepcon_assoc.
      apply sepcon_weak_valid_pointer1.
      eapply derives_trans; [| apply andp_left2, derives_refl].
      eapply derives_trans; [| apply HW].
      apply sepcon_derives; [apply derives_refl |]. apply data_at_data_at_.
Qed.

(* ---------- the facts of an RLE block ---------- *)

Lemma rle_facts md od osz0 ba fs hb v (c: list Z) :
  bl_cinv md od osz0 ba fs hb v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 1 ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  fs_rleSize fs = vlong (bv_rle v) /\ 0 <= bv_rle v < 2 ^ 21 /\ Zlength c = 1 /\ cold01 fs.
Proof.
  intros (_ & _ & _ & _ & Hc & _ & _ & _ & _ & _ & Hs & _) Hst Hbt Hsz.
  unfold bl_cstage, bl_size_ok in *.
  destruct Hst as [E | E]; rewrite E in Hs, Hsz; rewrite Hbt in Hsz; cbn in Hsz;
    destruct Hs as (_ & _ & _ & Hr & Hrr & _ & He); specialize (He Hbt); repeat split; auto; lia.
Qed.

Lemma rle_err_code : is_error_code (err_code ZSTD_error_dstSize_tooSmall) = true.
Proof. reflexivity. Qed.

Lemma rle_err_range : 0 <= err_code ZSTD_error_dstSize_tooSmall <= Int64.max_unsigned.
Proof. unfold err_code. cbv [ZSTD_error_dstSize_tooSmall]. rep_lia. Qed.

Lemma rle_blk_model md ba fs ts v (c: list Z) b dm :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 1 -> s34_fol ba c b dm ->
  blk_model dm b c = Some (ts_d ts, repeat (byte_at c 0) (Z.to_nat (bv_rle v))).
Proof.
  intros Hm Hst Hbt (Hb & _ & _). destruct (Hm b Hb) as (Es & _ & Ed & _ & _ & Hx).

  assert (Hy: bs_btype b = 1 /\ bs_rle b = bv_rle v)
    by (destruct Hst as [E | E]; rewrite E in Hx; destruct Hx as (_ & Ht & Hr & _); rewrite Ht, Hbt; auto).
  destruct Hy as [Ht Hr]. unfold blk_model. rewrite Ht, Hr, Ed. reflexivity.
Qed.

Lemma rle_byte_at (c: list Z) : Zlength c = 1 -> byte_at c 0 = Znth 0 c.
Proof. intros. destruct c as [ | x l]; [list_solve | reflexivity]. Qed.

Lemma rle_mid_err md od ba fs ts v osz opos (oc: list val) (c: list Z) cold :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 1 ->
  0 <= bv_rle v -> osz - opos < bv_rle v -> Zlength oc = osz ->
  (cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)) ->
  s34_mid_ok od ba v osz opos oc c (err_code ZSTD_error_dstSize_tooSmall) oc 0 cold (TInit (bd_oxo od) ts).
Proof.
  intros Hm Hst Hbt Hr0 Hlt Hl Hc. unfold s34_mid_ok.
  split; [apply rle_err_range |]. split; [auto |]. split; [auto |]. split; [auto |].
  rewrite rle_err_code. split; [| discriminate].
  intros _ b dm Hf. rewrite (rle_blk_model md ba fs ts v c b dm) by auto.
  rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. lia.
Qed.

Lemma rle_mid_succ md od ba fs ts v osz opos (oc: list val) (c: list Z) cold :
  bl_mrel md ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 1 ->
  0 <= bv_rle v < 2 ^ 21 -> bv_rle v <= osz - opos -> 0 <= opos -> Zlength oc = osz -> Zlength c = 1 -> bytes_ok c ->
  (cold = Vint (Int.repr 0) \/ cold = Vint (Int.repr 1)) ->
  s34_mid_ok od ba v osz opos oc c (bv_rle v) (put_bytes oc opos (Zrepeat (Znth 0 c) (bv_rle v))) 0 cold
    (TInit (bd_oxo od) ts).
Proof.
  intros Hm Hst Hbt Hr Hle Ho Hl Hc1 Hbc Hc.
  assert (Lz: Zlength (Zrepeat (Znth 0 c) (bv_rle v)) = bv_rle v) by (rewrite Zlength_Zrepeat; lia).
  assert (Hnoerr: is_error_code (bv_rle v) = false)
    by (unfold is_error_code; apply Z.ltb_ge; lia).
  unfold s34_mid_ok. split; [rep_lia |].
  split; [unfold put_bytes; rewrite !Zlength_app, Zlength_map, !Zlength_sublist by lia; lia |].
  split; [unfold put_bytes; list_solve |]. split; [auto |].
  rewrite Hnoerr. split; [discriminate |]. intros _.
  split; [lia |]. rewrite Hbt. split; [reflexivity |]. split; [lia |].
  exists (Zrepeat (Znth 0 c) (bv_rle v)), ts. split.
  { unfold put_bytes. rewrite Lz. list_solve. }
  split.
  { unfold bytes_ok in *. unfold Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x.
    apply Forall_Znth; auto. lia. }
  split; [auto |]. split; [reflexivity |].
  intros b dm x Hf Hx. rewrite (rle_blk_model md ba fs ts v c b dm) in Hx by auto. inv Hx.
  rewrite rle_byte_at by auto. reflexivity.
Qed.

End CM_RleHelp_1.
