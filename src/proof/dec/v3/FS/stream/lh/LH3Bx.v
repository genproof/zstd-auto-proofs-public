(* FS3 streaming, case zdss_loadHeader, piece B: helper lemmas (ported from v2's StreamSeg_lhB.v; R1). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3Bx_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma fcs_repr_unknown : forall x, 0 <= x <= Int64.max_unsigned ->
  (Int64.repr x = Int64.sub (Int64.repr 0) (Int64.repr 1) <-> x = ZSTD_CONTENTSIZE_UNKNOWN).
Proof.
intros x Hx. split; intros E.
- apply (f_equal Int64.unsigned) in E. rewrite Int64.unsigned_repr in E by lia.
  rewrite E. reflexivity.
- subst x. unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia.
  apply Int64.eqm_samerepr. exists 1. reflexivity.
Qed.

Lemma lhB_t26 : forall h, 0 <= fh_contentSize h <= Int64.max_unsigned ->
  (fh_frameType h = 0 \/ fh_frameType h = 1) ->
  Int64.repr (fh_contentSize h) <> Int64.sub (Int64.repr 0) (Int64.repr 1) ->
  Vint (Int.repr (if andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN)) (negb (fh_frameType h =? 1))
                  then 1 else 0)) = bool2val (negb (zeq (fh_frameType h) 1)).
Proof.
intros h Hf Ht Hn.
destruct (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN) eqn:E.
- apply Z.eqb_eq in E. exfalso. apply Hn. apply fcs_repr_unknown; auto.
- destruct Ht as [Ht|Ht]; rewrite Ht; reflexivity.
Qed.

Lemma lhB_t26' : forall h, 0 <= fh_contentSize h <= Int64.max_unsigned ->
  Int64.eq (Int64.repr (fh_contentSize h)) (Int64.sub (Int64.repr 0) (Int64.repr 1)) = true ->
  Vint (Int.repr (if andb (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN)) (negb (fh_frameType h =? 1))
                  then 1 else 0)) = Vint (Int.repr 0).
Proof.
intros h Hf Hn. apply Int64.same_if_eq in Hn. apply fcs_repr_unknown in Hn; auto.
rewrite Hn, Z.eqb_refl. reflexivity.
Qed.

(* do { } while (0) *)
Lemma semax_dowhile0 : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c R -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_seq with P; [| exact H].
destruct R as [Rn Rb Rc Rr]; simpl.
apply semax_loop with (Q' := P).
- eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto;
    try apply FF_left.
- eapply semax_pre; [| apply semax_break]. simpl. intros; apply andp_left2; auto.
Qed.

Lemma sub_pp_tschar : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 30 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* a point of a caller's buffer is weakly valid: its ends from buf_ok, its inside from the cells *)
Lemma wvp_buf : forall (W: list ptr_witness) sh n (c: list val) p (R: mpred) x,
  buf_ok W sh n p -> readable_share sh -> 0 <= x <= n ->
  (pws_pred W * data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val x p))%logic.
Proof.
intros W sh n c p R x Hb Hr Hx.
apply sepcon_weak_valid_pointer1.
assert_PROP (isptr p) as Pp by (saturate_local; entailer!).
destruct (Z.eq_dec x n) as [->|Hxn].
- sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left2. auto.
- destruct (Z.eq_dec x 0) as [->|Hx0].
  + sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
    rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left1. rewrite isptr_offset_val_zero by auto. auto.
  + apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply data_at_memory_block|].
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    eapply derives_trans; [apply (memory_block_valid_pointer sh n p x); [lia | apply readable_nonidentity; auto]|].
    apply valid_pointer_weak.
Qed.

Lemma lhB_t27 : forall ob osz opc fcs, isptr ob -> 0 <= opc <= osz -> osz <= 2 ^ 30 ->
  0 <= fcs <= Int64.max_unsigned ->
  force_val (sem_cast tint tbool (eval_binop Oge tulong tulong (eval_cast tulong tulong (eval_cast tlong tulong
    (eval_binop Osub (tptr tschar) (tptr tschar) (offset_val osz ob) (offset_val opc ob))))
    (Vlong (Int64.repr fcs)))) = Vint (Int.repr (if fcs <=? osz - opc then 1 else 0)).
Proof.
intros ob osz opc fcs Hob Ho Hosz Hf.
change (eval_binop Osub (tptr tschar) (tptr tschar) (offset_val osz ob) (offset_val opc ob))
  with (force_val (sem_sub_pp tschar (offset_val osz ob) (offset_val opc ob))).
rewrite sub_pp_tschar by (auto; lia).
simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
destruct (zlt (osz - opc) fcs); destruct (Z.leb_spec fcs (osz - opc)); try lia; reflexivity.
Qed.

Lemma lhB_bytes_sub : forall bs i j, bytes_ok bs -> bytes_ok (sublist i j bs).
Proof. intros. unfold bytes_ok in *. apply Forall_sublist; auto. Qed.

Lemma lhB_arr_split : forall sh n k (c: list val) p, 0 <= k <= n -> Zlength c = n ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) c p =
  data_at sh (tarray tuchar k) (sublist 0 k c) p * data_at sh (tarray tuchar (n - k)) (sublist k n c) (offset_val k p).
Proof.
intros sh n k c p Hk Hc Hf. unfold tarray.
rewrite (split2_data_at_Tarray_tuchar sh n k) by auto.
rewrite field_address0_offset.
- simpl nested_field_offset. rewrite Z.mul_1_l, Z.add_0_l. reflexivity.
- destruct Hf as (?&?&?&?&?). repeat split; auto; simpl; try lia.
Qed.

(* a point of a byte array at the end of k readable bytes is weakly valid *)
Lemma lhB_wvp_end : forall sh k (c: list val) p, readable_share sh -> 0 < k ->
  data_at sh (tarray tuchar k) c p |-- weak_valid_pointer (offset_val k p).
Proof.
intros. eapply derives_trans; [apply data_at_memory_block|].
simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

Lemma lhB_wvp_start : forall sh k (c: list val) p, readable_share sh -> 0 < k ->
  data_at sh (tarray tuchar k) c p |-- weak_valid_pointer p.
Proof.
intros. assert_PROP (isptr p) as Hp by (saturate_local; entailer!).
rewrite <- (isptr_offset_val_zero p) at 2 by auto.
eapply derives_trans; [apply data_at_memory_block|].
simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

(* lending the k bytes before a range of m bytes as a witness *)
Lemma lhB_buf_ok1 : forall W shp k (cp: list val) sh p m,
  readable_share shp -> readable_share sh -> 0 <= k -> 0 <= m -> buf_ok W sh (k + m) p ->
  buf_ok (pw_bytes shp k cp p :: W) sh m (offset_val k p).
Proof.
intros W shp k cp sh p m Hr Hrs Hk Hm Hb. unfold buf_ok in *.
unfold pws_pred in *. simpl map. simpl fold_right. unfold pw_pred at 1.
assert_PROP (isptr p) as Hp by (saturate_local; entailer!).
rewrite offset_offset_val.
destruct (Z.eq_dec m 0) as [->|Hm0]; [destruct (Z.eq_dec k 0) as [->|Hk0] |].
- rewrite !Z.add_0_r in *. rewrite !isptr_offset_val_zero in * by auto.
  rewrite sepcon_assoc. apply andp_right; apply sepcon_weak_valid_pointer2;
    (eapply derives_trans; [apply Hb|]); [apply andp_left1 | apply andp_left2]; auto.
- rewrite Z.add_0_r. apply andp_right; do 2 apply sepcon_weak_valid_pointer1; apply lhB_wvp_end; auto; lia.
- unfold data_at_. apply andp_right; apply sepcon_weak_valid_pointer2.
  + apply lhB_wvp_start; auto; lia.
  + rewrite <- offset_offset_val. apply lhB_wvp_end; auto; lia.
Qed.

(* lending the k bytes before and the q bytes after a range of m bytes *)
Lemma lhB_buf_ok3 : forall W shp k (cp: list val) shq q (cq: list val) sh p m,
  readable_share shp -> readable_share shq -> readable_share sh -> 0 <= k -> 0 <= m -> 0 <= q ->
  buf_ok W sh (k + m + q) p ->
  buf_ok (pw_bytes shp k cp p :: pw_bytes shq q cq (offset_val (k + m) p) :: W) sh m (offset_val k p).
Proof.
intros W shp k cp shq q cq sh p m Hr Hrq Hrs Hk Hm Hq Hb. unfold buf_ok in *.
unfold pws_pred in *. cbn [map fold_right pw_pred].
assert_PROP (isptr p) as Hp by (saturate_local; entailer!).
rewrite offset_offset_val.
destruct (Z.eq_dec m 0) as [->|Hm0]; [destruct (Z.eq_dec k 0) as [->|Hk0] |].
- rewrite !Z.add_0_r in *. rewrite !Z.add_0_l in *. rewrite !isptr_offset_val_zero in * by auto.
  destruct (Z.eq_dec q 0) as [->|Hq0].
  + rewrite isptr_offset_val_zero in Hb by auto.
    rewrite !sepcon_assoc. apply andp_right; do 2 apply sepcon_weak_valid_pointer2;
      (eapply derives_trans; [apply Hb|]); [apply andp_left1 | apply andp_left2]; auto.
  + apply andp_right; apply sepcon_weak_valid_pointer1; apply sepcon_weak_valid_pointer2;
      apply sepcon_weak_valid_pointer1; apply lhB_wvp_start; auto; lia.
- rewrite Z.add_0_r. apply andp_right; do 2 apply sepcon_weak_valid_pointer1; apply lhB_wvp_end; auto; lia.
- unfold data_at_. apply andp_right; apply sepcon_weak_valid_pointer2.
  + apply lhB_wvp_start; auto; lia.
  + rewrite <- offset_offset_val. apply lhB_wvp_end; auto; lia.
Qed.

Lemma lhB_buf_ok_cons : forall x W sh n p, buf_ok W sh n p -> buf_ok (x :: W) sh n p.
Proof.
intros x W sh n p Hb. unfold buf_ok in *. unfold pws_pred in *. cbn [map fold_right].
rewrite sepcon_assoc. apply andp_right; apply sepcon_weak_valid_pointer2;
  (eapply derives_trans; [apply Hb|]); [apply andp_left1 | apply andp_left2]; auto.
Qed.

Lemma lhB_pws3 : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 W,
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  pws_pred W = pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: W).
Proof. intros. unfold pws_pred. cbn [map fold_right pw_pred]. apply pred_ext; cancel. Qed.

Lemma lhB_pws3_i : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 W,
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  pws_pred W |-- pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: W).
Proof. intros. rewrite lhB_pws3. auto. Qed.

Lemma lhB_pws3_e : forall sh1 n1 c1 p1 sh2 n2 c2 p2 sh3 n3 c3 p3 W,
  pws_pred (pw_bytes sh1 n1 c1 p1 :: pw_bytes sh2 n2 c2 p2 :: pw_bytes sh3 n3 c3 p3 :: W) |--
  data_at sh1 (tarray tuchar n1) c1 p1 * data_at sh2 (tarray tuchar n2) c2 p2 * data_at sh3 (tarray tuchar n3) c3 p3 *
  pws_pred W.
Proof. intros. rewrite lhB_pws3. auto. Qed.

Lemma lhB_join : forall sh n k m (c1 c2: list val) p q, k = Zlength c1 -> m = Zlength c2 -> n = k + m ->
  q = offset_val k p -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar k) c1 p * data_at sh (tarray tuchar m) c2 q |-- data_at sh (tarray tuchar n) (c1 ++ c2) p.
Proof.
intros sh n k m c1 c2 p q Hk Hm Hn Hq Hf. subst q.
pose proof (Zlength_nonneg c1). pose proof (Zlength_nonneg c2).
rewrite (lhB_arr_split sh n k (c1 ++ c2)) by (auto; rewrite ?Zlength_app; lia).
rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
rewrite sublist_same by lia. replace (n - k) with m by lia.
replace (k - Zlength c1) with 0 by lia. replace (n - Zlength c1) with (Zlength c2) by lia.
rewrite sublist_same by lia. auto.
Qed.

(* a return to any ret_assert (forward only handles a function body's; as lhA_semax_return of piece A) *)
Lemma lhB_semax_return : forall {Espec: OracleKind} Delta P Q R ret v (Post: ret_assert),
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (fun rho => v = eval_expr (Ecast ret (ret_type Delta)) rho) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- tc_expr Delta (Ecast ret (ret_type Delta)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- RA_return Post (Some v) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) (Sreturn (Some ret)) Post.
Proof.
intros Espec Delta P Q R ret v Post H1 H2 H3.
eapply semax_pre; [| apply semax_return].
apply andp_right; [exact H2 |].
apply derives_trans with (local (fun rho => v = eval_expr (Ecast ret (ret_type Delta)) rho) && RA_return Post (Some v)).
{ apply andp_right; auto. }
intro rho. unfold local, lift1, cast_expropt. unfold_lift. simpl.
apply derives_extract_prop; intro Hv. rewrite <- Hv. auto.
Qed.

End CM_LH3Bx_1.

Ltac lhB_return :=
  match goal with |- @semax ?CS _ ?Delta ?Pre (Sreturn (Some ?ret)) _ =>
    let v := fresh "v" in let H := fresh "HRE" in
    do_compute_expr1 CS Delta Pre constr:(Ecast ret (ret_type Delta));
    match goal with v' := _, H':_ |- _ => rename H' into H; rename v' into v end;
    subst v;
    eapply lhB_semax_return; [exact H | entailer_for_return | ]; clear H;
    try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end
  end.

Section CM_LH3Bx_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma lhB_ip_add : forall p i c, isptr p ->
  offset_val (i + c) p =
  force_val (sem_binary_operation' Oadd (tptr tschar) tulong (offset_val i p) (Vlong (Int64.repr c))).
Proof.
intros p i c Hp. destruct p; try contradiction. simpl.
f_equal. rewrite Ptrofs.add_assoc. f_equal. rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
rewrite Int64.unsigned_repr_eq. rewrite ptrofs_add_repr. apply Ptrofs.eqm_samerepr. unfold Ptrofs.eqm.
rewrite Ptrofs.modulus_eq64 by reflexivity. apply Zbits.eqmod_add; [apply Zbits.eqmod_refl|].
apply Zbits.eqmod_mod. reflexivity.
Qed.


(* the frame group but fParams and format *)
Definition lhB_frest (TABS: tabs_pred) (gv: globals) (p: val) (fs: fstate) (t: tabs3) (pr: dparams) (sp: val) : mpred :=
  cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  tabs_rep TABS gv p t *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) sp p.

Lemma lhB_fg_split : forall TABS gv p fs t pr sp, fgroup3 TABS gv p fs t pr sp =
  !! (cold01 fs /\ par_ok pr) &&
  (field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
   field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p *
   lhB_frest TABS gv p fs t pr sp).
Proof. intros. unfold fgroup3, lhB_frest, frame_fields, cfg_fmt. f_equal. apply pred_ext; cancel. Qed.

Lemma lhB_fg_fold : forall TABS gv p fs t pr sp, cold01 fs -> par_ok pr ->
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p *
  lhB_frest TABS gv p fs t pr sp |-- fgroup3 TABS gv p fs t pr sp.
Proof. intros. rewrite lhB_fg_split. apply andp_right; [apply prop_right; auto | auto]. Qed.

(* the frame group but expected (the store of the break) *)
Definition lhB_fgx (TABS: tabs_pred) (gv: globals) (p: val) (fs: fstate) (t: tabs3) (pr: dparams) (sp: val) : mpred :=
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
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  tabs_rep TABS gv p t *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) sp p.

Lemma lhB_fg_exp : forall TABS gv p fs t pr sp, fgroup3 TABS gv p fs t pr sp =
  !! (cold01 fs /\ par_ok pr) &&
  (field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * lhB_fgx TABS gv p fs t pr sp).
Proof. intros. unfold fgroup3, lhB_fgx, frame_fields. f_equal. apply pred_ext; cancel. Qed.

Lemma lhB_dict_rel_uses od d : dict_rel3_of od d -> df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1.
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; auto].
  destruct (dr_src dr); intros H.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as [_ [_ H]]; rewrite H; destruct (dr_once dr); auto.
    + destruct H as [_ [_ [H _]]]; rewrite H; destruct (dr_once dr); auto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as [? [? [? [_ [_ [H _]]]]]]; rewrite H; auto.
  - destruct H as [_ [_ [_ [_ [_ [H _]]]]]]; rewrite H; auto.
Qed.

Lemma lhB_dict_rel_ddict od d : dict_rel3_of od d -> df_uses d <> 0 -> is_pointer_or_null (df_ddict d).
Proof.
  unfold dict_rel3_of. destruct od as [dr | ]; [ | intros [H _]; rewrite H; congruence].
  destruct (dr_src dr) as [pk | | q dd]; intros H Hu.
  - destruct (Zlength (dr_bytes dr) =? 0).
    + destruct H as [_ [H _]]; rewrite H; simpl; auto.
    + destruct H as [Hp [H _]]; rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as [_ H]. destruct (Zlength (dr_bytes dr) =? 0).
    + subst d; simpl; auto.
    + destruct H as [? [? [? [Hp [H _]]]]]; rewrite H; destruct (df_local d); simpl in *; tauto.
  - destruct H as [_ [_ [Hp [_ [H _]]]]]; rewrite H; destruct q; simpl in *; tauto.
Qed.

Lemma lhB_hset_isptr : forall am sp l hb tbl, hset_t am sp l hb tbl |-- !! Forall (fun e => isptr (fst e)) l.
Proof.
  intros. unfold hset_t, hset_tbl. destruct (eq_dec sp nullval).
  - entailer!.
  - Intros tp. entailer!. match goal with H: hs_inv _ _ |- _ => destruct H as (_&_&_&_&_&Hf&_) end. auto.
Qed.

(* ZSTD_getDDict's precondition from the dictionary relation *)
Lemma lhB_getddict_pre : forall st d, dict_rel3 st d -> Forall (fun e => isptr (fst e)) (dc_set st) ->
  (df_uses d = -1 \/ df_uses d = 0 \/ df_uses d = 1) /\ (df_uses d <> 0 -> is_pointer_or_null (df_ddict d)).
Proof.
  intros st d Hd Hp. destruct Hd as [Hd | [Hn [Hl [Hu [Hlx Hin]]]]].
  - split; [apply (lhB_dict_rel_uses _ _ Hd) | apply (lhB_dict_rel_ddict _ _ Hd)].
  - split; [auto | intros _].
    apply in_map_iff in Hin. destruct Hin as [e [E Hin]].
    rewrite Forall_forall in Hp. specialize (Hp e Hin). rewrite E in Hp.
    destruct (df_ddict d); simpl in *; tauto.
Qed.

Lemma lhB_sddict_cons : forall x W dd, sddict_ok W dd -> sddict_ok (x :: W) dd.
Proof.
  intros x W dd H. unfold sddict_ok in *. destruct (dd_ref dd); auto.
  destruct H as [H1 H2]. split; auto. unfold pws_pred in *. cbn [map fold_right].
  apply sepcon_valid_pointer2. auto.
Qed.

Lemma lhB_stream_dict_ok_cons : forall x W st, stream_dict_ok W st -> stream_dict_ok (x :: W) st.
Proof.
  intros x W st (H1 & H2 & H3). unfold stream_dict_ok. split; [|split; auto].
  - destruct (dc_dict st) as [d|]; auto. destruct H1 as [H1 H1']. split; auto.
    destruct (dr_src d); auto. apply lhB_sddict_cons; auto.
  - eapply Forall_impl; [|exact H2]. intros e He. apply lhB_sddict_cons; auto.
Qed.

Lemma lhB_sel_res_off : forall DENT gv p pr sp d l tbl xq, sel_on pr sp = false ->
  sel_res DENT gv p pr sp d l tbl xq = emp.
Proof. intros. unfold sel_res. rewrite H. auto. Qed.

Lemma lhB_hset_fold : forall am sp l hb tbl, hset_t am sp l hb tbl |-- hset_rep am sp l hb.
Proof. intros. rewrite hset_rep_t. Exists tbl. auto. Qed.

End CM_LH3Bx_2.
