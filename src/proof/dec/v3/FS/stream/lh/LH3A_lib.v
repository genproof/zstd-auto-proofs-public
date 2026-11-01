(* FS3 streaming, case zdss_loadHeader, piece A: plain facts and tactics (from v2's StreamSeg_lhA.v). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3A_lib_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- plain facts ---------- *)

Lemma a3_fhd_le : forall d, fhd_header_size d <= 18.
Proof.
intros d. unfold fhd_header_size. cbv zeta.
set (ss := Z.land (Z.shiftr d 5) 1).
assert (Hss: 0 <= ss <= 1).
{ subst ss. replace (Z.land (Z.shiftr d 5) 1) with (Z.shiftr d 5 mod 2)
    by (rewrite <- (Z.land_ones _ 1) by lia; reflexivity).
  pose proof (Z.mod_pos_bound (Z.shiftr d 5) 2). lia. }
assert (H1: forall n, nth n [0; 1; 2; 4] 0 <= 4) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia).
assert (H2: forall n, nth n [0; 2; 4; 8] 0 <= 8) by (intros [|[|[|[|n]]]]; simpl; try lia; destruct n; simpl; lia).
specialize (H1 (Z.to_nat (Z.land d 3))). specialize (H2 (Z.to_nat (Z.shiftr d 6))).
set (n1 := nth (Z.to_nat (Z.land d 3)) [0; 1; 2; 4] 0) in *.
set (n2 := nth (Z.to_nat (Z.shiftr d 6)) [0; 2; 4; 8] 0) in *.
assert (0 <= n1) by (subst n1; destruct (Z.to_nat (Z.land d 3)) as [|[|[|[|[|]]]]]; simpl; lia).
assert (0 <= n2) by (subst n2; destruct (Z.to_nat (Z.shiftr d 6)) as [|[|[|[|[|]]]]]; simpl; lia).
clearbody ss n1 n2.
destruct (Z.eqb_spec ss 1); destruct (Z.shiftr d 6 =? 0); simpl; lia.
Qed.

Lemma a3_more : forall s k, get_frame_header s = FH_more k -> Zlength s < k <= 18.
Proof.
intros s k H. unfold get_frame_header in H.
destruct (Zlength s <? 5) eqn:E5.
- apply Z.ltb_lt in E5.
  destruct (Zlength s >? 0); [destruct (andb _ _) |]; inversion H; subst; lia.
- apply Z.ltb_ge in E5.
  destruct (negb (le_field s 0 4 =? ZSTD_MAGICNUMBER)).
  + destruct (is_skippable_magic (le_field s 0 4)); [|discriminate].
    destruct (Zlength s <? ZSTD_SKIPPABLEHEADERSIZE) eqn:E8; inversion H; subst.
    apply Z.ltb_lt in E8. unfold ZSTD_SKIPPABLEHEADERSIZE in *. lia.
  + destruct (Zlength s <? fhd_header_size (byte_at s 4)) eqn:Eh.
    * inversion H; subst. apply Z.ltb_lt in Eh. split; [lia | apply a3_fhd_le].
    * repeat match type of H with
             | context [if ?b then _ else _] => destruct b
             end; discriminate.
Qed.

Lemma a3_small_noerr : forall x, 0 <= x <= 18 -> is_error_code x = false.
Proof. intros x Hx. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma a3_splice_nil : forall c n, Zlength c = 18 -> 0 <= n <= 18 -> hb_splice c n [] = c.
Proof.
intros c n Hc Hn. unfold hb_splice. rewrite Zlength_nil, Z.add_0_r. simpl.
rewrite <- Hc, <- sublist_split by lia. apply sublist_same; lia.
Qed.

Lemma a3_splice_len : forall c n u, Zlength c = 18 -> 0 <= n -> n + Zlength u <= 18 ->
  Zlength (hb_splice c n u) = 18.
Proof.
intros c n u Hc Hn Hu. unfold hb_splice.
pose proof (Zlength_nonneg u).
rewrite !Zlength_app, Zlength_map, !Zlength_sublist by lia. lia.
Qed.

Lemma a3_splice_pre : forall c hb u, Zlength c = 18 -> Zlength hb + Zlength u <= 18 ->
  sublist 0 (Zlength hb) c = zbytes hb ->
  sublist 0 (Zlength hb + Zlength u) (hb_splice c (Zlength hb) u) = zbytes (hb ++ u).
Proof.
intros c hb u Hc Hu Hs. unfold hb_splice.
pose proof (Zlength_nonneg u). pose proof (Zlength_nonneg hb).
rewrite Hs, map_app, app_assoc.
rewrite sublist_app1; [| lia | rewrite Zlength_app, !Zlength_map; lia].
apply sublist_same; [lia | rewrite Zlength_app, !Zlength_map; lia].
Qed.

Lemma a3_split3 : forall {cs: compspecs} sh N lo hi (c: list val) q,
  0 <= lo <= hi -> hi <= N -> Zlength c = N -> field_compatible (tarray tuchar N) [] q ->
  data_at sh (tarray tuchar N) c q =
  data_at sh (tarray tuchar lo) (sublist 0 lo c) q *
  data_at sh (tarray tuchar (hi - lo)) (sublist lo hi c) (offset_val lo q) *
  data_at sh (tarray tuchar (N - hi)) (sublist hi N c) (offset_val hi q).
Proof.
intros cs sh N lo hi c q Hl Hh Hc Hf. unfold tarray.
rewrite (split3_data_at_Tarray_tuchar sh N lo hi) by lia.
rewrite !field_address0_offset by auto with field_compatible.
simpl. rewrite !Z.mul_1_l, !Z.add_0_l. reflexivity.
Qed.


Lemma a3_psub : forall q i j, isptr q -> 0 <= j <= i -> i <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub (tptr tschar) (tptr tschar) (offset_val i q) (offset_val j q)) =
  Vlong (Int64.repr (i - j)).
Proof.
intros q i j Hq Hij Hi. destruct q; try contradiction.
unfold sem_binary_operation', sem_sub, sem_sub_pp, offset_val. simpl.
rewrite peq_true. simpl.
rewrite (Ptrofs.add_commut i0 (Ptrofs.repr i)), (Ptrofs.add_commut i0 (Ptrofs.repr j)), Ptrofs.sub_shifted.
unfold Vptrofs. simpl. f_equal. unfold Ptrofs.to_int64.
unfold Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia.
unfold Ptrofs.divs. rewrite (Ptrofs.signed_repr 1) by rep_lia. rewrite Z.quot_1_r, Ptrofs.repr_signed.
rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma a3_sub64 : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.sub (Int64.repr x) (Int64.repr y) = Int64.repr (x - y).
Proof. intros. unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma a3_splice_parts : forall c n u, Zlength c = 18 -> 0 <= n -> n + Zlength u <= 18 ->
  sublist 0 n (hb_splice c n u) = sublist 0 n c /\
  sublist n (n + Zlength u) (hb_splice c n u) = zbytes u /\
  sublist (n + Zlength u) 18 (hb_splice c n u) = sublist (n + Zlength u) 18 c.
Proof.
intros c n u Hc Hn Hu. pose proof (Zlength_nonneg u). unfold hb_splice.
split3; list_solve.
Qed.

Lemma a3_add64 : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y).
Proof. intros. unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma a3_hb_split : forall {cs: compspecs} sh (c: list val) q L (bs: list Z),
  Zlength c = 18 -> 0 <= L <= 18 -> sublist 0 L c = zbytes bs -> Zlength bs = L ->
  field_compatible (tarray tuchar 18) [] q ->
  data_at sh (tarray tuchar 18) c q =
  data_at sh (tarray tuchar (Zlength bs)) (zbytes bs) q *
  data_at sh (tarray tuchar (18 - L)) (sublist L 18 c) (offset_val L q).
Proof.
intros cs sh c q L bs Hc HL Hs Hb Hf. unfold tarray.
rewrite (split2_data_at_Tarray_tuchar sh 18 L) by lia.
rewrite field_address0_offset by auto with field_compatible.
simpl. rewrite Z.mul_1_l, Z.add_0_l, Hs, Hb. reflexivity.
Qed.

Lemma a3_padd : forall q i n, isptr q -> 0 <= n <= Int64.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tschar) tulong (offset_val i q) (Vlong (Int64.repr n))) =
  offset_val (i + n) q.
Proof.
intros q i n Hq Hn. destruct q; try contradiction.
simpl. unfold sem_add_ptr_long. simpl. f_equal.
change (Ptrofs.repr 1) with Ptrofs.one. rewrite Ptrofs.mul_commut, Ptrofs.mul_one.
unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
rewrite Ptrofs.add_assoc, ptrofs_add_repr. reflexivity.
Qed.

Lemma a3_fp_eq : forall sh v q,
  data_at sh t_fh v (field_address t_dctx (DOT _fParams) q) = field_at sh t_dctx (DOT _fParams) v q.
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

Lemma a3_hb_eq : forall sh c q,
  data_at sh (tarray tuchar 18) c (field_address t_dctx (DOT _headerBuffer) q) =
  field_at sh t_dctx (DOT _headerBuffer) c q.
Proof. intros. rewrite field_at_data_at. reflexivity. Qed.

(* a return to any ret_assert (forward only handles a function body's) *)
Lemma a3_semax_return : forall {Espec: OracleKind} Delta P Q R ret v (Post: ret_assert),
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

End CM_LH3A_lib_1.

Ltac a3_return :=
  match goal with |- @semax ?CS _ ?Delta ?Pre (Sreturn (Some ?ret)) _ =>
    let v := fresh "v" in let H := fresh "HRE" in
    do_compute_expr1 CS Delta Pre constr:(Ecast ret (ret_type Delta));
    match goal with v' := _, H':_ |- _ => rename H' into H; rename v' into v end;
    subst v;
    eapply a3_semax_return; [exact H | entailer_for_return | ]; clear H;
    try match goal with Post := _ : ret_assert |- _ => subst Post; unfold abbreviate end
  end.

Section CM_LH3A_lib_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma a3_xxh_fp : forall f x, fs_xxh (fsu_fParams f x) = fs_xxh f.
Proof. reflexivity. Qed.

End CM_LH3A_lib_2.

Ltac a3_absurd := Intros; first [contradiction | discriminate | (exfalso; lia)].

Ltac a3_skip_loop2 :=
  repeat apply -> seq_assoc;
  match goal with |- semax _ ?P (Ssequence (Sloop _ Sbreak) _) _ =>
    forward_loop P break: P;
      [apply ENTAIL_refl
      | match goal with |- semax _ ?Q _ _ => forward_if Q end;
        [a3_absurd | forward; apply ENTAIL_refl | forward; apply ENTAIL_refl]
      | ]
  end.

Ltac a3_skip_loop :=
  repeat apply -> seq_assoc;
  match goal with |- semax _ ?P (Ssequence (Sloop Sskip Sbreak) _) _ =>
    forward_loop P break: P; [apply ENTAIL_refl | forward; apply ENTAIL_refl | ]
  end.

Section CM_LH3A_lib_3.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma a3_more_m : forall mg s k, get_frame_header_m mg s = FH_more k -> Zlength s < k <= 18.
Proof.
intros mg s k H. unfold get_frame_header_m in H. destruct mg; cbv [negb] in H.
- destruct (Zlength s <? 1) eqn:E1.
  + inversion H; subst. apply Z.ltb_lt in E1. lia.
  + destruct (get_frame_header (magic_bytes ++ s)) eqn:E; try discriminate; inversion H; subst.
    apply a3_more in E. rewrite Zlength_app in E.
    assert (Zlength magic_bytes = 4) by reflexivity. lia.
- apply a3_more; auto.
Qed.

(* ---------- the frame fields and the stream fields with the fields piece A touches taken out ---------- *)

Definition ff_rest (p: val) (fs: fstate) : mpred :=
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
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma ff_split (p: val) (fs: fstate) :
  frame_fields p fs = field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p * ff_rest p fs.
Proof. unfold frame_fields, ff_rest. apply pred_ext; cancel. Qed.

Definition sg_props (s: sfields) : Prop :=
  0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
  Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
  0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
  (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
  (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s).

Definition sg_rest (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
  ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
  mgroup (sf_mem s) p (sf_given s).

(* sg_rest without the allocator's group (mgroup), whose byte count changes when the local DDict is freed *)
Definition sg_rest0 (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
  ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s).

Lemma sg_rest_0 (p: val) (s: sfields) : sg_rest p s = sg_rest0 p s * mgroup (sf_mem s) p (sf_given s).
Proof. reflexivity. Qed.

(* the stream fields after the local DDict changed (LH3Defs.held_redict): only the count of held bytes moved *)
Lemma sg_rest0_redict (p: val) (s: sfields) (d d1: dfields) : sg_rest0 p (held_redict s d d1) = sg_rest0 p s.
Proof. reflexivity. Qed.

Lemma hr_lh (s: sfields) (d d1: dfields) : sf_lhSize (held_redict s d d1) = sf_lhSize s.
Proof. reflexivity. Qed.
Lemma hr_hbuf (s: sfields) (d d1: dfields) : sf_hbuf (held_redict s d d1) = sf_hbuf s.
Proof. reflexivity. Qed.
Lemma hr_mem (s: sfields) (d d1: dfields) : sf_mem (held_redict s d d1) = sf_mem s.
Proof. reflexivity. Qed.

Lemma sg_props_redict (s: sfields) (d d1: dfields) :
  sg_props s -> 0 <= sf_held s - local_held d -> sg_props (held_redict s d d1).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) Hh. pose proof (local_held_nonneg d1).
  unfold sg_props, held_redict, sf_with_held; cbn [sf_inSize sf_outSize sf_stage sf_nfp sf_over sf_hbuf sf_ring
    sf_inBuff sf_outBuff sf_held].
  split3; [exact H1 | exact H2 |]. split3; [exact H3 | exact H4 |]. split3; [exact H5 | exact H6 |].
  split3; [exact H7 | exact H8 |]. split3; [exact H9 | lia | exact H11].
Qed.

(* k_A with the selection off: the dictionary fields and the held bytes unchanged *)
Lemma kA_off (k: cst3) (v: reptype t_fh) (did1: val) :
  k_A k v (c3_dict k) did1 = c3_with_fs k (fsu_dictID (fsu_fParams (c3_fs k) v) did1) (c3_tabs k).
Proof. unfold k_A. exact (k_redict_same _). Qed.

Lemma sg_split (p: val) (s: sfields) :
  sgroup p s = !! sg_props s &&
    (field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p * field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
     sg_rest p s).
Proof.
unfold sgroup, sg_props, sg_rest. f_equal. apply pred_ext; cancel.
Qed.

Lemma fsu_dictID_same (fs: fstate) : fsu_dictID fs (fs_dictID fs) = fs.
Proof. destruct fs; reflexivity. Qed.

(* fParams' dictID after getFrameHeader_advanced *)
Lemma a3_fp_id : forall mg s r v0 v, GAP_fherr -> fh_post_m mg s r v0 v -> fp_id_ok v0 -> fp_id_ok v.
Proof.
intros mg s r v0 v Hg Hp H0.
destruct (get_frame_header_m mg s) eqn:E.
- eapply Hg; eauto.
- unfold fh_post_m in Hp. rewrite E in Hp. destruct Hp as [_ ->].
  destruct (Zlength s <? starting_len mg); auto.
  exists 0. split; [reflexivity | rep_lia].
- unfold fh_post_m in Hp. rewrite E in Hp. destruct Hp as [_ ->].
  exists (Int.unsigned (Int.repr (fh_dictID h))). split; [| rep_lia].
  unfold fp_dictID, fh_val; simpl. rewrite Int.repr_unsigned. reflexivity.
Qed.

Lemma a3_sel_on : forall k hb r v tbl id,
  sel_on (c3_par k) (c3_sp k) = true -> 0 <= r <= Int64.max_unsigned ->
  fh_post_m (lh_mg k) hb r (fs_fParams (c3_fs k)) v -> fp_dictID v = Vint (Int.repr id) ->
  0 <= id <= Int.max_unsigned -> hs_inv (c3_set k) tbl ->
  lhA_sel k hb r v tbl (sel_dict (c3_dict k) (sel_r (c3_dict k) (c3_set k) tbl id))
    (if eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval then fs_dictID (c3_fs k)
     else Vint (Int.repr id)).
Proof.
intros k hb r v tbl id Hon Hr Hp Hi Hid Hinv.
split; [auto | split; [auto |]].
exists id. split; [intros _; auto |].
unfold sel_by. rewrite Hon. split; [auto | split; [auto | split; reflexivity]].
Qed.

(* lhA_sel with the selection off *)
Lemma a3_sel_off : forall k hb r v tbl,
  sel_on (c3_par k) (c3_sp k) = false -> 0 <= r <= Int64.max_unsigned ->
  fh_post_m (lh_mg k) hb r (fs_fParams (c3_fs k)) v ->
  lhA_sel k hb r v tbl (c3_dict k) (fs_dictID (c3_fs k)).
Proof.
intros k hb r v tbl Hoff Hr Hp.
split; [auto | split; [auto |]].
exists 0. split; [intro E; congruence |].
unfold sel_by. rewrite Hoff. split; reflexivity.
Qed.

Lemma ff_fold (p: val) (fs: fstate) (v: reptype t_fh) :
  field_at Ews t_dctx (DOT _fParams) v p * ff_rest p fs |-- frame_fields p (fsu_fParams fs v).
Proof. rewrite (ff_split p (fsu_fParams fs v)). apply derives_refl. Qed.

Lemma fsu_dictID_fp_same (fs: fstate) (v: reptype t_fh) :
  fsu_dictID (fsu_fParams fs v) (fs_dictID fs) = fsu_fParams fs v.
Proof. destruct fs; reflexivity. Qed.

Lemma fsu_dictID_sel (fs: fstate) (v: reptype t_fh) (r: val) (x: val) :
  (if eq_dec r nullval then fsu_fParams fs v else fsu_dictID (fsu_fParams fs v) x) =
  fsu_dictID (fsu_fParams fs v) (if eq_dec r nullval then fs_dictID fs else x).
Proof. destruct (eq_dec r nullval); [rewrite fsu_dictID_fp_same |]; reflexivity. Qed.

(* ---------- the context with piece A's fields taken out ---------- *)

Definition ctxA_rest (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) (tbl: list val) : mpred :=
  dctx_token p * dctx_pad p * cfg_lit p * ff_rest p (c3_fs k) * tabs_rep TABS gv p (c3_tabs k) *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore (c3_par k)))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax (c3_par k)))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi (c3_par k)))) p *
  field_at Ews t_dctx (DOT _ddictSet) (c3_sp k) p *
  cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) * dgroup DENT gv p (c3_dict k) * sg_rest p (c3_s k) *
  hset_t (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k)) tbl.

Definition ctxA_props (k: cst3) : Prop := cold01 (c3_fs k) /\ par_ok (c3_par k) /\ sg_props (c3_s k).

Lemma ctxA_split (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) (tbl: list val) :
  ctx_rep3t DENT TABS gv p k tbl =
  !! ctxA_props k &&
  (field_at Ews t_dctx (DOT _fParams) (fs_fParams (c3_fs k)) p *
   field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt (c3_par k)))) p *
   field_at Ews t_dctx (DOT _lhSize) (sf_lhSize (c3_s k)) p *
   field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf (c3_s k)) p *
   ctxA_rest DENT TABS gv p k tbl).
Proof.
unfold ctx_rep3t, fgroup3, ctxA_rest, ctxA_props, cfg_fmt.
rewrite sg_split, ff_split.
apply pred_ext.
- Intros. entailer!.
- Intros. entailer!.
Qed.

Lemma ctxA_rest_load (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) a w k hb m v' tbl :
  ctxA_rest DENT TABS gv p (lh_k_load a w k hb m v') tbl = ctxA_rest DENT TABS gv p k tbl.
Proof. reflexivity. Qed.

End CM_LH3A_lib_3.
