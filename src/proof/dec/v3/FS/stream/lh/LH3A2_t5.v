(* FS3 streaming, case zdss_loadHeader, piece A: the tail lh_A after the selection, case "the input
   ends inside the header": the hint of a Zstandard frame header (MAX(FRAMEHEADERSIZE_MIN(format), hSize) - lhSize + ZSTD_blockHeaderSize). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3A2_tl.
Local Open Scope logic.

Section CM_LH3A2_t5_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhA_t_hint2 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) r v tbl d1 did1 kq,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
  lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kq ->
  a_isz a - w_ipc w < kq - Zlength hb ->
  get_frame_header_m (lh_mg (w_k w)) (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <> FH_err ->
  andb (negb (lh_mg (w_k w))) (orb (Zlength (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) <? 4)
    (is_skippable_frame (hb ++ sublist (w_ipc w) (a_isz a) (a_ibs a)) =? 1)) = false ->
  GAP_fherr -> fp_ok v ->
  semax (ds_Delta DENT TABS BR) (lhA_mid DENT TABS a w r v tbl d1 did1) lhA_t (lhA_post DENT TABS a w hb).
Proof.
intros Espec DENT TABS BR a w hb r v tbl d1 did1 kk HD HT Ha He Hsel Eg HcB HcC HcD Hfh Hfpv.
pose proof Ha as Ha'.
destruct Ha' as (Hbo & Hbi & _ & Hwso & Hwsi & Hwsob & Hrsb & _ & _ & Hopos & Hosz & Hoclen & Hipos & Hisz & Hibslen & Hibsok & _ & _ & _).
pose proof He as He'.
destruct He' as (Hstage & Hlh & Hhb18 & Hhbok & Hsub & Hhost & Hinpos & Hos & Hoe & Hipc & Hopc & Hoc & Hsmw & Hbc & Hlen).
assert (Hsel' := Hsel). destruct Hsel' as (Hr & Hpost & _).
unfold fh_post_m in Hpost. rewrite Eg in Hpost. destruct Hpost as [-> _].
pose proof (a3_more_m _ _ _ Eg) as Hkk.
assert (Hhbz: 0 <= Zlength hb) by apply Zlength_nonneg.
a3_open.
rewrite Hlh. unfold vlong.
forward_call kk.
rewrite (a3_small_noerr kk) by lia.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx R))) end.
{ a3_absurd. }
{ forward. apply ENTAIL_refl. }
forward_if.
2: { match goal with H: Int64.repr kk = Int64.zero |- _ =>
       change Int64.zero with (Int64.repr 0) in H; apply repr_inj_unsigned64 in H; [lia | rep_lia | rep_lia] end. }
forward. forward.
assert_PROP (isptr (a_ib a)) as Hib by entailer!.
forward.
{ entailer!.
  apply prop_right; destruct (a_ib a); try contradiction; unfold sameblock; simpl;
    destruct (peq b b); [auto | congruence]. }
rewrite (a3_psub (a_ib a) (a_isz a) (w_ipc w)) by (auto; rep_lia).
rewrite a3_sub64 by rep_lia.
set (m := a_isz a - w_ipc w).
set (u := sublist (w_ipc w) (a_isz a) (a_ibs a)) in *.
assert (Hu: Zlength u = m) by (unfold u, m; rewrite Zlength_sublist; lia).
assert (Hhb18': Zlength (sf_hbuf (c3_s (w_k w))) = 18)
  by (destruct H as (_ & _ & Hsg); unfold sg_props in Hsg; tauto).
forward_if.
2: { repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
       rewrite (Int64.unsigned_repr x) in H by rep_lia end.
     match goal with H: m >= kk - Zlength hb |- _ =>
       exfalso; assert (m = a_isz a - w_ipc w) by reflexivity; lia end. }
(* the input ends inside the header *)
match goal with H: m < kk - Zlength hb |- _ => rename H into Hlt end.
assert_PROP (field_compatible t_dctx (DOT _headerBuffer) (a_d a) /\ field_compatible t_dctx (DOT _fParams) (a_d a))
  as Hfc by entailer!.
destruct Hfc as [Hfc2 Hfc1].
rewrite (field_at_data_at Ews t_dctx (DOT _headerBuffer)), (field_at_data_at Ews t_dctx (DOT _fParams)).
simpl nested_field_type.
assert_PROP (field_compatible (tarray tuchar 18) [] (field_address t_dctx (DOT _headerBuffer) (a_d a)) /\
             field_compatible (tarray tuchar (a_isz a)) [] (a_ib a)) as Hfc3 by entailer!.
destruct Hfc3 as [Hfc3 Hfc4].
freeze FR2 := - (data_at _ (tarray tuchar 18) _ _) (field_at _ _ (DOT _lhSize) _ _)
  (data_at _ (tarray tuchar (a_isz a)) _ _).
match goal with |- semax _ (PROPx ?P (LOCALx ?Q _)) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx [FRZL FR2;
    data_at Ews (tarray tuchar 18) (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)
      (field_address t_dctx (DOT _headerBuffer) (a_d a));
    field_at Ews t_dctx (DOT _lhSize) (Vlong (Int64.repr (Zlength hb + m))) (a_d a);
    data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)]))) end.
{ forward.
  rewrite (a3_split3 Ews 18 (Zlength hb) (Zlength hb + m) (sf_hbuf (c3_s (w_k w)))) by (auto; lia).
  rewrite (a3_split3 (a_shb a) (a_isz a) (w_ipc w) (a_isz a) (zbytes (a_ibs a))) by (auto; rewrite ?Zlength_map; lia).
  Intros.
  replace (Zlength hb + m - Zlength hb) with m by lia.
  replace (a_isz a - w_ipc w) with m by reflexivity.
  sep_apply (data_at_data_at_ Ews (tarray tuchar m) (sublist (Zlength hb) (Zlength hb + m) (sf_hbuf (c3_s (w_k w))))
               (offset_val (Zlength hb) (field_address t_dctx (DOT _headerBuffer) (a_d a)))).
  forward_call (a_shb a, Ews, offset_val (w_ipc w) (a_ib a),
                offset_val (Zlength hb) (field_address t_dctx (DOT _headerBuffer) (a_d a)),
                existT (fun t => reptype t) (tarray tuchar m) (sublist (w_ipc w) (a_isz a) (zbytes (a_ibs a)))).
  { apply prop_right. unfold field_address; rewrite if_true by auto.
    destruct (a_d a); try (destruct Hfc2; contradiction). destruct (a_ib a); try contradiction.
    simpl. rewrite Z.max_r by lia. rewrite Z.mul_1_l. change (Ptrofs.repr 1) with Ptrofs.one.
    rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
    rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  1: lazymatch goal with |- semax _ _ _ _ => idtac | _ =>
    (* the size, and the copied input bytes are defined *)
    cbn [projT1 projT2]; split; [simpl; rewrite Z.max_r by lia; rep_lia |];
    apply memcpy_ok_bytes; [list_solve | apply byte_val_sublist, byte_val_zbytes; exact Hibsok] end.
  forward. forward.
  rewrite a3_add64 by rep_lia.
  destruct (a3_splice_parts (sf_hbuf (c3_s (w_k w))) (Zlength hb) u ltac:(assumption) Hhbz) as (E1 & E2 & E3); [lia |].
  rewrite Hu in E2, E3.
  rewrite (a3_split3 Ews 18 (Zlength hb) (Zlength hb + m)
             (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)) by (auto; try lia; apply a3_splice_len; lia).
  rewrite E1, E2, E3.
  rewrite (a3_split3 (a_shb a) (a_isz a) (w_ipc w) (a_isz a) (zbytes (a_ibs a))) by (auto; rewrite ?Zlength_map; lia).
  replace (Zlength hb + m - Zlength hb) with m by lia.
  unfold u. rewrite sublist_map.
  simpl RA_normal. entailer!. }
{ forward.
  match goal with H: Int64.unsigned (Int64.repr 0) >= Int64.unsigned (Int64.repr m) |- _ =>
    rewrite !Int64.unsigned_repr in H by rep_lia end.
  assert (Hm0: m = 0) by lia.
  assert (Hu0: u = []) by (apply Zlength_nil_inv; lia).
  rewrite Hu0, a3_splice_nil by (auto; lia).
  replace (Zlength hb + m) with (Zlength hb) by lia.
  simpl RA_normal. entailer!. }
thaw FR2.
forward. forward.
assert (Hhb'len: Zlength (hb ++ u) = Zlength hb + m) by (rewrite Zlength_app; lia).
assert (Hc'len: Zlength (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u) = 18)
  by (apply a3_splice_len; lia).
assert (Hhb'ok: bytes_ok (hb ++ u)).
{ unfold bytes_ok in *. apply Forall_app. split; auto. unfold u. apply Forall_sublist; auto. }
assert (Hw2: win_ok Ews 18 (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u) 0 (Zlength (hb ++ u)) (hb ++ u)).
{ unfold win_ok. rewrite Z.add_0_l, Hhb'len. repeat split; auto; try lia; auto with share.
  rewrite <- Hu. apply a3_splice_pre; auto; lia. }
assert (Hfmt: dp_fmt (c3_par (w_k w)) = 0 \/ dp_fmt (c3_par (w_k w)) = 1)
  by (destruct H as (_ & Hpar & _); unfold par_ok in Hpar; tauto).
freeze [0; 1; 2; 6; 7; 8; 9; 10; 11; 14] FR3.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_loop (PROPx P (LOCALx Q (SEPx R)))
    break: (EX r2: Z, EX v2: reptype t_fh,
      PROPx ((0 <= r2 <= Int64.max_unsigned) :: fh_post_m (lh_mg (w_k w)) (hb ++ u) r2 v v2 :: (is_error_code r2 = false) :: P)
      (LOCALx Q (SEPx [FRZL FR3; zstd_globals (a_gv a);
         data_at Ews t_fh v2 (field_address t_dctx (DOT _fParams) (a_d a));
         field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt (c3_par (w_k w))))) (a_d a);
         data_at Ews (tarray tuchar 18) (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)
           (field_address t_dctx (DOT _headerBuffer) (a_d a));
         field_at Ews t_dctx (DOT _lhSize) (Vlong (Int64.repr (Zlength hb + m))) (a_d a)])))%assert
end.
{ apply ENTAIL_refl. }
{ forward. forward.
  rewrite <- Hhb'len.
  forward_call (a_gv a, Ews, field_address t_dctx (DOT _fParams) (a_d a), v, Ews,
                field_address t_dctx (DOT _headerBuffer) (a_d a), 18,
                hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u, 0, hb ++ u, dp_fmt (c3_par (w_k w))).
  Intros vret. destruct vret as [r2 v2]. cbv [fst snd] in *.
  match goal with H: fh_post_m _ _ _ _ _ |- _ => rename H into Hpost2 end.
  change (fmt_mg (dp_fmt (c3_par (w_k w)))) with (lh_mg (w_k w)) in Hpost2.
  forward.
  forward_call r2.
  destruct (is_error_code r2) eqn:Er2.
  - exfalso. apply HcC. unfold fh_post_m in Hpost2. destruct (get_frame_header_m (lh_mg (w_k w)) (hb ++ u)) eqn:E2; auto.
    + destruct Hpost2 as [Hpost2 _]. subst r2. pose proof (a3_more_m _ _ _ E2). rewrite a3_small_noerr in Er2 by lia. discriminate.
    + destruct Hpost2 as [-> _]. discriminate.
  - forward_if.
    { a3_absurd. }
    forward.
    rewrite Hhb'len. Exists r2 v2. entailer!. }
Intros r2 v2.
match goal with H: fh_post_m _ _ _ _ _ |- _ => rename H into Hpost3 end.
match goal with H: is_error_code r2 = false |- _ => rename H into Er3 end.
rewrite <- Hhb'len.
forward.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'18 (Vint (Int.repr
    (if andb (negb (lh_mg (w_k w))) (orb (Zlength (hb ++ u) <? 4) (is_skippable_frame (hb ++ u) =? 1))
     then 1 else 0))) :: Q) (SEPx R))) end.
{ assert (Hmg0: lh_mg (w_k w) = false).
  { unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [reflexivity | exfalso; lia]. }
  forward.
  forward_if.
  { match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
    forward. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    simpl RA_normal. rewrite Hmg0; simpl andb. entailer!. }
  match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
  forward.
  rewrite (a3_hb_split Ews (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)
             (field_address t_dctx (DOT _headerBuffer) (a_d a)) (Zlength (hb ++ u)) (hb ++ u))
    by (auto; try lia; rewrite Hhb'len, <- Hu; apply a3_splice_pre; auto; lia).
  Intros.
  forward_call (Ews, field_address t_dctx (DOT _headerBuffer) (a_d a), hb ++ u).
  { unfold src_spec_pre. split3; auto with share. lia. }
  forward. forward.
  rewrite (a3_hb_split Ews (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u)
             (field_address t_dctx (DOT _headerBuffer) (a_d a)) (Zlength (hb ++ u)) (hb ++ u))
    by (auto; try lia; rewrite Hhb'len, <- Hu; apply a3_splice_pre; auto; lia).
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  simpl RA_normal. rewrite Hmg0; simpl andb.
  entailer!.
  unfold is_skippable_frame. destruct (Zlength (hb ++ u) <? 4); [| destruct (is_skippable_magic _)]; reflexivity. }
{ assert (Hmg1: lh_mg (w_k w) = true).
  { unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [exfalso; lia | reflexivity]. }
  forward. simpl RA_normal. rewrite Hmg1. entailer!. }
rewrite HcD.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx Q (SEPx R))) end.
{ a3_absurd. }
{ forward. apply ENTAIL_refl. }
assert (Hsu: sublist (w_ipc w) (w_ipc w + (a_isz a - w_ipc w)) (a_ibs a) = u) by (unfold u; f_equal; lia).
remember (if lh_mg (w_k w) then 2 else 6) as fm eqn:Efm.
assert (Hfm: fm = 2 \/ fm = 6) by (destruct (lh_mg (w_k w)); auto).
assert (Hfms: Int.signed (Int.repr fm) = fm) by (apply Int.signed_repr; destruct Hfm; subst; rep_lia).
forward.
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'20 (Vint (Int.repr fm)) :: Q) (SEPx R))) end.
{ forward. subst fm. unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [| exfalso; lia].
  simpl RA_normal. entailer!. }
{ forward. subst fm. unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [exfalso; lia |].
  simpl RA_normal. entailer!. }
match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'21 (Vlong (Int64.repr (Z.max fm kk))) :: Q) (SEPx R))) end.
{ forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'22 (Vint (Int.repr fm)) :: Q) (SEPx R))) end.
  { forward. subst fm. unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [| exfalso; lia].
    simpl RA_normal. entailer!. }
  { forward. subst fm. unfold lh_mg. destruct Hfmt as [E|E]; rewrite E in *; [exfalso; lia |].
    simpl RA_normal. entailer!. }
  forward.
  try rewrite Hfms in *.
  repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
    rewrite (Int64.unsigned_repr x) in H by (destruct Hfm; subst; rep_lia) end.
  rewrite Z.max_l by lia.
  simpl RA_normal. entailer!. }
{ forward.
  try rewrite Hfms in *.
  repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
    rewrite (Int64.unsigned_repr x) in H by (destruct Hfm; subst; rep_lia) end.
  rewrite Z.max_r by lia.
  simpl RA_normal. entailer!. }
forward.
repeat apply -> seq_assoc.
unfold zstd_globals. Intros.
forward.
try (apply semax_seq with (Q := FF); [| apply semax_ff]).
a3_return.
cbv beta iota delta [overridePost lhA_post RA_return lh_ret].
unfold ZSTD_blockHeaderSize_val.
assert (Hmx: 0 <= Z.max fm kk - Zlength (hb ++ u) <= 18) by (destruct Hfm; subst; lia).
change (force_val (both_long _ _ _ (Vlong ?x) (Vlong ?y))) with (Vlong (Int64.add x y)).
rewrite a3_sub64, a3_add64 by rep_lia.
assert (Hhint: lh_hint (lh_mg (w_k w)) (hb ++ u) kk = Z.max fm kk - Zlength (hb ++ u) + 3)
  by (unfold lh_hint; rewrite HcD; subst fm; reflexivity).
assert (Hfpv2: fp_ok v2) by (match goal with H: fh_post_m _ _ _ _ v2 |- _ => exact (a3_fp_id _ _ _ _ _ Hfh H Hfpv) end).
assert (Hrc: lh_rc a w hb (lh_hint (lh_mg (w_k w)) (hb ++ u) kk) (a_isz a)
               (lw_k w (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v2)))
  by (apply (RC_hint a w hb kk v tbl d1 did1 r2 v2); auto).
rewrite Hhint in Hrc.
Exists (Z.max fm kk - Zlength (hb ++ u) + 3) (a_isz a)
       (lw_k w (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v2)).
thaw FR3.
unfold ds_S_ip, ds_LI_L. rewrite ctx_rep3_t. Exists tbl. rewrite ctxA_split.
a3_rw. a3_rwL. rewrite Hsu.
assert (Hprops: ctxA_props (lh_k_load a w (k_A (w_k w) v d1 did1) hb (a_isz a - w_ipc w) v2))
  by (apply kL_props; auto; rewrite Hsu; auto).
rewrite a3_fp_eq, a3_hb_eq. unfold vlong, zstd_globals.
rewrite Hhb'len in *.
entailer!.
Qed.

End CM_LH3A2_t5_1.
