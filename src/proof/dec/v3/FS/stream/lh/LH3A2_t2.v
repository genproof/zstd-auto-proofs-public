(* FS3 streaming, case zdss_loadHeader, piece A: the tail lh_A after the selection, case "the header
   needs more bytes, all within the input" (the break). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3A2_tl.
Local Open Scope logic.

Section CM_LH3A2_t2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lhA_t_brk : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) r v tbl d1 did1 kq,
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb ->
  lhA_sel (w_k w) hb r v tbl d1 did1 -> get_frame_header_m (lh_mg (w_k w)) hb = FH_more kq ->
  kq - Zlength hb <= a_isz a - w_ipc w ->
  semax (ds_Delta DENT TABS BR) (lhA_mid DENT TABS a w r v tbl d1 did1) lhA_t (lhA_post DENT TABS a w hb).
Proof.
intros Espec DENT TABS BR a w hb r v tbl d1 did1 kk HD HT Ha He Hsel Eg HcB.
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
forward_if.
{ match goal with H: m < kk - Zlength hb |- _ =>
    exfalso; assert (m = a_isz a - w_ipc w) by reflexivity; lia end. }
(* the header is complete within the input *)
repeat match goal with H: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
  rewrite (Int64.unsigned_repr x) in H by rep_lia end.
match goal with H: m >= kk - Zlength hb |- _ => rename H into Hge end.
assert (Hhb18': Zlength (sf_hbuf (c3_s (w_k w))) = 18)
  by (destruct H as (_ & _ & Hsg); unfold sg_props in Hsg; tauto).
assert_PROP (field_compatible t_dctx (DOT _headerBuffer) (a_d a)) as Hfc2 by entailer!.
rewrite (field_at_data_at Ews t_dctx (DOT _headerBuffer)). simpl nested_field_type.
assert_PROP (field_compatible (tarray tuchar 18) [] (field_address t_dctx (DOT _headerBuffer) (a_d a)) /\
             field_compatible (tarray tuchar (a_isz a)) [] (a_ib a)) as Hfc3 by entailer!.
destruct Hfc3 as [Hfc3 Hfc4].
forward.
rewrite (a3_split3 Ews 18 (Zlength hb) kk (sf_hbuf (c3_s (w_k w)))) by (auto; lia).
rewrite (a3_split3 (a_shb a) (a_isz a) (w_ipc w) (w_ipc w + (kk - Zlength hb)) (zbytes (a_ibs a)))
  by (auto; rewrite ?Zlength_map; lia).
Intros.
replace (w_ipc w + (kk - Zlength hb) - w_ipc w) with (kk - Zlength hb) by lia.
sep_apply (data_at_data_at_ Ews (tarray tuchar (kk - Zlength hb)) (sublist (Zlength hb) kk (sf_hbuf (c3_s (w_k w))))
             (offset_val (Zlength hb) (field_address t_dctx (DOT _headerBuffer) (a_d a)))).
forward_call (a_shb a, Ews, offset_val (w_ipc w) (a_ib a),
              offset_val (Zlength hb) (field_address t_dctx (DOT _headerBuffer) (a_d a)),
              existT (fun t => reptype t) (tarray tuchar (kk - Zlength hb))
                (sublist (w_ipc w) (w_ipc w + (kk - Zlength hb)) (zbytes (a_ibs a)))).
{ apply prop_right. unfold field_address; rewrite if_true by auto.
  destruct (a_d a); try (destruct Hfc2; contradiction). destruct (a_ib a); try contradiction.
  simpl. rewrite Z.max_r by lia. rewrite Z.mul_1_l. change (Ptrofs.repr 1) with Ptrofs.one.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
1: lazymatch goal with |- semax _ _ _ _ => idtac | _ =>
    (* the size, and the copied input bytes are defined *)
    cbn [projT1 projT2]; split; [simpl; rewrite Z.max_r by lia; rep_lia |];
    apply memcpy_ok_bytes; [list_solve | apply byte_val_sublist, byte_val_zbytes; exact Hibsok] end.
forward. forward. forward.
rewrite a3_padd by (auto; rep_lia).
unfold lhA_post; cbv beta iota delta [RA_break].
set (u2 := sublist (w_ipc w) (w_ipc w + (kk - Zlength hb)) (a_ibs a)).
assert (Hu2: Zlength u2 = kk - Zlength hb) by (unfold u2; rewrite Zlength_sublist; lia).
assert (Hc2len: Zlength (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u2) = 18)
  by (apply a3_splice_len; lia).
destruct (a3_splice_parts (sf_hbuf (c3_s (w_k w))) (Zlength hb) u2 ltac:(assumption) Hhbz) as (E1 & E2 & E3); [lia |].
rewrite Hu2 in E2, E3.
replace (Zlength hb + (kk - Zlength hb)) with kk in E2, E3 by lia.
Exists kk v tbl d1 did1.
unfold ds_LI_S, ds_LI_L. rewrite ctx_rep3_t. Exists tbl. rewrite ctxA_split.
a3_rwL. a3_rw.
assert (Hprops: ctxA_props (lh_k_load a w (k_A (w_k w) v d1 did1) hb (kk - Zlength hb) v)) by (apply kL_props; auto).
rewrite (field_at_data_at Ews t_dctx (DOT _headerBuffer)). simpl nested_field_type.
fold u2. unfold vlong.
replace (Zlength hb + (kk - Zlength hb)) with kk by lia.
rewrite (a3_split3 Ews 18 (Zlength hb) kk (hb_splice (sf_hbuf (c3_s (w_k w))) (Zlength hb) u2))
  by (auto; lia).
rewrite E1, E2, E3.
rewrite (a3_split3 (a_shb a) (a_isz a) (w_ipc w) (w_ipc w + (kk - Zlength hb)) (zbytes (a_ibs a)))
  by (auto; rewrite ?Zlength_map; lia).
replace (w_ipc w + (kk - Zlength hb) - w_ipc w) with (kk - Zlength hb) by lia.
rewrite sublist_map. fold u2.
entailer!.
Qed.

End CM_LH3A2_t2_1.
