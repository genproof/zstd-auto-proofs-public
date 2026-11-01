(* FS3 streaming, case zdss_loadHeader, piece A: the split of lh_A into its prefix (the loop of the
   legacy macro, getFrameHeader_advanced, the selection) and its tail (the error test, the need-more branch); the
   state between them; the prefix's proof. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3A_lib.
Local Open Scope logic.

Section CM_LH3A2_pre_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition lhA_p : statement := ltac:(
  let t := eval cbv delta [lh_A] in lh_A in
  match t with Ssequence ?s1 (Ssequence ?s2 (Ssequence ?s3 _)) => exact (Ssequence s1 (Ssequence s2 s3)) end).

Definition lhA_t : statement := ltac:(
  let t := eval cbv delta [lh_A] in lh_A in
  match t with Ssequence _ (Ssequence _ (Ssequence _ ?s45)) => exact s45 end).

Lemma lhA_seq3 : forall {Espec: OracleKind} {cs: compspecs} Delta P Q R s1 s2 s3 s4,
  semax Delta P (Ssequence s1 (Ssequence s2 s3)) (overridePost Q R) -> semax Delta Q s4 R ->
  semax Delta P (Ssequence s1 (Ssequence s2 (Ssequence s3 s4))) R.
Proof.
intros Espec cs Delta P Q R s1 s2 s3 s4 H1 H2.
apply seq_assoc. apply seq_assoc.
apply semax_seq with Q; auto.
apply seq_assoc. exact H1.
Qed.

Lemma lhA_split : forall {Espec: OracleKind} Delta P Q R,
  semax Delta P lhA_p (overridePost Q R) -> semax Delta Q lhA_t R -> semax Delta P lh_A R.
Proof.
intros Espec Delta P Q R H1 H2. unfold lhA_p in H1. unfold lhA_t in H2.
exact (lhA_seq3 _ _ _ _ _ _ _ _ H1 H2).
Qed.

(* the state after the prefix: hSize = r, fParams := v, the selection done (dictionary fields d1, dictID did1) *)
Definition lhA_mid (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) (r: Z) (v: reptype t_fh) (tbl: list val)
    (d1: dfields) (did1: val) : environ -> mpred :=
  PROPx [] (LOCALx (temp _hSize (Vlong (Int64.repr r)) :: ds_LI_L a w)
    (SEPx (ds_LI_St DENT TABS a (lw_k w (k_A (w_k w) v d1 did1)) tbl))).

Definition lhA_midx (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) (hb: list Z) : environ -> mpred :=
  EX r: Z, EX v: reptype t_fh, EX tbl: list val, EX d1: dfields, EX did1: val,
  !! lhA_sel (w_k w) hb r v tbl d1 did1 && lhA_mid DENT TABS a w r v tbl d1 did1.

End CM_LH3A2_pre_1.

(* closing the prefix without the selection *)
Ltac a3_off_close Hoff a w hb r v tbl Hr Hpost Hlh :=
  pose proof (a3_sel_off (w_k w) hb r v tbl Hoff Hr Hpost) as Hsel;
  unfold lhA_midx, lhA_mid; Exists r v tbl (c3_dict (w_k w)) (fs_dictID (c3_fs (w_k w)));
  rewrite kA_off;
  unfold ds_LI_St, ctx_rep3t, fgroup3, cgroup3, hset_t, lw_k, c3_with_fs;
  cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set];
  rewrite fsu_dictID_fp_same, ff_split, sg_split, Hlh; unfold vlong;
  change (ff_rest (a_d a) (fsu_fParams (c3_fs (w_k w)) v)) with (ff_rest (a_d a) (c3_fs (w_k w)));
  change (fs_fParams (fsu_fParams (c3_fs (w_k w)) v)) with v;
  first [rewrite if_true by auto | rewrite if_false by auto]; unfold ds_LI_L;
  entailer!.

Section CM_LH3A2_pre_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma lhA_pre_ok : lend_sel_ok -> GAP_fherr ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (R: ret_assert),
    DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> lh_entry a w hb -> lh_sel_pre a w ->
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a w) lhA_p (overridePost (lhA_midx DENT TABS a w hb) R).
Proof.
intros Hlend Hfherr Espec DENT TABS BR a w hb R HD HT Ha He Hsp.
destruct R as [Rn Rb Rc Rr]. cbv beta iota delta [overridePost].
rewrite lh_st_t. Intros tbl.
unfold lh_stt, ds_LI_St, ds_LI_L, ctx_rep3t.
assert_PROP (0 <= sf_held (c3_s (w_k w)) - local_held (c3_dict (w_k w))) as Hhs.
{ sep_apply hset_t_held. entailer!. }
unfold fgroup3, cgroup3, hset_t.
Intros.
unfold ds_Delta. simplify_func_tycontext.
unfold lhA_p.
a3_skip_loop.
abbreviate_semax.
destruct He as (Hstage & Hlh & Hhb18 & Hhbok & Hsub & Hhost & Hinpos & Hos & Hoe & Hipc & Hopc & Hoc & Hsmw & Hbc & Hlen).
rewrite sg_split, ff_split. Intros.
unfold cfg_fmt.
rewrite Hlh. unfold vlong.
forward. forward.
assert (Hhbz: 0 <= Zlength hb) by apply Zlength_nonneg.
assert (Hsg := H1). destruct Hsg as (_ & _ & _ & _ & _ & _ & Hhb18' & _).
assert (Hw: win_ok Ews 18 (sf_hbuf (c3_s (w_k w))) 0 (Zlength hb) hb).
{ unfold win_ok. rewrite Z.add_0_l. repeat split; auto; try lia; auto with share. }
assert (Hfmt: dp_fmt (c3_par (w_k w)) = 0 \/ dp_fmt (c3_par (w_k w)) = 1) by (destruct H0; tauto).
assert_PROP (field_compatible t_dctx (DOT _fParams) (a_d a) /\ field_compatible t_dctx (DOT _headerBuffer) (a_d a))
  as Hfc by entailer!.
destruct Hfc as [Hfc1 Hfc2].
rewrite (field_at_data_at Ews t_dctx (DOT _fParams)).
rewrite (field_at_data_at Ews t_dctx (DOT _headerBuffer)).
simpl nested_field_type.
forward_call (a_gv a, Ews, field_address t_dctx (DOT _fParams) (a_d a), fs_fParams (c3_fs (w_k w)), Ews,
              field_address t_dctx (DOT _headerBuffer) (a_d a), 18, sf_hbuf (c3_s (w_k w)), 0, hb,
              dp_fmt (c3_par (w_k w))).
{ apply prop_right. simpl. rewrite isptr_offset_val_zero by (apply field_address_isptr; auto).
  unfold field_address. rewrite !if_true by auto. reflexivity. }
Intros vret. destruct vret as [r v]. cbv [fst snd] in *.
rename H2 into Hr, H3 into Hpost.
forward.
rewrite a3_fp_eq, a3_hb_eq.
assert (Hmulti: dp_multi (c3_par (w_k w)) = 0 \/ dp_multi (c3_par (w_k w)) = 1) by (unfold par_ok in H0; tauto).
forward.
destruct (eq_dec (c3_sp (w_k w)) nullval) as [Hsp0 | Hsp1].
- (* no set: no selection *)
  Intros.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'13 (Vint (Int.repr 0)) :: Q) (SEPx R))) end.
  { rewrite Hsp0. forward. forward. rewrite Hsp0. entailer!. }
  { forward. entailer!. }
  forward_if.
  { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
  forward.
  assert (Hoff: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = false)
    by (unfold sel_on; rewrite Hsp0; simpl; rewrite andb_false_r; reflexivity).
  a3_off_close Hoff a w hb r v tbl Hr Hpost Hlh.
- (* a set *)
  Intros.
  destruct Hmulti as [Hm0 | Hm1].
  + (* refMultipleDDicts off *)
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'13 (Vint (Int.repr 0)) :: Q) (SEPx R))) end.
    { exfalso. match goal with H: Int.repr _ <> Int.zero |- _ => rewrite Hm0 in H; apply H; reflexivity end. }
    { forward. entailer!. }
    forward_if.
    { exfalso. match goal with H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity end. }
    forward.
    assert (Hoff: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = false)
      by (unfold sel_on; rewrite Hm0; reflexivity).
    a3_off_close Hoff a w hb r v tbl Hr Hpost Hlh.
  + (* the selection *)
    assert (Hon: sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = true)
      by (unfold sel_on, veqb; rewrite Hm1; simpl; destruct (Val.eq (c3_sp (w_k w)) nullval); [contradiction | reflexivity]).
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'13 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { assert_PROP (isptr (c3_sp (w_k w))) as Hspp by (unfold hset_tbl; Intros tp; entailer!).
      forward. forward.
      { unfold hset_tbl; Intros tp; entailer!. }
      entailer!. destruct (c3_sp (w_k w)); try contradiction; reflexivity. }
    { exfalso. rewrite Hm1 in *. discriminate. }
    forward_if.
    2: { exfalso. match goal with H: Int.repr 1 = Int.zero |- _ => discriminate H end. }
    destruct Hbc as (Hbst & Hbpar & Hbset & Hbrel & Hbcur & Hbfp & Hbmem & Hbroom & Hblm).
    destruct Ha as (_ & _ & _ & _ & _ & _ & _ & Hsdo & _).
    destruct (Hsp Hon) as [Hfp0 Hnone].
    assert (Hfp: fp_id_ok v) by (eapply a3_fp_id; eauto).
    destruct Hfp as (id & Hid & Hidr).
    assert_PROP (hs_inv (c3_set (w_k w)) tbl) as Hinv by (unfold hset_tbl; Intros tp; entailer!).
    assert (Hnd: NoDup (map fst (dc_set (a_st a))))
      by (rewrite <- Hbset; destruct Hinv as (_ & _ & _ & Hnd & _); exact Hnd).
    destruct (Hlend DENT (a_gv a) (a_W a) (a_st a) (c3_dict (w_k w)) Hbrel Hbcur Hsdo Hnd)
      as (xq & Hcur & Hlent).
    { exact Hnone. }
    sep_apply Hlent.
    sep_apply (ff_fold (a_d a) (c3_fs (w_k w)) v).
    rewrite <- Hbset.
    rewrite <- Hbset in Hcur.
    (* the allocator's bytes: those of the local DDict (which the selection may free) and the others *)
    rewrite sg_rest_0. unfold mgroup. Intros.
    replace (sf_given (c3_s (w_k w))) with
      ((sf_given (c3_s (w_k w)) - local_held (c3_dict (w_k w))) + local_held (c3_dict (w_k w))) by lia.
    forward_call (a_gv a, a_d a, fsu_fParams (c3_fs (w_k w)) v, id, c3_dict (w_k w), c3_sp (w_k w),
                  c3_set (w_k w), tbl, xq, sf_mem (c3_s (w_k w)),
                  sf_given (c3_s (w_k w)) - local_held (c3_dict (w_k w))).
    { unfold sf_given, dctx_size. pose proof H1 as (Hi & Ho & _).
      pose proof (sizeof_pos (Tstruct _ZSTD_DCtx_s noattr)). lia. }
    sep_apply (wand_frame_elim (set_ids (c3_set (w_k w)) * opt_token xq)
      (dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
       set_res (DD3x DENT) (a_gv a) Ews (c3_set (w_k w)) (dc_dict (a_st a)))).
    pose proof (a3_sel_on (w_k w) hb r v tbl id Hon Hr Hpost Hid Hidr Hinv) as Hsel.
    unfold lhA_midx, lhA_mid.
    Exists r v tbl (sel_dict (c3_dict (w_k w)) (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id))
      (if eq_dec (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id) nullval then fs_dictID (c3_fs (w_k w))
       else Vint (Int.repr id)).
    unfold ds_LI_St, ctx_rep3t, fgroup3, cgroup3, hset_t, k_A, k_redict, lw_k, c3_with_dict, c3_with_fs, c3_with_s.
    cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set].
    rewrite <- fsu_dictID_sel, sg_split, hr_lh, hr_hbuf, held_redict_set, sg_rest_0, sg_rest0_redict, !hr_mem,
      sf_given_redict, Hlh, <- Hbset. unfold vlong, mgroup.
    pose proof (sg_props_redict (c3_s (w_k w)) (c3_dict (w_k w))
      (sel_dict (c3_dict (w_k w)) (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id)) H1 Hhs) as Hsgr.
    destruct (eq_dec (c3_sp (w_k w)) nullval); [contradiction |]. unfold ds_LI_L.
    entailer!.
    destruct (eq_dec (sel_r (c3_dict (w_k w)) (c3_set (w_k w)) tbl id) nullval); exact H.
Qed.

End CM_LH3A2_pre_2.
