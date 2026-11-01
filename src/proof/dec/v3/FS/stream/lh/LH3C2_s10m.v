(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: ZSTD_decodeFrameHeader on the state
   (the selection's resources lent by dict_res / set_res; the second selection finds what the first did). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_vC Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10c.
Local Open Scope logic.

Section CM_LH3C2_s10m_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c10_res_cold k1 hb h dd cold did' r fs' :
  c10_res k1 hb h dd cold did' r fs' -> cold01 (c10_fsB k1 dd cold) -> cold01 fs'.
Proof. intros [_ [_ H]] Hc. destruct (_ || _)%bool; [ destruct H as [_ ->] | destruct H as [_ [-> _]] ]; exact Hc. Qed.

Lemma c10_PLS_derives (P: list Prop) (Q: list localdef) (R R': list mpred) :
  fold_right and True P -> fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx [] (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros HP HR. unfold PROPx, LOCALx, SEPx. intro rho. simpl. normalize.
first [apply andp_left2; exact HR | apply andp_right; [apply prop_right; auto | apply andp_derives; [apply derives_refl | exact HR]]
  | apply andp_derives; [apply derives_refl | exact HR]].
Qed.

(* a pure fact of the resources of a state *)
Lemma c10_sep_prop (Delta: tycontext) (P: list Prop) (Q: list localdef) (R: list mpred) (A: Prop) :
  fold_right_sepcon R |-- !! A -> ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! A.
Proof.
intros H rho. unfold PROPx, LOCALx, SEPx. simpl.
apply andp_left2. apply andp_left2. apply andp_left2. exact H.
Qed.

Lemma c10_Lc : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) dd cold lxb (R: ret_assert),
  lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (c10_S2b DENT TABS a w k1 h tbl dd cold lxb) c10_call
    (overridePost (c10_SM DENT TABS a w k1 hb h tbl dd cold lxb) R).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 dd cold lxb R HP k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hsp & Hg & Hf & HA).
destruct He as (Hstg & Hlh & Hhb18 & Hhbok & Hhbsub & Hhost & Hinp & Hos & Hoe & Hipc & Hopc & Hoc & Hsmw & Hbc & Hlen).
destruct Hbc as (Hbst & Hbpar & Hbset & Hbrel & Hbcur & _ & (_ & _ & Hlm0)).
assert (Hsdo: stream_dict_ok (a_W a) (a_st a)) by (destruct Ha as (_ & _ & _ & _ & _ & _ & _ & H & _); exact H).
assert (Hdr: 0 <= fh_dictID h <= Int.max_unsigned)
  by (destruct Hf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
unfold c10_S2b.
rewrite (c10_prop_sep _ _ _ _ _ (c10_vC DENT TABS a w (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb) tbl)).
apply semax_extract_PROP; intros (((Hcold & Hpar) & Hsg) & Hcm).
apply semax_extract_PROP; intro Hsm. apply semax_extract_PROP; intro Hdd. apply semax_extract_PROP; intro Hcd.
change (sf_lhSize (c3_s (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb))) with (sf_lhSize (c3_s (w_k w))).
rewrite Hlh.
(* the allocator: the bytes besides the local DDict of getDDict's dictionary fields *)
set (S := c3_s (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)).
set (dg := snd (getddict_res d1)).
change (c3_dict (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)) with dg.
assert_PROP (0 <= sf_held S - local_held dg) as Hh0.
{ apply c10_sep_prop. cbn [fold_right_sepcon].
  sep_apply (hset_t_held (sf_mem S) (c3_sp (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb))
    (c3_set (lhC_kx k1 (c10_fsB k1 dd cold) dd lxb)) (sf_held S - local_held dg) tbl). entailer!. }
assert (Hmem: sel_mem (c3_par (w_k w)) (c3_sp (w_k w)) dg (sf_mem S) (sf_given S - local_held dg)).
{ intros _. split; [| split; [exact Hcm |]].
  - exact (local_mem_redict _ _ _ (redict_ok_trans _ _ _ (lhA_sel_redict _ _ _ _ _ _ _ HA) (redict_ok_getddict d1))
             Hlm0).
  - destruct Hsg as (Hi & Ho & _). unfold sf_given. rewrite dctx_size_eq. unfold S in *. lia. }
replace (sf_given S) with (sf_given S - local_held dg + local_held dg) by lia.
(* the selection's resources *)
assert (Hlend: exists xq: option (val * val),
  sel_on (c3_par (w_k w)) (c3_sp (w_k w)) = true ->
  cur_ok (snd (getddict_res d1)) (c3_set (w_k w)) xq /\
  (dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a)) |--
   set_ids (c3_set (w_k w)) * opt_token xq *
   (set_ids (c3_set (w_k w)) * opt_token xq -*
    dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
    set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a))))).
{ destruct (sel_on (c3_par (w_k w)) (c3_sp (w_k w))) eqn:Hon; [| exists None; discriminate].
  destruct (Hsp Hon) as [_ Hnone].
  assert (Hnd: NoDup (map fst (dc_set (a_st a)))).
  { destruct HA as (_ & _ & idx & _ & Hsb). unfold sel_by in Hsb. rewrite Hon in Hsb. destruct Hsb as (Hinv & _).
    rewrite <- Hbset. exact (proj1 (proj2 (proj2 (proj2 Hinv)))). }
  destruct (Hsel DENT (a_gv a) (a_W a) (a_st a) (c3_dict (w_k w)) Hbrel Hbcur Hsdo Hnd) as (xq & Hcur & Hle).
  { intro E. destruct (Hnone E); auto. }
  exists xq. intros _. rewrite Hbset. split; [| exact Hle].
  rewrite <- Hbset in Hcur |- *. exact (c10_cur_ok (w_k w) hb tbl h d1 did1 xq Hpr HA Hon Hcur). }
destruct Hlend as (xq & Hlend).
eapply c10_post_n.
{ eapply (c10_Lc_core _ _ _ _ a (lw_k w k1) _ _ hb (c10_fsB k1 dd cold) (c3_par (w_k w)) (c3_sp (w_k w))
            dg (c3_set (w_k w)) tbl xq (c10_did dd) (sf_mem S) (sf_given S - local_held dg)
            (sf_held S - local_held dg)).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hsg))))))).
  - exact Hhb18.
  - exact Hhbsub.
  - exact Hhbok.
  - apply c10_fsB_dictID.
  - apply c10_did_range.
  - apply c10_fsB_pcs.
  - exact Hmem.
  - exact Hlend. }
unfold c10_Cpost, c10_SM.
Intros r fs' d'.
match goal with H: dfh_post3 _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hdfh end.
destruct (c10_dfh (w_k w) hb h tbl d1 did1 dd cold r fs' d' (fun E => ltac:(subst dd; exact Hdd)) HA Hg Hdr Hdfh) as [-> [did' Hres]].
Exists r fs' did'.
rewrite (c10_prop_sep _ _ _ _ _ (c10_vC DENT TABS a w (lhC_kx k1 fs' dd lxb) tbl)).
change (sf_lhSize (c3_s (lhC_kx k1 fs' dd lxb))) with (sf_lhSize (c3_s (w_k w))).
rewrite Hlh.
change (local_held (snd (getddict_res d1))) with (local_held dg).
replace (sf_given S - local_held dg + local_held dg) with (sf_given S) by lia.
apply andp_left2. apply c10_PLS_derives; [| apply derives_refl].
cbn [fold_right].
split; [split; [split; [split; [exact (c10_res_cold _ _ _ _ _ _ _ _ Hres Hcold) | exact Hpar] | exact Hsg] | exact Hcm] |].
exact (conj Hsm (conj Hdd (conj Hcd (conj H (conj Hres I))))).
Qed.

End CM_LH3C2_s10m_1.
