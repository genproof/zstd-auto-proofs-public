(* ZSTD_decompressStream, case zdss_loadHeader with the exact claim: the case from its pieces and glue (LH3XDefs.v),
   as LH3Main.v assembles the relational case.  The loop invariant's exact conjunct (S3Main.ex_call) at the entry
   gives lhx_entry; the pieces' exits rebuild it (G1, G2, G4) or return (lh_ret_x). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3XDefs Zstd.proof.dec.v3.FS.stream.lh.LH3Main.
Local Open Scope logic.

Section CM_LH3MainX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Ltac lhx_cbn := cbn [RA_normal RA_break RA_continue RA_return overridePost lhA_post lhA_post_x lhB_post_x
                     lhC_post_x lhD_post_x].

(* the case from its pieces (C level): every exit given *)
Lemma lh_case_ok_x : lhA_x_stmt -> lhB_x_stmt -> lhC_x_stmt -> lhD_x_stmt -> lend_sel_ok -> lend_use_ok ->
  lend_begin_ok -> hs_probe_ok -> GAP_fherr -> MF3 -> lh_short_model ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (R: ret_assert),
    DENT_OK DENT -> TABS_OK TABS -> lh_ctx a w hb -> lh_sel_pre a w -> dd_bytes_ok (a_st a) -> lhx_entry a w ->
    (gfh3_stmt) ->
    (forall kk v tbl d1 did1, lhA_sel (w_k w) hb kk v tbl d1 did1 ->
       get_frame_header_m (lh_mg (w_k w)) hb = FH_more kk -> kk - Zlength hb <= a_isz a - w_ipc w ->
       lh_st DENT TABS a (lhA_brk a w (k_A (w_k w) v d1 did1) hb kk) |-- RA_break R) ->
    (forall h tbl d1 did1 cSize r out c fs' d' lxb',
       get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
       lhB_facts a w (k_A (w_k w) (fh_val h) d1 did1) hb h cSize r out -> is_error_code r = false ->
       bytes_ok c -> Zlength c = r -> sublist 0 r out = zbytes c -> lhB_dict (k_A (w_k w) (fh_val h) d1 did1) d' ->
       fp_ok (fs_fParams fs') ->
       lhB_sel_fp (k_A (w_k w) (fh_val h) d1 did1) tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) fs' d' ->
       lhB_sw (k_A (w_k w) (fh_val h) d1 did1) tbl (sublist (a_ipos a) (a_ipos a + cSize) (a_ibs a)) d' ->
       sublist (w_opc w + r) (a_osz a) (sublist 0 (w_opc w) (w_oc w) ++ out) = sublist (w_opc w + r) (a_osz a) (w_oc w) ->
       lhB_x a w (k_A (w_k w) (fh_val h) d1 did1) h cSize r out lxb' ->
       lh_st DENT TABS a (lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c)
         |-- RA_break R) ->
    (forall vl, lh_ret_x DENT TABS a w hb vl |-- RA_return R vl) ->
    (forall h tbl d1 did1 c s3, get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
       lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 -> lhB_none a w hb h ->
       lhC_facts a w (k_A (w_k w) (fh_val h) d1 did1) h c -> lhC_x (k_A (w_k w) (fh_val h) d1 did1) c ->
       let k3 := lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c in
       lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) -> lhD_x (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
       lh_st DENT TABS a (lw_k w (lhD_k k3 h s3)) |-- RA_normal R) ->
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a w) ds_case_loadHeader R.
Proof.
intros HA HB HC HD Lsel Luse Lbeg Hprobe Gfh MFh Hsm Espec DENT TABS BR a w hb R HDENT HTABS Hc Hsp Hddb Hx Hgfh
  Hbrk1 Hbrk2 Hret Hnorm.
pose proof (lh_hb_in_of a w hb Hc) as Hhbi.
assert (Hc' := Hc). destruct Hc' as (Ha & _ & _ & _ & _ & He & _).
assert (Hbo: bytes_ok hb) by (unfold lh_entry in He; tauto).
destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_break RA_continue RA_return] in Hbrk1, Hbrk2, Hret, Hnorm.
destruct lh_shape as (s1 & s2 & s3 & s4 & s5 & s7 & s8 & s9 & s10 & s11 & s12 & s13 & Heq & HAeq & HCeq).
rewrite Heq.
do 4 apply <- seq_assoc.
eapply semax_seq with (Q := RA_normal (lhA_post_x DENT TABS a w hb)).
{ repeat apply seq_assoc1. rewrite <- HAeq.
  eapply semax_post with (R' := lhA_post_x DENT TABS a w hb); [ | | | | apply HA; auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lhx_cbn. Intros kk v tbl d1 did1. repeat (apply lh_PROP_cons; intro). eapply Hbrk1; eauto.
  - apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lhx_cbn. apply Hret. }
lhx_cbn. Intros h tbl d1 did1. rename H into Hh. rename H0 into Hsel.
assert (Hgf: gfh3_facts (lh_mg (w_k w)) hb h) by (apply Hgfh; auto).
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
eapply semax_seq with (Q := PROPx [lhB_none a w hb h] (LOCALx (ds_LI_L a (lw_k w k1)) (SEPx (ds_LI_St DENT TABS a (lw_k w k1) tbl)))).
{ eapply semax_post with (R' := lhB_post_x DENT TABS a w hb h k1 tbl);
    [ | | | | apply (HB MFh Luse Hprobe Hsm Espec DENT TABS BR a w hb h tbl d1 did1); auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lhx_cbn. Intros cSize r out c fs' d' lxb'. repeat (apply lh_PROP_cons; intro).
    eapply Hbrk2; eauto.
  - apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lhx_cbn. apply Hret. }
apply semax_extract_PROP. intros Hns.
do 6 apply <- seq_assoc.
eapply semax_seq with (Q := RA_normal (lhC_post_x DENT TABS a w hb h k1)).
{ repeat apply seq_assoc1. rewrite <- HCeq.
  eapply semax_post with (R' := lhC_post_x DENT TABS a w hb h k1);
    [ | | | | apply (HC Lsel Lbeg Hprobe Espec DENT TABS BR a w hb h tbl d1 did1); auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
  - apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lhx_cbn. apply Hret. }
lhx_cbn. Intros c. rename H into HCf. rename H0 into HCx.
eapply semax_post with (R' := lhD_post_x DENT TABS a w hb h (lhC_k k1 hb h c));
  [ | | | | apply (HD Espec DENT TABS BR a w hb h tbl d1 did1 c); auto ].
- apply lh_entail_ENTAIL. lhx_cbn. Intros sf3. repeat (apply lh_PROP_cons; intro). eapply Hnorm; eauto.
- apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
- apply lh_entail_ENTAIL. lhx_cbn. apply FF_left.
- intros vl. apply lh_entail_ENTAIL. lhx_cbn. apply Hret.
Qed.

(* ---------- the loop invariant's exact conjunct at the entry ---------- *)

Lemma lhx_entry_of : forall a w,
  ex_call a w -> w_smw w = 1 -> w_dl w = nil -> lhx_entry a w.
Proof.
intros a w Hx Hs Hdl. split; [ exact Hdl | ]. intros Hf.
destruct (ex_call_go a w Hx Hs Hf) as (z0 & zi & f & Hl & Hz).
exists z0, zi, f. split; [ exact Hl | ].
destruct Hz as [(_ & _ & _ & Hz) | (Hz & _)]; exact Hz.
Qed.

(* ex_call does not read the view *)
Lemma ex_call_sv : forall a w sv, ex_call a w -> ex_call a (lw_sv w sv (w_dl w)).
Proof. intros a w sv H. exact H. Qed.

Lemma seg_lh_x_pieces :
  lhA_x_stmt -> lhB_x_stmt -> lhC_x_stmt -> lhD_x_stmt -> gfh3_stmt -> lend_sel_ok -> lend_use_ok -> lend_begin_ok ->
  hs_probe_ok -> lh_short_model -> lh_brkA_x_stmt -> lh_brkB_x_stmt -> lh_read_stmt -> lh_read_x_stmt ->
  lh_ret_x_stmt -> lh_hint_x_stmt -> MF3 -> RET3x -> seg_case_x 2 -> seg_case_x 1.
Proof.
intros HA HB HC HD Hgfh Lsel Luse Lbeg Hprobe Hsm G1 G2 G4 G4x Gret Ghint MFh RTh Hs2
  Espec DENT TABS BR a w R HDn HT Ha Hci Hsmw Hle Hst HRn HRr Hstart Hentry Hun Hxc.
destruct (lh_entry_of a w Hci Hsmw Hle Hst) as (hb & He & Hfp & Hdl & Hah & Hpend).
assert (Hc: lh_ctx a w hb) by (unfold lh_ctx; tauto).
assert (Hsp: lh_sel_pre a w) by exact (lh_sel_pre_of a w hb Hc).
assert (Hx: lhx_entry a w) by exact (lhx_entry_of a w Hxc Hsmw Hdl).
pose proof lh_fherr_ok as Gfe. pose proof lh_dd_bytes_ok as Gddb.
assert (Hddb: dd_bytes_ok (a_st a)) by exact (Gddb a w hb Hc).
assert (Hbo: bytes_ok hb) by (unfold lh_entry in He; tauto).
change (seq_of_labeled_statement (ds_tail 1))
  with (Ssequence ds_case_loadHeader (seq_of_labeled_statement (ds_tail 2))).
eapply semax_seq with (Q := EX h: frame_header, EX tbl: list val, EX d1: dfields, EX did1: val, EX c: lhc,
  EX s3: sfields,
  PROPx [get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h; lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1;
         lhB_none a w hb h;
         lhC_facts a w (k_A (w_k w) (fh_val h) d1 did1) h c; lhC_x (k_A (w_k w) (fh_val h) d1 did1) c;
         lhD_facts (c3_stable (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c))
           (c3_s (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)) s3 h
           (lh_bsm (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h);
         lhD_x (c3_stable (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c))
           (c3_s (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)) s3 h
           (lh_bsm (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h)]
  (LOCALx (ds_LI_L a (lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)))
  (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)))))).
- destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_return] in HRn, HRr; subst Rn Rr.
  apply (lh_case_ok_x HA HB HC HD Lsel Luse Lbeg Hprobe Gfe MFh Hsm Espec DENT TABS BR a w hb); auto.
  + intros kk v tbl d1 did1 Hs Hk Hkk. cbn [RA_break switch_ret_assert]. eapply G1; eauto.
  + intros h tbl d1 did1 cSize r out c fs' d' lxb' Hh Hs HBf Hr Hcb Hcl Hco Hd' Hfo Hsf Hsw Hut HBx.
    cbn [RA_break switch_ret_assert]. eapply G2; eauto.
  + intros vl. unfold lh_ret_x. Intros r ipos' w'.
    apply lh_PROP_cons; intro Hvl. apply lh_PROP_cons; intro Hr. apply lh_PROP_cons; intro Hrc.
    apply lh_PROP_cons; intro Hxok. subst vl.
    cbn [RA_return overridePost switch_ret_assert].
    apply (Gret MFh RTh Hprobe Gddb DENT TABS BR a w hb r ipos' w' HT Hc Hx Hr Hrc Hxok).
    intros Hh. apply (Ghint MFh Hprobe DENT TABS BR a w hb r ipos' w' HT Hc Hx Hr Hh).
  + intros h tbl d1 did1 c s3 Hh Hs Hns HCf HCx k3 HDf HDx. unfold lh_st.
    cbn [RA_normal overridePost switch_ret_assert].
    Exists h tbl d1 did1 c s3. repeat (apply lh_PROP_intro2; [ auto | ]). apply derives_refl.
- Intros h tbl d1 did1 c s3.
  match goal with H: get_frame_header_m _ _ = FH_ok _ |- _ => rename H into Hh end.
  match goal with H: lhA_sel _ _ _ _ _ _ _ |- _ => rename H into Hs end.
  match goal with H: lhB_none _ _ _ _ |- _ => rename H into Hns end.
  match goal with H: lhC_facts _ _ _ _ _ |- _ => rename H into HCf end.
  match goal with H: lhC_x _ _ |- _ => rename H into HCx end.
  match goal with H: lhD_facts _ _ _ _ _ |- _ => rename H into HDf end.
  match goal with H: lhD_x _ _ _ _ _ |- _ => rename H into HDx end.
  assert (Hgf: gfh3_facts (lh_mg (w_k w)) hb h) by (apply Hgfh; auto).
  set (w3 := lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)).
  assert_PROP (exists sv, call_inv a (w_k w3) sv (w_ipc w3) (w_opc w3) (w_oc w3) nil /\
               loop_extra (lw_sv w3 sv nil)) as Hx3.
  { apply andp_left2. apply (G4 MFh Hprobe Gddb DENT TABS a w hb h tbl d1 did1 c s3); auto. }
  assert_PROP (ex_call a w3) as Hxc3.
  { apply andp_left2. apply (G4x MFh Hprobe Gddb DENT TABS a w hb h tbl d1 did1 c s3); auto. }
  destruct Hx3 as (sv & Hci' & Hle').
  assert (Hst3: sf_stage s3 = zdss_read) by (unfold lhD_facts in HDf; tauto).
  assert (Hxc3': ex_call a (lw_sv w3 sv nil)).
  { replace nil with (w_dl w3) by (cbn [w3 lw_k w_dl]; exact Hdl). apply ex_call_sv. exact Hxc3. }
  eapply semax_pre; [ | apply (Hs2 Espec DENT TABS BR a (lw_sv w3 sv nil) R
                                HDn HT Ha Hci' ltac:(cbn; auto) Hle' ltac:(cbn; exact Hst3) HRn HRr Hstart
     ltac:(unfold entry_ok; cbn; intros _ Hx'; rewrite Hst3 in Hx'; unfold zdss_read, zdss_init in Hx'; lia)
     ltac:(exact Hun) Hxc3') ].
  apply andp_left2. apply derives_refl.
Qed.

End CM_LH3MainX_1.
