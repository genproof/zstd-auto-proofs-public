(* FS3 streaming, case zdss_loadHeader: the case from its pieces and glue (LH3Stmts.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3Main_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lh_entail_ENTAIL : forall Delta (P Q: environ -> mpred), P |-- Q -> ENTAIL Delta, P |-- Q.
Proof. intros. apply andp_left2; auto. Qed.

Lemma lh_PROP_cons : forall (P: Prop) Ps QR (S: environ -> mpred),
  (P -> PROPx Ps QR |-- S) -> PROPx (P :: Ps) QR |-- S.
Proof.
intros. eapply derives_trans; [ | apply (derives_extract_PROP P TT Ps QR S) ].
- rewrite TT_andp; apply derives_refl.
- intros; rewrite TT_andp; auto.
Qed.

Lemma lh_PROP_intro : forall (P: Prop) Ps QR, P -> PROPx Ps QR |-- PROPx (P :: Ps) QR.
Proof.
intros. unfold PROPx. apply andp_right.
- apply andp_left1. intro rho. simpl. apply prop_derives. tauto.
- apply andp_left2. apply derives_refl.
Qed.

Lemma lh_PROP_intro2 : forall (P: Prop) Ps Qs QR, P -> PROPx Qs QR |-- PROPx Ps QR -> PROPx Qs QR |-- PROPx (P :: Ps) QR.
Proof. intros. eapply derives_trans; [ exact H0 | apply lh_PROP_intro; auto ]. Qed.

Ltac lh_cbn := cbn [RA_normal RA_break RA_continue RA_return overridePost lhA_post lhB_post lhC_post lhD_post].

(* the case from its pieces (C level): every exit given *)
Lemma lh_case_ok : lhA_stmt -> lhB_stmt -> lhC_stmt -> lhD_stmt -> lend_sel_ok -> lend_use_ok -> lend_begin_ok ->
  hs_probe_ok -> GAP_fherr -> MF3 ->
  forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (R: ret_assert),
    DENT_OK DENT -> TABS_OK TABS -> lh_ctx a w hb -> lh_sel_pre a w -> dd_bytes_ok (a_st a) ->
    (gfh3_stmt) ->
    RA_break R = ds_inv DENT TABS a ->
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
       lh_st DENT TABS a (lhB_brk w (k_A (w_k w) (fh_val h) d1 did1) fs' d' lxb' (a_ipos a + cSize) r out c)
         |-- RA_break R) ->
    (forall vl, lh_ret DENT TABS a w hb vl |-- RA_return R vl) ->
    (forall h tbl d1 did1 c s3, get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h ->
       lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
       lhC_facts a w (k_A (w_k w) (fh_val h) d1 did1) h c ->
       let k3 := lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c in
       lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
       lh_st DENT TABS a (lw_k w (lhD_k k3 h s3)) |-- RA_normal R) ->
    semax (ds_Delta DENT TABS BR) (lh_st DENT TABS a w) ds_case_loadHeader R.
Proof.
intros HA HB HC HD Lsel Luse Lbeg Hprobe Gfh MFh Espec DENT TABS BR a w hb R HDENT HTABS Hc Hsp Hddb Hgfh HRb
  Hbrk1 Hbrk2 Hret Hnorm.
pose proof (lh_hb_in_of a w hb Hc) as Hhbi.
assert (Hc' := Hc). destruct Hc' as (Ha & _ & _ & _ & _ & He & _).
assert (Hbo: bytes_ok hb) by (unfold lh_entry in He; tauto).
destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_break RA_continue RA_return] in HRb, Hbrk1, Hbrk2, Hret, Hnorm.
subst Rb.
destruct lh_shape as (s1 & s2 & s3 & s4 & s5 & s7 & s8 & s9 & s10 & s11 & s12 & s13 & Heq & HAeq & HCeq).
rewrite Heq.
do 4 apply <- seq_assoc.
eapply semax_seq with (Q := RA_normal (lhA_post DENT TABS a w hb)).
{ repeat apply seq_assoc1. rewrite <- HAeq.
  eapply semax_post with (R' := lhA_post DENT TABS a w hb); [ | | | | apply HA; auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lh_cbn. Intros kk v tbl d1 did1. repeat (apply lh_PROP_cons; intro). eapply Hbrk1; eauto.
  - apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lh_cbn. apply Hret. }
lh_cbn. Intros h tbl d1 did1. rename H into Hh. rename H0 into Hsel.
assert (Hgf: gfh3_facts (lh_mg (w_k w)) hb h) by (apply Hgfh; auto).
set (k1 := k_A (w_k w) (fh_val h) d1 did1).
eapply semax_seq with (Q := lh_stt DENT TABS a (lw_k w k1) tbl).
{ eapply semax_post with (R' := lhB_post DENT TABS a w hb h k1 tbl);
    [ | | | | apply (HB MFh Luse Hprobe Espec DENT TABS BR a w hb h tbl d1 did1); auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lh_cbn. Intros cSize r out c fs' d' lxb'. repeat (apply lh_PROP_cons; intro).
    eapply Hbrk2; eauto.
  - apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lh_cbn. apply Hret. }
do 6 apply <- seq_assoc.
eapply semax_seq with (Q := RA_normal (lhC_post DENT TABS a w hb h k1)).
{ repeat apply seq_assoc1. rewrite <- HCeq.
  eapply semax_post with (R' := lhC_post DENT TABS a w hb h k1);
    [ | | | | apply (HC Lsel Lbeg Hprobe Espec DENT TABS BR a w hb h tbl d1 did1); auto ].
  - apply lh_entail_ENTAIL. apply derives_refl.
  - apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
  - apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
  - intros vl. apply lh_entail_ENTAIL. lh_cbn. apply Hret. }
lh_cbn. Intros c. rename H into HCf.
eapply semax_post with (R' := lhD_post DENT TABS a w hb h (lhC_k k1 hb h c));
  [ | | | | apply (HD Espec DENT TABS BR a w hb h tbl d1 did1 c); auto ].
- apply lh_entail_ENTAIL. lh_cbn. Intros sf3. repeat (apply lh_PROP_cons; intro). eapply Hnorm; eauto.
- apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
- apply lh_entail_ENTAIL. lh_cbn. apply FF_left.
- intros vl. apply lh_entail_ENTAIL. lh_cbn. apply Hret.
Qed.

(* ---------- the loop invariant around the pieces ---------- *)

Definition lw_sv (w: lw) (sv: sview) (dl: list Z) : lw :=
  {| w_smw := w_smw w; w_k := w_k w; w_sv := sv; w_ipc := w_ipc w; w_opc := w_opc w; w_oc := w_oc w;
     w_dl := dl |}.

(* the entry of case 1 *)
Lemma lh_entry_of : forall a w,
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 -> loop_extra w ->
  sf_stage (c3_s (w_k w)) = zdss_loadHeader ->
  exists hb, lh_entry a w hb /\ sv_fp (w_sv w) = FP_hdr hb /\ w_dl w = nil /\ sv_ahead (w_sv w) = nil /\
             sv_pend (w_sv w) = nil.
Proof.
intros a w Hci Hsmw Hle Hst.
destruct (Hle Hsmw) as [Hdl Hah]; [ rewrite Hst; unfold zdss_loadHeader; lia | ].
destruct Hci as (Hipc & Hopc & Hloc & _ & _ & _ & _ & Hbase & _ & _ & _ & _ & Hcore & _).
destruct Hcore as (_ & _ & _ & Hbr). rewrite Hst in Hbr. cbn in Hbr.
destruct Hbr as (Hpend & Hhost & HinPos & Hos & Hoe & hb & Hfp & Hlen & Hbo & Hlh & Hsub & Hlok).
exists hb. unfold lh_entry. rewrite Hst.
repeat match goal with |- _ /\ _ => split end; auto; try lia.
Qed.

(* what the selection needs at the entry (R1: base_call's fp_ok, dict_rel3_of None) *)
Lemma lh_sel_pre_of : forall a w hb, lh_ctx a w hb -> lh_sel_pre a w.
Proof.
intros a w hb Hc. unfold lh_sel_pre. intros _.
destruct Hc as (_ & _ & _ & _ & _ & He & _).
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbc & _).
destruct Hbc as (_ & _ & _ & Hrel & _ & Hfp & _).
split; [ exact Hfp | ].
intros Hn. destruct Hrel as [Hr | [_ (_ & _ & _ & Hin)]].
- rewrite Hn in Hr. cbn in Hr. destruct Hr as [_ [E | E]]; auto.
- auto.
Qed.

Lemma seg_lh_ok_pieces :
  lhA_stmt -> lhB_stmt -> lhC_stmt -> lhD_stmt -> gfh3_stmt -> lend_sel_ok -> lend_use_ok -> lend_begin_ok ->
  hs_probe_ok -> lh_brkA_stmt -> lh_brkB_stmt -> lh_read_stmt -> lh_ret_stmt -> lh_hint_stmt ->
  MF3 -> RET3 -> seg_case 2 -> seg_case 1.
Proof.
intros HA HB HC HD Hgfh Lsel Luse Lbeg Hprobe G1 G2 G4 Gret Ghint MFh RTh Hs2
  Espec DENT TABS BR a w R HDn HT Ha Hci Hsmw Hle Hst HRn HRr Hstart Hentry Hun.
destruct (lh_entry_of a w Hci Hsmw Hle Hst) as (hb & He & Hfp & Hdl & Hah & Hpend).
assert (Hc: lh_ctx a w hb) by (unfold lh_ctx; tauto).
assert (Hsp: lh_sel_pre a w) by exact (lh_sel_pre_of a w hb Hc).
pose proof lh_fherr_ok as Gfe. pose proof lh_dd_bytes_ok as Gddb.
assert (Hddb: dd_bytes_ok (a_st a)) by exact (Gddb a w hb Hc).
assert (Hbo: bytes_ok hb) by (unfold lh_entry in He; tauto).
change (seq_of_labeled_statement (ds_tail 1))
  with (Ssequence ds_case_loadHeader (seq_of_labeled_statement (ds_tail 2))).
eapply semax_seq with (Q := EX h: frame_header, EX tbl: list val, EX d1: dfields, EX did1: val, EX c: lhc,
  EX s3: sfields,
  PROPx [get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h; lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1;
         lhC_facts a w (k_A (w_k w) (fh_val h) d1 did1) h c;
         lhD_facts (c3_stable (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c))
           (c3_s (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c)) s3 h
           (lh_bsm (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h)]
  (LOCALx (ds_LI_L a (lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)))
  (SEPx (ds_LI_S DENT TABS a (lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)))))).
- destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_return] in HRn, HRr; subst Rn Rr.
  apply (lh_case_ok HA HB HC HD Lsel Luse Lbeg Hprobe Gfe MFh Espec DENT TABS BR a w hb); auto.
  + intros kk v tbl d1 did1 Hs Hk Hkk. eapply G1; eauto.
  + intros h tbl d1 did1 cSize r out c fs' d' lxb' Hh Hs HBf Hr Hcb Hcl Hco Hd' Hfo Hsf Hsw Hut.
    eapply G2; eauto.
  + intros vl. unfold lh_ret. Intros r ipos' w'.
    apply lh_PROP_cons; intro Hvl. apply lh_PROP_cons; intro Hr. apply lh_PROP_cons; intro Hrc. subst vl.
    cbn [RA_return overridePost switch_ret_assert].
    apply (Gret MFh RTh Hprobe Gddb DENT TABS BR a w hb r ipos' w' HT Hc Hr Hrc).
    intros Hh. apply (Ghint MFh Hprobe DENT TABS BR a w hb r ipos' w' HT Hc Hr Hh).
  + intros h tbl d1 did1 c s3 Hh Hs HCf k3 HDf. unfold lh_st. cbn [RA_normal overridePost switch_ret_assert].
    Exists h tbl d1 did1 c s3. repeat (apply lh_PROP_intro2; [ auto | ]). apply derives_refl.
- Intros h tbl d1 did1 c s3.
  match goal with H: get_frame_header_m _ _ = FH_ok _ |- _ => rename H into Hh end.
  match goal with H: lhA_sel _ _ _ _ _ _ _ |- _ => rename H into Hs end.
  match goal with H: lhC_facts _ _ _ _ _ |- _ => rename H into HCf end.
  match goal with H: lhD_facts _ _ _ _ _ |- _ => rename H into HDf end.
  assert (Hgf: gfh3_facts (lh_mg (w_k w)) hb h) by (apply Hgfh; auto).
  set (w3 := lw_k w (lhD_k (lhC_k (k_A (w_k w) (fh_val h) d1 did1) hb h c) h s3)).
  assert_PROP (exists sv, call_inv a (w_k w3) sv (w_ipc w3) (w_opc w3) (w_oc w3) nil /\
               loop_extra (lw_sv w3 sv nil)) as Hx.
  { apply andp_left2. apply (G4 MFh Hprobe Gddb DENT TABS a w hb h tbl d1 did1 c s3); auto. }
  destruct Hx as (sv & Hci' & Hle').
  assert (Hst3: sf_stage s3 = zdss_read) by (unfold lhD_facts in HDf; tauto).
  eapply semax_pre; [ | apply (Hs2 Espec DENT TABS BR a (lw_sv w3 sv nil) R
                                HDn HT Ha Hci' ltac:(cbn; auto) Hle' ltac:(cbn; exact Hst3) HRn HRr Hstart
     ltac:(unfold entry_ok; cbn; intros _ Hx; rewrite Hst3 in Hx; unfold zdss_read, zdss_init in Hx; lia)
     ltac:(exact Hun)) ].
  apply andp_left2. apply derives_refl.
Qed.

End CM_LH3Main_1.
