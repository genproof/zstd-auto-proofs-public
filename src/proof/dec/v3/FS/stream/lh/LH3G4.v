(* FS3 streaming, case zdss_loadHeader: G4, after piece D: zdss_read's precondition (call_inv of the new frame). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3R2Lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3G42_dict Zstd.proof.dec.v3.FS.stream.lh.LH3G42_sep Zstd.proof.dec.v3.FS.stream.lh.LH3G42_alive Zstd.proof.dec.v3.FS.stream.lh.LH3G42_core.
Local Open Scope logic.

Section CM_LH3G4_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* G4 given the facts the FIXED definitions do not give yet (g4_gaps) *)
Lemma g4_read : MF3 -> hs_probe_ok ->
  forall DENT TABS (a: dsa) (w: lw) (hb: list Z) (h: frame_header) (tbl: list val) (d1: dfields) (did1: val)
         (c: lhc) (s3: sfields),
    lh_ctx a w hb -> get_frame_header_m (lh_mg (w_k w)) hb = FH_ok h -> gfh3_facts (lh_mg (w_k w)) hb h ->
    lhA_sel (w_k w) hb 0 (fh_val h) tbl d1 did1 ->
    let k1 := k_A (w_k w) (fh_val h) d1 did1 in
    lhC_facts a w k1 h c ->
    let k3 := lhC_k k1 hb h c in
    lhD_facts (c3_stable k3) (c3_s k3) s3 h (lh_bsm k3 h) ->
    let w3 := lw_k w (lhD_k k3 h s3) in
    g4_gaps a w h c ->
    lh_st DENT TABS a w3 |-- !! exists sv, call_inv a (w_k w3) sv (w_ipc w3) (w_opc w3) (w_oc w3) nil /\
      loop_extra {| w_smw := w_smw w3; w_k := w_k w3; w_sv := sv; w_ipc := w_ipc w3; w_opc := w_opc w3;
                    w_oc := w_oc w3; w_dl := nil |}.
Proof.
intros HMF Hpr DENT TABS a w hb h tbl d1 did1 c s3 Hctx Hgfh Hgf Hsel k1 HC k3 HD w3 Hgaps.
assert (Hsco: set_cur_ok (a_st a)).
{ destruct Hctx as (_ & _ & _ & _ & _ & Hent & _).
  destruct Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _). exact (proj1 (proj2 (proj2 (proj2 (proj2 Hb))))). }
assert (Hbo: lh_st DENT TABS a w3 |-- !! (forall x buf, lc_dd c = Some (x, buf) ->
          bytes_ok (dx_bytes x) /\ (ddx_copied x = true -> 0 < Zlength (dx_bytes x)))).
{ destruct (lc_dd c) as [[x buf]|] eqn:El.
  - destruct HC as (HCdd & _). rewrite El in HCdd. cbn [lhC_dd] in HCdd. destruct HCdd as (_ & Hqn & Hsrc & _).
    eapply derives_trans; [ apply (g4_ddb DENT TABS a w3 x buf Hsco Hqn Hsrc) | ].
    apply prop_derives. intros Hf x' buf' E. inversion E; subst. exact Hf.
  - apply prop_right. intros x buf E; discriminate. }
eapply derives_trans; [ apply andp_right; [ exact Hbo | apply derives_refl ] | ].
apply derives_extract_prop. intros Hbo'.
eapply derives_trans.
{ apply andp_right; [ apply g4_par | apply andp_right; [ apply g4_sp | apply andp_right; [ apply g4_local | apply andp_right; [ apply g4_sizes | apply rl_st_held ] ] ] ]. }
apply derives_extract_prop. intros Hpok.
apply derives_extract_prop. intros (Hsp1 & Hsp0).
apply derives_extract_prop. intros Hloc.
apply derives_extract_prop. intros (_ & Hout0).
apply prop_derives. intros Hheld.
exact (g4_pure HMF Hpr a w hb h tbl d1 did1 c s3 Hctx Hgfh Hgf Hsel HC HD Hgaps Hpok Hsp1 Hsp0 Hloc Hout0 Hheld Hbo').
Qed.

Lemma lh_read_ok : lh_read_stmt.
Proof.
intros HMF Hpr _ DENT TABS a w hb h tbl d1 did1 c s3 Hctx Hgfh Hgf Hsel k1 HC k3 HD w3.
apply (g4_read HMF Hpr DENT TABS a w hb h tbl d1 did1 c s3 Hctx Hgfh Hgf Hsel HC HD).
pose proof HC as (HCdd & _ & _ & _ & _ & HCnone & _).
split; [ exact HCnone | ].
intros x buf E; rewrite E in HCdd; cbn [lhC_dd] in HCdd; unfold lh_dd_ok in HCdd;
  destruct HCdd as (_ & _ & _ & _ & _ & Hm); unfold ddx_model;
  destruct (dx_raw x); [ discriminate | destruct Hm as [Hm|Hm]; [ discriminate | exact Hm ] ].
Qed.

End CM_LH3G4_1.
