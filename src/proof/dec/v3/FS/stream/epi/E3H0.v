(* FS3 streaming: the epilogue's head (positions, expectedOutBuffer, the no-progress guard): its
   pieces (statements, intermediate assertions, tactics); port of v2 src/proof/dec/FS/StreamSeg_epi.v. 
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst Zstd.proof.dec.v3.FS.stream.epi.E3T0.
Require Export Zstd.proof.dec.v3.FS.stream.epi.E3Dsub.
Local Open Scope logic.

Section CM_E3H0_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_off_inj : forall p i j, isptr p -> 0 <= i <= 2 ^ 30 -> 0 <= j <= 2 ^ 30 ->
  offset_val i p = offset_val j p -> i = j.
Proof.
intros p i j Hp Hi Hj E.
pose proof (epi_cmp_eq p i j Hp Hi Hj) as C. rewrite E in C.
rewrite (epi_cmp_eq p j j Hp Hj Hj), Z.eqb_refl in C.
destruct (Z.eqb_spec i j); auto. discriminate.
Qed.

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

Lemma semax_dowhile0_gen : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_loop with (Q' := RA_normal R); auto.
eapply semax_pre; [| apply semax_break]. destruct R; simpl; intros; apply andp_left2; auto.
Qed.

(* what the head needs: the two no-progress errors, the tail after the guard *)
Lemma epi_split : forall {CS: compspecs} {Espec: OracleKind} Delta P S1 S2 S3 S4 T Q R,
  semax Delta P (Ssequence S1 (Ssequence S2 (Ssequence S3 S4))) (overridePost Q R) ->
  semax Delta Q T R ->
  semax Delta P (Ssequence S1 (Ssequence S2 (Ssequence S3 (Ssequence S4 T)))) R.
Proof.
intros CS Espec Delta P S1 S2 S3 S4 T Q R H1 H2.
apply (semax_unfold_Ssequence (Ssequence (Ssequence S1 (Ssequence S2 (Ssequence S3 S4))) T)).
- simpl. rewrite <- !app_assoc. reflexivity.
- eapply semax_seq; eauto.
Qed.

Lemma epi_neg_repr : forall e, Vlong (Int64.repr (- e)) = Vlong (Int64.repr (2 ^ 64 - e)).
Proof.
intros e. f_equal. apply Int64.eqm_samerepr. unfold Int64.eqm, Zbits.eqmod. exists (-1).
change Int64.modulus with (2 ^ 64). lia.
Qed.

(* a piece that only falls through, in a sequence *)
Lemma epi_normal_over : forall {Espec: OracleKind} {cs: compspecs} Delta P c Q R,
  semax Delta P c (normal_ret_assert Q) -> semax Delta P c (overridePost Q R).
Proof.
intros Espec cs Delta P c Q R H.
eapply semax_post; [..|exact H]; destruct R; simpl; intros; try (apply andp_left2; apply derives_refl);
  apply andp_left2; apply FF_left.
Qed.

(* ---------- the pieces of the head ---------- *)

Definition ds_h1 : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in match s with Ssequence ?x _ => exact x end).
Definition ds_h2 : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with Ssequence _ (Ssequence ?x _) => exact x end).
Definition ds_h3 : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with Ssequence _ (Ssequence _ (Ssequence ?x _)) => exact x end).
Definition ds_h62 : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence ?x _) _))) => exact x end).
Definition ds_hnp : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ ?x) _))) => exact x end).
Definition ds_np : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Sifthenelse (Etempvar _t'64 tint) ?x _] => exact x end).
Definition ds_errs : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Sifthenelse (Ebinop Oge (Etempvar _t'77 tint) (Econst_int (Int.repr 16) tint) tint) ?x Sskip] =>
          exact x end).
Definition ds_l1 : statement :=
  ltac:(let s := eval cbv delta [ds_errs] in ds_errs in match s with Ssequence ?x _ => exact x end).
Definition ds_l2 : statement :=
  ltac:(let s := eval cbv delta [ds_errs] in ds_errs in match s with Ssequence _ ?x => exact x end).

Lemma ds_epilogue_eq : ds_epilogue = Ssequence ds_h1 (Ssequence ds_h2 (Ssequence ds_h3 (Ssequence
  (Ssequence ds_h62 ds_hnp) ds_epi_tail))).
Proof. reflexivity. Qed.

(* the state of the head: the context k, input->pos = ip0, output->pos = op0, op = opc *)
Definition hS DENT TABS (a: dsa) (k: cst3) (ip0 op0 opc: Z) (oc1: list val) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val opc (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
   zstd_globals (a_gv a); ctx_rep3 DENT TABS (a_gv a) (a_d a) k;
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong op0)) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong ip0)) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) oc1 (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

Definition hpre DENT TABS (a: dsa) (k: cst3) (ipc ip0 op0 opc: Z) (oc1: list val) (tl: list localdef)
    : environ -> mpred :=
  PROPx [] (LOCALx (tl ++ epi_L a ipc) (SEPx (hS DENT TABS a k ip0 op0 opc oc1))).

(* between the guard and the tail *)
Definition emid DENT TABS (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) : environ -> mpred :=
  EX n: Z, PROPx [tail_ok a (k_nfp a k opc n) ipc opc oc1]
    (LOCALx (epi_L a ipc) (SEPx (epi_S DENT TABS a (k_nfp a k opc n) ipc opc oc1))).

End CM_E3H0_1.

Ltac epi_to_emid n Ht :=
  unfold emid; Exists n;
  unfold epi_S, epi_L, k_nfp, epi_ev; rewrite ctx_rep_epi; unfold sg_seven; rewrite epi_rest_epi; unfold k_epi, sf_epi;
  cbn [c3_fs c3_s c3_tabs c3_stable c3_dict c3_par c3_sp c3_set c3_with_s sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
       sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring];
  pose proof Ht; entailer!.

(* the start of a piece: the context split, its updated fields normalised *)
Ltac epi_hstart :=
  unfold hpre, hS, epi_L; cbn [app];
  unfold ds_Delta, epi_Delta0, epi_Delta1, ds_R_x, ds_post_x; abbreviate_semax;
  rewrite ctx_rep_epi; unfold sg_seven; unfold k_nfp, epi_ev; rewrite ?epi_rest_epi; unfold k_epi, sf_epi;
  cbn [c3_fs c3_s c3_tabs c3_stable c3_dict c3_par c3_sp c3_set c3_with_s sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
       sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring]; Intros.

(* the end of a piece: fold the context into the next assertion *)
Ltac epi_hend :=
  unfold hpre, hS, epi_L; cbn [app];
  rewrite ctx_rep_epi; unfold sg_seven; unfold k_nfp, epi_ev; rewrite ?epi_rest_epi; unfold k_epi, sf_epi;
  cbn [c3_fs c3_s c3_tabs c3_stable c3_dict c3_par c3_sp c3_set c3_with_s sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
       sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring]; entailer!.

(* pieces that never touch the context's fields keep it folded (much cheaper) *)
Ltac epi_fstart :=
  unfold hpre, hS, epi_L; cbn [app]; unfold ds_Delta, epi_Delta0, epi_Delta1, ds_R_x, ds_post_x; abbreviate_semax.

