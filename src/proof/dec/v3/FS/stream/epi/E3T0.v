(* FS3 streaming: the epilogue of ZSTD_decompressStream, the tail (the hint, the hostage byte): its
   pieces (statements, preconditions, tactics); port of v2 src/proof/dec/FS/StreamSeg_epi.v.
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs Zstd.proof.dec.v3.FS.stream.epi.E3Vst.
Require Export Zstd.proof.dec.v3.FS.stream.epi.E3Dsub.
Local Open Scope logic.

Section CM_E3T0_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- the tail: the hint, the hostage byte ---------- *)

Definition ds_epi_tail : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Ssequence (Ssequence (Scall (Some _t'65) ?f ?args) ?x) ?y] =>
          exact (Ssequence (Ssequence (Scall (Some _t'65) f args) x) y) end).

End CM_E3T0_1.


(* the k of the tail with streamStage and hostageByte changed *)
Ltac epi_norm :=
  repeat match goal with
  | H: Int64.eq (Int64.repr _) (Int64.repr _) = true |- _ => apply Int64.same_if_eq in H
  | H: Int64.repr ?x <> Int64.repr ?y |- _ =>
      let E := fresh "E" in assert (E: x <> y) by (intros E'; apply H; rewrite E'; reflexivity); clear H
  | H: Int64.repr ?x = Int64.repr ?y |- _ =>
      apply (f_equal Int64.unsigned) in H; rewrite !Int64.unsigned_repr in H by rep_lia
  | H: Int64.ltu (Int64.repr ?x) (Int64.repr ?y) = _ |- _ =>
      unfold Int64.ltu in H; rewrite !Int64.unsigned_repr in H by rep_lia;
      destruct (zlt x y); try discriminate H; clear H
  end.

Ltac epi_fold :=
  rewrite ctx_rep_epi; unfold sg_seven, k_sh, k_nfp, epi_ev; rewrite ?epi_rest_epi; unfold k_epi, sf_epi;
  cbn [c3_fs c3_s c3_tabs c3_stable c3_dict c3_par c3_sp c3_set c3_with_s sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
       sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring].

Section CM_E3T0_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_hint_val : forall e fstg ip0, 0 <= fstg <= 7 ->
  Vlong (Int64.repr (e + 3 * Int.signed (Int.repr (Z.b2z (Int.eq (Int.repr (next_input_type fstg)) (Int.repr 2))))
    - ip0)) = Vlong (Int64.repr (e + ZSTD_blockHeaderSize * nit_blk fstg - ip0)).
Proof.
intros e fstg ip0 Hf.
assert (Hc: Int.signed (Int.repr (Z.b2z (Int.eq (Int.repr (next_input_type fstg)) (Int.repr 2)))) = nit_blk fstg).
{ assert (fstg = 0 \/ fstg = 1 \/ fstg = 2 \/ fstg = 3 \/ fstg = 4 \/ fstg = 5 \/ fstg = 6 \/ fstg = 7)
    as Hs by lia.
  destruct Hs as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity. }
rewrite Hc. reflexivity.
Qed.

(* the pieces of the tail *)
Definition ds_tail_Z : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Sifthenelse (Eunop Onotbool (Etempvar _nextSrcSizeHint tulong) tint) ?z Sskip] =>
          exact z end).

Definition ds_tail_hint : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Ssequence (Ssequence (Scall (Some _t'66) ?f ?args) ?x) ?y] =>
          exact (Ssequence (Ssequence (Scall (Some _t'66) f args) x) y) end).

Definition ds_tail_E : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Sifthenelse (Ebinop Oeq (Etempvar _t'71 tulong) (Etempvar _t'72 tulong) tint) ?e Sskip] =>
          exact e end).

Definition ds_tail_neq : statement :=
  ltac:(let s := eval cbv delta [ds_tail_Z] in ds_tail_Z in
        match s with Ssequence _ ?n => exact n end).

Definition ds_tail_h1r : statement :=
  ltac:(let s := eval cbv delta [ds_tail_E] in ds_tail_E in
        match s with Ssequence (Ssequence _ (Sifthenelse _ ?h1 Sskip)) ?r => exact (Ssequence h1 r) end).

Definition ds_tail_cr : statement :=
  ltac:(let s := eval cbv delta [ds_epilogue] in ds_epilogue in
        match s with context [Sifthenelse (Ebinop Oge (Etempvar _t'75 tulong) (Etempvar _t'76 tulong) tint) ?cr Sskip] =>
          exact cr end).

Definition ds_tail_relr : statement :=
  ltac:(let s := eval cbv delta [ds_tail_h1r] in ds_tail_h1r in
        match s with Ssequence (Ssequence _ ?rel) ?r => exact (Ssequence rel r) end).

Definition ds_tail_taker : statement :=
  ltac:(let s := eval cbv delta [ds_tail_neq] in ds_tail_neq in
        match s with Ssequence (Ssequence _ (Sifthenelse _ ?t Sskip)) ?r => exact (Ssequence t r) end).

(* the precondition of a piece: the context folded, extra locals tl *)
Definition tpre DENT TABS (a: dsa) (k: cst3) (ipc opc: Z) (oc1: list val) (tl: list localdef) : environ -> mpred :=
  PROPx [] (LOCALx (tl ++ epi_L a ipc) (SEPx (epi_S DENT TABS a k ipc opc oc1))).

(* a piece that always returns, under any post with the function's return part *)
Lemma epi_R_sub : forall {Espec: OracleKind} DENT TABS BR (a: dsa) Delta P c R0,
  RA_return R0 = RA_return (ds_R_x DENT TABS BR a) -> semax Delta P c (ds_R_x DENT TABS BR a) -> semax Delta P c R0.
Proof.
intros Espec DENT TABS BR a Delta P c R0 HR H.
eapply semax_post; [..|exact H].
- unfold ds_R_x, frame_ret_assert, function_body_ret_assert. destruct R0; simpl. intros rho.
  unfold bind_ret. simpl. normalize.
- unfold ds_R_x, frame_ret_assert, function_body_ret_assert. destruct R0; simpl. intros rho. normalize.
- unfold ds_R_x, frame_ret_assert, function_body_ret_assert. destruct R0; simpl. intros rho. normalize.
- intros vl. rewrite HR. apply andp_left2. apply derives_refl.
Qed.

Lemma epi_seq_ret : forall {Espec: OracleKind} {cs: compspecs} Delta P c rest R,
  semax Delta P c (overridePost FF R) -> semax Delta P (Ssequence c rest) R.
Proof.
intros Espec cs Delta P c rest R H.
eapply semax_seq; [exact H | apply semax_ff].
Qed.

End CM_E3T0_2.

Ltac epi_piece_start :=
  unfold tpre, epi_S, epi_L; cbn [app];
  unfold ds_Delta, epi_Delta0, epi_Delta1, ds_R_x, ds_post_x; abbreviate_semax;
  rewrite ctx_rep_epi; unfold sg_seven; Intros.

(* from the split state of the walk to a piece's precondition *)
Ltac epi_to_tpre :=
  unfold tpre, epi_S, epi_L; cbn [app]; rewrite ctx_rep_epi; unfold sg_seven; entailer!.

