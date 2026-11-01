(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the error test after
   ZSTD_decodeFrameHeader (return the error: lh_rc's RC_dict). 
   2026-10-24: the temps renamed after F9. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_lib.
Local Open Scope logic.

Section CM_LH3C2_s10e_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c10_sep1 (L: list mpred) : @SEPx environ L = @SEPx environ [fold_right_sepcon L].
Proof. unfold SEPx. extensionality rho. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* the value of `return <temp i>` (a size_t temp) *)
Lemma c10_ret_temp : forall {CS: compspecs} Delta P Q R i (x: int64),
  In (temp i (Vlong x)) Q ->
  ENTAIL Delta, PROPx P (LOCALx Q R) |-- local (fun rho => Vlong x = eval_expr (Ecast (Etempvar i tulong) tulong) rho).
Proof.
intros CS Delta P Q R i x Hin.
eapply derives_trans; [apply (in_local _ Delta P Q R Hin) |].
intro rho. unfold local, lift1. simpl. unfold_lift. normalize.
Qed.

Lemma c10_Le_core : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w1: lw) (r: Z) (FR: mpred)
    (Pn: environ -> mpred) (Pr: option val -> environ -> mpred),
  0 <= r <= Int64.max_unsigned ->
  (is_error_code r = false -> PROPx [] (LOCALx (ds_LI_L a w1) (SEPx [FR])) |-- Pn) ->
  (is_error_code r = true -> PROPx [] (LOCALx (ds_LI_L a w1) (SEPx [FR])) |-- Pr (Some (Vlong (Int64.repr r)))) ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (temp _t'38 (Vlong (Int64.repr r)) :: ds_LI_L a w1) (SEPx [FR])))
    c10_test {| RA_normal := Pn; RA_break := FF; RA_continue := FF; RA_return := Pr |}.
Proof.
intros Espec DENT TABS BR a w1 r FR Pn Pr Hr Hn He.
unfold ds_Delta. simplify_func_tycontext. unfold c10_test, ds_LI_L. abbreviate_semax.
forward.
forward_call r.
forward_if.
- (* the error *)
  assert (Herr: is_error_code r = true) by (destruct (is_error_code r); [reflexivity | contradiction]).
  unfold MORE_COMMANDS, abbreviate.
  apply semax_dowhile0.
  match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
  { apply c10_dowhile0_gen.
    match goal with |- semax _ _ _ ?Q =>
      let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
    abbreviate_semax.
    forward_if.
    { match goal with H: 0 <> 0 |- _ => contradiction H; reflexivity end. }
    forward. entailer!. }
  apply semax_dowhile0. apply semax_dowhile0.
  eapply c10_semax_return with (v := Vlong (Int64.repr r)).
  + change (ret_type Delta) with tulong. apply c10_ret_temp. simpl; auto 50.
  + change (ret_type Delta) with tulong. entailer!.
  + cbn [RA_return]. eapply derives_trans; [| apply (He Herr)].
    unfold ds_LI_L. entailer!.
- (* no error *)
  assert (Herr: is_error_code r = false).
  { destruct (is_error_code r); [| reflexivity]. exfalso.
    match goal with H: Int.repr 1 = Int.zero |- _ => apply (f_equal Int.unsigned) in H end.
    rewrite Int.unsigned_repr in * by rep_lia. cbn in *. discriminate. }
  forward.
  eapply derives_trans; [| apply (Hn Herr)].
  unfold ds_LI_L. entailer!.
Qed.

Lemma c10_PLS_derives (P: list Prop) (Q: list localdef) (R R': list mpred) :
  fold_right and True P -> fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx [] (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R')).
Proof.
intros HP HR. unfold PROPx, LOCALx, SEPx. intro rho. simpl. normalize.
first [apply andp_left2; exact HR | apply andp_right; [apply prop_right; auto | apply andp_derives; [apply derives_refl | exact HR]]
  | apply andp_derives; [apply derives_refl | exact HR]].
Qed.

Lemma c10_ctx_t (DENT: dent_pred) (TABS: tabs_pred) gv p k tbl :
  ctx_rep3t DENT TABS gv p k tbl |-- ctx_rep3 DENT TABS gv p k.
Proof. rewrite ctx_rep3_t. Exists tbl. apply derives_refl. Qed.

Lemma c10_St_Sip (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w': lw) (tbl: list val) :
  fold_right_sepcon (ds_LI_St DENT TABS a w' tbl) |-- fold_right_sepcon (ds_S_ip DENT TABS a w' (a_ipos a)).
Proof.
unfold ds_LI_St, ds_S_ip. cbn [fold_right_sepcon].
sep_apply (c10_ctx_t DENT TABS (a_gv a) (a_d a) (w_k w') tbl). cancel.
Qed.

Lemma c10_Le : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (hb: list Z) (h: frame_header)
    (tbl: list val) (d1: dfields) (did1: val) dd cold lxb,
  lhC_hyps DENT TABS a w hb h tbl d1 did1 -> fh_frameType h <> 1 ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  semax (ds_Delta DENT TABS BR) (c10_SM DENT TABS a w k1 hb h tbl dd cold lxb) c10_test
    {| RA_normal := c10_S2c DENT TABS a w k1 hb h tbl dd cold lxb; RA_break := FF; RA_continue := FF;
       RA_return := lh_ret DENT TABS a w hb |}.
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 dd cold lxb HP Hft k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hsp & Hg & Hf & HA).
unfold c10_SM. Intros r fs' did'.
match goal with H: c10_res _ _ _ _ _ _ _ _ |- _ => destruct H as [Hdid [HdN Hres]] end.
match goal with H: 0 <= r <= Int64.max_unsigned |- _ => rename H into Hr end.
rewrite c10_sep1.
apply c10_Le_core; [exact Hr | intros Herr | intros Herr].
- destruct (orb (fh_dictID h =? 0) (fh_dictID h =? did')) eqn:Eo.
  + destruct Hres as [-> ->]. unfold c10_S2c. apply exp_right with did'. rewrite <- c10_sep1.
    apply c10_PLS_derives; [| apply derives_refl].
    cbn [fold_right]. rewrite orb_true_iff, !Z.eqb_eq in Eo. tauto.
  + destruct Hres as [[Hde _] _]. congruence.
- destruct (orb (fh_dictID h =? 0) (fh_dictID h =? did')) eqn:Eo.
  + destruct Hres as [-> _]. discriminate.
  + destruct Hres as [Hde [-> Hdc]].
    unfold lh_ret. apply exp_right with r. apply exp_right with (a_ipos a).
    apply exp_right with (lw_k w (lhC_kx k1 (c10_fs1 k1 h dd cold did') dd lxb)).
    rewrite <- c10_sep1.
    apply c10_PLS_derives; [| apply c10_St_Sip].
    cbn [fold_right]. split; [reflexivity | split; [exact Hr | split; [| exact I]]].
    rewrite orb_false_iff, !Z.eqb_neq in Eo. destruct Eo as [Eo1 Eo2].
    assert (Hdr: 0 <= fh_dictID h <= Int.max_unsigned)
      by (destruct Hf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdr & _); exact Hdr).
    eapply RC_dict; eauto.
    * apply c10_did_ne; [ exact Hdr | rewrite <- Hdc; exact Eo2 ].
    * exists (fh_dictID h). split; [reflexivity | exact Hdr].
Qed.

End CM_LH3C2_s10e_1.
