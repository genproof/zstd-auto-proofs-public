(* FS3 streaming, case zdss_loadHeader, piece C: helper lemmas of the segments s7, s12, s13 (from v2's
   StreamSeg_lhC.v). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Local Open Scope logic.

Section CM_LH3C_util_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma fcs_repr_unknown : forall x, 0 <= x <= Int64.max_unsigned ->
  (Int64.repr x = Int64.sub (Int64.repr 0) (Int64.repr 1) <-> x = ZSTD_CONTENTSIZE_UNKNOWN).
Proof.
intros x Hx. split; intros E.
- apply (f_equal Int64.unsigned) in E. rewrite Int64.unsigned_repr in E by lia.
  rewrite E. reflexivity.
- subst x. unfold Int64.sub. rewrite !Int64.unsigned_repr by rep_lia.
  apply Int64.eqm_samerepr. exists 1. reflexivity.
Qed.

Lemma sub_pp_tschar : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 30 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* do { c } while (0) *)
Lemma semax_dowhile0_gen : forall {CS: compspecs} {Espec: OracleKind} Delta P c R,
  semax Delta P c (loop1_ret_assert (RA_normal R) R) -> semax Delta P (Sloop c Sbreak) R.
Proof.
intros CS Espec Delta P c R H.
apply semax_loop with (Q' := RA_normal R); auto.
eapply semax_pre; [| apply semax_break]. destruct R; simpl; intros; apply andp_left2; auto.
Qed.

(* return e, whose value is v, into a custom ret_assert *)
Lemma semax_return_v : forall {CS: compspecs} {Espec: OracleKind} Delta P (e: expr) (v: val) R,
  let e' := Ecast e (ret_type Delta) in
  ENTAIL Delta, P |-- tc_expr Delta e' ->
  ENTAIL Delta, P |-- local (fun rho => v = eval_expr e' rho) ->
  ENTAIL Delta, P |-- RA_return R (Some v) ->
  semax Delta P (Sreturn (Some e)) R.
Proof.
intros CS Espec Delta P e v R e' H1 H2 H3.
eapply semax_pre; [| apply semax_return].
apply andp_right; [exact H1|].
eapply derives_trans; [apply andp_right; [exact H2 | exact H3]|].
intro rho. unfold local, lift1, liftx, lift. simpl. normalize.
apply derives_refl.
Qed.

Lemma fcs_cne : forall x, 0 <= x <= Int64.max_unsigned ->
  Int64.cmpu Cne (Int64.repr x) (Int64.repr (- (1))) = negb (x =? ZSTD_CONTENTSIZE_UNKNOWN).
Proof.
intros x Hx. simpl. f_equal. unfold Int64.eq.
rewrite (Int64.unsigned_repr x) by lia.
change (Int64.unsigned (Int64.repr (-1))) with ZSTD_CONTENTSIZE_UNKNOWN.
destruct (zeq x ZSTD_CONTENTSIZE_UNKNOWN); destruct (Z.eqb_spec x ZSTD_CONTENTSIZE_UNKNOWN); congruence.
Qed.

Lemma if_bool_ne0 : forall b: bool, Int.repr (if b then 1 else 0) <> Int.zero -> b = true.
Proof. intros [|] H; [reflexivity | contradiction]. Qed.

Lemma if_bool_eq0 : forall b: bool, Int.repr (if b then 1 else 0) = Int.zero -> b = false.
Proof. intros [|] H; [discriminate | reflexivity]. Qed.

Lemma repr_err_code : forall n, Int64.repr (err_code n) = Int64.repr (- n).
Proof. intros n. apply Int64.eqm_samerepr. exists 1. unfold err_code. reflexivity. Qed.

End CM_LH3C_util_1.

(* the value of `return (size_t)-n` *)
Ltac ret_err_val :=
  intro rho; unfold local, lift1; apply prop_right; clear; rewrite repr_err_code; reflexivity.

Section CM_LH3C_util_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* skip into a post whose normal part is Q *)
Lemma semax_skip_override : forall {CS: compspecs} {Espec: OracleKind} Delta P Q R,
  ENTAIL Delta, P |-- Q -> semax Delta P Sskip (overridePost Q R).
Proof.
intros CS Espec Delta P Q R H.
eapply semax_pre; [exact H |].
destruct R as [Rn Rb Rc Rr]; unfold overridePost; simpl.
eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto; try apply FF_left.
Qed.

(* skip into a post whose normal part holds *)
Lemma semax_skip_normal : forall {CS: compspecs} {Espec: OracleKind} Delta P R,
  ENTAIL Delta, P |-- RA_normal R -> semax Delta P Sskip R.
Proof.
intros CS Espec Delta P R H.
eapply semax_pre; [exact H |].
destruct R as [Rn Rb Rc Rr]; simpl.
eapply semax_post_flipped; [apply semax_skip | ..]; simpl; intros; try apply andp_left2; auto; try apply FF_left.
Qed.

Lemma small_false : forall (st: bool) ft fcs x,
  (st && negb (ft =? 1) && negb (fcs =? ZSTD_CONTENTSIZE_UNKNOWN) && (x <? fcs))%bool = false ->
  st = true -> ft <> 1 -> fcs <> ZSTD_CONTENTSIZE_UNKNOWN -> fcs <= x.
Proof.
intros st ft fcs x H Hs Hf Hc. subst st. apply Z.eqb_neq in Hf. apply Z.eqb_neq in Hc.
rewrite Hf, Hc in H. simpl in H. apply Z.ltb_ge in H. lia.
Qed.


(* k1 = k, hidden from entailer!'s subst *)
Definition lhC_eqk (k1 k: cst3) : Prop := k1 = k.

End CM_LH3C_util_2.
