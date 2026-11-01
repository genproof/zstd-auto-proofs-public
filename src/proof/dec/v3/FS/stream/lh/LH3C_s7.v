(* FS3 streaming, case zdss_loadHeader, piece C, segment s7 (LH3C_lib.v): the stable-buffer check. *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_lib.
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3C_util.
Local Open Scope logic.

Section CM_LH3C_s7_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition lhC_s7a : statement := ltac:(
  let t := eval cbv delta [lhC_s7] in lhC_s7 in lazymatch t with Ssequence ?x _ => exact x end).
Definition lhC_e7 : expr := ltac:(
  let t := eval cbv delta [lhC_s7] in lhC_s7 in lazymatch t with Ssequence _ (Sifthenelse ?e _ _) => exact e end).
Definition lhC_s7t : statement := ltac:(
  let t := eval cbv delta [lhC_s7] in lhC_s7 in lazymatch t with Ssequence _ (Sifthenelse _ ?b _) => exact b end).
Lemma lhC_s7_eq : lhC_s7 = Ssequence lhC_s7a (Sifthenelse lhC_e7 lhC_s7t Sskip).
Proof. reflexivity. Qed.

(* [p + i - (p + j)] on char pointers, for offsets up to PTRDIFF_MAX ([sub_pp_tschar] is
   stated for offsets up to 2^30; the output buffer may be larger). *)
Lemma sub_pp_tschar63 : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 63 - 1 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

(* after the three tests of s7: _t'33 = whether the stable buffer is too small *)
Definition lhC_S7m (DENT: dent_pred) (TABS: tabs_pred) (a: dsa) (w: lw) (k1: cst3) (h: frame_header)
    (tbl: list val) : environ -> mpred :=
  PROPx []
  (LOCALx (temp _t'33 (Vint (Int.repr (if lhC_small a w k1 h then 1 else 0))) :: ds_LI_L a (lw_k w k1))
  (SEPx (ds_LI_St DENT TABS a (lw_k w k1) tbl))).

Lemma lhC_L7a : forall (Espec: OracleKind) DENT TABS BR a w hb h tbl k1 (R: ret_assert),
  dsa_ok a -> lh_entry a w hb -> gfh3_facts (lh_mg (w_k w)) hb h -> fs_fParams (c3_fs k1) = fh_val h ->
  semax (ds_Delta DENT TABS BR) (lh_stt DENT TABS a (lw_k w k1) tbl) lhC_s7a
    (overridePost (lhC_S7m DENT TABS a w k1 h tbl) R).
Proof.
intros Espec DENT TABS BR a w hb h tbl k1 R Ha He Hf Hfp.
destruct R as [Rn Rb Rc Rr]. unfold overridePost.
unfold lh_stt, ds_Delta. simplify_func_tycontext. unfold lhC_s7a. abbreviate_semax.
unfold ds_LI_St, ds_LI_L, ctx_rep3t, fgroup3, cgroup3, frame_fields.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
Intros.
rewrite Hfp.
destruct Ha as (Hbo & Hbi & Hst & Wsho & Wshi & Wshob & Rshb & Hsdo & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbok & Hstout & Hosz0 & Hstpos & _).
destruct He as (Hstg & Hlh & Hhb18 & Hhbok & Hhbsub & Hhost & Hinp & Hos & Hoe & Hipc & Hopc & Hoc' & Hsmw & Hbc & Hlen).
destruct Hf as (Hhb5 & Hfcs & Hws & Hbsm & Hbsm' & Hck & Hft & Hft1 & Hft2 & Hdid & Hhs).
assert_PROP (isptr (a_ob a)) as Hob by entailer!.
forward.
forward_if (temp _t'31 (Vint (Int.repr (if andb (c3_stable k1) (negb (fh_frameType h =? 1)) then 1 else 0)))).
{ forward. forward. entailer!.
  destruct (c3_stable k1); [| discriminate]. destruct Hft as [-> | ->]; reflexivity. }
{ forward. entailer!. destruct (c3_stable k1); [contradiction | reflexivity]. }
forward_if (temp _t'32 (Vint (Int.repr (if andb (andb (c3_stable k1) (negb (fh_frameType h =? 1)))
  (negb (fh_contentSize h =? ZSTD_CONTENTSIZE_UNKNOWN)) then 1 else 0)))).
{ forward.
  match goal with |- context [temp _t'133 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
  forward. entailer!.
  match goal with Hx: Int.repr (if _ then 1 else 0) <> Int.zero |- _ => apply if_bool_ne0 in Hx; rewrite Hx end.
  rewrite fcs_cne by auto. reflexivity. }
{ forward. entailer!.
  match goal with Hx: Int.repr (if _ then 1 else 0) = Int.zero |- _ => apply if_bool_eq0 in Hx; rewrite Hx end.
  reflexivity. }
forward_if (temp _t'33 (Vint (Int.repr (if lhC_small a w k1 h then 1 else 0)))).
{ forward. forward.
  match goal with |- context [temp _t'132 ?v] => change v with (Vlong (Int64.repr (fh_contentSize h))) end.
  forward.
  { entailer!. apply prop_right. destruct (a_ob a); try contradiction. simpl. unfold sameblock.
    destruct (peq b b); [reflexivity | congruence]. }
  entailer!. unfold lhC_small.
  match goal with Hx: Int.repr (if _ then 1 else 0) <> Int.zero |- _ => apply if_bool_ne0 in Hx; rewrite Hx end.
  rewrite sub_pp_tschar63 by (auto; lia).
  simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt (a_osz a - w_opc w) (fh_contentSize h)); destruct (Z.ltb_spec (a_osz a - w_opc w) (fh_contentSize h));
    try lia; reflexivity. }
{ forward. entailer!. unfold lhC_small.
  match goal with Hx: Int.repr (if _ then 1 else 0) = Int.zero |- _ => apply if_bool_eq0 in Hx; rewrite Hx end.
  reflexivity. }
unfold lhC_S7m, ds_LI_St, ds_LI_L, ctx_rep3t, fgroup3, cgroup3, frame_fields.
cbn [lw_k w_k w_smw w_ipc w_opc w_oc].
rewrite Hfp.
entailer!.
Qed.

Lemma lhC_L7t : forall (Espec: OracleKind) DENT TABS BR a w hb h tbl d1 did1,
  lhC_hyps DENT TABS a w hb h tbl d1 did1 ->
  let k1 := k_A (w_k w) (fh_val h) d1 did1 in
  lhC_small a w k1 h = true ->
  semax (ds_Delta DENT TABS BR) (lhC_S7m DENT TABS a w k1 h tbl) lhC_s7t
    (overridePost (lhC_S1 DENT TABS a w k1 h tbl) (lhC_post DENT TABS a w hb h k1)).
Proof.
intros Espec DENT TABS BR a w hb h tbl d1 did1 HP k1 Hsm.
assert (Hk1: lhC_eqk k1 (k_A (w_k w) (fh_val h) d1 did1)) by reflexivity.
clearbody k1.
destruct HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hs & Hg & Hf & HA).
unfold lhC_S7m, lhC_post, overridePost, ds_Delta, ds_LI_L. simplify_func_tycontext. unfold lhC_s7t. abbreviate_semax.
unfold lhC_small in Hsm. rewrite !andb_true_iff in Hsm. destruct Hsm as [[[Hs1 Hs2] Hs3] Hs4].
apply semax_dowhile0_gen.
match goal with |- semax _ _ _ ?Q =>
  let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
abbreviate_semax. unfold MORE_COMMANDS, abbreviate.
apply semax_dowhile0.
match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
{ apply semax_dowhile0_gen.
  match goal with |- semax _ _ _ ?Q =>
    let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
  abbreviate_semax.
  forward_if.
  all: try (match goal with H: Int.repr 0 <> Int.zero |- _ => contradiction H; reflexivity end).
  forward. entailer!. }
abbreviate_semax. unfold MORE_COMMANDS, abbreviate.
apply semax_dowhile0. apply semax_dowhile0.
apply semax_return_v with (v := Vlong (Int64.repr (err_code ZSTD_error_dstSize_tooSmall))).
{ entailer!. }
{ ret_err_val. }
unfold POSTCONDITION, abbreviate. cbn [RA_return loop1_ret_assert].
clear POSTCONDITION. try clear MORE_COMMANDS.
unfold lh_ret. Exists (err_code ZSTD_error_dstSize_tooSmall) (a_ipos a) (lw_k w k1).
unfold ds_S_ip, ds_LI_St, ds_LI_L. rewrite ctx_rep3_t. Exists tbl.
go_lower.
apply andp_right.
{ apply prop_right. repeat split; auto; try (rewrite eqb_type_refl; reflexivity);
    try (unfold err_code, ZSTD_error_dstSize_tooSmall; rep_lia).
  unfold lhC_eqk in Hk1. subst k1.
  apply (RC_small a w hb h tbl d1 did1); auto.
  - intros E. rewrite E in Hs2. discriminate.
  - intros E. rewrite E, Z.eqb_refl in Hs3. discriminate.
  - apply Z.ltb_lt; auto. }
cancel.
Qed.

Lemma lhC_seg7_ok : lhC_seg7_stmt.
Proof.
unfold lhC_seg7_stmt. intros Espec DENT TABS BR a w hb h tbl d1 did1 HP.
pose proof HP as (Hsel & Hbeg & Hpr & HD & HT & Ha & He & Hs & Hg & Hf & HA).
rewrite lhC_s7_eq.
apply semax_seq with (lhC_S7m DENT TABS a w (k_A (w_k w) (fh_val h) d1 did1) h tbl).
{ apply lhC_L7a with hb; auto. }
eapply semax_pre; [apply andp_left2; apply now_later |].
apply semax_ifthenelse_PQR' with
  (v := Vint (Int.repr (if lhC_small a w (k_A (w_k w) (fh_val h) d1 did1) h then 1 else 0))).
- reflexivity.
- unfold lhC_S7m, lhC_e7, ds_LI_L. entailer!.
- unfold lhC_S7m, lhC_e7, ds_LI_L. entailer!.
- apply semax_extract_PROP. intro Ht.
  apply lhC_L7t; auto.
  destruct (lhC_small _ _ _ _); [reflexivity | cbv in Ht; discriminate].
- apply semax_extract_PROP. intro Ht.
  apply semax_skip_override.
  assert (E: lhC_small a w (k_A (w_k w) (fh_val h) d1 did1) h = false)
    by (destruct (lhC_small _ _ _ _); [cbv in Ht; discriminate | reflexivity]).
  unfold lhC_S7m, lhC_S1, ds_LI_L. entailer!.
Qed.

End CM_LH3C_s7_1.
