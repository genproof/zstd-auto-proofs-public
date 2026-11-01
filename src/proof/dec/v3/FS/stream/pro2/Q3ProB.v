(* FS3 streaming, the prologue of ZSTD_decompressStream: statements 2-4 (iend, ip, dst). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro2.Q3ProC.
Local Open Scope logic.

Section CM_Q3ProB_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* F9: the prologue compares input->src and output->dst with NULL; a caller's buffer that is not NULL is weakly
   valid at its start by buf_ok (also when it is empty), so the comparison is defined *)
Lemma buf_ok_null_test : forall (W: list ptr_witness) sh n (c: list val) p (R: mpred),
  buf_ok W sh n p ->
  (pws_pred W * data_at sh (tarray tuchar n) c p * R |-- denote_tc_test_eq p (Vlong (Int64.repr 0)))%logic.
Proof.
intros W sh n c p R Hb.
assert_PROP (isptr p) as Pp by (saturate_local; entailer!).
destruct p; try contradiction.
eapply derives_trans with (weak_valid_pointer (Vptr b i)).
- apply sepcon_weak_valid_pointer1.
  sep_apply (data_at_data_at_ sh (tarray tuchar n) c (Vptr b i)).
  rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left1. auto.
- Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq.
Qed.

Lemma pro_segB : forall (Espec: OracleKind) DENT TABS BR (a: dsa) REST k,
  pro_hyp Espec DENT TABS BR a REST k ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (pro_L2 a) (SEPx (pro_S0 DENT TABS a k))))
    (sdrop 2 (ds_prologue REST)) (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a REST k H. pose proof H as H0. destruct H as (HD & HT & Hok & Hbr & PV & HR & HX).
unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
clear PV HR HX.
pose proof (pro_segC Espec DENT TABS BR a REST k H0) as HE.
unfold pro_L2, pro_L5, pro_S0 in HE |- *. unfold ds_R_x, ds_post_x in HE |- *.
unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
assert_PROP (isptr (a_ib a)) as Hib by entailer!.
forward.
forward_if (temp _t'3 (offset_val (a_isz a) (a_ib a))).
{ forward. forward. entailer!. }
{ z0. forward. entailer!; match goal with E: ?x = 0 |- offset_val ?x _ = _ => rewrite E; apply isptr_offset_val_zero; auto end. }
assert_PROP (isptr (a_ob a)) as Pob by entailer!.
forward. forward. forward.
{ (* the struct's pointer output->dst: NULL, or the base itself (a pointer) *)
  entailer!. unfold a_ob in Pob; destruct (nbase_cases (a_gv a) (a_obf a)) as [[_ E]|[E _]];
  [rewrite E in Pob; destruct (a_obf a); try contradiction; simpl; auto | rewrite E; simpl; auto]. }
(* F9: dst = output->dst != NULL ? output->dst : ZSTD_emptyBuffer, the base a_ob a *)
forward_if (temp _t'4 (a_ob a)).
{ destruct (nbase_cases (a_gv a) (a_obf a)) as [[Hon Eob] | [Hon Eob]]; change (nbase (a_gv a) (a_obf a)) with (a_ob a) in Eob.
  - rewrite Eob in Hbo.
    eapply derives_trans; [| apply (buf_ok_null_test (a_W a) (a_shob a) (a_osz a) (a_oc a) (a_obf a) TT Hbo)].
    rewrite Eob. cancel.
  - rewrite Hon. entailer!. }
{ forward. forward. entailer!. all: unfold a_ob; rewrite nbase_ptr; auto. }
{ forward. entailer!. all: unfold a_ob; match goal with E: a_obf _ = nullval |- _ => rewrite E end; rewrite nbase_null; auto. }
forward.
eapply semax_pre; [| exact HE].
entailer!.
Qed.

End CM_Q3ProB_1.
