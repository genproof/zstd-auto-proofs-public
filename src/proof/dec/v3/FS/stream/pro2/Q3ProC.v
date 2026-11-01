(* FS3 streaming, the prologue of ZSTD_decompressStream: statements 5-6 (ostart, oend). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro2.Q3ProD.
Local Open Scope logic.

Section CM_Q3ProC_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma pro_segC : forall (Espec: OracleKind) DENT TABS BR (a: dsa) REST k,
  pro_hyp Espec DENT TABS BR a REST k ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (pro_L5 a) (SEPx (pro_S0 DENT TABS a k))))
    (sdrop 5 (ds_prologue REST)) (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a REST k H. pose proof H as H0. destruct H as (HD & HT & Hok & Hbr & PV & HR & HX).
unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
clear PV HR HX.
pose proof (pro_segD Espec DENT TABS BR a REST k H0) as HE.
unfold pro_L5, pro_S0 in HE |- *. unfold ds_R_x, ds_post_x in HE |- *.
unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
assert_PROP (isptr (a_ob a)) as Hob by entailer!.
forward.
forward_if (temp _t'5 (offset_val (a_opos a) (a_ob a))).
{ forward. forward. entailer!. }
{ z0. forward. entailer!; match goal with E: ?x = 0 |- offset_val ?x _ = _ => rewrite E; apply isptr_offset_val_zero; auto end. }
forward. forward.
forward_if (temp _t'6 (offset_val (a_osz a) (a_ob a))).
{ forward. forward. entailer!. }
{ z0. forward. entailer!; match goal with E: ?x = 0 |- offset_val ?x _ = _ => rewrite E; apply isptr_offset_val_zero; auto end. }
forward.
eapply semax_pre; [| exact HE].
entailer!.
Qed.

End CM_Q3ProC_1.
