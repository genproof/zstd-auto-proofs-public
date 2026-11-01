(* FS3 streaming, the prologue of ZSTD_decompressStream: statements 11-12 (the output position
   check, an empty do-while). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro2.Q3ProE.
Local Open Scope logic.

Section CM_Q3ProD2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma pro_segD2 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) REST k,
  pro_hyp Espec DENT TABS BR a REST k ->
  semax (ds_Delta DENT TABS BR)
    (PROPx [] (LOCALx (ds_LI_L a (pro_w0 a k)) (SEPx (ds_LI_S DENT TABS a (pro_w0 a k)))))
    (sdrop 11 (ds_prologue REST)) (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a REST k H. pose proof H as H0. destruct H as (HD & HT & Hok & Hbr & PV & HR & HX).
unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
clear PV HR HX.
unfold ds_LI_L, ds_LI_S, pro_w0. cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl].
unfold ds_R_x, ds_post_x. unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
do0_loop.
{ forward. forward.
  forward_if (temp _t'167 (Vlong (Int64.repr (a_opos a)))).
  { exfalso. lia. }
  { forward. entailer!. }
  forward; try solve [apply andp_left2, derives_refl | entailer!]. }
skip_loop.
pose proof (pro_segE Espec DENT TABS BR a REST k H0) as HE.
unfold ds_LI_L, ds_LI_S, pro_w0, ds_R_x, ds_post_x in HE. cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl] in HE.
exact HE.
Qed.

End CM_Q3ProD2_1.
