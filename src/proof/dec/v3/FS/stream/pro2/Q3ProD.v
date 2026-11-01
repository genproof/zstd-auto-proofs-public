(* FS3 streaming, the prologue of ZSTD_decompressStream: statements 7-10 (op = ostart,
   someMoreWork = 1, an empty do-while, the input position check). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro2.Q3ProD2.
Local Open Scope logic.

Section CM_Q3ProD_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma pro_segD : forall (Espec: OracleKind) DENT TABS BR (a: dsa) REST k,
  pro_hyp Espec DENT TABS BR a REST k ->
  semax (ds_Delta DENT TABS BR)
    (PROPx [] (LOCALx (temp _ostart (offset_val (a_opos a) (a_ob a)) :: temp _oend (offset_val (a_osz a) (a_ob a)) ::
                       pro_L5 a) (SEPx (pro_S0 DENT TABS a k))))
    (sdrop 7 (ds_prologue REST)) (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a REST k H. pose proof H as H0. destruct H as (HD & HT & Hok & Hbr & PV & HR & HX).
unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
clear PV HR HX.
unfold pro_L5, pro_S0.
unfold ds_R_x, ds_post_x. unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
forward. forward.
skip_loop.
do0_loop.
{ forward. forward.
  forward_if (temp _t'171 (Vlong (Int64.repr (a_ipos a)))).
  { exfalso. lia. }
  { forward. entailer!. }
  forward; try solve [apply andp_left2, derives_refl | entailer!]. }
pose proof (pro_segD2 Espec DENT TABS BR a REST k H0) as HE.
unfold ds_LI_L, ds_LI_S, pro_w0, ds_R_x, ds_post_x in HE. cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl] in HE.
eapply semax_pre; [| exact HE].
entailer!.
Qed.

End CM_Q3ProD_1.
