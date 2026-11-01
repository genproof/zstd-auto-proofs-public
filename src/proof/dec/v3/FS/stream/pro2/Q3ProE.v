(* FS3 streaming, the prologue of ZSTD_decompressStream: statement 13 (ZSTD_checkOutBuffer) and the
   loop invariant. *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Require Import Zstd.proof.dec.v3.FS.stream.pro2.Q3ProPure Zstd.proof.dec.v3.FS.stream.pro.P3ProCtx.
Require Import Zstd.proof.dec.v3.FS.stream.S3XKit.
Local Open Scope logic.

Section CM_Q3ProE_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the loop's first state is the model's state of the calls before this one: from a fresh configuration the
   context's exact relation (FSRep3.ex_on3 with S3XRel.xrel3) holds, and raising the allocator's bound changes no
   field the exact relation reads *)
Lemma pro_ex_call (a: dsa) (k: cst3) (sv: sview) :
  dsa_ok a -> ex_on3 SR3 (a_st a) k ->
  ex_call a {| w_smw := 1; w_k := c3_raise k (dp_wmax (dc_par (a_st a))); w_sv := sv; w_ipc := a_ipos a;
               w_opc := a_opos a; w_oc := a_oc a; w_dl := [] |}.
Proof.
intros Hok HX. apply ex_call_start; try reflexivity.
intros (Hd & Hp & Hs & Hb & He).
assert (Herr: ss_err (dc_ss (a_st a)) = false) by (unfold dsa_ok in Hok; tauto).
exact (HX He Herr (or_intror (conj Hd (conj Hp (conj Hs Hb))))).
Qed.


Lemma pro_segE : forall (Espec: OracleKind) DENT TABS BR (a: dsa) REST k,
  pro_hyp Espec DENT TABS BR a REST k ->
  semax (ds_Delta DENT TABS BR)
    (PROPx [] (LOCALx (ds_LI_L a (pro_w0 a k)) (SEPx (ds_LI_S DENT TABS a (pro_w0 a k)))))
    (sdrop 13 (ds_prologue REST)) (ds_R_x DENT TABS BR a).
Proof.
intros Espec DENT TABS BR a REST k H. destruct H as (HD & HT & Hok & Hbr & PV & HR & HX).
pose proof Hok as Hok0. unfold dsa_ok in Hok.
destruct Hok as (Hbo & Hbi & Hsob & Wsho & Wshi & Wshob & Rshb & Hdict & Herr & Hopos & Hosz & Hoc & Hipos & Hisz & Hibs & Hbibs & HI2 & HF6 & Hpos & _).
pose proof (pro_view_exp _ _ _ _ _ PV) as Hexp.
unfold ds_LI_L, ds_LI_S, pro_w0. cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl].
unfold ds_R_x, ds_post_x. unfold ds_prologue. simpl sdrop.
unfold ds_Delta. simplify_func_tycontext.
do0_loop.
{ sep_apply (@ctx_rep_split CMI DENT TABS (a_gv a) (a_d a) k).
  assert_PROP (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed) as Hstg by (unfold ctx_rest3; entailer!).
  forward_call (a_d a, c3_stable k, sf_stage (c3_s k), sf_expOut (c3_s k), a_sho a, a_outp a, a_obf a, a_osz a,
                a_opos a, a_W a, a_shob a, a_oc a, a_ob a).
  { cancel. }
  { split; [intros ? ? | unfold a_ob, nbase; destruct (eq_dec (a_obf a) nullval); auto].
    match goal with Hs: c3_stable k = true, Hne: sf_stage (c3_s k) <> zdss_init |- _ =>
      assert (Hs': dc_stable (a_st a) = true) by (destruct Hbr as [<- _]; exact Hs); rewrite (Hexp Hs' Hne) end.
    exists (a_osz a), (Int64.unsigned (Int64.repr (Zlength (ss_out (dc_ss (a_st a)))))).
    split; [unfold vlong; rewrite Int64.repr_unsigned; reflexivity | split; [rep_lia | apply Int64.unsigned_range_2]]. }
  sep_apply (@ctx_rep_join CMI DENT TABS (a_gv a) (a_d a) k).
  rewrite (check_out_zero (a_st a) k (a_obf a) (a_osz a) (a_opos a) Hbr Hexp Hpos).
  forward_call 0.
  change (is_error_code 0) with false.
  forward_if (temp _t'8 (Vint (Int.repr 0))).
  { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
  { forward. entailer!. }
  forward; try solve [apply andp_left2, derives_refl | entailer!]. }
destruct PV as (sv & Hn0 & Hn1 & Hn2 & HnT & Hcore & Hdd & Hsa & Hsin & Hm & _ & Hah & Hby).
unfold pro_rest in HR.
eapply semax_pre;
  [| exact (HR {| w_smw := 1; w_k := c3_raise k (dp_wmax (dc_par (a_st a))); w_sv := sv; w_ipc := a_ipos a; w_opc := a_opos a; w_oc := a_oc a; w_dl := [] |}
              (pro_call_inv a k sv Hok0 Hbr Hby Hn1 Hn2 HnT Hexp Hcore Hdd Hsa Hsin Hm) eq_refl
              (fun _ Hle => conj eq_refl (Hah Hle)) (pro_start_ok a k sv Hcore Hby Hsa Hsin Hm Hn0)
              ltac:(unfold exit_ok; simpl; intros Hx; discriminate Hx)
              ltac:(unfold entry_ok; simpl; intros; reflexivity)
              ltac:(unfold untouched_ok; simpl; intros; reflexivity)
              (pro_ex_call a k sv Hok0 HX))].
unfold ds_LI_L, ds_LI_S.
cbn [w_smw w_k w_sv w_ipc w_opc w_oc w_dl].
(* the loop runs on the context with the allocator's bound raised for the window limit (S3Main.mem_call) *)
sep_apply (@ctx_rep3_raise CMI DENT TABS (a_gv a) (a_d a) k (dp_wmax (dc_par (a_st a)))).
entailer!.
Qed.

End CM_Q3ProE_1.
