(* FS3 streaming: one iteration of the loop of ZSTD_decompressStream (read streamStage, the
   switch), from the cases seg_case_x 0..4 (with the exact claim) (helper of body3_stream_main.v, v2 body_stream_main.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main.
Local Open Scope logic.

Section CM_ds_body3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma c3_core_stage : forall stable obuf sout k sv,
  c_core stable obuf sout k sv -> 0 <= sf_stage (c3_s k) <= 4.
Proof.
intros stable obuf sout k sv H. unfold c_core in H. destruct H as (_ & _ & _ & H).
destruct (sf_stage (c3_s k) =? zdss_init) eqn:E1; [apply Z.eqb_eq in E1; unfold zdss_init in E1; lia|].
destruct (sf_stage (c3_s k) =? zdss_loadHeader) eqn:E2; [apply Z.eqb_eq in E2; unfold zdss_loadHeader in E2; lia|].
destruct H as [H _]. unfold zdss_read, zdss_load, zdss_flush in H. lia.
Qed.

Definition ds_body3 : statement := match ds_loop with Sloop (Ssequence _ b) _ => b | _ => Sskip end.

Lemma ds_body3_ok : forall (Espec: OracleKind) DENT TABS BR (A: dsa) (w: lw) (R: ret_assert),
  (forall k, 0 <= k <= 4 -> seg_case_x k) ->
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok A -> start_ok A ->
  call_inv A (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 0 \/ w_smw w = 1 ->
  loop_extra w -> entry_ok A w -> untouched_ok A w -> ex_call A w -> w_smw w <> 0 ->
  RA_normal R = ds_inv_x DENT TABS A -> RA_return R = RA_return (ds_R_x DENT TABS BR A) ->
  semax (ds_Delta DENT TABS BR) (PROPx [] (LOCALx (ds_LI_L A w) (SEPx (ds_LI_S DENT TABS A w)))) ds_body3 R.
Proof.
intros Espec DENT TABS BR A w R Hcase HD HT HA Hstart Hinv Hsmw Hex Hentry Hun Hx HRE' HRn HRr.
unfold ds_Delta, ds_body3, ds_loop. simplify_func_tycontext.
match goal with |- semax _ _ ?c _ => let c' := eval cbv beta iota delta [Swhile] in c in change c with c' end.
assert (Hst: 0 <= sf_stage (c3_s (w_k w)) <= 4).
{ pose proof Hinv as Hc. unfold call_inv in Hc.
  repeat match type of Hc with _ /\ _ =>
    first [ let Hcc := fresh in destruct Hc as [Hcc _]; apply c3_core_stage in Hcc; exact Hcc
          | destruct Hc as [_ Hc] ] end. }
assert (Hsmw1: w_smw w = 1) by lia.
unfold ds_LI_S, ctx_rep3, ctx_body3, sgroup. Intros.
unfold ds_LI_L. forward.
apply (semax_switch_PQR (sf_stage (c3_s (w_k w)))); [reflexivity | entailer! | entailer! | ].
rewrite ds_select by lia.
eapply semax_pre;
  [| apply (Hcase _ Hst Espec DENT TABS BR A w R HD HT HA Hinv Hsmw1 Hex eq_refl)].
+ unfold ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, sgroup. go_lower.
  rewrite (prop_true_andp (0 <= sf_inSize (c3_s (w_k w)) /\ _)) by tauto.
  apply andp_right; [apply prop_right; rewrite ?eqb_type_refl; repeat split; auto |].
  cancel.
+ exact HRn.
+ exact HRr.
+ exact Hstart.
+ exact Hentry.
+ exact Hun.
+ exact Hx.
Qed.

End CM_ds_body3_1.
