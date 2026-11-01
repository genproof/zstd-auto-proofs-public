(* FS3 streaming: the loop of ZSTD_decompressStream, from the prologue's precondition (helper of
   body3_stream_main.v, v2 body_stream_main.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.main3.ds_body3.
Local Open Scope logic.

Section CM_ds_loop3_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ds_after_pro : forall (Espec: OracleKind) DENT TABS BR (A: dsa),
  seg_prologue_x -> (forall k, 0 <= k <= 4 -> seg_case_x k) -> seg_epilogue_x ->
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok A ->
  semax (ds_Delta DENT TABS BR)
    (PROP ()
     LOCAL (lvar _op (tptr tschar) (a_vop A); gvars (a_gv A); temp _zds (a_d A);
            temp _output (a_outp A); temp _input (a_inp A))
     SEP (data_at_ Tsh (tptr tschar) (a_vop A); pws_pred (a_W A); mem_mgr (a_gv A); zstd_globals (a_gv A);
          DC3x DENT TABS SR3 BR (a_gv A) (a_d A) (a_st A);
          dict_res (DD3x DENT) (a_gv A) Ews (dc_dict (a_st A));
          set_res (DD3x DENT) (a_gv A) Ews (dc_set (a_st A)) (dc_dict (a_st A));
          data_at (a_sho A) t_outBuffer (a_obf A, (Vlong (Int64.repr (a_osz A)), Vlong (Int64.repr (a_opos A)))) (a_outp A);
          data_at (a_shi A) t_inBuffer (a_ibf A, (Vlong (Int64.repr (a_isz A)), Vlong (Int64.repr (a_ipos A)))) (a_inp A);
          data_at (a_shob A) (tarray tuchar (a_osz A)) (a_oc A) (a_ob A);
          data_at (a_shb A) (tarray tuchar (a_isz A)) (zbytes (a_ibs A)) (a_ib A)))
    (ds_prologue (Ssequence ds_loop ds_epilogue)) (ds_R_x DENT TABS BR A).
Proof.
intros Espec DENT TABS BR A Hpro Hcase Hepi HD HT HA.
apply (Hpro Espec DENT TABS BR A (Ssequence ds_loop ds_epilogue) HD HT HA).
intros w0 Hinv0 Hw0 Hex0 Hstart Hexit0 Hentry0 Hun0 Hx0.
unfold ds_Delta, ds_loop. simplify_func_tycontext.
forward_while (EX w: lw, PROPx (ds_LI_Px A w) (LOCALx (ds_LI_L A w) (SEPx (ds_LI_S DENT TABS A w)))).
- Exists w0. unfold ds_LI_Px, ds_LI_L, ds_LI_S. entailer!.
  all: try (unfold exit_ok; intros Hx; rewrite Hw0 in Hx; discriminate).
  all: try exact Hexit0. all: try exact Hentry0. all: try exact Hun0. all: try exact Hx0.
- unfold ds_LI_L, ds_LI_S. entailer!.
- (* the loop body: read streamStage, dispatch *)
  eapply (ds_body3_ok Espec DENT TABS BR A w POSTCONDITION Hcase HD HT HA Hstart); try eassumption; reflexivity.
- (* after the loop *)
  match goal with Hc: call_inv A (w_k w) _ _ _ _ _ |- _ => rename Hc into Hinv end.
  match goal with Hc: w_smw w = 0 \/ w_smw w = 1 |- _ => rename Hc into Hsmw end.
  assert (Hsmw0: w_smw w = 0) by (destruct Hsmw as [Hz|Ho]; [exact Hz | rewrite Ho in HRE; discriminate]).
  match goal with Hc: exit_ok A w |- _ => rename Hc into Hexit end.
  match goal with Hc: untouched_ok A w |- _ => rename Hc into Hun end.
  match goal with Hc: ex_call A w |- _ => rename Hc into Hx end.
  apply (Hepi Espec DENT TABS BR A w HD HT HA Hinv Hsmw0 Hstart Hexit Hun Hx).
Qed.

End CM_ds_loop3_1.
