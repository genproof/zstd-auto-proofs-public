(* FS3-bl: ZSTD_decompressContinue's API specification from its internal one (DC3_of unpacked, BR = BLDefs.BR).
   Helpers: sub/SubFacts.v (the API frame vs the body's view), sub/SubSep.v (the context
   and the dictionary's memory split and joined). *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Require Import Zstd.proof.dec.v3.FS.BL.sub.SubSep.
Local Open Scope logic.

Section CM_BLSub_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma base_rel3_cont (st: dctx_st) (k: cst3) (ba: Spec_api6.blabs) fs t hb (ob: option Spec_api6.blabs) (x: bool) :
  base_rel3 st k -> dc_bl st = Some ba -> fp_ok (fs_fParams fs) ->
  (ob <> None -> fs_isFrameDecompression fs = Vint (Int.repr 1)) ->
  base_rel3 (set_ex (set_bl st ob) x) (c3_bl k fs t hb).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & _ & H6 & H7 & Hm) Hb Hfp Hi.
  assert (Hss: dc_ss st = ss_init) by (apply H7; rewrite Hb; discriminate).
  unfold base_rel3, set_ex, set_bl, c3_bl, c3_with_s, c3_with_fs, sf_with_hbuf; simpl.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [exact H4|]. split; [exact H5|]. split; [exact Hfp|]. split; [exact H6|].
  split; [intros Hn; split; [exact Hss | exact (Hi Hn)] | exact Hm].
Qed.

Lemma BR_cont (pr: dparams) (od: option bldict) (osz: Z) (ba: Spec_api6.blabs) (ba': blabs) fs ts hb :
  par_ok pr -> bd_rel (Spec_api6.ba_dict ba) od -> ba_dict ba' = Spec_api6.ba_dict ba ->
  BRc (dmode_of pr) od osz ba' fs ts hb ->
  BR pr (bl_glob ba' osz) fs (TInit (bd_oxo od) ts) hb.
Proof.
  intros Hp Hr Hd Hc. split; [exact Hp|]. exists od, osz, ts.
  split; [reflexivity|]. split; [apply bl_osz_glob|].
  split; [unfold bl_glob; simpl; rewrite Hd; exact Hr|].
  rewrite bl_loc_glob. exact Hc.
Qed.

Lemma BL_cont_sub : forall (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3),
  DENT_OK DENT -> TABS_OK TABS ->
  funspec_sub (snd (ZSTD_decompressContinue_ispec DENT TABS))
              (snd (ZSTD_decompressContinue_aspec (DC3x DENT TABS SR BR) (DD3x DENT))).
Proof.
  intros DENT TABS SR HD HT.
  apply NDsubsume_subsume; [split; reflexivity|].
  split; [split; reflexivity|].
  intros [[[[[[[[[[[[[W gv] d] st] ba] shk] shd] ob] osz] opos] oc] shs] src] c] [g args]. simpl.
  unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
  rename H into Harg, H0 into Hbl, H1 into Hexp, H2 into Hhist, H3 into Hset, H4 into Hbd, H5 into Hbs,
    H6 into Hdk, H7 into Hwd, H8 into Hrs, H9 into Hrk, H10 into Hop, H11 into Hosz30, H12 into Hloc,
    H13 into Hc30, H14 into Hcb.
  unfold DC3x at 1, DC3_of. unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
  rename H into Hb3, H0 into Hsr, H1 into Hbr.
  (* the call clears dc_ex: the exact relation of the context before is not needed *)
  match goal with Hx: ex_on3 _ _ _ |- _ => clear Hx end.
  pose proof (Hbr ba Hbl) as HBRp.
  destruct HBRp as [Hpar [od [osz0 [ts [Ht [Hoz [Hrel HBRc]]]]]]].
  assert (Hfp: fp_ok (fs_fParams (c3_fs k))) by (destruct Hb3 as (_ & _ & _ & _ & _ & Hf & _); exact Hf).
  assert (Hsetk: c3_set k = nil) by (destruct Hb3 as (_ & _ & E & _); rewrite E; exact Hset).
  assert (Hpst: c3_par k = dc_par st) by (destruct Hb3 as (_ & E & _); exact E).
  destruct (bl_hist_loc ba ob (Zlength oc) opos oc Hhist) as [Hh Hos].
  assert_PROP (dict_ref_ptr (Spec_api6.ba_dict ba)) as Hrp.
  { apply andp_left2. sep_apply (dict_res_ref_ptr DENT gv shk (Spec_api6.ba_dict ba)). entailer!. }
  eapply derives_trans;
    [apply andp_derives; [apply derives_refl |
       sep_apply (ctx3_split DENT TABS gv d k); sep_apply (dict_split DENT gv shk (Spec_api6.ba_dict ba) od Hrel);
       apply derives_refl] |].
  normalize. rename H into Hcold, H0 into Hhb.
  assert_PROP (c3_sp k = nullval) as Hsp.
  { apply andp_left2. unfold ctx_rest3. rewrite Hsetk.
    sep_apply (hset_nil_null (sf_mem (c3_s k)) (c3_sp k) (sf_held (c3_s k) - local_held (c3_dict k))). entailer!. }
  assert_PROP (dict_ref_buf (Spec_api6.ba_dict ba)) as Hrb.
  { apply andp_left2. sep_apply (dict_rest_buf (Spec_api6.ba_dict ba)). entailer!. }
  rewrite Ht. simpl tabs_rep. rewrite Hsp.
  Exists (W, gv, d, c3_par k, od, osz0, bl_loc ba, c3_fs k, ts, sf_hbuf (c3_s k), bd_sh shk (Spec_api6.ba_dict ba),
          shd, ob, Zlength oc, opos, oc, shs, src, c)
    (ctx_rest3 DENT gv d k * dict_rest (Spec_api6.ba_dict ba)).
  simpl.
  apply andp_right.
  { unfold LOCALx, argsassert2assert; simpl. entailer!.
    - split; [| split].
      + intros Hn. destruct (Spec_api6.ba_out ba) as [[[[ob' o] f] pe]|] eqn:Eo; [| contradiction].
        assert (E1: bl_osz ba = Some o) by (unfold bl_osz; rewrite Eo; reflexivity).
        rewrite <- (Hos o E1). apply (Hoz o E1).
      + exact (bd_buf_conv W shk _ od shd (Zlength oc - opos) (offset_val opos ob) Hrel Hrb Hdk).
      + apply bd_sh_readable; auto.
    - unfold local, lift1; simpl. Intros. rewrite prop_true_andp by auto. cancel. }
  apply prop_right. intros rho'.
  unfold local, lift1; simpl. normalize.
  rename x into r, x0 into oc', x1 into ba', x2 into fs', x3 into t', x4 into hb'.
  Exists r oc' (bl_glob ba' (Zlength oc)).
  unfold local, lift1; simpl. normalize.
  sep_apply (dict_join DENT gv shk (Spec_api6.ba_dict ba) od Hrel Hrp).
  rewrite <- Hsp.
  sep_apply (ctx3_join DENT TABS gv d k fs' t' hb'); auto.
  unfold DC3x, DC3_of. Exists (c3_bl k fs' t' hb').
  assert (Hss: dc_ss st = ss_init).
  { destruct Hb3 as (_ & _ & _ & _ & _ & _ & _ & H7'). apply H7'. rewrite Hbl. discriminate. }
  set (X := if is_error_code r then None else Some (bl_glob ba' (Zlength oc))).
  assert (HB: base_rel3 (set_ex (set_bl st X) false) (c3_bl k fs' t' hb')).
  { apply (base_rel3_cont st k ba); auto. intros Hn. unfold X in Hn.
    destruct (is_error_code r) eqn:Er; [contradiction|].
    destruct (H6 eq_refl) as (_ & _ & _ & _ & _ & _ & ts' & _ & Hc).
    destruct Hc as [v [Hci _]]. destruct Hci as (_ & _ & _ & HI & _). exact HI. }
  assert (HS: dc_ss (set_ex (set_bl st X) false) <> ss_init -> ss_err (dc_ss (set_ex (set_bl st X) false)) = false ->
              SR gv (set_ex (set_bl st X) false) (c3_bl k fs' t' hb') \/
              (dc_ss (set_ex (set_bl st X) false) = ss_restart /\ sf_stage (c3_s (c3_bl k fs' t' hb')) = 0)).
  { intros Hn. exfalso. apply Hn. simpl. exact Hss. }
  assert (HR: forall ba0, dc_bl (set_ex (set_bl st X) false) = Some ba0 ->
            BR (c3_par (c3_bl k fs' t' hb')) ba0 (c3_fs (c3_bl k fs' t' hb')) (c3_tabs (c3_bl k fs' t' hb')) (sf_hbuf (c3_s (c3_bl k fs' t' hb')))).
  { intros ba0 Hb0. unfold X in Hb0; simpl in Hb0. destruct (is_error_code r) eqn:Er; [discriminate|].
    inversion Hb0; subst ba0.
    destruct (H6 eq_refl) as (_ & _ & Hd & _ & _ & _ & ts' & Et & Hc).
    unfold c3_bl, c3_with_s, c3_with_fs, sf_with_hbuf; simpl. rewrite Et. apply (BR_cont (c3_par k) od (Zlength oc) ba); auto. }
  assert (HP: is_error_code r = false ->
          r <= Zlength oc - opos /\ cells_bytes (sublist opos (opos + r) oc') /\ ba_dict ba' = Spec_api6.ba_dict ba /\
          match ba_out ba' with
          | Some (ob0, f0, pe) => Some (ob0, Zlength oc, f0, pe)
          | None => None
          end = Some (ob, Zlength oc, Spec_api6.bl_start ba opos, opos + r) /\
          Spec_api6.bl_hist_ok (bl_glob ba' (Zlength oc)) ob (Zlength oc) (opos + r) oc' /\
          (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b')).
  { intros Hn. destruct (H6 Hn) as (Hr1 & Hcb' & Hd & Ho & Hhs & Hex & _).
    split; [exact Hr1|]. split; [exact Hcb'|]. split; [exact Hd|].
    split; [rewrite Ho, bl_start_loc; reflexivity|]. split; [apply bl_hist_glob; exact Hhs | exact Hex]. }
  assert (HX: ex_on3 SR (set_ex (set_bl st X) false) (c3_bl k fs' t' hb')) by (apply ex_on3_noex; reflexivity).
  assert (HC: bl_claim (dmode_of (dc_par st)) ba (bl_glob ba' (Zlength oc)) c r opos (Zlength oc) oc').
  { rewrite <- Hpst. apply bl_claim_glob. exact H7. }
  entailer!.
Qed.

End CM_BLSub_1.
