(* FS3-bl BODY, stages 3/4, the tail: the post of the content size error at the last block (pure):
   frameContentSize != UNKNOWN && decodedSize != frameContentSize -> return -20. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TFp.
Local Open Scope logic.

Section CM_TPFcs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_fcs_pp (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (x: option (list Z)) :
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  e' = 0 -> bv_stage v = BLastBlk -> ~ t34_fcs_ok v ds r ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba (t34_fsB (t34_fsm fs ob osz opos pcs c e' cold) ds r x ob opos) t' hb.
Proof.
  intros HH Hmid Herr Hbs Hcnt Hds Hdsr He Hst Hfcs. subst e'.
  destruct HH as (Hpar & Hpre & Hcinv & Hmrel & Hbdm & Hfpo & _ & _ & _ & _ & _).
  destruct Hmid as (_ & Hlen & Hpref & Hcold & _ & Hok).
  destruct (Hok Herr) as (Hroom & _ & _ & _).
  destruct Hcnt as (_ & _ & Hcl & _ & Hfol).
  destruct Hcinv as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _ & Hcst & _).
  destruct Hpre as (_ & Hhist & _ & _ & _ & _ & _ & _ & _ & Hopos & Hosz & Hoc & _).
  unfold t34_pp.
  split; [rep_lia|]. split; [auto|]. split; [auto|]. split.
  { unfold cold01. unfold t34_fsB; cbn. exact Hcold. }
  split; [auto|]. split; [t34_fp Hfpo|]. split; [intro Hx; discriminate Hx|].
  unfold bl_claim_nc. destruct (ba_st ba) as [b|] eqn:Hb; [|exact I].
  destruct (dictref_model (ba_dict ba)) as [dm|] eqn:Hdm; [|exact I]. intro Hc.
  destruct (Hmrel b Hb) as (Hstg & Hexp & Hts & Hdsz & _ & Hm). rewrite Hst in Hm.
  destruct Hm as (Hhdr & Hbt & Hrle & _).
  unfold bl_cstage in Hcst. rewrite Hst in Hcst. destruct Hcst as (_ & _ & Hbt' & _).
  assert (Hob: 0 <= Zlength (bs_out b) <= 2 ^ 63 - 1).
  { unfold bl_hist_ok in Hhist. rewrite Hb in Hhist.
    destruct (ba_out ba) as [[[ob' f0] pe]|].
    - destruct Hhist as (_ & -> & Hf0 & Hsub). apply (f_equal (@Zlength val)) in Hsub.
      rewrite Zlength_map, Zlength_sublist in Hsub by lia. lia.
    - rewrite Hhist. rewrite Zlength_nil. lia. }
  assert (Hdseq: ds = Zlength (bs_out b)).
  { rewrite Hds in Hdsz. unfold vlong in Hdsz.
    apply (f_equal (fun w => match w with Vlong i => Int64.unsigned i | _ => 0 end)) in Hdsz.
    cbv beta iota in Hdsz. rewrite !Int64.unsigned_repr in Hdsz by rep_lia. exact Hdsz. }
  assert (Hkey: forall d content, blk_model dm b c = Some (d, content) -> bl_block_done b d content = BLErr).
  { intros d content Hbm. apply Hfol in Hbm; [| split; [exact Hb | split; [exact Hdm | lia]]].
    inversion Hbm; subst d content. unfold bl_block_done. rewrite Hhdr.
    destruct (Zlength cnt >? fh_blockSizeMax (bv_h v)) eqn:E0; [apply Z.gtb_lt in E0; lia|].
    rewrite Hstg, Hst.
    destruct (fh_contentSize (bv_h v) =? ZSTD_CONTENTSIZE_UNKNOWN) eqn:E1.
    { apply Z.eqb_eq in E1. exfalso. apply Hfcs. left. exact E1. }
    destruct (Zlength (bs_out b ++ cnt) =? fh_contentSize (bv_h v)) eqn:E2.
    { apply Z.eqb_eq in E2. exfalso. apply Hfcs. right. rewrite <- E2, Zlength_app, Hdseq, Hcl.
      apply Z.mod_small. pose proof (Zlength_nonneg cnt). rep_lia. }
    reflexivity. }
  unfold bl_step_nc. rewrite Hstg, Hst. unfold bl_step. rewrite Hstg, Hst.
  assert (Hbt3: bv_bt v = 0 \/ bv_bt v = 1 \/ bv_bt v = 2) by lia.
  destruct Hbt3 as [H0|[H0|H0]]; rewrite Hbt, H0; cbn [Z.eqb Pos.eqb].
  - rewrite (Hkey (bs_ds b) c); [reflexivity|]. unfold blk_model. rewrite Hbt, H0. reflexivity.
  - rewrite (Hkey (bs_ds b) (repeat (byte_at c 0) (Z.to_nat (bs_rle b)))); [reflexivity|].
    unfold blk_model. rewrite Hbt, H0. reflexivity.
  - destruct (decode_block _ _ _ _ _ _) as [[d content]|] eqn:Hd; [|exact I].
    rewrite (Hkey d content); [reflexivity|]. unfold blk_model. rewrite Hbt, H0. exact Hd.
Qed.

End CM_TPFcs_1.
