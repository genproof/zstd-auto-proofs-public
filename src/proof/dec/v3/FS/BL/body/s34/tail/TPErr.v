(* FS3-bl BODY, stages 3/4, the tail: the posts of the two first error returns (pure).
   FORWARD_IF_ERROR(rSize): return rSize (an error); rSize > fParams.blockSizeMax: return -20. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TFp.
Local Open Scope logic.

Section CM_TPErr_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma tpe_step_eq md dm b c :
  bs_stage b = BBlk \/ bs_stage b = BLastBlk ->
  bl_step_nc md dm b c =
  match blk_model dm b c with
  | Some (ds', cnt) => bl_block_done b ds' cnt
  | None => if bs_btype b =? 2 then BLUnk else BLErr
  end.
Proof.
  intros H. unfold bl_step_nc, bl_step, blk_model.
  destruct H as [H|H]; rewrite H;
  (destruct (bs_btype b =? 0); [reflexivity|]);
  (destruct (bs_btype b =? 1); [reflexivity|]);
  (destruct (bs_btype b =? 2); try reflexivity);
  destruct (decode_block _ _ _ _ _ _) as [[? ?]|]; reflexivity.
Qed.

Lemma tpe_done_cases b ds cnt :
  bl_block_done b ds cnt = BLErr \/ exists b', bl_block_done b ds cnt = BLOk b' cnt.
Proof.
  unfold bl_block_done.
  destruct (Zlength cnt >? fh_blockSizeMax (bs_hdr b)); [left; reflexivity|].
  destruct (bs_stage b); try (right; eexists; reflexivity).
  destruct (_ && _)%bool; [left; reflexivity|].
  destruct (bl_frame_end b); right; eexists; reflexivity.
Qed.

Lemma tpe_done_big b ds cnt :
  fh_blockSizeMax (bs_hdr b) < Zlength cnt -> bl_block_done b ds cnt = BLErr.
Proof.
  intros H. unfold bl_block_done.
  replace (Zlength cnt >? fh_blockSizeMax (bs_hdr b)) with true by (symmetry; apply Z.gtb_lt; lia).
  reflexivity.
Qed.

Lemma t34_err_pp (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) :
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = true ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c r oc' ba (t34_fsm fs ob osz opos pcs c e' cold) t' hb.
Proof.
  intros HH Hm Herr.
  destruct HH as (_ & _ & Hci & Hmr & _ & Hfpo & Hstg & _).
  destruct Hm as (Hr & Hl & Hs & Hc & He & _).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _).
  pose proof (t34_fsm_fields fs ob osz opos pcs c e' cold) as Hf; cbv zeta in Hf.
  destruct Hf as (_ & _ & _ & _ & _ & _ & Hcold & _).
  unfold t34_pp. split; [exact Hr|]. split; [exact Hl|]. split; [exact Hs|].
  split; [unfold cold01; rewrite Hcold; exact Hc|]. split; [exact Hhb|]. split; [t34_fp Hfpo|].
  split; [intros Hf; congruence|].
  unfold bl_claim_nc.
  destruct (ba_st ba) as [b|] eqn:Eb; [|exact I].
  destruct (dictref_model (ba_dict ba)) as [dm|] eqn:Ed; [|exact I].
  intros Hcl.
  specialize (He Herr b dm (conj Eb (conj Ed Hcl))).
  destruct (Hmr b Eb) as (Hbs & _).
  rewrite tpe_step_eq by (rewrite Hbs; exact Hstg).
  destruct (blk_model dm b c) as [[ds' cnt]|].
  - destruct (tpe_done_cases b ds' cnt) as [E|[b' E]]; rewrite E; [exact Herr|].
    split; [intros; congruence|]. intros _; exact He.
  - destruct (bs_btype b =? 2); [exact I|exact Herr].
Qed.

Lemma t34_bsm_pp (W: list ptr_witness) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) :
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> fh_blockSizeMax (bv_h v) < r ->
  t34_pp (dmode_of pr) od ba ob osz opos oc c (2 ^ 64 - 20) oc' ba (t34_fsm fs ob osz opos pcs c e' cold) t' hb.
Proof.
  intros HH Hm Hok Hbig.
  assert (Herr: is_error_code (2 ^ 64 - 20) = true) by (vm_compute; reflexivity).
  destruct HH as (_ & _ & Hci & Hmr & _ & Hfpo & Hstg & _).
  destruct Hm as (_ & Hl & Hs & Hc & _ & Hsu).
  destruct (Hsu Hok) as (_ & _ & _ & cnt & ts' & _ & _ & Hcnt & _ & Hx).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & Hhb & _).
  pose proof (t34_fsm_fields fs ob osz opos pcs c e' cold) as Hf; cbv zeta in Hf.
  destruct Hf as (_ & _ & _ & _ & _ & _ & Hcold & _).
  unfold t34_pp. split; [unfold Int64.max_unsigned, Int64.modulus; simpl; lia|].
  split; [exact Hl|]. split; [exact Hs|].
  split; [unfold cold01; rewrite Hcold; exact Hc|]. split; [exact Hhb|]. split; [t34_fp Hfpo|].
  split; [intros Hf; congruence|].
  unfold bl_claim_nc.
  destruct (ba_st ba) as [b|] eqn:Eb; [|exact I].
  destruct (dictref_model (ba_dict ba)) as [dm|] eqn:Ed; [|exact I].
  intros Hcl.
  specialize (Hx b dm).
  assert (Hfol: s34_fol ba c b dm) by (split; [exact Eb|split; [exact Ed|exact Hcl]]).
  destruct (Hmr b Eb) as (Hbs & _ & _ & _ & _ & Hv).
  assert (Hh: bs_hdr b = bv_h v) by (destruct Hstg as [E|E]; rewrite E in Hv; apply Hv).
  rewrite tpe_step_eq by (rewrite Hbs; exact Hstg).
  destruct (blk_model dm b c) as [[ds' cnt']|].
  - specialize (Hx _ Hfol eq_refl). inversion Hx; subst.
    rewrite tpe_done_big by (rewrite Hh; lia). exact Herr.
  - destruct (bs_btype b =? 2); [exact I|exact Herr].
Qed.

End CM_TPErr_1.
