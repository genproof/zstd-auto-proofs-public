(* FS3-bl BODY: stage 2 (ZSTDds_decodeBlockHeader): ZSTD_getcBlockSize, blockSizeMax check, empty blocks.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s2.BLS2X.
Local Open Scope logic.

Section CM_BLStage2_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage2_ok : bl_case_spec (fun v => bv_stage v = BBlkHdr) 2.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfo Hv Hst Hpcs Hpcsr Hsz Hlay.
  unfold bl_size_ok in Hsz. rewrite Hv in Hsz.
  pose proof Hci as (_ & _ & _ & _ & Hcold & _ & _ & _ & Hhb & _ & Hcs & _).
  cbv [bl_cstage] in Hcs. rewrite Hv in Hcs. destruct Hcs as [Hhf He3].
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & Hrs & _ & Hop & _ & _ & _ & Hbc).
  assert (Hc3: Zlength c = 3) by (rewrite Hsz, He3; reflexivity).
  rewrite bl2_cmd_eq.
  apply semax_seq with (Q := FF); [| apply semax_ff].
  apply <- seq_assoc.
  apply semax_seq with (Q := EX cs: Z, !! (cblock_size c = Some cs) &&
    bl2_mid DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src c
      v_bp cs).
  2:{ apply extract_exists_pre; intros cs. apply semax_extract_prop; intros Ec.
      eapply bl2_x_ok; eauto. }
  unfold bl_case_pre, bl_R, bl_post. simplify_func_tycontext. unfold bl2_a, bl2_b. abbreviate_semax.
  assert_PROP (isptr src) as Hsrc by entailer!.
  freeze FR1 := (pws_pred W) (TABS gv p (bd_oxo od) ts) (field_at Ews t_dctx (DOT _headerBuffer) _ p)
    (dent_of DENT gv (bd_oxo od)) (bd_res shk od) (data_at shd _ _ ob).
  unfold zstd_globals. Intros.
  forward.
  sep_apply (zstd_globals_fold3 gv).
  forward_call (gv, Tsh, v_bp, shs, src, Zlength c, zbytes c, 0, c).
  { rewrite isptr_offset_val_zero by auto. rewrite Hc3. unfold ZSTD_blockHeaderSize_val. entailer!. }
  { unfold win_ok. rewrite Zlength_map, sublist_same by (rewrite ?Zlength_map; lia).
    repeat split; auto; lia. }
  Intros vret. destruct vret as [r bv]; cbn [fst snd] in *.
  match goal with Hm: match cblock_size _ with Some _ => _ | None => _ end |- _ => rename Hm into Hcb end.
  match goal with Hm: 0 <= r <= Int64.max_unsigned |- _ => rename Hm into Hr end.
  forward.
  forward_call r.
  freeze FR2 := (zstd_globals gv) (data_at shs _ _ src).
  forward_if.
  { (* getcBlockSize failed *)
    assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
    assert (Hcn: cblock_size c = None).
    { destruct (cblock_size c) as [k |] eqn:Ek; auto. exfalso. destruct Hcb as [-> _].
      pose proof (cblock_size_range3 _ _ Hbc Ek). unfold is_error_code in Er. apply Z.ltb_lt in Er. lia. }
    forward.
    thaw FR2. thaw FR1.
    sep_apply (data_at_data_at_ Tsh t_bp bv v_bp).
    Exists r oc ba (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) (TInit (bd_oxo od) ts) hb.
    unfold tabs_rep.
    pose proof Hfo as Hfo1. rewrite <- (bl_fs1_fParams fs ob (Zlength oc) opos pcs (Zlength c)) in Hfo1.
    entailer!.
    split; [apply bh_cold; auto |].
    eapply bh_err_claim; eauto. }
  assert (Ner: is_error_code r = false).
  { destruct (is_error_code r); [| reflexivity]. exfalso.
    match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
  destruct (cblock_size c) as [cs |] eqn:Ec; [| destruct Hcb as [Hcb' _]; rewrite Hcb' in Ner; discriminate].
  destruct Hcb as [-> ->].
  thaw FR2. thaw FR1.
  forward. Exists cs. unfold bl2_mid. entailer!.
Qed.

End CM_BLStage2_1.
