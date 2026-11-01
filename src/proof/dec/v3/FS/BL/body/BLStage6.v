(* FS3-bl BODY: stage 6 (ZSTDds_decodeSkippableHeader): the skippable header's rest, its size.  Statement: BLCase.bl_case_spec. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.BLCase.
Require Import Zstd.proof.dec.v3.FS.BL.body.s6.S6Tail.
Require Import Zstd.proof.dec.v3.FS.BL.body.s6.S6Delta.
Local Open Scope logic.

Section CM_BLStage6_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl_stage6_ok : bl_case_spec (fun v => bv_stage v = BSkipHdr) 6.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hmd Hfp Hst Hstz Hpcs Hpcsr Hsz Hlay.
  unfold bl_case_pre, bl_cmd, bl_R, bl_post; s6_simplify; abbreviate_semax.
  cbv [select_switch select_switch_case]. simpl seq_of_labeled_statement.
  pose proof Hci as Hci0.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (Hmg & Hhl & Hhok & Hhb5 & He3).
  unfold bl_size_ok in Hsz; rewrite Hst in Hsz.
  assert (Hc3: Zlength c = 3) by (rewrite Hsz, He3; reflexivity).
  destruct Hpre as (Hne & Hho & Hoz & Hbo & Hbs & Hbd & Hwd & Hrs & Hrk & Hop & Hosz & Hoc & Hcl & Hcb).
  sep_apply (s6_fcore3_split p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  rewrite <- s6_hb_eq.
  assert_PROP (field_compatible (tarray tuchar 18) [] (field_address t_dctx (DOT _headerBuffer) p)) as Hfc by entailer!.
  rewrite (s6_hb_before hb) by auto.
  sep_apply (data_at_data_at_ Ews (tarray tuchar 3) (sublist 5 8 hb) (offset_val 5 (field_address t_dctx (DOT _headerBuffer) p))).
  rewrite Hc3.
  forward_call (shs, Ews, src, offset_val 5 (field_address t_dctx (DOT _headerBuffer) p),
                existT (fun t => reptype t) (tarray tuchar 3) (zbytes c)).
  { apply prop_right. simpl. pose proof (field_compatible_isptr _ _ _ Hfc) as Hq.
    unfold field_address in Hq |- *. destruct (field_compatible_dec t_dctx (DOT _headerBuffer) p); [|contradiction].
    destruct p; try contradiction. simpl. reflexivity. }
  { memcpy_side. }
  cbn [projT1 projT2].
  sep_apply (s6_hb_after hb c (field_address t_dctx (DOT _headerBuffer) p) Hhb Hc3 Hfc).
  change ZSTD_FRAMEHEADERSIZE_PREFIX with 5 in Hhl, Hhb5.
  rewrite (s6_hb_read hb (bv_hdr v) c) by auto.
  assert (Hrd: bytes_ok (sublist 4 (4 + 4) (bv_hdr v ++ c))).
  { apply Forall_sublist. apply Forall_app; auto. }
  forward_call (Ews, field_address t_dctx (DOT _headerBuffer) p, bv_hdr v ++ c, 4).
  { apply prop_right. simpl. pose proof (field_compatible_isptr _ _ _ Hfc) as Hq.
    unfold field_address in Hq |- *. destruct (field_compatible_dec t_dctx (DOT _headerBuffer) p); [|contradiction].
    destruct p; try contradiction. simpl. reflexivity. }
  { cancel. }
  { unfold mem_read_pre. rewrite Zlength_app, Hhl, Hc3. repeat split; auto; lia. }
  unfold MORE_COMMANDS, abbreviate.
  exact (s6_tail_ok _ DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
           Hpr Hci0 Hmr Hmd Hfp Hst Hc3 Hcb Hho Hop Hoc Hlay Hhb Hhl Hhb5 Hhok Hfc).
Qed.

End CM_BLStage6_1.
