(* FS3-bl BODY stage 6: the tail of ZSTDds_decodeSkippableHeader after MEM_readLE32 (expected := the size,
   stage := 7, return 0), split from BLStage6 for its check time. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s6.S6Pure.
Require Import Zstd.proof.dec.v3.FS.BL.body.s6.S6Delta.
Local Open Scope logic.

Section CM_S6Tail_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the statements left after the call of MEM_readLE32: expected := t'19, then stage := 7; return 0 *)
Definition s6_asg : statement :=
  ltac:(let b := eval cbv [bl_cmd] in (bl_cmd 6) in
        lazymatch b with context [LScons (Some 6) (Ssequence _ (Ssequence (Ssequence _ ?asg) _)) _] => exact asg end).
Definition s6_tl : statement :=
  ltac:(let b := eval cbv [bl_cmd] in (bl_cmd 6) in
        lazymatch b with context [LScons (Some 6) (Ssequence _ (Ssequence (Ssequence _ _) ?tl)) _] => exact tl end).

Lemma s6_tail_ok {Espec: OracleKind} (REST: statement) DENT TABS SR BR' W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
    v_bp v pcs st :
  par_ok pr -> bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v ->
  bd_model_ok (ba_dict ba) od -> fp_ok (fs_fParams fs) -> bv_stage v = BSkipHdr ->
  Zlength c = 3 -> bytes_ok c -> bl_hist_ok ba ob opos oc -> 0 <= opos <= osz -> Zlength oc = osz ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  Zlength hb = 18 -> Zlength (bv_hdr v) = 5 -> sublist 0 5 hb = zbytes (bv_hdr v) -> bytes_ok (bv_hdr v) ->
  field_compatible (tarray tuchar 18) [] (field_address t_dctx (DOT _headerBuffer) p) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
   (PROP ( )
    LOCAL (temp _t'19 (Vint (Int.repr (le_field (bv_hdr v ++ c) 4 4))); temp _t'20 (Vint (Int.repr st));
    lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
    gvars gv; temp _dctx p; temp _dst (offset_val opos ob);
    temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
    temp _src src; temp _srcSize (Vlong (Int64.repr 3)))
    SEP (data_at Ews (tarray tuchar (Zlength (bv_hdr v ++ c))) (zbytes (bv_hdr v ++ c))
           (field_address t_dctx (DOT _headerBuffer) p);
    data_at Ews (tarray tuchar 10) (sublist 8 18 hb) (offset_val 8 (field_address t_dctx (DOT _headerBuffer) p));
    data_at shs (tarray tuchar 3) (zbytes c) src;
    field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs 3)) p;
    field_at Ews t_dctx (DOT _bType) (fs_bType (bl_fs1 fs ob osz opos pcs 3)) p;
    field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs 3)) p;
    s6_fc_rest p (bl_fs1 fs ob osz opos pcs 3) pr;
    data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
    pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
    dent_of DENT gv (bd_oxo od); bd_res shk od;
    data_at shd (tarray tuchar osz) oc ob))
   (Ssequence s6_asg (Ssequence s6_tl REST))
   (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).
Proof.
  intros Hpr Hci0 Hmr Hmd Hfp Hst Hc3 Hcb Hho Hop Hoc Hlay Hhb Hhl Hhb5 Hhok Hfc.
  unfold s6_asg, s6_tl, bl_R, bl_post; s6_simplify; abbreviate_semax.
  pose proof (s6_le_field_range (bv_hdr v ++ c) 4 ltac:(apply Forall_app; auto)) as He'.
  set (e' := le_field (bv_hdr v ++ c) 4 4) in *.
  forward. forward.
  gather_SEP (data_at _ (tarray tuchar (Zlength _)) _ _) (data_at _ (tarray tuchar 10) _ _).
  rewrite <- (s6_hb_read hb (bv_hdr v) c) by auto.
  rewrite s6_hb_eq.
  rewrite Int.unsigned_repr by rep_lia.
  sep_apply (s6_fcore3_join7 p (bl_fs1 fs ob osz opos pcs 3) pr e' Hpr).
  change (fsu_stage (fsu_expected (bl_fs1 fs ob osz opos pcs 3) (vlong e')) (Vint (Int.repr 7)))
    with (s6_fs fs ob osz opos pcs e').
  forward.
  pose proof (s6_post_pure (dmode_of pr) od (Zlength oc) osz0 ba fs ts hb v ob opos oc c pcs
                Hho Hop eq_refl Hci0 Hmr Hmd Hfp Hst Hc3 Hcb Hlay) as P.
  cbv zeta in P. rewrite !Z.add_0_r in P.
  Exists 0 oc (s6_ba ba c e' ob opos) (s6_fs fs ob (Zlength oc) opos pcs e') (TInit (bd_oxo od) ts) (s6_hb hb c).
  rewrite !Z.add_0_r. unfold tabs_rep. rewrite Hc3.
  apply andp_right.
  { apply prop_right. destruct P as (P1 & P2 & P3 & P4 & P5 & P8 & P6 & P7).
    exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P8 (conj P6 (conj P7 eq_refl)))))))). }
  cancel.
Qed.

End CM_S6Tail_1.
