(* FS3-bl BODY, stages 3/4, raw block: case 0 after ZSTD_copyRawBlock: FORWARD_IF_ERROR(rSize)
   (the error returns), expected -= rSize, break (s34_mid). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.raw.RawStmt.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.comp.S34Delta.
Local Open Scope logic.

Section CM_RawAfter_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma raw_after_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel)
    W gv p pr od ba fs ts hb shk shd ob opos oc shs src c v_bp v pcs r ocm :
  par_ok pr -> bl_mrel (dmode_of pr) ba fs ts v -> (bv_stage v = BBlk \/ bv_stage v = BLastBlk) -> bv_bt v = 0 ->
  cold01 fs -> fp_ok (fs_fParams fs) -> fs_expected fs = vlong (ba_expect ba) -> 0 <= ba_expect ba < 2 ^ 32 -> Zlength hb = 18 ->
  writable_share shd -> 0 <= opos <= Zlength oc -> Zlength oc <= 2 ^ 63 - 1 -> Zlength c <= 2 ^ 30 -> bytes_ok c ->
  1 <= Zlength c <= ba_expect ba -> field_compatible (tarray tuchar (Zlength oc)) [] ob ->
  0 <= r <= Int64.max_unsigned ->
  (if Zlength (iw_s (raw_i shs src c)) >? oa_cap (mid_o (raw_o shd ob oc opos))
   then r = err_code ZSTD_error_dstSize_tooSmall /\ ocm = oa_c (mid_o (raw_o shd ob oc opos))
   else r = Zlength (iw_s (raw_i shs src c)) /\
        ocm = put_bytes (oa_c (mid_o (raw_o shd ob oc opos))) (oa_d (mid_o (raw_o shd ob oc opos)))
                (iw_s (raw_i shs src c))) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (PROP ( )
     LOCAL (temp _rSize (Vlong (Int64.repr r)); temp _t'20 (Vint (Int.repr (bl_stz (bv_stage v))));
            lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p;
            temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (Zlength oc - opos)));
            temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
     SEP (pws_pred W; pws_pred (side_W (raw_o shd ob oc opos));
          data_at (oa_sh (mid_o (raw_o shd ob oc opos))) (tarray tuchar (oa_N (mid_o (raw_o shd ob oc opos)))) ocm
            (oa_base (mid_o (raw_o shd ob oc opos)));
          data_at (iw_sh (raw_i shs src c)) (tarray tuchar (iw_N (raw_i shs src c))) (iw_c (raw_i shs src c))
            (iw_base (raw_i shs src c));
          data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; zstd_globals gv;
          fcore3 p (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) pr nullval;
          TABS gv p (bd_oxo od) ts; field_at Ews t_dctx (DOT _headerBuffer) hb p;
          dent_of DENT gv (bd_oxo od); bd_res shk od))
    (Ssequence raw_after raw_more)
    (switch_ret_assert
       (overridePost
          (s34_mid DENT TABS W gv p pr od ba (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) hb shk shd ob
             (Zlength oc) opos oc shs src c v_bp v)
          (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob (Zlength oc) opos oc shs src c)))).
Proof.
  intros H1 H4 H6 H12 Hcold Hfp Hex Hexr Hhb SHd Hop Hosz Hcl Hcb Hsz Fob Hr Hraw.
  destruct (raw_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) as [Ex1 Ec1].
  unfold bl_R, bl_post. s34c_simplify. abbreviate_semax.
  cbv [raw_after].
  set (o := raw_o shd ob oc opos) in *. set (i := raw_i shs src c) in *.
  assert (Hoo: outarr_ok o) by (unfold o, raw_o; split; [exact SHd |]; cbn; repeat split; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((is_error_code r = false) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward. forward_call r. forward_if.
    - apply dbg_skip_seq. apply dbg_if0_seq. apply dbg_skip_seq. apply dbg_skip_seq. forward.
      assert (Er: is_error_code r = true) by (destruct (is_error_code r); auto; contradiction).
      destruct (Zlength (iw_s i) >? oa_cap (mid_o o)) eqn:Eg.
      2: { exfalso. destruct Hraw as [-> _]. unfold i, raw_i in Er; cbn in Er. rewrite raw_small_noerr in Er by lia.
           discriminate. }
      destruct Hraw as [Hde ->].
      change (oa_sh (mid_o o)) with (oa_sh o). change (oa_N (mid_o o)) with (oa_cap o).
      change (oa_base (mid_o o)) with (offset_val (oa_d o) (oa_base o)).
      sep_apply (out_unsplit o); auto.
      Exists r oc ba (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) (TInit (bd_oxo od) ts) hb.
      unfold tabs_rep. entailer!.
      split; [apply raw_cold01; exact Hcold |].
      split; [rewrite bl_fs1_fParams; exact Hfp |].
      apply (raw_claim_err _ _ _ fs ts v); auto. unfold i, o, raw_i, raw_o in Eg; cbn in Eg. apply Z.gtb_lt in Eg. lia.
    - forward. entailer!. destruct (is_error_code r); auto.
      exfalso. match goal with Hz: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero Hz) end. }
  Intros. match goal with Hx: is_error_code r = false |- _ => rename Hx into Ner end.
  destruct (Zlength (iw_s i) >? oa_cap (mid_o o)) eqn:Eg.
  { exfalso. destruct Hraw as [-> _]. rewrite raw_tooSmall_err in Ner. discriminate. }
  destruct Hraw as [-> ->]. unfold i, o, raw_i, raw_o in Eg |- *.
  cbn [mid_o oa_cap oa_d oa_c oa_sh oa_N oa_base iw_s iw_sh iw_N iw_c iw_base] in Eg |- *.
  rewrite Z.gtb_ltb in Eg. apply Z.ltb_ge in Eg.
  sep_apply (fcore3_split p (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) pr). Intros.
  rewrite Ex1, Hex.
  forward. forward.
  forward.
  rewrite sub64_repr.
  pose proof (out_join o c Hoo Fob ltac:(unfold o, raw_o; cbn; lia)) as J.
  unfold o, raw_o in J; cbn [mid_o oa_sh oa_cap oa_c oa_d oa_base oa_N] in J.
  sep_apply J.
  sep_apply (raw_join p (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c)) pr (ba_expect ba - Zlength c) H1).
  unfold s34_mid.
  Exists (Zlength c) (put_bytes oc opos c) (ba_expect ba - Zlength c)
    (fs_ddictIsCold (bl_fs1 fs ob (Zlength oc) opos pcs (Zlength c))) (TInit (bd_oxo od) ts).
  unfold tabs_rep. entailer!.
  rewrite Ec1. apply (raw_mid_ok (dmode_of pr) od ba fs ts v); auto; lia.
Qed.

End CM_RawAfter_1.
