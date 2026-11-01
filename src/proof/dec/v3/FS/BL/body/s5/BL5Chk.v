(* FS3-bl BODY, stage 5: the check `if (check32 != h32) return checksum_wrong` of the then-branch (after
   XXH64_digest and MEM_readLE32), split from BL5Then for check time. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Mid.
Local Open Scope logic.

Section CM_BL5Chk_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the then-branch after its two calls *)
Definition bl5_chk : statement :=
  ltac:(let s := eval cbv [bl5_if bl5_s5 bl_switch] in bl5_if in
        lazymatch s with Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ ?r)) _) => exact r end).

End CM_BL5Chk_1.


(* a DEBUGLOG loop (BL5Facts.bl5_dw_skip / bl5_dw_if0) *)
Ltac bl5_dw :=
  repeat apply -> seq_assoc;
  first [ apply bl5_dw_skip | apply bl5_dw_if0 ];
  try (match goal with |- semax _ _ ?c _ => is_var c; subst c end; unfold abbreviate).

Section CM_BL5Chk_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma bl5_chk_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (l: list Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> fp_ok (fs_fParams fs) ->
  bv_stage v = BCk -> bl_val (md_ignore (dmode_of pr)) (bv_h v) = true -> fs_xxh fs = Some l ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (PROP ()
     LOCAL (temp _check32 (Vint (Int.repr (le_field c 0 4)));
            temp _h32 (Vint (Int.repr (Int64.unsigned (Int64.repr (xxh64_digest_model 0 l)))));
            temp _t'23 (Vint (Int.repr 1)); temp _t'20 (Vint (Int.repr 5));
            lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p;
            temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
            temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
     SEP (data_at shs (tarray tuchar (Zlength c)) (zbytes c) src;
          xxh64_state Ews 0 l (field_address t_dctx (DOT _xxhState) p);
          field_at Ews t_dctx (DOT _validateChecksum) (Vint (Int.repr 1)) p;
          field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
          field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
          field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
          field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
          bl5_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
          data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
          pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
          field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
          data_at shd (tarray tuchar osz) oc ob))
    bl5_chk
    (overridePost (bl5_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs)
       (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs l
    Hpr Hpre Hci Hmr Hfpo Hst Hval Hl.
  unfold bl5_chk, bl_R, bl_post; simplify_func_tycontext; abbreviate_semax.
  pose proof Hci as Hci'.
  destruct Hci' as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs. rewrite Hst in Hcs. destruct Hcs as ((Hhok & Hfp & Hvc & Hxs) & Hck & He4).
  rewrite Hval in Hvc.
  pose proof Hpre as Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & Hbs & _ & _ & Hrs & _ & Hop & Hosz & Hoc & _ & Hbc).
  destruct (bl5_fs1 fs ob osz opos pcs (Zlength c)) as (Fv & Fx & Fd & Fp & Fi & Fdi & Fc & Ff).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  assert (Hc1: cold01 fs1) by (unfold cold01; rewrite Fc; exact Hcold).
  assert (Hfp1: fp_ok (fs_fParams fs1)) by (rewrite Ff; exact Hfpo).
  freeze [7; 8; 9; 10; 11; 12; 13; 14; 15] FR.
  bl5_dw.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_loop (PROPx P (LOCALx Q (SEPx R)))
      break: (PROPx ((le_field c 0 4 = xxh64 l 0 mod 2 ^ 32) :: P) (LOCALx Q (SEPx R))) end.
  { entailer!. }
  { forward_if.
    - bl5_dw. bl5_dw. bl5_dw. bl5_dw.
      forward.
      thaw FR.
      sep_apply (bl5_xxh_fold p fs1 l (eq_trans Fx Hl)).
      sep_apply (bl5_fold_same p fs1 pr (Vint (Int.repr 1)) (fs_decodedSize fs1) (fs_processedCSize fs1) Hpr
                   ltac:(rewrite Fv, Hvc; reflexivity) eq_refl eq_refl).
      Exists (2 ^ 64 - 22) oc ba fs1 (TInit (bd_oxo od) ts) hb.
      unfold tabs_rep. entailer!.
      try (split; [exact Hc1 |]).
      try (split; [exact Hfp1 |]).
      split; [intros X; vm_compute in X; discriminate X |].
      split; [| f_equal; apply Int64.eqm_samerepr; exists (-1); reflexivity].
      assert (Hle := bl5_lef_range c 0 4 Hbc ltac:(lia)).
      eapply bl5_err_claim; [exact Hmr | exact Hst | exact Hval | exact Hl | | reflexivity].
      intros E. match goal with Hn: Int.repr _ <> Int.repr _ |- _ => apply Hn end.
      rewrite bl5_digest_eq. apply bl5_ck_iff; [rep_lia | exact E].
    - forward. entailer!.
      assert (Hle := bl5_lef_range c 0 4 Hbc ltac:(lia)).
      rewrite bl5_digest_eq in *.
      apply bl5_ck_iff; [rep_lia |].
      match goal with Hn: ~ (Int.repr _ <> Int.repr _) |- _ => apply Classical_Prop.NNPP in Hn; exact Hn
                 | Hn: Int.repr _ = Int.repr _ |- _ => exact Hn end. }
  Intros. thaw FR.
  sep_apply (bl5_xxh_fold p fs1 l (eq_trans Fx Hl)).
  unfold bl5_mid. change (bl_fs1 fs ob osz opos pcs (Zlength c)) with fs1. rewrite Hval.
  entailer!. exists l. auto.
Qed.

End CM_BL5Chk_2.
