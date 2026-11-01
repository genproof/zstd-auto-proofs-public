(* FS3-bl BODY, stage 5: the branch `if (validateChecksum) { h32 = XXH64_digest; check32 = readLE32;
   if (check32 != h32) return checksum_wrong }` of case 5, from the state bl5_pth to BL5Mid.bl5_mid. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Chk.
Local Open Scope logic.

Section CM_BL5Then_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bl5_then : statement :=
  ltac:(let s := eval cbv [bl5_if] in bl5_if in
        lazymatch s with Ssequence _ (Sifthenelse _ ?t _) => exact t end).

Lemma bl5_if_eq : exists e ld, bl5_if = Ssequence ld (Sifthenelse e bl5_then Sskip).
Proof. eexists; eexists; reflexivity. Qed.

Section Pth.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition bl5_pth (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) (pcs: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'23 (Vint (Int.repr 1));
         temp _t'20 (Vint (Int.repr 5)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (field_at Ews t_dctx (DOT _validateChecksum) (Vint (Int.repr 1)) p;
       xxh_field p (fs_xxh (bl_fs1 fs ob osz opos pcs (Zlength c)));
       field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       bl5_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

End Pth.

Lemma bl5_then_ok (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) :
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> fp_ok (fs_fParams fs) ->
  bv_stage v = BCk -> bl_val (md_ignore (dmode_of pr)) (bv_h v) = true ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl5_pth DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp pcs)
    bl5_then
    (overridePost (bl5_mid DENT TABS W gv p pr od fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs)
       (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    Hpr Hpre Hci Hmr Hfpo Hst Hval Hsz.
  unfold bl5_pth, bl5_then; simplify_func_tycontext; abbreviate_semax.
  pose proof Hci as Hci'.
  destruct Hci' as (Hexp & Hexr & Hstg & Hifd & Hcold & Hdid & _ & (ds & Hds & Hdsr) & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs. rewrite Hst in Hcs. destruct Hcs as ((Hhok & Hfp & Hvc & Hxs) & Hck & He4).
  rewrite Hval in Hvc.
  unfold bl_size_ok in Hsz. rewrite Hst, He4 in Hsz.
  pose proof Hpre as Hpre'.
  destruct Hpre' as (_ & _ & _ & _ & Hbs & _ & _ & Hrs & _ & Hop & Hosz & Hoc & _ & Hbc).
  destruct (bl5_fs1 fs ob osz opos pcs (Zlength c)) as (Fv & Fx & Fd & Fp & Fi & Fdi & Fc & Ff).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  assert (Hc1: cold01 fs1) by (unfold cold01; rewrite Fc; exact Hcold).
  assert (Hfp1: fp_ok (fs_fParams fs1)) by (rewrite Ff; exact Hfpo).
  assert_PROP (field_compatible t_dctx (DOT _expected) p) as Fce by entailer!.
  assert (Fcx: field_compatible t_dctx (DOT _xxhState) p).
  { apply field_compatible_cons in Fce. apply field_compatible_cons. simpl in Fce |- *.
    split; [| tauto]. unfold in_members. simpl. repeat (first [left; reflexivity | right]). }
  freeze [6; 7; 8; 9; 10; 11; 12; 13; 14] FR.
  destruct (Hxs Hval) as [l Hl].
  rewrite Fx, Hl. unfold xxh_field.
  apply -> seq_assoc.
  forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, l).
  forward.
  forward_call (shs, src, c, 0).
  { entailer!. }
  { unfold mem_read_pre. split; [auto | split; [lia | split; [lia |]]]. apply Forall_sublist; auto. }
  thaw FR.
  eapply semax_pre;
    [| exact (bl5_chk_ok Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c
                v_bp v pcs l Hpr Hpre Hci Hmr Hfpo Hst Hval Hl)].
  change (bl_fs1 fs ob osz opos pcs (Zlength c)) with fs1.
  entailer!.
Qed.

End CM_BL5Then_1.
