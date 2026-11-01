(* FS3-bl BODY stage 1: FORWARD_IF_ERROR(ZSTD_decodeFrameHeader(dctx, dctx->headerBuffer,
   dctx->headerSize)): the error return, or the state s1_Q. *)
Require Import Zstd.proof.dec.v3.FS.BL.body.s1.S1Defs.
Local Open Scope logic.

Section CM_S1Loop_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s1_loop_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z),
  s1_hyps pr W od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (s1_pre_loop DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts
       (s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)) shk shd ob osz oc shs src c v_bp)
    s1_loop
    (overridePost
       (s1_Q DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) (pcs + Zlength c) (bv_hdr v ++ c) ts
          (s1_hb hb c (starting_len (md_magicless (dmode_of pr))) (bv_hs v)) shk shd ob osz oc shs src c v_bp)
       (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c))).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs Hh.
  destruct Hh as (Hpr & Hpre & Hci0 & Hmr & Hmd & Hst & Hpcs & Hpcsr & Hsz & Hlay & Hfp).
  pose proof Hci0 as Hci.
  destruct Hci as (Hexp & Her & Hstg & Hifd & Hcold & Hdid & Hpcs' & Hds & Hhb & Hwf & Hcs & Hly).
  cbv [bl_cstage] in Hcs; rewrite Hst in Hcs; destruct Hcs as (Hhl & Hhok & Hhb5 & Hhs & Hfhs & He & Hnsk0).
  unfold bl_size_ok in Hsz; rewrite Hst in Hsz.
  destruct Hpre as (Hne & Hho & Hoz & Hbo & Hbs & Hbd & Hwd & Hrs & Hrk & Hop & Hosz & Hoc & Hcl & Hcb).
  destruct (s1_fs1_eq fs ob osz opos pcs (Zlength c)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  assert (Hn: 0 < Zlength c) by lia.
  destruct (s1_hsize_rng (dmode_of pr) v Hhl Hhs ltac:(lia)) as (Hsl & Hhs18).
  pose proof (s1_did_rng _ _ _ _ _ _ _ Hci0) as Hdr.
  set (mg := md_magicless (dmode_of pr)) in *. set (sl := starting_len mg) in *.
  set (hb' := s1_hb hb c sl (bv_hs v)).
  set (fs1 := bl_fs1 fs ob osz opos pcs (Zlength c)) in *.
  set (q := field_address t_dctx (DOT _headerBuffer) p).
  assert (Hwin: win_ok Ews 18 hb' 0 (bv_hs v) (bv_hdr v ++ c)) by (apply s1_hb_win; auto; lia).
  assert (Hlen: Zlength (bv_hdr v ++ c) = bv_hs v) by (rewrite Zlength_app; lia).
  unfold s1_pre_loop, s1_Q, bl_R, bl_post. s1_delta. unfold s1_loop. abbreviate_semax.
  assert_PROP (field_compatible (tarray tuchar 18) [] q) as Hfc by entailer!.
  apply semax_loop_nocontinue.
  sep_apply (s1_fcore3_split p fs1 pr). Intros.
  rewrite E1, Hfhs.
  freeze FR := (pws_pred W) (TABS gv p (bd_oxo od) ts) (dent_of DENT gv (bd_oxo od)) (bd_res shk od)
    (data_at shd _ _ ob) (data_at shs _ _ src).
  forward.
  sep_apply (s1_fcore3_join_hs p fs1 pr (vlong (bv_hs v)) Hpr ltac:(rewrite E1; exact Hfhs)).
  forward_call (gv, p, fs1, bd_idz od, pcs + Zlength c, pr, nullval, df_none, @nil (val * ddict_st), @nil val,
                @None (val * val), Ews, q, 18, hb', 0, bv_hdr v ++ c, @None cmem, 0).
  { unfold q, field_address in Hfc.
    destruct (field_compatible_dec t_dctx (DOT _headerBuffer) p) as [Hf |];
      [exact (field_compatible_isptr _ _ _ Hf) | destruct Hfc; contradiction]. }
  { entailer!. simpl. unfold q, field_address in *.
    destruct (field_compatible_dec t_dctx (DOT _headerBuffer) p) as [Hf | Hf];
      [| destruct Hfc as (Hfc & _); contradiction Hfc].
    rewrite Hlen. reflexivity. }
  { rewrite s1_sel_res_emp. cancel. }
  { unfold sel_mem, sel_on; rewrite andb_false_r; split; intros; discriminate. }
  assert (Hsel: sel_on pr nullval = false) by (unfold sel_on; apply andb_false_r).
  Intros vret. destruct vret as [[r fs'] d']. cbn [fst snd]. rewrite Hsel in *. rewrite s1_sel_res_emp.
  forward.
  forward_call r.
  cbn [fst snd] in H, H0.
  destruct (is_error_code r) eqn:Er.
  - forward_if; [| exfalso; match goal with Hz: Int.repr 1 = Int.zero |- _ => discriminate Hz end].
    apply seq_assoc1, s1_skiploop, seq_assoc1, s1_ifloop, seq_assoc1, s1_skiploop, seq_assoc1, s1_skiploop.
    thaw FR.
    forward.
    destruct (s1_err_pure (dmode_of pr) od osz0 ba fs ts hb v c ob (Zlength oc) opos oc pcs df_none nil nil r fs' d'
                Hci0 Hmr Hmd Hst Hcb Hfp H0 Er) as (Hcold1 & Hfp1 & Hclm).
    Exists r oc ba fs' (TInit (bd_oxo od) ts) hb'. unfold tabs_rep.
    entailer!.
    unfold q; rewrite s1_hb_eq; cancel.
  - forward_if; [exfalso; match goal with Hz: Int.repr 0 <> Int.zero |- _ => exact (Hz eq_refl) end |].
    forward.
    thaw FR.
    Exists r fs' d'. entailer!.
Qed.

End CM_S1Loop_1.
