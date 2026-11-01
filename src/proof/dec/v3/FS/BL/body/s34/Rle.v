(* FS3-bl BODY, stages 3/4: the RLE block (case 1) part (S34Defs.v). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.S34Defs.
Require Import Zstd.proof.dec.v3.FS.BL.body.s34.rle.RleHelp.
Local Open Scope logic.

Section CM_Rle_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma s34_rle_ok : s34_case_spec 1.
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs st
    Hpr Hpre Hci Hmr Hbm Hfpok Hst Hstz Hpcs Hpcsr Hsz Hlay Hbt.
  unfold bl_case_pre, bl_R, bl_post. abbreviate_semax.
  unfold s34_ls. simpl select_switch. simpl seq_of_labeled_statement.
  destruct (rle_facts _ _ _ _ _ _ _ c Hci Hst Hbt Hsz) as (Hrle & Hrr & Hc1 & Hcold).
  destruct Hpre as (_ & _ & _ & Hbo & _ & _ & Hwsd & Hrss & _ & Hop & Hosz30 & Hloc & _ & Hbc).
  (* *src *)
  assert (Hb0: 0 <= Znth 0 c <= Byte.max_unsigned).
  { unfold bytes_ok in Hbc. pose proof (proj1 (Forall_Znth _ _) Hbc 0 ltac:(lia)) as Hz. unfold is_byte in Hz. rep_lia. }
  assert (Hs1: data_at shs (tarray tuchar (Zlength c)) (zbytes c) src =
               data_at shs tuchar (Vint (Int.repr (Znth 0 c))) src).
  { rewrite Hc1. destruct c as [ | x [ | y l]]; try (rewrite ?Zlength_nil, ?Zlength_cons in Hc1; rep_lia).
    apply (data_at_singleton_array_eq shs tuchar). reflexivity. }
  rewrite Hs1.
  forward.
  { entailer!; rep_lia. }
  (* dctx->rleSize *)
  sep_apply (fcore3_split_rl p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr). Intros.
  rewrite bl_fs1_rle, Hrle. unfold vlong.
  forward.
  (* the output window *)
  set (o := {| oa_sh := shd; oa_base := ob; oa_N := osz; oa_c := oc; oa_d := opos; oa_cap := osz - opos |}).
  assert (Ho: outarr_ok o) by (unfold o, outarr_ok; cbn; split; [exact Hwsd |]; split; [exact Hloc |]; lia).
  assert_PROP (field_compatible (tarray tuchar osz) [] ob) as Fc by entailer!.
  assert (E := rl_out_split o Ho Fc).
  cbn [o oa_sh oa_N oa_c oa_base oa_d oa_cap rl_mid] in E. rewrite E. clear E. Intros.
  sep_apply (rl_pws_fold W (rl_side o)).
  forward_call (W ++ rl_side o, rl_mid o, Znth 0 c, bv_rle v).
  { split; [apply rl_mid_ok; auto |]. intros H0. cbn [rl_mid oa_d oa_base].
    rewrite isptr_offset_val_zero by (destruct Fc as [Fp _]; destruct ob; try contradiction; exact I).
    apply rl_mid_wvp; auto. }
  Intros vret. destruct vret as [r ocm]; cbn [fst snd] in *.
  match goal with Hx: if _ >? _ then _ else _ |- _ => rename Hx into Hres end.
  sep_apply (rl_pws_unfold W (rl_side o)). Intros.
  forward. forward.
  change (Int.signed (Int.repr 0)) with 0.
  replace (Vlong (Int64.repr (bv_rle v))) with (fs_rleSize (bl_fs1 fs ob osz opos pcs (Zlength c)))
    by (rewrite bl_fs1_rle, Hrle; reflexivity).
  sep_apply (fcore3_join_rl p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr (Vlong (Int64.repr 0)) Hpr).
  rewrite <- Hs1.
  change (TABS gv p (bd_oxo od) ts) with (tabs_rep TABS gv p (TInit (bd_oxo od) ts)).
  assert (Hcold1: fs_ddictIsCold (bl_fs1 fs ob osz opos pcs (Zlength c)) = Vint (Int.repr 0) \/
                  fs_ddictIsCold (bl_fs1 fs ob osz opos pcs (Zlength c)) = Vint (Int.repr 1))
    by (rewrite bl_fs1_cold; exact Hcold).
  forward.
  unfold s34_mid.
  assert (Hcap: oa_cap (rl_mid o) = osz - opos) by reflexivity.
  rewrite Hcap in Hres. rewrite Z.gtb_ltb in Hres.
  destruct (osz - opos <? bv_rle v) eqn:Eg.
  - destruct Hres as [-> ->]. apply Z.ltb_lt in Eg.
    assert (J := rl_out_unsplit o Ho Fc). cbn [o rl_mid oa_sh oa_N oa_c oa_base oa_d oa_cap] in J |- *.
    sep_apply J.
    Exists (err_code ZSTD_error_dstSize_tooSmall) oc 0 (fs_ddictIsCold (bl_fs1 fs ob osz opos pcs (Zlength c)))
      (TInit (bd_oxo od) ts).
    unfold vlong. entailer!.
    apply (rle_mid_err (dmode_of pr) od ba fs ts v); auto; lia.
  - destruct Hres as [-> ->]. apply Z.ltb_ge in Eg.
    assert (J := rl_out_join o (Zrepeat (Znth 0 c) (bv_rle v)) Ho Fc
                   ltac:(rewrite Zlength_Zrepeat by lia; cbn; lia)).
    cbn [o rl_mid oa_sh oa_N oa_c oa_base oa_d oa_cap] in J |- *.
    sep_apply J.
    Exists (bv_rle v) (put_bytes oc opos (Zrepeat (Znth 0 c) (bv_rle v))) 0
      (fs_ddictIsCold (bl_fs1 fs ob osz opos pcs (Zlength c))) (TInit (bd_oxo od) ts).
    unfold vlong. entailer!.
    apply (rle_mid_succ (dmode_of pr) od ba fs ts v); auto; lia.
Qed.

End CM_Rle_1.
