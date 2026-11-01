(* FS3-bl BODY, stages 3/4, the tail (split for the check time): t34_xx (VST): the checksum update
   `if (validateChecksum) XXH64_update(&xxhState, dst, rSize)`. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TUpdSep.
Local Open Scope logic.

Section CM_TUpdX_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma t34_upd_xx_ok : forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs: Z) (r: Z) (oc': list val) (e': Z) (cold: val) (t': tabs3) (ds: Z) (cnt: list Z) (ts': tstate) (Q: environ -> mpred) (K: statement),
  t34_H W pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v pcs ->
  s34_mid_ok od ba v osz opos oc c r oc' e' cold t' ->
  is_error_code r = false -> r <= fh_blockSizeMax (bv_h v) -> t34_cnt od ba c opos oc' r t' cnt ts' ->
  fs_decodedSize fs = vlong ds -> 0 <= ds <= Int64.max_unsigned ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (t34_fs1 (t34_fsm fs ob osz opos pcs c e' cold) ds r (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt)) oc' t') K (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil) (t34_st DENT TABS W gv p pr od hb shk shd ob osz opos shs src c v_bp r (fsu_decodedSize (t34_fsm fs ob osz opos pcs c e' cold) (vlong (ds + r))) oc' t') (Ssequence t34_xx K) (t34_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c Q).
Proof.
  intros Espec DENT TABS SR BR' HD HT W gv p pr od osz0 ba fs ts hb shk shd ob osz opos oc shs src c v_bp v pcs
    r oc' e' cold t' ds cnt ts' Q K HH Hmid Herr Hrb Hcnt Hds Hdsr Hk.
  destruct HH as (Hpr & Hpre & Hci & _ & _ & _ & Hst & _ & _ & _ & _).
  destruct Hci as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcs & _).
  assert (Hhf: hdr_fields (md_ignore (dmode_of pr)) v fs).
  { cbv [bl_cstage] in Hcs. destruct Hst as [E | E]; rewrite E in Hcs; apply Hcs. }
  clear Hcs.
  destruct Hhf as (_ & _ & Hvc & Hxs).
  change (bl_val (md_ignore (dmode_of pr)) (bv_h v)) with (t34_vc pr v) in Hvc, Hxs.
  destruct Hcnt as (Hsub & Hbo & Hlc & _ & _). subst r.
  destruct Hpre as (_ & _ & _ & Hbuf & _ & _ & Hwsd & _ & _ & Hop & Hosz & _ & _).
  destruct (t34_fsm_fields fs ob osz opos pcs c e' cold) as (Fv & Fx & Fd & _).
  set (fsm := t34_fsm fs ob osz opos pcs c e' cold) in *.
  set (fsy := fsu_decodedSize fsm (vlong (ds + Zlength cnt))) in *.
  assert (Fv': fs_validateChecksum fsy = fs_validateChecksum fs) by exact Fv.
  assert (Fx': fs_xxh fsy = fs_xxh fs) by exact Fx.
  unfold t34_st in Hk |- *. unfold t34_R, bl_R. unfold t34_xx.
  assert_PROP (Zlength oc' = osz /\ field_compatible (tarray tuchar osz) [] ob) as Hoa by entailer!.
  destruct Hoa as (Hlo & Fob).
  assert (Hr: 0 <= Zlength cnt <= osz - opos).
  { pose proof (Zlength_sublist2 _ opos (opos + Zlength cnt) oc') as Z2. rewrite Hsub in Z2.
    rewrite Zlength_map in Z2. pose proof (Zlength_nonneg cnt). lia. }
  sep_apply (tu_split p fsy pr). Intros.
  simplify_func_tycontext.
  abbreviate_semax.
  rewrite Fv', Hvc. forward.
  rewrite Fx'.
  assert_PROP (field_compatible t_dctx (DOT _validateChecksum) p) as Fcv by entailer!.
  assert (Fcx: field_compatible t_dctx (DOT _xxhState) p).
  { apply field_compatible_cons in Fcv. apply field_compatible_cons. simpl in Fcv |- *.
    split; [| tauto]. unfold in_members. simpl. repeat (first [left; reflexivity | right]). }
  freeze [0; 3; 4; 5; 6; 8; 9; 10; 11; 12; 14] FR.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx (?F :: ?V :: _ :: ?R)))) _ _ =>
    forward_if (PROPx P (LOCALx L (SEPx (F :: V :: xxh_field p (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) :: R)))) end.
  - destruct (t34_vc pr v) eqn:Evc; [| exfalso; apply H'; reflexivity].
    destruct (Hxs eq_refl) as [l Hl]. rewrite Hl. unfold t34_xxh. cbn [option_map]. unfold xxh_field.
    destruct (zlt 0 (Zlength cnt)) as [Hr0 | Hr0].
    + rewrite (tu_arr_split shd osz oc' ob opos cnt) by (auto; lia). Intros.
      forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, l, shd, offset_val opos ob, cnt, @nil ptr_witness).
      { unfold pws_pred; simpl. cancel. }
      change (xxh_bytes cnt) with (zbytes cnt). change (pws_pred []) with (@emp mpred _ _).
      sep_apply (tu_arr_join shd osz oc' ob opos cnt); auto; try lia.
      entailer!. rewrite Hl. apply derives_refl.
    + assert (Hc0: cnt = []).
      { destruct cnt; [reflexivity | rewrite Zlength_cons in Hr0; pose proof (Zlength_nonneg cnt); lia]. }
      subst cnt.
      assert (Pob: isptr ob) by (destruct Fob; auto).
      assert (Ez0: data_at shd (tarray tuchar (Zlength (@nil Z))) (xxh_bytes []) (offset_val opos ob) = emp)
        by (apply data_at_zero_array_eq; auto; apply isptr_offset_val; auto).
      destruct (zlt 0 osz) as [HN0 | HN0].
      * forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, l, shd, offset_val opos ob, @nil Z,
                      [pw_bytes shd osz oc' ob]).
        { rewrite Ez0. unfold pws_pred; simpl. unfold pw_pred. cancel. }
        { try intros _. unfold pws_pred; simpl. unfold pw_pred. rewrite sepcon_emp.
          apply tu_arr_wvp; [apply readable_nonidentity, writable_readable; auto | lia | lia]. }
        rewrite Ez0. unfold pws_pred; cbn [map fold_right]. unfold pw_pred. rewrite sepcon_emp.
        rewrite app_nil_r. entailer!. rewrite Hl. unfold t34_xxh, xxh_field; cbn [option_map].
        rewrite app_nil_r. apply derives_refl.
      * assert (HN00: osz = 0) by lia. assert (Ho0: opos = 0) by lia. subst opos.
        forward_call (Ews, field_address t_dctx (DOT _xxhState) p, 0, l, shd, offset_val 0 ob, @nil Z, W).
        { rewrite Ez0. cancel. }
        { try intros _.
          eapply derives_trans; [| eapply derives_trans; [apply Hbuf | apply andp_left1, derives_refl]].
          rewrite HN00, data_at__eq, data_at_zero_array_eq by (auto; reflexivity). rewrite sepcon_emp.
          apply derives_refl. }
        rewrite Ez0. rewrite app_nil_r. entailer!. rewrite Hl. unfold t34_xxh, xxh_field; cbn [option_map].
        rewrite app_nil_r. apply derives_refl.
  - destruct (t34_vc pr v) eqn:Evc; [exfalso; exact (Int.one_not_zero H) |]. forward. entailer!.
  - thaw FR.
    sep_apply (tu_join_xx p fsy pr (Vint (Int.repr (if t34_vc pr v then 1 else 0)))
                 (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt) Hpr ltac:(rewrite Fv', Hvc; reflexivity)).
    change (fsu_xxh fsy (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt))
      with (t34_fs1 fsm ds (Zlength cnt) (t34_xxh (t34_vc pr v) (fs_xxh fs) cnt)).
    eapply semax_pre; [| exact Hk].
    entailer!.
Qed.

End CM_TUpdX_1.
