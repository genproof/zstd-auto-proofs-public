(* valid_params main, segment D2: the loop body up to D2_tail (the call bounds, the chunk and the
   output buffer, ZSTD_decompressStream, main's asserts on its results), then D2_tail_ok (VPD2B.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_params.VPD2Help.
Require Import Zstd.proof.harness.valid_params.VPD2B.
Require Import Zstd.proof.zstd.ApiBridge.

Local Notation HCS := Zstd.proof.harness.valid_params.HOK_valid_params.CompSpecs.
Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Section Seg.
Context {Espec: OracleKind}.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.
Variable WG : globals -> mpred.
Variable WDS : wdict -> reptype t_wstate -> Prop.
Local Notation Delta := (VP_Delta DC DD WG WDS).

Lemma D2_body_ok (gv: globals) (vz vi vo: val) (wsr ws': wseries) (p: dparams) (base wlim: Z) (src dctx: val)
    (calls ipos got stalled: Z) (st: dctx_st) (R0: ret_assert) :
  VP_dfacts wsr ws' p base wlim -> isptr src ->
  semax Delta
    (D2_A DC WG gv vz vi vo wsr ws' p base (D2_wb wsr wlim) src dctx (0 <= calls <= 4096 /\ 0 <= stalled <= calls)
       calls ipos got stalled st)
    D2_body
    (D2_RA DC WG gv vz vi vo wsr ws' p base (D2_wb wsr wlim) src dctx R0).
Proof.
intros Hd Psrc. destruct R0 as [Rn Rb Rc Rr].
unfold D2_A, D2_R, D2_L, D2_body, D2_RA, overridePost, loop1_ret_assert, VP_Delta. simplify_func_tycontext. abbreviate_semax.
Intros. match goal with H: _ /\ _ <= calls |- _ => destruct H as [Hcalls Hstalled] end.
match goal with H: D2_st_ok _ _ _ _ _ _ _ |- _ => rename H into Hst end.
pose proof Hd as (Hw & Hc & Hbs' & Hbase & HN0 & Hbok & Hcok & HN & HC & Hnf & Hwf & Hfb & Hwl & _).
assert (HNb: Zlength (ws_bytes ws') <= 2 ^ 19).
{ rewrite Hbs'. destruct (Z_le_gt_dec base (Zlength (ws_bytes wsr))).
  - rewrite Zlength_sublist by lia; lia.
  - rewrite sublist_nil_gen by lia. rewrite Zlength_nil; lia. }
assert (Hbok': bytes_ok (ws_bytes ws')) by (destruct Hw; assumption).
forward_if.
2: { forward. unfold D2_brk, VP_SD1. Exists st. entailer!. }
forward_call (Zlength (ws_bytes ws') - ipos).
Intros ilen.
forward_call (2 ^ 18).
Intros olen0. forward.
sep_apply (D2_src_borrow (ws_bytes ws') src ipos ilen); [lia..|].
forward_call (gv, Ews, offset_val ipos src, sublist ipos (ipos + ilen) (ws_bytes ws')).
{ entailer!. simpl. rewrite Zlength_sublist by lia. do 4 f_equal; lia. }
{ cancel. }
{ rewrite Zlength_sublist by lia. split; [rep_lia|].
  unfold bytes_ok in *. apply Forall_sublist. auto. }
Intros ib.
sep_apply (wand_frame_elim (@data_at HCS Ews (tarray tuchar (Zlength (sublist ipos (ipos + ilen) (ws_bytes ws'))))
   (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws'))) (offset_val ipos src))).
rewrite Zlength_sublist by lia. replace (ipos + ilen - ipos) with ilen by lia.
change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr.
forward_call (tarray tuchar (1 + olen0), gv).
{ simpl. rewrite Z.max_r by lia. rep_lia. }
Intros ob.
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_params__t'53 (Vint (Int.repr
      (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
end.
{ D2_tc_null_test ib. }
{ forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
{ forward.
  { entailer!; D2_tc_null_test ob. }
  destruct (eq_dec ib nullval); [contradiction|].
  destruct (eq_dec ob nullval); entailer!;
    try reflexivity; destruct ob; try contradiction; reflexivity. }
forward_if.
{ sep_apply (D2_free_prep Ews (tarray tuchar (Z.max 1 ilen))
    (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws')) ++ Zrepeat Vundef (Z.max 1 ilen - ilen)) ib).
  forward_call (tarray tuchar (Z.max 1 ilen), ib, gv).
  forward_call (tarray tuchar (1 + olen0), ob, gv).
  forward. unfold D2_brk, VP_SD1. Exists st. entailer!. }
match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht6 end.
change (EqDec_val ib nullval) with (eq_dec ib nullval) in Ht6.
change (EqDec_val ob nullval) with (eq_dec ob nullval) in Ht6.
destruct (eq_dec ib nullval) as [|Hib]; [now apply D2_repr1_neq0 in Ht6|].
destruct (eq_dec ob nullval) as [|Hob]; [now apply D2_repr1_neq0 in Ht6|].
clear Ht6. Intros.
assert (Hm: (0 < ilen /\ Z.max 1 ilen = ilen) \/ (ilen = 0 /\ Z.max 1 ilen = 1)) by lia.
set (m := Z.max 1 ilen) in *. clearbody m.
forward. forward. forward. forward. forward. forward.
change (Int.signed (Int.repr 0)) with 0.
assert (HA: Zlength (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws'))) = ilen)
  by (rewrite Zlength_map, Zlength_sublist by lia; lia).
rewrite <- (D2_arr Ews m _ ib).
sep_apply (D2_ib_split ib ilen m _ HA Hm). Intros.
rewrite <- (D2_arr_ Ews (1 + olen0) ob), <- D2_out, <- D2_in.
rewrite (@data_at__eq ZCS).
assert (Hbytes: bytes_ok (sublist ipos (ipos + ilen) (ws_bytes ws'))).
{ unfold bytes_ok in *. apply Forall_sublist. auto. }
pose proof Hst as (Hpar & Hdict & Hset & Hbl & Hstab & Herr & _).
forward_call (D2_W ilen ib, gv, dctx, st, vo, vi, Tsh, Tsh, Ews, ob, 1 + olen0, 0,
              @default_val ZCS (tarray tuchar (1 + olen0)), Ews, ib, ilen, 0, sublist ipos (ipos + ilen) (ws_bytes ws')).
{ rewrite Hdict, Hset. unfold dict_res, set_res, mbuf. rewrite !if_false by auto. simpl. cancel. }
{ split; [apply D2_buf_ok_pos; lia|]. split.
  { unfold stream_dict_ok. rewrite Hdict, Hset, Hbl. split; [exact I | split; [constructor | reflexivity]]. }
  split; [apply Zlength_default_val_Tarray_tuchar; lia|].
  rewrite Zlength_sublist by lia. lia. }
Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
unfold mbuf; rewrite !if_false by auto.
rewrite Hdict, Hset. change (dict_res DD gv Ews None) with emp. rewrite set_res_nil.
sep_apply (andp_left1 (DC gv dctx st') (valid_pointer dctx) (DC gv dctx st') (derives_refl _)).
match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hpost end.
match goal with H: 0 <= r <= Int64.max_unsigned |- _ => rename H into Hr end.
destruct (D2_post_M2 wsr ws' p base wlim st st' r ob (1 + olen0) opos' _ oc' calls ipos ilen ipos' got stalled
            Hd Hst ltac:(rewrite !Int64.unsigned_repr in H0 by rep_lia; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
            ltac:(lia) ltac:(lia) Hr Hpost)
  as (dl & (Hip' & Hdlen & Hdl1 & Hoc) & (Hdl & Hbo) & (Hgot' & Hdl') & Hip2 & HM2).
clear Hpost. subst opos'.
sep_apply (D2_ib_join ib ilen m (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws'))) Hm).
rewrite D2_out, D2_in, (D2_arr_ Ews m ib), (D2_arr Ews (1 + olen0) oc' ob).
forward. forward.
forward_call Int.one.
{ entailer!. rewrite D2_ltu64_false by rep_lia. reflexivity. }
forward. forward.
forward_call Int.one.
{ entailer!. rewrite D2_ltu64_false by rep_lia. reflexivity. }
sep_apply (VP_sr_unfold7w wsr (gv _x_valid_params__sr)). Intros.
unfold VP_Rcn.
forward.
match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?R))) _ _ =>
  forward_loop (EX j: Z, PROPx ((0 <= j <= Zlength dl) :: P) (LOCALx (temp _j (Vint (Int.repr j)) :: L) (SEPx R)))
    continue: (EX j: Z, PROPx ((0 <= j < Zlength dl) :: P) (LOCALx (temp _j (Vint (Int.repr j)) :: L) (SEPx R)))
    break: (PROPx P (LOCALx L (SEPx R)))
end.
{ Exists 0. entailer!. }
{ Intros j. forward. forward_if.
  2: { forward. entailer!. }
  match goal with H: Int.unsigned (Int.repr j) < _ |- _ => rewrite Int.unsigned_repr in H by rep_lia end.
  forward. forward_call Int.one.
  { entailer!. rewrite D2_ltu_Z by rep_lia.
    replace (got + j <? Zlength (ws_content wsr)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (Ej: Znth j oc' = Vint (Int.repr (Znth j dl))) by (apply VSF_oc with (Zlength dl); auto; lia).
  assert (Ec: Znth (got + j) (zbytes (ws_content wsr) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content wsr)))
              = Vint (Int.repr (Znth j dl))).
  { rewrite VSF_zb by lia. rewrite (VSF_dl (ws_content wsr) dl got j) by (first [exact Hdl' | lia]). reflexivity. }
  assert (Hbj: 0 <= Znth j dl <= 255).
  { unfold bytes_ok in Hbo. pose proof (proj1 (Forall_Znth _ _) Hbo j ltac:(lia)) as Hb. cbv beta in Hb.
    unfold is_byte in Hb. lia. }
  forward.
  { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity).
    simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  remember (zbytes (ws_content wsr) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content wsr))) as CV eqn:ECV.
  assert (HCV: Zlength CV = 2 ^ 18) by (subst CV; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
  sep_apply (D2_content_borrow_w CV (gv _x_valid_params__sr) (got + j) ltac:(lia) HCV).
  replace (Znth (got + j) CV) with (Vint (Int.repr (Znth j dl))) by (clear - Ec ECV; subst CV; symmetry; exact Ec).
  Intros.
  assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_params__sr))
                 (Vlong (Int64.add (Int64.repr got) (Int64.repr (Int.unsigned (Int.repr j)))))) =
               field_address tuchar [] (offset_val (524296 + (got + j)) (gv _x_valid_params__sr))).
  { entailer!. rewrite field_address_offset by auto. simpl. try rewrite Int.unsigned_repr by rep_lia. normalize. }
  forward.
  { entailer!. rep_lia. }
  forward_call Int.one.
  { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity).
    simpl. rewrite Int.eq_true. reflexivity. }
  sep_apply (wand_frame_elim (data_at Ews tuchar (Vint (Int.repr (Znth j dl)))
                                (offset_val (524296 + (got + j)) (gv _x_valid_params__sr)))).
  Exists j. clear Ec HCV. entailer!. }
{ Intros j. forward. Exists (j + 1). entailer!. }
fold (VP_Rcn (vl (Zlength (ws_content wsr))) (gv _x_valid_params__sr)).
forward. forward. forward. forward.
forward_call (tarray tuchar m, ib, gv).
{ rewrite if_false by auto. cancel. }
forward_call (tarray tuchar (1 + olen0), ob, gv).
{ rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (1 + olen0)) oc' ob). cancel. }
sep_apply (VP_sr_fold7w wsr (gv _x_valid_params__sr)).
rewrite !add64_repr.
eapply semax_pre; [|apply (D2_tail_ok DC DD WG WDS gv vz vi vo wsr ws' p base wlim src dctx calls (ipos + ipos')
  (got + Zlength dl) stalled ib ilen ipos' ob (1 + olen0) (Zlength dl) r st' {| RA_normal := Rn; RA_break := Rb;
  RA_continue := Rc; RA_return := Rr |} HM2)].
unfold D2_M2, D2_L. entailer!.
Qed.

End Seg.
