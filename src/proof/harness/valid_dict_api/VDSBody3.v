(* the body of vd_stream (harness/valid_dict_api.c) against vd_stream_spec, in a small context VD_G0 (lifted to
   G0 in WSide_valid_dict_api.v); its loop is that of valid_stream's v2 main (WMain_valid_stream.v). *)
Require Import VST.floyd.proofauto.
Require Import Zstd.proof.harness.valid_dict_api.VDSHelp3.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_api.HOK_valid_dict_api.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Definition VD_G0 (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred) : funspecs :=
  [(_quickproof_malloc, @malloc_spec' HCS); (_quickproof_free, @free_spec' HCS);
   ZSTD_isError_spec; ZSTD_getErrorCode_spec; ZSTD_decompressStream_spec DC DD; gp_assert_spec;
   exact_copy_spec; within_stream_spec; stall_error_spec; vd_chunk_spec].

(* what the loop keeps of the context *)
Definition VD_inv (st st1: dctx_st) : Prop :=
  dc_dict st1 = dc_dict st /\ dc_set st1 = dc_set st /\ dc_par st1 = dc_par st /\ dc_stable st1 = false /\
  dc_bl st1 = None.

Lemma VD_sel_eq st st1 : dc_dict st1 = dc_dict st -> dc_set st1 = dc_set st -> dc_par st1 = dc_par st ->
  st_sel st1 = st_sel st.
Proof. intros A B C. unfold st_sel. rewrite A, B, C. reflexivity. Qed.

Ltac VD_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Lemma VD_body DC DD : semax_body Vprog (VD_G0 DC DD) f_vd_stream (vd_stream_spec DC DD).
Proof.
start_function.
rename H into Hsf, H0 into Hwf, H2 into Hsdo, H3 into Hss, H4 into Hstab, H5 into Hdesc.
pose proof Hsf as (Hbok & Hcok & Hn & Hcn & Hnf & _).
assert (Hbl: dc_bl st = None) by (destruct Hsdo as (_ & _ & X); exact X).
destruct Hdesc as [Hwl HD].
forward. forward. forward.
forward_loop
  (EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st1: dctx_st,
   PROP (0 <= calls <= 4096; 0 <= ipos <= Zlength (ws_bytes ws); 0 <= got <= Zlength (ws_content ws);
         0 <= stalled <= calls; VD_inv st st1; ss_err (dc_ss st1) = false;
         VD_in_ok (dc_ss st1) ipos (ws_bytes ws); ss_out (dc_ss st1) = sublist 0 got (ws_content ws);
         0 <= ss_stall (dc_ss st1) <= stalled)
   LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
          temp _got (Vlong (Int64.repr got)); temp _stalled (Vlong (Int64.repr stalled));
          lvar _out tout v_out; lvar _in tin v_in; gvars gv; temp _ds d; temp _src src)
   SEP (data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st1;
        dict_res DD gv Ews (dc_dict st1); set_res DD gv Ews (dc_set st1) (dc_dict st1);
        data_at sh t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
        data_at shs (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src))
continue:
  (EX calls: Z, EX ipos: Z, EX got: Z, EX stalled: Z, EX st1: dctx_st,
   PROP (0 <= calls < 4096; 0 <= ipos <= Zlength (ws_bytes ws); 0 <= got <= Zlength (ws_content ws);
         0 <= stalled <= calls + 1; VD_inv st st1; ss_err (dc_ss st1) = false;
         VD_in_ok (dc_ss st1) ipos (ws_bytes ws); ss_out (dc_ss st1) = sublist 0 got (ws_content ws);
         0 <= ss_stall (dc_ss st1) <= stalled)
   LOCAL (temp _calls (Vlong (Int64.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
          temp _got (Vlong (Int64.repr got)); temp _stalled (Vlong (Int64.repr stalled));
          lvar _out tout v_out; lvar _in tin v_in; gvars gv; temp _ds d; temp _src src)
   SEP (data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st1;
        dict_res DD gv Ews (dc_dict st1); set_res DD gv Ews (dc_set st1) (dc_dict st1);
        data_at sh t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
        data_at shs (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src))
break:
  (EX st1: dctx_st,
   PROP (VD_inv st st1)
   LOCAL (lvar _out tout v_out; lvar _in tin v_in; gvars gv)
   SEP (data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; pws_pred W; mem_mgr gv; zstd_globals gv; DC gv d st1;
        dict_res DD gv Ews (dc_dict st1); set_res DD gv Ews (dc_set st1) (dc_dict st1);
        data_at sh t_wseries (wseries_val ws) (gv _x_valid_dict_api__sr);
        data_at shs (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) src)).
{ forward. Exists 0 0 0 0 st. entailer!. unfold VD_inv, VD_in_ok; rewrite Hss; simpl.
  repeat split; auto; try lia. pose proof (Zlength_nonneg (ws_bytes ws)); lia. }
2: { Intros calls ipos got stalled st1. forward. Exists (calls + 1) ipos got stalled st1. entailer!. }
2: { Intros st1. destruct H as (Hd1 & Hs1 & Hp1 & Hst1 & Hb1).
     unfold POSTCONDITION, abbreviate. simpl_ret_assert. Exists st1. rewrite Hd1, Hs1. entailer!. }
Intros calls ipos got stalled st1.
match goal with H: VD_inv st st1 |- _ => destruct H as (Hd1 & Hs1 & Hp1 & Hst1 & Hb1) end.
match goal with H: VD_in_ok _ _ _ |- _ => rename H into Hino end.
match goal with H: ss_out (dc_ss st1) = _ |- _ => rename H into Hout1 end.
match goal with H: ss_err (dc_ss st1) = false |- _ => rename H into Herr1 end.
forward_if.
2: { forward. Exists st1. entailer!. unfold VD_inv; auto. }
sep_apply (VD_sr_unfold sh ws (gv _x_valid_dict_api__sr)). Intros.
unfold VD_Rn. forward. fold (VD_Rn sh (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_api__sr)).
forward_call (Zlength (ws_bytes ws) - ipos).
Intros ilen. forward.
forward_call (2 ^ 18).
Intros olen0. forward.
sep_apply (VD_src_borrow shs (ws_bytes ws) src ipos ilen); [lia..|].
forward_call (gv, shs, offset_val ipos src, sublist ipos (ipos + ilen) (ws_bytes ws)).
{ entailer!. simpl. rewrite Zlength_sublist by lia. do 4 f_equal; lia. }
{ rewrite Zlength_sublist by lia. replace (ipos + ilen - ipos) with ilen by lia. cancel. }
{ rewrite Zlength_sublist by lia. split; [rep_lia|].
  unfold bytes_ok in *. apply Forall_sublist. auto. }
Intros ib.
rewrite Zlength_sublist by lia. replace (ipos + ilen - ipos) with ilen by lia.
sep_apply (wand_frame_elim (@data_at HCS shs (tarray tuchar ilen)
   (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) (offset_val ipos src))).
change (Int.signed (Int.repr 1)) with 1. rewrite add64_repr.
forward_call (tarray tuchar (1 + olen0), gv).
{ simpl. rewrite Z.max_r by lia. rep_lia. }
Intros ob.
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'5 (Vint (Int.repr
      (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
end.
{ VD_tc_null_test ib. }
{ forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
{ forward.
  { entailer!; VD_tc_null_test ob. }
  destruct (eq_dec ib nullval); [contradiction|].
  destruct (eq_dec ob nullval); entailer!;
    try reflexivity; destruct ob; try contradiction; reflexivity. }
forward_if.
{ sep_apply (VD_free_prep Ews (tarray tuchar (Z.max 1 ilen))
    (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws)) ++ Zrepeat Vundef (Z.max 1 ilen - ilen)) ib).
  forward_call (tarray tuchar (Z.max 1 ilen), ib, gv).
  forward_call (tarray tuchar (1 + olen0), ob, gv).
  forward. sep_apply (VD_sr_fold sh ws (gv _x_valid_dict_api__sr)). Exists st1. entailer!. unfold VD_inv; auto. }
match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht5 end.
change (EqDec_val ib nullval) with (eq_dec ib nullval) in Ht5.
change (EqDec_val ob nullval) with (eq_dec ob nullval) in Ht5.
destruct (eq_dec ib nullval) as [|Hib]; [now apply VD_repr1_neq0 in Ht5|].
destruct (eq_dec ob nullval) as [|Hob]; [now apply VD_repr1_neq0 in Ht5|].
clear Ht5. Intros.
assert (Hm: (0 < ilen /\ Z.max 1 ilen = ilen) \/ (ilen = 0 /\ Z.max 1 ilen = 1)) by lia.
set (m := Z.max 1 ilen) in *. clearbody m.
forward. forward. forward. forward. forward. forward.
change (Int.signed (Int.repr 0)) with 0.
assert (HA: Zlength (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) = ilen)
  by (rewrite Zlength_map, Zlength_sublist by lia; lia).
rewrite <- (VD_arr Ews m _ ib).
sep_apply (VD_ib_split ib ilen m _ HA Hm). Intros.
match goal with H: buf_ok (VD_W ilen ib) _ _ _ |- _ => rename H into Hbib end.
sep_apply (VD_pws_join W (VD_W ilen ib)).
rewrite <- (VD_arr_ Ews (1 + olen0) ob), <- VD_out, <- VD_in.
rewrite (@data_at__eq ZCS).
assert (Hbytes: bytes_ok (sublist ipos (ipos + ilen) (ws_bytes ws))).
{ unfold bytes_ok in *. apply Forall_sublist. auto. }
assert (Hsdo1: stream_dict_ok (W ++ VD_W ilen ib) st1).
{ apply VD_sdo_app. apply (VD_sdo_eq W st st1); auto; congruence. }
forward_call (W ++ VD_W ilen ib, gv, d, st1, v_out, v_in, Tsh, Tsh, Ews, ob, 1 + olen0, 0,
              @default_val ZCS (tarray tuchar (1 + olen0)), Ews, ib, ilen, 0, sublist ipos (ipos + ilen) (ws_bytes ws)).
{ unfold mbuf; rewrite ?if_false by auto. cancel. }
{ split; [apply VD_buf_ok_pos; lia|]. split; [apply VD_buf_ok_app; exact Hbib|].
  split; [apply Zlength_default_val_Tarray_tuchar; lia|].
  rewrite Zlength_sublist by lia. lia. }
Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
unfold mbuf; rewrite ?if_false by auto.
sep_apply (andp_left1 (DC gv d st') (valid_pointer d) (DC gv d st') (derives_refl _)).
match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct (VD_post _ _ _ _ _ _ _ _ _ _ _ _ _ Hst1 H) as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdlen0 & Hcells &
    Ha' & Hia & Hia2 & Hr0a & Hst' & Hs1' & Hs2' & Hstall & Hcl); clear H end.
sep_apply (VD_pws_split W (VD_W ilen ib)).
sep_apply (VD_ib_join ib ilen m (zbytes (sublist ipos (ipos + ilen) (ws_bytes ws))) Hm).
rewrite VD_out, VD_in, (VD_arr_ Ews m ib), (VD_arr Ews (1 + olen0) oc' ob).
pose proof Hino as (Ha0 & Ha1 & Ha2).
destruct (VSF_read (ws_bytes ws) ipos ilen (ss_ahead (dc_ss st1)) ipos' a') as [Hsin Hlen']; try lia.
rewrite Ha2, Hsin in Hst', Hcl, Hcells. rewrite Hout1 in Hcl.
rewrite VD_sin0 in Hcl by lia.
rewrite (VD_sel_eq st st1 Hd1 Hs1 Hp1), Hp1 in Hcl, Hcells. rewrite Hwl in Hcl.
assert (Hsall: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws) ++
                 sublist (ipos' + a') ilen (sublist ipos (ipos + ilen) (ws_bytes ws))) (ws_bytes ws))
  by (apply VSF_sall; lia).
assert (Hpin: is_prefix (sublist 0 (ipos + ipos' + a') (ws_bytes ws)) (ws_bytes ws))
  by (apply VSF_is_prefix_sublist; lia).
destruct (Hcells (VDP_alive _ _ _ dm ws HD Hsf _ Hpin)) as [Hdl Hbo]. clear Hcells.
assert (Hdlen: Zlength dl = opos') by lia.
subst opos'.
pose proof (VDP_content _ _ _ dm ws HD Hsf _ _ _ _ _ _ _ _ _ Hpin Hcl) as Hpre'.
apply VSF_prefix_app in Hpre'; [|lia]. destruct Hpre' as [Hgot' Hdl'].
forward. forward.
forward_call Int.one.
{ entailer!. rewrite VD_ltu64_false by rep_lia. reflexivity. }
forward. forward.
forward_call Int.one.
{ entailer!. rewrite VD_ltu64_false by rep_lia. reflexivity. }
unfold VD_Rcn.
forward.
match goal with |- semax _ (PROPx ?P (LOCALx (_ :: ?L) (SEPx ?R))) _ _ =>
  forward_loop (EX j: Z, PROPx ((0 <= j <= Zlength dl) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
    continue: (EX j: Z, PROPx ((0 <= j < Zlength dl) :: P) (LOCALx (temp _j (Vlong (Int64.repr j)) :: L) (SEPx R)))
    break: (PROPx P (LOCALx L (SEPx R)))
end.
{ Exists 0. entailer!. }
{ Intros j. forward. forward_if.
  2: { forward. entailer!. }
  try match goal with H: Int64.ltu _ _ = true |- _ => rewrite VD_ltu_Z in H by rep_lia; apply Z.ltb_lt in H end.
  forward.
  forward_call Int.one.
  { entailer!. try rewrite add64_repr; rewrite VD_ltu_Z by rep_lia.
    destruct (got + j <? Zlength (ws_content ws)) eqn:E; [reflexivity|]. apply Z.ltb_ge in E. lia. }
  assert (Ej: Znth j oc' = Vint (Int.repr (Znth j dl))) by (apply VSF_oc with (Zlength dl); auto; lia).
  assert (Ec: Znth (got + j) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws)))
              = Vint (Int.repr (Znth j dl))).
  { rewrite VSF_zb by lia. rewrite (VSF_dl (ws_content ws) dl got j) by (first [exact Hdl' | lia]). reflexivity. }
  assert (Hbj: 0 <= Znth j dl <= 255).
  { unfold bytes_ok in Hbo. pose proof (proj1 (Forall_Znth _ _) Hbo j ltac:(lia)) as Hb. cbv beta in Hb.
    unfold is_byte in Hb. lia. }
  forward.
  { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity). simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
  remember (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) as CV eqn:ECV.
  assert (HCV: Zlength CV = 2 ^ 18) by (subst CV; rewrite Zlength_app, Zlength_map, Zlength_Zrepeat by lia; lia).
  unfold VD_cv. rewrite <- ECV.
  sep_apply (VD_content_borrow sh CV (gv _x_valid_dict_api__sr) (got + j) ltac:(lia) HCV).
  replace (Znth (got + j) CV) with (Vint (Int.repr (Znth j dl))) by (clear - Ec ECV; subst CV; symmetry; exact Ec).
  Intros.
  assert_PROP (force_val (sem_add_ptr_long tuchar (offset_val 524296 (gv _x_valid_dict_api__sr))
                 (Vlong (Int64.add (Int64.repr got) (Int64.repr j)))) =
               field_address tuchar [] (offset_val (524296 + (got + j)) (gv _x_valid_dict_api__sr))).
  { entailer!. rewrite field_address_offset by auto. simpl. normalize. }
  forward.
  { entailer!. rep_lia. }
  forward_call Int.one.
  { entailer!. replace (Znth j oc') with (Vint (Int.repr (Znth j dl))) by (rewrite <- Ej; reflexivity).
    simpl. rewrite Int.eq_true. reflexivity. }
  sep_apply (wand_frame_elim (data_at sh tuchar (Vint (Int.repr (Znth j dl)))
                                (offset_val (524296 + (got + j)) (gv _x_valid_dict_api__sr)))).
  Exists j. clear Ec HCV. entailer!. }
{ Intros j. forward. Exists (j + 1). entailer!. }
fold (VD_Rcn sh (vl (Zlength (ws_content ws))) (gv _x_valid_dict_api__sr)).
forward. forward. forward. forward.
forward_call (tarray tuchar m, ib, gv).
{ rewrite if_false by auto. cancel. }
forward_call (tarray tuchar (1 + olen0), ob, gv).
{ rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (1 + olen0)) oc' ob). cancel. }
assert (Hdd2: dc_dict st' = dc_dict st1) by (subst st'; reflexivity).
assert (Hds2: dc_set st' = dc_set st1) by (subst st'; reflexivity).
assert (Hinv2: VD_inv st st') by (subst st'; unfold VD_inv; simpl; auto).
forward_call r.
forward_if.
{ match goal with H: Int.repr (if is_error_code r then 1 else 0) <> Int.zero |- _ => rename H into Herr end.
  destruct (is_error_code r) eqn:Er; [|contradiction Herr; reflexivity]. clear Herr.
  sep_apply (VD_sr_fold sh ws (gv _x_valid_dict_api__sr)).
  forward_call (sh, gv _x_valid_dict_api__sr, ws).
  assert (He: r = 2 ^ 64 - error_of r) by (unfold error_of; rewrite Er; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX v8: int, PROPx ((v8 = Int.zero -> within_stream_b (ws_frames ws) = true /\ error_of r <> 64) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'8 (Vint v8) :: L) (SEPx R)))
  end.
  { forward. Exists Int.one. entailer!. exfalso; apply Int.one_not_zero; assumption. }
  { forward_call r. forward.
    Exists (if Int.eq (Int.repr (error_of r)) (Int.repr 64) then Int.one else Int.zero). entailer!.
    split.
    { intro X. destruct (within_stream_b (ws_frames ws)); [|match goal with H: _ |- _ => contradiction H; reflexivity end].
      split; auto. intro E. rewrite E, Int.eq_true in X. exfalso; apply Int.one_not_zero; exact X. }
    destruct (Int.eq _ _); reflexivity. }
  Intros v8.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
    forward_if (EX v10: int, PROPx ((v10 <> Int.zero) :: P)
                 (LOCALx (temp _x_valid_dict_api__t'10 (Vint v10) :: L) (SEPx R)))
  end.
  { forward. Exists Int.one. entailer!. }
  { match goal with H: v8 = Int.zero -> _ |- _ => rename H into Hv8 end.
    destruct (Hv8 ltac:(assumption)) as [Hws He64].
    assert (Hst: stall_error_b (error_of r) stalled ipos' ilen (Zlength dl) (1 + olen0) 0 = true).
    { apply (VSF_stall r (error_of r) (ss_stall (dc_ss st1))); auto; try lia.
      destruct (VDP_err _ _ _ dm ws HD Hsf _ _ _ _ _ _ r Hws Hpin Hsall Hcl Er (error_of r) He) as [X | X];
        [contradiction | exact X]. }
    forward_call r.
    forward_call (error_of r, stalled, Tsh, v_in, ib, ilen, ipos', Tsh, v_out, ob, 1 + olen0, Zlength dl, 0).
    { unfold error_of; rewrite Er. unfold is_error_code in Er. apply Z.ltb_lt in Er. rep_lia. }
    forward. Exists Int.one. rewrite Hst. entailer!. }
  Intros v10. forward_call v10. forward.
  Exists st'. rewrite Hdd2, Hds2. entailer!. }
match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ => rename H into Herr end.
destruct (is_error_code r) eqn:Er; [exfalso; apply VD_repr1_neq0; exact Herr|]. clear Herr.
rewrite !add64_repr.
forward.
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'14
    (Vint (if andb (ipos' =? 0) (Zlength dl =? 0) then Int.one else Int.zero)) :: L) (SEPx R)))
end.
{ forward. forward. entailer!.
  match goal with H: Int64.repr ipos' = Int64.zero |- _ =>
    apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
    change (Int64.unsigned Int64.zero) with 0 in H; subst ipos' end.
  unfold Int64.cmpu. destruct (Z.eqb_spec (Zlength dl) 0) as [E|E]; [rewrite E; reflexivity|].
  rewrite Int64.eq_false; [reflexivity|]. intro X. apply (f_equal Int64.unsigned) in X.
  rewrite !Int64.unsigned_repr in X by rep_lia. lia. }
{ forward. entailer!.
  destruct (Z.eqb_spec ipos' 0); [subst; contradiction|]. reflexivity. }
set (b0 := andb (ipos' =? 0) (Zlength dl =? 0)).
assert (Hst2: 0 <= stall' <= (if b0 then stalled + 1 else 0)).
{ subst b0. destruct (Z.eqb_spec ipos' 0), (Z.eqb_spec (Zlength dl) 0); simpl.
  - specialize (Hs2' eq_refl ltac:(assumption) ltac:(assumption)). lia.
  - rewrite (Hs1' eq_refl ltac:(right; assumption)). lia.
  - rewrite (Hs1' eq_refl ltac:(left; assumption)). lia.
  - rewrite (Hs1' eq_refl ltac:(left; assumption)). lia. }
match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'15
    (Vlong (Int64.repr (if b0 then stalled + 1 else 0))) :: L) (SEPx R)))
end.
{ forward. entailer!. destruct b0; [|contradiction]. try rewrite add64_repr. reflexivity. }
{ forward. entailer!. destruct b0; [discriminate|]. reflexivity. }
forward.
assert (Hcalls: calls < 4096) by (rewrite !Int64.unsigned_repr in H4 by rep_lia; lia).
assert (Hin2: VD_in_ok (dc_ss st') (ipos + ipos') (ws_bytes ws))
  by (subst st'; unfold VD_in_ok; simpl; split; [lia | split; [lia | reflexivity]]).
assert (Hout2: ss_out (dc_ss st') = sublist 0 (got + Zlength dl) (ws_content ws))
  by (subst st'; simpl; rewrite Hout1; apply VSF_out_app; auto; lia).
assert (Hd2: ss_err (dc_ss st') = false /\ 0 <= ss_stall (dc_ss st') <= (if b0 then stalled + 1 else 0))
  by (subst st'; simpl; auto).
assert (Hsl: 0 <= (if b0 then stalled + 1 else 0) <= calls + 1) by (destruct b0; lia).
assert (Hlin: Zlength (sublist 0 (ipos + ipos' + a') (ws_bytes ws)) = ipos + ipos' + a')
  by (rewrite Zlength_sublist by lia; lia).
assert (Hlout: Zlength (sublist 0 got (ws_content ws) ++ dl) = got + Zlength dl)
  by (rewrite Zlength_app, Zlength_sublist by lia; lia).
clear Hst'.
forward_if.
{ match goal with H: Int64.repr r = Int64.zero |- _ =>
    apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia;
    change (Int64.unsigned Int64.zero) with 0 in H; subst r end.
  pose proof (VDP_zero _ _ _ dm ws HD Hsf _ _ _ _ _ _ _ _ 0 Hpin Hcl eq_refl) as Hz. rewrite Hlin, Hlout in Hz.
  rewrite (Hr0a eq_refl), Z.add_0_r in Hz.
  assert (Hnf': 1 <= Zlength (ws_frames ws) <= 4) by (rewrite Zlength_correct; lia).
  assert (EQ64: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned ->
                  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b)).
  { intros a b Ha Hb. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
    destruct (zeq a b); symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; auto. }
  unfold VD_Rf, VD_Rnf, VD_fv.
  forward. forward.
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: ?L) (SEPx ?R))) _ _ =>
    forward_loop (EX k: Z, PROPx ((0 <= k <= Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
         temp _at_end (Vint (Int.repr (if VSF_at (ws_frames ws) (ipos + ipos') (got + Zlength dl) k then 1 else 0))) :: L) (SEPx R)))
     continue: (EX k: Z, PROPx ((0 <= k < Zlength (ws_frames ws)) :: P) (LOCALx (temp _k (Vint (Int.repr k)) ::
         temp _at_end (Vint (Int.repr (if VSF_at (ws_frames ws) (ipos + ipos') (got + Zlength dl) (k + 1) then 1 else 0))) :: L) (SEPx R)))
     break: (PROPx P (LOCALx (temp _at_end (Vint (Int.repr 1)) :: L) (SEPx R)))
  end.
  { Exists 0. entailer!. }
  { Intros k. forward. forward_if.
    2: { forward. entailer!.
         try match goal with H: Int.unsigned (Int.repr k) >= _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
         replace k with (Zlength (ws_frames ws)) by lia. rewrite VSF_at_all, Hz. reflexivity. }
    try match goal with H: Int.unsigned (Int.repr k) < _ |- _ => rewrite !Int.unsigned_repr in H by rep_lia end.
    assert (Fk: forall d, @Znth (reptype t_winfo) d k (map winfo_val (ws_frames ws) ++
              Zrepeat (winfo_val winfo0) (4 - Zlength (ws_frames ws))) = winfo_val (Znth k (ws_frames ws))).
    { intros. rewrite Znth_app1 by (rewrite Zlength_map; lia). rewrite Znth_map by lia. reflexivity. }
    pose proof (proj1 (Forall_Znth _ _) (VSP_frames_bounds _ _ Hsf) k ltac:(lia)) as Bf. cbv beta in Bf.
    forward.
    { entailer!. rewrite Fk. exact I. }
    forward.
    { entailer!. rewrite Fk. exact I. }
    rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
    set (f := Znth k (ws_frames ws)) in *.
    unfold wi_end in Bf |- *.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _x_valid_dict_api__t'16 (Vint (if andb (wi_start f + wi_size f =? ipos + ipos')
        (got + Zlength dl =? wi_cstart f + wi_csize f) then Int.one else Int.zero)) :: L) (SEPx R)))
    end.
    { match goal with H: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H; rewrite add64_repr in H;
        apply (f_equal Int64.unsigned) in H; rewrite !Int64.unsigned_repr in H by rep_lia; rename H into Hend end.
      forward.
      { entailer!. rewrite Fk. exact I. }
      forward.
      { entailer!. rewrite Fk. exact I. }
      rewrite !Fk. unfold winfo_val at 1 2. cbv beta iota zeta.
      forward. entailer!.
      rewrite (proj2 (Z.eqb_eq _ _) Hend). simpl andb.
      unfold Int64.cmpu. rewrite EQ64 by rep_lia. unfold bool2val.
      destruct (got + Zlength dl =? wi_cstart f + wi_csize f); reflexivity. }
    { forward. entailer!.
      try match goal with H: Int64.add _ _ <> _ |- _ => rewrite add64_repr in H end.
      destruct (Z.eqb_spec (wi_start f + wi_size f) (ipos + ipos')) as [E|E]; [rewrite E in *; contradiction|].
      reflexivity. }
    forward_if.
    { forward. Exists k. entailer!.
      rewrite VSF_at_step by lia. fold f.
      unfold wi_end.
      match goal with H: (if ?c then Int.one else _) <> Int.zero |- _ =>
        destruct c; [rewrite orb_true_r; reflexivity | exfalso; apply H; reflexivity] end. }
    { forward. Exists k. entailer!.
      rewrite VSF_at_step by lia. fold f.
      unfold wi_end.
      match goal with H: (if ?c then Int.one else _) = Int.zero |- _ =>
        destruct c; [exfalso; apply Int.one_not_zero; assumption | rewrite orb_false_r; reflexivity] end. } }
  { Intros k. forward. Exists (k + 1). entailer!. }
  forward_call Int.one. unfold VD_Rn. forward.
  fold (VD_Rn sh (vl (Zlength (ws_bytes ws))) (gv _x_valid_dict_api__sr)).
  fold (VD_Rnf sh (vu (Zlength (ws_frames ws))) (gv _x_valid_dict_api__sr)).
  fold (VD_fv ws). fold (VD_Rf sh (VD_fv ws) (gv _x_valid_dict_api__sr)).
  sep_apply (VD_sr_fold sh ws (gv _x_valid_dict_api__sr)).
  forward_if.
  { forward. Exists st'. rewrite Hdd2, Hds2. entailer!. }
  { forward. Exists calls (ipos + ipos') (got + Zlength dl) (if b0 then stalled + 1 else 0) st'.
    destruct Hd2 as (Hd2a & Hd2b). rewrite Hdd2, Hds2. entailer!. } }
forward.
sep_apply (VD_sr_fold sh ws (gv _x_valid_dict_api__sr)).
Exists calls (ipos + ipos') (got + Zlength dl) (if b0 then stalled + 1 else 0) st'.
destruct Hd2 as (Hd2a & Hd2b). rewrite Hdd2, Hds2. entailer!.
Qed.
