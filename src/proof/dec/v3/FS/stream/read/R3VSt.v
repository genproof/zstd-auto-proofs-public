(* FS3 streaming, case zdss_read: the branch decoding a unit directly from the caller's input,
   stable mode (v2 StreamSeg_read.v rd_direct_st), in the small context of its two callees. *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Stab Zstd.proof.dec.v3.FS.stream.read.R3Err Zstd.proof.dec.v3.FS.stream.read.R3Dsub Zstd.proof.dec.v3.FS.stream.read.R3Dm Zstd.proof.dec.v3.FS.stream.read.R3DmV.
Local Open Scope logic.

Section CM_R3VSt_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma dd_borrow3 : forall DENT gv p st k W dd,
  (forall x buf, dd = Some (x, buf) -> dd_src st k x buf) ->
  stream_dict_ok W st -> set_cur_ok st ->
  dgroup DENT gv p (c3_dict k) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
  set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) |--
    !! dd_facts W dd && (dd_lend DENT gv dd * (dd_lend DENT gv dd -* dd_all DENT gv p st (c3_dict k))).
Proof. intros. apply dd_borrow; auto. Qed.

(* stable mode: the exact claims (S3Main.ex_call, ex_err) assume the configuration of a new context, which is
   buffered, so they hold vacuously *)
Ltac stable_noex :=
  first [ (unfold ex_call; intros (_ & _ & _ & ?Hf & _); simpl in Hf; congruence)
        | (unfold ex_err; intros (_ & _ & _ & ?Hf & _); simpl in Hf; congruence) ].

Definition rd_Delta2 (DENT: dent_pred) (TABS: tabs_pred) : tycontext :=
  rd_Delta [ZSTD_decompressContinueStream_spec3 DENT TABS; ERR_isError_spec;
            ZSTD_nextSrcSizeToDecompressWithInputSize_spec].

(* an error returned as it is (positions unchanged), from the loop invariant's state plus the error value; the
   model fails on the call too, or the error is a memory allocation (ex_err) *)
Lemma ret_err_semax3 : forall (Espec: OracleKind) (Delta: tycontext) DENT TABS BR (a: dsa) (w: lw) (R: ret_assert)
    (r: Z) (id: ident),
  RET3x -> TABS_OK TABS -> dsa_ok a -> start_ok a -> base_call (a_st a) (w_k w) ->
  Zlength (w_oc w) = a_osz a -> sublist 0 (a_opos a) (w_oc w) = sublist 0 (a_opos a) (a_oc a) ->
  0 <= r <= Int64.max_unsigned -> err_why a r -> ex_err a r ->
  Maps.PTree.get id (temp_types Delta) = Some tulong -> ret_type Delta = tulong ->
  RA_return R = RA_return (ds_R_x DENT TABS BR a) ->
  semax Delta
    (PROPx [] (LOCALx (temp id (Vlong (Int64.repr r)) :: ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
    (Sreturn (Some (Etempvar id tulong))) R.
Proof.
intros Espec Delta DENT TABS BR a w R r id RT HT Ha Hs Hb Hl Hp Hr He Hx Hid Hrt HR.
eapply semax_pre; [| apply semax_return].
rewrite Hrt.
rewrite <- insert_local.
apply andp_right.
{ unfold tc_expropt. apply tc_ret_temp_ulong; auto. }
pose proof (ret3x_err_ok RT DENT TABS BR a w r HT Ha Hs Hb Hl Hp Hr He Hx) as RE.
rewrite HR. intro rho. unfold local, lift1. simpl. normalize.
destruct H0 as [H0 _]. assert (E: Vlong (Int64.repr r) = eval_id id rho) by exact H0. clear H0.
unfold eval_id in E. destruct (Map.get (te_of rho) id) eqn:E2; simpl in E; [|discriminate]. subst.
eapply derives_trans; [apply (RE rho)|]. unfold liftx; simpl. unfold lift, eval_id. simpl. rewrite E2. simpl.
apply derives_refl.
Qed.

(* the tables after a call of ZSTD_decompressContinue(Stream), as the context's tables: when the call leaves them
   uninitialised, the litExtra buffer they hold is named by the existential *)
Lemma tabs_match_rep : forall (TABS: tabs_pred) gv p dd tabs',
  (match tabs' with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end) =
  EX lxb: list Z, tabs_rep TABS gv p (tabs_of dd lxb tabs').
Proof.
intros. destruct tabs'; [|reflexivity].
apply pred_ext; [apply (exp_right nil); apply derives_refl | apply exp_left; intros; apply derives_refl].
Qed.

Lemma rd_direct_st3 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (R: ret_assert) (ns: Z),
  MF3 -> RET3x -> TABS_OK TABS -> dsa_ok a -> start_ok a ->
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> w_smw w = 1 ->
  sf_stage (c3_s (w_k w)) = zdss_read -> fp_complete (sv_fp (w_sv w)) = false ->
  unit_ok (sv_fp (w_sv w)) ns -> 0 < ns -> w_ipc w + ns <= a_isz a ->
  dc_stable (a_st a) = true ->
  RA_break R = ds_inv_x DENT TABS a -> RA_return R = RA_return (ds_R_x DENT TABS BR a) ->
  semax (rd_Delta2 DENT TABS)
    (PROPx [] (LOCALx (temp _neededInSize (Vlong (Int64.repr ns)) :: ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
    rd_direct R.
Proof.
intros Espec DENT TABS BR a w R ns M RT HT Ha Hstart Hinv Hsmw Hstage Hnc Hunit Hns0 Hge0 Est HRn HRr.
destruct a as [W gv d st outp inp sho shi shob obf osz opos oc shb ibf isz ipos ibs vop].
destruct w as [smw k sv ipc opc oc1 dl]. simpl in *. subst smw.
pose proof Hinv as Hinv'.
destruct Hinv' as (Hip & Hop & Hloc & Hpre & Hdl & Hdlc & Hdlb & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 &
                   Hcore & Hddok & Hstout & Hahead & Hblk & Hmodel & Hlh & Hsin & Hexp0 & HT0).
simpl in *.
pose proof Hcore as Hcore'. unfold c_core in Hcore'. destruct Hcore' as (Hhost & Hcold & Hsz & Hcs).
rewrite Hstage in Hcs. simpl in Hcs.
destruct Hcs as (_ & Hcf & Hring & Hstfl & _ & Hnld & Hrd).
destruct Hnld as (Hinpos & Hraw & Hsk); [unfold zdss_read, zdss_load; lia|].
destruct Hrd as (Hpend & Hoso); [reflexivity|].
destruct R as [Rn Rb Rc Rr]. cbn [RA_break RA_return] in HRn, HRr.
pose proof Ha as Ha'.
destruct Ha' as (Hbufo & Hbufi & Hstbuf & Hwso & Hwsi & Hwsob & Hrsb & Hdict & Herr & Hopos & Hosz & Hloc0 &
                 Hipos & Hisz & Hlibs & Hbibs & Hstout0 & Hw0 & Hopst & _).
cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf
  a_isz a_ipos a_ibs a_vop] in *.
(* the bases the code computes with (the caller's pointers, or ZSTD_emptyBuffer for NULL) *)
set (ob := a_ob _) in *. set (ib := a_ib _) in *.
destruct (c_frame_tabs _ _ _ _ _ Hcf) as [ts Hts].
unfold rd_direct, ds_case_read. cbv beta iota.
unfold rd_Delta2, rd_Delta. abbreviate_semax.
unfold ds_LI_S, ds_LI_L, ctx_rep3, ctx_body3, fgroup3, cgroup3, tabs_rep.
cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_obf a_osz a_opos a_oc a_shb a_ibf
  a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl].
fold ob ib.
rewrite Hts. rewrite frame_fields_split.
Intros.
unfold sgroup. Intros.
assert_PROP (isptr ib) as Pib by entailer!.
assert (Hge: ns <= isz - ipc) by lia.
assert (Hns1: 0 < ns <= Int64.max_unsigned) by rep_lia.
destruct (c_ring_ostart _ _ _ _ _ _ _ Hring ltac:(lia)) as (ostart & oend & Hos & Hoe & Hoo & Hoeb & Host).
rewrite Est in Host. destruct (Host eq_refl) as [-> ->].
destruct Hbase as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6 & Hb7).
rewrite Hb1, Est, Hstage, Hos.
gather_SEP (field_at _ _ (DOT _stage) _ d) (field_at _ _ (DOT _bType) _ d)
           (field_at _ _ (DOT _expected) _ d) (frame_rest d _).
rewrite <- frame_fields_split.
rewrite (in_res_split (sv_fp sv) shb ib isz ibs ipc ns).
(* the frame's DDict lends its entropy and content *)
assert (Hddsrc: forall x buf, sv_dd sv = Some (x, buf) -> dd_src st k x buf).
{ intros x buf E. apply (Hddok ltac:(rewrite Hstage; lia) x buf E). }
gather_SEP (dgroup DENT gv d (c3_dict k)) (dict_res (DD3x DENT) gv Ews (dc_dict st))
           (set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)).
sep_apply (dd_all_bytes_keep DENT gv d st (c3_dict k) W Hb4 Hb5 Hdict).
Intros. match goal with H: dicts_bytes _ |- _ => rename H into Hdb end.
try gather_SEP (dgroup DENT gv d (c3_dict k)) (dict_res (DD3x DENT) gv Ews (dc_dict st))
           (set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)).
sep_apply (dd_borrow3 DENT gv d st k W (sv_dd sv) Hddsrc Hdict Hb5).
Intros. match goal with H: dd_facts _ _ |- _ => rename H into Hddf end.
assert (Hld: lay_dd (sv_lay sv) (sv_dd sv)).
{ destruct (sv_fp sv); unfold c_frame in Hcf; destruct Hcf as (_&_&_&_&Hld&_); exact Hld. }
rewrite (lend_lay DENT gv (sv_lay sv) (sv_dd sv) Hld).
pose proof (lay_wit_of W (sv_lay sv) (sv_dd sv) Hld Hddf) as Hlw.
pose proof (read_pre_stable3 _ _ _ _ _ _ _ Ha Hinv Hstage Est Hnc Hddf) as Hps.
cbv zeta in Hps. cbn [a_shob a_ob a_osz a_st a_W] in Hps. destruct Hps as [Hlay Hhist].
repeat flatten_sepcon_in_SEP.
set (o := oa_stable shob ob osz (sv_fp sv) oc1 opc) in *.
evar (Qf: Z -> list val -> fstate -> option tstate -> environ -> mpred).
apply semax_seq with (Q := exp (fun rr: Z => exp (fun oc': list val => exp (fun fs': fstate =>
                             exp (fun tabs': option tstate => Qf rr oc' fs' tabs'))))).
{ apply semax_dowhile0_gen.
  match goal with |- semax _ _ _ ?P =>
    let P' := eval cbv beta iota delta [overridePost loop1_ret_assert] in P in change P with P' end.
  abbreviate_semax.
  assert_PROP (Forall (value_fits tuchar) oc1) as Hfits
    by (entailer!; try (match goal with H: value_fits (tarray tuchar _) oc1 |- _ => destruct H as [_ H]; exact H end)).
  pose proof (read_cont_hist_stable3 _ _ _ _ _ _ _ Ha Hinv Hstage Est Hnc Hddf Hfits) as Hch.
  cbn [a_shob a_ob a_osz] in Hch. fold o in Hch.
  forward_call (gv, d, c3_fs k, ts, sv_fp sv, sv_lay sv, sv_dd sv, W, o,
                offset_val ipc ib, iw_read shb ib isz ibs ipc ns, ns, dp_fmt (c3_par k), true, zdss_read,
                sf_outBuff (c3_s k), sf_outSize (c3_s k), 0, sf_outEnd (c3_s k), vop,
                offset_val opc ob, offset_val osz ob).
  { split.
    - unfold cont_pre. split; [rewrite <- Hts; exact Hcf|]. split; [exact Hnc|]. split; [exact Hunit|].
      split; [rep_lia|].
      split; [unfold outarr_ok, o, oa_stable; cbn [oa_sh oa_N oa_c oa_d oa_cap]; split; [auto|];
              destruct (is_skip (sv_fp sv)); repeat split; try rep_lia; lia|].
      split; [exact Hlay|]. split; [exact Hch|]. split; [exact Hlw|].
      split; [intros Hsk'; unfold o, oa_stable; cbn [oa_cap]; rewrite Hsk'; reflexivity|].
      split.
      { intros _. cbn [iw_off iw_base iw_s iw_read iw_c iw_N iw_sh]. split; [reflexivity|].
        split; [|split; [rewrite Zlength_sublist; lia | apply byte_cells_zbytes; auto]].
        unfold inwin_ok, win_ok; cbn [iw_off iw_base iw_s iw_read iw_c iw_N iw_sh]. rewrite Zlength_sublist by lia.
        repeat split; auto; try rep_lia;
          [rewrite Zlength_map; auto | apply Forall_sublist; auto | rewrite sublist_map; f_equal; f_equal; lia]. }
      split; [intros Hz; unfold o, oa_stable in Hz; cbn [oa_N] in Hz; unfold o, oa_stable; cbn [oa_base];
              apply Hw0; exact Hz|].
      destruct H0 as [Hf _]; exact Hf.
    - unfold ccs_out_ok, o, oa_stable; cbn [oa_cap oa_N oa_d oa_base]. auto. }
  Intros vret. destruct vret as [[[rr oc'] fs'] tabs']. cbn [fst snd] in *.
  match goal with H: cont_res _ _ _ _ _ _ _ _ _ |- _ => rename H into Hres end.
  assert (Hrr: 0 <= rr <= Int64.max_unsigned) by (destruct Hres; lia).
  forward_call (if is_error_code rr then rr else 0).
  { destruct (is_error_code rr); rep_lia. }
  forward_if.
  - (* an error: return it *)
    assert (Hrerr: is_error_code rr = true).
    { destruct (is_error_code rr) eqn:E; auto;
      try match goal with H: Int.repr _ <> Int.zero |- _ => rewrite E in H; simpl in H; contradiction end. }
    rewrite Hrerr.
    rewrite tabs_match_rep. Intros lxb.
    unfold MORE_COMMANDS, abbreviate.
    apply semax_dowhile0.
    match goal with |- semax _ ?P (Ssequence _ _) _ => apply semax_seq with P end.
    { apply semax_dowhile0_gen.
      match goal with |- semax _ _ _ ?Q =>
        let Q' := eval cbv beta iota delta [overridePost loop1_ret_assert] in Q in change Q with Q' end.
      abbreviate_semax.
      forward_if.
      { match goal with H: 0 <> 0 |- _ => contradiction H; reflexivity end. }
      forward. entailer!. }
    abbreviate_semax.
    apply semax_dowhile0. apply semax_dowhile0.
    assert (Hcold': cold01 fs').
    { match goal with H: fs_ddictIsCold fs' = _ \/ _ |- _ => destruct H as [Hc|Hc] end;
      unfold cold01 in *; rewrite Hc; auto. }
    pose proof (read_err_why3 M _ _ _ _ _ _ _ ns rr _ oc' fs' tabs' Ha Hstart Hinv Hstage Hnc Hunit
                  ltac:(lia) ltac:(simpl; lia) Hddf ltac:(simpl; rewrite Est; discriminate) Hres Hrerr
                  (fun _ => eq_refl) ltac:(simpl; rewrite Est; discriminate)) as Hwhy.
    assert (Hfp': fs_fParams fs' = fs_fParams (c3_fs k))
      by (match goal with H: is_error_code rr = true -> fs_fParams fs' = _ |- _ => exact (H Hrerr) end).
    destruct Hres as (_ & Hloc' & Hunc' & _). unfold o, oa_stable in Hloc', Hunc'.
    cbn [oa_N oa_c oa_d oa_cap] in Hloc', Hunc'.
    assert (Hpre': sublist 0 opos oc' = sublist 0 opos oc).
    { rewrite <- Hpre. apply (unch_sublist _ _ opc (opc + (if is_skip (sv_fp sv) then 0 else osz - opc)));
        auto; lia. }
    eapply semax_pre; [| apply (ret_err_semax3 Espec _ DENT TABS BR _
         {| w_smw := 1; w_k := c3_with_fs k fs' (tabs_of (sv_dd sv) lxb tabs'); w_sv := sv; w_ipc := ipc;
            w_opc := opc; w_oc := oc'; w_dl := dl |} _ rr _err_code__4 RT HT Ha Hstart)];
      cbn [w_k w_oc a_st a_osz a_opos a_oc]; [ | | exact Hloc' | exact Hpre' | exact Hrr | exact Hwhy
                                              | stable_noex | reflexivity | reflexivity | exact HRr].
    2:{ unfold base_call. cbn [c3_with_fs c3_stable c3_par c3_set c3_dict c3_fs]. rewrite Hfp'.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ Hb7)))))); auto. }
    gather_SEP (dent_of DENT gv (dd_ox (sv_dd sv))) (lay_res (sv_lay sv)) (lay_rest (sv_lay sv) (sv_dd sv)).
    sep_apply (modus_ponens_wand (dent_of DENT gv (dd_ox (sv_dd sv)) * lay_res (sv_lay sv) * lay_rest (sv_lay sv) (sv_dd sv))
                 (dd_all DENT gv d st (c3_dict k))).
    unfold dd_all.
    unfold ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, cgroup3, sgroup.
    cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_ob a_osz a_opos a_oc a_shb a_ib
      a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_fs c3_fs c3_tabs c3_stable c3_dict c3_s
      c3_par c3_sp c3_set].
    rewrite ?Hb1, ?Est, ?Hstage, ?Hos, ?Hrerr. cbn [andb negb]. cbv iota.
    unfold o, oa_stable. cbn [oa_sh oa_N oa_base oa_d oa_c].
    entailer!.
    destruct (is_skip (sv_fp sv)) eqn:Esk; unfold in_res; rewrite Esk; cancel.
  - (* a success *)
    assert (Hok: is_error_code rr = false).
    { destruct (is_error_code rr) eqn:E; auto.
      match goal with H: Int.repr _ = Int.zero |- _ =>
        rewrite E in H; simpl in H; rewrite ?E in H; apply (f_equal Int.unsigned) in H;
        rewrite Int.unsigned_repr, Int.unsigned_zero in H by rep_lia; discriminate end. }
    rewrite Hok. cbn [oa_sh oa_N oa_base oa_d oa_c]. simpl andb. cbv iota.
    eapply semax_post_flipped; [apply semax_skip | ..]; intros; cbv [normal_ret_assert RA_normal RA_break
      RA_continue RA_return loop1_ret_assert];
      try (apply andp_left2; apply FF_left).
    apply andp_left2. apply exp_right with rr. apply exp_right with oc'. apply exp_right with fs'.
    apply exp_right with tabs'.
    eapply derives_trans; [apply (andp_right _ _ _ (prop_right _ _ (conj Hres (conj Hok Hrr))) (derives_refl _)) |].
    unfold Qf. apply derives_refl. }
Intros rr oc' fs' tabs'. unfold Qf. apply semax_extract_prop. intros (Hres & Hok & Hrr).
(* a success leaves the tables initialised: the litExtra buffer of the uninitialised case is not used *)
destruct (read_cont_stable3 _ _ _ _ _ _ _ _ _ _ _ _ nil M Ha Hinv Hstage Est Hnc Hunit Hns0 ltac:(simpl; lia)
            Hddf Hdb Hres Hok) as (sv' & dl' & Hinv' & Hdd').
cbn [a_shob a_ob a_osz] in Hres. fold o in Hres.
assert (Hcold': cold01 fs').
{ destruct Hres as (_&_&_&_&Hpost). rewrite Hok in Hpost.
  destruct (sv_fp sv); cbn [cont_post] in Hpost; try contradiction.
  - destruct Hpost as (_&_&tsx&_&Hc). unfold c_frame in Hc. destruct Hc as (_&Hc&_). exact Hc.
  - destruct Hpost as (cx&tsx&_&_&_&_&_&_&_&Hc). unfold c_frame in Hc. destruct Hc as (_&Hc&_). exact Hc. }
assert (Htabs: exists ts', tabs' = Some ts').
{ destruct Hres as (_&_&_&_&Hpost). rewrite Hok in Hpost.
  destruct (sv_fp sv); cbn [cont_post] in Hpost; try contradiction.
  - destruct Hpost as (_&_&ts'&->&_). eauto.
  - destruct Hpost as (_&ts'&_&_&_&_&->&_). eauto. }
destruct Htabs as [ts' ->].
destruct Hres as (_ & Hloc' & _).
unfold MORE_COMMANDS, abbreviate. forward. forward.
rewrite HRn. unfold ds_inv_x.
Exists {| w_smw := 1; w_k := c3_with_fs k fs' (tabs_of (sv_dd sv) nil (Some ts')); w_sv := sv'; w_ipc := ipc + ns;
          w_opc := opc + rr; w_oc := oc'; w_dl := dl' |}.
gather_SEP (dent_of DENT gv (dd_ox (sv_dd sv))) (lay_res (sv_lay sv)) (lay_rest (sv_lay sv) (sv_dd sv)).
sep_apply (modus_ponens_wand (dent_of DENT gv (dd_ox (sv_dd sv)) * lay_res (sv_lay sv) * lay_rest (sv_lay sv) (sv_dd sv))
             (dd_all DENT gv d st (c3_dict k))).
unfold dd_all.
unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, cgroup3, sgroup, tabs_rep, tabs_of.
cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_ob a_osz a_opos a_oc a_shb a_ib
  a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_fs c3_fs c3_tabs c3_stable c3_dict c3_s c3_par
  c3_sp c3_set option_map].
rewrite ?Hb1, ?Est, ?Hstage, ?Hos, ?Hok. cbn [andb negb]. cbv iota.
unfold o, oa_stable. cbn [oa_sh oa_N oa_base oa_d oa_c].
entailer!.
all: repeat match goal with |- _ /\ _ => split end.
all: try exact Hcold'.
all: try (unfold loop_extra; cbn; intros _ Hx; rewrite Hstage in Hx; unfold zdss_read, zdss_loadHeader in Hx; lia).
all: try (unfold exit_ok; cbn; intros Hx; discriminate).
all: try (unfold entry_ok; cbn; intros _ Hx; rewrite Hstage in Hx; unfold zdss_read, zdss_init in Hx; lia).
all: try (destruct (is_skip (sv_fp sv)) eqn:Esk; unfold in_res; rewrite Esk; cancel).
all: try (unfold untouched_ok; cbn; intros Hx; congruence).
all: try stable_noex.
Qed.

End CM_R3VSt_1.
