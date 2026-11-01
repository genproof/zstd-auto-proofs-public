(* FS3 streaming, case zdss_read: the branch decoding a unit directly from the caller's input,
   buffered mode (v2 StreamSeg_read.v rd_direct_bf), in the small context of its two callees. *)
Require Import Zstd.proof.dec.v3.FS.stream.read.R3Step Zstd.proof.dec.v3.FS.stream.read.R3Err Zstd.proof.dec.v3.FS.stream.read.R3Dsub Zstd.proof.dec.v3.FS.stream.read.R3VSt Zstd.proof.dec.v3.FS.stream.read.R3Buf Zstd.proof.dec.v3.FS.stream.read.R3Dm Zstd.proof.dec.v3.FS.stream.read.R3DmV.
Require Import Zstd.proof.dec.v3.FS.stream.read.R3X.
Local Open Scope logic.

Section CM_R3VBf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma dd_facts_cons : forall w W dd, dd_facts W dd -> dd_facts (w :: W) dd.
Proof.
intros w W dd H. destruct dd as [[x buf]|]; [|exact I]. unfold dd_facts in *.
destruct H as (H1&H2&H3&H4&H5&H6). do 4 (split; [assumption|]). split; [|exact H6].
destruct H5 as [H5|(H5&H7)]; [left; exact H5|right; split; [exact H5|]].
unfold pws_pred in *. cbn [map fold_right]. apply sepcon_valid_pointer2. exact H7.
Qed.

(* the history bytes for a compressed block at outStart, any progress *)
Lemma read_cont_hist_buf3' : forall obuf sout s fp l dd W ostart fs tabs,
  c_ring false obuf sout s fp nil l -> c_frame fs tabs fp l dd -> dd_facts W dd -> lay_cbound fp l ->
  sf_outStart s = vlong ostart -> sf_outEnd s = vlong ostart -> 0 <= ostart <= sf_outSize s ->
  sf_outSize s <= 2 ^ 32 ->
  Zlength (sf_ring s) = sf_inSize s + sf_outSize s -> 0 <= sf_inSize s -> byte_cells (sf_ring s) ->
  cont_hist fp l (oa_ring s fp ostart).
Proof.
intros obuf sout s fp l dd W ostart fs tabs Hr Hcf Hdf Hcb Hos Hoe Hor HN Hlr HI Hby.
destruct fp as [| | |hdr z]; try exact I.
destruct (c_frame_zstd_facts _ _ _ _ _ _ Hcf) as (_&Hld&Hdm&Hb0&Hbsm&Hws&_).
eapply read_cont_hist_buf3; eauto.
Qed.

(* the exact claim: the loop invariant's ex_call is rebuilt from ZSTD_decompressContinueStream's cont_exact on the
   model's state (R3X.rx_ok), an error is the model's (R3X.rx_err) *)
Lemma rd_direct_bf3 : forall (Espec: OracleKind) DENT TABS BR (a: dsa) (w: lw) (R: ret_assert) (ns fstage e: Z),
  MF3 -> RET3x -> TABS_OK TABS -> dsa_ok a -> start_ok a ->
  call_inv a (w_k w) (w_sv w) (w_ipc w) (w_opc w) (w_oc w) (w_dl w) -> untouched_ok a w -> w_smw w = 1 ->
  sf_stage (c3_s (w_k w)) = zdss_read -> fp_complete (sv_fp (w_sv w)) = false ->
  unit_ok (sv_fp (w_sv w)) ns -> 0 < ns -> w_ipc w + ns <= a_isz a ->
  dc_stable (a_st a) = false ->
  lay_cbound (sv_fp (w_sv w)) (sv_lay (w_sv w)) ->
  ex_call a w -> rx_hd a w fstage e -> rx_ns a w fstage e = ns ->
  RA_break R = ds_inv_x DENT TABS a -> RA_return R = RA_return (ds_R_x DENT TABS BR a) ->
  semax (rd_Delta2 DENT TABS)
    (PROPx [] (LOCALx (temp _neededInSize (Vlong (Int64.repr ns)) :: ds_LI_L a w) (SEPx (ds_LI_S DENT TABS a w))))
    rd_direct R.
Proof.
intros Espec DENT TABS BR a w R ns fstage e M RT HT Ha Hstart Hinv Hun Hsmw Hstage Hnc Hunit Hns0 Hge0 Est Hcb Hxa Hhd Hnsx
  HRn HRr.
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
assert (Hoe': sf_outEnd (c3_s k) = vlong ostart) by (rewrite <- Hoso; exact Hos).
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
repeat flatten_sepcon_in_SEP.
(* the stream buffer [inBuff | outBuff] *)
rewrite Est in Hring.
assert (HinB: sf_inBuff (c3_s k) <> nullval /\ isptr (sf_inBuff (c3_s k)) /\
              Z.max (fp_bsm (sv_fp sv)) 4 <= sf_inSize (c3_s k))
  by (destruct Hring as (?&?&?&_); auto).
destruct HinB as (HinB & PinB & HnI).
unfold ring_rep. rewrite if_false by auto. Intros.
match goal with H: Zlength (sf_ring (c3_s k)) = _ |- _ => rename H into Hlr end.
pose proof (read_pre_buf3 _ _ _ _ _ _ _ ostart Hinv Hstage Est Hos ltac:(lia) Hlr H1 H2) as Hpb.
cbv zeta in Hpb. destruct Hpb as (Hoa & Hlay).
assert_PROP (field_compatible (tarray tuchar (sf_inSize (c3_s k) + sf_outSize (c3_s k))) []
               (sf_inBuff (c3_s k))) as Hfc by entailer!.
rewrite (ring_data_split (sf_inBuff (c3_s k)) (sf_inSize (c3_s k)) (sf_outSize (c3_s k)) (sf_ring (c3_s k)))
  by (auto; lia).
rewrite <- (H8 HinB). repeat flatten_sepcon_in_SEP.
set (cI := sublist 0 (sf_inSize (c3_s k)) (sf_ring (c3_s k))).
gather_SEP (data_at Ews (tarray tuchar (sf_inSize (c3_s k))) cI (sf_inBuff (c3_s k))) (pws_pred W).
change (data_at Ews (tarray tuchar (sf_inSize (c3_s k))) cI (sf_inBuff (c3_s k)) * pws_pred W)%logic
  with (pws_pred (pw_bytes Ews (sf_inSize (c3_s k)) cI (sf_inBuff (c3_s k)) :: W)).
set (W' := pw_bytes Ews (sf_inSize (c3_s k)) cI (sf_inBuff (c3_s k)) :: W).
pose proof (dd_facts_cons (pw_bytes Ews (sf_inSize (c3_s k)) cI (sf_inBuff (c3_s k))) W _ Hddf) as Hddf'.
fold W' in Hddf'.
pose proof (lay_wit_of W' (sv_lay sv) (sv_dd sv) Hld Hddf') as Hlw.
set (o := oa_ring (c3_s k) (sv_fp sv) ostart) in *.
assert (HN: sf_outSize (c3_s k) <= 2 ^ 32) by lia.
pose proof (read_cont_hist_buf3' _ _ _ _ _ _ _ ostart _ _ ltac:(rewrite <- Hpend; exact Hring) Hcf Hddf Hcb
              Hos Hoe' ltac:(lia) HN Hlr H1 H7) as Hch.
fold o in Hch.
evar (Qf: Z -> list val -> fstate -> option tstate -> environ -> mpred).
apply semax_seq with (Q := exp (fun rr: Z => exp (fun oc': list val => exp (fun fs': fstate =>
                             exp (fun tabs': option tstate => Qf rr oc' fs' tabs'))))).
{ apply semax_dowhile0_gen.
  match goal with |- semax _ _ _ ?P =>
    let P' := eval cbv beta iota delta [overridePost loop1_ret_assert] in P in change P with P' end.
  abbreviate_semax.
  forward_call (gv, d, c3_fs k, ts, sv_fp sv, sv_lay sv, sv_dd sv, W', o,
                offset_val ipc ib, iw_read shb ib isz ibs ipc ns, ns, dp_fmt (c3_par k), false, zdss_read,
                sf_outBuff (c3_s k), sf_outSize (c3_s k), ostart, sf_outEnd (c3_s k), vop,
                offset_val opc ob, offset_val osz ob).
  { split.
    - unfold cont_pre. split; [rewrite <- Hts; exact Hcf|]. split; [exact Hnc|]. split; [exact Hunit|].
      split; [rep_lia|].
      split; [exact Hoa|].
      split; [exact Hlay|]. split; [exact Hch|]. split; [exact Hlw|].
      split; [intros Hsk'; unfold o, oa_ring; cbn [oa_cap]; rewrite Hsk'; reflexivity|].
      split.
      { intros _. cbn [iw_off iw_base iw_s iw_read iw_c iw_N iw_sh]. split; [reflexivity|].
        split; [|split; [rewrite Zlength_sublist; lia | apply byte_cells_zbytes; auto]].
        unfold inwin_ok, win_ok; cbn [iw_off iw_base iw_s iw_read iw_c iw_N iw_sh]. rewrite Zlength_sublist by lia.
        repeat split; auto; try rep_lia;
          [rewrite Zlength_map; auto | apply Forall_sublist; auto | rewrite sublist_map; f_equal; f_equal; lia]. }
      split; [intros _; unfold o, oa_ring; cbn [oa_base]; rewrite (H8 HinB); unfold W', pws_pred; cbn [map fold_right];
              apply sepcon_weak_valid_pointer1; apply pw_ring_wvp; lia|].
      destruct H0 as [Hf _]; exact Hf.
    - unfold ccs_out_ok, o, oa_ring; cbn [oa_cap oa_N oa_d oa_base]. auto. }
  Intros vret. destruct vret as [[[rr oc'] fs'] tabs']. cbn [fst snd] in *.
  match goal with H: cont_res _ _ _ _ _ _ _ _ _ |- _ => rename H into Hres end.
  match goal with H: false = false -> _ |- _ => pose proof (H eq_refl) as Hce; clear H end.
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
    assert (Hosb: 0 <= ostart <= sf_outSize (c3_s k)) by lia.
    pose proof (read_err_why3 M _ _ _ _ _ _ _ ns rr _ oc' fs' tabs' Ha Hstart Hinv Hstage Hnc Hunit
                  ltac:(lia) ltac:(simpl; lia) Hddf (fun _ => Hcb) Hres Hrerr
                  ltac:(simpl; rewrite Est; discriminate)
                  (fun _ => ex_intro _ ostart (conj Hos (conj Hosb eq_refl)))) as Hwhy.
    assert (Hfp': fs_fParams fs' = fs_fParams (c3_fs k))
      by (match goal with H: is_error_code rr = true -> fs_fParams fs' = _ |- _ => exact (H Hrerr) end).
    destruct Hres as (_ & Hloc' & _ & Hbyo' & _). unfold o, oa_ring in Hloc', Hbyo'.
    cbn [oa_N oa_c] in Hloc', Hbyo'.
    set (k' := c3_with_s (c3_with_fs k fs' (tabs_of (sv_dd sv) lxb tabs'))
                 (sf_cont (c3_s k) (sf_stage (c3_s k)) (sf_outEnd (c3_s k))
                    (sublist 0 (sf_inSize (c3_s k)) (sf_ring (c3_s k)) ++ oc'))).
    eapply semax_pre; [| apply (ret_err_semax3 Espec _ DENT TABS BR _
         {| w_smw := 1; w_k := k'; w_sv := sv; w_ipc := ipc;
            w_opc := opc; w_oc := oc1; w_dl := dl |} _ rr _err_code__4 RT HT Ha Hstart)];
      cbn [w_k w_oc a_st a_osz a_opos a_oc]; [ | | exact Hloc | exact Hpre | exact Hrr | exact Hwhy
                                              | | reflexivity | reflexivity | exact HRr].
    3:{ apply (rx_err _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e ns (sv_fp sv) (sv_lay sv) (sv_dd sv) ts ostart rr oc'
                fs' tabs' Hxa eq_refl Hhd Hnsx Hns0 ltac:(simpl; lia) Hcf Hnc Hts Hos ltac:(simpl; lia) ltac:(simpl; rep_lia)
                Hce Hrerr). }
    2:{ unfold base_call, k'. cbn [c3_with_s c3_with_fs c3_stable c3_par c3_set c3_dict c3_fs]. rewrite Hfp'.
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ Hb7)))))); auto. }
    gather_SEP (dent_of DENT gv (dd_ox (sv_dd sv))) (lay_res (sv_lay sv)) (lay_rest (sv_lay sv) (sv_dd sv)).
    sep_apply (modus_ponens_wand (dent_of DENT gv (dd_ox (sv_dd sv)) * lay_res (sv_lay sv) * lay_rest (sv_lay sv) (sv_dd sv))
                 (dd_all DENT gv d st (c3_dict k))).
    unfold dd_all.
    unfold ds_LI_L, ds_LI_S, k', ctx_rep3, ctx_body3, fgroup3, cgroup3, sgroup, sf_given.
    cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_ob a_osz a_opos a_oc a_shb a_ib
      a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_with_fs c3_fs c3_tabs c3_stable
      c3_dict c3_s c3_par c3_sp c3_set sf_cont sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
      sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held].
    rewrite ?Hb1, ?Est, ?Hstage, ?Hos, ?Hrerr. cbn [andb negb]. cbv iota.
    unfold ring_rep. rewrite if_false by auto.
    rewrite (ring_data_split (sf_inBuff (c3_s k)) (sf_inSize (c3_s k)) (sf_outSize (c3_s k))) by (auto; list_solve).
    rewrite sublist_app1, sublist_app2 by list_solve.
    autorewrite with sublist.
    rewrite <- (H8 HinB).
    unfold W'. change (pws_pred (pw_bytes Ews (sf_inSize (c3_s k)) cI (sf_inBuff (c3_s k)) :: W))
      with (data_at Ews (tarray tuchar (sf_inSize (c3_s k))) cI (sf_inBuff (c3_s k)) * pws_pred W)%logic.
    rewrite (sublist_same 0 (sf_outSize (c3_s k)) oc') by lia.
    unfold o, oa_ring. cbn [oa_sh oa_N oa_base oa_d oa_c].
    entailer!.
    + apply byte_cells_app; [apply byte_cells_sublist; exact H7 | apply Hbyo'; apply byte_cells_sublist; exact H7].
    + destruct (is_skip (sv_fp sv)) eqn:Esk; unfold in_res; rewrite Esk; cancel.
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
    eapply derives_trans; [apply (andp_right _ _ _ (prop_right _ _ (conj Hres (conj Hok (conj Hrr Hce)))) (derives_refl _)) |].
    unfold Qf. apply derives_refl. }
Intros rr oc' fs' tabs'. unfold Qf. apply semax_extract_prop. intros (Hres & Hok & Hrr & Hce).
(* a success leaves the tables initialised: the litExtra buffer of the uninitialised case is not used *)
pose proof (read_cont_buf3 _ _ _ _ _ _ _ _ _ _ _ _ _ nil M Ha Hinv Hstage Est Hnc Hunit Hns0 ltac:(simpl; lia)
            Hos ltac:(lia) Hlr H7 Hddf Hcb Hdb Hres Hok) as Hcbuf.
cbv zeta in Hcbuf. destruct Hcbuf as (sv' & Hinv' & Hdd' & Hcb').
fold o in Hres.
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
destruct Hres as (_ & Hloc' & _ & Hbyo' & _). unfold o, oa_ring in Hloc', Hbyo'. cbn [oa_N oa_c] in Hloc', Hbyo'.
unfold MORE_COMMANDS, abbreviate. forward. forward.
(* the exact claim of the next iteration *)
assert (Hxc: ex_call {| a_W := W; a_gv := gv; a_d := d; a_st := st; a_outp := outp; a_inp := inp; a_sho := sho;
                        a_shi := shi; a_shob := shob; a_obf := obf; a_osz := osz; a_opos := opos; a_oc := oc;
                        a_shb := shb; a_ibf := ibf; a_isz := isz; a_ipos := ipos; a_ibs := ibs; a_vop := vop |}
  {| w_smw := 1;
     w_k := c3_with_s (c3_with_fs k fs' (tabs_of (sv_dd sv) nil (Some ts')))
              (sf_cont (c3_s k) (if ((rr =? 0) && negb (is_skip (sv_fp sv)))%bool then zdss_read else zdss_flush)
                 (if ((rr =? 0) && negb (is_skip (sv_fp sv)))%bool then sf_outEnd (c3_s k) else vlong (ostart + rr))
                 (sublist 0 (sf_inSize (c3_s k)) (sf_ring (c3_s k)) ++ oc'));
     w_sv := sv'; w_ipc := ipc + ns; w_opc := opc; w_oc := oc1; w_dl := dl |}).
{ apply (rx_ok _ (Build_lw 1 k sv ipc opc oc1 dl) fstage e ns (sv_fp sv) (sv_lay sv) (sv_dd sv) ts ostart rr oc'
           fs' (Some ts') sv' Hxa eq_refl Hhd Hnsx Hns0 ltac:(simpl; lia) Hcf Hnc Hts Hos ltac:(simpl; lia)
           ltac:(simpl; rep_lia) Hce Hok Hloc' Hlr ltac:(simpl; lia)). }
rewrite HRn. unfold ds_inv_x.
set (rd := andb (rr =? 0) (negb (is_skip (sv_fp sv)))) in *.
Exists {| w_smw := 1;
          w_k := c3_with_s (c3_with_fs k fs' (tabs_of (sv_dd sv) nil (Some ts')))
                   (sf_cont (c3_s k) (if rd then zdss_read else zdss_flush)
                      (if rd then sf_outEnd (c3_s k) else vlong (ostart + rr))
                      (sublist 0 (sf_inSize (c3_s k)) (sf_ring (c3_s k)) ++ oc'));
          w_sv := sv'; w_ipc := ipc + ns; w_opc := opc; w_oc := oc1; w_dl := dl |}.
gather_SEP (dent_of DENT gv (dd_ox (sv_dd sv))) (lay_res (sv_lay sv)) (lay_rest (sv_lay sv) (sv_dd sv)).
sep_apply (modus_ponens_wand (dent_of DENT gv (dd_ox (sv_dd sv)) * lay_res (sv_lay sv) * lay_rest (sv_lay sv) (sv_dd sv))
             (dd_all DENT gv d st (c3_dict k))).
unfold dd_all.
unfold ds_LI_Px, ds_LI_L, ds_LI_S, ctx_rep3, ctx_body3, fgroup3, cgroup3, sgroup, tabs_rep, tabs_of, sf_given.
fold rd in Hxc. revert Hxc.
cbn [a_W a_gv a_d a_st a_outp a_inp a_sho a_shi a_shob a_ob a_osz a_opos a_oc a_shb a_ib
  a_isz a_ipos a_ibs a_vop w_smw w_k w_sv w_ipc w_opc w_oc w_dl c3_with_s c3_with_fs c3_fs c3_tabs c3_stable
  c3_dict c3_s c3_par c3_sp c3_set sf_cont sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize
  sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held option_map].
rewrite ?Hb1, ?Est, ?Hos, ?Hok. cbn [andb negb]. cbv iota. intros Hxc.
unfold ring_rep. rewrite if_false by auto.
rewrite (ring_data_split (sf_inBuff (c3_s k)) (sf_inSize (c3_s k)) (sf_outSize (c3_s k))) by (auto; list_solve).
rewrite sublist_app1, sublist_app2 by list_solve.
autorewrite with sublist.
rewrite <- (H8 HinB).
unfold W'. change (pws_pred (pw_bytes Ews (sf_inSize (c3_s k)) cI (sf_inBuff (c3_s k)) :: W))
  with (data_at Ews (tarray tuchar (sf_inSize (c3_s k))) cI (sf_inBuff (c3_s k)) * pws_pred W)%logic.
rewrite (sublist_same 0 (sf_outSize (c3_s k)) oc') by lia.
unfold o, oa_ring. cbn [oa_sh oa_N oa_base oa_d oa_c].
fold rd.
entailer!.
all: repeat match goal with |- _ /\ _ => split end.
all: try exact Hcold'.
all: try (apply byte_cells_app; [apply byte_cells_sublist; exact H7 | apply Hbyo'; apply byte_cells_sublist; exact H7]).
all: try (unfold loop_extra; cbn; intros _ Hx; destruct rd; unfold zdss_read, zdss_flush, zdss_loadHeader in Hx; lia).
all: try (destruct rd; unfold zdss_read, zdss_flush; rep_lia).
all: try (unfold exit_ok; cbn; intros Hx; discriminate).
all: try (unfold entry_ok; cbn; intros _ Hx; destruct rd; unfold zdss_read, zdss_flush, zdss_init in Hx; lia).
all: try (destruct (is_skip (sv_fp sv)) eqn:Esk; unfold in_res; rewrite Esk; cancel).
all: try exact Hun.
all: try exact Hxc.
Qed.

End CM_R3VBf_1.
