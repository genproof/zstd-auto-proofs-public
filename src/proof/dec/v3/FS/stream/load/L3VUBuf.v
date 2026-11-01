(* FS3 streaming, case zdss_load: buffered mode, the loaded unit: inPos := 0, then
   ZSTD_decompressContinueStream(zds, &op, oend, inBuff, neededInSize) in `do { } while (0)`.  Port of v2 ld_unit_buf. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Stmts Zstd.proof.dec.v3.FS.stream.load.L3Borrow Zstd.proof.dec.v3.FS.stream.load.L3Dsub Zstd.proof.dec.v3.FS.stream.load.L3VIf Zstd.proof.dec.v3.FS.stream.load.L3VCall Zstd.proof.dec.v3.FS.stream.load.L3Dm Zstd.proof.dec.v3.FS.stream.load.L3DmV.
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Ex.
Local Open Scope logic.

Ltac ldunf3 := unfold ld_join_full, ds_LI_L, ds_LI_S, k_load, c3_with_s, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given;
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set s_load
       sf_stage sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize
       sf_hostage sf_nfp sf_expOut sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].

Section CM_L3VUBuf_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma ld_unit_buf : forall (Espec: OracleKind) DENT TABS BR a k0 sv ipc opc oc dl E L R,
  MF3 -> RET3x -> P_load_cont_hist_buf -> P_load_cont_buf -> P_load_err_why ->
  lay_cbound (sv_fp sv) (sv_lay sv) ->
  DENT_OK DENT -> TABS_OK TABS -> dsa_ok a -> start_ok a ->
  call_inv a k0 sv ipc opc oc dl -> (dc_stable (a_st a) = false -> sublist opc (a_osz a) oc = sublist opc (a_osz a) (a_oc a)) ->
  sf_stage (c3_s k0) = zdss_load ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) ->
  Zlength (sf_ring (c3_s k0)) = sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  dc_stable (a_st a) = false -> ex_call a (ld_w0 k0 sv ipc opc oc dl) ->
  RA_normal R = ds_inv_x DENT TABS a -> RA_return R = RA_return (ds_R_x DENT TABS BR a) ->
  semax (ds_Delta DENT TABS BR)
    (ld_join_full DENT TABS a
       (k_load k0 (fp_inpos (sv_fp sv) + L)
          (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L))
       sv (ipc + L) opc oc dl E L)
    ld_unit0 (overridePost FF (switch_ret_assert R)).
Proof.
intros Espec DENT TABS BR a k0 sv ipc opc oc dl E L R HMF HRET Hhb Hcb Hew Hcbd HD HT Ha Hs0 Hinv Huntc Hstage HE HE0
  HL Hrl0 Hstable Hxc HRn HRr.
destruct R as [Rn Rb Rc Rr]; cbn [RA_normal RA_return] in HRn, HRr; subst Rn Rr.
apply (ld_Delta_lift DENT TABS BR (ld_Gu DENT TABS)); [apply ld_Gu_in|]. unfold ld_DeltaG, ld_Gu.
unfold ld_join_full. apply semax_extract_PROP; intros HLE.
cbv beta iota delta [ld_unit0 ld_rest ds_case_load].
set (P := fp_inpos (sv_fp sv)) in *.
set (ring1 := ring_load (sv_fp sv) (sf_ring (c3_s k0)) P (a_ibs a) ipc L).
pose proof Ha as Ha'.
destruct Ha' as (Hbo & Hbi & Hstb & Hwo & Hwi & Hwob & Hrb & Hdict & Herr & Hopos & Hosz & Hloc0 & Hipos & Hisz & Hlibs & Hbibs & Hstbuf & Hwit).
pose proof Hinv as Hinv'.
destruct Hinv' as (Hipc & Hopc & Hloc & Hpre & Hldl & Hdl & Hbdl & Hbase & Hbin & Hnfp1 & Hnfp2 & Hnfp3 & Hcore &
                  Hdd & Hstout & Hahead & Hbsm & Hmodel & Hlh & Hsah & Hexp & HTT).
destruct (load_facts _ _ _ _ _ Hcore Hstage) as (E' & fstg & HE' & HP & HPE & HE32 & Hfst & Hfst7 & Hskip & HEin & [ts Hts] & Hib).
rewrite HE in HE'. apply vlong_eq in HE'; [|rep_lia|rep_lia]. subst E'.
assert (HL0: 0 <= L <= E - P) by (subst L; lia).
ldunf3. Intros.
match goal with H: byte_cells ring1 |- _ => rename H into Hbyc1 end.
match goal with H: sf_inBuff (c3_s k0) <> nullval -> sf_outBuff _ = _ |- _ => rename H into H6 end.
forward.
assert_PROP (Zlength ring1 = sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) as Hrl1
  by (unfold ring_rep; rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction); entailer!).
destruct (load_call_pre a k0 sv ipc opc oc dl E L Ha Hinv Hstage ltac:(assumption) ltac:(assumption) Hrl1 HE HE0 HL HLE)
  as (ts' & ostart & Hts' & Hos & Hos1 & Hoe & Hcf & Hldd & Hfc & Hun & Hsk1 & Hin0 & Hlr & Hstp & Hbfp).
rewrite Hts in Hts'. inversion Hts'; subst ts'. clear Hts'.
match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: (ds_inv_x DENT TABS a) end.
{ entailer!. }
2: { forward. apply andp_left2; apply derives_refl. }
forward.
unfold ring_rep. rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
unfold cgroup3. Intros.
rewrite Hts. unfold tabs_rep.
(* the frame's DDict lends its entropy and content *)
assert (Hsrc: forall x buf, sv_dd sv = Some (x, buf) -> dd_src (a_st a) k0 x buf).
{ intros x buf Hx. apply Hdd; [rewrite Hstage; unfold zdss_read, zdss_load; lia|exact Hx]. }
assert (Hscur: set_cur_ok (a_st a)) by (destruct Hbase as (_&_&_&_&Hc&_); exact Hc).
assert (Hdr3: dict_rel3 (a_st a) (c3_dict k0)) by (destruct Hbase as (_&_&_&Hr&_); exact Hr).
sep_apply (dd_all_bytes_keep DENT (a_gv a) (a_d a) (a_st a) (c3_dict k0) (a_W a) Hdr3 Hscur Hdict).
Intros. match goal with H: dicts_bytes _ |- _ => rename H into Hdb end.
assert (Hdm: ld_dm (a_st a) k0 (sv_fp sv)) by (intros cd Hc; exact (ld_dm_of _ _ _ _ _ Hdb Hc)).
sep_apply (dd_borrow_unf DENT (a_gv a) (a_d a) (a_st a) k0 (a_W a) (sv_dd sv) Hsrc Hdict Hscur).
Intros. match goal with H: dd_facts _ _ |- _ => rename H into Hddf end.
sep_apply (lend_split DENT (a_gv a) (sv_lay sv) (sv_dd sv) Hldd).
rewrite Hstable in *.
destruct (Hbfp eq_refl) as (Hob & Hlb & Hiw).
assert (Hob0: sf_outBuff (c3_s k0) = offset_val (sf_inSize (c3_s k0)) (sf_inBuff (c3_s k0)))
  by (apply H6; intro Hn; rewrite Hn in Hib; contradiction).
assert (Hldok: ld_ok a k0 sv ipc opc oc dl E L).
{ unfold ld_ok, ld_ring.
  refine (conj Ha (conj Hinv (conj Hstage (conj HE (conj HE0 (conj HL (conj HLE (conj _ (conj _
    (conj Hrl0 (conj Hrl1 (conj Hbyc1 _)))))))))))).
  all: first [lia | eapply ld_dd_of; exact Hddf]. }
assert_PROP (field_compatible (tarray tuchar (sf_inSize (c3_s k0) + sf_outSize (c3_s k0))) []
               (sf_inBuff (c3_s k0))) as Hfc0 by entailer!.
rewrite (ring_data_split (sf_inBuff (c3_s k0)) (sf_inSize (c3_s k0)) (sf_outSize (c3_s k0)) ring1) by first [lia | assumption].
rewrite <- Hob0.
rewrite (ews_halves (tarray tuchar (sf_inSize (c3_s k0))) (sublist 0 (sf_inSize (c3_s k0)) ring1)).
change (data_at (fst (slice.cleave Ews)) (tarray tuchar (sf_inSize (c3_s k0)))
          (sublist 0 (sf_inSize (c3_s k0)) ring1) (sf_inBuff (c3_s k0))) with
  (data_at (iw_sh (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L)))
     (tarray tuchar (iw_N (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L))))
     (iw_c (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L)))
     (iw_base (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L)))).
sep_apply (in_res_split (fp_unit (sv_fp sv)) (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L))).
change (data_at (snd (slice.cleave Ews)) (tarray tuchar (sf_inSize (c3_s k0)))
          (sublist 0 (sf_inSize (c3_s k0)) ring1) (sf_inBuff (c3_s k0))) with
  (pw_pred (pw_bytes (snd (slice.cleave Ews)) (sf_inSize (c3_s k0)) (sublist 0 (sf_inSize (c3_s k0)) ring1)
              (sf_inBuff (c3_s k0)))).
sep_apply (pws_cons (pw_bytes (snd (slice.cleave Ews)) (sf_inSize (c3_s k0))
             (sublist 0 (sf_inSize (c3_s k0)) ring1) (sf_inBuff (c3_s k0))) (a_W a)).
change (data_at Ews (tarray tuchar (sf_outSize (c3_s k0)))
          (sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0)) ring1)
          (sf_outBuff (c3_s k0))) with
  (data_at (oa_sh (o_bf (c3_s k0) ring1 ostart sv)) (tarray tuchar (oa_N (o_bf (c3_s k0) ring1 ostart sv)))
     (oa_c (o_bf (c3_s k0) ring1 ostart sv)) (oa_base (o_bf (c3_s k0) ring1 ostart sv))).
rewrite Hos.
set (W' := pw_bytes (snd (slice.cleave Ews)) (sf_inSize (c3_s k0)) (sublist 0 (sf_inSize (c3_s k0)) ring1)
             (sf_inBuff (c3_s k0)) :: a_W a).
assert (Hpar: dp_fmt (c3_par k0) = 0 \/ dp_fmt (c3_par k0) = 1)
  by (match goal with H: par_ok _ |- _ => destruct H as [Hf _]; exact Hf end).
assert (Hcp: cont_pre (c3_fs k0) ts (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) W'
               (o_bf (c3_s k0) ring1 ostart sv) (sf_inBuff (c3_s k0)) (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L))
               E (dp_fmt (c3_par k0))).
{ unfold cont_pre.
  split; [exact Hcf|]. split; [exact Hfc|]. split; [exact Hun|]. split; [rep_lia|].
  split; [exact Hob|]. split; [exact Hlb|].
  split; [exact (Hhb a k0 sv ipc opc oc dl E L ostart Hldok Hstable Hos)|].
  split; [apply lay_wit_cons; eapply lay_wit_of; eassumption|].
  split; [intros Hk; unfold o_bf; cbn [oa_cap]; rewrite <- Hsk1, Hk; reflexivity|].
  split.
  { intro Hn. rewrite Hsk1 in Hn. destruct (Hiw Hn) as [Hi1 Hi2].
    split; [cbn [iw_off iw_base i_bf]; rewrite isptr_offset_val_zero by exact Hib; reflexivity|].
    split; [exact Hi1|]. split; [exact Hi2|]. cbn [iw_c i_bf]. apply Forall_sublist. exact Hbyc1. }
  split; [|exact Hpar].
  intros _. eapply derives_trans; [apply pws_uncons|]. apply sepcon_weak_valid_pointer1.
  cbn [pw_pred oa_base o_bf]. rewrite Hob0.
  apply data_at_end_wvp; [apply slice.cleave_readable2; auto with share | lia]. }
assert (Hcst: c3_stable k0 = false) by (destruct Hbase as (Hs&_); rewrite Hs; exact Hstable).
rewrite Hcst.
forward_call (a_gv a, a_d a, c3_fs k0, ts, fp_unit (sv_fp sv), sv_lay sv, sv_dd sv, W',
  o_bf (c3_s k0) ring1 ostart sv, sf_inBuff (c3_s k0), i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L), E,
  dp_fmt (c3_par k0), false, sf_stage (c3_s k0), sf_outBuff (c3_s k0), sf_outSize (c3_s k0), ostart, sf_outEnd (c3_s k0),
  a_vop a, offset_val opc (a_ob a), offset_val (a_osz a) (a_ob a)).
{ unfold ccs_out_ok, o_bf; cbn. rewrite Hsk1. auto. }
Intros x. destruct x as [[[rr oc'] fs'] tabs']. cbn [Datatypes.fst Datatypes.snd] in *. Intros.
match goal with H: cont_res _ _ _ _ _ rr _ _ _ |- _ => rename H into Hcr end.
match goal with H: false = false -> _ -> cont_exact _ _ _ _ _ _ _ _ _ |- _ => rename H into Hcx end.
assert (Hrr: 0 <= rr <= Int64.max_unsigned) by apply (proj1 Hcr).
assert (Hloc': Zlength oc' = sf_outSize (c3_s k0)) by apply (proj1 (proj2 Hcr)).
assert (Hcold2: cold01 fs')
  by (match goal with H: cold01 (c3_fs k0) |- _ => unfold cold01 in *;
      match goal with Hc: fs_ddictIsCold fs' = fs_ddictIsCold _ \/ _ |- _ => destruct Hc as [Hc|Hc]; rewrite Hc; auto end end).
assert (Hsl: Zlength (sublist 0 (sf_inSize (c3_s k0)) ring1) = sf_inSize (c3_s k0))
  by (rewrite Zlength_sublist by lia; lia).
pose proof (ring_join (sf_inBuff (c3_s k0)) (sf_inSize (c3_s k0)) (sf_outSize (c3_s k0))
              (sublist 0 (sf_inSize (c3_s k0)) ring1) oc' ltac:(lia) ltac:(lia) Hsl Hloc' Hfc0) as Hrj.
assert (Hbyn: byte_cells (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc')).
{ apply Forall_app. split; [apply Forall_sublist; exact Hbyc1|].
  apply (proj1 (proj2 (proj2 (proj2 Hcr)))). cbn [o_bf oa_c]. apply Forall_sublist; exact Hbyc1. }
rewrite (tabs_rep_of TABS (a_gv a) (a_d a) (sv_dd sv) tabs'). Intros lxb.
forward.
forward_call (if is_error_code rr then rr else 0).
{ destruct (is_error_code rr); rep_lia. }
forward_if.
- (* an error: returned *)
  eapply semax_seq; [|apply semax_ff].
  apply ld_dowhile0. apply ld_dowhile0_if0. apply ld_dowhile0. apply ld_dowhile0.
  match goal with H: Int.repr _ <> Int.zero |- _ => rename H into Hz end.
  assert (Her: is_error_code rr = true).
  { destruct (is_error_code rr) eqn:He; auto; exfalso; apply Hz; cbv iota beta; try rewrite He; reflexivity. }
  assert (Hwhy: err_why a rr).
  { apply (Hew a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' HMF Hldok Hs0 (fun _ => Hcbd) Hos Hos1); [|exact Her].
    rewrite Hstable. exact Hcr. }
  set (kE := k_cont k0 fs' tabs' lxb (sv_dd sv)
               (s_cont (c3_s k0) (sf_stage (c3_s k0)) (sf_outEnd (c3_s k0))
                  (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc'))).
  assert (Hbc: base_call (a_st a) kE).
  { destruct Hbase as (B1&B2&B3&B4&B5&B6&B7). unfold base_call, kE, k_cont; cbn [c3_stable c3_par c3_set c3_dict c3_fs].
    refine (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 (conj _ B7)))))).
    match goal with H: is_error_code rr = true -> fs_fParams fs' = _ |- _ => rewrite (H Her); exact B6 end. }
  assert (Hxe: ex_err a rr)
    by exact (ld_x_err a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' ts Ha Hinv Hstage HE HE0 HL HLE Hrl0 Hts
                Hos Hos1 (Z.lt_le_incl _ _ Hin0) (fun Hk => proj1 (Hiw Hk)) (Hcx eq_refl) Hxc Her).
  ld_ret rr Her.
  eapply derives_trans; [|apply (ret3x_err_ok HRET DENT TABS BR a
     {| w_smw := 1; w_k := kE; w_sv := sv; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |} rr
     HT Ha Hs0 Hbc ltac:(cbn; assumption) ltac:(cbn; assumption) Hrr Hwhy Hxe)].
  unfold ds_LI_L, ds_LI_S, kE, k_cont, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, cgroup3, ring_rep.
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set s_cont sf_stage
       sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut
       sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].
  rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
  match goal with |- context [in_res ?f ?i] => sep_apply (in_res_join f i) end.
  unfold W'.
  sep_apply (pws_uncons (pw_bytes (snd (slice.cleave Ews)) (sf_inSize (c3_s k0))
               (sublist 0 (sf_inSize (c3_s k0)) ring1) (sf_inBuff (c3_s k0))) (a_W a)).
  cbn [pw_pred].
  cbn [i_bf iw_sh iw_N iw_c iw_base o_bf oa_sh oa_N oa_c oa_base oa_d].
  sep_apply (ews_join (tarray tuchar (sf_inSize (c3_s k0))) (sublist 0 (sf_inSize (c3_s k0)) ring1)
               (sf_inBuff (c3_s k0))).
  rewrite Hob0.
  sep_apply Hrj.
  sep_apply (lend_join DENT (a_gv a) (a_d a) (a_st a) (c3_dict k0) (sv_lay sv) (sv_dd sv) Hldd).
  rewrite Her, Hos, Hcst.
  entailer!.
- (* a success: the new invariant *)
  match goal with H: Int.repr _ = Int.zero |- _ => rename H into Hz end.
  assert (Hok: is_error_code rr = false).
  { destruct (is_error_code rr) eqn:He; auto. exfalso.
    cbv iota beta in Hz. rewrite He in Hz. cbv iota beta in Hz.
    apply (f_equal Int.unsigned) in Hz. rewrite Int.unsigned_repr in Hz by rep_lia. discriminate. }
  forward.
  destruct (Hcb a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' lxb HMF Hldok Hstable Hdm Hcbd Hos Hos1 Hcr Hok)
    as (sv2 & Hinv2).
  set (rd := andb (rr =? 0) (negb (is_skip (sv_fp sv)))) in *.
  set (k2 := k_cont k0 fs' tabs' lxb (sv_dd sv)
               (s_cont (c3_s k0) (if rd then zdss_read else zdss_flush)
                  (if rd then sf_outEnd (c3_s k0) else vlong (ostart + rr))
                  (sublist 0 (sf_inSize (c3_s k0)) ring1 ++ oc'))) in *.
  assert (Hxn: ex_call a {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by exact (ld_x_next a k0 sv ipc opc oc dl E L ostart rr oc' fs' tabs' ts sv2 lxb Ha Hinv Hstage HE HE0 HL HLE Hrl0
                Hts Hos Hos1 (Z.lt_le_incl _ _ Hin0) (fun Hk => proj1 (Hiw Hk)) (Hcx eq_refl) Hxc Hok).
  unfold ds_inv_x.
  Exists {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |}.
  assert (Hent: entry_ok a {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by (intros _ Hc; unfold k2, k_cont in Hc; cbn in Hc; destruct rd; unfold zdss_read, zdss_flush, zdss_init in Hc; lia).
  assert (Hex: exit_ok a {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by (intros Hc; discriminate).
  assert (Hle: loop_extra {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |}).
  { intros _ Hc. unfold k2, k_cont in Hc; cbn in Hc. destruct rd; unfold zdss_read, zdss_flush, zdss_loadHeader in Hc; lia. }
  assert (Hun': untouched_ok a {| w_smw := 1; w_k := k2; w_sv := sv2; w_ipc := ipc + L; w_opc := opc; w_oc := oc; w_dl := dl |})
    by (intros _; apply Huntc; reflexivity).
  unfold ds_LI_Px, ds_LI_L, ds_LI_S, k2, k_cont, ctx_rep3, ctx_body3, fgroup3, sgroup, sf_given, cgroup3, ring_rep.
  cbn [w_k w_sv w_ipc w_opc w_oc w_dl w_smw c3_fs c3_tabs c3_stable c3_dict c3_s c3_par c3_sp c3_set s_cont sf_stage
       sf_inBuff sf_inSize sf_inPos sf_outBuff sf_outSize sf_outStart sf_outEnd sf_lhSize sf_hostage sf_nfp sf_expOut
       sf_hbuf sf_over sf_ring sf_mem sf_held sf_given].
  rewrite if_false by (intro Hn; rewrite Hn in Hib; contradiction).
  unfold W'.
  sep_apply (pws_uncons (pw_bytes (snd (slice.cleave Ews)) (sf_inSize (c3_s k0))
               (sublist 0 (sf_inSize (c3_s k0)) ring1) (sf_inBuff (c3_s k0))) (a_W a)).
  cbn [pw_pred].
  sep_apply (in_res_join (fp_unit (sv_fp sv)) (i_bf (c3_s k0) ring1 (ld_u sv (a_ibs a) ipc L))).
  cbn [i_bf iw_sh iw_N iw_c iw_base o_bf oa_sh oa_N oa_c oa_base oa_d].
  sep_apply (ews_join (tarray tuchar (sf_inSize (c3_s k0))) (sublist 0 (sf_inSize (c3_s k0)) ring1)
               (sf_inBuff (c3_s k0))).
  rewrite Hob0.
  sep_apply Hrj.
  sep_apply (lend_join DENT (a_gv a) (a_d a) (a_st a) (c3_dict k0) (sv_lay sv) (sv_dd sv) Hldd).
  try rewrite Hsk1; rewrite Hos, Hcst, Hok; try fold rd.
  entailer!.
  all: try (destruct rd; unfold zdss_read, zdss_flush; rep_lia).
  unfold k_cont in Hinv2. rewrite Hcst in Hinv2.
  split; [exact Hinv2|destruct rd; unfold zdss_read, zdss_flush; rep_lia].
Qed.

End CM_L3VUBuf_1.
