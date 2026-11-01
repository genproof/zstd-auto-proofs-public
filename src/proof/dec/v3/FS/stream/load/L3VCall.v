(* FS3 streaming, case zdss_load: the premises of the call ZSTD_decompressContinueStream (load_call_pre),
   frame-field folding, the stream buffer split around the call.  Port of v2 StreamSeg_load.v. *)
Require Import Zstd.proof.dec.v3.FS.stream.load.L3Borrow Zstd.proof.dec.v3.FS.stream.load.L3VIf Zstd.proof.dec.v3.FS.stream.load.L3Dsub.
Local Open Scope logic.

Section CM_L3VCall_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma lcp_vlong_inj : forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  vlong x = vlong y -> x = y.
Proof.
intros x y Hx Hy H. unfold vlong in H. inversion H as [H1].
rewrite <- (Int64.unsigned_repr x), <- (Int64.unsigned_repr y) by rep_lia. congruence.
Qed.

(* the unit view of a frame at zdss_load: same C fields, the unit's size E *)
Lemma lcp_frame : forall fs tabs fp l dd E,
  c_frame fs tabs fp l dd -> fp_complete fp = false -> fp_rawbody fp = false ->
  fs_expected fs = vlong E -> 0 <= E < 2 ^ 32 ->
  exists ts, tabs = TInit (dd_ox dd) ts /\ c_frame fs (TInit (dd_ox dd) ts) (fp_unit fp) l dd /\
    fp_complete (fp_unit fp) = false /\
    unit_ok (fp_unit fp) E /\ is_skip (fp_unit fp) = is_skip fp /\ lay_fields fs l /\ lay_dd l dd /\
    0 <= fp_ws fp /\ 0 <= fp_bsm fp /\
    (is_skip fp = false ->
       0 <= fp_inpos fp < E /\ E <= Z.max (fp_bsm fp) 4 /\ bytes_ok (fp_loaded fp) /\
       fp_inpos fp = Zlength (fp_loaded fp)).
Proof.
intros fs tabs fp l dd E Hfr Hnc Hraw HE HE0.
destruct fp as [|hb|hdr got|hdr z].
1,2: destruct Hfr as (_&_&_&_&_&[]).
- destruct Hfr as (H1&H2&H3&Hlf&Hld&Hl&[ts Hts]&Hh&Hgot&Hsz&Hif).
  cbn [fp_complete] in Hnc. rewrite Hnc in Hif. destruct Hif as [Hstg Hexp].
  apply Z.eqb_neq in Hnc.
  assert (Hz: (0 =? le_field hdr 4 4) = false) by (apply Z.eqb_neq; lia).
  assert (E = le_field hdr 4 4) by (rewrite HE in Hexp; apply lcp_vlong_inj in Hexp; rep_lia).
  exists ts. split; [exact Hts|].
  cbn [fp_unit fp_complete unit_ok is_skip fp_ws fp_bsm]. unfold c_frame. rewrite Hz.
  split; [refine (conj H1 (conj H2 (conj H3 (conj Hlf (conj Hld _))))); split; [exact Hl|];
    split; [eauto|]; split; [exact Hh|]; split; [lia|]; split; [exact Hsz|]; split; assumption|].
  split; [reflexivity|]. split; [split; [reflexivity|exact H]|]. split; [reflexivity|].
  split; [exact Hlf|]. split; [exact Hld|]. split; [lia|]. split; [lia|]. discriminate.
- destruct Hfr as (H1&H2&H3&Hlf&Hld&Hft&Hfp&Hbsm0&Hbsm&Hws&Hws2&Hcs&Hck&Hdm&Htabs&Hph&Hdec&Hvc&Hxxh&Hout&Hphx&Hgotb).
  destruct Htabs as (ts0 & Htabs & Hts0). exists ts0. split; [exact Htabs|].
  cbn [fp_unit fp_complete unit_ok is_skip fp_ws fp_bsm fp_inpos fp_loaded fp_rawbody] in *.
  unfold c_frame, zp_set_got, zp_with, phase_fields in *. cbn [zp_h zp_dm zp_bsm zp_ign zp_ts zp_out zp_ph zp_got] in *.
  destruct (zp_ph z) as [|bh| |] eqn:Eph.
  + destruct Hph as [Hstg Hexp].
    assert (E = ZSTD_blockHeaderSize) by (rewrite HE in Hexp; apply lcp_vlong_inj in Hexp; unfold ZSTD_blockHeaderSize in *; rep_lia).
    split; [(refine (conj H1 (conj H2 (conj H3 (conj Hlf (conj Hld _)))));
    refine (conj Hft (conj Hfp (conj Hbsm0 (conj Hbsm (conj Hws (conj Hws2 (conj Hcs (conj Hck (conj Hdm (conj (ex_intro _ ts0 (conj eq_refl Hts0))
    (conj _ (conj Hdec (conj Hvc (conj Hxxh (conj Hout (conj _ _))))))))))))))))); [split; assumption|rewrite Zlength_nil; unfold ZSTD_blockHeaderSize; lia|constructor]|].
    split; [reflexivity|]. split; [split; [reflexivity|exact H]|]. split; [reflexivity|].
    split; [exact Hlf|]. split; [exact Hld|]. split; [lia|]. split; [lia|]. intros _. unfold ZSTD_blockHeaderSize in *.
    split; [split; [apply Zlength_nonneg|lia]|]. split; [lia|]. split; [exact Hgotb|reflexivity].
  + rewrite Hraw in Hph |- *.
    destruct Hph as (c & Hc & Hstg & Hbt & Hrle & Hexp).
    destruct Hphx as (Hbhl & Hbhb & c' & Hc' & Hcr & Hgc & Ht3).
    rewrite Hc in Hc'. inversion Hc'; subst c'.
    assert (E = c) by (rewrite HE in Hexp; apply lcp_vlong_inj in Hexp; unfold ZSTD_BLOCKSIZE_MAX in *; rep_lia).
    split; [(refine (conj H1 (conj H2 (conj H3 (conj Hlf (conj Hld _)))));
    refine (conj Hft (conj Hfp (conj Hbsm0 (conj Hbsm (conj Hws (conj Hws2 (conj Hcs (conj Hck (conj Hdm (conj (ex_intro _ ts0 (conj eq_refl Hts0))
    (conj _ (conj Hdec (conj Hvc (conj Hxxh (conj Hout (conj _ _))))))))))))))))); [exists c; repeat split; assumption|split; [exact Hbhl|split; [exact Hbhb|exists c; rewrite Zlength_nil; repeat split; auto; lia]]|constructor]|].
    split; [reflexivity|]. split; [exists c; split; [exact Hc|split; [reflexivity|exact H]]|].
    split; [reflexivity|].
    split; [exact Hlf|]. split; [exact Hld|]. split; [lia|]. split; [lia|]. intros _.
    split; [split; [apply Zlength_nonneg|lia]|]. split; [lia|]. split; [exact Hgotb|reflexivity].
  + destruct Hph as [Hstg Hexp]. destruct Hphx as [Hg4 Hck1].
    assert (E = 4) by (rewrite HE in Hexp; apply lcp_vlong_inj in Hexp; rep_lia).
    split; [(refine (conj H1 (conj H2 (conj H3 (conj Hlf (conj Hld _)))));
    refine (conj Hft (conj Hfp (conj Hbsm0 (conj Hbsm (conj Hws (conj Hws2 (conj Hcs (conj Hck (conj Hdm (conj (ex_intro _ ts0 (conj eq_refl Hts0))
    (conj _ (conj Hdec (conj Hvc (conj Hxxh (conj Hout (conj _ _))))))))))))))))); [split; assumption|split; [rewrite Zlength_nil; lia|exact Hck1]|constructor]|].
    split; [reflexivity|]. split; [split; [reflexivity|exact H]|]. split; [reflexivity|].
    split; [exact Hlf|]. split; [exact Hld|]. split; [lia|]. split; [lia|]. intros _.
    split; [split; [apply Zlength_nonneg|lia]|]. split; [lia|]. split; [exact Hgotb|reflexivity].
  + discriminate.
Qed.

(* the unit in the stream buffer after the load: its first E cells *)
Lemma lcp_ring_prefix : forall (ring: list val) g ibs ipc L,
  sublist 0 (Zlength g) ring = zbytes g -> 0 <= L -> 0 <= ipc -> ipc + L <= Zlength ibs ->
  sublist 0 (Zlength g + L) (copy_cells ring (Zlength g) (zbytes ibs) ipc L) =
    zbytes (g ++ sublist ipc (ipc + L) ibs).
Proof.
intros ring g ibs ipc L Hg HL Hi Hie. unfold copy_cells. rewrite Hg.
pose proof (Zlength_nonneg g).
assert (H1: Zlength (zbytes g) = Zlength g) by (rewrite Zlength_map; auto).
assert (H2: Zlength (sublist ipc (ipc + L) (zbytes ibs)) = L)
  by (rewrite Zlength_sublist; rewrite ?Zlength_map; lia).
rewrite app_assoc, sublist_app1 by (rewrite ?Zlength_app; lia).
rewrite sublist_same by (rewrite ?Zlength_app; lia).
rewrite map_app, sublist_map. reflexivity.
Qed.

Lemma lcp_win : forall fp ring ibs ipc L E,
  is_skip fp = false -> fp_inpos fp = Zlength (fp_loaded fp) ->
  sublist 0 (Zlength (fp_loaded fp)) ring = zbytes (fp_loaded fp) ->
  bytes_ok (fp_loaded fp) -> bytes_ok ibs -> 0 <= ipc -> ipc + L <= Zlength ibs ->
  L = E - fp_inpos fp -> 0 <= fp_inpos fp <= E ->
  sublist 0 E (ring_load fp ring (fp_inpos fp) ibs ipc L) = zbytes (fp_loaded fp ++ sublist ipc (ipc + L) ibs) /\
  Zlength (fp_loaded fp ++ sublist ipc (ipc + L) ibs) = E /\
  bytes_ok (fp_loaded fp ++ sublist ipc (ipc + L) ibs).
Proof.
intros fp ring ibs ipc L E Hsk Hp Hg Hgb Hib Hi Hie HL HP.
unfold ring_load. rewrite Hsk. rewrite Hp in *.
split; [replace E with (Zlength (fp_loaded fp) + L) by lia; apply lcp_ring_prefix; auto; lia|].
split; [rewrite Zlength_app, Zlength_sublist; lia|].
apply Forall_app; split; auto. apply Forall_sublist; auto.
Qed.

(* the pure premises of the call *)
Lemma load_call_pre : forall a k0 sv ipc opc oc dl E L,
  dsa_ok a -> call_inv a k0 sv ipc opc oc dl -> sf_stage (c3_s k0) = zdss_load ->
  0 <= sf_inSize (c3_s k0) -> 0 <= sf_outSize (c3_s k0) ->
  Zlength (ring_load (sv_fp sv) (sf_ring (c3_s k0)) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L) =
    sf_inSize (c3_s k0) + sf_outSize (c3_s k0) ->
  fs_expected (c3_fs k0) = vlong E -> 0 <= E < 2 ^ 32 ->
  L = Z.min (E - fp_inpos (sv_fp sv)) (a_isz a - ipc) -> L = E - fp_inpos (sv_fp sv) ->
  let s := c3_s k0 in
  let ring1 := ring_load (sv_fp sv) (sf_ring s) (fp_inpos (sv_fp sv)) (a_ibs a) ipc L in
  let u := ld_u sv (a_ibs a) ipc L in
  exists ts ostart,
    c3_tabs k0 = TInit (dd_ox (sv_dd sv)) ts /\ sf_outStart s = vlong ostart /\ 0 <= ostart <= sf_outSize s /\
    sf_outEnd s = vlong ostart /\
    c_frame (c3_fs k0) (TInit (dd_ox (sv_dd sv)) ts) (fp_unit (sv_fp sv)) (sv_lay sv) (sv_dd sv) /\
    lay_dd (sv_lay sv) (sv_dd sv) /\
    fp_complete (fp_unit (sv_fp sv)) = false /\ unit_ok (fp_unit (sv_fp sv)) E /\
    is_skip (fp_unit (sv_fp sv)) = is_skip (sv_fp sv) /\
    0 < sf_inSize s /\ Zlength ring1 = sf_inSize s + sf_outSize s /\
    (dc_stable (a_st a) = true ->
       ostart = 0 /\ opc = Zlength (ss_out (dc_ss (a_st a)) ++ dl) /\
       outarr_ok (o_st a sv opc oc) /\ lay_at (sv_lay sv) (o_st a sv opc oc) /\
       (is_skip (sv_fp sv) = false -> inwin_ok (i_st s ring1 u) /\ Zlength u = E)) /\
    (dc_stable (a_st a) = false ->
       outarr_ok (o_bf s ring1 ostart sv) /\ lay_at (sv_lay sv) (o_bf s ring1 ostart sv) /\
       (is_skip (sv_fp sv) = false -> inwin_ok (i_bf s ring1 u) /\ Zlength u = E)).
Proof.
intros a k0 sv ipc opc oc dl E L Ha Hinv Hst Hin Hout Hrl HE HE0 HL HL2. cbv zeta.
destruct sv as [fp pend ahead lay dd]; cbn [sv_fp sv_pend sv_ahead sv_lay sv_dd] in *.
destruct Hinv as (Hipc & Hopc & Hoc & Hoc0 & Hdl & Hdl1 & Hdlb & Hbase & Hssin & Hnfp & Hnfp2 & Hinit &
  Hcore & Hdd & Hst1 & Hah & Hpend & Hm).
destruct Ha as (Hbo & Hbi & Hobuf & Hwo & Hwi & Hwob & Hrb & Hdict & Herr & Hopos & Hosz & Hoclen & Hipos & Hisz &
  Hibl & Hibs & Hsout & Hwit).
unfold c_core in Hcore; cbv zeta in Hcore.
destruct Hcore as (_ & _ & Hsz & Hrest).
replace (sf_stage (c3_s k0) =? zdss_init) with false in Hrest by (rewrite Hst; reflexivity).
replace (sf_stage (c3_s k0) =? zdss_loadHeader) with false in Hrest by (rewrite Hst; reflexivity).
destruct Hrest as (_ & Hfr & Hring & _ & Hld & _ & _).
destruct (Hld Hst) as (Hpn & Hnc & Hraw & Hoe & Hip & Hgot); clear Hld.
unfold c_ring in Hring; cbv zeta in Hring.
destruct Hring as (Hnn & Hptr & Hbsm & ostart & oend & Hos & Hoe' & Hrng & Hmode).
cbn [sv_fp sv_pend sv_ahead sv_lay] in *.
clear Hm Hpend Hah Hwit Hbo Hbi Hinit Hnfp Hnfp2 Hssin Hdict Herr Hwo Hwi.
destruct (lcp_frame _ _ _ _ _ _ Hfr Hnc Hraw HE HE0) as (ts & Hts & Hfr' & Hnc' & Hu & Hsk & Hlf & Hldd & Hws & Hbsm0 & Hz).
assert (Hos2: 0 <= ostart <= sf_outSize (c3_s k0))
  by (destruct (dc_stable (a_st a)); [destruct Hmode as (-> & _); lia | destruct Hmode as (Hx & _); lia]).
assert (HLle: L <= a_isz a - ipc) by lia.
(* the unit in the stream buffer *)
assert (Hwin: is_skip fp = false ->
  sublist 0 E (ring_load fp (sf_ring (c3_s k0)) (fp_inpos fp) (a_ibs a) ipc L) =
    zbytes (fp_loaded fp ++ sublist ipc (ipc + L) (a_ibs a)) /\
  Zlength (fp_loaded fp ++ sublist ipc (ipc + L) (a_ibs a)) = E /\
  bytes_ok (fp_loaded fp ++ sublist ipc (ipc + L) (a_ibs a)) /\ E <= sf_inSize (c3_s k0)).
{ intros Hs. destruct (Hz Hs) as (HP & HEb & Hgb & HPl).
  destruct (lcp_win fp (sf_ring (c3_s k0)) (a_ibs a) ipc L E) as (W1 & W2 & W3); auto; try lia.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. lia. }
exists ts, ostart.
split; [exact Hts|]. split; [exact Hos|]. split; [exact Hos2|]. split; [congruence|].
split; [exact Hfr'|]. split; [exact Hldd|]. split; [exact Hnc'|]. split; [exact Hu|]. split; [exact Hsk|].
split; [lia|]. split; [exact Hrl|].
unfold ld_u; cbn [sv_fp sv_lay].
split.
- intros Hstb. rewrite Hstb in Hmode.
  destruct Hmode as (Ho0 & _ & _ & ob & osz & Hob & Hlay). inversion Hob; subst ob osz; clear Hob.
  assert (Hso: Zlength (ss_out (dc_ss (a_st a))) = a_opos a).
  { specialize (Hsout Hstb). apply (f_equal (@Zlength val)) in Hsout.
    rewrite Zlength_sublist, Zlength_map in Hsout by lia. lia. }
  assert (Hopc2: opc = Zlength (ss_out (dc_ss (a_st a)) ++ dl)) by (rewrite Zlength_app; lia).
  split; [exact Ho0|]. split; [exact Hopc2|].
  split.
  { unfold outarr_ok, o_st; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap sv_fp].
    split; [exact Hwob|]. destruct (is_skip fp); repeat split; auto; lia. }
  split.
  { unfold lay_at, o_st; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap sv_fp].
    destruct lay as [|eb ec gp|b pe od|b ps pe e]; auto.
    - destruct Hlay as (-> & _ & Hpe & Hpe2). split; [reflexivity|]. split; [lia|].
      destruct (is_skip fp); lia.
    - destruct Hlay as (-> & He & Hpe & _ & _). destruct Hlf as (_ & _ & Hps & _).
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      destruct e; simpl in *; auto; contradiction. }
  intros Hs. destruct (Hwin Hs) as (W1 & W2 & W3 & W4).
  split; [|exact W2].
  unfold inwin_ok, win_ok, i_st; cbn [iw_sh iw_base iw_N iw_c iw_off iw_s].
  split; [apply writable_readable; apply writable_Ews|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hrl|]. split; [reflexivity|].
  split; [exact W3|]. rewrite W2, Z.add_0_l. exact W1.
- intros Hstb. rewrite Hstb in Hmode.
  destruct Hmode as (Hoend & _ & _ & _ & Hlay).
  assert (Hol: Zlength (sublist (sf_inSize (c3_s k0)) (sf_inSize (c3_s k0) + sf_outSize (c3_s k0))
     (ring_load fp (sf_ring (c3_s k0)) (fp_inpos fp) (a_ibs a) ipc L)) = sf_outSize (c3_s k0))
    by (rewrite Zlength_sublist by lia; lia).
  split.
  { unfold outarr_ok, o_bf; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap sv_fp].
    split; [apply writable_Ews|]. split; [exact Hol|].
    destruct (is_skip fp); repeat split; lia. }
  split.
  { unfold lay_at, o_bf; cbn [oa_sh oa_base oa_N oa_c oa_d oa_cap sv_fp].
    destruct lay as [|eb ec gp|b pe od|b ps pe e]; auto.
    - destruct Hlay as (-> & _ & -> & -> & _ & Hz0). split; [reflexivity|]. split; [reflexivity|].
      destruct (is_skip fp); lia.
    - destruct Hlay as (-> & -> & Hpe & Hpc & Hroom & _). destruct Hlf as (_ & _ & Hps & _).
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      unfold lay_room in Hroom. destruct e as [|e1 elen|]; auto.
      destruct Hroom as (-> & _ & Hr). unfold WILDCOPY_OVERLENGTH in Hr. lia. }
  intros Hs. destruct (Hwin Hs) as (W1 & W2 & W3 & W4).
  split; [|exact W2].
  unfold inwin_ok, win_ok, i_bf; cbn [iw_sh iw_base iw_N iw_c iw_off iw_s].
  split; [apply slice.cleave_readable1; apply writable_readable; apply writable_Ews|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite Zlength_sublist by lia; lia|].
  split; [reflexivity|]. split; [exact W3|].
  rewrite W2, Z.add_0_l, sublist_sublist00 by lia. exact W1.
Qed.

(* folding the frame fields back for a call *)
Lemma ff_fold : forall p fs,
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p
  |-- frame_fields p fs.
Proof. intros. unfold frame_fields. cancel. Qed.

Lemma in_res_ns : forall fp sh b N c off u, is_skip fp = false ->
  data_at sh (tarray tuchar N) c b |--
  in_res fp {| iw_sh := sh; iw_base := b; iw_N := N; iw_c := c; iw_off := off; iw_s := u |}.
Proof. intros. unfold in_res. rewrite H. simpl. auto. Qed.

Lemma in_res_split : forall fp i,
  data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) |--
  in_res fp i * (if is_skip fp then data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) else emp).
Proof. intros. unfold in_res. destruct (is_skip fp); simpl; cancel. Qed.

Lemma in_res_join : forall fp i,
  in_res fp i * (if is_skip fp then data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i) else emp)
  |-- data_at (iw_sh i) (tarray tuchar (iw_N i)) (iw_c i) (iw_base i).
Proof. intros. unfold in_res. destruct (is_skip fp); simpl; cancel. Qed.

(* ---------- buffered mode: the stream buffer [inBuff | outBuff] around the call ---------- *)

(* from the v2 proof of case zdss_read *)
Lemma ring_data_split : forall b n1 n2 (c: list val), 0 <= n1 -> 0 <= n2 -> Zlength c = n1 + n2 ->
  field_compatible (tarray tuchar (n1 + n2)) [] b ->
  data_at Ews (tarray tuchar (n1 + n2)) c b =
  (data_at Ews (tarray tuchar n1) (sublist 0 n1 c) b *
   data_at Ews (tarray tuchar n2) (sublist n1 (n1 + n2) c) (offset_val n1 b))%logic.
Proof.
intros b n1 n2 c H1 H2 Hc Hf.
unfold tarray. rewrite (split2_data_at_Tarray_tuchar Ews (n1 + n2) n1 c b) by lia.
replace (n1 + n2 - n1) with n2 by lia.
rewrite field_address0_offset by auto with field_compatible.
simpl. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma pws_cons : forall w W, pw_pred w * pws_pred W |-- pws_pred (w :: W).
Proof. intros. unfold pws_pred. simpl. auto. Qed.

Lemma pws_uncons : forall w W, pws_pred (w :: W) |-- pw_pred w * pws_pred W.
Proof. intros. unfold pws_pred. simpl. auto. Qed.

Lemma data_at_end_wvp : forall sh n (c: list val) p, readable_share sh -> 0 < n ->
  data_at sh (tarray tuchar n) c p |-- weak_valid_pointer (offset_val n p).
Proof.
intros sh n c p Hr Hn.
eapply derives_trans; [apply data_at_memory_block|].
simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; auto].
Qed.

Lemma ews_halves : forall t v p,
  data_at Ews t v p = (data_at (fst (slice.cleave Ews)) t v p * data_at (snd (slice.cleave Ews)) t v p)%logic.
Proof. intros. symmetry. apply data_at_share_join. apply slice.cleave_join. Qed.

Lemma ews_join : forall t v p,
  data_at (fst (slice.cleave Ews)) t v p * data_at (snd (slice.cleave Ews)) t v p |-- data_at Ews t v p.
Proof. intros. rewrite (ews_halves t v p). auto. Qed.

Lemma ring_join : forall b n1 n2 (c1 c2: list val), 0 <= n1 -> 0 <= n2 -> Zlength c1 = n1 -> Zlength c2 = n2 ->
  field_compatible (tarray tuchar (n1 + n2)) [] b ->
  data_at Ews (tarray tuchar n1) c1 b * data_at Ews (tarray tuchar n2) c2 (offset_val n1 b) |--
  data_at Ews (tarray tuchar (n1 + n2)) (c1 ++ c2) b.
Proof.
intros b n1 n2 c1 c2 H1 H2 Hc1 Hc2 Hf.
rewrite (ring_data_split b n1 n2 (c1 ++ c2)) by (try rewrite Zlength_app; auto; lia).
rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
rewrite sublist_same by lia. rewrite Hc1. replace (n1 + n2 - n1) with n2 by lia.
rewrite sublist_same by lia. replace (n1 - n1) with 0 by lia. auto.
Qed.


(* ---------- the frame's DDict around the call (L3Borrow = read/R3Borrow.v) ---------- *)

Lemma dd_borrow_unf : forall DENT gv p st k W dd,
  (forall x buf, dd = Some (x, buf) -> dd_src st k x buf) ->
  stream_dict_ok W st -> set_cur_ok st ->
  dgroup DENT gv p (c3_dict k) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
    set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) |--
    !! dd_facts W dd && (dd_lend DENT gv dd * (dd_lend DENT gv dd -* dd_all DENT gv p st (c3_dict k))).
Proof. intros. apply dd_borrow; auto. Qed.

Lemma lend_split : forall DENT gv l dd, lay_dd l dd ->
  dd_lend DENT gv dd |-- dent_of DENT gv (dd_ox dd) * lay_res l * lay_rest l dd.
Proof. intros. rewrite (lend_lay DENT gv l dd H). auto. Qed.

Lemma lend_join : forall DENT gv p st d l dd, lay_dd l dd ->
  dent_of DENT gv (dd_ox dd) * lay_res l * lay_rest l dd * (dd_lend DENT gv dd -* dd_all DENT gv p st d) |--
  dgroup DENT gv p d * dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st).
Proof.
intros. rewrite <- (lend_lay DENT gv l dd H). apply modus_ponens_wand.
Qed.

Lemma lay_wit_cons : forall w W l, lay_wit W l -> lay_wit (w :: W) l.
Proof.
intros w W l H.
assert (Hv: forall p, (pws_pred W |-- valid_pointer p) -> (pws_pred (w :: W) |-- valid_pointer p)).
{ intros p Hp. eapply derives_trans; [apply pws_uncons|]. apply sepcon_valid_pointer2. exact Hp. }
destruct l as [|eb ec gp|b pe [[[eb ec] gp]|]|b ps pe [|e1 elen|sh eb en ec e1 elen]]; cbn [lay_wit] in *; auto;
  unfold pre_ok in *.
- destruct H as [H1 [H2|(H2&H3&H4)]]; split; auto.
- destruct H as [H1 [H2|(H2&H3&H4)]]; split; auto.
- destruct H as [H1 H2]; split; auto.
Qed.

(* the tables in the post of ZSTD_decompressContinue as tabs_rep of tabs_of (lxb is irrelevant for initialised
   tables) *)
Lemma tabs_rep_of : forall TABS gv p dd t,
  (match t with Some ts' => TABS gv p (dd_ox dd) ts' | None => EX lxb: list Z, tables_uninit p lxb end) =
  EX lxb: list Z, tabs_rep TABS gv p (tabs_of dd lxb t).
Proof.
intros. destruct t as [ts'|]; cbn [tabs_of tabs_rep]; [|reflexivity].
apply pred_ext; [Exists (@nil Z); apply derives_refl|Intros lxb; apply derives_refl].
Qed.

(* ld_dd from the borrow's facts *)
Lemma ld_dd_of : forall W dd, dd_facts W dd -> ld_dd dd.
Proof.
intros W dd H x buf E. subst dd. unfold dd_facts in H. tauto.
Qed.

(* ---------- the error return after the call ---------- *)

(* a return whose value v the precondition knows, into an abstract return assertion *)
Lemma ld_semax_ret : forall {cs: compspecs} {Espec: OracleKind} Delta P ret (v: val) (R: ret_assert),
  ENTAIL Delta, P |-- local (fun rho => v = eval_expr (Ecast ret (ret_type Delta)) rho) ->
  ENTAIL Delta, P |-- tc_expr Delta (Ecast ret (ret_type Delta)) ->
  ENTAIL Delta, P |-- RA_return R (Some v) ->
  semax Delta P (Sreturn (Some ret)) R.
Proof.
intros cs Espec Delta P ret v R H0 H1 H2.
eapply semax_pre; [|apply semax_return].
apply andp_right; [exact H1|].
intro rho.
change ((local (tc_environ Delta) && P) rho) with (local (tc_environ Delta) rho && P rho).
apply derives_trans with (!! (v = eval_expr (Ecast ret (ret_type Delta)) rho) && (local (tc_environ Delta) rho && P rho)).
{ apply andp_right; [|apply derives_refl].
  eapply derives_trans; [apply (H0 rho)|]. unfold local, lift1. simpl. apply derives_refl. }
apply derives_extract_prop; intros Hv. unfold cast_expropt; unfold_lift. rewrite <- Hv. apply (H2 rho).
Qed.

End CM_L3VCall_1.

Ltac ld_ret rr Her :=
  try (eapply semax_seq; [|apply semax_ff]);
  eapply ld_semax_ret with (v := Vlong (Int64.repr rr));
  [ go_lowerx; apply prop_right;
    match goal with H: context [eval_id _err_code__5] |- _ =>
      unfold_lift in H; simpl in H; let Hq := fresh "Hq" in destruct H as [Hq _];
      unfold_lift; rewrite <- Hq; rewrite Her; reflexivity end
  | entailer!
  | repeat match goal with P := _ : ret_assert |- _ => subst P end; unfold abbreviate;
    cbn [RA_return overridePost loop1_ret_assert loop2_ret_assert switch_ret_assert loop_nocontinue_ret_assert] ].

Section CM_L3VCall_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Lemma ld_in_err : forall DENT TABS BR, In ERR_isError_spec (stream_G3 DENT TABS BR).
Proof.
intros. unfold stream_G3, FS3_G. apply in_or_app; left. apply in_or_app; left.
unfold Gprog. apply in_or_app; right. right. unfold Specs_L0. apply in_or_app; left.
unfold Specs_util. simpl In. repeat (first [left; reflexivity | right]).
Qed.

Lemma ld_in_ccs : forall DENT TABS BR, In (ZSTD_decompressContinueStream_spec3 DENT TABS) (stream_G3 DENT TABS BR).
Proof. intros. apply ld_in_ss. unfold stream_ss3. right; left; reflexivity. Qed.

Definition ld_Gu (DENT: dent_pred) (TABS: tabs_pred) : funspecs :=
  [ZSTD_decompressContinueStream_spec3 DENT TABS; ERR_isError_spec].

Lemma ld_Gu_in : forall DENT TABS BR sp, In sp (ld_Gu DENT TABS) -> In sp (stream_G3 DENT TABS BR).
Proof.
intros DENT TABS BR sp [<-|[<-|[]]]; [apply ld_in_ccs|apply ld_in_err].
Qed.

End CM_L3VCall_2.
