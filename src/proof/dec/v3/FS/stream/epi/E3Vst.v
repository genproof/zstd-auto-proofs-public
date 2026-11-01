(* FS3 streaming: the epilogue of ZSTD_decompressStream, the VST side: helpers, the context as the
   epilogue sees it, the returns (port of v2 src/proof/dec/FS/StreamSeg_epi.v). *)
Require Import Zstd.proof.dec.v3.FS.stream.S3Main Zstd.proof.dec.v3.FS.stream.epi.E3Defs.
Local Open Scope logic.

Section CM_E3Vst_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma epi_sub_pp : forall p i j, isptr p -> 0 <= j <= i -> i <= 2 ^ 30 ->
  force_val (sem_sub_pp tschar (offset_val i p) (offset_val j p)) = Vlong (Int64.repr (i - j)).
Proof.
intros p i j Hp Hj Hi. destruct p; try contradiction.
unfold sem_sub_pp; simpl. rewrite if_true by auto. simpl. f_equal.
rewrite !(Ptrofs.add_commut i0), Ptrofs.sub_shifted. rewrite Ptrofs.divs_one by reflexivity.
unfold Vptrofs, Ptrofs.sub. rewrite !Ptrofs.unsigned_repr by rep_lia. simpl.
unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma epi_sub_pp0 : forall p i, isptr p -> 0 <= i <= 2 ^ 30 ->
  force_val (sem_sub_pp tschar (offset_val i p) p) = Vlong (Int64.repr i).
Proof.
intros p i Hp Hi. replace p with (offset_val 0 p) at 2 by (apply isptr_offset_val_zero; auto).
rewrite epi_sub_pp by (auto; lia). f_equal. f_equal. lia.
Qed.

(* the caller's buffers: their ends from buf_ok, their inside from the cells *)
Lemma epi_wvp_buf : forall (W: list ptr_witness) sh n (c: list val) p (R: mpred) x,
  buf_ok W sh n p -> readable_share sh -> 0 <= x <= n ->
  (pws_pred W * data_at sh (tarray tuchar n) c p * R |-- weak_valid_pointer (offset_val x p))%logic.
Proof.
intros W sh n c p R x Hb Hr Hx.
apply sepcon_weak_valid_pointer1.
assert_PROP (isptr p) as Pp by (saturate_local; entailer!).
destruct (Z.eq_dec x n) as [->|Hxn].
- sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
  rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left2. auto.
- destruct (Z.eq_dec x 0) as [->|Hx0].
  + sep_apply (data_at_data_at_ sh (tarray tuchar n) c p).
    rewrite sepcon_comm. eapply derives_trans; [apply Hb|]. apply andp_left1. rewrite isptr_offset_val_zero by auto. auto.
  + apply sepcon_weak_valid_pointer2.
    eapply derives_trans; [apply data_at_memory_block|].
    simpl sizeof. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
    eapply derives_trans; [apply (memory_block_valid_pointer sh n p x); [lia | apply readable_nonidentity; auto]|].
    apply valid_pointer_weak.
Qed.

Local Transparent denote_tc_test_eq.
Lemma epi_tc_test_eq : forall (P: mpred) p i j, isptr p ->
  (P |-- weak_valid_pointer (offset_val i p)) -> (P |-- weak_valid_pointer (offset_val j p)) ->
  P |-- denote_tc_test_eq (offset_val i p) (offset_val j p).
Proof.
intros P p i j Hp Hi Hj. destruct p; try contradiction.
unfold denote_tc_test_eq, offset_val in *. simpl. unfold test_eq_ptrs.
unfold sameblock. destruct (peq b b); [|congruence]. simpl.
apply andp_right; auto.
Qed.
Global Opaque denote_tc_test_eq.

Lemma epi_cmp_eq : forall p i j, isptr p -> 0 <= i <= 2 ^ 30 -> 0 <= j <= 2 ^ 30 ->
  force_val (sem_cmp_pp Ceq (offset_val i p) (offset_val j p)) = Val.of_bool (i =? j).
Proof.
intros p i j Hp Hi Hj. destruct p as [| | | | |b o]; try contradiction.
unfold sem_cmp_pp, offset_val; simpl.
unfold Val.cmplu_bool; simpl.
destruct (eq_block b b) as [_|E]; [|congruence]. simpl.
unfold Ptrofs.eq. rewrite !(Ptrofs.add_commut o).
destruct (Z.eq_dec i j) as [->|Hne]; [rewrite zeq_true, Z.eqb_refl; reflexivity|].
rewrite (proj2 (Z.eqb_neq i j) Hne).
rewrite zeq_false; [reflexivity|].
intro E. apply Hne.
pose proof (Ptrofs.unsigned_range o).
rewrite !Ptrofs.add_unsigned in E.
rewrite (Ptrofs.unsigned_repr i), (Ptrofs.unsigned_repr j) in E by rep_lia.
rewrite !Ptrofs.unsigned_repr_eq in E.
set (u := Ptrofs.unsigned o) in *. set (M := Ptrofs.modulus) in *.
assert (HM: M = 2 ^ 64) by reflexivity. rewrite HM in *.
pose proof (Z.div_mod (i + u) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (i + u) (2 ^ 64) ltac:(lia)).
pose proof (Z.div_mod (j + u) (2 ^ 64) ltac:(lia)). pose proof (Z.mod_pos_bound (j + u) (2 ^ 64) ltac:(lia)).
lia.
Qed.

End CM_E3Vst_1.

Ltac epi_wvp W sh c p :=
  match goal with |- context [data_at sh (tarray tuchar ?n) c p] =>
    eapply derives_trans; [| apply (epi_wvp_buf W sh n c p TT); auto; lia]; cancel end.

Section CM_E3Vst_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Definition epi_L (a: dsa) (ipc: Z) : list localdef :=
  [lvar _op (tptr tschar) (a_vop a); gvars (a_gv a); temp _zds (a_d a); temp _output (a_outp a);
   temp _input (a_inp a); temp _istart (offset_val (a_ipos a) (a_ib a));
   temp _iend (offset_val (a_isz a) (a_ib a)); temp _ip (offset_val ipc (a_ib a));
   temp _ostart (offset_val (a_opos a) (a_ob a)); temp _oend (offset_val (a_osz a) (a_ob a))].

Definition epi_S DENT TABS (a: dsa) (k: cst3) (ipos' opc: Z) (oc1: list val) : list mpred :=
  [data_at Tsh (tptr tschar) (offset_val opc (a_ob a)) (a_vop a); pws_pred (a_W a); mem_mgr (a_gv a);
   zstd_globals (a_gv a); ctx_rep3 DENT TABS (a_gv a) (a_d a) k;
   dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a));
   set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a));
   data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong opc)) (a_outp a);
   data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong ipos')) (a_inp a);
   data_at (a_shob a) (tarray tuchar (a_osz a)) oc1 (a_ob a);
   data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a)].

Lemma epi_ctx_valid : forall DENT TABS (gv: globals) (p: val) (k: cst3),
  TABS_OK TABS -> ctx_rep3 DENT TABS gv p k |-- valid_pointer p.
Proof.
intros DENT TABS gv p k HT. unfold ctx_rep3, ctx_body3, fgroup3, tabs_rep. normalize.
assert (V: field_at_ Ews t_dctx (DOT _LLTptr) p |-- valid_pointer p)
  by (apply field_at_valid_ptr0; auto; reflexivity).
destruct (c3_tabs k) as [lxb|ox ts].
- unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
- sep_apply (HT gv p ox ts). unfold tables_uninit.
  apply (derives_trans _ (field_at_ Ews t_dctx (DOT _LLTptr) p * TT)); [cancel | ].
  apply sepcon_valid_pointer1. exact V.
Qed.

Lemma epi_DC : forall DENT TABS BR (gv: globals) (p: val) (k: cst3) (st: dctx_st),
  TABS_OK TABS -> base_rel3 st k -> (dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR3 gv st k) ->
  dc_bl st = None -> ex_on3 SR3 st k ->
  ctx_rep3 DENT TABS gv p k |-- DC3x DENT TABS SR3 BR gv p st && valid_pointer p.
Proof.
intros DENT TABS BR gv p k st HT Hb Hs Hbl Hx.
apply andp_right; [| apply epi_ctx_valid; auto].
unfold DC3x, DC3_of. Exists k. apply andp_right; [| apply derives_refl].
apply prop_right. split; [exact Hb|]. split; [intros E1 E2; left; exact (Hs E1 E2)|].
split; [intros ba H; congruence | exact Hx].
Qed.

(* the context as the epilogue sees it: the nine fields it reads or writes, and the rest (grouped, so that
   the rearrangements stay small) *)
Definition ff_rest (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma ff_split : forall p fs, frame_fields p fs =
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p * field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  ff_rest p fs.
Proof. intros. unfold frame_fields, ff_rest. apply pred_ext; cancel. Qed.

Definition fg_rest (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) : mpred :=
  let pr := c3_par k in
  cfg_fmt p (dp_fmt pr) * cfg_lit p * ff_rest p (c3_fs k) * tabs_rep TABS gv p (c3_tabs k) *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) (c3_sp k) p.

Lemma fg_split : forall DENT TABS gv p k,
  fgroup3 TABS gv p (c3_fs k) (c3_tabs k) (c3_par k) (c3_sp k) =
  !! (cold01 (c3_fs k) /\ par_ok (c3_par k)) &&
  (field_at Ews t_dctx (DOT _expected) (fs_expected (c3_fs k)) p *
   field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs k)) p * fg_rest DENT TABS gv p k).
Proof.
intros. unfold fgroup3, fg_rest. rewrite ff_split. f_equal. apply pred_ext; cancel.
Qed.

Definition sg_rest (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p *
  field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
  ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
  mgroup (sf_mem s) p (sf_given s).

Definition sg_props (s: sfields) : Prop :=
  0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\ 
  0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\ 
  (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
  (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s).

Definition sg_seven (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p.

Lemma sg_split : forall p s, sgroup p s =
  !! (sg_props s /\ Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed) &&
  (sg_seven p s * sg_rest p s).
Proof.
intros. unfold sgroup, sg_rest, sg_seven, sg_props.
f_equal; [f_equal; apply prop_ext; tauto | apply pred_ext; cancel].
Qed.

Definition epi_rest (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (k: cst3) : mpred :=
  !! (cold01 (c3_fs k) /\ par_ok (c3_par k) /\ sg_props (c3_s k)) &&
  (dctx_token p * dctx_pad p * fg_rest DENT TABS gv p k * cgroup3 p (c3_stable k) (dp_wmax (c3_par k)) *
   dgroup DENT gv p (c3_dict k) * sg_rest p (c3_s k) * hset_rep (sf_mem (c3_s k)) (c3_sp k) (c3_set k) (sf_held (c3_s k) - local_held (c3_dict k))).

Lemma ctx_rep_epi : forall DENT TABS (gv: globals) (p: val) (k: cst3),
  ctx_rep3 DENT TABS gv p k =
  (!! (Int.min_signed <= sf_stage (c3_s k) <= Int.max_signed /\ Int.min_signed <= sf_nfp (c3_s k) <= Int.max_signed) &&
   (field_at Ews t_dctx (DOT _expected) (fs_expected (c3_fs k)) p *
    field_at Ews t_dctx (DOT _stage) (fs_stage (c3_fs k)) p *
    sg_seven p (c3_s k) *
    epi_rest DENT TABS gv p k)).
Proof.
intros. unfold ctx_rep3, ctx_body3. rewrite (fg_split DENT TABS gv p k), sg_split. unfold epi_rest.
apply pred_ext; normalize; apply andp_right; try (apply prop_right; tauto); cancel.
Qed.

Lemma epi_rest_epi : forall DENT TABS gv p k stage nfp hst ev,
  epi_rest DENT TABS gv p (k_epi k stage nfp hst ev) = epi_rest DENT TABS gv p k.
Proof. reflexivity. Qed.

Definition epi_zg_rest (gv: globals) : mpred := (
  data_at Ews tint g_debuglevel_val (gv _g_debuglevel) *
  data_at Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
  data_at Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
  data_at Ers tulong zeroFilled_val (gv _zeroFilled) *
  data_at Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
  data_at Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
  data_at Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
  data_at Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
  data_at Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
  data_at Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
  data_at Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
  data_at Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
  data_at Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
  data_at Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
  data_at Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) LL_defaultDTable_val (gv _LL_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 33) OF_defaultDTable_val (gv _OF_defaultDTable) *
  data_at Ers (tarray (Tstruct ___gp_ZSTD_seqSymbol noattr) 65) ML_defaultDTable_val (gv _ML_defaultDTable) *
  data_at Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
  data_at Ers (tarray tint 8) dec64table_val (gv _dec64table) * eb_res gv)%logic.

Lemma epi_zg : forall gv,
  zstd_globals gv = (data_at Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) * epi_zg_rest gv)%logic.
Proof. intros. unfold zstd_globals, epi_zg_rest. apply pred_ext; cancel. Qed.

(* a return, as forward leaves it: fold the context, then the postcondition *)
Lemma epi_close_gen : forall DENT TABS BR (a: dsa) (k': cst3) (r ipos' opc: Z) (oc1: list val) (v: val) (L: mpred),
  TABS_OK TABS -> epi_ok a k' r ipos' opc oc1 -> v = Vlong (Int64.repr r) ->
  (L |-- ctx_rep3 DENT TABS (a_gv a) (a_d a) k' * data_at Tsh (tptr tschar) (offset_val opc (a_ob a)) (a_vop a) *
         pws_pred (a_W a) * mem_mgr (a_gv a) * zstd_globals (a_gv a) *
         dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
         set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a)) *
         data_at (a_sho a) t_outBuffer (a_obf a, (vlong (a_osz a), vlong opc)) (a_outp a) *
         data_at (a_shi a) t_inBuffer (a_ibf a, (vlong (a_isz a), vlong ipos')) (a_inp a) *
         data_at (a_shob a) (tarray tuchar (a_osz a)) oc1 (a_ob a) *
         data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a))%logic ->
  L |-- EX r0: Z, EX opos': Z, EX ipos0: Z, EX oc': list val, EX st': dctx_st,
    !! (0 <= r0 <= Int64.max_unsigned /\
        stream_post (a_st a) st' r0 (a_obf a) (a_osz a) (a_opos a) opos' (a_oc a) oc' (a_ibs a) (a_isz a)
          (a_ipos a) ipos0 /\
        stream_progress (a_st a) st' r0 (a_osz a) (a_opos a) opos' (a_isz a) (a_ipos a) ipos0 (a_ibs a) /\
        stream_untouched (a_st a) r0 (a_osz a) opos' (a_oc a) oc' /\
        stream_exact (a_st a) st' r0 (a_osz a) (a_opos a) opos' oc' (a_ibs a) (a_isz a) (a_ipos a) ipos0 /\
        v = Vlong (Int64.repr r0)) &&
    (pws_pred (a_W a) * (mem_mgr (a_gv a) * (zstd_globals (a_gv a) *
     ((DC3x DENT TABS SR3 BR (a_gv a) (a_d a) st' && valid_pointer (a_d a)) *
      (dict_res (DD3x DENT) (a_gv a) Ews (dc_dict (a_st a)) *
       (set_res (DD3x DENT) (a_gv a) Ews (dc_set (a_st a)) (dc_dict (a_st a)) *
      (data_at (a_sho a) t_outBuffer (a_obf a, (Vlong (Int64.repr (a_osz a)), Vlong (Int64.repr opos'))) (a_outp a) *
       (data_at (a_shi a) t_inBuffer (a_ibf a, (Vlong (Int64.repr (a_isz a)), Vlong (Int64.repr ipos0))) (a_inp a) *
        (data_at (a_shob a) (tarray tuchar (a_osz a)) oc' (a_ob a) *
         (data_at (a_shb a) (tarray tuchar (a_isz a)) (zbytes (a_ibs a)) (a_ib a) *
          data_at_ Tsh (tptr tschar) (a_vop a)))))))))))%logic.
Proof.
intros DENT TABS BR a k' r ipos' opc oc1 v L HT (Hr & st' & (Hpost & Hbase & Hsr & Hbl & Hprog & Hun) & Hex & Hon) Hv HL.
change (stream_progress (a_st a) st' r (a_osz a) (a_opos a) opc (a_isz a) (a_ipos a) ipos' (a_ibs a)) in Hprog.
eapply derives_trans; [exact HL|].
Exists r opc ipos' oc1 st'.
sep_apply (epi_DC DENT TABS BR (a_gv a) (a_d a) k' st' HT Hbase Hsr Hbl Hon).
sep_apply (data_at_data_at_ Tsh (tptr tschar) (offset_val opc (a_ob a)) (a_vop a)).
unfold vlong. entailer!.
Qed.

End CM_E3Vst_2.
