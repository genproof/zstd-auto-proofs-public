(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the state after fix F4's probe, and model facts
   of the frame's dictionary. *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3QV.
Require Import Zstd.proof.dec.v3.FS.frames.Multi3FD.
Local Open Scope logic.

Section CM_Multi3Pp_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* after the probe: the variable `ddict` is mf_probe .. qv ..; streamStage already zdss_init (F10); the tables
   uninitialised, litExtraBuffer holding lxb *)
Definition mf_pp (DENT: dent_pred) (TABS: tabs_pred) (gv: globals) (p: val) (W: list ptr_witness) (pr: dparams)
    (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val) (shk: share) (a: darg) (s: list Z)
    (cap: Z) (shd: share) (dst: val) (shs: share) (src v_src v_srcSize v_zfh: val)
    (off u: Z) (oc: list val) (fs1: fstate) (m: Z) (qv: val) (dcur: dfields) (am: option cmem) (hb: Z)
    (lxb: list Z) : environ -> mpred :=
  PROP () LOCAL (temp _moreThan1Frame (Vint (Int.repr m)); temp _dststart dst;
    lvar _zfh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
    lvar _srcSize tulong v_srcSize; lvar _src (tptr tvoid) v_src; gvars gv; temp _dctx p;
    temp _dst (offset_val u dst); temp _dstCapacity (Vlong (Int64.repr (cap - u)));
    temp _dict (darg_dictv a); temp _dictSize (Vlong (Int64.repr (darg_dsize a)));
    temp _ddict (mf_probe pr sp a l tbl qv (sublist off (Zlength s) s)))
  SEP (data_at_ Tsh (Tstruct ___gp_ZSTD_FrameHeader noattr) v_zfh;
    data_at Tsh tulong (Vlong (Int64.repr (Zlength s - off))) v_srcSize;
    data_at Tsh (tptr tvoid) (offset_val off src) v_src; pws_pred W; zstd_globals gv;
    field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
    cfg_lit p; frame_fields p fs1; tabs_rep TABS gv p (TUninit lxb);
    field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p;
    field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p;
    field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p;
    field_at Ews t_dctx (DOT _ddictSet) sp p;
    msel_res DENT gv p pr sp dcur l tbl shk a am hb; darg_res3 DENT gv pr sp d a;
    data_at shd (tarray tuchar cap) oc dst;
    data_at shs (tarray tuchar (Zlength s)) (zbytes s) src;
    field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr 0)) p).

(* msel_ok's entry fact *)
Lemma msel_entry: forall W d l a shk shd cap dst, msel_ok W d l a shk shd cap dst ->
  forall x buf sh dd, a = DA_ddict x buf sh -> In (dx_q x, dd) l -> x = dd_x (dx_q x) dd.
Proof. intros. destruct H as (_ & _ & _ & H & _). destruct (H x buf sh dd H0 H1); auto. Qed.

(* the model's dictionary of a frame: mf_frame_dict with or without the selection *)
Lemma mf_frame_dict2: forall pr sp a l tbl shk qv sfr dm W d shd cap dst,
  (sel_on pr sp = true -> hs_inv l tbl) -> (sel_on pr sp = true -> msel_ok W d l a shk shd cap dst) ->
  darg_model (mf_dict a l shk (mf_probe pr sp a l tbl qv sfr)) = Some dm ->
  darg_model (mf_dict a l shk qv) <> None ->
  frame_dict (dp_fmt pr =? 1) (mf_sel pr sp a l tbl) (darg_model (mf_dict a l shk qv)) sfr = Some dm.
Proof.
  intros pr sp a l tbl shk qv sfr dm W d shd cap dst Hh Hm E N.
  destruct (sel_on pr sp) eqn:Hs.
  - apply mf_frame_dict; auto. intros. eapply msel_entry; eauto.
  - unfold mf_sel. rewrite Hs. cbn [andb].
    rewrite mf_probe_off in E by (rewrite Hs; reflexivity). rewrite E. apply frame_dict3_none.
Qed.

End CM_Multi3Pp_1.
