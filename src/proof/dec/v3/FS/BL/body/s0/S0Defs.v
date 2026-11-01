(* FS3-bl BODY stage 0: the pieces of case 0 of ZSTD_decompressContinue's switch and the states between
   them (the proof is split over several files: 60 s per file).  Every assertion takes the same arguments
   DENT TABS W gv p pr od ba fs ts hb shk shd ob osz opos oc shs src c v_bp pcs st. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s0.S0Delta.
Local Open Scope logic.

Section CM_S0Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* bl_cmd 0 = Ssequence (Ssequence s0_A (Ssequence s0_B1 (Ssequence s0_B2 (Ssequence s0_B3 s0_R)))) tail;
   s0_A = Ssequence (t'58 = format) (if (t'58 == 0) s0_THEN); s0_THEN = Ssequence (t'2 = readLE32) (if .. s0_SKIP) *)
Definition s0_full : statement :=
  ltac:(let s := eval cbv [bl_cmd select_switch select_switch_case] in (bl_cmd 0) in
        let s := eval simpl seq_of_labeled_statement in s in exact s).
Definition s0_A : statement :=
  ltac:(let s := eval unfold s0_full in s0_full in lazymatch s with Ssequence (Ssequence ?a _) _ => exact a end).
Definition s0_REST : statement :=
  ltac:(let s := eval unfold s0_full in s0_full in lazymatch s with Ssequence (Ssequence _ ?r) _ => exact r end).
Definition s0_THEN : statement :=
  ltac:(let s := eval unfold s0_A in s0_A in lazymatch s with Ssequence _ (Sifthenelse _ ?t Sskip) => exact t end).
Definition s0_SKIP : statement :=
  ltac:(let s := eval unfold s0_THEN in s0_THEN in lazymatch s with Ssequence _ (Sifthenelse _ ?t Sskip) => exact t end).
Definition s0_HB : statement :=
  ltac:(let s := eval unfold s0_REST in s0_REST in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence ?b3 ?r)) => exact (Ssequence b3 r) end).

Definition s0_D (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : tycontext :=
  func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil.

Section Asserts.
Variables (DENT: dent_pred) (TABS: tabs_pred) (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams)
  (od: option bldict) (ba: blabs) (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z)
  (oc: list val) (shs: share) (src: val) (c: list Z) (v_bp: val) (pcs st: Z).

Definition s0_RA : ret_assert := switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c).

Definition s0_L0 : list localdef :=
  [temp _t'20 (Vint (Int.repr st)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
   temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
   temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c)))].

(* the state after t'58 = format: before the test, in its then-branch, and after it *)
Definition s0_preA : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'58 (Vint (Int.repr (dp_fmt pr))); temp _t'20 (Vint (Int.repr st));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _headerSize) (fs_headerSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       s0_fc_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W; zstd_globals gv;
       TABS gv p (bd_oxo od) ts; field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od);
       bd_res shk od; data_at shd (tarray tuchar osz) oc ob;
       data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

Definition s0_mid : environ -> mpred :=
  PROP (dp_fmt pr = 0 -> is_skippable_magic (le_field c 0 4) = false)
  LOCAL (temp _t'58 (Vint (Int.repr (dp_fmt pr))); temp _t'20 (Vint (Int.repr st));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _headerSize) (fs_headerSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       s0_fc_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W; zstd_globals gv;
       TABS gv p (bd_oxo od) ts; field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od);
       bd_res shk od; data_at shd (tarray tuchar osz) oc ob;
       data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* the skippable branch, after t'2 = MEM_readLE32(src) *)
Definition s0_preS : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'2 (Vint (Int.repr (le_field c 0 4))); temp _t'58 (Vint (Int.repr (dp_fmt pr)));
         temp _t'20 (Vint (Int.repr st));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at shs (tarray tuchar (Zlength c)) (zbytes c) src;
       field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _headerSize) (fs_headerSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       s0_fc_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W; zstd_globals gv;
       TABS gv p (bd_oxo od) ts; field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od);
       bd_res shk od; data_at shd (tarray tuchar osz) oc ob).

(* the header branch, after the ZSTD_isError test of headerSize hs *)
Definition s0_preH (hs: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'4 (Vint (Int.repr 0)); temp _t'56 (Vlong (Int64.repr hs)); temp _t'3 (Vlong (Int64.repr hs));
         temp _t'57 (Vint (Int.repr (dp_fmt pr))); temp _t'58 (Vint (Int.repr (dp_fmt pr)));
         temp _t'20 (Vint (Int.repr st));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (zstd_globals gv; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src;
       field_at Ews t_dctx (DOT _format) (Vint (Int.repr (dp_fmt pr))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _headerSize) (Vlong (Int64.repr hs)) p;
       s0_fc_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W;
       TABS gv p (bd_oxo od) ts; field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od);
       bd_res shk od; data_at shd (tarray tuchar osz) oc ob).

End Asserts.

(* the facts every piece uses *)
Definition s0_ok (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate) (ts: tstate) (hb: list val)
    (v: blv) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (c: list Z) : Prop :=
  par_ok pr /\ bl_hist_ok ba ob opos oc /\ 0 <= opos <= osz /\ Zlength oc = osz /\
  bl_cinv (dmode_of pr) od osz0 ba fs hb v /\ bl_mrel (dmode_of pr) ba fs ts v /\ bd_model_ok (ba_dict ba) od /\
  bv_stage v = BHdrPrefix /\ Zlength c = starting_len (md_magicless (dmode_of pr)) /\ bytes_ok c /\
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) /\
  readable_share shs /\ Zlength hb = 18 /\ ba_expect ba <> 0 /\ fp_ok (fs_fParams fs).

(* stage 0 does not write fParams *)
Lemma s0_fs'_fp_ok mg fs ob osz opos pcs c : fp_ok (fs_fParams fs) -> fp_ok (fs_fParams (s0_fs' mg fs ob osz opos pcs c)).
Proof. intros H. unfold s0_fs', s0_fs. cbn [fs_fParams fsu_stage fsu_expected fsu_headerSize]. rewrite bl_fs1_fParams. exact H. Qed.

End CM_S0Defs_1.
