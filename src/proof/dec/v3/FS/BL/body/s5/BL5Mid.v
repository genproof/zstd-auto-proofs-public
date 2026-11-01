(* FS3-bl BODY, stage 5: case 5 cut after `if (validateChecksum) {..}`: the statements and the state
   there (bl5_mid).  BLStage5 proves the if, BL5Tail the rest (ZSTD_DCtx_trace_end, expected/stage, return 0). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s5.BL5Fold.
Local Open Scope logic.

Section CM_BL5Mid_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bl5_s5 : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with context [LScons (Some 5) ?x _] => exact x end).
Definition bl5_ls6 : labeled_statements :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with context [LScons (Some 5) _ ?r] => exact r end).
Definition bl5_if : statement :=
  ltac:(let s := eval cbv [bl5_s5] in bl5_s5 in lazymatch s with Ssequence ?a _ => exact a end).
Definition bl5_tl : statement :=
  ltac:(let s := eval cbv [bl5_s5] in bl5_s5 in lazymatch s with Ssequence _ ?b => exact b end).

Lemma bl5_cmd_eq : bl_cmd 5 = Ssequence (Ssequence bl5_if bl5_tl) (seq_of_labeled_statement bl5_ls6).
Proof. reflexivity. Qed.

Section Mid.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition bl5_mid (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) (v: blv) (pcs: Z) : environ -> mpred :=
  PROP (bl_val (md_ignore (dmode_of pr)) (bv_h v) = true ->
        exists l, fs_xxh fs = Some l /\ le_field c 0 4 = xxh64 l 0 mod 2 ^ 32)
  LOCAL (temp _t'23 (Vint (Int.repr (if bl_val (md_ignore (dmode_of pr)) (bv_h v) then 1 else 0)));
         temp _t'20 (Vint (Int.repr 5)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (field_at Ews t_dctx (DOT _validateChecksum)
         (Vint (Int.repr (if bl_val (md_ignore (dmode_of pr)) (bv_h v) then 1 else 0))) p;
       xxh_field p (fs_xxh (bl_fs1 fs ob osz opos pcs (Zlength c)));
       field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _expected) (fs_expected (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       field_at Ews t_dctx (DOT _stage) (fs_stage (bl_fs1 fs ob osz opos pcs (Zlength c))) p;
       bl5_rest p (bl_fs1 fs ob osz opos pcs (Zlength c)) pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

End Mid.

End CM_BL5Mid_1.
