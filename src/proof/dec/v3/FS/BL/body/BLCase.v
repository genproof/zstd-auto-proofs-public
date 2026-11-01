(* FS3-bl BODY: the shared statements of the parts of ZSTD_decompressContinue's body proof (BLBody.v).
   The parts prove the lemmas stated with these definitions (BLCont: the history pointers
   after ZSTD_checkContinuity; BLStage*: one case of the switch on dctx->stage each).

   - bl_pre_ok: the PRE facts of ZSTD_decompressContinue_ispec besides BRc;
   - bl_size_ok: what the srcSize check (ZSTD_nextSrcSizeToDecompressWithInputSize) let through;
   - bl_moved ba ob opos: ba with the output begun at the call (bl_start), as checkContinuity leaves the context;
   - bl_fs1 fs ob osz opos pcs n: the frame fields at the switch (checkContinuity, processedCSize += n);
   - bl_case_pre: the state at the switch (the ispec's PRE with fs1, the switch's temporary _t'20);
   - bl_post / bl_R: the ispec's POST and the function's return assertion;
   - bl_cmd k: the statement of the switch from the case label k on (what VST's forward_switch' leaves). *)
Require Export Zstd.proof.dec.v3.FS.BL.BLDefs.
Local Open Scope logic.

Section CM_BLCase_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition bl_moved (ba: blabs) (ob: val) (opos: Z) : blabs :=
  {| ba_dict := ba_dict ba; ba_st := ba_st ba; ba_expect := ba_expect ba;
     ba_out := Some (pair (pair ob (bl_start ba opos)) opos) |}.

(* the dictionary's bytes as a pointer witness (pw_pred (bd_pw sh od) = bd_res sh od) *)
Definition bd_pw (sh: share) (od: option bldict) : ptr_witness :=
  match od with
  | None => pw_none
  | Some d => if eq_dec (bd_eb d) nullval then pw_none else pw_bytes sh (Zlength (bd_b d)) (zbytes (bd_b d)) (bd_eb d)
  end.

Lemma bd_pw_res sh od : pw_pred (bd_pw sh od) = bd_res sh od.
Proof. destruct od as [d|]; [|reflexivity]. simpl. unfold bytes_at.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; first [reflexivity | congruence].
Qed.

Definition bl_pre_ok (W: list ptr_witness) (od: option bldict) (osz0: Z) (ba: blabs) (shk shd: share) (ob: val)
    (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z) : Prop :=
  ba_expect ba <> 0 /\ bl_hist_ok ba ob opos oc /\ (ba_out ba <> None -> osz = osz0) /\
  buf_ok W shd osz ob /\ buf_ok W shs (Zlength c) src /\ bd_buf_ok W shk od shd (osz - opos) (offset_val opos ob) /\
  writable_share shd /\ readable_share shs /\ readable_share shk /\
  0 <= opos <= osz /\ osz <= 2 ^ 63 - 1 /\ Zlength oc = osz /\ Zlength c <= 2 ^ 30 /\ bytes_ok c.

(* the srcSize check: n = expected, or within a raw block's remaining size *)
Definition bl_size_ok (v: blv) (e n: Z) : Prop :=
  match bv_stage v with
  | BBlk | BLastBlk => if bv_bt v =? 0 then 1 <= n <= e else n = e
  | _ => n = e
  end.

Definition bl_fs1 (fs: fstate) (ob: val) (osz opos pcs n: Z) : fstate :=
  fsu_processedCSize (continuity fs (offset_val opos ob) (osz - opos)) (vlong (pcs + n)).

Lemma bl_fs1_fParams fs ob osz opos pcs n : fs_fParams (bl_fs1 fs ob osz opos pcs n) = fs_fParams fs.
Proof.
  unfold bl_fs1, continuity; destruct (cont_moves _ _ _); reflexivity.
Qed.

Section Case.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

Definition bl_case_pre (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) (st: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'20 (Vint (Int.repr st)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; fcore3 p fs1 pr nullval; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

Definition bl_post (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z)
    : environ -> mpred :=
   (EX r: Z, EX oc': list val, EX ba': blabs, EX fs': fstate, EX t': tabs3, EX hb': list val,
    PROP (0 <= r <= Int64.max_unsigned; Zlength oc' = osz; sublist 0 opos oc' = sublist 0 opos oc;
          cold01 fs'; Zlength hb' = 18; fp_ok (fs_fParams fs');
          (is_error_code r = false ->
             r <= osz - opos /\ cells_bytes (sublist opos (opos + r) oc') /\ ba_dict ba' = ba_dict ba /\
             ba_out ba' = Some (pair (pair ob (bl_start ba opos)) (opos + r)%Z) /\
             bl_hist_ok ba' ob (opos + r) oc' /\
             (forall b', ba_st ba' = Some b' -> ba_expect ba' = bs_expect b') /\
             exists ts', t' = TInit (bd_oxo od) ts' /\ BRc (dmode_of pr) od osz ba' fs' ts' hb');
          bl_claim_nc (dmode_of pr) ba ba' c r opos osz oc')
    RETURN (Vlong (Int64.repr r))
    SEP (pws_pred W; zstd_globals gv; fcore3 p fs' pr nullval; tabs_rep TABS gv p t';
         field_at Ews t_dctx (DOT _headerBuffer) hb' p; dent_of DENT gv (bd_oxo od); bd_res shk od;
         data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src))%assert.

Definition bl_R (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (ba: blabs)
    (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val) (c: list Z) : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tulong (bl_post W gv p pr od ba shk shd ob osz opos oc shs src c))
    (stackframe_of f_ZSTD_decompressContinue).

End Case.

(* the switch on dctx->stage and the statement of each of its cases *)
Definition bl_switch : labeled_statements :=
  ltac:(let b := eval cbv [f_ZSTD_decompressContinue fn_body] in (fn_body f_ZSTD_decompressContinue) in
        lazymatch b with context [Sswitch (Etempvar _t'20 tint) ?ls] => exact ls end).

Definition bl_cmd (k: Z) : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        exact (seq_of_labeled_statement (select_switch k s))).

(* the obligation of one case of the switch: from the state at the switch (stage st, the stage P of the frame), the
   statement bl_cmd k (the cases from label k on) establishes the ispec's POST *)
Definition bl_case_spec (P: blv -> Prop) (k: Z) : Prop :=
  forall (Espec: OracleKind) (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel),
  DENT_OK DENT -> TABS_OK TABS ->
  forall (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (osz0: Z) (ba: blabs)
    (fs: fstate) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share)
    (src: val) (c: list Z) (v_bp: val) (v: blv) (pcs st: Z),
  par_ok pr ->
  bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c ->
  bl_cinv (dmode_of pr) od osz0 ba fs hb v -> bl_mrel (dmode_of pr) ba fs ts v -> bd_model_ok (ba_dict ba) od ->
  fp_ok (fs_fParams fs) ->
  P v -> bl_stz (bv_stage v) = st ->
  fs_processedCSize fs = vlong pcs -> 0 <= pcs <= Int64.max_unsigned ->
  bl_size_ok v (ba_expect ba) (Zlength c) ->
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) ->
  semax (func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil)
    (bl_case_pre DENT TABS W gv p pr od (bl_fs1 fs ob osz opos pcs (Zlength c)) ts hb shk shd ob osz opos oc shs src
       c v_bp st)
    (bl_cmd k)
    (switch_ret_assert (bl_R DENT TABS W gv p pr od ba shk shd ob osz opos oc shs src c)).

End CM_BLCase_1.
