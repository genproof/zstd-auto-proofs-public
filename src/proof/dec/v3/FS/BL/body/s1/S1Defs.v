(* FS3-bl BODY stage 1: the parts of case ZSTDds_decodeFrameHeader (memcpy; the FORWARD_IF_ERROR loop
   around ZSTD_decodeFrameHeader; the stores and the return), and the states between them. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s1.S1Loops.
Local Open Scope logic.

Section CM_S1Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition s1_cmd : statement :=
  ltac:(let s := eval cbv [bl_cmd select_switch select_switch_case] in (bl_cmd 1) in
        let s := eval simpl seq_of_labeled_statement in s in exact s).

Definition s1_memcpy : statement :=
  ltac:(let s := eval cbv [s1_cmd] in s1_cmd in
        lazymatch s with Ssequence (Ssequence ?a (Ssequence (Sloop ?b Sbreak) ?r)) ?m => exact a end).
Definition s1_loop : statement :=
  ltac:(let s := eval cbv [s1_cmd] in s1_cmd in
        lazymatch s with Ssequence (Ssequence ?a (Ssequence (Sloop ?b Sbreak) ?r)) ?m => exact (Sloop b Sbreak) end).
Definition s1_rest : statement :=
  ltac:(let s := eval cbv [s1_cmd] in s1_cmd in
        lazymatch s with Ssequence (Ssequence ?a (Ssequence (Sloop ?b Sbreak) ?r)) ?m => exact r end).
Definition s1_more : statement :=
  ltac:(let s := eval cbv [s1_cmd] in s1_cmd in
        lazymatch s with Ssequence (Ssequence ?a (Ssequence (Sloop ?b Sbreak) ?r)) ?m => exact m end).

Lemma s1_cmd_eq : bl_cmd 1 = Ssequence (Ssequence s1_memcpy (Ssequence s1_loop s1_rest)) s1_more.
Proof. reflexivity. Qed.

(* copied from s2/BLS2Defs (bl2_delta): the type context of ZSTD_decompressContinue, computed once (what simplify_func_tycontext computes) *)
Definition s1_DS (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : Maps.PTree.t funspec :=
  ltac:(let d := make_ground_PTree constr:(make_tycontext_s (FS3_G DENT TABS SR BR')) in exact d).

Definition s1_D (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : tycontext.
Proof.
  pose (D1 := func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil).
  unfold func_tycontext, make_tycontext in D1.
  change (make_tycontext_s (FS3_G DENT TABS SR BR')) with (s1_DS DENT TABS SR BR') in D1.
  cbv beta iota zeta delta - [s1_DS] in D1.
  exact D1.
Defined.

Lemma s1_D_eq DENT TABS SR BR' :
  func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil = s1_D DENT TABS SR BR'.
Proof. reflexivity. Qed.

End CM_S1Defs_1.

(* replaces simplify_func_tycontext (the context computed above; no function calls are made with it) *)
Ltac s1_delta :=
  match goal with |- semax (func_tycontext _ _ (FS3_G ?a ?b ?c ?d) _) _ _ _ =>
    rewrite (s1_D_eq a b c d);
    let DS := fresh "Delta_specs" in pose (DS := @abbreviate (Maps.PTree.t funspec) (s1_DS a b c d));
    let D := eval cbv [s1_D] in (s1_D a b c d) in
    let D1 := fresh "D1" in pose (D1 := D);
    let Delta := fresh "Delta" in pose (Delta := @abbreviate tycontext D1);
    change (s1_D a b c d) with Delta;
    change (s1_DS a b c d) with DS in D1; subst D1
  end.

Section CM_S1Defs_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

Section S1.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the state before the FORWARD_IF_ERROR loop: the header bytes in headerBuffer *)
Definition s1_pre_loop (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (ts: tstate) (hb': list val) (shk shd: share) (ob: val) (osz: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p)
  SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W; zstd_globals gv;
       fcore3 p fs1 pr nullval; TABS gv p (bd_oxo od) ts;
       data_at Ews (tarray tuchar 18) hb' (field_address t_dctx (DOT _headerBuffer) p);
       dent_of DENT gv (bd_oxo od); bd_res shk od; data_at shd (tarray tuchar osz) oc ob;
       data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* after the loop: ZSTD_decodeFrameHeader succeeded *)
Definition s1_Q (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (pcs1: Z) (s: list Z) (ts: tstate) (hb': list val) (shk shd: share) (ob: val) (osz: Z) (oc: list val)
    (shs: share) (src: val) (c: list Z) (v_bp: val) : environ -> mpred :=
  EX r: Z, EX fs': fstate, EX d': dfields,
  PROP (dfh_post3 (dmode_of pr) false df_none nil nil fs1 (bd_idz od) pcs1 s r fs' d'; is_error_code r = false)
  LOCAL (lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv; temp _dctx p)
  SEP (data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp; pws_pred W; zstd_globals gv;
       fcore3 p fs' pr nullval; TABS gv p (bd_oxo od) ts;
       data_at Ews (tarray tuchar 18) hb' (field_address t_dctx (DOT _headerBuffer) p);
       dent_of DENT gv (bd_oxo od); bd_res shk od; data_at shd (tarray tuchar osz) oc ob;
       data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

End S1.

(* the hypotheses of bl_case_spec at stage 1, for the parts *)
Definition s1_hyps (pr: dparams) (W: list ptr_witness) (od: option bldict) (osz0: Z) (ba: blabs) (fs: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v: blv) (pcs: Z) : Prop :=
  par_ok pr /\ bl_pre_ok W od osz0 ba shk shd ob osz opos oc shs src c /\
  bl_cinv (dmode_of pr) od osz0 ba fs hb v /\ bl_mrel (dmode_of pr) ba fs ts v /\ bd_model_ok (ba_dict ba) od /\
  bv_stage v = BHdrRest /\ fs_processedCSize fs = vlong pcs /\ 0 <= pcs <= Int64.max_unsigned /\
  bl_size_ok v (ba_expect ba) (Zlength c) /\
  bl_lay od osz (bl_moved ba ob opos) (continuity fs (offset_val opos ob) (osz - opos)) /\
  fp_ok (fs_fParams fs).

End CM_S1Defs_2.
