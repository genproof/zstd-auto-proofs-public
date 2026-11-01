(* FS3-bl BODY stage 2: the pieces of the block-header case and the states between them. *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s2.BLS2Facts.
Local Open Scope logic.

Section CM_BLS2Defs_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* case 2 of the switch: bl2_a (getcBlockSize), bl2_b (its error return), bl2_x (the rest); bl2_more the cases after *)
Definition bl2_body : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with LScons (Some 0) _ (LScons (Some 1) _ (LScons (Some 2) ?b _)) => exact b end).
Definition bl2_more : statement :=
  ltac:(let s := eval cbv [bl_switch] in bl_switch in
        lazymatch s with LScons (Some 0) _ (LScons (Some 1) _ (LScons (Some 2) _ ?r)) =>
          let r' := eval cbn [seq_of_labeled_statement] in (seq_of_labeled_statement r) in exact r' end).
Definition bl2_a : statement :=
  ltac:(let s := eval cbv [bl2_body] in bl2_body in lazymatch s with Ssequence ?a (Ssequence ?b ?x) => exact a end).
Definition bl2_b : statement :=
  ltac:(let s := eval cbv [bl2_body] in bl2_body in lazymatch s with Ssequence ?a (Ssequence ?b ?x) => exact b end).
Definition bl2_x : statement :=
  ltac:(let s := eval cbv [bl2_body] in bl2_body in lazymatch s with Ssequence ?a (Ssequence ?b ?x) => exact x end).

Lemma bh_fs_fParams fs1 h cs bp : fs_fParams (bh_fs fs1 h cs bp) = fs_fParams fs1.
Proof. reflexivity. Qed.

Lemma bl2_cmd_eq : bl_cmd 2 = Ssequence (Ssequence bl2_a (Ssequence bl2_b bl2_x)) bl2_more.
Proof. reflexivity. Qed.

(* bl2_x = the blockSizeMax check (bl2_loop); the stores and the returns (bl2_y) *)
Definition bl2_loop : statement :=
  ltac:(let s := eval cbv [bl2_x] in bl2_x in lazymatch s with Ssequence ?l _ => exact l end).
Definition bl2_y : statement :=
  ltac:(let s := eval cbv [bl2_x] in bl2_x in lazymatch s with Ssequence _ ?y => exact y end).
Lemma bl2_x_eq : bl2_x = Ssequence bl2_loop bl2_y.
Proof. reflexivity. Qed.

(* bl2_y = the stores of expected, bType, rleSize; then bl2_w (the test of cBlockSize and the returns) *)
Definition bl2_w : statement :=
  ltac:(let s := eval cbv [bl2_y] in bl2_y in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ ?w)) => exact w end).

(* the zero-size block (after the stores and the test of cBlockSize) *)
Definition bl2_z : statement :=
  ltac:(let s := eval cbv [bl2_x] in bl2_x in
        lazymatch s with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?z)))) => exact z end).

Section States.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* after ZSTD_getcBlockSize succeeded with cs *)
Definition bl2_mid (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val) (shs: share) (src: val)
    (c: list Z) (v_bp: val) (cs: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _cBlockSize (Vlong (Int64.repr cs)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
         gvars gv; temp _dctx p; temp _dst (offset_val opos ob);
         temp _dstCapacity (Vlong (Int64.repr (osz - opos))); temp _src src;
         temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at Tsh t_bp (bp_val (block_props_of c)) v_bp;
       pws_pred W; zstd_globals gv; fcore3 p fs1 pr nullval; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* after the stores of expected, bType, rleSize (a block of cs bytes) *)
Definition bl2_mid3 (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (h: frame_header) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val)
    (shs: share) (src: val) (c: list Z) (v_bp: val) (cs: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _cBlockSize (Vlong (Int64.repr cs)); lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
         gvars gv; temp _dctx p; temp _dst (offset_val opos ob);
         temp _dstCapacity (Vlong (Int64.repr (osz - opos))); temp _src src;
         temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at Tsh t_bp (bp_val (block_props_of c)) v_bp;
       field_at Ews t_dctx (DOT _stage) (fs_stage fs1) p;
       field_at Ews t_dctx (DOT _bType) (Vint (Int.repr (bp_type (block_props_of c)))) p;
       field_at Ews t_dctx (DOT _expected) (vlong cs) p;
       field_at Ews t_dctx (DOT _rleSize) (vlong (bp_origSize (block_props_of c))) p;
       field_at Ews t_dctx (DOT _fParams) (fh_val h) p; fc2_rest p fs1 pr;
       pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* a block of size 0: expected, bType, rleSize stored *)
Definition bl2_mid2 (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (fs1: fstate)
    (h: frame_header) (ts: tstate) (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (oc: list val)
    (shs: share) (src: val) (c: list Z) (v_bp: val) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp;
         gvars gv; temp _dctx p; temp _dst (offset_val opos ob);
         temp _dstCapacity (Vlong (Int64.repr (osz - opos))); temp _src src;
         temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (data_at Tsh t_bp (bp_val (block_props_of c)) v_bp;
       field_at Ews t_dctx (DOT _stage) (fs_stage fs1) p;
       field_at Ews t_dctx (DOT _bType) (Vint (Int.repr (bp_type (block_props_of c)))) p;
       field_at Ews t_dctx (DOT _expected) (vlong 0) p;
       field_at Ews t_dctx (DOT _rleSize) (vlong (bp_origSize (block_props_of c))) p;
       field_at Ews t_dctx (DOT _fParams) (fh_val h) p; fc2_rest p fs1 pr;
       pws_pred W; zstd_globals gv; TABS gv p (bd_oxo od) ts;
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).
End States.

(* the type context of ZSTD_decompressContinue, computed once (what simplify_func_tycontext computes) *)
Definition bl2_DS (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : Maps.PTree.t funspec :=
  ltac:(let d := make_ground_PTree constr:(make_tycontext_s (FS3_G DENT TABS SR BR')) in exact d).

Definition bl2_D (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3) (BR': blrel) : tycontext.
Proof.
  pose (D1 := func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil).
  unfold func_tycontext, make_tycontext in D1.
  change (make_tycontext_s (FS3_G DENT TABS SR BR')) with (bl2_DS DENT TABS SR BR') in D1.
  cbv beta iota zeta delta - [bl2_DS] in D1.
  exact D1.
Defined.

Lemma bl2_D_eq DENT TABS SR BR' :
  func_tycontext f_ZSTD_decompressContinue Vprog (FS3_G DENT TABS SR BR') nil = bl2_D DENT TABS SR BR'.
Proof. reflexivity. Qed.

End CM_BLS2Defs_1.

(* replaces simplify_func_tycontext (the context computed above; no function calls are made with it) *)
Ltac bl2_delta :=
  match goal with |- semax (func_tycontext _ _ (FS3_G ?a ?b ?c ?d) _) _ _ _ =>
    rewrite (bl2_D_eq a b c d);
    let DS := fresh "Delta_specs" in pose (DS := @abbreviate (Maps.PTree.t funspec) (bl2_DS a b c d));
    let D := eval cbv [bl2_D] in (bl2_D a b c d) in
    let D1 := fresh "D1" in pose (D1 := D);
    let Delta := fresh "Delta" in pose (Delta := @abbreviate tycontext D1);
    change (bl2_D a b c d) with Delta;
    change (bl2_DS a b c d) with DS in D1; subst D1
  end.

