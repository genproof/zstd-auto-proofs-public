(* FS3-bl BODY, stages 3/4, the tail (part of TS4.v t34_s4_ok): helpers of the last block (stage 4):
   the frame group split into the five fields stage 4 touches (ts4_split, ts4_fold), the content size test
   (ts4_t15, from v2 body_stream_continue.v), the state after `t'24 = stage` (ts4_mid) and the statements of the
   then-branch of `if (stage == 4)`: ts4_dw (DEBUGLOG), ts4_loop (the content size check), ts4_ck (checksumFlag). *)
Require Export Zstd.proof.dec.v3.FS.BL.body.s34.tail.TDefs.
Local Open Scope logic.

Section CM_TS4Sep_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without the five fields stage 4 touches *)
Definition ts4_rest (p: val) (fs: fstate) (pr: dparams) : mpred :=
  cfg_fmt p (dp_fmt pr) * cfg_lit p *
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) nullval p.

Lemma ts4_split p fs pr :
  fcore3 p fs pr nullval |--
  !! par_ok pr &&
  (field_at Ews t_dctx (DOT _stage) (fs_stage fs) p * field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
   field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
   field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
   field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p * ts4_rest p fs pr).
Proof. unfold fcore3, frame_fields, ts4_rest. Intros. apply andp_right; [apply prop_right; auto | cancel]. Qed.

Lemma ts4_fold p fs pr stg e vf vd vq :
  par_ok pr -> vf = fs_fParams fs -> vd = fs_decodedSize fs -> vq = fs_processedCSize fs ->
  field_at Ews t_dctx (DOT _stage) (Vint (Int.repr (bl_stz stg))) p *
  field_at Ews t_dctx (DOT _expected) (vlong e) p *
  field_at Ews t_dctx (DOT _fParams) vf p * field_at Ews t_dctx (DOT _decodedSize) vd p *
  field_at Ews t_dctx (DOT _processedCSize) vq p * ts4_rest p fs pr |-- fcore3 p (t34_fsE fs stg e) pr nullval.
Proof.
  intros Hp -> -> ->. unfold fcore3, frame_fields, ts4_rest, t34_fsE. cbn.
  apply andp_right; [apply prop_right; auto | cancel].
Qed.

(* the content size test (v2 body_stream_continue.v) *)
Definition ts4_t15 (f a: Z) : Z := if f =? 2 ^ 64 - 1 then 0 else if a mod 2 ^ 64 =? f then 0 else 1.

Lemma ts4_fthen a f : 0 <= f < 2 ^ 64 -> Int64.repr f <> Int64.repr (- (1)) ->
  Vint (Int.repr (ts4_t15 f a)) = bool2val (Int64.cmpu Cne (Int64.repr a) (Int64.repr f)).
Proof.
  intros Hf Hn. unfold ts4_t15.
  assert (Hne: f <> 2 ^ 64 - 1).
  { intros ->. apply Hn. apply Int64.eqm_samerepr. exists 1. reflexivity. }
  rewrite (proj2 (Z.eqb_neq _ _) Hne). unfold Int64.cmpu, Int64.eq. rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64). rewrite (Z.mod_small f) by lia.
  destruct (zeq (a mod 2 ^ 64) f), (Z.eqb_spec (a mod 2 ^ 64) f); simpl; auto; congruence.
Qed.

Lemma ts4_felse a f : 0 <= f < 2 ^ 64 -> Int64.repr f = Int64.repr (- (1)) -> ts4_t15 f a = 0.
Proof.
  intros Hf He. unfold ts4_t15. apply (f_equal Int64.unsigned) in He.
  rewrite Int64.unsigned_repr in He by (unfold Int64.max_unsigned; simpl; lia).
  rewrite He. reflexivity.
Qed.

Lemma ts4_ok_of v ds r : ts4_t15 (fh_contentSize (bv_h v)) (ds + r) = 0 -> t34_fcs_ok v ds r.
Proof.
  unfold ts4_t15, t34_fcs_ok, ZSTD_CONTENTSIZE_UNKNOWN. destruct (Z.eqb_spec (fh_contentSize (bv_h v)) (2 ^ 64 - 1)); [auto |].
  destruct (Z.eqb_spec ((ds + r) mod 2 ^ 64) (fh_contentSize (bv_h v))); [auto | discriminate].
Qed.

Lemma ts4_bad_of v ds r : 0 <= fh_contentSize (bv_h v) < 2 ^ 64 ->
  ts4_t15 (fh_contentSize (bv_h v)) (ds + r) <> 0 -> ~ t34_fcs_ok v ds r.
Proof.
  unfold ts4_t15, t34_fcs_ok, ZSTD_CONTENTSIZE_UNKNOWN. intros Hf.
  destruct (Z.eqb_spec (fh_contentSize (bv_h v)) (2 ^ 64 - 1)); [congruence |].
  destruct (Z.eqb_spec ((ds + r) mod 2 ^ 64) (fh_contentSize (bv_h v))); [congruence |]. intros _ [E | E]; auto.
Qed.

Lemma ts4_neg k : Int64.repr (- k) = Int64.repr (2 ^ 64 - k).
Proof. apply Int64.eqm_samerepr. exists (-1). simpl. lia. Qed.

Lemma ts4_t15_01 f a : ts4_t15 f a = 0 \/ ts4_t15 f a = 1.
Proof. unfold ts4_t15. destruct (f =? 2 ^ 64 - 1); [auto |]. destruct (a mod 2 ^ 64 =? f); auto. Qed.

(* the DEBUGLOG loops as lemmas (copied from s5/BL5Facts.v): for(;;break){} and
   for(;;break){ if (0) s } before c *)
Lemma ts4_loop_break {cs: compspecs} {Espec: OracleKind} Delta P body Post :
  semax Delta P body (loop1_ret_assert P (overridePost P Post)) ->
  semax Delta P (Sloop body Sbreak) (overridePost P Post).
Proof.
  intros H. eapply semax_loop; [exact H |].
  eapply semax_pre; [| apply semax_break]. intros rho. destruct Post; cbn. apply andp_left2, derives_refl.
Qed.

Lemma ts4_dw_skip {cs: compspecs} {Espec: OracleKind} Delta P c Post :
  semax Delta P c Post -> semax Delta P (Ssequence (Sloop Sskip Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply ts4_loop_break.
  destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
    first [apply derives_refl | apply FF_left].
Qed.

Lemma ts4_dw_if0 {cs: compspecs} {Espec: OracleKind} Delta P s c Post :
  semax Delta P c Post ->
  semax Delta P (Ssequence (Sloop (Sifthenelse (Econst_int (Int.repr 0) tint) s Sskip) Sbreak) c) Post.
Proof.
  intros H. eapply semax_seq; [| exact H]. apply ts4_loop_break.
  eapply semax_pre; [| apply semax_ifthenelse; [reflexivity | |]].
  - apply andp_left2. eapply derives_trans; [| apply now_later]. apply andp_right; [| apply derives_refl].
    intros rho. cbn. apply TT_right.
  - eapply semax_pre; [| apply semax_ff]. apply andp_left2.
    intros rho. unfold local, lift1, liftx. cbn. apply andp_left2. apply prop_left. intros Hf.
    cbv in Hf. inversion Hf.
  - destruct Post. eapply semax_post; [| | | | apply semax_skip]; intros; intros rho; cbn; apply andp_left2;
      first [apply andp_left1, derives_refl | apply FF_left].
Qed.

End CM_TS4Sep_1.

Ltac ts4_dw :=
  repeat apply -> seq_assoc;
  first [ apply ts4_dw_skip | apply ts4_dw_if0 ];
  try (match goal with |- semax _ _ ?c _ => is_var c; subst c end; unfold abbreviate).

Ltac ts4_fif id v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp id v :: Q) (SEPx R))) end.

Section CM_TS4Sep_2.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.

(* the then-branch of `if (stage == 4)` *)
Definition ts4_then : statement :=
  ltac:(let s := eval cbv [t34_stg] in t34_stg in
        lazymatch s with Ssequence _ (Sifthenelse _ ?t _) => exact t end).
Definition ts4_dw : statement :=
  ltac:(let s := eval cbv [ts4_then] in ts4_then in lazymatch s with Ssequence ?a _ => exact a end).
Definition ts4_loop : statement :=
  ltac:(let s := eval cbv [ts4_then] in ts4_then in lazymatch s with Ssequence _ (Ssequence ?a _) => exact a end).
Definition ts4_ck : statement :=
  ltac:(let s := eval cbv [ts4_then] in ts4_then in lazymatch s with Ssequence _ (Ssequence _ ?a) => exact a end).

Lemma ts4_then_eq : ts4_then = Ssequence ts4_dw (Ssequence ts4_loop ts4_ck).
Proof. reflexivity. Qed.

(* the content size check: for (;;break) { ts4_s1 (t'29 = fcs; t'16 = (fcs != -1 && decodedSize != fcs));
   ts4_s2 (if (t'16) { DEBUGLOGs; return -20 }) } *)
Definition ts4_s1 : statement :=
  ltac:(let s := eval cbv [ts4_loop] in ts4_loop in lazymatch s with Sloop (Ssequence ?a _) _ => exact a end).
Definition ts4_s2 : statement :=
  ltac:(let s := eval cbv [ts4_loop] in ts4_loop in lazymatch s with Sloop (Ssequence _ ?a) _ => exact a end).

Lemma ts4_loop_eq : ts4_loop = Sloop (Ssequence ts4_s1 ts4_s2) Sbreak.
Proof. reflexivity. Qed.

Section Mid.
Variable DENT : dent_pred.
Variable TABS : tabs_pred.

(* the state after `t'24 = stage` (stage 4), the frame fields fsB split *)
Definition ts4_mid (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict) (hb: list val)
    (shk shd: share) (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val)
    (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'24 (Vint (Int.repr 4)); temp _rSize (Vlong (Int64.repr r));
         lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp; gvars gv;
         temp _dctx p; temp _dst (offset_val opos ob); temp _dstCapacity (Vlong (Int64.repr (osz - opos)));
         temp _src src; temp _srcSize (Vlong (Int64.repr (Zlength c))))
  SEP (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 4)) p;
       field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 0)) p;
       field_at Ews t_dctx (DOT _fParams) (fh_val (bv_h v)) p;
       field_at Ews t_dctx (DOT _decodedSize) (Vlong (Int64.repr (ds + r))) p;
       field_at Ews t_dctx (DOT _processedCSize) (Vlong (Int64.repr (pcs + Zlength c))) p;
       ts4_rest p fsB pr;
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp;
       pws_pred W; zstd_globals gv; tabs_rep TABS gv p t';
       field_at Ews t_dctx (DOT _headerBuffer) hb p; dent_of DENT gv (bd_oxo od); bd_res shk od;
       data_at shd (tarray tuchar osz) oc' ob; data_at shs (tarray tuchar (Zlength c)) (zbytes c) src).

(* the state after ts4_s1 (t'16 = the test, t'29 = fcs), with the facts Ps *)
Definition ts4_m15 (Ps: list Prop) (W: list ptr_witness) (gv: globals) (p: val) (pr: dparams) (od: option bldict)
    (hb: list val) (shk shd: share) (ob: val) (osz opos: Z) (shs: share) (src: val) (c: list Z) (v_bp: val)
    (r: Z) (v: blv) (ds pcs: Z) (fsB: fstate) (oc': list val) (t': tabs3) : environ -> mpred :=
  PROPx Ps
  (LOCALx (temp _t'16 (Vint (Int.repr (ts4_t15 (fh_contentSize (bv_h v)) (ds + r)))) ::
           temp _t'29 (Vlong (Int64.repr (fh_contentSize (bv_h v)))) ::
           temp _t'24 (Vint (Int.repr 4)) :: temp _rSize (Vlong (Int64.repr r)) ::
           lvar _bp (Tstruct ___gp_blockProperties_t noattr) v_bp :: gvars gv ::
           temp _dctx p :: temp _dst (offset_val opos ob) :: temp _dstCapacity (Vlong (Int64.repr (osz - opos))) ::
           temp _src src :: temp _srcSize (Vlong (Int64.repr (Zlength c))) :: nil)
  (SEPx (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr 4)) p ::
       field_at Ews t_dctx (DOT _expected) (Vlong (Int64.repr 0)) p ::
       field_at Ews t_dctx (DOT _fParams) (fh_val (bv_h v)) p ::
       field_at Ews t_dctx (DOT _decodedSize) (Vlong (Int64.repr (ds + r))) p ::
       field_at Ews t_dctx (DOT _processedCSize) (Vlong (Int64.repr (pcs + Zlength c))) p ::
       ts4_rest p fsB pr ::
       data_at_ Tsh (Tstruct ___gp_blockProperties_t noattr) v_bp ::
       pws_pred W :: zstd_globals gv :: tabs_rep TABS gv p t' ::
       field_at Ews t_dctx (DOT _headerBuffer) hb p :: dent_of DENT gv (bd_oxo od) :: bd_res shk od ::
       data_at shd (tarray tuchar osz) oc' ob :: data_at shs (tarray tuchar (Zlength c)) (zbytes c) src :: nil))).

End Mid.

End CM_TS4Sep_2.
