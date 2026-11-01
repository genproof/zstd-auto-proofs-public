(* FS3 streaming, case zdss_loadHeader, piece C, segment s10: the groups of the context split into the
   fields s10 touches and the rest. *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3C2_s10_lib.
Local Open Scope logic.

Section CM_LH3C2_s10_g_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the frame group without the format and the frame fields *)
Definition c10_fgr (TABS: tabs_pred) (gv: globals) (p: val) (t: tabs3) (pr: dparams) (sp: val) : mpred :=
  cfg_lit p * tabs_rep TABS gv p t *
  field_at Ews t_dctx (DOT _forceIgnoreChecksum) (Vint (Int.repr (dp_ignore pr))) p *
  field_at Ews t_dctx (DOT _maxBlockSizeParam) (Vint (Int.repr (dp_bmax pr))) p *
  field_at Ews t_dctx (DOT _refMultipleDDicts) (Vint (Int.repr (dp_multi pr))) p *
  field_at Ews t_dctx (DOT _ddictSet) sp p.

Lemma c10_fg_eq (TABS: tabs_pred) gv p fs t pr sp :
  fgroup3 TABS gv p fs t pr sp =
  !! (cold01 fs /\ par_ok pr) && (cfg_fmt p (dp_fmt pr) * frame_fields p fs * c10_fgr TABS gv p t pr sp).
Proof. unfold fgroup3, c10_fgr. f_equal. apply pred_ext; cancel. Qed.

Definition c10_sgp (s: sfields) : Prop :=
  0 <= sf_inSize s /\ 0 <= sf_outSize s /\ sf_inSize s + sf_outSize s <= 2 ^ 32 /\
  Int.min_signed <= sf_stage s <= Int.max_signed /\ Int.min_signed <= sf_nfp s <= Int.max_signed /\
  0 <= sf_over s <= Int64.max_unsigned /\ Zlength (sf_hbuf s) = 18 /\ byte_cells (sf_ring s) /\
  (sf_inBuff s <> nullval -> sf_outBuff s = offset_val (sf_inSize s) (sf_inBuff s)) /\ 0 <= sf_held s /\
  (sf_inBuff s <> nullval -> 0 < sf_inSize s + sf_outSize s).

(* the stream group without lhSize and headerBuffer *)
Definition c10_sgr (p: val) (s: sfields) : mpred :=
  field_at Ews t_dctx (DOT _streamStage) (Vint (Int.repr (sf_stage s))) p *
  field_at Ews t_dctx (DOT _inBuff) (sf_inBuff s) p *
  field_at Ews t_dctx (DOT _inBuffSize) (Vlong (Int64.repr (sf_inSize s))) p *
  field_at Ews t_dctx (DOT _inPos) (sf_inPos s) p *
  field_at Ews t_dctx (DOT _outBuff) (sf_outBuff s) p *
  field_at Ews t_dctx (DOT _outBuffSize) (Vlong (Int64.repr (sf_outSize s))) p *
  field_at Ews t_dctx (DOT _outStart) (sf_outStart s) p *
  field_at Ews t_dctx (DOT _outEnd) (sf_outEnd s) p *
  field_at Ews t_dctx (DOT _hostageByte) (sf_hostage s) p *
  field_at Ews t_dctx (DOT _noForwardProgress) (Vint (Int.repr (sf_nfp s))) p *
  field_at Ews t_dctx (DOT _expectedOutBuffer) (sf_expOut s) p *
  field_at Ews t_dctx (DOT _oversizedDuration) (Vlong (Int64.repr (sf_over s))) p *
  ring_rep (sf_mem s) (sf_inBuff s) (sf_inSize s + sf_outSize s) (sf_ring s) *
  mgroup (sf_mem s) p (sf_given s).

Lemma c10_sg_eq (p: val) (s: sfields) :
  sgroup p s = !! (c10_sgp s) &&
    (field_at Ews t_dctx (DOT _lhSize) (sf_lhSize s) p * field_at Ews t_dctx (DOT _headerBuffer) (sf_hbuf s) p *
     c10_sgr p s).
Proof. unfold sgroup, c10_sgp, c10_sgr. f_equal. apply pred_ext; cancel. Qed.

(* moving pure facts between a SEP list and the PROP list *)
Lemma c10_prop_sep (P: list Prop) (Q: list localdef) (A: Prop) (R R': list mpred) :
  fold_right_sepcon R = !! A && fold_right_sepcon R' ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx (A :: P) (LOCALx Q (SEPx R')).
Proof.
intros H. unfold PROPx, LOCALx, SEPx. extensionality rho. simpl. rewrite H.
apply pred_ext; normalize.
Qed.

Lemma c10_props_pre {Espec: OracleKind} {cs: compspecs} Delta (P: list Prop) Q R c Post :
  (fold_right and True P -> semax Delta (PROPx [] (LOCALx Q (SEPx R))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros H. eapply semax_pre with (!! (fold_right and True P) && PROPx [] (LOCALx Q (SEPx R))).
- unfold PROPx. intro rho. simpl. normalize.
  first [apply andp_left2; apply derives_refl | apply andp_right; [apply prop_right; auto | apply andp_left2; apply derives_refl]].
- apply semax_extract_prop. exact H.
Qed.

Lemma c10_props_post (P: list Prop) Q R : fold_right and True P ->
  PROPx [] (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R)).
Proof.
intros H. unfold PROPx. intro rho. simpl. normalize.
Qed.

Lemma c10_post_n {Espec: OracleKind} {cs: compspecs} Delta P c (Q Q': environ -> mpred) (R: ret_assert) :
  semax Delta P c (overridePost Q' R) -> ENTAIL Delta, Q' |-- Q -> semax Delta P c (overridePost Q R).
Proof.
intros H HQ. destruct R. eapply semax_post_flipped;
  [exact H | exact HQ | apply andp_left2; apply derives_refl | apply andp_left2; apply derives_refl |
   intros; apply andp_left2; apply derives_refl].
Qed.

(* the headerBuffer merged back *)
Lemma c10_hbuf_merge : forall p (c: list val) L, 0 <= L <= 18 -> Zlength c = 18 ->
  data_at Ews (tarray tuchar L) (sublist 0 L c) (field_address t_dctx (DOT _headerBuffer) p) *
  data_at Ews (tarray tuchar (18 - L)) (sublist L 18 c)
    (field_address0 (tarray tuchar 18) (SUB L) (field_address t_dctx (DOT _headerBuffer) p))
  |-- field_at Ews t_dctx (DOT _headerBuffer) c p.
Proof. intros. rewrite (c10_hbuf_split p c L) by auto. apply derives_refl. Qed.

Lemma c10_skip_magic_eq' : forall m, 0 <= m < 2 ^ 32 ->
  Int.eq (Int.repr (Z.land m (-16))) (Int.repr 407710288) = is_skippable_magic m.
Proof.
intros m Hm. rewrite <- (c10_skip_magic_eq m Hm). f_equal. unfold Int.and.
rewrite (Int.unsigned_repr m) by rep_lia. f_equal.
change (Int.unsigned (Int.repr (-16))) with (Z.land (Z.ones 32) (-16)).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

End CM_LH3C2_s10_g_1.
