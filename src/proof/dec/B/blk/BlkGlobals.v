(* Group BLK: the predefined sequence tables of zstd_globals (BlkGroups.predef_tabs; BRep.predef_cells). *)
Require Export Zstd.proof.dec.B.blk.BlkGroups.

Lemma fc_seqsym_hdr: forall p,
  field_compatible t_seqSymbol [] p <-> field_compatible t_seqhdr [] p.
Proof.
  intros p.
  unfold field_compatible; simpl. split; intros (?&?&?&?&?); destruct p; try contradiction; repeat split; auto.
  - unfold align_compatible in *.
    assert (A: (4 | Ptrofs.unsigned i)).
    { eapply align_compatible_rec_Tstruct_inv with (i0 := _baseValue) in H2; [| reflexivity | reflexivity | reflexivity].
      eapply align_compatible_rec_by_value_inv in H2; [|reflexivity]. simpl in H2.
      replace (Ptrofs.unsigned i) with (Ptrofs.unsigned i + 4 - 4) by lia. apply Z.divide_sub_r; auto. exists 1; lia. }
    eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity |].
    intros i0 t0 z0 Ht Ho. simpl in Ht.
    destruct (ident_eq i0 _fastMode); [subst; inv Ht; simpl in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|]; simpl; rewrite Z.add_0_r; auto|].
    destruct (ident_eq i0 _tableLog); [subst; inv Ht; simpl in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|]; simpl; apply Z.divide_add_r; auto; exists 1; lia|].
    discriminate.
  - unfold align_compatible in *.
    assert (A: (4 | Ptrofs.unsigned i)).
    { eapply align_compatible_rec_Tstruct_inv with (i0 := _fastMode) in H2; [| reflexivity | reflexivity | reflexivity].
      eapply align_compatible_rec_by_value_inv in H2; [|reflexivity]. simpl in H2. rewrite Z.add_0_r in H2; auto. }
    eapply align_compatible_rec_Tstruct; [reflexivity | reflexivity |].
    intros i0 t0 z0 Ht Ho. simpl in Ht.
    repeat (destruct (ident_eq i0 _) in Ht; [subst; inv Ht; simpl in Ho; inv Ho; eapply align_compatible_rec_by_value; [reflexivity|]; simpl; apply Z.divide_add_r; [apply Z.divide_trans with 4; auto; first [exists 2; lia | exists 4; lia | exists 1; lia]| first [exists 0; lia | exists 1; lia | exists 2; lia | exists 3; lia]] |]).
    discriminate.
Qed.

Local Open Scope logic.

Lemma hdr_cell_fc: forall sh (log: Z) p,
  field_compatible t_seqSymbol [] p ->
  data_at sh t_seqSymbol (Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log)))) p =
  data_at sh t_seqhdr (Vint (Int.repr predef_fm), Vint (Int.repr log)) p.
Proof.
  intros sh log p FC.
  assert (FH: field_compatible t_seqhdr [] p) by (apply fc_seqsym_hdr; auto).
  unfold_data_at (data_at _ t_seqSymbol _ _).
  unfold_data_at (data_at _ t_seqhdr _ _).
  rewrite !field_at_data_at. rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (P: isptr p) by auto with field_compatible.
  rewrite !isptr_offset_val_zero by auto.
  assert (A: (4 | Ptrofs.unsigned (match p with Vptr _ i => i | _ => Ptrofs.zero end))).
  { destruct FH as (?&?&?&AL&?). destruct p; try contradiction. red in AL.
    eapply align_compatible_rec_Tstruct_inv with (i0 := _fastMode) in AL; [| reflexivity | reflexivity | reflexivity].
    eapply align_compatible_rec_by_value_inv in AL; [|reflexivity]. simpl in AL. rewrite Z.add_0_r in AL; auto. }
  assert (FI: field_compatible tuint [] p).
  { destruct FH as (?&?&?&?&?). destruct p; try contradiction. repeat split; auto.
    - red in H1 |- *. simpl in *. lia.
    - eapply align_compatible_rec_by_value; [reflexivity|]. auto. }
  assert (FS: field_compatible tushort [] p).
  { destruct FH as (?&?&?&?&?). destruct p; try contradiction. repeat split; auto.
    - red in H1 |- *. simpl in *. lia.
    - eapply align_compatible_rec_by_value; [reflexivity|]. simpl. apply Z.divide_trans with 4; auto. exists 2; lia. }
  rewrite <- !sepcon_assoc. f_equal.
  transitivity (data_at sh tuchar (Vubyte (Byte.repr 1)) p * data_at sh tuchar (Vubyte (Byte.repr 0)) (offset_val 1 p) *
    data_at sh tuchar (Vubyte (Byte.repr 1)) (offset_val 2 p) * data_at sh tuchar (Vubyte (Byte.repr 1)) (offset_val 3 p)).
  - rewrite (data_at_short_bytes sh (Byte.repr 1) (Byte.repr 0) p FS). reflexivity.
  - rewrite data_at_int_bytes by auto. reflexivity.
Qed.

Lemma tab_split: forall sh (log m: Z) (rest: list (val * (val * (val * val)))) p,
  Zlength rest = m -> 0 <= m ->
  field_compatible (tarray t_seqSymbol (1 + m)) [] p ->
  data_at sh (tarray t_seqSymbol (1 + m))
    ((Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log)))) :: rest) p =
  data_at sh t_seqhdr (Vint (Int.repr predef_fm), Vint (Int.repr log)) p *
  data_at sh (tarray t_seqSymbol m) rest (offset_val 8 p).
Proof.
  intros sh log m rest p Hl Hm FC.
  change ((Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log)))) :: rest)
    with ([(Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log))))] ++ rest).
  rewrite (@split2_data_at_Tarray_app CompSpecs 1 (1 + m) sh t_seqSymbol
    [(Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log))))] rest)
    by (try reflexivity; list_solve).
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (@data_at_singleton_array_eq CompSpecs sh t_seqSymbol (Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr log))))) by reflexivity.
  replace (1 + m - 1) with m by lia. simpl nested_field_offset.
  rewrite hdr_cell_fc; [reflexivity|]. destruct FC as (?&?&?&AL&?). destruct p; try contradiction. repeat split; auto.
  - red in H1 |- *. simpl sizeof in *. rewrite Z.max_r in H1 by lia. lia.
  - red in AL |- *. eapply align_compatible_rec_Tarray_inv with (i := 0) in AL; [|lia]. rewrite Z.mul_0_r, Z.add_0_r in AL. exact AL.
Qed.

Lemma tab_pred: forall sh k t (vals: list (val * (val * (val * val)))) n p,
  vals = (Vint (Int.repr 1), (Vint (Int.repr 1), (Vint (Int.repr 1), Vint (Int.repr (ft_log t))))) ::
         map (seqcell k) (ft_cells t) ->
  n = 1 + 2 ^ ft_log t -> Zlength (ft_cells t) = 2 ^ ft_log t -> fse_ok k t ->
  data_at sh (tarray t_seqSymbol n) vals p =
  !! field_compatible (tarray t_seqSymbol n) [] p && seqtab_at_fm sh k t predef_fm p.
Proof.
  intros sh k t vals n p -> -> HL OK.
  assert (0 <= 2 ^ ft_log t) by (rewrite <- HL; apply Zlength_nonneg).
  apply pred_ext.
  - saturate_local. rewrite tab_split by (rewrite ?Zlength_map; auto).
    unfold seqtab_at_fm. entailer!.
  - unfold seqtab_at_fm. Intros. rewrite tab_split by (rewrite ?Zlength_map; auto). cancel.
Qed.

Lemma globals_ok : GLOBALS_obligation.
Proof.
  intros gv.
  destruct predef_cells as (CL & CO & CM).
  destruct predef_ok as (OL & OO & OM).
  exists (!! (field_compatible (tarray t_seqSymbol 65) [] (gv _LL_defaultDTable) /\
              field_compatible (tarray t_seqSymbol 33) [] (gv _OF_defaultDTable) /\
              field_compatible (tarray t_seqSymbol 65) [] (gv _ML_defaultDTable)) &&
   (@data_at CompSpecs Ews tint g_debuglevel_val (gv _g_debuglevel) *
    @data_at CompSpecs Ers (tarray tuint 32) DeBruijnBytePos_val (gv _DeBruijnBytePos) *
    @data_at CompSpecs Ers (tarray tuint 32) DeBruijnClz_val (gv _DeBruijnClz) *
    @data_at CompSpecs Ers tulong zeroFilled_val (gv _zeroFilled) *
    @data_at CompSpecs Ers (Tstruct ___gp_ZSTD_customMem noattr) ZSTD_defaultCMem_val (gv _ZSTD_defaultCMem) *
    @data_at CompSpecs Ers (tarray tuint 3) repStartValue_val (gv _repStartValue) *
    @data_at CompSpecs Ers (tarray tulong 4) ZSTD_fcs_fieldSize_val (gv _ZSTD_fcs_fieldSize) *
    @data_at CompSpecs Ers (tarray tulong 4) ZSTD_did_fieldSize_val (gv _ZSTD_did_fieldSize) *
    @data_at CompSpecs Ers tulong ZSTD_blockHeaderSize_val (gv _ZSTD_blockHeaderSize) *
    @data_at CompSpecs Ers (tarray tuchar 36) LL_bits_val (gv _LL_bits) *
    @data_at CompSpecs Ers (tarray tuchar 53) ML_bits_val (gv _ML_bits) *
    @data_at CompSpecs Ers (tarray (tarray (Tstruct ___gp_algo_time_t noattr) 2) 16) algoTime_val (gv _algoTime) *
    @data_at CompSpecs Ers (tarray tuint 36) LL_base_val (gv _LL_base) *
    @data_at CompSpecs Ers (tarray tuint 32) OF_base_val (gv _OF_base) *
    @data_at CompSpecs Ers (tarray tuchar 32) OF_bits_val (gv _OF_bits) *
    @data_at CompSpecs Ers (tarray tuint 53) ML_base_val (gv _ML_base) *
    @data_at CompSpecs Ers (tarray tuint 8) dec32table_val (gv _dec32table) *
    @data_at CompSpecs Ers (tarray tint 8) dec64table_val (gv _dec64table) *
    eb_res gv)).
  unfold zstd_globals, predef_tabs.
  change (Tstruct ___gp_ZSTD_seqSymbol noattr) with t_seqSymbol.
  rewrite (tab_pred Ers KLL LL_predef LL_defaultDTable_val 65)
    by (try rewrite <- CL; vm_compute; reflexivity || auto).
  rewrite (tab_pred Ers KOF OF_predef OF_defaultDTable_val 33)
    by (try rewrite <- CO; vm_compute; reflexivity || auto).
  rewrite (tab_pred Ers KML ML_predef ML_defaultDTable_val 65)
    by (try rewrite <- CM; vm_compute; reflexivity || auto).
  apply pred_ext; Intros; entailer!.
Qed.
