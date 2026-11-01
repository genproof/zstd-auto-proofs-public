(* FS3-bl: ZSTD_nextSrcSizeToDecompress and ZSTD_nextInputType: the API specifications from the small helpers'
   (FSSpecs3), with BR = BLDefs.BR. *)
Require Export Zstd.proof.dec.v3.FS.BL.BLSmallSplit2.
Local Open Scope logic.

Section CM_BLSmall_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* the facts of BR the two readers need *)
Lemma BR_reader_facts (pr: dparams) (ba: Spec_api6.blabs) fs t hb :
  BR pr ba fs t hb ->
  fs_expected fs = vlong (Spec_api6.ba_expect ba) /\ 0 <= Spec_api6.ba_expect ba <= Int64.max_unsigned /\
  exists s, fs_stage fs = Vint (Int.repr (bl_stz s)) /\ (forall b, Spec_api6.ba_st ba = Some b -> bs_stage b = s).
Proof.
  intros [_ [od [osz0 [ts [_ [_ [_ [v [Hc [Hm _]]]]]]]]]].
  destruct Hc as (Ee & Er & Es & _). cbn [bl_loc ba_expect ba_st] in Ee, Er, Hm.
  split; [exact Ee | split; [rep_lia |]].
  exists (bv_stage v). split; [exact Es |].
  intros b Hb. destruct (Hm b Hb) as [E _]. exact E.
Qed.

Lemma bl_stz_range s : 0 <= bl_stz s <= 7.
Proof. destruct s; simpl; lia. Qed.

Lemma next_input_type_stz s : next_input_type (bl_stz s) = bl_input_type {| bs_stage := s; bs_expect := 0;
  bs_hbuf := nil; bs_hdr := fh_none; bs_ds := dstate_init; bs_out := nil; bs_btype := 0; bs_rle := 0 |}.
Proof. destruct s; reflexivity. Qed.

Lemma bl_input_type_stage b s : bs_stage b = s -> bl_input_type b = next_input_type (bl_stz s).
Proof. intros <-. destruct b as [s ? ? ? ? ? ? ?]; destruct s; reflexivity. Qed.

Lemma BL_next_subs : forall (DENT: dent_pred) (TABS: tabs_pred) (SR: srel3),
  DENT_OK DENT -> TABS_OK TABS ->
  funspec_sub (snd ZSTD_nextSrcSizeToDecompress_spec)
              (snd (ZSTD_nextSrcSizeToDecompress_aspec (DC3x DENT TABS SR BR))) /\
  funspec_sub (snd ZSTD_nextInputType_spec) (snd (ZSTD_nextInputType_aspec (DC3x DENT TABS SR BR))).
Proof.
  intros DENT TABS SR HD HT. split.
  - apply NDsubsume_subsume; [split; reflexivity|].
    split; [split; reflexivity|].
    intros [[[gv d] st] ba] [g args]. simpl.
    unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    unfold DC3x, DC3_of at 1.
    unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
    match goal with Hb: dc_bl st = Some ba, H3: forall ba0, dc_bl st = Some ba0 -> _ |- _ =>
      pose proof (H3 ba Hb) as HBR end.
    destruct (BR_reader_facts _ _ _ _ _ HBR) as (Ee & Er & _).
    Exists (d, Spec_api6.ba_expect ba)
      (field_at Ews t_dctx (DOT _expected) (vlong (Spec_api6.ba_expect ba)) d -* DC3_of DENT TABS SR BR gv d st).
    simpl. apply andp_right.
    + unfold LOCALx, argsassert2assert; simpl. entailer!.
      apply andp_left2. sep_apply (DC3_expected_split DENT TABS SR gv d st k); auto. rewrite Ee. cancel.
    + apply prop_right. intros rho'. unfold PROPx, LOCALx, SEPx; simpl. normalize.
      unfold local, lift1; simpl. normalize.
      rewrite sepcon_comm. apply modus_ponens_wand.
  - apply NDsubsume_subsume; [split; reflexivity|].
    split; [split; reflexivity|].
    intros [[[gv d] st] ba] [g args]. simpl.
    unfold PROPx, LOCALx, SEPx, PARAMSx, GLOBALSx; simpl. normalize.
    unfold DC3x, DC3_of at 1.
    unfold LOCALx at 1, argsassert2assert at 1; simpl. Intros k.
    match goal with Hb: dc_bl st = Some ba, H3: forall ba0, dc_bl st = Some ba0 -> _ |- _ =>
      pose proof (H3 ba Hb) as HBR end.
    destruct (BR_reader_facts _ _ _ _ _ HBR) as (_ & _ & s & Es & Hs).
    Exists (d, bl_stz s)
      (field_at Ews t_dctx (DOT _stage) (Vint (Int.repr (bl_stz s))) d -* DC3_of DENT TABS SR BR gv d st).
    simpl. apply andp_right.
    + unfold LOCALx, argsassert2assert; simpl. pose proof (bl_stz_range s). entailer!.
      apply andp_left2. sep_apply (DC3_stage_split DENT TABS SR gv d st k); auto. rewrite Es. cancel.
    + apply prop_right. intros rho'. unfold PROPx, LOCALx, SEPx; simpl. normalize.
      Exists (next_input_type (bl_stz s)).
      unfold local, lift1; simpl. normalize.
      apply andp_right.
      * apply prop_right. pose proof (bl_stz_range s).
        split; [| split; [split; [| auto] | assumption]].
        -- unfold next_input_type.
           destruct (Z.leb_spec (bl_stz s) 1); [lia|]. destruct (Z.leb_spec (bl_stz s) 5); lia.
        -- intros b Hb. rewrite (bl_input_type_stage b s (Hs b Hb)). reflexivity.
      * rewrite sepcon_comm. apply modus_ponens_wand.
Qed.

End CM_BLSmall_1.
