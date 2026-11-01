(* ZSTD_copyDDictParameters *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

(* the addresses of a DDict's tables, as VST computes them for ddict->entropy.X *)
Lemma dd_addrs (q: val) :
  field_compatible t_entropy_dd [] q ->
  dd_seq KLL q = offset_val 0 (offset_val 24 q) /\ dd_seq KOF q = offset_val 4104 (offset_val 24 q) /\
  dd_seq KML q = offset_val 6160 (offset_val 24 q) /\ dd_huf q = offset_val 10264 (offset_val 24 q).
Proof.
  intros FC. unfold dd_seq, dd_huf, field_address.
  rewrite !if_true;
    try (destruct FC as [? [? [? [? ?]]]]; repeat split; auto; simpl; unfold in_members; simpl; tauto).
  rewrite !offset_offset_val. auto.
Qed.

(* the context's tables pointing at the DDict x's (TDict), its repeat offsets copied *)
Lemma tabs_def_dict gv p x st ht a b c r1 r2 r3 lxb :
  ddx_ent x = Some st -> st_huf st = Some ht -> st_seq st = Some (a, b, c) ->
  st_rep st = (r1, r2, r3) -> dstate_ok st ->
  field_at Ews t_dctx (DOT _HUFptr) (dd_huf (dx_q x)) p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr 1)) p *
  hufhdr_at Ews (ctx_huf p) *
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p *
  field_at Ews t_dctx (DOT _LLTptr) (dd_seq KLL (dx_q x)) p *
  field_at Ews t_dctx (DOT _OFTptr) (dd_seq KOF (dx_q x)) p *
  field_at Ews t_dctx (DOT _MLTptr) (dd_seq KML (dx_q x)) p *
  seqspace_at Ews KLL None (ctx_seq KLL p) * seqspace_at Ews KOF None (ctx_seq KOF p) *
  seqspace_at Ews KML None (ctx_seq KML p) *
  field_at Ews t_dctx (DOT _entropy DOT _rep) [Vint (Int.repr r1); Vint (Int.repr r2); Vint (Int.repr r3)] p *
  tabs_scratch p * lit_extra_at p lxb
  |-- tabs_def gv p (Some x) (mk_tstate st false lxb).
Proof.
  intros Ee Eh Es Er Hok.
  assert (Hoh: ox_huf (Some x) = Some ht) by (unfold ox_huf, ox_ent; simpl; rewrite Ee, Eh; auto).
  assert (Hos: ox_seq KLL (Some x) = Some a /\ ox_seq KOF (Some x) = Some b /\ ox_seq KML (Some x) = Some c)
    by (unfold ox_seq, ox_ent; simpl; rewrite Ee, Es; auto).
  destruct Hos as [HoLL [HoOF HoML]].
  unfold tabs_def, tabs_huf, tabs_seq, seq_where. cbn [ts_d ts_x2 ts_lxb]. rewrite Eh, Es, Er.
  apply andp_right; [apply prop_right; auto |].
  Exists (dd_huf (dx_q x)) false (dd_seq KLL (dx_q x)) TDict (dd_seq KML (dx_q x)) TDict
    (dd_seq KOF (dx_q x)) TDict.
  simpl seq_ptr_at. simpl ox_q. simpl rep_vals.
  entailer!.
Qed.

(* no entropy in the DDict: the context's own tables, as ZSTD_decompressBegin left them *)
Lemma tabs_def_init gv p ox x2 lxb :
  field_at Ews t_dctx (DOT _HUFptr) (ctx_huf p) p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr 0)) p *
  hufhdr_at Ews (ctx_huf p) *
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 0)) p *
  field_at Ews t_dctx (DOT _LLTptr) (ctx_seq KLL p) p *
  field_at Ews t_dctx (DOT _OFTptr) (ctx_seq KOF p) p *
  field_at Ews t_dctx (DOT _MLTptr) (ctx_seq KML p) p *
  seqspace_at Ews KLL None (ctx_seq KLL p) * seqspace_at Ews KOF None (ctx_seq KOF p) *
  seqspace_at Ews KML None (ctx_seq KML p) *
  field_at Ews t_dctx (DOT _entropy DOT _rep) [Vint (Int.repr 1); Vint (Int.repr 4); Vint (Int.repr 8)] p *
  tabs_scratch p * lit_extra_at p lxb
  |-- tabs_def gv p ox (mk_tstate dstate_init x2 lxb).
Proof.
  unfold tabs_def, tabs_huf, tabs_seq. cbn [ts_d ts_x2 ts_lxb]. simpl st_huf; simpl st_seq; simpl st_rep; simpl rep_vals.
  apply andp_right.
  { apply prop_right. unfold dstate_ok, rep_ok; simpl. repeat split; rep_lia. }
  Exists (ctx_huf p).
  entailer!.
Qed.

Lemma body_dict_copy : body_ok DICT_G ZSTD_copyDDictParameters_spec.
Proof.
  exists f_ZSTD_copyDDictParameters; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold ddict_struct, begin_tabs, frame_fields. Intros.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end;
    [entailer! | forward; entailer! | ].
  match goal with H: isptr buf \/ _ |- _ => rename H into Hbuf end.
  assert (Hpn: is_pointer_or_null buf)
    by (destruct Hbuf as [Hp | (-> & _)]; [destruct buf; try contradiction; simpl; auto | simpl; auto]).
  forward. forward. forward. forward. forward. forward. forward.
  (* F12: dictEnd = dictSize != 0 ? dictContent + dictSize : dictContent *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'1 (ddx_end x buf) :: Q) (SEPx R))) end.
  { assert (Hp: isptr buf).
    { destruct Hbuf as [Hp | (_ & _ & Hn)]; [exact Hp |].
      rewrite Hn in *. exfalso. match goal with H: Int64.repr (Zlength []) <> _ |- _ => apply H; reflexivity end. }
    forward. forward.
    assert (Hend: force_val (sem_add_ptr_long tuchar buf (Vlong (Int64.repr (Zlength (dx_bytes x)))))
                  = ddx_end x buf).
    { destruct buf; try contradiction; unfold ddx_end; simpl.
      rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_int64.
      rewrite Int64.unsigned_repr by rep_lia; reflexivity. }
    forward.
    entailer!; try (rewrite Hend; destruct buf; try contradiction; reflexivity). }
  { assert (Hz: Zlength (dx_bytes x) = 0).
    { match goal with H: Int64.repr (Zlength (dx_bytes x)) = _ |- _ =>
        apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; exact H end. }
    forward. forward.
    all: entailer!; try (destruct Hbuf as [Hp | (-> & _)]; [destruct buf; try contradiction; simpl; auto | simpl; auto]).
    all: try (destruct Hbuf as [Hp | (-> & _)]; [ | reflexivity];
              destruct buf; try contradiction; unfold ddx_end; rewrite Hz; simpl; rewrite Ptrofs.add_zero; reflexivity).
    all: try (rewrite Hz; change (Ptrofs.repr 0) with Ptrofs.zero; rewrite Ptrofs.add_zero; reflexivity). }
  forward.
  unfold ddict_copy.
  destruct (ddx_copied x) eqn:Ec; Intros.
  { match goal with Hc: true = true -> _ |- _ => pose proof (Hc eq_refl) as Hlen end.
    pose proof (ddx_buf_copied x buf Ec Hbuf) as Hbp.
    forward. forward. forward. forward.
    assert (Hg: force_val (sem_cast_i2i I32 Signed (force_val (sem_cmp_pp Cne buf
                  (Vlong (Int64.repr (Int.signed (Int.repr 0))))))) = Vint (Int.repr 1))
      by (destruct buf; try contradiction; reflexivity).
    rewrite Hg.
    destruct (ddx_ent x) as [st|] eqn:Ee.
    - unfold dent_def.
      destruct (st_huf st) as [ht|] eqn:Eh;
        [| assert_PROP False by entailer!; contradiction].
      destruct (st_seq st) as [[[a b] c]|] eqn:Es;
        [| assert_PROP False by entailer!; contradiction].
      Intros.
      destruct (st_rep st) as [[r1 r2] r3] eqn:Er. simpl rep_vals.
      forward. forward_if.
      2: { exfalso. discriminate. }
      forward. forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward. forward.
      assert_PROP (field_compatible t_entropy_dd [] (dx_q x)) as FC.
      { entailer!. match goal with Hf: field_compatible t_entropy_dd (_ :: _) (dx_q x) |- _ =>
          destruct Hf as (? & ? & ? & ? & ? & ?); repeat split; auto end. }
      destruct (dd_addrs _ FC) as [A1 [A2 [A3 A4]]].
      rewrite <- A1, <- A2, <- A3, <- A4.
      match goal with Hk: dstate_ok st |- _ =>
        sep_apply (tabs_def_dict gv p x st ht a b c r1 r2 r3 lxb Ee Eh Es Er Hk) end.
      unfold ddx_state; rewrite Ee.
      unfold ddict_struct, ddict_copy, dent_def, frame_fields.
      rewrite Ee, Ec, Eh, Es, Er.
      unfold fs_set_dictEnd, fs_with_dict.
      cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
           fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
           fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold st_huf st_seq st_rep rep_vals].
      entailer!.
    - unfold dent_def.
      forward. forward_if.
      { match goal with Hn: Int.repr 0 <> Int.zero |- _ => contradiction Hn; reflexivity end. }
      forward. forward.
      sep_apply (tabs_def_init gv p (Some x) false lxb).
      unfold ddx_state; rewrite Ee.
      unfold ddict_struct, ddict_copy, dent_def, frame_fields.
      rewrite Ee, Ec.
      unfold fs_set_dictEnd, fs_with_dict.
      cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
           fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
           fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
      entailer!.
  }
  { forward. forward. forward. forward.
    destruct (ddx_ent x) as [st|] eqn:Ee.
    - unfold dent_def.
      destruct (st_huf st) as [ht|] eqn:Eh;
        [| assert_PROP False by entailer!; contradiction].
      destruct (st_seq st) as [[[a b] c]|] eqn:Es;
        [| assert_PROP False by entailer!; contradiction].
      Intros.
      destruct (st_rep st) as [[r1 r2] r3] eqn:Er. simpl rep_vals.
      forward. forward_if.
      2: { exfalso. discriminate. }
      forward. forward. forward. forward. forward. forward.
      forward. forward. forward. forward. forward. forward.
      assert_PROP (field_compatible t_entropy_dd [] (dx_q x)) as FC.
      { entailer!. match goal with Hf: field_compatible t_entropy_dd (_ :: _) (dx_q x) |- _ =>
          destruct Hf as (? & ? & ? & ? & ? & ?); repeat split; auto end. }
      destruct (dd_addrs _ FC) as [A1 [A2 [A3 A4]]].
      rewrite <- A1, <- A2, <- A3, <- A4.
      match goal with Hk: dstate_ok st |- _ =>
        sep_apply (tabs_def_dict gv p x st ht a b c r1 r2 r3 lxb Ee Eh Es Er Hk) end.
      unfold ddx_state; rewrite Ee.
      unfold ddict_struct, ddict_copy, dent_def, frame_fields.
      rewrite Ee, Ec, Eh, Es, Er.
      unfold fs_set_dictEnd, fs_with_dict.
      cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
           fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
           fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold st_huf st_seq st_rep rep_vals].
      entailer!.
    - unfold dent_def.
      forward. forward_if.
      { match goal with Hn: Int.repr 0 <> Int.zero |- _ => contradiction Hn; reflexivity end. }
      forward. forward.
      sep_apply (tabs_def_init gv p (Some x) false lxb).
      unfold ddx_state; rewrite Ee.
      unfold ddict_struct, ddict_copy, dent_def, frame_fields.
      rewrite Ee, Ec.
      unfold fs_set_dictEnd, fs_with_dict.
      cbn [fs_previousDstEnd fs_gpDictCopy fs_prefixStart fs_virtualStart fs_dictEnd fs_expected fs_fParams
           fs_processedCSize fs_decodedSize fs_bType fs_stage fs_xxh fs_headerSize fs_validateChecksum
           fs_rleSize fs_isFrameDecompression fs_dictID fs_ddictIsCold].
      entailer!.
  }
Qed.
