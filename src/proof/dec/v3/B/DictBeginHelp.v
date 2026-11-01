(* The helper lemmas of v2's B/dict/body_dict_begin.v (ent_split, huf_hdr), without its body proof *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

Lemma ent_split (p: val):
  field_at_ Ews t_dctx (DOT _entropy) p |--
  field_at_ Ews t_dctx (DOT _entropy DOT _LLTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _OFTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _MLTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _hufTable) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _rep) p *
  field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p.
Proof.
  unfold field_at_. unfold_field_at 1%nat. cancel.
Qed.

Lemma huf_hdr (p: val):
  field_at Ews t_dctx (DOT _entropy DOT _hufTable)
    (upd_Znth 0 (default_val (tarray tuint 4097)) (Vint (Int.mul (Int.repr 12) (Int.repr 16777217)))) p
  |-- hufhdr_at Ews (ctx_huf p).
Proof.
  unfold hufhdr_at, ctx_huf.
  rewrite field_at_data_at. simpl nested_field_type.
  set (q := field_address t_dctx (DOT _entropy DOT _hufTable) p).
  assert_PROP (field_compatible (tarray tuint 4097) [] q) as FC by entailer!.
  change (default_val (tarray tuint 4097)) with (Zrepeat Vundef 4097).
  rewrite upd_Znth0_old by (rewrite Zlength_Zrepeat; lia).
  match goal with |- context [?v :: ?l] => change (v :: l) with ([v] ++ l) end.
  rewrite (split2_data_at_Tarray_app 1 4097) by list_solve.
  erewrite (data_at_singleton_array_eq Ews tuint) by reflexivity.
  rewrite field_address0_offset by auto with field_compatible.
  sep_apply (data_at_memory_block Ews (tarray tuint (4097 - 1))).
  simpl sizeof. simpl nested_field_offset.
  assert (E: Int.mul (Int.repr 12) (Int.repr 16777217) =
             Int.repr (decode_int [Byte.repr 12; Byte.zero; Byte.zero; Byte.repr 12])) by reflexivity.
  rewrite E.
  assert (FCu: field_compatible tuint [] q).
  { assert (H0: field_compatible (tarray tuint 4097) (SUB 0) q) by auto with field_compatible.
    apply field_compatible_nested_field in H0. simpl in H0.
    rewrite isptr_offset_val_zero in H0 by auto with field_compatible. exact H0. }
  rewrite <- (data_at_int_bytes eq_refl) by exact FCu.
  assert (FCd: field_compatible t_dtdesc [] q).
  { destruct FCu as (Hp & Hl & Hs & Ha & Hn). red. repeat split; auto.
    destruct q; try contradiction. red. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
    intros i0 t0 z0 Hf Ho. simpl in Hf, Ho.
    repeat (if_tac in Hf; [inv Hf; inv Ho; eapply align_compatible_rec_by_value;
                           [reflexivity | apply Z.divide_1_l] |]).
    discriminate. }
  Exists (Vubyte Byte.zero) (Vubyte Byte.zero) (Vubyte (Byte.repr 12)).
  rewrite prop_true_andp
    by (split; [destruct FCu as (_ & _ & _ & Ha & _); exact Ha |];
        split; [exists 0 | split; [exists 0 | exists 12]]; split; auto; lia).
  unfold_data_at (data_at _ t_dtdesc _ _).
  rewrite !field_at_data_at.
  rewrite !field_compatible_field_address by auto with field_compatible.
  simpl nested_field_offset. simpl nested_field_type.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  replace (Vint (Int.repr 12)) with (Vubyte (Byte.repr 12)) by reflexivity.
  unfold HUF_CELLBYTES. cancel.
Qed.

