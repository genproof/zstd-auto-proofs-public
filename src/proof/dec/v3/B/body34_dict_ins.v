(* body3_dict_ins.v against BSpecs34 (insertDictionary's error branch keeps fParams, which
   DecIface3's usingDict_spec3 now states): ZSTD_decompressBegin in a context of format f,
   ZSTD_decompress_insertDictionary after it, ZSTD_decompressBegin_usingDict (v2: B/dict/body_dict_begin.v,
   body_dict_ins.v). *)
Require Export Zstd.proof.dec.v3.B.BSpecs34.
Require Import Zstd.proof.dec.v3.B.DictBeginHelp Zstd.proof.dec.B.dict.body_dict_ins.
Require Import Zstd.proof.dec.B.BMemcpyOk.
Local Open Scope logic.

(* the bodies in the group's context for an allocator class (they call no allocation helper) *)
Section DI34.
Context {CMI: cmem_preds}.

Lemma body_dict_begin34 : body_ok DICT34_G ZSTD_decompressBegin_spec3s.
Proof.
  exists f_ZSTD_decompressBegin; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold tables_uninit, frame_fields, cfg_fmt. Intros.
  forward.
  forward_call f. do 9 forward.
  sep_apply (ent_split p). Intros.
  forward.
  do 6 forward.
  unfold zstd_globals. Intros.
  assert_PROP (field_compatible t_dctx (DOT _entropy DOT _rep) p) by entailer!.
  rewrite (field_at__data_at_ Ews t_dctx (DOT _entropy DOT _rep)). simpl nested_field_type.
  forward_call (Ers, Ews, gv _repStartValue, field_address t_dctx (DOT _entropy DOT _rep) p,
                existT (fun t => reptype t) (tarray tuint 3) repStartValue_val).
  { memcpy_side_B. }
  simpl projT1; simpl projT2.
  forward. forward. forward. forward.
  sep_apply (huf_hdr p).
  forward.
  assert (FCd: field_compatible t_dctx [] p)
    by (destruct H65 as (? & ? & ? & ? & ?); repeat split; auto).
  assert (FCh: field_compatible t_dctx (DOT _entropy DOT _hufTable) p)
    by (clear - FCd; destruct FCd as (? & ? & ? & ? & ?); repeat split; auto;
        unfold legal_field; simpl; unfold in_members; simpl;
        repeat (first [left; reflexivity | right])).
  assert (E1: offset_val 32 p = ctx_seq KLL p)
    by (unfold ctx_seq; simpl; rewrite field_compatible_field_address by auto with field_compatible; reflexivity).
  assert (E2: offset_val (32 + 6160) p = ctx_seq KML p)
    by (unfold ctx_seq; simpl; rewrite field_compatible_field_address by auto with field_compatible; reflexivity).
  assert (E3: offset_val (32 + 4104) p = ctx_seq KOF p)
    by (unfold ctx_seq; simpl; rewrite field_compatible_field_address by auto with field_compatible; reflexivity).
  assert (E4: offset_val (32 + 10264) p = ctx_huf p)
    by (unfold ctx_huf; rewrite field_compatible_field_address by auto; reflexivity).
  rewrite E1, E2, E3, E4.
  unfold zstd_globals, cfg_fmt, frame_fields, fs_begin3, begin_tabs, seqspace_at, tabs_scratch; simpl.
  rewrite (field_at_data_at Ews t_dctx (DOT _entropy DOT _rep)).
  unfold ctx_seq. simpl sk_tfield.
  rewrite (field_at__data_at_ Ews t_dctx (DOT _entropy DOT _LLTable)).
  rewrite (field_at__data_at_ Ews t_dctx (DOT _entropy DOT _OFTable)).
  rewrite (field_at__data_at_ Ews t_dctx (DOT _entropy DOT _MLTable)).
  simpl nested_field_type.
  cancel.
Qed.

Lemma body_insertDictionary34 : body_ok DICT34_G ZSTD_decompress_insertDictionary_spec34.
Proof.
  exists f_ZSTD_decompress_insertDictionary; split; [reflexivity | split; [reflexivity |]].
  start_function.
  assert_PROP (isptr dk) as Hdk by entailer!.
  forward_if.
  { (* |b| < 8: raw content *)
    forward_call (p, fs_begin3 fs f, dk, Zlength b, 0).
    forward.
    rewrite !Int64.unsigned_repr in H1 by rep_lia.
    assert (Ha: dict_auto_c b (load_dentropy b) = Some (dict_raw b)) by (unfold dict_auto_c; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    Exists 0 (load_dentropy b). rewrite Ha. cbn [dm_content dm_id dm_state dict_raw]. rewrite Z.sub_diag, isptr_offset_val_zero by auto.
    entailer!. Exists false. apply begin_tabs_init. }
  rewrite !Int64.unsigned_repr in H1 by rep_lia.
  pose proof (le_field_range b 0 H0) as Hm.
  forward_call (shk, dk, b, 0).
  { unfold mem_read_pre. split; [auto | split; [lia | split; [lia | apply Forall_sublist; auto]]]. }
  forward_if.
  { (* no magic number: raw content *)
    forward_call (p, fs_begin3 fs f, dk, Zlength b, 0).
    forward.
    assert (Ha: dict_auto_c b (load_dentropy b) = Some (dict_raw b)).
    { unfold dict_auto_c. rewrite (proj2 (Z.ltb_ge _ _)) by lia.
      destruct (Z.eqb_spec (le_field b 0 4) ZSTD_MAGIC_DICTIONARY) as [E|E]; [|reflexivity].
      exfalso. apply H2. rewrite E. apply Int.eqm_samerepr. exists 1. reflexivity. }
    Exists 0 (load_dentropy b). rewrite Ha. cbn [dm_content dm_id dm_state dict_raw]. rewrite Z.sub_diag, isptr_offset_val_zero by auto.
    entailer!. Exists false. apply begin_tabs_init. }
  assert (Hmag: le_field b 0 4 = ZSTD_MAGIC_DICTIONARY).
  { apply (f_equal Int.unsigned) in H2. rewrite Int.unsigned_repr in H2 by rep_lia. rewrite H2. reflexivity. }
  forward_call (shk, dk, b, 4).
  { unfold mem_read_pre. split; [auto | split; [lia | split; [lia | apply Forall_sublist; auto]]]. }
  rewrite ff_id_split. Intros.
  forward.
  unfold begin_tabs, tabs_scratch. Intros.
  assert_PROP (field_compatible t_dctx (DOT _HUFptr) p) as Hfc by entailer!.
  sep_apply (tabs_to_ent p (rep_vals (1, 4, 8))). Intros.
  forward_call (gv, ctx_ent p, shk, dk, b).
  { entailer!. unfold ctx_ent. rewrite field_compatible_field_address; [reflexivity | auto with field_compatible]. }
  Intros vret. destruct vret as [r ores]. Intros.
  cbn [fst snd] in H3, H4, H5. rename H4 into Hld, H5 into Hor.
  destruct ores as [[st es]|].
  { (* the entropy tables loaded *)
    destruct Hor as [-> [Hst Hes]].
    match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
    { entailer!. }
    { forward_call es. rewrite is_error_small by lia.
      forward_if; [contradiction |]. forward. entailer!. }
    forward. forward. forward. forward. forward.
    sep_apply (ff_set_id p (fs_begin3 fs f) (Vint (Int.repr (le_field b 4 4)))).
    forward_call (p, fs_set_id (fs_begin3 fs f) (Vint (Int.repr (le_field b 4 4))), offset_val es dk,
                  Zlength b - es, le_field b 4 4).
    forward.
    assert (Ha: dict_auto_c b (Some (st, es)) = Some {| dm_content := skipn (Z.to_nat es) b; dm_id := le_field b 4 4; dm_state := st |}).
    { unfold dict_auto_c. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hmag, Z.eqb_refl. reflexivity. }
    Exists 0 (Some (st, es)). rewrite Ha. cbn [dm_content dm_id dm_state].
    rewrite Zlength_skipn_nat by lia. rewrite fs_with_dict_set_id.
    replace (Zlength b - (Zlength b - es)) with es by lia. replace (es + (Zlength b - es)) with (Zlength b) by lia.
    entailer!. sep_apply (ent_full_to_tabs gv p st lxb Hst). Intros x2. Exists x2. cancel. }
  (* corrupted entropy tables *)
  match goal with |- semax _ ?P _ _ =>
    forward_loop P continue: (PROP (False) LOCAL () SEP ()) break: (PROP (False) LOCAL () SEP ()) end.
  { entailer!. }
  { forward_call r. rewrite Hor.
    forward_if; [| discriminate].
    dw0.
    match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ => forward_loop P break: P end.
    { entailer!. }
    { match goal with |- semax _ ?Q _ _ => forward_if Q end.
      { exfalso; match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end. }
      { forward; entailer!. }
      { forward; entailer!. } }
    dw0. dw0.
    forward.
    Exists (err_code 30) (@None (dstate * Z)).
    assert (Ha: dict_auto_c b None = None).
    { unfold dict_auto_c. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hmag, Z.eqb_refl. reflexivity. }
    rewrite Ha. Exists (fs_set_id (fs_begin3 fs f) (Vint (Int.repr (le_field b 4 4)))).
    entailer!.
    { split; [unfold err_code; rep_lia | f_equal; apply repr_err30]. }
    sep_apply (ff_set_id p (fs_begin3 fs f) (Vint (Int.repr (le_field b 4 4)))).
    sep_apply (ent_fail_to_uninit p). cancel. }
Qed.

Lemma body_usingDict34 : body_ok DICT34_G (ZSTD_decompressBegin_usingDict_spec3 tabs_def).
Proof.
  exists f_ZSTD_decompressBegin_usingDict; split; [reflexivity | split; [reflexivity |]].
  start_function.
  match goal with |- semax _ ?P _ _ =>
    forward_loop P
      continue: (PROP () LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
                 SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p (fs_begin3 fs f); begin_tabs p lxb;
                      if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))
      break: (PROP () LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
                 SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p; frame_fields p (fs_begin3 fs f); begin_tabs p lxb;
                      if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)) end.
  { entailer!. }
  { forward_call (gv, p, fs, f, lxb).
    forward_call 0.
    forward_if; [exfalso; match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end |].
    forward. entailer!. }
  { forward; entailer!. }
  destruct (eq_dec dk nullval) as [Edk|Ndk].
  { (* no dictionary *)
    subst dk.
    forward_if (temp _t'5 (Vint (Int.repr 0))).
    { match goal with H: isptr _ |- _ => destruct H end. }
    { forward. entailer!. }
    match goal with |- semax _ ?P _ _ => forward_if P end.
    { neq_self. }
    { forward. entailer!. }
    forward.
    Exists 0 (load_dentropy b). pose proof (ld_rel_exact b). unfold usingdict_model. rewrite if_true by reflexivity.
    cbn [dm_state no_dict dict_raw]. entailer!. Exists false. apply begin_tabs_init. }
  (* the caller's dictionary *)
  assert (Hbuf: buf_ok W shk (Zlength b) dk) by (match goal with Hd: dk = nullval /\ _ \/ _ |- _ => destruct Hd as [[? ?] | ?]; [contradiction | assumption] end).
  destruct (eq_dec dk nullval) as [?|_]; [contradiction |].
  assert_PROP (isptr dk) as Hdk by entailer!.
  forward_if (temp _t'5 (Vint (Int.repr (if Z.eq_dec (Zlength b) 0 then 0 else 1)))).
  { apply (tc_test_dict _ W shk (Zlength b) dk dk Hbuf Hdk). cancel. }
  { forward. entailer!.
    destruct (Z.eq_dec (Zlength b) 0) as [E|E]; [rewrite E; reflexivity |].
    rewrite Int64.eq_false; [reflexivity |]. intro C. apply (f_equal Int64.unsigned) in C.
    rewrite Int64.unsigned_repr in C by rep_lia. rewrite Int64.unsigned_zero in C. contradiction. }
  { contradiction. }
  destruct (Z.eq_dec (Zlength b) 0) as [Eb|Nb].
  { (* 0 bytes: no dictionary *)
    match goal with |- semax _ ?P _ _ => forward_if P end.
    { neq_self. }
    { forward. entailer!. }
    forward.
    Exists 0 (load_dentropy b). pose proof (ld_rel_exact b). unfold usingdict_model.
    destruct (eq_dec dk nullval); [contradiction |]. rewrite Eb. cbn [Z.eqb dm_state no_dict dict_raw].
    entailer!. Exists false. apply begin_tabs_init. }
  assert (Hb0: 0 < Zlength b) by (pose proof (Zlength_nonneg b); lia).
  forward_if (EX ores: option (dstate * Z), EX dm: dict_model,
      PROP (ld_rel b ores; dict_auto_c b ores = Some dm)
      LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
      SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
           frame_fields p (fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert.
  { match goal with |- semax _ ?P _ _ => forward_loop P continue: (EX ores: option (dstate * Z), EX dm: dict_model,
      PROP (ld_rel b ores; dict_auto_c b ores = Some dm)
      LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
      SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
           frame_fields p (fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert break: (EX ores: option (dstate * Z), EX dm: dict_model,
      PROP (ld_rel b ores; dict_auto_c b ores = Some dm)
      LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
      SEP (zstd_globals gv; pws_pred W; cfg_fmt p f; cfg_lit p;
           frame_fields p (fs_with_dict (fs_begin3 fs f) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert end.
    { entailer!. }
    { forward_call (gv, p, fs, shk, dk, b, f, lxb).
      Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. Intros.
      destruct (dict_auto_c b ores) as [dm|] eqn:Ea.
      - Intros. subst r.
        forward_call 0.
        forward_if; [neq_self |]. forward. Exists ores dm. entailer!.
      - Intros fs'.
        forward_call r.
        match goal with Hr: is_error_code r = true |- _ => rewrite Hr end.
        forward_if; [| exfalso; apply Int.one_not_zero; assumption].
        dw0.
        match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ => forward_loop P break: P end.
        { entailer!. }
        { match goal with |- semax _ ?Q _ _ => forward_if Q end.
          { neq_self. }
          { forward; entailer!. }
          { forward; entailer!. } }
        dw0. dw0.
        forward.
        Exists (err_code 30) ores. unfold usingdict_model.
        destruct (eq_dec dk nullval); [contradiction |]. rewrite (proj2 (Z.eqb_neq _ _) Nb), Ea.
        Exists fs'. pose proof dec_err_err30. entailer!.
        split; [unfold err_code; rep_lia | f_equal; apply repr_err30]. }
    { Intros ores dm. forward. Exists ores dm. entailer!. }
    unfold POSTCONDITION, abbreviate. simpl_ret_assert. Intros ores dm. Exists ores dm. entailer!. }
  { exfalso; apply Int.one_not_zero; assumption. }
  Intros ores dm.
  forward.
  Exists 0 ores. unfold usingdict_model.
  destruct (eq_dec dk nullval); [contradiction |]. rewrite (proj2 (Z.eqb_neq _ _) Nb).
  match goal with Ea: dict_auto_c b ores = Some dm |- _ => rewrite Ea end.
  entailer!. Exists x2. apply derives_refl.
Qed.

Lemma DICT34_ins_ok :
  body_ok DICT34_G ZSTD_decompressBegin_spec3s /\
  body_ok DICT34_G ZSTD_decompress_insertDictionary_spec34 /\
  body_ok DICT34_G (ZSTD_decompressBegin_usingDict_spec3 tabs_def).
Proof.
  split; [exact body_dict_begin34 | split; [exact body_insertDictionary34 | exact body_usingDict34]].
Qed.

End DI34.
