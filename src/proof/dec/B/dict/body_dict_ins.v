(* ZSTD_refDictContent, ZSTD_decompress_insertDictionary, ZSTD_decompressBegin_usingDict *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

(* ---------- facts about the model ---------- *)

Lemma le_value_bound (l: list Z) : Forall is_byte l -> 0 <= le_value l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
  induction 1 as [|x l Hx Hl IH]; cbn [le_value length]; [simpl; lia|].
  unfold is_byte in Hx. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia.
  change (2 ^ 8) with 256. nia.
Qed.

Lemma le_field_range (b: list Z) (i: Z) : bytes_ok b -> 0 <= le_field b i 4 < 2 ^ 32.
Proof.
  intros Hb. unfold le_field, slice.
  assert (HF: Forall is_byte (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b))).
  { apply Forall_firstn, Forall_skipn, Hb. }
  pose proof (le_value_bound _ HF) as [H0 H1]. split; [lia|].
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; [lia|].
  rewrite firstn_length. pose proof (Nat.le_min_l (Z.to_nat 4) (length (skipn (Z.to_nat i) b))). change (Z.to_nat 4) with 4%nat in *. lia.
Qed.

Lemma load_dentropy_size (b: list Z) st es : load_dentropy b = Some (st, es) -> es <= Zlength b.
Proof.
  unfold load_dentropy. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E; try discriminate
  | context [match ?m with Some _ => _ | None => _ end] =>
      let E := fresh "E" in destruct m as [[[? ?] ?]|] eqn:E || destruct m as [[? ?]|] eqn:E; try discriminate
  end.
  inversion H; subst. lia.
Qed.

Lemma is_error_small (c: Z) : 0 <= c <= 2 ^ 63 - 1 -> is_error_code c = false.
Proof. intros. unfold is_error_code. apply Z.ltb_ge. lia. Qed.

Lemma is_error_err30 : is_error_code (err_code 30) = true.
Proof. reflexivity. Qed.

Lemma dec_err_err30 : dec_err (err_code 30).
Proof.
  unfold dec_err, err_code, ZSTD_error_noForwardProgress_destFull, ZSTD_error_noForwardProgress_inputEmpty.
  split; [reflexivity | split; lia].
Qed.

Lemma repr_err30 : Int64.repr (-30) = Int64.repr (err_code 30).
Proof. apply Int64.eqm_samerepr. unfold err_code. exists (-1). reflexivity. Qed.

(* ---------- the context's entropy field as a ZSTD_entropyDTables_t ---------- *)

Lemma ctx_huf_ent (p: val) : ctx_huf p = ent_huf (ctx_ent p).
Proof.
  unfold ctx_huf, ent_huf, ctx_ent.
  change [StructField (_hufTable); StructField _entropy] with ([StructField (_hufTable)] ++ [StructField _entropy]).
  rewrite field_address_app. reflexivity.
Qed.

Lemma ctx_seq_ent (k: seqkind) (p: val) : ctx_seq k p = ent_seq k (ctx_ent p).
Proof.
  unfold ctx_seq, ent_seq, ctx_ent.
  change [StructField (sk_tfield k); StructField _entropy] with ([StructField (sk_tfield k)] ++ [StructField _entropy]).
  rewrite field_address_app. reflexivity.
Qed.

Lemma ctx_rep_ent (sh: share) (v: list val) (p: val) :
  field_at sh t_dctx (DOT _entropy DOT _rep) v p = field_at sh t_entropy (DOT _rep) v (ctx_ent p).
Proof.
  change [StructField (_rep); StructField _entropy] with ([StructField (_rep)] ++ [StructField _entropy]).
  unfold ctx_ent. erewrite field_at_app; [reflexivity | apply JMeq_refl].
Qed.

Lemma ctx_ws_ent (sh: share) (p: val) :
  field_at_ sh t_dctx (DOT _entropy DOT _workspace) p = field_at_ sh t_entropy (DOT _workspace) (ctx_ent p).
Proof.
  unfold field_at_. change [StructField (_workspace); StructField _entropy] with ([StructField (_workspace)] ++ [StructField _entropy]).
  unfold ctx_ent. erewrite field_at_app; [reflexivity | apply JMeq_refl].
Qed.

Lemma ctx_entropy_ent (sh: share) (p: val) :
  field_at_ sh t_dctx (DOT _entropy) p = data_at_ sh t_entropy (ctx_ent p).
Proof. unfold field_at_, data_at_. rewrite field_at_data_at. reflexivity. Qed.

(* ---------- the frame fields: the dictID field apart ---------- *)

Definition fs_set_id (fs: fstate) (v: val) : fstate :=
  {| fs_previousDstEnd := fs_previousDstEnd fs; fs_gpDictCopy := fs_gpDictCopy fs;
     fs_prefixStart := fs_prefixStart fs; fs_virtualStart := fs_virtualStart fs; fs_dictEnd := fs_dictEnd fs;
     fs_expected := fs_expected fs; fs_fParams := fs_fParams fs; fs_processedCSize := fs_processedCSize fs;
     fs_decodedSize := fs_decodedSize fs; fs_bType := fs_bType fs; fs_stage := fs_stage fs;
     fs_xxh := fs_xxh fs; fs_headerSize := fs_headerSize fs; fs_validateChecksum := fs_validateChecksum fs;
     fs_rleSize := fs_rleSize fs; fs_isFrameDecompression := fs_isFrameDecompression fs;
     fs_dictID := v; fs_ddictIsCold := fs_ddictIsCold fs |}.

Definition ff_rest (p: val) (fs: fstate) : mpred :=
  field_at Ews t_dctx (DOT _previousDstEnd) (fs_previousDstEnd fs) p *
  field_at Ews t_dctx (DOT _gpDictCopy) (fs_gpDictCopy fs) p *
  field_at Ews t_dctx (DOT _prefixStart) (fs_prefixStart fs) p *
  field_at Ews t_dctx (DOT _virtualStart) (fs_virtualStart fs) p *
  field_at Ews t_dctx (DOT _dictEnd) (fs_dictEnd fs) p *
  field_at Ews t_dctx (DOT _expected) (fs_expected fs) p *
  field_at Ews t_dctx (DOT _fParams) (fs_fParams fs) p *
  field_at Ews t_dctx (DOT _processedCSize) (fs_processedCSize fs) p *
  field_at Ews t_dctx (DOT _decodedSize) (fs_decodedSize fs) p *
  field_at Ews t_dctx (DOT _bType) (fs_bType fs) p *
  field_at Ews t_dctx (DOT _stage) (fs_stage fs) p *
  xxh_field p (fs_xxh fs) *
  field_at Ews t_dctx (DOT _headerSize) (fs_headerSize fs) p *
  field_at Ews t_dctx (DOT _validateChecksum) (fs_validateChecksum fs) p *
  field_at Ews t_dctx (DOT _rleSize) (fs_rleSize fs) p *
  field_at Ews t_dctx (DOT _isFrameDecompression) (fs_isFrameDecompression fs) p *
  field_at Ews t_dctx (DOT _ddictIsCold) (fs_ddictIsCold fs) p.

Lemma ff_id_split (p: val) (fs: fstate) :
  frame_fields p fs = field_at Ews t_dctx (DOT _dictID) (fs_dictID fs) p * ff_rest p fs.
Proof. unfold frame_fields, ff_rest. apply pred_ext; cancel. Qed.

Lemma fs_with_dict_set_id (fs: fstate) (v start fin: val) (g i: Z) :
  fs_with_dict (fs_set_id fs v) start fin g i = fs_with_dict fs start fin g i.
Proof. reflexivity. Qed.

Lemma Zlength_skipn_nat (l: list Z) (n: Z) : 0 <= n <= Zlength l -> Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros Hn. rewrite !Zlength_correct, skipn_length, Nat2Z.inj_sub, Z2Nat.id by (rewrite Zlength_correct in Hn; lia).
  reflexivity.
Qed.

Lemma ff_set_id (p: val) (fs: fstate) (v: val) :
  field_at Ews t_dctx (DOT _dictID) v p * ff_rest p fs |-- frame_fields p (fs_set_id fs v).
Proof. rewrite ff_id_split. apply derives_refl. Qed.

(* ---------- the tables after ZSTD_decompressBegin ---------- *)

Lemma dstate_init_ok : dstate_ok dstate_init.
Proof. unfold dstate_ok, rep_ok, seqs_ok, dstate_init; simpl. lia. Qed.

Lemma begin_tabs_init (gv: globals) (p: val) (x2: bool) (lxb: list Z) :
  begin_tabs p lxb |-- tabs_def gv p None (mk_tstate dstate_init x2 lxb).
Proof.
  unfold begin_tabs, tabs_def, tabs_huf, tabs_seq. simpl.
  Exists (ctx_huf p). entailer!. apply dstate_init_ok.
Qed.

Lemma tabs_to_ent (p: val) (v: list val) :
  hufhdr_at Ews (ctx_huf p) * seqspace_at Ews KLL None (ctx_seq KLL p) *
  seqspace_at Ews KOF None (ctx_seq KOF p) * seqspace_at Ews KML None (ctx_seq KML p) *
  field_at Ews t_dctx (DOT _entropy DOT _rep) v p * field_at_ Ews t_dctx (DOT _entropy DOT _workspace) p
  |-- ent_blank (ctx_ent p) * field_at_ Ews t_entropy (DOT _rep) (ctx_ent p) *
      field_at_ Ews t_entropy (DOT _workspace) (ctx_ent p).
Proof.
  unfold ent_blank. rewrite <- ctx_huf_ent, <- !ctx_seq_ent, ctx_rep_ent, ctx_ws_ent. cancel.
Qed.

Lemma ent_full_to_tabs (gv: globals) (p: val) (st: dstate) (lxb: list Z) :
  dstate_ok st ->
  ent_full (ctx_ent p) st *
  field_at Ews t_dctx (DOT _HUFptr) (ctx_huf p) p *
  field_at Ews t_dctx (DOT _LLTptr) (ctx_seq KLL p) p *
  field_at Ews t_dctx (DOT _MLTptr) (ctx_seq KML p) p *
  field_at Ews t_dctx (DOT _OFTptr) (ctx_seq KOF p) p *
  field_at Ews t_dctx (DOT _litEntropy) (Vint (Int.repr 1)) p *
  field_at Ews t_dctx (DOT _fseEntropy) (Vint (Int.repr 1)) p *
  field_at_ Ews t_dctx (DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_at p lxb
  |-- EX x2: bool, tabs_def gv p None (mk_tstate st x2 lxb).
Proof.
  intros Hok. unfold ent_full.
  destruct (st_huf st) as [ht|] eqn:Eh; [| entailer!].
  destruct (st_seq st) as [[[a b] c]|] eqn:Es; [| entailer!].
  unfold hufdt_at. Intros x2. Exists x2.
  unfold tabs_def, tabs_huf, tabs_seq, tabs_scratch. cbn [ts_d ts_x2 ts_lxb]. rewrite Eh, Es.
  rewrite <- ctx_huf_ent, <- !ctx_seq_ent, <- ctx_rep_ent, <- ctx_ws_ent.
  Exists (ctx_huf p) true. unfold seq_where, seq_ptr_at.
  Exists (ctx_seq KLL p) TCtx (ctx_seq KML p) TCtx (ctx_seq KOF p) TCtx.
  entailer!.
Qed.

Lemma ent_fail_to_uninit (p: val) (h l m o: val) (le fe: val) (lxb: list Z) :
  data_at_ Ews t_entropy (ctx_ent p) *
  field_at Ews t_dctx (DOT _HUFptr) h p *
  field_at Ews t_dctx (DOT _LLTptr) l p *
  field_at Ews t_dctx (DOT _MLTptr) m p *
  field_at Ews t_dctx (DOT _OFTptr) o p *
  field_at Ews t_dctx (DOT _litEntropy) le p *
  field_at Ews t_dctx (DOT _fseEntropy) fe p *
  field_at_ Ews t_dctx (DOT _workspace) p *
  field_at_ Ews t_dctx (DOT _litPtr) p *
  field_at_ Ews t_dctx (DOT _litSize) p *
  field_at_ Ews t_dctx (DOT _litBuffer) p *
  field_at_ Ews t_dctx (DOT _litBufferEnd) p *
  field_at_ Ews t_dctx (DOT _litBufferLocation) p *
  lit_extra_at p lxb
  |-- tables_uninit p lxb.
Proof.
  unfold tables_uninit. rewrite <- ctx_entropy_ent. cancel.
Qed.

Lemma body_refDictContent : body_ok DICT_G ZSTD_refDictContent_spec.
Proof.
  exists f_ZSTD_refDictContent; split; [reflexivity | split; [reflexivity |]].
  start_function. unfold frame_fields. Intros. rewrite H1, H2, H3.
  forward. forward. forward.
  forward_if (temp _t'1 (Vlong (Int64.repr 0))).
  { forward. entailer!. }
  { exfalso. apply H4; reflexivity. }
  forward. forward. forward. forward. forward.
  unfold frame_fields, fs_with_dict; simpl. rewrite H2.
  destruct d; try contradiction. simpl. rewrite Ptrofs.sub_zero_l. cancel.
Qed.

(* zstd's do { ... } while (0) around an error report: the loop runs its body once *)
Ltac neq_self := exfalso; match goal with H: ?x <> ?x |- _ => exact (H eq_refl) end.

Ltac dw0 :=
  match goal with |- semax _ ?P (Ssequence (Sloop _ _) _) _ =>
    forward_loop P break: P;
    [ entailer!
    | first [ forward_if; [ exfalso; match goal with H: _ <> _ |- _ => apply H; reflexivity end | forward; entailer! ]
            | forward; entailer! ]
    | ] end.

Lemma body_insertDictionary : body_ok DICT_G ZSTD_decompress_insertDictionary_spec.
Proof.
  exists f_ZSTD_decompress_insertDictionary; split; [reflexivity | split; [reflexivity |]].
  start_function.
  assert_PROP (isptr dk) as Hdk by entailer!.
  forward_if.
  { (* |b| < 8: raw content *)
    forward_call (p, fs_begin fs, dk, Zlength b, 0).
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
    forward_call (p, fs_begin fs, dk, Zlength b, 0).
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
    sep_apply (ff_set_id p (fs_begin fs) (Vint (Int.repr (le_field b 4 4)))).
    forward_call (p, fs_set_id (fs_begin fs) (Vint (Int.repr (le_field b 4 4))), offset_val es dk,
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
    rewrite Ha. Exists (fs_set_id (fs_begin fs) (Vint (Int.repr (le_field b 4 4)))).
    entailer!.
    { split; [unfold err_code; rep_lia | f_equal; apply repr_err30]. }
    sep_apply (ff_set_id p (fs_begin fs) (Vint (Int.repr (le_field b 4 4)))).
    sep_apply (ent_fail_to_uninit p). cancel. }
Qed.

(* `if (dict)` on the caller's dictionary: a weakly valid pointer (Spec_api6.buf_ok) *)
Lemma tc_test_dict (P: mpred) (W: list ptr_witness) (sh: share) (n: Z) (v: val) (d: val) :
  buf_ok W sh n d -> isptr d ->
  P |-- pws_pred W * data_at_ sh (tarray tuchar n) d * TT ->
  P |-- denote_tc_test_eq d (Vlong Int64.zero).
Proof.
  intros Hb Hd HP. destruct d; try contradiction.
  Transparent denote_tc_test_eq. unfold denote_tc_test_eq. Opaque denote_tc_test_eq. simpl.
  apply andp_right; [apply prop_right; reflexivity |].
  eapply derives_trans; [exact HP |].
  eapply derives_trans; [apply sepcon_derives; [apply Hb | apply derives_refl] |].
  eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl] |].
  apply extend_weak_valid_pointer.
Qed.

Lemma body_usingDict : body_ok DICT_G (ZSTD_decompressBegin_usingDict_spec tabs_def).
Proof.
  exists f_ZSTD_decompressBegin_usingDict; split; [reflexivity | split; [reflexivity |]].
  start_function.
  match goal with |- semax _ ?P _ _ =>
    forward_loop P
      continue: (PROP () LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
                 SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p (fs_begin fs); begin_tabs p lxb;
                      if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))
      break: (PROP () LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
                 SEP (zstd_globals gv; pws_pred W; cfg_b p; frame_fields p (fs_begin fs); begin_tabs p lxb;
                      if eq_dec dk nullval then emp else data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk)) end.
  { entailer!. }
  { forward_call (gv, p, fs, lxb).
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
  assert (Hbuf: buf_ok W shk (Zlength b) dk) by (destruct H1 as [[? ?] | ?]; [contradiction | assumption]).
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
      SEP (zstd_globals gv; pws_pred W; cfg_b p;
           frame_fields p (fs_with_dict (fs_begin fs) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert.
  { match goal with |- semax _ ?P _ _ => forward_loop P continue: (EX ores: option (dstate * Z), EX dm: dict_model,
      PROP (ld_rel b ores; dict_auto_c b ores = Some dm)
      LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
      SEP (zstd_globals gv; pws_pred W; cfg_b p;
           frame_fields p (fs_with_dict (fs_begin fs) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert break: (EX ores: option (dstate * Z), EX dm: dict_model,
      PROP (ld_rel b ores; dict_auto_c b ores = Some dm)
      LOCAL (temp _dctx p; temp _dict dk; temp _dictSize (Vlong (Int64.repr (Zlength b))); gvars gv)
      SEP (zstd_globals gv; pws_pred W; cfg_b p;
           frame_fields p (fs_with_dict (fs_begin fs) (offset_val (Zlength b - Zlength (dm_content dm)) dk)
                             (offset_val (Zlength b) dk) 0 (dm_id dm));
           EX x2: bool, tabs_def gv p None (mk_tstate (dm_state dm) x2 lxb);
           data_at shk (tarray tuchar (Zlength b)) (zbytes b) dk))%assert end.
    { entailer!. }
    { forward_call (gv, p, fs, shk, dk, b, lxb).
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

Lemma body_dict_ins :
  body_ok DICT_G ZSTD_refDictContent_spec /\
  body_ok DICT_G ZSTD_decompress_insertDictionary_spec.
Proof. split; [exact body_refDictContent | exact body_insertDictionary]. Qed.
