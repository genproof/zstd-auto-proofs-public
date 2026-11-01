(* ZSTD_loadEntropy_intoDDict, ZSTD_initDDict_internal *)
Require Export Zstd.proof.dec.B.dict.DictSpecs.
Local Open Scope logic.

(* ---------- the entropy field of a DDict: its six fields ---------- *)

Lemma di_ent_split (q: val):
  field_at_ Ews t_ddict (DOT _entropy) q =
  field_at_ Ews t_ddict (DOT _entropy DOT _LLTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _OFTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _MLTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _hufTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _rep) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q.
Proof.
  unfold field_at_. unfold_field_at 1%nat. apply pred_ext; cancel.
Qed.

Lemma di_ent_huf (q: val): ent_huf (dd_ent q) = field_address t_ddict (DOT _entropy DOT _hufTable) q.
Proof.
  unfold ent_huf, dd_ent.
  change [StructField _hufTable; StructField _entropy] with ([StructField _hufTable] ++ [StructField _entropy]). rewrite field_address_app.
  reflexivity.
Qed.

Lemma di_ent_seq (k: seqkind) (q: val):
  ent_seq k (dd_ent q) = field_address t_ddict (DOT _entropy DOT sk_tfield k) q.
Proof.
  unfold ent_seq, dd_ent.
  change [StructField (sk_tfield k); StructField _entropy] with ([StructField (sk_tfield k)] ++ [StructField _entropy]). rewrite field_address_app.
  reflexivity.
Qed.

Lemma di_fa_rep (q: val):
  field_at_ Ews t_entropy (DOT _rep) (dd_ent q) = field_at_ Ews t_ddict (DOT _entropy DOT _rep) q.
Proof.
  unfold field_at_, dd_ent. change (DOT _entropy DOT _rep)%gfield with ((DOT _rep)%gfield ++ (DOT _entropy)%gfield).
  erewrite field_at_app. reflexivity. apply JMeq_refl.
Qed.

Lemma di_fa_ws (q: val):
  field_at_ Ews t_entropy (DOT _workspace) (dd_ent q) =
  field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q.
Proof.
  unfold field_at_, dd_ent. change (DOT _entropy DOT _workspace)%gfield with ((DOT _workspace)%gfield ++ (DOT _entropy)%gfield).
  erewrite field_at_app. reflexivity. apply JMeq_refl.
Qed.

(* ---------- the Huffman header: hufTable[0] = 12 * 0x1000001, forgotten ---------- *)

Lemma di_hufhdr_forget (p: val):
  field_compatible (tarray tuint 4097) [] p ->
  hufhdr_at Ews p |-- data_at_ Ews (tarray tuint 4097) p.
Proof.
  intros FC. unfold hufhdr_at, HUF_CELLBYTES. Intros ty lg res.
  sep_apply (data_at_memory_block Ews t_dtdesc). change (sizeof t_dtdesc) with 4.
  destruct (proj1 (field_compatible_Tarray_split tuint 1 4097 p ltac:(lia)) FC) as [FC1 FC2].
  unfold data_at_, field_at_. fold (data_at Ews (tarray tuint 4097) (default_val (tarray tuint 4097)) p).
  change (default_val (tarray tuint 4097)) with (Zrepeat Vundef 4097).
  replace (Zrepeat Vundef 4097) with ([Vundef] ++ Zrepeat Vundef (4097 - 1)) by list_solve.
  change (field_at Ews (tarray tuint 4097) [] (default_val (nested_field_type (tarray tuint 4097) [])) p)
    with (data_at Ews (tarray tuint 4097) ([Vundef] ++ Zrepeat Vundef (4097 - 1)) p).
  rewrite (split2_data_at_Tarray_app 1 4097) by list_solve.
  rewrite field_address0_offset in * by auto with field_compatible.
  change (offset_val (nested_field_offset (tarray tuint 4097) (SUB 1)) p) with (offset_val 4 p) in *.
  change (data_at Ews (tarray tuint 1) [Vundef] p) with (data_at_ Ews (tarray tuint 1) p).
  change (data_at Ews (tarray tuint (4097-1)) (Zrepeat Vundef (4097 - 1)) (offset_val 4 p))
    with (data_at_ Ews (tarray tuint (4097-1)) (offset_val 4 p)).
  rewrite <- !memory_block_data_at_ by auto.
  change (sizeof (tarray tuint 1)) with 4. change (sizeof (tarray tuint (4097 - 1))) with 16384.
  cancel.
Qed.

(* hufTable[0] = 12 * 0x1000001 as a U32: the descriptor {12, 0, 0, 12} *)
Lemma di_huf_hdr (q: val):
  field_at Ews t_ddict (DOT _entropy DOT _hufTable)
    (upd_Znth 0 (default_val (tarray tuint 4097)) (Vint (Int.mul (Int.repr 12) (Int.repr 16777217)))) q
  |-- hufhdr_at Ews (field_address t_ddict (DOT _entropy DOT _hufTable) q).
Proof.
  unfold hufhdr_at.
  rewrite field_at_data_at. simpl nested_field_type.
  set (p := field_address t_ddict (DOT _entropy DOT _hufTable) q).
  assert_PROP (field_compatible (tarray tuint 4097) [] p) as FC
    by (eapply derives_trans; [apply data_at_local_facts | apply prop_derives; tauto]).
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
  assert (FCu: field_compatible tuint [] p).
  { assert (H0: field_compatible (tarray tuint 4097) (SUB 0) p) by auto with field_compatible.
    apply field_compatible_nested_field in H0. simpl in H0.
    rewrite isptr_offset_val_zero in H0 by auto with field_compatible. exact H0. }
  rewrite <- (data_at_int_bytes eq_refl) by exact FCu.
  assert (FCd: field_compatible t_dtdesc [] p).
  { destruct FCu as (Hp & Hl & Hs & Ha & Hn). red. repeat split; auto.
    destruct p; try contradiction. red. eapply align_compatible_rec_Tstruct; [reflexivity|reflexivity|].
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

Lemma di_fc_path (q: val) (gfs: list gfield):
  field_compatible t_ddict nil q -> legal_nested_field t_ddict gfs -> field_compatible t_ddict gfs q.
Proof.
  intros (? & ? & ? & ? & ?) ?. repeat split; auto.
Qed.

(* the tables before ZSTD_loadDEntropy, from the struct's fields *)
Lemma di_blank_make (q: val):
  field_compatible t_ddict nil q ->
  hufhdr_at Ews (field_address t_ddict (DOT _entropy DOT _hufTable) q) *
  field_at_ Ews t_ddict (DOT _entropy DOT _LLTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _OFTable) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _MLTable) q
  |-- ent_blank (dd_ent q).
Proof.
  intros FC. unfold ent_blank, seqspace_at. rewrite di_ent_huf, !di_ent_seq. simpl sk_tfield.
  rewrite !field_at__data_at_. simpl nested_field_type. simpl sk_size. cancel.
Qed.

(* ... and back: the whole entropy field, anything *)
Lemma di_blank_forget (q: val):
  field_compatible t_ddict nil q ->
  ent_blank (dd_ent q) * field_at_ Ews t_ddict (DOT _entropy DOT _rep) q *
  field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q
  |-- field_at_ Ews t_ddict (DOT _entropy) q.
Proof.
  intros FC. unfold ent_blank, seqspace_at. rewrite di_ent_huf, !di_ent_seq. simpl sk_tfield.
  assert (FCh: field_compatible t_ddict (DOT _entropy DOT _hufTable) q)
    by (apply di_fc_path; auto; compute; intuition).
  sep_apply (di_hufhdr_forget (field_address t_ddict (DOT _entropy DOT _hufTable) q)).
  { pose proof FCh as FCh'. apply field_compatible_nested_field in FCh'.
    rewrite field_compatible_field_address by auto. exact FCh'. }
  rewrite di_ent_split.
  rewrite (field_at__data_at_ Ews t_ddict (DOT _entropy DOT _LLTable)).
  rewrite (field_at__data_at_ Ews t_ddict (DOT _entropy DOT _OFTable)).
  rewrite (field_at__data_at_ Ews t_ddict (DOT _entropy DOT _MLTable)).
  rewrite (field_at__data_at_ Ews t_ddict (DOT _entropy DOT _hufTable)).
  simpl nested_field_type. simpl sk_size. cancel.
Qed.

(* after a successful ZSTD_loadDEntropy *)
Lemma di_full_dent (gv: globals) (q: val) (st: dstate):
  dstate_ok st -> ent_full (dd_ent q) st |-- dent_def gv q (Some st).
Proof.
  intros Hok. unfold ent_full, dent_def.
  destruct (st_huf st) as [ht|]; [| apply FF_left].
  destruct (st_seq st) as [[[a b] c]|]; [| apply FF_left].
  rewrite di_ent_huf, !di_ent_seq, di_fa_ws.
  unfold dd_ent. change (DOT _entropy DOT _rep)%gfield with ((DOT _rep)%gfield ++ (DOT _entropy)%gfield).
  erewrite (field_at_app Ews t_ddict (DOT _rep) (DOT _entropy)) by apply JMeq_refl.
  unfold dd_huf, dd_seq. entailer!.
Qed.

(* ---------- model facts ---------- *)

Lemma di_le_value_bound (bs: list Z): Forall is_byte bs -> 0 <= le_value bs < 2 ^ (8 * Zlength bs).
Proof.
  intros H. induction H as [|x l Hx H IH]; cbn [le_value].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. rewrite <- Z.add_1_r, Z.mul_add_distr_l, Z.mul_1_r.
    rewrite Z.pow_add_r by (pose proof (Zlength_nonneg l); lia).
    red in Hx. change (2^8) with 256. nia.
Qed.

Lemma di_le_field4 (b: list Z) (i: Z): bytes_ok b -> 0 <= le_field b i 4 < 2 ^ 32.
Proof.
  intros Hb. unfold le_field, slice.
  assert (Hf: Forall is_byte (firstn (Z.to_nat 4) (skipn (Z.to_nat i) b))).
  { apply Forall_firstn. apply Forall_skipn. exact Hb. }
  pose proof (di_le_value_bound _ Hf) as [H0 H1]. split; [lia|].
  eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; [lia|].
  rewrite Zlength_correct, firstn_length. lia.
Qed.

Lemma di_load_size (b: list Z) (st: dstate) (es: Z):
  load_dentropy b = Some (st, es) -> es <= Zlength b.
Proof.
  unfold load_dentropy. intros H.
  repeat match type of H with
  | context [if ?c then _ else _] => destruct c eqn:?; [try discriminate|]
  | context [match ?x with _ => _ end] => destruct x eqn:?; try discriminate
  end.
  all: try discriminate.
  inversion H; subst.
  match goal with Hb: (_ + 12 >? Zlength b) = false |- _ => rewrite Z.gtb_ltb, Z.ltb_ge in Hb; exact Hb end.
Qed.

Lemma di_small (b: list Z):
  Zlength b < 8 -> dict_auto b = Some (dict_raw b) /\ dict_id_of b = 0 /\ ddict_ent b false = None.
Proof.
  intros Hl. unfold dict_auto, dict_id_of, ddict_ent, is_formatted.
  replace (Zlength b <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (8 <=? Zlength b) with false by (symmetry; apply Z.leb_gt; lia).
  auto.
Qed.

Lemma di_nomagic (b: list Z):
  8 <= Zlength b -> le_field b 0 4 <> ZSTD_MAGIC_DICTIONARY ->
  dict_auto b = Some (dict_raw b) /\ dict_id_of b = 0 /\ ddict_ent b false = None.
Proof.
  intros Hl Hm. unfold dict_auto, dict_id_of, ddict_ent, is_formatted.
  replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (8 <=? Zlength b) with true by (symmetry; apply Z.leb_le; lia).
  replace (le_field b 0 4 =? ZSTD_MAGIC_DICTIONARY) with false by (symmetry; apply Z.eqb_neq; auto).
  auto.
Qed.

Lemma di_magic (b: list Z):
  8 <= Zlength b -> le_field b 0 4 = ZSTD_MAGIC_DICTIONARY ->
  dict_id_of b = le_field b 4 4 /\
  dict_auto b = match load_dentropy b with
                | None => None
                | Some (st, esize) =>
                    Some {| dm_content := skipn (Z.to_nat esize) b; dm_id := le_field b 4 4; dm_state := st |}
                end /\
  ddict_ent b false = match load_dentropy b with Some (st, _) => Some st | None => None end.
Proof.
  intros Hl Hm. unfold dict_auto, dict_id_of, ddict_ent, is_formatted.
  replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (8 <=? Zlength b) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Hm, Z.eqb_refl. auto.
Qed.

Lemma di_magic_c (b: list Z) (ores: option (dstate * Z)):
  8 <= Zlength b -> le_field b 0 4 = ZSTD_MAGIC_DICTIONARY ->
  dict_auto_c b ores = match ores with
                       | None => None
                       | Some (st, esize) =>
                           Some {| dm_content := skipn (Z.to_nat esize) b; dm_id := le_field b 4 4; dm_state := st |}
                       end /\
  ddict_ent_c b false ores = match ores with Some (st, _) => Some st | None => None end.
Proof.
  intros Hl Hm. unfold dict_auto_c, ddict_ent_c, is_formatted.
  replace (Zlength b <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (8 <=? Zlength b) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Hm, Z.eqb_refl. auto.
Qed.

(* the loops of zstd's error macros: do { } while (0), do { if (0) _force_has_format_string(..); } while (0) *)
Ltac di_loop0 :=
  match goal with |- semax _ ?Pre _ _ =>
    forward_loop Pre break: Pre; [entailer! | forward; entailer! | ] end.
Ltac di_loop_if :=
  match goal with |- semax _ ?Pre _ _ =>
    forward_loop Pre break: Pre;
    [ entailer!
    | forward_if Pre;
      [ match goal with Hc: ?x <> ?x |- _ => exfalso; apply Hc; reflexivity end
      | forward; entailer!
      | forward; entailer! ]
    | ] end.

Lemma body_load_into : body_ok DICT_G ZSTD_loadEntropy_intoDDict_spec.
Proof.
  exists f_ZSTD_loadEntropy_intoDDict; split; [reflexivity | split; [reflexivity |]].
  start_function.
  assert_PROP (field_compatible t_ddict nil q) as FCq.
  { entailer!. match goal with H: field_compatible t_ddict (DOT _dictContent) q |- _ =>
      destruct H as (? & ? & ? & ? & ?); repeat split; auto end. }
  assert_PROP (isptr buf) as Hbuf by entailer!.
  forward. forward.
  forward_if (ctype = 0).
  { forward. Exists 0 (load_dentropy b). rewrite if_true by auto. simpl.
    sep_apply (di_blank_forget q FCq). entailer!. }
  { forward. entailer!. }
  Intros. subst ctype.
  forward.
  forward_if (8 <= Zlength b).
  { forward_if.
    { exfalso. lia. }
    forward.
    match goal with Hc: Int64.unsigned _ < Int64.unsigned _ |- _ =>
      rewrite !Int64.unsigned_repr in Hc by rep_lia end.
    destruct (di_small b ltac:(lia)) as (E1 & E2 & E3).
    Exists 0 (load_dentropy b). change (0 =? 1) with false.
    rewrite dict_auto_c_exact, ddict_ent_c_exact, E1, E2, E3, if_true by auto. unfold dent_def.
    sep_apply (di_blank_forget q FCq). entailer!. }
  { forward. entailer!.
    match goal with Hc: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
      rewrite !Int64.unsigned_repr in Hc by rep_lia end. lia. }
  forward.
  forward_call (sh, buf, b, 0).
  { red. split; auto. split; [lia|]. split; [lia|]. apply Forall_sublist. auto. }
  forward.
  pose proof (di_le_field4 b 0 H0) as Hm0.
  forward_if (le_field b 0 4 = ZSTD_MAGIC_DICTIONARY).
  { forward_if.
    { exfalso. lia. }
    forward.
    assert (Hne: le_field b 0 4 <> ZSTD_MAGIC_DICTIONARY).
    { intros Heq. rewrite Heq in *. match goal with Hc: Int.repr _ <> Int.repr _ |- _ => apply Hc end.
      unfold ZSTD_MAGIC_DICTIONARY. apply Int.eqm_samerepr. exists 1. reflexivity. }
    destruct (di_nomagic b ltac:(lia) Hne) as (E1 & E2 & E3).
    Exists 0 (load_dentropy b). change (0 =? 1) with false.
    rewrite dict_auto_c_exact, ddict_ent_c_exact, E1, E2, E3, if_true by auto. unfold dent_def.
    sep_apply (di_blank_forget q FCq). entailer!. }
  { forward. entailer!.
    match goal with Hc: Int.repr _ = Int.repr _ |- _ =>
      apply (f_equal Int.unsigned) in Hc; rewrite Int.unsigned_repr in Hc by rep_lia; rewrite Hc; reflexivity end. }
  forward.
  forward_call (sh, buf, b, 4).
  { red. split; auto. split; [lia|]. split; [lia|]. apply Forall_sublist. auto. }
  forward.
  destruct (di_magic b ltac:(lia) H3) as (E1 & _ & _).
  rewrite <- di_fa_rep, <- di_fa_ws.
  match goal with |- semax _ ?Pre _ _ =>
    forward_loop Pre
      continue: (EX st: dstate, EX es: Z,
                 PROP (dstate_ok st; ld_rel b (Some (st, es))) LOCAL (gvars gv; temp _ddict q)
                 SEP (zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) buf q;
                      field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
                      field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (le_field b 4 4))) q;
                      field_at Ews t_ddict (DOT _entropyPresent) (Vint (Int.repr 0)) q;
                      ent_full (dd_ent q) st;
                      data_at sh (tarray tuchar (Zlength b)) (zbytes b) buf))%assert
      break: (EX st: dstate, EX es: Z,
                 PROP (dstate_ok st; ld_rel b (Some (st, es))) LOCAL (gvars gv; temp _ddict q)
                 SEP (zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) buf q;
                      field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
                      field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (le_field b 4 4))) q;
                      field_at Ews t_ddict (DOT _entropyPresent) (Vint (Int.repr 0)) q;
                      ent_full (dd_ent q) st;
                      data_at sh (tarray tuchar (Zlength b)) (zbytes b) buf))%assert end.
  + entailer!.
  + forward. forward.
    forward_call (gv, dd_ent q, sh, buf, b).
    { entailer!. unfold dd_ent. simpl.
      rewrite field_compatible_field_address by (apply di_fc_path; auto; compute; intuition).
      reflexivity. }
    Intros vret. destruct vret as [r [[st es]|]]; Intros; cbn [fst snd] in *.
    * match goal with Hc: _ /\ _ /\ _ |- _ => destruct Hc as (? & Hok & Hes); subst r end.
      forward_call es.
      replace (is_error_code es) with false by (symmetry; unfold is_error_code; apply Z.ltb_ge; rep_lia).
      forward_if.
      { exfalso. auto. }
      forward. Exists st es. entailer!.
    * forward_call r.
      match goal with Hc: is_error_code r = true |- _ => rewrite Hc end.
      forward_if.
      2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
      di_loop0. di_loop_if. di_loop0. di_loop0.
      forward.
      Exists (err_code 30) (@None (dstate * Z)). change (0 =? 1) with false.
      rewrite (proj1 (di_magic_c b None ltac:(lia) H3)).
      rewrite if_false by (unfold err_code; lia).
      assert (Ee: data_at_ Ews t_entropy (dd_ent q) = field_at_ Ews t_ddict (DOT _entropy) q)
        by (rewrite field_at__data_at_; reflexivity).
      rewrite Ee.
      entailer!. unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
  + Intros st es. forward. Exists st es. entailer!.
  + Intros st es. rename H4 into Hok. forward. forward.
    Exists 0 (Some (st, es)). change (0 =? 1) with false.
    destruct (di_magic_c b (Some (st, es)) ltac:(lia) H3) as (E2 & E3).
    rewrite E1, E2, E3, if_true by auto.
    sep_apply (di_full_dent gv q st Hok). entailer!.
Qed.

Lemma di_wvp_test_eq (bk: block) (i: ptrofs):
  weak_valid_pointer (Vptr bk i) |-- denote_tc_test_eq (Vptr bk i) (Vlong Int64.zero).
Proof. Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. entailer!. Opaque denote_tc_test_eq. Qed.

Lemma di_ok_raw (ctype: Z) (b: list Z) (dm: dict_model):
  (if ctype =? 1 then Some (dict_raw b) else dict_auto b) = Some dm ->
  (ctype =? 1) = true \/ dict_auto b <> None.
Proof. destruct (ctype =? 1); auto. intros E. right. congruence. Qed.

Lemma di_err_case (ctype: Z) (b: list Z):
  ctype = 0 \/ ctype = 1 ->
  (if ctype =? 1 then Some (dict_raw b) else dict_auto b) = None ->
  ctype = 0 /\ dict_auto b = None.
Proof.
  intros [-> | ->]; simpl; auto. discriminate.
Qed.

Lemma di_ok_raw_c (ctype: Z) (b: list Z) (ores: option (dstate * Z)) (dm: dict_model):
  (if ctype =? 1 then Some (dict_raw b) else dict_auto_c b ores) = Some dm ->
  (ctype =? 1) = true \/ dict_auto_c b ores <> None.
Proof. destruct (ctype =? 1); auto. intros E. right. congruence. Qed.

Lemma di_err_case_c (ctype: Z) (b: list Z) (ores: option (dstate * Z)):
  ctype = 0 \/ ctype = 1 -> ld_rel b ores ->
  (if ctype =? 1 then Some (dict_raw b) else dict_auto_c b ores) = None ->
  ctype = 0 /\ dict_auto b = None.
Proof.
  intros [-> | ->] HL; simpl; [|discriminate]. intros E. split; [reflexivity|]. exact (ld_rel_auto_none b ores HL E).
Qed.

Lemma body_init_internal : body_ok DICT_G (ZSTD_initDDict_internal_spec dent_def).
Proof.
  exists f_ZSTD_initDDict_internal; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold ddict_fresh. Intros.
  assert_PROP (isptr pk) as Hpk by entailer!.
  assert_PROP (field_compatible t_ddict nil q) as FCq.
  { entailer!. match goal with H: field_compatible _ (DOT _cMem) q |- _ =>
      destruct H as (? & ? & ? & ? & ?); repeat split; auto end. }
  assert (Hw: pws_pred W * data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk |-- weak_valid_pointer pk).
  { sep_apply (data_at_data_at_ sh (tarray tuchar (Zlength b)) (zbytes b) pk).
    unfold buf_ok in H1. sep_apply H1. apply andp_left1. auto. }
  freeze FE := (field_at_ _ _ (DOT _entropy) _).
  freeze FR := (mem_mgr _) (zstd_globals _) (field_at_ _ _ (DOT _dictBuffer) _) (field_at_ _ _ (DOT _dictContent) _)
    (field_at_ _ _ (DOT _dictSize) _) (FRZL FE) (field_at_ _ _ (DOT _dictID) _)
    (field_at_ _ _ (DOT _entropyPresent) _) (field_at _ _ (DOT _cMem) _ _).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if method =? 1 then 1 else 0))) :: Q) (SEPx R))) end.
  { forward. subst method. entailer!. }
  { forward.
    { entailer!. destruct pk; try contradiction. eapply derives_trans; [| apply di_wvp_test_eq].
      apply derives_trans with (pws_pred W * data_at sh (tarray tuchar (Zlength b)) (zbytes b) (Vptr b0 i) * TT);
        [cancel | apply sepcon_weak_valid_pointer1; exact Hw]. }
    entailer!. destruct pk; try contradiction. simpl. rewrite (proj2 (Z.eqb_neq _ _) H5). reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (if orb (method =? 1) (Zlength b =? 0) then 1 else 0)))
                                  :: Q) (SEPx R))) end.
  { forward. entailer!. destruct (method =? 1); [reflexivity | contradiction]. }
  { forward. entailer!.
    destruct (method =? 1) eqn:Em; [discriminate |]. simpl orb.
    destruct (Zlength b =? 0) eqn:Ez.
    - apply Z.eqb_eq in Ez. rewrite Ez. reflexivity.
    - apply Z.eqb_neq in Ez. rewrite Int64.eq_false; [reflexivity|].
      intro Hc. apply Ez. apply (f_equal Int64.unsigned) in Hc.
      rewrite Int64.unsigned_repr in Hc by rep_lia. exact Hc. }
  thaw FR.
  destruct (orb (method =? 1) (Zlength b =? 0)) eqn:Eref.
  - forward_if (PROP () LOCAL (gvars gv; temp _ddict q; temp _dict pk;
                 temp _dictSize (Vlong (Int64.repr (Zlength b))); temp _dictContentType (Vint (Int.repr ctype)))
                SEP (FRZL FE; mem_mgr gv; zstd_globals gv; pws_pred W;
                     field_at Ews t_ddict (DOT _dictBuffer) nullval q; field_at Ews t_ddict (DOT _dictContent) pk q;
                     field_at_ Ews t_ddict (DOT _dictSize) q; field_at_ Ews t_ddict (DOT _dictID) q;
                     field_at_ Ews t_ddict (DOT _entropyPresent) q; field_at Ews t_ddict (DOT _cMem) cmem_null q;
                     data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk)).
    2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
    forward. forward.
    freeze FR2 := (FRZL FE) (mem_mgr _) (zstd_globals _) (field_at _ _ (DOT _dictBuffer) _ _)
      (field_at _ _ (DOT _dictContent) _ _) (field_at_ _ _ (DOT _dictSize) _) (field_at_ _ _ (DOT _dictID) _)
      (field_at_ _ _ (DOT _entropyPresent) _) (field_at _ _ (DOT _cMem) _ _).
    forward_if.
    { entailer!. destruct pk; try contradiction. eapply derives_trans; [| apply di_wvp_test_eq].
      apply derives_trans with (pws_pred W * data_at sh (tarray tuchar (Zlength b)) (zbytes b) (Vptr b0 i) * TT);
        [cancel | apply sepcon_weak_valid_pointer1; exact Hw]. }
    { destruct pk; try contradiction; discriminate. }
    forward. thaw FR2. entailer!.
    forward.
    thaw FE. rewrite di_ent_split. Intros.
    forward.
    sep_apply (di_huf_hdr q). sep_apply (di_blank_make q FCq).
    freeze FX := (mem_mgr _) (pws_pred _) (field_at _ _ (DOT _dictBuffer) _ _) (field_at _ _ (DOT _cMem) _ _).
    forward_loop (PROP () LOCAL (gvars gv; temp _ddict q; temp _dictContentType (Vint (Int.repr ctype))) SEP (FRZL FX; zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
           ent_blank (dd_ent q);
           field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
           data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))
        continue: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))%assert
        break: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk))%assert.
      * entailer!.
      * forward_call (gv, q, sh, pk, b, ctype).
        Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. Intros.
        match goal with Hc: match (if ctype =? 1 then _ else _) with _ => _ end |- _ => rename Hc into Hr end.
        destruct (if ctype =? 1 then Some (dict_raw b) else dict_auto_c b ores) as [dm|] eqn:Eok;
          try rewrite Eok in Hr; subst r.
        + rewrite if_true by auto. Intros.
          forward_call 0.
          change (is_error_code 0) with false.
          forward_if.
          { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
          forward. Exists ores. pose proof (di_ok_raw_c ctype b ores dm Eok). entailer!.
        + rewrite if_false by (unfold err_code; lia). Intros.
          forward_call (err_code 30).
          { unfold err_code; rep_lia. }
          change (is_error_code (err_code 30)) with true.
          forward_if.
          2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
          di_loop0. di_loop_if. di_loop0. di_loop0.
          forward.
          Exists (err_code 30) ores. rewrite if_false by (unfold err_code; lia).
          unfold ddict_failed. Exists nullval. rewrite if_true by auto. thaw FX.
          destruct (di_err_case_c ctype b ores H3 ltac:(assumption) Eok) as [Ec Ea].
          entailer!.
          all: try (unfold err_code; rep_lia).
      * Intros ores. forward. Exists ores. entailer!.
      * Intros ores. forward. Exists 0 ores. rewrite if_true by auto.
        unfold ddx_of, ddict_struct, ddx_copied, ddx_ent. simpl dx_q; simpl dx_bytes; simpl dx_ref; simpl dx_raw; simpl dx_ld.
        rewrite Eref. Exists pk. thaw FX.
        entailer!.
  - assert (Hm0: method = 0) by (destruct H2; subst; auto; discriminate).
    assert (Hb0: 0 < Zlength b).
    { subst method. simpl in Eref. apply Z.eqb_neq in Eref. pose proof (Zlength_nonneg b). lia. }
    subst method.
    forward_if (EX ib: val,
                PROP (isptr ib) LOCAL (gvars gv; temp _ddict q; temp _dict pk;
                 temp _dictSize (Vlong (Int64.repr (Zlength b))); temp _dictContentType (Vint (Int.repr ctype)))
                SEP (FRZL FE; mem_mgr gv; zstd_globals gv; pws_pred W;
                     field_at Ews t_ddict (DOT _dictBuffer) ib q; field_at Ews t_ddict (DOT _dictContent) ib q;
                     field_at_ Ews t_ddict (DOT _dictSize) q; field_at_ Ews t_ddict (DOT _dictID) q;
                     field_at_ Ews t_ddict (DOT _entropyPresent) q; field_at Ews t_ddict (DOT _cMem) cmem_null q;
                     data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk;
                     malloc_token Ews (tarray tuchar (Zlength b)) ib;
                     data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert.
    { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
    {
    assert (Ecm: data_at Ews t_cmem cmem_null (field_address t_ddict (DOT _cMem) q) =
                 field_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) cmem_null q)
      by (rewrite field_at_data_at; reflexivity).
    rewrite <- Ecm.
    forward_call (gv, tarray tuchar (Zlength b), Ews, field_address t_ddict (DOT _cMem) q).
    all: try (simpl sizeof; rewrite Z.max_r by lia; rep_lia).
    Intros ib.
    forward. forward.
    destruct (eq_dec ib nullval) as [Eib | Nib].
    + subst ib.
      forward_if (PROP (False) LOCAL () SEP ()).
      * forward. Exists (err_code 64) (load_dentropy b). pose proof (ld_rel_exact b). rewrite if_false by (unfold err_code; lia).
        unfold ddict_failed. Exists nullval. rewrite if_true by auto. thaw FE.
        rewrite Ecm.
        entailer!.
        split; [unfold err_code; rep_lia |].
        unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
      * exfalso. match goal with Hc: Int64.zero <> Int64.zero |- _ => apply Hc; reflexivity end.
    + Intros.
      assert_PROP (isptr ib) as Hib by entailer!.
      freeze FR4 := (field_at_ _ _ (DOT _dictID) _) (field_at_ _ _ (DOT _entropyPresent) _) (pws_pred _)
        (data_at sh _ _ pk).
      freeze FR3 := (mem_mgr _) (data_at _ t_cmem _ _) (zstd_globals _) (field_at _ _ (DOT _dictBuffer) _ _)
        (field_at _ _ (DOT _dictContent) _ _) (field_at_ _ _ (DOT _dictSize) _) (FRZL FE) (FRZL FR4).
      match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx Q (SEPx R))) end.
      { exfalso. destruct ib; try contradiction. }
      { forward. entailer!. }
      thaw FR3. thaw FR4.
      forward_call (sh, Ews, pk, ib, existT (fun t => reptype t) (tarray tuchar (Zlength b)) (zbytes b)).
      { cbn [projT1 projT2]. split; [simpl sizeof; rewrite Z.max_r by lia; rep_lia |].
        apply memcpy_ok_zbytes; [reflexivity | assumption]. }
      simpl projT1; simpl projT2.
      Exists ib. rewrite Ecm. entailer!. }
    Intros ib.
    forward.
    thaw FE. rewrite di_ent_split. Intros.
    forward.
    sep_apply (di_huf_hdr q). sep_apply (di_blank_make q FCq).
    freeze FX := (mem_mgr _) (pws_pred _) (field_at _ _ (DOT _dictBuffer) _ _) (field_at _ _ (DOT _cMem) _ _)
      (data_at sh _ _ pk) (malloc_token _ _ ib).
    forward_loop (PROP () LOCAL (gvars gv; temp _ddict q; temp _dictContentType (Vint (Int.repr ctype))) SEP (FRZL FX; zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
           ent_blank (dd_ent q);
           field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))
        continue: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert
        break: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert.
      * entailer!.
      * forward_call (gv, q, Ews, ib, b, ctype).
        Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. Intros.
        match goal with Hc: match (if ctype =? 1 then _ else _) with _ => _ end |- _ => rename Hc into Hr end.
        destruct (if ctype =? 1 then Some (dict_raw b) else dict_auto_c b ores) as [dm|] eqn:Eok;
          try rewrite Eok in Hr; subst r.
        + rewrite if_true by auto. Intros.
          forward_call 0.
          change (is_error_code 0) with false.
          forward_if.
          { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
          forward. Exists ores. pose proof (di_ok_raw_c ctype b ores dm Eok). entailer!.
        + rewrite if_false by (unfold err_code; lia). Intros.
          forward_call (err_code 30).
          { unfold err_code; rep_lia. }
          change (is_error_code (err_code 30)) with true.
          forward_if.
          2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
          di_loop0. di_loop_if. di_loop0. di_loop0.
          forward.
          Exists (err_code 30) ores. rewrite if_false by (unfold err_code; lia).
          unfold ddict_failed. Exists ib. rewrite if_false by (destruct ib; try contradiction; discriminate). thaw FX.
          sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength b)) (zbytes b) ib).
          destruct (di_err_case_c ctype b ores H3 ltac:(assumption) Eok) as [Ec Ea].
          entailer!.
          all: try (unfold err_code; rep_lia).
      * Intros ores. forward. Exists ores. entailer!.
      * Intros ores. forward. Exists 0 ores. rewrite if_true by auto.
        unfold ddx_of, ddict_struct, ddx_copied, ddx_ent. simpl dx_q; simpl dx_bytes; simpl dx_ref; simpl dx_raw; simpl dx_ld.
        replace (Zlength b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        Exists ib. thaw FX.
        entailer!.
Qed.

Lemma body_dict_init : body_ok DICT_G ZSTD_loadEntropy_intoDDict_spec.
Proof. exact body_load_into. Qed.
