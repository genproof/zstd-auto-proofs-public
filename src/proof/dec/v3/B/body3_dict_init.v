(* API v3, subtree B, group DICT: ZSTD_loadEntropy_intoDDict and
   ZSTD_initDDict_internal with ZSTD_dct_fullDict (ctype 2) (v2: B/dict/body_dict_init.v). *)
Require Export Zstd.proof.dec.v3.B.BSpecs3.
Require Import Zstd.proof.dec.B.dict.body_dict_init.
Local Open Scope logic.

(* the bodies for an allocator class: ZSTD_initDDict_internal's copy goes through the DDict's allocator *)
Section DI3.
Context {CMI: cmem_preds}.

(* ---------- the result selector of ZSTD_loadEntropy_intoDDict_spec3 ---------- *)

Definition di3_sel (ctype: Z) (b: list Z) (ores: option (dstate * Z)) : option dict_model :=
  if ctype =? 1 then Some (dict_raw b)
  else if andb (ctype =? 2) (negb (dict_formatted b)) then None
  else dict_auto_c b ores.

Lemma di3_fmt_small (b: list Z): Zlength b < 8 -> dict_formatted b = false.
Proof. intros H. unfold dict_formatted. replace (8 <=? Zlength b) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma di3_fmt_nomagic (b: list Z): le_field b 0 4 <> ZSTD_MAGIC_DICTIONARY -> dict_formatted b = false.
Proof. intros H. unfold dict_formatted. rewrite (proj2 (Z.eqb_neq _ _) H). apply andb_false_r. Qed.

Lemma di3_fmt_magic (b: list Z):
  8 <= Zlength b -> le_field b 0 4 = ZSTD_MAGIC_DICTIONARY -> dict_formatted b = true.
Proof.
  intros H1 H2. unfold dict_formatted. rewrite H2, Z.eqb_refl.
  replace (8 <=? Zlength b) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma di3_sel_0 (b: list Z) (ores: option (dstate * Z)): di3_sel 0 b ores = dict_auto_c b ores.
Proof. reflexivity. Qed.

Lemma di3_sel_fmt (ctype: Z) (b: list Z) (ores: option (dstate * Z)):
  ctype = 0 \/ ctype = 2 -> dict_formatted b = true -> di3_sel ctype b ores = dict_auto_c b ores.
Proof. intros [-> | ->] Hf; unfold di3_sel; rewrite ?Hf; reflexivity. Qed.

Lemma di3_sel_2 (b: list Z) (ores: option (dstate * Z)):
  dict_formatted b = false -> di3_sel 2 b ores = None.
Proof. intros Hf. unfold di3_sel. rewrite Hf. reflexivity. Qed.

Lemma di3_n1 (ctype: Z): ctype = 0 \/ ctype = 2 -> (ctype =? 1) = false.
Proof. intros [-> | ->]; reflexivity. Qed.

Lemma body3_load_into : body_ok DICT3_G ZSTD_loadEntropy_intoDDict_spec3.
Proof.
  exists f_ZSTD_loadEntropy_intoDDict; split; [reflexivity | split; [reflexivity |]].
  start_function.
  assert_PROP (field_compatible t_ddict nil q) as FCq.
  { entailer!. match goal with H: field_compatible t_ddict (DOT _dictContent) q |- _ =>
      destruct H as (? & ? & ? & ? & ?); repeat split; auto end. }
  match goal with Hn: buf = nullval -> b = nil |- _ => rename Hn into Hbnil end.
  forward. forward.
  forward_if (ctype = 0 \/ ctype = 2).
  { forward. Exists 0 (load_dentropy b). rewrite if_true by auto. simpl.
    sep_apply (di_blank_forget q FCq). entailer!. }
  { forward. entailer!. }
  Intros. rename H2 into Hc02.
  forward.
  forward_if (8 <= Zlength b).
  { forward_if.
    { forward.
      Exists (err_code 30) (load_dentropy b).
      fold (di3_sel 2 b (load_dentropy b)).
      rewrite !Int64.unsigned_repr in H2 by rep_lia.
      rewrite di3_sel_2 by (apply di3_fmt_small; lia).
      rewrite if_false by (unfold err_code; lia).
      sep_apply (di_blank_forget q FCq). pose proof (ld_rel_exact b).
      entailer!. unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    assert (ctype = 0) by lia. subst ctype.
    forward.
    rewrite !Int64.unsigned_repr in H2 by rep_lia.
    destruct (di_small b ltac:(lia)) as (E1 & E2 & E3).
    Exists 0 (load_dentropy b). change (0 =? 1) with false. change (0 =? 2) with false. simpl andb.
    rewrite dict_auto_c_exact, ddict_ent_c_exact, E1, E2, E3, if_true by auto. unfold dent_def.
    sep_apply (di_blank_forget q FCq). entailer!. }
  { forward. entailer!.
    match goal with Hc: Int64.unsigned _ >= Int64.unsigned _ |- _ =>
      rewrite !Int64.unsigned_repr in Hc by rep_lia end. lia. }
  (* at least 8 bytes: the content is at a pointer *)
  assert_PROP (8 <= Zlength b) as H8 by entailer!.
  assert (Hbn: buf <> nullval).
  { intros E. specialize (Hbnil E). subst b. rewrite Zlength_nil in H8. lia. }
  unfold bytes_at. rewrite if_false by exact Hbn.
  assert_PROP (isptr buf) as Hbuf by entailer!.
  forward.
  forward_call (sh, buf, b, 0).
  { red. split; auto. split; [lia|]. split; [lia|]. apply Forall_sublist. auto. }
  forward.
  pose proof (di_le_field4 b 0 H0) as Hm0.
  forward_if (le_field b 0 4 = ZSTD_MAGIC_DICTIONARY).
  { assert (Hne: le_field b 0 4 <> ZSTD_MAGIC_DICTIONARY).
    { intros Heq. rewrite Heq in *. match goal with Hc: Int.repr _ <> Int.repr _ |- _ => apply Hc end.
      unfold ZSTD_MAGIC_DICTIONARY. apply Int.eqm_samerepr. exists 1. reflexivity. }
    forward_if.
    { forward.
      Exists (err_code 30) (load_dentropy b).
      fold (di3_sel 2 b (load_dentropy b)).
      rewrite di3_sel_2 by (apply di3_fmt_nomagic; auto).
      rewrite if_false by (unfold err_code; lia).
      sep_apply (di_blank_forget q FCq). pose proof (ld_rel_exact b).
      rewrite (bytes_at_ptr sh b buf Hbuf). entailer!. unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity. }
    assert (ctype = 0) by lia. subst ctype.
    forward.
    destruct (di_nomagic b ltac:(lia) Hne) as (E1 & E2 & E3).
    Exists 0 (load_dentropy b). change (0 =? 1) with false. change (0 =? 2) with false. simpl andb.
    rewrite dict_auto_c_exact, ddict_ent_c_exact, E1, E2, E3, if_true by auto. unfold dent_def.
    sep_apply (di_blank_forget q FCq). rewrite (bytes_at_ptr sh b buf Hbuf). entailer!. }
  { forward. entailer!.
    match goal with Hc: Int.repr _ = Int.repr _ |- _ =>
      apply (f_equal Int.unsigned) in Hc; rewrite Int.unsigned_repr in Hc by rep_lia; rewrite Hc; reflexivity end. }
  forward.
  forward_call (sh, buf, b, 4).
  { red. split; auto. split; [lia|]. split; [lia|]. apply Forall_sublist. auto. }
  forward.
  match goal with Hm: le_field b 0 4 = ZSTD_MAGIC_DICTIONARY |- _ => rename Hm into Hmg end.
  assert (Hf: dict_formatted b = true) by (apply di3_fmt_magic; auto; lia).
  destruct (di_magic b ltac:(lia) Hmg) as (E1 & _ & _).
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
      Exists (err_code 30) (@None (dstate * Z)).
      fold (di3_sel ctype b None). rewrite (di3_sel_fmt ctype b None Hc02 Hf).
      rewrite (proj1 (di_magic_c b None ltac:(lia) Hmg)).
      rewrite if_false by (unfold err_code; lia).
      assert (Ee: data_at_ Ews t_entropy (dd_ent q) = field_at_ Ews t_ddict (DOT _entropy) q)
        by (rewrite field_at__data_at_; reflexivity).
      rewrite Ee.
      rewrite (bytes_at_ptr sh b buf Hbuf). entailer!. unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
  + Intros st es. forward. Exists st es. entailer!.
  + Intros st es. match goal with Hd: dstate_ok st |- _ => rename Hd into Hok end. forward. forward.
    Exists 0 (Some (st, es)).
    fold (di3_sel ctype b (Some (st, es))). rewrite (di3_sel_fmt ctype b _ Hc02 Hf), (di3_n1 ctype Hc02).
    destruct (di_magic_c b (Some (st, es)) ltac:(lia) Hmg) as (E2 & E3).
    rewrite E1, E2, E3, if_true by auto.
    sep_apply (di_full_dent gv q st Hok). rewrite (bytes_at_ptr sh b buf Hbuf). entailer!.
Qed.

Lemma di3_ok (ctype: Z) (b: list Z) (ores: option (dstate * Z)) (dm: dict_model):
  di3_sel ctype b ores = Some dm ->
  ((ctype =? 1) = true \/ dict_auto_c b ores <> None) /\ (ctype = 2 -> dict_formatted b = true).
Proof.
  unfold di3_sel. intros E. destruct (ctype =? 1) eqn:E1.
  - split; auto. intros ->. discriminate.
  - destruct ((ctype =? 2) && negb (dict_formatted b))%bool eqn:E2; [discriminate|].
    split; [right; congruence|]. intros ->. simpl in E2. destruct (dict_formatted b); auto.
Qed.

Lemma di3_err (ctype: Z) (b: list Z) (ores: option (dstate * Z)):
  ctype = 0 \/ ctype = 1 \/ ctype = 2 -> ld_rel b ores -> di3_sel ctype b ores = None ->
  (ctype <> 1 /\ dict_auto b = None) \/ (ctype = 2 /\ dict_formatted b = false).
Proof.
  intros Hc HL. unfold di3_sel. destruct Hc as [-> | [-> | ->]]; simpl.
  - intros E. left. split; [lia|]. exact (ld_rel_auto_none b ores HL E).
  - discriminate.
  - destruct (dict_formatted b) eqn:Ef; simpl.
    + intros E. left. split; [lia|]. exact (ld_rel_auto_none b ores HL E).
    + intros _. right. auto.
Qed.

(* `!dict`: the bytes are NULL or the caller's, whose start is weakly valid (buf_ok) *)
Lemma di3_test_eq_pk (W: list ptr_witness) (sh: share) (b: list Z) (pk: val) (R: mpred) :
  is_pointer_or_null pk ->
  (pws_pred W * bytes_at sh b pk |-- weak_valid_pointer pk) ->
  pws_pred W * bytes_at sh b pk * R |-- denote_tc_test_eq pk (Vlong Int64.zero).
Proof.
  intros Hp Hw. destruct pk; try contradiction.
  - simpl in Hp. subst. Transparent denote_tc_test_eq. unfold denote_tc_test_eq. simpl. Opaque denote_tc_test_eq.
    entailer!.
  - eapply derives_trans; [| apply di_wvp_test_eq]. apply sepcon_weak_valid_pointer1. exact Hw.
Qed.

(* whether the bytes are NULL *)
Definition di3_null (pk: val) : bool := if eq_dec pk nullval then true else false.

Lemma body3_init_internal : body_ok DICT3_G (ZSTD_initDDict_internal_spec3 dent_def).
Proof.
  exists f_ZSTD_initDDict_internal; split; [reflexivity | split; [reflexivity |]].
  start_function.
  unfold ddict_fresh3. Intros.
  match goal with H: is_pointer_or_null pk |- _ => rename H into Hpn end.
  match goal with H: pk = nullval -> b = nil |- _ => rename H into Hnil end.
  match goal with H: pk <> nullval -> buf_ok _ _ _ _ |- _ => rename H into Hbo end.
  match goal with H: method = 0 \/ method = 1 |- _ => rename H into H2 end.
  match goal with H: ctype = 0 \/ ctype = 1 \/ ctype = 2 |- _ => rename H into H3 end.
  assert_PROP (field_compatible t_ddict nil q) as FCq.
  { entailer!. match goal with H: field_compatible _ (DOT _cMem) q |- _ =>
      destruct H as (? & ? & ? & ? & ?); repeat split; auto end. }
  (* the bytes NULL (none) or the caller's at a pointer *)
  assert (Hw: pws_pred W * bytes_at sh b pk |-- weak_valid_pointer pk).
  { destruct (eq_dec pk nullval) as [E|E].
    - subst pk. apply valid_pointer_weak'. apply valid_pointer_zero64; reflexivity.
    - unfold bytes_at. rewrite if_false by exact E.
      sep_apply (data_at_data_at_ sh (tarray tuchar (Zlength b)) (zbytes b) pk).
      specialize (Hbo E). unfold buf_ok in Hbo. sep_apply Hbo. apply andp_left1. auto. }
  freeze FE := (field_at_ _ _ (DOT _entropy) _).
  freeze FR := (mem_mgr _) (zstd_globals _) (field_at_ _ _ (DOT _dictBuffer) _) (field_at_ _ _ (DOT _dictContent) _)
    (field_at_ _ _ (DOT _dictSize) _) (FRZL FE) (field_at_ _ _ (DOT _dictID) _)
    (field_at_ _ _ (DOT _entropyPresent) _) (field_at _ _ (DOT _cMem) _ _).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'2 (Vint (Int.repr (if orb (method =? 1) (di3_null pk) then 1 else 0))) :: Q)
                         (SEPx R))) end.
  { forward. subst method. entailer!. }
  { forward.
    { entailer!. apply derives_trans with (pws_pred W * bytes_at sh b pk * TT); [cancel | apply di3_test_eq_pk; auto]. }
    entailer!. match goal with Hn: method <> 1 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hn) end. simpl orb.
    unfold di3_null. destruct (eq_dec pk nullval) as [E|E]; [subst pk; reflexivity |].
    destruct pk; try contradiction; [simpl in Hpn; subst; exfalso; apply E; reflexivity | reflexivity]. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (if orb (method =? 1) (Zlength b =? 0) then 1 else 0)))
                                  :: Q) (SEPx R))) end.
  { forward. entailer!. destruct (method =? 1); [reflexivity |]. simpl orb in *. unfold di3_null in *.
    destruct (eq_dec pk nullval) as [E|E]; [rewrite (Hnil E); reflexivity | contradiction]. }
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
                     field_at_ Ews t_ddict (DOT _entropyPresent) q; field_at Ews t_ddict (DOT _cMem) (cmem_v am) q;
                     cm_have am h; bytes_at sh b pk)).
    2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
    forward. forward.
    freeze FR2 := (FRZL FE) (mem_mgr _) (zstd_globals _) (field_at _ _ (DOT _dictBuffer) _ _)
      (field_at _ _ (DOT _dictContent) _ _) (field_at_ _ _ (DOT _dictSize) _) (field_at_ _ _ (DOT _dictID) _)
      (field_at_ _ _ (DOT _entropyPresent) _) (field_at _ _ (DOT _cMem) _ _).
    forward_if.
    { entailer!. apply derives_trans with (pws_pred W * bytes_at sh b pk * TT); [cancel | apply di3_test_eq_pk; auto]. }
    { (* dict = NULL (no bytes): dictSize = 0 *)
      assert (E: pk = nullval).
      { destruct pk; try contradiction; [simpl in Hpn; subst; reflexivity | discriminate]. }
      assert (Eb: b = nil) by exact (Hnil E).
      forward. thaw FR2. entailer!; try (rewrite Eb; reflexivity). }
    forward. thaw FR2. entailer!.
    forward.
    thaw FE. rewrite di_ent_split. Intros.
    forward.
    sep_apply (di_huf_hdr q). sep_apply (di_blank_make q FCq).
    freeze FX := (mem_mgr _) (pws_pred _) (field_at _ _ (DOT _dictBuffer) _ _) (field_at _ _ (DOT _cMem) _ _)
      (cm_have _ _).
    forward_loop (PROP () LOCAL (gvars gv; temp _ddict q; temp _dictContentType (Vint (Int.repr ctype))) SEP (FRZL FX; zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
           ent_blank (dd_ent q);
           field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
           bytes_at sh b pk))
        continue: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None; ctype = 2 -> dict_formatted b = true) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           bytes_at sh b pk))%assert
        break: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None; ctype = 2 -> dict_formatted b = true) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) pk q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           bytes_at sh b pk))%assert.
      * entailer!.
      * forward_call (gv, q, sh, pk, b, ctype).
        Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. Intros.
        match goal with Hc: match (if ctype =? 1 then _ else _) with _ => _ end |- _ => rename Hc into Hr end.
        fold (di3_sel ctype b ores) in Hr.
        destruct (di3_sel ctype b ores) as [dm|] eqn:Eok; subst r.
        + rewrite if_true by auto. Intros.
          forward_call 0.
          change (is_error_code 0) with false.
          forward_if.
          { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
          forward. Exists ores. destruct (di3_ok ctype b ores dm Eok). entailer!.
        + rewrite if_false by (unfold err_code; lia). Intros.
          forward_call (err_code 30).
          { unfold err_code; rep_lia. }
          change (is_error_code (err_code 30)) with true.
          forward_if.
          2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
          di_loop0. di_loop_if. di_loop0. di_loop0.
          forward.
          Exists (err_code 30) ores. rewrite if_false by (unfold err_code; lia).
          Exists 0. unfold ddict_failed3. Exists nullval. rewrite !if_true by auto. thaw FX. rewrite Z.add_0_r.
          pose proof (di3_err ctype b ores H3 ltac:(assumption) Eok).
          entailer!.
          split; [unfold err_code; rep_lia | right; split; [reflexivity | tauto]].
      * Intros ores. forward. Exists ores. entailer!.
      * Intros ores. forward. Exists 0 ores. rewrite if_true by auto.
        unfold ddx_of3, ddict_struct, ddx_copied, ddx_ent. simpl dx_q; simpl dx_bytes; simpl dx_ref; simpl dx_raw; simpl dx_ld; simpl dx_mem.
        rewrite Eref. Exists pk. thaw FX. rewrite Z.add_0_r.
        entailer!.
        destruct (eq_dec pk nullval) as [E|E]; [right; rewrite (Hnil E); auto |].
        left. destruct pk; try contradiction; [simpl in Hpn; subst; exfalso; apply E; reflexivity | exact I].
  - assert (Hm0: method = 0) by (destruct H2; subst; auto; discriminate).
    assert (Hb0: 0 < Zlength b).
    { subst method. simpl in Eref. apply Z.eqb_neq in Eref. pose proof (Zlength_nonneg b). lia. }
    subst method.
    (* a copy of at least one byte: the bytes are at a pointer *)
    assert (Epk: pk <> nullval) by (intros E; rewrite (Hnil E), Zlength_nil in Hb0; lia).
    assert (Hpk: isptr pk) by (destruct pk; try contradiction; simpl in Hpn; try subst; try (exfalso; apply Epk; reflexivity); exact I).
    unfold bytes_at. rewrite if_false by exact Epk.
    forward_if (EX ib: val,
                PROP (isptr ib) LOCAL (gvars gv; temp _ddict q; temp _dict pk;
                 temp _dictSize (Vlong (Int64.repr (Zlength b))); temp _dictContentType (Vint (Int.repr ctype)))
                SEP (FRZL FE; mem_mgr gv; zstd_globals gv; pws_pred W;
                     field_at Ews t_ddict (DOT _dictBuffer) ib q; field_at Ews t_ddict (DOT _dictContent) ib q;
                     field_at_ Ews t_ddict (DOT _dictSize) q; field_at_ Ews t_ddict (DOT _dictID) q;
                     field_at_ Ews t_ddict (DOT _entropyPresent) q; field_at Ews t_ddict (DOT _cMem) (cmem_v am) q;
                     data_at sh (tarray tuchar (Zlength b)) (zbytes b) pk;
                     cm_have am (h + Zlength b); blk_tok am (tarray tuchar (Zlength b)) ib;
                     data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert.
    { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
    {
    assert (Ecm: data_at Ews t_cmem3 (cmem_v am) (field_address t_ddict (DOT _cMem) q) =
                 field_at Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _cMem) (cmem_v am) q)
      by (rewrite field_at_data_at; reflexivity).
    rewrite <- Ecm.
    assert (Esz: sizeof (tarray tuchar (Zlength b)) = Zlength b) by (simpl; rewrite Z.max_r by lia; lia).
    forward_call (gv, tarray tuchar (Zlength b), Ews, field_address t_ddict (DOT _cMem) q, am, h).
    all: try (simpl sizeof; rewrite Z.max_r by lia; rep_lia).
    Intros ib.
    forward. forward.
    destruct (eq_dec ib nullval) as [Eib | Nib].
    + subst ib.
      forward_if (PROP (False) LOCAL () SEP ()).
      * forward. Exists (err_code 64) (load_dentropy b). pose proof (ld_rel_exact b). rewrite if_false by (unfold err_code; lia).
        Exists 0. unfold ddict_failed3. Exists nullval. rewrite !if_true by auto. thaw FE. rewrite Z.add_0_r.
        rewrite Ecm. rewrite (bytes_at_ptr sh b pk Hpk).
        entailer!.
        split; [unfold err_code; rep_lia |].
        unfold err_code. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
      * exfalso. match goal with Hc: Int64.zero <> Int64.zero |- _ => apply Hc; reflexivity end.
    + Intros.
      assert_PROP (isptr ib) as Hib by entailer!.
      freeze FR4 := (field_at_ _ _ (DOT _dictID) _) (field_at_ _ _ (DOT _entropyPresent) _) (pws_pred _)
        (data_at sh _ _ pk).
      freeze FR3 := (mem_mgr _) (data_at _ t_cmem3 _ _) (zstd_globals _) (field_at _ _ (DOT _dictBuffer) _ _)
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
      Exists ib. rewrite Ecm, Esz. entailer!. }
    Intros ib.
    forward.
    thaw FE. rewrite di_ent_split. Intros.
    forward.
    sep_apply (di_huf_hdr q). sep_apply (di_blank_make q FCq).
    freeze FX := (mem_mgr _) (pws_pred _) (field_at _ _ (DOT _dictBuffer) _ _) (field_at _ _ (DOT _cMem) _ _)
      (data_at sh _ _ pk) (blk_tok _ _ ib) (cm_have _ _).
    forward_loop (PROP () LOCAL (gvars gv; temp _ddict q; temp _dictContentType (Vint (Int.repr ctype))) SEP (FRZL FX; zstd_globals gv; field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at_ Ews t_ddict (DOT _dictID) q; field_at_ Ews t_ddict (DOT _entropyPresent) q;
           ent_blank (dd_ent q);
           field_at_ Ews t_ddict (DOT _entropy DOT _rep) q; field_at_ Ews t_ddict (DOT _entropy DOT _workspace) q;
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))
        continue: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None; ctype = 2 -> dict_formatted b = true) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert
        break: (EX ores: option (dstate * Z), PROP (ld_rel b ores; (ctype =? 1) = true \/ dict_auto_c b ores <> None; ctype = 2 -> dict_formatted b = true) LOCAL (gvars gv; temp _ddict q) SEP (FRZL FX; zstd_globals gv;
           field_at Ews t_ddict (DOT _dictContent) ib q;
           field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength b))) q;
           field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if ctype =? 1 then 0 else dict_id_of b))) q;
           field_at Ews t_ddict (DOT _entropyPresent)
             (Vint (Int.repr (match ddict_ent_c b (ctype =? 1) ores with Some _ => 1 | None => 0 end))) q;
           dent_def gv q (ddict_ent_c b (ctype =? 1) ores);
           data_at Ews (tarray tuchar (Zlength b)) (zbytes b) ib))%assert.
      * entailer!.
      * assert (Hib2: isptr ib) by assumption.
        rewrite <- (bytes_at_ptr Ews b ib Hib2).
        forward_call (gv, q, Ews, ib, b, ctype).
        Intros vret. destruct vret as [r ores]. cbn [fst snd] in *. Intros.
        rewrite (bytes_at_ptr Ews b ib Hib2).
        match goal with Hc: match (if ctype =? 1 then _ else _) with _ => _ end |- _ => rename Hc into Hr end.
        fold (di3_sel ctype b ores) in Hr.
        destruct (di3_sel ctype b ores) as [dm|] eqn:Eok; subst r.
        + rewrite if_true by auto. Intros.
          forward_call 0.
          change (is_error_code 0) with false.
          forward_if.
          { exfalso. match goal with Hc: Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end. }
          forward. Exists ores. destruct (di3_ok ctype b ores dm Eok). entailer!.
        + rewrite if_false by (unfold err_code; lia). Intros.
          forward_call (err_code 30).
          { unfold err_code; rep_lia. }
          change (is_error_code (err_code 30)) with true.
          forward_if.
          2: { exfalso. match goal with Hc: Int.repr 1 = Int.zero |- _ => inversion Hc end. }
          di_loop0. di_loop_if. di_loop0. di_loop0.
          forward.
          Exists (err_code 30) ores. rewrite if_false by (unfold err_code; lia).
          Exists (Zlength b). unfold ddict_failed3. Exists ib.
          rewrite !if_false by (destruct ib; try contradiction; discriminate). thaw FX.
          sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength b)) (zbytes b) ib).
          pose proof (di3_err ctype b ores H3 ltac:(assumption) Eok).
          rewrite (bytes_at_ptr sh b pk Hpk).
          entailer!.
          split; [unfold err_code; rep_lia | right; split; [reflexivity | tauto]].
      * Intros ores. forward. Exists ores. entailer!.
      * Intros ores. forward. Exists 0 ores. rewrite if_true by auto.
        unfold ddx_of3, ddict_struct, ddx_copied, ddx_ent. simpl dx_q; simpl dx_bytes; simpl dx_ref; simpl dx_raw; simpl dx_ld; simpl dx_mem.
        replace (Zlength b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        Exists ib. thaw FX. rewrite (bytes_at_ptr sh b pk Hpk).
        entailer!.
Qed.

Lemma DICT3_init_ok :
  body_ok DICT3_G ZSTD_loadEntropy_intoDDict_spec3 /\
  body_ok DICT3_G (ZSTD_initDDict_internal_spec3 dent_def).
Proof. exact (conj body3_load_into body3_init_internal). Qed.

End DI3.
