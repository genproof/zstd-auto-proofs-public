(* The harness obligation of harness/any_dict_copy.c under the decoder's API v3:
   for ANY predicates DC, DD of the decoder's API (Spec_api6), specifications of the harness's helpers such that
   every helper and main satisfy them.  The v2 proof adapted: every context state of the run has
   the default parameters, an empty DDict set and no buffer-less frame.  v3.1/v3.2 (the v3 proof
   adapted): DDict states mkdd with createDDict's hidden fields, kept with the DDict's valid_pointer; refDDict's
   empty dict_res/set_res frame on a fresh context; oneshot_dctx with an empty set is oneshot_ok. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_dict_copy.HOK_any_dict_copy.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.harness.ApiAfterKit.

Lemma vars_in_tycontext (l: list (ident * globvar type)) G :
  Forall (fun ig : ident * _ => isSome (Maps.PTree.get (fst ig) (make_tycontext_g (map (fun iv => (fst iv, gvar_info (snd iv))) l) G))) l.
Proof.
  rewrite Forall_forall. intros [i v] Hin. simpl.
  unfold make_tycontext_g.
  induction G as [|[j fs] G IH]; simpl.
  - induction l as [|[k w] l IHl]; simpl in *; [contradiction|].
    rewrite Maps.PTree.gsspec. destruct (peq i k); [exact I|].
    destruct Hin as [E|E]; [inversion E; congruence | auto].
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [exact I | exact IH].
Qed.

Local Ltac expand_main_pre ::= idtac.

Lemma sepcon_emp_fun_ADC (P: environ -> mpred) : (P * (fun _ : environ => emp))%logic = P.
Proof. extensionality rho. simpl. apply sepcon_emp. Qed.

Definition b2i (b: bool) : int := if b then Int.one else Int.zero.

Lemma b2i_nz b : b2i b <> Int.zero -> b = true.
Proof. destruct b; [reflexivity | intros H; exfalso; apply H; reflexivity]. Qed.

Lemma ltu64_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma le64_b2i n c : 0 <= n <= Int64.max_unsigned -> 0 <= c <= Int64.max_unsigned ->
  Int.repr (Z.b2z (negb (Int64.ltu (Int64.repr c) (Int64.repr n)))) = b2i (n <=? c).
Proof.
  intros. rewrite ltu64_Z by lia. unfold b2i.
  destruct (Z.ltb_spec c n), (Z.leb_spec n c); try lia; reflexivity.
Qed.

Ltac if_set_post t v :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end.

Ltac norm :=
  try match goal with H: ?x <> ?x |- _ => exfalso; exact (H eq_refl) end;
  repeat match goal with
  | H: Int64.ltu (Int64.repr ?x) (Int64.repr ?y) = _ |- _ =>
      rewrite ltu64_Z in H by rep_lia;
      first [apply Z.ltb_lt in H | apply Z.ltb_ge in H]
  | H: context [Int64.unsigned (Int64.repr ?x)] |- _ => rewrite (Int64.unsigned_repr x) in H by rep_lia
  | H: context [Int.unsigned (Int.repr ?x)] |- _ => rewrite (Int.unsigned_repr x) in H by rep_lia
  end;
  try (exfalso; lia).

(* byte arrays mean the same at any two compspecs *)
Definition adc_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma adc_data_at_cs: forall (cs1 cs2: compspecs) sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. apply equal_f.
  exact (@data_at_change_composite _ _ (adc_cce cs1 cs2) sh (tarray tuchar n) v v (JMeq_refl v) eq_refl).
Qed.

Lemma adc_data_at__cs: forall (cs1 cs2: compspecs) sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. rewrite (@data_at__change_composite _ _ (adc_cce cs1 cs2)); auto. Qed.

Definition ZCS : compspecs := Zstd.proof.zstd.Base.CompSpecs.

(* the slack bytes [c, max 1 c) of a buffer of max(1,c) bytes: lent to the decoder as a pointer witness *)
Definition rest_w (p: val) (c: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 c - c) (Zrepeat Vundef (Z.max 1 c - c))
    (field_address0 (tarray tuchar (Z.max 1 c)) [ArraySubsc c] p).

(* a malloc'd byte buffer of max(1,c) bytes (NULL: nothing), whose first c bytes hold v *)
Definition buf_res (p: val) (c: Z) (v: list val) : mpred :=
  if eq_dec p nullval then emp else
  (!! field_compatible (tarray tuchar (Z.max 1 c)) [] p &&
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at ZCS Ews (tarray tuchar c) v p *
    pw_pred (rest_w p c)))%logic.

Lemma rest_w_eq p c : pw_pred (rest_w p c) =
  data_at_ Ews (tarray tuchar (Z.max 1 c - c)) (field_address0 (tarray tuchar (Z.max 1 c)) [ArraySubsc c] p).
Proof.
  unfold pw_pred, rest_w. unfold ZCS.
  rewrite (adc_data_at_cs Zstd.proof.zstd.Base.CompSpecs CompSpecs). reflexivity.
Qed.

Lemma malloc_buf p c : 0 <= c ->
  (if eq_dec p nullval then emp else
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * data_at_ Ews (tarray tuchar (Z.max 1 c)) p)%logic)
  |-- buf_res p c (Zrepeat Vundef c).
Proof.
  intros Hc. unfold buf_res. destruct (eq_dec p nullval); [apply derives_refl|].
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 c)) [] p) as Hfc by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Ews (Z.max 1 c) c p) by (auto; try lia; apply Hfc).
  rewrite rest_w_eq. rewrite (adc_data_at_cs ZCS CompSpecs). entailer!.
Qed.

Lemma buf_free p c v : 0 <= c ->
  buf_res p c v |--
  (if eq_dec p nullval then emp else
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * data_at_ Ews (tarray tuchar (Z.max 1 c)) p)).
Proof.
  intros Hc. unfold buf_res. destruct (eq_dec p nullval); [apply derives_refl|].
  Intros. rewrite rest_w_eq. rewrite (adc_data_at_cs ZCS CompSpecs).
  rewrite (split2_data_at__Tarray_tuchar Ews (Z.max 1 c) c p) by (auto; try lia; apply H).
  cancel.
Qed.

Lemma buf_parts_free p c v : 0 <= c -> field_compatible (tarray tuchar (Z.max 1 c)) [] p ->
  (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at ZCS Ews (tarray tuchar c) v p * pw_pred (rest_w p c))%logic
  |-- (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * data_at_ Ews (tarray tuchar (Z.max 1 c)) p)%logic.
Proof.
  intros Hc Hfc. rewrite rest_w_eq. rewrite (adc_data_at_cs ZCS CompSpecs).
  rewrite (split2_data_at__Tarray_tuchar Ews (Z.max 1 c) c p) by (auto; try lia; apply Hfc).
  cancel.
Qed.

Lemma if_nn_intro p (A: mpred) : p <> nullval -> A |-- if eq_dec p nullval then emp else A.
Proof. intros. rewrite if_false by auto. apply derives_refl. Qed.

Lemma buf_res_nn p c v : p <> nullval -> buf_res p c v =
  (!! field_compatible (tarray tuchar (Z.max 1 c)) [] p &&
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at ZCS Ews (tarray tuchar c) v p *
    pw_pred (rest_w p c)))%logic.
Proof. intros. unfold buf_res. rewrite if_false by auto. reflexivity. Qed.

Lemma fa0_eq p c : 0 <= c -> field_compatible (tarray tuchar (Z.max 1 c)) [] p ->
  field_address0 (tarray tuchar (Z.max 1 c)) [ArraySubsc c] p = offset_val c p.
Proof.
  intros Hc Hfc. rewrite field_address0_offset.
  - simpl. f_equal. lia.
  - apply field_compatible0_cons. split; [simpl; lia | exact Hfc].
Qed.

(* the slack bytes and the c bytes of a buffer show both ends weakly valid *)
Lemma rest_wv p c : 0 <= c -> field_compatible (tarray tuchar (Z.max 1 c)) [] p ->
  pw_pred (rest_w p c) * @data_at_ ZCS Ews (tarray tuchar c) p |--
  weak_valid_pointer p && weak_valid_pointer (offset_val c p).
Proof.
  intros Hc Hfc. unfold pw_pred, rest_w. rewrite (fa0_eq p c Hc Hfc).
  assert (Hp: isptr p) by (destruct Hfc; auto).
  destruct (Z.eq_dec c 0) as [->|Hc0].
  - rewrite isptr_offset_val_zero by auto.
    change (Z.max 1 0 - 0) with 1.
    eapply derives_trans; [apply sepcon_derives; [apply data_at_valid_ptr; [auto | simpl; lia] | apply derives_refl]|].
    eapply derives_trans; [apply extend_valid_pointer|].
    apply andp_right; apply valid_pointer_weak.
  - rewrite sepcon_comm. rewrite data_at__memory_block. Intros.
    eapply derives_trans; [apply sepcon_derives; [|apply derives_refl]|].
    + apply andp_right.
      * apply (memory_block_weak_valid_pointer Ews (sizeof (tarray tuchar c)) p 0); simpl; try lia; auto.
      * apply (memory_block_weak_valid_pointer Ews (sizeof (tarray tuchar c)) p c); simpl; try lia; auto.
    + rewrite isptr_offset_val_zero by auto.
      apply andp_right.
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl]|].
        apply extend_weak_valid_pointer.
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl]|].
        apply extend_weak_valid_pointer.
Qed.

Lemma pws_one w : pws_pred [w] = pw_pred w.
Proof. unfold pws_pred. simpl. apply sepcon_emp. Qed.

Lemma andp_drop_vp (A: mpred) p : A && valid_pointer p |-- A.
Proof. apply andp_left1, derives_refl. Qed.

Lemma bytes_ok_Zrepeat0 k : bytes_ok (Zrepeat 0 k).
Proof. unfold bytes_ok, Zrepeat. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst. unfold is_byte. lia. Qed.
#[export] Hint Resolve bytes_ok_Zrepeat0 : core.

Lemma pws_app W1 W2 : pws_pred (W1 ++ W2) = (pws_pred W1 * pws_pred W2)%logic.
Proof.
  induction W1 as [|w W1 IH]; simpl.
  - unfold pws_pred at 2. simpl. rewrite emp_sepcon. reflexivity.
  - unfold pws_pred in *. simpl. rewrite IH, sepcon_assoc. reflexivity.
Qed.

Lemma buf_ok_of W1 W2 p c : 0 <= c -> field_compatible (tarray tuchar (Z.max 1 c)) [] p ->
  buf_ok (W1 ++ rest_w p c :: W2) Ews c p.
Proof.
  intros Hc Hfc. unfold buf_ok. rewrite pws_app.
  change (pws_pred (rest_w p c :: W2)) with (pw_pred (rest_w p c) * pws_pred W2)%logic.
  assert (E: (pws_pred W1 * (pw_pred (rest_w p c) * pws_pred W2) * @data_at_ ZCS Ews (tarray tuchar c) p)%logic =
             ((pw_pred (rest_w p c) * @data_at_ ZCS Ews (tarray tuchar c) p) * (pws_pred W1 * pws_pred W2))%logic).
  { apply pred_ext; cancel. }
  change (@data_at_ Zstd.proof.zstd.Base.CompSpecs) with (@data_at_ ZCS). rewrite E.
  eapply derives_trans; [apply sepcon_derives; [apply rest_wv; auto | apply derives_refl]|].
  apply andp_right.
  - eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl]|].
    apply extend_weak_valid_pointer.
  - eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl]|].
    apply extend_weak_valid_pointer.
Qed.

Lemma bytes_ok_of l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. intros H. unfold bytes_ok. eapply Forall_impl; [|exact H]. intros b Hb. unfold is_byte. rep_lia. Qed.

Lemma buf_valid p c v : 0 <= c -> buf_res p c v |-- valid_pointer p.
Proof.
  intros. eapply derives_trans; [apply buf_free; auto|].
  destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - entailer!.
Qed.

#[export] Hint Extern 1 (buf_res _ _ _ |-- valid_pointer _) => (apply buf_valid; rep_lia) : valid_pointer.
#[export] Hint Extern 1 (andp _ (valid_pointer ?p) |-- valid_pointer ?p) => (apply andp_left2, derives_refl) : valid_pointer.

Lemma api_eq a : 0 <= a <= Int.max_unsigned ->
  Int.add (Int.repr 1) (Int.modu (Int.repr a) (Int.repr 3)) = Int.repr (1 + a mod 3).
Proof.
  intros. unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia.
  rewrite add_repr. reflexivity.
Qed.

Ltac norm2 :=
  norm;
  repeat match goal with
  | H: Int.repr ?x = Int.zero |- _ => change Int.zero with (Int.repr 0) in H
  | H: Int.repr ?x <> Int.zero |- _ => change Int.zero with (Int.repr 0) in H
  | H: Int.repr ?x = Int.repr ?y |- _ => apply repr_inj_unsigned in H; [|rep_lia|rep_lia]
  | H: Int.repr ?x <> Int.repr ?y |- _ => assert (x <> y) by (intro; subst; contradiction); clear H
  end;
  try (exfalso; lia);
  try discriminate;
  try match goal with H: ?x = ?y, H': ?x <> ?y |- _ => exfalso; exact (H' H) end.

Lemma ptr_nn p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; try tauto. subst. exfalso; apply H2; reflexivity. Qed.

Ltac blk_step :=
  first
  [ match goal with |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
      apply semax_if_seq; forward_if; norm2 end
  | match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end
  | match goal with |- semax _ _ (Sifthenelse _ _ _) _ => forward_if; norm2 end
  | forward; norm2 ].

Lemma pws3 a b c : pws_pred [a; b; c] = (pw_pred a * pw_pred b * pw_pred c)%logic.
Proof. unfold pws_pred; simpl. rewrite sepcon_emp, sepcon_assoc. reflexivity. Qed.

Lemma pws3_fold a b c : (pw_pred a * pw_pred b * pw_pred c)%logic |-- pws_pred [a; b; c].
Proof. rewrite pws3. apply derives_refl. Qed.

Lemma rest_v p c : 0 <= c -> field_compatible (tarray tuchar (Z.max 1 c)) [] p ->
  pw_pred (rest_w p c) * @data_at_ ZCS Ews (tarray tuchar c) p |-- valid_pointer p.
Proof.
  intros Hc Hfc. unfold pw_pred, rest_w. rewrite (fa0_eq p c Hc Hfc).
  assert (Hp: isptr p) by (destruct Hfc; auto).
  destruct (Z.eq_dec c 0) as [->|Hc0].
  - rewrite isptr_offset_val_zero by auto.
    change (Z.max 1 0 - 0) with 1.
    eapply derives_trans; [apply sepcon_derives; [apply data_at_valid_ptr; [auto | simpl; lia] | apply derives_refl]|].
    apply extend_valid_pointer.
  - rewrite sepcon_comm.
    eapply derives_trans; [apply sepcon_derives; [apply data_at_valid_ptr; [auto | simpl; lia] | apply derives_refl]|].
    apply extend_valid_pointer.
Qed.

Lemma rest_v0 p : field_compatible (tarray tuchar (Z.max 1 0)) [] p ->
  pw_pred (rest_w p 0) |-- valid_pointer p.
Proof.
  intros Hfc. unfold pw_pred, rest_w. rewrite (fa0_eq p 0 ltac:(lia) Hfc).
  assert (Hp: isptr p) by (destruct Hfc; auto).
  rewrite isptr_offset_val_zero by auto.
  change (Z.max 1 0 - 0) with 1.
  apply data_at_valid_ptr; [auto | simpl; lia].
Qed.

Lemma dict0_ok dst cap src n dict k : k = 0 -> 0 <= cap ->
  field_compatible (tarray tuchar (Z.max 1 cap)) [] dst ->
  field_compatible (tarray tuchar (Z.max 1 k)) [] dict ->
  dict_ptr_ok [rest_w dst cap; rest_w src n; rest_w dict k] Ews k dict Ews cap dst.
Proof.
  intros -> Hc Hd Hk. right. split; [auto|]. rewrite pws3.
  change (@data_at_ Zstd.proof.zstd.Base.CompSpecs) with (@data_at_ ZCS).
  split.
  - eapply derives_trans with (pw_pred (rest_w dict 0) *
       (pw_pred (rest_w dst cap) * pw_pred (rest_w src n)))%logic.
    { cancel. }
    eapply derives_trans; [apply sepcon_derives; [apply rest_v0; auto | apply derives_refl]|].
    apply extend_valid_pointer.
  - eapply derives_trans with ((pw_pred (rest_w dst cap) * @data_at_ ZCS Ews (tarray tuchar cap) dst) *
       (pw_pred (rest_w dict 0) * pw_pred (rest_w src n)))%logic.
    { cancel. }
    eapply derives_trans; [apply sepcon_derives; [apply rest_v; auto | apply derives_refl]|].
    apply extend_valid_pointer.
Qed.

Definition dict_own (st: dctx_st) : Prop :=
  match dc_dict st with None => True | Some d => dr_src d = DSOwn /\ last_ok st d end.

Lemma own_after_load st' r b : load_result dctx_init st' r
    {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := b |} ->
  dict_own st' /\ dc_ss st' = ss_init /\ dc_set st' = nil /\ dc_bl st' = None.
Proof.
  unfold load_result, dict_own, last_ok. intros [[_ ->]|[_ [-> _]]]; simpl; auto.
Qed.

Lemma own_after_decode st st' : dict_own st -> after_decode (after_use st) st' (dc_dict st) ->
  dict_own st' /\ dc_ss st' = dc_ss st.
Proof.
  unfold dict_own, after_decode, after_use, last_ok. destruct st as [d stb ss l par set bl]; simpl.
  destruct d as [d|]; simpl.
  - intros [Hs Hl]. destruct (dr_once d); intros [->| ->]; simpl; auto;
      rewrite ?Hs; repeat split; auto.
  - intros _ [->| ->]; simpl; auto.
Qed.

Lemma after_decode_ss st st' l : after_decode st st' l -> dc_ss st' = dc_ss st.
Proof. intros [->| ->]; reflexivity. Qed.

Lemma after_decode_set st st' l : after_decode st st' l -> dc_set st' = dc_set st.
Proof. intros [->| ->]; reflexivity. Qed.

Lemma after_decode_bl st st' l : after_decode st st' l -> dc_bl st' = dc_bl st.
Proof. intros [->| ->]; reflexivity. Qed.

Lemma after_use_set st : dc_set (after_use st) = dc_set st.
Proof. unfold after_use. destruct (dc_dict st) as [d|]; [destruct (dr_once d)|]; reflexivity. Qed.

Lemma after_use_bl st : dc_bl (after_use st) = dc_bl st.
Proof. unfold after_use. destruct (dc_dict st) as [d|]; [destruct (dr_once d)|]; reflexivity. Qed.

(* ZSTD_DCtx_refDDict on a fresh context (refMultipleDDicts off): 0, and the DDict referenced *)
Lemma refdd_init st' r q dd : refddict_result dctx_init st' r q dd ->
  r = 0 /\ st' = set_dict dctx_init (Some (ddict_ref q dd)).
Proof. unfold refddict_result. intros [[-> ->]|[H _]]; [split; reflexivity | discriminate H]. Qed.

Lemma oneshot_dctx_nil2 st s cap r out : dc_set st = nil -> oneshot_dctx st s cap r out ->
  oneshot_ok (dmode_of (dc_par st)) (dictref_model (dc_dict st)) s cap r out.
Proof. intros H. unfold oneshot_dctx. rewrite H. tauto. Qed.

Lemma after_use_ss st : dc_ss (after_use st) = dc_ss st.
Proof. unfold after_use. destruct (dc_dict st) as [d|]; [destruct (dr_once d)|]; reflexivity. Qed.

Lemma dict_buf_ok_own W sh st shd cap dst : dict_own st -> dict_buf_ok W sh (dc_dict st) shd cap dst.
Proof. unfold dict_own, dict_buf_ok. destruct (dc_dict st) as [d|]; auto. intros [-> _]. exact I. Qed.

Lemma last_ok_own st : dict_own st -> match dc_dict st with Some dr => last_ok st dr | None => True end.
Proof. unfold dict_own. destruct (dc_dict st); tauto. Qed.

Lemma is_error_code_0 : is_error_code 0 = false.
Proof. reflexivity. Qed.

Lemma if_drop_vp p (A: mpred) :
  (if eq_dec p nullval then emp else (A && valid_pointer p)) |-- (if eq_dec p nullval then emp else A).
Proof. destruct (eq_dec p nullval); [apply derives_refl | apply andp_drop_vp]. Qed.

Ltac splits := repeat match goal with |- _ /\ _ => split end.

Ltac fin0 :=
  splits;
  try (apply bytes_ok_of; assumption);
  try (rewrite Zlength_Zrepeat; lia);
  try (match goal with |- context [Z.eq_dec ?x ?y] => destruct (Z.eq_dec x y) end; lia);
  try (intros; splits; auto; try discriminate; try lia);
  try (intros; unfold dict_own; simpl; auto);
  try (erewrite after_decode_ss by eassumption; rewrite ?after_use_ss;
       first [reflexivity | assumption | (simpl; assumption)]);
  try (erewrite after_decode_set by eassumption; rewrite ?after_use_set;
       first [reflexivity | assumption | (simpl; assumption)]);
  try (erewrite after_decode_bl by eassumption; rewrite ?after_use_bl;
       first [reflexivity | assumption | (simpl; assumption)]).
Ltac fin := entailer!; fin0.

Ltac kill_ifs :=
  repeat match goal with |- context [eq_dec ?p nullval] =>
    destruct (eq_dec p nullval); try contradiction; try discriminate end.

(* buf_ok of the witness list: pick the position of p's own witness by matching (a blind
   `apply (buf_ok_of [..] [..])` with the wrong split takes minutes to fail) *)
Ltac buf_side :=
  match goal with
  | |- buf_ok [rest_w ?p _; _; _] _ _ ?p => apply (buf_ok_of [] [_; _])
  | |- buf_ok [_; rest_w ?p _; _] _ _ ?p => apply (buf_ok_of [_] [_])
  | |- buf_ok [_; _; rest_w ?p _] _ _ ?p => apply (buf_ok_of [_; _] [])
  | |- buf_ok [rest_w ?p _; _] _ _ ?p => apply (buf_ok_of [] [_])
  | |- buf_ok [_; rest_w ?p _] _ _ ?p => apply (buf_ok_of [_] [])
  | |- buf_ok [rest_w ?p _] _ _ ?p => apply (buf_ok_of [] [])
  end; auto; lia.

Ltac side :=
  splits;
  try (match goal with |- Forall _ (dc_set ?st) =>
         first [match goal with H: dc_set st = nil |- _ => rewrite H end | cbn [dc_set set_dict dctx_init]];
         apply Forall_nil end);
  try buf_side;
  try (apply (buf_ok_of [] [_; _]); auto; lia);
  try (apply (buf_ok_of [_] [_]); auto; lia);
  try (apply (buf_ok_of [] [_]); auto; lia);
  try (left; reflexivity);
  try rep_lia;
  try (apply bytes_ok_of; auto);
  try (unfold ddict_buf_ok; simpl; apply dict0_ok; auto; lia);
  try (unfold ddict_buf_ok; simpl; exact I);
  try (apply (buf_ok_of [_; _] []); auto; lia);
  try (apply dict_buf_ok_own; assumption);
  try (apply last_ok_own; assumption);
  try (unfold dict_buf_ok; simpl; first [exact I | apply dict0_ok; auto; lia]);
  try (simpl; left; reflexivity);
  try reflexivity;
  try assumption.

Ltac ifseq := first [apply semax_if_seq | apply -> seq_assoc; apply semax_if_seq].

Ltac assume_fix := match goal with H: b2i _ <> Int.zero |- _ => apply b2i_nz, Z.leb_le in H end.

Section G.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

Definition mkdd (b: list Z) (r: option val) (db: val) (dl: option (dstate * Z)) : ddict_st :=
  {| dd_bytes := b; dd_ref := r; dd_buf := db; dd_ld := dl |}.

Lemma ddres_some gv sh q b p db dl : ddict_res DD gv sh q (mkdd b (Some p) db dl) =
  ((DD gv q (mkdd b (Some p) db dl) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic.
Proof. reflexivity. Qed.

Lemma ddres_none gv sh q b db dl : ddict_res DD gv sh q (mkdd b None db dl) =
  ((DD gv q (mkdd b None db dl) && valid_pointer q) * emp)%logic.
Proof. reflexivity. Qed.

Lemma ddres_some_fold gv sh q b p db dl :
  ((DD gv q (mkdd b (Some p) db dl) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic
  |-- ddict_res DD gv sh q (mkdd b (Some p) db dl).
Proof. rewrite ddres_some. apply derives_refl. Qed.

Lemma ddres_none_fold gv sh q b db dl :
  (DD gv q (mkdd b None db dl) && valid_pointer q) |-- ddict_res DD gv sh q (mkdd b None db dl).
Proof. rewrite ddres_none, sepcon_emp. apply derives_refl. Qed.

Lemma dres_ddict gv sh q pref b db dl : dict_res DD gv sh (Some (ddict_ref q (mkdd b pref db dl))) =
  ((DD gv q (mkdd b pref db dl) && valid_pointer q) *
   match pref with Some p => @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p | None => emp end)%logic.
Proof. reflexivity. Qed.

Lemma dres_some_fold gv sh q b p db dl :
  ((DD gv q (mkdd b (Some p) db dl) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic
  |-- dict_res DD gv sh (Some (ddict_ref q (mkdd b (Some p) db dl))).
Proof. rewrite dres_ddict. apply derives_refl. Qed.

Lemma dres_none_fold gv sh q b db dl :
  (DD gv q (mkdd b None db dl) && valid_pointer q)
  |-- dict_res DD gv sh (Some (ddict_ref q (mkdd b None db dl))).
Proof. rewrite dres_ddict, sepcon_emp. apply derives_refl. Qed.

Lemma dres_own gv sh st : dict_own st -> dict_res DD gv sh (dc_dict st) = emp.
Proof. unfold dict_own, dict_res. destruct (dc_dict st) as [d|]; auto. intros [-> _]. reflexivity. Qed.

Lemma dres_some_eq gv sh q b p db dl :
  dict_res DD gv sh (Some (ddict_ref q (mkdd b (Some p) db dl))) =
  ((DD gv q (mkdd b (Some p) db dl) && valid_pointer q) * @data_at ZCS sh (tarray tuchar (Zlength b)) (zbytes b) p)%logic.
Proof. reflexivity. Qed.

Lemma dres_none_eq gv sh q b db dl :
  dict_res DD gv sh (Some (ddict_ref q (mkdd b None db dl))) =
  ((DD gv q (mkdd b None db dl) && valid_pointer q) * emp)%logic.
Proof. reflexivity. Qed.

Lemma dctx_free_form gv p st :
  (if eq_dec p nullval then emp else DC gv p st) =
  match (if eq_dec p nullval then None else Some st) with None => emp | Some st' => DC gv p st' end.
Proof. destruct (eq_dec p nullval); reflexivity. Qed.

Lemma ddict_free_form gv p dd :
  (if eq_dec p nullval then emp else DD gv p dd) =
  match (if eq_dec p nullval then None else Some dd) with None => emp | Some dd' => DD gv p dd' end.
Proof. destruct (eq_dec p nullval); reflexivity. Qed.

Lemma dres_own_intro gv sh st : dict_own st -> emp |-- dict_res DD gv sh (dc_dict st).
Proof. intros H. rewrite (dres_own gv sh st H). apply derives_refl. Qed.

(* the DDict set is empty in every state of the run *)
Lemma set_res_drop gv sh st cur : dc_set st = nil -> set_res DD gv sh (dc_set st) cur = emp.
Proof. intros H. rewrite H. reflexivity. Qed.

Lemma dres_init_emp gv sh : dict_res DD gv sh (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Lemma sres_init_emp gv sh : set_res DD gv sh (dc_set dctx_init) (dc_dict dctx_init) = emp.
Proof. reflexivity. Qed.

Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompress_usingDDict_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD;
   ZSTD_DCtx_loadDictionary_spec DC; ZSTD_DCtx_refDDict_spec DC DD;
   nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].

Ltac reinv st out dst dict :=
  try forward;
  Exists st out; rewrite ?pws3; rewrite ?ddres_some, ?ddres_none;
  rewrite (buf_res_nn dst) by auto; rewrite (buf_res_nn dict) by auto; kill_ifs;
  repeat match goal with H: (?x =? ?y) = _ |- context [?x =? ?y] => rewrite H end;
  fin.

Ltac assert_side :=
  first [ (entailer!; simpl; rewrite le64_b2i by rep_lia; reflexivity)
        | (match goal with H: oneshot_ok _ _ _ _ _ _, Er: is_error_code _ = false |- _ =>
             let Hle := fresh in
             destruct H as [Hle _]; specialize (Hle Er);
             match goal with Hz: b2i _ = Int.zero |- _ =>
               unfold b2i in Hz; rewrite (proj2 (Z.leb_le _ _) Hle) in Hz; discriminate Hz end end) ].

(* decompressDCtx's frame holds the (empty) DDict set of the state st *)
Ltac add_set_res DD gv st :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx (set_res DD gv Ews (dc_set st) (dc_dict st) :: R))));
    [rewrite set_res_drop by (first [assumption | reflexivity]); entailer! |] end.

(* refDDict's frame on a fresh context: its (empty) dictionary and DDict set *)
Ltac add_init_res DD gv :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (PROPx P (LOCALx Q (SEPx (dict_res DD gv Ews (dc_dict dctx_init) ::
      set_res DD gv Ews (dc_set dctx_init) (dc_dict dctx_init) :: R))));
    [rewrite dres_init_emp, sres_init_emp; entailer! |] end.

Ltac refdd_side := splits; try reflexivity; try (apply ptr_nn; auto); try auto; try (cbn; rep_lia).

Ltac drop_set_res := rewrite ?set_res_drop by (first [assumption | reflexivity]).

Ltac tail r cap st out dst dict :=
  api_init;
  forward_call r;
  try match goal with H: oneshot_dctx ?st0 _ _ _ _ |- _ =>
    apply oneshot_dctx_nil2 in H; [|first [assumption | reflexivity]] end;
  let Er := fresh "Er" in
  destruct (is_error_code r) eqn:Er;
  try match goal with H1: ?e = true, H2: ?e = false |- _ => rewrite H1 in H2; discriminate H2 end;
  forward_if; norm2;
  try (forward_call (b2i (r <=? cap)); try assert_side);
  reinv st out dst dict.

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_dict_copy.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (Zstd.proof.zstd.Globals.zstd_globals gv * TT)%logic).
  { intros Hgv. eapply derives_trans.
    - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_any_dict_copy.whole_prog); [simpl; tauto | exact Hgv].
    - cancel. }
  { reflexivity. }
  { apply vars_in_tycontext. }
  eapply semax_pre with (P' := PROP () LOCAL (gvars gv) SEP (mem_mgr gv; zstd_globals gv; TT)).
  { change (stackframe_of f_main) with (fun _ : environ => @emp mpred _ _).
    rewrite sepcon_emp_fun_ADC. entailer!. sep_apply (create_mem_mgr gv). cancel. }
  abbreviate_semax.
  forward_call tt. Intros n.
  forward_call tt. Intros a.
  forward. forward.
  forward_call (b2i (n <=? 4096)).
  { entailer!. simpl. rewrite le64_b2i by rep_lia. reflexivity. }
  Intros. assume_fix.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  if_set_post _t'3 (Vlong (Int64.repr (Z.max 1 n))).
  { forward. entailer!. norm. do 2 f_equal; lia. }
  { forward. entailer!. norm. do 2 f_equal; lia. }
  forward_call (tarray tuchar (Z.max 1 n), gv).
  { simpl. rep_lia. }
  Intros src. forward.
  forward_if. { destruct (eq_dec src nullval); entailer!. } { forward. }
  sep_apply (malloc_buf src n); [lia|].
  rewrite buf_res_nn by auto. Intros.
  rewrite (adc_data_at_cs ZCS CompSpecs Ews n).
  forward_call (src, n, Ews).
  Intros s.
  rewrite (adc_data_at_cs CompSpecs ZCS Ews n).
  forward_call tt. Intros cap.
  forward_call (b2i (cap <=? 65536)).
  { entailer!. simpl. rewrite le64_b2i by rep_lia. reflexivity. }
  Intros. assume_fix.
  forward_call tt. Intros dn.
  forward_call (b2i (dn <=? 4096)).
  { entailer!. simpl. rewrite le64_b2i by rep_lia. reflexivity. }
  Intros. assume_fix.
  if_set_post _t'7 (Vlong (Int64.repr (Z.max 1 cap))).
  { forward. entailer!. norm. do 2 f_equal; lia. }
  { forward. entailer!. norm. do 2 f_equal; lia. }
  forward_call (tarray tuchar (Z.max 1 cap), gv).
  { simpl. rep_lia. }
  Intros dst. forward.
  assert_PROP (is_pointer_or_null dst) as PNdst by (destruct (eq_dec dst nullval); entailer!).
  sep_apply (malloc_buf dst cap); [lia|].
  if_set_post _t'9 (Vlong (Int64.repr (Z.max 1 dn))).
  { forward. entailer!. norm. do 2 f_equal; lia. }
  { forward. entailer!. norm. do 2 f_equal; lia. }
  forward_call (tarray tuchar (Z.max 1 dn), gv).
  { simpl. rep_lia. }
  Intros dict. forward.
  assert_PROP (is_pointer_or_null dict) as PNdict by (destruct (eq_dec dict nullval); entailer!).
  sep_apply (malloc_buf dict dn); [lia|].
  forward_call gv.
  Intros dctx.
  apply -> seq_assoc.
  rewrite api_eq by lia.
  assert (Hapi: 1 <= 1 + a mod 3 <= 3) by (pose proof (Z.mod_pos_bound a 3); lia).
  forget (1 + a mod 3) as api.
  set (R0 := if eq_dec dst nullval then 0 else if eq_dec dict nullval then 0 else
             if eq_dec dctx nullval then 0 else if Z.eq_dec api 2 then 2 else 1).
  match goal with |- semax _ (PROPx ?P (LOCALx ?Ql (SEPx ?Rl))) (Ssequence _ _) _ =>
    apply semax_seq with (Q := PROPx P (LOCALx (temp _rounds (Vint (Int.repr R0)) :: Ql) (SEPx Rl))) end.
  { abbreviate_semax. subst R0.
    destruct (eq_dec dst nullval) as [Ed|Nd].
    { subst dst. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdst Nd). destruct dst; try contradiction.
    destruct (eq_dec dict nullval) as [Ei|Ni].
    { subst dict. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdict Ni). destruct dict; try contradiction.
    destruct (eq_dec dctx nullval) as [Ec|Nc].
    { subst dctx. repeat blk_step. all: entailer!. }
    pose proof (ptr_nn _ PNdctx Nc). destruct dctx; try contradiction.
    destruct (Z.eq_dec api 2).
    { repeat blk_step. all: entailer!. }
    { repeat blk_step. all: entailer!. } }
  assert (HR0: 0 <= R0 <= 2 /\ (R0 > 0 -> dst <> nullval /\ dict <> nullval /\ dctx <> nullval /\
             R0 = if Z.eq_dec api 2 then 2 else 1)).
  { subst R0. repeat destruct (eq_dec _ _); destruct (Z.eq_dec api 2); split; try lia; intros; repeat split; auto; lia. }
  clearbody R0.
  forward_if (EX R: Z, EX dd: val, EX b: list Z, EX db: val, EX dl: option (dstate * Z), EX dcont: list val,
    PROP (0 <= R <= 2;
          R > 0 -> dst <> nullval /\ dict <> nullval /\ dctx <> nullval /\
                   R = (if Z.eq_dec api 2 then 2 else 1) /\ dcont = zbytes b /\ (api <> 2 -> dd <> nullval);
          api = 2 -> dd = nullval; Zlength b = dn; bytes_ok b; Zlength dcont = dn; is_pointer_or_null dd)
    LOCAL (temp _rounds (Vint (Int.repr R)); temp _ddict dd; temp _dctx dctx; temp _dict dict;
           temp _dst dst; temp _dn (Vlong (Int64.repr dn)); temp _cap (Vlong (Int64.repr cap));
           temp _src src; temp _api (Vint (Int.repr api)); temp _n (Vlong (Int64.repr n)); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv;
         if eq_dec dctx nullval then emp else DC gv dctx dctx_init && valid_pointer dctx;
         buf_res dict dn dcont; buf_res dst cap (Zrepeat Vundef cap);
         @data_at ZCS Ews (tarray tuchar n) (zbytes s) src;
         malloc_token Ews (tarray tuchar (Z.max 1 n)) src;
         pw_pred (rest_w src n);
         if eq_dec dd nullval then emp else (DD gv dd (mkdd b (if Zlength b =? 0 then Some dict else None) db dl) && valid_pointer dd);
         TT)).
  { norm2. destruct HR0 as [_ HR0]. destruct (HR0 ltac:(lia)) as (Nd & Ni & Nc & ER).
    rewrite (buf_res_nn dict) by auto. Intros.
    rewrite (adc_data_at_cs ZCS CompSpecs Ews dn).
    forward_call (dict, dn, Ews).
    Intros b.
    match goal with H: Zlength b = dn |- _ => subst dn end.
    rewrite (adc_data_at_cs CompSpecs ZCS Ews (Zlength b)).
    forward_if.
    { rewrite <- (pws_one (rest_w dict (Zlength b))).
      forward_call ([rest_w dict (Zlength b)], gv, Ews, dict, b).
      { rewrite bytes_at_ptr by (eapply field_compatible_isptr; eassumption). cancel. }
      { try (split; [intro; contradiction |]). split; [intros _; apply (buf_ok_of [] []); auto; rep_lia | apply bytes_ok_of; auto]. }
      Intros vret. destruct vret as [q ddst]. cbn [fst snd] in *. rewrite pws_one.
      rewrite bytes_at_ptr by (eapply field_compatible_isptr; eassumption).
      match goal with H: dd_ref ddst = _ |- _ => rewrite if_false in H by auto end.
      match goal with H: is_pointer_or_null q |- _ => rename H into PNq end.
      destruct ddst as [b1 r1 db dl]. cbn [dd_bytes dd_ref] in *. subst b1 r1.
      change {| dd_bytes := b; dd_ref := if Zlength b =? 0 then Some dict else None; dd_buf := db; dd_ld := dl |}
        with (mkdd b (if Zlength b =? 0 then Some dict else None) db dl).
      destruct (eq_dec q nullval) as [Eq|Nq].
      { subst q. forward_if.
        { forward. Exists 0 nullval b db dl (zbytes b). rewrite (buf_res_nn dict) by auto. fin. }
        { norm2. } }
      { pose proof (ptr_nn _ PNq Nq). destruct q; try contradiction.
        forward_if.
        { norm2. }
        { forward. Exists R0 (Vptr b0 i) b db dl (zbytes b). rewrite (buf_res_nn dict) by auto.
          destruct (eq_dec (Vptr b0 i) nullval); [discriminate|].
          fin. } } }
    { forward. Exists R0 nullval b nullval (@None (dstate * Z)) (zbytes b). rewrite (buf_res_nn dict) by auto. fin. } }
  { forward. assert (R0 = 0) by lia. subst R0.
    Exists 0 nullval (Zrepeat 0 dn) nullval (@None (dstate * Z)) (Zrepeat Vundef dn). fin. }
  Intros R dd b db dl dcont.
  match goal with H: Zlength b = dn |- _ => subst dn end.
  match goal with H: Zlength s = n |- _ => subst n end.
  sep_apply (if_drop_vp dctx (DC gv dctx dctx_init)).
  forward_for_simple_bound R (EX k: Z, EX st: dctx_st, EX out: list val,
    PROP (dc_ss st = ss_init; Zlength out = cap; k = 0 -> st = dctx_init; api = 2 -> dict_own st;
          dc_set st = nil; dc_bl st = None)
    LOCAL (temp _rounds (Vint (Int.repr R)); temp _ddict dd; temp _dctx dctx; temp _dict dict;
           temp _dst dst; temp _dn (Vlong (Int64.repr (Zlength b))); temp _cap (Vlong (Int64.repr cap));
           temp _src src; temp _api (Vint (Int.repr api)); temp _n (Vlong (Int64.repr (Zlength s))); gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; if eq_dec dctx nullval then emp else DC gv dctx st;
         buf_res dict (Zlength b) dcont; buf_res dst cap out;
         @data_at ZCS Ews (tarray tuchar (Zlength s)) (zbytes s) src;
         malloc_token Ews (tarray tuchar (Z.max 1 (Zlength s))) src; pw_pred (rest_w src (Zlength s));
         if eq_dec dd nullval then emp else (DD gv dd (mkdd b (if Zlength b =? 0 then Some dict else None) db dl) && valid_pointer dd);
         TT)).
  { Exists dctx_init (Zrepeat Vundef cap). fin. }
  { Intros.
    match goal with H: R > 0 -> _ |- _ => destruct (H ltac:(lia)) as (Nd & Ni & Nc & ER & Edc & Edd) end. subst dcont.
    rewrite (buf_res_nn dst) by auto. rewrite (buf_res_nn dict) by auto. Intros.
    destruct (eq_dec dctx nullval); [contradiction|].
    sep_apply (pws3_fold (rest_w dst cap) (rest_w src (Zlength s)) (rest_w dict (Zlength b))).
    apply semax_if_seq. forward_if.
    { (* api = 1: ZSTD_decompress_usingDDict *)
      norm2. subst api. assert (i = 0) by (simpl in ER; lia). subst i.
      specialize (Edd ltac:(lia)). destruct (eq_dec dd nullval); [contradiction|].
      match goal with H: 0 = 0 -> st = dctx_init |- _ => specialize (H eq_refl); subst st end.
      destruct (Zlength b =? 0) eqn:Eb.
      - apply Z.eqb_eq in Eb.
        sep_apply (ddres_some_fold gv Ews dd b dict db dl).
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
        forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx, dctx_init,
          Ews, dst, cap, Ews, src, s, Ews, dd, mkdd b (Some dict) db dl).
        { side. }
        Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *.
        tail r cap st' out' dst dict.
      - sep_apply (ddres_none_fold gv Ews dd b db dl).
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
        forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx, dctx_init,
          Ews, dst, cap, Ews, src, s, Ews, dd, mkdd b None db dl).
        { side. }
        Intros vret. destruct vret as [[r out'] st']. cbn [fst snd] in *.
        tail r cap st' out' dst dict. }
    { (* api <> 1 *)
      norm2. forward. change (Int.signed (Int.repr 0)) with 0.
      ifseq. forward_if.
      { (* k = 0 *)
        norm2. subst i.
        match goal with H: 0 = 0 -> st = dctx_init |- _ => specialize (H eq_refl); subst st end.
        ifseq. forward_if.
        { (* api = 2: ZSTD_DCtx_loadDictionary *)
          norm2. subst api.
          forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx, dctx_init,
            Ews, dict, b).
          { side. }
          Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *.
          api_init; match goal with H: load_result _ _ _ _ |- _ => destruct (own_after_load _ _ _ H) as (Own1 & Ss1 & Set1 & Bl1) end.
          forward. forward_call r1. ifseq.
          destruct (is_error_code r1) eqn:Er1.
          { forward_if; norm2. tail r1 cap st1 out dst dict. }
          { forward_if; norm2.
            sep_apply (dres_own_intro gv Ews st1 Own1).
            sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
            add_set_res DD gv st1.
            forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx, st1,
              Ews, Ews, dst, cap, Ews, src, s).
            { unfold mbuf; rewrite (if_false (dst = nullval)) by auto. cancel. }
            { side. }
            Intros vret. destruct vret as [[r2 out'] st2]. cbn [fst snd] in *. drop_set_res.
            unfold mbuf; rewrite (if_false (dst = nullval)) by auto.
            rewrite (dres_own gv Ews st1 Own1).
            api_init; match goal with H: after_decode _ _ _ |- _ => destruct (own_after_decode st1 st2 Own1 H) as [Own2 Ss2] end.
            tail r2 cap st2 out' dst dict. } }
        { (* api = 3: ZSTD_DCtx_refDDict *)
          norm2. assert (api = 3) by lia. subst api.
          specialize (Edd ltac:(lia)). destruct (eq_dec dd nullval) as [|Ndd]; [contradiction|].
          sep_apply (andp_drop_vp (DD gv dd (mkdd b (if Zlength b =? 0 then Some dict else None) db dl)) dd).
          add_init_res DD gv.
          forward_call (gv, dctx, dctx_init, dd, mkdd b (if Zlength b =? 0 then Some dict else None) db dl, Ews).
          { destruct (eq_dec dd nullval); [contradiction|]. cancel. }
          Intros vret. destruct vret as [r1 st1]. cbn [fst snd] in *.
          api_init. destruct (eq_dec dd nullval) as [|_]; [contradiction|].
          match goal with H: refddict_result _ _ _ _ _ |- _ => destruct (refdd_init _ _ _ _ H) as [-> ->] end.
          rewrite dres_init_emp, sres_init_emp.
          forward. forward_call 0. rewrite is_error_code_0.
          ifseq. forward_if; norm2.
          destruct (Zlength b =? 0) eqn:Eb; cbn [dd_ref dd_bytes].
          - apply Z.eqb_eq in Eb.
            sep_apply (dres_some_fold gv Ews dd b dict db dl).
            sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
            add_set_res DD gv (set_dict dctx_init (Some (ddict_ref dd (mkdd b (Some dict) db dl)))).
            forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx,
              set_dict dctx_init (Some (ddict_ref dd (mkdd b (Some dict) db dl))),
              Ews, Ews, dst, cap, Ews, src, s).
            { unfold mbuf; rewrite (if_false (dst = nullval)) by auto. cancel. }
            { side. }
            Intros vret. destruct vret as [[r2 out'] st2]. cbn [fst snd] in *. drop_set_res.
            unfold mbuf; rewrite (if_false (dst = nullval)) by auto.
            cbn [dc_dict set_dict]. rewrite dres_some_eq.
            tail r2 cap st2 out' dst dict.
          - sep_apply (dres_none_fold gv Ews dd b db dl).
            sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
            add_set_res DD gv (set_dict dctx_init (Some (ddict_ref dd (mkdd b None db dl)))).
            forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx,
              set_dict dctx_init (Some (ddict_ref dd (mkdd b None db dl))),
              Ews, Ews, dst, cap, Ews, src, s).
            { unfold mbuf; rewrite (if_false (dst = nullval)) by auto. cancel. }
            { side. }
            Intros vret. destruct vret as [[r2 out'] st2]. cbn [fst snd] in *. drop_set_res.
            unfold mbuf; rewrite (if_false (dst = nullval)) by auto.
            cbn [dc_dict set_dict]. rewrite dres_none_eq.
            tail r2 cap st2 out' dst dict. } }
      { (* k <> 0: api = 2, second round *)
        norm2.
        assert (api = 2) by (revert ER; destruct (Z.eq_dec api 2); intros ER; [auto | lia]). subst api.
        match goal with H: 2 = 2 -> dict_own st |- _ => specialize (H eq_refl) as Own end.
        forward_call 0. rewrite is_error_code_0.
        ifseq. forward_if; norm2.
        sep_apply (dres_own_intro gv Ews st Own).
        sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) out dst).
        add_set_res DD gv st.
        forward_call ([rest_w dst cap; rest_w src (Zlength s); rest_w dict (Zlength b)], gv, dctx, st,
          Ews, Ews, dst, cap, Ews, src, s).
        { unfold mbuf; rewrite (if_false (dst = nullval)) by auto. cancel. }
        { side. }
        Intros vret. destruct vret as [[r2 out'] st2]. cbn [fst snd] in *. drop_set_res.
        unfold mbuf; rewrite (if_false (dst = nullval)) by auto.
        rewrite (dres_own gv Ews st Own).
        api_init; match goal with H: after_decode _ _ _ |- _ => destruct (own_after_decode st st2 Own H) as [Own2 Ss2] end.
        tail r2 cap st2 out' dst dict. } } }
  Intros st out.
  rewrite (dctx_free_form gv dctx st).
  forward_call (gv, dctx, if eq_dec dctx nullval then None else Some st).
  { destruct (eq_dec dctx nullval); auto. }
  sep_apply (if_drop_vp dd (DD gv dd (mkdd b (if Zlength b =? 0 then Some dict else None) db dl))).
  rewrite (ddict_free_form gv dd).
  forward_call (gv, dd, if eq_dec dd nullval then None
     else Some (mkdd b (if Zlength b =? 0 then Some dict else None) db dl)).
  { destruct (eq_dec dd nullval); auto. }
  forward_call (gv, nullval, @None ddict_st). 1: cancel.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx _))) _ _ =>
    eapply semax_pre with (P' := PROPx P (LOCALx Q (SEPx (mem_mgr gv :: zstd_globals gv ::
      (if eq_dec src nullval then emp else
        (malloc_token Ews (tarray tuchar (Z.max 1 (Zlength s))) src *
         data_at_ Ews (tarray tuchar (Z.max 1 (Zlength s))) src)%logic) ::
      (if eq_dec dst nullval then emp else
        (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dst *
         data_at_ Ews (tarray tuchar (Z.max 1 cap)) dst)%logic) ::
      (if eq_dec dict nullval then emp else
        (malloc_token Ews (tarray tuchar (Z.max 1 (Zlength b))) dict *
         data_at_ Ews (tarray tuchar (Z.max 1 (Zlength b))) dict)%logic) :: TT :: nil)))) end.
  { rewrite (if_false _ (eq_dec src nullval)) by auto.
    sep_apply (buf_parts_free src (Zlength s) (zbytes s) ltac:(lia) H3).
    sep_apply (buf_free dst cap out ltac:(lia)).
    sep_apply (buf_free dict (Zlength b) dcont ltac:(lia)).
    entailer!. }
  forward_call (tarray tuchar (Z.max 1 (Zlength s)), src, gv).
  forward_call (tarray tuchar (Z.max 1 cap), dst, gv).
  forward_call (tarray tuchar (Z.max 1 (Zlength b)), dict, gv).
  forward.
Qed.
End G.

(* ---------- from G0 to Gprog (Specs_api DC DD) [] ---------- *)

Lemma Externals_eq : Externals = [nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].
Proof.
  unfold Externals, present, env_harness, filter.
  repeat match goal with |- context [id_in_list ?i ?l] =>
    let b := eval lazy in (id_in_list i l) in change (id_in_list i l) with b end.
  reflexivity.
Qed.

Lemma make_tycontext_g_find (Vs: varspecs) (G: funspecs) i :
  Maps.PTree.get i (make_tycontext_g Vs G) =
  match initial_world.find_id i G with Some fs => Some (type_of_funspec fs) | None => Maps.PTree.get i (make_tycontext_g Vs nil) end.
Proof.
  induction G as [|[j fs] G IH]; simpl; auto.
  rewrite Maps.PTree.gsspec. unfold make_tycontext_g in IH |- *. simpl in IH.
  destruct (peq i j) as [->|Hne].
  - rewrite if_true by reflexivity. reflexivity.
  - rewrite if_false by exact Hne. exact IH.
Qed.

Lemma make_tycontext_g_nil_in (Vs: varspecs) i t :
  Maps.PTree.get i (make_tycontext_g Vs nil) = Some t -> In i (map fst Vs).
Proof.
  unfold make_tycontext_g. simpl. induction Vs as [|[j u] Vs IH]; simpl.
  - rewrite Maps.PTree.gempty. discriminate.
  - rewrite Maps.PTree.gsspec. destruct (peq i j); [left; auto | intros H; right; auto].
Qed.

(* A name that is not a function of G keeps its type of the global variables: stated for an abstract G, so that
   the rewriting never compares the concrete function list with the empty one (which unfolds the specifications). *)
Lemma sub_none_G (V: varspecs) (G: funspecs) i :
  (forall t, Maps.PTree.get i (make_tycontext_g V nil) = Some t -> initial_world.find_id i G = None) ->
  tycontext.sub_option (Maps.PTree.get i (make_tycontext_g V nil)) (Maps.PTree.get i (make_tycontext_g V G)).
Proof.
  intros H. rewrite (make_tycontext_g_find V G i).
  destruct (Maps.PTree.get i (make_tycontext_g V nil)) as [t|] eqn:EV; [|exact Logic.I].
  rewrite (H t eq_refl). reflexivity.
Qed.

Lemma find_id_in_fst {A} i (l: list (ident * A)) x : initial_world.find_id i l = Some x -> In i (map fst l).
Proof. intros H. apply initial_world.find_id_e in H. apply (in_map fst) in H. exact H. Qed.

Section L.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

Lemma Gprog_eq : Gprog (Specs_api DC DD) [] =
  ((_quickproof_malloc, malloc_spec') :: (_quickproof_free, free_spec') :: Specs_api DC DD) ++
  [nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec] ++ [] ++ [main_spec].
Proof. unfold Gprog, Imports. rewrite Externals_eq. reflexivity. Qed.

Lemma G0_in_Gprog i fs : initial_world.find_id i (G0 DC DD) = Some fs ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = Some fs.
Proof.
  intros Hf. rewrite Gprog_eq.
  apply initial_world.find_id_e in Hf. unfold G0 in Hf.
  repeat (destruct Hf as [Hf|Hf]; [inversion Hf; subst; reflexivity|]). contradiction.
Qed.

Lemma vars_not_funs i t : Maps.PTree.get i (make_tycontext_g Vprog nil) = Some t ->
  initial_world.find_id i (Gprog (Specs_api DC DD) []) = None.
Proof.
  intros Hv. apply make_tycontext_g_nil_in in Hv.
  destruct (initial_world.find_id i (Gprog (Specs_api DC DD) [])) as [fs|] eqn:E; [|reflexivity].
  exfalso. apply find_id_in_fst in E. rewrite Gprog_eq in E.
  revert i Hv E. idtac.
  assert (HV: map fst Vprog = ltac:(let x := eval vm_compute in (map fst Vprog) in exact x)) by (vm_compute; reflexivity).
  rewrite HV. intros i Hv E. simpl in Hv, E.
  repeat (destruct E as [E|E];
    [subst i; vm_compute in Hv; repeat (destruct Hv as [Hv|Hv]; [discriminate Hv|]); exact Hv |]).
  exact E.
Qed.

End L.

Theorem any_dict_copy_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * rewrite (make_tycontext_g_find Vprog (Gprog (Specs_api DC DD) []) i).
        rewrite (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * apply (sub_none_G Vprog (Gprog (Specs_api DC DD) []) i). exact (vars_not_funs DC DD i).
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.
