(* The harness obligation of harness/any_params.c under the decoder's API v3.
   A law added by a later revision of the contract: templates in the any_* proofs of the other laws. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.zstd.Spec_api6.
Require Export Zstd.proof.harness.any_params.HOK_any_params.
Require Zstd.proof.top.MainPre6.
Require Import Zstd.proof.zstd.NullBuf.
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


(* ---------- the harness's two dictionary slots: dd[j], dbuf[j] ---------- *)

(* SNone: dd[j] = dbuf[j] = NULL; SBuf b c: dd[j] = NULL, dbuf[j] = b, a buffer of max(1,c) bytes whose
   dictionary was not created; SDD q b bs: dd[j] = q, the DDict made by copy from bs, at dbuf[j] = b *)
Inductive slot := SNone | SBuf (b: val) (c: Z) | SDD (q: val) (b: val) (bs: list Z) (dd: ddict_st).
#[export] Instance Inh_slot : Inhabitant slot := SNone.

Definition slot_q (s: slot) : val := match s with SDD q _ _ _ => q | _ => nullval end.
Definition slot_b (s: slot) : val := match s with SNone => nullval | SBuf b _ => b | SDD _ b _ _ => b end.
Definition slot_bs (s: slot) : list Z := match s with SDD _ _ bs _ => bs | _ => nil end.
Definition isSDD (s: slot) : Prop := match s with SDD _ _ _ _ => True | _ => False end.

(* the state ZSTD_createDDict gave the slot's DDict *)
Definition slot_ddst (s: slot) : ddict_st :=
  match s with SDD _ _ _ dd => dd | _ => {| dd_bytes := nil; dd_ref := None; dd_buf := nullval; dd_ld := None |} end.
Definition slot_e (s: slot) : val * ddict_st := (slot_q s, slot_ddst s).
Definition slot_ref (s: slot) : dictref := ddict_ref (slot_q s) (slot_ddst s).

Definition slot_ok (s: slot) : Prop :=
  match s with
  | SNone => True
  | SBuf b c => isptr b /\ 0 <= c <= 512
  | SDD q b bs dd => isptr q /\ Zlength bs <= 512 /\ bytes_ok bs /\
                  field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] b /\
                  dd_bytes dd = bs /\ dd_ref dd = (if Zlength bs =? 0 then Some b else None)
  end.

(* the slack bytes of a slot's buffer, lent to the decoder as pointer witnesses *)
Definition slot_w (s: slot) : list ptr_witness :=
  match s with SDD _ b bs _ => [rest_w b (Zlength bs)] | _ => [] end.
Definition slots_w (sl: list slot) : list ptr_witness := slot_w (Znth 0 sl) ++ slot_w (Znth 1 sl).

(* the dictionaries a context refers to: its current one (the last DDict referenced) and its DDict set,
   both made of the slots' DDicts, each slot at most once in the set *)
Definition ctx_ds (sl: list slot) (d: option dictref) (l: list (val * ddict_st)) : Prop :=
  (match d with
   | None => True
   | Some dr => exists j, 0 <= j < 2 /\ isSDD (Znth j sl) /\ dr = slot_ref (Znth j sl)
   end) /\
  exists idx, NoDup idx /\ Forall (fun j => 0 <= j < 2 /\ isSDD (Znth j sl)) idx /\
              l = map (fun j => slot_e (Znth j sl)) idx.

(* the context during the parameter loop (with the default allocator, as ZSTD_DCtx_refDDict requires) *)
Definition ctx_ok (sl: list slot) (st: dctx_st) : Prop :=
  dc_ss st = ss_init /\ dc_bl st = None /\ dc_last st = None /\ dc_stable st = false /\ dc_mem st = None /\
  ctx_ds sl (dc_dict st) (dc_set st).

Lemma ctx_ok_init : ctx_ok [SNone; SNone] dctx_init.
Proof.
  unfold ctx_ok, ctx_ds. simpl. repeat split; auto.
  exists nil. split; [constructor | split; [constructor | reflexivity]].
Qed.

Lemma ctx_ok_par sl st p : ctx_ok sl st -> ctx_ok sl (set_par st p).
Proof. unfold ctx_ok. destruct st; simpl. tauto. Qed.

(* a slot changes without becoming a DDict: the context does not refer to it *)
Lemma ctx_ds_upd_non sl j s d l : Zlength sl = 2 -> 0 <= j < 2 -> ~ isSDD (Znth j sl) -> ~ isSDD s ->
  ctx_ds sl d l -> ctx_ds (upd_Znth j sl s) d l.
Proof.
  intros Hl Hj Hn Hs [Hd (idx & Hnd & Hf & ->)].
  assert (Hk: forall k, 0 <= k < 2 -> isSDD (Znth k sl) -> Znth k (upd_Znth j sl s) = Znth k sl).
  { intros k Hk Hsk. rewrite upd_Znth_diff by (try lia; intro; subst; contradiction). reflexivity. }
  split.
  - destruct d as [dr|]; auto. destruct Hd as (k & Hk2 & Hsk & ->).
    exists k. rewrite Hk by auto. auto.
  - exists idx. split; [exact Hnd|]. split.
    + eapply Forall_impl; [|exact Hf]. intros k [Hk2 Hsk]. rewrite Hk by auto. auto.
    + apply map_ext_in. intros k Hin. rewrite Forall_forall in Hf. destruct (Hf k Hin).
      rewrite Hk by auto. reflexivity.
Qed.

(* ZSTD_DCtx_refDDict of a new slot j's DDict *)
Lemma ctx_ok_refdd sl j s st st' r : Zlength sl = 2 -> 0 <= j < 2 -> ~ isSDD (Znth j sl) -> isSDD s ->
  ctx_ok sl st -> refddict_result st st' r (slot_q s) (slot_ddst s) ->
  ctx_ok (upd_Znth j sl s) st' /\ dc_par st' = dc_par st.
Proof.
  intros Hl Hj Hn Hs [Hss [Hbl [Hlast [Hst [Hmem [Hd (idx & Hnd & Hf & Hset)]]]]]] Hr.
  destruct s as [| b0 c0 | q b bs dd]; try contradiction. simpl in Hr.
  assert (Hjs: Znth j (upd_Znth j sl (SDD q b bs dd)) = SDD q b bs dd) by (apply upd_Znth_same; lia).
  assert (Hk: forall k, 0 <= k < 2 -> isSDD (Znth k sl) -> Znth k (upd_Znth j sl (SDD q b bs dd)) = Znth k sl).
  { intros k Hk Hsk. rewrite upd_Znth_diff by (try lia; intro; subst; contradiction). reflexivity. }
  assert (Hidx: idx = nil \/ exists k, idx = [k] /\ 0 <= k < 2 /\ k <> j /\ isSDD (Znth k sl)).
  { destruct idx as [|k1 [|k2 rest]]; [left; reflexivity| |].
    - right. exists k1. apply Forall_inv in Hf. destruct Hf as [Hk1 Hs1].
      split; [reflexivity|]. split; [auto|]. split; [intro; subst; contradiction|auto].
    - exfalso. pose proof (Forall_inv Hf) as [Hk1 Hs1]. apply Forall_inv_tail in Hf.
      pose proof (Forall_inv Hf) as [Hk2 Hs2]. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin _].
      apply Hnin. left.
      assert (k1 <> j) by (intro; subst; contradiction).
      assert (k2 <> j) by (intro; subst; contradiction). lia. }
  assert (Hdict: match Some (ddict_ref q dd) with None => True | Some dr =>
     exists j0, 0 <= j0 < 2 /\ isSDD (Znth j0 (upd_Znth j sl (SDD q b bs dd))) /\
                dr = slot_ref (Znth j0 (upd_Znth j sl (SDD q b bs dd))) end).
  { exists j. rewrite Hjs. simpl. auto. }
  assert (Hsame: exists idx', NoDup idx' /\
      Forall (fun j0 => 0 <= j0 < 2 /\ isSDD (Znth j0 (upd_Znth j sl (SDD q b bs dd)))) idx' /\
      dc_set st = map (fun j0 => slot_e (Znth j0 (upd_Znth j sl (SDD q b bs dd)))) idx').
  { exists idx. split; [exact Hnd|]. split.
    + eapply Forall_impl; [|exact Hf]. intros k [Hk2 Hsk]. rewrite Hk by auto. auto.
    + rewrite Hset. apply map_ext_in. intros k Hin. rewrite Forall_forall in Hf. destruct (Hf k Hin).
      rewrite Hk by auto. reflexivity. }
  destruct Hr as [[-> ->] | (Hm & _ & ->)].
  - unfold ctx_ok, ctx_ds. destruct st; simpl in *.
    split; [|reflexivity]. repeat (split; [assumption|]).
    destruct (dp_multi dc_par =? 1); [|exact Hsame].
    unfold set_add. subst dc_set.
    destruct Hidx as [-> | (k & -> & Hk2 & Hkj & Hsk)].
    + exists [j]. simpl. split; [constructor; [intros []|constructor]|].
      split; [constructor; [rewrite Hjs; simpl; auto|constructor]|]. rewrite Hjs. reflexivity.
    + simpl. destruct (dd_id (slot_ddst (Znth k sl)) =? dd_id dd); simpl.
      * exists [j]. simpl. split; [constructor; [intros []|constructor]|].
        split; [constructor; [rewrite Hjs; simpl; auto|constructor]|]. rewrite Hjs. reflexivity.
      * exists [k; j]. simpl. split.
        { constructor; [intros [H|[]]; lia|constructor; [intros []|constructor]]. }
        split; [constructor; [rewrite Hk by auto; auto|constructor; [rewrite Hjs; simpl; auto|constructor]]|].
        rewrite Hjs, Hk by auto. reflexivity.
  - unfold ctx_ok, ctx_ds. destruct st; simpl in *.
    split; [|reflexivity]. repeat (split; [assumption|]). try exact Hsame.
Qed.

Section Res.
Variable DD : globals -> val -> ddict_st -> mpred.

(* a slot's DDict (with the caller's 0 bytes at b for an empty one, as ddict_res holds them) *)
Definition slot_ddres (gv: globals) (s: slot) : mpred :=
  match s with SDD q b bs dd => ddict_res DD gv Ews q dd | _ => emp end.

(* the same (v3.2: ddict_res carries the DDict pointer's validity, which main's NULL tests use) *)
Definition slot_ddres_v (gv: globals) (s: slot) : mpred := slot_ddres gv s.

(* the slot's buffer *)
Definition slot_buf (s: slot) : mpred :=
  match s with
  | SNone => emp
  | SBuf b c => sepcon (malloc_token Ews (tarray tuchar (Z.max 1 c)) b) (data_at_ Ews (tarray tuchar (Z.max 1 c)) b)
  | SDD _ b bs _ => sepcon (malloc_token Ews (tarray tuchar (Z.max 1 (Zlength bs))) b)
                  (@data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) b)
  end.

(* the current dictionary and the DDict set of the context, taken from the slots' DDicts; Rest: the
   slots' DDicts the context does not use *)
Lemma slots_arrange gv sl d l : Zlength sl = 2 -> ctx_ds sl d l ->
  exists Rest: mpred,
    (slot_ddres gv (Znth 0 sl) * slot_ddres gv (Znth 1 sl))%logic =
    (dict_res DD gv Ews d * set_res DD gv Ews l d * Rest)%logic.
Proof.
  intros Hl [Hd (idx & Hnd & Hf & ->)].
  assert (Hdr: forall s, isSDD s -> dict_res DD gv Ews (Some (slot_ref s)) = slot_ddres gv s)
    by (intros [] H; try contradiction; reflexivity).
  assert (Hcur: forall s, cur_ddict (Some (slot_ref s)) = Some (slot_q s)) by (intros; reflexivity).
  assert (He: forall s, isSDD s -> ddict_res DD gv Ews (fst (slot_e s)) (snd (slot_e s)) = slot_ddres gv s)
    by (intros [] H; try contradiction; reflexivity).
  assert (Hidx: idx = [] \/ idx = [0] \/ idx = [1] \/ idx = [0;1] \/ idx = [1;0]).
  { destruct idx as [|a [|b [|c r]]]; [auto| | |].
    - rewrite Forall_cons_iff in Hf. destruct Hf as [[Ha _] _]. assert (a = 0 \/ a = 1) as [-> | ->] by lia; auto.
    - rewrite Forall_cons_iff, Forall_cons_iff in Hf. destruct Hf as [[Ha _] [[Hb _] _]].
      apply NoDup_cons_iff in Hnd. destruct Hnd as [Hn _].
      assert (a <> b) by (intro; subst; apply Hn; left; auto).
      assert ((a = 0 /\ b = 1) \/ (a = 1 /\ b = 0)) as [[-> ->] | [-> ->]] by lia; auto.
    - exfalso. rewrite Forall_cons_iff, Forall_cons_iff, Forall_cons_iff in Hf.
      destruct Hf as [[Ha _] [[Hb _] [[Hc _] _]]].
      apply NoDup_cons_iff in Hnd. destruct Hnd as [Hn1 Hnd].
      apply NoDup_cons_iff in Hnd. destruct Hnd as [Hn2 _].
      assert (a <> b) by (intro; subst; apply Hn1; left; auto).
      assert (a <> c) by (intro; subst; apply Hn1; right; left; auto).
      assert (b <> c) by (intro; subst; apply Hn2; left; auto).
      lia. }
  assert (Hs: Forall (fun j => isSDD (Znth j sl)) idx) by (eapply Forall_impl; [|exact Hf]; intros ? []; auto).
  clear Hf Hnd.
  destruct Hidx as [-> | [-> | [-> | [-> | ->]]]];
  (destruct d as [dr|];
   [destruct Hd as (j & Hj & Hsj & ->); assert (j = 0 \/ j = 1) as [-> | ->] by lia;
    rewrite (Hdr _ Hsj) | ]);
  repeat match goal with H: Forall _ (_ :: _) |- _ => inv H end;
  unfold set_res; rewrite ?Hcur; cbn [map fold_right cur_ddict dict_res];
  rewrite ?He by auto;
  repeat match goal with |- context [Val.eq ?a ?b] => destruct (Val.eq a b) end;
  try match goal with H: ?x <> ?y |- _ => solve [exfalso; apply H; reflexivity] end;
  first
  [ exists emp; solve [apply pred_ext; cancel]
  | exists (slot_ddres gv (Znth 0 sl)); solve [apply pred_ext; cancel]
  | exists (slot_ddres gv (Znth 1 sl)); solve [apply pred_ext; cancel]
  | exists (slot_ddres gv (Znth 0 sl) * slot_ddres gv (Znth 1 sl))%logic; solve [apply pred_ext; cancel] ].
Qed.

End Res.

Lemma slot_sddict_ok W sl j : Zlength sl = 2 -> Forall slot_ok sl -> 0 <= j < 2 -> isSDD (Znth j sl) ->
  sddict_ok (W ++ slots_w sl) (slot_ddst (Znth j sl)).
Proof.
  intros Hl Hok Hj Hs.
  assert (Hsj: slot_ok (Znth j sl)) by (apply Forall_Znth; auto; lia).
  assert (Hw: pws_pred (W ++ slots_w sl) |-- pws_pred (slot_w (Znth j sl)) * TT).
  { unfold slots_w. rewrite !pws_app.
    destruct (Z.eq_dec j 0) as [->|Hj1]; [|replace j with 1 by lia]; cancel. }
  destruct (Znth j sl) as [| |q b bs dd] eqn:E; simpl in Hs; try contradiction.
  destruct Hsj as (_ & _ & _ & Hfc & Hb & Hr).
  unfold sddict_ok. simpl. rewrite Hr.
  destruct (Zlength bs =? 0) eqn:Hz; [|exact I].
  apply Z.eqb_eq in Hz. split; [rewrite Hb; apply Zlength_nil_inv; auto|].
  eapply derives_trans; [exact Hw|].
  simpl slot_w. rewrite pws_one. rewrite Hz in Hfc |- *.
  apply sepcon_valid_pointer1. apply rest_v0; auto.
Qed.

(* the slots' witnesses give stream_dict_ok (W: the witnesses of the call's buffers) *)
Lemma slots_stream_ok W sl st : Zlength sl = 2 -> Forall slot_ok sl ->
  ctx_ds sl (dc_dict st) (dc_set st) -> dc_bl st = None -> stream_dict_ok (W ++ slots_w sl) st.
Proof.
  intros Hl Hok [Hd (idx & _ & Hf & Hset)] Hbl.
  unfold stream_dict_ok. split; [|split; [|exact Hbl]].
  - destruct (dc_dict st) as [dr|]; [|exact I].
    destruct Hd as (j & Hj & Hs & ->).
    unfold slot_ref, ddict_ref. simpl. split; [reflexivity|].
    apply (slot_sddict_ok W sl j); auto.
  - rewrite Hset. apply Forall_map. eapply Forall_impl; [|exact Hf].
    intros j [Hj Hs]. unfold slot_e. simpl. apply (slot_sddict_ok W sl j); auto.
Qed.

(* a witness of the list *)
Lemma pws_in w W : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  induction W as [|w' W IH]; intros Hin; [contradiction|].
  unfold pws_pred; simpl. destruct Hin as [->|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin]|].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred w')), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

(* ... and dict_buf_ok for a one-shot call into dst (W: the witnesses of the call's buffers, showing dst valid) *)
Lemma slots_dict_buf_ok W sl d l cap dst : Zlength sl = 2 -> Forall slot_ok sl -> ctx_ds sl d l ->
  (pws_pred W * @data_at_ ZCS Ews (tarray tuchar cap) dst |-- valid_pointer dst) ->
  dict_buf_ok (W ++ slots_w sl) Ews d Ews cap dst.
Proof.
  intros Hl Hok [Hd _] HW. destruct d as [dr|]; [|exact I].
  destruct Hd as (j & Hj & Hs & ->).
  assert (Hsj: slot_ok (Znth j sl)) by (apply Forall_Znth; [exact Hok | lia]).
  destruct (Znth j sl) as [|b0 c0|q b bs dd] eqn:E; try contradiction.
  destruct Hsj as (_ & _ & _ & Hfc & Hb & Hr).
  unfold dict_buf_ok, slot_ref, ddict_ref. simpl. rewrite Hr, Hb.
  destruct (Zlength bs =? 0) eqn:Ez; [|exact I].
  apply Z.eqb_eq in Ez. right. split; [exact Ez|]. split.
  - rewrite Ez in Hfc.
    assert (Hin: In (rest_w b 0) (W ++ slots_w sl)).
    { apply in_or_app. right. unfold slots_w.
      assert (j = 0 \/ j = 1) as [->| ->] by lia; apply in_or_app; [left | right];
      rewrite E; simpl; rewrite Ez; left; reflexivity. }
    eapply derives_trans; [apply pws_in; exact Hin|].
    apply sepcon_valid_pointer1. apply rest_v0. exact Hfc.
  - rewrite pws_app.
    eapply derives_trans; [|apply (sepcon_valid_pointer1 (pws_pred W * @data_at_ ZCS Ews (tarray tuchar cap) dst)%logic (pws_pred (slots_w sl))); exact HW].
    change (@data_at_ Zstd.proof.zstd.Base.CompSpecs) with (@data_at_ ZCS). cancel.
Qed.

Lemma AP_InitGPred_In x l gv: In x l -> InitGPred l gv |-- globs2pred gv x * TT.
Proof.
  induction l as [|a l IH]; simpl; [contradiction | ].
  rewrite InitGPred_consD. intros [<- | Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] | ].
    rewrite <- sepcon_assoc, (sepcon_comm (globs2pred gv a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma AP_int_el {cs: compspecs} gv sh:
  Zstd.proof.top.MainPre6.MP_El gv sh tint Zstd.proof.top.MainPre6.MP_f32 Zstd.proof.top.MainPre6.MP_isint.
Proof.
  intros x q Hok Hfc. destruct x; try discriminate.
  simpl. rewrite sepcon_emp. change (Tint I32 Unsigned noattr) with tuint. rewrite mapsto_tuint_tint.
  rewrite <- (mapsto_data_at' sh tint (Vint i) (Vint i) q) by auto; apply derives_refl.
Qed.

Lemma AP_int_sz {cs: compspecs}:
  Zstd.proof.top.MainPre6.MP_Sz tint Zstd.proof.top.MainPre6.MP_f32 Zstd.proof.top.MainPre6.MP_isint.
Proof. intros x Hok. destruct x; try discriminate; reflexivity. Qed.

Lemma AP_params_glob gv:
  globs2pred gv (_ap_params, Gvar Zstd.harness.x_any_params.code.v_ap_params) |--
  data_at Ers (tarray tint 5) (map (fun k => Vint (Int.repr k))
        [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_forceIgnoreChecksum; ZSTD_d_refMultipleDDicts;
         ZSTD_d_maxBlockSize]) (gv _ap_params).
Proof.
  eapply (Zstd.proof.top.MainPre6.MP_glob' gv _ Zstd.harness.x_any_params.code.v_ap_params (tarray tint 5)
            (Zstd.proof.top.MainPre6.MP_arr_f tint Zstd.proof.top.MainPre6.MP_f32)
            (Zstd.proof.top.MainPre6.MP_arr_ok tint Zstd.proof.top.MainPre6.MP_isint 5)).
  - reflexivity.
  - apply Zstd.proof.top.MainPre6.MP_El_array; [apply AP_int_sz | apply AP_int_el].
  - reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - apply la_env_cs_sound; vm_compute; reflexivity.
Qed.

(* main's globals besides zstd_globals: the parameter table ap_params (the rest into TT) *)
Lemma ap_pre_globals gv :
  globals_ok gv ->
  InitGPred (filter (fun ig => negb (id_in_list (fst ig) Zstd.proof.top.MainPre6.zstd_var_ids))
                    (Vardefs Zstd.contracts.x_any_params.whole_prog)) gv
  |-- sepcon (data_at Ers (tarray tint 5) (map (fun k => Vint (Int.repr k))
        [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_forceIgnoreChecksum; ZSTD_d_refMultipleDDicts;
         ZSTD_d_maxBlockSize]) (gv _ap_params)) TT.
Proof.
  intros Hgv.
  eapply derives_trans;
    [ apply (AP_InitGPred_In (_ap_params, Gvar Zstd.harness.x_any_params.code.v_ap_params))
    | apply sepcon_derives; [apply AP_params_glob | apply derives_refl] ].
  apply filter_In. split.
  - apply (Zstd.proof.top.MainPre6.MP_incl_Vardefs _
             [(_ap_params, Gvar Zstd.harness.x_any_params.code.v_ap_params)]);
      [vm_compute; reflexivity | vm_compute; reflexivity | left; reflexivity].
  - vm_compute; reflexivity.
Qed.


(* ---------- main ---------- *)

Local Notation HCS := Zstd.proof.harness.any_params.HOK_any_params.CompSpecs.
Local Notation tout := (Tstruct _ZSTD_outBuffer_s noattr).
Local Notation tin := (Tstruct _ZSTD_inBuffer_s noattr).

Lemma AS_out: forall sh (a b c: val) p,
  @data_at ZCS sh t_outBuffer (a, (b, c)) p = @data_at HCS sh tout (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (adc_cce ZCS HCS) sh tout (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma AS_in: forall sh (a b c: val) p,
  @data_at ZCS sh t_inBuffer (a, (b, c)) p = @data_at HCS sh tin (a, (b, c)) p.
Proof.
  intros. pose proof (@data_at_change_composite ZCS HCS (adc_cce ZCS HCS) sh tin (a, (b, c)) (a, (b, c))
    (JMeq_refl _) ltac:(vm_compute; reflexivity)) as E. exact (f_equal (fun f => f p) E).
Qed.

Lemma tok_to_Z sh n p :
  @malloc_token HCS sh (tarray tuchar n) p |-- @malloc_token ZCS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ (adc_cce HCS ZCS) sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma tok_of_Z sh n p :
  @malloc_token ZCS sh (tarray tuchar n) p |-- @malloc_token HCS sh (tarray tuchar n) p.
Proof. rewrite (@malloc_token_change_composite _ _ (adc_cce HCS ZCS) sh (tarray tuchar n)) by reflexivity. apply derives_refl. Qed.

Lemma AS_chunk_in u : 0 <= u <= Int.max_unsigned ->
  Int.unsigned (Int.modu (Int.repr u) (Int.add (Int.repr 256) (Int.repr 1))) = u mod 257.
Proof.
  intros. change (Int.add (Int.repr 256) (Int.repr 1)) with (Int.repr 257).
  pose proof (Z.mod_pos_bound u 257 ltac:(lia)).
  unfold Int.modu. rewrite (Int.unsigned_repr u) by rep_lia.
  rewrite (Int.unsigned_repr 257) by rep_lia. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma AS_chunk_out u : 0 <= u <= Int.max_unsigned ->
  Int.unsigned (Int.add (Int.modu (Int.repr u) (Int.repr 256)) (Int.repr 1)) = u mod 256 + 1.
Proof.
  intros. pose proof (Z.mod_pos_bound u 256 ltac:(lia)).
  unfold Int.modu, Int.add.
  rewrite (Int.unsigned_repr u) by rep_lia.
  rewrite (Int.unsigned_repr 256) by rep_lia.
  rewrite (Int.unsigned_repr (u mod 256)) by rep_lia.
  rewrite (Int.unsigned_repr 1) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma ap_mod u k : 0 <= u <= Int.max_unsigned -> 0 < k <= Int.max_unsigned ->
  Int.unsigned (Int.modu (Int.repr u) (Int.repr k)) = u mod k.
Proof.
  intros. pose proof (Z.mod_pos_bound u k ltac:(lia)).
  unfold Int.modu. rewrite (Int.unsigned_repr u), (Int.unsigned_repr k) by rep_lia.
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Ltac AS_tc_null_test p :=
  apply denote_tc_test_eq_split; [|apply valid_pointer_null];
  destruct (eq_dec p nullval); [subst; apply valid_pointer_null|];
  rewrite ?(if_false (p = nullval)) by auto;
  match goal with |- context [malloc_token ?sh ?t p] =>
    destruct (zlt 0 (sizeof t));
    [ apply derives_trans with (data_at_ sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply data_at__valid_ptr; [auto | lia]
    | apply derives_trans with (malloc_token sh t p * TT)%logic; [cancel|];
      apply sepcon_valid_pointer1; apply malloc_token_valid_pointer; lia ]
  end.

Lemma AS_repr1_neq0: Int.repr 1 <> Int.zero.
Proof. intro H; inv H. Qed.

(* the witnesses lent to ZSTD_decompressStream for ib = malloc(max 1 il): its unused byte when il = 0 *)
Definition AS_W (il: Z) (ib: val) : list ptr_witness :=
  if zeq il 0 then [pw_bytes Ews 1 [Vundef] ib] else [].

Lemma AS_buf_ok_pos W n p : 0 < n -> buf_ok W Ews n p.
Proof.
  intros Hn. unfold buf_ok. rewrite data_at__memory_block. rewrite sepcon_andp_prop.
  apply derives_extract_prop; intros FC.
  replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
  assert (Hp: isptr p) by (destruct FC; auto).
  apply andp_right; apply sepcon_weak_valid_pointer2.
  - eapply derives_trans; [apply (memory_block_weak_valid_pointer Ews n p 0); auto; try lia |].
    rewrite isptr_offset_val_zero by auto. apply derives_refl.
  - apply memory_block_weak_valid_pointer; auto; lia.
Qed.

Lemma buf_ok_app W1 W2 sh n p : buf_ok W1 sh n p -> buf_ok (W1 ++ W2) sh n p.
Proof.
  unfold buf_ok. intros H. rewrite pws_app.
  eapply derives_trans with ((pws_pred W1 * @data_at_ ZCS sh (tarray tuchar n) p) * pws_pred W2)%logic; [cancel|].
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply H|]); [apply andp_left1 | apply andp_left2]; apply derives_refl.
Qed.

Lemma AS_buf_ok_zero p c : buf_ok [pw_bytes Ews 1 c p] Ews 0 p.
Proof.
  unfold buf_ok, pws_pred. simpl map. simpl fold_right. cbn [pw_pred]. rewrite sepcon_emp.
  assert_PROP (isptr p) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ p |- _ => destruct H as [? _]; auto end).
  rewrite isptr_offset_val_zero by auto.
  apply andp_right; apply sepcon_weak_valid_pointer1;
    (eapply derives_trans; [apply data_at_valid_ptr; auto; simpl; lia | apply valid_pointer_weak]).
Qed.

Lemma AS_buf_ok_W W il ib : 0 <= il -> buf_ok (AS_W il ib ++ W) Ews il ib.
Proof.
  intros. apply buf_ok_app. unfold AS_W. destruct (zeq il 0).
  - subst. apply AS_buf_ok_zero.
  - apply AS_buf_ok_pos. lia.
Qed.

Lemma AS_ib_split ib il m A : Zlength A = il -> (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar m) (A ++ Zrepeat Vundef (m - il)) ib |--
  (@data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (AS_W il ib)).
Proof.
  intros HA [[Hil ->] | [-> ->]].
  - unfold AS_W. destruct (zeq il 0); [lia|]. rewrite Z.sub_diag.
    change (Zrepeat Vundef 0) with (@nil val). rewrite app_nil_r.
    unfold pws_pred; simpl. rewrite sepcon_emp. apply derives_refl.
  - apply Zlength_nil_inv in HA. subst A. unfold AS_W. rewrite if_true by auto.
    unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (isptr ib) by (saturate_local; apply prop_right; match goal with H: field_compatible _ _ ib |- _ => destruct H as [? _]; auto end).
    change (Zrepeat Vundef (1 - 0)) with [Vundef].
    rewrite <- (emp_sepcon (@data_at ZCS Ews (tarray tuchar 1) [Vundef] ib)) at 1.
    apply sepcon_derives; [apply data_at_zero_array; auto | apply derives_refl].
Qed.

Lemma AS_ib_join ib il m A : (0 < il /\ m = il) \/ (il = 0 /\ m = 1) ->
  @data_at ZCS Ews (tarray tuchar il) A ib * pws_pred (AS_W il ib) |-- @data_at_ ZCS Ews (tarray tuchar m) ib.
Proof.
  intros [[Hil ->] | [-> ->]].
  - unfold AS_W. destruct (zeq il 0); [lia|]. unfold pws_pred; simpl. rewrite sepcon_emp.
    apply data_at_data_at_.
  - unfold AS_W. rewrite if_true by auto. unfold pws_pred; simpl. rewrite sepcon_emp.
    assert_PROP (A = []) by (entailer!; apply Zlength_nil_inv; auto). subst A.
    sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) ib); auto.
    rewrite emp_sepcon. apply data_at_data_at_.
Qed.

Lemma AS_ltu64_false: forall a b, 0 <= a <= Int64.max_unsigned -> 0 <= b <= Int64.max_unsigned -> a <= b ->
  Int64.ltu (Int64.repr b) (Int64.repr a) = false.
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt b a); [lia | reflexivity].
Qed.

(* the in-list witness of a malloc'd block of n bytes (its malloc_token) shows src valid *)
Lemma pws_in' W w : In w W -> pws_pred W |-- pw_pred w * TT.
Proof.
  unfold pws_pred. induction W as [|a W IH]; simpl; [contradiction|]. intros [<-|Hin].
  - apply sepcon_derives; [apply derives_refl | apply TT_right].
  - eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH; exact Hin] |].
    rewrite <- sepcon_assoc, (sepcon_comm (pw_pred a)), sepcon_assoc.
    apply sepcon_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma buf_ok_tok W sh n p : In (pw_token Ews (tarray tuchar n) p) W -> readable_share sh -> 0 <= n -> isptr p ->
  buf_ok W sh n p.
Proof.
  intros Hin Hsh Hn Hp. unfold buf_ok.
  eapply derives_trans; [apply sepcon_derives; [apply (pws_in' W _ Hin) | apply derives_refl] |].
  simpl pw_pred.
  destruct (zlt 0 n) as [Hpos|Hz].
  - rewrite (@data_at__memory_block ZCS). normalize.
    replace (sizeof (tarray tuchar n)) with n by (simpl; lia).
    apply andp_right; apply sepcon_weak_valid_pointer2.
    + rewrite <- (isptr_offset_val_zero p) at 2 by exact Hp.
      apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
    + apply memory_block_weak_valid_pointer; [lia | lia | apply readable_nonidentity; exact Hsh].
  - assert (n = 0) by lia. subst n. rewrite isptr_offset_val_zero by exact Hp.
    rewrite sepcon_assoc.
    assert (Hv: @malloc_token ZCS Ews (tarray tuchar 0) p |-- weak_valid_pointer p)
      by (eapply derives_trans; [apply malloc_token_valid_pointer; simpl; lia | apply valid_pointer_weak]).
    apply andp_right; apply sepcon_weak_valid_pointer1; exact Hv.
Qed.

(* ---------- the parameter table and the parameter calls ---------- *)

Definition ap_list : list Z :=
  [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_forceIgnoreChecksum; ZSTD_d_refMultipleDDicts; ZSTD_d_maxBlockSize].

Lemma ap_cases w : 0 <= w < 5 -> w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4.
Proof. lia. Qed.

Lemma ap_in w : 0 <= w < 5 ->
  In (Znth w ap_list) [ZSTD_d_windowLogMax; ZSTD_d_format; ZSTD_d_stableOutBuffer; ZSTD_d_forceIgnoreChecksum;
                       ZSTD_d_refMultipleDDicts; ZSTD_d_maxBlockSize].
Proof. intros Hw. destruct (ap_cases w Hw) as [->|[->|[->|[->| ->]]]]; simpl; tauto. Qed.

Lemma ap_param_ok sl st st' r w v : 0 <= w < 5 -> ctx_ok sl st ->
  (if Znth w ap_list =? ZSTD_d_stableOutBuffer then
     (if ((0 <=? v) && (v <=? 1))%bool then r = 0 /\ st' = set_stable st (v =? 1)
      else is_error_code r = true /\ st' = st)
   else match param_set (dc_par st) (Znth w ap_list) v with
        | Some p' => r = 0 /\ st' = set_par st p'
        | None => is_error_code r = true /\ st' = st
        end) -> ctx_ok sl st'.
Proof.
  intros Hw Hc H.
  assert (E: Znth w ap_list =? ZSTD_d_stableOutBuffer = false)
    by (destruct (ap_cases w Hw) as [->|[->|[->|[->| ->]]]]; reflexivity).
  rewrite E in H. destruct (param_set _ _ _); destruct H as [_ ->]; auto using ctx_ok_par.
Qed.

Lemma ap_mws_ok sl st st' r m : ctx_ok sl st ->
  (if ((2 ^ 10 <=? m) && (m <=? 2 ^ 31))%bool
   then r = 0 /\ st' = set_par st {| dp_fmt := dp_fmt (dc_par st); dp_ignore := dp_ignore (dc_par st);
                                     dp_bmax := dp_bmax (dc_par st); dp_wmax := m;
                                     dp_multi := dp_multi (dc_par st) |}
   else is_error_code r = true /\ st' = st) -> ctx_ok sl st'.
Proof. intros Hc H. destruct (_ && _)%bool; destruct H as [_ ->]; auto using ctx_ok_par. Qed.

(* ---------- the slots' resources ---------- *)

Lemma slot_at_ok sl j : Forall slot_ok sl -> 0 <= j < Zlength sl -> slot_ok (Znth j sl).
Proof. intros H Hj. exact (proj1 (Forall_Znth _ _) H j Hj). Qed.

Section Slots.
Variable DD : globals -> val -> ddict_st -> mpred.

Definition slot_one (gv: globals) (s: slot) : mpred :=
  (slot_buf s * slot_ddres_v DD gv s * pws_pred (slot_w s))%logic.
Definition slots_res (gv: globals) (sl: list slot) : mpred :=
  (slot_one gv (Znth 0 sl) * slot_one gv (Znth 1 sl))%logic.

Lemma slots_res_none gv : slots_res gv [SNone; SNone] = emp.
Proof. unfold slots_res, slot_one, pws_pred. simpl. rewrite !emp_sepcon. reflexivity. Qed.

Lemma slots_res_j gv sl j : 0 <= j < 2 ->
  slots_res gv sl = (slot_one gv (Znth j sl) * slot_one gv (Znth (1 - j) sl))%logic.
Proof.
  intros. unfold slots_res. assert (j = 0 \/ j = 1) as [->| ->] by lia; simpl; [reflexivity | apply sepcon_comm].
Qed.

Lemma slots_res_upd gv sl j s : Zlength sl = 2 -> 0 <= j < 2 ->
  (slot_one gv s * slot_one gv (Znth (1 - j) sl))%logic = slots_res gv (upd_Znth j sl s).
Proof.
  intros. rewrite (slots_res_j gv _ j) by auto. rewrite upd_Znth_same by lia.
  rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma slots_vp gv sl j : 0 <= j < 2 -> isSDD (Znth j sl) ->
  slots_res gv sl |-- valid_pointer (slot_q (Znth j sl)).
Proof.
  intros Hj Hs. rewrite (slots_res_j gv sl j Hj). unfold slot_one.
  destruct (Znth j sl) as [| | q b bs]; simpl in Hs |- *; try contradiction.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply sepcon_valid_pointer1. apply andp_left2, derives_refl.
Qed.

Lemma slot_one_non gv s : ~ isSDD s -> slot_one gv s = slot_buf s.
Proof. intros H. destruct s; simpl in H; try contradiction; unfold slot_one, pws_pred; simpl; rewrite !sepcon_emp; reflexivity. Qed.

Lemma slot_one_sdd gv q b bs dd : slot_one gv (SDD q b bs dd) =
  (malloc_token Ews (tarray tuchar (Z.max 1 (Zlength bs))) b *
   @data_at ZCS Ews (tarray tuchar (Zlength bs)) (zbytes bs) b *
   (andp (DD gv q dd) (valid_pointer q) *
    (match dd_ref dd with
                   | Some p => @data_at ZCS Ews (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
                   | None => emp end)) *
   pws_pred [rest_w b (Zlength bs)])%logic.
Proof. reflexivity. Qed.

(* after the parameter loop: the DDict pointers are no longer compared *)
Definition slots_after (gv: globals) (sl: list slot) : mpred :=
  (slot_buf (Znth 0 sl) * slot_buf (Znth 1 sl) * pws_pred (slots_w sl) *
   (slot_ddres DD gv (Znth 0 sl) * slot_ddres DD gv (Znth 1 sl)))%logic.

Lemma slot_drop_v gv s : slot_ddres_v DD gv s |-- slot_ddres DD gv s.
Proof. apply derives_refl. Qed.

Lemma slots_to_after gv sl : slots_res gv sl |-- slots_after gv sl.
Proof.
  unfold slots_res, slots_after, slot_one, slots_w. rewrite pws_app.
  sep_apply (slot_drop_v gv (Znth 0 sl)). sep_apply (slot_drop_v gv (Znth 1 sl)). cancel.
Qed.

(* what main frees at the end: a slot's DDict and buffer *)
Definition slot_sz (s: slot) : Z :=
  Z.max 1 (match s with SNone => 0 | SBuf _ c => c | SDD _ _ bs _ => Zlength bs end).
Definition slot_odd (s: slot) : option ddict_st :=
  match s with SDD _ b bs dd => Some dd | _ => None end.
Definition slot_fin (gv: globals) (s: slot) : mpred :=
  ((match slot_odd s with None => emp | Some dd => DD gv (slot_q s) dd end) *
   (if eq_dec (slot_b s) nullval then emp
    else malloc_token Ews (tarray tuchar (slot_sz s)) (slot_b s) * data_at_ Ews (tarray tuchar (slot_sz s)) (slot_b s)))%logic.

Lemma slot_to_fin gv s : slot_ok s ->
  (slot_buf s * pws_pred (slot_w s) * slot_ddres DD gv s)%logic |-- slot_fin gv s.
Proof.
  intros Hok. destruct s as [|b c|q b bs dd]; unfold slot_fin, slot_buf, slot_ddres, slot_w; cbn [slot_odd slot_b slot_q slot_sz].
  - rewrite if_true by auto. unfold pws_pred. simpl. cancel.
  - destruct Hok as [Hb Hc]. rewrite if_false by (destruct b; try contradiction; discriminate).
    unfold pws_pred. simpl. cancel.
  - destruct Hok as (Hq & Hl & Hbo & Hfc & Hdb & Hdr).
    assert (Hb: isptr b) by (destruct Hfc; auto).
    rewrite if_false by (destruct b; try contradiction; discriminate).
    rewrite pws_one.
    sep_apply (buf_parts_free b (Zlength bs) (zbytes bs) (Zlength_nonneg _) Hfc).
    unfold ddict_res. rewrite Hdr, Hdb.
    sep_apply (andp_left1 (DD gv q dd) (valid_pointer q) (DD gv q dd) (derives_refl _)).
    destruct (Zlength bs =? 0) eqn:E.
    + apply Z.eqb_eq in E. apply Zlength_nil_inv in E. subst bs. rewrite E. unfold slot_sz. rewrite Zlength_nil. simpl map.
      sep_apply (@data_at_zero_array_inv ZCS Ews tuchar (@nil val) b); auto. cancel.
    + cancel.
Qed.

Lemma slots_after_fin gv sl : Zlength sl = 2 -> Forall slot_ok sl ->
  slots_after gv sl |-- slot_fin gv (Znth 0 sl) * slot_fin gv (Znth 1 sl).
Proof.
  intros Hl Hf. unfold slots_after, slots_w. rewrite pws_app.
  sep_apply (slot_to_fin gv (Znth 0 sl) ltac:(apply slot_at_ok; auto; lia)).
  sep_apply (slot_to_fin gv (Znth 1 sl) ltac:(apply slot_at_ok; auto; lia)).
  cancel.
Qed.

End Slots.

#[export] Hint Extern 1 (andp _ (valid_pointer ?p) |-- valid_pointer ?p) => (apply andp_left2, derives_refl) : valid_pointer.


Lemma isSDD_dec s : {isSDD s} + {~ isSDD s}.
Proof. destruct s; simpl; auto. Qed.
Lemma slot_q_non s : ~ isSDD s -> slot_q s = nullval.
Proof. destruct s; simpl; tauto. Qed.
Lemma slot_w_non s : ~ isSDD s -> slot_w s = [].
Proof. destruct s; simpl; tauto. Qed.
Lemma slot_ddres_v_non DD gv s : ~ isSDD s -> slot_ddres_v DD gv s = emp.
Proof. destruct s; simpl; tauto. Qed.

Lemma slot_buf_free s : ~ isSDD s -> slot_ok s ->
  slot_buf s |-- (if eq_dec (slot_b s) nullval then emp else
    (malloc_token Ews (tarray tuchar (slot_sz s)) (slot_b s) * data_at_ Ews (tarray tuchar (slot_sz s)) (slot_b s))).
Proof.
  destruct s as [|b c|q b bs]; simpl; intros Hn Hok; try tauto.
  - destruct (eq_dec nullval nullval); [apply derives_refl | contradiction].
  - destruct Hok as [Hb _]. rewrite if_false by (intro; subst; contradiction). apply derives_refl.
Qed.

Lemma zero_piece d (bs: list Z) (dd: ddict_st) : isptr d -> dd_bytes dd = bs ->
  dd_ref dd = (if Zlength bs =? 0 then Some d else None) ->
  emp |-- (match dd_ref dd with
           | Some p => @data_at ZCS Ews (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
           | None => emp end).
Proof.
  intros Hd Hb Hr. rewrite Hr, Hb. destruct (Zlength bs =? 0) eqn:E; [|apply derives_refl].
  apply Z.eqb_eq in E. rewrite E. apply Zlength_nil_inv in E. subst bs. apply data_at_zero_array; auto.
  rewrite E. reflexivity.
Qed.

Lemma ap_modu u k : 0 <= u <= Int.max_unsigned -> 0 < k <= Int.max_unsigned ->
  Int.modu (Int.repr u) (Int.repr k) = Int.repr (u mod k).
Proof. intros. unfold Int.modu. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma slot_q_pn s : slot_ok s -> is_pointer_or_null (slot_q s).
Proof. destruct s as [| b c | q b bs dd]; simpl; intros; auto. destruct H as [Hq _]. destruct q; try contradiction; exact I. Qed.
Lemma slot_b_pn s : slot_ok s -> is_pointer_or_null (slot_b s).
Proof.
  destruct s as [| b c | q b bs dd]; simpl; intros; auto.
  - destruct H as [Hb _]. destruct b; try contradiction; exact I.
  - destruct H as (_ & _ & _ & Hfc & _). destruct Hfc as [Hb _]. destruct b; try contradiction; exact I.
Qed.

Lemma ctx_ok_upd_non sl j s st : Zlength sl = 2 -> 0 <= j < 2 -> ~ isSDD (Znth j sl) -> ~ isSDD s ->
  ctx_ok sl st -> ctx_ok (upd_Znth j sl s) st.
Proof. unfold ctx_ok. intros ? ? ? ? (? & ? & ? & ? & ? & ?). split; [|split; [|split; [|split; [|split]]]]; auto. apply ctx_ds_upd_non; auto. Qed.

Lemma ap_dn u : 0 <= u <= Int.max_unsigned ->
  Int.unsigned (Int.modu (Int.repr u) (Int.add (Int.repr 512) (Int.repr 1))) = u mod 513.
Proof.
  intros. change (Int.add (Int.repr 512) (Int.repr 1)) with (Int.repr 513).
  pose proof (Z.mod_pos_bound u 513 ltac:(lia)).
  unfold Int.modu. rewrite (Int.unsigned_repr u) by rep_lia.
  rewrite (Int.unsigned_repr 513) by rep_lia. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma map_slot_q_upd_non sl j s : Zlength sl = 2 -> 0 <= j < 2 -> ~ isSDD (Znth j sl) -> ~ isSDD s ->
  map slot_q (upd_Znth j sl s) = map slot_q sl.
Proof.
  intros Hl Hj Hn Hs. rewrite <- upd_Znth_map. rewrite (slot_q_non s Hs).
  apply upd_Znth_triv; [rewrite Zlength_map; lia|]. rewrite Znth_map by lia. apply slot_q_non; auto.
Qed.

Lemma slot_odd_pre s : match slot_odd s with None => slot_q s = nullval | Some _ => True end.
Proof. destruct s; simpl; auto. Qed.

Lemma sublist_next {A} {d: Inhabitant A} (l: list A) i : 0 <= i < Zlength l ->
  sublist i (Zlength l) l = Znth i l :: sublist (i + 1) (Zlength l) l.
Proof. intros. rewrite (sublist_split i (i + 1) (Zlength l)) by lia. rewrite sublist_len_1 by lia. reflexivity. Qed.

Lemma fins_start DD gv sl : Zlength sl = 2 ->
  (slot_fin DD gv (Znth 0 sl) * slot_fin DD gv (Znth 1 sl))%logic |--
  fold_right sepcon emp (map (slot_fin DD gv) (sublist 0 2 sl)).
Proof.
  intros Hl. destruct sl as [|a [|b [|c l]]]; try (exfalso; list_solve).
  unfold sublist. simpl. change (Znth 0 [a; b]) with a. change (Znth 1 [a; b]) with b.
  rewrite sepcon_emp. apply derives_refl.
Qed.

Ltac ret_frame :=
  repeat match goal with |- context [data_at Tsh ?t ?v ?p] => sep_apply (data_at_data_at_ Tsh t v p) end;
  cancel.

Lemma pws_cons2 a b W : pws_pred (a :: b :: W) = (pw_pred a * pw_pred b * pws_pred W)%logic.
Proof. unfold pws_pred. simpl. rewrite sepcon_assoc. reflexivity. Qed.

Lemma ddres_pair_j DD gv sl j : 0 <= j < 2 -> ~ isSDD (Znth j sl) ->
  slot_ddres DD gv (Znth (1 - j) sl) = (slot_ddres DD gv (Znth 0 sl) * slot_ddres DD gv (Znth 1 sl))%logic.
Proof.
  intros Hj Hn.
  assert (E: slot_ddres DD gv (Znth j sl) = emp) by (destruct (Znth j sl); simpl in Hn |- *; tauto).
  assert (j = 0 \/ j = 1) as [-> | ->] by lia; simpl in *; rewrite E; [rewrite emp_sepcon | rewrite sepcon_emp]; reflexivity.
Qed.

Lemma ctx_ds_len sl d l : ctx_ds sl d l -> Zlength l < 2 ^ 20.
Proof.
  intros [_ (idx & Hnd & Hf & ->)]. rewrite Zlength_map.
  assert (Hin: incl idx [0; 1]).
  { intros k Hk. rewrite Forall_forall in Hf. destruct (Hf k Hk) as [Hk2 _].
    assert (k = 0 \/ k = 1) as [-> | ->] by lia; simpl; auto. }
  pose proof (NoDup_incl_length Hnd Hin) as Hlen. simpl in Hlen.
  rewrite Zlength_correct. lia.
Qed.

Lemma slots_set_buf_ok W sl d l cap dst : Zlength sl = 2 -> Forall slot_ok sl -> ctx_ds sl d l ->
  (pws_pred W * @data_at_ ZCS Ews (tarray tuchar cap) dst |-- valid_pointer dst) ->
  Forall (fun e => ddict_buf_ok (W ++ slots_w sl) Ews (snd e) Ews cap dst) l.
Proof.
  intros Hl Hok [_ (idx & _ & Hf & ->)] HW. apply Forall_map. eapply Forall_impl; [|exact Hf].
  intros j [Hj Hs]. cbv beta. unfold slot_e. simpl snd.
  pose proof (slots_dict_buf_ok W sl (Some (slot_ref (Znth j sl))) nil cap dst Hl Hok) as H.
  apply H; [|exact HW].
  split; [exists j; auto|]. exists nil. split; [constructor|]. split; [constructor | reflexivity].
Qed.

Lemma oneshot_dctx_cap st s cap r out : oneshot_dctx st s cap r out -> is_error_code r = false -> r <= cap.
Proof. unfold oneshot_dctx. destruct (dc_set st); intros [H _]; exact H. Qed.

Ltac assume_fix := match goal with H: b2i _ <> Int.zero |- _ => apply b2i_nz, Z.leb_le in H end.

Section G.
Variable DC : globals -> val -> dctx_st -> mpred.
Variable DD : globals -> val -> ddict_st -> mpred.

Definition G0 : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   ZSTD_isError_spec; ZSTD_decompressDCtx_spec DC DD; ZSTD_decompressStream_spec DC DD;
   ZSTD_createDCtx_spec DC; ZSTD_freeDCtx_spec DC; ZSTD_DCtx_reset_spec DC;
   ZSTD_DCtx_setParameter_spec DC; ZSTD_DCtx_setMaxWindowSize_aspec DC;
   ZSTD_createDDict_spec DD; ZSTD_freeDDict_spec DD; ZSTD_DCtx_refDDict_spec DC DD;
   nondet_u32_spec; nondet_size_spec; nondet_bytes_nn_spec; gp_assert_spec; gp_assume_spec].

Lemma pre_globals gv : globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_any_params.whole_prog) gv |--
  zstd_globals gv * (data_at Ers (tarray tint 5) (map (fun k => Vint (Int.repr k)) ap_list) (gv _ap_params) * TT).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (Zstd.proof.top.MainPre6.main_pre_fact6 Zstd.contracts.x_any_params.whole_prog); [|exact Hgv].
    unfold Zstd.proof.top.MainPre6.all_progs. simpl. tauto.
  - apply sepcon_derives; [apply derives_refl | apply ap_pre_globals; exact Hgv].
Qed.

Lemma vars_in_Vprog (G: funspecs) :
  Forall (fun ig : ident * globvar type => isSome (Maps.PTree.get (fst ig) (make_tycontext_g Vprog G)))
    (QPprog_vars Zstd.contracts.x_any_params.whole_prog).
Proof.
  apply Forall_forall. intros [i v] Hin. unfold Vprog, QPvarspecs.
  pose proof (vars_in_tycontext (QPprog_vars Zstd.contracts.x_any_params.whole_prog) G) as H.
  rewrite Forall_forall in H. apply (H (i, v) Hin).
Qed.

Lemma body_main_G0 : semax_body Vprog G0 f_main main_spec.
Proof.
  change (semax_body Vprog G0 f_main (_main, WITH gv: globals PRE [] VST.floyd.VSU.main_pre
    Zstd.contracts.x_any_params.whole_prog tt gv POST [tint] (fun _ : environ => TT))).
  replace (fun _ : environ => @TT mpred _) with (PROP () LOCAL () SEP (@TT mpred _))
    by (extensionality rho; unfold PROPx, LOCALx, SEPx; simpl; normalize).
  start_function1.
  eapply (main_pre_InitGpred (zstd_globals gv * (data_at Ers (tarray tint 5) (map (fun k => Vint (Int.repr k)) ap_list) (gv _ap_params) * TT))%logic).
  { apply pre_globals. }
  { reflexivity. }
  { apply vars_in_Vprog. }
  start_function3.
  sep_apply (create_mem_mgr gv).
  forward_call tt. Intros n.
  forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  forward_call (b2i (n <=? 4096)).
  { entailer!. simpl. rewrite le64_b2i by rep_lia. reflexivity. }
  Intros. assume_fix.
  forward_call (tarray tuchar n, gv).
  { simpl. rep_lia. }
  Intros src.
  destruct (eq_dec src nullval) as [Hsrc|Hsrc].
  { subst src. forward_if. forward. entailer!. exfalso. auto. }
  Intros. forward_if. contradiction.
  forward_call (src, n, Ews).
  Intros s.
  forward_call tt. Intros cap.
  forward_call (b2i (cap <=? 65536)).
  { entailer!. simpl. rewrite le64_b2i by rep_lia. reflexivity. }
  Intros. assume_fix.
  forward_for_simple_bound 2 (EX i: Z,
    PROP ()
    LOCAL (temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _dst nullval;
           temp _got (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0));
           temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
           lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
           lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
    SEP (mem_mgr gv; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
         data_at Tsh (tarray (tptr tuchar) 2) (Zrepeat nullval i ++ Zrepeat Vundef (2 - i)) v_dbuf;
         data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (Zrepeat nullval i ++ Zrepeat Vundef (2 - i)) v_dd;
         zstd_globals gv; data_at Ers (tarray tint 5) (zbytes ap_list) (gv _ap_params);
         malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes s) src;
         TT; has_ext tt))%assert.
  { entailer!. }
  { forward. forward. entailer!.
    rewrite !upd_Znth_app2 by (rewrite !Zlength_Zrepeat; lia).
    rewrite !Zlength_Zrepeat by lia. replace (i - i) with 0 by lia.
    replace (Zrepeat Vundef (2 - i)) with (Vundef :: Zrepeat Vundef (2 - (i + 1))) by (list_solve).
    rewrite !upd_Znth0. replace (Zrepeat nullval (i + 1)) with (Zrepeat nullval i ++ [nullval]) by list_solve.
    rewrite <- !app_assoc. cancel. }
  change (Zrepeat nullval 2 ++ Zrepeat Vundef (2 - 2)) with [nullval; nullval].
  forward_call gv.
  Intros dctx.
  destruct (eq_dec dctx nullval) as [Hdc|Hdc].
  { subst dctx. forward_if.
    - forward_call (tarray tuchar n, src, gv).
      { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes s) src). cancel. }
      forward. entailer!.
    - exfalso; auto. }
  forward_if. contradiction.
  sep_apply (andp_left1 (DC gv dctx dctx_init) (valid_pointer dctx) (DC gv dctx dctx_init) (derives_refl _)).
  forward_for_simple_bound 8 (EX i: Z, EX sl: list slot, EX st: dctx_st,
    PROP (Zlength sl = 2; Forall slot_ok sl; ctx_ok sl st)
    LOCAL (temp _dctx dctx; temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _dst nullval;
           temp _got (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr n));
           lvar _out tout v_out; lvar _in tin v_in; lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
           lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
    SEP (DC gv dctx st; mem_mgr gv; zstd_globals gv; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
         data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
         data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
         data_at Ers (tarray tint 5) (zbytes ap_list) (gv _ap_params);
         malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes s) src;
         slots_res DD gv sl; TT; has_ext tt))%assert.
  { Exists [SNone; SNone] dctx_init. rewrite slots_res_none. entailer!.
    split; [repeat constructor | apply ctx_ok_init]. }
  { (* one parameter step *)
    Intros.
    match goal with H: ctx_ok sl st |- _ => pose proof H as Hcx; destruct H as (Hss & Hbl & Hlast & Hstab & Hmem & Hds) end.
    forward_call tt. Intros u5. forward.
    rewrite ap_modu by rep_lia.
    pose proof (Z.mod_pos_bound u5 7 ltac:(lia)) as Hw.
    forward_if (EX sl': list slot, EX st': dctx_st,
     PROP (Zlength sl' = 2; Forall slot_ok sl'; ctx_ok sl' st')
     LOCAL (temp _i (Vint (Int.repr i)); temp _dctx dctx; temp _cap (Vlong (Int64.repr cap)); temp _src src; temp _dst nullval;
           temp _got (Vlong (Int64.repr 0)); temp _ipos (Vlong (Int64.repr 0)); temp _n (Vlong (Int64.repr n));
           lvar _out tout v_out; lvar _in tin v_in; lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
           lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
     SEP (DC gv dctx st'; mem_mgr gv; zstd_globals gv; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
         data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl') v_dbuf;
         data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl') v_dd;
         data_at Ers (tarray tint 5) (zbytes ap_list) (gv _ap_params);
         malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes s) src;
         slots_res DD gv sl'; TT; has_ext tt))%assert.
    { (* which < 5: ZSTD_DCtx_setParameter *)
      assert (Hw5': 0 <= u5 mod 7 < Zlength ap_list) by (change (Zlength ap_list) with 5; lia).
      forward_call tt. Intros v6. forward.
      forward_call (gv, dctx, st, Znth (u5 mod 7) ap_list, Int.signed (Int.repr v6)).
      { entailer!. rewrite Int.repr_signed. reflexivity. }
      { apply ap_in; lia. }
      Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
      match goal with H: after_stage _ _ _ _ |- _ =>
        apply after_stage_init in H; [unfold setpar_res in H | exact (proj1 Hcx)] end.
      match goal with H: context [param_set] |- _ =>
        assert (Hc': ctx_ok sl st') by (eapply ap_param_ok; [ | exact Hcx | exact H]; lia); clear H end.
      Exists sl st'. entailer!. }
    { forward_if.
      { (* which = 5: ZSTD_DCtx_setMaxWindowSize *)
        forward_call tt. Intros u7. forward_call tt. Intros u8.
        match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
          forward_if (EX sft: Z, PROPx ((sft = 0 \/ sft = 8) :: P) (LOCALx (temp _t'9 (Vint (Int.repr sft)) :: L) (SEPx R))) end.
        { forward. Exists 0. entailer!. }
        { forward. Exists 8. entailer!. }
        Intros sft.
        forward_call (gv, dctx, st, Int64.unsigned (Int64.shl (Int64.repr u7) (Int64.repr sft))).
        { change (Int.unsigned Int64.iwordsize') with 64; lia. }
        { entailer!; rewrite Int64.repr_unsigned; simpl; reflexivity. }
        Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
        match goal with H: context [set_par] |- _ =>
          assert (Hc': ctx_ok sl st') by (eapply ap_mws_ok; [exact Hcx | exact H]); clear H end.
        Exists sl st'. entailer!. }
      { (* which = 6: a dictionary for slot i mod 2 *)
        assert (Hj: 0 <= i mod 2 < 2) by (apply Z.mod_pos_bound; lia).
        forward.
        { entailer!. rewrite Znth_map by lia. apply slot_q_pn, slot_at_ok; auto; lia. }
        rewrite Znth_map by lia.
        assert (Hsj: slot_ok (Znth (i mod 2) sl)) by (apply slot_at_ok; auto; lia).
        destruct (isSDD_dec (Znth (i mod 2) sl)) as [Hy|Hn].
        { (* the slot has its DDict: nothing *)
          assert (Hq: isptr (slot_q (Znth (i mod 2) sl))).
          { destruct (Znth (i mod 2) sl) as [| |q b bs]; simpl in Hy |- *; try contradiction. apply Hsj. }
          forward_if.
          { entailer!. apply denote_tc_test_eq_split; [|apply valid_pointer_null].
            eapply derives_trans with (slots_res DD gv sl * TT)%logic; [cancel|].
            apply sepcon_valid_pointer1. apply slots_vp; auto. }
          { exfalso. destruct (slot_q (Znth (i mod 2) sl)); try contradiction; discriminate. }
          { forward. Exists sl st. entailer!. } }
        rewrite (slot_q_non _ Hn).
        forward_if.
        2: { exfalso. auto. }
        forward_call tt. Intros u10. forward.
        rewrite ap_dn by lia.
        pose proof (Z.mod_pos_bound u10 513 ltac:(lia)) as Hdn.
        set (dn := u10 mod 513) in *. clearbody dn.
        forward.
        { entailer!. rewrite Znth_map by lia. apply slot_b_pn; auto. }
        rewrite Znth_map by lia.
        rewrite (slots_res_j DD gv sl (i mod 2) Hj). rewrite (slot_one_non DD gv _ Hn).
        sep_apply (slot_buf_free (Znth (i mod 2) sl) Hn Hsj).
        forward_call (tarray tuchar (slot_sz (Znth (i mod 2) sl)), slot_b (Znth (i mod 2) sl), gv).
        if_set_post _t'11 (Vlong (Int64.repr (Z.max 1 dn))).
        { forward. entailer!. norm. do 2 f_equal; lia. }
        { forward. entailer!. norm. do 2 f_equal; lia. }
        forward_call (tarray tuchar (Z.max 1 dn), gv).
        { simpl. rep_lia. }
        Intros d. forward.
        assert_PROP (is_pointer_or_null d) as PNd by (destruct (eq_dec d nullval); entailer!).
        sep_apply (malloc_buf d dn); [lia|].
        forward.
        forward_if.
        { (* a buffer: its bytes, then the DDict *)
          rewrite (buf_res_nn d) by auto. Intros.
          rewrite (adc_data_at_cs ZCS CompSpecs Ews dn).
          forward_call (d, dn, Ews). Intros bs.
          match goal with H: Zlength bs = dn |- _ => subst dn end.
          rewrite (adc_data_at_cs CompSpecs ZCS Ews (Zlength bs)).
          rewrite <- (pws_one (rest_w d (Zlength bs))).
          forward_call ([rest_w d (Zlength bs)], gv, Ews, d, bs).
          { rewrite bytes_at_ptr by (apply ptr_nn; auto). cancel. }
          { try (split; [intro; contradiction |]).
            split; [intros _; apply (buf_ok_of [] []); auto; rep_lia | apply bytes_ok_of; auto]. }
          Intros vq. destruct vq as [q dd]. cbn [fst snd] in *.
          rewrite bytes_at_ptr by (apply ptr_nn; auto).
          match goal with H: dd_ref dd = _ |- _ => rewrite if_false in H by auto end.
          match goal with H1: dd_bytes dd = bs, H2: dd_ref dd = _ |- _ => rename H1 into Hdb; rename H2 into Hdr end.
          forward. forward.
          { entailer!. rewrite upd_Znth_same by (rewrite Zlength_map; lia). auto. }
          rewrite upd_Znth_same by (rewrite Zlength_map; lia).
          destruct (eq_dec q nullval) as [Eq|Nq].
          { (* no DDict: the buffer stays *)
            subst q. forward_if; [discriminate|].
            forward.
            Exists (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))) st.
            rewrite <- (slots_res_upd DD gv sl (i mod 2) (SBuf d (Zlength bs))) by auto.
            rewrite (slot_one_non DD gv (SBuf d (Zlength bs))) by (simpl; tauto).
            rewrite pws_one.
            match goal with Hf: field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] d |- _ =>
              sep_apply (buf_parts_free d (Zlength bs) (zbytes bs) ltac:(lia) Hf) end.
            replace (upd_Znth (i mod 2) (map slot_b sl) d) with (map slot_b (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))))
              by (rewrite <- upd_Znth_map; reflexivity).
            replace (upd_Znth (i mod 2) (map slot_q sl) nullval) with (map slot_q (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))))
              by (rewrite <- upd_Znth_map; reflexivity).
            assert (Hl': Zlength (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))) = 2) by (rewrite upd_Znth_Zlength by lia; auto).
            assert (Hf': Forall slot_ok (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))))
              by (apply Forall_upd_Znth; auto; simpl; split; [apply ptr_nn; auto | lia]).
            assert (Hc': ctx_ok (upd_Znth (i mod 2) sl (SBuf d (Zlength bs))) st) by (apply ctx_ok_upd_non; auto; simpl; tauto).
            cbn [slot_buf]. entailer!. }
          { (* a DDict: referenced *)
            try rewrite if_false by auto.
            forward_if; [|first [discriminate | congruence | (exfalso; auto)]].
            forward.
            { entailer!. rewrite upd_Znth_same by (rewrite Zlength_map; lia). auto. }
            rewrite upd_Znth_same by (rewrite Zlength_map; lia).
            sep_apply (andp_drop_vp (DD gv q dd) q).
            (* lend the context's dictionaries (the other slot's DDict) *)
            unfold slot_one at 1. unfold slot_ddres_v. Intros.
            rewrite (ddres_pair_j DD gv sl (i mod 2) Hj Hn).
            destruct (slots_arrange DD gv sl (dc_dict st) (dc_set st) ltac:(assumption) Hds) as [Rest0 HR0].
            rewrite HR0. Intros.
            forward_call (gv, dctx, st, q, dd, Ews).
            { destruct (eq_dec q nullval); [contradiction|]. cancel. }
            { eapply ctx_ds_len; eassumption. }
            Intros vret. destruct vret as [r st']. cbn [fst snd] in *.
            sep_apply (derives_refl' _ _ (eq_sym HR0)).
            sep_apply (derives_refl' _ _ (eq_sym (ddres_pair_j DD gv sl (i mod 2) Hj Hn))).
            pose proof Hcx as (Hss0 & _ & _ & _ & Hmem0 & _).
            api_init. destruct (eq_dec q nullval); [contradiction|].
            match goal with H: refddict_result _ _ _ _ _ |- _ =>
              destruct (ctx_ok_refdd sl (i mod 2) (SDD q d bs dd) st st' r ltac:(auto) ltac:(auto) Hn I Hcx H) as [Hc' _] end.
            Exists (upd_Znth (i mod 2) sl (SDD q d bs dd)) st'.
            rewrite <- (slots_res_upd DD gv sl (i mod 2) (SDD q d bs dd)) by auto.
            rewrite slot_one_sdd.
            unfold slot_one at 1. unfold slot_ddres_v.
            assert (Hd: isptr d) by (apply ptr_nn; auto).
            sep_apply (zero_piece d bs dd Hd Hdb Hdr).
            replace (upd_Znth (i mod 2) (map slot_b sl) d) with (map slot_b (upd_Znth (i mod 2) sl (SDD q d bs dd)))
              by (rewrite <- upd_Znth_map; reflexivity).
            replace (upd_Znth (i mod 2) (map slot_q sl) q) with (map slot_q (upd_Znth (i mod 2) sl (SDD q d bs dd)))
              by (rewrite <- upd_Znth_map; reflexivity).
            assert (Hl': Zlength (upd_Znth (i mod 2) sl (SDD q d bs dd)) = 2) by (rewrite upd_Znth_Zlength by lia; auto).
            assert (Hf': Forall slot_ok (upd_Znth (i mod 2) sl (SDD q d bs dd))).
            { apply Forall_upd_Znth; auto. simpl. split; [apply ptr_nn; auto|]. split; [lia|].
              split; [apply bytes_ok_of; auto | auto]. }
            entailer!. } }
        { (* no buffer *)
          forward.
          match goal with H: d = nullval |- _ => subst d end.
          Exists (upd_Znth (i mod 2) sl SNone) st.
          rewrite <- (slots_res_upd DD gv sl (i mod 2) SNone) by auto.
          rewrite (slot_one_non DD gv SNone) by (simpl; tauto).
          rewrite (map_slot_q_upd_non sl (i mod 2) SNone) by (auto; simpl; tauto).
          replace (upd_Znth (i mod 2) (map slot_b sl) nullval) with (map slot_b (upd_Znth (i mod 2) sl SNone))
            by (rewrite <- upd_Znth_map; reflexivity).
          unfold buf_res. rewrite if_true by auto.
          assert (Hl': Zlength (upd_Znth (i mod 2) sl SNone) = 2) by (rewrite upd_Znth_Zlength by lia; auto).
          assert (Hf': Forall slot_ok (upd_Znth (i mod 2) sl SNone)) by (apply Forall_upd_Znth; auto; simpl; auto).
          assert (Hc': ctx_ok (upd_Znth (i mod 2) sl SNone) st) by (apply ctx_ok_upd_non; auto; simpl; tauto).
          cbn [slot_buf]. entailer!. } } } }
  Intros sl st.
  match goal with H: ctx_ok sl st |- _ => pose proof H as Hcx; destruct H as (Hss & Hbl & Hlast & Hstab & Hmem & Hds) end.
  sep_apply (slots_to_after DD gv sl). unfold slots_after.
  destruct (slots_arrange DD gv sl (dc_dict st) (dc_set st) ltac:(assumption) Hds) as [Rest HR].
  rewrite HR. Intros.
  forward_call tt. Intros u30.
  forward_if (EX st': dctx_st, EX dstv: val,
    PROP ()
    LOCAL (temp _dst dstv; temp _dctx dctx; temp _src src; temp _n (Vlong (Int64.repr n)); temp _cap (Vlong (Int64.repr cap));
           lvar _out tout v_out; lvar _in tin v_in; lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
           lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
    SEP (DC gv dctx st'; if eq_dec dstv nullval then emp else
           (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dstv * data_at_ Ews (tarray tuchar (Z.max 1 cap)) dstv);
         mem_mgr gv; zstd_globals gv; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
         data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
         data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
         malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes s) src;
         slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
         dict_res DD gv Ews (dc_dict st) ; set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))%assert.
  { (* one-shot *)
    if_set_post _t'14 (Vlong (Int64.repr (Z.max 1 cap))).
    { forward. entailer!. norm. do 2 f_equal; lia. }
    { forward. entailer!. norm. do 2 f_equal; lia. }
    forward_call (tarray tuchar (Z.max 1 cap), gv).
    { simpl. rep_lia. }
    Intros dst.
    assert_PROP (is_pointer_or_null dst) as PNdst by (destruct (eq_dec dst nullval); entailer!).
    sep_apply (malloc_buf dst cap); [lia|].
    forward.
    forward_if.
    { (* ZSTD_decompressDCtx *)
      rewrite (buf_res_nn dst) by auto. Intros.
      subst n.
      assert_PROP (isptr src) as Hsp by entailer!.
      sep_apply (tok_to_Z Ews (Zlength s) src).
      rewrite (adc_data_at_cs HCS ZCS Ews (Zlength s) (zbytes s) src).
      sep_apply (@data_at_data_at_ ZCS Ews (tarray tuchar cap) (Zrepeat Vundef cap) dst).
      change (@malloc_token ZCS Ews (tarray tuchar (Zlength s)) src) with (pw_pred (pw_token Ews (tarray tuchar (Zlength s)) src)).
      sep_apply (derives_refl' _ _ (eq_sym (pws_cons2 (pw_token Ews (tarray tuchar (Zlength s)) src) (rest_w dst cap) (slots_w sl)))).
      sep_apply (data_at__mbuf Ews cap dst).
      forward_call ([pw_token Ews (tarray tuchar (Zlength s)) src] ++ rest_w dst cap :: slots_w sl,
                    gv, dctx, st, Ews, Ews, dst, cap, Ews, src, s).
      { assert (HWd: pws_pred [pw_token Ews (tarray tuchar (Zlength s)) src; rest_w dst cap] *
                     @data_at_ ZCS Ews (tarray tuchar cap) dst |-- valid_pointer dst).
        { unfold pws_pred. simpl. rewrite sepcon_emp.
          eapply derives_trans with (pw_pred (rest_w dst cap) * @data_at_ ZCS Ews (tarray tuchar cap) dst *
                                      pw_pred (pw_token Ews (tarray tuchar (Zlength s)) src))%logic; [cancel|].
          apply sepcon_valid_pointer1. apply rest_v; auto; lia. }
        refine (conj _ (conj _ (conj _ (conj _ _)))).
        { apply (buf_ok_of [_] (slots_w sl)); auto; lia. }
        { apply buf_ok_tok; auto; [left; reflexivity | apply Zlength_nonneg]. }
        { apply (slots_dict_buf_ok [pw_token Ews (tarray tuchar (Zlength s)) src; rest_w dst cap] sl
                   (dc_dict st) (dc_set st)); auto. }
        { apply (slots_set_buf_ok [pw_token Ews (tarray tuchar (Zlength s)) src; rest_w dst cap] sl
                   (dc_dict st) (dc_set st)); auto. }
        { apply bytes_ok_of; auto. } }
      Intros vret. destruct vret as [[r out] st']. cbn [fst snd] in *.
      rewrite mbuf_isptr by auto with field_compatible.
      forward_call r.
      match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
        forward_if (PROPx P (LOCALx (temp _t'18 (Vint Int.one) :: L) (SEPx R))) end.
      { forward. entailer!. }
      { forward. entailer!.
        match goal with H: oneshot_dctx _ _ _ _ _ |- _ => pose proof (oneshot_dctx_cap _ _ _ _ _ H) as Hle end.
        match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ =>
          destruct (is_error_code r) eqn:Er; [discriminate H|] end.
        specialize (Hle eq_refl). unfold Int64.cmpu. rewrite AS_ltu64_false by rep_lia. reflexivity. }
      forward_call Int.one.
      Exists st' dst.
      rewrite if_false by auto.
      match goal with |- context [pws_pred ([?a] ++ ?b :: ?c)] =>
        change ([a] ++ b :: c) with (a :: b :: c); rewrite (pws_cons2 a b c) end.
      change (pw_pred (pw_token Ews (tarray tuchar (Zlength s)) src)) with (@malloc_token ZCS Ews (tarray tuchar (Zlength s)) src).
      sep_apply (tok_of_Z Ews (Zlength s) src).
      match goal with Hf: field_compatible (tarray tuchar (Z.max 1 ?c)) [] dst |- _ =>
        sep_apply (buf_parts_free dst c out ltac:(lia) Hf) end.
      rewrite <- (adc_data_at_cs HCS _ Ews (Zlength s) (zbytes s) src).
      entailer!. }
    { (* no output buffer *)
      forward. Exists st nullval. rewrite if_true by auto.
      unfold buf_res. rewrite if_true by auto. entailer!. } }
  { (* streaming *)
    forward.
    forward_loop
      (EX calls: Z, EX got: Z, EX ipos: Z, EX st2: dctx_st,
       PROP (0 <= calls <= 512; 0 <= ipos <= n; 0 <= got <= cap + 256; dc_dict st2 = dc_dict st; dc_set st2 = dc_set st; dc_bl st2 = None; dc_stable st2 = false; ss_err (dc_ss st2) = false)
       LOCAL (temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
            lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st2;
          data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
          data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
          slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))
    continue:
      (EX calls: Z, EX got: Z, EX ipos: Z, EX st2: dctx_st,
       PROP (0 <= calls < 512; 0 <= ipos <= n; 0 <= got <= cap + 256; dc_dict st2 = dc_dict st; dc_set st2 = dc_set st; dc_bl st2 = None; dc_stable st2 = false; ss_err (dc_ss st2) = false)
       LOCAL (temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
            temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
            temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
            lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
            lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st2;
          data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
          data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
          slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))
    break:
      (EX st2: dctx_st,
       PROP ()
       LOCAL (temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st2;
          data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
          data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
          data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
          slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
          dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt)).
    { Exists 0 0 0 st. entailer!. rewrite Hss. auto. }
    2: { Intros calls got ipos st2. forward. Exists (calls + 1) got ipos st2. entailer!. }
    2: { Intros st2. Exists st2 nullval. rewrite if_true by auto. entailer!. }
    Intros calls got ipos st2.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX b: bool, PROPx ((b = true -> calls < 512 /\ got <= cap) :: P)
                   (LOCALx (temp _t'19 (Vint (if b then Int.one else Int.zero)) :: L) (SEPx R)))
    end.
    { forward. Exists (negb (Int64.ltu (Int64.repr cap) (Int64.repr got))). entailer!.
      split.
      { rewrite ltu64_Z by rep_lia. intro E. destruct (cap <? got) eqn:E2; simpl in E; [discriminate|].
        apply Z.ltb_ge in E2. lia. }
      unfold Int64.cmpu. destruct (Int64.ltu _ _); reflexivity. }
    { forward. Exists false. entailer!. }
    Intros b. forward_if.
    2: { forward. Exists st2. entailer!. }
    match goal with H: (if b then Int.one else Int.repr 0) <> Int.zero |- _ => rename H into Hb end.
    destruct b; [|exfalso; apply Hb; reflexivity].
    match goal with H: true = true -> _ |- _ => destruct (H eq_refl) as [Hcalls Hgot]; clear H end. clear Hb.
    forward_call tt. Intros u1. forward.
    forward_call tt. Intros u2. forward.
    rewrite (AS_chunk_in u1), (AS_chunk_out u2) by lia.
    pose proof (Z.mod_pos_bound u1 257 ltac:(lia)). pose proof (Z.mod_pos_bound u2 256 ltac:(lia)).
    set (a1 := u1 mod 257) in *. set (ol := u2 mod 256 + 1).
    assert (Ha1: 0 <= a1 <= 256) by (subst a1; lia). assert (Hol: 1 <= ol <= 256) by (subst ol; lia).
    clearbody a1 ol.
    forward_if
      (PROP ()
       LOCAL (temp _ilen (Vlong (Int64.repr (Z.min a1 (n - ipos)))); temp _olen (Vlong (Int64.repr ol));
              temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
              temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st2;
            data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
            data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt)).
    { forward. entailer!.
      match goal with H: Int64.ltu _ _ = true |- _ => try rewrite sub64_repr in H; rewrite ltu64_Z in H by rep_lia; apply Z.ltb_lt in H end.
      rewrite Z.min_r by lia. reflexivity. }
    { forward. entailer!.
      match goal with H: Int64.ltu _ _ = false |- _ => try rewrite sub64_repr in H; rewrite ltu64_Z in H by rep_lia; apply Z.ltb_ge in H end.
      rewrite Z.min_l by lia. reflexivity. }
    assert (Hil: 0 <= Z.min a1 (n - ipos) <= 256 /\ Z.min a1 (n - ipos) <= n - ipos) by lia.
    set (il := Z.min a1 (n - ipos)) in *. clearbody il. destruct Hil as [Hil1 Hil2].
    forward_if
      (PROP ()
       LOCAL (temp _t'22 (Vlong (Int64.repr (Z.max 1 il))); temp _ilen (Vlong (Int64.repr il)); temp _olen (Vlong (Int64.repr ol));
              temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
              temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
       SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st2;
            data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
            data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt)).
    { forward. entailer!.
      match goal with H: Int64.unsigned _ < Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      rewrite Z.max_r by lia. reflexivity. }
    { forward. entailer!.
      match goal with H: Int64.unsigned _ >= Int64.unsigned _ |- _ => rewrite !Int64.unsigned_repr in H by rep_lia end.
      replace il with 0 by lia. reflexivity. }
    forward_call (tarray tuchar (Z.max 1 il), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros ib. forward.
    forward_call (tarray tuchar ol, gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros ob.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp _t'25 (Vint (Int.repr
          (if eq_dec ib nullval then 1 else if eq_dec ob nullval then 1 else 0))) :: L) (SEPx R)))
    end.
    { AS_tc_null_test ib. }
    { forward. destruct (eq_dec ib nullval); [|contradiction]. entailer!. }
    { forward.
      { entailer!; AS_tc_null_test ob. }
      destruct (eq_dec ib nullval); [contradiction|].
      destruct (eq_dec ob nullval); entailer!;
        try reflexivity; destruct ob; try contradiction; reflexivity. }
    forward_if.
    { forward_call (tarray tuchar (Z.max 1 il), ib, gv).
      forward_call (tarray tuchar ol, ob, gv).
      forward. Exists st2. entailer!. }
    match goal with H: Int.repr _ = Int.zero |- _ => rename H into Ht12 end.
    change (EqDec_val ib nullval) with (eq_dec ib nullval) in Ht12.
    change (EqDec_val ob nullval) with (eq_dec ob nullval) in Ht12.
    destruct (eq_dec ib nullval) as [|Hib]; [now apply AS_repr1_neq0 in Ht12|].
    destruct (eq_dec ob nullval) as [|Hob]; [now apply AS_repr1_neq0 in Ht12|].
    clear Ht12. Intros.
    try rewrite (if_false (ib = nullval)) by auto. try rewrite (if_false (ob = nullval)) by auto.
    Intros.
    assert (Hm: (0 < il /\ Z.max 1 il = il) \/ (il = 0 /\ Z.max 1 il = 1)) by lia.
    set (m := Z.max 1 il) in *. clearbody m.
    apply -> seq_assoc. forward.
    forward_loop
      (EX k: Z, PROP (0 <= k <= il) LOCAL (temp _i (Vint (Int.repr k)); temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il)); temp _olen (Vlong (Int64.repr ol));
              temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
              temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv) SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
            malloc_token Ews (tarray tuchar m) ib;
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + k) (zbytes s) ++ Zrepeat Vundef (m - k)) ib;
            zstd_globals gv; DC gv dctx st2; data_at Ews (tarray tuchar n) (zbytes s) src;
            malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
            data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))
    continue:
      (EX k: Z, PROP (0 <= k < il) LOCAL (temp _i (Vint (Int.repr k)); temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il)); temp _olen (Vlong (Int64.repr ol));
              temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
              temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv) SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
            malloc_token Ews (tarray tuchar m) ib;
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + (k + 1)) (zbytes s) ++ Zrepeat Vundef (m - (k + 1))) ib;
            zstd_globals gv; DC gv dctx st2; data_at Ews (tarray tuchar n) (zbytes s) src;
            malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
            data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))
    break:
      (PROP () LOCAL (temp _ob ob; temp _ib ib; temp _ilen (Vlong (Int64.repr il)); temp _olen (Vlong (Int64.repr ol));
              temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr ipos));
              temp _got (Vlong (Int64.repr got)); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv) SEP (mem_mgr gv; malloc_token Ews (tarray tuchar ol) ob; data_at_ Ews (tarray tuchar ol) ob;
            malloc_token Ews (tarray tuchar m) ib;
            data_at Ews (tarray tuchar m) (sublist ipos (ipos + il) (zbytes s) ++ Zrepeat Vundef (m - il)) ib;
            zstd_globals gv; DC gv dctx st2; data_at Ews (tarray tuchar n) (zbytes s) src;
            malloc_token Ews (tarray tuchar n) src; data_at_ Tsh tout v_out; data_at_ Tsh tin v_in;
            data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt)).
    { Exists 0. entailer!. rewrite sublist_nil, app_nil_l. cancel. }
    { Intros k. forward_if.
      2: { forward. entailer!.
           match goal with H: Int.unsigned (Int.repr k) >= _ |- _ => rewrite Int.unsigned_repr in H by rep_lia end.
           replace k with il by lia. cancel. }
      match goal with H: Int.unsigned (Int.repr k) < _ |- _ => rewrite Int.unsigned_repr in H by rep_lia end.
      assert (Hik: 0 <= ipos + k < Zlength s) by lia.
      forward.
      { entailer!.
        match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) s |- _ =>
          pose proof (proj1 (Forall_Znth _ _) Hf (ipos + k) ltac:(lia)) as Hbk end.
        cbv beta in Hbk. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      forward.
      Exists k. entailer!.
      match goal with Hf: Forall (fun b : Z => 0 <= b <= Byte.max_unsigned) s |- _ =>
        pose proof (proj1 (Forall_Znth _ _) Hf (ipos + k) ltac:(lia)) as Hbk end.
      cbv beta in Hbk.
      try rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
      replace (Vint (Int.repr (Znth (ipos + k) s))) with (Znth (ipos + k) (zbytes s))
        by (rewrite Znth_map by lia; reflexivity).
      replace (upd_Znth k (sublist ipos (ipos + k) (zbytes s) ++ Zrepeat Vundef (m - k)) (Znth (ipos + k) (zbytes s)))
        with (sublist ipos (ipos + (k + 1)) (zbytes s) ++ Zrepeat Vundef (m - (k + 1))); [cancel|].
      list_solve. }
    { Intros k. forward. Exists (k + 1). entailer!. }
    forward. forward. forward. forward. forward. forward.
    change (Int.signed (Int.repr 0)) with 0.
    replace (sublist ipos (ipos + il) (zbytes s)) with (zbytes (sublist ipos (ipos + il) s))
      by (rewrite sublist_map; auto).
    assert (HA: Zlength (zbytes (sublist ipos (ipos + il) s)) = il)
      by (rewrite Zlength_map, Zlength_sublist by lia; lia).
    rewrite (adc_data_at_cs HCS ZCS Ews m _ ib).
    sep_apply (AS_ib_split ib il m _ HA Hm).
    rewrite (adc_data_at__cs HCS ZCS Ews ol ob), <- AS_out, <- AS_in.
    rewrite (@data_at__eq ZCS).
    assert (Hbytes: bytes_ok (sublist ipos (ipos + il) s)) by (apply bytes_ok_of; apply Forall_sublist; auto).
    match goal with Hd: dc_dict st2 = dc_dict st, Hs: dc_set st2 = dc_set st |- _ => rewrite <- Hd, <- Hs end.
    sep_apply (derives_refl' _ _ (eq_sym (pws_app (AS_W il ib) (slots_w sl)))).
    forward_call (AS_W il ib ++ slots_w sl, gv, dctx, st2, v_out, v_in, Tsh, Tsh, Ews, ob, ol, 0,
                  @default_val ZCS (tarray tuchar ol), Ews, ib, il, 0, sublist ipos (ipos + il) s).
    { unfold mbuf; rewrite ?if_false by auto. cancel. }
    { refine (conj _ (conj _ (conj _ (conj _ _)))).
      - apply AS_buf_ok_pos; lia.
      - apply AS_buf_ok_W; lia.
      - apply slots_stream_ok; auto.
        match goal with Hd: dc_dict st2 = _, Hs: dc_set st2 = _ |- _ => rewrite Hd, Hs; exact Hds end.
      - apply Zlength_default_val_Tarray_tuchar; lia.
      - rewrite Zlength_sublist by lia; lia. }
    Intros vret. destruct vret as [[[[r opos'] ipos'] oc'] st']. simpl fst in *; simpl snd in *.
    unfold mbuf; rewrite ?if_false by auto.
    match goal with H: stream_post _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      destruct H as (dl & stall' & a' & Hop & Hip & Hoc & Hpre & Hdl & Hbo & Ha' & Hah & Hor & Hr0 & Hst' & Hs1 & Hs2 & Hbm & Hstall & Hcl & _) end.
    sep_apply (andp_left1 (DC gv dctx st') (valid_pointer dctx) (DC gv dctx st') (derives_refl _)).
    match goal with Hd: dc_dict st2 = dc_dict st, Hs: dc_set st2 = dc_set st |- _ => rewrite Hd, Hs end.
    rewrite pws_app. Intros.
    sep_apply (AS_ib_join ib il m (zbytes (sublist ipos (ipos + il) s)) Hm).
    rewrite AS_out, AS_in, (adc_data_at__cs ZCS HCS Ews m ib), <- (adc_data_at_cs HCS _ Ews ol oc' ob).
    forward. forward.
    forward_call Int.one.
    { entailer!. unfold Int64.cmpu. rewrite AS_ltu64_false by rep_lia. reflexivity. }
    forward. forward.
    forward_call Int.one.
    { entailer!. unfold Int64.cmpu. rewrite AS_ltu64_false by rep_lia. reflexivity. }
    forward. forward. forward. forward.
    forward_call (tarray tuchar m, ib, gv).
    { rewrite if_false by auto. cancel. }
    forward_call (tarray tuchar ol, ob, gv).
    { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar ol) oc' ob). cancel. }
    forward_call r.
    subst st'.
    match goal with |- context [DC gv dctx (set_last (set_ss st2 ?x) _)] => set (s2 := x) end.
    set (st3 := set_last (set_ss st2 s2) (Some stream_mark)).
    forward_if ((EX st4: dctx_st,
      PROP (dc_dict st4 = dc_dict st; dc_set st4 = dc_set st; dc_bl st4 = None; dc_stable st4 = false;
            ss_err (dc_ss st4) = false)
      LOCAL (temp _r (Vlong (Int64.repr r)); temp _calls (Vint (Int.repr calls)); temp _ipos (Vlong (Int64.repr (ipos + ipos')));
              temp _got (Vlong (Int64.repr (got + opos'))); temp _dst nullval; temp _dctx dctx; temp _cap (Vlong (Int64.repr cap));
              temp _src src; temp _n (Vlong (Int64.repr n)); lvar _out tout v_out; lvar _in tin v_in;
              lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
              lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
      SEP (mem_mgr gv; zstd_globals gv; DC gv dctx st4;
            data_at Tsh tout (ob, (Vlong (Int64.repr ol), Vlong (Int64.repr opos'))) v_out;
            data_at Tsh tin (ib, (Vlong (Int64.repr il), Vlong (Int64.repr ipos'))) v_in;
            data_at Ews (tarray tuchar n) (zbytes s) src; malloc_token Ews (tarray tuchar n) src;
            data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
            data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
            slot_buf (Znth 0 sl); slot_buf (Znth 1 sl); pws_pred (slots_w sl);
            dict_res DD gv Ews (dc_dict st); set_res DD gv Ews (dc_set st) (dc_dict st); Rest; TT; has_ext tt))%assert).
    { forward_call (gv, dctx, st3, ZSTD_reset_session_only).
      Intros vret. destruct vret as [r0 st0]. cbn [fst snd] in *.
      match goal with H: reset_post _ _ _ _ |- _ => destruct (reset_post_session _ _ _ H) as [-> ->]; clear H end.
      Exists (set_ex (set_ss st3 ss_init) false). subst st3 s2. entailer!. }
    { forward. Exists st3.
      match goal with H: Int.repr (if is_error_code r then 1 else 0) = Int.zero |- _ =>
        destruct (is_error_code r) eqn:Er; [discriminate H|] end.
      subst st3 s2. entailer!; try (rewrite Er; auto). }
    Intros st4.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX v: int, PROPx P (LOCALx (temp _t'28 (Vint v) :: L) (SEPx R))) end.
    { forward. forward.
      Exists (if Int64.cmpu Ceq (Int64.repr ipos') (Int64.repr 0) then Int.one else Int.zero). entailer!.
      destruct (Int64.cmpu _ _ _); reflexivity. }
    { forward. Exists Int.zero. entailer!. }
    Intros v28.
    match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?R))) _ _ =>
      forward_if (EX v: int, PROPx P (LOCALx (temp _t'29 (Vint v) :: L) (SEPx R))) end.
    { forward. forward.
      Exists (if Int64.cmpu Ceq (Int64.repr opos') (Int64.repr 0) then Int.one else Int.zero). entailer!.
      destruct (Int64.cmpu _ _ _); reflexivity. }
    { forward. Exists Int.zero. entailer!. }
    Intros v29.
    sep_apply (data_at_data_at_ Tsh tout (ob, (Vlong (Int64.repr ol), Vlong (Int64.repr opos'))) v_out).
    sep_apply (data_at_data_at_ Tsh tin (ib, (Vlong (Int64.repr il), Vlong (Int64.repr ipos'))) v_in).
    forward_if.
    { forward. Exists st4. entailer!. }
    { forward. Exists calls (got + opos') (ipos + ipos') st4. entailer!. } }
  Intros st' dstv.
  forward_call (gv, dctx, Some st').
  sep_apply (sepcon_derives (dict_res DD gv Ews (dc_dict st) * set_res DD gv Ews (dc_set st) (dc_dict st) * Rest)%logic
     (slot_ddres DD gv (Znth 0 sl) * slot_ddres DD gv (Znth 1 sl))%logic emp emp ltac:(rewrite HR; apply derives_refl) (derives_refl _)).
  assert (Hfin: (slot_buf (Znth 0 sl) * slot_buf (Znth 1 sl) * pws_pred (slots_w sl) *
                 (slot_ddres DD gv (Znth 0 sl) * slot_ddres DD gv (Znth 1 sl)))%logic |--
                fold_right sepcon emp (map (slot_fin DD gv) (sublist 0 2 sl)))
    by (eapply derives_trans; [apply (slots_after_fin DD gv sl); auto | apply fins_start; auto]).
  sep_apply Hfin.
  forward_for_simple_bound 2 (EX i: Z,
    PROP ()
    LOCAL (temp _dst dstv; temp _src src; lvar _out tout v_out; lvar _in tin v_in;
           lvar _dbuf (tarray (tptr tuchar) 2) v_dbuf;
           lvar _dd (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) v_dd; gvars gv)
    SEP (mem_mgr gv; zstd_globals gv; fold_right sepcon emp (map (slot_fin DD gv) (sublist i 2 sl));
         data_at Tsh (tarray (tptr tuchar) 2) (map slot_b sl) v_dbuf;
         data_at Tsh (tarray (tptr (Tstruct _ZSTD_DDict_s noattr)) 2) (map slot_q sl) v_dd;
         if eq_dec dstv nullval then emp else
           (malloc_token Ews (tarray tuchar (Z.max 1 cap)) dstv * data_at_ Ews (tarray tuchar (Z.max 1 cap)) dstv);
         malloc_token Ews (tarray tuchar n) src; data_at Ews (tarray tuchar n) (zbytes s) src;
         data_at_ Tsh tout v_out; data_at_ Tsh tin v_in; TT; has_ext tt))%assert.
  { entailer!. }
  { replace (sublist i 2 sl) with (Znth i sl :: sublist (i + 1) 2 sl)
      by (rewrite <- H7; symmetry; apply sublist_next; lia).
    cbn [map fold_right]. unfold slot_fin at 1. Intros.
    forward.
    { entailer!. rewrite Znth_map by lia. apply slot_q_pn, slot_at_ok; auto; lia. }
    rewrite Znth_map by lia.
    forward_call (gv, slot_q (Znth i sl), slot_odd (Znth i sl)).
    { apply slot_odd_pre. }
    forward.
    { entailer!. rewrite Znth_map by lia. apply slot_b_pn, slot_at_ok; auto; lia. }
    rewrite Znth_map by lia.
    forward_call (tarray tuchar (slot_sz (Znth i sl)), slot_b (Znth i sl), gv).
    entailer!. }
  forward_call (tarray tuchar (Z.max 1 cap), dstv, gv).
  forward_call (tarray tuchar n, src, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar n) (zbytes s) src). cancel. }
  forward. ret_frame.
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

Theorem any_params_ok :
  forall (DC: globals -> val -> dctx_st -> mpred) (DD: globals -> val -> ddict_st -> mpred),
    exists Hs, HarnessOK (Specs_api DC DD) Hs.
Proof.
  intros DC DD. exists []. split.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    exists f_main. split; [reflexivity|]. split; [reflexivity|].
    eapply semax_body_subsumption; [apply (body_main_G0 DC DD) |].
    apply tycontext_sub_i99. split; intro i.
    + (* the function list is abstracted, so that no rewriting compares it with the empty list by computation *)
      remember (Gprog (Specs_api DC DD) []) as GP eqn:HGP.
      rewrite (make_tycontext_g_find Vprog (G0 DC DD) i).
      rewrite (make_tycontext_g_find Vprog GP i).
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E.
      * rewrite HGP, (G0_in_Gprog DC DD i fs E). apply sub_option_refl.
      * destruct (Maps.PTree.get i (make_tycontext_g Vprog nil)) as [t|] eqn:Ev; [|exact Logic.I].
        rewrite HGP, (vars_not_funs DC DD i t Ev). apply sub_option_refl.
    + rewrite !semax_prog.find_id_maketycontext_s.
      destruct (initial_world.find_id i (G0 DC DD)) as [fs|] eqn:E; [|exact Logic.I].
      rewrite (G0_in_Gprog DC DD i fs E). exists fs. split; [reflexivity|]. apply funspec_sub_si_refl.
Qed.

