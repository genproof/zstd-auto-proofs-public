(* VDC3Lemmas adapted to API v3.2: dd0 and dr_of carry the DDict state (dd_buf, dd_ld) *)
(* API v3 copy of VDCLemmas.v (VDC_oneshot under md_dflt). Helper lemmas for main of harness/valid_dict_copy.c (WMain_valid_dict_copy.v): main's precondition, the
   model of a decoded written series, byte buffers and witnesses, the unfolded sr / wd structs. *)
Require Import VST.floyd.proofauto.
Require Export Zstd.proof.harness.valid_dict_copy.WTopSpecs_valid_dict_copy.
Require Zstd.proof.top.MainPre6.
Require Export Zstd.proof.harness.writer.SeriesLemmas.
Require Export Zstd.proof.zstd.ApiBridge Zstd.proof.model.ParamsDflt.

Local Notation ZCS := Zstd.proof.zstd.Base.CompSpecs.
Local Notation HCS := Zstd.proof.harness.valid_dict_copy.HOK_valid_dict_copy.CompSpecs.

(* ---------- main's precondition: the decoder's tables, the writer's statics, sr and wd ---------- *)

Lemma VDC_filter_filter {A: Type} (f g: A -> bool) l :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  destruct (g a); simpl; [destruct (f a); simpl; rewrite IH; auto | exact IH].
Qed.

Lemma VDC_wvar_not_zstd : forallb (fun i => negb (id_in_list i MainPre6.zstd_var_ids)) wvar_ids = true.
Proof. vm_compute. reflexivity. Qed.

Lemma VDC_wvardefs :
  filter (fun ig => id_in_list (fst ig) wvar_ids)
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_dict_copy.whole_prog))
  = wvardefs.
Proof.
  rewrite VDC_filter_filter. unfold wvardefs. apply filter_ext. intros [i g]; cbn [fst].
  destruct (id_in_list i wvar_ids) eqn:E; [|apply andb_false_r].
  rewrite andb_true_r.
  pose proof VDC_wvar_not_zstd as H. rewrite forallb_forall in H.
  apply id_in_list_true in E. specialize (H i E). exact H.
Qed.

Local Notation VDC_rest :=
  (filter (fun ig => negb (id_in_list (fst ig) wvar_ids))
    (filter (fun ig => negb (id_in_list (fst ig) MainPre6.zstd_var_ids)) (Vardefs Zstd.contracts.x_valid_dict_copy.whole_prog))) (only parsing).

(* the remaining globals in the order of their identifiers (PTree order): wd and sr at positions 82 and 83 of 86 (the
   decoder's ZSTD_emptyBuffer, F9, after them) *)
Lemma VDC_rest_eq :
  VDC_rest = firstn 82 VDC_rest ++ (_x_valid_dict_copy__wd, Gvar v_x_valid_dict_copy__wd) ::
                                   (_x_valid_dict_copy__sr, Gvar v_x_valid_dict_copy__sr) :: skipn 84 VDC_rest.
Proof. vm_compute. reflexivity. Qed.   (* 2026-10-24: was rewrite <- (firstn_skipn 82 VDC_rest) at 1; f_equal, which no longer ends after F9's new global (killed after hours) *)

Lemma VDC_sr_zero gv :
  globs2pred gv (_x_valid_dict_copy__sr, Gvar v_x_valid_dict_copy__sr) |--
  data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict_copy__sr).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 786936 with (@sizeof HCS t_wseries).
  apply mapsto_zero_data_at_zero.
  - apply writable_readable, writable_Ews.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    all: first [apply la_env_cs_sound; vm_compute; reflexivity | simpl; rep_lia].
Qed.

Lemma VDC_wd_zero gv :
  globs2pred gv (_x_valid_dict_copy__wd, Gvar v_x_valid_dict_copy__wd) |--
  data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict_copy__wd).
Proof.
  unfold globs2pred. apply derives_extract_prop; intros Hh.
  unfold globvar2pred. simpl. rewrite sepcon_emp.
  change 13984 with (@sizeof HCS t_wdict).
  apply mapsto_zero_data_at_zero.
  - apply writable_readable, writable_Ews.
  - reflexivity.
  - reflexivity.
  - destruct Hh as [b ->]. repeat split; auto.
    all: first [apply la_env_cs_sound; vm_compute; reflexivity | simpl; rep_lia].
Qed.

Lemma VDC_rest_globals gv :
  InitGPred VDC_rest gv |--
  data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict_copy__sr) *
  data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict_copy__wd) * TT.
Proof.
  rewrite VDC_rest_eq, InitGPred_app, !InitGPred_consD.
  sep_apply VDC_sr_zero. sep_apply VDC_wd_zero. cancel.
Qed.

Lemma VDC_pre (WG: globals -> mpred) (HWG: forall gv, InitGPred wvardefs gv |-- WG gv) gv :
  globals_ok gv ->
  InitGPred (Vardefs Zstd.contracts.x_valid_dict_copy.whole_prog) gv |--
  zstd_globals gv * (WG gv * (data_at Ews t_wseries (zero_val t_wseries) (gv _x_valid_dict_copy__sr) *
    data_at Ews t_wdict (zero_val t_wdict) (gv _x_valid_dict_copy__wd) * TT)).
Proof.
  intros Hgv. eapply derives_trans.
  - apply (MainPre6.main_pre_fact6 Zstd.contracts.x_valid_dict_copy.whole_prog); [|exact Hgv].
    unfold MainPre6.all_progs. do 9 right; left; reflexivity.
  - apply sepcon_derives; [apply derives_refl|].
    rewrite (MainPre6.MP_InitGPred_filter (fun ig => id_in_list (fst ig) wvar_ids)).
    rewrite VDC_wvardefs. apply sepcon_derives; [apply HWG|].
    apply VDC_rest_globals.
Qed.

(* ---------- the model: decoding the written series ---------- *)

Lemma VDC_ok_prefix_all wl fs : all_ok wl fs = true -> ok_prefix wl fs = fs.
Proof.
  induction fs as [|f fs IH]; simpl; auto.
  intros H. apply andb_prop in H as [H1 H2].
  destruct (wi_rejected wl f); [discriminate|]. rewrite IH; auto.
Qed.

Lemma VDC_decode dm ws : series_facts dm ws -> wseries_wf ws ->
  decode_series dm no_wlim (ws_bytes ws) = if within_oneshot_b (ws_frames ws) then SOk (ws_content ws) else SDet.
Proof.
  intros Hf Hw. unfold decode_series. rewrite (series_frames_written dm ws no_wlim Hf).
  rewrite (within_oneshot_all_ok ws Hw).
  destruct (all_ok no_wlim (ws_frames ws)) eqn:E; auto.
  rewrite VDC_ok_prefix_all by auto. rewrite (written_content dm ws Hf). reflexivity.
Qed.

Lemma VDC_dict_auto wd : dict_facts wd -> dict_auto (wd_bytes wd) = Some (wd_model wd).
Proof.
  intros (_ & _ & Hda & _). unfold wd_model. destruct (dict_auto (wd_bytes wd)); congruence.
Qed.

Lemma VDC_oneshot wd ws cap r out : dict_facts wd -> series_facts (wd_model wd) ws -> wseries_wf ws ->
  oneshot_ok md_dflt (dict_auto (wd_bytes wd)) (ws_bytes ws) cap r out ->
  (is_error_code r = false -> r = Zlength (ws_content ws) /\ sublist 0 r out = zbytes (ws_content ws)) /\
  (is_error_code r = true -> Zlength (ws_content ws) <= cap -> within_oneshot_b (ws_frames ws) = true ->
     r = err_code ZSTD_error_memory_allocation).
Proof.
  intros Hd Hf Hw Ho0. apply oneshot_ok_dflt in Ho0. destruct Ho0 as [_ Ho]. rewrite (VDC_dict_auto wd Hd), (VDC_decode _ ws Hf Hw) in Ho.
  destruct (within_oneshot_b (ws_frames ws)) eqn:E.
  - destruct Ho as [Ho1 Ho2]. split; auto.
    intros He Hc _. destruct (Ho2 He); [lia | auto].
  - split; [intros He; congruence | intros _ _ H; discriminate].
Qed.

(* ---------- small facts ---------- *)

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

Lemma sepcon_emp_fun_VDC (P: environ -> mpred) : (P * (fun _ : environ => emp))%logic = P.
Proof. extensionality rho. simpl. apply sepcon_emp. Qed.

Lemma ltu64_Z x y : 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
  Int64.ltu (Int64.repr x) (Int64.repr y) = (x <? y).
Proof.
  intros. unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

(* byte arrays mean the same at any two compspecs *)
Definition vdc_cce (cs1 cs2: compspecs) : change_composite_env cs1 cs2 :=
  {| coeq := cs_preserve_env cs1 cs2;
     coeq_consistent := cs_preserve_env_consistent cs1 cs2 _ eq_refl;
     coeq_complete := cs_preserve_completeness cs1 cs2 _ eq_refl |}.

Lemma vdc_data_at_cs: forall (cs1 cs2: compspecs) sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. apply equal_f.
  exact (@data_at_change_composite _ _ (vdc_cce cs1 cs2) sh (tarray tuchar n) v v (JMeq_refl v) eq_refl).
Qed.

Lemma vdc_data_at__cs: forall (cs1 cs2: compspecs) sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. rewrite (@data_at__change_composite _ _ (vdc_cce cs1 cs2)); auto. Qed.

(* ---------- byte buffers of max(1,c) bytes (malloc / exact_copy): c bytes, then a slack byte lent as witness ---------- *)

Definition rest_w (p: val) (c: Z) : ptr_witness :=
  pw_bytes Ews (Z.max 1 c - c) (Zrepeat Vundef (Z.max 1 c - c))
    (field_address0 (tarray tuchar (Z.max 1 c)) [ArraySubsc c] p).

Definition buf_res (p: val) (c: Z) (v: list val) : mpred :=
  if eq_dec p nullval then emp else
  (!! field_compatible (tarray tuchar (Z.max 1 c)) [] p &&
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at ZCS Ews (tarray tuchar c) v p *
    pw_pred (rest_w p c)))%logic.

Lemma rest_w_eq p c : pw_pred (rest_w p c) =
  @data_at_ HCS Ews (tarray tuchar (Z.max 1 c - c)) (field_address0 (tarray tuchar (Z.max 1 c)) [ArraySubsc c] p).
Proof.
  unfold pw_pred, rest_w. rewrite (vdc_data_at_cs ZCS HCS). reflexivity.
Qed.

Lemma malloc_buf p c : 0 <= c ->
  (if eq_dec p nullval then emp else
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at_ HCS Ews (tarray tuchar (Z.max 1 c)) p)%logic)
  |-- buf_res p c (Zrepeat Vundef c).
Proof.
  intros Hc. unfold buf_res. destruct (eq_dec p nullval); [apply derives_refl|].
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 c)) [] p) as Hfc by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Ews (Z.max 1 c) c p) by (auto; try lia; apply Hfc).
  rewrite rest_w_eq. rewrite (vdc_data_at_cs ZCS HCS). entailer!.
Qed.

Lemma copy_buf p (bs: list Z) :
  (if eq_dec p nullval then emp else
   (malloc_token Ews (tarray tuchar (Z.max 1 (Zlength bs))) p *
    @data_at HCS Ews (tarray tuchar (Z.max 1 (Zlength bs)))
      (zbytes bs ++ Zrepeat Vundef (Z.max 1 (Zlength bs) - Zlength bs)) p)%logic)
  |-- buf_res p (Zlength bs) (zbytes bs).
Proof.
  unfold buf_res. destruct (eq_dec p nullval); [apply derives_refl|].
  assert_PROP (field_compatible (tarray tuchar (Z.max 1 (Zlength bs))) [] p) as Hfc by entailer!.
  rewrite (split2_data_at_Tarray_app (Zlength bs) (Z.max 1 (Zlength bs))) by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
  rewrite rest_w_eq. rewrite (vdc_data_at_cs ZCS HCS). entailer!.
Qed.

Lemma buf_free p c v : 0 <= c ->
  buf_res p c v |--
  (if eq_dec p nullval then emp else
   (malloc_token Ews (tarray tuchar (Z.max 1 c)) p * @data_at_ HCS Ews (tarray tuchar (Z.max 1 c)) p)).
Proof.
  intros Hc. unfold buf_res. destruct (eq_dec p nullval); [apply derives_refl|].
  Intros. rewrite rest_w_eq. rewrite (vdc_data_at_cs ZCS HCS).
  rewrite (split2_data_at__Tarray_tuchar Ews (Z.max 1 c) c p) by (auto; try lia; apply H).
  cancel.
Qed.

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
  rewrite E.
  eapply derives_trans; [apply sepcon_derives; [apply rest_wv; auto | apply derives_refl]|].
  apply andp_right.
  - eapply derives_trans; [apply sepcon_derives; [apply andp_left1, derives_refl | apply derives_refl]|].
    apply extend_weak_valid_pointer.
  - eapply derives_trans; [apply sepcon_derives; [apply andp_left2, derives_refl | apply derives_refl]|].
    apply extend_weak_valid_pointer.
Qed.

Lemma buf_valid p c v : 0 <= c -> buf_res p c v |-- valid_pointer p.
Proof.
  intros. eapply derives_trans; [apply buf_free; auto|].
  destruct (eq_dec p nullval).
  - subst. apply valid_pointer_null.
  - entailer!.
Qed.

#[export] Hint Extern 1 (buf_res _ _ _ |-- valid_pointer _) => (apply buf_valid; rep_lia) : valid_pointer.

Lemma ptr_nn p : is_pointer_or_null p -> p <> nullval -> isptr p.
Proof. intros H1 H2. destruct p; simpl in *; try tauto. subst. exfalso; apply H2; reflexivity. Qed.

Lemma bytes_ok_of l : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes_ok l.
Proof. intros H. unfold bytes_ok. eapply Forall_impl; [|exact H]. intros b Hb. unfold is_byte. rep_lia. Qed.

Lemma if_drop_vp (d: val) (P: mpred) :
  (if eq_dec d nullval then emp else (P && valid_pointer d)) |-- (if eq_dec d nullval then emp else P).
Proof. destruct (eq_dec d nullval); [apply derives_refl | apply andp_left1, derives_refl]. Qed.

Lemma andp_drop_vp (A: mpred) p : A && valid_pointer p |-- A.
Proof. apply andp_left1, derives_refl. Qed.

Lemma pws_one w : pws_pred [w] = pw_pred w.
Proof. unfold pws_pred. simpl. apply sepcon_emp. Qed.

(* v3.2: a DDict state of the dictionary's bytes when no DDict is made (api 2) *)
Definition dd0 (wd: wdict) : ddict_st := {| dd_bytes := wd_bytes wd; dd_ref := None; dd_buf := nullval; dd_ld := None |}.

(* the dictionary the context decodes with after round 0: its own copy (api 2) or the DDict dd of state ddv (api 1, 3) *)
Definition dr_of (api: Z) (dd: val) (ddv: ddict_st) : dictref :=
  if Z.eq_dec api 2 then {| dr_src := DSOwn; dr_raw := false; dr_once := false; dr_bytes := dd_bytes ddv |}
  else ddict_ref dd ddv.


Lemma after_decode_facts st st' l : after_decode st st' l ->
  dc_ss st' = dc_ss st /\ dc_dict st' = dc_dict st /\ (dc_last st' = dc_last st \/ dc_last st' = l).
Proof. intros [-> | ->]; simpl; auto. Qed.


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

Ltac norm2 :=
  norm;
  repeat match goal with
  | H: Int.repr ?x = Int.repr ?y |- _ => apply repr_inj_unsigned in H; [|rep_lia|rep_lia]
  | H: Int.repr ?x <> Int.repr ?y |- _ => assert (x <> y) by (intro; subst; contradiction); clear H
  end;
  try (exfalso; lia);
  try discriminate;
  try match goal with H: ?x = ?y, H': ?x <> ?y |- _ => exfalso; exact (H' H) end.

Ltac blk_step :=
  first
  [ match goal with |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
      apply semax_if_seq; forward_if; norm2 end
  | match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end
  | match goal with |- semax _ _ (Sifthenelse _ _ _) _ => forward_if; norm2 end
  | forward; norm2 ].

Ltac if_set_post v :=
  match goal with
  | |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) ?c _ =>
      match c with context [Sifthenelse _ (Sset ?t _) _] =>
        forward_if (PROPx P (LOCALx (temp t v :: Q) (SEPx R))) end
  end.


(* ---------- borrowing the bytes of sr / wd (their first field) ---------- *)

Lemma borrow_of (P A R: mpred) : P |-- A * R -> A * R |-- P -> P |-- A * (A -* P).
Proof.
  intros H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
  apply wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma sr_unfold ws p : exists R: mpred,
  data_at Ews t_wseries (wseries_val ws) p = (
  field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p *
  field_at Ews t_wseries (DOT _n) (vl (Zlength (ws_bytes ws))) p *
  field_at Ews t_wseries (DOT _content) (zbytes (ws_content ws) ++ Zrepeat (Vint Int.zero) (2 ^ 18 - Zlength (ws_content ws))) p *
  field_at Ews t_wseries (DOT _content_n) (vl (Zlength (ws_content ws))) p * R)%logic.
Proof.
  eexists. unfold_data_at (data_at _ _ _ p). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma wd_unfold wd p stv : exists R: mpred,
  data_at Ews t_wdict (wdict_val wd p stv) p = (
  field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p *
  field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p * R)%logic.
Proof.
  eexists. unfold_data_at (data_at _ _ _ p). rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma sr_bytes_split ws p : Zlength (ws_bytes ws) <= 2 ^ 19 -> field_compatible t_wseries (DOT _bytes) p ->
  field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p =
  (data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) p *
   data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (field_address0 (tarray tuchar (2 ^ 19)) [ArraySubsc (Zlength (ws_bytes ws))] p))%logic.
Proof.
  intros Hn Hfc.
  rewrite field_at_data_at, field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  change (Tarray tuchar 524288 noattr) with (tarray tuchar (2^19)).
  apply (split2_data_at_Tarray_app (Zlength (ws_bytes ws)) (2^19)); rewrite ?Zlength_map, ?Zlength_Zrepeat; lia.
Qed.

Lemma sr_bytes_borrow ws p : Zlength (ws_bytes ws) <= 2 ^ 19 ->
  field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p |--
  data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) p *
  (data_at Ews (tarray tuchar (Zlength (ws_bytes ws))) (zbytes (ws_bytes ws)) p -*
   field_at Ews t_wseries (DOT _bytes) (zbytes (ws_bytes ws) ++ Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws))) p).
Proof.
  intros Hn.
  assert_PROP (field_compatible t_wseries (DOT _bytes) p) as Hfc by entailer!.
  apply borrow_of with (R := data_at Ews (tarray tuchar (2 ^ 19 - Zlength (ws_bytes ws))) (Zrepeat (Vint Int.zero) (2 ^ 19 - Zlength (ws_bytes ws)))
     (field_address0 (tarray tuchar (2 ^ 19)) [ArraySubsc (Zlength (ws_bytes ws))] p)); rewrite (sr_bytes_split ws p Hn Hfc); apply derives_refl.
Qed.

Lemma wd_bytes_split wd p : Zlength (wd_bytes wd) <= 6144 ->
  field_at Ews t_wdict (DOT _bytes) (zbytes (wd_bytes wd) ++ Zrepeat (Vint Int.zero) (6144 - Zlength (wd_bytes wd))) p |--
  data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) p * TT.
Proof.
  intros Hn.
  assert_PROP (field_compatible t_wdict (DOT _bytes) p) as Hfc by entailer!.
  rewrite field_at_data_at, field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  rewrite isptr_offset_val_zero by auto with field_compatible.
  change (Tarray tuchar 6144 noattr) with (tarray tuchar 6144).
  rewrite (split2_data_at_Tarray_app (Zlength (wd_bytes wd)) 6144) by (rewrite ?Zlength_map, ?Zlength_Zrepeat; lia).
  cancel.
Qed.

Lemma wd_take wd p stv : Zlength (wd_bytes wd) <= 6144 ->
  data_at Ews t_wdict (wdict_val wd p stv) p |--
  data_at Ews (tarray tuchar (Zlength (wd_bytes wd))) (zbytes (wd_bytes wd)) p *
  field_at Ews t_wdict (DOT _n) (vl (Zlength (wd_bytes wd))) p * TT.
Proof.
  intros Hn. destruct (wd_unfold wd p stv) as [R E]. rewrite E.
  sep_apply (wd_bytes_split wd p Hn). cancel.
Qed.

