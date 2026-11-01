(* FS3 streaming, case zdss_loadHeader: the lending of the DDict set's IDs / tokens and of getDDict's DDict (dgroup, dict_res, set_res). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope logic.

Section CM_LH3Lend_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- lending: A holds B, and gets back A when B is returned ---------- *)
Definition lendable (A B: mpred) : Prop := A |-- B * (B -* A).

Lemma lendable_of (A B R: mpred) : A |-- B * R -> B * R |-- A -> lendable A B.
Proof.
  intros H1 H2. unfold lendable. eapply derives_trans; [exact H1 | ].
  apply sepcon_derives; [apply derives_refl | ]. apply -> wand_sepcon_adjoint. rewrite sepcon_comm. exact H2.
Qed.

Lemma lendable_emp (A: mpred) : lendable A emp.
Proof. apply (lendable_of A emp A); rewrite emp_sepcon; auto. Qed.

Lemma lendable_refl (A: mpred) : lendable A A.
Proof. apply (lendable_of A A emp); rewrite sepcon_emp; auto. Qed.

Lemma lendable_sep (A1 B1 A2 B2: mpred) : lendable A1 B1 -> lendable A2 B2 -> lendable (A1 * A2) (B1 * B2).
Proof.
  unfold lendable. intros H1 H2.
  assert (HW: (B1 -* A1) * (B2 -* A2) |-- (B1 * B2 -* A1 * A2)).
  { apply -> wand_sepcon_adjoint.
    eapply derives_trans with ((B1 * (B1 -* A1)) * (B2 * (B2 -* A2))); [cancel | ].
    apply sepcon_derives; apply modus_ponens_wand. }
  eapply derives_trans; [apply sepcon_derives; [exact H1 | exact H2] | ].
  sep_apply HW. cancel.
Qed.

Lemma lendable_frame (A B C: mpred) : lendable A B -> lendable (A * C) B.
Proof.
  intros H. pose proof (lendable_sep A B C emp H (lendable_emp C)) as H2. rewrite sepcon_emp in H2. exact H2.
Qed.

Lemma lendable_frame_l (A B C: mpred) : lendable A B -> lendable (C * A) B.
Proof. intros H. rewrite sepcon_comm. apply lendable_frame; auto. Qed.

Lemma lendable_wand (A B: mpred) : lendable A B -> A |-- B * (B -* A).
Proof. auto. Qed.


Lemma lend_wand_frame (A B C: mpred) : (B -* A) * C |-- (B -* A * C).
Proof.
  apply -> wand_sepcon_adjoint. eapply derives_trans with ((B * (B -* A)) * C); [cancel | ].
  apply sepcon_derives; [apply modus_ponens_wand | apply derives_refl].
Qed.

(* lending one of several resources B x, chosen by the heap *)
Definition lendx {X: Type} (A: mpred) (P: X -> Prop) (B: X -> mpred) : Prop :=
  A |-- EX x: X, !! (P x) && (B x * (B x -* A)).

Lemma lendx_frame {X: Type} (A C: mpred) (P: X -> Prop) (B: X -> mpred) : lendx A P B -> lendx (A * C) P B.
Proof.
  unfold lendx. intros H. sep_apply H. Intros x. Exists x. rewrite prop_true_andp by auto.
  sep_apply (lend_wand_frame A (B x) C). cancel.
Qed.

Lemma lendx_frame_l {X: Type} (A C: mpred) (P: X -> Prop) (B: X -> mpred) : lendx A P B -> lendx (C * A) P B.
Proof. intros H. rewrite sepcon_comm. apply lendx_frame; auto. Qed.

Lemma lendx_eq {X: Type} (A A': mpred) (P: X -> Prop) (B: X -> mpred) : A = A' -> lendx A' P B -> lendx A P B.
Proof. intros E; subst; auto. Qed.

Lemma lendx_weak {X: Type} (A: mpred) (P Q: X -> Prop) (B: X -> mpred) :
  (forall x, P x -> Q x) -> lendx A P B -> lendx A Q B.
Proof.
  unfold lendx. intros HPQ H. sep_apply H. Intros x. Exists x. rewrite prop_true_andp by auto. cancel.
Qed.

(* ---------- the dictID of a DDict is a 32-bit value ---------- *)
Lemma lend_le_value_range: forall l, bytes_ok l -> 0 <= le_value l < 256 ^ Zlength l.
Proof.
  induction l as [| b l IH]; intros Hb; simpl; [lia |].
  inversion Hb as [| ? ? Hb1 Hb2]; subst. specialize (IH Hb2). unfold is_byte in Hb1.
  rewrite Zlength_cons, Z.pow_succ_r by (apply Zlength_nonneg). nia.
Qed.

Lemma lend_le_field_4_range: forall l i, bytes_ok l -> 0 <= le_field l i 4 <= Int.max_unsigned.
Proof.
  intros. unfold le_field, slice.
  assert (Hok: bytes_ok (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l))).
  { unfold bytes_ok in *. apply Forall_firstn, Forall_skipn. auto. }
  pose proof (lend_le_value_range _ Hok).
  assert (Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 4).
  { rewrite Zlength_correct, firstn_length. lia. }
  assert (256 ^ Zlength (firstn (Z.to_nat 4) (skipn (Z.to_nat i) l)) <= 256 ^ 4)
    by (apply Z.pow_le_mono_r; [lia | auto]).
  rep_lia.
Qed.

Lemma lend_dict_id_range: forall b, bytes_ok b -> 0 <= dict_id_of b <= Int.max_unsigned.
Proof.
  intros. unfold dict_id_of. destruct (Zlength b <? 8); [rep_lia |].
  destruct (negb _); [rep_lia | apply lend_le_field_4_range; auto].
Qed.

(* ---------- a DDict of the caller (FSRep3.DD3_of: pinned by dd) ---------- *)
Section DD.
Variable DENT : dent_pred.
Variable gv : globals.

Lemma DD3_props (q: val) (dd: ddict_st) :
  DD3_of DENT gv q dd |--
    !! (isptr q /\ ld_rel (dd_bytes dd) (dd_ld dd) /\ bytes_ok (dd_bytes dd) /\
        (isptr (dd_buf dd) \/ (dd_buf dd = nullval /\ dd_xref dd = Some nullval /\ dd_bytes dd = nil)) /\
        match dd_xref dd with Some p => dd_buf dd = p | None => True end /\
        dict_auto_c (dd_bytes dd) (dd_ld dd) <> None).
Proof.
  unfold DD3_of, ddict_rep_at, ddict_struct, dd_x. simpl. Intros.
  match goal with H: false = true \/ _ |- _ => destruct H as [H | H]; [discriminate | ] end.
  entailer!.
Qed.

Lemma DD3_valid (q: val) (dd: ddict_st) : DD3_of DENT gv q dd && valid_pointer q = DD3_of DENT gv q dd.
Proof.
  apply pred_ext; [apply andp_left1, derives_refl | ].
  apply andp_right; [apply derives_refl | ].
  unfold DD3_of, ddict_rep_at, ddict_struct. Intros. change (dx_q (dd_x q dd)) with q.
  do 8 apply sepcon_valid_pointer1. apply field_at_valid_ptr0; auto; simpl; lia.
Qed.

Lemma ddict_res3 (q: val) (dd: ddict_st) :
  ddict_res (DD3_of DENT) gv Ews q dd =
  DD3_of DENT gv q dd *
  match dd_ref dd with
  | Some p => data_at Ews (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
  | None => emp
  end.
Proof. unfold ddict_res. rewrite DD3_valid. reflexivity. Qed.

Lemma DD_lend_id (q: val) (dd: ddict_st) : lendable (DD3_of DENT gv q dd) (ddid q (dd_id dd) (ddb dd)).
Proof.
  unfold lendable. sep_apply (DD3_props q dd). Intros.
  assert (Hr: 0 <= dd_id dd <= Int.max_unsigned) by (apply lend_dict_id_range; tauto).
  unfold DD3_of, ddict_rep_at, ddict_struct, ddid, dd_x, ddb, dd_id in *. simpl. Intros.
  unfold ddx_copied; simpl. rewrite prop_true_andp by auto.
  destruct (dd_xref dd); unfold t_ddict; cancel;
    apply -> wand_sepcon_adjoint; Intros; entailer!.
Qed.

Lemma DD_lend_tok (q: val) (dd: ddict_st) :
  lendable (DD3_of DENT gv q dd) (field_at Ews t_ddict (DOT _dictBuffer) (ddb dd) q).
Proof.
  unfold lendable. sep_apply (DD3_props q dd). Intros.
  unfold DD3_of, ddict_rep_at, ddict_struct, dd_x, ddb in *. simpl. Intros.
  unfold ddx_copied; simpl.
  destruct (dd_xref dd); unfold t_ddict; cancel;
    apply -> wand_sepcon_adjoint; entailer!.
Qed.

Definition dd_lent (xb: ddx * val) : mpred :=
  ddict_struct (fst xb) (snd xb) * DENT gv (dx_q (fst xb)) (ddx_ent (fst xb)) * ddict_mem (fst xb) (snd xb).

Definition dd_facts (q: val) (dd: ddict_st) : Prop :=
  isptr q /\ ld_rel (dd_bytes dd) (dd_ld dd) /\ bytes_ok (dd_bytes dd) /\
  (isptr (dd_buf dd) \/ (dd_buf dd = nullval /\ dd_xref dd = Some nullval /\ dd_bytes dd = nil)) /\
  match dd_xref dd with Some p => dd_buf dd = p | None => True end /\
  dict_auto_c (dd_bytes dd) (dd_ld dd) <> None.

Lemma DD_lend_begin (q: val) (dd: ddict_st) :
  lendx (ddict_res (DD3_of DENT) gv Ews q dd)
        (fun xb => fst xb = dd_x q dd /\ snd xb = dd_buf dd /\ dd_facts q dd) dd_lent.
Proof.
  unfold lendx. rewrite ddict_res3. sep_apply (DD3_props q dd). Intros.
  Exists (dd_x q dd, dd_buf dd). rewrite prop_true_andp by (unfold dd_facts; simpl; tauto).
  unfold dd_lent, DD3_of, ddict_rep_at. simpl fst; simpl snd. cancel.
  apply -> wand_sepcon_adjoint. cancel.
Qed.

Lemma DD_lend_use (q: val) (dd: ddict_st) :
  lendx (ddict_res (DD3_of DENT) gv Ews q dd)
        (fun ad => ad = DA_ddict (dd_x q dd) (dd_buf dd) Ews /\ dd_facts q dd) (darg_res DENT gv).
Proof.
  unfold lendx. rewrite ddict_res3. sep_apply (DD3_props q dd). Intros.
  Exists (DA_ddict (dd_x q dd) (dd_buf dd) Ews). rewrite prop_true_andp by (unfold dd_facts; tauto).
  simpl darg_res. unfold ddx_copied, DD3_of. simpl dx_ref. simpl dx_bytes.
  destruct (dd_xref_cases dd) as [(p0 & Ep & Ex) | [(Ep & Hb & Ex) | (Ep & Hb & Ex)]]; rewrite Ep, Ex in *.
  - match goal with H: dd_buf dd = p0 |- _ => rewrite H end. saturate_local. rewrite bytes_at_ptr by auto.
    cancel. apply -> wand_sepcon_adjoint. cancel.
  - cancel. apply -> wand_sepcon_adjoint. cancel.
  - match goal with H: dd_buf dd = nullval |- _ => rewrite H end. rewrite bytes_at_null.
    cancel. apply -> wand_sepcon_adjoint. cancel.
Qed.

(* ---------- the local DDict (dgroup) ---------- *)

Definition dgroup_f (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p.

Lemma dgroup_split p d x buf :
  df_local d = dx_q x -> isptr (dx_q x) -> df_lx d = Some (x, buf) ->
  dgroup DENT gv p d = dgroup_f p d * ddict_rep_at DENT gv x buf.
Proof.
  intros H1 H2 H3. unfold dgroup, dgroup_f, local_rep. rewrite H1, H3.
  rewrite if_false by (destruct (dx_q x); simpl in *; try contradiction; discriminate).
  rewrite prop_true_andp by auto. reflexivity.
Qed.

Lemma local_lend_begin p d x buf :
  df_local d = dx_q x -> isptr (dx_q x) -> df_lx d = Some (x, buf) ->
  lendx (dgroup DENT gv p d)
    (fun xb => fst xb = x /\ snd xb = buf /\ ld_rel (dx_bytes x) (dx_ld x) /\ (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
               (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None)) dd_lent.
Proof.
  intros H1 H2 H3. unfold lendx. rewrite (dgroup_split p d x buf H1 H2 H3).
  assert_PROP (ld_rel (dx_bytes x) (dx_ld x) /\ (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
               (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None)) as Hs.
  { unfold ddict_rep_at, ddict_struct. entailer!. }
  Exists (x, buf). rewrite prop_true_andp by (simpl; tauto).
  unfold dd_lent, ddict_rep_at. simpl fst; simpl snd. cancel.
  apply -> wand_sepcon_adjoint. cancel.
Qed.

Lemma local_lend_use p d x buf :
  df_local d = dx_q x -> isptr (dx_q x) -> df_lx d = Some (x, buf) -> dx_ref x = None ->
  lendx (dgroup DENT gv p d)
    (fun ad => ad = DA_ddict x buf Ews /\ ld_rel (dx_bytes x) (dx_ld x) /\ isptr buf) (darg_res DENT gv).
Proof.
  intros H1 H2 H3 H4. unfold lendx. rewrite (dgroup_split p d x buf H1 H2 H3).
  assert_PROP (ld_rel (dx_bytes x) (dx_ld x) /\ isptr buf) as Hs.
  { unfold ddict_rep_at, ddict_struct. Intros.
    match goal with H: isptr buf \/ _ |- _ => destruct H as [? | (_ & ? & _)]; [| congruence] end. entailer!. }
  Exists (DA_ddict x buf Ews). rewrite prop_true_andp by tauto.
  simpl darg_res. unfold ddx_copied. rewrite H4. cancel.
  apply -> wand_sepcon_adjoint. cancel.
Qed.

(* ---------- the set ---------- *)

Lemma set_res_cons DD sh e (l: list (val * ddict_st)) cur :
  set_res DD gv sh (e :: l) cur =
  (match cur_ddict cur with
   | Some q => if Val.eq (fst e) q then emp else ddict_res DD gv sh (fst e) (snd e)
   | None => ddict_res DD gv sh (fst e) (snd e)
   end) * set_res DD gv sh l cur.
Proof. reflexivity. Qed.

Lemma set_res_app DD sh (l1 l2: list (val * ddict_st)) cur :
  set_res DD gv sh (l1 ++ l2) cur = set_res DD gv sh l1 cur * set_res DD gv sh l2 cur.
Proof.
  induction l1 as [ | e l1 IH]; simpl app.
  - unfold set_res at 2. simpl. rewrite emp_sepcon. reflexivity.
  - rewrite !set_res_cons, IH. rewrite sepcon_assoc. reflexivity.
Qed.

(* without a current DDict in the set, set_res holds every DDict *)
Lemma set_res_nocur DD sh (l: list (val * ddict_st)) cur :
  (forall q, cur_ddict cur = Some q -> ~ In q (map fst l)) -> set_res DD gv sh l cur = set_res DD gv sh l None.
Proof.
  induction l as [ | e l IH]; intros H; [reflexivity | ].
  rewrite !set_res_cons. simpl cur_ddict. rewrite IH.
  - f_equal. destruct (cur_ddict cur) as [q | ] eqn:E; [ | reflexivity].
    destruct (Val.eq (fst e) q); [ | reflexivity]. exfalso. apply (H q); [first [reflexivity | exact E] | simpl; auto].
  - intros q E Hin. apply (H q E). simpl. auto.
Qed.

Lemma set_lend_ids (l: list (val * ddict_st)) :
  lendable (set_res (DD3_of DENT) gv Ews l None) (set_ids l).
Proof.
  induction l as [ | e l IH].
  - unfold set_res, set_ids. simpl. apply lendable_refl.
  - rewrite set_res_cons. simpl cur_ddict. unfold set_ids. simpl map. simpl fold_right. fold (set_ids l).
    apply lendable_sep; [ | exact IH]. rewrite ddict_res3. apply lendable_frame. apply DD_lend_id.
Qed.

(* a DDict of the set other than the current one, out of set_res *)
Lemma set_res_extract DD sh (l: list (val * ddict_st)) cur q dd :
  In (q, dd) l -> cur_ddict cur <> Some q ->
  exists R, set_res DD gv sh l cur = ddict_res DD gv sh q dd * R.
Proof.
  induction l as [ | e l IH]; intros Hin Hc; [contradiction | ].
  rewrite set_res_cons.
  destruct Hin as [E | Hin].
  - subst e. exists (set_res DD gv sh l cur). simpl fst; simpl snd. f_equal.
    destruct (cur_ddict cur) as [q0 | ]; [ | reflexivity].
    destruct (Val.eq q q0); [subst; congruence | reflexivity].
  - destruct (IH Hin Hc) as [R HR]. rewrite HR.
    match goal with |- exists _, ?T * (?D * R) = _ => exists (T * R) end.
    apply pred_ext; cancel.
Qed.

End DD.
(* ---------- the selection's resources (lend_sel_ok) ---------- *)

Lemma cur_ok_switched d l xq : dict_switched l d -> cur_ok d l xq.
Proof. intros (_ & Hu & _ & Hin). split; [left; auto | right; right; left; auto]. Qed.

Lemma sel_lend (DENT: dent_pred) (gv: globals) (W: list ptr_witness) (st: dctx_st) (d: dfields) :
  dict_rel3 st d -> set_cur_ok st -> stream_dict_ok W st -> NoDup (map fst (dc_set st)) ->
  exists xq: option (val * val), cur_ok d (dc_set st) xq /\
    lendable (dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))
             (set_ids (dc_set st) * opt_token xq).
Proof.
  intros Hrel Hcur Hsd Hnd. unfold DD3x.
  pose proof (set_lend_ids DENT gv (dc_set st)) as Hids.
  destruct (dc_dict st) as [dr | ] eqn:Hd.
  2:{ exists None. split.
      - destruct Hrel as [Hr | [_ Hs]]; [ | apply cur_ok_switched; auto].
        rewrite Hd in Hr. destruct Hr as [Hu Hdd]. split; [auto | ]. destruct Hdd; auto.
      - simpl dict_res. simpl opt_token. rewrite emp_sepcon, sepcon_emp. exact Hids. }
  unfold stream_dict_ok in Hsd. rewrite Hd in Hsd. destruct Hsd as [[Honce Hsrc] [Hset _]].
  destruct (dr_src dr) as [pk | | q dd] eqn:Hs; [contradiction | | ].
  - (* the context's own copy: no caller DDict in dict_res *)
    exists None. split.
    + destruct Hrel as [Hr | [_ Hsw]]; [ | apply cur_ok_switched; auto].
      rewrite Hd in Hr. unfold dict_rel3_of in Hr. rewrite Hs in Hr. destruct Hr as (_ & Hr).
      destruct (Zlength (dr_bytes dr) =? 0).
      * subst d. split; simpl; auto.
      * destruct Hr as (buf & ld & am & _ & E & U & _). split; auto.
    + unfold dict_res. rewrite Hs. simpl opt_token. rewrite emp_sepcon, sepcon_emp.
      rewrite (set_res_nocur gv (DD3_of DENT) Ews (dc_set st) (Some dr)) by (simpl; rewrite Hs; discriminate). exact Hids.
  - (* a caller's DDict q *)
    assert (Hcq: cur_ddict (Some dr) = Some q) by (simpl; rewrite Hs; reflexivity).
    assert (Hdr: dict_res (DD3_of DENT) gv Ews (Some dr) = ddict_res (DD3_of DENT) gv Ews q dd)
      by (unfold dict_res; rewrite Hs; reflexivity).
    rewrite Hdr.
    assert (Hcu: df_uses d = -1 /\ df_ddict d = q \/ dict_switched (dc_set st) d).
    { destruct Hrel as [Hr | [_ Hsw]]; [ | right; auto].
      rewrite Hd in Hr. unfold dict_rel3_of in Hr. rewrite Hs in Hr. destruct Hr as (_ & _ & _ & _ & E & U & _). auto. }
    destruct (in_dec Val.eq q (map fst (dc_set st))) as [Hin | Hnin].
    + exists None. split.
      * destruct Hcu as [[U E] | Hsw]; [ | apply cur_ok_switched; auto].
        split; [auto | ]. rewrite E. auto.
      * apply in_map_iff in Hin. destruct Hin as [[q0 dd0] [Eq Hin]]. simpl in Eq. subst q0.
        assert (Edd: dd0 = dd) by (apply (Hcur dr q dd dd0); auto).
        subst dd0. simpl opt_token. rewrite sepcon_emp.
        destruct (in_split _ _ Hin) as [l1 [l2 Hl]].
        rewrite Hl in Hnd, Hids |- *. rewrite map_app in Hnd. simpl map in Hnd.
        pose proof (NoDup_remove_2 _ _ _ Hnd) as Hn12. rewrite in_app_iff in Hn12.
        rewrite set_res_app, set_res_cons, Hcq. simpl fst; simpl snd.
        rewrite if_true by auto. rewrite emp_sepcon.
        rewrite (set_res_nocur gv (DD3_of DENT) Ews l1 (Some dr)) by (rewrite Hcq; intros q0 E; inv E; tauto).
        rewrite (set_res_nocur gv (DD3_of DENT) Ews l2 (Some dr)) by (rewrite Hcq; intros q0 E; inv E; tauto).
        rewrite set_res_app, set_res_cons in Hids. simpl cur_ddict in Hids. simpl fst in Hids; simpl snd in Hids.
        replace (ddict_res (DD3_of DENT) gv Ews q dd *
                 (set_res (DD3_of DENT) gv Ews l1 None * set_res (DD3_of DENT) gv Ews l2 None))
          with (set_res (DD3_of DENT) gv Ews l1 None *
                (ddict_res (DD3_of DENT) gv Ews q dd * set_res (DD3_of DENT) gv Ews l2 None)) by (apply pred_ext; cancel).
        exact Hids.
    + exists (Some (q, ddb dd)). split.
      * destruct Hcu as [[U E] | Hsw]; [ | apply cur_ok_switched; auto].
        split; [auto | ]. rewrite E. right; right; right. exists (ddb dd). reflexivity.
      * rewrite (set_res_nocur gv (DD3_of DENT) Ews (dc_set st) (Some dr)) by (rewrite Hcq; intros q0 E; inv E; auto).
        simpl opt_token. rewrite (sepcon_comm (set_ids _)).
        apply lendable_sep; [ | exact Hids]. rewrite ddict_res3. apply lendable_frame. apply DD_lend_tok.
Qed.

(* ---------- getDDict's DDict ---------- *)

(* a caller's DDict q: the context's (dict_res) or one of the set's (set_res) *)
Lemma caller_extract (DENT: dent_pred) (gv: globals) (st: dctx_st) (q: val) :
  cur_ddict (dc_dict st) = Some q \/ (In q (map fst (dc_set st)) /\ cur_ddict (dc_dict st) <> Some q) ->
  exists dd R, dd_caller st q dd /\
    dict_res (DD3_of DENT) gv Ews (dc_dict st) * set_res (DD3_of DENT) gv Ews (dc_set st) (dc_dict st) =
    ddict_res (DD3_of DENT) gv Ews q dd * R.
Proof.
  intros [Hc | [Hin Hc]].
  - destruct (dc_dict st) as [dr | ] eqn:Hd; [ | discriminate]. simpl in Hc.
    destruct (dr_src dr) as [pk | | q0 dd] eqn:Hs; try discriminate. inv Hc.
    exists dd, (set_res (DD3_of DENT) gv Ews (dc_set st) (Some dr)).
    split.
    + right. exists dr. auto.
    + unfold dict_res. rewrite Hs. reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [[q0 dd] [Eq Hin]]. simpl in Eq. subst q0.
    destruct (set_res_extract gv (DD3_of DENT) Ews (dc_set st) (dc_dict st) q dd Hin Hc) as [R HR].
    exists dd, (dict_res (DD3_of DENT) gv Ews (dc_dict st) * R). split; [left; auto | ].
    rewrite HR. apply pred_ext; cancel.
Qed.

Lemma dd_caller_sddict (W: list ptr_witness) (st: dctx_st) (q: val) (dd: ddict_st) :
  stream_dict_ok W st -> dd_caller st q dd -> sddict_ok W dd.
Proof.
  intros (H1 & H2 & _) [Hin | (dr & Hd & Hs)].
  - rewrite Forall_forall in H2. apply (H2 _ Hin).
  - rewrite Hd in H1. destruct H1 as [_ H1]. rewrite Hs in H1. exact H1.
Qed.

(* what getDDict returns, when not NULL: the local DDict (a copy), or a caller's DDict *)
Lemma getdd_cases (W: list ptr_witness) (st: dctx_st) (d: dfields) :
  dict_rel3 st d -> stream_dict_ok W st -> fst (getddict_res d) <> nullval ->
  fst (getddict_res d) = df_ddict d /\
  ((exists x buf, df_local d = dx_q x /\ isptr (dx_q x) /\ df_lx d = Some (x, buf) /\ dx_ref x = None /\
       df_ddict d = dx_q x /\
       (dc_set st = nil -> exists dr, dc_dict st = Some dr /\ dr_raw dr = dx_raw x /\ dr_bytes dr = dx_bytes x)) \/
   ((cur_ddict (dc_dict st) = Some (df_ddict d) \/
     (In (df_ddict d) (map fst (dc_set st)) /\ cur_ddict (dc_dict st) <> Some (df_ddict d))) /\
    (dc_set st = nil -> exists dr dd, dc_dict st = Some dr /\ dr_raw dr = false /\
                                      dr_src dr = DSDDict (df_ddict d) dd))).
Proof.
  intros Hrel Hsd Hg.
  assert (Hfst: fst (getddict_res d) = df_ddict d).
  { unfold getddict_res in *. destruct (df_uses d =? 0); [contradiction | ].
    destruct (df_uses d =? 1); reflexivity. }
  assert (Hu: df_uses d <> 0).
  { intros E. unfold getddict_res in Hg. rewrite E in Hg. contradiction. }
  split; [exact Hfst | ].
  destruct Hrel as [Hr | [Hn Hsw]].
  - unfold dict_rel3_of in Hr. destruct (dc_dict st) as [dr | ] eqn:Hd; [ | destruct Hr as [U _]; contradiction].
    unfold stream_dict_ok in Hsd. rewrite Hd in Hsd. destruct Hsd as [[_ Hsrc] _].
    destruct (dr_src dr) as [pk | | q dd] eqn:Hs; [contradiction | | ].
    + destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0).
      * subst d. simpl in Hu. congruence.
      * destruct Hr as (buf & ld & am & Hp & E & U & Hlx). left.
        exists {| dx_q := df_local d; dx_bytes := dr_bytes dr; dx_ref := None; dx_raw := dr_raw dr; dx_ld := ld;
                  dx_mem := am |}, buf.
        simpl. split; [auto | ]. split; [auto | ]. split; [auto | ]. split; [auto | ]. split; [auto | ].
        intros _. exists dr. auto.
    + destruct Hr as (Hraw & _ & Hq & _ & E & _ & _). right. split.
      * left. simpl. rewrite Hs, E. reflexivity.
      * intros _. exists dr, dd. rewrite E. auto.
  - right. destruct Hsw as (_ & _ & _ & Hin). split; [ | intros E; contradiction].
    destruct (cur_ddict (dc_dict st)) as [q0 | ] eqn:Ec.
    + destruct (Val.eq q0 (df_ddict d)) as [E | E]; [subst; left; auto | right; split; [auto | congruence]].
    + right. split; [auto | discriminate].
Qed.

Lemma getdd_d2 (d: dfields) :
  fst (getddict_res d) <> nullval ->
  df_local (snd (getddict_res d)) = df_local d /\ df_lx (snd (getddict_res d)) = df_lx d /\
  df_ddict (snd (getddict_res d)) = df_ddict d.
Proof.
  unfold getddict_res. destruct (df_uses d =? 0); [intros H; contradiction H; reflexivity | intros _].
  destruct (df_uses d =? 1); simpl; auto.
Qed.

(* ZSTD_decompressBegin_usingDDict's DDict *)
Lemma begin_lend (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3) :
  c3_set k = dc_set st -> dict_rel3 st (c3_dict k) -> set_cur_ok st -> stream_dict_ok W st ->
  fst (getddict_res (c3_dict k)) <> nullval ->
  lendx (dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
         set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))
        (fun xb => lh_dd_ok st k (fst xb) (snd xb)) (dd_lent DENT gv).
Proof.
  intros Hset Hrel Hcur Hsd Hg. unfold DD3x.
  destruct (getdd_cases W st (c3_dict k) Hrel Hsd Hg) as [Hfst [Hloc | [Hcl _]]].
  - destruct Hloc as (x & buf & Hl & Hq & Hlx & Hr & Hdd & _).
    assert (Hd2: df_local (snd (getddict_res (c3_dict k))) = df_local (c3_dict k) /\
                 df_lx (snd (getddict_res (c3_dict k))) = df_lx (c3_dict k)).
    { destruct (getdd_d2 (c3_dict k) Hg) as (E1 & E2 & _). auto. }
    destruct Hd2 as [E1 E2].
    rewrite sepcon_assoc. apply lendx_frame.
    eapply lendx_weak; [ | apply (local_lend_begin DENT gv p _ x buf); [rewrite E1; auto | auto | rewrite E2; auto]].
    intros [x' buf'] (Ex & Eb & Hld & Hbuf & Hau). simpl in Ex, Eb. subst x' buf'. simpl fst; simpl snd.
    unfold lh_dd_ok. rewrite Hfst. split; [auto | ]. split; [destruct (dx_q x); simpl in Hq; try contradiction; discriminate | ].
    split; [ | auto]. left. simpl. rewrite E1, E2. split; [auto | ]. split.
    + destruct (dx_q x); simpl in Hq; try contradiction; discriminate.
    + split; [unfold ddx_copied; rewrite Hr; reflexivity | auto].
  - destruct (caller_extract DENT gv st _ Hcl) as (dd & R & Hdc & HR).
    rewrite sepcon_assoc, HR. apply lendx_frame_l. apply lendx_frame.
    eapply lendx_weak; [ | apply DD_lend_begin].
    intros [x buf] (Hx & Hb & Hqp & Hld & _ & Hbuf & _ & Hau). cbn [fst snd] in *. subst x buf.
    unfold lh_dd_ok. simpl dx_q. simpl dx_bytes. simpl dx_ld. simpl dx_raw. rewrite Hfst.
    split; [auto | ].
    split; [destruct (df_ddict (c3_dict k)); simpl in Hqp; try contradiction; discriminate | ].
    split; [ | auto]. right. exists dd. auto.
Qed.

(* the facts ZSTD_decompress_usingDDict needs of its dictionary argument *)
Definition use_arg_ok (W: list ptr_witness) (st: dctx_st) (k: cst3) (shd: share) (cap: Z) (dst: val) (ad: darg) : Prop :=
  darg_is_ddict ad /\ darg_ddict ad = fst (getddict_res (c3_dict k)) /\ darg_ok3 W ad shd cap dst /\
  (dc_set st = nil -> forall dm, dictref_model (dc_dict st) = Some dm -> darg_model ad = Some dm).

(* FS3 R3: at cap 0 the valid pointer of the 0-byte dictionary is enough (dict_ptr_ok0) *)
Lemma ptr_ok_zero (W: list ptr_witness) (shd: share) (cap: Z) (dst p0: val) :
  writable_share shd -> 0 <= cap ->
  (pws_pred W |-- valid_pointer p0) -> dict_ptr_ok0 W Ews 0 p0 shd cap dst.
Proof.
  intros Hw Hc0 Hp. destruct (Z.eq_dec cap 0) as [E | Hc].
  { right. split; [exact E | ]. split; [reflexivity | exact Hp]. }
  left. right. split; [reflexivity | ]. split; [exact Hp | ].
  apply sepcon_valid_pointer2. apply data_at__valid_ptr.
  - auto with share.
  - simpl. rewrite Z.max_r by lia. lia.
Qed.

(* ZSTD_decompress_usingDDict's dictionary argument *)
Lemma use_lend (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3)
      (shd: share) (cap: Z) (dst: val) :
  dd_bytes_ok st ->
  c3_set k = dc_set st -> dict_rel3 st (c3_dict k) -> set_cur_ok st -> stream_dict_ok W st ->
  writable_share shd -> buf_ok W shd cap dst -> 0 <= cap ->
  lendx (dgroup DENT gv p (snd (getddict_res (c3_dict k))) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
         set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))
        (use_arg_ok W st k shd cap dst) (darg_res DENT gv).
Proof.
  intros Hbok Hset Hrel Hcur Hsd Hw Hbo Hc0. unfold DD3x.
  destruct (eq_dec (fst (getddict_res (c3_dict k))) nullval) as [Hn | Hg].
  - (* no DDict *)
    unfold lendx. Exists DA_none. rewrite prop_true_andp.
    { simpl darg_res. pose proof (lendable_emp (dgroup DENT gv p (snd (getddict_res (c3_dict k))) *
        dict_res (DD3_of DENT) gv Ews (dc_dict st) * set_res (DD3_of DENT) gv Ews (dc_set st) (dc_dict st))) as H.
      exact H. }
    split; [exact I | ]. split; [simpl; auto | ]. split; [exact I | ].
    intros Hnil dm Hdm. destruct Hrel as [Hr | [Hne _]]; [ | contradiction].
    unfold dict_rel3_of in Hr. destruct (dc_dict st) as [dr | ] eqn:Hd; [ | simpl in Hdm; exact Hdm].
    unfold stream_dict_ok in Hsd. rewrite Hd in Hsd. destruct Hsd as [[_ Hsrc] _].
    destruct (dr_src dr) as [pk | | q dd] eqn:Hs; [contradiction | | ].
    + destruct Hr as (_ & Hr). destruct (Zlength (dr_bytes dr) =? 0) eqn:Hz.
      * apply Z.eqb_eq in Hz. apply Zlength_nil_inv in Hz.
        simpl in Hdm. rewrite Hz in Hdm. destruct (dr_raw dr); simpl in Hdm; inv Hdm; reflexivity.
      * destruct Hr as (buf & ld & am & Hp & E & U & _). exfalso.
        unfold getddict_res in Hn. rewrite U in Hn. simpl in Hn. rewrite E in Hn. subst.
        rewrite Hn in Hp. contradiction.
    + destruct Hr as (_ & _ & Hq & _ & E & U & _). exfalso.
      unfold getddict_res in Hn. rewrite U in Hn. simpl in Hn. rewrite E in Hn. rewrite Hn in Hq. contradiction.
  - destruct (getdd_cases W st (c3_dict k) Hrel Hsd Hg) as [Hfst [Hloc | [Hcl Hnil]]].
    + (* the local DDict (a copy) *)
      destruct Hloc as (x & buf & Hl & Hq & Hlx & Hr & Hdd & Hm).
      destruct (getdd_d2 (c3_dict k) Hg) as (E1 & E2 & _).
      rewrite sepcon_assoc. apply lendx_frame.
      eapply lendx_weak; [ | apply (local_lend_use DENT gv p _ x buf); [rewrite E1; auto | auto | rewrite E2; auto | auto]].
      intros ad (Ead & Hld & Hbuf). subst ad. unfold use_arg_ok. simpl.
      split; [exact I | ]. split; [rewrite Hfst; auto | ]. split.
      { unfold ddx_copied. rewrite Hr. discriminate. }
      intros Hn dm Hdm. destruct (Hm Hn) as (dr & Hd & Hdr & Hb). rewrite Hd in Hdm. simpl in Hdm.
      rewrite Hdr, Hb in Hdm. apply ddx_model_some; auto.
    + (* a caller's DDict *)
      destruct (caller_extract DENT gv st _ Hcl) as (dd & R & Hdc & HR).
      rewrite sepcon_assoc, HR. apply lendx_frame_l. apply lendx_frame.
      eapply lendx_weak; [ | apply DD_lend_use].
      intros ad (Ead & Hqp & Hld & Hbk & Hbuf & Hbr & Hau). subst ad.
      unfold use_arg_ok. simpl. split; [exact I | ]. split; [rewrite Hfst; auto | ]. split.
      * unfold ddx_copied. simpl. intros Hc Hbn.
        destruct (dd_xref_cases dd) as [(p0 & Ep & Ex) | [(Ep & Hb & Ex) | (Ep & Hb & Ex)]];
          rewrite Ex in Hc, Hbr; try discriminate; [| contradiction].
        subst p0. pose proof (dd_caller_sddict W st _ dd Hsd Hdc) as Hs. unfold sddict_ok in Hs.
        rewrite Ep in Hs. destruct Hs as [Hnb Hvp]. split; [auto | ].
        rewrite Hnb, Zlength_nil. apply ptr_ok_zero; auto.
      * intros Hn dm Hdm. destruct (Hnil Hn) as (dr & dd' & Hd & Hdr & Hs).
        destruct Hdc as [Hin | (dr' & Hd' & Hs')]; [rewrite Hn in Hin; contradiction | ].
        rewrite Hd in Hd'. inv Hd'. rewrite Hs in Hs'. inv Hs'.
        rewrite Hd in Hdm. simpl in Hdm. rewrite Hdr in Hdm. rewrite (Hbok Hn dr' _ dd Hd Hs) in Hdm.
        unfold ddx_model. simpl. apply ld_rel_auto_some; auto.
Qed.

Lemma lend_sel_holds : lend_sel_ok.
Proof.
  intros DENT gv W st d Hrel Hcur Hsd Hnd _.
  destruct (sel_lend DENT gv W st d Hrel Hcur Hsd Hnd) as [xq [Hok Hl]].
  exists xq. split; [exact Hok | exact Hl].
Qed.

Lemma lend_begin_holds : lend_begin_ok.
Proof.
  intros DENT gv p W st k Hset Hrel Hcur Hsd Hg.
  eapply derives_trans; [apply (begin_lend DENT gv p W st k); auto | ].
  Intros xb. destruct xb as [x buf]. Exists x buf. rewrite prop_true_andp by auto. apply derives_refl.
Qed.

Lemma lend_use_holds : lend_use_ok.
Proof.
  intros DENT gv p W st k shd cap dst Hset Hrel Hcur Hsd Hbok Hw Hbo Hc0.
  eapply derives_trans; [apply (use_lend DENT gv p W st k shd cap dst); auto | ].
  Intros ad. Exists ad. rewrite prop_true_andp by (unfold use_arg_ok in *; auto). apply derives_refl.
Qed.

Lemma lend_ok : lend_sel_ok /\ lend_use_ok /\ lend_begin_ok.
Proof. split; [exact lend_sel_holds | split; [exact lend_use_holds | exact lend_begin_holds]]. Qed.

End CM_LH3Lend_1.
