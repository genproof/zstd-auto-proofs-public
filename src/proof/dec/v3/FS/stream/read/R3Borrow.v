(* FS3 streaming (shared with case zdss_load): the frame's DDict lends ZSTD_decompressContinue(Stream) its
   entropy (dent_of) and its content bytes (lay_res), from the context's local DDict (dgroup) or from the
   caller's DDicts (dict_res / set_res); a magic wand gives them back. *)
Require Export Zstd.proof.dec.v3.FS.stream.read.R3Base.
Local Open Scope logic.

Section CM_R3Borrow_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Borrow.
Variable DENT : dent_pred.

(* the content bytes of a DDict x at buf (none for the DDict without content, buf = NULL) *)
Definition dd_bytes_res (x: ddx) (buf: val) : mpred := bytes_at Ews (dx_bytes x) buf.

(* what the frame's DDict lends to the unit's decoding *)
Definition dd_lend (gv: globals) (dd: option (ddx * val)) : mpred :=
  match dd with
  | None => emp
  | Some (x, buf) => DENT gv (dx_q x) (ddx_ent x) * dd_bytes_res x buf
  end.

(* the pure facts of the frame's DDict (ddict_struct, stream_dict_ok) *)
Definition dd_facts (W: list ptr_witness) (dd: option (ddx * val)) : Prop :=
  match dd with
  | None => True
  | Some (x, buf) =>
      bytes_ok (dx_bytes x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\
      (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
      (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\
      (ddx_copied x = true \/ (dx_bytes x = nil /\ (pws_pred W |-- valid_pointer buf))) /\
      ld_rel (dx_bytes x) (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None)
  end.

Lemma lend_wand : forall (A P R: mpred), (A |-- P * R) -> (R * P |-- A) -> A |-- P * (P -* A).
Proof.
intros A P R H1 H2. eapply derives_trans; [exact H1|]. apply sepcon_derives; [apply derives_refl|].
apply wand_sepcon_adjoint. exact H2.
Qed.

Lemma ddict_rep_at_vp : forall gv x buf, ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
intros. unfold ddict_rep_at, ddict_struct. Intros.
sep_apply (field_at_valid_ptr0 Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer)); auto.
entailer!.
Qed.

(* the parts of a DDict besides what it lends *)
Definition dd_rest (x: ddx) (buf: val) : mpred :=
  ddict_struct x buf * ddict_pad (dx_q x) * blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
  (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp).

Definition dd_facts0 (x: ddx) (buf: val) : Prop :=
  bytes_ok (dx_bytes x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\
  (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
  (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\
  ld_rel (dx_bytes x) (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None) /\
  isptr (dx_q x) /\ (match dx_ref x with Some p => buf = p | None => True end).

Lemma dd_rest_facts : forall x buf, dd_rest x buf |-- !! dd_facts0 x buf.
Proof.
intros. unfold dd_rest, ddict_struct, dd_facts0. Intros. entailer!.
Qed.

(* a copied DDict *)
Lemma rep_split_copied : forall gv x buf, ddx_copied x = true ->
  ddict_rep_at DENT gv x buf = dd_lend gv (Some (x, buf)) * dd_rest x buf.
Proof.
intros gv x buf Hc. unfold ddict_rep_at, dd_lend, dd_rest, ddict_mem, dd_bytes_res. rewrite Hc.
apply pred_ext; unfold ddict_struct; Intros;
  match goal with H: isptr buf \/ _ |- _ => pose proof (ddx_buf_copied x buf Hc H) end;
  rewrite bytes_at_ptr by auto; entailer!.
Qed.

(* the caller's content pointer of a DDict by reference is a pointer (its bytes are there) *)
Lemma ddict_res_ref_ptr : forall gv q dd,
  ddict_res (DD3x DENT) gv Ews q dd |-- !! (forall p, dd_ref dd = Some p -> isptr p).
Proof.
intros gv q dd. unfold ddict_res. destruct (dd_ref dd) as [p|] eqn:Er.
- Intros. entailer!. intros p0 E. inversion E; subst p0; auto.
- apply prop_right. intros p0 E. discriminate.
Qed.

(* a caller's DDict by reference (its bytes are the caller's, at buf) *)
Lemma res_split : forall gv q dd, (forall p, dd_ref dd = Some p -> isptr p) ->
  ddict_res (DD3x DENT) gv Ews q dd =
  dd_lend gv (Some (dd_x q dd, dd_buf dd)) * dd_rest (dd_x q dd) (dd_buf dd).
Proof.
intros gv q dd Hptr. unfold ddict_res, DD3x, DD3_of.
assert (E: ddict_rep_at DENT gv (dd_x q dd) (dd_buf dd) && valid_pointer q =
           ddict_rep_at DENT gv (dd_x q dd) (dd_buf dd)).
{ apply pred_ext; [apply andp_left1, derives_refl|].
  apply andp_right; [apply derives_refl|]. apply (ddict_rep_at_vp gv (dd_x q dd) (dd_buf dd)). }
rewrite E. clear E.
destruct (dd_xref_cases dd) as [(p & Er & Ex) | [(Er & Hb & Ex) | (Er & Hb & Ex)]]; rewrite Er.
- (* by reference to the caller's p *)
  assert (Hc: ddx_copied (dd_x q dd) = false) by (unfold ddx_copied, dd_x; simpl; rewrite Ex; reflexivity).
  specialize (Hptr p Er).
  unfold ddict_rep_at, dd_lend, dd_rest, ddict_mem, dd_bytes_res. rewrite Hc.
  apply pred_ext.
  + unfold ddict_struct at 1. Intros. cbn [dx_ref dd_x] in *. rewrite Ex in *. subst p.
    rewrite bytes_at_ptr by auto. unfold ddict_struct. cbn [dx_bytes dx_ref dd_x]. rewrite Ex. entailer!.
  + unfold ddict_struct. Intros. cbn [dx_bytes dx_ref dd_x] in *. rewrite Ex in *. subst p.
    rewrite bytes_at_ptr by auto. entailer!.
- (* zstd's copy *)
  assert (Hc: ddx_copied (dd_x q dd) = true) by (unfold ddx_copied, dd_x; simpl; rewrite Ex; reflexivity).
  rewrite sepcon_emp. apply rep_split_copied; auto.
- (* no content: its buffer is NULL, no bytes *)
  assert (Hc: ddx_copied (dd_x q dd) = false) by (unfold ddx_copied, dd_x; simpl; rewrite Ex; reflexivity).
  unfold ddict_rep_at, dd_lend, dd_rest, ddict_mem, dd_bytes_res. rewrite Hc, sepcon_emp.
  apply pred_ext.
  + unfold ddict_struct at 1. Intros. cbn [dx_ref dd_x] in *. rewrite Ex in *.
    match goal with H: dd_buf dd = nullval |- _ => rewrite H in * end. rewrite bytes_at_null.
    unfold ddict_struct. cbn [dx_bytes dx_ref dd_x]. rewrite Ex. entailer!.
  + unfold ddict_struct. Intros. cbn [dx_bytes dx_ref dd_x] in *. rewrite Ex in *.
    match goal with H: dd_buf dd = nullval |- _ => rewrite H in * end. rewrite bytes_at_null. entailer!.
Qed.

Lemma fold_sep_split : forall {A: Type} (f: A -> mpred) l1 e l2,
  fold_right sepcon emp (map f (l1 ++ e :: l2)) =
  f e * (fold_right sepcon emp (map f l1) * fold_right sepcon emp (map f l2)).
Proof.
intros A f l1 e l2. induction l1 as [|a l1 IH]; simpl.
- rewrite emp_sepcon. reflexivity.
- rewrite IH. apply pred_ext; cancel.
Qed.

(* the dictionary memory a stream holds (the context's dgroup and the caller's dict_res / set_res) *)
Definition dd_all (gv: globals) (p: val) (st: dctx_st) (d: dfields) : mpred :=
  dgroup DENT gv p d * dict_res (DD3x DENT) gv Ews (dc_dict st) *
  set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st).

Lemma sddict_facts : forall W q dd buf, sddict_ok W dd -> dd_facts0 (dd_x q dd) buf ->
  dd_facts W (Some (dd_x q dd, buf)).
Proof.
intros W q dd buf Hs (H1&H2&H3&H4&H5&H6&_&H8). unfold dd_facts. do 4 (split; [assumption|]).
split; [|split; assumption].
unfold ddx_copied, sddict_ok in *. cbn [dx_ref dx_bytes dd_x] in *.
destruct (dd_xref_cases dd) as [(p & Er & Ex) | [(Er & Hb & Ex) | (Er & Hb & Ex)]]; rewrite Ex in *.
- right. rewrite Er in Hs. subst p. exact Hs.
- left; reflexivity.
- right. subst buf. split; [exact Hb | apply valid_pointer_null].
Qed.

(* a caller's DDict q dd (in the set, or the context's dictionary) *)
Definition set_f (gv: globals) (cur: option dictref) (e: val * ddict_st) : mpred :=
  match cur_ddict cur with
  | Some q0 => if Val.eq (fst e) q0 then emp else ddict_res (DD3x DENT) gv Ews (fst e) (snd e)
  | None => ddict_res (DD3x DENT) gv Ews (fst e) (snd e)
  end.

Lemma set_res_split : forall gv l1 q dd l2 cur, (forall p, dd_ref dd = Some p -> isptr p) ->
  set_f gv cur (q, dd) = ddict_res (DD3x DENT) gv Ews q dd ->
  set_res (DD3x DENT) gv Ews (l1 ++ (q, dd) :: l2) cur =
  dd_lend gv (Some (dd_x q dd, dd_buf dd)) *
  (dd_rest (dd_x q dd) (dd_buf dd) * fold_right sepcon emp (map (set_f gv cur) l1) *
   fold_right sepcon emp (map (set_f gv cur) l2)).
Proof.
intros gv l1 q dd l2 cur Hptr Hf. unfold set_res. fold (set_f gv cur). rewrite fold_sep_split, Hf, res_split by exact Hptr.
apply pred_ext; cancel.
Qed.

(* the member's pointer fact, from the set's memory *)
Lemma set_res_ref_ptr : forall gv l1 q dd l2 cur,
  set_f gv cur (q, dd) = ddict_res (DD3x DENT) gv Ews q dd ->
  set_res (DD3x DENT) gv Ews (l1 ++ (q, dd) :: l2) cur |-- !! (forall p, dd_ref dd = Some p -> isptr p).
Proof.
intros gv l1 q dd l2 cur Hf. unfold set_res. fold (set_f gv cur). rewrite fold_sep_split, Hf.
sep_apply (ddict_res_ref_ptr gv q dd). entailer!.
Qed.

Lemma dd_borrow_caller : forall gv p st d W q dd,
  dd_caller st q dd -> stream_dict_ok W st -> set_cur_ok st ->
  dd_all gv p st d |--
    !! dd_facts W (Some (dd_x q dd, dd_buf dd)) &&
    (dd_lend gv (Some (dd_x q dd, dd_buf dd)) * (dd_lend gv (Some (dd_x q dd, dd_buf dd)) -* dd_all gv p st d)).
Proof.
intros gv p st d W q dd Hc Hsd Hcur.
unfold stream_dict_ok in Hsd. destruct Hsd as (Hsd1 & Hsd2 & _).
assert (Hdict: forall dr, dc_dict st = Some dr -> dr_src dr = DSDDict q dd ->
          dd_all gv p st d |--
          !! dd_facts W (Some (dd_x q dd, dd_buf dd)) &&
          (dd_lend gv (Some (dd_x q dd, dd_buf dd)) * (dd_lend gv (Some (dd_x q dd, dd_buf dd)) -* dd_all gv p st d))).
{ intros dr Hd Hs. rewrite Hd, Hs in Hsd1. destruct Hsd1 as [_ Hsd1].
  apply (derives_trans _ (!! (forall p0, dd_ref dd = Some p0 -> isptr p0) && dd_all gv p st d));
    [apply andp_right; [|apply derives_refl] |].
  { unfold dd_all, dict_res. rewrite Hd, Hs. sep_apply (ddict_res_ref_ptr gv q dd). entailer!. }
  apply derives_extract_prop. intros Hptr.
  assert (E: dict_res (DD3x DENT) gv Ews (dc_dict st) =
             dd_lend gv (Some (dd_x q dd, dd_buf dd)) * dd_rest (dd_x q dd) (dd_buf dd))
    by (unfold dict_res; rewrite Hd, Hs; apply res_split; exact Hptr).
  apply andp_right.
  - unfold dd_all. rewrite E. sep_apply (dd_rest_facts (dd_x q dd) (dd_buf dd)). Intros. apply prop_right.
    apply sddict_facts; auto.
  - apply (lend_wand _ _ (dd_rest (dd_x q dd) (dd_buf dd) * dgroup DENT gv p d *
                          set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))).
    + unfold dd_all. rewrite E. cancel.
    + unfold dd_all. rewrite E. cancel. }
assert (Hset: set_f gv (dc_dict st) (q, dd) = ddict_res (DD3x DENT) gv Ews q dd -> In (q, dd) (dc_set st) ->
          dd_all gv p st d |--
          !! dd_facts W (Some (dd_x q dd, dd_buf dd)) &&
          (dd_lend gv (Some (dd_x q dd, dd_buf dd)) * (dd_lend gv (Some (dd_x q dd, dd_buf dd)) -* dd_all gv p st d))).
{ intros Hf Hin. rewrite Forall_forall in Hsd2. specialize (Hsd2 _ Hin). cbn [snd] in Hsd2.
  destruct (in_split _ _ Hin) as (l1 & l2 & El).
  apply (derives_trans _ (!! (forall p0, dd_ref dd = Some p0 -> isptr p0) && dd_all gv p st d));
    [apply andp_right; [|apply derives_refl] |].
  { unfold dd_all. rewrite El. sep_apply (set_res_ref_ptr gv l1 q dd l2 (dc_dict st) Hf). entailer!. }
  apply derives_extract_prop. intros Hptr.
  pose proof (set_res_split gv l1 q dd l2 (dc_dict st) Hptr Hf) as E. rewrite <- El in E.
  apply andp_right.
  - unfold dd_all. rewrite E. sep_apply (dd_rest_facts (dd_x q dd) (dd_buf dd)). Intros. apply prop_right.
    apply sddict_facts; auto.
  - apply (lend_wand _ _ (dd_rest (dd_x q dd) (dd_buf dd) *
                          fold_right sepcon emp (map (set_f gv (dc_dict st)) l1) *
                          fold_right sepcon emp (map (set_f gv (dc_dict st)) l2) *
                          dgroup DENT gv p d * dict_res (DD3x DENT) gv Ews (dc_dict st))).
    + unfold dd_all. rewrite E. cancel.
    + unfold dd_all. rewrite E. cancel. }
destruct Hc as [Hin|(dr&Hd&Hs)]; [|exact (Hdict dr Hd Hs)].
destruct (dc_dict st) as [dr|] eqn:Hd.
2:{ apply Hset; [reflexivity|exact Hin]. }
destruct (dr_src dr) as [pk| |q' dd'] eqn:Hs.
3:{ destruct (Val.eq q q') as [<-|Hne].
    - assert (dd = dd') by (exact (Hcur dr q dd' dd Hd Hs Hin)). subst dd'.
      apply (Hdict dr); auto.
    - apply Hset; [|exact Hin]. unfold set_f. cbn [cur_ddict fst snd]. rewrite Hs.
      destruct (Val.eq q q'); [contradiction|reflexivity]. }
all: apply Hset; [unfold set_f; cbn [cur_ddict fst snd]; rewrite Hs; reflexivity|exact Hin].
Qed.

Definition dgroup_fields (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p.

(* the context's local DDict (zstd's copy) *)
Lemma dd_borrow_local : forall gv p st d W x buf,
  df_local d = dx_q x -> df_lx d = Some (x, buf) -> dx_q x <> nullval -> ddx_copied x = true ->
  dd_all gv p st d |--
    !! dd_facts W (Some (x, buf)) && (dd_lend gv (Some (x, buf)) * (dd_lend gv (Some (x, buf)) -* dd_all gv p st d)).
Proof.
intros gv p st d W x buf Hl Hx Hn Hc.
assert (E: local_rep DENT gv (df_local d) (df_lx d) = dd_lend gv (Some (x, buf)) * dd_rest x buf).
{ unfold local_rep. rewrite Hl, Hx. rewrite if_false by auto. rewrite <- rep_split_copied by auto.
  apply pred_ext; [Intros; apply derives_refl | entailer!]. }
apply andp_right.
- unfold dd_all, dgroup. rewrite E. sep_apply (dd_rest_facts x buf). Intros. apply prop_right.
  match goal with H: dd_facts0 _ _ |- _ => destruct H as (H1&H2&H3&H4&H5&H6&_) end.
  unfold dd_facts. repeat (split; [assumption|]). split; [left; exact Hc|]. auto.
- apply (lend_wand _ _ (dd_rest x buf * dgroup_fields p d *
                        dict_res (DD3x DENT) gv Ews (dc_dict st) *
                        set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))).
  + unfold dd_all, dgroup, dgroup_fields. rewrite E. cancel.
  + unfold dd_all, dgroup, dgroup_fields. rewrite E. cancel.
Qed.

(* the frame's DDict (the read-stage view's sv_dd) *)
Lemma dd_borrow : forall gv p st k W dd,
  (forall x buf, dd = Some (x, buf) -> dd_src st k x buf) ->
  stream_dict_ok W st -> set_cur_ok st ->
  dd_all gv p st (c3_dict k) |--
    !! dd_facts W dd && (dd_lend gv dd * (dd_lend gv dd -* dd_all gv p st (c3_dict k))).
Proof.
intros gv p st k W dd Hdd Hsd Hcur.
destruct dd as [[x buf]|].
2:{ apply andp_right; [apply prop_right; exact I|]. unfold dd_lend. rewrite emp_sepcon.
    rewrite <- wand_sepcon_adjoint. rewrite sepcon_emp. apply derives_refl. }
pose proof (Hdd x buf eq_refl) as Hs.
destruct Hs as [(Hl & Hn & Hc & Hx)|(dd & Hc & Ex & Eb)].
- apply dd_borrow_local; auto.
- rewrite Eb. rewrite Ex. apply dd_borrow_caller; auto.
Qed.

(* the layout refers to the DDict's content (lay_res) or not; the rest of what the DDict lends *)
Definition lay_has_dict (l: hlay) : bool :=
  match l with
  | HL_dict _ _ _ => true
  | HL_stuck _ _ (Some _) => true
  | HL_seg _ _ _ (ExtSep _ _ _ _ _ _) => true
  | _ => false
  end.

Definition lay_rest (l: hlay) (dd: option (ddx * val)) : mpred :=
  match dd with
  | Some (x, buf) => if lay_has_dict l then emp else dd_bytes_res x buf
  | None => emp
  end.

Lemma lend_lay : forall gv l dd, lay_dd l dd ->
  dd_lend gv dd = dent_of DENT gv (dd_ox dd) * lay_res l * lay_rest l dd.
Proof.
intros gv l dd H.
destruct dd as [[x buf]|].
- unfold dd_lend, lay_rest, dent_of, dd_ox. cbn [option_map fst].
  destruct l as [|eb ec gp|b pe [[[eb ec] gp]|]|b ps pe [|e1 elen|sh eb en ec e1 elen]]; cbn [lay_has_dict lay_res ext_res];
    unfold lay_dd, dd_pre in H; try (apply pred_ext; cancel; fail).
  + destruct H as (x' & E & -> & _ & _ & _ & Hp). inversion E; subst. unfold dd_bytes_res.
    rewrite bytes_at_ptr by exact Hp. rewrite Zlength_map. apply pred_ext; cancel.
  + destruct H as (x' & E & -> & _ & _ & _ & Hp). inversion E; subst. unfold dd_bytes_res.
    rewrite bytes_at_ptr by exact Hp. rewrite Zlength_map. apply pred_ext; cancel.
  + destruct H as (-> & -> & -> & -> & gp & x' & E & -> & _ & _ & _ & Hp). inversion E; subst. unfold dd_bytes_res.
    rewrite bytes_at_ptr by exact Hp. rewrite Zlength_map. apply pred_ext; cancel.
- unfold dd_lend, lay_rest, dent_of, dd_ox. cbn [option_map].
  destruct l as [|eb ec gp|b pe [[[eb ec] gp]|]|b ps pe [|e1 elen|sh eb en ec e1 elen]]; cbn [lay_res ext_res];
    unfold lay_dd, dd_pre in H; try (destruct H as (x' & E & _); discriminate E);
    try (destruct H as (_&_&_&_&gp&x'&E&_); discriminate E);
    apply pred_ext; cancel.
Qed.

(* the layout's witnesses (StreamSpecs lay_wit) from the DDict's facts *)
Lemma lay_wit_of : forall W l dd, lay_dd l dd -> dd_facts W dd -> lay_wit W l.
Proof.
intros W l dd H Hf.
destruct l as [|eb ec gp|b pe [[[eb ec] gp]|]|b ps pe [|e1 elen|sh eb en ec e1 elen]]; cbn [lay_wit]; auto;
  unfold lay_dd, dd_pre in H.
- destruct H as (x & -> & -> & -> & _ & _). unfold dd_facts in Hf.
  destruct Hf as (Hb & Hl & Hp & Hc0 & Hc & _). unfold pre_ok. rewrite Zlength_map. split; [lia|].
  destruct (ddx_copied x); [left; reflexivity|]. right. destruct Hc as [Hc|[Hn Hv]]; [discriminate|].
  rewrite Hn. auto.
- destruct H as (x & -> & -> & -> & _ & _). unfold dd_facts in Hf.
  destruct Hf as (Hb & Hl & Hp & Hc0 & Hc & _). unfold pre_ok. rewrite Zlength_map. split; [lia|].
  destruct (ddx_copied x); [left; reflexivity|]. right. destruct Hc as [Hc|[Hn Hv]]; [discriminate|].
  rewrite Hn. auto.
- destruct H as (-> & -> & -> & -> & gp & x & -> & -> & _ & _ & _). unfold dd_facts in Hf.
  destruct Hf as (Hb & Hl & Hp & Hc0 & Hc & _). rewrite Zlength_map. split; [lia|].
  intros H0. destruct Hc as [Hc|[Hn Hv]]; [|exact Hv]. specialize (Hc0 Hc). lia.
Qed.

End Borrow.

End CM_R3Borrow_1.
