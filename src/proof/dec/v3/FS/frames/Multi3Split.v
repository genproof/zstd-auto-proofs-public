(* FS3 one-shot frames, ZSTD_decompressMultiFrame: the resources of one frame (Begin, decompressFrame, back) *)
Require Export Zstd.proof.dec.v3.FS.frames.Multi3Res.
Local Open Scope logic.

Section CM_Multi3Split_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* ---------- a DDict struct, split: the fields the selection reads (dictBuffer, dictID) ---------- *)

Definition ds_facts (x: ddx) (buf: val) : Prop :=
  isptr (dx_q x) /\ Zlength (dx_bytes x) <= 2 ^ 63 - 1 /\ bytes_ok (dx_bytes x) /\
  ld_rel (dx_bytes x) (dx_ld x) /\ (dx_raw x = true \/ dict_auto_c (dx_bytes x) (dx_ld x) <> None) /\
  (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)) /\
  (ddx_copied x = true -> 0 < Zlength (dx_bytes x)) /\
  (match dx_ref x with Some p => buf = p | None => True end) /\ cmem_ok (dx_mem x).

Definition ds_dbv (x: ddx) (buf: val) : val := if ddx_copied x then buf else nullval.

(* the struct without dictBuffer *)
Definition ds_nobuf (x: ddx) (buf: val) : mpred :=
  !! ds_facts x buf &&
  (field_at Ews t_ddict (DOT _dictContent) buf (dx_q x) *
   field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength (dx_bytes x)))) (dx_q x) *
   field_at Ews t_ddict (DOT _dictID) (Vint (Int.repr (if dx_raw x then 0 else dict_id_of (dx_bytes x)))) (dx_q x) *
   field_at Ews t_ddict (DOT _entropyPresent)
     (Vint (Int.repr (match ddx_ent x with Some _ => 1 | None => 0 end))) (dx_q x) *
   field_at Ews t_ddict (DOT _cMem) (cmem_v (dx_mem x)) (dx_q x)).

(* the struct without dictBuffer and dictID *)
Definition ds_noid (x: ddx) (buf: val) : mpred :=
  !! ds_facts x buf &&
  (field_at Ews t_ddict (DOT _dictContent) buf (dx_q x) *
   field_at Ews t_ddict (DOT _dictSize) (Vlong (Int64.repr (Zlength (dx_bytes x)))) (dx_q x) *
   field_at Ews t_ddict (DOT _entropyPresent)
     (Vint (Int.repr (match ddx_ent x with Some _ => 1 | None => 0 end))) (dx_q x) *
   field_at Ews t_ddict (DOT _cMem) (cmem_v (dx_mem x)) (dx_q x)).

Lemma ddict_struct_buf: forall x buf,
  ddict_struct x buf = field_at Ews t_ddict (DOT _dictBuffer) (ds_dbv x buf) (dx_q x) * ds_nobuf x buf.
Proof.
  intros. unfold ddict_struct, ds_nobuf, ds_dbv, ds_facts, t_ddict. apply pred_ext; Intros; entailer!.
Qed.

Lemma ddict_struct_id: forall x buf, dx_raw x = false ->
  ddict_struct x buf = ddid (dx_q x) (dict_id_of (dx_bytes x)) (ds_dbv x buf) * ds_noid x buf.
Proof.
  intros x buf Hr. unfold ddict_struct, ds_noid, ds_dbv, ds_facts, ddid, t_ddict. rewrite Hr.
  apply pred_ext; Intros.
  - pose proof (dict_id_of_range (dx_bytes x)). entailer!. 
  - entailer!.
Qed.

Lemma ddict_struct_vp: forall x buf, ddict_struct x buf |-- valid_pointer (dx_q x).
Proof.
  intros. rewrite ddict_struct_buf. eapply derives_trans; [apply sepcon_derives; [apply field_at_valid_ptr0 | apply derives_refl] |].
  - apply readable_nonidentity, writable_readable, writable_Ews.
  - simpl. lia.
  - reflexivity.
  - apply sepcon_valid_pointer1. apply derives_refl.
Qed.

(* ---------- folds over the set ---------- *)

Lemma fold_sep_app: forall (A: list mpred) B,
  fold_right sepcon emp (A ++ B) = fold_right sepcon emp A * fold_right sepcon emp B.
Proof.
  induction A; intros; simpl. rewrite emp_sepcon; auto. rewrite IHA, sepcon_assoc; auto.
Qed.

Lemma fold_skip_notin: forall (F: val * ddict_st -> mpred) l q,
  ~ In q (map fst l) ->
  fold_right sepcon emp (map (fun e => if Val.eq (fst e) q then emp else F e) l) = fold_right sepcon emp (map F l).
Proof.
  induction l as [| e l IH]; intros q Hn; simpl; auto.
  simpl in Hn. destruct (Val.eq (fst e) q). { exfalso; apply Hn; auto. }
  rewrite IH; auto.
Qed.

(* one DDict out of a fold (the IDs of the set are distinct pointers) *)
Lemma fold_pick: forall (F: val * ddict_st -> mpred) l e,
  NoDup (map fst l) -> In e l ->
  fold_right sepcon emp (map F l) =
  F e * fold_right sepcon emp (map (fun e' => if Val.eq (fst e') (fst e) then emp else F e') l).
Proof.
  induction l as [| e0 l IH]; intros e Hd Hin; [contradiction |]. simpl in Hd |- *. inv Hd.
  destruct Hin as [<- | Hin].
  - destruct (Val.eq (fst e0) (fst e0)); [| congruence]. rewrite emp_sepcon, fold_skip_notin; auto.
  - destruct (Val.eq (fst e0) (fst e)) as [E | Ne].
    + exfalso. apply H1. rewrite E. apply in_map; auto.
    + rewrite (IH e); auto. rewrite <- !sepcon_assoc, (sepcon_comm (F e0)). auto.
Qed.

Section SP.
Variable DENT : dent_pred.

Definition refb (shk: share) (dd: ddict_st) : mpred :=
  match dd_ref dd with
  | Some p => data_at shk (tarray tuchar (Zlength (dd_bytes dd))) (zbytes (dd_bytes dd)) p
  | None => emp
  end.

Lemma ddict_rep_at_vp: forall gv x buf, ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  intros. unfold ddict_rep_at. rewrite !sepcon_assoc. apply sepcon_valid_pointer1. apply ddict_struct_vp.
Qed.

Lemma ddict_res_eq: forall gv shk X dd,
  ddict_res (DD3_of DENT) gv shk X dd = DD3_of DENT gv X dd * refb shk dd.
Proof.
  intros. unfold ddict_res, refb. f_equal. apply pred_ext.
  - apply andp_left1, derives_refl.
  - apply andp_right; auto. unfold DD3_of. apply (ddict_rep_at_vp gv (dd_x X dd)).
Qed.

Lemma DD3_begin: forall gv shk X dd,
  DD3_of DENT gv X dd = begin_res DENT gv (DA_ddict (dd_x X dd) (dd_buf dd) shk) * ddict_pad X.
Proof. intros. unfold DD3_of, ddict_rep_at, begin_res. reflexivity. Qed.

Lemma ds_dbv_dd: forall X dd, ds_dbv (dd_x X dd) (dd_buf dd) = ddb dd.
Proof. intros. unfold ds_dbv, ddb, ddx_copied, dd_x. simpl. destruct (dd_xref dd); auto. Qed.

(* a DDict of the set without its ID fields *)
Definition mrest (gv: globals) (shk: share) (e: val * ddict_st) : mpred :=
  ds_noid (dd_x (fst e) (snd e)) (dd_buf (snd e)) * DENT gv (fst e) (ddx_ent (dd_x (fst e) (snd e))) *
  ddict_mem (dd_x (fst e) (snd e)) (dd_buf (snd e)) * ddict_pad (fst e) * refb shk (snd e).

Lemma member_split: forall gv shk X dd,
  ddict_res (DD3_of DENT) gv shk X dd = ddid X (dd_id dd) (ddb dd) * mrest gv shk (X, dd).
Proof.
  intros. rewrite ddict_res_eq. unfold DD3_of, ddict_rep_at, mrest. simpl fst; simpl snd.
  rewrite ddict_struct_id by reflexivity. rewrite ds_dbv_dd. unfold dd_id. simpl dx_q. simpl dx_bytes.
  apply pred_ext; cancel.
Qed.

Definition set_ids_ne (l: list (val * ddict_st)) (q0: val) : mpred :=
  fold_right sepcon emp (map (fun e => if Val.eq (fst e) q0 then emp else ddid (fst e) (dd_id (snd e)) (ddb (snd e))) l).

Definition set_rest_ne (gv: globals) (shk: share) (l: list (val * ddict_st)) (q0: val) : mpred :=
  fold_right sepcon emp (map (fun e => if Val.eq (fst e) q0 then emp else mrest gv shk e) l).

Lemma set_full_split: forall gv shk l q0,
  set_full DENT gv shk l q0 = set_ids_ne l q0 * set_rest_ne gv shk l q0.
Proof.
  intros. unfold set_full, set_ids_ne, set_rest_ne. induction l as [| e l IH]; simpl.
  - rewrite emp_sepcon; auto.
  - rewrite IH. destruct (Val.eq (fst e) q0).
    + rewrite !emp_sepcon; auto.
    + destruct e as [X dd]. rewrite member_split. simpl. apply pred_ext; cancel.
Qed.

Lemma set_ids_ne_notin: forall l q0, ~ In q0 (map fst l) -> set_ids_ne l q0 = set_ids l.
Proof.
  intros. unfold set_ids_ne, set_ids.
  apply (fold_skip_notin (fun e => ddid (fst e) (dd_id (snd e)) (ddb (snd e)))); auto.
Qed.

Lemma set_ids_ne_in: forall l q0 dd, NoDup (map fst l) -> In (q0, dd) l ->
  set_ids l = ddid q0 (dd_id dd) (ddb dd) * set_ids_ne l q0.
Proof.
  intros. unfold set_ids_ne, set_ids.
  rewrite (fold_pick (fun e => ddid (fst e) (dd_id (snd e)) (ddb (snd e))) l (q0, dd)); auto.
Qed.

End SP.

(* ---------- the argument's resources, split ---------- *)

Section ARG.
Variable DENT : dent_pred.
Variable gv : globals.

(* darg_res besides what Begin takes *)
Definition begin_rest (a: darg) : mpred :=
  match a with
  | DA_ddict x buf sh =>
      ddict_pad (dx_q x) *
      (if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf)
  | _ => emp
  end.

Lemma darg_res_begin: forall a, darg_res DENT gv a = begin_res DENT gv a * begin_rest a.
Proof.
  intros [| sh pk b | x buf sh]; simpl; rewrite ?sepcon_emp; auto.
  unfold ddict_rep_at. apply pred_ext; cancel.
Qed.

Definition dobj_rest (x: ddx) (buf: val) : mpred :=
  blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
  (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp) *
  ddict_pad (dx_q x).

Definition dbuf_fld (x: ddx) (buf: val) : mpred :=
  field_at Ews t_ddict (DOT _dictBuffer) (ds_dbv x buf) (dx_q x).

(* the part of a non-local argument the selection reads: the ID fields of a set member, the dictBuffer field
   of another DDict (lent as opt_token) *)
Lemma ap_split: forall (l: list (val * ddict_st)) a,
  NoDup (map fst l) -> Forall (fun e => isptr (fst e)) l ->
  (forall x buf sh dd, a = DA_ddict x buf sh -> In (dx_q x, dd) l -> x = dd_x (dx_q x) dd /\ buf = dd_buf dd) ->
  exists xq AP AR2,
    (darg_ddict a = nullval \/ In (darg_ddict a) (map fst l) \/ exists v, xq = Some (darg_ddict a, v)) /\
    set_ids l * opt_token xq = set_ids_ne l (darg_ddict a) * AP /\
    forall dm, darg_res DENT gv a = AP * (dent_of DENT gv (darg_ox a) * ext_res (ext_of a dm) * AR2).
Proof.
  intros l a Hd Hp Hst.
  assert (Hnull: ~ In nullval (map fst l)).
  { intros Hin. apply in_map_iff in Hin. destruct Hin as [e [E Hin]].
    rewrite Forall_forall in Hp. specialize (Hp e Hin). rewrite E in Hp. exact Hp. }
  destruct a as [| sh pk b | x buf sh].
  - exists None, emp, emp. split; [left; reflexivity |]. split.
    + simpl. rewrite set_ids_ne_notin by auto. rewrite !sepcon_emp. auto.
    + intros. simpl. rewrite !emp_sepcon. auto.
  - exists None, emp, (darg_rest (DA_dict sh pk b)). split; [left; reflexivity |]. split.
    + simpl. rewrite set_ids_ne_notin by auto. rewrite !sepcon_emp. auto.
    + intros dm. rewrite emp_sepcon. apply darg_res_split.
  - destruct (in_dec Val.eq (dx_q x) (map fst l)) as [Hin | Hn].
    + pose proof Hin as Hin0. apply in_map_iff in Hin. destruct Hin as [[q dd] [Eq Hin]]. simpl in Eq. subst q.
      destruct (Hst x buf sh dd eq_refl Hin) as [Ex Eb].
      exists None, (ddid (dx_q x) (dd_id dd) (ddb dd)), (ds_noid x buf * dobj_rest x buf).
      split; [right; left; exact Hin0 |]. split.
      * simpl opt_token. rewrite sepcon_emp, sepcon_comm. apply set_ids_ne_in; auto.
      * intros dm. rewrite (darg_res_split DENT gv _ dm). simpl darg_rest. rewrite ddict_struct_id.
        2: rewrite Ex; reflexivity.
        replace (dict_id_of (dx_bytes x)) with (dd_id dd) by (rewrite Ex; reflexivity).
        replace (ds_dbv x buf) with (ddb dd) by (rewrite Ex, Eb; symmetry; apply ds_dbv_dd).
        unfold dobj_rest. simpl. apply pred_ext; cancel.
    + exists (Some (dx_q x, ds_dbv x buf)), (dbuf_fld x buf),
        (ds_nobuf x buf * dobj_rest x buf).
      split; [right; right; eexists; reflexivity |]. split.
      * simpl. rewrite set_ids_ne_notin by auto. auto.
      * intros dm. rewrite (darg_res_split DENT gv _ dm). simpl darg_rest. rewrite ddict_struct_buf.
        unfold dobj_rest, dbuf_fld. simpl. apply pred_ext; cancel.
Qed.

End ARG.

Lemma veqb_true: forall a b, veqb a b = true -> a = b.
Proof. unfold veqb; intros a b H. destruct (Val.eq a b); auto; discriminate. Qed.

Lemma veqb_refl: forall a, veqb a a = true.
Proof. unfold veqb; intros. destruct (Val.eq a a); auto. Qed.

(* ---------- without `lent`: the selection's part and the dictionary's part ---------- *)

Section NL.
Variable DENT : dent_pred.
Variable gv : globals.

Definition sx (pr: dparams) (sp: val) (l: list (val * ddict_st)) (xq: option (val * val)) : mpred :=
  if sel_on pr sp then set_ids l * opt_token xq else emp.

Definition sfo (pr: dparams) (sp: val) (shk: share) (l: list (val * ddict_st)) (q0: val) : mpred :=
  if sel_on pr sp then set_full DENT gv shk l q0 else emp.

Definition gd (p: val) (pr: dparams) (sp: val) (d: dfields) (l: list (val * ddict_st)) (tbl: list val)
    (am: option cmem) (hb: Z) : mpred :=
  if sel_on pr sp then mem_mgr gv * dgroup DENT gv p d * cm_have am (hb + local_held d) * hset_tbl am sp l tbl
  else emp.

Lemma msel_gd: forall p pr sp d l tbl shk a am hb,
  msel_res DENT gv p pr sp d l tbl shk a am hb = gd p pr sp d l tbl am hb * sfo pr sp shk l (darg_ddict a).
Proof.
  intros. unfold msel_res, gd, sfo. destruct (sel_on pr sp); [auto | rewrite emp_sepcon; auto].
Qed.

Lemma fsel_gd: forall p pr sp d l tbl xq am hb ox,
  mf_fsel DENT gv p pr sp d l tbl xq false am hb ox = gd p pr sp d l tbl am hb * sx pr sp l xq * dent_of DENT gv ox.
Proof.
  intros. unfold mf_fsel, sel_any, sel_res, gd, sx. destruct (sel_on pr sp).
  - rewrite <- !sepcon_assoc. auto.
  - rewrite !emp_sepcon; auto.
Qed.

(* the dictionary's part: R0 (the set's DDicts and the argument's memory) is Begin's and the frame's *)
Definition nl_ok (pr: dparams) (sp: val) (l: list (val * ddict_st)) (xq: option (val * val)) (R0: mpred)
    (a': darg) (W: list ptr_witness) (shd: share) (cap: Z) (dst: val) : Prop :=
  exists MKd MK2d: mpred,
    R0 = begin_res DENT gv a' * MKd /\
    (R0 |-- !! (darg_wf a' /\ darg_ok3 W a' shd cap dst)) /\
    forall dm, R0 = sx pr sp l xq * dent_of DENT gv (darg_ox a') * ext_res (ext_of a' dm) * MK2d.

Lemma nl_main: forall p pr sp d dcur l tbl shk a a' W shd cap dst xq am hb,
  nl_ok pr sp l xq (sfo pr sp shk l (darg_ddict a) * darg_res3 DENT gv pr sp d a) a' W shd cap dst ->
  exists MK MK2: mpred,
    (msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a |-- begin_res DENT gv a' * MK) /\
    (begin_res DENT gv a' * MK |-- !! (darg_wf a' /\ darg_ok3 W a' shd cap dst)) /\
    (begin_res DENT gv a' * MK |-- msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a) /\
    (forall dm, begin_res DENT gv a' * MK |--
       mf_fsel DENT gv p pr sp dcur l tbl xq false am hb (darg_ox a') * ext_res (ext_of a' dm) * MK2) /\
    (forall dm dcur', mf_fsel DENT gv p pr sp dcur' l tbl xq false am hb (darg_ox a') * ext_res (ext_of a' dm) * MK2 |--
       msel_res DENT gv p pr sp dcur' l tbl shk a am hb * darg_res3 DENT gv pr sp d a).
Proof.
  intros until hb. intros (MKd & MK2d & E1 & Hw & E2).
  set (R0 := sfo pr sp shk l (darg_ddict a) * darg_res3 DENT gv pr sp d a) in *.
  assert (EB: begin_res DENT gv a' * (gd p pr sp dcur l tbl am hb * MKd) = gd p pr sp dcur l tbl am hb * R0).
  { rewrite E1. apply pred_ext; cancel. }
  assert (EM: forall dc, msel_res DENT gv p pr sp dc l tbl shk a am hb * darg_res3 DENT gv pr sp d a = gd p pr sp dc l tbl am hb * R0).
  { intros. rewrite msel_gd. unfold R0. rewrite sepcon_assoc. auto. }
  exists (gd p pr sp dcur l tbl am hb * MKd), MK2d. split; [| split; [| split; [| split]]].
  - rewrite EM, EB. auto.
  - rewrite EB. eapply derives_trans; [apply sepcon_derives; [apply TT_right | apply Hw] |].
    rewrite sepcon_comm, prop_sepcon. apply andp_left1, derives_refl.
  - rewrite EM, EB. auto.
  - intros dm. rewrite EB, (E2 dm), fsel_gd. apply derives_refl'. apply pred_ext; cancel.
  - intros dm dcur'. rewrite EM, (E2 dm), fsel_gd. apply derives_refl'. apply pred_ext; cancel.
Qed.

End NL.

Section NLC.
Variable DENT : dent_pred.
Variable gv : globals.

(* the selection off: the argument itself *)
Lemma nl_A: forall pr sp l a W shd cap dst,
  sel_on pr sp = false -> darg_ok3 W a shd cap dst ->
  nl_ok DENT gv pr sp l None (darg_res DENT gv a) a W shd cap dst.
Proof.
  intros pr sp l a W shd cap dst Hs Hok. exists (begin_rest a), (darg_rest a). split; [| split].
  - apply darg_res_begin.
  - eapply derives_trans; [eapply darg_wf_res; eauto |]. apply prop_derives; auto.
  - intros dm. unfold sx. rewrite Hs, emp_sepcon. apply darg_res_split.
Qed.

(* the selection on, the argument (not the local DDict) *)
Lemma nl_B: forall pr sp l shk a W shd cap dst,
  sel_on pr sp = true -> NoDup (map fst l) -> Forall (fun e => isptr (fst e)) l ->
  (forall x buf sh dd, a = DA_ddict x buf sh -> In (dx_q x, dd) l -> x = dd_x (dx_q x) dd /\ buf = dd_buf dd) ->
  darg_ok3 W a shd cap dst ->
  exists xq,
    (darg_ddict a = nullval \/ In (darg_ddict a) (map fst l) \/ exists v, xq = Some (darg_ddict a, v)) /\
    nl_ok DENT gv pr sp l xq (set_full DENT gv shk l (darg_ddict a) * darg_res DENT gv a) a W shd cap dst.
Proof.
  intros pr sp l shk a W shd cap dst Hs Hd Hp Hst Hok.
  destruct (ap_split DENT gv l a Hd Hp Hst) as (xq & AP & AR2 & Hx & Hsx & Hr).
  exists xq. split; auto.
  exists (set_full DENT gv shk l (darg_ddict a) * begin_rest a), (set_rest_ne DENT gv shk l (darg_ddict a) * AR2).
  split; [| split].
  - rewrite darg_res_begin. apply pred_ext; cancel.
  - sep_apply (darg_wf_res DENT gv W a shd cap dst Hok). entailer!.
  - intros dm. unfold sx. rewrite Hs. rewrite set_full_split, (Hr dm), Hsx. apply pred_ext; cancel.
Qed.

(* a set member of a frame (not the argument); the caller's bytes of a DDict by reference are at a pointer (as
   their data_at in ddict_res says) *)
Lemma mrest_split: forall shk X dd dm,
  (match dd_ref dd with Some p => isptr p | None => True end) ->
  mrest DENT gv shk (X, dd) =
  DENT gv X (ddx_ent (dd_x X dd)) * ext_res (ext_of (DA_ddict (dd_x X dd) (dd_buf dd) shk) dm) *
  (ds_noid (dd_x X dd) (dd_buf dd) * dobj_rest (dd_x X dd) (dd_buf dd)).
Proof.
  intros shk X dd dm Hrp. unfold mrest, ext_of, ext_res, ddict_mem, dobj_rest, refb. simpl fst; simpl snd.
  unfold ds_noid, ds_facts, ddx_copied. simpl dx_ref. simpl dx_bytes. simpl dx_q.
  destruct (dd_xref_cases dd) as [(pp & E & Ex) | [(E & Ene & Ex) | (E & Enil & Ex)]];
    rewrite Ex; rewrite E in *.
  - apply pred_ext; Intros; subst; destruct (dd_buf dd); try contradiction; entailer!.
  - apply pred_ext; Intros;
      match goal with H: isptr (dd_buf dd) \/ _ |- _ =>
        destruct H as [H | (_ & H & _)]; [| discriminate] end;
      destruct (dd_buf dd); try contradiction; entailer!.
  - apply pred_ext; Intros;
      match goal with H: dd_buf dd = nullval |- _ => rewrite H end; simpl; entailer!.
Qed.

Lemma begin_wf_D: forall shk X dd W shd cap dst,
  readable_share shk -> ddict_buf_ok0 W shk dd shd cap dst ->
  begin_res DENT gv (DA_ddict (dd_x X dd) (dd_buf dd) shk) * refb shk dd |--
  !! (darg_wf (DA_ddict (dd_x X dd) (dd_buf dd) shk) /\ darg_ok3 W (DA_ddict (dd_x X dd) (dd_buf dd) shk) shd cap dst).
Proof.
  intros shk X dd W shd cap dst Hsh Hb. unfold begin_res, ddict_struct, ddict_mem, refb, ddx_copied.
  unfold ddict_buf_ok0 in Hb. simpl dx_ref. simpl dx_bytes. simpl dx_q. simpl dx_raw. simpl dx_ld.
  destruct (dd_xref_cases dd) as [(pp & E & Ex) | [(E & Ene & Ex) | (E & Enil & Ex)]];
    rewrite Ex; rewrite E in *; Intros.
  - (* by reference *)
    subst pp. entailer!.
    destruct (fc_bound (Zlength (dd_bytes dd)) (dd_buf dd)) as (bk & o & Eo & Ho); auto; [rep_lia |].
    simpl. unfold ddx_copied. simpl dx_ref. rewrite Ex. split; [| intros _ _; auto].
    repeat split; auto; try rep_lia; try (intros; discriminate);
      try (match goal with Hd: false = true \/ _ |- _ => destruct Hd as [Hd | Hd]; [discriminate | auto] end).
    left; eauto.
  - (* zstd's copy *)
    entailer!.
    destruct (fc_bound (Zlength (dd_bytes dd)) (dd_buf dd)) as (bk & o & Eo & Ho); auto; [rep_lia |].
    simpl. unfold ddx_copied. simpl dx_ref. rewrite Ex. split; [| intros; discriminate].
    repeat split; auto; try rep_lia; try (intros; discriminate);
      try (match goal with Hd: false = true \/ _ |- _ => destruct Hd as [Hd | Hd]; [discriminate | auto] end).
    left; eauto.
  - (* no content *)
    entailer!.
    simpl. unfold ddx_copied. simpl dx_ref. rewrite Ex.
    repeat split; auto; try (intros; discriminate); try (intros; congruence);
      try (match goal with Hd: false = true \/ _ |- _ => destruct Hd as [Hd | Hd]; [discriminate | auto] end).
Qed.

Lemma nl_D: forall pr sp l shk q0 X dd xq AP AR' D3 W shd cap dst,
  sel_on pr sp = true -> NoDup (map fst l) -> In (X, dd) l -> X <> q0 ->
  readable_share shk -> ddict_buf_ok0 W shk dd shd cap dst ->
  set_ids l * opt_token xq = set_ids_ne l q0 * AP -> D3 = AP * AR' ->
  nl_ok DENT gv pr sp l xq (set_full DENT gv shk l q0 * D3) (DA_ddict (dd_x X dd) (dd_buf dd) shk) W shd cap dst.
Proof.
  intros pr sp l shk q0 X dd xq AP AR' D3 W shd cap dst Hs Hd Hin Hne Hsh Hb Hsx HD.
  set (F := fun e: val * ddict_st => if Val.eq (fst e) q0 then emp else ddict_res (DD3_of DENT) gv shk (fst e) (snd e)).
  set (F' := fun e: val * ddict_st => if Val.eq (fst e) q0 then emp else mrest DENT gv shk e).
  assert (EF: set_full DENT gv shk l q0 = ddict_res (DD3_of DENT) gv shk X dd *
     fold_right sepcon emp (map (fun e' => if Val.eq (fst e') X then emp else F e') l)).
  { unfold set_full. fold F. rewrite (fold_pick F l (X, dd) Hd Hin). unfold F at 1. simpl.
    destruct (Val.eq X q0); [contradiction | auto]. }
  assert (EF': set_rest_ne DENT gv shk l q0 = mrest DENT gv shk (X, dd) *
     fold_right sepcon emp (map (fun e' => if Val.eq (fst e') X then emp else F' e') l)).
  { unfold set_rest_ne. fold F'. rewrite (fold_pick F' l (X, dd) Hd Hin). unfold F' at 1. simpl.
    destruct (Val.eq X q0); [contradiction | auto]. }
  set (P := match dd_ref dd with Some p => isptr p | None => True end).
  exists (ddict_pad X * refb shk dd * fold_right sepcon emp (map (fun e' => if Val.eq (fst e') X then emp else F e') l) * D3),
    (!! P && (fold_right sepcon emp (map (fun e' => if Val.eq (fst e') X then emp else F' e') l) *
     (ds_noid (dd_x X dd) (dd_buf dd) * dobj_rest (dd_x X dd) (dd_buf dd)) * AR')).
  assert (E1: set_full DENT gv shk l q0 * D3 = begin_res DENT gv (DA_ddict (dd_x X dd) (dd_buf dd) shk) *
    (ddict_pad X * refb shk dd * fold_right sepcon emp (map (fun e' => if Val.eq (fst e') X then emp else F e') l) * D3)).
  { rewrite EF, ddict_res_eq, (DD3_begin DENT gv shk). apply pred_ext; cancel. }
  split; [exact E1 | split].
  - rewrite E1. sep_apply (begin_wf_D shk X dd W shd cap dst Hsh Hb). entailer!.
  - intros dm. unfold sx. rewrite Hs.
    assert (Hrl: set_full DENT gv shk l q0 * D3 |-- !! P).
    { rewrite EF, ddict_res_eq. unfold refb, P. destruct (dd_ref dd); entailer!. }
    apply pred_ext.
    + apply derives_trans with (!! P && (set_full DENT gv shk l q0 * D3)); [apply andp_right; auto |].
      apply derives_extract_prop; intros Hrp.
      rewrite set_full_split, EF', (mrest_split shk X dd dm Hrp), Hsx, HD.
      simpl darg_ox. unfold dent_of. simpl dx_q. entailer!.
    + Intros. rename H into Hrp.
      rewrite set_full_split, EF', (mrest_split shk X dd dm Hrp), Hsx, HD.
      simpl darg_ox. unfold dent_of. simpl dx_q. cancel.
Qed.

End NLC.

(* ---------- `lent`: the local DDict ---------- *)

(* Frames3Model's f3m_probe / hs_probe_in (not in this file's imports) *)
Lemma msp_probe_f: forall fuel l tbl j n id, n = Zlength tbl -> 0 <= j < n ->
  hs_probe_f fuel l tbl j n id <> nullval -> In (hs_probe_f fuel l tbl j n id) tbl.
Proof.
  induction fuel as [|f IH]; intros l tbl j n id En Hj H; cbn [hs_probe_f] in *; [contradiction|].
  destruct (eq_dec (Znth j tbl) nullval) as [N|N]; [contradiction|].
  destruct (orb _ _).
  - apply Znth_In. lia.
  - apply IH; auto. apply Z.mod_pos_bound. lia.
Qed.

Lemma msp_probe_in: forall l tbl id,
  hs_inv l tbl -> hs_probe l tbl id <> nullval -> In (hs_probe l tbl id) (map fst l).
Proof.
  intros l tbl id Hi Hn. destruct Hi as ([k [Hk En]] & _ & _ & _ & _ & _ & Hp & _).
  unfold hs_probe in *.
  assert (Hj: 0 <= hs_home id (Zlength tbl) < Zlength tbl).
  { unfold hs_home. rewrite En. replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
    rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  pose proof (msp_probe_f _ l tbl _ _ id eq_refl Hj Hn) as Hin.
  eapply Permutation_in; [exact Hp|]. apply filter_In. split; [exact Hin|].
  unfold veqb. destruct (Val.eq _ nullval); [contradiction|reflexivity].
Qed.

Lemma lent_ok_of: forall pr sp d l tbl x buf sfr q0,
  sel_on pr sp = true -> df_lx d = Some (x, buf) -> df_local d <> nullval -> ~ In q0 (map fst l) -> hs_inv l tbl ->
  bytes_ok sfr -> starting_len (dp_fmt pr =? 1) <= Zlength sfr ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field sfr 0 4) = false) ->
  (forall h, get_frame_header_m (dp_fmt pr =? 1) sfr = FH_ok h ->
     hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = q0) ->
  lent_ok pr sp d l tbl (Some x) sfr.
Proof.
  intros pr sp d l tbl x buf sfr q0 Hs Hlx Hloc Hn Hi Hb Hl Hns Hpr.
  split; auto. split; [exists x, buf; auto |]. intros h Hh. unfold sel_r.
  destruct (eq_dec (df_ddict d) nullval); auto.
  destruct (gfh3_prefix _ sfr Hb Hl Hns) as [E | [Hn' _]]; [| exfalso; eapply Hn'; eauto].
  rewrite E in Hh. destruct (Hpr h Hh) as [? | Eq]; auto.
  destruct (eq_dec (hs_probe l tbl (fh_dictID h)) nullval); auto.
  exfalso. apply Hn. rewrite <- Eq. apply msp_probe_in; auto.
Qed.

Lemma cur_ok_of: forall pr sp l d dcur q0 xq,
  dc_ok pr sp l d dcur -> cur_ok3 d l q0 ->
  (q0 = nullval \/ q0 = df_local d \/ In q0 (map fst l) \/ exists v, xq = Some (q0, v)) ->
  cur_ok dcur l xq.
Proof.
  intros pr sp l d dcur q0 xq Hdc (Hu & Hd) Hx. unfold cur_ok. destruct Hdc as [-> | (_ & q & Hq & ->)].
  - split; auto. destruct Hd as [? | [? | [? | E]]]; auto. rewrite E.
    destruct Hx as [? | [? | [? | ?]]]; auto.
  - simpl. split; auto.
Qed.

(* an equation between two predicates that both imply Q, proved under Q *)
Lemma pred_ext_prop: forall (Q: Prop) (A B: mpred), (A |-- !! Q) -> (B |-- !! Q) -> (Q -> A = B) -> A = B.
Proof.
  intros Q A B HA HB H. apply pred_ext.
  - apply derives_trans with (!! Q && A); [apply andp_right; auto |].
    apply derives_extract_prop; intros HQ. rewrite (H HQ). auto.
  - apply derives_trans with (!! Q && B); [apply andp_right; auto |].
    apply derives_extract_prop; intros HQ. rewrite (H HQ). auto.
Qed.

Section LENT.
Variable DENT : dent_pred.
Variable gv : globals.

Definition dfld3 (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p.

Lemma lent_res: forall p pr sp d l tbl shk x buf sh W shd cap dst am hb,
  sel_on pr sp = true -> df_lx d = Some (x, buf) -> darg_local d (DA_ddict x buf sh) = true ->
  ~ In (dx_q x) (map fst l) -> darg_ok3 W (DA_ddict x buf sh) shd cap dst ->
  exists MK MK2: mpred,
    msel_res DENT gv p pr sp d l tbl shk (DA_ddict x buf sh) am hb * darg_res3 DENT gv pr sp d (DA_ddict x buf sh) =
      begin_res DENT gv (DA_ddict x buf sh) * MK /\
    (begin_res DENT gv (DA_ddict x buf sh) * MK |--
       !! (darg_wf (DA_ddict x buf sh) /\ darg_ok3 W (DA_ddict x buf sh) shd cap dst)) /\
    forall dm, begin_res DENT gv (DA_ddict x buf sh) * MK =
      mf_fsel DENT gv p pr sp d l tbl None true am hb (Some x) * ext_res (ext_of (DA_ddict x buf sh) dm) * MK2.
Proof.
  intros p pr sp d l tbl shk x buf sh W shd cap dst am hb Hs Hlx Hl Hn Hok.
  pose proof Hl as Hl'. unfold darg_local in Hl'. simpl darg_ddict in Hl'.
  apply andb_prop in Hl'. destruct Hl' as [Eq Hnn]. apply veqb_true in Eq.
  assert (Hnl: df_local d <> nullval).
  { intros E. rewrite E in Hnn. rewrite veqb_refl in Hnn. discriminate. }
  set (F3 := dfld3 p d).
  set (LB := if ddx_copied x then emp else bytes_at sh (dx_bytes x) buf).
  assert (ED: darg_res3 DENT gv pr sp d (DA_ddict x buf sh) = LB).
  { unfold darg_res3. rewrite Hs, Hl. reflexivity. }
  assert (EG: dgroup DENT gv p d = F3 * ddict_rep_at DENT gv x buf).
  { unfold dgroup, local_rep. rewrite Hlx. destruct (eq_dec (df_local d) nullval); [contradiction |].
    rewrite prop_true_andp by auto. reflexivity. }
  assert (EH: dgroup_hole gv p d = F3 * (ddict_struct x buf * blk_tok (dx_mem x) (Tstruct _ZSTD_DDict_s noattr) (dx_q x) *
       (if ddx_copied x then blk_tok (dx_mem x) (tarray tuchar (Zlength (dx_bytes x))) buf else emp) *
       ddict_pad (dx_q x))).
  { unfold dgroup_hole. rewrite Hlx. rewrite prop_true_andp by auto. reflexivity. }
  exists (mem_mgr gv * F3 * ddict_pad (dx_q x) * cm_have am (hb + local_held d) * hset_tbl am sp l tbl *
          set_full DENT gv shk l (dx_q x) * LB),
    (set_rest_ne DENT gv shk l (dx_q x)).
  split; [| split].
  - unfold msel_res. rewrite Hs, EG, ED. simpl darg_ddict. unfold ddict_rep_at, begin_res. apply pred_ext; cancel.
  - apply derives_trans with (darg_res DENT gv (DA_ddict x buf sh) * TT).
    { rewrite darg_res_begin. simpl begin_rest. fold LB. cancel. }
    sep_apply (darg_wf_res DENT gv W _ shd cap dst Hok). entailer!.
  - intros dm. unfold mf_fsel, sel_any, sel_hole. rewrite Hs, EH. simpl opt_token. unfold dent_of.
    rewrite set_full_split, set_ids_ne_notin by auto. unfold begin_res, ddict_mem. subst LB.
    apply (pred_ext_prop (isptr buf \/ (buf = nullval /\ dx_ref x = Some nullval /\ dx_bytes x = nil)));
      [sep_apply (ddict_struct_cont x buf); entailer! | sep_apply (ddict_struct_cont x buf); entailer! |].
    intros [Hp | (-> & Hr & Hn0)].
    + destruct buf; try contradiction. unfold ext_of, ext_res. rewrite bytes_at_ptr by exact I.
      destruct (ddx_copied x); apply pred_ext; cancel.
    + (* the DDict without content: no extDict *)
      assert (Hcf: ddx_copied x = false) by (unfold ddx_copied; rewrite Hr; reflexivity).
      unfold ext_of. simpl. rewrite Hcf, bytes_at_null. unfold ext_res. apply pred_ext; cancel.
Qed.

End LENT.

(* ---------- one frame: Begin's resources, decompressFrame's, and back ---------- *)

Lemma mf_split: forall DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv sfr am hb,
  (sel_on pr sp = true -> msel_ok W d l a shk shd cap dst) ->
  darg_ok3 W a shd cap dst ->
  (sel_on pr sp = true -> darg_local d a = true -> ~ In (darg_ddict a) (map fst l)) ->
  (sel_on pr sp = true -> hs_inv l tbl) ->
  qv_ok pr sp a l qv -> dc_ok pr sp l d dcur ->
  (darg_local d a = true -> qv = darg_ddict a -> dcur = d) ->
  bytes_ok sfr -> starting_len (dp_fmt pr =? 1) <= Zlength sfr ->
  ((dp_fmt pr =? 1) = true \/ is_skippable_magic (le_field sfr 0 4) = false) ->
  (forall h, get_frame_header_m (dp_fmt pr =? 1) sfr = FH_ok h -> sel_on pr sp = true -> darg_ddict a <> nullval ->
     hs_probe l tbl (fh_dictID h) = nullval \/ hs_probe l tbl (fh_dictID h) = qv) ->
  let a' := mf_dict a l shk qv in
  exists (MK MK2: mpred) (xq: option (val * val)) (lent: bool),
    (sel_on pr sp = true -> cur_ok dcur l xq) /\
    (lent = true -> lent_ok pr sp dcur l tbl (darg_ox a') sfr /\ forall dm, lent_ext dcur (ext_of a' dm)) /\
    (darg_local d a = true -> qv = darg_ddict a -> sel_on pr sp = true -> lent = true) /\
    (msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a |-- begin_res DENT gv a' * MK) /\
    (begin_res DENT gv a' * MK |-- !! (darg_wf a' /\ darg_ok3 W a' shd cap dst)) /\
    (begin_res DENT gv a' * MK |-- msel_res DENT gv p pr sp dcur l tbl shk a am hb * darg_res3 DENT gv pr sp d a) /\
    (forall dm, begin_res DENT gv a' * MK |--
       mf_fsel DENT gv p pr sp dcur l tbl xq lent am hb (darg_ox a') * ext_res (ext_of a' dm) * MK2) /\
    (forall dm dcur', dict_after pr sp l dcur dcur' -> (lent = true -> dcur' = dcur) ->
       mf_fsel DENT gv p pr sp dcur' l tbl xq lent am hb (darg_ox a') * ext_res (ext_of a' dm) * MK2 |--
       msel_res DENT gv p pr sp dcur' l tbl shk a am hb * darg_res3 DENT gv pr sp d a).
Proof.
  intros DENT gv p pr sp d l tbl shk a W shd cap dst dcur qv sfr am hb Hmsel Hok HG1 Hinv Hqv Hdc Hlq Hb Hl Hns Hpr a'.
  destruct (sel_on pr sp) eqn:Hs.
  2: { (* the selection off *)
    destruct Hqv as [Hqv | (? & _)]; [| congruence].
    destruct Hdc as [-> | (? & _)]; [| congruence].
    assert (Ea: a' = a) by (unfold a', mf_dict; rewrite Hqv, veqb_refl; auto).
    clearbody a'. subst a'.
    destruct (nl_main DENT gv p pr sp d d l tbl shk a a W shd cap dst None am hb) as (MK & MK2 & H1 & H2 & H3 & H4 & H5).
    { unfold sfo, darg_res3. rewrite Hs, emp_sepcon. simpl. apply nl_A; auto. }
    exists MK, MK2, None, false. split; [intros; discriminate |]. split; [intros; discriminate |].
    split; [intros _ _ ?; discriminate |]. split; [auto | split; [auto | split; [auto | split; [auto |]]]].
    intros dm dcur' _ _. apply H5. }
  specialize (Hmsel eq_refl). specialize (HG1 eq_refl). specialize (Hinv eq_refl).
  destruct Hmsel as (Hc3 & Hshk & Hloc & Hst & Hbuf & HmG1).
  assert (Hd: NoDup (map fst l)) by apply Hinv.
  assert (Hp: Forall (fun e => isptr (fst e)) l) by apply Hinv.
  assert (Hsfo: sfo DENT gv pr sp shk l (darg_ddict a) = set_full DENT gv shk l (darg_ddict a))
    by (unfold sfo; rewrite Hs; auto).
  destruct (veqb qv (darg_ddict a)) eqn:Eq.
  - (* the argument's DDict *)
    apply veqb_true in Eq.
    assert (Ea: a' = a) by (unfold a', mf_dict; rewrite Eq, veqb_refl; auto).
    clearbody a'. subst a'.
    destruct (darg_local d a) eqn:Hla.
    + (* the local DDict: lent *)
      specialize (Hlq eq_refl Eq). subst dcur.
      destruct (Hloc eq_refl) as (x & buf & sh & -> & Hlx).
      pose proof Hla as Hla'. unfold darg_local in Hla'. simpl darg_ddict in Hla'.
      apply andb_prop in Hla'. destruct Hla' as [Eql Hnn]. apply veqb_true in Eql.
      assert (Hnl: df_local d <> nullval).
      { intros E. rewrite E in Hnn. rewrite veqb_refl in Hnn. discriminate. }
      specialize (HG1 eq_refl). simpl darg_ddict in HG1.
      destruct (lent_res DENT gv p pr sp d l tbl shk x buf sh W shd cap dst am hb Hs Hlx Hla HG1 Hok)
        as (MK & MK2 & E1 & Hw & E2).
      exists MK, MK2, None, true. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
      * intros _. eapply cur_ok_of; [exact Hdc | exact Hc3 |]. simpl. right; left; auto.
      * intros _. split.
        -- apply (lent_ok_of pr sp d l tbl x buf sfr (dx_q x)); auto. intros h Hh.
           rewrite Eq in Hpr. apply Hpr; auto. simpl. rewrite Eql; auto.
        -- intros dm. unfold lent_ext. rewrite Hlx. intros Hc. unfold ext_of. destruct buf; rewrite Hc; eauto.
      * auto.
      * rewrite E1. auto.
      * exact Hw.
      * rewrite E1. auto.
      * intros dm. rewrite (E2 dm). apply derives_refl.
      * intros dm dcur' _ Hd'. rewrite (Hd' eq_refl). simpl darg_ox. rewrite <- (E2 dm), E1. auto.
    + (* another DDict, or none *)
      assert (ED: darg_res3 DENT gv pr sp d a = darg_res DENT gv a) by (unfold darg_res3; rewrite Hs, Hla; auto).
      destruct (nl_B DENT gv pr sp l shk a W shd cap dst Hs Hd Hp
                  (fun x buf sh dd E Hin => Hst x buf sh dd E Hin) Hok) as (xq & Hx & Hnl).
      destruct (nl_main DENT gv p pr sp d dcur l tbl shk a a W shd cap dst xq am hb) as (MK & MK2 & H1 & H2 & H3 & H4 & H5).
      { rewrite Hsfo, ED. exact Hnl. }
      exists MK, MK2, xq, false. split; [| split; [intros; discriminate | split; [intros; discriminate |]]].
      * intros _. eapply cur_ok_of; eauto. destruct Hx as [? | [? | ?]]; auto.
      * split; [auto | split; [auto | split; [auto | split; [auto |]]]]. intros dm dcur' _ _. apply H5.
  - (* a DDict of the set *)
    assert (Hne: qv <> darg_ddict a) by (intros E; rewrite E, veqb_refl in Eq; discriminate).
    destruct Hqv as [? | (_ & Hq0 & Hin)]; [contradiction |].
    destruct (find (fun e => veqb (fst e) qv) l) as [[X dd] |] eqn:Ef.
    2: { exfalso. apply in_map_iff in Hin. destruct Hin as [e [Ee Hin]].
         pose proof (find_none _ _ Ef e Hin) as Hf. simpl in Hf. rewrite Ee, veqb_refl in Hf. discriminate. }
    assert (Ea: a' = DA_ddict (dd_x qv dd) (dd_buf dd) shk) by (unfold a', mf_dict; rewrite Eq, Ef; reflexivity).
    clearbody a'. subst a'.
    apply find_some in Ef. destruct Ef as [HinX HXq]. simpl in HXq. apply veqb_true in HXq. subst X.
    assert (Hbd: ddict_buf_ok0 W shk dd shd cap dst).
    { rewrite Forall_forall in Hbuf. apply (Hbuf (qv, dd) HinX). simpl. auto. }
    assert (Hpart: exists xq AP AR',
      (darg_ddict a = nullval \/ darg_ddict a = df_local d \/ In (darg_ddict a) (map fst l) \/
       exists v, xq = Some (darg_ddict a, v)) /\
      set_ids l * opt_token xq = set_ids_ne l (darg_ddict a) * AP /\
      darg_res3 DENT gv pr sp d a = AP * AR').
    { destruct (darg_local d a) eqn:Hla.
      - exists None, emp, (darg_res3 DENT gv pr sp d a). split; [| split].
        + right; left. unfold darg_local in Hla. apply andb_prop in Hla. destruct Hla as [E _].
          apply veqb_true in E. auto.
        + simpl. rewrite !sepcon_emp, set_ids_ne_notin; auto.
        + rewrite emp_sepcon; auto.
      - destruct (ap_split DENT gv l a Hd Hp (fun x buf sh dd E Hin => Hst x buf sh dd E Hin))
          as (xq & AP & AR2 & Hx & Hsx & Hr).
        exists xq, AP, (dent_of DENT gv (darg_ox a) * ext_res (ext_of a no_dict) * AR2). split; [| split].
        + destruct Hx as [? | [? | ?]]; auto.
        + exact Hsx.
        + unfold darg_res3. rewrite Hs, Hla. simpl. apply Hr. }
    destruct Hpart as (xq & AP & AR' & Hx & Hsx & HD).
    pose proof (nl_D DENT gv pr sp l shk (darg_ddict a) qv dd xq AP AR' (darg_res3 DENT gv pr sp d a) W shd cap dst
                  Hs Hd HinX Hne Hshk Hbd Hsx HD) as Hnl.
    destruct (nl_main DENT gv p pr sp d dcur l tbl shk a (DA_ddict (dd_x qv dd) (dd_buf dd) shk) W shd cap dst xq am hb)
      as (MK & MK2 & H1 & H2 & H3 & H4 & H5).
    { rewrite Hsfo. exact Hnl. }
    exists MK, MK2, xq, false. split; [| split; [intros; discriminate | split; [intros _ E; contradiction |]]].
    * intros _. eapply cur_ok_of; eauto.
    * split; [auto | split; [auto | split; [auto | split; [auto |]]]]. intros dm dcur' _ _. apply H5.
Qed.

End CM_Multi3Split_1.
