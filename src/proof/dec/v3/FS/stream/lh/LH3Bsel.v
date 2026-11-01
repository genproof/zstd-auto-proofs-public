(* FS3 streaming, case zdss_loadHeader, piece B: the lending of the context's dictionary resources to
   ZSTD_decompress_usingDDict(zds, .., ZSTD_getDDict(zds)) in the shortcut, the selection on or off
   (usingDDict_int_spec3: msel_res / darg_res3; the one-shot part's oneshot3/O3Cases*.v is the
   template for the selection on). *)
Require Export Zstd.proof.dec.v3.FS.stream.lh.LH3Bx.
Local Open Scope logic.

Section CM_LH3Bsel_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Section Lend.
Variable DENT : dent_pred.
Variables (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3) (tbl: list val)
          (shd: share) (cap: Z) (dst: val).
(* the context's allocator am, the bytes hb it has given out besides the local DDict, the set's bytes hs *)
Variables (am: option cmem) (hb hs: Z).

(* the dictionary fields after ZSTD_getDDict *)
Definition lb_d2 : dfields := snd (getddict_res (c3_dict k)).

(* the resources before the call (dgroup with getDDict's fields) and after it (dgroup with the fields d'; the
   allocator then holds the local DDict of d', if any) *)
Definition lb_post (d': dfields) : mpred :=
  mem_mgr gv * dgroup DENT gv p d' * cm_have am (hb + local_held d') * hset_t am (c3_sp k) (c3_set k) hs tbl *
  dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st).

Definition lb_pre : mpred := lb_post lb_d2.

(* what usingDDict_int_spec3 holds: the selection's resources with the fields d', the argument's *)
Definition lb_mid (d': dfields) (ad: darg) : mpred :=
  msel_res DENT gv p (c3_par k) (c3_sp k) d' (c3_set k) tbl Ews ad am hb *
  darg_res3 DENT gv (c3_par k) (c3_sp k) lb_d2 ad.

(* the facts of the argument ad: the call's precondition, and what its model is *)
Definition lb_facts (ad: darg) : Prop :=
  darg_is_ddict ad /\ darg_ddict ad = fst (getddict_res (c3_dict k)) /\ darg_ok3 W ad shd cap dst /\
  (sel_on (c3_par k) (c3_sp k) = true -> msel_ok W lb_d2 (c3_set k) ad Ews shd cap dst) /\
  (sel_on (c3_par k) (c3_sp k) = false -> dc_set st = nil ->
     forall dm, dictref_model (dc_dict st) = Some dm -> darg_model ad = Some dm) /\
  (sel_on (c3_par k) (c3_sp k) = true ->
     Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k) /\
     (forall dd dm, In (darg_ddict ad, dd) (c3_set k) -> dict_auto (dd_bytes dd) = Some dm ->
        darg_model ad = Some dm)).

End Lend.

(* ---------- helpers (adapted from the one-shot part, oneshot3/O3Cases*.v) ---------- *)

Lemma lbs_msel_off DENT gv p pr sp d l tbl shk a am hb :
  sel_on pr sp = false -> msel_res DENT gv p pr sp d l tbl shk a am hb = emp.
Proof. intros H. unfold msel_res. rewrite H. reflexivity. Qed.

Lemma lbs_darg3_off DENT gv pr sp d a :
  sel_on pr sp = false -> darg_res3 DENT gv pr sp d a = darg_res DENT gv a.
Proof. intros H. unfold darg_res3. rewrite H. reflexivity. Qed.

Lemma lbs_darg3_none DENT gv pr sp d : darg_res3 DENT gv pr sp d DA_none = emp.
Proof. unfold darg_res3. destruct (andb _ _); reflexivity. Qed.

Lemma lbs_local_null d a : df_local d = nullval -> darg_local d a = false.
Proof.
  intros H. unfold darg_local. rewrite H. unfold veqb at 2.
  destruct (Val.eq nullval nullval); [ | congruence]. apply andb_false_r.
Qed.

Lemma lbs_darg3_nonlocal DENT gv pr sp d a :
  darg_local d a = false -> darg_res3 DENT gv pr sp d a = darg_res DENT gv a.
Proof. intros H. unfold darg_res3. rewrite H, andb_false_r. reflexivity. Qed.

Lemma lbs_local_none d : darg_local d DA_none = false.
Proof.
  unfold darg_local, darg_ddict, veqb.
  destruct (Val.eq nullval (df_local d)) as [E | E]; [ | reflexivity].
  rewrite <- E. destruct (Val.eq nullval nullval); [reflexivity | congruence].
Qed.

Lemma lbs_null_notin (l: list (val * ddict_st)) : Forall (fun e => isptr (fst e)) l -> ~ In nullval (map fst l).
Proof.
  intros H Hin. apply in_map_iff in Hin. destruct Hin as [e [E Hin]].
  rewrite Forall_forall in H. specialize (H e Hin). rewrite E in H. exact H.
Qed.

Lemma lbs_rep_valid DENT gv x buf : ddict_rep_at DENT gv x buf |-- valid_pointer (dx_q x).
Proof.
  unfold ddict_rep_at, ddict_struct. Intros.
  apply derives_trans with (field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictBuffer) (dx_q x) * TT); [cancel | ].
  apply sepcon_valid_pointer1. unfold field_at_.
  apply field_at_valid_ptr0; [auto | simpl; lia | reflexivity].
Qed.

Lemma lbs_DD3_valid DENT gv q dd : DD3_of DENT gv q dd = (DD3_of DENT gv q dd && valid_pointer q).
Proof.
  apply pred_ext; [apply andp_right; [auto | ] | apply andp_left1; auto].
  unfold DD3_of. apply (lbs_rep_valid DENT gv (dd_x q dd) (dd_buf dd)).
Qed.

Lemma lbs_dgroup_split DENT gv p d x buf :
  df_local d = dx_q x -> isptr (dx_q x) -> df_lx d = Some (x, buf) ->
  dgroup DENT gv p d =
    (field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
     field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
     field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p) * ddict_rep_at DENT gv x buf.
Proof.
  intros H1 H2 H3. unfold dgroup, local_rep. rewrite H1, H3.
  rewrite if_false by (destruct (dx_q x); simpl in *; try contradiction; discriminate).
  rewrite prop_true_andp by auto. reflexivity.
Qed.

(* the caller's content pointer of a DDict by reference is a pointer (its bytes are there) *)
Lemma lbs_ddict_res_ptr DENT gv sh q dd :
  ddict_res (DD3x DENT) gv sh q dd |-- !! (forall p0, dd_ref dd = Some p0 -> isptr p0).
Proof.
  unfold ddict_res. destruct (dd_ref dd) as [p|] eqn:Er.
  - Intros. entailer!. intros p0 E. inversion E; subst p0; auto.
  - apply prop_right. intros p0 E. discriminate.
Qed.

(* a DDict's resources as an argument of the call (by reference, a copy, or without content) *)
Lemma lbs_ddict_res_darg DENT gv sh q dd : (forall p0, dd_ref dd = Some p0 -> isptr p0) ->
  ddict_res (DD3x DENT) gv sh q dd = darg_res DENT gv (DA_ddict (dd_x q dd) (dd_buf dd) sh).
Proof.
  intros Hptr. unfold ddict_res, DD3x. rewrite <- lbs_DD3_valid. unfold DD3_of, darg_res, ddx_copied.
  cbn [dx_ref dd_x dx_bytes].
  destruct (dd_xref_cases dd) as [(p0 & Ep & Ex) | [(Ep & Hn & Ex) | (Ep & Hn & Ex)]]; rewrite Ep, Ex.
  - specialize (Hptr p0 Ep).
    apply pred_ext;
      (assert_PROP (dd_buf dd = p0) as Hb
         by (unfold ddict_rep_at, ddict_struct; cbn [dx_ref dd_x]; rewrite Ex; entailer!));
      rewrite Hb, bytes_at_ptr by auto; cancel.
  - apply pred_ext; cancel.
  - apply pred_ext;
      (assert_PROP (dd_buf dd = nullval) as Hb
         by (unfold ddict_rep_at, ddict_struct; cbn [dx_ref dd_x]; rewrite Ex; entailer!));
      rewrite Hb, bytes_at_null; cancel.
Qed.

Section LbsRes.
Variable DENT : dent_pred.
Variables (gv: globals) (shk: share).

Definition lbs_all (l: list (val * ddict_st)) : mpred :=
  fold_right sepcon emp (map (fun e => ddict_res (DD3x DENT) gv shk (fst e) (snd e)) l).

Lemma lbs_set_res_none (l: list (val * ddict_st)) cur :
  cur_ddict cur = None -> set_res (DD3x DENT) gv shk l cur = lbs_all l.
Proof. intros H. unfold set_res, lbs_all. rewrite H. reflexivity. Qed.

Lemma lbs_set_res_some (l: list (val * ddict_st)) cur q :
  cur_ddict cur = Some q -> set_res (DD3x DENT) gv shk l cur = set_full DENT gv shk l q.
Proof. intros H. unfold set_res, set_full. rewrite H. reflexivity. Qed.

Lemma lbs_full_notin (l: list (val * ddict_st)) q :
  ~ In q (map fst l) -> set_full DENT gv shk l q = lbs_all l.
Proof.
  induction l as [ | e l IH]; intros Hn; [reflexivity | ].
  unfold set_full, lbs_all in *. simpl in *. rewrite IH by tauto.
  destruct (Val.eq (fst e) q); [tauto | reflexivity].
Qed.

Lemma lbs_all_split (l: list (val * ddict_st)) q dd :
  NoDup (map fst l) -> In (q, dd) l -> lbs_all l = ddict_res (DD3x DENT) gv shk q dd * set_full DENT gv shk l q.
Proof.
  induction l as [ | e l IH]; intros Hnd Hin; [contradiction | ].
  simpl in Hnd. inv Hnd. unfold lbs_all, set_full in *. simpl.
  destruct Hin as [E | Hin].
  - subst e. simpl. destruct (Val.eq q q); [ | congruence]. rewrite emp_sepcon.
    f_equal. fold (lbs_all l). symmetry. apply lbs_full_notin. exact H1.
  - rewrite (IH H2 Hin).
    destruct (Val.eq (fst e) q) as [E | E].
    + exfalso. apply H1. rewrite E. apply in_map_iff. exists (q, dd); auto.
    + apply pred_ext; cancel; apply derives_refl.
Qed.

(* the argument q (entry dd of the set) out of the caller's memory (the frame R0 chosen before NoDup is known) *)
Lemma lbs_regroup (l: list (val * ddict_st)) (cur: option dictref) q dd :
  (forall dr q0 dd0 dd', cur = Some dr -> dr_src dr = DSDDict q0 dd0 -> In (q0, dd') l -> dd' = dd0) ->
  exists R0, NoDup (map fst l) -> In (q, dd) l ->
    dict_res (DD3x DENT) gv shk cur * set_res (DD3x DENT) gv shk l cur =
    ddict_res (DD3x DENT) gv shk q dd * set_full DENT gv shk l q * R0.
Proof.
  intros Hcur.
  destruct (cur_ddict cur) as [q0 | ] eqn:Ec.
  - rewrite (lbs_set_res_some l cur q0 Ec).
    destruct (in_dec Val.eq q0 (map fst l)) as [Hq0 | Hq0].
    + apply in_map_iff in Hq0. destruct Hq0 as [[q1 dd1] [E1 Hin1]]. simpl in E1. subst q1.
      destruct cur as [[[pk | | q2 dd2] raw once b] | ]; simpl in Ec; try discriminate. inv Ec.
      assert (dd1 = dd2) by (eapply Hcur; [reflexivity | reflexivity | exact Hin1]). subst dd1.
      exists emp. intros Hnd Hin. simpl dict_res. rewrite sepcon_emp.
      rewrite <- (lbs_all_split l q dd Hnd Hin), (lbs_all_split l q0 dd2 Hnd Hin1). apply pred_ext; cancel.
    + exists (dict_res (DD3x DENT) gv shk cur). intros Hnd Hin.
      rewrite (lbs_full_notin l q0 Hq0), (lbs_all_split l q dd Hnd Hin).
      apply pred_ext; cancel.
  - exists (dict_res (DD3x DENT) gv shk cur). intros Hnd Hin.
    rewrite (lbs_set_res_none l cur Ec). rewrite (lbs_all_split l q dd Hnd Hin). apply pred_ext; cancel.
Qed.

Lemma lbs_ddict_res_ld q dd : ddict_res (DD3_of DENT) gv shk q dd |-- !! ld_rel (dd_bytes dd) (dd_ld dd).
Proof.
  unfold ddict_res, DD3_of, ddict_rep_at, ddict_struct. Intros. apply prop_right.
  match goal with H: ld_rel _ _ |- _ => exact H end.
Qed.

Lemma lbs_full_ld (l: list (val * ddict_st)) q0 :
  set_full DENT gv shk l q0 |-- !! Forall (fun e => fst e <> q0 -> ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l.
Proof.
  induction l as [ | e l IH]; [apply prop_right; constructor | ].
  unfold set_full in *. simpl.
  destruct (Val.eq (fst e) q0) as [E | E].
  - rewrite emp_sepcon. eapply derives_trans; [exact IH | ]. apply prop_derives. intros H. constructor; auto.
    intros Hn; contradiction.
  - sep_apply (lbs_ddict_res_ld (fst e) (snd e)). Intros. sep_apply IH. Intros. apply prop_right.
    constructor; auto.
Qed.

Lemma lbs_all_ld (l: list (val * ddict_st)) :
  lbs_all l |-- !! Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) l.
Proof.
  induction l as [ | e l IH]; [apply prop_right; constructor | ].
  unfold lbs_all, DD3x in *. simpl.
  sep_apply (lbs_ddict_res_ld (fst e) (snd e)). Intros. sep_apply IH. Intros. apply prop_right.
  constructor; auto.
Qed.

(* the local DDict is not one of the set's (both would hold its dictID field) *)
Lemma lbs_local_not_in x buf (l: list (val * ddict_st)) :
  ddict_rep_at DENT gv x buf * lbs_all l |-- !! (~ In (dx_q x) (map fst l)).
Proof.
  induction l as [ | e l IH].
  - apply prop_right. simpl. tauto.
  - unfold lbs_all. simpl fold_right.
    destruct (Val.eq (fst e) (dx_q x)) as [E | E].
    + unfold ddict_res, DD3x. rewrite <- lbs_DD3_valid. unfold DD3_of. rewrite E.
      unfold ddict_rep_at, ddict_struct. Intros. simpl dx_q.
      apply derives_trans with
        (field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) (dx_q x) *
         field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) (dx_q x) * TT).
      * cancel.
      * eapply derives_trans; [apply sepcon_derives; [apply field_at_conflict; [auto | simpl; lia] | apply derives_refl] | ].
        rewrite FF_sepcon. apply FF_left.
    + fold (lbs_all l).
      assert_PROP (~ In (dx_q x) (map fst l)) as Hn.
      { sep_apply IH. entailer!. }
      apply prop_right. simpl. intros [H' | H']; [congruence | tauto].
Qed.

End LbsRes.

(* a by-reference DDict a stream may use (0 bytes at a valid pointer) is a valid argument (FS3 R3: at cap 0 the
   pointer is enough, dict_ptr_ok0) *)
Lemma lbs_ptr_ok W shd cap dst p0 :
  writable_share shd -> (pws_pred W |-- valid_pointer p0) -> 0 <= cap ->
  dict_ptr_ok0 W Ews 0 p0 shd cap dst.
Proof.
  intros Hw Hp Hc0. destruct (Z.eq_dec cap 0) as [E | Hc].
  { right. split; [exact E | ]. split; [reflexivity | exact Hp]. }
  left. right. split; [reflexivity | ]. split; [exact Hp | ].
  apply sepcon_valid_pointer2. unfold data_at_. apply data_at_valid_ptr.
  - apply readable_nonidentity. apply writable_readable. exact Hw.
  - simpl. rewrite Z.max_r by lia. lia.
Qed.

Lemma lbs_buf_ok W shd cap dst dd :
  writable_share shd -> sddict_ok W dd -> 0 <= cap ->
  ddict_buf_ok0 W Ews dd shd cap dst.
Proof.
  intros Hw Hs Hc. unfold ddict_buf_ok0. unfold sddict_ok in Hs. destruct (dd_ref dd) as [p0 | ]; [ | exact I].
  destruct Hs as [Hb Hp]. rewrite Hb. apply lbs_ptr_ok; auto.
Qed.

Section LbsCases.
Variable DENT : dent_pred.
Variables (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3) (tbl: list val)
          (shd: share) (cap: Z) (dst: val).
Variables (am: option cmem) (hb hs: Z).

Definition lbs_concl : Prop :=
  exists Rf: darg -> mpred,
    (lb_pre DENT gv p st k tbl am hb hs |--
       EX ad: darg, !! lb_facts W st k shd cap dst ad && (lb_mid DENT gv p k tbl am hb (lb_d2 k) ad * Rf ad)) /\
    (forall ad d', lb_facts W st k shd cap dst ad ->
       (d' = lb_d2 k \/ (sel_on (c3_par k) (c3_sp k) = true /\
                         exists q, In q (map fst (c3_set k)) /\ d' = switch_fields q)) ->
       lb_mid DENT gv p k tbl am hb d' ad * Rf ad |-- lb_post DENT gv p st k tbl am hb hs d').

Variable Hsel : sel_on (c3_par k) (c3_sp k) = true.
Variable Hset : c3_set k = dc_set st.
Variable Hsp : Forall (fun e => ddict_buf_ok0 W Ews (snd e) shd cap dst) (c3_set k).
Variable Hw : writable_share shd.
Variable Hcap : 0 <= cap.

Lemma lbs_sp_ne : c3_sp k <> nullval.
Proof.
  intros E. unfold sel_on in Hsel. rewrite E in Hsel. unfold veqb in Hsel.
  destruct (Val.eq nullval nullval); [ | congruence]. rewrite andb_false_r in Hsel. discriminate.
Qed.

Lemma lbs_hset_t : hset_t am (c3_sp k) (c3_set k) hs tbl =
  !! (c3_set k <> nil /\ hs = set_bytes am (Zlength tbl)) && hset_tbl am (c3_sp k) (c3_set k) tbl.
Proof. unfold hset_t. rewrite if_false by apply lbs_sp_ne. reflexivity. Qed.

Lemma lbs_pre_hs : lb_pre DENT gv p st k tbl am hb hs |--
  !! (c3_set k <> nil /\ hs = set_bytes am (Zlength tbl) /\ hs_inv (c3_set k) tbl).
Proof.
  unfold lb_pre, lb_post. rewrite lbs_hset_t. unfold hset_tbl. Intros tp. apply prop_right. auto.
Qed.

(* the generic lending: the argument a0, the facts Q the resources give, the frame R0 *)
Lemma lbs_gen (a0: darg) (Q: Prop) (R0: mpred) :
  (lb_pre DENT gv p st k tbl am hb hs |-- !! Q) ->
  (c3_set k <> nil -> hs_inv (c3_set k) tbl -> Q -> lb_facts W st k shd cap dst a0) ->
  (hs_inv (c3_set k) tbl -> Q ->
     dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) =
     set_full DENT gv Ews (c3_set k) (darg_ddict a0) * darg_res3 DENT gv (c3_par k) (c3_sp k) (lb_d2 k) a0 * R0) ->
  lbs_concl.
Proof.
  intros HQ HF HE.
  exists (fun ad => !! (ad = a0 /\ c3_set k <> nil /\ hs = set_bytes am (Zlength tbl) /\ hs_inv (c3_set k) tbl /\ Q)
                    && R0).
  split.
  - assert_PROP Q as Hq by exact HQ.
    assert_PROP (c3_set k <> nil /\ hs = set_bytes am (Zlength tbl) /\ hs_inv (c3_set k) tbl) as Hh
      by apply lbs_pre_hs.
    destruct Hh as [Hn [Hhs Hi]].
    Exists a0. apply andp_right; [apply prop_right; auto | ].
    unfold lb_pre, lb_post, lb_mid, msel_res. rewrite Hsel, lbs_hset_t.
    rewrite !prop_true_andp by tauto.
    apply derives_trans with
      (mem_mgr gv * dgroup DENT gv p (lb_d2 k) * cm_have am (hb + local_held (lb_d2 k)) *
       hset_tbl am (c3_sp k) (c3_set k) tbl *
       (dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)));
      [cancel | ].
    rewrite (HE Hi Hq). cancel.
  - intros ad d' _ _. unfold lb_mid, lb_post, msel_res. rewrite Hsel, lbs_hset_t. Intros.
    rename H into Ea, H0 into Hn, H1 into Hhs, H2 into Hi, H3 into Hq. subst ad.
    rewrite prop_true_andp by tauto.
    apply derives_trans with
      (mem_mgr gv * dgroup DENT gv p d' * cm_have am (hb + local_held d') * hset_tbl am (c3_sp k) (c3_set k) tbl *
       (set_full DENT gv Ews (c3_set k) (darg_ddict a0) * darg_res3 DENT gv (c3_par k) (c3_sp k) (lb_d2 k) a0 * R0));
      [cancel | ].
    rewrite <- (HE Hi Hq). cancel.
Qed.

(* ZSTD_getDDict returns NULL *)
Lemma lbs_null :
  fst (getddict_res (c3_dict k)) = nullval -> cur_ddict (dc_dict st) = None ->
  cur_ok3 (lb_d2 k) (c3_set k) nullval -> lbs_concl.
Proof.
  intros Hg Hcd Hcur.
  apply (lbs_gen DA_none (Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k))
           (dict_res (DD3x DENT) gv Ews (dc_dict st))).
  - unfold lb_pre, lb_post. rewrite (lbs_set_res_none DENT gv Ews _ _ Hcd), <- Hset.
    sep_apply (lbs_all_ld DENT gv Ews (c3_set k)). entailer!.
  - intros Hn Hi Hld. unfold lb_facts.
    split; [exact I | ]. split; [simpl; congruence | ]. split; [exact I | ].
    split.
    { intros _. unfold msel_ok. simpl darg_ddict. split; [exact Hcur | ].
      split; [apply writable_readable, writable_Ews | ].
      split; [rewrite lbs_local_none; discriminate | ].
      split; [intros x buf sh dd E; discriminate | ].
      split; [eapply Forall_impl; [ | exact Hsp]; simpl; auto | ].
      rewrite lbs_local_none; discriminate. }
    split; [intros E; congruence | ].
    intros _. split; [exact Hld | ]. intros dd dm Hin. exfalso.
    destruct Hi as [_ [_ [_ [_ [_ [Hp _]]]]]]. apply (lbs_null_notin _ Hp). apply in_map_iff.
    exists (nullval, dd). auto.
  - intros Hi _. rewrite (lbs_set_res_none DENT gv Ews _ _ Hcd), <- Hset, lbs_darg3_none. simpl darg_ddict.
    rewrite lbs_full_notin by (destruct Hi as [_ [_ [_ [_ [_ [Hp _]]]]]]; apply lbs_null_notin; exact Hp).
    apply pred_ext; cancel.
Qed.

(* ZSTD_getDDict returns the local DDict x0 (zstd's copy): it stays in dgroup *)
Lemma lbs_local (x0: ddx) (buf: val) :
  fst (getddict_res (c3_dict k)) = dx_q x0 -> df_local (lb_d2 k) = dx_q x0 ->
  isptr (dx_q x0) -> df_lx (lb_d2 k) = Some (x0, buf) -> ddx_copied x0 = true ->
  cur_ddict (dc_dict st) = None -> dict_res (DD3x DENT) gv Ews (dc_dict st) = emp ->
  cur_ok3 (lb_d2 k) (c3_set k) (dx_q x0) -> lbs_concl.
Proof.
  intros Hg Hl Hq Hlx Hc Hcd Hdr Hcur.
  assert (Hloc: darg_local (lb_d2 k) (DA_ddict x0 buf Ews) = true).
  { unfold darg_local, darg_ddict. rewrite Hl. unfold veqb.
    destruct (Val.eq (dx_q x0) (dx_q x0)); [ | congruence].
    destruct (Val.eq (dx_q x0) nullval) as [E | E]; [rewrite E in Hq; contradiction | reflexivity]. }
  apply (lbs_gen (DA_ddict x0 buf Ews)
     (Forall (fun e => ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k) /\ ~ In (dx_q x0) (map fst (c3_set k)))
     emp).
  - unfold lb_pre, lb_post. rewrite (lbs_set_res_none DENT gv Ews _ _ Hcd), <- Hset.
    rewrite (lbs_dgroup_split DENT gv p _ x0 buf Hl Hq Hlx).
    assert_PROP (~ In (dx_q x0) (map fst (c3_set k))) as Hni.
    { sep_apply (lbs_local_not_in DENT gv Ews x0 buf (c3_set k)). entailer!. }
    sep_apply (lbs_all_ld DENT gv Ews (c3_set k)). entailer!.
  - intros Hn Hi [Hld Hni]. unfold lb_facts.
    split; [exact I | ]. split; [simpl; congruence | ]. split; [simpl; intros Hc'; congruence | ].
    split.
    { intros _. unfold msel_ok. simpl darg_ddict. split; [exact Hcur | ].
      split; [apply writable_readable, writable_Ews | ].
      split; [intros _; exists x0, buf, Ews; split; [reflexivity | exact Hlx] | ].
      split; [intros x' buf' sh' dd' Ea Hin; inv Ea; exfalso; apply Hni; apply in_map_iff; exists (dx_q x', dd'); auto | ].
      split; [eapply Forall_impl; [ | exact Hsp]; simpl; auto | ].
      intros _; exact Hni. }
    split; [intros E; congruence | ].
    intros _. split; [exact Hld | ]. intros dd dm Hin. exfalso. apply Hni. simpl in Hin. apply in_map_iff.
    exists (dx_q x0, dd). auto.
  - intros Hi [Hld Hni]. rewrite Hdr, (lbs_set_res_none DENT gv Ews _ _ Hcd), <- Hset. simpl darg_ddict.
    rewrite (lbs_full_notin DENT gv Ews _ _ Hni).
    unfold darg_res3. rewrite Hsel, Hloc. simpl. rewrite Hc. apply pred_ext; cancel.
Qed.

(* ZSTD_getDDict returns a DDict q of the caller (entry dd in the set if there), the rest of the memory R0 *)
Lemma lbs_dd (q: val) (dd: ddict_st) (R0: mpred) :
  fst (getddict_res (c3_dict k)) = q -> df_local (lb_d2 k) = nullval ->
  (NoDup (map fst (c3_set k)) ->
     dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st) =
     ddict_res (DD3x DENT) gv Ews q dd * set_full DENT gv Ews (c3_set k) q * R0) ->
  (NoDup (map fst (c3_set k)) -> forall dd', In (q, dd') (c3_set k) -> dd' = dd) ->
  cur_ok3 (lb_d2 k) (c3_set k) q -> sddict_ok W dd -> lbs_concl.
Proof.
  intros Hg Hloc Hres Hmem Hcur Hsd.
  assert (Hnl: darg_local (lb_d2 k) (DA_ddict (dd_x q dd) (dd_buf dd) Ews) = false)
    by (apply lbs_local_null; exact Hloc).
  apply (lbs_gen (DA_ddict (dd_x q dd) (dd_buf dd) Ews)
     (ld_rel (dd_bytes dd) (dd_ld dd) /\ (match dd_xref dd with Some p0 => dd_buf dd = p0 | None => True end) /\
      Forall (fun e => fst e <> q -> ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k) /\
      (forall p0, dd_ref dd = Some p0 -> isptr p0)) R0).
  - assert_PROP (c3_set k <> nil /\ hs = set_bytes am (Zlength tbl) /\ hs_inv (c3_set k) tbl) as Hh by apply lbs_pre_hs.
    destruct Hh as [_ [_ Hi]]. pose proof Hi as [_ [_ [_ [Hnd _]]]].
    unfold lb_pre, lb_post.
    apply derives_trans with
      (TT * (dict_res (DD3x DENT) gv Ews (dc_dict st) * set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)));
      [cancel | ].
    rewrite (Hres Hnd). sep_apply (lbs_ddict_res_ptr DENT gv Ews q dd). Intros.
    match goal with H: forall p0, dd_ref dd = Some p0 -> isptr p0 |- _ => rename H into Hptr end.
    rewrite (lbs_ddict_res_darg DENT gv Ews q dd Hptr).
    unfold darg_res, ddict_rep_at, ddict_struct. Intros.
    sep_apply (lbs_full_ld DENT gv Ews (c3_set k) q). Intros. apply prop_right. simpl in *. auto.
  - intros Hn Hi [Hld [Hbuf [Hld1 _]]]. pose proof Hi as [_ [_ [_ [Hnd _]]]]. unfold lb_facts.
    split; [exact I | ]. split; [simpl; congruence | ].
    split.
    { simpl. unfold ddx_copied. simpl. intros Hc Hbn.
      destruct (dd_xref_cases dd) as [(p0 & Er & Ex) | [(Er & Hn' & Ex) | (Er & Hn' & Ex)]];
        rewrite Ex in Hc, Hbuf; try discriminate; [ | contradiction ].
      split; [apply writable_readable, writable_Ews | ].
      unfold sddict_ok in Hsd. rewrite Er in Hsd. destruct Hsd as [Hb Hp]. rewrite Hb, Hbuf.
      apply lbs_ptr_ok; auto. }
    split.
    { intros _. unfold msel_ok. simpl darg_ddict. split; [exact Hcur | ].
      split; [apply writable_readable, writable_Ews | ].
      split; [rewrite Hnl; discriminate | ].
      split.
      - intros x buf sh dd' Ea Hin. injection Ea as E1 E2 E3. subst x buf sh. simpl in Hin.
        rewrite (Hmem Hnd _ Hin). split; reflexivity.
      - split; [eapply Forall_impl; [ | exact Hsp]; simpl; auto | ].
        rewrite Hnl; discriminate. }
    split; [intros E; congruence | ].
    intros _. split.
    + rewrite Forall_forall in *. intros [q1 dd1] Hin1. destruct (Val.eq q1 q) as [E | E].
      * subst q1. simpl. rewrite (Hmem Hnd _ Hin1). exact Hld.
      * apply (Hld1 _ Hin1). simpl. exact E.
    + intros dd' dm Hin Ha. simpl in Hin. rewrite (Hmem Hnd _ Hin) in Ha. simpl. unfold ddx_model. simpl.
      apply ld_rel_auto_some; auto.
  - intros Hi (_ & _ & _ & Hptr). pose proof Hi as [_ [_ [_ [Hnd _]]]]. rewrite (Hres Hnd). simpl darg_ddict.
    rewrite lbs_darg3_nonlocal by exact Hnl. rewrite (lbs_ddict_res_darg DENT gv Ews q dd Hptr).
    apply pred_ext; cancel.
Qed.

End LbsCases.

Lemma lbs_nodup_unique {A: Type} (l: list (val * A)) q a b :
  NoDup (map fst l) -> In (q, a) l -> In (q, b) l -> a = b.
Proof.
  induction l as [ | e l IH]; intros Hnd Ha Hb; [contradiction | ].
  simpl in Hnd. inv Hnd. destruct Ha as [Ea | Ha]; destruct Hb as [Eb | Hb].
  - subst e. inv Eb. reflexivity.
  - subst e. exfalso. apply H1. apply in_map_iff. exists (q, b); auto.
  - subst e. exfalso. apply H1. apply in_map_iff. exists (q, a); auto.
  - auto.
Qed.

(* the lending: before the call, the resources give an argument ad (the DDict getDDict returned) and a rest Rf ad;
   after it, with the fields d' the call returns, they come back *)
Lemma lend_B : lend_use_ok ->
  forall (DENT: dent_pred) (gv: globals) (p: val) (W: list ptr_witness) (st: dctx_st) (k: cst3) (tbl: list val)
         (shd: share) (cap: Z) (dst: val) (am: option cmem) (hb hs: Z),
    c3_set k = dc_set st -> dict_rel3 st (c3_dict k) -> set_cur_ok st -> stream_dict_ok W st -> dd_bytes_ok st ->
    writable_share shd -> buf_ok W shd cap dst -> 0 <= cap ->
    exists Rf: darg -> mpred,
      (lb_pre DENT gv p st k tbl am hb hs |--
         EX ad: darg, !! lb_facts W st k shd cap dst ad && (lb_mid DENT gv p k tbl am hb (lb_d2 k) ad * Rf ad)) /\
      (forall ad d', lb_facts W st k shd cap dst ad ->
         (d' = lb_d2 k \/ (sel_on (c3_par k) (c3_sp k) = true /\
                           exists q, In q (map fst (c3_set k)) /\ d' = switch_fields q)) ->
         lb_mid DENT gv p k tbl am hb d' ad * Rf ad |-- lb_post DENT gv p st k tbl am hb hs d').
Proof.
  intros Huse DENT gv p W st k tbl shd cap dst am hb hs Hset Hdr Hcur Hsd Hddb Hw Hbuf Hcap.
  change (lbs_concl DENT gv p W st k tbl shd cap dst am hb hs).
  destruct (sel_on (c3_par k) (c3_sp k)) eqn:Hsel.
  2:{ (* without the selection: lend_use_ok *)
    exists (fun ad => mem_mgr gv * cm_have am (hb + local_held (lb_d2 k)) * hset_t am (c3_sp k) (c3_set k) hs tbl *
              (darg_res DENT gv ad -*
               (dgroup DENT gv p (lb_d2 k) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
                set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st)))).
    split.
    - unfold lb_pre, lb_post.
      apply derives_trans with
        (mem_mgr gv * cm_have am (hb + local_held (lb_d2 k)) * hset_t am (c3_sp k) (c3_set k) hs tbl *
         (dgroup DENT gv p (lb_d2 k) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
          set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))); [cancel | ].
      unfold lb_d2. sep_apply (Huse DENT gv p W st k shd cap dst Hset Hdr Hcur Hsd Hddb Hw Hbuf Hcap).
      Intros ad. Exists ad.
      apply andp_right.
      + apply prop_right. unfold lb_facts.
        refine (conj H (conj H0 (conj H1 (conj _ (conj (fun _ => H2) _))))); intros E; congruence.
      + unfold lb_mid. rewrite lbs_msel_off, lbs_darg3_off by auto. unfold lb_d2. cancel.
    - intros ad d' _ [E | [E _]]; [subst d' | congruence].
      unfold lb_mid, lb_post. rewrite lbs_msel_off, lbs_darg3_off by auto. rewrite emp_sepcon.
      apply derives_trans with
        (mem_mgr gv * cm_have am (hb + local_held (lb_d2 k)) * hset_t am (c3_sp k) (c3_set k) hs tbl *
         (darg_res DENT gv ad *
          (darg_res DENT gv ad -*
           (dgroup DENT gv p (lb_d2 k) * dict_res (DD3x DENT) gv Ews (dc_dict st) *
            set_res (DD3x DENT) gv Ews (dc_set st) (dc_dict st))))); [cancel | ].
      sep_apply (modus_ponens_wand (darg_res DENT gv ad)). cancel. }
  (* with the selection *)
  assert (Hsp: Forall (fun e => ddict_buf_ok0 W Ews (snd e) shd cap dst) (c3_set k)).
  { destruct Hsd as [_ [Hs _]]. rewrite Hset. eapply Forall_impl; [ | exact Hs]. intros e He.
    apply lbs_buf_ok; auto. }
  destruct Hdr as [Hdr | [Hn [Hl [Hu [Hlx Hin]]]]].
  - destruct (dc_dict st) as [[dsrc raw once b] | ] eqn:Hdd.
    2:{ (* no dictionary *)
      simpl in Hdr. destruct Hdr as [Hu _].
      apply lbs_null; try assumption.
      - unfold getddict_res. rewrite Hu. reflexivity.
      - rewrite Hdd. reflexivity.
      - unfold lb_d2, getddict_res. rewrite Hu. simpl. split; [right; left; reflexivity | left; reflexivity]. }
    destruct dsrc as [pk | | q dd]; simpl in Hdr.
    + (* by reference: not in a stream *)
      destruct Hsd as [Hd _]. rewrite Hdd in Hd. simpl in Hd. destruct Hd as [_ []].
    + (* the context's own copy *)
      destruct Hdr as [Ho Hdr]. destruct (Zlength b =? 0) eqn:Hb0.
      * apply lbs_null; try assumption.
        -- rewrite Hdr. reflexivity.
        -- rewrite Hdd. reflexivity.
        -- unfold lb_d2. rewrite Hdr. simpl. split; [right; left; reflexivity | left; reflexivity].
      * destruct Hdr as [buf [ld [am0 [Hq [Hdk [Hu Hlx]]]]]].
        set (x0 := {| dx_q := df_local (c3_dict k); dx_bytes := b; dx_ref := None; dx_raw := raw; dx_ld := ld;
                      dx_mem := am0 |}) in *.
        assert (Hgd: getddict_res (c3_dict k) = (df_local (c3_dict k), c3_dict k))
          by (unfold getddict_res; rewrite Hu, Hdk; reflexivity).
        apply lbs_local with (x0 := x0) (buf := buf); try assumption; unfold lb_d2; rewrite ?Hgd; simpl;
          first [reflexivity | assumption | (rewrite Hdd; reflexivity) |
                 (split; [left; exact Hu | right; left; exact Hdk])].
    + (* a DDict *)
      destruct Hdr as [Hr [Ho [Hq [Hl [Hdk [Hu _]]]]]].
      assert (Hgd: getddict_res (c3_dict k) = (q, c3_dict k))
        by (unfold getddict_res; rewrite Hu, Hdk; reflexivity).
      apply lbs_dd with (q := q) (dd := dd) (R0 := emp); try assumption.
      * rewrite Hgd. reflexivity.
      * unfold lb_d2. rewrite Hgd. exact Hl.
      * intros _. rewrite Hdd. simpl dict_res. rewrite (lbs_set_res_some DENT gv Ews _ _ q) by reflexivity.
        rewrite <- Hset, sepcon_emp. reflexivity.
      * intros _ dd' Hin. rewrite Hset in Hin. eapply Hcur; [exact Hdd | reflexivity | exact Hin].
      * unfold lb_d2. rewrite Hgd. simpl. split; [left; exact Hu | right; right; right; exact Hdk].
      * destruct Hsd as [Hd _]. rewrite Hdd in Hd. simpl in Hd. destruct Hd as [_ Hd]. exact Hd.
  - (* switched to a DDict of the set *)
    apply in_map_iff in Hin. destruct Hin as [[q dd] [Eq Hin]]. simpl in Eq.
    assert (Hgd: getddict_res (c3_dict k) = (df_ddict (c3_dict k), c3_dict k))
      by (unfold getddict_res; rewrite Hu; reflexivity).
    destruct (lbs_regroup DENT gv Ews (dc_set st) (dc_dict st) q dd) as [R0 HR0].
    { intros dr q0 dd0 dd' E1 E2 Hin2. exact (Hcur dr q0 dd0 dd' E1 E2 Hin2). }
    apply lbs_dd with (q := q) (dd := dd) (R0 := R0); try assumption.
    + rewrite Hgd. simpl. symmetry. exact Eq.
    + unfold lb_d2. rewrite Hgd. exact Hl.
    + intros Hnd. rewrite Hset in Hnd. rewrite (HR0 Hnd Hin), <- Hset. reflexivity.
    + intros Hnd dd' Hin2. rewrite Hset in Hnd, Hin2. exact (lbs_nodup_unique _ q dd' dd Hnd Hin2 Hin).
    + unfold lb_d2. rewrite Hgd. simpl. split; [left; exact Hu | right; right; left].
      rewrite <- Eq, Hset. apply in_map_iff. exists (q, dd). auto.
    + destruct Hsd as [_ [Hs _]]. rewrite Forall_forall in Hs. exact (Hs _ Hin).
Qed.

End CM_LH3Bsel_1.
