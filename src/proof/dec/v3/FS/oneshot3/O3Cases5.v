(* FS3 one-shot: the lending of ZSTD_decompressDCtx WITH the selection (refMultipleDDicts and a set):
   generic cases (no DDict, the local DDict, a DDict of the caller) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Valid Zstd.proof.dec.v3.FS.oneshot3.O3Cases1 Zstd.proof.dec.v3.FS.oneshot3.O3Cases4.
Local Open Scope logic.

Section CM_O3Cases5_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma darg_res3_none DENT gv pr sp d : darg_res3 DENT gv pr sp d DA_none = emp.
Proof. unfold darg_res3. destruct (andb _ _); reflexivity. Qed.

Lemma darg_local_null d a : df_local d = nullval -> darg_local d a = false.
Proof.
  intros H. unfold darg_local. rewrite H. unfold veqb at 2.
  destruct (Val.eq nullval nullval); [ | congruence]. apply andb_false_r.
Qed.

Lemma darg_res3_nonlocal DENT gv pr sp d a :
  darg_local d a = false -> darg_res3 DENT gv pr sp d a = darg_res DENT gv a.
Proof. intros H. unfold darg_res3. rewrite H, andb_false_r. reflexivity. Qed.

Lemma darg_local_none d : darg_local d DA_none = false.
Proof.
  unfold darg_local, darg_ddict, veqb.
  destruct (Val.eq nullval (df_local d)) as [E | E]; [ | reflexivity].
  rewrite <- E. destruct (Val.eq nullval nullval); [reflexivity | congruence].
Qed.

Lemma null_notin (l: list (val * ddict_st)) : Forall (fun e => isptr (fst e)) l -> ~ In nullval (map fst l).
Proof.
  intros H Hin. apply in_map_iff in Hin. destruct Hin as [e [E Hin]].
  rewrite Forall_forall in H. specialize (H e Hin). rewrite E in H. exact H.
Qed.

Lemma hset_rep_on (am: option cmem) (sp: val) (l: list (val * ddict_st)) (hs: Z) :
  sp <> nullval ->
  hset_rep am sp l hs = !! (l <> nil) && EX tbl: list val, !! (hs = set_bytes am (Zlength tbl)) && hset_tbl am sp l tbl.
Proof. intros H. rewrite (hset_rep_at am sp l hs H). reflexivity. Qed.

Lemma hset_tbl_inv am sp l tbl : hset_tbl am sp l tbl |-- !! hs_inv l tbl.
Proof. unfold hset_tbl. Intros tp. apply prop_right. auto. Qed.

(* the local DDict is not one of the set's (zstd's own: both would hold its dictID field) *)
Lemma local_not_in_set DENT gv shk x buf (l: list (val * ddict_st)) :
  ddict_rep_at DENT gv x buf * all_res DENT gv shk l |-- !! (~ In (dx_q x) (map fst l)).
Proof.
  induction l as [ | e l IH].
  - apply prop_right. simpl. tauto.
  - unfold all_res. simpl fold_right.
    destruct (Val.eq (fst e) (dx_q x)) as [E | E].
    + unfold ddict_res, DD3x. rewrite <- DD3_valid. unfold DD3_of. rewrite E.
      unfold ddict_rep_at, ddict_struct. Intros. simpl dx_q.
      apply derives_trans with
        (field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) (dx_q x) *
         field_at_ Ews (Tstruct _ZSTD_DDict_s noattr) (DOT _dictID) (dx_q x) * TT).
      * cancel.
      * eapply derives_trans; [apply sepcon_derives; [apply field_at_conflict; [auto | simpl; lia] | apply derives_refl] | ].
        rewrite FF_sepcon. apply FF_left.
    + fold (all_res DENT gv shk l).
      assert_PROP (~ In (dx_q x) (map fst l)) as Hn.
      { sep_apply IH. entailer!. }
      apply prop_right. simpl. intros [H' | H']; [congruence | tauto].
Qed.

Section Cases.
Variable DENT : dent_pred.
Variables (gv: globals) (p: val) (W: list ptr_witness) (shk shd: share) (cap: Z) (dst: val) (s: list Z)
          (st: dctx_st) (k: cst3) (am: option cmem) (hb hs: Z).

Hypothesis Hsel : sel_on (c3_par k) (c3_sp k) = true.
Hypothesis Hpar : c3_par k = dc_par st.
Hypothesis Hset : c3_set k = dc_set st.
Hypothesis Hhs : hset_props (c3_sp k) (c3_set k).
Hypothesis Hptrs : Forall (fun e => ddict_buf_ok W shk (snd e) shd cap dst) (c3_set k).
Hypothesis SH : readable_share shk.

Lemma sel_sp_ne : c3_sp k <> nullval.
Proof.
  intros E. unfold sel_on in Hsel. rewrite E in Hsel. unfold veqb in Hsel.
  destruct (Val.eq nullval nullval); [ | congruence]. rewrite andb_false_r in Hsel. discriminate.
Qed.

Lemma sel_set_ne : c3_set k <> nil.
Proof. intros E. destruct Hhs as [[_ H] _]. apply sel_sp_ne. apply H. exact E. Qed.

Lemma rel_switch q : In q (map fst (c3_set k)) -> dict_rel3 (after_use st) (switch_fields q).
Proof.
  intros H. right. destruct (after_use_parts st) as [_ [_ [E3 _]]]. rewrite E3, <- Hset.
  split; [apply sel_set_ne | ]. unfold dict_switched, switch_fields; simpl. auto.
Qed.

Lemma rel_after d1 d' :
  dict_rel3 (after_use st) d1 ->
  (d' = d1 \/ (sel_on (c3_par k) (c3_sp k) = true /\ exists q, In q (map fst (c3_set k)) /\ d' = switch_fields q)) ->
  dict_rel3 (after_use st) d'.
Proof.
  intros H [E | [_ [q [Hq E]]]]; subst; auto. apply rel_switch; auto.
Qed.

(* the hset group, with the selection: the set's table *)
Lemma hset_back tbl : hs = set_bytes am (Zlength tbl) ->
  hset_tbl am (c3_sp k) (c3_set k) tbl |-- hset_rep am (c3_sp k) (c3_set k) hs.
Proof.
  intros E. rewrite (hset_rep_on _ _ _ _ sel_sp_ne). rewrite prop_true_andp by apply sel_set_ne. Exists tbl. entailer!.
Qed.

(* ZSTD_getDDict returns a DDict q of the caller, of entry dd in the set if there *)
Lemma lend_sel_dd (q: val) (dd: ddict_st) (R0: mpred) :
  hs_probe_ok ->
  fst (getddict_res (c3_dict k)) = q -> df_local (snd (getddict_res (c3_dict k))) = nullval ->
  dict_res (DD3x DENT) gv shk (dc_dict st) * set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st) =
    ddict_res (DD3x DENT) gv shk q dd * set_full DENT gv shk (c3_set k) q * R0 ->
  (forall dd', In (q, dd') (c3_set k) -> dd' = dd) ->
  cur_ok3 (snd (getddict_res (c3_dict k))) (c3_set k) q ->
  (forall p0, dd_ref dd = Some p0 -> dict_ptr_ok W shk (Zlength (dd_bytes dd)) p0 shd cap dst) ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hprobe Hg Hloc Hres Hmem Hcur Hptr Hrel.
  set (x := dd_x q dd). set (buf := dd_buf dd). set (d1 := snd (getddict_res (c3_dict k))).
  exists (fun w => !! (fst w = DA_ddict x buf shk /\ hs = set_bytes am (Zlength (snd w)) /\
                       match dd_ref dd with Some p0 => isptr p0 | None => True end) && R0).
  split.
  - unfold lend_pre. rewrite (hset_rep_on _ _ _ _ sel_sp_ne). Intros tbl.
    assert_PROP (hs_inv (c3_set k) tbl) as Hinv.
    { sep_apply (hset_tbl_inv am (c3_sp k) (c3_set k) tbl). entailer!. }
    rewrite !sepcon_assoc. rewrite Hres.
    assert_PROP (Forall (fun e => fst e <> q -> ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k)) as Hld1.
    { sep_apply (set_full_ld DENT gv shk (c3_set k) q). entailer!. }
    unfold ddict_res at 1, DD3x. rewrite <- DD3_valid. unfold DD3_of. fold x. fold buf.
    assert_PROP (ld_rel (dx_bytes x) (dx_ld x) /\ isptr (dx_q x) /\
                 match dx_ref x with Some p0 => buf = p0 | None => True end) as Hx.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    destruct Hx as [Hld [Hq Hbuf]].
    assert_PROP (match dd_ref dd with Some p0 => isptr p0 | None => True end) as Hrp.
    { destruct (dd_ref dd); entailer!. }
    pose proof (dd_darg_bytes shk q dd Hrp Hbuf) as Hm0. fold x buf in Hm0.
    Exists (DA_ddict x buf shk, tbl). unfold lend_mid, msel_res. rewrite Hsel.
    rewrite darg_res3_nonlocal by (apply darg_local_null; exact Hloc). simpl darg_res.
    apply andp_right; [apply prop_right | rewrite prop_true_andp by (repeat split; auto)].
    2:{ rewrite Hm0. simpl darg_ddict. change (dx_q x) with q. change (dx_bytes x) with (dd_bytes dd). cancel. }
    unfold lend_ok. split; [exact I | ]. split; [simpl; rewrite Hg; reflexivity | ].
    split.
    { apply dd_darg_ok3; [intros p0 E; split; [exact SH | apply Hptr; exact E] | exact Hbuf]. }
    split.
    { intros _. split; [exact Hcur | ]. split; [exact SH | ].
      split; [rewrite darg_local_null by exact Hloc; discriminate | ].
      split.
      - intros x' buf' sh' dd' Ea Hin. inv Ea. simpl in Hin. rewrite (Hmem _ Hin). split; reflexivity.
      - split; [eapply Forall_impl; [ | exact Hptrs]; intros [q0 dd0] Hb _; unfold ddict_buf_ok0; unfold ddict_buf_ok in Hb; simpl in Hb |- *; destruct (dd_ref dd0); [left; exact Hb | exact I] | ].
        rewrite darg_local_null by exact Hloc; discriminate. }
    split; [ | split; [intros E; exfalso; apply sel_set_ne; rewrite Hset; exact E |
                       simpl; intros E; change (dx_q x) with q in Hq; rewrite E in Hq; contradiction]].
    intros r out Hb H1 H2 H3.
    apply (model_sel st k tbl (darg_model (DA_ddict x buf shk))); auto.
    + rewrite Forall_forall in *. intros [q1 dd1] Hin1. destruct (Val.eq q1 q) as [E | E].
      * subst q1. rewrite (Hmem _ Hin1). exact Hld.
      * apply (Hld1 _ Hin1). simpl. exact E.
    + apply H3; [exact Hsel | ]. simpl. intros E. simpl in Hq. rewrite E in Hq. exact Hq.
  - intros [a tbl] d' Hok Hd'. split; [eapply rel_after; eauto | ].
    unfold lend_mid, lend_post. Intros. simpl in *. subst a.
    unfold msel_res. rewrite Hsel.
    rewrite darg_res3_nonlocal by (apply darg_local_null; exact Hloc). simpl darg_res.
    sep_apply (hset_back tbl ltac:(assumption)).
    rewrite !sepcon_assoc. rewrite Hres.
    unfold ddict_res at 1, DD3x. rewrite <- DD3_valid. unfold DD3_of. fold x. fold buf.
    assert_PROP (match dx_ref x with Some p0 => buf = p0 | None => True end) as Hbuf.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    match goal with H: match dd_ref dd with Some _ => _ | None => True end |- _ => rename H into Hrp end.
    pose proof (dd_darg_bytes shk q dd Hrp Hbuf) as Hm0. fold x buf in Hm0. rewrite Hm0. cancel; apply derives_refl.
Qed.

(* ZSTD_getDDict returns NULL (no DDict: no selection in zstd) *)
Lemma lend_sel_null :
  fst (getddict_res (c3_dict k)) = nullval -> cur_ddict (dc_dict st) = None ->
  cur_ok3 (snd (getddict_res (c3_dict k))) (c3_set k) nullval ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  (forall dr, dc_dict st = Some dr ->
     match dr_src dr with DSDDict _ _ => false | _ => Nat.eqb (length (dr_bytes dr)) 0 end = true) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hg Hcd Hcur Hrel Hd7.
  assert (Hfull: set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st) = set_full DENT gv shk (c3_set k) nullval).
  { rewrite set_res_none by exact Hcd. rewrite Hset. symmetry. apply set_full_notin.
    destruct Hhs as [_ [Hp _]]. rewrite Hset in Hp. apply null_notin; auto. }
  exists (fun w => !! (fst w = DA_none /\ hs = set_bytes am (Zlength (snd w))) && dict_res (DD3x DENT) gv shk (dc_dict st)).
  split.
  - unfold lend_pre. rewrite (hset_rep_on _ _ _ _ sel_sp_ne). Intros tbl. rewrite Hfull.
    Exists (DA_none, tbl). unfold lend_mid, msel_res. rewrite Hsel, darg_res3_none. simpl darg_ddict.
    apply andp_right; [apply prop_right | rewrite prop_true_andp by (split; auto); cancel].
    unfold lend_ok. split; [exact I | ]. split; [simpl; rewrite Hg; reflexivity | ]. split; [exact I | ].
    split.
    { intros _. split; [exact Hcur | ]. split; [exact SH | ].
      split; [rewrite darg_local_none; discriminate | ].
      split; [intros x' buf' sh' dd' Ea; discriminate | ].
      split; [eapply Forall_impl; [ | exact Hptrs]; intros [q0 dd0] Hb _; unfold ddict_buf_ok0; unfold ddict_buf_ok in Hb; simpl in Hb |- *; destruct (dd_ref dd0); [left; exact Hb | exact I] | ].
      rewrite darg_local_none; discriminate. }
    split; [ | split; [intros E; exfalso; apply sel_set_ne; rewrite Hset; exact E | intros _; reflexivity]].
    intros r out Hb H1 H2 H3. apply model_null; auto.
    + rewrite <- Hset. apply sel_set_ne.
    + rewrite <- Hpar. apply H2. right. reflexivity.
  - intros [a tbl] d' Hok Hd'. split; [eapply rel_after; eauto | ].
    unfold lend_mid, lend_post. Intros. simpl in *. subst a.
    unfold msel_res. rewrite Hsel, darg_res3_none. simpl darg_ddict.
    sep_apply (hset_back tbl ltac:(assumption)). rewrite Hfull. cancel.
Qed.

(* ZSTD_getDDict returns the local DDict x0: it stays in the dictionary group, its caller's bytes are lent *)
Lemma lend_sel_local (x0: ddx) (buf: val) :
  hs_probe_ok ->
  fst (getddict_res (c3_dict k)) = dx_q x0 -> df_local (snd (getddict_res (c3_dict k))) = dx_q x0 ->
  isptr (dx_q x0) -> df_lx (snd (getddict_res (c3_dict k))) = Some (x0, buf) ->
  cur_ddict (dc_dict st) = None ->
  dict_res (DD3x DENT) gv shk (dc_dict st) =
    (if ddx_copied x0 then emp
     else data_at shk (tarray tuchar (Zlength (dx_bytes x0))) (zbytes (dx_bytes x0)) buf) ->
  (ddx_copied x0 = false -> readable_share shk /\ dict_ptr_ok W shk (Zlength (dx_bytes x0)) buf shd cap dst) ->
  cur_ok3 (snd (getddict_res (c3_dict k))) (c3_set k) (dx_q x0) ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hprobe Hg Hl Hq Hlx Hcd Hdr Hptr Hcur Hrel.
  set (d1 := snd (getddict_res (c3_dict k))).
  assert (Hloc: darg_local d1 (DA_ddict x0 buf shk) = true).
  { unfold darg_local, darg_ddict. fold d1 in Hl. rewrite Hl. unfold veqb.
    destruct (Val.eq (dx_q x0) (dx_q x0)); [ | congruence].
    destruct (Val.eq (dx_q x0) nullval) as [E | E]; [rewrite E in Hq; contradiction | reflexivity]. }
  (* the caller's bytes of a DDict by reference: darg_res3 has them as bytes_at, at a pointer *)
  assert (Hres3: (ddx_copied x0 = false -> isptr buf) ->
                 darg_res3 DENT gv (c3_par k) (c3_sp k) d1 (DA_ddict x0 buf shk) =
                 dict_res (DD3x DENT) gv shk (dc_dict st)).
  { intros Hp. unfold darg_res3. rewrite Hsel, Hloc. simpl. rewrite Hdr.
    destruct (ddx_copied x0); [reflexivity | apply bytes_at_ptr; auto]. }
  exists (fun w => !! (fst w = DA_ddict x0 buf shk /\ ~ In (dx_q x0) (map fst (c3_set k)) /\
                      hs = set_bytes am (Zlength (snd w)) /\ (ddx_copied x0 = false -> isptr buf)) && emp).
  split.
  - unfold lend_pre. rewrite (hset_rep_on _ _ _ _ sel_sp_ne). Intros tbl.
    assert_PROP (hs_inv (c3_set k) tbl) as Hinv.
    { sep_apply (hset_tbl_inv am (c3_sp k) (c3_set k) tbl). entailer!. }
    rewrite (set_res_none DENT gv shk _ _ Hcd), <- Hset.
    assert_PROP (~ In (dx_q x0) (map fst (c3_set k))) as Hni.
    { fold d1. rewrite (dgroup_split DENT gv p d1 x0 buf Hl Hq Hlx).
      sep_apply (local_not_in_set DENT gv shk x0 buf (c3_set k)). entailer!. }
    assert_PROP (Forall (fun e => fst e <> dx_q x0 -> ld_rel (dd_bytes (snd e)) (dd_ld (snd e))) (c3_set k)) as Hld1.
    { rewrite <- (set_full_notin DENT gv shk _ _ Hni). sep_apply (set_full_ld DENT gv shk (c3_set k) (dx_q x0)).
      entailer!. }
    rewrite <- (set_full_notin DENT gv shk _ _ Hni).
    assert_PROP (ddx_copied x0 = false -> isptr buf) as Hbp.
    { rewrite Hdr. destruct (ddx_copied x0); [apply prop_right; discriminate | entailer!]. }
    Exists (DA_ddict x0 buf shk, tbl). unfold lend_mid. fold d1. rewrite (Hres3 Hbp). unfold msel_res. rewrite Hsel.
    simpl darg_ddict.
    apply andp_right; [apply prop_right | rewrite prop_true_andp by (repeat split; auto); cancel].
    unfold lend_ok. fold d1. split; [exact I | ]. split; [simpl; rewrite Hg; reflexivity | ]. split; [intros Hc _; destruct (Hptr Hc); split; [assumption | left; assumption] | ].
    split.
    { intros _. split; [exact Hcur | ]. split; [exact SH | ].
      split; [intros _; exists x0, buf, shk; split; [reflexivity | exact Hlx] | ].
      split; [intros x' buf' sh' dd' Ea Hin; inv Ea; exfalso; apply Hni; apply in_map_iff; exists (dx_q x', dd'); auto | ].
      split; [eapply Forall_impl; [ | exact Hptrs]; intros [q0 dd0] Hb _; unfold ddict_buf_ok0; unfold ddict_buf_ok in Hb; simpl in Hb |- *; destruct (dd_ref dd0); [left; exact Hb | exact I] | ].
      intros _. exact Hni. }
    split; [ | split; [intros E; exfalso; apply sel_set_ne; rewrite Hset; exact E |
                       simpl; intros E; rewrite E in Hq; contradiction]].
    intros r out Hb H1 H2 H3.
    apply (model_sel st k tbl (darg_model (DA_ddict x0 buf shk))); auto.
    + rewrite Forall_forall in *. intros e Hin. apply (Hld1 e Hin). intros E. apply Hni.
      rewrite <- E. apply in_map; auto.
    + apply H3; [exact Hsel | ]. simpl. intros E. rewrite E in Hq. exact Hq.
  - intros [a tbl] d' Hok Hd'. split; [eapply rel_after; eauto | ].
    unfold lend_mid, lend_post. Intros. simpl in *.
    match goal with H: ~ In (dx_q x0) _ |- _ => rename H into Hni end.
    match goal with H: ddx_copied x0 = false -> isptr buf |- _ => rename H into Hbp end.
    match goal with H: a = DA_ddict _ _ _ |- _ => subst a end. fold d1. rewrite (Hres3 Hbp).
    unfold msel_res. rewrite Hsel. simpl darg_ddict.
    sep_apply (hset_back tbl ltac:(assumption)).
    rewrite (set_res_none DENT gv shk _ _ Hcd), <- Hset, <- (set_full_notin DENT gv shk _ _ Hni). cancel.
Qed.

End Cases.

End CM_O3Cases5_1.
