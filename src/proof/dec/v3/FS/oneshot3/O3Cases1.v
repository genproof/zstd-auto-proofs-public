(* FS3 one-shot: the lending of ZSTD_decompressDCtx (O3DCtxDef.dctx_lend) without the selection:
   generic cases (no DDict, the local DDict, a DDict the caller holds) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3 Zstd.proof.dec.v3.FS.oneshot3.O3Base Zstd.proof.dec.v3.FS.oneshot3.O3DCtxDef Zstd.proof.dec.v3.FS.oneshot3.O3Valid Zstd.proof.dec.v3.FS.oneshot3.O3ModelWalk.
Require Import Zstd.proof.zstd.Spec_codes_facts.
Local Open Scope logic.

Section CM_O3Cases1_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Definition dgroup_f (p: val) (d: dfields) : mpred :=
  field_at Ews t_dctx (DOT _ddictLocal) (df_local d) p *
  field_at Ews t_dctx (DOT _ddict) (df_ddict d) p *
  field_at Ews t_dctx (DOT _dictUses) (Vint (Int.repr (df_uses d))) p.

Lemma dgroup_split DENT gv p d x buf :
  df_local d = dx_q x -> isptr (dx_q x) -> df_lx d = Some (x, buf) ->
  dgroup DENT gv p d = dgroup_f p d * ddict_rep_at DENT gv x buf.
Proof.
  intros H1 H2 H3. unfold dgroup, dgroup_f, local_rep. rewrite H1, H3.
  rewrite if_false by (destruct (dx_q x); simpl in *; try contradiction; discriminate).
  rewrite prop_true_andp by auto. reflexivity.
Qed.

(* the claims without the selection: the context's dictionary, or with a set (parameter off) nothing beyond the
   empty selection's *)
Lemma model_off (st: dctx_st) (k: cst3) (dm: dict_model) (s: list Z) (cap r: Z) (out: list val) :
  sel_on (c3_par k) (c3_sp k) = false -> c3_par k = dc_par st -> c3_set k = dc_set st ->
  hset_props (c3_sp k) (c3_set k) ->
  (dc_set st = nil -> oneshot_ok (dmode_of (dc_par st)) (Some dm) s cap r out ->
     oneshot_ok (dmode_of (dc_par st)) (dictref_model (dc_dict st)) s cap r out) ->
  oneshot_ok (dmode_of (c3_par k)) (Some dm) s cap r out -> oneshot_dctx st s cap r out.
Proof.
  intros Hsel Hpar Hset [Hsp _] Hm Ho. rewrite Hpar in Ho.
  unfold oneshot_dctx. destruct (dc_set st) as [ | e l] eqn:E; [apply Hm; auto | ].
  assert (Hm1: (dp_multi (dc_par st) =? 1) = false).
  { rewrite <- Hpar. unfold sel_on in Hsel. rewrite Hset in Hsp.
    destruct (veqb (c3_sp k) nullval) eqn:Ev.
    - unfold veqb in Ev. destruct (Val.eq (c3_sp k) nullval) as [Eq | ]; [ | discriminate].
      apply Hsp in Eq. discriminate.
    - rewrite andb_true_r in Hsel. exact Hsel. }
  unfold st_sel. rewrite E. destruct (dc_dict st); [rewrite Hm1; simpl | ];
    apply (proj1 (proj2 o3_walk_facts) _ dm); exact Ho.
Qed.

(* zstd's loading of a dictionary (C-result form) gives the error codes of the model's where the model loads, and
   there are none to give where it does not (O3Base.oneshot_ok_c3 for the codes) *)
Lemma oneshot_codes_c3 (md: dmode) (b: list Z) ores s cap r :
  0 <= cap -> ld_rel b ores -> oneshot_codes md sel_none (dict_auto_c b ores) s cap r ->
  oneshot_codes md sel_none (dict_auto b) s cap r.
Proof.
  intros Hc HL H. destruct (dict_auto b) as [dm|] eqn:E.
  - rewrite (ld_rel_auto_some _ _ _ HL E) in H. exact H.
  - apply oneshot_codes_none. exact Hc.
Qed.

(* the darg of a DDict is described *)
Lemma ddx_model_some DENT gv x buf : ddict_rep_at DENT gv x buf |-- !! (exists dm, ddx_model x = Some dm).
Proof.
  unfold ddict_rep_at, ddict_struct. Intros. apply prop_right.
  unfold ddx_model. destruct (dx_raw x); [eauto | ].
  destruct (dict_auto_c (dx_bytes x) (dx_ld x)) eqn:E; eauto.
  match goal with H: true = true \/ _ |- _ => idtac | H: false = true \/ _ |- _ => destruct H as [H | H]; [discriminate | contradiction] end.
Qed.

Section Cases.
Variable DENT : dent_pred.
Variables (gv: globals) (p: val) (W: list ptr_witness) (shk shd: share) (cap: Z) (dst: val) (s: list Z)
          (st: dctx_st) (k: cst3) (am: option cmem) (hb hs: Z).

Hypothesis Hset : c3_set k = dc_set st.
Hypothesis Hhs : hset_props (c3_sp k) (c3_set k).

(* ZSTD_getDDict returns NULL: no dictionary argument, the context's dictionary memory stays aside *)
Lemma lend_null :
  sel_on (c3_par k) (c3_sp k) = false -> c3_par k = dc_par st ->
  fst (getddict_res (c3_dict k)) = nullval ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  (dc_set st = nil -> forall md r out, oneshot_ok md (Some no_dict) s cap r out ->
     oneshot_ok md (dictref_model (dc_dict st)) s cap r out) ->
  (dc_set st = nil -> forall md r, oneshot_codes md sel_none (Some no_dict) s cap r ->
     oneshot_codes md sel_none (dictref_model (dc_dict st)) s cap r) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hsel Hpar Hg Hrel Hm Hmc.
  exists (fun w => !! (w = (DA_none, @nil val)) &&
            (mem_mgr gv * dgroup DENT gv p (snd (getddict_res (c3_dict k))) * cm_have am (hb + local_held (snd (getddict_res (c3_dict k)))) *
             hset_rep am (c3_sp k) (c3_set k) hs *
             dict_res (DD3x DENT) gv shk (dc_dict st) * set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))).
  split.
  - unfold lend_pre. Exists (DA_none, @nil val). unfold lend_mid.
    rewrite msel_res_off, darg_res3_off by auto. simpl darg_res.
    apply andp_right; [apply prop_right | rewrite prop_true_andp by auto; cancel].
    unfold lend_ok. split; [exact I | ]. split; [rewrite Hg; reflexivity | ]. split; [exact I | ].
    split; [intros; congruence | ].
    split; [ | split; [intros E r Hc; rewrite <- Hpar; apply Hmc; auto; apply Hc; left; exact Hsel | intros _; reflexivity]].
    intros r out Hb H1 H2 H3. apply (model_off st k no_dict); auto.
  - intros w d' Hok Hd'. destruct Hd' as [E | [Hs _]]; [subst d' | congruence].
    split; [exact Hrel | ].
    unfold lend_mid, lend_post. Intros. subst w. rewrite msel_res_off, darg_res3_off by auto. simpl darg_res.
    cancel.
Qed.

(* ZSTD_getDDict returns the local DDict x0 (content at buf): it is lent from the dictionary group, with the
   caller's bytes when it refers to them *)
Lemma lend_local (x0: ddx) (buf: val) :
  sel_on (c3_par k) (c3_sp k) = false -> c3_par k = dc_par st ->
  fst (getddict_res (c3_dict k)) = dx_q x0 -> df_local (snd (getddict_res (c3_dict k))) = dx_q x0 ->
  isptr (dx_q x0) -> df_lx (snd (getddict_res (c3_dict k))) = Some (x0, buf) ->
  dict_res (DD3x DENT) gv shk (dc_dict st) =
    (if ddx_copied x0 then emp
     else data_at shk (tarray tuchar (Zlength (dx_bytes x0))) (zbytes (dx_bytes x0)) buf) ->
  (ddx_copied x0 = false -> readable_share shk /\ dict_ptr_ok W shk (Zlength (dx_bytes x0)) buf shd cap dst) ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  (dc_set st = nil -> forall md r out, ld_rel (dx_bytes x0) (dx_ld x0) ->
     oneshot_ok md (ddx_model x0) s cap r out -> oneshot_ok md (dictref_model (dc_dict st)) s cap r out) ->
  (dc_set st = nil -> forall md r, ld_rel (dx_bytes x0) (dx_ld x0) ->
     oneshot_codes md sel_none (ddx_model x0) s cap r -> oneshot_codes md sel_none (dictref_model (dc_dict st)) s cap r) ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hsel Hpar Hg Hl Hq Hlx Hdr Hptr Hrel Hm Hmc.
  (* the caller's bytes of a DDict by reference: darg_res has them as bytes_at, at a pointer *)
  assert (Hba: (ddx_copied x0 = false -> isptr buf) ->
     (if ddx_copied x0 then emp else bytes_at shk (dx_bytes x0) buf) =
     (if ddx_copied x0 then emp
      else data_at shk (tarray tuchar (Zlength (dx_bytes x0))) (zbytes (dx_bytes x0)) buf)).
  { intros Hp. destruct (ddx_copied x0); [reflexivity | apply bytes_at_ptr; auto]. }
  exists (fun w => !! (w = (DA_ddict x0 buf shk, @nil val) /\ (ddx_copied x0 = false -> isptr buf)) &&
            (mem_mgr gv * dgroup_f p (snd (getddict_res (c3_dict k))) * cm_have am (hb + local_held (snd (getddict_res (c3_dict k)))) *
             hset_rep am (c3_sp k) (c3_set k) hs *
             set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st))).
  split.
  - unfold lend_pre. rewrite (dgroup_split DENT gv p _ x0 buf Hl Hq Hlx), Hdr.
    assert_PROP (ld_rel (dx_bytes x0) (dx_ld x0)) as Hld.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    assert_PROP (exists dm, ddx_model x0 = Some dm) as Hdm.
    { sep_apply (ddx_model_some DENT gv x0 buf). entailer!. }
    destruct Hdm as [dm Hdm].
    assert_PROP (ddx_copied x0 = false -> isptr buf) as Hbp.
    { destruct (ddx_copied x0); [apply prop_right; discriminate | entailer!]. }
    Exists (DA_ddict x0 buf shk, @nil val). unfold lend_mid.
    rewrite msel_res_off, darg_res3_off by auto. simpl darg_res. rewrite (Hba Hbp).
    apply andp_right; [apply prop_right | rewrite prop_true_andp by (split; auto); cancel].
    unfold lend_ok. split; [exact I | ]. split; [simpl; rewrite Hg; reflexivity | ]. split; [intros Hc _; destruct (Hptr Hc); split; [assumption | left; assumption] | ].
    split; [intros; congruence | ].
    split; [ | split; [intros E r Hc; rewrite <- Hpar; apply Hmc; auto; apply Hc; left; exact Hsel |
                       simpl; intros E; rewrite E in Hq; contradiction]].
    intros r out Hb H1 H2 H3. apply (model_off st k dm); auto.
    + intros E Ho. apply Hm; auto. rewrite Hdm; exact Ho.
    + simpl in H2. rewrite <- Hdm. apply H2; auto.
  - intros w d' Hok Hd'. destruct Hd' as [E | [Hs _]]; [subst d' | congruence].
    split; [exact Hrel | ].
    unfold lend_mid, lend_post. Intros. match goal with H: w = _ |- _ => subst w end.
    match goal with H: ddx_copied x0 = false -> isptr buf |- _ => rename H into Hbp end.
    rewrite msel_res_off, darg_res3_off by auto. simpl darg_res. rewrite (Hba Hbp).
    rewrite (dgroup_split DENT gv p _ x0 buf Hl Hq Hlx), Hdr. cancel.
Qed.

(* ZSTD_getDDict returns a DDict q (described by dd) whose memory the caller holds, in dict_res or set_res *)
Lemma lend_ddict_gen (q: val) (dd: ddict_st) (R0: mpred) :
  sel_on (c3_par k) (c3_sp k) = false -> c3_par k = dc_par st ->
  fst (getddict_res (c3_dict k)) = q ->
  dict_res (DD3x DENT) gv shk (dc_dict st) * set_res (DD3x DENT) gv shk (dc_set st) (dc_dict st) =
    ddict_res (DD3x DENT) gv shk q dd * R0 ->
  (forall p0, dd_ref dd = Some p0 -> readable_share shk /\ dict_ptr_ok W shk (Zlength (dd_bytes dd)) p0 shd cap dst) ->
  dict_rel3 (after_use st) (snd (getddict_res (c3_dict k))) ->
  (dc_set st = nil -> forall md r out,
     oneshot_ok md (dict_auto (dd_bytes dd)) s cap r out -> oneshot_ok md (dictref_model (dc_dict st)) s cap r out) ->
  (dc_set st = nil -> forall md r, oneshot_codes md sel_none (dict_auto (dd_bytes dd)) s cap r ->
     oneshot_codes md sel_none (dictref_model (dc_dict st)) s cap r) ->
  0 <= cap ->
  dctx_lend DENT gv p W shk shd cap dst s st k am hb hs.
Proof.
  intros Hsel Hpar Hg Hres Hptr Hrel Hm Hmc Hcap.
  set (x := dd_x q dd). set (buf := dd_buf dd).
  exists (fun w => !! (w = (DA_ddict x buf shk, @nil val) /\ match dd_ref dd with Some p0 => isptr p0 | None => True end) &&
            (mem_mgr gv * dgroup DENT gv p (snd (getddict_res (c3_dict k))) * cm_have am (hb + local_held (snd (getddict_res (c3_dict k)))) *
             hset_rep am (c3_sp k) (c3_set k) hs * R0)).
  split.
  - unfold lend_pre. rewrite !sepcon_assoc. rewrite Hres. unfold ddict_res, DD3x. rewrite <- DD3_valid.
    unfold DD3_of. fold x. fold buf.
    assert_PROP (ld_rel (dx_bytes x) (dx_ld x)) as Hld.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    assert_PROP (isptr (dx_q x)) as Hq.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    assert_PROP (match dx_ref x with Some p0 => buf = p0 | None => True end) as Hbuf.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    assert_PROP (exists dm, ddx_model x = Some dm) as Hdm.
    { sep_apply (ddx_model_some DENT gv x buf). entailer!. }
    destruct Hdm as [dm Hdm].
    assert_PROP (match dd_ref dd with Some p0 => isptr p0 | None => True end) as Hrp.
    { destruct (dd_ref dd); entailer!. }
    Exists (DA_ddict x buf shk, @nil val). unfold lend_mid.
    rewrite msel_res_off, darg_res3_off by auto. simpl darg_res.
    pose proof (dd_darg_bytes shk q dd Hrp Hbuf) as Hm0. fold x buf in Hm0.
    apply andp_right; [apply prop_right | rewrite prop_true_andp by (split; auto)].
    2:{ rewrite Hm0. cancel; apply derives_refl. }
    unfold lend_ok. split; [exact I | ]. split; [simpl; rewrite Hg; auto | ].
    split; [apply dd_darg_ok3; auto |].
    split; [intros; congruence | ].
    split; [ | split; [intros E r Hc; rewrite <- Hpar; apply Hmc; auto;
                       apply (oneshot_codes_c3 _ _ (dd_ld dd)); [exact Hcap | exact Hld | ];
                       apply Hc; left; exact Hsel |
                       simpl; intros E; change (dx_q x) with q in Hq; rewrite E in Hq; contradiction]].
    intros r out Hb H1 H2 H3. apply (model_off st k dm); auto.
    + intros E Ho. apply Hm; auto. unfold ddx_model in Hdm. simpl in Hdm.
      apply (oneshot_ok_c3 _ _ (dd_ld dd)); [exact Hld | ]. rewrite Hdm. exact Ho.
    + simpl in H2. rewrite <- Hdm. apply H2; auto.
  - intros w d' Hok Hd'. destruct Hd' as [E | [Hs _]]; [subst d' | congruence].
    split; [exact Hrel | ].
    unfold lend_mid, lend_post. Intros. match goal with H: w = _ |- _ => subst w end.
    match goal with H: match dd_ref dd with Some _ => _ | None => True end |- _ => rename H into Hrp end.
    rewrite msel_res_off, darg_res3_off by auto. simpl darg_res.
    rewrite !sepcon_assoc. rewrite Hres. unfold ddict_res, DD3x. rewrite <- DD3_valid. unfold DD3_of. fold x. fold buf.
    assert_PROP (match dx_ref x with Some p0 => buf = p0 | None => True end) as Hbuf.
    { unfold ddict_rep_at, ddict_struct. entailer!. }
    pose proof (dd_darg_bytes shk q dd Hrp Hbuf) as Hm0. fold x buf in Hm0. rewrite Hm0. cancel; apply derives_refl.
Qed.

End Cases.

End CM_O3Cases1_1.
