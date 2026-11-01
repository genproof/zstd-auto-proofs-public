(* FS3 load3: ZSTD_DCtx_refDDict: the weak validity of a DDict pointer (from v2 FSSub.v) and the abstract state
   after ZSTD_DCtx_refDDict (pure) *)
Require Import Zstd.proof.dec.v3.FS.FSOblig3.
Require Import Zstd.proof.dec.v3.FS.load3.Load3Post Zstd.proof.dec.v3.FS.load3.Load3Adv.
Local Open Scope logic.

Section CM_Load3Rdd_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


(* weak validity of a DDict pointer: an unreadable part of its first field (dictBuffer), lent as bytes *)
Lemma rdd_join : sepalg.join (retainer_part Ews) Share.Rsh Ews.
Proof.
  split.
  - unfold retainer_part. rewrite Share.glb_assoc, (Share.glb_commute Ews), <- Share.glb_assoc.
    rewrite glb_Lsh_Rsh, Share.glb_commute. apply Share.glb_bot.
  - apply semax_straight.writable0_lub_retainer_Rsh. auto.
Qed.

Lemma rdd_nonid : sepalg.nonidentity (retainer_part Ews).
Proof.
  intro H. apply identity_share_bot in H. unfold retainer_part, Ews in H.
  rewrite Share.distrib1, glb_Lsh_Rsh in H. apply lub_bot_e in H. destruct H as [H _].
  unfold extern_retainer in H. destruct (Share.split Share.Lsh) as [a b] eqn:E. simpl in H.
  pose proof (Share.split_together _ _ _ E). rewrite <- H0 in H.
  rewrite Share.glb_commute, Share.glb_absorb in H. subst a.
  apply nonidentity_extern_retainer. unfold extern_retainer. rewrite E. simpl. apply bot_identity.
Qed.

Definition rdd_w (q: val) : ptr_witness := pw_bytes (retainer_part Ews) 8 (Zrepeat Vundef 8) q.

Lemma rdd_fa_mb v q : is_pointer_or_null v ->
  field_at (retainer_part Ews) t_ddict (DOT _dictBuffer) v q =
  !! field_compatible t_ddict (DOT _dictBuffer) q && memory_block (retainer_part Ews) 8 q.
Proof.
  intros Hv.
  rewrite <- nonreadable_memory_block_field_at; [| apply retainer_part_nonreadable | ].
  all: swap 1 2. { simpl. rewrite value_fits_eq. simpl. intros _. destruct v; simpl in *; try contradiction; auto. }
  unfold field_address. destruct (field_compatible_dec t_ddict (DOT _dictBuffer) q) as [Hc|Hc].
  - rewrite prop_true_andp by auto. simpl. rewrite isptr_offset_val_zero by auto. reflexivity.
  - rewrite prop_false_andp by auto. rewrite memory_block_isptr. apply pred_ext; normalize.
Qed.

Lemma rdd_fc q : field_compatible t_ddict (DOT _dictBuffer) q -> field_compatible (tarray tuchar 8) [] q.
Proof.
  intros H. destruct H as [Hp [_ [Hs [Ha _]]]]. destruct q; try contradiction.
  repeat split; auto.
  - red in Hs |- *. simpl in Hs |- *. lia.
  - red. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity|]. apply Z.divide_1_l.
Qed.

Lemma rdd_vf : value_fits (tarray tuchar 8) (Zrepeat Vundef 8).
Proof.
  rewrite value_fits_eq; simpl. split; [reflexivity|]. unfold Zrepeat; simpl.
  repeat constructor; rewrite value_fits_eq; simpl; intros X; contradiction.
Qed.

Lemma rdd_lend v q : is_pointer_or_null v ->
  field_at Ews t_ddict (DOT _dictBuffer) v q |--
  field_at Share.Rsh t_ddict (DOT _dictBuffer) v q * pws_pred [rdd_w q].
Proof.
  intros Hv.
  rewrite <- (field_at_share_join _ _ _ _ _ _ _ rdd_join).
  rewrite sepcon_comm. apply sepcon_derives; [apply derives_refl|].
  unfold pws_pred, rdd_w; simpl. rewrite sepcon_emp.
  rewrite rdd_fa_mb by auto. Intros.
  rewrite <- nonreadable_memory_block_data_at.
  - apply derives_refl.
  - apply retainer_part_nonreadable.
  - apply rdd_fc; auto.
  - apply rdd_vf.
Qed.

Lemma rdd_back v q : is_pointer_or_null v ->
  field_at Share.Rsh t_ddict (DOT _dictBuffer) v q * pws_pred [rdd_w q] |--
  field_at Ews t_ddict (DOT _dictBuffer) v q.
Proof.
  intros Hv.
  assert_PROP (field_compatible t_ddict (DOT _dictBuffer) q) as Hc by entailer!.
  rewrite <- (field_at_share_join _ _ _ _ _ _ _ rdd_join).
  rewrite sepcon_comm. apply sepcon_derives; [|apply derives_refl].
  unfold pws_pred, rdd_w; simpl. rewrite sepcon_emp.
  rewrite rdd_fa_mb by auto. rewrite prop_true_andp by auto.
  rewrite <- nonreadable_memory_block_data_at.
  - apply derives_refl.
  - apply retainer_part_nonreadable.
  - apply rdd_fc; auto.
  - apply rdd_vf.
Qed.

Lemma rdd_wvp q : pws_pred [rdd_w q] |-- weak_valid_pointer q.
Proof.
  unfold pws_pred, rdd_w; simpl. rewrite sepcon_emp.
  eapply derives_trans; [apply data_at_memory_block|]. simpl sizeof.
  eapply derives_trans; [apply memory_block_valid_ptr; [apply rdd_nonid | lia] | apply valid_pointer_weak].
Qed.


(* ---------- the abstract state after ZSTD_DCtx_refDDict ---------- *)

Lemma in_set_add q dd l q' dd' :
  ~ In q (map fst l) -> In (q', dd') (set_add l q dd) -> q' = q -> dd' = dd.
Proof.
  intros Hn Hin ->. unfold set_add in Hin.
  destruct (existsb _ l).
  - apply in_map_iff in Hin. destruct Hin as [e [He Hin]].
    destruct (dd_id (snd e) =? dd_id dd).
    + inversion He; auto.
    + subst e. exfalso. apply Hn. apply in_map_iff. exists (q, dd'). auto.
  - apply in_app_or in Hin. destruct Hin as [Hin | [E | []]].
    + exfalso. apply Hn. apply in_map_iff. exists (q, dd'). auto.
    + inversion E; auto.
Qed.


Lemma set_set_same (st: dctx_st) d : set_set (set_dict st d) (dc_set st) = set_dict st d.
Proof. destruct st; reflexivity. Qed.

(* the new state: the context references q (its set l') *)
Definition st_ref (st: dctx_st) (q: val) (dd: ddict_st) (l': list (val * ddict_st)) : dctx_st :=
  set_set (set_dict st (Some (ddict_ref q dd))) l'.

Lemma refddict_post (st: dctx_st) (k: cst3) (q: val) (dd: ddict_st) (r: Z) (sp': val) (l': list (val * ddict_st)) :
  c3_par k = dc_par st -> c3_set k = dc_set st -> isptr q ->
  refddict_res3 (dp_multi (c3_par k)) (c3_sp k) (c3_set k) q dd r sp' l' ->
  refddict_result st (st_ref st q dd l') r q dd /\ (l' = dc_set st \/ l' = set_add (dc_set st) q dd).
Proof.
  intros Hp Hs Hq H. unfold refddict_res3 in H. rewrite Hp, Hs in H.
  assert (Hv: veqb q nullval = false) by (unfold veqb; destruct (Val.eq q nullval); [subst; contradiction | reflexivity]).
  rewrite Hv in H. simpl in H. unfold refddict_result, st_ref.
  destruct (Z.eqb_spec (dp_multi (dc_par st)) 1) as [E | E]; simpl in H.
  - destruct H as [[-> [-> _]] | [He [_ ->]]].
    + split; [left; split; [reflexivity | rewrite ?E; reflexivity] | right; reflexivity].
    + split; [right; split; [exact E |]; split; [exact He | apply set_set_same] | left; reflexivity].
  - destruct H as [-> [_ ->]]. split; [left; split; [reflexivity |] | left; reflexivity].
    try (destruct (dp_multi (dc_par st) =? 1) eqn:E2; [apply Z.eqb_eq in E2; contradiction |]); reflexivity.
Qed.

(* the concrete state with the allocator om (the same allocator, its bound maybe raised) *)
Definition k_mem (k: cst3) (om: option cmem) : cst3 := c3_with_s k (sf_with_mem (c3_s k) om).

Lemma c3_with_set_same_dict (k: cst3) (s: sfields) (d: dfields) :
  c3_with_set (c3_with_dict (c3_with_s k s) d) (c3_sp k) (c3_set k) = c3_with_dict (c3_with_s k s) d.
Proof. destruct k; reflexivity. Qed.

(* DC3_of's relation after ZSTD_DCtx_refDDict(q) on the context st0 related to k0 (load_pre), through the allocator
   om, the context's other blocks then holding h' bytes *)
Lemma ref_rel_any (SR: srel3) (gv: globals) (BR: blrel) (st0: dctx_st) (k0: cst3) (om: option cmem) (h': Z)
    (q: val) (dd: ddict_st) (r: Z) (sp': val) (l': list (val * ddict_st)) :
  load_pre st0 k0 -> isptr q -> ~ In q (map fst (dc_set st0)) ->
  refddict_res3 (dp_multi (c3_par k0)) (c3_sp k0) (c3_set k0) q dd r sp' l' ->
  mem_room (sf_with_held (sf_with_mem (c3_s k0) om) h') ->
  let k' := c3_with_set (c3_with_dict (c3_with_s (k_mem k0 om) (sf_with_held (c3_s (k_mem k0 om)) h'))
                                      (ddict_ref_fields q)) sp' l' in
  let st' := st_ref (set_mem st0 om) q dd l' in
  refddict_result (set_mem st0 om) st' r q dd /\
  base_rel3 st' k' /\
  (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false ->
     SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
  (forall ba, dc_bl st' = Some ba -> BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))).
Proof.
  intros [[H1 [H2 [H3 [H4 [H5 [H5' [H6 [H7 H8]]]]]]]] [Hst [Hbl Hss]]] Hq Hn Hr Hroom k' st'.
  simpl in H1, H2, H3.
  destruct (refddict_post (set_mem st0 om) k0 q dd r sp' l' H2 H3 Hq Hr) as [Hres Hl].
  split; [exact Hres |]. split; [| split].
  - unfold base_rel3, st', st_ref, k'; simpl.
    refine (conj H1 (conj H2 (conj eq_refl (conj _ (conj _ (conj H5' (conj H6 (conj _ _)))))))).
    + left. unfold dict_rel3_of; simpl. repeat split; auto.
    + intros dr q0 dd1 dd0 Hd Hs Hin. inversion Hd; subst dr. simpl in Hs. inversion Hs; subst q0 dd1.
      simpl in Hl. destruct Hl as [-> | ->].
      * exfalso. apply Hn. apply in_map_iff. exists (q, dd0). auto.
      * exact (in_set_add q dd (dc_set st0) q dd0 Hn Hin eq_refl).
    + rewrite Hbl. intros E; contradiction.
    + unfold mem_rel3; simpl. split; [reflexivity | split; [exact Hroom |]].
      unfold local_mem; simpl. intros E; contradiction.
  - simpl. intros E Herr. right. split; [exact (Hss E Herr) | exact Hst].
  - simpl. rewrite Hbl. discriminate.
Qed.

(* the result of ZSTD_DCtx_refDDict(q) in the API (Spec_api6.ZSTD_DCtx_refDDict_spec) on the context st0 *)
Definition ref_api_res (q: val) (dd: ddict_st) (st0: dctx_st) (r0: Z) (st1: dctx_st) : Prop :=
  if eq_dec q nullval then r0 = 0 /\ st1 = set_dict st0 None
  else exists om, cm_raised (dc_mem st0) om /\ refddict_result (set_mem st0 om) st1 r0 q dd.

(* the allocator of the internal call: the context's own when zstd refuses, the one of st_next st for NULL (nothing
   is allocated), else the context's raised to cover the window limit w *)
Definition ref_mem (st: dctx_st) (k: cst3) (q: val) (w: Z) : option cmem :=
  if Z.eq_dec (sf_stage (c3_s k)) 0
  then (if eq_dec q nullval then dc_mem (st_next st) else cm_raise (dc_mem st) w)
  else sf_mem (c3_s k).

(* the context's representation holds with the allocator of the call (CMem.CM_mono) *)
Lemma ref_mem_raise (st: dctx_st) (k: cst3) (q: val) (w: Z) :
  sf_mem (c3_s k) = dc_mem st ->
  (exists w', ref_mem st k q w = cm_raise (sf_mem (c3_s k)) w') \/ ref_mem st k q w = sf_mem (c3_s k).
Proof.
  intros Hm. unfold ref_mem, st_next. rewrite <- Hm.
  destruct (Z.eq_dec (sf_stage (c3_s k)) 0); [| right; reflexivity].
  destruct (eq_dec q nullval); [| left; exists w; reflexivity].
  destruct (ss_eq_dec (dc_ss st) ss_init); [right; simpl; auto | left; simpl].
  rewrite <- Hm. eexists; reflexivity.
Qed.

Lemma ref_api_post (SR: srel3) (gv: globals) (BR: blrel) (st: dctx_st) (k: cst3) (q: val) (dd: ddict_st) (w: Z)
    (r: Z) (k': cst3) :
  base_rel3 st k -> dc_bl st = None ->
  (dc_ss st <> ss_init -> ss_err (dc_ss st) = false -> SR gv st k \/ (dc_ss st = ss_restart /\ sf_stage (c3_s k) = 0)) ->
  (forall ba, dc_bl st = Some ba -> BR (c3_par k) ba (c3_fs k) (c3_tabs k) (sf_hbuf (c3_s k))) ->
  ex_on3 SR st k ->
  (q <> nullval -> isptr q /\ ~ In q (map fst (dc_set st))) ->
  dp_wmax (dc_par st) <= w -> 3 * set_new_bytes + 3 * sf_held (c3_s k) + dstream_size (2 ^ 31) <= dstream_size w ->
  refddict_int_res (k_mem k (ref_mem st k q w)) q dd r k' ->
  exists st', after_stage (ref_api_res q dd) st r st' /\ base_rel3 st' k' /\
    (dc_ss st' <> ss_init -> ss_err (dc_ss st') = false ->
       SR gv st' k' \/ (dc_ss st' = ss_restart /\ sf_stage (c3_s k') = 0)) /\
    (forall ba, dc_bl st' = Some ba -> BR (c3_par k') ba (c3_fs k') (c3_tabs k') (sf_hbuf (c3_s k'))) /\
    ex_on3 SR st' k'.
Proof.
  intros Hb Hbl Hsr Hbr Hex Hq Hw1 Hw2 Hres.
  destruct (base_rel3_mem _ _ Hb) as (Hm1 & Hm2 & Hm3).
  destruct Hres as [[Hs [He ->]] | [Hs (sp' & l' & h' & Hr3 & Hh' & Hhn & Hhq & ->)]].
  - (* refused *)
    cbn [k_mem c3_s c3_with_s sf_stage sf_with_mem] in Hs.
    unfold k_mem, ref_mem. destruct (Z.eq_dec (sf_stage (c3_s k)) 0) as [E|E]; [contradiction |].
    rewrite sf_with_mem_same, c3_with_s_same.
    exists st. split; [apply after_stage_refuse; [exact (base_rel3_stage _ _ Hb E) | exact He] |].
    split; [exact Hb | split; [exact Hsr | split; [exact Hbr | exact Hex]]].
  - cbn [k_mem c3_s c3_with_s sf_stage sf_with_mem] in Hs.
    assert (Hp: load_pre (st_next st) k) by (apply load_pre_next; auto).
    unfold ref_mem in *. destruct (Z.eq_dec (sf_stage (c3_s k)) 0) as [_|E]; [| contradiction].
    cbn [k_mem c3_s c3_with_s c3_par c3_sp c3_set c3_dict sf_mem sf_held sf_with_mem] in *.
    destruct (eq_dec q nullval) as [Hqn | Hqn].
    + (* NULL: no dictionary *)
      subst q. unfold refddict_res3 in Hr3. replace (veqb nullval nullval) with true in Hr3 by (unfold veqb; destruct (Val.eq nullval nullval); congruence). simpl in Hr3. destruct Hr3 as (-> & -> & ->).
      specialize (Hhq eq_refl).
      set (om := dc_mem (st_next st)) in *.
      assert (Hroom: mem_room (sf_with_held (sf_with_mem (c3_s k) om) h')).
      { unfold mem_room in *; simpl. subst om. unfold st_next.
        pose proof (local_held_nonneg (c3_dict k)).
        destruct (ss_eq_dec (dc_ss st) ss_init); simpl; rewrite <- Hm1;
          destruct (sf_mem (c3_s k)) as [m|] eqn:Em; simpl.
        all: change (Z.pow_pos 2 31) with (2 ^ 31) in *.
        - destruct Hm2 as [Hm2 | Hm2]; [left; lia | right; lia].
        - rewrite (local_held_none _ Hm3) in Hhq. lia.
        - destruct Hm2 as [Hm2 | Hm2]; [left; lia | right; lia].
        - rewrite (local_held_none _ Hm3) in Hhq. lia. }
      pose proof (load3_rel_any SR gv BR (st_next st) k om h' None df_none Hp ltac:(intros ? E'; discriminate)
                    ltac:(split; [reflexivity | left; reflexivity]) ltac:(intros E'; contradiction) Hroom) as X.
      cbv zeta in X. subst om. rewrite set_mem_same in X.
      exists (ex_next st (set_dict (st_next st) None)). split.
      { apply after_stage_next. unfold ref_api_res. rewrite if_true by auto. split; reflexivity. }
      destruct X as (X1 & X2 & X3).
      apply (ex_next_dc3 SR gv BR st (set_dict (st_next st) None) k); auto; try reflexivity.
      apply dc_ex_st_next.
    + (* a DDict *)
      destruct (Hq Hqn) as [Hqp Hnin].
      set (om := cm_raise (dc_mem st) w) in *.
      assert (Hroom: mem_room (sf_with_held (sf_with_mem (c3_s k) om) h')).
      { unfold mem_room; simpl. subst om. rewrite <- Hm1.
        destruct (sf_mem (c3_s k)) as [m|] eqn:Em; simpl; change (Z.pow_pos 2 31) with (2 ^ 31) in *; [right; lia |].
        apply Hhn. rewrite <- Hm1. reflexivity. }
      rewrite <- dc_set_st_next in Hnin.
      pose proof (ref_rel_any SR gv BR (st_next st) k om h' q dd r sp' l' Hp Hqp Hnin Hr3 Hroom) as X.
      cbv zeta in X. destruct X as [Hres X].
      exists (ex_next st (st_ref (set_mem (st_next st) om) q dd l')). split.
      { apply after_stage_next. unfold ref_api_res. rewrite if_false by auto.
        exists om. split; [subst om; apply cm_raised_next; exact Hw1 | exact Hres]. }
      try rewrite if_false by auto. destruct X as (X1 & X2 & X3).
      apply (ex_next_dc3 SR gv BR st (st_ref (set_mem (st_next st) om) q dd l') k); auto; try reflexivity.
      apply dc_ex_st_next.
Qed.

End CM_Load3Rdd_1.
