(* FS3 streaming, case zdss_loadHeader, G4: the dictionary of the new frame (pure facts). *)
Require Import Zstd.proof.dec.v3.FS.stream.lh.LH3Stmts.
Local Open Scope Z_scope.

Section CM_LH3G42_dict_1.
Context {CMI: Zstd.proof.zstd.CMem.cmem_preds}.


Lemma g4_dec_nohdr : forall md d wl s, (forall h, get_frame_header_m (md_magicless md) s <> FH_ok h) ->
  forall out k, decode_frame_m md d wl s <> FOk out k.
Proof.
intros md d wl s H out k. unfold decode_frame_m. cbv zeta.
destruct (get_frame_header_m (md_magicless md) s) eqn:E; try (exfalso; exact (H _ eq_refl));
repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma g4_walk_cur_none : forall fuel md wl s, walk_cur fuel md sel_none None wl s = None.
Proof.
induction fuel; intros md wl s; cbn [walk_cur]; auto.
destruct (Zlength s <? starting_len (md_magicless md)); auto.
destruct (negb (md_magicless md) && is_skippable_magic (le_field s 0 4))%bool.
- destruct (skippable_frame_size s); auto. unfold skip_cd, sel_none. destruct (md_dwin md); apply IHfuel.
- unfold frame_dict, sel_none. destruct (get_frame_header_m _ s) eqn:E; auto;
  destruct (decode_frame_m md no_dict wl s) eqn:D; auto;
  exfalso; refine (g4_dec_nohdr md no_dict wl s _ _ _ D); intros h; rewrite E; discriminate.
Qed.

Lemma g4_clean_ids : forall l, set_clean l = true -> Forall (fun e => dd_id (snd e) <> 0) l.
Proof.
intros l Hc. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. apply Forall_forall. intros e He. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [Hc _]. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.

Lemma g4_clean_auto : forall l e, set_clean l = true -> In e l -> dict_auto (dd_bytes (snd e)) <> None.
Proof.
intros l e Hc He. unfold set_clean in Hc. apply andb_prop in Hc. destruct Hc as [_ Hc].
rewrite forallb_forall in Hc. specialize (Hc e He).
apply andb_prop in Hc. destruct Hc as [_ Hc]. destruct (dict_auto _); congruence.
Qed.

Lemma g4_find0 : forall l, Forall (fun e => dd_id (snd e) <> 0) l -> set_find l 0 = nullval.
Proof.
intros l Hl. unfold set_find. destruct (find (fun e => dd_id (snd e) =? 0) l) eqn:E; auto.
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
rewrite Forall_forall in Hl. exfalso. exact (Hl _ Hin Heq).
Qed.

(* a miss of the model's selection on a clean set is a miss of the lookup *)
Lemma g4_find_miss : forall l id, set_clean l = true -> set_sel l id = None -> set_find l id = nullval.
Proof.
intros l id Hc Hs. destruct (Z.eq_dec id 0) as [->|Hn]; [ apply g4_find0, g4_clean_ids; auto | ].
unfold set_sel in Hs. rewrite (proj2 (Z.eqb_neq _ _) Hn) in Hs.
unfold set_find. destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:E; auto.
apply find_some in E. destruct E as [Hin _]. exfalso. exact (g4_clean_auto l e Hc Hin Hs).
Qed.

(* a hit *)
Lemma g4_find_hit : forall l id dq, set_sel l id = Some dq ->
  id <> 0 /\ exists e, In e l /\ dd_id (snd e) = id /\ set_find l id = fst e /\ dict_auto (dd_bytes (snd e)) = Some dq.
Proof.
intros l id dq Hs. unfold set_sel in Hs. destruct (Z.eqb_spec id 0) as [_|Hn]; [ discriminate | ].
split; [ exact Hn | ]. unfold set_find.
destruct (find (fun e => dd_id (snd e) =? id) l) as [e|] eqn:E; [ | discriminate ].
apply find_some in E. destruct E as [Hin Heq]. apply Z.eqb_eq in Heq.
exists e. auto.
Qed.

(* two entries of a set with the same pointer are the same *)
Lemma g4_nodup_in : forall (l: list (val * ddict_st)) q dd dd', NoDup (map fst l) -> In (q, dd) l -> In (q, dd') l -> dd = dd'.
Proof.
induction l as [|[q0 d0] l IH]; intros q dd dd' Hnd H1 H2; [ contradiction | ].
cbn in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- inversion E1; inversion E2; subst; auto.
- inversion E1; subst. exfalso. apply Hni. apply (in_map fst) in H2. exact H2.
- inversion E2; subst. exfalso. apply Hni. apply (in_map fst) in H1. exact H1.
- eapply IH; eauto.
Qed.

Lemma g4_state : forall x dm, ddx_model x = Some dm -> ddx_state x = dm_state dm.
Proof.
intros x dm H. unfold ddx_model, ddx_state, ddx_ent, ddict_ent_c, dict_auto_c, is_formatted in *.
destruct (dx_raw x); [ inversion H; reflexivity | ].
destruct (Zlength (dx_bytes x) <? 8) eqn:E1.
- inversion H; subst. cbn [dm_state dict_raw]. rewrite Z.ltb_lt in E1.
  replace (8 <=? Zlength (dx_bytes x)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
- rewrite Z.ltb_ge in E1. replace (8 <=? Zlength (dx_bytes x)) with true by (symmetry; apply Z.leb_le; lia).
  destruct (le_field (dx_bytes x) 0 4 =? ZSTD_MAGIC_DICTIONARY); cbn [andb negb] in *.
  + destruct (dx_ld x) as [[st es] |]; inversion H; auto.
  + inversion H; auto.
Qed.

Lemma g4_fpid : forall h, fp_dictID (fh_val h) = Vint (Int.repr (fh_dictID h)).
Proof. reflexivity. Qed.

Lemma g4_repr_inj : forall a b, 0 <= a <= Int.max_unsigned -> 0 <= b <= Int.max_unsigned ->
  Vint (Int.repr a) = Vint (Int.repr b) -> a = b.
Proof.
intros a b Ha Hb E. apply Vint_inj in E. apply (f_equal Int.unsigned) in E.
rewrite !Int.unsigned_repr in E by lia. exact E.
Qed.

(* the selection's dictionary fields are a context dictionary (copy of G1's g1_dict_rel) *)
Lemma g4_dict_rel1 : hs_probe_ok -> forall st k hb kk v tbl d1 did1,
  base_call st k -> lhA_sel k hb kk v tbl d1 did1 -> dict_rel3 st d1.
Proof.
intros Hpr st k hb kk v tbl d1 did1 Hb Hsel.
destruct Hb as (_ & _ & Hset & Hdr & _).
destruct Hsel as (_ & _ & id & _ & Hsb). unfold sel_by in Hsb.
destruct (sel_on (c3_par k) (c3_sp k)).
- destruct Hsb as (Hinv & Hidr & Hd1 & _). subst d1. unfold sel_dict.
  destruct (eq_dec (sel_r (c3_dict k) (c3_set k) tbl id) nullval) as [E|E]; [ exact Hdr | ].
  right. unfold sel_r in *.
  destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
  destruct (Hpr _ _ _ Hinv Hidr) as [[Hn | Hin] _]; [ contradiction | ].
  rewrite Hset in Hin. split.
  + intro Hnil. rewrite Hnil in Hin. contradiction.
  + unfold dict_switched, switch_fields. cbn. rewrite Hset. auto.
- destruct Hsb as [Hd1 _]. subst d1. exact Hdr.
Qed.

(* ZSTD_getDDict keeps the context's dictionary (a stream never uses a prefix once) *)
Lemma g4_dict_rel2 : forall W st d, stream_dict_ok W st -> dict_rel3 st d -> dict_rel3 st (snd (getddict_res d)).
Proof.
intros W st d Hsd Hd. unfold getddict_res.
destruct (Z.eqb_spec (df_uses d) 0) as [U0|U0]; cbn [snd].
- destruct Hd as [Hd | (_ & _ & Hu & _ & _)]; [ | lia ].
  left. destruct (dc_dict st) as [dr|] eqn:Ed; cbn [dict_rel3_of] in Hd |- *.
  + unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
    destruct (dr_src dr) as [pk | | q pref]; [ contradiction | | ].
    * destruct Hd as (Ho' & Hz). split; [ exact Ho' | ].
      destruct (Zlength (dr_bytes dr) =? 0); [ reflexivity | ].
      destruct Hz as (buf & ld & am & _ & _ & Hu & _). lia.
    * destruct Hd as (_ & _ & _ & _ & _ & Hu). lia.
  + split; [ reflexivity | left; reflexivity ].
- destruct (Z.eqb_spec (df_uses d) 1) as [U1|U1]; cbn [snd]; [ | exact Hd ].
  exfalso. destruct Hd as [Hd | (_ & _ & Hu & _ & _)]; [ | lia ].
  destruct (dc_dict st) as [dr|] eqn:Ed; cbn [dict_rel3_of] in Hd; [ | lia ].
  unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
  destruct (dr_src dr) as [pk | | q pref]; [ contradiction | | ].
  + destruct Hd as (Ho' & Hz). destruct (Zlength (dr_bytes dr) =? 0).
    * subst d. cbn in U1. lia.
    * destruct Hz as (buf & ld & am & _ & _ & Hu & _). lia.
  + destruct Hd as (_ & _ & _ & _ & _ & Hu). lia.
Qed.

(* the streaming selection with a set: not described, or the set's selection *)
Lemma g4_st_sel : forall st, dc_set st <> nil ->
  st_sel st = (sel_none, None) \/
  (st_sel st = (set_sel (dc_set st), None) /\ dp_multi (dc_par st) = 1 /\ set_clean (dc_set st) = true /\
   dc_dict st <> None).
Proof.
intros st Hne. unfold st_sel. destruct (dc_set st) as [|e0 l0]; [ contradiction | ].
destruct (dc_dict st) as [dr|]; [ | left; reflexivity ].
destruct ((dp_multi (dc_par st) =? 1) && set_clean (e0 :: l0) &&
          match dr_src dr with DSDDict _ _ => true | _ => negb (Nat.eqb (length (dr_bytes dr)) 0) end)%bool eqn:E;
  [ | left; reflexivity ].
apply andb_prop in E. destruct E as [E _]. apply andb_prop in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1.
right. split; [ reflexivity | ]. split; [ exact E1 | ]. split; [ exact E2 | ]. discriminate.
Qed.

(* a caller's DDict at a member's pointer has the member's bytes *)
Lemma g4_caller_bytes : forall st q dd dd0, NoDup (map fst (dc_set st)) -> set_cur_ok st ->
  In (q, dd0) (dc_set st) -> dd_caller st q dd -> dd_bytes dd = dd_bytes dd0.
Proof.
intros st q dd dd0 Hnd Hsco Hin [Hc | (dr & Ed & Hsrc)].
- rewrite (g4_nodup_in _ _ _ _ Hnd Hc Hin). reflexivity.
- rewrite (Hsco dr q dd dd0 Ed Hsrc Hin). reflexivity.
Qed.

Lemma g4_model_bytes : forall x b dm, dx_bytes x = b -> dx_raw x = false -> ld_rel b (dx_ld x) ->
  dict_auto b = Some dm -> ddx_model x = Some dm.
Proof.
intros x b dm Hb Hr Hl Ha. subst b. apply ddx_model_some; auto. rewrite Hr. exact Ha.
Qed.

Lemma g4_getddict_m1 : forall d, df_uses d = -1 -> getddict_res d = (df_ddict d, d).
Proof. intros d Hu. unfold getddict_res. rewrite Hu. reflexivity. Qed.

Lemma g4_sel_on_t : forall k st, base_call st k -> dc_set st <> nil -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  dp_multi (dc_par st) = 1 -> sel_on (c3_par k) (c3_sp k) = true.
Proof.
intros k st (_ & Hpar & Hset & _) Hne Hsp Hm. unfold sel_on. rewrite Hpar, Hm. cbn.
assert (c3_sp k <> nullval) by (apply Hsp; rewrite Hset; auto).
unfold veqb. destruct (Val.eq (c3_sp k) _) as [E|E]; [ contradiction | reflexivity ].
Qed.

Lemma g4_sel_on_f : forall k st, base_call st k -> dc_set st = nil -> (c3_set k = nil -> c3_sp k = nullval) ->
  sel_on (c3_par k) (c3_sp k) = false.
Proof.
intros k st (_ & _ & Hset & _) Hn Hsp. unfold sel_on. rewrite Hsp by (rewrite Hset; auto).
unfold veqb. destruct (Val.eq nullval nullval) as [_|E]; [ | congruence ]. apply andb_false_r.
Qed.

(* the facts the dictionary lemmas take from the representation (lh_st): the local DDict is not one of the
   caller's DDicts in set_res *)
Definition g4_local_ok (st: dctx_st) (d: dfields) : Prop :=
  forall x buf dd, df_lx d = Some (x, buf) -> df_local d <> nullval -> In (df_local d, dd) (dc_set st) ->
    cur_ddict (dc_dict st) = Some (df_local d).

(* piece C's DDict, unfolded *)
Lemma g4_dd_some : forall a k1 x buf, lhC_dd a k1 (Some (x, buf)) ->
  dx_q x = fst (getddict_res (c3_dict k1)) /\ dx_q x <> nullval /\
  ((df_local (snd (getddict_res (c3_dict k1))) = dx_q x /\ df_lx (snd (getddict_res (c3_dict k1))) = Some (x, buf)) \/
   (exists dd, dd_caller (a_st a) (dx_q x) dd /\ dx_bytes x = dd_bytes dd /\ dx_ref x = dd_xref dd /\ dx_raw x = false)) /\
  ld_rel (dx_bytes x) (dx_ld x).
Proof.
intros a k1 x buf H. cbn [lhC_dd] in H. unfold lh_dd_ok, dd_src in H.
destruct H as (H1 & H2 & H3 & H4 & _). unfold c3_with_dict in H3. cbn [c3_dict] in H3.
split; [ exact H1 | ]. split; [ exact H2 | ]. split; [ | exact H4 ].
destruct H3 as [(H3a & _ & _ & H3b) | (dd & Hc & Ex & _)]; [ left; exact (conj H3a H3b) | right; exists dd; split; [ exact Hc | ] ].
repeat split; rewrite Ex; reflexivity.
Qed.

(* the dictionary of a Zstandard frame: the model's (frame_dict) is the DDict piece C began it with, and the
   context then describes it (cur_dict_ok) *)
Lemma g4_dm : hs_probe_ok -> forall W a k hb h tbl d1 did1 c cd dm,
  base_call (a_st a) k -> stream_dict_ok W (a_st a) ->
  (c3_set k = nil -> c3_sp k = nullval) -> (c3_set k <> nil -> c3_sp k <> nullval) ->
  lhA_sel k hb 0 (fh_val h) tbl d1 did1 -> 0 <= fh_dictID h <= Int.max_unsigned ->
  lhC_dd a (k_A k (fh_val h) d1 did1) (lc_dd c) ->
  (fh_dictID h = 0 \/ fh_dictID h = lc_did c) ->
  (lc_dd c = None -> lc_did c = 0) ->
  g4_local_ok (a_st a) (snd (getddict_res d1)) ->
  (st_sel (a_st a) = (sel_none, None) -> cd = None) ->
  cur_dict_ok (a_st a) k cd ->
  get_frame_header_m (lh_mg k) hb = FH_ok h ->
  frame_dict (lh_mg k) (fst (st_sel (a_st a))) cd hb = Some dm ->
  dd_model (lc_dd c) dm /\
  (forall k', c3_dict k' = snd (getddict_res d1) ->
     fp_dictID (fs_fParams (c3_fs k')) = Vint (Int.repr (fh_dictID h)) -> cur_dict_ok (a_st a) k' (Some dm)).
Proof.
intros Hpr W a k hb h tbl d1 did1 c cd dm Hb Hsd Hsp0 Hsp1 Hsel Hidr HCdd HCid HCnone Hloc Hcd0 Hcd Hgfh Hfd.
pose proof Hb as Hb'. destruct Hb' as (Hstab & Hpar & Hset & Hdr & Hsco & _).
destruct Hsel as (_ & _ & id & Hid & Hsb). unfold sel_by in Hsb.
assert (HDN: lc_dd c = None -> fst (getddict_res d1) = nullval).
{ intros E. rewrite E in HCdd. exact HCdd. }
assert (HDS: forall x buf, lc_dd c = Some (x, buf) ->
  dx_q x = fst (getddict_res d1) /\ dx_q x <> nullval /\
  ((df_local (snd (getddict_res d1)) = dx_q x /\ df_lx (snd (getddict_res d1)) = Some (x, buf)) \/
   (exists dd, dd_caller (a_st a) (dx_q x) dd /\ dx_bytes x = dd_bytes dd /\ dx_ref x = dd_xref dd /\ dx_raw x = false)) /\
  ld_rel (dx_bytes x) (dx_ld x)).
{ intros x buf E. rewrite E in HCdd. exact (g4_dd_some _ _ _ _ HCdd). }
clear HCdd.
assert (Hcase: dc_set (a_st a) = nil \/ dc_set (a_st a) <> nil)
  by (destruct (dc_set (a_st a)); [ left; auto | right; discriminate ]).
destruct Hcase as [Es | Hne].
- (* no set: the context's dictionary *)
  rewrite (g4_sel_on_f k (a_st a) Hb Es Hsp0) in Hsb. destruct Hsb as [Hd1 _]. subst d1.
  unfold st_sel in Hfd. rewrite Es in Hfd. cbn [fst] in Hfd. unfold frame_dict, sel_none in Hfd. rewrite Hgfh in Hfd.
  destruct (Hcd dm Hfd) as [(_ & Hdm) | (Hne & _)]; [ | contradiction ].
  split.
  2: { intros k' _ _ dm' E. inversion E; subst dm'. left. split; [ exact Es | exact Hdm ]. }
  destruct Hdr as [Hdr | (Hne & _)]; [ | contradiction ].
  unfold dd_model. destruct (dc_dict (a_st a)) as [dr|] eqn:Ed.
  + unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
    cbn [dict_rel3_of] in Hdr. unfold dictref_model in Hdm.
    destruct (dr_src dr) as [pk | | q pref] eqn:Esrc; [ contradiction | | ].
    * destruct Hdr as (_ & Hz).
      destruct (Z.eqb_spec (Zlength (dr_bytes dr)) 0) as [Z0|Z0].
      -- destruct (lc_dd c) as [[x buf]|] eqn:El.
         ++ exfalso. destruct (HDS x buf eq_refl) as (Hq & Hqn & _). rewrite Hz in Hq. cbn in Hq. contradiction.
         ++ apply Zlength_nil_inv in Z0. rewrite Z0 in Hdm. destruct (dr_raw dr); cbn in Hdm; inversion Hdm; reflexivity.
      -- destruct Hz as (buf0 & ld & am0 & Hlp & Hdd & Hu & Hlx).
         destruct (lc_dd c) as [[x buf]|] eqn:El.
         ++ destruct (HDS x buf eq_refl) as (Hq & Hqn & Hsrc & Hld). rewrite g4_getddict_m1 in Hsrc by exact Hu.
            cbn [snd] in Hsrc. destruct Hsrc as [(Hl1 & Hl2) | (dd & Hc & _)].
            ** rewrite Hlx in Hl2. inversion Hl2; subst x. apply ddx_model_some; [ exact Hld | exact Hdm ].
            ** exfalso. destruct Hc as [Hc | (dr' & Ed' & Hs')]; [ rewrite Es in Hc; exact Hc | ].
               rewrite Ed in Ed'. inversion Ed'; subst dr'. congruence.
         ++ exfalso. specialize (HDN eq_refl). rewrite g4_getddict_m1 in HDN by exact Hu. cbn [fst] in HDN.
            rewrite Hdd in HDN. rewrite HDN in Hlp. exact Hlp.
    * destruct Hdr as (Hr & _ & Hq & Hl & Hdd & Hu & Hbdr). rewrite Hr in Hdm.
      destruct (lc_dd c) as [[x buf]|] eqn:El.
      -- destruct (HDS x buf eq_refl) as (Hq' & Hqn & Hsrc & Hld). rewrite g4_getddict_m1 in Hsrc by exact Hu.
         cbn [snd] in Hsrc. destruct Hsrc as [(Hl1 & Hl2) | (dd & Hc & Hbx & _ & Hrx)].
         ++ exfalso. rewrite Hl in Hl1. apply Hqn. rewrite <- Hl1. reflexivity.
         ++ destruct Hc as [Hc | (dr' & Ed' & Hs')]; [ rewrite Es in Hc; contradiction | ].
            rewrite Ed in Ed'. inversion Ed'; subst dr'. assert (Hb': dr_bytes dr = dd_bytes dd) by (rewrite Esrc in Hs'; inversion Hs'; subst; exact Hbdr).
            apply (g4_model_bytes x (dr_bytes dr)); auto. rewrite Hbx. auto. rewrite Hbx, <- Hb' in Hld. exact Hld.
      -- exfalso. specialize (HDN eq_refl). rewrite g4_getddict_m1 in HDN by exact Hu. cbn [fst] in HDN.
         rewrite Hdd in HDN. rewrite HDN in Hq. exact Hq.
  + cbn [dict_rel3_of] in Hdr. destruct Hdr as [Hdr _]. cbn in Hdm. inversion Hdm; subst dm.
    destruct (lc_dd c) as [[x buf]|] eqn:El; [ | reflexivity ].
    exfalso. destruct (HDS x buf eq_refl) as (Hq & Hqn & _). unfold getddict_res in Hq. rewrite Hdr in Hq.
    cbn in Hq. contradiction.
- (* a set *)
  destruct (g4_st_sel _ Hne) as [Hss | (Hss & Hmulti & Hclean & Hdn)].
  { exfalso. rewrite (Hcd0 Hss) in Hfd. rewrite Hss in Hfd. cbn [fst] in Hfd.
    unfold frame_dict, sel_none in Hfd. rewrite Hgfh in Hfd. discriminate. }
  rewrite Hss in Hfd. cbn [fst] in Hfd. unfold frame_dict in Hfd. rewrite Hgfh in Hfd.
  pose proof (g4_sel_on_t k (a_st a) Hb Hne Hsp1 Hmulti) as Hon.
  specialize (Hid Hon). rewrite g4_fpid in Hid. rewrite Hon in Hsb.
  destruct Hsb as (Hinv & Hidr' & Hd1 & _).
  pose proof (g4_repr_inj _ _ Hidr Hidr' Hid) as <-. clear Hid Hidr'.
  rewrite Hset in Hinv. pose proof Hinv as Hinv'.
  destruct Hinv' as (_ & _ & _ & Hnd & _ & Hptr & _).
  pose proof (g4_clean_ids _ Hclean) as Hnz.
  assert (Hr: df_ddict (c3_dict k) <> nullval ->
              sel_r (c3_dict k) (c3_set k) tbl (fh_dictID h) = set_find (dc_set (a_st a)) (fh_dictID h)).
  { intros Hn. unfold sel_r. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ contradiction | ].
    rewrite Hset. destruct (Hpr _ _ _ Hinv Hidr) as [_ Hf]. apply Hf, Hnz. }
  assert (Hptr': forall q dd, In (q, dd) (dc_set (a_st a)) -> q <> nullval).
  { intros q dd Hin E. rewrite Forall_forall in Hptr. specialize (Hptr _ Hin). cbn in Hptr. subst q. exact Hptr. }
  destruct (set_sel (dc_set (a_st a)) (fh_dictID h)) as [dq|] eqn:Esel.
  + (* a hit: the set's DDict *)
    inversion Hfd; subst dq. clear Hfd.
    destruct (g4_find_hit _ _ _ Esel) as (Hid0 & e & Hin & Hide & Hfind & Hauto).
    destruct e as [q dd0]. cbn [fst snd] in *.
    destruct (eq_dec (df_ddict (c3_dict k)) nullval) as [Dn|Dn].
    * (* no current DDict: no selection, no dictionary; then the frame's ID is 0 *)
      exfalso.
      assert (Hs0: sel_r (c3_dict k) (c3_set k) tbl (fh_dictID h) = nullval).
      { unfold sel_r. destruct (eq_dec (df_ddict (c3_dict k)) nullval); [ reflexivity | contradiction ]. }
      rewrite Hs0 in Hd1. unfold sel_dict in Hd1. destruct (eq_dec nullval nullval); [ | congruence ]. subst d1.
      assert (Hg: fst (getddict_res (c3_dict k)) = nullval).
      { destruct Hdr as [Hdr | (_ & (_ & _ & _ & Hin'))].
        - destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [ | contradiction ].
          unfold stream_dict_ok in Hsd. rewrite Ed in Hsd. destruct Hsd as ((Ho & Hs) & _).
          cbn [dict_rel3_of] in Hdr. destruct (dr_src dr) as [pk | | q' pref]; [ contradiction | | ].
          + destruct Hdr as (_ & Hz). destruct (Zlength (dr_bytes dr) =? 0).
            * rewrite Hz. reflexivity.
            * destruct Hz as (buf0 & ld & am0 & Hlp & Hdd & _). rewrite Hdd in Dn. rewrite Dn in Hlp. contradiction.
          + destruct Hdr as (_ & _ & Hq & _ & Hdd & _). rewrite Hdd in Dn. rewrite Dn in Hq. contradiction.
        - apply list_in_map_inv in Hin'. destruct Hin' as ([q' dd'] & Eq & Hin'). cbn in Eq. subst q'.
          exfalso. exact (Hptr' _ _ Hin' Dn). }
      destruct (lc_dd c) as [[x buf]|] eqn:El.
      -- destruct (HDS x buf eq_refl) as (Hq & Hqn & _). rewrite Hg in Hq. contradiction.
      -- specialize (HCnone eq_refl). destruct HCid as [HCid|HCid]; lia.
    * (* the selection switched to the set's DDict q *)
      rewrite (Hr Dn), Hfind in Hd1. unfold sel_dict in Hd1.
      destruct (eq_dec q nullval) as [Eq|_]; [ exfalso; exact (Hptr' _ _ Hin Eq) | ]. subst d1.
      assert (Hgs: getddict_res (switch_fields q) = (q, switch_fields q)) by reflexivity.
      rewrite Hgs in HDS, HDN, Hloc |- *. cbn [fst snd] in HDS, HDN.
      split.
      -- unfold dd_model. destruct (lc_dd c) as [[x buf]|] eqn:El.
         ++ destruct (HDS x buf eq_refl) as (Hq & Hqn & Hsrc & Hld).
            destruct Hsrc as [(Hl1 & _) | (dd & Hc & Hbx & _ & Hrx)].
            ** exfalso. cbn in Hl1. apply Hqn. rewrite <- Hl1. reflexivity.
            ** rewrite Hq in Hc. pose proof (g4_caller_bytes _ _ _ _ Hnd Hsco Hin Hc) as Hbb.
               apply (g4_model_bytes x (dd_bytes dd0)); auto. rewrite Hbx; auto. rewrite Hbx, Hbb in Hld; exact Hld.
         ++ exfalso. specialize (HDN eq_refl). exact (Hptr' _ _ Hin HDN).
      -- intros k' Hk' Hfp dm' E. inversion E; subst dm'. right. rewrite Hk'.
         split; [ exact Hne | ]. split; [ reflexivity | ]. split; [ exists dd0; split; [ exact Hin | exact Hauto ] | ].
         exists (fh_dictID h). split; [ exact Hfp | ]. split; [ exact Hidr | ]. right. rewrite Hfind. reflexivity.
  + (* a miss: the current DDict, which cur_dict_ok describes *)
    destruct (Hcd dm Hfd) as [(Hn & _) | (_ & Hu & (dd0 & Hin0 & Hauto0) & _)]; [ contradiction | ].
    assert (Dn: df_ddict (c3_dict k) <> nullval) by exact (Hptr' _ _ Hin0).
    rewrite (Hr Dn), (g4_find_miss _ _ Hclean Esel) in Hd1. unfold sel_dict in Hd1.
    destruct (eq_dec nullval nullval) as [_|E]; [ | congruence ]. subst d1.
    rewrite (g4_getddict_m1 _ Hu) in HDS, HDN, Hloc |- *. cbn [fst snd] in HDS, HDN.
    split.
    * unfold dd_model. destruct (lc_dd c) as [[x buf]|] eqn:El.
      -- destruct (HDS x buf eq_refl) as (Hq & Hqn & Hsrc & Hld).
         destruct Hsrc as [(Hl1 & Hl2) | (dd & Hc & Hbx & _ & Hrx)].
         ++ exfalso. cbn [snd] in Hloc.
            assert (Hlq: df_local (c3_dict k) <> nullval) by (rewrite Hl1; exact Hqn).
            assert (Hin1: In (df_local (c3_dict k), dd0) (dc_set (a_st a))) by (rewrite Hl1, Hq; exact Hin0).
            pose proof (Hloc x buf dd0 Hl2 Hlq Hin1) as Hcur.
            destruct Hdr as [Hdr | (_ & (Hl0 & _))]; [ | contradiction ].
            unfold cur_ddict in Hcur. destruct (dc_dict (a_st a)) as [dr|] eqn:Ed; [ | discriminate ].
            cbn [dict_rel3_of] in Hdr. destruct (dr_src dr); try discriminate.
            destruct Hdr as (_ & _ & _ & Hl0 & _). contradiction.
         ++ rewrite Hq in Hc. pose proof (g4_caller_bytes _ _ _ _ Hnd Hsco Hin0 Hc) as Hbb.
            apply (g4_model_bytes x (dd_bytes dd0)); auto. rewrite Hbx; auto. rewrite Hbx, Hbb in Hld; exact Hld.
      -- exfalso. exact (Dn (HDN eq_refl)).
    * intros k' Hk' Hfp dm' E. inversion E; subst dm'. right. cbn [snd] in Hk'. rewrite Hk'.
      split; [ exact Hne | ]. split; [ exact Hu | ]. split; [ exists dd0; split; [ exact Hin0 | exact Hauto0 ] | ].
      exists (fh_dictID h). split; [ exact Hfp | ]. split; [ exact Hidr | ]. left. apply g4_find_miss; auto.
Qed.

(* a skippable frame keeps the model's current dictionary when the selection is off (with it on: GAP_skip_sel) *)
Lemma g4_cd_skip : forall a k cd,
  base_call (a_st a) k -> (c3_set k <> nil -> c3_sp k <> nullval) -> sel_on (c3_par k) (c3_sp k) = false ->
  (st_sel (a_st a) = (sel_none, None) -> cd = None) ->
  cur_dict_ok (a_st a) k cd -> forall k', cur_dict_ok (a_st a) k' cd.
Proof.
intros a k cd Hb Hsp1 Hoff Hcd0 Hcd k' dm Hdm.
destruct (Hcd dm Hdm) as [Hl | (Hne & _)]; [ left; exact Hl | ].
exfalso. destruct (g4_st_sel _ Hne) as [Hss | (_ & Hmulti & _ & _)].
- rewrite (Hcd0 Hss) in Hdm. discriminate.
- rewrite (g4_sel_on_t k (a_st a) Hb Hne Hsp1 Hmulti) in Hoff. discriminate.
Qed.

End CM_LH3G42_dict_1.
